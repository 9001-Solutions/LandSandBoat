#!/usr/bin/env python3
"""
Export Level ≤75 Gear to JSON

Aggregates all equippable gear (level ≤75) from the SQL data files into a
single JSON file with stats, slot, jobs, latents, client name, and Rare flag.

Data sources (all parsed directly, no DB connection needed):
    sql/item_basic.sql      - name, sortname (client name), type, flags
    sql/item_equipment.sql  - level, jobs bitmask, slot bitmask
    sql/item_weapon.sql     - weapon skill type, delay, damage
    sql/item_mods.sql       - stat modifiers
    sql/item_latents.sql    - conditional modifiers
    scripts/enum/mod.lua    - mod ID -> human-readable name
    scripts/enum/latent.lua - latent ID -> human-readable name

Usage:
    python tools/export_gear_json.py [--max-level N] [--output PATH]

Options:
    --max-level N   Maximum equipment level to include (default: 75)
    --output PATH   Output file path (default: tools/gear_data.json)
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

SLOT_NAMES = {
    0: "Main", 1: "Sub", 2: "Ranged", 3: "Ammo", 4: "Head", 5: "Body",
    6: "Hands", 7: "Legs", 8: "Feet", 9: "Neck", 10: "Waist",
    11: "Ear", 12: "Ear", 13: "Ring", 14: "Ring", 15: "Back",
}

JOB_ABBREVS = {
    1: "WAR", 2: "MNK", 3: "WHM", 4: "BLM", 5: "RDM", 6: "THF", 7: "PLD",
    8: "DRK", 9: "BST", 10: "BRD", 11: "RNG", 12: "SAM", 13: "NIN", 14: "DRG",
    15: "SMN", 16: "BLU", 17: "COR", 18: "PUP", 19: "DNC", 20: "SCH",
    21: "GEO", 22: "RUN",
}

WEAPON_SKILLS = {
    1: "H2H", 2: "Dagger", 3: "Sword", 4: "GreatSword", 5: "Axe",
    6: "GreatAxe", 7: "Scythe", 8: "Polearm", 9: "Katana", 10: "GreatKatana",
    11: "Club", 12: "Staff", 25: "Archery", 26: "Marksmanship",
    27: "Throwing", 41: "StringInstrument", 42: "WindInstrument",
    45: "Handbell",
}

# Weapon skill IDs that are non-combat (fishing)
NON_COMBAT_WEAPON_SKILLS = {48, 255}

EQUIPMENT_TYPE = 6
WEAPON_TYPE = 7

# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def parse_lua_enum(path):
    """Parse a Lua enum file and return {int_id: 'NAME'} reverse map."""
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            stripped = line.strip()
            if not stripped or stripped.startswith('--'):
                continue
            m = re.match(r'(\w+)\s*=\s*(-?\d+)', stripped)
            if m:
                name, val = m.group(1), int(m.group(2))
                result[val] = name
    return result


def parse_sql_variables(path):
    """Pre-scan a SQL file for SET @VAR = N lines, return {'VAR': int}."""
    variables = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            m = re.match(r"SET\s+@(\w+)\s*=\s*(-?\d+)", line.strip())
            if m:
                variables[m.group(1)] = int(m.group(2))
    return variables


def parse_sql_insert(line, sql_vars=None):
    """Extract a VALUES tuple from an INSERT line.

    Handles: integers, negative integers, @VAR references, and 'string' values.
    Returns a list of values (int or str), or None if the line isn't an INSERT.
    """
    m = re.search(r'VALUES\s*\((.+)\)\s*;', line)
    if not m:
        return None

    raw = m.group(1)
    values = []
    i = 0
    while i < len(raw):
        c = raw[i]
        if c in (' ', '\t'):
            i += 1
            continue
        if c == ',':
            i += 1
            continue
        if c == "'":
            # String literal — find closing quote
            end = raw.index("'", i + 1)
            values.append(raw[i + 1:end])
            i = end + 1
        elif c == '@':
            # Variable reference
            j = i + 1
            while j < len(raw) and (raw[j].isalnum() or raw[j] == '_'):
                j += 1
            var_name = raw[i + 1:j]
            values.append(sql_vars.get(var_name, 0) if sql_vars else 0)
            i = j
        elif c == '-' or c.isdigit():
            # Number (possibly negative)
            j = i + 1
            while j < len(raw) and raw[j].isdigit():
                j += 1
            values.append(int(raw[i:j]))
            i = j
        else:
            i += 1

    return values


# ---------------------------------------------------------------------------
# SQL table parsers
# ---------------------------------------------------------------------------

def parse_item_basic(path):
    """Parse item_basic.sql.

    Returns {itemId: {'name': str, 'sortname': str, 'flags': int}}
    filtered to type EQUIPMENT_TYPE or WEAPON_TYPE.
    """
    sql_vars = parse_sql_variables(path)
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line, sql_vars)
            if vals is None or len(vals) < 9:
                continue
            # Columns: itemid, subid, name, sortname, type, stackSize, flags, aH, BaseSell
            item_id = int(vals[0])
            item_type = int(vals[4])
            if item_type not in (EQUIPMENT_TYPE, WEAPON_TYPE):
                continue
            result[item_id] = {
                'name': vals[2],
                'sortname': vals[3],
                'flags': int(vals[6]),
            }
    return result


def parse_item_equipment(path, max_level=75):
    """Parse item_equipment.sql.

    Returns {itemId: {'level': int, 'jobs': int, 'slot': int}}
    filtered to level <= max_level.
    """
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 9:
                continue
            # Columns: itemId, name, level, ilevel, jobs, MId, shieldSize, scriptType, slot, rslot, rslotlook, su_level
            item_id = int(vals[0])
            level = int(vals[2])
            if level > max_level:
                continue
            result[item_id] = {
                'level': level,
                'jobs': int(vals[4]),
                'slot': int(vals[8]),
            }
    return result


def parse_item_weapon(path):
    """Parse item_weapon.sql.

    Returns {itemId: {'skill': int, 'delay': int, 'dmg': int}}.
    """
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 11:
                continue
            # Columns: itemId, name, skill, subskill, ilvl_skill, ilvl_parry, ilvl_macc, dmgType, hit, delay, dmg, unlock_points
            item_id = int(vals[0])
            result[item_id] = {
                'skill': int(vals[2]),
                'delay': int(vals[9]),
                'dmg': int(vals[10]),
            }
    return result


def parse_item_mods(path):
    """Parse item_mods.sql.

    Returns {itemId: [(modId, value), ...]}.
    """
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 3:
                continue
            # Columns: itemId, modId, value
            item_id = int(vals[0])
            mod_id = int(vals[1])
            value = int(vals[2])
            result.setdefault(item_id, []).append((mod_id, value))
    return result


def parse_item_latents(path):
    """Parse item_latents.sql.

    Returns {itemId: [(modId, value, latentId, latentParam), ...]}.
    """
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 5:
                continue
            # Columns: itemId, modId, value, latentId, latentParam
            item_id = int(vals[0])
            mod_id = int(vals[1])
            value = int(vals[2])
            latent_id = int(vals[3])
            latent_param = int(vals[4])
            result.setdefault(item_id, []).append((mod_id, value, latent_id, latent_param))
    return result


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

def format_name(raw):
    """Convert SQL name like 'scp._harness_+1' to 'Scp. Harness +1'."""
    return raw.replace('_', ' ').strip().title().replace(' +', ' +').replace(' -', ' -')


def decode_slot(bitmask):
    """Decode slot bitmask to a human-readable slot name (lowest set bit)."""
    if bitmask == 0:
        return "None"
    for bit in range(16):
        if bitmask & (1 << bit):
            return SLOT_NAMES.get(bit, f"Slot{bit}")
    return "Unknown"


ALL_JOBS_MASK = sum(1 << bit for bit in JOB_ABBREVS)  # bits 1-22
ALL_JOBS_NO_RUN = ALL_JOBS_MASK & ~(1 << 22)          # bits 1-21 (pre-RUN era)


def decode_jobs(bitmask):
    """Decode jobs bitmask to a list of job abbreviations.

    Returns ["All"] if every standard job bit is set (with or without RUN).
    """
    masked = bitmask & ALL_JOBS_MASK
    if masked == ALL_JOBS_MASK or masked == ALL_JOBS_NO_RUN:
        return ['All']
    jobs = []
    for bit in range(1, 23):
        if bitmask & (1 << bit):
            abbrev = JOB_ABBREVS.get(bit)
            if abbrev:
                jobs.append(abbrev)
    return jobs


# ---------------------------------------------------------------------------
# Combat relevance filter
# ---------------------------------------------------------------------------

# Mods that are non-combat (crafting, gathering, cosmetic, race-lock, etc.)
# An item whose only mods (besides DEF) are in this set is filtered out.
NON_COMBAT_MODS = {
    # Race / cosmetic
    'EQUIPMENT_ONLY_RACE', 'APPRECIATE_GYSAHL_GREENS',
    # Gathering
    'FISH', 'LOGGING_RESULT', 'MINING_RESULT', 'HARVESTING_RESULT',
    'DIGGING_RESULT', 'CLAMMING_RESULT',
    'CLAMMING_IMPROVED_RESULTS', 'CLAMMING_REDUCED_INCIDENTS',
    'DIG_BYPASS_FATIGUE', 'DIG_RARE_ABILITY',
    'EAT_RAW_FISH',
    # Crafting skill bonuses
    'WOOD', 'SMITH', 'GOLDSMITH', 'CLOTH', 'LEATHER', 'BONE', 'ALCHEMY', 'COOK',
    # Synth modifiers
    'SYNTH_SUCCESS_RATE', 'SYNTH_SKILL_GAIN', 'SYNTH_HQ_RATE', 'SYNTH_MATERIAL_LOSS',
    'SYNTH_SUCCESS_RATE_WOODWORKING', 'SYNTH_SUCCESS_RATE_SMITHING',
    'SYNTH_SUCCESS_RATE_GOLDSMITHING', 'SYNTH_SUCCESS_RATE_CLOTHCRAFT',
    'SYNTH_SUCCESS_RATE_LEATHERCRAFT', 'SYNTH_SUCCESS_RATE_BONECRAFT',
    'SYNTH_SUCCESS_RATE_ALCHEMY', 'SYNTH_SUCCESS_RATE_COOKING',
    'SYNTH_ANTI_HQ_WOODWORKING', 'SYNTH_ANTI_HQ_SMITHING',
    'SYNTH_ANTI_HQ_GOLDSMITHING', 'SYNTH_ANTI_HQ_CLOTHCRAFT',
    'SYNTH_ANTI_HQ_LEATHERCRAFT', 'SYNTH_ANTI_HQ_BONECRAFT',
    'SYNTH_ANTI_HQ_ALCHEMY', 'SYNTH_ANTI_HQ_COOKING',
}

# Level threshold below which "basic" gear (DEF-only armor, modless weapons)
# is considered filler and filtered out.
LOW_LEVEL_THRESHOLD = 10


def has_combat_value(entry, weapon_info):
    """Return True if an item has meaningful combat purpose.

    Filters out:
    - Fishing gear, pet food, animators, and other non-combat weapon types
    - Any non-weapon item with zero mods and zero latents
    - Low-level (≤10) armor whose only combat mod is DEF
    - Low-level (≤10) weapons with no mods and no latents
    """
    item_id = entry['id']
    mods = entry['mods']
    latents = entry['latents']
    is_weapon = 'dmg' in entry
    level = entry['level']

    # Filter out non-combat weapon types (fishing rods/bait)
    if is_weapon:
        wpn = weapon_info.get(item_id)
        if wpn and wpn['skill'] in NON_COMBAT_WEAPON_SKILLS:
            return False
        # Skill 0 contains a mix: grips/stat-ammo (combat) and pet food/jugs/
        # automaton parts/soul trappers (non-combat). Filter the latter by traits:
        #   - BST jugs: dmg > 200 (encodes pet ID)
        #   - Pet food: delay 84-85, dmg 50-900
        #   - Automaton oil: delay 84, dmg 527+
        #   - Soul trappers/animators: Ranged slot, skill 0
        if wpn and wpn['skill'] == 0:
            slot = entry['slot']
            dmg, delay = wpn['dmg'], wpn['delay']
            if slot == 'Ranged':
                return False  # animators, soul trappers
            if dmg > 200:
                return False  # BST jugs, automaton oil
            if delay in (84, 85) and not mods:
                return False  # pet food

    # Items with latents always have combat purpose
    if latents:
        return True

    # Check for meaningful (non-cosmetic) mods
    combat_mods = {k: v for k, v in mods.items() if k not in NON_COMBAT_MODS}

    non_def_mods = {k: v for k, v in mods.items() if k != 'DEF'}

    if not is_weapon:
        # Items whose only non-DEF mods are all non-combat → crafting/gathering gear
        if non_def_mods and all(k in NON_COMBAT_MODS for k in non_def_mods):
            return False

        # No mods at all, or only DEF
        if not combat_mods:
            return False

        # Low-level armor where DEF is the only combat mod is filler
        if level <= LOW_LEVEL_THRESHOLD and all(k == 'DEF' for k in combat_mods):
            return False
    else:
        # Low-level weapons with no combat mods are generic vendor trash
        if level <= LOW_LEVEL_THRESHOLD and not combat_mods:
            return False

    return True


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Export level-capped equippable gear from SQL data to JSON.'
    )
    parser.add_argument(
        '--max-level', type=int, default=75,
        help='Maximum equipment level to include (default: 75)'
    )
    parser.add_argument(
        '--output', type=str, default=None,
        help='Output file path (default: tools/gear_data.json)'
    )
    parser.add_argument(
        '--no-filter', action='store_true',
        help='Disable combat-relevance filter (include cosmetics, fishing gear, etc.)'
    )
    args = parser.parse_args()

    # Resolve paths relative to repo root (parent of tools/)
    repo_root = os.path.normpath(os.path.join(os.path.dirname(__file__), '..'))

    def repo_path(rel):
        return os.path.join(repo_root, rel)

    output_path = args.output or os.path.join(os.path.dirname(__file__), 'gear_data.json')

    print(f'Parsing data files (max level: {args.max_level})...')

    # Parse Lua enums for human-readable names
    mod_names = parse_lua_enum(repo_path('scripts/enum/mod.lua'))
    latent_names = parse_lua_enum(repo_path('scripts/enum/latent.lua'))

    # Parse SQL tables
    basics = parse_item_basic(repo_path('sql/item_basic.sql'))
    equipment = parse_item_equipment(repo_path('sql/item_equipment.sql'), args.max_level)
    weapons = parse_item_weapon(repo_path('sql/item_weapon.sql'))
    mods = parse_item_mods(repo_path('sql/item_mods.sql'))
    latents = parse_item_latents(repo_path('sql/item_latents.sql'))

    print(f'  item_basic:     {len(basics)} equipment/weapon entries')
    print(f'  item_equipment: {len(equipment)} entries (level <= {args.max_level})')
    print(f'  item_weapon:    {len(weapons)} entries')
    print(f'  item_mods:      {sum(len(v) for v in mods.values())} mod rows')
    print(f'  item_latents:   {sum(len(v) for v in latents.values())} latent rows')

    # Join on itemId
    items = []
    for item_id in sorted(equipment.keys()):
        if item_id not in basics:
            continue

        basic = basics[item_id]
        equip = equipment[item_id]
        flags = basic['flags']

        entry = {
            'id': item_id,
            'name': format_name(basic['name']),
            'clientName': format_name(basic['sortname']),
            'slot': decode_slot(equip['slot']),
            'level': equip['level'],
            'rare': bool(flags & 0x8000),
            'exclusive': bool(flags & 0x4000),
            'jobs': decode_jobs(equip['jobs']),
        }

        # Mods
        item_mods = mods.get(item_id, [])
        mods_dict = {}
        for mod_id, value in item_mods:
            mod_name = mod_names.get(mod_id, str(mod_id))
            mods_dict[mod_name] = value
        entry['mods'] = mods_dict

        # Latents
        item_latents = latents.get(item_id, [])
        latents_list = []
        for mod_id, value, latent_id, latent_param in item_latents:
            latents_list.append({
                'mod': mod_names.get(mod_id, str(mod_id)),
                'value': value,
                'latent': latent_names.get(latent_id, str(latent_id)),
                'param': latent_param,
            })
        entry['latents'] = latents_list

        # Weapon fields
        if item_id in weapons:
            wpn = weapons[item_id]
            entry['dmg'] = wpn['dmg']
            entry['delay'] = wpn['delay']
            entry['weaponType'] = WEAPON_SKILLS.get(wpn['skill'], f"Skill{wpn['skill']}")

        items.append(entry)

    # Filter out non-combat items
    if not args.no_filter:
        pre_filter = len(items)
        items = [i for i in items if has_combat_value(i, weapons)]
        print(f'  Filtered: {pre_filter} -> {len(items)} (removed {pre_filter - len(items)} non-combat items)')

    output = {
        'generated': datetime.now(timezone.utc).isoformat(),
        'count': len(items),
        'items': items,
    }

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f'Wrote {len(items)} items to {output_path}')


if __name__ == '__main__':
    main()
