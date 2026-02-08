#!/usr/bin/env python3
"""
Export Mob Stats to JSON

Computes combat stats for every mob spawn in the game by replicating the C++
stat calculation pipeline (mobutils.cpp, battleentity.cpp, grades.cpp) using
only SQL file parsing — no database connection required.

Data sources:
    sql/mob_spawn_points.sql   - mobid, groupid, minLevel, maxLevel
    sql/mob_groups.sql         - groupid, poolid, zoneid, HP, MP
    sql/mob_pools.sql          - poolid, name, familyid, mJob, sJob, mobType
    sql/mob_family_system.sql  - familyID, family name, stat ranks, HP/MP %
    sql/mob_pool_mods.sql      - poolid, modid, value, is_mob_mod
    sql/mob_family_mods.sql    - familyid, modid, value, is_mob_mod
    sql/zone_settings.sql      - zoneid, zone name
    sql/skill_caps.sql         - level -> r0..r13 skill cap table
    sql/skill_ranks.sql        - skillid -> rank per job

Usage:
    python tools/export_mob_stats.py [--output PATH]
"""

import argparse
import json
import math
import os
import re
import sys
from datetime import datetime, timezone

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

JOB_ABBREVS = {
    0: 'NON', 1: 'WAR', 2: 'MNK', 3: 'WHM', 4: 'BLM', 5: 'RDM', 6: 'THF',
    7: 'PLD', 8: 'DRK', 9: 'BST', 10: 'BRD', 11: 'RNG', 12: 'SAM',
    13: 'NIN', 14: 'DRG', 15: 'SMN', 16: 'BLU', 17: 'COR', 18: 'PUP',
    19: 'DNC', 20: 'SCH', 21: 'GEO', 22: 'RUN',
}

# Jobs that grant MP (used for MP calculation)
MP_JOBS = {3, 4, 5, 7, 8, 15, 16, 20}  # WHM BLM RDM PLD DRK SMN BLU SCH

MOBTYPE_NOTORIOUS = 0x02

# grades.cpp: JobGrades[23][9] — {HP, MP, STR, DEX, VIT, AGI, INT, MND, CHR}
JOB_GRADES = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0],  # NON
    [2, 0, 1, 3, 4, 3, 6, 6, 5],  # WAR
    [1, 0, 3, 2, 1, 6, 7, 4, 5],  # MNK
    [5, 3, 4, 6, 4, 5, 5, 1, 3],  # WHM
    [6, 2, 6, 3, 6, 3, 1, 5, 4],  # BLM
    [4, 4, 4, 4, 5, 5, 3, 3, 4],  # RDM
    [4, 0, 4, 1, 4, 2, 3, 7, 7],  # THF
    [3, 6, 2, 5, 1, 7, 7, 3, 3],  # PLD
    [3, 6, 1, 3, 3, 4, 3, 7, 7],  # DRK
    [3, 0, 4, 3, 4, 6, 5, 5, 1],  # BST
    [4, 0, 4, 4, 4, 6, 4, 4, 2],  # BRD
    [5, 0, 5, 4, 4, 1, 5, 4, 5],  # RNG
    [2, 0, 3, 3, 3, 4, 5, 5, 4],  # SAM
    [4, 0, 3, 2, 3, 2, 4, 7, 6],  # NIN
    [3, 0, 2, 4, 3, 4, 6, 5, 3],  # DRG
    [7, 1, 6, 5, 6, 4, 2, 2, 2],  # SMN
    [4, 4, 5, 5, 5, 5, 5, 5, 5],  # BLU
    [4, 0, 5, 3, 5, 2, 3, 5, 5],  # COR
    [4, 0, 5, 2, 4, 3, 5, 6, 3],  # PUP
    [4, 0, 4, 3, 5, 2, 6, 6, 2],  # DNC
    [5, 4, 6, 4, 5, 4, 3, 4, 3],  # SCH
    [3, 2, 6, 4, 5, 4, 3, 3, 4],  # GEO
    [3, 6, 3, 4, 5, 2, 4, 4, 6],  # RUN
]

# grades.cpp: MobHPScale[8][3] — {Base, Job/SJ Scale, ScaleX}
MOB_HP_SCALE = [
    [0, 0, 0],   # 0
    [36, 9, 1],  # A (1)
    [33, 8, 1],  # B (2)
    [32, 7, 1],  # C (3)
    [29, 6, 0],  # D (4)
    [27, 5, 0],  # E (5)
    [24, 4, 0],  # F (6)
    [22, 3, 0],  # G (7)
]

# grades.cpp: MobRBI[6][2] — {RI, Scale}
MOB_RBI = [
    [0, 0],   # 0
    [1, 0],   # 1
    [2, 0],   # 2
    [3, 3],   # 3
    [4, 7],   # 4
    [5, 14],  # 5
]

# CheckSubJobZone — zone IDs from mobutils.cpp:484-580
# Original/RoZ zones where mobs under level 50 use the complex sub-job stat formula
SUB_JOB_ZONES = {
    100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
    115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
    139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152,
    153, 154,
    157, 158, 159, 160,
    161, 162, 163,
    165, 166, 167, 168, 169, 170,
    172, 173, 174,
    176, 177, 178, 179, 180, 181,
    184,
    190, 191, 192, 193, 194, 195, 196, 197, 198,
    200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
    211, 212, 213,
    220, 221,
    227, 228,
}

# Mod IDs we care about (from scripts/enum/mod.lua)
MOD_ATT = 23
MOD_DEF = 1
MOD_ACC = 25
MOD_EVA = 68

# Mod name -> ID mapping for Lua override parsing
MOD_NAME_TO_ID = {
    'DEF': 1, 'STR': 8, 'DEX': 9, 'VIT': 10, 'AGI': 11,
    'INT': 12, 'MND': 13, 'CHR': 14, 'ATT': 23, 'ACC': 25,
    'ATTP': 62, 'DEFP': 63, 'EVA': 68,
}

# ---------------------------------------------------------------------------
# SQL parsing (reused from export_gear_json.py)
# ---------------------------------------------------------------------------

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

    Handles: integers, negative integers, floats, @VAR references,
    'string' values, hex literals (0x...), and NULL.
    Returns a list of values (int, float, str, or None), or None if not an INSERT.
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
            # Handle backslash-escaped quotes inside strings (e.g. Selh\'teus)
            j = i + 1
            parts = []
            while j < len(raw):
                if raw[j] == '\\' and j + 1 < len(raw):
                    parts.append(raw[j + 1])
                    j += 2
                elif raw[j] == "'":
                    break
                else:
                    parts.append(raw[j])
                    j += 1
            values.append(raw[i + 1:j].replace("\\'", "'"))
            i = j + 1
        elif c == '@':
            j = i + 1
            while j < len(raw) and (raw[j].isalnum() or raw[j] == '_'):
                j += 1
            var_name = raw[i + 1:j]
            values.append(sql_vars.get(var_name, 0) if sql_vars else 0)
            i = j
        elif raw[i:i+4].upper() == 'NULL':
            values.append(None)
            i += 4
        elif raw[i:i+2] == '0x' or raw[i:i+2] == '0X':
            j = i + 2
            while j < len(raw) and raw[j] in '0123456789abcdefABCDEF':
                j += 1
            values.append(raw[i:j])  # keep as hex string
            i = j
        elif c == '-' or c == '.' or c.isdigit():
            j = i + 1
            is_float = (c == '.')
            while j < len(raw) and (raw[j].isdigit() or raw[j] == '.'):
                if raw[j] == '.':
                    is_float = True
                j += 1
            token = raw[i:j]
            values.append(float(token) if is_float else int(token))
            i = j
        else:
            i += 1

    return values


# ---------------------------------------------------------------------------
# C++ formula ports
# ---------------------------------------------------------------------------

def get_base_to_rank(rank, lvl):
    """mobutils.cpp:304-325 — GetBaseToRank"""
    if rank == 1:  return 5 + ((lvl - 1) * 50) // 100   # A
    if rank == 2:  return 4 + ((lvl - 1) * 45) // 100   # B
    if rank == 3:  return 4 + ((lvl - 1) * 40) // 100   # C
    if rank == 4:  return 3 + ((lvl - 1) * 35) // 100   # D
    if rank == 5:  return 3 + ((lvl - 1) * 30) // 100   # E
    if rank == 6:  return 2 + ((lvl - 1) * 25) // 100   # F
    if rank == 7:  return 2 + ((lvl - 1) * 20) // 100   # G
    return 0


def get_sub_job_stats(rank, level, stat):
    """mobutils.cpp:332-477 — GetSubJobStats"""
    s = 0.0
    if rank == 1:  # A
        if level <= 30:
            s = max(math.floor(stat / (4.0 - 0.225 * (level - 30))), 2.0)
        elif level <= 40:
            s = math.floor(stat / (3.25 - 0.073 * (level - 30)))
        elif level <= 46:
            s = math.floor(stat / (2.55 - 0.001 * (level - 41)))
        else:
            s = math.floor(stat / (2.7 - 0.001 * (level - 45)))
    elif rank == 2:  # B
        if level <= 30:
            s = max(math.floor(stat / (3.1 - 0.075 * (level - 32))), 2.0)
        elif level <= 40:
            s = math.floor(stat / (3.1 - 0.075 * (level - 32)))
        elif level <= 45:
            s = math.floor(stat / (2.5 - 0.025 * (level - 40)))
        else:
            s = math.floor(stat / (2.35 - 0.04 * (level - 44)))
    elif rank == 3:  # C
        if level <= 30:
            s = max(math.floor(stat / (4.5 - 0.15 * (level - 26))), 2.0)
        elif level <= 40:
            s = math.floor(stat / (3.28 - 0.001 * (level - 30)))
        elif level <= 45:
            s = math.floor(stat / (2.6 - 0.025 * (level - 40)))
        else:
            s = math.floor(stat / (2.1 - 0.2 * (level - 49)))
    elif rank == 4:  # D
        if level <= 30:
            s = max(math.floor(stat / (5.0 - 0.05 * (level - 21))), 1.0)
        elif level <= 40:
            s = math.floor(stat / (3.2 - 0.001 * (level - 29)))
        elif level <= 45:
            s = math.floor(stat / (3.5 - 0.08 * (level - 32)))
        else:
            s = math.floor(stat / (3.25 - 0.045 * (level - 32)))
    elif rank == 5:  # E
        if level <= 30:
            s = max(math.floor(stat / (3.8 - 0.1 * (level - 32))), 1.0)
        elif level <= 40:
            s = math.floor(stat / (3.8 - 0.15 * (level - 32)))
        elif level <= 45:
            s = math.floor(stat / (2.7 - 0.075 * (level - 40)))
        else:
            s = math.floor(stat / (2.7 - 0.05 * (level - 45)))
    elif rank == 6:  # F
        if level <= 30:
            s = max(math.floor(stat / (4.0 - 0.15 * (level - 35))), 1.0)
        elif level <= 40:
            s = math.floor(stat / (4.0 - 0.15 * (level - 30)))
        elif level <= 46:
            s = math.floor(stat / (3.0 - 0.1125 * (level - 40)))
        else:
            s = math.floor(stat / (3.0 - 0.07 * (level - 40)))
    elif rank == 7:  # G
        if level <= 30:
            s = max(math.floor(stat / (4.0 - 0.15 * (level - 35))), 1.0)
        elif level <= 40:
            s = math.floor(stat / (4.0 - 0.2 * (level - 31)))
        elif level <= 46:
            s = math.floor(stat / (2.5 - 0.09 * (level - 40)))
        else:
            s = math.floor(stat / 2)
    else:
        s = stat / 2
    return int(s)


def get_base_def_eva(rank, lvl):
    """mobutils.cpp:254-296 — GetBaseDefEva"""
    if lvl > 50:
        if rank == 1: return int(math.floor(153 + (lvl - 50) * 5.0))
        if rank == 2: return int(math.floor(147 + (lvl - 50) * 4.9))
        if rank == 3: return int(math.floor(142 + (lvl - 50) * 4.8))
        if rank == 4: return int(math.floor(136 + (lvl - 50) * 4.7))
        if rank == 5: return int(math.floor(126 + (lvl - 50) * 4.5))
    else:
        if rank == 1: return int(math.floor(6 + (lvl - 1) * 3.0))
        if rank == 2: return int(math.floor(5 + (lvl - 1) * 2.9))
        if rank == 3: return int(math.floor(5 + (lvl - 1) * 2.8))
        if rank == 4: return int(math.floor(4 + (lvl - 1) * 2.7))
        if rank == 5: return int(math.floor(4 + (lvl - 1) * 2.5))
    return 0


def get_base_skill(rank, lvl, skill_caps, skill_ranks):
    """mobutils.cpp:212-232 — GetBaseSkill

    Maps rank 1-5 to specific skill lookups:
      rank 1: skill_caps[lvl][skill_ranks[6][1]]   (great_axe/WAR = A+)
      rank 2: skill_caps[lvl][skill_ranks[12][1]]   (staff/WAR = B)
      rank 3: skill_caps[lvl][skill_ranks[29][1]]   (evasion/WAR = C)
      rank 4: skill_caps[lvl][skill_ranks[25][1]]   (archery/WAR = D)
      rank 5: skill_caps[lvl][skill_ranks[27][2]]   (throwing/MNK = E)
    """
    capped_lvl = min(lvl, 99)
    skill_rank_lookups = {
        1: (6, 1),   # great_axe, WAR
        2: (12, 1),  # staff, WAR
        3: (29, 1),  # evasion, WAR
        4: (25, 1),  # archery, WAR
        5: (27, 2),  # throwing, MNK
    }
    if rank not in skill_rank_lookups:
        return 0
    skill_id, job_id = skill_rank_lookups[rank]
    cap_rank = skill_ranks.get(skill_id, {}).get(job_id, 0)
    return skill_caps.get(capped_lvl, {}).get(cap_rank, 0)


def get_skill_rank(skill_id, job_id, skill_ranks):
    """battleutils.cpp:340-343 — GetSkillRank"""
    return skill_ranks.get(skill_id, {}).get(job_id, 0)


def job_skill_rank_to_base_eva_rank(mjob, sjob, skill_ranks):
    """mobutils.cpp:1247-1276 — JobSkillRankToBaseEvaRank

    Pick the best evasion skill rank between main/sub job (lower=better),
    then map to DEF/EVA base rank 1-5.
    """
    main_eva = get_skill_rank(29, mjob, skill_ranks)  # SKILL_EVASION = 29
    sub_eva = get_skill_rank(29, sjob, skill_ranks)

    # If either is 0 (job doesn't have evasion), use the other
    if main_eva == 0 and sub_eva == 0:
        return 3  # fallback C rank
    if main_eva == 0:
        best = sub_eva
    elif sub_eva == 0:
        best = main_eva
    else:
        best = min(main_eva, sub_eva)

    if best <= 2:   return 1  # A, A+
    if best <= 5:   return 2  # B+, B, B-
    if best <= 8:   return 3  # C+, C, C-
    if best == 9:   return 4  # D
    if best == 10:  return 5  # E
    return 3  # fallback


def calculate_hp(mlvl, mjob, sjob, family_hp_pct, family_id, hp_override):
    """mobutils.cpp:617-706 — HP calculation

    If hp_override > 0, use it directly. Otherwise, compute from formula.
    """
    if hp_override > 0:
        return hp_override

    m_job_grade = JOB_GRADES[mjob][0] if mjob < len(JOB_GRADES) else 0
    s_job_grade = JOB_GRADES[sjob][0] if sjob < len(JOB_GRADES) else 0

    base_hp = MOB_HP_SCALE[m_job_grade][0]    # BaseHP
    job_scale = MOB_HP_SCALE[m_job_grade][1]   # JobScale
    scale_x = MOB_HP_SCALE[m_job_grade][2]     # ScaleXHP
    sj_job_scale = MOB_HP_SCALE[s_job_grade][1]
    sj_scale_x = MOB_HP_SCALE[s_job_grade][2]

    ri_grade = min(mlvl, 5)
    ri = MOB_RBI[ri_grade][1]

    mlvl_if = 1 if mlvl > 5 else 0
    mlvl_if30 = 1 if mlvl > 30 else 0
    race_scale = 6

    base_mob_hp = 0
    if mlvl > 0:
        min_lvl_5 = min(mlvl, 5)
        min_lvl_30 = min(mlvl, 30)
        base_mob_hp = (base_hp
            + (min_lvl_5 - 1) * (job_scale + race_scale - 1)
            + ri
            + mlvl_if * (min_lvl_30 - 5) * (2 * (job_scale + race_scale) + min_lvl_30 - 6) // 2
            + mlvl_if30 * ((mlvl - 30) * (63 + scale_x) + (mlvl - 31) * (job_scale + race_scale)))

    # Subjob HP contribution
    if mlvl > 49:
        mlvl_scale = mlvl
    elif mlvl > 39:
        mlvl_scale = int(math.floor(mlvl * 0.75))
    elif mlvl > 30:
        mlvl_scale = int(math.floor(mlvl * 0.50))
    elif mlvl > 24:
        mlvl_scale = int(math.floor(mlvl * 0.25))
    else:
        mlvl_scale = 0

    sj_hp = math.ceil((sj_job_scale * max(mlvl_scale - 1, 0)
        + (0.5 + 0.5 * sj_scale_x) * max(mlvl_scale - 10, 0)
        + max(mlvl_scale - 30, 0)
        + max(mlvl_scale - 50, 0)
        + max(mlvl_scale - 70, 0)) / 2)

    mob_hp = base_mob_hp + sj_hp

    # Family modifiers
    if family_id in (189, 190):  # Orc families: +5%
        mob_hp = int(mob_hp * 1.05)
    elif family_id == 202:  # Quadav: -5%
        mob_hp = int(mob_hp * 0.95)
    elif family_id == 179:  # Manticore: +50%
        mob_hp = int(mob_hp * 1.5)

    return max(1, mob_hp)


def calculate_mp(mlvl, mjob, sjob, family_mp_pct, mp_override):
    """mobutils.cpp:725-794 — MP calculation

    Only if main or sub job is a mage job. family_mp_pct is the MP% from
    mob_family_system (used as scale factor, e.g. 140 means 1.4x).
    """
    has_mp = mjob in MP_JOBS or sjob in MP_JOBS
    if not has_mp:
        return 0

    if mp_override > 0:
        return mp_override

    scale = family_mp_pct / 100.0
    return int(18.2 * pow(mlvl, 1.1075) * scale) + 10


def compute_stats(mlvl, mjob, sjob, family, zone_id, hp_override, mp_override,
                  skill_caps, skill_ranks):
    """Compute all combat stats for a mob at a given level.

    Returns a dict with STR-CHR, HP, MP, base/total ATT/DEF/ACC/EVA.
    """
    # Stat indices in JOB_GRADES: 2=STR, 3=DEX, 4=VIT, 5=AGI, 6=INT, 7=MND, 8=CHR
    stat_names = ['STR', 'DEX', 'VIT', 'AGI', 'INT', 'MND', 'CHR']
    stat_indices = [2, 3, 4, 5, 6, 7, 8]

    # Family stat ranks from mob_family_system
    family_stat_ranks = [family.get(s, 3) for s in stat_names]

    result = {}
    for i, (name, idx) in enumerate(zip(stat_names, stat_indices)):
        f_stat = get_base_to_rank(family_stat_ranks[i], mlvl)
        m_stat = get_base_to_rank(JOB_GRADES[mjob][idx] if mjob < len(JOB_GRADES) else 0, mlvl)
        s_stat_raw = get_base_to_rank(JOB_GRADES[sjob][idx] if sjob < len(JOB_GRADES) else 0, mlvl)

        # Sub-job stat processing
        if zone_id in SUB_JOB_ZONES and mlvl < 50:
            s_job_grade = JOB_GRADES[sjob][idx] if sjob < len(JOB_GRADES) else 0
            s_stat = get_sub_job_stats(s_job_grade, mlvl, s_stat_raw)
        else:
            s_stat = s_stat_raw // 2

        result[name] = f_stat + m_stat + s_stat

    # HP/MP
    result['HP'] = calculate_hp(mlvl, mjob, sjob, family.get('HP_pct', 100),
                                family.get('family_id', 0), hp_override)
    result['MP'] = calculate_mp(mlvl, mjob, sjob, family.get('MP_pct', 100), mp_override)

    # ATT/ACC base (skill-based ranks from family)
    att_rank = family.get('ATT', 1)
    acc_rank = family.get('ACC', 1)
    def_rank = family.get('DEF', 3)
    eva_rank = family.get('EVA', 3)

    base_att = get_base_skill(att_rank, mlvl, skill_caps, skill_ranks)
    base_acc = get_base_skill(acc_rank, mlvl, skill_caps, skill_ranks)
    base_def = get_base_def_eva(def_rank, mlvl)
    base_eva_rank = job_skill_rank_to_base_eva_rank(mjob, sjob, skill_ranks)
    base_eva = get_base_def_eva(base_eva_rank, mlvl)

    result['baseATT'] = base_att
    result['baseACC'] = base_acc
    result['baseDEF'] = base_def
    result['baseEVA'] = base_eva

    # Total combat stats (battleentity.cpp)
    # Mobs: ATT = max(1, 8 + base_att + floor(STR * 0.5))
    result['totalAttack'] = max(1, 8 + base_att + int(math.floor(result['STR'] * 0.5)))
    # DEF = max(1, 8 + floor(VIT * 0.5) + base_def)
    result['totalDefense'] = max(1, 8 + int(math.floor(result['VIT'] * 0.5)) + base_def)
    # ACC = max(1, base_acc + floor(DEX / 2))
    result['totalAccuracy'] = max(1, base_acc + int(math.floor(result['DEX'] / 2)))
    # EVA = max(1, base_eva + floor(AGI / 2))
    result['totalEvasion'] = max(1, base_eva + int(math.floor(result['AGI'] / 2)))

    # Accuracy target for a level 75 player to reach 95% hit rate.
    # physical_hit_rate.lua: hitrate = (75 + (acc - eva) / 2) / 100
    # Level correction: if player_lvl < mob_lvl, acc += (player_lvl - mob_lvl) * 4
    # Solving for 95%: player_acc = mob_eva + 40 + max(mob_lvl - 75, 0) * 4
    level_penalty = max(mlvl - 75, 0) * 4
    result['accTarget95'] = result['totalEvasion'] + 40 + level_penalty

    return result


# ---------------------------------------------------------------------------
# AirSkyBoat Lua override parsing
# ---------------------------------------------------------------------------

def extract_spawn_mods(filepath):
    """Extract setMod/addMod calls from onMobSpawn/onMobInitialize in a Lua file.

    Only extracts from the top-level of spawn/init functions (depth 1),
    skipping nested callbacks (timers, listeners).
    Returns [(method, mod_name, value), ...] where method is 'set' or 'add'.
    """
    ops = []
    mod_re = re.compile(r'mob:(set|add)Mod\(xi\.mod\.(\w+)\s*,\s*(-?\d+)\)')
    section_re = re.compile(r'entity\.onMob(?:Spawn|Initialize)\s*=\s*function')
    block_open_re = re.compile(r'\b(?:function|if|for|while)\b')
    block_close_re = re.compile(r'\bend\b')

    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
    except OSError:
        return ops

    in_section = False
    depth = 0

    for line in lines:
        stripped = line.strip()
        if stripped.startswith('--'):
            continue

        if not in_section:
            if section_re.search(stripped):
                in_section = True
                depth = 1
                continue
        else:
            opens = len(block_open_re.findall(stripped))
            closes = len(block_close_re.findall(stripped))
            depth += opens - closes

            if depth <= 0:
                in_section = False
                depth = 0
                continue

            if depth == 1:
                for m in mod_re.finditer(stripped):
                    mod_name = m.group(2)
                    if mod_name in MOD_NAME_TO_ID:
                        ops.append((m.group(1), mod_name, int(m.group(3))))

    return ops


def parse_asb_overrides(asb_root):
    """Parse AirSkyBoat mob Lua scripts for setMod/addMod overrides.

    Returns {(zone_name, pool_name): [(method, mod_name, value), ...]}
    """
    overrides = {}
    scripts_dir = os.path.join(asb_root, 'scripts', 'zones')

    if not os.path.isdir(scripts_dir):
        print(f'  WARNING: AirSkyBoat scripts dir not found: {scripts_dir}')
        return overrides

    for zone_dir in sorted(os.listdir(scripts_dir)):
        mobs_dir = os.path.join(scripts_dir, zone_dir, 'mobs')
        if not os.path.isdir(mobs_dir):
            continue
        for mob_file in os.listdir(mobs_dir):
            if not mob_file.endswith('.lua'):
                continue
            mob_name = mob_file[:-4]
            filepath = os.path.join(mobs_dir, mob_file)
            ops = extract_spawn_mods(filepath)
            if ops:
                overrides[(zone_dir, mob_name)] = ops

    return overrides


def compute_stats_with_overrides(mlvl, mjob, sjob, family, zone_id, hp_override,
                                  mp_override, skill_caps, skill_ranks,
                                  sql_mods, lua_ops):
    """Compute mob stats with AirSkyBoat Lua overrides applied.

    Replicates the C++ runtime behavior:
      1. restoreModifiers() -> m_modStat = SQL mods
      2. addModifier(ATT/DEF/ACC/EVA, computedBase)
      3. Lua setMod/addMod from onMobSpawn
      4. Final stats = computed + m_modStat
    """
    base = compute_stats(mlvl, mjob, sjob, family, zone_id, hp_override, mp_override,
                         skill_caps, skill_ranks)

    # Initialize m_modStat from SQL mods
    m_mod = {}
    for name, mid in MOD_NAME_TO_ID.items():
        m_mod[name] = sql_mods.get(mid, 0)

    # Add computed combat bases (replicates C++ addModifier calls in CalculateMobStats)
    m_mod['ATT'] += base['baseATT']
    m_mod['DEF'] += base['baseDEF']
    m_mod['ACC'] += base['baseACC']
    m_mod['EVA'] += base['baseEVA']

    # Replay Lua operations in order
    for method, mod_name, value in lua_ops:
        if mod_name not in m_mod:
            continue
        if method == 'set':
            m_mod[mod_name] = value
        else:
            m_mod[mod_name] += value

    # Build result with stat mods applied
    result = {}
    for stat in ('STR', 'DEX', 'VIT', 'AGI', 'INT', 'MND', 'CHR'):
        result[stat] = base[stat] + m_mod.get(stat, 0)

    result['HP'] = base['HP']
    result['MP'] = base['MP']
    result['baseATT'] = base['baseATT']
    result['baseACC'] = base['baseACC']
    result['baseDEF'] = base['baseDEF']
    result['baseEVA'] = base['baseEVA']

    # Total combat stats using m_modStat (replicates battleentity.cpp)
    result['totalAttack'] = max(1, 8 + m_mod['ATT'] + int(math.floor(result['STR'] * 0.5)))
    result['totalDefense'] = max(1, 8 + int(math.floor(result['VIT'] * 0.5)) + m_mod['DEF'])
    result['totalAccuracy'] = max(1, m_mod['ACC'] + int(math.floor(result['DEX'] / 2)))
    result['totalEvasion'] = max(1, m_mod['EVA'] + int(math.floor(result['AGI'] / 2)))

    # ATTP/DEFP percentage modifiers
    attp = m_mod.get('ATTP', 0)
    defp = m_mod.get('DEFP', 0)
    if attp:
        result['totalAttack'] += result['totalAttack'] * attp // 100
    if defp:
        result['totalDefense'] += result['totalDefense'] * defp // 100

    # AccTarget95
    level_penalty = max(mlvl - 75, 0) * 4
    result['accTarget95'] = result['totalEvasion'] + 40 + level_penalty

    return result


# ---------------------------------------------------------------------------
# SQL table parsers
# ---------------------------------------------------------------------------

def parse_zone_settings(path):
    """Parse zone_settings.sql -> {zoneid: zone_name}"""
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 5:
                continue
            # zoneid, misc, ip, port, name, ...
            zone_id = int(vals[0])
            zone_name = vals[4] if isinstance(vals[4], str) else str(vals[4])
            result[zone_id] = zone_name
    return result


def parse_mob_family_system(path):
    """Parse mob_family_system.sql -> {familyID: {family, HP_pct, MP_pct, stat ranks, ...}}"""
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 22:
                continue
            # familyID, family, superFamilyID, superFamily, ecosystemID, ecosystem,
            # speed, HP, MP, STR, DEX, VIT, AGI, INT, MND, CHR, ATT, DEF, ACC, EVA,
            # Element, detects, charmable
            fam_id = int(vals[0])
            result[fam_id] = {
                'family_id': fam_id,
                'family_name': vals[1] if isinstance(vals[1], str) else str(vals[1]),
                'HP_pct': int(vals[7]),
                'MP_pct': int(vals[8]),
                'STR': int(vals[9]),
                'DEX': int(vals[10]),
                'VIT': int(vals[11]),
                'AGI': int(vals[12]),
                'INT': int(vals[13]),
                'MND': int(vals[14]),
                'CHR': int(vals[15]),
                'ATT': int(vals[16]),
                'DEF': int(vals[17]),
                'ACC': int(vals[18]),
                'EVA': int(vals[19]),
            }
    return result


def parse_mob_pools(path):
    """Parse mob_pools.sql -> {poolid: {name, familyid, mJob, sJob, mobType}}"""
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 15:
                continue
            # poolid, name, packet_name, familyid, modelid, mJob, sJob, cmbSkill,
            # cmbDelay, cmbDmgMult, behavior, aggro, true_detection, links, mobType, ...
            pool_id = int(vals[0])
            result[pool_id] = {
                'name': vals[1] if isinstance(vals[1], str) else str(vals[1]),
                'familyid': int(vals[3]),
                'mJob': int(vals[5]),
                'sJob': int(vals[6]),
                'mobType': int(vals[14]),
            }
    return result


def parse_mob_groups(path):
    """Parse mob_groups.sql -> {(zoneid, groupid): {poolid, HP, MP}}"""
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 9:
                continue
            # groupid, poolid, zoneid, name, respawntime, spawntype, dropid, HP, MP, ...
            group_id = int(vals[0])
            zone_id = int(vals[2])
            result[(zone_id, group_id)] = {
                'poolid': int(vals[1]),
                'HP': int(vals[7]),
                'MP': int(vals[8]),
            }
    return result


def parse_mob_spawn_points(path):
    """Parse mob_spawn_points.sql -> list of {mobid, groupid, minLevel, maxLevel, zone_id}

    zone_id is derived from mobid: zone_id = (mobid >> 12) & 0xFFF
    """
    result = []
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 7:
                continue
            # mobid, spawnslotid, mobname, polutils_name, groupid, minLevel, maxLevel, ...
            mob_id = int(vals[0])
            zone_id = (mob_id >> 12) & 0xFFF
            result.append({
                'mobid': mob_id,
                'groupid': int(vals[4]),
                'polutils_name': vals[3] if isinstance(vals[3], str) else str(vals[3]),
                'minLevel': int(vals[5]),
                'maxLevel': int(vals[6]),
                'zone_id': zone_id,
            })
    return result


def parse_skill_caps(path):
    """Parse skill_caps.sql -> {level: {rank: cap_value}}

    Columns: level, r0, r1, r2, ..., r13
    """
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 15:
                continue
            level = int(vals[0])
            caps = {}
            for r in range(14):
                caps[r] = int(vals[1 + r])
            result[level] = caps
    return result


def parse_skill_ranks(path):
    """Parse skill_ranks.sql -> {skillid: {job_id: rank}}

    Columns: skillid, name, war(1), mnk(2), whm(3), blm(4), rdm(5), thf(6),
             pld(7), drk(8), bst(9), brd(10), rng(11), sam(12), nin(13),
             drg(14), smn(15), blu(16), cor(17), pup(18), dnc(19), sch(20),
             geo(21), run(22)
    """
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 24:
                continue
            skill_id = int(vals[0])
            ranks = {}
            for job in range(1, 23):
                ranks[job] = int(vals[2 + job - 1])  # vals[2] = war (job 1)
            result[skill_id] = ranks
    return result


def parse_mob_mods(path):
    """Parse mob_pool_mods.sql or mob_family_mods.sql -> {id: [(modid, value, is_mob_mod)]}"""
    result = {}
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if not line.strip().startswith('INSERT'):
                continue
            vals = parse_sql_insert(line)
            if vals is None or len(vals) < 4:
                continue
            # id (poolid or familyid), modid, value, is_mob_mod
            entity_id = int(vals[0])
            mod_id = int(vals[1])
            value = int(vals[2])
            is_mob_mod = int(vals[3])
            result.setdefault(entity_id, []).append((mod_id, value, is_mob_mod))
    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Export mob combat stats from SQL data to JSON.'
    )
    parser.add_argument(
        '--output', type=str, default=None,
        help='Output file path (default: tools/mob_stats.json)'
    )
    parser.add_argument(
        '--asb-path', type=str, default=None,
        help='Path to AirSkyBoat repo root for NM Lua overrides (outputs mob_stats_asb.json)'
    )
    args = parser.parse_args()

    repo_root = os.path.normpath(os.path.join(os.path.dirname(__file__), '..'))

    def repo_path(rel):
        return os.path.join(repo_root, rel)

    output_path = args.output or os.path.join(os.path.dirname(__file__), 'mob_stats.json')

    print('Parsing SQL files...')

    zones = parse_zone_settings(repo_path('sql/zone_settings.sql'))
    families = parse_mob_family_system(repo_path('sql/mob_family_system.sql'))
    pools = parse_mob_pools(repo_path('sql/mob_pools.sql'))
    groups = parse_mob_groups(repo_path('sql/mob_groups.sql'))
    spawns = parse_mob_spawn_points(repo_path('sql/mob_spawn_points.sql'))
    skill_caps = parse_skill_caps(repo_path('sql/skill_caps.sql'))
    skill_ranks_data = parse_skill_ranks(repo_path('sql/skill_ranks.sql'))
    pool_mods = parse_mob_mods(repo_path('sql/mob_pool_mods.sql'))
    family_mods = parse_mob_mods(repo_path('sql/mob_family_mods.sql'))

    print(f'  zones:        {len(zones)}')
    print(f'  families:     {len(families)}')
    print(f'  pools:        {len(pools)}')
    print(f'  groups:       {len(groups)}')
    print(f'  spawn_points: {len(spawns)}')
    print(f'  skill_caps:   {len(skill_caps)} levels')
    print(f'  skill_ranks:  {len(skill_ranks_data)} skills')
    print(f'  pool_mods:    {sum(len(v) for v in pool_mods.values())} entries')
    print(f'  family_mods:  {sum(len(v) for v in family_mods.values())} entries')

    print('Computing mob stats...')

    # Build output: zone_name -> mob_name -> level -> stats
    # Merge level ranges when multiple spawn points use the same pool in a zone
    zone_data = {}
    seen_ranges = set()  # (zone_id, pool_id, min_lvl, max_lvl) dedup
    nm_info = {}  # (zone_name, pool_name_raw) -> NM parameters for ASB pass

    mob_count = 0
    skipped = 0

    for spawn in spawns:
        zone_id = spawn['zone_id']
        group_id = spawn['groupid']
        min_lvl = spawn['minLevel']
        max_lvl = spawn['maxLevel']

        if min_lvl == 0 and max_lvl == 0:
            skipped += 1
            continue

        group = groups.get((zone_id, group_id))
        if group is None:
            skipped += 1
            continue

        pool_id = group['poolid']

        pool = pools.get(pool_id)
        if pool is None:
            skipped += 1
            continue

        family_id = pool['familyid']
        family = families.get(family_id)
        if family is None:
            skipped += 1
            continue

        zone_name = zones.get(zone_id, f'Zone_{zone_id}')
        mob_name = spawn['polutils_name']
        mjob = pool['mJob']
        sjob = pool['sJob']
        mob_type = pool['mobType']
        is_nm = bool(mob_type & MOBTYPE_NOTORIOUS)

        hp_override = group['HP']
        mp_override = group['MP']

        # Collect applicable mods (only non-mob-mods, i.e. stat mods)
        mods = {}
        for mod_id, value, is_mob in family_mods.get(family_id, []):
            if is_mob == 0:
                mods[mod_id] = mods.get(mod_id, 0) + value
        for mod_id, value, is_mob in pool_mods.get(pool_id, []):
            if is_mob == 0:
                mods[mod_id] = mods.get(mod_id, 0) + value

        # Store in zone structure, merging level ranges for same mob
        if zone_name not in zone_data:
            zone_data[zone_name] = {
                'zone_id': zone_id,
                'mobs': {},
            }

        # Disambiguate when different pools share the same client name in a zone
        existing = zone_data[zone_name]['mobs'].get(mob_name)
        if existing and existing['pool_id'] != pool_id:
            # Rename the first entry to include its job suffix too
            first_job = existing['main_job']
            renamed = f"{mob_name} ({first_job})"
            if renamed not in zone_data[zone_name]['mobs']:
                zone_data[zone_name]['mobs'][renamed] = zone_data[zone_name]['mobs'].pop(mob_name)
            # Suffix the current entry
            job_suffix = f" ({JOB_ABBREVS.get(mjob, f'JOB_{mjob}')})"
            mob_name = mob_name + job_suffix

        if mob_name not in zone_data[zone_name]['mobs']:
            zone_data[zone_name]['mobs'][mob_name] = {
                'pool_id': pool_id,
                'family': family['family_name'],
                'is_nm': is_nm,
                'main_job': JOB_ABBREVS.get(mjob, f'JOB_{mjob}'),
                'sub_job': JOB_ABBREVS.get(sjob, f'JOB_{sjob}'),
                'mobids': [],
                'levels': {},
            }
            if mods:
                zone_data[zone_name]['mobs'][mob_name]['mods'] = {
                    str(k): v for k, v in mods.items()
                }
            mob_count += 1

        # Always collect mobid
        mob_entry = zone_data[zone_name]['mobs'][mob_name]
        mob_id = spawn['mobid']
        if mob_id not in mob_entry['mobids']:
            mob_entry['mobids'].append(mob_id)

        # Collect NM info for ASB override pass
        if is_nm and args.asb_path:
            nm_key = (zone_name, pool['name'])
            if nm_key not in nm_info:
                nm_info[nm_key] = {
                    'mjob': mjob, 'sjob': sjob, 'family': family,
                    'zone_id': zone_id, 'hp_override': hp_override,
                    'mp_override': mp_override, 'sql_mods': dict(mods),
                    'pool_id': pool_id, 'family_name': family['family_name'],
                    'mob_name_display': mob_name,
                    'main_job': JOB_ABBREVS.get(mjob, f'JOB_{mjob}'),
                    'sub_job': JOB_ABBREVS.get(sjob, f'JOB_{sjob}'),
                    'mobids': [],
                    'levels': set(),
                }
            if mob_id not in nm_info[nm_key]['mobids']:
                nm_info[nm_key]['mobids'].append(mob_id)
            nm_info[nm_key]['levels'].update(range(max(min_lvl, 1), max_lvl + 1))

        # Skip stats computation for duplicate spawn ranges
        dedup_key = (zone_id, pool_id, min_lvl, max_lvl)
        if dedup_key in seen_ranges:
            continue
        seen_ranges.add(dedup_key)

        existing_levels = mob_entry['levels']

        # Compute stats for each level in this spawn's range
        for lvl in range(max(min_lvl, 1), max_lvl + 1):
            if str(lvl) in existing_levels:
                continue  # already computed from another spawn range

            stats = compute_stats(lvl, mjob, sjob, family, zone_id,
                                  hp_override, mp_override,
                                  skill_caps, skill_ranks_data)

            # Apply pool/family mods to totals
            att_mod = mods.get(MOD_ATT, 0)
            def_mod = mods.get(MOD_DEF, 0)
            acc_mod = mods.get(MOD_ACC, 0)
            eva_mod = mods.get(MOD_EVA, 0)

            if att_mod:
                stats['totalAttack'] = max(1, stats['totalAttack'] + att_mod)
            if def_mod:
                stats['totalDefense'] = max(1, stats['totalDefense'] + def_mod)
            if acc_mod:
                stats['totalAccuracy'] = max(1, stats['totalAccuracy'] + acc_mod)
            if eva_mod:
                stats['totalEvasion'] = max(1, stats['totalEvasion'] + eva_mod)

            existing_levels[str(lvl)] = stats

    # Sort zones alphabetically
    sorted_zones = dict(sorted(zone_data.items()))

    output = {
        'metadata': {
            'generated': datetime.now(timezone.utc).isoformat(),
            'note': 'Lua script overrides and runtime mob mods are not captured',
            'mob_count': mob_count,
            'zone_count': len(sorted_zones),
        },
        'zones': sorted_zones,
    }

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f'Wrote {mob_count} unique mobs across {len(sorted_zones)} zones to {output_path}')
    if skipped:
        print(f'  ({skipped} spawn points skipped due to missing data or level 0)')

    # ----- AirSkyBoat NM override pass -----
    if args.asb_path:
        print('\nParsing AirSkyBoat Lua overrides...')
        asb_overrides = parse_asb_overrides(args.asb_path)
        print(f'  Found overrides in {len(asb_overrides)} mob scripts')

        asb_zone_data = {}
        asb_mob_count = 0
        override_count = 0

        for (zone_name, pool_name_raw), info in sorted(nm_info.items()):
            lua_ops = asb_overrides.get((zone_name, pool_name_raw), [])

            mob_entry = {
                'pool_id': info['pool_id'],
                'family': info['family_name'],
                'is_nm': True,
                'main_job': info['main_job'],
                'sub_job': info['sub_job'],
                'mobids': info['mobids'],
                'has_overrides': bool(lua_ops),
                'levels': {},
            }
            if lua_ops:
                mob_entry['overrides'] = [
                    {'method': m, 'mod': n, 'value': v} for m, n, v in lua_ops
                ]
                override_count += 1

            for lvl in sorted(info['levels']):
                stats = compute_stats_with_overrides(
                    lvl, info['mjob'], info['sjob'], info['family'],
                    info['zone_id'], info['hp_override'], info['mp_override'],
                    skill_caps, skill_ranks_data, info['sql_mods'], lua_ops
                )
                mob_entry['levels'][str(lvl)] = stats

            if zone_name not in asb_zone_data:
                asb_zone_data[zone_name] = {'zone_id': info['zone_id'], 'mobs': {}}
            asb_zone_data[zone_name]['mobs'][info['mob_name_display']] = mob_entry
            asb_mob_count += 1

        sorted_asb_zones = dict(sorted(asb_zone_data.items()))

        asb_output = {
            'metadata': {
                'generated': datetime.now(timezone.utc).isoformat(),
                'note': 'NMs only, with AirSkyBoat Lua onMobSpawn/onMobInitialize overrides applied',
                'base_data': 'LandSandBoat SQL',
                'override_source': os.path.abspath(args.asb_path),
                'nm_count': asb_mob_count,
                'nms_with_overrides': override_count,
                'zone_count': len(sorted_asb_zones),
            },
            'zones': sorted_asb_zones,
        }

        asb_output_path = os.path.join(os.path.dirname(output_path), 'mob_stats_asb.json')
        with open(asb_output_path, 'w', encoding='utf-8') as f:
            json.dump(asb_output, f, indent=2, ensure_ascii=False)

        print(f'Wrote {asb_mob_count} NMs ({override_count} with overrides) '
              f'across {len(sorted_asb_zones)} zones to {asb_output_path}')


if __name__ == '__main__':
    main()
