import os
import re
import json
import ctypes
from ctypes import wintypes
import sqlite3
import webbrowser
import threading
from io import BytesIO
from pathlib import Path
from collections import defaultdict
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

import numpy as np
import requests
import pandas as pd
import customtkinter as ctk
from PIL import Image, ImageTk

try:
    from curl_cffi import requests as cffi_requests
except ImportError:
    cffi_requests = None

try:
    import cloudscraper
except ImportError:
    cloudscraper = None

ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

USERPROFILE = Path(os.environ.get("USERPROFILE", ""))
APPDATA_LOW_MTGA = USERPROFILE / "AppData" / "LocalLow" / "Wizards Of The Coast" / "MTGA"

SAVED_DECKS_FILE = Path("mtga_saved_decks.json")
CLEAN_COLLECTION_CACHE = Path("mtga_clean_collection_v3.json")
OLD_CACHES = [
    Path("mtga_collection_cache.json"),
    Path("mtga_verified_collection.json"),
]

BASIC_LANDS = {
    "plains", "island", "swamp", "mountain", "forest", "wastes",
    "snow-covered plains", "snow-covered island", "snow-covered swamp",
    "snow-covered mountain", "snow-covered forest"
}

MULTI_COPY_CARDS = {
    "rat colony", "relentless rats", "persistent petitioners", "shadowborn apostle",
    "dragon's approach", "slime against humanity", "hare apparent", "tempest hawk",
    "seven dwarves", "nazgul", "nazgûl"
}

COLOR_MAP = {"W": "White", "U": "Blue", "B": "Black", "R": "Red", "G": "Green"}
RARITY_MAP_DB = {0: "Token", 1: "Basic Land", 2: "Common", 3: "Uncommon", 4: "Rare", 5: "Mythic"}
COLOR_INT_MAP = {1: "W", 2: "U", "B": "B", 3: "B", 4: "R", 5: "G"}

SCRYFALL_HEADERS = {
    "User-Agent": "MTGABrawlCompanion/2026.10.2 (Windows; Python)",
    "Accept": "application/json",
}


def normalize_card_name(name: str) -> str:
    """Normalizes card names across split/DFC faces, Alchemy 'A-' prefixes, and punctuation."""
    if not name:
        return ""
    name = str(name).strip()
    name = re.sub(r"<[^>]+>", "", name)
    if name.startswith("A-"):
        name = name[2:]
    if "//" in name:
        name = name.split("//")[0].strip()
    name = name.replace("’", "'").replace("`", "'").replace("“", '"').replace("”", '"')
    name = name.replace("û", "u").replace("ú", "u").replace("é", "e").replace("á", "a")
    name = re.sub(r"\s+", " ", name)
    return name.lower()


def format_colors(color_list):
    if not color_list:
        return "Colorless"
    names = [COLOR_MAP.get(c, c) for c in color_list if c in COLOR_MAP]
    if not names:
        return "Colorless"
    if len(names) > 1:
        return f"Multicolored ({', '.join(names)})"
    return names[0]


# ==============================================================================
# 1. LOCAL MTG ARENA SQLITE DATABASE LOADER (OCTOBER 2026 SCHEMA)
# ==============================================================================
def find_local_card_db() -> Path | None:
    """Locates Raw_CardDatabase_*.mtga across standard install paths and Player.log hints."""
    candidate_subpaths = [
        r"Program Files\Wizards of the Coast\MTGA\MTGA_Data\Downloads\Raw",
        r"Program Files (x86)\Wizards of the Coast\MTGA\MTGA_Data\Downloads\Raw",
        r"Program Files (x86)\Steam\steamapps\common\MTGA\MTGA_Data\Downloads\Raw",
        r"Program Files\Steam\steamapps\common\MTGA\MTGA_Data\Downloads\Raw",
        r"SteamLibrary\steamapps\common\MTGA\MTGA_Data\Downloads\Raw",
        r"Games\MTGA\MTGA_Data\Downloads\Raw",
        r"MTGA\MTGA_Data\Downloads\Raw",
        r"Program Files\Epic Games\MagicTheGathering\MTGA_Data\Downloads\Raw",
    ]
    found_files = []

    player_log = APPDATA_LOW_MTGA / "Player.log"
    if player_log.exists():
        try:
            head = player_log.read_text(encoding="utf-8", errors="ignore")[:8000]
            m = re.search(r"([A-Za-z]:[\\/][^\r\n\"']+?MTGA_Data)", head)
            if m:
                raw_dir = Path(m.group(1)) / "Downloads" / "Raw"
                if raw_dir.exists():
                    found_files.extend(raw_dir.glob("Raw_CardDatabase_*.mtga"))
        except Exception:
            pass

    for drive in ["C:", "D:", "E:", "F:", "G:"]:
        for sub in candidate_subpaths:
            folder = Path(f"{drive}\\{sub}")
            if folder.exists():
                found_files.extend(folder.glob("Raw_CardDatabase_*.mtga"))

    if found_files:
        return max(found_files, key=os.path.getmtime)
    return None


def load_local_mtga_db(db_path: Path):
    """
    Loads Raw_CardDatabase_*.mtga:
      - all_db_grp_ids: Set of ALL GrpIds in the Cards table (including Basic Lands, Tokens, and A- rebalanced cards)
        so that valid entries inside the C# Dictionary<int, int> NEVER break a contiguous memory run.
      - collectible_by_id: GrpId -> metadata dict for collectible cards (IsToken == 0, IsPrimaryCard == 1, non-A-).
      - metadata_by_name: normalized_name -> primary card dict.
      - grp_ids_by_name: normalized_name -> list of collectible GrpIds.
      - commander_names: sorted list of Legendary Creature / Planeswalker names.
    """
    all_db_grp_ids = set()
    collectible_by_id = {}
    metadata_by_name = {}
    grp_ids_by_name = defaultdict(list)
    commander_names = set()

    conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    cursor = conn.cursor()

    try:
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table'")
        tables = [r[0] for r in cursor.fetchall()]

        loc_table = "Localizations_enUS" if "Localizations_enUS" in tables else next((t for t in tables if "Localizations" in t), None)
        if not loc_table:
            return set(), {}, {}, {}, []

        cursor.execute(f"PRAGMA table_info({loc_table})")
        loc_cols = [c[1] for c in cursor.fetchall()]
        id_col = "LocId" if "LocId" in loc_cols else loc_cols[0]
        text_col = "enUS" if "enUS" in loc_cols else ("Loc" if "Loc" in loc_cols else loc_cols[1])

        cursor.execute(f"SELECT {id_col}, {text_col} FROM {loc_table}")
        loc_map = {row[0]: row[1] for row in cursor.fetchall() if row[1]}

        cursor.execute("PRAGMA table_info(Cards)")
        cols = [c[1] for c in cursor.fetchall()]

        select_cols = ["GrpId", "TitleId"]
        for opt in [
            "ExpansionCode", "Rarity", "Colors", "ColorIdentity",
            "TypeTextId", "OldSchoolManaText", "IsToken", "IsPrimaryCard",
            "LinkedFaceType", "IsRebalanced"
        ]:
            if opt in cols:
                select_cols.append(opt)

        cursor.execute(f"SELECT {', '.join(select_cols)} FROM Cards")
        for row in cursor.fetchall():
            row_dict = dict(zip(select_cols, row))
            grp_id = int(row_dict["GrpId"])
            all_db_grp_ids.add(grp_id)

            if row_dict.get("IsToken") == 1:
                continue
            if "IsPrimaryCard" in row_dict and row_dict.get("IsPrimaryCard") == 0:
                continue
            # LinkedFaceType: 1 = Adventure spell face, 3 = MDFC back face, 6 = Specialize back face, etc.
            linked_type = row_dict.get("LinkedFaceType", 0)
            if linked_type in (1, 3, 5, 6, 7, 9):
                continue

            raw_name = loc_map.get(row_dict.get("TitleId"), "")
            if not raw_name:
                continue

            clean_name = re.sub(r"<[^>]+>", "", str(raw_name)).strip()
            if not clean_name:
                continue

            # Skip "A-" Alchemy rebalanced rows for ownership counting because MTGA grants "A-" virtual rows
            # or links them to the base card; counting A- separately or without base causes mismatches.
            if clean_name.startswith("A-") or row_dict.get("IsRebalanced") == 1:
                continue

            exp_code = str(row_dict.get("ExpansionCode") or "").upper()

            type_line = re.sub(r"<[^>]+>", "", str(loc_map.get(row_dict.get("TypeTextId"), ""))).strip()
            if "Legendary" in type_line and ("Creature" in type_line or "Planeswalker" in type_line or "Background" in type_line):
                commander_names.add(clean_name)

            raw_colors = str(row_dict.get("Colors") or "")
            color_codes = [
                COLOR_INT_MAP.get(int(c), c)
                for c in re.findall(r'\d+|\w', raw_colors)
                if c.isdigit() and int(c) in COLOR_INT_MAP
            ]
            if not color_codes and any(c in raw_colors for c in "WUBRG"):
                color_codes = [c for c in "WUBRG" if c in raw_colors]

            raw_ci = str(row_dict.get("ColorIdentity") or "")
            ci_codes = [
                COLOR_INT_MAP.get(int(c), c)
                for c in re.findall(r'\d+|\w', raw_ci)
                if c.isdigit() and int(c) in COLOR_INT_MAP
            ]

            rarity_str = RARITY_MAP_DB.get(row_dict.get("Rarity"), "Common")
            card_info = {
                "Arena ID": grp_id,
                "Name": clean_name,
                "Color": format_colors(color_codes),
                "Color Identity": ", ".join(ci_codes) if ci_codes else "Colorless",
                "Mana Cost": row_dict.get("OldSchoolManaText") or "",
                "Type Line": type_line,
                "Set Code": exp_code,
                "Rarity": rarity_str,
            }
            collectible_by_id[grp_id] = card_info
            norm = normalize_card_name(clean_name)
            if norm:
                grp_ids_by_name[norm].append(grp_id)
                if norm not in metadata_by_name or (metadata_by_name[norm]["Rarity"] == "Common" and rarity_str != "Common"):
                    metadata_by_name[norm] = card_info
    except Exception as e:
        print(f"SQLite load warning: {e}")
    finally:
        conn.close()

    return all_db_grp_ids, collectible_by_id, metadata_by_name, dict(grp_ids_by_name), sorted(commander_names)


# ==============================================================================
# 2. WILDCARD LOG PARSER & STRICT CONTIGUOUS MEMORY SCANNER
# ==============================================================================
class MEMORY_BASIC_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("BaseAddress", ctypes.c_void_p),
        ("AllocationBase", ctypes.c_void_p),
        ("AllocationProtect", wintypes.DWORD),
        ("PartitionId", wintypes.WORD),
        ("RegionSize", ctypes.c_size_t),
        ("State", wintypes.DWORD),
        ("Protect", wintypes.DWORD),
        ("Type", wintypes.DWORD),
    ]


def find_mtga_pid() -> int | None:
    if os.name != "nt":
        return None
    TH32CS_SNAPPROCESS = 0x00000002

    class PROCESSENTRY32(ctypes.Structure):
        _fields_ = [
            ("dwSize", wintypes.DWORD),
            ("cntUsage", wintypes.DWORD),
            ("th32ProcessID", wintypes.DWORD),
            ("th32DefaultHeapID", ctypes.c_void_p),
            ("th32ModuleID", wintypes.DWORD),
            ("cntThreads", wintypes.DWORD),
            ("th32ParentProcessID", wintypes.DWORD),
            ("pcPriClassBase", wintypes.LONG),
            ("dwFlags", wintypes.DWORD),
            ("szExeFile", ctypes.c_char * 260),
        ]

    kernel32 = ctypes.windll.kernel32
    snap = kernel32.CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
    if snap == -1:
        return None

    pe = PROCESSENTRY32()
    pe.dwSize = ctypes.sizeof(PROCESSENTRY32)
    pid = None
    if kernel32.Process32First(snap, ctypes.byref(pe)):
        while True:
            exe_name = pe.szExeFile.decode("utf-8", errors="ignore").lower()
            if exe_name == "mtga.exe":
                pid = int(pe.th32ProcessID)
                break
            if not kernel32.Process32Next(snap, ctypes.byref(pe)):
                break
    kernel32.CloseHandle(snap)
    return pid


def parse_logs_for_wildcards_only() -> dict:
    """
    Extracts ONLY Wildcard and Vault balances from the MTGA logs (never deck cards).

    Accuracy fixes vs. the old version:
      * Logs are ranked purely by modified time (newest first) and the LAST wildcard snapshot in the
        NEWEST log that has one wins. Previously older logs could be read after newer ones and
        overwrite fresh values with stale ones.
      * The old regex required an `InventoryInfo` object with NO nested braces, so most real snapshots
        (which contain Boosters/CustomTokens objects) were skipped and an old, simple one was used.
        Now we anchor on the wildcard keys themselves and read the sibling keys next to them.
      * `...Delta` keys (wcCommonDelta etc.) can never be mistaken for balances.
    """
    inventory = {
        "wc_common": 0,
        "wc_uncommon": 0,
        "wc_rare": 0,
        "wc_mythic": 0,
        "vault": 0.0,
        "found_wc": False
    }

    candidate_logs = []
    utc_log_dir = APPDATA_LOW_MTGA / "Logs" / "Logs"
    if utc_log_dir.exists():
        candidate_logs.extend(utc_log_dir.glob("UTC_Log*.log"))
    for lp in [APPDATA_LOW_MTGA / "Player-prev.log", APPDATA_LOW_MTGA / "Player.log"]:
        if lp.exists():
            candidate_logs.append(lp)

    def _mtime(p: Path) -> float:
        try:
            return os.path.getmtime(p)
        except OSError:
            return 0.0

    # Newest first; keep the 6 most recent files
    candidate_logs = sorted(set(candidate_logs), key=_mtime, reverse=True)[:6]

    q = r'\\?"'
    anchor_rgx = re.compile(q + r'(?:WcCommon|wcCommon|WildCardCommons)' + q + r'\s*:\s*(\d+)')
    wc_u_rgx = re.compile(q + r'(?:WcUncommon|wcUncommon|WildCardUnCommons)' + q + r'\s*:\s*(\d+)')
    wc_r_rgx = re.compile(q + r'(?:WcRare|wcRare|WildCardRares)' + q + r'\s*:\s*(\d+)')
    wc_m_rgx = re.compile(q + r'(?:WcMythic|wcMythic|WildCardMythics)' + q + r'\s*:\s*(\d+)')
    vault_rgx = re.compile(q + r'(?:TotalVaultProgress|VaultProgress|vaultProgress|totalVaultProgress)' + q + r'\s*:\s*(\d+(?:\.\d+)?)')

    def nearest(rgx, window: str, pos: int):
        best = None
        for m in rgx.finditer(window):
            dist = abs(m.start() - pos)
            if best is None or dist < best[0]:
                best = (dist, m)
        return best[1] if best else None

    for log_file in candidate_logs:
        try:
            content = log_file.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue

        last_snapshot = None
        for m in anchor_rgx.finditer(content):
            lo = max(0, m.start() - 300)
            window = content[lo: m.start() + 1500]
            pos = m.start() - lo
            u_m = nearest(wc_u_rgx, window, pos)
            r_m = nearest(wc_r_rgx, window, pos)
            m_m = nearest(wc_m_rgx, window, pos)
            if not (u_m and r_m and m_m):
                continue
            v_m = nearest(vault_rgx, window, pos)
            last_snapshot = (
                int(m.group(1)), int(u_m.group(1)), int(r_m.group(1)), int(m_m.group(1)),
                float(v_m.group(1)) if v_m else None
            )

        if last_snapshot:
            c_val, u_val, r_val, m_val, raw_v = last_snapshot
            inventory["wc_common"] = c_val
            inventory["wc_uncommon"] = u_val
            inventory["wc_rare"] = r_val
            inventory["wc_mythic"] = m_val
            inventory["found_wc"] = True
            if raw_v is not None:
                inventory["vault"] = round(raw_v / 10.0, 1) if raw_v >= 100 else round(raw_v, 1)
            inventory["source"] = log_file.name
            break  # newest log with a snapshot wins

    return inventory


def scan_mtga_memory_strict(
    all_db_grp_ids: set[int],
    collectible_by_id: dict[int, dict],
    user_anchors: dict[str, int],
    grp_ids_by_name: dict[str, list[int]],
    status_callback=None
) -> dict[int, int]:
    """
    Scans MTGA.exe RAM for the exact C# Dictionary<int, int>.Entry[] array holding the player's card collection.
    Fixes both false negatives and false positives:
      1. Allows `1 <= value <= 5000` and checks against `all_db_grp_ids` (including Basic Lands and A- cards)
         during contiguous run detection so Basic Lands with >4 copies NEVER split the array and cut off newer cards
         like Hydroponics Architect (GrpId 1086846).
      2. Requires `diffs == 1` (ZERO gaps allowed between entries 0..count-1) so the scanner NEVER bridges across
         a 32-byte MonoArray header into an adjacent deck or store bundle dictionary in memory.
      3. Verifies that every `next` pointer in the run satisfies `-1 <= next < run_length` and that there are
         0% duplicate GrpId keys inside the contiguous array.
    """
    if os.name != "nt" or not all_db_grp_ids:
        return {}

    pid = find_mtga_pid()
    if not pid:
        return {}

    PROCESS_QUERY_INFORMATION = 0x0400
    PROCESS_VM_READ = 0x0010
    MEM_COMMIT = 0x1000
    PAGE_READWRITE = 0x04

    kernel32 = ctypes.windll.kernel32
    h_proc = kernel32.OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, False, pid)
    if not h_proc:
        return {}

    min_gid = min(all_db_grp_ids)
    max_gid = max(all_db_grp_ids)

    candidates = []
    mbi = MEMORY_BASIC_INFORMATION()
    address = 0
    max_address = 0x7FFFFFFFFFFF

    try:
        while address < max_address:
            res = kernel32.VirtualQueryEx(h_proc, ctypes.c_void_p(address), ctypes.byref(mbi), ctypes.sizeof(mbi))
            if not res:
                break

            base_addr = mbi.BaseAddress or 0
            region_size = mbi.RegionSize or 0
            next_addr = base_addr + region_size

            if mbi.State == MEM_COMMIT and (mbi.Protect & PAGE_READWRITE) and 16384 <= region_size <= 67108864:
                buf = ctypes.create_string_buffer(region_size)
                bytes_read = ctypes.c_size_t(0)
                if kernel32.ReadProcessMemory(h_proc, ctypes.c_void_p(base_addr), buf, region_size, ctypes.byref(bytes_read)):
                    actual_bytes = bytes_read.value - (bytes_read.value % 4)
                    if actual_bytes >= 1024:
                        words = np.frombuffer(buf.raw[:actual_bytes], dtype=np.int32)
                        for align in range(4):
                            rem = (len(words) - align) // 4
                            if rem < 50:
                                continue
                            entries = words[align: align + rem * 4].reshape(-1, 4)
                            h = entries[:, 0]
                            nxt = entries[:, 1]
                            k = entries[:, 2]
                            v = entries[:, 3]

                            # Note: v can be > 4 for Basic Lands and Rat Colony! Allowing up to 5000 prevents Basic Lands
                            # from breaking the contiguous Entry[] run in memory.
                            valid_mask = (
                                (h == k) &
                                (k >= min_gid) & (k <= max_gid) &
                                (v >= 1) & (v <= 5000) &
                                (nxt >= -1) & (nxt < 100000)
                            )
                            valid_idx = np.nonzero(valid_mask)[0]
                            if len(valid_idx) < 50:
                                continue

                            # STRICT CONTIGUITY: diffs > 1 splits immediately!
                            # Never jump across empty slots or 32-byte MonoArray headers!
                            diffs = np.diff(valid_idx)
                            split_points = np.nonzero(diffs > 1)[0] + 1
                            runs = np.split(valid_idx, split_points)

                            for run in runs:
                                run_len = len(run)
                                if run_len < 50:
                                    continue

                                run_keys = k[run].tolist()
                                run_vals = v[run].tolist()
                                run_nxts = nxt[run].tolist()

                                # In a genuine .NET Dictionary<int, int> without removals, every `next` index
                                # is either -1 or points to an earlier/valid index < run_len.
                                invalid_nxt = sum(1 for n_idx in run_nxts if n_idx >= run_len)
                                if invalid_nxt > 0:
                                    continue

                                # Check that keys are valid MTGA GrpIds and has ZERO duplicate keys
                                seen_keys = set()
                                duplicates = 0
                                db_hits = 0
                                collectible_map = {}

                                for gid, qty in zip(run_keys, run_vals):
                                    if gid in seen_keys:
                                        duplicates += 1
                                    seen_keys.add(gid)
                                    if gid in all_db_grp_ids:
                                        db_hits += 1
                                    if gid in collectible_by_id:
                                        collectible_map[gid] = qty

                                # A single Dictionary<int, int> Entry[] array CANNOT have duplicate keys
                                if duplicates > 0:
                                    continue

                                # At least 98% of keys in the contiguous run must be known GrpIds in Raw_CardDatabase
                                if (db_hits / run_len) < 0.98:
                                    continue

                                unique_collectible = len(collectible_map)
                                if unique_collectible < 40:
                                    continue

                                # Reject static game metadata tables where >90% of cards have the exact same value
                                val_counts = defaultdict(int)
                                for qty in collectible_map.values():
                                    val_counts[min(qty, 5)] += 1
                                if (max(val_counts.values()) / unique_collectible) > 0.90 and unique_collectible > 200:
                                    continue

                                # Verify MonoArray capacity header right before run[0] if available
                                start_entry_idx = int(run[0])
                                start_word_idx = align + start_entry_idx * 4
                                header_bonus = 0
                                if start_word_idx >= 2:
                                    # In 64-bit MonoArray, max_length (int32) sits 2 int32 words before entries[0]
                                    arr_cap = int(words[start_word_idx - 2])
                                    arr_cap_hi = int(words[start_word_idx - 1])
                                    if run_len <= arr_cap <= (run_len * 4 + 64) and arr_cap_hi == 0:
                                        header_bonus = 5000

                                # Score against any user-verified anchor cards (both owned > 0 and known unowned == 0)
                                anchor_score = 0
                                for norm_name, expected_qty in user_anchors.items():
                                    possible_gids = grp_ids_by_name.get(norm_name, [])
                                    owned_in_candidate = sum(collectible_map.get(g, 0) for g in possible_gids)
                                    if expected_qty == 0:
                                        if owned_in_candidate == 0:
                                            anchor_score += 500
                                        else:
                                            anchor_score -= 2000  # Immediately penalize tables containing known unowned cards
                                    else:
                                        if owned_in_candidate >= expected_qty:
                                            anchor_score += 500
                                        else:
                                            anchor_score -= 1000

                                total_score = header_bonus + anchor_score + unique_collectible
                                candidates.append((total_score, unique_collectible, run_len, collectible_map))

            address = next_addr
    except Exception as e:
        print(f"Memory scan error: {e}")
    finally:
        kernel32.CloseHandle(h_proc)

    if not candidates:
        return {}

    candidates.sort(key=lambda x: x[0], reverse=True)
    best_score, best_collectible, best_run_len, best_map = candidates[0]
    if status_callback:
        status_callback(
            f"Verified contiguous Dictionary<int,int> in MTGA.exe: {best_collectible:,} collectible printings ({best_run_len:,} total entries)."
        )
    return best_map


# ==============================================================================
# 3. RESILIENT MOXFIELD + SCRYFALL CLIENT
# ==============================================================================
class MoxfieldClient:
    def __init__(self):
        self.headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36",
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": "en-US,en;q=0.9",
            "Referer": "https://moxfield.com/",
            "Origin": "https://moxfield.com",
        }
        if cffi_requests is not None:
            self.session = cffi_requests.Session(impersonate="chrome")
        elif cloudscraper is not None:
            self.session = cloudscraper.create_scraper(browser={"browser": "chrome", "platform": "windows", "mobile": False})
        else:
            self.session = requests.Session()

    def _get_json(self, url: str, params: dict = None) -> dict:
        resp = self.session.get(url, params=params, headers=self.headers, timeout=15)
        resp.raise_for_status()
        return resp.json()

    def get_commander_card(self, query: str) -> tuple[str | None, str | None]:
        canonical_name = query.strip()
        try:
            sf_resp = requests.get(
                "https://api.scryfall.com/cards/named",
                params={"fuzzy": canonical_name},
                headers=SCRYFALL_HEADERS,
                timeout=8
            )
            if sf_resp.status_code == 200:
                canonical_name = sf_resp.json().get("name", canonical_name)
        except Exception:
            pass

        search_q = canonical_name.split("//")[0].strip() if "//" in canonical_name else canonical_name

        for q_attempt in [canonical_name, search_q, query.strip()]:
            try:
                data = self._get_json(
                    "https://api2.moxfield.com/v2/cards/search",
                    params={"q": q_attempt, "page": 1, "pageSize": 25}
                ).get("data", [])
                if data:
                    target_norm = normalize_card_name(canonical_name)
                    for card in data:
                        if normalize_card_name(card.get("name", "")) == target_norm:
                            return card.get("id"), card.get("name")
                    return data[0].get("id"), data[0].get("name")
            except Exception:
                continue

        return None, None

    @staticmethod
    def _looks_like_60_card(summary: dict) -> bool:
        """Cheap pre-filter on the search summary so 60-card Standard Brawl decks never cost a full fetch."""
        fmt_val = str(summary.get("format") or "").lower()
        if "standardbrawl" in fmt_val or "standard brawl" in fmt_val:
            return True
        mb = summary.get("mainboardCount")
        if isinstance(mb, int) and 0 < mb < 90:
            return True
        return False

    def search_brawl_decks(self, commander_id: str, mode: str = "Casual Brawl", max_decks: int = 40, max_pages: int = 5) -> list[dict]:
        sort_types = ["views", "likes"] if mode == "Competitive Brawl" else ["updated"]
        endpoints = [
            "https://api2.moxfield.com/v2/decks/search-sfw",
            "https://api2.moxfield.com/v2/decks/search",
        ]
        page_size = 50
        results = []
        seen_ids = set()

        for fmt in ["historicBrawl", "brawl"]:
            for sort_type in sort_types:
                for page in range(1, max_pages + 1):
                    if len(results) >= max_decks:
                        break
                    deck_list = []
                    for ep in endpoints:
                        params = {
                            "pageNumber": page,
                            "pageSize": page_size,
                            "sortType": sort_type,
                            "sortDirection": "Descending",
                            "fmt": fmt,
                            "commanderCardId": commander_id,
                        }
                        try:
                            deck_list = self._get_json(ep, params=params).get("data", [])
                            if deck_list:
                                break
                        except Exception:
                            continue
                    if not deck_list:
                        break
                    for d in deck_list:
                        pid = d.get("publicId")
                        if not pid or pid in seen_ids:
                            continue
                        seen_ids.add(pid)
                        if self._looks_like_60_card(d):
                            continue
                        results.append(d)
                    if len(deck_list) < page_size:
                        break

        return results[:max_decks]

    def get_full_deck(self, public_id: str) -> dict:
        for ver in ("v3", "v2"):
            url = f"https://api2.moxfield.com/{ver}/decks/all/{public_id}"
            try:
                return self._get_json(url)
            except Exception:
                continue
        raise RuntimeError(f"Failed to fetch deck {public_id}")


# ==============================================================================
# 4. MAIN OVERLAY & COLLECTION BROWSER APPLICATION
# ==============================================================================
class BrawlOverlayApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("MTGA Brawl Companion & Collection Browser (October 2026)")
        self.geometry("1300x790+40+40")
        self.attributes("-topmost", True)
        self.attributes("-alpha", 0.96)

        # Automatically delete any polluted caches from previous versions
        for old_c in OLD_CACHES:
            if old_c.exists():
                try:
                    old_c.unlink()
                except Exception:
                    pass

        self.moxfield = MoxfieldClient()
        self.all_db_grp_ids: set[int] = set()
        self.raw_collection: dict[int, int] = {}
        self.local_metadata_by_id: dict[int, dict] = {}
        self.local_metadata_by_name: dict[str, dict] = {}
        self.grp_ids_by_name: dict[str, list[int]] = {}
        self.owned_by_name: dict[str, int] = defaultdict(int)
        self.user_anchors: dict[str, int] = {}
        self.commander_list: list[str] = []
        self.inventory = {
            "wc_common": 0, "wc_uncommon": 0, "wc_rare": 0, "wc_mythic": 0,
            "vault": 0.0, "found_wc": False
        }

        self.all_fetched_decks = []
        self.displayed_decks = []
        self.saved_decks = self._load_saved_decks()
        self.current_selected_deck = None
        self.collection_table_rows = []
        self.image_cache = {}
        self._active_photo_ref = None
        self.visible = True
        self.is_mini_mode = False
        self.saved_geometry = "1300x790+40+40"

        self._setup_treeview_styles()
        self._build_ui()
        self._register_global_hotkey()

        threading.Thread(target=self._full_collection_sync, daemon=True).start()

    def _setup_treeview_styles(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure(
            "Treeview",
            background="#1e1e24",
            foreground="#f4f4f5",
            fieldbackground="#1e1e24",
            rowheight=28,
            borderwidth=0,
            font=("Segoe UI", 9)
        )
        style.configure(
            "Treeview.Heading",
            background="#272730",
            foreground="#e4e4e7",
            font=("Segoe UI", 9, "bold"),
            borderwidth=0
        )
        style.map("Treeview", background=[("selected", "#3b82f6")], foreground=[("selected", "#ffffff")])

    def _build_ui(self):
        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

        # ==================== 1. TOP UTILITY & WALLET BAR ====================
        self.top_bar = ctk.CTkFrame(self, corner_radius=0, fg_color="#141418", height=48)
        self.top_bar.grid(row=0, column=0, sticky="ew")

        self.wallet_label = ctk.CTkLabel(
            self.top_bar,
            text="Scanning MTGA database & collection...",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#fbbf24",
            cursor="hand2"
        )
        self.wallet_label.pack(side="left", padx=12, pady=8)
        self.wallet_label.bind("<Button-1>", lambda _: self.edit_wildcard_wallet_dialog())

        self.sync_btn = ctk.CTkButton(
            self.top_bar, text="⚡ Sync Live MTGA", width=130, height=30,
            fg_color="#4f46e5", hover_color="#4338ca", font=ctk.CTkFont(size=12, weight="bold"),
            command=lambda: threading.Thread(target=self._full_collection_sync, daemon=True).start()
        )
        self.sync_btn.pack(side="left", padx=3)

        self.test_paste_btn = ctk.CTkButton(
            self.top_bar, text="📋 Test Clipboard Deck", width=145, height=30,
            fg_color="#0284c7", hover_color="#0369a1", font=ctk.CTkFont(size=12, weight="bold"),
            command=self.audit_clipboard_deck
        )
        self.test_paste_btn.pack(side="left", padx=3)

        self.calibrate_btn = ctk.CTkButton(
            self.top_bar, text="🎯 Calibrate Missing", width=130, height=30,
            fg_color="#27272a", hover_color="#3f3f46",
            command=self.calibrate_from_arena_missing_list
        )
        self.calibrate_btn.pack(side="left", padx=3)

        self.import_btn = ctk.CTkButton(
            self.top_bar, text="📂 Import File", width=100, height=30,
            fg_color="#27272a", hover_color="#3f3f46",
            command=self.import_external_collection
        )
        self.import_btn.pack(side="left", padx=3)

        self.export_btn = ctk.CTkButton(
            self.top_bar, text="💾 Export CSV / XLSX", width=135, height=30,
            fg_color="#059669", hover_color="#047857", font=ctk.CTkFont(size=12, weight="bold"),
            command=self.prompt_and_export_spreadsheets
        )
        self.export_btn.pack(side="left", padx=3)

        # Right-side window controls
        self.mini_btn = ctk.CTkButton(
            self.top_bar, text="🗕 Mini Mode", width=90, height=28,
            fg_color="#3b82f6", hover_color="#2563eb", command=self.toggle_mini_mode
        )
        self.mini_btn.pack(side="right", padx=10, pady=8)

        self.topmost_var = ctk.BooleanVar(value=True)
        self.topmost_switch = ctk.CTkSwitch(
            self.top_bar, text="Pin", variable=self.topmost_var,
            command=lambda: self.attributes("-topmost", self.topmost_var.get()),
            font=ctk.CTkFont(size=11), width=36
        )
        self.topmost_switch.pack(side="right", padx=6)

        self.opacity_slider = ctk.CTkSlider(
            self.top_bar, from_=0.35, to=1.0, number_of_steps=65, width=75,
            command=lambda val: self.attributes("-alpha", float(val))
        )
        self.opacity_slider.set(0.96)
        self.opacity_slider.pack(side="right", padx=4)

        # ==================== 2. MAIN WORKSPACE + SHARED PREVIEW ====================
        self.main_container = ctk.CTkFrame(self, fg_color="transparent")
        self.main_container.grid(row=1, column=0, sticky="nsew", padx=12, pady=(4, 4))
        self.main_container.grid_rowconfigure(0, weight=1)
        self.main_container.grid_columnconfigure(0, weight=1)

        self.mode_tabs = ctk.CTkTabview(
            self.main_container, fg_color="#18181f",
            segmented_button_selected_color="#4f46e5",
            segmented_button_unselected_color="#272730"
        )
        self.mode_tabs.grid(row=0, column=0, sticky="nsew", padx=(0, 8))

        self.tab_brawl = self.mode_tabs.add("⚔️ Brawl Deck Finder (Moxfield)")
        self.tab_collection = self.mode_tabs.add("🗂 My Collection (Browser)")

        self._build_brawl_finder_tab(self.tab_brawl)
        self._build_collection_browser_tab(self.tab_collection)

        # Shared Right-Hand Live Card Art Preview Panel
        self.preview_panel = ctk.CTkFrame(self.main_container, width=248, fg_color="#141418", corner_radius=8)
        self.preview_panel.grid(row=0, column=1, sticky="ns", pady=(12, 0))
        self.preview_panel.grid_propagate(False)

        ctk.CTkLabel(
            self.preview_panel, text="Card Preview",
            font=ctk.CTkFont(size=13, weight="bold"), text_color="#e4e4e7"
        ).pack(pady=(10, 4))

        self.card_img_label = tk.Label(
            self.preview_panel,
            text="Click any card in a deck\nor in My Collection\nto preview art",
            bg="#141418",
            fg="#71717a",
            font=("Segoe UI", 10),
            justify="center",
            wraplength=210
        )
        self.card_img_label.pack(fill="both", expand=True, padx=8, pady=6)

        self.card_detail_lbl = ctk.CTkLabel(
            self.preview_panel, text="", font=ctk.CTkFont(size=11),
            text_color="#a1a1aa", wraplength=225, justify="center"
        )
        self.card_detail_lbl.pack(padx=8, pady=(0, 12))

        # ==================== 3. STATUS & PROGRESS BAR ====================
        self.bottom_bar = ctk.CTkFrame(self, corner_radius=0, fg_color="#141418", height=32)
        self.bottom_bar.grid(row=2, column=0, sticky="ew")

        self.status_var = ctk.StringVar(value="Starting up...")
        ctk.CTkLabel(self.bottom_bar, textvariable=self.status_var, font=ctk.CTkFont(size=11), text_color="#a1a1aa").pack(side="left", padx=12, pady=4)

        self.progress_bar = ctk.CTkProgressBar(self.bottom_bar, width=180, height=10)
        self.progress_bar.set(0)
        self.progress_bar.pack(side="right", padx=14, pady=10)

        ctk.CTkLabel(self.bottom_bar, text="Hotkey: Alt + B  |  Double-Click Any Card to Edit Owned Qty", font=ctk.CTkFont(size=11, slant="italic"), text_color="#71717a").pack(side="right", padx=8)

        self._refresh_saved_decks_tree()

    def _build_brawl_finder_tab(self, parent):
        parent.grid_rowconfigure(1, weight=1)
        parent.grid_columnconfigure(0, weight=5)
        parent.grid_columnconfigure(1, weight=6)

        search_bar = ctk.CTkFrame(parent, corner_radius=8, fg_color="#1f1f27")
        search_bar.grid(row=0, column=0, columnspan=2, sticky="ew", padx=4, pady=(2, 8))

        row_a = ctk.CTkFrame(search_bar, fg_color="transparent")
        row_a.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(row_a, text="Commander:", font=ctk.CTkFont(size=13, weight="bold")).pack(side="left", padx=(0, 6))
        self.cmd_var = ctk.StringVar()
        self.cmd_entry = ctk.CTkEntry(
            row_a, textvariable=self.cmd_var, width=260,
            placeholder_text="Type a commander name..."
        )
        self.cmd_entry.pack(side="left", padx=(0, 12))
        self._build_commander_popup()

        ctk.CTkLabel(row_a, text="Format:", font=ctk.CTkFont(size=12, weight="bold")).pack(side="left", padx=(0, 6))
        self.format_var = ctk.StringVar(value="Casual Brawl")
        ctk.CTkOptionMenu(
            row_a, variable=self.format_var,
            values=["Casual Brawl", "Competitive Brawl"],
            width=155
        ).pack(side="left", padx=(0, 12))

        ctk.CTkLabel(row_a, text="Max Missing Cards:", font=ctk.CTkFont(size=12, weight="bold")).pack(side="left", padx=(0, 6))
        self.max_wc_entry = ctk.CTkEntry(row_a, width=50, justify="center")
        self.max_wc_entry.insert(0, "5")
        self.max_wc_entry.pack(side="left", padx=(0, 6))
        self.max_wc_entry.bind("<Return>", lambda _: self._apply_missing_filter_live())

        ctk.CTkButton(
            row_a, text="Filter", width=60, height=28,
            fg_color="#27272a", hover_color="#3f3f46",
            command=self._apply_missing_filter_live
        ).pack(side="left", padx=(0, 12))

        ctk.CTkLabel(row_a, text="Scan:", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 4))
        self.scan_limit_var = ctk.StringVar(value="40")
        ctk.CTkOptionMenu(row_a, variable=self.scan_limit_var, values=["25", "40", "60", "100"], width=70).pack(side="left", padx=(0, 8))

        self.search_btn = ctk.CTkButton(
            row_a, text="🔍 Search Brawl Decks", font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#4f46e5", hover_color="#4338ca", width=165, command=self.start_search
        )
        self.search_btn.pack(side="right", padx=4)

        self.left_tabs = ctk.CTkTabview(parent, fg_color="#141418", segmented_button_selected_color="#3b82f6")
        self.left_tabs.grid(row=1, column=0, sticky="nsew", padx=(4, 6), pady=2)
        tab_search = self.left_tabs.add("Moxfield Results")
        tab_saved = self.left_tabs.add("★ Saved Decks")

        cols = ("name", "author", "cards", "complete", "missing", "breakdown", "views")
        self.deck_tree = ttk.Treeview(tab_search, columns=cols, show="headings", selectmode="browse")
        self.deck_tree.heading("name", text="Deck Name", command=lambda: self._sort_treeview(self.deck_tree, "name", False))
        self.deck_tree.heading("author", text="Author", command=lambda: self._sort_treeview(self.deck_tree, "author", False))
        self.deck_tree.heading("cards", text="Cards", command=lambda: self._sort_treeview(self.deck_tree, "cards", True))
        self.deck_tree.heading("complete", text="Owned %", command=lambda: self._sort_treeview(self.deck_tree, "complete", True))
        self.deck_tree.heading("missing", text="Missing", command=lambda: self._sort_treeview(self.deck_tree, "missing", False))
        self.deck_tree.heading("breakdown", text="M / R / U / C")
        self.deck_tree.heading("views", text="Views", command=lambda: self._sort_treeview(self.deck_tree, "views", True))

        self.deck_tree.column("name", width=150, anchor=tk.W)
        self.deck_tree.column("author", width=70, anchor=tk.W)
        self.deck_tree.column("cards", width=48, anchor=tk.CENTER)
        self.deck_tree.column("complete", width=62, anchor=tk.CENTER)
        self.deck_tree.column("missing", width=58, anchor=tk.CENTER)
        self.deck_tree.column("breakdown", width=90, anchor=tk.CENTER)
        self.deck_tree.column("views", width=50, anchor=tk.CENTER)

        self.deck_tree.tag_configure("zero_wc", foreground="#4ade80")
        self.deck_tree.tag_configure("low_wc", foreground="#facc15")

        d_scroll = ttk.Scrollbar(tab_search, orient=tk.VERTICAL, command=self.deck_tree.yview)
        self.deck_tree.configure(yscrollcommand=d_scroll.set)
        self.deck_tree.pack(side="left", fill="both", expand=True)
        d_scroll.pack(side="right", fill="y")
        self.deck_tree.bind("<<TreeviewSelect>>", lambda e: self.on_deck_select(self.deck_tree, self.displayed_decks))

        self.saved_tree = ttk.Treeview(tab_saved, columns=cols, show="headings", selectmode="browse")
        for c, label, w in [("name", "Deck Name", 150), ("author", "Author", 70), ("cards", "Cards", 48), ("complete", "Owned %", 62),
                            ("missing", "Missing", 58), ("breakdown", "M / R / U / C", 90), ("views", "Views", 50)]:
            self.saved_tree.heading(c, text=label)
            self.saved_tree.column(c, width=w, anchor=tk.W if c in ("name", "author") else tk.CENTER)

        s_scroll = ttk.Scrollbar(tab_saved, orient=tk.VERTICAL, command=self.saved_tree.yview)
        self.saved_tree.configure(yscrollcommand=s_scroll.set)
        self.saved_tree.pack(side="left", fill="both", expand=True)
        s_scroll.pack(side="right", fill="y")
        self.saved_tree.bind("<<TreeviewSelect>>", lambda e: self.on_deck_select(self.saved_tree, self.saved_decks))

        right_pane = ctk.CTkFrame(parent, fg_color="#141418", corner_radius=8)
        right_pane.grid(row=1, column=1, sticky="nsew", padx=(6, 4), pady=2)
        right_pane.grid_rowconfigure(3, weight=1)
        right_pane.grid_columnconfigure(0, weight=1)

        action_bar = ctk.CTkFrame(right_pane, fg_color="transparent")
        action_bar.grid(row=0, column=0, sticky="ew", padx=8, pady=(8, 4))

        self.copy_btn = ctk.CTkButton(
            action_bar, text="📋 Copy Deck for MTG Arena", state="disabled",
            fg_color="#10b981", hover_color="#059669", font=ctk.CTkFont(size=12, weight="bold"),
            command=self.copy_selected_deck
        )
        self.copy_btn.pack(side="left", fill="x", expand=True, padx=(0, 4))

        self.copy_missing_btn = ctk.CTkButton(
            action_bar, text="Copy Missing", state="disabled", width=105,
            fg_color="#3f3f46", hover_color="#52525b", command=self.copy_missing_only
        )
        self.copy_missing_btn.pack(side="left", padx=(0, 4))

        self.bookmark_btn = ctk.CTkButton(
            action_bar, text="★ Save", state="disabled", width=70,
            fg_color="#f59e0b", hover_color="#d97706", command=self.toggle_bookmark_deck
        )
        self.bookmark_btn.pack(side="left", padx=(0, 4))

        self.open_web_btn = ctk.CTkButton(
            action_bar, text="🌐 Web", state="disabled", width=70,
            fg_color="#3b82f6", hover_color="#2563eb", command=self.open_in_moxfield
        )
        self.open_web_btn.pack(side="left")

        self.deck_summary_lbl = ctk.CTkLabel(
            right_pane, text="Select a deck on the left (or click '📋 Test Clipboard Deck') to inspect owned vs. missing cards.",
            font=ctk.CTkFont(size=11), text_color="#a1a1aa", anchor="w", justify="left"
        )
        self.deck_summary_lbl.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 4))

        card_filter_bar = ctk.CTkFrame(right_pane, fg_color="transparent")
        card_filter_bar.grid(row=2, column=0, sticky="ew", padx=8, pady=(0, 4))

        self.card_view_filter = ctk.CTkSegmentedButton(
            card_filter_bar, values=["All Cards", "Uncrafted / Missing", "Owned Only"],
            command=self._refresh_card_inspector_table
        )
        self.card_view_filter.set("All Cards")
        self.card_view_filter.pack(side="left")

        self.curve_lbl = ctk.CTkLabel(card_filter_bar, text="", font=ctk.CTkFont(family="Consolas", size=11), text_color="#93c5fd")
        self.curve_lbl.pack(side="right", padx=4)

        c_frame = ctk.CTkFrame(right_pane, fg_color="#1e1e24")
        c_frame.grid(row=3, column=0, sticky="nsew", padx=8, pady=(0, 8))

        c_cols = ("status", "owned", "name", "type", "rarity", "cmc")
        self.card_tree = ttk.Treeview(c_frame, columns=c_cols, show="headings", selectmode="browse")
        self.card_tree.heading("status", text="Status")
        self.card_tree.heading("owned", text="Own/Need")
        self.card_tree.heading("name", text="Card Name")
        self.card_tree.heading("type", text="Type")
        self.card_tree.heading("rarity", text="Rarity")
        self.card_tree.heading("cmc", text="MV")

        self.card_tree.column("status", width=95, anchor=tk.CENTER)
        self.card_tree.column("owned", width=65, anchor=tk.CENTER)
        self.card_tree.column("name", width=180, anchor=tk.W)
        self.card_tree.column("type", width=110, anchor=tk.W)
        self.card_tree.column("rarity", width=68, anchor=tk.CENTER)
        self.card_tree.column("cmc", width=36, anchor=tk.CENTER)

        self.card_tree.tag_configure("missing", foreground="#f87171")
        self.card_tree.tag_configure("not_in_arena", foreground="#fb923c")
        self.card_tree.tag_configure("owned", foreground="#4ade80")
        self.card_tree.tag_configure("commander", foreground="#c084fc")

        c_scroll = ttk.Scrollbar(c_frame, orient=tk.VERTICAL, command=self.card_tree.yview)
        self.card_tree.configure(yscrollcommand=c_scroll.set)
        self.card_tree.pack(side="left", fill="both", expand=True)
        c_scroll.pack(side="right", fill="y")
        self.card_tree.bind("<<TreeviewSelect>>", self.on_deck_card_row_select)
        self.card_tree.bind("<Double-1>", self.on_deck_card_double_click)

    def _build_collection_browser_tab(self, parent):
        parent.grid_rowconfigure(1, weight=1)
        parent.grid_columnconfigure(0, weight=1)

        filter_bar = ctk.CTkFrame(parent, corner_radius=8, fg_color="#1f1f27")
        filter_bar.grid(row=0, column=0, sticky="ew", padx=4, pady=(2, 8))

        f_row = ctk.CTkFrame(filter_bar, fg_color="transparent")
        f_row.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(f_row, text="Search Card:", font=ctk.CTkFont(size=12, weight="bold")).pack(side="left", padx=(0, 6))
        self.col_search_var = ctk.StringVar()
        col_search_entry = ctk.CTkEntry(f_row, textvariable=self.col_search_var, width=210, placeholder_text="Card name, set, or type...")
        col_search_entry.pack(side="left", padx=(0, 12))
        col_search_entry.bind("<KeyRelease>", lambda _: self.refresh_collection_browser())

        ctk.CTkLabel(f_row, text="Show:", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 4))
        self.col_owner_filter = ctk.StringVar(value="Owned Only (>0)")
        ctk.CTkOptionMenu(
            f_row, variable=self.col_owner_filter,
            values=["Owned Only (>0)", "All Arena Cards", "Unowned Only (0)"],
            width=145, command=lambda _: self.refresh_collection_browser()
        ).pack(side="left", padx=(0, 12))

        ctk.CTkLabel(f_row, text="Color:", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 4))
        self.col_color_filter = ctk.StringVar(value="All Colors")
        ctk.CTkOptionMenu(
            f_row, variable=self.col_color_filter,
            values=["All Colors", "White", "Blue", "Black", "Red", "Green", "Multicolored", "Colorless"],
            width=130, command=lambda _: self.refresh_collection_browser()
        ).pack(side="left", padx=(0, 12))

        ctk.CTkLabel(f_row, text="Rarity:", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 4))
        self.col_rarity_filter = ctk.StringVar(value="All Rarities")
        ctk.CTkOptionMenu(
            f_row, variable=self.col_rarity_filter,
            values=["All Rarities", "Mythic", "Rare", "Uncommon", "Common"],
            width=120, command=lambda _: self.refresh_collection_browser()
        ).pack(side="left", padx=(0, 12))

        self.col_stats_lbl = ctk.CTkLabel(f_row, text="0 Cards", font=ctk.CTkFont(size=12, weight="bold"), text_color="#4ade80")
        self.col_stats_lbl.pack(side="right", padx=8)

        table_frame = ctk.CTkFrame(parent, fg_color="#1e1e24", corner_radius=8)
        table_frame.grid(row=1, column=0, sticky="nsew", padx=4, pady=2)

        col_columns = ("name", "qty", "color", "rarity", "set", "type", "mana", "id")
        self.collection_tree = ttk.Treeview(table_frame, columns=col_columns, show="headings", selectmode="browse")

        headings = [
            ("name", "Card Name", 240, tk.W, False),
            ("qty", "Owned Qty", 80, tk.CENTER, True),
            ("color", "Color", 145, tk.W, False),
            ("rarity", "Rarity", 85, tk.CENTER, False),
            ("set", "Set", 65, tk.CENTER, False),
            ("type", "Type Line", 210, tk.W, False),
            ("mana", "Mana Cost", 95, tk.W, False),
            ("id", "Arena ID", 75, tk.CENTER, True),
        ]
        for col_id, text, width, anchor, is_num in headings:
            self.collection_tree.heading(col_id, text=text, command=lambda c=col_id, n=is_num: self._sort_treeview(self.collection_tree, c, n))
            self.collection_tree.column(col_id, width=width, anchor=anchor)

        self.collection_tree.tag_configure("owned_row", foreground="#4ade80")
        self.collection_tree.tag_configure("unowned_row", foreground="#71717a")

        col_scroll = ttk.Scrollbar(table_frame, orient=tk.VERTICAL, command=self.collection_tree.yview)
        self.collection_tree.configure(yscrollcommand=col_scroll.set)
        self.collection_tree.pack(side="left", fill="both", expand=True)
        col_scroll.pack(side="right", fill="y")

        self.collection_tree.bind("<<TreeviewSelect>>", self.on_collection_row_select)
        self.collection_tree.bind("<Double-1>", self.on_collection_row_double_click)

        hint_lbl = ctk.CTkLabel(
            parent,
            text="Tip: Click any card to preview its art on the right. Double-click any card row to manually edit its Owned Quantity (0–4).",
            font=ctk.CTkFont(size=11, slant="italic"), text_color="#a1a1aa"
        )
        hint_lbl.grid(row=2, column=0, sticky="w", padx=8, pady=(4, 2))

    # ==================== COLLECTION SYNC & CALIBRATION ====================
    def _full_collection_sync(self):
        self.after(0, lambda: self.sync_btn.configure(state="disabled"))
        try:
            self.status_var.set("Step 1/3: Loading MTG Arena Raw_CardDatabase_*.mtga SQLite catalog...")
            self.progress_bar.set(0.15)

            if not self.local_metadata_by_id:
                local_db_path = find_local_card_db()
                if local_db_path:
                    all_ids, meta_id, meta_name, gids_by_name, cmd_list = load_local_mtga_db(local_db_path)
                    self.all_db_grp_ids = all_ids
                    self.local_metadata_by_id = meta_id
                    self.local_metadata_by_name = meta_name
                    self.grp_ids_by_name = gids_by_name
                    self.commander_list = cmd_list
                else:
                    self.status_var.set("Warning: Could not auto-locate Raw_CardDatabase_*.mtga.")

            self.status_var.set("Step 2/3: Reading Wildcard & Vault balances from Player.log...")
            self.progress_bar.set(0.45)
            inv = parse_logs_for_wildcards_only()
            if inv.get("found_wc"):
                self.inventory = inv

            # Load saved clean cache if present
            cached_by_id = {}
            cached_by_name = {}
            if CLEAN_COLLECTION_CACHE.exists():
                try:
                    cached = json.loads(CLEAN_COLLECTION_CACHE.read_text(encoding="utf-8"))
                    cached_by_id = {int(k): int(v) for k, v in cached.get("cards_by_id", {}).items() if int(v) > 0}
                    cached_by_name = {str(k): int(v) for k, v in cached.get("cards_by_name", {}).items() if int(v) >= 0}
                    self.user_anchors.update(cached.get("user_anchors", {}))
                    if not self.inventory.get("found_wc") and "inventory" in cached:
                        self.inventory = cached["inventory"]
                except Exception:
                    pass

            self.status_var.set("Step 3/3: Scanning MTGA.exe memory for strict contiguous Dictionary<int,int>...")
            self.progress_bar.set(0.75)
            mem_cards = scan_mtga_memory_strict(
                self.all_db_grp_ids,
                self.local_metadata_by_id,
                self.user_anchors,
                self.grp_ids_by_name,
                status_callback=self.status_var.set
            )

            if mem_cards:
                self.raw_collection = mem_cards
                owned_by_name = defaultdict(int)
                for grp_id, qty in mem_cards.items():
                    info = self.local_metadata_by_id.get(grp_id)
                    if info:
                        norm = normalize_card_name(info["Name"])
                        if norm:
                            max_cap = 99 if norm in MULTI_COPY_CARDS or norm in BASIC_LANDS else 4
                            owned_by_name[norm] = min(max_cap, owned_by_name[norm] + qty)
                # Apply any explicit user overrides/calibrations
                for norm_name, qty in self.user_anchors.items():
                    owned_by_name[norm_name] = qty
                self.owned_by_name = owned_by_name
                self._save_clean_cache()
            else:
                self.raw_collection = cached_by_id
                owned_by_name = defaultdict(int, cached_by_name)
                for norm_name, qty in self.user_anchors.items():
                    owned_by_name[norm_name] = qty
                self.owned_by_name = owned_by_name

            self.progress_bar.set(1.0)
            self._update_top_wallet_banner(found_live_ram=bool(mem_cards))
            self.after(0, self.refresh_collection_browser)
            if self.all_fetched_decks or self.current_selected_deck:
                self.after(0, self._recalculate_loaded_decks)
        finally:
            self.after(0, lambda: self.sync_btn.configure(state="normal"))

    def _save_clean_cache(self):
        try:
            payload = {
                "cards_by_id": {str(k): v for k, v in self.raw_collection.items()},
                "cards_by_name": {k: v for k, v in self.owned_by_name.items() if v > 0},
                "user_anchors": self.user_anchors,
                "inventory": self.inventory,
            }
            CLEAN_COLLECTION_CACHE.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        except Exception:
            pass

    def audit_clipboard_deck(self):
        """
        Reads any MTG Arena decklist directly from your clipboard (like your Teval list),
        evaluates every card against your collection, and displays the exact breakdown in the Deck Inspector.
        """
        try:
            clip_text = self.clipboard_get()
        except Exception:
            messagebox.showwarning("Clipboard Empty", "Copy a decklist to your clipboard first, then click '📋 Test Clipboard Deck'.")
            return

        if not clip_text or not clip_text.strip():
            messagebox.showwarning("Clipboard Empty", "Copy a decklist to your clipboard first.")
            return

        cmd_cards = {}
        main_cards = {}
        current_section = "main"

        for raw_line in clip_text.splitlines():
            line = raw_line.strip()
            if not line:
                continue
            low = line.lower()
            if low in ("commander", "commanders"):
                current_section = "cmd"
                continue
            if low in ("deck", "mainboard", "main"):
                current_section = "main"
                continue
            if low in ("sideboard", "companion"):
                current_section = "side"
                continue
            if current_section == "side":
                continue

            # Match standard Arena line: "1 Uro, Titan of Nature's Wrath (THB) 229" or "1 Uro, Titan of Nature's Wrath"
            m = re.match(r"^(\d+)x?\s+([^\(\n\r]+)", line)
            if m:
                qty = int(m.group(1))
                c_name = m.group(2).strip()
                norm = normalize_card_name(c_name)
                local_info = self.local_metadata_by_name.get(norm, {})
                entry_obj = {
                    "quantity": qty,
                    "card": {
                        "name": local_info.get("Name", c_name),
                        "type_line": local_info.get("Type Line", ""),
                        "rarity": (local_info.get("Rarity") or "rare").lower(),
                        "cmc": 0,
                        "scryfall_id": ""
                    }
                }
                if current_section == "cmd" or (not cmd_cards and len(main_cards) == 0 and "commander" not in clip_text.lower()):
                    cmd_cards[c_name] = entry_obj
                    current_section = "main"
                else:
                    if c_name in main_cards:
                        main_cards[c_name]["quantity"] += qty
                    else:
                        main_cards[c_name] = entry_obj

        if not cmd_cards and not main_cards:
            messagebox.showwarning("Invalid Decklist", "Could not find valid MTG Arena card lines (e.g. '1 Arcane Signet') in clipboard.")
            return

        synthetic_deck = {
            "boards": {
                "commanders": {"cards": cmd_cards},
                "mainboard": {"cards": main_cards},
            }
        }
        analysis = self._analyze_deck(synthetic_deck)
        cmd_title = next(iter(cmd_cards.keys()), "Clipboard Deck")
        record = {
            "name": f"[Clipboard] {cmd_title}",
            "author": "You",
            "public_id": "",
            "views": 0,
            "likes": 0,
            "commander": cmd_title,
            "raw_deck": synthetic_deck,
            **analysis
        }

        self.mode_tabs.set("⚔️ Brawl Deck Finder (Moxfield)")
        self.left_tabs.set("Moxfield Results")
        self._insert_deck_row(record)
        last_iid = str(len(self.displayed_decks) - 1)
        self.deck_tree.selection_set(last_iid)
        self.deck_tree.see(last_iid)
        self.on_deck_select(self.deck_tree, self.displayed_decks)
        self.status_var.set(f"Audited clipboard deck '{cmd_title}': {analysis['total_missing']} uncrafted card(s) detected.")

    def calibrate_from_arena_missing_list(self):
        """
        Lets the user paste the list of missing cards from MTG Arena (or for the currently selected deck)
        to lock in 100% exact ownership and re-score the memory scanner.
        """
        win = ctk.CTkToplevel(self)
        win.title("Calibrate Missing / Owned Cards with MTG Arena")
        win.geometry("540x420+200+180")
        win.attributes("-topmost", True)

        ctk.CTkLabel(
            win,
            text="Paste the cards MTG Arena says you are MISSING for the current deck\n"
                 "(one card per line, e.g. '1 Bloom Tender' or 'Uro, Titan of Nature's Wrath').\n"
                 "If a deck is currently selected, all OTHER cards in that deck will also be marked Owned!",
            font=ctk.CTkFont(size=12), justify="left"
        ).pack(padx=14, pady=(12, 8), anchor="w")

        txt = ctk.CTkTextbox(win, width=500, height=240, font=ctk.CTkFont(family="Consolas", size=12))
        txt.pack(padx=14, pady=6)

        def apply_calibration():
            raw_lines = txt.get("1.0", "end").splitlines()
            missing_norms = set()

            for line in raw_lines:
                line = line.strip()
                if not line:
                    continue
                m = re.match(r"^(?:(\d+)x?\s+)?([^\(\n\r]+)", line)
                if m:
                    c_name = m.group(2).strip()
                    norm = self._fuzzy_resolve_arena_norm(c_name)
                    if norm:
                        missing_norms.add(norm)
                        self.user_anchors[norm] = 0
                        self.owned_by_name[norm] = 0

            # If a deck is currently selected, mark its non-missing cards as Owned (1x)
            marked_owned = 0
            if self.current_selected_deck:
                for r in self.current_selected_deck.get("card_rows", []):
                    r_norm = r.get("norm_name")
                    if r_norm and r_norm not in BASIC_LANDS and r_norm not in missing_norms:
                        if self.owned_by_name.get(r_norm, 0) < r.get("qty", 1):
                            self.owned_by_name[r_norm] = r.get("qty", 1)
                            self.user_anchors[r_norm] = r.get("qty", 1)
                            marked_owned += 1

            self._save_clean_cache()
            self._update_top_wallet_banner()
            self.refresh_collection_browser()
            self._recalculate_loaded_decks()
            win.destroy()
            messagebox.showinfo(
                "Calibration Applied",
                f"Calibrated {len(missing_norms)} unowned card(s) and {marked_owned} owned deck card(s).\n"
                "Future live MTGA memory scans will also use these anchors!"
            )

        btn_row = ctk.CTkFrame(win, fg_color="transparent")
        btn_row.pack(fill="x", padx=14, pady=10)
        ctk.CTkButton(
            btn_row, text="✓ Apply Calibration & Re-Analyze Decks",
            fg_color="#10b981", hover_color="#059669", font=ctk.CTkFont(size=12, weight="bold"),
            command=apply_calibration
        ).pack(side="right")

    def _fuzzy_resolve_arena_norm(self, raw_query: str) -> str:
        """Resolves even slightly misspelled card names (e.g. 'Bloomtender', 'Barrogoyf') to the exact Arena card name."""
        norm = normalize_card_name(raw_query)
        if norm in self.local_metadata_by_name:
            return norm

        # Strip spaces/hyphens match (e.g., "bloomtender" -> "bloom tender")
        compact_q = re.sub(r"[^a-z0-9]", "", norm)
        for cand_norm in self.local_metadata_by_name:
            if re.sub(r"[^a-z0-9]", "", cand_norm) == compact_q:
                return cand_norm

        # Prefix match (e.g., "uro, titan of nature" -> "uro, titan of nature's wrath")
        for cand_norm in self.local_metadata_by_name:
            if cand_norm.startswith(norm) or norm.startswith(cand_norm):
                return cand_norm

        # Substring / Levenshtein-like character overlap within currently selected deck first
        if self.current_selected_deck:
            best_deck_norm = None
            best_ratio = 0.0
            for r in self.current_selected_deck.get("card_rows", []):
                cand = r.get("norm_name", "")
                if not cand:
                    continue
                # Simple bigram Dice coefficient
                b1 = {norm[i:i+2] for i in range(len(norm) - 1)}
                b2 = {cand[i:i+2] for i in range(len(cand) - 1)}
                if b1 and b2:
                    score = (2.0 * len(b1 & b2)) / (len(b1) + len(b2))
                    if score > best_ratio:
                        best_ratio = score
                        best_deck_norm = cand
            if best_deck_norm and best_ratio >= 0.65:
                return best_deck_norm

        return norm

    def edit_wildcard_wallet_dialog(self):
        inv = self.inventory
        current_str = f"{inv['wc_mythic']}M, {inv['wc_rare']}R, {inv['wc_uncommon']}U, {inv['wc_common']}C"
        raw = simpledialog.askstring(
            "Verify / Edit Wildcard Counts",
            f"Current detected Wildcards: {current_str}\n\n"
            "Enter Mythic, Rare, Uncommon, Common counts separated by spaces or commas\n"
            "(e.g.  4 12 25 40):",
            parent=self
        )
        if not raw:
            return
        nums = [int(x) for x in re.findall(r"\d+", raw)]
        if len(nums) >= 4:
            self.inventory["wc_mythic"] = nums[0]
            self.inventory["wc_rare"] = nums[1]
            self.inventory["wc_uncommon"] = nums[2]
            self.inventory["wc_common"] = nums[3]
            self.inventory["found_wc"] = True
            self._save_clean_cache()
            self._update_top_wallet_banner()

    def _update_top_wallet_banner(self, found_live_ram: bool = False):
        inv = self.inventory
        unique_owned = sum(1 for k, v in self.owned_by_name.items() if v > 0 and k not in BASIC_LANDS)
        total_copies = sum(v for k, v in self.owned_by_name.items() if v > 0 and k not in BASIC_LANDS)

        wallet_str = (
            f"Wildcards:  {inv['wc_mythic']} M  |  {inv['wc_rare']} R  |  "
            f"{inv['wc_uncommon']} U  |  {inv['wc_common']} C   "
            f"(Vault: {inv['vault']}%)   •   Owned: {unique_owned:,} Cards ({total_copies:,} Copies)"
        )
        self.after(0, lambda: self.wallet_label.configure(text=wallet_str))

        if found_live_ram:
            self.status_var.set(
                f"Strict Contiguous RAM Scan Complete: {unique_owned:,} unique non-land cards ({total_copies:,} copies) verified."
            )
        elif unique_owned > 0:
            self.status_var.set(
                f"Loaded {unique_owned:,} unique owned cards. Keep MTG Arena running & click '⚡ Sync Live MTGA' to refresh from RAM."
            )
        else:
            self.status_var.set(
                "0 owned cards loaded. Launch MTG Arena and click '⚡ Sync Live MTGA', or click '📂 Import File'."
            )

    # ==================== COLLECTION BROWSER TAB LOGIC ====================
    def refresh_collection_browser(self):
        if not hasattr(self, "collection_tree"):
            return

        self.collection_tree.delete(*self.collection_tree.get_children())
        self.collection_table_rows.clear()

        search_q = self.col_search_var.get().strip().lower()
        owner_mode = self.col_owner_filter.get()
        color_mode = self.col_color_filter.get()
        rarity_mode = self.col_rarity_filter.get()

        rows_to_insert = []
        total_unique_owned = 0
        total_copies_owned = 0

        for norm_name, info in self.local_metadata_by_name.items():
            if norm_name in BASIC_LANDS:
                continue

            qty = self.owned_by_name.get(norm_name, 0)
            if qty > 0:
                total_unique_owned += 1
                total_copies_owned += qty

            if owner_mode == "Owned Only (>0)" and qty <= 0:
                continue
            if owner_mode == "Unowned Only (0)" and qty > 0:
                continue

            card_color = info.get("Color", "Colorless")
            if color_mode != "All Colors":
                if color_mode == "Multicolored" and not card_color.startswith("Multicolored"):
                    continue
                elif color_mode != "Multicolored" and card_color != color_mode:
                    continue

            card_rarity = info.get("Rarity", "Common")
            if rarity_mode != "All Rarities" and card_rarity != rarity_mode:
                continue

            card_name = info.get("Name", "")
            card_type = info.get("Type Line", "")
            card_set = info.get("Set Code", "")
            if search_q and (search_q not in card_name.lower() and search_q not in card_type.lower() and search_q not in card_set.lower()):
                continue

            rows_to_insert.append({
                "norm_name": norm_name,
                "name": card_name,
                "qty": qty,
                "color": card_color,
                "rarity": card_rarity,
                "set": card_set,
                "type": card_type,
                "mana": info.get("Mana Cost", ""),
                "id": info.get("Arena ID", ""),
            })

        rows_to_insert.sort(key=lambda r: (-r["qty"], r["name"]))
        self.collection_table_rows = rows_to_insert

        for idx, r in enumerate(rows_to_insert[:2500]):
            tag = "owned_row" if r["qty"] > 0 else "unowned_row"
            self.collection_tree.insert(
                "", tk.END, iid=str(idx),
                values=(r["name"], r["qty"], r["color"], r["rarity"], r["set"], r["type"], r["mana"], r["id"]),
                tags=(tag,)
            )

        shown_cnt = len(rows_to_insert)
        self.col_stats_lbl.configure(
            text=f"Showing {shown_cnt:,}  |  Total Owned: {total_unique_owned:,} Cards ({total_copies_owned:,} Copies)"
        )

    def on_collection_row_select(self, _event):
        selected = self.collection_tree.selection()
        if not selected:
            return
        idx = int(selected[0])
        if idx >= len(self.collection_table_rows):
            return
        row = self.collection_table_rows[idx]
        self.card_detail_lbl.configure(
            text=f"{row['name']}\nOwned: {row['qty']}x  •  {row['rarity']} ({row['set']})"
        )
        self.card_img_label.configure(image="", text=f"Loading\n{row['name']}...")
        threading.Thread(target=self._fetch_card_image, args=(row["name"], ""), daemon=True).start()

    def on_collection_row_double_click(self, _event):
        selected = self.collection_tree.selection()
        if not selected:
            return
        idx = int(selected[0])
        if idx >= len(self.collection_table_rows):
            return
        row = self.collection_table_rows[idx]
        new_qty = simpledialog.askinteger(
            "Edit Owned Quantity",
            f"Set owned quantity (0–4) for:\n{row['name']}",
            initialvalue=row["qty"],
            minvalue=0,
            maxvalue=4,
            parent=self
        )
        if new_qty is None:
            return

        norm = row["norm_name"]
        self.owned_by_name[norm] = new_qty
        self.user_anchors[norm] = new_qty
        row["qty"] = new_qty

        tag = "owned_row" if new_qty > 0 else "unowned_row"
        self.collection_tree.item(
            str(idx),
            values=(row["name"], new_qty, row["color"], row["rarity"], row["set"], row["type"], row["mana"], row["id"]),
            tags=(tag,)
        )
        self._save_clean_cache()
        self._update_top_wallet_banner()
        if self.all_fetched_decks or self.current_selected_deck:
            self._recalculate_loaded_decks()

    # ==================== IMPORT & EXPORT SPREADSHEETS ====================
    def import_external_collection(self):
        file_paths = filedialog.askopenfilenames(
            title="Select Collection CSV, JSON, or MTGA Decklist (.txt) Files",
            filetypes=[
                ("Supported Files", "*.csv *.txt *.json *.log"),
                ("CSV Spreadsheets", "*.csv"),
                ("MTGA Decklists / Text", "*.txt"),
                ("JSON / Log Files", "*.json *.log"),
            ]
        )
        if not file_paths:
            return

        added = 0
        for fp in file_paths:
            path = Path(fp)
            ext = path.suffix.lower()
            try:
                if ext == ".csv":
                    df = pd.read_csv(path)
                    name_col = next((c for c in df.columns if "name" in c.lower()), None)
                    qty_col = next((c for c in df.columns if c.lower() in ("quantity", "qty", "count", "owned", "owned quantity")), None)
                    if name_col:
                        for _, row in df.iterrows():
                            norm = normalize_card_name(str(row[name_col]))
                            qty = int(row[qty_col]) if qty_col and pd.notna(row[qty_col]) else 1
                            if norm and qty > 0:
                                self.owned_by_name[norm] = max(self.owned_by_name[norm], min(4, qty))
                                info = self.local_metadata_by_name.get(norm)
                                if info:
                                    self.raw_collection[info["Arena ID"]] = max(self.raw_collection.get(info["Arena ID"], 0), min(4, qty))
                                added += 1
                else:
                    text = path.read_text(encoding="utf-8", errors="ignore")
                    for line in text.splitlines():
                        line = line.strip()
                        m = re.match(r"^(\d+)\s+([^\(\n\r]+)", line)
                        if m:
                            qty = int(m.group(1))
                            c_name = m.group(2).strip()
                            norm = normalize_card_name(c_name)
                            if norm and qty > 0:
                                self.owned_by_name[norm] = max(self.owned_by_name[norm], min(4, qty))
                                info = self.local_metadata_by_name.get(norm)
                                if info:
                                    self.raw_collection[info["Arena ID"]] = max(self.raw_collection.get(info["Arena ID"], 0), min(4, qty))
                                added += 1
            except Exception as e:
                messagebox.showerror("Import Error", f"Failed to parse {path.name}:\n{e}")

        self._save_clean_cache()
        self._update_top_wallet_banner()
        self.refresh_collection_browser()
        if self.all_fetched_decks or self.current_selected_deck:
            self._recalculate_loaded_decks()
        messagebox.showinfo("Import Complete", f"Imported {added:,} card entries!")

    def prompt_and_export_spreadsheets(self):
        save_path = filedialog.asksaveasfilename(
            parent=self,
            title="Export MTG Arena Collection to Spreadsheet",
            defaultextension=".xlsx",
            initialfile="mtga_collection.xlsx",
            filetypes=[
                ("Excel Workbook (*.xlsx)", "*.xlsx"),
                ("CSV Spreadsheet (*.csv)", "*.csv"),
            ]
        )
        if not save_path:
            return

        owned_count = sum(1 for v in self.owned_by_name.values() if v > 0)
        export_all_if_empty = False
        if owned_count == 0:
            ans = messagebox.askyesno(
                "0 Owned Cards Detected",
                "Your collection currently shows 0 owned cards.\n\n"
                "Would you like to export the full MTG Arena card catalog with Quantity = 0?"
            )
            if not ans:
                return
            export_all_if_empty = True

        threading.Thread(target=self._export_worker, args=(Path(save_path), export_all_if_empty), daemon=True).start()

    def _export_worker(self, target_path: Path, export_all_if_empty: bool):
        self.status_var.set(f"Writing spreadsheet to {target_path.name}...")
        self.progress_bar.set(0.35)

        rows = []
        for norm_name, info in self.local_metadata_by_name.items():
            if norm_name in BASIC_LANDS:
                continue
            qty = self.owned_by_name.get(norm_name, 0)
            if not export_all_if_empty and qty <= 0:
                continue
            rows.append({
                "Arena ID": info.get("Arena ID", ""),
                "Name": info.get("Name", norm_name.title()),
                "Quantity": qty,
                "Color": info.get("Color", "Colorless"),
                "Color Identity": info.get("Color Identity", "Colorless"),
                "Mana Cost": info.get("Mana Cost", ""),
                "Type Line": info.get("Type Line", ""),
                "Rarity": info.get("Rarity", "Common"),
                "Set Code": info.get("Set Code", ""),
            })

        df = pd.DataFrame(rows)
        if not df.empty:
            df.sort_values(by=["Color", "Name", "Set Code"], inplace=True)

        try:
            if target_path.suffix.lower() == ".csv":
                df.to_csv(target_path, index=False, encoding="utf-8-sig")
                xlsx_path = target_path.with_suffix(".xlsx")
                self._write_excel_tabs(df, xlsx_path)
            else:
                self._write_excel_tabs(df, target_path)
                csv_path = target_path.with_suffix(".csv")
                df.to_csv(csv_path, index=False, encoding="utf-8-sig")

            self.progress_bar.set(1.0)
            self.status_var.set(f"Successfully exported {len(rows):,} cards to {target_path}!")
            self.after(0, lambda: messagebox.showinfo("Export Complete", f"Exported {len(rows):,} cards to:\n{target_path}"))
        except Exception as e:
            self.status_var.set(f"Export failed: {e}")
            self.after(0, lambda: messagebox.showerror("Export Error", f"Could not write file:\n{e}"))

    @staticmethod
    def _write_excel_tabs(df: pd.DataFrame, excel_path: Path):
        with pd.ExcelWriter(excel_path, engine="openpyxl") as writer:
            df.to_excel(writer, sheet_name="All Cards", index=False)
            if not df.empty and "Color" in df.columns:
                for color_group, group_df in df.groupby("Color"):
                    safe_sheet_name = re.sub(r'[\\/*?:\[\]]', '', str(color_group))[:31] or "Other"
                    group_df.to_excel(writer, sheet_name=safe_sheet_name, index=False)

    # ==================== LIVE COMMANDER AUTOCOMPLETE ====================
    DEFAULT_COMMANDERS = [
        "Teval, the Balanced Scale", "Galadriel, Light of Valinor",
        "Neheb, the Eternal", "Baron Helmut Zemo",
    ]

    def _build_commander_popup(self):
        inner = self.cmd_entry._entry  # underlying tk.Entry, so key bindings fire reliably
        self._cmd_popup = None
        self._cmd_listbox = None
        self._cmd_hide_job = None

        inner.bind("<KeyRelease>", self._on_commander_keyrelease)
        inner.bind("<Down>", self._cmd_nav_down)
        inner.bind("<Up>", self._cmd_nav_up)
        inner.bind("<Return>", self._cmd_on_return)
        inner.bind("<Escape>", lambda _: self._hide_commander_popup())
        inner.bind("<Button-1>", lambda _: self.after(10, self._update_commander_popup))
        inner.bind("<FocusOut>", lambda _: self._schedule_hide_commander_popup())
        self.bind("<Configure>", lambda e: self._hide_commander_popup() if e.widget is self else None, add="+")

    def _commander_matches(self, typed: str, limit: int = 12) -> list[str]:
        pool = self.commander_list or self.DEFAULT_COMMANDERS
        t = typed.strip().lower()
        if not t:
            return list(pool[:limit])
        starts, word_starts, contains = [], [], []
        for name in pool:
            low = name.lower()
            if low.startswith(t):
                starts.append(name)
            elif f" {t}" in low or f",{t}" in low:
                word_starts.append(name)
            elif t in low:
                contains.append(name)
        return (starts + word_starts + contains)[:limit]

    def _on_commander_keyrelease(self, event):
        if event.keysym in ("Up", "Down", "Return", "Escape", "Tab", "Left", "Right", "Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R"):
            return
        self._update_commander_popup()

    def _update_commander_popup(self):
        matches = self._commander_matches(self.cmd_var.get())
        # nothing useful to show: hide (also hide when the only match is exactly what's typed)
        if not matches or (len(matches) == 1 and matches[0].lower() == self.cmd_var.get().strip().lower()):
            self._hide_commander_popup()
            return

        if self._cmd_hide_job:
            self.after_cancel(self._cmd_hide_job)
            self._cmd_hide_job = None

        if self._cmd_popup is None or not self._cmd_popup.winfo_exists():
            popup = tk.Toplevel(self)
            popup.withdraw()
            popup.overrideredirect(True)
            popup.attributes("-topmost", True)
            lb = tk.Listbox(
                popup, activestyle="none", exportselection=False,
                bg="#1e1e24", fg="#f4f4f5", selectbackground="#3b82f6", selectforeground="#ffffff",
                font=("Segoe UI", 10), borderwidth=1, relief="solid", highlightthickness=0
            )
            lb.pack(fill="both", expand=True)
            lb.bind("<ButtonRelease-1>", self._cmd_on_click)
            lb.bind("<Motion>", self._cmd_on_hover)
            self._cmd_popup, self._cmd_listbox = popup, lb

        lb = self._cmd_listbox
        lb.delete(0, tk.END)
        for name in matches:
            lb.insert(tk.END, name)

        self.update_idletasks()
        x = self.cmd_entry.winfo_rootx()
        y = self.cmd_entry.winfo_rooty() + self.cmd_entry.winfo_height() + 2
        rows = min(len(matches), 12)
        lb.configure(height=rows)
        width = max(self.cmd_entry.winfo_width(), 300)
        self._cmd_popup.geometry(f"{width}x{rows * 20 + 6}+{x}+{y}")
        self._cmd_popup.deiconify()
        self._cmd_popup.lift()

    def _hide_commander_popup(self):
        if self._cmd_popup is not None and self._cmd_popup.winfo_exists():
            self._cmd_popup.withdraw()

    def _schedule_hide_commander_popup(self):
        # small delay so a click on the list still registers before the popup disappears
        if self._cmd_hide_job:
            self.after_cancel(self._cmd_hide_job)
        self._cmd_hide_job = self.after(200, self._hide_commander_popup)

    def _cmd_popup_visible(self) -> bool:
        return bool(self._cmd_popup is not None and self._cmd_popup.winfo_exists() and self._cmd_popup.winfo_viewable())

    def _cmd_choose(self, name: str):
        self.cmd_var.set(name)
        self._hide_commander_popup()
        self.cmd_entry._entry.focus_set()
        self.cmd_entry._entry.icursor(tk.END)

    def _cmd_on_click(self, event):
        idx = self._cmd_listbox.nearest(event.y)
        if 0 <= idx < self._cmd_listbox.size():
            self._cmd_choose(self._cmd_listbox.get(idx))

    def _cmd_on_hover(self, event):
        idx = self._cmd_listbox.nearest(event.y)
        self._cmd_listbox.selection_clear(0, tk.END)
        if 0 <= idx < self._cmd_listbox.size():
            self._cmd_listbox.selection_set(idx)

    def _cmd_move_selection(self, delta: int):
        if not self._cmd_popup_visible():
            self._update_commander_popup()
            if not self._cmd_popup_visible():
                return "break"
        lb = self._cmd_listbox
        cur = lb.curselection()
        new_idx = (cur[0] + delta) if cur else (0 if delta > 0 else lb.size() - 1)
        new_idx = max(0, min(lb.size() - 1, new_idx))
        lb.selection_clear(0, tk.END)
        lb.selection_set(new_idx)
        lb.see(new_idx)
        return "break"

    def _cmd_nav_down(self, _event):
        return self._cmd_move_selection(1)

    def _cmd_nav_up(self, _event):
        return self._cmd_move_selection(-1)

    def _cmd_on_return(self, _event):
        if self._cmd_popup_visible():
            cur = self._cmd_listbox.curselection()
            if cur:
                self._cmd_choose(self._cmd_listbox.get(cur[0]))
                return "break"
        self._hide_commander_popup()
        self.start_search()
        return "break"

    # ==================== MOXFIELD BRAWL DECK SEARCH & ACCURATE DIFF ====================
    def start_search(self):
        query = self.cmd_var.get().strip()
        if not query:
            messagebox.showwarning("Commander Required", "Please enter or select a Commander name.")
            return

        self.search_btn.configure(state="disabled")
        self.deck_tree.delete(*self.deck_tree.get_children())
        self.all_fetched_decks.clear()
        self.displayed_decks.clear()
        self.progress_bar.set(0.05)
        self.left_tabs.set("Moxfield Results")

        threading.Thread(target=self._search_worker, args=(query,), daemon=True).start()

    def _search_worker(self, query: str):
        try:
            self.status_var.set(f"Looking up commander '{query}'...")
            cmd_id, cmd_name = self.moxfield.get_commander_card(query)
            if not cmd_id:
                self.status_var.set(f"Could not find commander '{query}' on Moxfield or Scryfall.")
                return

            mode = self.format_var.get()
            scan_limit = int(self.scan_limit_var.get())
            try:
                max_wc = int(self.max_wc_entry.get().strip())
            except ValueError:
                max_wc = 5

            self.status_var.set(f"Searching Moxfield for {mode} decks led by {cmd_name}...")
            summaries = self.moxfield.search_brawl_decks(cmd_id, mode=mode, max_decks=scan_limit)
            if not summaries:
                self.status_var.set(f"No Brawl decks found on Moxfield for {cmd_name}.")
                return

            total = len(summaries)
            skipped_non_100 = 0
            for idx, summary in enumerate(summaries, start=1):
                self.progress_bar.set(idx / total)
                pub_id = summary.get("publicId")
                deck_name = summary.get("name", "Untitled Deck")
                self.status_var.set(f"[{idx}/{total}] Analyzing '{deck_name}'...")

                try:
                    full_deck = self.moxfield.get_full_deck(pub_id)
                    analysis = self._analyze_deck(full_deck)
                except Exception:
                    continue

                # Only true 100-card Brawl decks (commander(s) + mainboard). Drops 60-card / unfinished lists.
                if analysis["card_count"] != 100:
                    skipped_non_100 += 1
                    continue

                record = {
                    "name": deck_name,
                    "author": summary.get("createdByUser", {}).get("userName", "Unknown"),
                    "public_id": pub_id,
                    "views": summary.get("viewCount", 0),
                    "likes": summary.get("likeCount", 0),
                    "commander": cmd_name,
                    "raw_deck": full_deck,
                    **analysis
                }
                self.all_fetched_decks.append(record)
                if analysis["total_missing"] <= max_wc:
                    self.after(0, self._insert_deck_row, record)

            if not self.all_fetched_decks:
                self.status_var.set(
                    f"No 100-card Brawl decks found for {cmd_name} (skipped {skipped_non_100} non-100-card list(s))."
                )
            else:
                self.after(0, self._finalize_search_display, cmd_name, mode, max_wc)
        except Exception as e:
            self.status_var.set(f"Moxfield search error: {e}")
        finally:
            self.after(0, lambda: self.search_btn.configure(state="normal"))

    def _finalize_search_display(self, cmd_name: str, mode: str, max_wc: int):
        if len(self.displayed_decks) > 0:
            self.status_var.set(
                f"Found {len(self.displayed_decks)} {mode} deck(s) for {cmd_name} with <= {max_wc} missing cards (scanned {len(self.all_fetched_decks)})."
            )
        elif self.all_fetched_decks:
            self.all_fetched_decks.sort(key=lambda d: d["total_missing"])
            for rec in self.all_fetched_decks:
                self._insert_deck_row(rec)
            lowest = self.all_fetched_decks[0]["total_missing"]
            self.status_var.set(
                f"0 decks had <= {max_wc} missing cards (closest needed {lowest}). Showing all {len(self.all_fetched_decks)} decks sorted by fewest missing!"
            )

    def _apply_missing_filter_live(self):
        if not self.all_fetched_decks:
            return
        try:
            max_wc = int(self.max_wc_entry.get().strip())
        except ValueError:
            max_wc = 5

        self.deck_tree.delete(*self.deck_tree.get_children())
        self.displayed_decks.clear()

        filtered = [d for d in self.all_fetched_decks if d["total_missing"] <= max_wc]
        if filtered:
            for rec in filtered:
                self._insert_deck_row(rec)
            self.status_var.set(f"Showing {len(filtered)} deck(s) requiring <= {max_wc} missing cards.")
        else:
            self.all_fetched_decks.sort(key=lambda d: d["total_missing"])
            for rec in self.all_fetched_decks:
                self._insert_deck_row(rec)
            self.status_var.set(f"No decks had <= {max_wc} missing cards. Showing all {len(self.all_fetched_decks)} decks sorted by fewest missing.")

    def _recalculate_loaded_decks(self):
        for rec in self.all_fetched_decks:
            if "raw_deck" in rec:
                updated = self._analyze_deck(rec["raw_deck"])
                rec.update(updated)
        if self.current_selected_deck and "raw_deck" in self.current_selected_deck:
            updated_sel = self._analyze_deck(self.current_selected_deck["raw_deck"])
            self.current_selected_deck.update(updated_sel)
            self._refresh_card_inspector_table()
            summary_text = (
                f"{self.current_selected_deck['name']} (by {self.current_selected_deck['author']})  •  "
                f"{self.current_selected_deck.get('card_count', '?')} cards  •  "
                f"Uncrafted: {self.current_selected_deck['total_missing']} ({self.current_selected_deck['breakdown']})  •  "
                f"Owned: {self.current_selected_deck['completion_pct']}"
            )
            self.deck_summary_lbl.configure(text=summary_text)
        self._apply_missing_filter_live()

    def _analyze_deck(self, full_deck: dict) -> dict:
        boards = full_deck.get("boards", {})
        cmd_entries = boards.get("commanders", {}).get("cards", {})
        main_entries = boards.get("mainboard", {}).get("cards", {})

        card_count = sum(int(i.get("quantity", 1)) for i in cmd_entries.values()) + \
                     sum(int(i.get("quantity", 1)) for i in main_entries.values())

        missing_cards = []
        card_rows = []
        wc_counts = {"mythic": 0, "rare": 0, "uncommon": 0, "common": 0}
        curve = {1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0}

        total_nonland = 0
        owned_nonland = 0
        total_missing = 0
        not_in_arena_count = 0

        arena_cmd_lines = []
        arena_main_lines = []
        seen_norms_in_deck = set()

        def process_board(entries: dict, target_lines: list, is_cmd: bool):
            nonlocal total_missing, total_nonland, owned_nonland, not_in_arena_count
            for _, item in entries.items():
                raw_qty = int(item.get("quantity", 1))
                card_obj = item.get("card", {})
                raw_name = card_obj.get("name", "Unknown")
                type_line = card_obj.get("type_line", "")
                cmc = int(float(card_obj.get("cmc") or 0))
                scryfall_id = card_obj.get("scryfall_id", "")

                export_name = raw_name.split("//")[0].strip() if "//" in raw_name else raw_name
                norm = normalize_card_name(raw_name)

                if norm not in BASIC_LANDS:
                    if norm in seen_norms_in_deck:
                        continue
                    seen_norms_in_deck.add(norm)
                    qty = min(raw_qty, 4) if norm in MULTI_COPY_CARDS else 1
                else:
                    qty = raw_qty

                target_lines.append(f"{qty} {export_name}")

                if "Land" not in type_line and not is_cmd:
                    bucket = min(6, max(1, cmc))
                    curve[bucket] += qty

                if norm in BASIC_LANDS:
                    card_rows.append({
                        "status": "Basic Land",
                        "owned_str": f"∞ / {qty}",
                        "qty": qty,
                        "name": export_name,
                        "norm_name": norm,
                        "type": type_line,
                        "rarity": "Basic",
                        "cmc": cmc,
                        "scryfall_id": scryfall_id,
                        "tag": "owned"
                    })
                    continue

                in_arena_db = (not self.local_metadata_by_name) or (norm in self.local_metadata_by_name)
                local_info = self.local_metadata_by_name.get(norm, {})
                rarity = (local_info.get("Rarity") or card_obj.get("rarity") or "rare").lower()

                total_nonland += qty
                owned_qty = self.owned_by_name.get(norm, 0)
                shortfall = max(0, qty - owned_qty)

                if not in_arena_db:
                    not_in_arena_count += qty
                    total_missing += qty
                    r_key = rarity if rarity in wc_counts else "rare"
                    wc_counts[r_key] += qty
                    missing_cards.append(f"{qty} {export_name}")
                    card_rows.append({
                        "status": "Not in Arena",
                        "owned_str": f"0 / {qty}",
                        "qty": qty,
                        "name": export_name,
                        "norm_name": norm,
                        "type": type_line,
                        "rarity": r_key.capitalize(),
                        "cmc": cmc,
                        "scryfall_id": scryfall_id,
                        "tag": "not_in_arena"
                    })
                elif shortfall > 0:
                    total_missing += shortfall
                    r_key = rarity if rarity in wc_counts else "rare"
                    wc_counts[r_key] += shortfall
                    missing_cards.append(f"{shortfall} {export_name}")
                    card_rows.append({
                        "status": f"Uncrafted ({shortfall})",
                        "owned_str": f"{owned_qty} / {qty}",
                        "qty": qty,
                        "name": export_name,
                        "norm_name": norm,
                        "type": type_line,
                        "rarity": r_key.capitalize(),
                        "cmc": cmc,
                        "scryfall_id": scryfall_id,
                        "tag": "missing"
                    })
                else:
                    owned_nonland += qty
                    card_rows.append({
                        "status": "Commander" if is_cmd else "Owned",
                        "owned_str": f"{owned_qty} / {qty}",
                        "qty": qty,
                        "name": export_name,
                        "norm_name": norm,
                        "type": type_line,
                        "rarity": rarity.capitalize(),
                        "cmc": cmc,
                        "scryfall_id": scryfall_id,
                        "tag": "commander" if is_cmd else "owned"
                    })

        process_board(cmd_entries, arena_cmd_lines, True)
        process_board(main_entries, arena_main_lines, False)

        arena_export_str = "Commander\n" + "\n".join(arena_cmd_lines) + "\n\nDeck\n" + "\n".join(arena_main_lines)
        breakdown_str = f"{wc_counts['mythic']}M / {wc_counts['rare']}R / {wc_counts['uncommon']}U / {wc_counts['common']}C"
        pct = round((owned_nonland / max(1, total_nonland)) * 100, 1)

        tag_order = {"commander": 0, "missing": 1, "not_in_arena": 2, "owned": 3}
        card_rows.sort(key=lambda r: (tag_order.get(r["tag"], 4), r["cmc"], r["name"]))

        return {
            "card_count": card_count,
            "total_missing": total_missing,
            "not_in_arena_count": not_in_arena_count,
            "completion_pct": f"{pct}%",
            "wc_counts": wc_counts,
            "breakdown": breakdown_str,
            "missing_cards": missing_cards,
            "card_rows": card_rows,
            "curve": curve,
            "arena_export": arena_export_str,
        }

    # ==================== UI TABLE & CARD PREVIEW ====================
    def _insert_deck_row(self, record: dict):
        idx = len(self.displayed_decks)
        self.displayed_decks.append(record)
        tag = "zero_wc" if record["total_missing"] == 0 else ("low_wc" if record["total_missing"] <= 5 else "")
        self.deck_tree.insert(
            "", tk.END, iid=str(idx),
            values=(record["name"], record["author"], record.get("card_count", "—"), record["completion_pct"],
                    record["total_missing"], record["breakdown"], record["views"]),
            tags=(tag,) if tag else ()
        )

    def _sort_treeview(self, tree: ttk.Treeview, col: str, is_numeric: bool):
        items = [(tree.set(k, col), k) for k in tree.get_children("")]
        if is_numeric:
            items.sort(key=lambda t: float(str(t[0]).replace("%", "") or 0), reverse=True)
        elif col in ("missing", "qty", "id"):
            items.sort(key=lambda t: int(t[0] or 0))
        else:
            items.sort(key=lambda t: str(t[0]).lower())

        for index, (_, k) in enumerate(items):
            tree.move(k, "", index)

    def on_deck_select(self, tree: ttk.Treeview, source_list: list):
        selected = tree.selection()
        if not selected:
            return
        idx = int(selected[0])
        if idx >= len(source_list):
            return
        deck = source_list[idx]
        self.current_selected_deck = deck

        self.copy_btn.configure(state="normal", text="📋 Copy Deck for MTG Arena")
        self.copy_missing_btn.configure(state="normal")
        self.bookmark_btn.configure(state="normal")
        self.open_web_btn.configure(state="normal" if deck.get("public_id") else "disabled")

        is_saved = any(d.get("public_id") == deck.get("public_id") and deck.get("public_id") for d in self.saved_decks)
        self.bookmark_btn.configure(text="★ Unsave" if is_saved else "★ Save")

        extra_warn = f"  •  ⚠️ {deck.get('not_in_arena_count', 0)} Not in Arena" if deck.get("not_in_arena_count") else ""
        summary_text = (
            f"{deck['name']} (by {deck['author']})  •  "
            f"{deck.get('card_count', '?')} cards  •  "
            f"Uncrafted: {deck['total_missing']} ({deck['breakdown']})  •  "
            f"Owned: {deck['completion_pct']}{extra_warn}"
        )
        self.deck_summary_lbl.configure(text=summary_text)

        c = deck.get("curve", {})
        if c:
            curve_str = f"Curve: 1:{c.get(1,0)} | 2:{c.get(2,0)} | 3:{c.get(3,0)} | 4:{c.get(4,0)} | 5:{c.get(5,0)} | 6+:{c.get(6,0)}"
            self.curve_lbl.configure(text=curve_str)

        self._refresh_card_inspector_table()

        rows = deck.get("card_rows", [])
        if rows:
            first = rows[0]
            self.card_detail_lbl.configure(text=f"{first['name']}\n{first['status']} ({first['rarity']})")
            threading.Thread(
                target=self._fetch_card_image,
                args=(first["name"], first.get("scryfall_id", "")),
                daemon=True
            ).start()

    def _refresh_card_inspector_table(self, *_):
        self.card_tree.delete(*self.card_tree.get_children())
        if not self.current_selected_deck:
            return

        mode = self.card_view_filter.get()
        rows = self.current_selected_deck.get("card_rows", [])

        for i, r in enumerate(rows):
            if mode == "Uncrafted / Missing" and r["tag"] not in ("missing", "not_in_arena"):
                continue
            if mode == "Owned Only" and r["tag"] in ("missing", "not_in_arena"):
                continue
            self.card_tree.insert(
                "", tk.END, iid=str(i),
                values=(r["status"], r.get("owned_str", f"{r['qty']}"), r["name"], r["type"], r["rarity"], r["cmc"]),
                tags=(r["tag"],)
            )

    def on_deck_card_row_select(self, _event):
        selected = self.card_tree.selection()
        if not selected or not self.current_selected_deck:
            return
        row_idx = int(selected[0])
        rows = self.current_selected_deck.get("card_rows", [])
        if row_idx >= len(rows):
            return

        card_info = rows[row_idx]
        self.card_detail_lbl.configure(
            text=f"{card_info['name']}\nStatus: {card_info['status']}  •  {card_info['rarity']}"
        )
        self.card_img_label.configure(image="", text=f"Loading\n{card_info['name']}...")
        threading.Thread(
            target=self._fetch_card_image,
            args=(card_info["name"], card_info.get("scryfall_id", "")),
            daemon=True
        ).start()

    def on_deck_card_double_click(self, _event):
        selected = self.card_tree.selection()
        if not selected or not self.current_selected_deck:
            return
        row_idx = int(selected[0])
        rows = self.current_selected_deck.get("card_rows", [])
        if row_idx >= len(rows):
            return
        card_info = rows[row_idx]
        norm = card_info.get("norm_name") or normalize_card_name(card_info["name"])
        cur_owned = self.owned_by_name.get(norm, 0)
        new_qty = simpledialog.askinteger(
            "Update Card Ownership",
            f"Set how many copies of '{card_info['name']}' you own in MTG Arena (0–4):",
            initialvalue=cur_owned,
            minvalue=0,
            maxvalue=4,
            parent=self
        )
        if new_qty is None:
            return
        self.owned_by_name[norm] = new_qty
        self.user_anchors[norm] = new_qty
        self._save_clean_cache()
        self._update_top_wallet_banner()
        self.refresh_collection_browser()
        self._recalculate_loaded_decks()

    def _fetch_card_image(self, card_name: str, scryfall_id: str = ""):
        clean_name = card_name.split("//")[0].strip()
        if clean_name.startswith("A-"):
            clean_name = clean_name[2:]

        if clean_name in self.image_cache:
            pil_cached = self.image_cache[clean_name]
            self.after(0, self._display_pil_image, pil_cached)
            return

        try:
            data = None
            if scryfall_id:
                r_id = requests.get(f"https://api.scryfall.com/cards/{scryfall_id}", headers=SCRYFALL_HEADERS, timeout=8)
                if r_id.status_code == 200:
                    data = r_id.json()

            if not data:
                r_named = requests.get(
                    "https://api.scryfall.com/cards/named",
                    params={"fuzzy": clean_name},
                    headers=SCRYFALL_HEADERS,
                    timeout=8
                )
                r_named.raise_for_status()
                data = r_named.json()

            img_url = data.get("image_uris", {}).get("normal") or data.get("image_uris", {}).get("large")
            if not img_url and "card_faces" in data:
                for face in data["card_faces"]:
                    img_url = face.get("image_uris", {}).get("normal")
                    if img_url:
                        break

            if not img_url:
                self.after(0, lambda: self.card_img_label.configure(image="", text=f"No image found for\n{clean_name}"))
                return

            img_resp = requests.get(img_url, headers=SCRYFALL_HEADERS, timeout=10)
            img_resp.raise_for_status()

            pil_img = Image.open(BytesIO(img_resp.content)).convert("RGBA")
            pil_img = pil_img.resize((226, 315), Image.Resampling.LANCZOS)
            self.image_cache[clean_name] = pil_img
            self.after(0, self._display_pil_image, pil_img)
        except Exception:
            self.after(0, lambda: self.card_img_label.configure(image="", text=f"Preview unavailable\n({clean_name})"))

    def _display_pil_image(self, pil_img: Image.Image):
        tk_photo = ImageTk.PhotoImage(pil_img, master=self)
        self._active_photo_ref = tk_photo
        self.card_img_label.configure(image=tk_photo, text="")

    # ==================== CLIPBOARD, BOOKMARKS & HOTKEYS ====================
    def copy_selected_deck(self):
        if not self.current_selected_deck:
            return
        self.clipboard_clear()
        self.clipboard_append(self.current_selected_deck["arena_export"])
        self.update()
        self.copy_btn.configure(text="✓ Copied! Click 'Import' in MTG Arena")
        self.status_var.set(f"Copied '{self.current_selected_deck['name']}' to clipboard.")

    def copy_missing_only(self):
        if not self.current_selected_deck:
            return
        missing = self.current_selected_deck.get("missing_cards", [])
        if not missing:
            messagebox.showinfo("100% Owned", "You already own every card in this deck!")
            return
        text = "Deck\n" + "\n".join(missing)
        self.clipboard_clear()
        self.clipboard_append(text)
        self.update()
        self.status_var.set(f"Copied {len(missing)} uncrafted card line(s) to clipboard.")

    def open_in_moxfield(self):
        if not self.current_selected_deck:
            return
        pub_id = self.current_selected_deck.get("public_id")
        if pub_id:
            webbrowser.open(f"https://moxfield.com/decks/{pub_id}")

    def _load_saved_decks(self) -> list:
        if SAVED_DECKS_FILE.exists():
            try:
                return json.loads(SAVED_DECKS_FILE.read_text(encoding="utf-8"))
            except Exception:
                return []
        return []

    def _save_decks_to_disk(self):
        try:
            clean_list = [{k: v for k, v in d.items() if k != "raw_deck"} for d in self.saved_decks]
            SAVED_DECKS_FILE.write_text(json.dumps(clean_list, indent=2), encoding="utf-8")
        except Exception:
            pass

    def toggle_bookmark_deck(self):
        if not self.current_selected_deck:
            return
        pub_id = self.current_selected_deck.get("public_id") or self.current_selected_deck.get("name")
        existing = [d for d in self.saved_decks if (d.get("public_id") or d.get("name")) == pub_id]
        if existing:
            self.saved_decks = [d for d in self.saved_decks if (d.get("public_id") or d.get("name")) != pub_id]
            self.bookmark_btn.configure(text="★ Save")
            self.status_var.set("Removed deck from Saved Decks.")
        else:
            self.saved_decks.append(self.current_selected_deck)
            self.bookmark_btn.configure(text="★ Unsave")
            self.status_var.set("Saved deck to ★ Saved Decks tab!")

        self._save_decks_to_disk()
        self._refresh_saved_decks_tree()

    def _refresh_saved_decks_tree(self):
        self.saved_tree.delete(*self.saved_tree.get_children())
        for idx, record in enumerate(self.saved_decks):
            self.saved_tree.insert(
                "", tk.END, iid=str(idx),
                values=(record.get("name"), record.get("author"), record.get("card_count", "—"), record.get("completion_pct"),
                        record.get("total_missing"), record.get("breakdown"), record.get("views", 0))
            )

    def toggle_mini_mode(self):
        if not self.is_mini_mode:
            self.saved_geometry = self.geometry()
            self.main_container.grid_remove()
            self.bottom_bar.grid_remove()
            self.geometry("860x48")
            self.mini_btn.configure(text="🗖 Expand")
            self.is_mini_mode = True
        else:
            self.main_container.grid()
            self.bottom_bar.grid()
            self.geometry(self.saved_geometry)
            self.mini_btn.configure(text="🗕 Mini Mode")
            self.is_mini_mode = False

    def _register_global_hotkey(self):
        if os.name != "nt":
            return

        def hotkey_listener():
            user32 = ctypes.windll.user32
            MOD_ALT = 0x0001
            VK_B = 0x42
            if not user32.RegisterHotKey(None, 1, MOD_ALT, VK_B):
                return
            msg = ctypes.wintypes.MSG()
            while user32.GetMessageA(ctypes.byref(msg), None, 0, 0) != 0:
                if msg.message == 0x0312:
                    self.after(0, self.toggle_visibility)
                user32.TranslateMessage(ctypes.byref(msg))
                user32.DispatchMessageA(ctypes.byref(msg))

        threading.Thread(target=hotkey_listener, daemon=True).start()

    def toggle_visibility(self):
        if self.visible:
            self._hide_commander_popup()
            self.withdraw()
            self.visible = False
        else:
            self.deiconify()
            self.attributes("-topmost", self.topmost_var.get())
            self.visible = True


if __name__ == "__main__":
    app = BrawlOverlayApp()
    app.mainloop()
