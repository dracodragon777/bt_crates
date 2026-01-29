#!/usr/bin/env python3
"""
BattleTech: The Loot Boxing (v1.4) - crate generator + seed finder

Features
--------
- Loads CYOA CSV tables (as provided)
- Deterministic generation from (seed, sequence)
- Resolves GoTo sub-tables (engines, units, weapons, ammo, cryo, books, lostech maps)
- Manifest / Supply List fixed-width output with dashed separators and grouped identical items
- Reroll-on-duplicate support driven by tables/reroll.csv (Table #11 and #12 by default)
- "find-seed" command to search seeds within an inclusive [lower, upper] range using a configurable alphabet/base,
  optionally searching across many sequence values so the seed is agnostic to the user's choice order.

Typical usage
-------------
# Generate one run (sequence 0)
python bt_lootbox.py --seed "my-seed" --sequence 0 --nationality "Federated Suns" --tables ./tables

# Generate N runs (sequences 0..N-1)
python bt_lootbox.py --seed "my-seed" --sets 3 --nationality "Draconis Combine"

# Find a seed that hits Table #11 at least once in any sequence 0..50, searching seed-space "0000".."00zz" (base62)
python bt_lootbox.py find-seed --lower 0000 --upper 00zz --alphabet-preset base62 --seq-max 50 --must 11

Notes
-----
- The PDF table for Energy Weapons includes "12 -> Snub Nosed PPC". Some CSV exports omit it; we patch at runtime.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import os
import random
import re
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Set, Tuple

# -------------------------
# Constants / helpers
# -------------------------

NATIONALITIES = [
    "Capellan Confederation",
    "ComStar",
    "Draconis Combine",
    "Federated Suns",
    "Free Worlds League",
    "Lyran Commonwealth",
    "Magistracy of Canopus",
    "Mercenary",
    "Periphery",
    "Rasalhague Republic",
    "Taurian Concordat",
]

TABLE_ID_RE = re.compile(r"^(?:T#)?(\d{1,2})$")

DICE_RE = re.compile(r"^\s*(?:(\d*)d(\d+))\s*([+-]\s*\d+)?\s*$|^\s*(\d+)\s*$")
RANGE_RE = re.compile(r"^\s*(\d+)\s*(?:-\s*(\d+)\s*)?$")

def stable_int_seed(seed_str: str) -> int:
    """Convert an arbitrary seed string to a stable 64-bit integer seed."""
    h = hashlib.sha256(seed_str.encode("utf-8")).digest()
    return int.from_bytes(h[:8], "big", signed=False)

def roll_expr(expr: str, rng: random.Random) -> int:
    """
    Roll an expression:
      - integer: "4"
      - dice: "d6", "3d6"
      - optional modifier: "4d6+20", "2d6-1"
    """
    m = DICE_RE.match(str(expr))
    if not m:
        raise ValueError(f"Unsupported dice expression: {expr!r}")

    if m.group(4):  # integer
        return int(m.group(4))

    n_str, sides = m.group(1), int(m.group(2))
    n = int(n_str) if n_str else 1
    total = sum(rng.randint(1, sides) for _ in range(n))
    if m.group(3):
        total += int(m.group(3).replace(" ", ""))
    return total

def parse_range(s: str) -> Tuple[int, int]:
    """
    Parse "02" or "03-04" (inclusive).
    Returns (lo, hi).
    """
    m = RANGE_RE.match(str(s))
    if not m:
        raise ValueError(f"Bad range: {s!r}")
    lo = int(m.group(1))
    hi = int(m.group(2)) if m.group(2) else lo
    return lo, hi

def load_csv_dicts(path: str) -> List[Dict[str, str]]:
    with open(path, "r", encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))

def clean_item_template(s: str) -> str:
    # Replace "${Number}" with empty for canonical grouping,
    # leaving the actual count in qty.
    return s.replace("${Number}", "").replace("  ", " ").strip()

# -------------------------
# Table wrappers
# -------------------------

class RangeTable:
    """A table indexed by an inclusive integer range like '03-04' or exact values like '12'."""
    def __init__(self, rows: List[Dict[str, str]], range_field: str = "Range"):
        self._entries: List[Tuple[int, int, Dict[str, str]]] = []
        for row in rows:
            lo, hi = parse_range(row[range_field])
            self._entries.append((lo, hi, row))

    def lookup(self, roll: int) -> Dict[str, str]:
        for lo, hi, row in self._entries:
            if lo <= roll <= hi:
                return row
        raise KeyError(f"Roll {roll} not in any range for this table.")

    def all_texts(self, text_field: str = "Text") -> Set[str]:
        return {r.get(text_field, "").strip() for _, _, r in self._entries}

class ValueTable:
    """A table indexed by an exact integer field (e.g. 3..18)."""
    def __init__(self, rows: List[Dict[str, str]], key_field: str = "Number"):
        self._map: Dict[int, Dict[str, str]] = {int(r[key_field]): r for r in rows}
        self._rows = rows

    def lookup(self, roll: int) -> Dict[str, str]:
        return self._map[roll]

    def all_texts(self, text_field: str = "Text") -> Set[str]:
        return {r.get(text_field, "").strip() for r in self._rows}

def lookup_model(rows: List[Dict[str, str]], nationality: str, roll: int) -> str:
    nat = nationality.strip().lower()
    for r in rows:
        if r["Nationality"].strip().lower() == nat and int(r["Number"]) == roll:
            return r["Model"]
    raise KeyError(f"No model found for nationality={nationality!r}, roll={roll}")

# -------------------------
# Run state / auditing
# -------------------------

@dataclass(frozen=True)
class AuditEvent:
    table: str
    roll: int
    result: str
    origin: str

@dataclass
class RunState:
    # For reroll-on-duplicate: table_id -> seen result texts
    seen_results: Dict[str, Set[str]] = field(default_factory=lambda: defaultdict(set))
    # Quick checks for find-seed: table_id -> rolls observed
    rolls_seen: Dict[str, Set[int]] = field(default_factory=lambda: defaultdict(set))
    tables_seen: Set[str] = field(default_factory=set)
    audit: List[AuditEvent] = field(default_factory=list)

    def record(self, table: str, roll: int, result: str, origin: str, keep_audit: bool = True) -> None:
        self.tables_seen.add(table)
        self.rolls_seen[table].add(roll)
        if keep_audit:
            self.audit.append(AuditEvent(table=table, roll=roll, result=result, origin=origin))

# -------------------------
# Loot items + generation
# -------------------------

@dataclass
class LootItem:
    qty: int
    item: str
    detail: str
    origin: str  # crate id

class LootBoxGenerator:
    def __init__(self, tables_dir: str, reroll_config: Optional[str] = None):
        self.tables_dir = tables_dir

        # Load base crates table
        crates_rows = load_csv_dicts(os.path.join(tables_dir, "crates.csv"))
        self.crates: Dict[int, Dict[str, str]] = {int(r["Roll"]): r for r in crates_rows}

        # Load sub-tables
        self.house_bills = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t01-House Bills.csv")), "Number")
        self.lostech_maps = RangeTable(load_csv_dicts(os.path.join(tables_dir, "t02-Lostech Maps.csv")), "Range")
        self.engine_ratings = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t03-Engine Ratings.csv")), "Number")

        self.battlemechs = load_csv_dicts(os.path.join(tables_dir, "t04-BattleMechs.csv"))
        self.vehicles = load_csv_dicts(os.path.join(tables_dir, "t05-Combat Vehicles.csv"))
        self.aerospace = load_csv_dicts(os.path.join(tables_dir, "t06-Aerospace Fighters.csv"))

        # Weapons / ammo: these CSVs use "Range" as a discrete key (02..12)
        energy_rows = load_csv_dicts(os.path.join(tables_dir, "t07-Energy Weapons.csv"))
        # Patch missing "12 -> Snub Nosed PPC" if needed
        if not any(str(r.get("Range", "")).strip() == "12" for r in energy_rows):
            energy_rows.append({"Range": "12", "Number": "1", "Text": "${Number} Snub Nosed PPC(s)"})
        self.energy_weapons = ValueTable(energy_rows, "Range")

        self.ballistic_weapons = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t08-Ballistic Weapons.csv")), "Range")
        self.missile_weapons = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t09-Missile Weapons.csv")), "Range")
        self.ammunition = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t10-Ammunition.csv")), "Range")

        self.cryo_capsule = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t11-Cryo Capsule.csv")), "Number")
        self.books_disks = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t12-Books and Data Disks.csv")), "Number")

        # Reroll config
        self.reroll_tables: Set[str] = self._load_reroll_tables(reroll_config)

        # Precompute uniqueness domain size for reroll tables (by result text)
        self._unique_texts: Dict[str, Set[str]] = {
            "T#11": self.cryo_capsule.all_texts("Text"),
            "T#12": self.books_disks.all_texts("Text"),
        }

    def _load_reroll_tables(self, reroll_config: Optional[str]) -> Set[str]:
        """
        Read tables/reroll.csv with at least a 'name' column listing CSV filenames.
        Filenames like 't11-...' map to table IDs like 'T#11'.
        """
        # Default: tables #11 and #12
        default = {"T#11", "T#12"}

        cfg_path = reroll_config or os.path.join(self.tables_dir, "reroll.csv")
        if not os.path.exists(cfg_path):
            return set(default)

        try:
            rows = load_csv_dicts(cfg_path)
        except Exception:
            return set(default)

        out: Set[str] = set()
        for r in rows:
            name = (r.get("name") or r.get("Name") or "").strip()
            if not name:
                continue
            m = re.match(r"^t(\d{2})-", name, re.I)
            if m:
                out.add(f"T#{int(m.group(1)):02d}")
        return out or set(default)

    # --- low-level roll helpers (with optional reroll-on-duplicate) ---

    def _roll_unique(
        self,
        table_id: str,
        roll_fn,
        resolve_fn,
        state: RunState,
        origin: str,
        keep_audit: bool,
    ) -> Tuple[int, str]:
        """
        Roll and resolve a table, rerolling if the resolved result text is a duplicate
        for configured tables (using reroll.csv).
        """
        # If not configured, do a single roll
        if table_id not in self.reroll_tables:
            roll = roll_fn()
            text = resolve_fn(roll)
            state.record(table_id, roll, text, origin, keep_audit=keep_audit)
            return roll, text

        seen = state.seen_results[table_id]
        domain = self._unique_texts.get(table_id, set())
        # If we have exhausted the unique domain, reroll can't help anymore.
        if domain and len(seen) >= len(domain):
            roll = roll_fn()
            text = resolve_fn(roll)
            state.record(table_id, roll, text, origin, keep_audit=keep_audit)
            return roll, text

        for _ in range(2000):  # deterministic upper bound to avoid infinite loops
            roll = roll_fn()
            text = resolve_fn(roll)
            if text in seen:
                continue
            seen.add(text)
            state.record(table_id, roll, text, origin, keep_audit=keep_audit)
            return roll, text

        # Fallback: accept duplicate if we're extremely unlucky
        roll = roll_fn()
        text = resolve_fn(roll)
        state.record(table_id, roll, text, origin, keep_audit=keep_audit)
        return roll, text

    # --- crate + goto resolution ---

    def open_one_crate(
        self,
        crate_id: str,
        rng: random.Random,
        nationality: str,
        items: List[LootItem],
        events: List[str],
        crate_queue: "deque[str]",
        state: RunState,
        keep_audit: bool,
    ) -> int:
        roll = rng.randrange(0, 100)  # 0..99 corresponds to 00..99 on the table
        row = self.crates[roll]

        qty = roll_expr(row["Number"], rng)
        text = row["Text"].strip()
        goto = row["GoTo"].strip()

        # record crate-table selection as table "CRATE"
        state.record("CRATE", roll, text, crate_id, keep_audit=keep_audit)

        if goto == "-":
            if "${Number}" in text:
                item = clean_item_template(text)
                items.append(LootItem(qty, item, "", crate_id))
            else:
                items.append(LootItem(qty, text, "", crate_id))
            return roll

        # Resolve sub-table
        base_item = clean_item_template(text) if "${Number}" in text else text
        self._resolve_goto(goto, qty, base_item, rng, nationality, items, events, crate_id, crate_queue, state, keep_audit)
        return roll

    def _resolve_goto(
        self,
        goto: str,
        qty: int,
        base_item: str,
        rng: random.Random,
        nationality: str,
        items: List[LootItem],
        events: List[str],
        origin: str,
        crate_queue: "deque[str]",
        state: RunState,
        keep_audit: bool,
    ) -> None:
        if goto == "T#01":  # House bills (d6)
            for _ in range(qty):
                r = rng.randint(1, 6)
                bills = self.house_bills.lookup(r)["Text"]
                state.record("T#01", r, str(bills), origin, keep_audit=keep_audit)
                items.append(LootItem(1, base_item, str(bills), origin))
            return

        if goto == "T#03":  # engine rating (3d6)
            for _ in range(qty):
                r = sum(rng.randint(1, 6) for _ in range(3))
                rating = self.engine_ratings.lookup(r)["Rating"]
                state.record("T#03", r, str(rating), origin, keep_audit=keep_audit)
                items.append(LootItem(1, base_item, f"Rating {rating}", origin))
            return

        if goto in ("T#04", "T#05", "T#06"):  # units: mech/vehicle/ASF (1d6)
            rows = self.battlemechs if goto == "T#04" else self.vehicles if goto == "T#05" else self.aerospace
            for _ in range(qty):
                r = rng.randint(1, 6)
                model = lookup_model(rows, nationality, r)
                state.record(goto, r, model, origin, keep_audit=keep_audit)
                items.append(LootItem(1, base_item, model, origin))
            return

        if goto in ("T#07", "T#08", "T#09"):  # weapons (2d6)
            table_id = goto
            tbl = self.energy_weapons if goto == "T#07" else self.ballistic_weapons if goto == "T#08" else self.missile_weapons

            for _ in range(qty):
                r = sum(rng.randint(1, 6) for _ in range(2))
                row = tbl.lookup(r)
                n = roll_expr(row["Number"], rng)
                text = row["Text"]
                # Record "the 2d6 roll number" as the roll
                state.record(table_id, r, text, origin, keep_audit=keep_audit)
                if "${Number}" in text:
                    item = clean_item_template(text)
                    items.append(LootItem(n, item, "", origin))
                else:
                    items.append(LootItem(n, text, "", origin))
            return

        if goto == "T#10":  # ammunition (3d6)
            for _ in range(qty):
                r = sum(rng.randint(1, 6) for _ in range(3))
                row = self.ammunition.lookup(r)
                n = roll_expr(row["Number"], rng)
                text = row["Text"]
                state.record("T#10", r, text, origin, keep_audit=keep_audit)
                if "${Number}" in text:
                    item = clean_item_template(text)
                    items.append(LootItem(n, item, "", origin))
                else:
                    items.append(LootItem(n, text, "", origin))
            return

        if goto == "T#11":  # Cryo Capsule occupant (2d6; duplicates rerolled per reroll.csv)
            def roll_fn():
                return sum(rng.randint(1, 6) for _ in range(2))
            def resolve_fn(rr: int):
                return self.cryo_capsule.lookup(rr)["Text"]

            for _ in range(qty):
                rr, occ = self._roll_unique("T#11", roll_fn, resolve_fn, state, origin, keep_audit)
                items.append(LootItem(1, base_item, occ, origin))
            return

        if goto == "T#12":  # Books/Data Disks (2d6; duplicates rerolled per reroll.csv)
            def roll_fn():
                return sum(rng.randint(1, 6) for _ in range(2))
            def resolve_fn(rr: int):
                return self.books_disks.lookup(rr)["Text"]

            for _ in range(qty):
                rr, detail = self._roll_unique("T#12", roll_fn, resolve_fn, state, origin, keep_audit)
                items.append(LootItem(1, base_item, detail, origin))
            return

        if goto == "T#02":  # Lostech maps: each map rolls 2d6; each result grants extra crates
            for _ in range(qty):
                r = sum(rng.randint(1, 6) for _ in range(2))
                row = self.lostech_maps.lookup(r)
                found_crates = roll_expr(row["Number"], rng)
                text = row["Text"].strip()
                state.record("T#02", r, text, origin, keep_audit=keep_audit)

                events.append(f"{origin}: Lostech map roll={r} -> {found_crates} extra crate(s) ({text})")
                for _ in range(found_crates):
                    crate_queue.append("lostech")
                # Also add the map itself
                items.append(LootItem(1, base_item, text, origin))
            return

        # Fallback: unknown goto
        state.record("UNKNOWN", 0, goto, origin, keep_audit=keep_audit)
        items.append(LootItem(qty, base_item, f"Unresolved GoTo: {goto}", origin))

    def generate(
        self,
        seed: str,
        sequence: int,
        nationality: str,
        max_total_crates: int = 2000,
        show_crates: bool = False,
        keep_audit: bool = False,
        stop_when: Optional["SeedCriteria"] = None,
    ) -> Tuple[int, int, List[LootItem], List[str], List[str], RunState]:
        """
        Returns:
          (initial_crates, total_opened, items, events, crate_lines, run_state)
        """
        rng = random.Random(stable_int_seed(f"{seed}:{sequence}"))

        initial_crates = roll_expr("4d6+20", rng)
        crate_queue: deque[str] = deque(["initial"] * initial_crates)

        items: List[LootItem] = []
        events: List[str] = []
        crate_lines: List[str] = []

        state = RunState()

        opened = 0
        crate_id_counter = 0

        while crate_queue:
            if opened >= max_total_crates:
                events.append(f"STOP: reached max_total_crates={max_total_crates}, remaining={len(crate_queue)}")
                break

            provenance = crate_queue.popleft()
            crate_id_counter += 1
            crate_id = f"C{crate_id_counter:04d}({provenance})"

            roll = self.open_one_crate(crate_id, rng, nationality, items, events, crate_queue, state, keep_audit)
            opened += 1

            if show_crates:
                last_origin_items = [it for it in items if it.origin == crate_id]
                for it in last_origin_items:
                    qty_s = f"{it.qty}x"
                    detail = f" | {it.detail}" if it.detail else ""
                    crate_lines.append(f"{crate_id} roll={roll:02d} -> {qty_s} {it.item}{detail}")

            if stop_when is not None and stop_when.is_satisfied(state):
                break

        return initial_crates, opened, items, events, crate_lines, state

# -------------------------
# Aggregation / manifest
# -------------------------

def aggregate_items(items: List[LootItem]) -> List[Tuple[str, str, str]]:
    """
    Aggregate items by (item, detail), summing qty.
    Returns rows as (qty_str, item, detail).
    """
    counter: Dict[Tuple[str, str], int] = defaultdict(int)
    for it in items:
        key = (it.item.strip(), it.detail.strip())
        counter[key] += it.qty

    rows: List[Tuple[str, str, str]] = []
    for (item, detail), qty in sorted(counter.items(), key=lambda x: (x[0][0].lower(), x[0][1].lower())):
        rows.append((f"{qty}x", item, detail))
    return rows

def truncate(s: str, w: int) -> str:
    if len(s) <= w:
        return s
    if w <= 3:
        return s[:w]
    return s[: w - 3] + "..."

def format_fixed_table(rows: List[Tuple[str, str, str]], widths: Tuple[int, int, int] = (6, 60, 70),
                       headers: Tuple[str, str, str] = ("Qty", "Item", "Details")) -> str:
    q_w, i_w, d_w = widths
    header_line = f"{headers[0]:<{q_w}} {headers[1]:<{i_w}} {headers[2]:<{d_w}}"
    dash_line = f"{'-'*q_w} {'-'*i_w} {'-'*d_w}"
    lines = [header_line, dash_line]
    for qty, item, detail in rows:
        lines.append(f"{truncate(qty, q_w):<{q_w}} {truncate(item, i_w):<{i_w}} {truncate(detail, d_w):<{d_w}}")
    return "\n".join(lines)

# -------------------------
# Seed search (find-seed)
# -------------------------

ALPHABET_PRESETS: Dict[str, str] = {
    "base62": "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
    # 94 printable ASCII characters excluding space: '!'..'~'
    "ascii94": "".join(chr(c) for c in range(33, 127)),
}

def decode_seed_to_int(s: str, alphabet: str) -> int:
    base = len(alphabet)
    index = {ch: i for i, ch in enumerate(alphabet)}
    n = 0
    for ch in s:
        if ch not in index:
            raise ValueError(f"Character {ch!r} not in alphabet (base={base}).")
        n = n * base + index[ch]
    return n

def encode_int_to_seed(n: int, alphabet: str) -> str:
    base = len(alphabet)
    if n == 0:
        return alphabet[0]
    out: List[str] = []
    while n > 0:
        n, rem = divmod(n, base)
        out.append(alphabet[rem])
    return "".join(reversed(out))

@dataclass(frozen=True)
class MustSpec:
    table: str          # normalized "T#NN" or special "CRATE"
    lo: Optional[int] = None
    hi: Optional[int] = None

    def matches(self, state: RunState) -> bool:
        if self.table not in state.tables_seen:
            return False
        if self.lo is None:
            return True
        rolls = state.rolls_seen.get(self.table, set())
        if self.hi is None:
            return self.lo in rolls
        return any(self.lo <= r <= self.hi for r in rolls)

@dataclass
class SeedCriteria:
    must: List[MustSpec]

    def is_satisfied(self, state: RunState) -> bool:
        return all(m.matches(state) for m in self.must)

def normalize_table_id(raw: str) -> str:
    raw = raw.strip()
    if raw.upper() in ("CRATE", "CRATES", "CRATES.CSV"):
        return "CRATE"
    # file name like t11-...
    fm = re.match(r"^t(\d{2})-", raw, re.I)
    if fm:
        return f"T#{int(fm.group(1)):02d}"
    m = TABLE_ID_RE.match(raw.replace(" ", ""))
    if m:
        return f"T#{int(m.group(1)):02d}"
    # already like T#11
    if raw.upper().startswith("T#") and raw[2:].isdigit():
        return f"T#{int(raw[2:]):02d}"
    raise ValueError(f"Unrecognized table id/name: {raw!r}")

def parse_must(spec: str) -> MustSpec:
    """
    Accept:
      - "11" or "T#11" => must hit that table
      - "11:7" => must have roll 7 on that table
      - "T#12:2-4" => must have roll in [2,4] on that table
      - "t12-Books and Data Disks.csv:12" => same
      - "CRATE:00-10" => constrain crate d100 roll range (0..99, where 00 is 0)
    """
    spec = spec.strip()
    if ":" not in spec:
        return MustSpec(table=normalize_table_id(spec))

    left, right = spec.split(":", 1)
    table = normalize_table_id(left)

    right = right.strip()
    if "-" in right:
        a, b = right.split("-", 1)
        lo = int(a.strip())
        hi = int(b.strip())
        return MustSpec(table=table, lo=lo, hi=hi)
    else:
        lo = int(right)
        return MustSpec(table=table, lo=lo, hi=None)

def run_find_seed(args: argparse.Namespace) -> int:
    # Alphabet
    if args.alphabet is not None and args.alphabet_preset is not None:
        raise SystemExit("Use either --alphabet or --alphabet-preset, not both.")
    if args.alphabet is not None:
        alphabet = args.alphabet
    else:
        preset = args.alphabet_preset or "base62"
        if preset not in ALPHABET_PRESETS:
            raise SystemExit(f"Unknown alphabet preset: {preset}. Choices: {', '.join(ALPHABET_PRESETS)}")
        alphabet = ALPHABET_PRESETS[preset]

    if len(set(alphabet)) != len(alphabet):
        raise SystemExit("Alphabet must contain unique characters (no duplicates).")

    # Bounds
    lo_n = decode_seed_to_int(args.lower, alphabet)
    hi_n = decode_seed_to_int(args.upper, alphabet)
    if lo_n > hi_n:
        lo_n, hi_n = hi_n, lo_n

    pad_width = args.pad_width
    if pad_width is None and args.pad:
        pad_width = max(len(args.lower), len(args.upper))

    # Criteria
    must_specs = [parse_must(s) for s in (args.must or [])]
    criteria = SeedCriteria(must=must_specs) if must_specs else SeedCriteria(must=[])

    # Sequences / nationalities
    seq_min = args.seq_min
    seq_max = args.seq_max
    sequences = range(seq_min, seq_max + 1)

    nats: List[str]
    if args.any_nationality:
        nats = list(NATIONALITIES)
    else:
        nats = [args.nationality]

    gen = LootBoxGenerator(args.tables, reroll_config=args.reroll_config)

    found = 0
    checked = 0

    for n in range(lo_n, hi_n + 1):
        seed_s = encode_int_to_seed(n, alphabet)
        if pad_width is not None:
            seed_s = seed_s.rjust(pad_width, alphabet[0])

        checked += 1

        for seq in sequences:
            for nat in nats:
                # Stop early when criteria met
                _, _, _, _, _, state = gen.generate(
                    seed=seed_s,
                    sequence=seq,
                    nationality=nat,
                    max_total_crates=args.max_crates,
                    show_crates=False,
                    keep_audit=False,
                    stop_when=criteria if criteria.must else None,
                )
                ok = criteria.is_satisfied(state) if criteria.must else True
                if ok:
                    print(f"{seed_s}\t(seq={seq}, nat={nat})")
                    found += 1
                    break
            if found and args.first:
                return 0
            if found and args.limit and found >= args.limit:
                return 0

        if args.progress_every and checked % args.progress_every == 0:
            print(f"# checked={checked} found={found}", file=sys.stderr)

    return 0

# -------------------------
# CLI
# -------------------------

def build_gen_parser(ap: argparse.ArgumentParser) -> None:
    ap.add_argument("--seed", required=True, help="Base seed (string). Deterministic with --sequence.")
    ap.add_argument("--sequence", type=int, default=0, help="Sequence number: 0 for first pick, 1 for second, etc.")
    ap.add_argument("--sets", type=int, default=1, help="Generate N runs: sequences 0..N-1 (ignores --sequence if N>1).")
    ap.add_argument("--nationality", default="Federated Suns", choices=NATIONALITIES, help="Used for unit sub-tables (#4/#5/#6).")
    ap.add_argument("--tables", default="tables", help="Path to the tables directory (default: ./tables).")
    ap.add_argument("--reroll-config", default=None, help="Path to reroll.csv (default: <tables>/reroll.csv).")
    ap.add_argument("--max-crates", type=int, default=2000, help="Safety limit to avoid runaway recursion (lostech maps).")
    ap.add_argument("--show-crates", action="store_true", help="Print per-crate results before the manifest.")
    ap.add_argument("--widths", nargs=3, type=int, default=[6, 60, 70], metavar=("QTY_W", "ITEM_W", "DETAIL_W"),
                    help="Column widths for the manifest table.")
    ap.add_argument("--audit", action="store_true", help="Include a short audit dump (table rolls) after generation.")

def build_find_parser(ap: argparse.ArgumentParser) -> None:
    ap.add_argument("find_seed", nargs="?", help=argparse.SUPPRESS)  # placeholder
    ap.add_argument("--lower", required=True, help="Lower bound seed (inclusive), interpreted in the chosen alphabet/base.")
    ap.add_argument("--upper", required=True, help="Upper bound seed (inclusive), interpreted in the chosen alphabet/base.")
    ap.add_argument("--alphabet-preset", default="base62", choices=sorted(ALPHABET_PRESETS.keys()),
                    help="Alphabet preset for seed bounds/base conversion.")
    ap.add_argument("--alphabet", default=None, help="Explicit alphabet string (overrides --alphabet-preset).")
    ap.add_argument("--pad", action="store_true", help="Pad output seeds to max(len(lower),len(upper)) with alphabet[0].")
    ap.add_argument("--pad-width", type=int, default=None, help="Pad output seeds to this width (overrides --pad).")
    ap.add_argument("--must", action="append", default=[], help="Requirement, e.g. '11', '11:7', 'T#12:2-4', 'CRATE:0-10'. Can repeat.")
    ap.add_argument("--seq-min", type=int, default=0, help="Minimum sequence to test (inclusive).")
    ap.add_argument("--seq-max", type=int, default=0, help="Maximum sequence to test (inclusive).")
    ap.add_argument("--nationality", default="Federated Suns", choices=NATIONALITIES, help="Nationality used (unless --any-nationality).")
    ap.add_argument("--any-nationality", action="store_true", help="Test all nationalities (useful if criteria depend on unit results).")
    ap.add_argument("--tables", default="tables", help="Path to the tables directory (default: ./tables).")
    ap.add_argument("--reroll-config", default=None, help="Path to reroll.csv (default: <tables>/reroll.csv).")
    ap.add_argument("--max-crates", type=int, default=2000, help="Safety limit while testing each seed.")
    ap.add_argument("--first", action="store_true", help="Stop after the first matching seed is found.")
    ap.add_argument("--limit", type=int, default=None, help="Stop after N matches are found.")
    ap.add_argument("--progress-every", type=int, default=0, help="Write progress to stderr every N seeds checked (0 disables).")

def main(argv: Optional[List[str]] = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)

    # Backward compatible mode: if first arg is "find-seed"/"find", use search mode.
    if argv and argv[0] in ("find-seed", "find", "find_seed"):
        ap = argparse.ArgumentParser(prog="bt_lootbox.py find-seed")
        build_find_parser(ap)
        args = ap.parse_args(argv[1:])
        return run_find_seed(args)

    # Generation mode
    ap = argparse.ArgumentParser(prog="bt_lootbox.py")
    build_gen_parser(ap)
    args = ap.parse_args(argv)

    gen = LootBoxGenerator(args.tables, reroll_config=args.reroll_config)
    sequences = list(range(args.sets)) if args.sets > 1 else [args.sequence]

    for seq in sequences:
        initial, opened, items, events, crate_lines, state = gen.generate(
            seed=args.seed,
            sequence=seq,
            nationality=args.nationality,
            max_total_crates=args.max_crates,
            show_crates=args.show_crates,
            keep_audit=args.audit,
            stop_when=None,
        )

        print(f"Seed: {args.seed!r}  Sequence: {seq}  Nationality: {args.nationality}")
        print(f"Initial crates: {initial}  Total opened (incl. extras): {opened}")
        print()

        if args.show_crates and crate_lines:
            print("Crates opened (per-crate summary)")
            print("------------------------------")
            for line in crate_lines:
                print(line)
            print()

        if events:
            print("Events (Lostech maps)")
            print("--------------------")
            for e in events:
                print(e)
            print()

        manifest_rows = aggregate_items(items)
        print("Manifest / Supply List")
        print("----------------------")
        print(format_fixed_table(manifest_rows, widths=tuple(args.widths)))
        print()

        if args.audit and state.audit:
            print("Audit (table rolls)")
            print("-------------------")
            # keep this short; dump last ~40 entries
            num = 40
            tail = state.audit[-num:]
            for ev in tail:
                print(f"{ev.origin}\t{ev.table}\troll={ev.roll}\t{ev.result}")
            if len(state.audit) > num:
                print(f"... ({len(state.audit)} total audit entries)")
            print()

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
