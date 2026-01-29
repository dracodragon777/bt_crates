#!/usr/bin/env python3
"""
BattleTech: The Loot Boxing (v1.4) - crate generator

- Loads the provided CSV tables
- Generates crates deterministically from (seed, sequence)
- Resolves referenced sub-tables (weapons, engines, units, books, cryo, lostech maps)
- Prints a fixed-width manifest with dashed separators

Usage examples
--------------
# One run (sequence 0)
python bt_lootbox.py --seed "my-seed" --sequence 0 --nationality "Federated Suns"

# Two runs (sequence 0 and 1)
python bt_lootbox.py --seed "my-seed" --sets 2 --nationality "Draconis Combine"

Notes
-----
- The PDF table for Energy Weapons includes a "12 -> Snub Nosed PPC" entry.
  The provided t07-Energy Weapons.csv is missing that row, so this script patches it at runtime.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import os
import random
import re
from dataclasses import dataclass
from typing import Dict, List, Tuple, Iterable, Optional, Set
from collections import defaultdict, deque

DICE_RE = re.compile(r'^\s*(?:(\d*)d(\d+)|(\d+))\s*(?:([+-])\s*(\d+))?\s*$')

NATIONALITIES = [
    "Capellan Confederation",
    "Draconis Combine",
    "Federated Suns",
    "Free Worlds League",
    "Lyran Commonwealth",
    "Periphery",
]

# -------------------------
# Utilities
# -------------------------

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

    if m.group(3):  # integer
        base = int(m.group(3))
    else:
        n_str, sides = m.group(1), int(m.group(2))
        n = int(n_str) if n_str not in (None, "") else 1
        base = sum(rng.randint(1, sides) for _ in range(n))

    if m.group(4):
        op = m.group(4)
        k = int(m.group(5))
        base = base + k if op == "+" else base - k

    return base

def clean_item_template(text: str) -> str:
    """Remove ${Number} from a template and normalize whitespace."""
    t = text.replace("${Number}", "").strip()
    t = re.sub(r"\s+", " ", t)
    t = t.lstrip(" ,.-")
    return t

def parse_range(r: str) -> Tuple[int, int]:
    """
    Parse:
      - "12" -> (12,12)
      - "03-04" -> (3,4)
      - "02-02" -> (2,2)
    """
    r = str(r).strip()
    if re.fullmatch(r"\d+", r):
        v = int(r)
        return v, v
    m = re.fullmatch(r"(\d+)\s*-\s*(\d+)", r)
    if m:
        return int(m.group(1)), int(m.group(2))
    raise ValueError(f"Bad range: {r!r}")

def format_fixed_table(
    rows: Iterable[Tuple[str, str, str]],
    headers: Tuple[str, str, str] = ("Qty", "Item", "Details"),
    widths: Tuple[int, int, int] = (6, 60, 75),
) -> str:
    """
    Create a fixed-width table with a dashed separator line.

    The dashed line uses the exact column widths, and columns are separated by a single space:
      Qty<spaces> Item<spaces> Details
      ------ ----- -----------
    """
    qty_w, item_w, detail_w = widths

    def trunc(s: str, w: int) -> str:
        s = s or ""
        if len(s) <= w:
            return s
        if w <= 3:
            return s[:w]
        return s[: w - 3] + "..."

    header_line = f"{headers[0]:<{qty_w}} {headers[1]:<{item_w}} {headers[2]:<{detail_w}}"
    dash_line = f"{'-' * qty_w} {'-' * item_w} {'-' * detail_w}"
    out = [header_line, dash_line]

    for qty, item, detail in rows:
        out.append(
            f"{trunc(qty, qty_w):<{qty_w}} {trunc(item, item_w):<{item_w}} {trunc(detail, detail_w):<{detail_w}}"
        )

    return "\n".join(out)

# -------------------------
# Table loaders
# -------------------------

def load_csv_dicts(path: str) -> List[Dict[str, str]]:
    with open(path, "r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        return [row for row in reader]

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

class ValueTable:
    """A table indexed by an exact integer field (e.g. 3..18)."""
    def __init__(self, rows: List[Dict[str, str]], key_field: str = "Number"):
        self._map: Dict[int, Dict[str, str]] = {int(r[key_field]): r for r in rows}

    def lookup(self, roll: int) -> Dict[str, str]:
        return self._map[roll]

def lookup_model(rows: List[Dict[str, str]], nationality: str, roll: int) -> str:
    nat = nationality.strip().lower()
    for r in rows:
        if r["Nationality"].strip().lower() == nat and int(r["Number"]) == roll:
            return r["Model"]
    raise KeyError(f"No model found for nationality={nationality!r}, roll={roll}")

# -------------------------
# Loot items + generation
# -------------------------

@dataclass
class LootItem:
    qty: int
    item: str
    detail: str = ""
    origin: str = ""  # crate id / provenance label

class LootBoxGenerator:
    def __init__(self, tables_dir: str):
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

        energy_rows = load_csv_dicts(os.path.join(tables_dir, "t07-Energy Weapons.csv"))
        # Patch missing 12 -> Snub Nosed PPC entry if absent
        if not any(int(r["Range"]) == 12 for r in energy_rows if r.get("Range")):
            energy_rows.append({"Range": "12", "Number": "1", "Text": "${Number} Snub Nosed PPC(s)"})
        self.energy_weapons = ValueTable(energy_rows, "Range")

        self.ballistic_weapons = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t08-Ballistic Weapons.csv")), "Range")
        self.missile_weapons = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t09-Missile Weapons.csv")), "Range")
        self.ammunition = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t10-Ammunition.csv")), "Range")

        self.cryo_capsule = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t11-Cryo Capsule.csv")), "Number")
        self.books_disks = ValueTable(load_csv_dicts(os.path.join(tables_dir, "t12-Books and Data Disks.csv")), "Number")

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
    ) -> None:
        if goto == "T#03":  # engine rating (3d6)
            for _ in range(qty):
                roll = sum(rng.randint(1, 6) for _ in range(3))
                rating = int(self.engine_ratings.lookup(roll)["Rating"])
                items.append(LootItem(1, base_item, f"Rating {rating}", origin))
            return

        if goto in ("T#07", "T#08", "T#09", "T#10"):  # weapons/ammo crates
            table = {
                "T#07": self.energy_weapons,
                "T#08": self.ballistic_weapons,
                "T#09": self.missile_weapons,
                "T#10": self.ammunition,
            }[goto]
            dice = 2 if goto in ("T#07", "T#08", "T#09") else 3
            for _ in range(qty):
                roll = sum(rng.randint(1, 6) for _ in range(dice))
                row = table.lookup(roll)
                sub_qty = roll_expr(row["Number"], rng)
                sub_item = clean_item_template(row["Text"])
                items.append(LootItem(sub_qty, sub_item, "", origin))
            return

        if goto in ("T#04", "T#05", "T#06"):  # unit tables
            for _ in range(qty):
                r = rng.randint(1, 6)
                if goto == "T#04":
                    model = lookup_model(self.battlemechs, nationality, r)
                elif goto == "T#05":
                    model = lookup_model(self.vehicles, nationality, r)
                else:
                    model = lookup_model(self.aerospace, nationality, r)
                items.append(LootItem(1, base_item, f"Model: {model}", origin))
            return

        if goto == "T#01":  # House Bills (1d6)
            for _ in range(qty):
                r = rng.randint(1, 6)
                cur = self.house_bills.lookup(r)["Text"]
                items.append(LootItem(1, base_item, f"Source: {cur}", origin))
            return

        if goto == "T#11":  # Cryo Capsule (2d6; reroll duplicates if qty>1)
            seen: Set[int] = set()
            for _ in range(qty):
                while True:
                    r = sum(rng.randint(1, 6) for _ in range(2))
                    if qty > 1 and r in seen:
                        continue
                    seen.add(r)
                    occ = self.cryo_capsule.lookup(r)["Text"]
                    items.append(LootItem(1, base_item, occ, origin))
                    break
            return

        if goto == "T#12":  # Books/Data Disks (2d6)
            for _ in range(qty):
                r = sum(rng.randint(1, 6) for _ in range(2))
                detail = self.books_disks.lookup(r)["Text"]
                items.append(LootItem(1, base_item, detail, origin))
            return

        if goto == "T#02":  # Lostech maps: qty maps; each map roll 2d6 on ranges table
            for i in range(qty):
                r = sum(rng.randint(1, 6) for _ in range(2))
                row = self.lostech_maps.lookup(r)
                found_crates = roll_expr(row["Number"], rng)
                text = row["Text"].replace("${Number}", str(found_crates)).strip()
                events.append(f"{origin}: Lostech map {i+1}/{qty} (roll {r}) -> {text}")
                if found_crates > 0:
                    for _ in range(found_crates):
                        crate_queue.append(f"extra-from-lostech:{origin}:map{i+1}")
            return

        # Fallback
        items.append(LootItem(qty, base_item, f"(Unresolved goto {goto})", origin))

    def open_one_crate(
        self,
        crate_id: str,
        rng: random.Random,
        nationality: str,
        items: List[LootItem],
        events: List[str],
        crate_queue: "deque[str]",
    ) -> int:
        roll = rng.randrange(0, 100)  # 0..99 corresponds to 00..99 on the table
        row = self.crates[roll]

        qty = roll_expr(row["Number"], rng)
        text = row["Text"].strip()
        goto = row["GoTo"].strip()

        if goto == "-":
            if "${Number}" in text:
                item = clean_item_template(text)
                items.append(LootItem(qty, item, "", crate_id))
            else:
                items.append(LootItem(qty, text, "", crate_id))
            return roll

        # Resolve sub-table
        base_item = clean_item_template(text) if "${Number}" in text else text
        self._resolve_goto(goto, qty, base_item, rng, nationality, items, events, crate_id, crate_queue)
        return roll

    def generate(
        self,
        seed: str,
        sequence: int,
        nationality: str,
        max_total_crates: int = 2000,
        show_crates: bool = False,
    ) -> Tuple[int, int, List[LootItem], List[str], List[str]]:
        """
        Returns:
          (initial_crates, total_opened, items, events, crate_lines)
        """
        rng = random.Random(stable_int_seed(f"{seed}:{sequence}"))

        initial_crates = roll_expr("4d6+20", rng)
        crate_queue: deque[str] = deque(["initial"] * initial_crates)

        items: List[LootItem] = []
        events: List[str] = []
        crate_lines: List[str] = []

        opened = 0
        crate_id_counter = 0

        while crate_queue:
            if opened >= max_total_crates:
                events.append(f"STOP: reached max_total_crates={max_total_crates}, remaining={len(crate_queue)}")
                break

            provenance = crate_queue.popleft()
            crate_id_counter += 1
            crate_id = f"C{crate_id_counter:04d}({provenance})"

            roll = self.open_one_crate(crate_id, rng, nationality, items, events, crate_queue)
            opened += 1

            if show_crates and items:
                # Show only the last item(s) added by this crate
                last_origin_items = [it for it in items if it.origin == crate_id]
                for it in last_origin_items:
                    qty_s = f"{it.qty}x"
                    detail = f" | {it.detail}" if it.detail else ""
                    crate_lines.append(f"{crate_id} roll={roll:02d} -> {qty_s} {it.item}{detail}")

        return initial_crates, opened, items, events, crate_lines

# -------------------------
# Aggregation / manifest
# -------------------------

def aggregate_items(items: List[LootItem]) -> List[Tuple[str, str, str]]:
    """
    Aggregate items by (item, detail), summing qty.
    Returns rows as (qty_str, item, detail) sorted by item/detail.
    """
    agg = defaultdict(int)  # (item, detail) -> qty
    for it in items:
        key = (it.item.strip(), it.detail.strip())
        agg[key] += it.qty

    rows: List[Tuple[str, str, str]] = []
    for (item, detail), qty in sorted(agg.items(), key=lambda kv: (kv[0][0].lower(), kv[0][1].lower())):
        rows.append((f"{qty}x", item, detail))
    return rows

# -------------------------
# CLI
# -------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", required=True, help="Base seed (string). Deterministic with --sequence.")
    ap.add_argument("--sequence", type=int, default=0, help="Sequence number: use 0 for first pick, 1 for second, etc.")
    ap.add_argument("--sets", type=int, default=1, help="Generate N runs: sequences 0..N-1 (ignores --sequence if N>1).")
    ap.add_argument("--nationality", default="Federated Suns", choices=NATIONALITIES, help="Used for unit sub-tables (#4/#5/#6).")
    ap.add_argument("--tables", default="tables", help="Path to the tables directory (default: ./tables).")
    ap.add_argument("--max-crates", type=int, default=2000, help="Safety limit to avoid runaway recursion (lostech maps).")
    ap.add_argument("--show-crates", action="store_true", help="Print per-crate results before the manifest.")
    ap.add_argument("--widths", nargs=3, type=int, default=[6, 60, 70], metavar=("QTY_W", "ITEM_W", "DETAIL_W"),
                    help="Column widths for the manifest table.")
    args = ap.parse_args()

    gen = LootBoxGenerator(args.tables)

    sequences = list(range(args.sets)) if args.sets > 1 else [args.sequence]

    for seq in sequences:
        initial, opened, items, events, crate_lines = gen.generate(
            seed=args.seed,
            sequence=seq,
            nationality=args.nationality,
            max_total_crates=args.max_crates,
            show_crates=args.show_crates,
        )

        print(f"Seed: {args.seed!r}  Sequence: {seq}  Nationality: {args.nationality}")
        print(f"Initial crates: {initial}  Total opened (incl. extras): {opened}")
        print()

        if args.show_crates and crate_lines:
            print("Crate Results")
            print("------------")
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

if __name__ == "__main__":
    main()
