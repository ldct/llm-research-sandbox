#!/usr/bin/env python3
"""Check for duplicate signatures in invariants_data.csv.
Exits with code 0 if no collisions, 1 if collision found.
Prints the first collision found."""
import csv
import sys

signatures = {}  # signature tuple -> (order, index)

with open("invariants_data.csv") as f:
    reader = csv.DictReader(f)
    for row in reader:
        order = int(row["order"])
        index = int(row["index"])
        sig = (
            int(row["inv1"]), int(row["inv3"]), int(row["inv5"]),
            int(row["inv6"]), int(row["inv13"]), int(row["invA"]),
            int(row["invB"]), int(row["invC"])
        )
        if sig in signatures:
            prev_order, prev_index = signatures[sig]
            print(f"COLLISION: SmallGroup({prev_order},{prev_index}) and SmallGroup({order},{index}) have same signature {sig}")
            sys.exit(1)
        signatures[sig] = (order, index)

print(f"No collisions among {len(signatures)} groups.")
sys.exit(0)
