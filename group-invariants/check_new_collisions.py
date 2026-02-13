#!/usr/bin/env python3
"""Check for NEW collisions beyond existing ones.
Takes a baseline order as arg — collisions among groups ≤ baseline are ignored.
Exits 0 if no new collisions, 1 if new collision found."""
import csv
import sys
from collections import defaultdict

baseline = int(sys.argv[1]) if len(sys.argv) > 1 else 64

sigs = defaultdict(list)
with open("invariants_data.csv") as f:
    for row in csv.DictReader(f):
        order = int(row["order"])
        index = int(row["index"])
        sig = tuple(int(row[k]) for k in ['inv1','inv3','inv5','inv6','inv13','invA','invB','invC'])
        sigs[sig].append((order, index))

new_collisions = []
for sig, groups in sigs.items():
    if len(groups) < 2:
        continue
    # A collision is "new" if at least one group has order > baseline
    if max(o for o, _ in groups) > baseline:
        new_collisions.append((sig, groups))

if new_collisions:
    new_collisions.sort(key=lambda x: x[1])
    for sig, groups in new_collisions:
        gstr = ", ".join(f"SmallGroup({o},{k})" for o, k in groups)
        print(f"NEW COLLISION: {gstr} -> {sig}")
    sys.exit(1)
else:
    total = sum(len(gs) for gs in sigs.values())
    print(f"No new collisions among {total} groups.")
    sys.exit(0)
