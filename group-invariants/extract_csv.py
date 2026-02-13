#!/usr/bin/env python3
import re
import sys

with open("eight_invariants.md") as f:
    lines = f.readlines()

print("order,index,abelian,inv1,inv3,inv5,inv6,inv13,invA,invB,invC")

for line in lines:
    line = line.strip()
    # Match table data rows (skip header/separator)
    if not line.startswith("|") or line.startswith("|---") or "Order" in line:
        continue
    cols = [c.strip() for c in line.split("|")]
    # split on | gives empty strings at start/end
    cols = [c for c in cols if c != ""]
    if len(cols) < 12:
        continue
    order, index, _group_id, abelian_raw = cols[0], cols[1], cols[2], cols[3]
    inv1, inv3, inv5, inv6, inv13, invA, invB, invC = cols[4:12]
    abelian = "true" if "✓" in abelian_raw else "false"
    print(f"{order},{index},{abelian},{inv1},{inv3},{inv5},{inv6},{inv13},{invA},{invB},{invC}")
