#!/usr/bin/env python3
"""Scan orders, computing invariants and tracking all collisions.
Usage: python3 run_scanning.py [max_order]
"""
import subprocess
import csv
import sys
import os
from collections import defaultdict

os.chdir(os.path.dirname(os.path.abspath(__file__)))

MAX_ORDER = int(sys.argv[1]) if len(sys.argv) > 1 else 200
CSV_FILE = "invariants_data.csv"

# Load existing data
sigs = {}  # sig -> list of (order, index)
existing_orders = set()
with open(CSV_FILE) as f:
    for row in csv.DictReader(f):
        order = int(row["order"])
        index = int(row["index"])
        sig = tuple(int(row[k]) for k in ['inv1','inv3','inv5','inv6','inv13','invA','invB','invC'])
        sigs.setdefault(sig, []).append((order, index))
        existing_orders.add(order)

cumulative = sum(len(gs) for gs in sigs.values())
max_existing = max(existing_orders) if existing_orders else 0
start = max_existing + 1

print(f"Loaded {cumulative} groups through order {max_existing}")
print(f"Scanning orders {start} to {MAX_ORDER}")
print()

collision_orders = []

for n in range(start, MAX_ORDER + 1):
    gap_input = f"n:={n};;\n" + open("compute_order.g").read()
    try:
        result = subprocess.run(["gap", "-q"], input=gap_input, capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        print(f"Order {n}: TIMEOUT")
        break
    output = result.stdout.strip()
    
    if not output:
        continue
    
    lines = output.split("\n")
    num_new = len(lines)
    
    # Parse new groups
    new_groups = []
    for line in lines:
        parts = line.split(",")
        order, index = int(parts[0]), int(parts[1])
        sig = tuple(int(x) for x in parts[3:])
        new_groups.append((order, index, sig, line))
    
    # Check collisions: cross-order and within-order
    cross_collisions = []
    for order, index, sig, _ in new_groups:
        if sig in sigs:
            cross_collisions.append(((order, index), sigs[sig][:]))
    
    # Now add all new groups to sigs
    within_count = 0
    for order, index, sig, line in new_groups:
        if sig in sigs:
            # Check if this is within-order (all existing are same order)
            if all(o == n for o, _ in sigs[sig]):
                within_count += 1
            sigs[sig].append((order, index))
        else:
            sigs[sig] = [(order, index)]
    
    # Append to CSV
    with open(CSV_FILE, "a") as f:
        for _, _, _, line in new_groups:
            f.write(line + "\n")
    
    cumulative += num_new
    
    has_cross = len(cross_collisions) > 0
    # Count total within-order collision clusters
    order_sigs = defaultdict(list)
    for _, idx, sig, _ in new_groups:
        order_sigs[sig].append(idx)
    within_clusters = sum(1 for gs in order_sigs.values() if len(gs) > 1)
    
    if has_cross or within_clusters:
        collision_orders.append(n)
        label_parts = []
        if within_clusters:
            label_parts.append(f"{within_clusters} within-order")
        # Count true cross-order (colliding with different order)
        true_cross = []
        for (o, i), existing in cross_collisions:
            if any(eo != n for eo, _ in existing):
                true_cross.append(((o, i), existing))
        if true_cross:
            label_parts.append(f"{len(true_cross)} cross-order")
        print(f"Order {n}: {num_new} groups, cumulative {cumulative} \u2014 COLLISION ({', '.join(label_parts)})")
        for (o, i), existing in true_cross[:3]:
            estr = ", ".join(f"({eo},{ei})" for eo, ei in existing if eo != n)
            print(f"  SmallGroup({o},{i}) collides with {estr}")
        if len(true_cross) > 3:
            print(f"  ... and {len(true_cross) - 3} more cross-order")
    else:
        print(f"Order {n}: {num_new} groups, cumulative {cumulative} \u2014 PASS")
    
    sys.stdout.flush()

print()
print(f"Done! {cumulative} groups through order {MAX_ORDER}.")
if collision_orders:
    print(f"Orders with collisions: {collision_orders}")
else:
    print("No new collisions!")
