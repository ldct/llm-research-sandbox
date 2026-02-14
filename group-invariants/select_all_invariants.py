#!/usr/bin/env python3
"""Combined analysis: original 8 + Phase 1 extended + Phase 3 structural invariants.

Greedy selection to resolve all collisions among groups of order ≤ 200.
"""
import csv
from collections import defaultdict

# --- Load original 8 invariants ---
ORIG_COLS = ['inv1','inv3','inv5','inv6','inv13','invA','invB','invC']
original = {}  # (order, index) -> tuple
with open('invariants_data.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        original[key] = tuple(row[c] for c in ORIG_COLS)

# --- Load Phase 1 extended invariants ---
EXT_COLS = ['pe8','pe9','pe11','pe13','pe16','pe25','pe27',
            'pr2','pr3','pr4','pr5','pr7','pr8','pr9','pr11','pr13',
            'mix1','mix2','mix3','mix4','mix5']
extended = {}
with open('extended_invariants.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        extended[key] = {c: row[c] for c in EXT_COLS}

# --- Load Phase 3 structural invariants ---
P3_COLS = ['t1','t2','t3','t4','t5','t6','t8','t9','t10','t11','t12','t14','t16']
phase3 = {}
with open('phase3_invariants.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        phase3[key] = {c: row[c] for c in P3_COLS}

print(f"Loaded: {len(original)} original, {len(extended)} extended, {len(phase3)} phase3")

# --- Find collision clusters with original 8 ---
COLLISION_ORDERS = {64, 81, 96, 100, 121, 128, 147, 160, 162, 169, 189, 192, 200}

by_sig = defaultdict(list)
for (order, index), sig in original.items():
    if order in COLLISION_ORDERS:
        by_sig[(order, sig)].append(index)

collision_clusters = {}
for (order, sig), indices in by_sig.items():
    if len(indices) > 1:
        collision_clusters[(order, tuple(sorted(indices)))] = sorted(indices)

print(f"Original 8: {len(collision_clusters)} collision clusters, {sum(len(v) for v in collision_clusters.values())} groups")

# --- Build candidate invariant pool ---
ALL_NEW_COLS = EXT_COLS + P3_COLS

def get_new_value(order, index, col):
    key = (order, index)
    if col in EXT_COLS and key in extended:
        return extended[key][col]
    if col in P3_COLS and key in phase3:
        return phase3[key][col]
    return None

# --- Greedy selection ---
def count_pairs_resolved(inv_name, clusters):
    """Count collision pairs resolved by adding inv_name."""
    pairs = 0
    for ckey, indices in clusters.items():
        order = ckey[0]
        vals = [get_new_value(order, idx, inv_name) for idx in indices]
        for i in range(len(vals)):
            for j in range(i+1, len(vals)):
                if vals[i] is not None and vals[j] is not None and vals[i] != vals[j]:
                    pairs += 1
    return pairs

def refine_clusters(clusters, chosen):
    """Recompute clusters after adding chosen invariants."""
    new_clusters = {}
    for ckey, indices in clusters.items():
        order = ckey[0]
        sub = defaultdict(list)
        for idx in indices:
            vals = tuple(get_new_value(order, idx, c) for c in chosen)
            sub[vals].append(idx)
        for vals, sub_indices in sub.items():
            if len(sub_indices) > 1:
                new_clusters[(order, tuple(sorted(sub_indices)))] = sorted(sub_indices)
    return new_clusters

print("\n=== Greedy Invariant Selection (all candidates) ===")
chosen = []
remaining = dict(collision_clusters)

while remaining:
    best_inv = None
    best_score = 0
    for inv_name in ALL_NEW_COLS:
        if inv_name in chosen:
            continue
        score = count_pairs_resolved(inv_name, remaining)
        if score > best_score:
            best_score = score
            best_inv = inv_name
    
    if best_score == 0:
        break
    
    chosen.append(best_inv)
    remaining = refine_clusters(remaining, chosen)
    n_remaining = sum(len(v) for v in remaining.values())
    n_clusters = len(remaining)
    print(f"  + {best_inv:6s} -> {n_clusters:4d} clusters, {n_remaining:5d} groups still colliding")

print(f"\nChosen new invariants ({len(chosen)}): {chosen}")
print(f"Total invariant set: 8 original + {len(chosen)} new = {8 + len(chosen)}")

if remaining:
    print(f"\n=== REMAINING COLLISIONS ({len(remaining)} clusters) ===")
    by_order = defaultdict(list)
    for ckey, indices in remaining.items():
        by_order[ckey[0]].append(indices)
    for order in sorted(by_order):
        clusters_list = by_order[order]
        total_groups = sum(len(c) for c in clusters_list)
        print(f"  Order {order}: {len(clusters_list)} clusters, {total_groups} groups")
        if len(clusters_list) <= 5:
            for cl in clusters_list:
                print(f"    groups {cl}")
else:
    print("\n*** ALL COLLISIONS RESOLVED! ***")
