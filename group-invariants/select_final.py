#!/usr/bin/env python3
"""Final combined analysis: original 8 + all new invariant phases.

Greedy selection to resolve all collisions among groups of order ≤ 200.
"""
import csv
from collections import defaultdict

# --- Load all data ---
ORIG_COLS = ['inv1','inv3','inv5','inv6','inv13','invA','invB','invC']
original = {}
with open('invariants_data.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        original[key] = tuple(row[c] for c in ORIG_COLS)

EXT_COLS = ['pe8','pe9','pe11','pe13','pe16','pe25','pe27',
            'pr2','pr3','pr4','pr5','pr7','pr8','pr9','pr11','pr13',
            'mix1','mix2','mix3','mix4','mix5']
extended = {}
with open('extended_invariants.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        extended[key] = {c: row[c] for c in EXT_COLS}

P3_COLS = ['t1','t2','t3','t4','t5','t6','t8','t9','t10','t11','t12','t14','t16']
phase3 = {}
with open('phase3_invariants.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        phase3[key] = {c: row[c] for c in P3_COLS}

P4_COLS = ['u2','u3','u4','u5','u7','u8','u10','u13','u14','u15','u17','u18','u19','u20']
phase4 = {}
with open('phase4_invariants.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        phase4[key] = {c: row[c] for c in P4_COLS}

ALL_NEW = EXT_COLS + P3_COLS + P4_COLS
print(f"Loaded: {len(original)} orig, {len(extended)} ext, {len(phase3)} p3, {len(phase4)} p4")
print(f"Total candidate new invariants: {len(ALL_NEW)}")

def get_val(order, index, col):
    key = (order, index)
    if col in EXT_COLS:
        return extended.get(key, {}).get(col)
    if col in P3_COLS:
        return phase3.get(key, {}).get(col)
    if col in P4_COLS:
        return phase4.get(key, {}).get(col)
    return None

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

print(f"\nOriginal 8: {len(collision_clusters)} collision clusters, {sum(len(v) for v in collision_clusters.values())} groups")

# --- First: check if ALL invariants together resolve everything ---
def full_signature(order, index):
    sig = list(original.get((order,index), ()))
    for c in ALL_NEW:
        v = get_val(order, index, c)
        sig.append(v if v is not None else 'NA')
    return tuple(sig)

full_by_sig = defaultdict(list)
for (order, index) in original:
    if order in COLLISION_ORDERS:
        sig = full_signature(order, index)
        full_by_sig[(order, sig)].append(index)

full_remaining = sum(1 for v in full_by_sig.values() if len(v) > 1)
full_groups = sum(len(v) for v in full_by_sig.values() if len(v) > 1)
print(f"All {8+len(ALL_NEW)} invariants combined: {full_remaining} collision clusters, {full_groups} groups")

if full_remaining > 0:
    print("\nRemaining collisions with ALL invariants:")
    for (order, sig), indices in sorted(full_by_sig.items()):
        if len(indices) > 1:
            print(f"  Order {order}: groups {sorted(indices)}")

# --- Greedy selection ---
print("\n=== Greedy Invariant Selection ===")

def count_pairs_resolved(inv_name, clusters):
    pairs = 0
    for ckey, indices in clusters.items():
        order = ckey[0]
        vals = [get_val(order, idx, inv_name) for idx in indices]
        for i in range(len(vals)):
            for j in range(i+1, len(vals)):
                if vals[i] is not None and vals[j] is not None and vals[i] != vals[j]:
                    pairs += 1
    return pairs

def refine(clusters, chosen):
    new_clusters = {}
    for ckey, indices in clusters.items():
        order = ckey[0]
        sub = defaultdict(list)
        for idx in indices:
            vals = tuple(get_val(order, idx, c) for c in chosen)
            sub[vals].append(idx)
        for vals, sub_indices in sub.items():
            if len(sub_indices) > 1:
                new_clusters[(order, tuple(sorted(sub_indices)))] = sorted(sub_indices)
    return new_clusters

chosen = []
remaining = dict(collision_clusters)

while remaining:
    best_inv = None
    best_score = 0
    for inv_name in ALL_NEW:
        if inv_name in chosen:
            continue
        score = count_pairs_resolved(inv_name, remaining)
        if score > best_score:
            best_score = score
            best_inv = inv_name
    
    if best_score == 0:
        break
    
    chosen.append(best_inv)
    remaining = refine(remaining, chosen)
    n_remaining = sum(len(v) for v in remaining.values())
    n_clusters = len(remaining)
    print(f"  + {best_inv:6s} -> {n_clusters:4d} clusters, {n_remaining:5d} groups still colliding (resolved {best_score} pairs)")

print(f"\nChosen new invariants ({len(chosen)}): {chosen}")
print(f"Total invariant set: 8 original + {len(chosen)} new = {8 + len(chosen)}")

if remaining:
    print(f"\n=== REMAINING COLLISIONS ({len(remaining)} clusters) ===")
    by_order = defaultdict(list)
    for ckey, indices in remaining.items():
        by_order[ckey[0]].append(indices)
    for order in sorted(by_order):
        cls = by_order[order]
        total = sum(len(c) for c in cls)
        print(f"  Order {order}: {len(cls)} clusters, {total} groups")
        for cl in cls[:3]:
            print(f"    groups {cl}")
        if len(cls) > 3:
            print(f"    ... and {len(cls)-3} more clusters")
else:
    print("\n*** ALL COLLISIONS RESOLVED! ***")
