#!/usr/bin/env python3
"""Combined analysis: original 8 + extended + phase3 + phase4 + structural invariants."""
import csv
from collections import defaultdict

# --- Load all data ---
def load_csv(filename, cols):
    data = {}
    with open(filename) as f:
        for row in csv.DictReader(f):
            key = (int(row['order']), int(row['index']))
            data[key] = {c: row[c] for c in cols}
    return data

ORIG_COLS = ['inv1','inv3','inv5','inv6','inv13','invA','invB','invC']
original = {}
with open('invariants_data.csv') as f:
    for row in csv.DictReader(f):
        key = (int(row['order']), int(row['index']))
        original[key] = tuple(row[c] for c in ORIG_COLS)

EXT_COLS = ['pe8','pe9','pe11','pe13','pe16','pe25','pe27',
            'pr2','pr3','pr4','pr5','pr7','pr8','pr9','pr11','pr13',
            'mix1','mix2','mix3','mix4','mix5']
extended = load_csv('extended_invariants.csv', EXT_COLS)

P3_COLS = ['t1','t2','t3','t4','t5','t6','t8','t9','t10','t11','t12','t14','t16']
phase3 = load_csv('phase3_invariants.csv', P3_COLS)

P4_COLS = ['u2','u3','u4','u5','u7','u8','u10','u13','u14','u15','u17','u18','u19','u20']
phase4 = load_csv('phase4_invariants.csv', P4_COLS)

STRUCT_COLS = ['s1','s2','s3','s4','s5','s6','s7','s8','s9','s10','s11','s12','s13','s14','s15','s16','s17','s18']
structural = load_csv('structural_invariants.csv', STRUCT_COLS)

STRUCT2_COLS = ['r1','r2','r3','r4','r5','r6','r7','r8','r9','r10','r11','r12','r13','r14','r15','r16','r17','r18']
structural2 = load_csv('structural2_invariants.csv', STRUCT2_COLS)

ALL_NEW = EXT_COLS + P3_COLS + P4_COLS + STRUCT_COLS + STRUCT2_COLS
all_sources = [extended, phase3, phase4, structural, structural2]
all_col_lists = [EXT_COLS, P3_COLS, P4_COLS, STRUCT_COLS, STRUCT2_COLS]

def get_val(order, index, col):
    key = (order, index)
    for src, cols in zip(all_sources, all_col_lists):
        if col in cols and key in src:
            return src[key][col]
    return None

print(f"Data: {len(original)} orig, {len(extended)} ext, {len(phase3)} p3, {len(phase4)} p4, {len(structural)} struct, {len(structural2)} struct2")
print(f"Total candidate invariants: 8 + {len(ALL_NEW)} = {8 + len(ALL_NEW)}")

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

# --- Check: structural alone ---
def check_with_cols(label, cols_to_use):
    remaining = 0
    remaining_groups = 0
    for ckey, indices in collision_clusters.items():
        order = ckey[0]
        sigs = []
        for idx in indices:
            sig = tuple(get_val(order, idx, c) for c in cols_to_use)
            sigs.append(sig)
        if len(set(sigs)) < len(sigs):
            remaining += 1
            remaining_groups += len(indices)
    print(f"  {label}: {remaining} clusters, {remaining_groups} groups still colliding")
    return remaining

print("\n=== Power of individual invariant sets ===")
check_with_cols("Structural only", STRUCT_COLS)
check_with_cols("Extended only", EXT_COLS)
check_with_cols("Phase3 only", P3_COLS)
check_with_cols("Phase4 only", P4_COLS)
check_with_cols("All O(n^2) pair-counting", EXT_COLS + P3_COLS + P4_COLS)
check_with_cols("Structural 1+2", STRUCT_COLS + STRUCT2_COLS)
check_with_cols("All new combined", ALL_NEW)

# --- Full combined: original + all new ---
def full_signature(order, index):
    sig = list(original.get((order, index), ()))
    for c in ALL_NEW:
        v = get_val(order, index, c)
        sig.append(v if v is not None else 'NA')
    return tuple(sig)

full_by_sig = defaultdict(list)
for (order, index) in original:
    if order in COLLISION_ORDERS:
        sig = full_signature(order, index)
        full_by_sig[(order, sig)].append(index)

full_remaining = {k: v for k, v in full_by_sig.items() if len(v) > 1}
print(f"\n=== ALL {8+len(ALL_NEW)} invariants combined ===")
print(f"{len(full_remaining)} collision clusters, {sum(len(v) for v in full_remaining.values())} groups")

if full_remaining:
    by_order = defaultdict(list)
    for (order, sig), indices in full_remaining.items():
        by_order[order].append(sorted(indices))
    for order in sorted(by_order):
        cls = by_order[order]
        total = sum(len(c) for c in cls)
        print(f"  Order {order}: {len(cls)} clusters, {total} groups")
        for cl in cls[:5]:
            print(f"    {cl}")
        if len(cls) > 5:
            print(f"    ... and {len(cls)-5} more")
else:
    print("*** ALL COLLISIONS RESOLVED! ***")

# --- Greedy selection from ALL_NEW ---
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
    print(f"\n=== REMAINING ({len(remaining)} clusters) ===")
    by_order = defaultdict(list)
    for ckey, indices in remaining.items():
        by_order[ckey[0]].append(indices)
    for order in sorted(by_order):
        cls = by_order[order]
        total = sum(len(c) for c in cls)
        print(f"  Order {order}: {len(cls)} clusters, {total} groups")
else:
    print("\n*** ALL COLLISIONS RESOLVED! ***")
