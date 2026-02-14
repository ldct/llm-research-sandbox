#!/usr/bin/env python3
"""Step 2: Greedy invariant selection to resolve all collisions.

Loads original 8 invariants + new extended invariants, then greedily selects
the minimal set of new invariants that resolves all remaining collisions.
"""
import csv
from collections import defaultdict

# --- Load original 8 invariants ---
original = {}  # (order, index) -> tuple of 8 values
with open('invariants_data.csv') as f:
    reader = csv.DictReader(f)
    for row in reader:
        key = (int(row['order']), int(row['index']))
        sig = (row['inv1'], row['inv3'], row['inv5'], row['inv6'],
               row['inv13'], row['invA'], row['invB'], row['invC'])
        original[key] = sig

# --- Find collisions with original 8 ---
COLLISION_ORDERS = {64, 81, 96, 100, 121, 128, 147, 160, 162, 169, 189, 192, 200}

# Group by (order, signature) to find collision clusters
by_sig = defaultdict(list)
for (order, index), sig in original.items():
    if order in COLLISION_ORDERS:
        by_sig[(order, sig)].append(index)

collision_clusters = {}
for (order, sig), indices in by_sig.items():
    if len(indices) > 1:
        collision_clusters[(order, sig)] = sorted(indices)

print(f"Original 8 invariants: {len(collision_clusters)} collision clusters")
total_colliding = sum(len(v) for v in collision_clusters.values())
print(f"Total groups in collisions: {total_colliding}")

# --- Load extended invariants ---
EXT_COLS = ['pe8','pe9','pe11','pe13','pe16','pe25','pe27',
            'pr2','pr3','pr4','pr5','pr7','pr8','pr9','pr11','pr13',
            'mix1','mix2','mix3','mix4','mix5']

extended = {}  # (order, index) -> dict of invariant values
with open('extended_invariants.csv') as f:
    reader = csv.DictReader(f)
    for row in reader:
        key = (int(row['order']), int(row['index']))
        extended[key] = {col: int(row[col]) for col in EXT_COLS}

print(f"Extended invariants loaded for {len(extended)} groups")

# --- Check which extended invariants resolve which clusters ---
# For each candidate invariant, count how many collision clusters it splits
def clusters_split_by(inv_name):
    """Return set of cluster keys that are fully resolved by this invariant."""
    split = set()
    for cluster_key, indices in collision_clusters.items():
        order = cluster_key[0]
        values = []
        for idx in indices:
            key = (order, idx)
            if key in extended:
                values.append(extended[key][inv_name])
            else:
                values.append(None)
        # Cluster is split if all values are distinct
        if len(set(values)) == len(values) and None not in values:
            split.add(cluster_key)
    return split

def clusters_helped_by(inv_name, remaining_clusters):
    """Return number of collision PAIRS resolved by adding this invariant."""
    pairs_resolved = 0
    for cluster_key in remaining_clusters:
        indices = remaining_clusters[cluster_key]
        order = cluster_key[0]
        values = {}
        for idx in indices:
            key = (order, idx)
            if key in extended:
                values[idx] = extended[key][inv_name]
            else:
                values[idx] = None
        # Count pairs that become distinguishable
        for i in range(len(indices)):
            for j in range(i+1, len(indices)):
                if values[indices[i]] != values[indices[j]] and values[indices[i]] is not None:
                    pairs_resolved += 1
    return pairs_resolved

def refine_clusters(remaining_clusters, chosen_invariants):
    """Given current chosen invariants, recompute remaining collision clusters."""
    new_clusters = {}
    for cluster_key, indices in remaining_clusters.items():
        order = cluster_key[0]
        # Sub-partition by the chosen invariant values
        sub = defaultdict(list)
        for idx in indices:
            key = (order, idx)
            if key in extended:
                vals = tuple(extended[key][inv] for inv in chosen_invariants)
            else:
                vals = None
            sub[vals].append(idx)
        for vals, sub_indices in sub.items():
            if len(sub_indices) > 1:
                # Still a collision
                new_key = (cluster_key[0], cluster_key[1], vals)
                new_clusters[new_key] = sub_indices
    return new_clusters

# --- Greedy selection ---
print("\n=== Greedy Invariant Selection ===")
chosen = []
remaining = dict(collision_clusters)  # copy

while remaining:
    best_inv = None
    best_score = 0
    for inv_name in EXT_COLS:
        score = clusters_helped_by(inv_name, remaining)
        if score > best_score:
            best_score = score
            best_inv = inv_name
    
    if best_score == 0:
        print(f"\nNo more progress possible. {len(remaining)} clusters remain.")
        break
    
    chosen.append(best_inv)
    # Refine remaining clusters
    remaining = refine_clusters(remaining, chosen)
    n_remaining_groups = sum(len(v) for v in remaining.values())
    print(f"  + {best_inv:6s} -> {len(remaining):4d} clusters, {n_remaining_groups:5d} groups still colliding (resolved {best_score} pairs)")

print(f"\nChosen invariants ({len(chosen)}): {chosen}")

if remaining:
    print(f"\n=== REMAINING COLLISIONS ({len(remaining)} clusters) ===")
    for cluster_key, indices in sorted(remaining.items()):
        order = cluster_key[0]
        print(f"  Order {order}: groups {indices}")
        # Show their extended values
        for idx in indices:
            key = (order, idx)
            if key in extended:
                vals = {k: v for k, v in extended[key].items() if k in chosen or True}
                print(f"    [{idx}] {vals}")
else:
    print("\n*** ALL COLLISIONS RESOLVED! ***")
    print(f"Total invariants needed: 8 original + {len(chosen)} new = {8 + len(chosen)}")
