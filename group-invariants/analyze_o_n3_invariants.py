#!/usr/bin/env python3

# Parse the results
data = {}
with open('creative_o_n3_results.txt', 'r') as f:
    for line in f:
        if line.startswith('32,') or line.startswith('50,'):
            parts = line.strip().split(',')
            order, index = int(parts[0]), int(parts[1])
            invs = [int(x) for x in parts[2:]]
            data[(order, index)] = invs

pairs = [
    ((32, 2), (32, 24)),
    ((32, 13), (32, 15)),
    ((32, 27), (32, 34)),
    ((32, 30), (32, 31)),
    ((32, 37), (32, 38)),
    ((32, 40), (32, 42)),
    ((50, 1), (50, 4)),
]

inv_names = [
    "abc=cab", "abc=cba", "abc=bca", "(abc)^2=e", "Order(abc)=2", "Order(abc)=4",
    "(ab)c=a(bc) & ab≠ba", "[a,b]c=c[a,b]", "abc=a²b²c²", "ab*bc=a*bc*c",
    "aba*cbc=(ac)(ba)(bc)", "abc=acb"
]

print("=" * 80)
print("CREATIVE O(n³) INVARIANT ANALYSIS")
print("=" * 80)
print()

# For each invariant, check which pairs it distinguishes
distinguished_by_inv = []
for inv_idx in range(12):
    distinguished = []
    for pair_idx, (g1, g2) in enumerate(pairs):
        val1 = data[g1][inv_idx]
        val2 = data[g2][inv_idx]
        if val1 != val2:
            distinguished.append((pair_idx + 1, g1, g2, val1, val2))

    distinguished_by_inv.append((len(distinguished), inv_idx, inv_names[inv_idx], distinguished))

# Sort by number of pairs distinguished
distinguished_by_inv.sort(reverse=True)

# Print results
for count, inv_idx, name, distinguished in distinguished_by_inv:
    if count > 0:
        print(f"Invariant {inv_idx + 1}: {name}")
        print(f"  Distinguishes {count} out of 7 pairs:")
        for pair_num, g1, g2, val1, val2 in distinguished:
            print(f"    Pair {pair_num}: SmallGroup{g1} ({val1}) vs SmallGroup{g2} ({val2})")
        print()

print("=" * 80)
print("SUMMARY")
print("=" * 80)

# Best invariant
if distinguished_by_inv[0][0] > 0:
    best_count = distinguished_by_inv[0][0]
    best_invs = [(inv_idx + 1, name) for count, inv_idx, name, _ in distinguished_by_inv if count == best_count]

    print()
    print(f"🎯 Best single O(n³) invariant(s): distinguishes {best_count}/7 pairs ({100*best_count/7:.1f}%)")
    for inv_num, name in best_invs:
        print(f"   Invariant {inv_num}: {name}")

# Count remaining indistinguishable pairs
print()
print("Invariants ranked by distinguishing power:")
for count, inv_idx, name, _ in distinguished_by_inv:
    if count > 0:
        print(f"  {count}/7 pairs: inv{inv_idx + 1} - {name}")

# Check which pairs are still indistinguishable
print()
print("=" * 80)
print("REMAINING INDISTINGUISHABLE PAIRS")
print("=" * 80)
print()

remaining = []
for pair_idx, (g1, g2) in enumerate(pairs):
    all_same = True
    for inv_idx in range(12):
        if data[g1][inv_idx] != data[g2][inv_idx]:
            all_same = False
            break
    if all_same:
        remaining.append((pair_idx + 1, g1, g2))

if remaining:
    print(f"The following {len(remaining)} pairs have identical values for ALL 12 O(n³) invariants:")
    for pair_num, g1, g2 in remaining:
        print(f"  Pair {pair_num}: SmallGroup{g1} vs SmallGroup{g2}")
        print(f"    Values: {data[g1]}")
else:
    print("✓ All 7 pairs can be distinguished by at least one O(n³) invariant!")

print()
print("=" * 80)
print("CONCLUSION")
print("=" * 80)
print()

if distinguished_by_inv[0][0] > 0:
    best = distinguished_by_inv[0]
    print(f"Best single O(n³) invariant achieves {best[0]}/7 pairs ({100*best[0]/7:.1f}%):")
    print(f"  → {best[2]}")
    print()

    if best[0] == 7:
        print("🎉 Perfect! This single invariant distinguishes ALL 7 pairs!")
    elif best[0] >= 5:
        print(f"Excellent! This distinguishes most pairs, with only {7 - best[0]} remaining.")
    elif best[0] >= 3:
        print(f"Good progress! This distinguishes {best[0]} pairs, with {7 - best[0]} remaining.")
    else:
        print(f"Limited success. Only {best[0]} pairs distinguished.")

    print()
    print(f"For comparison:")
    print(f"  - Best O(n²) invariant: 2/7 pairs (28.6%)")
    print(f"  - Best O(n³) invariant: {best[0]}/7 pairs ({100*best[0]/7:.1f}%)")
    if best[0] > 2:
        print(f"  - Improvement: +{best[0] - 2} pairs distinguished")
