#!/usr/bin/env python3

# Parse the results
data = {}
with open('creative_invariants_pairs_v2.txt', 'r') as f:
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
    "a^5=b^5", "(ab)^5=(ba)^5", "Order(a)=Order(b)", "a^2b=ba^2", "a^3b=ba^3",
    "aba=a^2b", "aba^-1=b^2", "[a,b]^2=e", "(aba)^2=e", "Order(ab)=2",
    "Order(ab)=4", "Order(ab)=5", "abab=a^2b^2", "(ab)^-1=ba", "a^2b^2=(ab)^2"
]

print("=" * 80)
print("CREATIVE INVARIANT ANALYSIS")
print("=" * 80)
print()

# For each invariant, check which pairs it distinguishes
for inv_idx in range(15):
    distinguished = []
    for pair_idx, (g1, g2) in enumerate(pairs):
        val1 = data[g1][inv_idx]
        val2 = data[g2][inv_idx]
        if val1 != val2:
            distinguished.append((pair_idx + 1, g1, g2, val1, val2))

    if distinguished:
        print(f"Invariant {inv_idx + 1}: {inv_names[inv_idx]}")
        print(f"  Distinguishes {len(distinguished)} out of 7 pairs:")
        for pair_num, g1, g2, val1, val2 in distinguished:
            print(f"    Pair {pair_num}: SmallGroup{g1} ({val1}) vs SmallGroup{g2} ({val2})")
        print()

print("=" * 80)
print("SUMMARY")
print("=" * 80)

# Count how many pairs each invariant distinguishes
scores = []
for inv_idx in range(15):
    count = 0
    for g1, g2 in pairs:
        if data[g1][inv_idx] != data[g2][inv_idx]:
            count += 1
    scores.append((count, inv_idx, inv_names[inv_idx]))

scores.sort(reverse=True)

print()
print("Invariants ranked by number of pairs distinguished:")
for count, inv_idx, name in scores:
    if count > 0:
        print(f"  {count}/7 pairs: inv{inv_idx + 1} - {name}")

# Best single invariant
best_count = scores[0][0]
best_invs = [name for count, inv_idx, name in scores if count == best_count]

print()
print(f"Best single invariant(s): distinguishes {best_count}/7 pairs")
for name in best_invs:
    print(f"  - {name}")

# Check combinations
print()
print("=" * 80)
print("REMAINING PAIRS (not distinguished by any single invariant)")
print("=" * 80)
print()

for pair_idx, (g1, g2) in enumerate(pairs):
    all_same = True
    for inv_idx in range(15):
        if data[g1][inv_idx] != data[g2][inv_idx]:
            all_same = False
            break
    if all_same:
        print(f"Pair {pair_idx + 1}: SmallGroup{g1} vs SmallGroup{g2}")
        print(f"  All 15 invariants identical!")
        print(f"  Values: {data[g1]}")
