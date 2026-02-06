#!/usr/bin/env python3

# Parse the new invariant data
data = []
with open('new_invariants_test.txt', 'r') as f:
    lines = f.readlines()
    for line in lines[3:]:  # Skip first 3 lines
        parts = line.strip().split(',')
        if len(parts) == 8:
            order, index, inv1, inv2, inv3, inv4, inv5, time_ms = map(int, parts)
            data.append({
                'order': order,
                'index': index,
                'ab_eq_ba2': inv1,
                'a2b2_eq_b2a2': inv2,
                'aba_eq_bab': inv3,
                'ab2_eq_b2a': inv4,
                'a3b_eq_ba3': inv5,
                'time_ms': time_ms
            })

# The original pairs that were indistinguishable
pairs = [
    [(32, 4), (32, 12)],
    [(32, 10), (32, 13), (32, 14), (32, 15)],
    [(32, 23), (32, 24)],
    [(32, 27), (32, 34)],
    [(32, 29), (32, 33)],
    [(32, 30), (32, 31)],
    [(32, 32), (32, 35)],
    [(32, 37), (32, 38)],
    [(32, 40), (32, 42)],
    [(48, 12), (48, 13)]
]

print("=" * 80)
print("Testing 5 New O(n²) Invariants")
print("=" * 80)

invariant_names = ['ab_eq_ba2', 'a2b2_eq_b2a2', 'aba_eq_bab', 'ab2_eq_b2a', 'a3b_eq_ba3']

print("\nChecking which pairs are NOW distinguished:\n")

still_indistinguishable = []

for i, pair in enumerate(pairs, 1):
    print(f"Set {i}: {[f'({o},{idx})' for o, idx in pair]}")

    # Get data for all groups in this set
    group_data = []
    for order, index in pair:
        g = next(d for d in data if d['order'] == order and d['index'] == index)
        group_data.append(g)

    # Check if they're all still the same
    signatures = set()
    for g in group_data:
        sig = tuple(g[inv] for inv in invariant_names)
        signatures.add(sig)

    if len(signatures) == 1:
        print(f"  ✗ STILL INDISTINGUISHABLE")
        print(f"    Common signature: ab=ba²:{group_data[0]['ab_eq_ba2']}, "
              f"a²b²=b²a²:{group_data[0]['a2b2_eq_b2a2']}, "
              f"aba=bab:{group_data[0]['aba_eq_bab']}, "
              f"ab²=b²a:{group_data[0]['ab2_eq_b2a']}, "
              f"a³b=ba³:{group_data[0]['a3b_eq_ba3']}")
        still_indistinguishable.append(pair)
    else:
        print(f"  ✓ NOW DISTINGUISHED!")
        for g in group_data:
            print(f"    ({g['order']},{g['index']}): "
                  f"ab²=b²a:{g['ab2_eq_b2a']}, a³b=ba³:{g['a3b_eq_ba3']}")
    print()

print("=" * 80)
print(f"Summary: {len(still_indistinguishable)} / {len(pairs)} sets still indistinguishable")
print("=" * 80)

if still_indistinguishable:
    print(f"\nNeed to test more invariants for these {len(still_indistinguishable)} sets:")
    for pair in still_indistinguishable:
        print(f"  {[f'SmallGroup({o},{idx})' for o, idx in pair]}")
