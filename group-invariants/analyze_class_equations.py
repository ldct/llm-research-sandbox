#!/usr/bin/env python3

# Parse the class equation data
data = {}
with open('class_equations.txt', 'r') as f:
    for line in f:
        if line.startswith('SmallGroup'):
            parts = line.strip().split(',')
            # Parse "SmallGroup(n,i)"
            group_str = parts[0]
            order = int(parts[1])
            center_size = int(parts[2])
            # Parse class sizes
            class_sizes_str = parts[3].strip('"')
            class_sizes = [int(x) for x in class_sizes_str.split(',')]

            # Extract n, i from "SmallGroup(n,i)"
            group_parts = group_str.replace('SmallGroup(', '').replace(')', '').split(',')
            n, i = int(group_parts[0]), int(group_parts[1])

            data[(n, i)] = {
                'order': order,
                'center_size': center_size,
                'class_sizes': class_sizes
            }

pairs = [
    ((32, 2), (32, 24)),
    ((32, 13), (32, 15)),
    ((32, 27), (32, 34)),
    ((32, 30), (32, 31)),
    ((32, 37), (32, 38)),
    ((32, 40), (32, 42)),
    ((50, 1), (50, 4)),
]

print("=" * 80)
print("CLASS EQUATION ANALYSIS")
print("=" * 80)
print()

print("The class equation: |G| = |Z(G)| + sum of non-central conjugacy class sizes")
print()

# Analyze each pair
identical_count = 0
different_count = 0

for pair_num, (g1, g2) in enumerate(pairs, 1):
    print(f"Pair {pair_num}: SmallGroup{g1} vs SmallGroup{g2}")
    print(f"  Group 1: order={data[g1]['order']}, center={data[g1]['center_size']}")
    print(f"           class sizes: {data[g1]['class_sizes']}")
    print(f"  Group 2: order={data[g2]['order']}, center={data[g2]['center_size']}")
    print(f"           class sizes: {data[g2]['class_sizes']}")

    # Check if identical
    if (data[g1]['center_size'] == data[g2]['center_size'] and
        data[g1]['class_sizes'] == data[g2]['class_sizes']):
        print(f"  ✗ IDENTICAL class equations")
        identical_count += 1
    else:
        print(f"  ✓ DIFFERENT class equations!")
        different_count += 1

    # Show class equation
    order = data[g1]['order']
    center = data[g1]['center_size']
    non_central = [s for s in data[g1]['class_sizes'] if s > 1]
    if non_central:
        print(f"  Class equation: {order} = {center} + " + " + ".join(map(str, non_central)))
    else:
        print(f"  Class equation: {order} = {center} (abelian)")
    print()

print("=" * 80)
print("SUMMARY")
print("=" * 80)
print()
print(f"Pairs with IDENTICAL class equations: {identical_count}/7")
print(f"Pairs with DIFFERENT class equations: {different_count}/7")
print()

if identical_count == 7:
    print("🔍 REMARKABLE FINDING:")
    print("ALL 7 pairs have identical class equations!")
    print()
    print("This means these groups have:")
    print("  • Same center size")
    print("  • Same number of conjugacy classes")
    print("  • Same multiset of conjugacy class sizes")
    print()
    print("Combined with our previous findings:")
    print("  • Identical O(n²) invariant signatures")
    print("  • Identical O(n³) invariant signatures")
    print("  • Identical conjugacy class structure")
    print()
    print("These pairs are EXTRAORDINARILY similar structurally!")
    print()
    print("They likely differ only in:")
    print("  • How conjugacy classes relate to each other (fusion)")
    print("  • Subgroup lattice structure")
    print("  • Character table")
    print("  • Automorphism group")

elif identical_count > 0:
    print(f"Class equations distinguish {different_count} out of 7 pairs.")
    print()
    print("Pairs that remain indistinguishable:")
    for pair_num, (g1, g2) in enumerate(pairs, 1):
        if (data[g1]['center_size'] == data[g2]['center_size'] and
            data[g1]['class_sizes'] == data[g2]['class_sizes']):
            print(f"  • SmallGroup{g1} vs SmallGroup{g2}")

# Analyze by center size and class pattern
print()
print("=" * 80)
print("GROUPING BY CLASS STRUCTURE")
print("=" * 80)
print()

from collections import defaultdict
by_structure = defaultdict(list)

for n, i in [g for pair in pairs for g in pair]:
    key = (data[(n, i)]['center_size'], tuple(data[(n, i)]['class_sizes']))
    by_structure[key].append((n, i))

print(f"Found {len(by_structure)} distinct class structures among the 14 groups:")
print()

for idx, (key, groups) in enumerate(sorted(by_structure.items()), 1):
    center, class_sizes = key
    print(f"Structure {idx}: center={center}, {len(class_sizes)} conjugacy classes")
    print(f"  Class sizes: {list(class_sizes)}")
    print(f"  Groups: {[f'SmallGroup{g}' for g in groups]}")
    print()
