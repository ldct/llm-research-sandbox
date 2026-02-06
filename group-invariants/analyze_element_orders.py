#!/usr/bin/env python3
import re

# Parse the element order data
data = {}
with open('element_orders.txt', 'r') as f:
    for line in f:
        if line.startswith('SmallGroup'):
            # Parse using regex
            match = re.match(r'SmallGroup\((\d+),(\d+)\),(\d+),"([^"]+)"', line.strip())
            if match:
                n = int(match.group(1))
                i = int(match.group(2))
                order = int(match.group(3))
                orders_str = match.group(4)

                # Parse "1:1,2:7,4:24" format
                order_dist = {}
                for pair in orders_str.split(','):
                    elem_order, count = pair.split(':')
                    order_dist[int(elem_order)] = int(count)

                data[(n, i)] = {
                    'order': order,
                    'order_distribution': order_dist
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
print("ELEMENT ORDER DISTRIBUTION ANALYSIS")
print("=" * 80)
print()

print("Element order distribution: count of elements of each order")
print()

# Analyze each pair
identical_count = 0
different_count = 0

for pair_num, (g1, g2) in enumerate(pairs, 1):
    print(f"Pair {pair_num}: SmallGroup{g1} vs SmallGroup{g2}")

    dist1 = data[g1]['order_distribution']
    dist2 = data[g2]['order_distribution']

    # Format distributions nicely
    def format_dist(d):
        return ", ".join([f"order {k}: {v}" for k, v in sorted(d.items())])

    print(f"  Group 1: {format_dist(dist1)}")
    print(f"  Group 2: {format_dist(dist2)}")

    # Check if identical
    if dist1 == dist2:
        print(f"  ✗ IDENTICAL element order distributions")
        identical_count += 1
    else:
        print(f"  ✓ DIFFERENT element order distributions!")
        different_count += 1

        # Show differences
        all_orders = set(dist1.keys()) | set(dist2.keys())
        diffs = []
        for ord in sorted(all_orders):
            c1 = dist1.get(ord, 0)
            c2 = dist2.get(ord, 0)
            if c1 != c2:
                diffs.append(f"order {ord}: {c1} vs {c2}")
        print(f"  Differences: {', '.join(diffs)}")

    print()

print("=" * 80)
print("SUMMARY")
print("=" * 80)
print()
print(f"Pairs with IDENTICAL element orders: {identical_count}/7")
print(f"Pairs with DIFFERENT element orders: {different_count}/7")
print()

if different_count > 0:
    print(f"✓ Element order distribution distinguishes {different_count} out of 7 pairs!")
    print()
    print("Pairs that ARE distinguished:")
    for pair_num, (g1, g2) in enumerate(pairs, 1):
        if data[g1]['order_distribution'] != data[g2]['order_distribution']:
            print(f"  • Pair {pair_num}: SmallGroup{g1} vs SmallGroup{g2}")
    print()
    print("Pairs that remain indistinguishable:")
    for pair_num, (g1, g2) in enumerate(pairs, 1):
        if data[g1]['order_distribution'] == data[g2]['order_distribution']:
            print(f"  • Pair {pair_num}: SmallGroup{g1} vs SmallGroup{g2}")

print()
print("=" * 80)
print("COMPARISON WITH PREVIOUS METHODS")
print("=" * 80)
print()
print("| Method                              | Pairs Distinguished | Success Rate |")
print("|-------------------------------------|---------------------|--------------|")
print("| Best single O(n²) invariant         | 2/7                 | 28.6%        |")
print("| Best single O(n³) invariant         | 1/7                 | 14.3%        |")
print("| Element order distribution (O(n))   | {}/7                 | {:.1f}%        |".format(
    different_count, 100 * different_count / 7))
print()

if different_count >= 2:
    print("🎯 KEY FINDING:")
    print("Element order distribution (computed in O(n) time) matches or exceeds")
    print("the best O(n²) invariant performance while being much faster to compute!")
    print()
    print("This is a MUCH simpler invariant:")
    print("  • O(n) complexity vs O(n²) or O(n³)")
    print("  • Direct structural information about element orders")
    print("  • Easy to compute and interpret")

# Additional analysis: group by order distribution
print()
print("=" * 80)
print("GROUPS WITH IDENTICAL ELEMENT ORDER DISTRIBUTIONS")
print("=" * 80)
print()

from collections import defaultdict
by_dist = defaultdict(list)

for n, i in [g for pair in pairs for g in pair]:
    key = tuple(sorted(data[(n, i)]['order_distribution'].items()))
    by_dist[key].append((n, i))

print(f"Found {len(by_dist)} distinct element order distributions among the 14 groups:")
print()

for idx, (key, groups) in enumerate(sorted(by_dist.items()), 1):
    order_dist = dict(key)
    print(f"Distribution {idx}:")
    print(f"  Element orders: {', '.join([f'{k}×{v}' for k, v in sorted(order_dist.items())])}")
    print(f"  Groups: {[f'SmallGroup{g}' for g in groups]}")
    print()
