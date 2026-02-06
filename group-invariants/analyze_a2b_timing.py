#!/usr/bin/env python3

# Parse the timing data
results = []
with open('a2b_eq_b2a_results.txt', 'r') as f:
    for line in f:
        line = line.strip()
        if line.startswith('#'):
            if 'Total time' in line:
                total_time = int(line.split(':')[1].strip().split()[0])
            continue
        if not ',' in line:
            continue
        parts = line.split(',')
        if len(parts) == 4:
            order, index, count, time_ms = map(int, parts)
            results.append((order, index, count, time_ms))

print("=" * 80)
print("Property: Number of pairs (a,b) where a²b = b²a")
print("=" * 80)
print(f"\nTotal groups computed: {len(results)}")
print(f"Total computation time: {total_time} ms ({total_time/1000:.3f} seconds)")
print(f"Average per group: {total_time/len(results):.2f} ms")

# Compare to property 17 (triples) and property 16 (commuting pairs)
print("\n## Comparison with other properties:")
print("-" * 80)
print("Property 16 (commuting pairs ab=ba, O(n²)):     289 ms total")
print("Property 22 (a²b=b²a, O(n²)):                   779 ms total")
print("Property 17 (triples abc=cab, O(n³)):        22,549 ms total")
print()
print(f"Property 22 is {779/289:.1f}x slower than property 16")
print(f"Property 17 is {22549/779:.1f}x slower than property 22")

# Find slowest computations
print("\n## Slowest 10 Computations:")
slowest = sorted(results, key=lambda x: x[3], reverse=True)[:10]
for order, index, count, time_ms in slowest:
    print(f"  SmallGroup({order},{index}): {time_ms} ms (result={count})")

# Analyze by order
from collections import defaultdict
by_order = defaultdict(list)
for order, index, count, time_ms in results:
    by_order[order].append((count, time_ms))

print("\n## Average Time and Results by Order (selected orders):")
test_orders = [20, 30, 40, 48, 54, 60]
for order in test_orders:
    if order in by_order:
        times = [t[1] for t in by_order[order]]
        counts = [t[0] for t in by_order[order]]
        avg_time = sum(times) / len(times)
        avg_count = sum(counts) / len(counts)
        theoretical_n2 = order ** 2
        print(f"  Order {order}: avg {avg_time:.1f} ms, avg result={avg_count:.0f}, n²={theoretical_n2}")

# Look at interesting patterns in the counts
print("\n## Interesting Patterns in Results:")
print("-" * 80)

# Groups where count equals n (just diagonal elements a=b?)
minimal = [r for r in results if r[2] == r[0]]
print(f"\nGroups where count = n (minimal): {len(minimal)} groups")
for order, index, count, time_ms in minimal[:10]:
    print(f"  SmallGroup({order},{index}): {count} pairs")

# Groups with unusually high counts
print(f"\n## Groups with highest counts (relative to n²):")
high_ratio = sorted(results, key=lambda x: x[2]/(x[0]**2), reverse=True)[:10]
for order, index, count, time_ms in high_ratio:
    ratio = count / (order ** 2)
    print(f"  SmallGroup({order},{index}): {count} pairs ({ratio:.2%} of n²)")

# Check if it equals n^2 for abelian groups
import json
with open('group_properties_21_functions_complete.json', 'r') as f:
    groups = json.load(f)

print("\n## Verification: Abelian groups should have n² pairs")
print("-" * 80)
sample_abelian = [g for g in groups if g['is_abelian'] == 1][:10]
for g in sample_abelian:
    result_entry = next(r for r in results if r[0] == g['order'] and r[1] == g['index'])
    count = result_entry[2]
    n_squared = g['order'] ** 2
    print(f"  {g['group_id']}: {count} pairs, n²={n_squared}, match={count==n_squared}")

print("\n" + "=" * 80)
print(f"✓ O(n²) computation is very fast: only {total_time}ms for all groups!")
print("=" * 80)
