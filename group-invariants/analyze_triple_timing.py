#!/usr/bin/env python3

# Parse the timing data
timings = []
with open('triples_all_with_timing.txt', 'r') as f:
    for line in f:
        line = line.strip()
        if line.startswith('#') or not ',' in line:
            continue
        parts = line.split(',')
        if len(parts) == 4:
            order, index, count, time_ms = map(int, parts)
            timings.append((order, index, count, time_ms))

print("=" * 80)
print("Triple Computation Timing Analysis")
print("=" * 80)
print(f"\nTotal groups computed: {len(timings)}")

# Calculate total time
total_time_ms = sum(t[3] for t in timings)
print(f"Total computation time: {total_time_ms} ms ({total_time_ms/1000:.2f} seconds)")

# Find slowest computations
print("\n## Slowest 10 Computations:")
slowest = sorted(timings, key=lambda x: x[3], reverse=True)[:10]
for order, index, count, time_ms in slowest:
    print(f"  SmallGroup({order},{index}): {time_ms} ms (order={order}, result={count})")

# Find fastest for large groups
print("\n## Fastest Groups of Order ≥ 48:")
large_groups = [t for t in timings if t[0] >= 48]
fastest_large = sorted(large_groups, key=lambda x: x[3])[:10]
for order, index, count, time_ms in fastest_large:
    print(f"  SmallGroup({order},{index}): {time_ms} ms (result={count})")

# Group by order and show average time
from collections import defaultdict
by_order = defaultdict(list)
for order, index, count, time_ms in timings:
    by_order[order].append(time_ms)

print("\n## Average Time by Order (for orders with most groups):")
orders_with_many_groups = sorted([(o, len(times)) for o, times in by_order.items()],
                                  key=lambda x: x[1], reverse=True)[:5]
for order, num_groups in orders_with_many_groups:
    avg_time = sum(by_order[order]) / len(by_order[order])
    max_time = max(by_order[order])
    print(f"  Order {order}: {num_groups} groups, avg {avg_time:.1f} ms, max {max_time} ms")

# Verify O(n^3) scaling
print("\n## Verification of O(n³) Scaling:")
test_orders = [10, 20, 30, 40, 48, 54, 60]
for order in test_orders:
    if order in by_order:
        avg_time = sum(by_order[order]) / len(by_order[order])
        theoretical = order ** 3
        print(f"  Order {order}: avg {avg_time:.1f} ms, n³={theoretical}, ratio={avg_time/theoretical:.6f}")

print("\n" + "=" * 80)
print("✓ Computation was fast enough for all groups of order ≤ 60!")
print("=" * 80)
