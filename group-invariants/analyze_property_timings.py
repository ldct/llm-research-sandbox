#!/usr/bin/env python3

property_names = [
    "1. Exponent",
    "2. Center Size",
    "3. Derived Subgroup Size",
    "4. Number of Conjugacy Classes",
    "5. Number of Subgroups",
    "6. Number of Normal Subgroups",
    "7. Number of Maximal Subgroups",
    "8. Frattini Subgroup Size",
    "9. Number of Cyclic Subgroups",
    "10. Number of Abelian Subgroups",
    "11. Nilpotency Class",
    "12. Derived Length",
    "13. Number of Elements of Order 2",
    "14. Automorphism Group Size",
    "15. Minimum Number of Generators",
    "16. Number of Commuting Pairs",
    "17. Number of Triples abc = cab",
    "18. Is Abelian",
    "19. Is Cyclic",
    "20. Fitting Subgroup Size",
    "21. Number of Characteristic Subgroups"
]

# Read timing data
timings = []
with open('property_timings.txt', 'r') as f:
    for line in f:
        parts = line.strip().split(',')
        if len(parts) == 2:
            prop_num, time_ms = int(parts[0]), int(parts[1])
            timings.append((prop_num, property_names[prop_num - 1], time_ms))

# Sort by time
timings_sorted = sorted(timings, key=lambda x: x[2], reverse=True)

print("=" * 80)
print("Property Computation Time Analysis (312 groups, order ≤ 60)")
print("=" * 80)

total_time = sum(t[2] for t in timings)
print(f"\nTotal time for all 21 properties: {total_time} ms ({total_time/1000:.2f} seconds)")
print(f"Average per property: {total_time/21:.0f} ms")

print("\n## SLOWEST Properties:")
print("-" * 80)
for i, (num, name, time_ms) in enumerate(timings_sorted[:10], 1):
    pct = 100 * time_ms / total_time
    print(f"{i:2}. {name:45} {time_ms:6} ms ({pct:5.1f}%)")

print("\n## FASTEST Properties:")
print("-" * 80)
for i, (num, name, time_ms) in enumerate(timings_sorted[-10:][::-1], 1):
    pct = 100 * time_ms / total_time
    print(f"{i:2}. {name:45} {time_ms:6} ms ({pct:5.1f}%)")

print("\n## Categorization by Complexity:")
print("-" * 80)

slow = [t for t in timings if t[2] > 5000]
medium = [t for t in timings if 1000 <= t[2] <= 5000]
fast = [t for t in timings if t[2] < 1000]

print(f"\nSlow (> 5 seconds total):")
for num, name, time_ms in sorted(slow, key=lambda x: x[2], reverse=True):
    print(f"  {name:45} {time_ms:6} ms")

print(f"\nMedium (1-5 seconds total):")
for num, name, time_ms in sorted(medium, key=lambda x: x[2], reverse=True):
    print(f"  {name:45} {time_ms:6} ms")

print(f"\nFast (< 1 second total):")
for num, name, time_ms in sorted(fast, key=lambda x: x[2], reverse=True):
    print(f"  {name:45} {time_ms:6} ms")

print("\n## Top 5 Most Expensive (with percentage of total):")
print("-" * 80)
top5_time = sum(t[2] for t in timings_sorted[:5])
print(f"Top 5 properties account for {top5_time} ms ({100*top5_time/total_time:.1f}% of total time)\n")
for i, (num, name, time_ms) in enumerate(timings_sorted[:5], 1):
    pct = 100 * time_ms / total_time
    print(f"{i}. {name}")
    print(f"   {time_ms} ms ({pct:.1f}% of total)")
    print()

print("=" * 80)
