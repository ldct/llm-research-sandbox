# O(n²) Invariants for Distinguishing Non-Abelian Groups

## Executive Summary

Out of **210 non-abelian groups** of order ≤ 60, we tested whether O(n²) invariants alone can distinguish all groups of the same order.

### Results

- **200 / 210 groups (95.2%)** can be distinguished using only **O(n²) + fast O(n) properties**
- **10 remaining pairs** required additional work
- **8 / 10 pairs** were distinguished by adding `num_pairs_same_order` (O(n²))
- **2 / 10 pairs** CANNOT be distinguished by any O(n²) invariant we tested (need subgroup enumeration or automorphism groups)

## The O(n²) Invariants We Tested

### Successfully Used:
1. **num_commuting_pairs**: Count of (a,b) where ab = ba
2. **num_pairs_a2b_eq_b2a**: Count of (a,b) where a²b = b²a
3. **num_pairs_same_order**: Count of (a,b) where Order(a) = Order(b) ✓ **Distinguished 8 pairs!**

### Also Tested (didn't add new distinctions):
4. ab = ba²
5. a²b² = b²a²
6. aba = bab
7. ab² = b²a
8. a³b = ba³
9. (ab)² = (ba)²
10. aba⁻¹ = bab⁻¹
11. [a,b] = [b,a]
12. IsConjugate(a,b)
13. Order(ab) = Order(ba)
14. [a,b]² = id
15. Order(a) divides Order(b)
16. (ab)³ = a³b³
17. a²b = ab²
18. Order(ab) = 2
19. a⁴ = b⁴
20. ab³ = b³a
21. a²b³ = b³a²
22. Order(a²) = Order(b²)
23. (ab)⁴ = a⁴b⁴
24. Order(ab) ≤ 4
25. <a> = <b> (same cyclic subgroup)

## Pairs That REQUIRE More Than O(n²)

### Pair 1: SmallGroup(32,23) vs SmallGroup(32,24)
Distinguished by:
- `num_subgroups`: 54 vs 46
- `num_normal_subgroups`: 38 vs 30
- `num_abelian_subgroups`: 49 vs 41
- `automorphism_group_size`: 512 vs 256

### Pair 2: SmallGroup(32,32) vs SmallGroup(32,35)
Distinguished by:
- `num_subgroups`: 34 vs 42
- `num_normal_subgroups`: 22 vs 26
- `automorphism_group_size`: 256 vs 512

## Complexity Analysis

### O(n²) Properties - FAST
- Total time for all O(n²) properties: **< 2 seconds** for all 312 groups
- Examples:
  - `num_commuting_pairs`: 289 ms
  - `num_pairs_a2b_eq_b2a`: 779 ms
  - `num_pairs_same_order`: ~1000 ms (estimated)

### Subgroup Enumeration - SLOW
- `num_subgroups`: **18,386 ms** (18.4 seconds)
- `num_abelian_subgroups`: **18,124 ms** (18.1 seconds)
- `num_cyclic_subgroups`: **18,831 ms** (18.8 seconds)

### Automorphism Groups - MEDIUM
- `automorphism_group_size`: **11,881 ms** (11.9 seconds)

## Conclusion

**For 95.2% of non-abelian groups**, the following O(n²) invariants are sufficient:

1. `num_commuting_pairs` (ab = ba)
2. `num_pairs_a2b_eq_b2a` (a²b = b²a)
3. `num_pairs_same_order` (Order(a) = Order(b))

Plus fast O(n) properties:
- exponent
- center_size
- derived_subgroup_size
- num_conjugacy_classes
- num_elements_order_2
- nilpotency_class
- derived_length
- min_num_generators
- fitting_subgroup_size

**For the remaining 4.8%**, we need more expensive operations like:
- Enumerating all subgroups (O(?) complexity, very expensive)
- Computing automorphism groups (O(?) complexity, expensive)

## Total Computation Time

- **O(n²) + fast properties**: ~2-3 seconds for all 312 groups
- **Including subgroup enumeration**: ~110 seconds for all 312 groups (50x slower)

## Pairs Requiring Each Level

| Complexity Level | Pairs Requiring | Percentage |
|-----------------|-----------------|------------|
| O(n²) only | 208/210 | 99.0% |
| O(n²) + subgroups/aut | 210/210 | 100% |

