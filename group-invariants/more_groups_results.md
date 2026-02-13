# Results: Extending 8 Invariants Beyond Order 60

## Summary

The 8 O(n²) invariants from `eight_invariants.md` **fail at order 64**.

- **Orders 1–63**: All 319 groups have unique signatures ✓
- **Order 64**: 30 collision clusters among the 267 groups ✗

## Statistics (Orders 1–64)

| Metric | Value |
|--------|-------|
| Total groups | 586 |
| Unique signatures | 550 |
| Collision clusters | 30 |
| Groups in collisions | 66 |
| Uniquely identified | 520 (88.7%) |
| Cross-order collisions | 0 |

All collisions are **within order 64** — no group of order ≤ 63 collides with any order-64 group.

## Why Order 64?

Order 64 = 2⁶ is a power of 2, and 2-groups have notoriously many non-isomorphic groups that are structurally similar. The 267 groups of order 64 include many groups with:
- Identical exponents (all elements have order dividing some 2^k)
- Same number of elements of each order
- Same commutativity structure

Since all 8 invariants use exponents 1–7, and for 2-groups a^k only depends on k mod (order of a) which divides 64, many invariants degenerate (inv5, invB, invC all collapse when the group has exponent dividing 4).

## All 30 Collision Clusters

| # | Groups | Signature (inv1,inv3,inv5,inv6,inv13,invA,invB,invC) |
|---|--------|------------------------------------------------------|
| 1 | (64,2), (64,26) | (4096, 256, 64, 1024, 256, 256, 64, 64) |
| 2 | (64,3), (64,27) | (2560, 256, 64, 1024, 256, 256, 64, 64) |
| 3 | (64,13), (64,14) | (1216, 704, 64, 1536, 256, 256, 64, 64) |
| 4 | (64,17), (64,84) | (2560, 512, 64, 2048, 512, 512, 64, 64) |
| 5 | (64,18), (64,19) | (1408, 512, 64, 2560, 512, 320, 64, 64) |
| 6 | (64,20), (64,22) | (1792, 512, 64, 2560, 512, 384, 64, 64) |
| 7 | (64,21), (64,106) | (1792, 768, 64, 2560, 512, 512, 64, 64) |
| 8 | (64,61), (64,66) | (1792, 1024, 64, 4096, 1024, 768, 64, 64) |
| 9 | (64,63), (64,68) | (1792, 768, 64, 4096, 512, 512, 64, 64) |
| 10 | (64,65), (64,208) | (1792, 1280, 64, 4096, 512, 512, 64, 64) |
| 11 | (64,70), (64,72) | (1792, 1024, 64, 4096, 512, 512, 64, 64) |
| 12 | (64,74), (64,77), (64,80) | (1408, 1024, 64, 4096, 1024, 640, 64, 64) |
| 13 | (64,85), (64,86), (64,112) | (2560, 512, 64, 2048, 512, 384, 64, 64) |
| 14 | (64,97), (64,101) | (1792, 768, 64, 2560, 1024, 512, 64, 64) |
| 15 | (64,100), (64,109) | (1408, 896, 64, 2560, 512, 384, 64, 64) |
| 16 | (64,102), (64,146) | (1408, 768, 64, 2560, 1024, 448, 64, 64) |
| 17 | (64,104), (64,105) | (1792, 768, 64, 2048, 512, 384, 64, 64) |
| 18 | (64,108), (64,110) | (1792, 768, 64, 2560, 512, 384, 64, 64) |
| 19 | (64,129), (64,133), (64,161) | (1216, 960, 64, 2560, 1024, 448, 64, 64) |
| 20 | (64,137), (64,178) | (1024, 1024, 64, 2560, 768, 320, 64, 64) |
| 21 | (64,142), (64,157), (64,159) | (1216, 832, 64, 2560, 768, 384, 64, 64) |
| 22 | (64,143), (64,158) | (1216, 1088, 64, 2560, 256, 256, 64, 64) |
| 23 | (64,156), (64,160) | (1216, 832, 64, 2560, 256, 256, 64, 64) |
| 24 | (64,167), (64,173), (64,176) | (1408, 896, 64, 2560, 1280, 384, 64, 64) |
| 25 | (64,168), (64,179), (64,180) | (1408, 896, 64, 2560, 256, 256, 64, 64) |
| 26 | (64,175), (64,181) | (1408, 1408, 64, 2560, 256, 256, 64, 64) |
| 27 | (64,206), (64,207) | (1792, 1280, 64, 4096, 1536, 768, 64, 64) |
| 28 | (64,236), (64,240) | (1600, 1088, 64, 4096, 1280, 512, 64, 64) |
| 29 | (64,241), (64,242) | (1216, 1216, 64, 4096, 1792, 640, 64, 64) |
| 30 | (64,256), (64,258) | (1408, 1280, 64, 2560, 1536, 576, 64, 64) |

## Key Observation

For all colliding groups, **inv5 = inv7 = invB = invC = 64** (= n). This means:
- a³ = b³ iff a = b (inv5 = n) → group has no non-trivial 3rd-power coincidences
- Similarly for 5th and 7th powers

This happens because 2-groups have no elements of order 3, 5, or 7, so a^k = a^(k mod order(a)) where order(a) is a power of 2. The invariants involving odd primes (3, 5, 7) all degenerate to just counting identity pairs.

Only **inv1** (commutativity), **inv3** (same square), **inv6** (same 4th power), **inv13** ((ab)² = e), and **invA** (commuting involution pairs) carry information for 2-groups.

Effectively only 5 of the 8 invariants provide useful information for order-64 groups, which is insufficient to distinguish all 267 groups.

## Order-by-Order Log (61–64)

```
Order 61: 1 group, cumulative 313/313 — PASS
Order 62: 2 groups, cumulative 315/315 — PASS  
Order 63: 4 groups, cumulative 319/319 — PASS
Order 64: 267 groups, cumulative 586 — FAIL (30 collision clusters, 66 groups involved)
```

## Data

Full invariant data for all 586 groups is in `invariants_data.csv`.
