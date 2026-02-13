# Results: Extending 8 Invariants to Order 200

## Summary

The 8 O(n²) invariants from `eight_invariants.md` were tested on all **6,065 groups of order ≤ 200**.

- **4,856 unique signatures** out of 6,065 groups (80.1%)
- **686 collision clusters** involving 1,895 groups
- **Zero cross-order collisions** — every collision is within a single order
- **Collisions occur at exactly 13 orders**, all divisible by p² for some prime p

## Collision Orders

| Order | Factorization | # Groups | Collision Clusters | Groups in Collisions |
|------:|:-------------:|:--------:|:-----------------:|:--------------------:|
| 64 | 2⁶ | 267 | 30 | 66 |
| 81 | 3⁴ | 15 | 4 | 9 |
| 96 | 2⁵·3 | 231 | 4 | 8 |
| 100 | 2²5² | 16 | 1 | 2 |
| 121 | 11² | 2 | 1 | 2 |
| 128 | 2⁷ | 2328 | 463 | 1401 |
| 147 | 3·7² | 6 | 1 | 2 |
| 160 | 2⁵·5 | 238 | 6 | 12 |
| 162 | 2·3⁴ | 55 | 7 | 16 |
| 169 | 13² | 2 | 1 | 2 |
| 189 | 3³·7 | 13 | 1 | 2 |
| 192 | 2⁶·3 | 1543 | 165 | 369 |
| 200 | 2³·5² | 52 | 2 | 4 |

## Key Findings

### 1. All collisions are within-order

No group of order m ever has the same 8-invariant signature as a group of order n ≠ m. This is remarkable: the invariants always distinguish groups of different orders, even when they fail within an order.

### 2. All collision orders are divisible by p²

Every collision order n satisfies p² | n for some prime p. However, not all p²-divisible orders have collisions — many pass (e.g., 72 = 2³·3², 108 = 2²·3³, 144 = 2⁴·3²).

### 3. Powers of 2 are the worst

The 2-groups dominate:
- Order 64 (2⁶): 30 collision clusters
- Order 128 (2⁷): **463 collision clusters** — 60% of groups collide!
- Order 192 (2⁶·3): 165 collision clusters

### 4. Why prime powers fail

For a p-group (order p^k), the invariants involving exponents coprime to p collapse:
- In 2-groups: inv5 (a³=b³), invB ((ab)⁵=e), invC (a⁷=b⁷) all become trivially n
- In 3-groups: inv3 (a²=b²), inv6 (a⁴=b⁴), inv13 ((ab)²=e), invA, invB, invC all collapse
- For p²-groups with p ≥ 11: only inv1 (commutativity) is non-trivial

### 5. Pass/fail by order count threshold

| Order Range | Total Groups | Unique Sigs | % Distinguished |
|:-----------:|:------------:|:-----------:|:---------------:|
| 1–60 | 312 | 312 | 100.0% |
| 61–63 | 7 | 7 | 100.0% |
| 64 | 267 | 237 | 88.8% |
| 65–80 | 137 | 137 | 100.0% |
| 81 | 15 | 11 | 73.3% |
| 82–95 | 36 | 36 | 100.0% |
| 96 | 231 | 227 | 98.3% |
| 97–99 | 8 | 8 | 100.0% |
| 100 | 16 | 15 | 93.8% |
| 101–120 | 189 | 189 | 100.0% |
| 121 | 2 | 1 | 50.0% |
| 122–127 | 29 | 29 | 100.0% |
| 128 | 2328 | 1865 | 80.1% |
| 129–200 (excl. collision orders) | 1329 | 1329 | 100.0% |

## Orders 1–200 with no collisions that have p² | n

These orders are divisible by p² for some prime p but still pass:

63, 68, 72, 75, 76, 80, 84, 88, 90, 92, 98, 99, 104, 108, 112, 116, 117, 120, 124, 125, 126, 132, 135, 136, 140, 144, 148, 150, 152, 153, 156, 164, 168, 171, 172, 175, 176, 180, 184, 188, 196, 198

These orders have enough "mixed" structure (products of distinct primes) that the invariants with different exponents provide complementary information.

## Data

- Full invariant data: `invariants_data.csv` (6,065 rows)
- Computation script: `compute_order.g` (GAP)
- Scanning script: `run_scanning.py` (Python + GAP driver)
