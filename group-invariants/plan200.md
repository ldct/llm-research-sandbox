# Plan: Disambiguate All Groups of Order ≤ 200 with Pair-Counting Invariants

## Current State

8 invariants distinguish 4,856 / 6,065 groups. 686 collision clusters across 13 orders:

| Order | Factorization | Clusters | Root Cause |
|------:|:---:|---:|:---|
| 64 | 2⁶ | 30 | odd-exponent invariants degenerate |
| 81 | 3⁴ | 4 | only inv1, inv5 vary |
| 96 | 2⁵·3 | 4 | partial 2-group degeneracy |
| 100 | 2²·5² | 1 | all 8 identical |
| 121 | 11² | 1 | abelian p² vs p×p (all 8 identical) |
| 128 | 2⁷ | 463 | massive 2-group degeneracy |
| 147 | 3·7² | 1 | all 8 identical |
| 160 | 2⁵·5 | 6 | partial 2-group degeneracy |
| 162 | 2·3⁴ | 7 | partial 3-group degeneracy |
| 169 | 13² | 1 | abelian p² vs p×p (all 8 identical) |
| 189 | 3³·7 | 1 | all 8 identical |
| 192 | 2⁶·3 | 165 | partial 2-group degeneracy |
| 200 | 2³·5² | 2 | partial degeneracy |

## Why the Current 8 Fail

The 8 invariants use exponents {1,2,3,4,5,7}. For a p-group, a^k with gcd(k,p)=1 is a bijection, so `#{(a,b): a^k = b^k}` = n trivially. This kills:
- 2-groups: inv5(³), invB(⁵), invC(⁷) all → n
- 3-groups: inv3(²), inv6(⁴), inv13(²), invA(²), invB(⁵), invC(⁷) all → n
- p²-groups for p≥11: everything except inv1 → n

## Strategy

Add new pair-counting invariants in three targeted phases.

### Phase 1: Prime-Power Exponents

For p-groups, we need exponents that are powers of p.

**New invariants:**
- `a^p = b^p` for p ∈ {2, 3, 5, 7, 11, 13} — use p matching the group's prime
- `a^(p²) = b^(p²)` for small p
- `(ab)^p = e` for p ∈ {2, 3, 5, 7, 11, 13}

This directly fixes:
- 121 = 11²: `a^11 = b^11` distinguishes C₁₂₁ vs C₁₁×C₁₁
- 169 = 13²: `a^13 = b^13` distinguishes C₁₆₉ vs C₁₃×C₁₃
- 81 = 3⁴: `a^9 = b^9`, `a^27 = b^27` add new dimensions
- 64/128: `a^8 = b^8`, `a^16 = b^16` add new dimensions

**Implementation:** One GAP script parameterized by a list of exponents. Compute `#{(a,b): a^k = b^k}` and `#{(a,b): (ab)^k = e}` for each k in a candidate set.

**Candidate exponent set:** {2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27}

This covers p and p² for p ≤ 13, plus 8=2³ and 16=2⁴ and 27=3³ for the deep 2/3-groups.

### Phase 2: Mixed-Operation Invariants

For groups with identical same-power counts, try invariants mixing two elements asymmetrically:

- `ab = ba²` — tests how squaring interacts with conjugation
- `ab² = b²a` — does b² centralize a?
- `a²b = ba²` — does a² commute with b?
- `(ab)² = a²b²` — abelian-like squaring of products
- `a·b·a = b·a·b` — braid relation
- `[a,b]² = e` — commutator is an involution
- `[a,b] = [a²,b]` — stability of commutator under squaring

These are all O(n²). They test structural relationships that same-power invariants miss.

**Prioritize:** `(ab)² = a²b²` and `a²b = ba²` first — these encode how the squaring map interacts with group multiplication, which varies among 2-groups.

### Phase 3: Targeted Residual Cleanup

After phases 1–2, identify remaining collisions and design invariants specifically for them:

- For each remaining collision pair, test a battery of candidate invariants to find one that distinguishes
- Candidates: `a^i·b^j = b^k·a^l` for small i,j,k,l; `(a^i·b^j)^k = e`; `a^i·b·a^j = b·a^k·b`
- Keep only invariants that break at least one collision

## Implementation Plan

### Step 1: Compute Phase 1 invariants for collision orders only

Write `compute_extended.g` that takes an order and computes all candidate invariants. Run only on the 13 collision orders (not all 200) since non-collision orders don't need new invariants.

```
For each collision order n:
  For each SmallGroup(n, k):
    Compute #{(a,b): a^e = b^e} for e in {8, 9, 11, 13, 16, 25, 27}
    Compute #{(a,b): (ab)^e = e} for e in {3, 4, 7, 8, 9, 11, 13}
```

Output: `extended_invariants.csv`

### Step 2: Greedy invariant selection

Write `select_invariants.py`:
1. Load original 8 invariants + new candidates
2. Greedily pick the new invariant that resolves the most remaining collisions
3. Repeat until all collisions resolved or candidates exhausted
4. Report minimal set

### Step 3: Compute Phase 2 invariants for remaining collisions

Only compute the mixed-operation invariants for groups still in collision after Phase 1.

### Step 4: Compute winning set for ALL orders 1–200

Once a working set is identified from collision orders, compute it for all 6,065 groups and verify zero collisions.

### Step 5: Record results

Update `more_groups_results.md` with the final invariant set and full data table.

## Estimated Cost

- Phase 1: ~14 new invariants × 13 orders. Order 128 (2328 groups × 16384 pairs × 14 invariants) is the bottleneck — ~530M operations. Feasible in GAP in ~10 minutes.
- Phase 2: Only on residual collisions, likely small.
- Phase 3: Very targeted, minimal cost.

## Success Criterion

All 6,065 groups of order ≤ 200 have unique signatures using a set of O(n²) pair-counting invariants. Ideally ≤ 15 invariants total.
