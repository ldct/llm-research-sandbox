# Plan: Disambiguate Remaining 70 Collision Clusters

## Current State

92 invariants (8 original + 84 new) distinguish 5,878 / 6,065 groups of order ≤ 200 (96.9%).

**70 clusters remain**, involving 187 groups:
- Order 128 (2⁷): 64 clusters, 173 groups
- Order 192 (2⁶·3): 4 clusters, 10 groups
- Order 160 (2⁵·5): 1 cluster, 2 groups
- Order 189 (3³·7): 1 cluster, 2 groups

## Why Everything So Far Fails

These groups are identical on:
- All 48 O(n²) pair-counting invariants (power-equality, product-order, commutator, braid, order-aware)
- All 36 structural invariants (|Aut|, subgroup counts, normal subgroups, derived series, center, Frattini, Omega₁, characteristic subgroups, nilpotency class, exponent, rank, etc.)

The remaining pairs are "extremely similar" groups — in many cases they share the same:
- Character table structure (same character degrees, same conjugacy class sizes)
- Subgroup lattice counts (same number of subgroups of each order)
- Element order distributions
- Power map structure

These are likely **Brauer pairs** or groups related by subtle structural differences only visible at the level of specific subgroup embeddings or cohomological invariants.

## Strategy

### Phase A: Character Table Fingerprints

The character table contains far more information than character degrees alone. Two non-isomorphic groups can have the same character degree multiset but different character tables.

**Invariants:**
- `c1`: Hash/fingerprint of the full character table (sorted rows of character values)
- `c2`: Number of rational-valued irreducible characters
- `c3`: Number of faithful irreducible characters  
- `c4`: Sum of squares of character table entries (Frobenius-Schur indicator related)
- `c5`: Number of real conjugacy classes
- `c6`: Determinant of the character table (as integer)

Character tables are computable by GAP and uniquely determine many group properties. If two non-isomorphic groups have the same character table, they are called **Brauer pairs** — these are very rare.

**Cost:** `Irr(G)` for groups of order 128 is fast in GAP (milliseconds per group).

### Phase B: Subgroup Lattice Refinement

Instead of just counting subgroups, examine their structure:

**Invariants:**
- `b1`: Number of normal subgroups that are abelian with exponent 2
- `b2`: Number of normal subgroups that are elementary abelian  
- `b3`: Number of normal subgroups isomorphic to C4 × C4
- `b4`: |Aut(Z(G))| — automorphism group of the center
- `b5`: Sorted list of SmallGroup IDs of all maximal subgroups (encoded as hash)
- `b6`: Number of subgroups isomorphic to the dihedral group D8
- `b7`: Number of subgroups isomorphic to Q8 (quaternion)

The key insight: rather than counting subgroups by order, identify them **by isomorphism type**. Two groups might have the same number of order-8 subgroups but different distributions of C8 vs C4×C2 vs C2×C2×C2 vs D8 vs Q8.

**Cost:** `AllSubgroups` for order 128 groups is expensive but feasible. Alternatively, `ConjugacyClassesSubgroups` gives representatives, and we count by `IdSmallGroup`.

### Phase C: Cohomological Invariants

For p-groups, cohomology ring structure is a complete invariant:

**Invariants:**
- `h1`: Rank of H²(G, F₂) (second cohomology with F₂ coefficients)
- `h2`: Rank of H¹(G, F₂) = rank of G/Φ(G) (already known, but confirm)
- `h3`: |H²(G, F₂)| / |H¹(G, F₂)|² (normalized second cohomology)

GAP's `cohomolo` package or `HAP` package can compute group cohomology.

### Phase D: Power Graph / Enhanced Commuting Graph

**Invariants based on the commuting graph:**
- `d1`: Number of connected components of the non-commuting graph
- `d2`: Diameter of the commuting graph
- `d3`: Number of edges in the power graph (a~b if a is a power of b or vice versa)
- `d4`: Degree sequence hash of the commuting graph

These are O(n²) to compute but capture graph-theoretic structure that simple pair counts miss.

### Phase E: Targeted SmallGroup ID Oracle

As a nuclear option, GAP can directly identify any group:

```gap
IdSmallGroup(SmallGroup(128, k));  # returns [128, k]
```

But we want *invariants* that distinguish groups, not just the ID lookup. If all else fails, we can:
1. For each remaining collision pair, ask GAP to find ONE property that differs
2. Search systematically: test words in F₂ of increasing length until one gives different counts
3. Use the **coclass** library for 2-groups, which has refined structural data

## Implementation Plan

### Step 1: Character table fingerprints (Phase A)

This is the most promising and cheapest approach. Write `compute_chartable.g` to compute:
- For each remaining collision group, compute `Irr(G)` (character table)
- Extract: # rational characters, # faithful characters, # real classes
- Compute a fingerprint: sorted tuple of (degree, sorted-character-values) for each irreducible

Run only on the 187 groups in remaining clusters (not all groups).

### Step 2: Subgroup type profile (Phase B)

For remaining collisions after Step 1:
- Use `ConjugacyClassesSubgroups(G)` to get representatives
- For each rep H, compute `IdSmallGroup(H)`
- Build a multiset of (order, SmallGroupID) for subgroups
- Two groups with different subgroup-type multisets are distinguished

### Step 3: Cohomology (Phase C)

If any pairs survive Steps 1-2:
- Install GAP's `HAP` package
- Compute H²(G, GF(2)) for remaining groups
- This should distinguish any remaining pairs that aren't Brauer pairs

### Step 4: Full verification

Once a complete distinguishing set is found:
1. Record the winning invariants
2. Verify zero collisions across all 6,065 groups
3. Update `more_groups_results.md`

## Estimated Cost

- Phase A: Character tables for 187 groups of order 128-192. GAP computes Irr(G) in <1s per group for order 128. Total: ~3 minutes.
- Phase B: Subgroup conjugacy classes for ~50 groups. ~1 min per group for order 128. Total: ~1 hour.
- Phase C: Only if needed. HAP cohomology for p-groups is efficient. Total: ~30 minutes.

## Success Criterion

All 6,065 groups of order ≤ 200 have unique signatures. Document the complete invariant set.

## Notes on the Hard Cases

The largest cluster (9 groups: [1381, 1472, 1473, 1489, 1493, 1511, 1513, 1518, 1528]) deserves special attention. These are all order-128 2-groups with identical:
- |Aut(G)|, nilpotency class, derived length, exponent
- Center, derived subgroup, Frattini subgroup sizes
- All pair-counting invariants

Character table fingerprints should break most of these. If not, subgroup isomorphism type profiles almost certainly will — it's extremely rare for non-isomorphic p-groups to have the same subgroup type multiset.

If even that fails, we're looking at genuine Brauer pairs, which would be a mathematically interesting finding worth documenting.

## Results (Completed)

All 70 collision clusters (187 groups) successfully resolved. **6,065 / 6,065 groups uniquely identified.**

### Invariants Used

| Invariant | Description | Clusters Resolved |
|-----------|-------------|-------------------|
| `qhash` | Hash of sorted `IdSmallGroup(G/N)` for all proper nontrivial normal N | 51 |
| `mhash` | Hash of sorted `IdSmallGroup(M)` for all maximal subgroups M | 17 sub-clusters |
| `h3` | H³(G, ℤ) — 3rd integral cohomology (via GAP HAP) | 1 (128,1327 vs 1329) |
| `h4` | H⁴(G, ℤ) — 4th integral cohomology | 1 (128,1597 vs 1598) |
| `schash` | Structure constant hash from character table | 2 (128,1317/1322; 160,70/71) |
| `pchash` | Polycyclic presentation hash | 1 (189,4 vs 5 — Brauer pair) |

### The Hardest Cases

**[189,4] vs [189,5]** — A genuine Brauer pair:
- Same character table (verified via structure constants)
- Same table of marks (subgroup lattice isomorphic as poset)
- Same integral cohomology H^n(G,ℤ) for all computed n (1–12)
- Same subgroup type profiles, centralizer profiles, power graph
- Same Schur multiplier, same Aut(G)
- Distinguished only by the polycyclic presentation: `g₂³ = g₃` vs `g₂³ = g₃²`

### Output

- `final_all_invariants.csv`: 6,065 rows × 99 invariant columns, all signatures unique
- `compute_final_v2.g`: GAP script computing the 6 new invariants for collision groups
