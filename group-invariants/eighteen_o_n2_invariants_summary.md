# Distinguishing Non-Abelian Groups with 18 O(n²) Invariants

## Summary

Using **18 truly O(n²) invariants** (explicit pair enumeration without expensive GAP builtins), we can distinguish **96.7% of non-abelian groups** of order ≤ 60.

### Progressive Improvement

| Invariants | Indist. Sets | Distinguishable | Percentage |
|------------|--------------|-----------------|------------|
| 4 O(n²) invariants | 46 sets | 145/210 | 69.0% |
| 12 O(n²) invariants | 39 sets | 166/210 | 79.0% |
| **18 O(n²) invariants** | **7 sets** | **203/210** | **96.7%** |

**Improvement**: +27.7 percentage points from baseline

**Computation time**: ~3 seconds for all 312 groups (vs. ~110 seconds with expensive builtin operations)

## The 18 Invariants

### First Batch (4 invariants)

1. **inv1_ab_eq_ba**: Count of pairs (a,b) where ab = ba (commutativity)
2. **inv2_a2b_eq_b2a**: Count of pairs (a,b) where a²b = b²a (square compatibility)
3. **inv3_a2_eq_b2**: Count of pairs (a,b) where a² = b² (same square)
4. **inv4_conj_is_inv**: Count of pairs (a,b) where a⁻¹ba = b⁻¹ (conjugate equals inverse)

### Second Batch (+8 invariants, total 12)

5. **inv5_a3_eq_b3**: Count of pairs (a,b) where a³ = b³
6. **inv6_a4_eq_b4**: Count of pairs (a,b) where a⁴ = b⁴
7. **inv7_ab3_eq_b3a**: Count of pairs (a,b) where ab³ = b³a
8. **inv8_a3b_eq_ba3**: Count of pairs (a,b) where a³b = ba³
9. **inv9_a2b2_eq_b2a2**: Count of pairs (a,b) where a²b² = b²a²
10. **inv10_ord_ab_eq_3**: Count of pairs (a,b) where Order(ab) = 3
11. **inv11_ab2_eq_ba2**: Count of pairs (a,b) where (ab)² = (ba)²
12. **inv12_ab3_eq_ba3**: Count of pairs (a,b) where (ab)³ = (ba)³

### Third Batch (+6 invariants, total 18)

13. **inv13_ab_involution**: Count of pairs (a,b) where (ab)⁻¹ = ab (ab is an involution)
14. **inv14_aba_eq_bab**: Count of pairs (a,b) where aba = bab (braid relation)
15. **inv15_aba1_eq_bab1**: Count of pairs (a,b) where aba⁻¹ = bab⁻¹
16. **inv16_a2b3_eq_b3a2**: Count of pairs (a,b) where a²b³ = b³a²
17. **inv17_ab4_eq_ba4**: Count of pairs (a,b) where (ab)⁴ = (ba)⁴
18. **inv18_bab1_eq_a2**: Count of pairs (a,b) where bab⁻¹ = a² (conjugate gives square)

## Remaining Indistinguishable Groups

Only **7 pairs** of non-abelian groups cannot be distinguished by these 18 invariants:

1. **SmallGroup(32,2), SmallGroup(32,24)**
2. **SmallGroup(32,13), SmallGroup(32,15)**
3. **SmallGroup(32,27), SmallGroup(32,34)**
4. **SmallGroup(32,30), SmallGroup(32,31)**
5. **SmallGroup(32,37), SmallGroup(32,38)**
6. **SmallGroup(32,40), SmallGroup(32,42)**
7. **SmallGroup(50,1), SmallGroup(50,4)**

Note: 6 out of 7 remaining pairs are groups of order 32.

## Comparison with Expensive Methods

Using GAP's builtin subgroup enumeration functions (which are much more expensive), we can achieve higher distinguishability:

- **O(n²) invariants only**: 96.7% (203/210) - **~3 seconds**
- **With expensive builtins**: 98.6% (207/210) - **~110 seconds**

The O(n²) approach provides **36x speedup** with only a 1.9 percentage point decrease in distinguishability.

## Algorithmic Complexity

All 18 invariants are **truly O(n²)** - they use explicit double loops over group elements:

```gap
for a in elements do
    for b in elements do
        if [condition] then
            count := count + 1;
        fi;
    od;
od;
```

No expensive GAP builtin operations like:
- `Subgroups(G)` - expensive subgroup enumeration
- `ConjugacyClasses(G)` - conjugacy class computation
- `AutomorphismGroup(G)` - automorphism group computation

This makes the method practical for larger groups where subgroup enumeration becomes prohibitively expensive.

## Files

- `four_o_n2_invariants.json` - Original 4 invariants for all 312 groups
- `additional_8_invariants.txt` - Next 8 invariants (raw GAP output)
- `additional_6_invariants.txt` - Final 6 invariants (raw GAP output)
- `check_all_18_invariants.py` - Python script to analyze all 18 invariants
- `test_additional_o_n2.gap` - GAP script for invariants 5-12
- `test_more_creative_o_n2_v2.gap` - GAP script for invariants 13-18

## Conclusion

This investigation demonstrates that:

1. **Simple O(n²) invariants are surprisingly powerful** - achieving 96.7% distinguishability without expensive operations
2. **Incremental approach works** - systematically adding invariants improved results from 69% → 79% → 96.7%
3. **Order 32 groups are hard** - 6 of the 7 remaining indistinguishable pairs have order 32
4. **Practical performance** - 36x faster than expensive builtin methods with minimal accuracy loss

Future work could explore additional O(n²) invariants to tackle the remaining 7 pairs, or investigate why order 32 groups are particularly challenging for pair-counting invariants.
