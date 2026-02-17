import Mathlib

/-!
# Lower bounds for exp(1) via Taylor series

The Taylor series for exp(x) is:
  exp(x) = Σ_{n=0}^∞ x^n / n!

For exp(1) = e ≈ 2.718281828...:
  e = 1 + 1 + 1/2 + 1/6 + 1/24 + ...

Since all terms are positive, any partial sum is a lower bound.
This follows from `Real.sum_le_exp_of_nonneg`.
-/

/-- The n-th term of the Taylor series for exp(1): 1/n! -/
noncomputable def exp_one_term (n : ℕ) : ℝ := 1 / n.factorial

/-- exp(1) > 2, using 3 terms: 1 + 1 + 1/2 = 5/2 -/
theorem exp_one_gt_2 : (2 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 3
  have hsum : (∑ i ∈ Finset.range 3, (1 : ℝ)^i / i.factorial) = 5/2 := by
    norm_num [Finset.sum_range_succ]
  calc (2 : ℝ) < 5/2 := by norm_num
       _ = ∑ i ∈ Finset.range 3, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.5, using 3 terms -/
theorem exp_one_gt_2_5 : (2.5 : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 3
  have hsum : (∑ i ∈ Finset.range 3, (1 : ℝ)^i / i.factorial) = 5/2 := by
    norm_num [Finset.sum_range_succ]
  calc (2.5 : ℝ) = 5/2 := by norm_num
       _ = ∑ i ∈ Finset.range 3, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.7, using 6 terms -/
theorem exp_one_gt_2_7 : (2.7 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 6
  have hsum : (∑ i ∈ Finset.range 6, (1 : ℝ)^i / i.factorial) = 163/60 := by
    norm_num [Finset.sum_range_succ]
  calc (2.7 : ℝ) < 163/60 := by norm_num
       _ = ∑ i ∈ Finset.range 6, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.71, using 7 terms: 1957/720 ≈ 2.7180556 -/
theorem exp_one_gt_2_71 : (2.71 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 7
  have hsum : (∑ i ∈ Finset.range 7, (1 : ℝ)^i / i.factorial) = 1957/720 := by
    norm_num [Finset.sum_range_succ]
  calc (2.71 : ℝ) < 1957/720 := by norm_num
       _ = ∑ i ∈ Finset.range 7, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.718, using 8 terms: 685/252 ≈ 2.71825397 -/
theorem exp_one_gt_2_718 : (2.718 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 8
  have hsum : (∑ i ∈ Finset.range 8, (1 : ℝ)^i / i.factorial) = 685/252 := by
    norm_num [Finset.sum_range_succ]
  calc (2.718 : ℝ) < 685/252 := by norm_num
       _ = ∑ i ∈ Finset.range 8, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.7182, using 9 terms: 109601/40320 ≈ 2.71827877 -/
theorem exp_one_gt_2_7182 : (2.7182 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 9
  have hsum : (∑ i ∈ Finset.range 9, (1 : ℝ)^i / i.factorial) = 109601/40320 := by
    norm_num [Finset.sum_range_succ]
  calc (2.7182 : ℝ) < 109601/40320 := by norm_num
       _ = ∑ i ∈ Finset.range 9, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.71828, using 10 terms: 98641/36288 ≈ 2.71828153 -/
theorem exp_one_gt_2_71828 : (2.71828 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 10
  have hsum : (∑ i ∈ Finset.range 10, (1 : ℝ)^i / i.factorial) = 98641/36288 := by
    norm_num [Finset.sum_range_succ]
  calc (2.71828 : ℝ) < 98641/36288 := by norm_num
       _ = ∑ i ∈ Finset.range 10, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.718281, using 11 terms: 9864101/3628800 ≈ 2.7182818 -/
theorem exp_one_gt_2_718281 : (2.718281 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 11
  have hsum : (∑ i ∈ Finset.range 11, (1 : ℝ)^i / i.factorial) = 9864101/3628800 := by
    norm_num [Finset.sum_range_succ]
  calc (2.718281 : ℝ) < 9864101/3628800 := by norm_num
       _ = ∑ i ∈ Finset.range 11, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.7182818, using 12 terms: 13563139/4989600 ≈ 2.71828183 -/
theorem exp_one_gt_2_7182818 : (2.7182818 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 12
  have hsum : (∑ i ∈ Finset.range 12, (1 : ℝ)^i / i.factorial) = 13563139/4989600 := by
    norm_num [Finset.sum_range_succ]
  calc (2.7182818 : ℝ) < 13563139/4989600 := by norm_num
       _ = ∑ i ∈ Finset.range 12, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.71828182, using 13 terms -/
theorem exp_one_gt_2_71828182 : (2.71828182 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 13
  have hsum : (∑ i ∈ Finset.range 13, (1 : ℝ)^i / i.factorial) = 260412269/95800320 := by
    norm_num [Finset.sum_range_succ]
  calc (2.71828182 : ℝ) < 260412269/95800320 := by norm_num
       _ = ∑ i ∈ Finset.range 13, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.718281828, using 14 terms -/
theorem exp_one_gt_2_718281828 : (2.718281828 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 14
  have hsum : (∑ i ∈ Finset.range 14, (1 : ℝ)^i / i.factorial) = 8463398743/3113510400 := by
    norm_num [Finset.sum_range_succ]
  calc (2.718281828 : ℝ) < 8463398743/3113510400 := by norm_num
       _ = ∑ i ∈ Finset.range 14, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-- exp(1) > 2.7182818284, using 15 terms -/
theorem exp_one_gt_2_7182818284 : (2.7182818284 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 15
  have hsum : (∑ i ∈ Finset.range 15, (1 : ℝ)^i / i.factorial) = 47395032961/17435658240 := by
    norm_num [Finset.sum_range_succ]
  calc (2.7182818284 : ℝ) < 47395032961/17435658240 := by norm_num
       _ = ∑ i ∈ Finset.range 15, (1 : ℝ)^i / i.factorial := hsum.symm
       _ ≤ Real.exp 1 := h

/-!
## Upper bounds for exp(1)

For upper bounds, we use `Real.exp_bound` which gives:
  |exp(x) - Σ_{m<n} x^m/m!| ≤ |x|^n * (n+1)/(n! * n)  for |x| ≤ 1

For x=1: exp(1) ≤ partial_sum(n) + (n+1)/(n! * n)
-/

/-- exp(1) < 2.7182818285, using 14 terms.
    Tail bound: (n+1)/(n! * n) = 15/(14! * 14) ≈ 1.23e-11 -/
theorem exp_one_lt_2_7182818285 : Real.exp 1 < (2.7182818285 : ℝ) := by
  have h := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by norm_num : 0 < 14)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
             one_pow, Nat.factorial, Nat.cast_one, Nat.cast_ofNat,
             Nat.succ_eq_add_one] at h
  have habs := abs_sub_le_iff.mp h
  linarith

/-!
## Reusable macros for arbitrary precision

The `exp_lower_bound n` macro proves `c < Real.exp 1` for any `c` smaller than
the partial sum of n terms.

The `exp_upper_bound n` macro proves `Real.exp 1 < c` for any `c` larger than
the partial sum plus tail bound.
-/

/-- Tactic macro for proving lower bounds on exp(1) using n terms of Taylor series.
    Works for both `c < exp 1` and `c ≤ exp 1` goals. -/
macro "exp_lower_bound" n:num : tactic =>
  `(tactic|
    (have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) $n
     simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                one_pow, Nat.factorial, Nat.cast_one, Nat.cast_ofNat,
                Nat.succ_eq_add_one, Nat.add_eq, Nat.add_zero] at h
     linarith))

/-- Tactic macro for proving upper bounds on exp(1) using n terms of Taylor series + tail bound.
    Works for both `exp 1 < c` and `exp 1 ≤ c` goals. -/
macro "exp_upper_bound" n:num : tactic =>
  `(tactic|
    (have h := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by norm_num : 0 < $n)
     simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                one_pow, Nat.factorial, Nat.cast_one, Nat.cast_ofNat,
                Nat.succ_eq_add_one] at h
     have habs := abs_sub_le_iff.mp h
     linarith))

-- Examples using the lower bound macro
example : (2 : ℝ) < Real.exp 1 := by exp_lower_bound 3
example : (2.5 : ℝ) ≤ Real.exp 1 := by exp_lower_bound 3
example : (2.7 : ℝ) < Real.exp 1 := by exp_lower_bound 6
example : (2.718 : ℝ) < Real.exp 1 := by exp_lower_bound 8
example : (2.71828 : ℝ) < Real.exp 1 := by exp_lower_bound 10
example : (2.718281828 : ℝ) < Real.exp 1 := by exp_lower_bound 14
example : (2.7182818284 : ℝ) < Real.exp 1 := by exp_lower_bound 15

-- Examples using the upper bound macro
example : Real.exp 1 < (3 : ℝ) := by exp_upper_bound 3
example : Real.exp 1 < (2.72 : ℝ) := by exp_upper_bound 4
example : Real.exp 1 < (2.719 : ℝ) := by exp_upper_bound 5
example : Real.exp 1 < (2.7183 : ℝ) := by exp_upper_bound 7
example : Real.exp 1 < (2.71829 : ℝ) := by exp_upper_bound 9
example : Real.exp 1 < (2.718282 : ℝ) := by exp_upper_bound 10
example : Real.exp 1 < (2.718281829 : ℝ) := by exp_upper_bound 13
example : Real.exp 1 < (2.7182818285 : ℝ) := by exp_upper_bound 14
