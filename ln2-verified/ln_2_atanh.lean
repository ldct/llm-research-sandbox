/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

Lower bound on ln(2) using the fast-converging series:
  ln(z) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * ((z-1)/(z+1))^(2k+1)

For z = 2, this becomes:
  ln(2) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * (1/3)^(2k+1)

This is the series expansion of 2·atanh((z-1)/(z+1)), using the identity
ln(z) = 2·atanh((z-1)/(z+1)) for z > 0.

Convergence rate: Each term provides approximately log₁₀(9) ≈ 0.95 decimal
digits of precision, since the exponent increases by 2 and (1/3)^2 = 1/9.
Thus only 6 terms are needed to establish 0.693147 < ln(2).
-/
import Mathlib

/-! ## Main series representation theorem -/

/-- The series representation of ln(z) for positive z -/
theorem log_eq_hasSum_atanh {z : ℝ} (hz : 0 < z) :
    HasSum (fun k : ℕ => 2 * (1 / (2 * k + 1)) * ((z - 1) / (z + 1)) ^ (2 * k + 1)) (Real.log z) := by
  set x := (z - 1) / (z + 1) with hx_def
  have habs : |x| < 1 := by
    rw [hx_def, abs_div]
    have hz1 : 0 < z + 1 := by linarith
    rw [abs_of_pos hz1]
    have h1 : |z - 1| < z + 1 := by
      by_cases h : 1 ≤ z
      · rw [abs_of_nonneg (by linarith : 0 ≤ z - 1)]; linarith
      · push_neg at h
        rw [abs_of_neg (by linarith : z - 1 < 0)]; linarith
    calc |z - 1| / (z + 1) < (z + 1) / (z + 1) := div_lt_div_of_pos_right h1 hz1
      _ = 1 := div_self (ne_of_gt hz1)
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hz1_ne : z + 1 ≠ 0 := by linarith
  have one_plus_x : 1 + x = 2 * z / (z + 1) := by rw [hx_def]; field_simp; ring
  have one_minus_x : 1 - x = 2 / (z + 1) := by rw [hx_def]; field_simp; ring
  have h2z_pos : 0 < 2 * z := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  rw [one_plus_x, one_minus_x] at hs
  rw [Real.log_div (ne_of_gt h2z_pos) hz1_ne] at hs
  rw [Real.log_div (ne_of_gt h2_pos) hz1_ne] at hs
  convert hs using 1
  rw [Real.log_mul (ne_of_gt h2_pos) (ne_of_gt hz)]
  ring

theorem summable_log_atanh {z : ℝ} (hz : 0 < z) :
    Summable (fun k : ℕ => 2 * (1 / (2 * k + 1)) * ((z - 1) / (z + 1)) ^ (2 * k + 1)) :=
  (log_eq_hasSum_atanh hz).summable

/-! ## Specialization to z = 2 -/

/-- The k-th term of the series for ln(2): 2 * (1/(2k+1)) * (1/3)^(2k+1) -/
noncomputable def log_two_term (k : ℕ) : ℝ := 2 * (1 / (2 * k + 1)) * (1/3 : ℝ) ^ (2 * k + 1)

theorem summable_log_two_series : Summable log_two_term := by
  have h := summable_log_atanh (by norm_num : (0:ℝ) < 2)
  convert h using 1
  ext k
  simp only [log_two_term]
  norm_num

theorem log_two_eq_tsum : Real.log 2 = ∑' (k : ℕ), log_two_term k := by
  have h := log_eq_hasSum_atanh (by norm_num : (0:ℝ) < 2)
  have heq : ∀ k, 2 * (1 / (2 * ↑k + 1)) * ((2 - 1) / (2 + 1)) ^ (2 * k + 1) = log_two_term k := by
    intro k; simp only [log_two_term]; norm_num
  simp only [heq] at h
  exact h.tsum_eq.symm

/-! ## Lower bound theorem -/

/-- Lower bound on log 2 from first 6 terms of the series 2Σ (1/(2k+1))(1/3)^(2k+1):
    0.693147 < ln(2)

    The partial sum of 6 terms equals 15757912/22733865 ≈ 0.6931471806,
    which exceeds 0.693147. Since all remaining terms are positive, the full
    series (which equals ln(2)) is strictly greater than the partial sum.

-/
theorem log_2_gt : (0.693147 : ℝ) < Real.log 2 := by
  rw [log_two_eq_tsum]
  -- Partial sum of 6 terms: 15757912/22733865 > 0.693147
  have hpartial : ∑ k ∈ Finset.range 6, log_two_term k = 15757912 / 22733865 := by
    simp only [log_two_term]
    norm_num
  have hbound : (0.693147 : ℝ) < 15757912 / 22733865 := by norm_num
  calc (0.693147 : ℝ)
      < 15757912 / 22733865 := hbound
    _ = ∑ k ∈ Finset.range 6, log_two_term k := hpartial.symm
    _ < ∑' (k : ℕ), log_two_term k := by
        have hdecomp := summable_log_two_series.sum_add_tsum_compl (s := Finset.range 6)
        rw [← hdecomp]
        set S := (↑(Finset.range 6) : Set ℕ)ᶜ with hS_def
        suffices h : 0 < ∑' (x : S), log_two_term x by linarith
        have hmem : (6 : ℕ) ∈ S := by simp [hS_def]
        have hsum := summable_log_two_series.subtype S
        have hnn : ∀ (i : S), 0 ≤ log_two_term i := by
          intro ⟨i, _⟩
          simp only [log_two_term]
          positivity
        exact hsum.tsum_pos hnn ⟨6, hmem⟩ (by simp [log_two_term]; positivity)
