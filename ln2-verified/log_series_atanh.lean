/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

The series representation of the natural logarithm:
  ln(z) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * ((z-1)/(z+1))^(2k+1)

This is valid for all z > 0.
-/
import Mathlib

/-
  Proof idea: Use the substitution x = (z-1)/(z+1).
  For z > 0, we have |x| < 1, and:
    1 + x = 2z/(z+1)
    1 - x = 2/(z+1)
  So: ln(1+x) - ln(1-x) = ln(2z/(z+1)) - ln(2/(z+1))
                        = ln(2z) - ln(z+1) - (ln(2) - ln(z+1))
                        = ln(2z) - ln(2) = ln(z)
-/

/-- Main theorem: The series representation of ln(z) for positive z.
    This is the formula:
    ln(z) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * ((z-1)/(z+1))^(2k+1)
-/
theorem log_series_representation {z : ℝ} (hz : 0 < z) :
    HasSum (fun k : ℕ => 2 * (1 / (2 * k + 1)) * ((z - 1) / (z + 1)) ^ (2 * k + 1)) (Real.log z) := by
  set x := (z - 1) / (z + 1) with hx_def
  -- First show |x| < 1 for all z > 0
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
  -- Apply the Mathlib theorem about log(1+x) - log(1-x)
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  -- Algebraic simplifications
  have hz1_ne : z + 1 ≠ 0 := by linarith
  have one_plus_x : 1 + x = 2 * z / (z + 1) := by rw [hx_def]; field_simp; ring
  have one_minus_x : 1 - x = 2 / (z + 1) := by rw [hx_def]; field_simp; ring
  have h2z_pos : 0 < 2 * z := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  -- Rewrite the logs
  rw [one_plus_x, one_minus_x] at hs
  rw [Real.log_div (ne_of_gt h2z_pos) hz1_ne] at hs
  rw [Real.log_div (ne_of_gt h2_pos) hz1_ne] at hs
  convert hs using 1
  rw [Real.log_mul (ne_of_gt h2_pos) (ne_of_gt hz)]
  ring

/-- The series is summable for all positive z -/
theorem summable_log_series_representation {z : ℝ} (hz : 0 < z) :
    Summable (fun k : ℕ => 2 * (1 / (2 * k + 1)) * ((z - 1) / (z + 1)) ^ (2 * k + 1)) :=
  (log_series_representation hz).summable

/-- Infinite sum version: ln(z) equals the tsum -/
theorem log_eq_tsum {z : ℝ} (hz : 0 < z) :
    Real.log z = ∑' (k : ℕ), 2 * (1 / (2 * k + 1)) * ((z - 1) / (z + 1)) ^ (2 * k + 1) :=
  (log_series_representation hz).tsum_eq.symm
