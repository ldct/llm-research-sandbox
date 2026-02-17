/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

Bounds on ln(2) using the atanh series:
  ln(z) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * ((z-1)/(z+1))^(2k+1)

For z = 2, this becomes:
  ln(2) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * (1/3)^(2k+1)

This is the series expansion of 2·atanh((z-1)/(z+1)), using the identity
ln(z) = 2·atanh((z-1)/(z+1)) for z > 0.

Convergence rate: Each term provides approximately log₁₀(9) ≈ 0.95 decimal
digits of precision, since the exponent increases by 2 and (1/3)^2 = 1/9.

Main results:
- `log_2_gt`: 0.693147 < ln(2)  (6 terms, partial sum lower bound)
- `log_2_lt`: ln(2) < 0.693148  (7 terms + geometric tail bound)
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

/-! ## Upper bound theorem -/

/-- Bound: each term is at most 2 * (1/3)^(2k+1) -/
theorem log_two_term_le (k : ℕ) : log_two_term k ≤ 2 * (1/3 : ℝ) ^ (2 * k + 1) := by
  simp only [log_two_term]
  have h1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have h2 : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one h1]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h3 : (0 : ℝ) < (1/3 : ℝ) ^ (2 * k + 1) := by positivity
  have h4 : (0 : ℝ) ≤ (1/3 : ℝ) ^ (2 * k + 1) := le_of_lt h3
  calc 2 * (1 / (2 * k + 1)) * (1/3 : ℝ) ^ (2 * k + 1)
      ≤ 2 * 1 * (1/3 : ℝ) ^ (2 * k + 1) := by nlinarith
    _ = 2 * (1/3 : ℝ) ^ (2 * k + 1) := by ring

theorem summable_geo_bound : Summable (fun k : ℕ => (2 : ℝ) * (1/3) ^ (2 * k + 1)) := by
  have h : Summable (fun k : ℕ => (2/3 : ℝ) * (1/9) ^ k) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  convert h using 1
  ext k
  have : (1/3 : ℝ) ^ (2 * k + 1) = (1/3) * (1/9)^k := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  linarith

/-- Tail bound: Σ_{k≥K} log_two_term k ≤ (9/4) * (1/3)^(2K+1) -/
theorem tail_bound (K : ℕ) : ∑' k, log_two_term (K + k) ≤ (9/4 : ℝ) * (1/3) ^ (2 * K + 1) := by
  have hsummable : Summable (fun k => log_two_term (K + k)) :=
    summable_log_two_series.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hsummable_geo : Summable (fun k => (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1)) :=
    summable_geo_bound.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hle : ∀ k, log_two_term (K + k) ≤ 2 * (1/3 : ℝ) ^ (2 * (K + k) + 1) := fun k => log_two_term_le (K + k)
  have hsum_le : ∑' k, log_two_term (K + k) ≤ ∑' k, (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1) :=
    hsummable.tsum_le_tsum hle hsummable_geo
  have hgeo_eq : ∑' k, (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1) = (9/4) * (1/3) ^ (2 * K + 1) := by
    have factor : ∀ k, (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1) = 2 * (1/3)^(2*K+1) * (1/9)^k := by
      intro k
      have : 2 * (K + k) + 1 = 2 * K + 1 + 2 * k := by ring
      rw [this, pow_add]
      have : (1/3 : ℝ) ^ (2 * k) = (1/9)^k := by rw [pow_mul]; norm_num
      rw [this]
      ring
    simp_rw [factor]
    rw [tsum_mul_left]
    have hgeo : ∑' k : ℕ, (1/9 : ℝ)^k = 9/8 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [hgeo]
    ring
  linarith

/-- Upper bound on log 2 using 7 terms plus geometric tail bound:
    ln(2) < 0.693148

    The partial sum of 7 terms equals 5531027882/7979586615.
    The tail Σ_{k≥7} is bounded by (9/4)·(1/3)^15 = 3/19131876.
    Their sum is less than 0.693148.
-/
theorem log_2_lt : Real.log 2 < (0.693148 : ℝ) := by
  rw [log_two_eq_tsum]
  have hdecomp := Summable.sum_add_tsum_nat_add 7 summable_log_two_series
  rw [← hdecomp]
  have hpartial : ∑ k ∈ Finset.range 7, log_two_term k = 5531027882 / 7979586615 := by
    simp only [log_two_term]
    norm_num
  rw [hpartial]
  have htail := tail_bound 7
  have htail_val : (9/4 : ℝ) * (1/3) ^ (2 * 7 + 1) = 3 / 19131876 := by norm_num
  rw [htail_val] at htail
  have htail' : ∑' i, log_two_term (i + 7) ≤ 3 / 19131876 := by
    have heq : (fun i => log_two_term (i + 7)) = (fun k => log_two_term (7 + k)) := by
      ext k; ring_nf
    rw [heq]
    exact htail
  have hbound : 5531027882 / 7979586615 + 3 / 19131876 < (0.693148 : ℝ) := by norm_num
  have htail_nn : 0 ≤ ∑' i, log_two_term (i + 7) := by
    apply tsum_nonneg
    intro k
    simp only [log_two_term]
    positivity
  linarith
