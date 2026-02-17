/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

Tactics for proving bounds on ln(2) using the atanh series:
  ln(2) = 2 * Σ_{k=0}^∞ (1/(2k+1)) * (1/3)^(2k+1)

Provides two tactics:
- `log_lower_bound n`: proves goals of the form `c < Real.log 2` using n terms
- `log_upper_bound n`: proves goals of the form `Real.log 2 < c` using n terms + tail bound

Each term provides ~0.95 decimal digits of precision.
-/
import Mathlib

/-! ## Series infrastructure -/

noncomputable def log_two_term (k : ℕ) : ℝ := 2 * (1 / (2 * k + 1)) * (1/3 : ℝ) ^ (2 * k + 1)

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
      · push_neg at h; rw [abs_of_neg (by linarith : z - 1 < 0)]; linarith
    calc |z - 1| / (z + 1) < (z + 1) / (z + 1) := div_lt_div_of_pos_right h1 hz1
      _ = 1 := div_self (ne_of_gt hz1)
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hz1_ne : z + 1 ≠ 0 := by linarith
  have one_plus_x : 1 + x = 2 * z / (z + 1) := by rw [hx_def]; field_simp; ring
  have one_minus_x : 1 - x = 2 / (z + 1) := by rw [hx_def]; field_simp; ring
  rw [one_plus_x, one_minus_x] at hs
  rw [Real.log_div (by linarith : (2 * z : ℝ) ≠ 0) hz1_ne] at hs
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hz1_ne] at hs
  convert hs using 1
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hz)]; ring

theorem summable_log_two_series : Summable log_two_term := by
  have h := (log_eq_hasSum_atanh (by norm_num : (0:ℝ) < 2)).summable
  convert h using 1; ext k; simp only [log_two_term]; norm_num

theorem log_two_eq_tsum : Real.log 2 = ∑' (k : ℕ), log_two_term k := by
  have h := log_eq_hasSum_atanh (by norm_num : (0:ℝ) < 2)
  have heq : ∀ k, 2 * (1 / (2 * ↑k + 1)) * ((2 - 1) / (2 + 1)) ^ (2 * k + 1) = log_two_term k := by
    intro k; simp only [log_two_term]; norm_num
  simp only [heq] at h; exact h.tsum_eq.symm

theorem log_two_term_le (k : ℕ) : log_two_term k ≤ 2 * (1/3 : ℝ) ^ (2 * k + 1) := by
  simp only [log_two_term]
  have h1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by rw [div_le_one h1]; linarith
  have h4 : (0 : ℝ) ≤ (1/3 : ℝ) ^ (2 * k + 1) := by positivity
  have h5 : 2 * (1 / (2 * (k : ℝ) + 1)) * (1 / 3) ^ (2 * k + 1) ≤ 2 * 1 * (1 / 3 : ℝ) ^ (2 * k + 1) := by
    apply mul_le_mul_of_nonneg_right _ h4
    apply mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
  calc 2 * (1 / (2 * (k : ℝ) + 1)) * (1/3 : ℝ) ^ (2 * k + 1)
      ≤ 2 * 1 * (1/3 : ℝ) ^ (2 * k + 1) := h5
    _ = 2 * (1/3 : ℝ) ^ (2 * k + 1) := by ring

theorem summable_geo_bound : Summable (fun k : ℕ => (2 : ℝ) * (1/3) ^ (2 * k + 1)) := by
  have h : Summable (fun k : ℕ => (2/3 : ℝ) * (1/9) ^ k) := by
    apply Summable.mul_left; exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  convert h using 1; ext k
  have : (1/3 : ℝ) ^ (2 * k + 1) = (1/3) * (1/9)^k := by rw [pow_add, pow_mul]; norm_num; ring
  linarith

theorem tail_bound (K : ℕ) : ∑' k, log_two_term (K + k) ≤ (9/4 : ℝ) * (1/3) ^ (2 * K + 1) := by
  have hsummable : Summable (fun k => log_two_term (K + k)) :=
    summable_log_two_series.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hsummable_geo : Summable (fun k => (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1)) :=
    summable_geo_bound.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hle : ∀ k, log_two_term (K + k) ≤ 2 * (1/3 : ℝ) ^ (2 * (K + k) + 1) := fun k => log_two_term_le (K + k)
  have hsum_le := hsummable.tsum_le_tsum hle hsummable_geo
  have hgeo_eq : ∑' k, (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1) = (9/4) * (1/3) ^ (2 * K + 1) := by
    have factor : ∀ k, (2 : ℝ) * (1/3) ^ (2 * (K + k) + 1) = 2 * (1/3)^(2*K+1) * (1/9)^k := by
      intro k; rw [show 2 * (K + k) + 1 = 2 * K + 1 + 2 * k by ring, pow_add]
      rw [show (1/3 : ℝ) ^ (2 * k) = (1/9)^k by rw [pow_mul]; norm_num]; ring
    simp_rw [factor]; rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  linarith

theorem log_two_partial_lt_tsum (n : ℕ) :
    ∑ k ∈ Finset.range n, log_two_term k < ∑' k, log_two_term k := by
  have hdecomp := summable_log_two_series.sum_add_tsum_compl (s := Finset.range n)
  rw [← hdecomp]
  set S := (↑(Finset.range n) : Set ℕ)ᶜ
  suffices h : 0 < ∑' (x : S), log_two_term x by linarith
  have hmem : n ∈ S := by simp [S]
  have hsum := summable_log_two_series.subtype S
  have hnn : ∀ (i : S), 0 ≤ log_two_term i := by intro ⟨i, _⟩; simp only [log_two_term]; positivity
  exact hsum.tsum_pos hnn ⟨n, hmem⟩ (by simp [log_two_term]; positivity)

theorem log_two_tsum_le_partial_add_tail (n : ℕ) :
    ∑' k, log_two_term k ≤ ∑ k ∈ Finset.range n, log_two_term k + (9/4 : ℝ) * (1/3) ^ (2 * n + 1) := by
  have hdecomp := Summable.sum_add_tsum_nat_add n summable_log_two_series
  have htail := tail_bound n
  have htail' : ∑' i, log_two_term (i + n) ≤ (9/4 : ℝ) * (1/3) ^ (2 * n + 1) := by
    have heq : (fun i => log_two_term (i + n)) = (fun k => log_two_term (n + k)) := by ext k; ring_nf
    rw [heq]; exact htail
  have htail_nn : 0 ≤ ∑' i, log_two_term (i + n) := tsum_nonneg (fun k => by simp [log_two_term]; positivity)
  linarith

/-! ## Tactics -/

/-- Tactic for proving lower bounds: `c < Real.log 2` using n terms of the series -/
macro "log_lower_bound" n:num : tactic => `(tactic| (
  rw [log_two_eq_tsum]
  calc _ < ∑ k ∈ Finset.range $n, log_two_term k := by simp only [log_two_term]; norm_num
       _ < ∑' k, log_two_term k := log_two_partial_lt_tsum $n
))

/-- Tactic for proving upper bounds: `Real.log 2 < c` using n terms + geometric tail bound -/
macro "log_upper_bound" n:num : tactic => `(tactic| (
  rw [log_two_eq_tsum]
  calc ∑' k, log_two_term k
       ≤ ∑ k ∈ Finset.range $n, log_two_term k + (9/4 : ℝ) * (1/3) ^ (2 * $n + 1) :=
           log_two_tsum_le_partial_add_tail $n
     _ < _ := by simp only [log_two_term]; norm_num
))

/-! ## Main theorems -/

theorem log_2_gt : (0.693147 : ℝ) < Real.log 2 := by log_lower_bound 6

theorem log_2_lt : Real.log 2 < (0.693148 : ℝ) := by log_upper_bound 7

theorem log_2_gt_100 :
    (693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418687 : ℝ) / 10^99
    < Real.log 2 := by
  log_lower_bound 106

theorem log_2_lt_100 :
    Real.log 2 <
    (693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418688 : ℝ) / 10^99 := by
  log_upper_bound 106
