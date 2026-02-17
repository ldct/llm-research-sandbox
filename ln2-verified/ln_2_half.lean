import Mathlib

/-- The series representation of log 2: ln(2) = Σ 1/(n·2ⁿ) -/
theorem log_two_eq_tsum : ∑' (n : ℕ), (1:ℝ) / (n * 2^n) = Real.log 2 := by
  have h := Complex.hasSum_taylorSeries_neg_log (z := 1/2) (by norm_num : ‖(1/2 : ℂ)‖ < 1)
  simp only [one_div] at h
  have h2 : (1 : ℂ) - 2⁻¹ = (2⁻¹ : ℝ) := by norm_num
  rw [h2] at h
  have h3 : Complex.log (2⁻¹ : ℝ) = (Real.log 2⁻¹ : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2⁻¹)).symm
  rw [h3] at h
  have goal : HasSum (fun n : ℕ => (↑(2⁻¹ ^ n / (n : ℝ)) : ℂ)) (↑(-Real.log 2⁻¹)) := by
    convert h using 1
    · ext n; simp [Complex.ofReal_pow, Complex.ofReal_div]
    · simp
  rw [Complex.hasSum_ofReal] at goal
  have hs : HasSum (fun n : ℕ => 2⁻¹ ^ n / (n : ℝ)) (Real.log 2) := by
    convert goal using 1
    rw [Real.log_inv]; ring
  rw [← hs.tsum_eq]
  congr 1
  ext n
  cases n with
  | zero => simp
  | succ n =>
    field_simp
    simp only [one_div]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0))]

lemma summable_log_series : Summable (fun n : ℕ => (1:ℝ) / (n * 2^n)) := by
  have h := Complex.hasSum_taylorSeries_neg_log (z := 1/2) (by norm_num : ‖(1/2 : ℂ)‖ < 1)
  simp only [one_div] at h
  have h2 : (1 : ℂ) - 2⁻¹ = (2⁻¹ : ℝ) := by norm_num
  rw [h2] at h
  have h3 : Complex.log (2⁻¹ : ℝ) = (Real.log 2⁻¹ : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2⁻¹)).symm
  rw [h3] at h
  have goal : HasSum (fun n : ℕ => (↑(2⁻¹ ^ n / (n : ℝ)) : ℂ)) (↑(-Real.log 2⁻¹)) := by
    convert h using 1
    · ext n; simp [Complex.ofReal_pow, Complex.ofReal_div]
    · simp
  rw [Complex.hasSum_ofReal] at goal
  have hs : Summable (fun n : ℕ => 2⁻¹ ^ n / (n : ℝ)) := goal.summable
  convert hs using 1
  ext n
  cases n with
  | zero => simp
  | succ n =>
    field_simp
    simp only [one_div]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0))]

/-- Lower bound on log 2 from first 19 terms of the series Σ 1/(n·2ⁿ):
    0.693147 < ln(2)
    
    The partial sum of 19 terms equals 10574855234543/15256293212160 ≈ 0.6931470894,
    which exceeds 0.693147. Since all remaining terms are positive, the full
    series (which equals ln(2)) is strictly greater than the partial sum. -/
theorem lower_bound_log_two : (0.693147 : ℝ) < Real.log 2 := by
  have heq : Real.log 2 = ∑' (n : ℕ), (1:ℝ) / (n * 2^n) := log_two_eq_tsum.symm
  rw [heq]
  -- First 19 terms sum to 10574855234543/15256293212160 > 0.693147
  have hpartial : ∑ n ∈ Finset.range 20, (1:ℝ) / (n * 2^n) = 10574855234543/15256293212160 := by
    norm_num
  have hbound : (0.693147 : ℝ) < 10574855234543/15256293212160 := by norm_num
  calc (0.693147 : ℝ)
      < 10574855234543/15256293212160 := hbound
    _ = ∑ n ∈ Finset.range 20, (1:ℝ) / (n * 2^n) := hpartial.symm
    _ < ∑' (n : ℕ), (1:ℝ) / (n * 2^n) := by
        have hdecomp := summable_log_series.sum_add_tsum_compl (s := Finset.range 20)
        rw [← hdecomp]
        set S := (↑(Finset.range 20) : Set ℕ)ᶜ with hS_def
        suffices h : 0 < ∑' (x : S), (1:ℝ) / (↑x * 2^(↑x : ℕ)) by linarith
        have hmem : (20 : ℕ) ∈ S := by simp [hS_def]
        have hsum := summable_log_series.subtype S
        have hnn : ∀ (i : S), 0 ≤ (1:ℝ) / (↑i * 2^(↑i : ℕ)) := by
          intro ⟨i, hi⟩
          simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt, hS_def] at hi
          have : 1 ≤ i := Nat.one_le_of_lt (Nat.lt_of_lt_of_le (by norm_num : 0 < 20) hi)
          positivity
        exact hsum.tsum_pos hnn ⟨20, hmem⟩ (by norm_num)
