-- ══════════════════════════════════════════════════════════════
-- Mathematics in Lean — Selected Examples
-- Tested against Mathlib REPL (Lean 4 + Mathlib)
-- ══════════════════════════════════════════════════════════════

set_option linter.unusedVariables false

-- ── Chapter 2: Basics ────────────────────────────────────────
-- 2.1 Calculating with ring

example (a b c : ℝ) : a * b * c = b * (a * c) := by ring
example (a b c : ℝ) : c * b * a = b * (a * c) := by ring
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by ring

-- 2.1 Rewriting

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
    a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) :
    a * b * c * d = a * e * f * d := by
  rw [mul_assoc a, h, ← mul_assoc]

-- 2.2 Algebraic identities

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
    c = 2 * a * d := by
  rw [hyp, hyp']; ring

-- 2.3 Inequalities

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by linarith

example (a b : ℝ) (h : a ≤ b) (h' : 0 ≤ b) : a * b ≤ b * b :=
  mul_le_mul_of_nonneg_right h h'

example (a b c d : ℝ) (h₀ : a ≤ b) (h₁ : c ≤ d) :
    a + c ≤ b + d := by linarith

-- 2.4 Divisibility

example : (1 : ℤ) ∣ 5 := ⟨5, by ring⟩

example (a b c : ℕ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  dvd_trans h₁ h₂

-- ── Chapter 3: Logic ─────────────────────────────────────────
-- 3.1 Universal quantifier

theorem my_add_le_add (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d := by linarith

-- 3.2 Existential quantifier

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨2.5, by norm_num, by norm_num⟩

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n :=
  ⟨5, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- 3.3 Negation

example (a : ℝ) (h : ∀ ε > 0, a < ε) : a ≤ 0 := by
  by_contra h'
  push_neg at h'
  have := h (a / 2) (by linarith)
  linarith

-- 3.4 Conjunction

example (a b : ℝ) (h : a ≤ b) : a ≤ b ∧ b ≤ b :=
  ⟨h, le_refl b⟩

-- 3.5 Disjunction

example (a : ℝ) : a = a ∨ a = -a := Or.inl rfl
example (a b : ℝ) : |a * b| = |a| * |b| := abs_mul a b

example (x y : ℝ) (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · intro h' heq; exact h' (heq ▸ le_refl _)
  · intro h' h''; exact h' (le_antisymm h h'')

-- ── Chapter 4: Sets and Functions ────────────────────────────
open Set Function

variable {α : Type*} (s t u : Set α)

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs, xu⟩; exact ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x ⟨xs, xtu⟩
  rcases xtu with xt | xu
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s \ t ∪ t = s ∪ t := by ext x; simp [mem_union]

-- Injective, surjective

example : Injective (fun (x : ℝ) => 2 * x + 1) := by
  intro x₁ x₂ h; linarith

example : ¬Injective (fun (x : ℝ) => x ^ 2) := by
  intro h
  have : (1 : ℝ) = -1 := h (by ring : (1 : ℝ) ^ 2 = (-1) ^ 2)
  linarith

example : Surjective (fun (x : ℝ) => 2 * x + 1) := by
  intro y; exact ⟨(y - 1) / 2, by ring⟩

-- ── Chapter 5: Number Theory ─────────────────────────────────

example : Nat.Prime 17 := by decide
example : Nat.Coprime 12 7 := by decide

theorem prime_dvd_of_dvd_sq (p : ℕ) (hp : Nat.Prime p)
    (a : ℕ) (h : p ∣ a * a) : p ∣ a :=
  hp.dvd_of_dvd_pow (n := 2) (by rwa [pow_two])

-- Fermat's little theorem
#check ZMod.pow_card  -- x ^ p = x  in  ZMod p

-- ── Chapter 6: Topology & Analysis ──────────────────────────

example : Continuous (fun (x : ℝ) => x ^ 2 + 3 * x + 1) := by fun_prop
example : Continuous (fun (x : ℝ) => Real.sin x + Real.cos x) := by fun_prop

-- Intermediate Value Theorem
#check intermediate_value_uIcc

-- Limits: 1/n → 0
example : Filter.Tendsto (fun (n : ℕ) => (1 : ℝ) / n) Filter.atTop (nhds 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_nhds_zero_nat

-- ── Chapter 7: Algebra ──────────────────────────────────────

example {G : Type*} [Group G] (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  exact mul_left_cancel (by rwa [mul_inv_cancel])

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a * b) = f a * f b :=
  f.map_mul a b

-- ℤ/pℤ is a field when p is prime
#check ZMod.instField

example : (2 : ZMod 5) * 3 = 1 := by decide

-- ── Linear Algebra ──────────────────────────────────────────

#check !![1, 2; 3, 4] + !![5, 6; 7, 8]  -- Matrix (Fin 2) (Fin 2) ℕ

example : Matrix.det !![1, 2; 3, 4] = (-2 : ℤ) := by native_decide

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

example (v w : V) : (2 : ℝ) • (v + w) = (2 : ℝ) • v + (2 : ℝ) • w :=
  smul_add (2 : ℝ) v w

-- ── Capstone ────────────────────────────────────────────────

#check irrational_sqrt_two  -- Irrational √2
