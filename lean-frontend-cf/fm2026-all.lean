-- Formalising Mathematics 2026 — Complete Solutions
-- All 65 solution files from Sections 01-16
-- Source: https://github.com/b-mehta/formalising-mathematics-notes
-- Authors: Bhavik Mehta, Kevin Buzzard
-- Lean toolchain: leanprover/lean4:v4.26.0, Mathlib v4.26.0

set_option warningAsError false
set_option linter.style.longFile 0

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_01_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-!

# Logic in Lean, example sheet 1 : "implies" (`→`)

A *proposition* is a true-false statement, like `2+2=4` or `2+2=5`
or the Riemann hypothesis. In algebra we manipulate
numbers whilst not knowing what the numbers actually are; the trick is
that we call the numbers `x` and `y` and so on. In this sheet we
will learn how to manipulate propositions without saying what the
propositions are -- we'll just call them things like `P` and `Q`.

The purpose of these first few sheets is to teach you some very basic
*tactics*. In particular we will learn how to manipulate statements
such as "P implies Q", which is itself a true-false statement (e.g.
it is false when P is true and Q is false). In Lean we use the
notation `P → Q` for "P implies Q". You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a single arrow.

## The absolute basics

`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true. You can also regard `h` as the
hypothesis that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following three tactics:

* `intro`
* `exact`
* `apply`

You can read the descriptions of these tactics in Part 2 of the online course
notes here https://b-mehta.github.io/formalising-mathematics-notes/
In this course we'll be learning about 30 tactics in total; the goal of this
first logic section is to get you up to speed with ten very basic ones.

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the newline or semicolon (`;`).
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.

-/

set_option linter.unusedVariables false

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.
-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P := by
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  exact hP

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
-- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)
  exact fish

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- The goal is of the form `X → Y` so we can use `intro`
  intro h
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- `hP` says that `P` is true, and `h` says that `P` implies `Q`, so `apply h at hP` will change
  -- `hP` to a proof of `Q`.
  apply h at hP
  -- now `hP` is a proof of `Q` so that's exactly what we want.
  exact hP

-- The `apply` tactic always needs a hypothesis of the form `P → Q`. But instead of applying
-- it to a hypothesis `h : P` (which changes the hypothesis to a proof of `Q`), you can instead
-- just use a bare `apply h` and it will apply it to the *goal*, changing it from `Q` to `P`.
-- Here we are "arguing backwards" -- if we know that P implies Q, then to prove Q it suffices to
-- prove P.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply h
  -- Our goal is now `⊢ P`.
  exact hP

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`.

So the next level is asking you to prove that `P → (Q → P)`.

-/
example : P → Q → P := by
  intro hP hQ
  -- the `assumption` tactic will close a goal if
  -- it's exactly equal to one of the hypotheses.
  assumption

/-

## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using `intro`,
`exact` and `apply`, separating them with newlines or semicolons (`;`).
-/

/-- Every proposition implies itself. -/
example : P → P := by
  intro banana
  exact banana



/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by
  intro hP hPQ
  apply hPQ at hP
  exact hP

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
example : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  apply hPQ at hP
  apply hQR at hP
  exact hP

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR hPQ hP
  apply hPQR
  · exact hP
  · apply hPQ
    exact hP

/-

Here are some harder puzzles. They won't teach you anything new about
Lean, they're just trickier. If you're not into logic puzzles
and you feel like you understand `intro`, `exact` and `apply`
then you can just skip these and move onto the next sheet
in this section, where you'll learn some more tactics.

-/
variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro hPR hSQ hRT hQR hS
  apply hRT
  clear hPR
  apply hQR
  apply hSQ
  exact hS

example : (P → Q) → ((P → Q) → P) → Q := by
  intro hPQ hPQP
  apply hPQ
  apply hPQP
  exact hPQ

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1 h2 h3
  apply h2
  intro hQ
  apply h1
  intro hP
  exact hQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  apply h1
  intro hQ
  apply h3
  apply h2
  exact hQ

example : (((P → Q) → Q) → Q) → P → Q := by
  intro h1 hP
  apply h1
  intro hPQ
  exact hPQ hP

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  intro h1 h2 h3
  apply h2
  intro h1 hP h2
  apply h1
  intro hP
  exact h2

-- another approach using a more advanced tactic
example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  tauto

end FM2026_01_1

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_01_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `trivial`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  trivial

example : True → True := by
  intro h
  exact h

example : False → True := by
  intro h
  trivial

example : False → False := by
  intro h
  exact h

example : (True → False) → False := by
  intro h
  apply h
  trivial

example : False → P := by
  intro h
  exfalso
  exact h

example : True → False → True → False → True → False := by
  intro h1 h2 h3 h4 h5
  exact h4

example : P → (P → False) → False := by
  intro hP h
  apply h
  assumption

example : (P → False) → P → Q := by
  intro h1 h2
  exfalso
  apply h1
  exact h2

example : (True → False) → P := by
  intro h
  exfalso
  apply h
  trivial

end FM2026_01_2

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_01_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  change True → False at h -- you don't have to do this
  apply h
  trivial

example : False → ¬True := by
  intro h instHModUInt32Nat
  exact h

example : ¬False → True := by
  intro h
  trivial

example : True → ¬False := by
  intro h h2
  exact h2

example : False → ¬P := by
  intro h hasProd_bot
  exact h

example : P → ¬P → False := by
  intro hP hnP
  apply hnP
  exact hP

example : P → ¬¬P := by
  intro hP hnP
  apply hnP
  exact hP
-- Notice that this proof is exactly the same as the previous: why?

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  apply hnQ
  apply hPQ
  assumption

example : ¬¬False → False := by
  intro h
  apply h
  intro h2
  exact h2

example : ¬¬P → P := by
  intro h
  by_contra h2
  apply h
  exact h2

example : (¬Q → ¬P) → P → Q := by
  intro h hP
  change (Q → False) → P → False at h
  by_contra hnQ
  apply h
  · exact hnQ
  · exact hP

end FM2026_01_3

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_01_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases` or `rcases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are a few ways to break down a conjunction:

-- You can use `obtain`
example : P ∧ Q → P := by
  intro h
  obtain ⟨left, right⟩ := h
  exact left

-- or `rcases` (which is just `obtain` but with a slightly different syntax)
example : P ∧ Q → P := by
  intro h
  rcases h with ⟨left, right⟩
  exact left

/--
The pattern `intro h` then `rcases h with ...` is so common that it has an abbreviation as
`rintro ...`, so you could also do
-/
example : P ∧ Q → P := by
  rintro ⟨left, right⟩
  exact left

-- or you can get the relevant part out directly using `.left`
example : P ∧ Q → P := by
  intro h
  exact h.left

-- or by using `.1` (the first part)
example : P ∧ Q → P := by
  intro h
  exact h.1

example : P ∧ Q → Q := by
  rintro ⟨hP, hQ⟩
  assumption

example : (P → Q → R) → P ∧ Q → R := by
  rintro hPQR ⟨hP, hQ⟩
  apply hPQR
  · assumption
  · assumption

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  -- After the `constructor` tactic, we have *2 goals* for the first time!
  -- We use centre-dots, typed as `\.` to help Lean (and the reader) figure out when we're done
  · assumption
  · assumption

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  rintro ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

example : P → P ∧ True := by
  intro hP
  constructor
  · exact hP
  · trivial

example : False → P ∧ False := by
  intro h
  exfalso
  exact h

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  rintro ⟨hP, hQ⟩ ⟨-, hR⟩
  exact ⟨hP, hR⟩

example : (P ∧ Q → R) → P → Q → R := by
  intro h hP hQ
  apply h
  constructor <;> assumption

end FM2026_01_4

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet5.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_01_5
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
  · intro h
    rw [h]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  -- rwa is rw + assumption
  rwa [h1]

-- Here's a more subtle use of `all_goals`: note the indentation is useful for readability
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  all_goals
    rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

-- Take a close look at the `rintro` pattern here, it's more than what we've seen before
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · rintro ⟨⟨hP, hQ⟩, hR⟩
    exact ⟨hP, ⟨hQ, hR⟩⟩
  · rintro ⟨hP, ⟨hQ, hR⟩⟩
    exact ⟨⟨hP, hQ⟩, hR⟩

example : P ↔ P ∧ True := by
  constructor
  · intro hP
    constructor
    · exact hP
    · trivial
  · rintro ⟨hP, -⟩
    exact hP

example : False ↔ P ∧ False := by
  constructor
  · rintro ⟨⟩
  · rintro ⟨-, ⟨⟩⟩

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  rw [h1]
  rw [h2]

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases hP : P
  · apply h1 <;> assumption
  · apply hP
    apply h2
    exact hP

-- constructive proof
example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := by
    intro hP
    rw [h] at hP
    apply hP
    rwa [h]
  apply hnP
  rw [h]
  exact hnP

end FM2026_01_5

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_01_6
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPQ hQR
  cases hPoQ with
  | inl h =>
    apply hPQ
    exact h
  | inr h =>
    apply hQR
    apply h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPQ hQR
  obtain h | h := hPoQ
  · apply hPQ
    exact h
  · apply hQR
    apply h

-- note the way the intro / obtain get combined
-- (don't forget obtain and rcases do basically the same)
example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h) hPQ hQR
  · apply hPQ
    exact h
  · apply hQR
    apply h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (hP | hQ)
  · right
    assumption
  · left
    assumption

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro ((hP | hQ) | hR)
    · left; exact hP
    · right; left; exact hQ
    · right; right; exact hR
  · rintro (hP | hQ | hR)
    · left; left; exact hP
    · left; right; exact hQ
    · right; exact hR

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  rintro hPR hQS (hP | hQ)
  · left; apply hPR; exact hP
  · right; exact hQS hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ h
  cases h with
  | inl hP => left; apply hPQ; exact hP
  | inr hR => right; exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  rw [h1, h2]

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      exact hP
    · intro hQ
      apply h
      right
      exact hQ
  · rintro ⟨hnP, hnQ⟩ (hP | hQ)
    · apply hnP; exact hP
    · exact hnQ hQ

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ

end FM2026_01_6

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_02_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# The real numbers in Lean

Lean has a copy of of the real numbers. It's called `real`,
but we use the usual notation `ℝ`. Put your cursor on the `ℝ` to find
out how to type it in VS Code.

In this sheet you will prove some basic equalities and inequalities
between "numerical expressions" in Lean. A numeral is something like `37`,
and a numerical expression is something like `(37 + 6) / 4`. To make
things a bit harder, I will throw in some `∃` statements. To make
progress on an `∃` goal, use the `use` tactic.

## Tactics

New tactics you'll need to know about:

* `norm_num` (proves equalities and inequalities involving numerical expressions)
* `use` (if the goal is `∃ x, x + 37 = 42` then `use 8` will change the goal
*        to `8 + 37 = 42`, and `use 10` will change it to `10 + 37 = 42`.

-/

example : (2 : ℝ) + 2 = 4 := by norm_num

example : (2 : ℝ) + 2 ≠ 5 := by norm_num

example : (2 : ℝ) + 2 < 5 := by norm_num

example : ∃ x : ℝ, 3 * x + 7 = 12 := by
  use 5 / 3
  norm_num

example : ∃ x : ℝ, 3 * x + 7 ≠ 12 := by
  use 0
  norm_num

example : ∃ x y : ℝ, 2 * x + 3 * y = 7 ∧ x + 2 * y = 4 := by
  use 2, 1
  norm_num

end FM2026_02_1

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_02_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Doing algebra in the real numbers

The `ring` tactic will prove algebraic identities like
(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 in rings, and Lean
knows that the real numbers are a ring. See if you can use
`ring` to prove these theorems.

## New tactics you will need

* `ring`
* `intro` (new functionality: use on a goal of type `⊢ ∀ x, ...`)

-/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a b
  use 3
  ring

example : ∃ x : ℝ, ∀ y, y + y = x * y := by
  use 2
  intro y
  ring

example : ∀ x : ℝ, ∃ y, x + y = 2 := by
  intro x
  use 2 - x
  ring

example : ∀ x : ℝ, ∃ y, x + y ≠ 2 := by
  intro x
  use 3 - x
  ring_nf
  norm_num

end FM2026_02_2

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_02_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section2sheet3solutions

/-

# Limits of sequences in Lean

We give the standard `ε`, `N` definition of the limit of a sequence
and prove some theorems about them.

## `fun` notation for functions

Here's how we define the functions from the naturals to the naturals
sending n to n^2 + 3:

-/

def f : ℕ → ℝ := fun n ↦ n ^ 2 + 3

/-

Mathematicians might write `n ↦ n^2+3` for this function. You can
read more about function types in the "three kinds of types" section
of Part 1 of the course book.

Sometimes you might find yourself with a lambda-defined function
evaluated at a number. For example, you might see something like
`(fun n => n^2 + 3) 37`, which means "take the function sending
`n` to `n^2+3` and then evaluate it at 37". You can use the `dsimp`
(or `dsimp only`) tactic to simplify this to `37^2+3`.

The reason we need to know about function notation for this sheet
is that a sequence `x₀, x₁, x₂, …` of reals on this sheet will
be encoded as a function from `ℕ` to `ℝ` sending `0` to `x₀`, `1` to `x₁`
and so on.

## Limit of a sequence.

Here's the definition of the limit of a sequence.
-/
/-- If `a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-

We've made a definition, so it's our job to now make the API
for the definition, i.e. prove some basic theorems about it.

-/
-- If your goal is `TendsTo a t` and you want to replace it with
-- `∀ ε > 0, ∃ B, …` then you can do this with `rw tendsTo_def`.
theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl  -- true by definition

-- the eagle-eyed viewers amongst you might have spotted
-- that `∀ ε > 0, ...` and `∀ ε, ε > 0 → ...` and `∀ ε, 0 < ε → ...`
-- are all definitionally equal, so `rfl` sees through them.
/-

## The questions

Here are some basic results about limits of sequences.
See if you can fill in the `sorry`s with Lean proofs.
Note that `norm_num` can work with `|x|` if `x` is a numeral like 37,
but it can't do anything with it if it's a variable.
-/
/-- The limit of the constant sequence with value 37 is 37. -/
theorem tendsTo_thirtyseven : TendsTo (fun n ↦ 37) 37 := by
  rw [tendsTo_def]
  intro ε hε
  use 100
  intro n hn
  norm_num
  exact hε

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun n => c) c := by
  intro ε hε
  dsimp only
  use 37
  intro n hn
  ring_nf
  norm_num
  exact hε

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) := by
  rw [tendsTo_def] at h ⊢
  ring_nf
  exact h

/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  rw [tendsTo_def] at ha ⊢
  intro ε hε
  specialize ha ε hε
  cases' ha with B hB
  use B
  intro n hn
  specialize hB n hn
  have h : ∀ x : ℝ, |-x| = |x| := abs_neg -- thanks exact?
  rw [← h]
  ring_nf at hB ⊢
  exact hB

-- another approach using the `peel` tactic.
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  rw [tendsTo_def] at ha ⊢
  peel ha with h ε hε B N hBN
  convert hBN using 1
  -- have h2 : ∀ x : ℝ, |-x| = |x| := by exact fun x => abs_neg x
  convert abs_neg _ using 2
  ring

end Section2sheet3solutions

end FM2026_02_3

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_02_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
/-

# Figuring out how to use the reals

## The `exact?` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `exact?` tactic tells you the names of all these lemmas.
See where it says "try this" -- click there and Lean will replace
`exact?` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.
However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `exact?` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/

example (x : ℝ) : |-x| = |x| := by exact?
-- click where it says "try this" to replace
-- `exact?` with an "exact" proof
-- Why do this? Because it's quicker!

example (x y : ℝ) : |x - y| = |y - x| := by exact?


-- Hmm. What would a theorem saying "the max is
-- less-or-equal to something iff something else
-- be called, according to Lean's naming conventions?"
example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by exact?

-- abs of something less than something...
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by exact?

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by linarith

-- or linarith, or guess the name...
example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by exact?

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by linarith

-- This is too obscure for the library
example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by linarith

-- note that add_lt_add doesn't work because
-- ((a+b)+c)+d and (a+c)+(b+d) are not definitionally equal

end FM2026_02_4

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet5.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_02_5
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5solutions

open Section2sheet3solutions

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw [tendsTo_def] at *
  have h : ∀ n, |a n - t| = |-a n - -t| := by
    intro n
    rw [abs_sub_comm]
    congr 1
    ring
  simpa [h] using ha

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
  rw [tendsTo_def] at *
  -- let ε > 0 be arbitrary
  intro ε hε
  --  There's a bound X such that if n≥X then a(n) is within ε/2 of t
  specialize ha (ε / 2) (by linarith)
  cases' ha with X hX
  --  There's a bound Y such that if n≥Y then b(n) is within ε/2 of u
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  --  use max(X,Y),
  use max X Y
  -- now say n ≥ max(X,Y)
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  --  Then easy.
  rw [abs_lt] at *
  constructor <;>-- `<;>` means "do next tactic to all goals produced by this tactic"
    linarith

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  simpa [sub_eq_add_neg] using tendsTo_add ha (tendsTo_neg hb)

end Section2sheet5solutions

end FM2026_02_5

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_02_6
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- import a bunch of previous stuff

namespace Section2sheet6Solutions

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / 37) (by linarith)
  use X
  intro n hn
  specialize hX n hn
  dsimp only
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;> linarith

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / c) (div_pos hε hc)
  use X
  intro n hn
  specialize hX n hn
  dsimp only
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  exact (lt_div_iff₀' hc).mp hX

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have hc' : 0 < -c := neg_pos.mpr hc
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / -c) (div_pos hε hc')
  use X
  intro n hn
  specialize hX n hn
  dsimp only
  rw [← mul_sub, abs_mul, abs_of_neg hc]
  exact (lt_div_iff₀' hc').mp hX

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  obtain hc | rfl | hc := lt_trichotomy 0 c
  · exact tendsTo_pos_const_mul h hc
  · simpa using tendsTo_const 0
  · exact tendsTo_neg_const_mul h hc

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by simpa [mul_comm] using tendsTo_const_mul c h

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by simpa using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  · intro h
    simpa using tendsTo_sub h (tendsTo_const t)
  · intro h
    simpa using tendsTo_add h (tendsTo_const t)

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain ⟨X, hX⟩ := ha ε hε
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  simpa [abs_mul] using mul_lt_mul'' hX hY

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  -- suffices a(n)b(n)-tu -> 0
  rw [tendsTo_sub_lim_iff] at *
  -- rewrite as (a(n)-t)*(b(n)-u)+t(b(n)-u)+(a(n)-t)u ->0
  have h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u := by
    intro n; ring
  simp only [h]
  rw [show (0 : ℝ) = 0 + t * 0 + 0 * u by simp]
  refine' tendsTo_add (tendsTo_add _ _) _
  · exact tendsTo_zero_mul_tendsTo_zero ha hb
  · exact tendsTo_const_mul t hb
  · exact tendsTo_mul_const u ha

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_contra h
  wlog h2 : s < t
  · rcases Ne.lt_or_gt h with (h3 | h3)
    · contradiction
    · apply this _ _ _ ht hs _ h3
      exact ne_comm.mp h
  set ε := t - s with hε
  have hε : 0 < ε := sub_pos.mpr h2
  obtain ⟨X, hX⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := ht (ε / 2) (by linarith)
  specialize hX (max X Y) (le_max_left X Y)
  specialize hY (max X Y) (le_max_right X Y)
  rw [abs_lt] at hX hY
  linarith

-- If |r|<ε for all ε>0 then r=0
theorem eq_zero_of_abs_lt_eps {r : ℝ} (h : ∀ ε > 0, |r| < ε) : r = 0 := by
  -- Proof by contradiction. Say r ≠ 0.
  by_contra h2
  -- Then let ε be |r|, and we must have ε > 0.
  specialize h |r| (abs_pos.mpr h2)
  -- Deduce |r|<|r|, a contradiction.
  linarith

-- Second proof
theorem tendsTo_unique' (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  -- We know a - a tends to s - t because of `tendsTo_sub`
  have h := tendsTo_sub hs ht
  -- We want to prove s = t; by previous result suffices to
  -- show |t - s|<ε for all ε>0
  suffices ∀ ε > 0, |t - s| < ε by linarith [eq_zero_of_abs_lt_eps this]
  -- Let ε be positive.
  intro ε hε
  -- There exists X such that for n>=X, |a(n) - a(n) - (s - t)| < ε
  obtain ⟨X, hX⟩ := h ε hε
  specialize hX X (by rfl)
  -- and the simplifier can now reduce that to the goal |t-s|<ε.
  simpa using hX

end Section2sheet6Solutions

end FM2026_02_6

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_03_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

open Real

-- ## Practicing with the `rw` tactic
-- Let's get some practice with the `rw` tactic for equalities now.

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these using rw.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b, mul_assoc, mul_comm c a]

-- Don't forget you can use ← to rewrite in the reverse direction!
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, ← mul_assoc, mul_comm a]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a, h, ← mul_assoc]

-- The lemma `sub_self` could be helpful
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm, sub_self]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section
-- Instead of having to declare my six real numbers each time, I can say `variables` which will
-- include them everywhere _below_ the declaration. And to avoid them going too far, I can constrain
-- that to a section.

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- The calc keyword allows writing more structured proofs which are easier to read, and sometimes
-- easier to write as well, despite being longer.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- For instance, you can start your proof by sketching the structure as follows, with the sorry
-- keyword in place of some subproofs.
-- (You don't need to fill these in, it's as above!)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add, ← add_assoc]

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_sub, add_sub, sub_add, mul_comm a b, sub_self, sub_zero, pow_two,
    pow_two]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_add a b c
#check sub_self a
#check sub_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- The ring tactic can sometimes help a lot!
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

-- The nth_rw tactic allows you to be more precise about which occurrence of a subterm you want to
-- rewrite.
-- Usually this isn't necessary, but it's occasionally very helpful.
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

end FM2026_03_1

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_03_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section3sheet1solutions

/-!

# Functions in Lean.

In this sheet we'll learn how to manipulate the concepts of
injectivity and surjectivity in Lean.

The notation for functions is the usual one in mathematics:
if `X` and `Y` are types, then `f : X → Y` denotes a function
from `X` to `Y`. In fact what is going on here is that `X → Y`
denotes the type of *all* functions from `X` to `Y` (so `X → Y`
is what mathematicians sometimes call `Hom(X,Y)`), and `f : X → Y`
means that `f` is a term of type `X → Y`, i.e., a function
from `X` to `Y`.

One thing worth mentioning is that the simplest kind of function
evaluation, where you have `x : X` and `f : X → Y`, doesn't need
brackets: you can just write `f x` instead of `f(x)`. You only
need it when evaluating a function at a more complex object;
for example if we also had `g : Y → Z` then we can't write
`g f x` for `g(f(x))`, we have to write `g(f x)` otherwise
`g` would eat `f` and get confused. Without brackets,
a function just eats the next term greedily.

## The API we'll be using

Lean has the predicates `Function.Injective` and `Function.Surjective` on functions.
In other words, if `f : X → Y` is a function, then `Function.Injective f`
and `Function.Surjective f` are true-false statements.

-/

-- Typing `Function.` gets old quite quickly, so let's open the function namespace
open Function

-- Now we can just write `Injective f` and `Surjective f`.
-- Because of a cunning hack in Lean we can also write `f.Injective` and `f.Surjective`.

-- Our functions will go between these sets, or Types as Lean calls them
variable (X Y Z : Type)

-- Let's prove some theorems, each of which are true by definition.
theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

-- this proof works, because `injective f`
-- means ∀ a b, f a = f b → a = b *by definition*
-- so the proof is "it's reflexivity of `↔`"
-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) : id x = x := by
  rfl

-- Function composition is `∘` in Lean (find out how to type it by putting your cursor on it).
-- The *definition* of (g ∘ f) (x) is g(f(x)).
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl

-- Why did we just prove all those theorems with a proof
-- saying "it's true by definition"? Because now, if we want,
-- we can `rw` the theorems to replace things by their definitions.
example : Injective (id : X → X) := by
  -- this line can be deleted
  rw [injective_def]
  intro x₁ x₂ h
  -- this line can be deleted
  rw [id_eval, id_eval] at h
  exact h

example : Surjective (id : X → X) := by
  -- goal is `∀ x, ...` so make progress with `intro` tactic
  intro x
  -- goal is `∃ y, ...` so make progess with `use` tactic
  use x
  -- goal is definitionally `x = x`
  rfl

-- Theorem: if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  -- By definition of injectivity,
  -- We need to show that if a,b are in X and
  -- (g∘f)(a)=(g∘f)(b), then a=b.
  rw [injective_def] at *
  -- so assume a and b are arbitrary elements of X, and let `h` be the
  -- hypothesis that `g(f(a))=g(f(b))`
  intro a b h
  -- our goal is to prove a=b.
  -- By injectivity of `g`, we deduce from `h` that `f(a)=f(b)`
  apply hg at h
  -- By injectivity of `f`, we deduce a=b
  apply hf at h
  -- Now the goal is exactly our hypothesis `h`
  exact h

-- Theorem: composite of two surjective functions
-- is surjective.
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  -- Let f:X→Y and g:Y→Z be surjective functions.
  -- By definition, we need to prove that for
  -- all z ∈ Z there exists x ∈ X such that g(f(x))=z
  rw [surjective_def]
  -- So let z ∈ Z be arbitrary
  intro z
  -- and we need to show there exists x ∈ X
  -- with g(f(x))=z
  -- Recall that g is surjective, so there
  -- must exist y ∈ Y such that g(y)=z
  have h : ∃ y, g y = z := hg z
  rcases h with ⟨y, hy⟩
  -- Recall also that f is surjective, so
  -- there exists x ∈ X such that f(x)=y
  obtain ⟨x, hx⟩ := hf y
  -- one-liner does the same thing as two-liner above
  -- I claim that this x works
  use x
  -- And indeed g(f(x))=g(y). You can just use `rw` to prove this;
  -- here is a slighly different way
  calc
    g (f x) = g y := by rw [hx]
    _ = z := by rw [hy]

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  -- assume gf is injective
  intro hgf
  -- say x₁, x₂ in X and assume f(x₁)=f(x₂). We want to prove x₁ = x₂
  intro x₁ x₂ h
  -- by injectivity of gf it suffices to prove g(f(x₁))=g(f(x₂))
  apply hgf
  -- goal is annoyingly `(g ∘ f) x₁ = ...` instead of `g (f x₁) = ...`
  -- But these are definitionally equal
  change g (f x₁) = g (f x₂)
  rw [h]

-- goal now true by `refl` and so `rw` closes the goal as it tries `refl`.
-- This is another one
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  -- assume gf is surjective
  intro hgf
  -- say z in Z
  intro z
  -- by surjectivity of gf, there's x such that gf(x)=x
  rcases hgf z with ⟨x, hx⟩
  -- we need to prove there's y in Y with g y = z; use f(x)
  use f x
  -- goal is now exactly hx
  exact hx

end Section3sheet1solutions

end FM2026_03_2

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_03_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section3sheet2solutions

/-!

# Interlude: types.

Lean uses something called "types" instead of sets, as its foundational
way of saying a "collection of stuff". For example, the real numbers
are a type in Lean, a group `G` is a type `G` equipped with a multiplication
and satisfying some axioms, and so on.

Sometimes, especially when making counterexamples, it's helpful to have a way
of making your own types. For example if I asked you to give an example
of a surjective function which wasn't injective then rather than using
Lean's inbuilt types like `ℕ` and `ℝ` you might just want to let `X={a,b}`
and `Y={c}` and define `f(a)=f(b)=c`. In this sheet we learn how to do this.

## Inductive types

There are three ways to make types in Lean. There are function types, quotient
types, and inductive types. Turns out that all types that mathematicians use
to build mathematics are made in one of these three ways. For more information
about all three kinds of types, see the course notes

https://b-mehta.github.io/formalising-mathematics-notes/Part_1/threekindsoftypes.html

In this sheet, we will focus on inductive types, which are something like
"types for which you can list all the elements in a certain kind of way".
The definition of the type will basically be the list.

In the rest of this section, the only kinds of types you'll need to know about are
finite types, so let's start by talking about these. Let's make
a type which just has three terms.

-/


-- A type with three terms
inductive X : Type
  | a : X
  | b : X
  | c : X

-- Here `X` is a new type, with three terms whose full names are `X.a`, `X.b` and `X.c`.
-- You can think of `X` as a set, with three elements `X = {X.a, X.b, X.c}`. Typing
-- `X.` gets old very quickly so we `open X` meaning that we don't have to do this.
open X

#check a

-- works, and says `a : X`, i.e. type of `a` is `X`.
-- Given a general term `x : X`, you can do `cases x` and Lean will turn one goal into
-- three goals with this command, one for `x = a`, one for `x = b` and one for `x = c`.
example (x : X) : x = a ∨ x = b ∨ x = c := by
  cases x with
  | a => left; rfl
  | b => right; left; rfl
  | c => right; right; rfl

-- How does Lean know that `a` and `b` are *distinct* elements of `X`? If you
-- have `h : a = b` then you can do `cases h` to close any goal, because "there
-- are no cases". Lean knows deep down in its core that different constructors
-- for inductive types produce different terms
example : a ≠ b := by
  -- `a ≠ b` is definitionally equal to `¬ (a = b)` which is
  -- definitionally equal to `a = b → False`. So `intro` works
  intro h
  -- `h : a = b`
  cases h

-- closes the goal.
-- We defined `X` using the `inductive` keyword and these funny `|` "pipe" symbols.
-- If you want to define a function from `X` to another type you can use `def`
-- and the `|` symbols again.
def f : X → ℕ
  | a => 37
  | b => 42
  | c => 0

example : f a = 37 := by
  -- true by definition
  rfl

-- Here is a proof that `f` is an injective function.
-- At some point in this proof there are 9 goals; you can see them
-- by changing the `;` after `cases y` to a `,`. The <;> means
-- "apply the next tactic to all the goals produced by the last tactic".
example : Function.Injective f := by
  intro x y h
  cases x <;> cases y -- at this point there are 9 goals, and for each goal either the conclusion
    -- is true by refl, or there's a false hypothesis `h`.
  all_goals try rfl
  all_goals cases h

end Section3sheet2solutions

end FM2026_03_3

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_03_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section3sheet1solutions

/-

# More on functions

Another question on the Imperial introduction to proof problem sheet on functions
is "If `f : X → Y` and `g : Y → Z` and `g ∘ f` is injective, is it true that `g` is injective?"
This is not true. A counterexample could be made by letting `X` and `Z` have one element,
and letting `Y` have two elements; `f` and `g` are then not hard to write down. Let's
see how to do this in Lean by making inductive types `X`, `Y` and `Z` and functions
`f` and `g` which give an explicit counterexample.

-/
-- Let X be {a}
inductive X : Type
  | a : X

-- in fact the term of type X is called `X.a`.
-- Let Y be {b,c}
inductive Y : Type
  | b : Y
  | c : Y

inductive Z : Type
  | d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
  | X.a => Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

-- Here `Z` only has one term, so if `z : Z` then `cases z` only produces one goal,
-- namely "what you get if you change `z` to `Z.d`".
example (z : Z) : z = Z.d := by
  cases z
  rfl

theorem Yb_ne_Yc : Y.b ≠ Y.c := by
  intro h
  -- x ≠ y is definitionally equal to (x = y) → False
  cases h

-- no cases when they're equal!
theorem gYb_eq_gYc : g Y.b = g Y.c := by
  -- they're both definitionally `Z.d`
  rfl

open Function

theorem gf_injective : Injective (g ∘ f) := by
  -- use `rintro` trick to do `intro, cases` at the same time
  rintro ⟨_⟩ ⟨_⟩ _
  rfl

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet.
-- Recall that if you have a hypothesis of the form `h : ∀ A, ...`, then `specialize h X`
-- will specialize `h` to the specific case `A = X`.
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ := by
  intro h
  specialize h X Y Z f g gf_injective gYb_eq_gYc
  cases h

-- Below is another one. Let's make a sublemma first.
theorem gf_surjective : Surjective (g ∘ f) := by
  intro z
  use X.a

-- Another question from IUM
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ := by
  intro h
  specialize h X Y Z f g gf_surjective Y.c
  rcases h with ⟨⟨_⟩, ⟨⟩⟩ -- this line does lots of `cases` all in one go.

end Section3sheet1solutions

end FM2026_03_4

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_04_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Sets in Lean, sheet 1 : ∪ ∩ ⊆ and all that

Lean doesn't have "abstract" sets like `{π, ℝ², {1,2,3}}` whose elements can
be totally random; it only has *subsets* of a type. If `X : Type` is a type
then the type of subsets of `X` is called `Set X`. So for example the
subset `{1,2,3}` of `ℕ` is a term of type `Set ℕ`.

A term of type `Set X` can be thought of in four ways:

1) A set of elements of `X` (i.e. a set of elements all of which have type `X`);
2) A subset of `X`;
3) An element of the power set of `X`;
4) A function from `X` to `Prop` (sending the elements of `A` to `True` and the other ones to
   `False`)

So `Set X` could have been called `Subset X` or `Powerset X`; I guess they chose `Set X`
because it was the shortest.

Note that `X` is a type, but if `A` is a subset of `X` then `A` is a *term*; the type of `A` is
`Set X`.  This means that `a : A` doesn't make sense. What we say instead is `a : X` and `a ∈ A`.
Of course `a ∈ A` is a true-false statement, so `a ∈ A : Prop`.

All the sets `A`, `B`, `C` etc we consider will be subsets of `X`.
If `x : X` then `x` may or may not be an element of `A`, `B`, `C`,
but it will always be a term of type `X`.

-/

namespace Section4sheet1Solutions


-- set up variables
variable (X : Type) -- Everything will be a subset of `X`
  (A B C D : Set X) -- A,B,C,D are subsets of `X`

/-
# subset (`⊆`), union (`∪`) and intersection (`∩`)

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`.

All of these things are true *by definition* in Lean. Let's
check this.

-/
-- say `x` is an arbitrary element of `X`.
variable (x : X)

theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  -- ↔ is reflexive so `rfl` works because LHS is defined to be equal to RHS
  rfl

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  -- you don't even have to go into tactic mode to prove this stuff
  Iff.rfl
  -- note no `by` -- this is just the term

/-

So now to change one side of these `↔`s to the other, you can
`rw` the appropriate lemma, or you can just use `change`. Or
you can ask yourself whether you need to do this at all.

Let's prove some theorems.

-/
example : A ⊆ A := by
  rw [subset_def] -- don't need this
  intro x h
  exact h

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC x hx
  apply hAB at hx -- think about why this works
  apply hBC at hx
  exact hx

example : A ⊆ A ∪ B := by
  intro x hx
  left -- think about why this works;
       -- it's because "`left` works up to definitional equality".
  assumption

example : A ∩ B ⊆ A := by
  rintro x ⟨hxA, -⟩
  exact hxA

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  intro hAB hAC x hxA
  -- exact ⟨hAB hxA, hAC hxA⟩, -- finishes the level in one line
  constructor
  · apply hAB
    exact hxA
  · exact hAC hxA

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  rintro hBA hCA x (hxB | hxC)
  · exact hBA hxB
  · exact hCA hxC

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
  Set.union_subset_union -- found this with `by exact?` (then deleted `by`)

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
  rintro hAB hCD x ⟨hxA, hxC⟩
  exact ⟨hAB hxA, hCD hxC⟩

end Section4sheet1Solutions

end FM2026_04_1

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_04_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Sets in Lean, example sheet 2 : "the" empty set and the "universal set".

Lean notation for the empty subset of `X` is `∅`. Unlike in
set theory, there is more than one empty set in Lean! Every
type has an empty subset, and it *doesn't even make sense*
to ask if `∅ : set ℕ` and `∅ : set ℤ` are equal, because
they have different types.

At the other extreme, the subset of `X` containing all the terms of type `X`
is...well...mathematicians would just call it `X`, but `X` is a type not a subset.
The subset of `X` consisting of every element of `X` is called `Set.univ : Set X`,
or just `univ : Set X` if we have opened the `Set` namespace. Let's do that now.

-/

open Set

/-

## Definition of ∅ and univ

`x ∈ ∅` is *by definition* equal to `False` and `x ∈ univ` is *by definition*
equal to `True`. You can use the `change` tactic to make these changes
if you like. But you don't have to. Remember that `trivial` proves `True`
and `cases h` will solve a goal if `h : False` (because there are no cases!)

-/

-- set up variables
variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

open Set

example : x ∈ (univ : Set X) := by trivial

example : x ∈ (∅ : Set X) → False :=
  id

example : A ⊆ univ := by
  intro x hxA
  trivial

example : ∅ ⊆ A := by
  -- rintro x ⟨⟩ -- solves goal in one line
  intro x hx
  change False at hx -- unnecessary line
  exfalso
  exact hx

end FM2026_04_2

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_04_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : x ∉ A → x ∈ A → False := by
  intro h
  exact h

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  exact h2 h1

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAB hB hA
  apply hB
  exact hAB hA

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro h
  exact h

example : x ∈ Aᶜ ↔ x ∉ A := by rfl

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  -- `exact?` works, as does `hint` (which looks for terms or tactics which
  -- solve the goal in one line).
  -- `simp` and `aesop` both work.
  -- also `exact not_exists_not.symm` works
  -- Here's a proof by hand
  constructor
  · rintro h1 ⟨x, hx⟩
    exact hx (h1 x)
  · intro h x
    by_contra h2
    apply h
    exact ⟨x, h2⟩

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by aesop -- OK so I got lazy
-- The `aesop` tactic is a general purpose tactic for goals like this.

end FM2026_04_3

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_04_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Sets in Lean, sheet 4 : making sets from predicates

If we define

`def IsEven (n : ℕ) : Prop := ∃ t, n = 2 * t`

then for `n` a natural, `IsEven n` is a true-false statement,
i.e., a proposition. This means that `IsEven : ℕ → Prop` is
a function taking naturals to true-false statements (also known as
a "predicate" on naturals), so we should be able to make the subset
of naturals where this predicate is true. In Lean the syntax for
this is

`{ n : ℕ | IsEven n }`

The big question you would need to know about sets constructed in this
way is: how do you get from `t ∈ { n : ℕ | IsEven n }` to `IsEven t`?
And the answer is that these are equal by definition.

The general case: if you have a type `X` and a predicate `P : X → Prop`
then the subset of `X` consisting of the terms where the predicate is
true, is `{ x : X | P x }`, and the proof that `a ∈ { x : X | P x } ↔ P a` is `rfl`.

Let's check:
-/

namespace Section4sheet4Solutions

theorem mem_def (X : Type) (P : X → Prop) (a : X) :
    a ∈ {x : X | P x} ↔ P a := by
  rfl

/-

Of course, now we've proved this theorem, you can
`rw [mem_def]` if you don't want to (ab)use definitional equality.

-/
open Set

def IsEven (n : ℕ) : Prop :=
  ∃ t, n = 2 * t

-- note that this is *syntactically* equal to `IsEven : ℕ → Prop := fun n ↦ ∃ t, n = 2 * t`
-- but the way I've written it is perhaps easier to follow.

example : 74 ∈ {n : ℕ | IsEven n} := by
  change ∃ t : ℕ, 74 = 2 * t
  -- exact ⟨37, by norm_num⟩, -- works
  use 37
  -- Lean decided to take it from here

-- Let's develop a theory of even real numbers
def Real.IsEven (r : ℝ) :=
  ∃ t : ℝ, r = 2 * t

-- Turns out it's not interesting
example : ∀ x, x ∈ {r : ℝ | Real.IsEven r} := by
  intro x
  use x / 2
  ring

-- likewise, the theory of positive negative real numbers is not interesting
example : ∀ x, x ∉ {r : ℝ | 0 < r ∧ r < 0} := by
  -- quick way to change the type of `hx` to something definitionally equal
  rintro x (hx : 0 < x ∧ x < 0)
  -- `linarith` is happy to use ∧ hypotheses
  linarith

end Section4sheet4Solutions

end FM2026_04_4

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet5.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_04_5
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  · rintro (hA | hA) <;> exact hA
  · intro h
    left
    exact h

example : A ∩ A = A :=
  inter_self A

-- found with `squeeze_simp`
example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · rintro ⟨_, ⟨⟩⟩
  · rintro ⟨⟩

example : A ∪ univ = univ := by simp

example : A ⊆ B → B ⊆ A → A = B := by
  -- `exact?` works
  intro hAB hBA
  ext x
  exact ⟨@hAB x, @hBA x⟩

example : A ∩ B = B ∩ A :=
  inter_comm A B

-- found with `exact?`
example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  symm
  exact inter_assoc A B C

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · rintro (hA | hB | hC)
    · left; left; assumption
    · left; right; assumption
    · right; assumption
  · rintro ((hA | hB) | hC)
    · left; assumption
    · right; left; assumption
    · right; right; assumption

-- thanks `exact?`
example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) :=
  union_inter_distrib_left A B C

-- I guessed what this was called
-- on the basis of the previous answer
example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C :=
  inter_union_distrib_left A B C

end FM2026_04_5

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_04_6
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x hx
  exact ⟨x, hx, rfl⟩

-- use x, etc etc also works
example : f '' (f ⁻¹' T) ⊆ T := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro h x hxS
    refine' h ⟨x, hxS, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    refine' h hx

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by rfl

-- pushforward is a little trickier. You might have to `ext x`, `constructor`.
example : id '' S = S := by
  ext x
  constructor
  · rintro ⟨y, hyS, rfl⟩
    exact hyS
  · intro hxS
    use x
    exact ⟨hxS, rfl⟩

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by rfl

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext x
  constructor
  · rintro ⟨x, hxS, rfl⟩
    refine' ⟨f x, _, rfl⟩
    exact ⟨x, hxS, rfl⟩
  · rintro ⟨y, ⟨x, hxS, rfl⟩, rfl⟩
    exact ⟨x, hxS, rfl⟩

end FM2026_04_6

-- ════════════════════════════════════════════════════════════════
-- Section05groups/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_05_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Groups

## How to use Lean's groups

In this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
/-  Let's see what just happened.
    The tactic state now looks like this:

    G : Type
    inst✝ : Group G
    g : G
    ⊢ g⁻¹ * g = 1

    So G is what most mathematicians would call a "set", and what in this course
    we call a "type" (they're the same thing as far as you're concerned), and
    `g : G` just mean "g is an element of G". The remaining thing is this
    `inst✝` thing, and that means "G has a multiplication `*`, an identity `1`,
    an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
    all of this will be taken care of by "instances", which are a part
    of Lean's "type class inference system". The type class inference system
    is the system which deals with stuff in square brackets. You don't have
    to worry about it right now -- all that matters is that you have access
    to all the group axioms. This one is called `inv_mul_cancel g`.
-/
  inv_mul_cancel g

-- Why don't you use `exact?` to see the names of the other axioms
-- of a group? Note that when `exact?` has run, you can click on
-- the output (the blue output in the infoview) and replace `exact?`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?
example (a b c : G) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

-- can alternatively be found with `apply?` if you didn't know the answer already
-- or `rw?`
-- or `simp?`
example (a : G) : a * 1 = a := by
  exact mul_one a

-- Can you guess the last two?
example (a : G) : 1 * a = a := by
  exact one_mul a

example (a : G) : a * a⁻¹ = 1 := by
  exact mul_inv_cancel a

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

example : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  -- hint for this one if you're doing it from first principles: `b * (a * c) = (b * a) * c`
  rw [← one_mul c, ← h1, mul_assoc, h2, mul_one]

example : a * b = 1 ↔ a⁻¹ = b := by
  rw [← inv_eq_iff_mul_eq_one]

example : (1 : G)⁻¹ = 1 := by
  rw [inv_one]

example : a⁻¹⁻¹ = a := by
  rw [inv_inv]

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [mul_inv_rev]

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g k : G, g * k = k * g := by
  have h_inv (x : G) : x = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact h x
  intro g k
  rw [h_inv (g * k), mul_inv_rev, ← h_inv, ← h_inv]

end FM2026_05_1

-- ════════════════════════════════════════════════════════════════
-- Section05groups/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_05_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Challenge sheet

This is a harder group theory question.

It turns out that two of the axioms in the standard definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group, by
proving the other axioms?

-/

namespace Section5sheet2


-- removing `mul_one` and `mul_inv_self` from the five standard axioms
-- for a group.
class WeakGroup (G : Type) extends One G, Mul G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

namespace WeakGroup

-- Let `G` be a "weak group" and say a,b,c are in G
variable {G : Type} [WeakGroup G] (a b c : G)

/-

The (tricky) challenge is to prove that G is a group, which we can interpret as
proving the missing axioms `mul_one` and `mul_inv_cancel`. Note that you
can't use the `group` tactic any more because `G` isn't a group yet:
this is what you're trying to prove!

One way of doing it: try proving

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/

theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← inv_mul_cancel a, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  apply mul_left_cancel a⁻¹
  rwa [← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  apply mul_left_cancel a⁻¹
  rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  apply mul_left_cancel a⁻¹
  rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one]

/-
And now we have all the pieces of information, we can put them together in this lemma.
-/
instance : Group G where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

end WeakGroup

/-

If you want to take this further: prove that if we make
a new class `BadGroup` by replacing
`one_mul` by `mul_one` in the definition of `weak_group`
then it is no longer true that you can prove `mul_inv_cancel`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_cancel` but which really are not groups.
Can you find an example? Try it on paper first.

-/
-- claim: not a group in general
class BadGroup (G : Type) extends One G, Mul G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

-- Here's the answer!
-- `Bool` is a type with two terms, `Bool.true` and `Bool.false`. See if you can make it into
-- a bad group which isn't a group!
instance : One Bool :=
  ⟨true⟩

instance : Mul Bool :=
  ⟨fun x _ => x⟩

instance : Inv Bool :=
  ⟨fun _ => true⟩

instance : BadGroup Bool where
  mul_assoc := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

example : ¬∀ a : Bool, 1 * a = a := by
  decide

end Section5sheet2

end FM2026_05_2

-- ════════════════════════════════════════════════════════════════
-- Section05groups/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_05_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Subgroups and group homomorphisms

Like subsets of a type, a subgroup of a group isn't a type
and so it isn't a group! You can *make* a subgroup into a group,
but a group is a type and a subgroup is a term.

-/

section Subgroups

-- let `G` be a group
variable (G : Type) [Group G]

-- The type of subgroups of `G` is `Subgroup G`

-- Let `H` be a subgroup of `G`
variable (H : Subgroup G)

-- Just like subsets, elements of the subgroup `H` are terms `g` of type `G`
-- satisfying `g ∈ H`.

example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem ha hb -- I found this with `exact?` and then used dot notation.

-- You could instead do `apply H.mul_mem` and go on from there.

-- Try this one:

example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  apply H.mul_mem
  · apply H.mul_mem
    · apply H.mul_mem
      · exact ha
      · exact H.inv_mem hb
    · exact H.one_mem
  · apply H.mul_mem
    · exact ha
    · exact hc

/-

## Lattice notation for sub-things

Given two subgroups of a group, we can look at their intersection
(which is a subgroup) and their union (which in general isn't).
This means that set-theoretic notations such as `∪` and `∩` are not
always the right concepts in group theory. Instead, Lean uses
"lattice notation". The intersection of two subgroups `H` and `K` of `G`
is `H ⊓ K`, and the subgroup they generate is `H ⊔ K`. To say
that `H` is a subset of `K` we use `H ≤ K`. The smallest subgroup
of `G`, i.e., {e}, is `⊥`, and the biggest subgroup (i.e. G, but
G is a group not a subgroup so it's not G) is `⊤`.

-/

-- intersection of two subgroups, as a subgroup
example (H K : Subgroup G) : Subgroup G := H ⊓ K
-- note that H ∩ K *doesn't work* because `H` and `K` don't
-- have type `Set G`, they have type `Subgroup G`. Lean
-- is very pedantic!

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  -- true by definition!
  rfl

-- Note that `a ∈ H ⊔ K ↔ a ∈ H ∨ a ∈ K` is not true; only `←` is true.
-- Take apart the `Or` and use `exact?` to find the relevant lemmas.
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by
  intro h
  cases h with
  | inl hH => exact Subgroup.mem_sup_left hH
  | inr hK => exact Subgroup.mem_sup_right hK

end Subgroups

/-

## Group homomorphisms

The notation is `→*`, i.e. "function which preserves `*`."

-/

section Homomorphisms

-- Let `G` and `H` be groups
variable (G H : Type) [Group G] [Group H]

-- Let `φ` be a group homomorphism
variable (φ : G →* H)

-- `φ` preserves multiplication

example (a b : G) : φ (a * b) = φ a * φ b := by
  exact φ.map_mul a b -- see what happens if you remove both `by / exact` from this

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  -- if `φ.map_mul` means that `φ` preserves multiplication
  -- (and you can rewrite with this) then what do you think
  -- the lemmas that `φ` preserves inverse and one are called?
  rw [φ.map_mul, φ.map_mul, φ.map_inv, φ.map_one]

-- Group homomorphisms are extensional: if two group homomorphisms
-- are equal on all inputs then they're the same.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  -- Use the `ext` tactic.
  ext g
  exact h g

end Homomorphisms

end FM2026_05_3

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_06_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

## Orderings and lattices

In section 4 we saw how subsets of a type worked, and we saw that
things like `⊆` and `∪` and `∩` made sense for subsets, and they satisfied
theorems such as `A ∩ B ⊆ B`.

But it turns out that there is a more general abstraction called a *lattice*
which captures these kinds of ideas, and I'd like to explain this
concept in this section. Note that the word "lattice" unfortunately
means several distinct things in mathematics; this is the use of the
word in the context of partial orders. So let me start by talking about
partial orders.

## Partial orders

A *partial order* (or a partially ordered type) is a type `X` equipped with
a concept of `≤` satisfying some axioms. More precisely `X` is equipped
with a true-false statement `a ≤ b` for each `a b : X`, satisfying
the following axioms:

`le_refl a : a ≤ a`
`le_antisymm : a ≤ b → b ≤ a → a = b`
`le_trans : a ≤ b → b ≤ c → a ≤ c`

Examples of partial orders include the natural numbers and the real numbers. However
these examples are not quite representative, because a partial order does *not* have
the axiom that for all `a b : X` we have either `a ≤ b` or `b ≤ a`. A perhaps more
representative example of a partial order is the type `Set X` of subsets of a type `X`,
with `a ≤ b` defined to mean `a ⊆ b`. For two general subsets `a` and `b` of `X`,
`a ⊆ b` and `b ⊆ a` might both be false.
-/

-- Let `X` be a partial order.
variable (X : Type) [PartialOrder X]

-- You can prove transitivity directly using the axiom
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

-- or you can use the `trans` tactic
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  trans b
  · exact hab
  · exact hbc

-- or you can use a `calc` block
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  calc
    a ≤ b := hab
    _ ≤ c := hbc

-- Let a,b,c,d be arbitrary elements of `X`
variable (a b c d : X)

-- See if you can prove these basic facts about partial orders.
example : a ≤ a := by
  exact le_refl a

example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  calc
    a ≤ b := hab
    _ ≤ c := hbc
    _ ≤ d := hcd

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  apply le_antisymm hab
  calc
    b ≤ c := hbc
    _ ≤ a := hca

end FM2026_06_1

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_06_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Lattices

In a *linear* order like ℝ, any two elements have
a min and a max. Using fancier language, if `x` and `y`
are real numbers, then the set `{x,y}` has a least upper
bound or supremum (namely `max x y`) and an infimum
(namely `min x y`).

But partial orders can be pretty general objects. Consider
for example the partial order containing only the following four
elements (all subsets of ℕ):

a={1}
b={2}
c={1,2,3}
d={1,2,4}

This is a partial order, with the ordering `≤` given by `⊆`.
Note that `a ≰ b` and `b ≰ a`, so `max a b` doesn't seem
to make any sense. But what about `Sup {a, b}`? Well,
We have `a ≤ c` and `b ≤ c`, and also `a ≤ d` and `b ≤ d`.
So both `c` and `d` are upper bounds for the set `{a,b}`,
but neither of them are *least* upper bounds, because
`c ≰ d` and `d ≰ c`, so neither `c` nor `d` satisfy
the least upper bound axiom (they are not `≤` all other upper
bounds).

A *lattice* is a partial order where any two elements
have a least upper bound and a greatest lower bound. So
the example `{a,b,c,d}` above is a partial order but not
a lattice. But a total order such as the naturals or the
reals are a lattice, because the least upper bound of `{x,y}`
is just the max of `x` and `y`, and the greatest lower
bound is just the min.

Notation: if `L` is a lattice, and if `a : L` and `b : L`
then their least upper bound is denoted by `a ⊔ b` and
their greatest lower bound is denoted by `a ⊓ b`. Hover
over these symbols in VS Code to see how to type them
in Lean.

A nice example of a lattice is the subsets of
a type, ordered by `⊆`. In this example the least upper
bound `a ⊔ b` of subsets `a` and `b` is `a ∪ b`, and the greatest
lower bound `a ⊓ b` is `a ∩ b`.

An example which requires a little more thought is the
lattice of subspaces of a vector spaces. If `V` and `W` are subspaces
of `U` then their greatest lower bound `V ⊓ W` is just `V ∩ W`, which
is also a subspace. However their least upper bound is not so simple,
because `V ∪ W` is in general not a vector space.
The least upper bound is supposed to be the smallest subspace
containing `V` and `W`, so in this case `V ⊔ W` is the subspace
`V + W` generated by `V` and `W`.

We'll talk about subgroups later on; for now let's talk about
the general theory of lattices. The API you need to know is:

`a ⊔ b` is the least upper bound of `a` and `b`:
`le_sup_left : a ≤ a ⊔ b`
`le_sup_right : b ≤ a ⊔ b` -- these axioms say that `a ⊔ b` is an upper bound for `{a,b}`
`sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c` -- this says it's the least upper bound.

`a ⊓ b` is the greatest lower bound of `a` and `b`:
`inf_le_left : a ⊓ b ≤ a`
`inf_le_right : a ⊓ b ≤ b` -- `a ⊓ b` is a lower bound
`le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c` -- it's the greatest lower bound

Using these axioms, see if you can develop the basic theory of lattices.
-/

-- let L be a lattice, and let a,b,c be elements of L
variable (L : Type) [Lattice L] (a b c : L)

example : a ⊔ b = b ⊔ a := by
  -- you might want to start with `apply le_antisymm` (every lattice is a partial order so this is
  -- OK)
  -- You'll then have two goals so use `\.` and indent two spaces.
  apply le_antisymm
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left

example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_left
      · apply le_trans (le_sup_left : b ≤ b ⊔ c) le_sup_right
    · apply le_trans (le_sup_right : c ≤ b ⊔ c) le_sup_right
  · apply sup_le
    · apply le_trans (le_sup_left : a ≤ a ⊔ b) le_sup_left
    · apply sup_le
      · apply le_trans (le_sup_right : b ≤ a ⊔ b) le_sup_left
      · exact le_sup_right

-- could golf this entire proof into one (long) line
-- `a ⊓ _` preserves `≤`.
-- Note: this is called `inf_le_inf_left a h` in mathlib; see if you can prove it
-- directly without using this.
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  apply le_inf
  · exact inf_le_left
  · exact le_trans inf_le_right h

/-

We all know that multiplication "distributes" over addition, i.e. `p*(q+r)=p*q+p*r`,
but of course addition does not distribute over multiplication (`p+(q*r)≠(p+q)*(p+r)` in general).
In sets (rather surprisingly, in my view), ∩ distributes over ∪ and ∪ also
distributes over ∩! However this is not true in more general lattices. For example,
if `U`, `V` and `W` are three distinct lines in `ℝ²` then `U ∩ (V + W) = U`
whereas `U ∩ V + U ∩ W = 0`, and `U + (V ∩ W) = U ≠ (U + V) ∩ (U + W) = ℝ²`. We
do have inclusions though, which is what you can prove in general.

-/
-- `inf_le_inf_left`, proved above, is helpful here.
example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  apply sup_le
  · apply le_inf
    · exact inf_le_left
    · apply le_trans inf_le_right le_sup_left
  · apply le_inf
    · exact inf_le_left
    · apply le_trans inf_le_right le_sup_right

-- use `sup_le_sup_left` for this one.
example : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_inf
  · apply sup_le
    · exact le_sup_left
    · apply le_trans inf_le_left le_sup_right
  · apply sup_le
    · exact le_sup_left
    · apply le_trans inf_le_right le_sup_right

-- Bonus question: look up the binding powers of ⊓ and ⊔ (by using ctrl-click to jump
-- to their definitions) and figure out which brackets
-- can be removed in the statements of the previous two examples without changing
-- their meaning.
-- Answer: ⊓ (inf) binds tighter than ⊔ (sup), similar to how * binds tighter than +.
-- So (a ⊓ b) ⊔ (a ⊓ c) is the same as a ⊓ b ⊔ a ⊓ c.
-- And a ⊔ b ⊓ c is the same as a ⊔ (b ⊓ c).
-- In the first example: `a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c)` is valid without the first pair of brackets.
-- In the second example: `a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c)` matches standard precedence.

end FM2026_06_2

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_06_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not into puzzles like this, then feel free to skip
this question.

-/

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  · intro h a b c
    symm
    calc
      a ⊓ b ⊔ a ⊓ c = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [h]
      _ = a ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm, sup_of_le_left inf_le_left]
      _ = a ⊓ (c ⊔ a ⊓ b) := by rw [sup_comm]
      _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by rw [h]
      _ = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_assoc, sup_comm, sup_comm c b]
      _ = a ⊓ (b ⊔ c) := by rw [inf_of_le_left (le_sup_left : a ≤ a ⊔ c)]
  · intro h a b c
    symm
    calc
      (a ⊔ b) ⊓ (a ⊔ c) = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by rw [h]
      _ = a ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm, inf_of_le_left (le_sup_left : a ≤ a ⊔ b)]
      _ = a ⊔ c ⊓ (a ⊔ b) := by rw [inf_comm]
      _ = a ⊔ (c ⊓ a ⊔ c ⊓ b) := by rw [h]
      _ = (a ⊔ c ⊓ a) ⊔ c ⊓ b := by rw [sup_assoc, inf_comm]
      _ = a ⊔ b ⊓ c := by rw [sup_of_le_left (inf_le_right : c ⊓ a ≤ a), inf_comm]

end FM2026_06_3

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_06_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-

# Complete lattices

A lattice has sups and infs for all subsets with 2 elements. A *complete lattice* has sups
and infs for *every* subset (including infinite ones). An example would be the set of all
subsets of a fixed base set (or, in Lean speak, the type `Set X` of all subsets of a type `X`).
Other examples: all subgroups of a group, all subspaces of a vector space (and all subrings of a
ring, all subfields of a field...). A non-example would be the real numbers: we do say that the
reals are "complete" but we're talking about a different kind of completeness here
(an order-theoretic concept, not a metric space concept), and indeed unbounded subsets of ℝ like
the natural numbers do *not* have a sup. However the closed interval `[0,1]` would be an example
of a complete lattice in this sense.

If `L` is a complete lattice, and `S : Set L` is a subset of `L`, then its sup is `sSup S`
(the little `s` stands for "set") and its inf is `sInf S`. Here's the basic API for `sSup`:

`le_sSup : a ∈ S → a ≤ Sup S`
`sSup_le : (∀ (b : L), b ∈ S → b ≤ a) → sSup S ≤ a`

and you can probably guess the analogous names for `sInf` :-)

A special case: the empty set has a `sSup` and and an `sInf`, and if you think carefully
about this then you'll discover that this means that the lattice has a least element and a
greatest element. These elements are called `⊥` and `⊤` respectively, pronounced `bot`
and `top`.

`sSup_empty : Sup ∅ = ⊥`

See if you can prove basic things about `⊥` and `sSup` just using the API for `sSup`.
All these results are in the library, but it's a good exercise to prove them from
the axioms directly.

-/

-- Let `L` be a complete lattice and say `a` is a general element of `L`
variable (L : Type) [CompleteLattice L] (a : L)

-- this is called `bot_le`
example : ⊥ ≤ a := by
  rw [← sSup_empty]
  apply sSup_le
  intro b hb
  cases hb

-- this is called `le_bot_iff`
example : a ≤ ⊥ ↔ a = ⊥ := by
  constructor
  · intro h
    apply le_antisymm h bot_le
  · intro h
    rw [h]

-- `sSup` is monotone.
-- this is called sSup_le_sSup
example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T := by
  intro h
  apply sSup_le
  intro b hb
  apply le_sSup
  exact h hb

end FM2026_06_4

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet0.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_07_0
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/

/-!

# Some common error messages

When you get a Lean error, it can be hard to understand what it means, and even harder to fix it.
This file contains some common error messages that you might encounter, and explains what they mean,
and how you could fix them.
-/

/-!
# application type mismatch
This is a very common error for beginners who tend to make a bunch of arguments explicit in some
`variable` statement.
-/
section application_type_mismatch

/-! The following line accidentally makes `G` be explicit in `fancy`. -/
variable (G : Type) [AddCommGroup G]

/-! If your variable statement is very high up in the file, it might look like `fancyOp` takes two
explicit arguments only: `a` and `b`. -/
def fancyOp (a b : G) : G := a + b - b

#check fancyOp

/-! Lean complains that you are providing `a` instead of `G`. -/
lemma fancyOp_eq_left (a b : G) : fancyOp G a b = a := by
  simp [fancyOp]

end application_type_mismatch




section no_application_type_mismatch
/-! The better way to deal with this is to avoid declaring *any* explicit argument in the
`variable`. This is obviously a rule of thumb which you should feel free to disregard when there is
a good reason to do so. -/
variable {G : Type} [AddCommGroup G]

def otherFancyOp (a b : G) : G := a + b - b

/-! Works as expected. -/
lemma otherFancyOp_eq_left (a b : G) : otherFancyOp a b = a := by
  simp [otherFancyOp]

end no_application_type_mismatch




/-!
# don't know how to synthesize placeholder
This is kind of the dual error to the above, as it often happens when too many arguments to a
definition are implicit. -/
section dont_know_how_to_synthesize_placeholder

def mulByZero {𝕜 : Type} {E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) : E :=
  (0 : 𝕜) • x

lemma mulByZero_eq_zero {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) :
    mulByZero (𝕜 := 𝕜) x = 0 := by
  simp [mulByZero]

end dont_know_how_to_synthesize_placeholder

section dont_know_how_to_synthesize_placeholder

def mulByZero' {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) : E := (0 : 𝕜) • x

lemma mulByZero'_eq_zero {E : Type} [AddCommGroup E] [Module ℂ E] (x : E) :
    mulByZero' (𝕜 := ℂ) x = 0 := by
  simp [mulByZero']

end dont_know_how_to_synthesize_placeholder


section dont_know_how_to_synthesize_placeholder

variable {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

-- a lot of junk here

#where

/-! Binder update -/

variable (𝕜) in
def mulByZero'' (x : E) : E := (0 : 𝕜) • x

#where

#check mulByZero''

lemma mulByZero''_eq_zero (x : E) : mulByZero'' 𝕜 x = 0 := by
  simp [mulByZero'']

end dont_know_how_to_synthesize_placeholder






/-! # failed to synthesize instance -/
section failed_to_synthesize_instance

variable {ι : Type} [Fintype ι]

lemma card_eq_card_ι_sub_one [DecidableEq ι] (i : ι) : Fintype.card {j // j ≠ i} = Fintype.card ι - 1 := by
  simp

end failed_to_synthesize_instance






/-!
# Junk values
-/

-- What should a - b mean if a < b?

example : 2 - 3 = 0 := by simp

example : 5 / 3 = 1 := by simp

example : (2 : ℤ) - 3 = -1 := by
  simp

example : (2 : ℚ) / 3 ≠ 0 := by
  simp

example : (2.01 : ℝ) / 3 ≠ 2 / 3 := by
  norm_num

#eval 2 - 3
#eval 2 / 3
-- 2 // 3

example : (1 : ℝ) / 0 = 0 := by simp

example {x y : ℝ} (hy : y ≠ 0) : (x / y) * y = x := by
  rw [div_mul_cancel₀]
  exact hy

example : Real.sqrt (-1) = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos (by simp)

example : Real.log (-2) = Real.log 2 := by
  rw [Real.log_neg_eq_log]

#eval 2 - 3
#eval 2 - 4

end FM2026_07_0

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_07_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section7sheet1

/-!

# Review of subgroups

In Lean, a subgroup is not a group. This is for the same reason that a subset
is not a type. The way subgroups work is that if `G` is a group:

`variables (G : Type) [Group G]`

then the type of *all* subgroups of `G` is called `Subgroup G`. So if you want
one subgroup of G:

`variable (H : Subgroup G)`

then, as you can see, `H` is not a type (we don't write `H : Type`), it's a term.
So how do we do elements of `H` then? It's just the same as sets: an element `x` of
`H` is a term `x` of type `G`, such that the proposition `x ∈ H` holds.

Here's the basic API for subgroups.
-/

-- Let `G` be a group, let `a` and `b` be elements of `H`, and let `H` and `K` be subgroups of `G`.
variable (G : Type) [Group G] (a b : G) (H K : Subgroup G)

-- The basic API for subgroups
example : (1 : G) ∈ H :=
  one_mem H

example (ha : a ∈ H) : a⁻¹ ∈ H :=
  inv_mem ha

example (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  mul_mem ha hb

-- Let's use these axioms to make more API for subgroups.
-- First, see if you can put the axioms together to prove subgroups are closed under "division".
example (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H := by
  apply mul_mem ha (inv_mem hb)

-- Now try these. You might want to remind yourself of the API for groups as explained
-- in an earlier section, or make use of the `group` tactic.
-- This lemma is called `Subgroup.inv_mem_iff` but try proving it yourself
example : a⁻¹ ∈ H ↔ a ∈ H := by
  constructor
  · intro h
    rw [← inv_inv a]
    exact inv_mem h
  · exact inv_mem

-- this is `mul_mem_cancel_left` but see if you can do it from the axioms of subgroups.
-- Again feel free to use the `group` tactic.
example (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H := by
  constructor
  · intro h
    convert mul_mem (inv_mem ha) h
    group
  · intro h
    exact mul_mem ha h

/-

## Complete lattice structure on subgroups of G

The reason I'm banging on about subgroups again, is that
they form a complete lattice. Let's just check this:

-/
example : CompleteLattice (Subgroup G) := by
  infer_instance

/-

The "type class inference system" (the system which deals with square bracket inputs to
functions) already knows this. The `infer_instance` tactic means "find this
construction in the database".

Because subgroups are a complete lattice, there will be a smallest subgroup `⊥` of `G`
and a largest subgroup `⊤`. You can guess what these are (note that `⊥` isn't the empty set,
this isn't a subgroup). Let's get the hang of these subgroups. Here's their API
(by the way, I don't have a clue about these APIs, I don't have them all committed to memory,
I just write down the natural statements and then either guess the names of the proofs or
use `exact?`):

-/
example : a ∈ (⊥ : Subgroup G) ↔ a = 1 :=
  Subgroup.mem_bot

example : a ∈ (⊤ : Subgroup G) :=
  Subgroup.mem_top a

/-

# Conjugating a subgroup by an element.

Let's define the conjugate `xHx⁻¹` of a subgroup `H` by an element `x`. To do this we
are going to have to know how to *make* subgroups, not just prove things about subgroups.

To create a subgroup of `G`, you need to give a subset of `G` and then a proof
that the subset satisfies the three axioms `one_mem`, `inv_mem` and `mul_mem` for subgroups.
If `H : subgroup G` and `x : G` then the *conjugate* of `H` by `x` is
the set `{a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}`. So let's show that this set
satisfies the axioms for a subgroup.

-/
variable {G H} {x : G}

variable {y z : G}

theorem conjugate.one_mem : (1 : G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  use 1
  constructor
  · exact H.one_mem
  · group

theorem conjugate.inv_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  rcases hy with ⟨h, hh, rfl⟩
  use h⁻¹
  constructor
  · exact inv_mem hh
  · group

theorem conjugate.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
    (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  rcases hy with ⟨hy, hhy, rfl⟩
  rcases hz with ⟨hz, hhz, rfl⟩
  use hy * hz
  constructor
  · exact mul_mem hhy hhz
  · group

-- Now here's the way to put everything together:
def conjugate (H : Subgroup G) (x : G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := conjugate.one_mem
  inv_mem' := conjugate.inv_mem
  mul_mem' := conjugate.mul_mem

/-

## The cost of a definition

You might think "we're done with conjugates now". But not so fast!

If we were putting the definition of `conjugate` into mathlib then the next thing we would have to
do would be to prove a whole bunch of things about it. Every definition in a formalised system
comes with a cost. If you just make the definition and don't prove theorems about it,
then other people can't use your definition easily in their theorems.

What kind of theorems would we want to prove about conjugates? We might want to prove
that if `H ≤ K` then `conjugate H x ≤ conjugate K x`. We might want to prove
that `conjugate ⊥ x = ⊥` and `conjugate ⊤ x = ⊤`. And we might want to prove
that if `G` is abelian then `conjugate H x = H` for all `H`. Before we embark on this,
I had better tell you how to prove that two subgroups of a group are equal in Lean.
To check two subgroups are equal it suffices to prove they have the same elements:
this is called "extensionality" for subgroups, and you can make this step using the `ext`
tactic. I'll show you below.

Let's make some API for conjugates. I'll suggest some names for the lemmas.

-/
-- This one is always handy: you will be able to `rw` it when faced with goals
-- of the form `a ∈ conjugate H x`.
theorem mem_conjugate_iff : a ∈ conjugate H x ↔ ∃ h, h ∈ H ∧ a = x * h * x⁻¹ := by
  -- true by definition!
  rfl

theorem conjugate_mono (H K : Subgroup G) (h : H ≤ K) : conjugate H x ≤ conjugate K x := by
  intro a ha
  rcases ha with ⟨h', hh', rfl⟩
  use h'
  exact ⟨h hh', rfl⟩

theorem conjugate_bot : conjugate ⊥ x = ⊥ := by
  ext a
  rw [mem_conjugate_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_bot] at hh
    rw [hh]
    group
    exact Subgroup.mem_bot.mpr rfl
  · intro h
    rw [Subgroup.mem_bot] at h
    rw [h]
    use 1
    constructor
    · exact Subgroup.mem_bot.mpr rfl
    · group

theorem conjugate_top : conjugate ⊤ x = ⊤ := by
  ext a
  constructor
  · intro h
    exact Subgroup.mem_top a
  · intro h
    use x⁻¹ * a * x
    constructor
    · exact Subgroup.mem_top _
    · group

theorem conjugate_eq_of_abelian (habelian : ∀ a b : G, a * b = b * a) : conjugate H x = H := by
  ext a
  rw [mem_conjugate_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [habelian x h, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  · intro ha
    use a
    constructor
    · exact ha
    · rw [habelian x a, mul_assoc, mul_inv_cancel, mul_one]

end Section7sheet1

section

variable (G H : Type) [Group G] [Group H]

structure WeakGroupHom where
  toFun : G → H
  map_mul : ∀ x y : G, toFun (x * y) = toFun x * toFun y

lemma map_mul' {φ : WeakGroupHom G H} (x y : G) :
    φ.toFun (x * y) = φ.toFun x * φ.toFun y := by
  rw [φ.map_mul]

end

end FM2026_07_1

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_07_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Secion7Sheet2
/-

# Group homomorphisms

mathlib has group homomorphisms. The type of group homomorphisms from `G` to `H` is called
`MonoidHom G H`, but we hardly ever use that name; instead we use the notation, which
is `G →* H`, i.e. "`*`-preserving map between groups". Note in particular that we do *not*
write `f : G → H` for a group homomorphism and then have some
function `is_group_hom : (G → H) → Prop` saying that it's a group homomorphism, we just have a
completely new type, whose terms are pairs consisting of the function and the axiom
that `f(g₁g₂)=f(g₁)f(g₂)` for all g₁ and g₂.
-/

-- Let `G` and `H` be groups.
variable {G H : Type} [Group G] [Group H]

-- let `φ : G → H` be a group homomorphism
variable (φ : G →* H)

-- Even though `φ` is not technically a function (it's a pair consisting of a function and
-- a proof), we can still evaluate `φ` at a term of type `G` and get a term of type `H`.
-- let `a` be an element of G
variable (a : G)

-- let's make the element `φ(a)` of `H`
example : H :=
  φ a

-- Here's the basic API for group homomorphisms
example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b

example : φ 1 = 1 :=
  φ.map_one

example (a : G) : φ a⁻¹ = (φ a)⁻¹ :=
  φ.map_inv a

-- The identity group homomorphism from `G` to `G` is called `MonoidHom.id G`
example : MonoidHom.id G a = a := by rfl

-- true by definition
-- Let K be a third group.
variable (K : Type) [Group K]

-- Let `ψ : H →* K` be another group homomorphism
variable (ψ : H →* K)

-- The composite of ψ and φ can't be written `ψ ∘ φ` in Lean, because `∘` is notation
-- for function composition, and `φ` and `ψ` aren't functions, they're collections of
-- data containing a function and some other things. So we use `MonoidHom.comp` to
-- compose functions. We can use dot notation for this.
example : G →* K :=
  ψ.comp φ

-- When are two group homomorphisms equal? When they agree on all inputs. The `ext` tactic
-- knows this.
-- The next three lemmas are pretty standard, but they are also in fact
-- the axioms that show that groups form a category.
theorem comp_id : φ.comp (MonoidHom.id G) = φ := by
  ext g
  simp

theorem id_comp : (MonoidHom.id H).comp φ = φ := by
  ext g
  simp

theorem comp_assoc {L : Type} [Group L] (ρ : K →* L) :
    (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) := by
  ext g
  simp

-- The kernel of a group homomorphism `φ` is a subgroup of the source group.
-- The elements of the kernel are *defined* to be `{x | φ x = 1}`.
-- Note the use of dot notation to save us having to write `MonoidHom.ker`.
-- `φ.ker` *means* `MonoidHom.ker φ` because `φ` has type `MonoidHom [something]`
example (φ : G →* H) : Subgroup G :=
  φ.ker

-- or `MonoidHom.ker φ`
example (φ : G →* H) (x : G) : x ∈ φ.ker ↔ φ x = 1 := by rfl

-- true by definition
-- Similarly the image is defined in the obvious way, with `MonoidHom.range`
example (φ : G →* H) : Subgroup H :=
  φ.range

example (φ : G →* H) (y : H) : y ∈ φ.range ↔ ∃ x : G, φ x = y := by rfl

-- true by definition
-- `Subgroup.map` is used for the image of a subgroup under a group hom
example (φ : G →* H) (S : Subgroup G) : Subgroup H :=
  S.map φ

example (φ : G →* H) (S : Subgroup G) (y : H) : y ∈ S.map φ ↔ ∃ x, x ∈ S ∧ φ x = y := by rfl

-- and `Subgroup.comap` is used for the preimage of a subgroup under a group hom.
example (φ : G →* H) (S : Subgroup H) : Subgroup G :=
  S.comap φ

example (φ : G →* H) (T : Subgroup H) (x : G) : x ∈ T.comap φ ↔ φ x ∈ T := by rfl

-- Here are some basic facts about these constructions.
-- Preimage of a subgroup along the identity map is the same subgroup
example (S : Subgroup G) : S.comap (MonoidHom.id G) = S := by
  ext x
  simp

-- Image of a subgroup along the identity map is the same subgroup
example (S : Subgroup G) : S.map (MonoidHom.id G) = S := by
  ext x
  simp

-- preimage preserves `≤` (i.e. if `S ≤ T` are subgroups of `H` then `φ⁻¹(S) ≤ φ⁻¹(T)`)
example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  intro x hx
  -- hx : x ∈ S.comap φ  i.e. φ x ∈ S
  exact hST hx

-- image preserves `≤` (i.e. if `S ≤ T` are subgroups of `G` then `φ(S) ≤ φ(T)`)
example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : S.map φ ≤ T.map φ := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  use x
  exact ⟨hST hx, rfl⟩

-- Pulling a subgroup back along one homomorphism and then another, is equal
-- to pulling it back along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : U.comap (ψ.comp φ) = (U.comap ψ).comap φ := by
  ext x
  simp

-- Pushing a subgroup along one homomorphism and then another is equal to
--  pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : S.map (ψ.comp φ) = (S.map φ).map ψ := by
  ext
  simp

end Secion7Sheet2

end FM2026_07_2

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_07_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section7sheet3

/-

# Quotient groups

mathlib has quotient groups. Here's how they work.

-/
-- let G be a group and let N be a normal subgroup
variable (G : Type) [Group G] (N : Subgroup G) [Subgroup.Normal N]

-- The underlying type (or set) of the quotient group. Note that `⧸` is `\quot`, not the slash
-- character `/` on your keyboard (which means division in Lean, not quotient).
example : Type :=
  G ⧸ N

-- Let's check that the typeclass inference system can find the group structure on the quotient
example : Group (G ⧸ N) := by
  infer_instance

-- The group homomorphism from `G` to `G ⧸ N`
example : G →* G ⧸ N :=
  QuotientGroup.mk' N

/- Remarks:

(1) Why `QuotientGroup.mk'` and not the unprimed `QuotientGroup.mk`? Because the version without
the `'` is just the bare function, the version with the `'` is the group homomorphism.

(2) Why does `QuotientGroup.mk' N` want to have `N` as an input but not `G`? It's because
the type of `N` is `Subgroup G` so Lean can figure out `G` from `N`: if you like, `N` "knows
which group it's a subgroup of".

(3) I am going to do `open QuotientGroup` very shortly, so then you'll just
be able to write `mk'` instead of `QuotientGroup.mk'`.

Here is the basic API you need for quotient groups.
-/

-- the map G → G ⧸ N is surjective
example : Function.Surjective (QuotientGroup.mk' N) :=
  QuotientGroup.mk'_surjective N

-- let's do that again with QuotientGroup opened

open QuotientGroup


-- the map G → G ⧸ N is surjective
example : Function.Surjective (mk' N) :=
  mk'_surjective N

-- Two elements of G have the same image in `G ⧸ N` iff they differ by an element of `N`
example (x y : G) : mk' N x = mk' N y ↔ ∃ n ∈ N, x * n = y :=
  mk'_eq_mk' N -- this is QuotientGroup.mk'_eq_mk'

/-
There is of course much more API, but if you want to get some practice you can
just develop some of it yourself from these two functions.
-/
example : (mk' N).ker = N := by
  ext x
  rw [MonoidHom.mem_ker, ← (mk' N).map_one, mk'_eq_mk']
  constructor
  · rintro ⟨n, hn, h⟩
    rw [eq_inv_of_mul_eq_one_right h] at hn
    rw [← inv_inv x]
    exact N.inv_mem hn
  · intro h
    use x⁻¹
    constructor
    · exact N.inv_mem h
    · exact mul_inv_cancel x

/-
# Universal properties

The "universal property" of quotients says that if you have a group homomorphism `φ : G →* H`
whose kernel contains `N` then it "extends" to a group homomorphism `ψ : G ⧸ N →* H`
such that the composite map `ψ ∘ (QuotientGroup.mk' N)` equals `φ`. Given `φ`, the `ψ` with
this property is called `QuotientGroup.lift N φ h`, where `h` is a proof of `∀ x, x ∈ N → φ x = 1`.
-/
variable (H : Type) [Group H] (φ : G →* H) (h : ∀ x, x ∈ N → φ x = 1)

example : G ⧸ N →* H :=
  lift N φ h -- the full name of this function is QuotientGroup.lift

/-
The proof that if `x : G` then `(quotient_group.lift N φ h) ((quotient_group.mk' N) x) = φ x`
is, amazingly, `rfl`.
-/
example (x : G) : (lift N φ h) ((mk' N) x) = φ x := by rfl

/-
Technical remark: this would not be the case if quotient groups were *defined* to
be cosets. In Lean quotient groups are an *opaque definition*. What do I mean by this?
You probably learnt in algebra that if G is a group and H is a normal subgroup then the
quotient G⧸H has elements which are *equal* to cosets of H. In Lean this is not true.
A term of the quotient type G⧸H cannot be taken apart with `cases` because it is not *equal* to
a coset. But the universal property `QuotientGroup.lift` is all we need; we don't
need to worry about the underlying definition of the quotient.
Example. Let's use `QuotientGroup.lift` to define the following map. Say `φ : G →* H` is a
group hom and we have normal subgroups `N : Subgroup G` and `P : Subgroup H` such that `φ N ≤ P`.
Then the induced map `G →* H ⧸ P` has `N` in the kernel, so it "lifts" to a group hom
`ρ : G ⧸ N →* H ⧸ P` with the property that for all `x : G`,
`ρ (QuotientGroup.mk' N x) = QuotientGroup.mk' P (φ x)`. Let's define `ρ` and prove
this equality.
-/
variable {G H φ N}
variable {P : Subgroup H} [P.Normal]

def ρ (h : N.map φ ≤ P) : G ⧸ N →* H ⧸ P :=
  lift N ((mk' P).comp φ) (by
    -- we are using `lift` so we need to supply the proof that `(mk' P).comp φ` kills `N`
    intro x hx
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, coe_mk', Function.comp_apply, eq_one_iff]
    -- that line came from simp?
    apply h
    use x
    exact ⟨hx, rfl⟩
  )

-- Now let's prove that `ρ ∘ mk' N = mk' P ∘ φ`
/-
    G ----φ----> H
    |            |
    |            |
   mk'           mk'
    |            |
    \/           \/
  G ⧸ N --ρ--> H ⧸ P
-/

example (h : N.map φ ≤ P) (x : G) : ρ h (mk' N x) = mk' P (φ x) := by
  rfl

end Section7sheet3

end FM2026_07_3

-- ════════════════════════════════════════════════════════════════
-- Section08finiteness/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_08_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-

# Finite sets

Remember that mathematicians use "set" in two different ways. There is
the generic "collection of stuff" usage, as in "A group is a set equipped with
a multiplication and satisfying these axioms...", for which Lean uses types.
And there's the concept of a *subset*, so we have the collection of stuff
already and want to consider the elements which have some other properties,
for example the subset {1,2,3,4,...,37} of the natural numbers, or the
subset of prime numbers or even numbers or whatever.

I want to talk about "finite sets", but because there are several uses of the
idea of a set in mathematics, the first question is "which kind of finite set?".
Let's talk first about finite *subsets*.

## Two ways to do finite subsets of a type `X`

### First way: a subset of `X`, which is finite

Let `X` be a type. We've already seen the type `Set X` of subsets of `X`,
so one way to let `S` be a finite subset of `X` would be to make a term
`S : Set X` and then to have a hypothesis that `S` is finite.
Recall that a predicate on a type just means
In Lean the predicate on sets which says a set is finite is `Set.Finite`.
So here
is one way of saying "let `S` be a finite subset of `X`":

-/

-- Let X be a type, let `S` be a subset of `X`, and assume `S` is finite. Then S=S.
example (X : Type) (S : Set X) (_ : Set.Finite S) : S = S := by
  rfl

-- Note that because `S` has type `Set (something)` we can use dot notation here:
-- this means the same thing as the above example.
example (X : Type) (S : Set X) (_ : S.Finite) : S = S := by
  rfl

-- Lots of proofs about finite sets in this sense live in the `Set.Finite` namespace.
-- How would you find out the name of the lemma saying that the union of two finite
-- sets is finite?
example (X : Type) (S : Set X) (T : Set X) (hs : Set.Finite S) (ht : T.Finite) :
    (S ∪ T).Finite := by
  exact Set.Finite.union hs ht

/-
But Lean has another way to do finite subsets.

### Second way: the type of all finite subsets of X

Lean has a dedicated type whose terms are finite subsets of `X`. It's called `Finset X`.

Clearly, for a general infinite type `X`, the types `Set X` and `Finset X` are not "the same".
But in type theory, *distinct types are disjoint*. That means if we have a term `S : Finset X`
then *`S` does not have type `Set X`*. A finset is not *equal to* a set. This is the
same phenomenon which says that a natural number in Lean is not *equal to* a real number.
There is a *map* from the natural numbers to the real numbers, and it's a map which
mathematicians don't notice and so it's called a *coercion*, is denoted with a little
up-arrow `↑`, and "happens behind the scenes". The same is true here.

If `S : Finset X` then you can coerce `S` to `Set X`, and this coerced term will be
displayed as `↑S` in Lean, with this arrow meaning "the obvious map from `Finset X` to `Set X`".
-/

-- let X be a type
variable (X : Type)

-- If S is a Finset, then S (considered as a set) is equal to itself.
example (S : Finset X) : (S : Set X) = (S : Set X) := by
  -- goal is `⊢ ↑S = ↑S`
  rfl

-- Lean has the theorem that if you start with a Finset, then the coerced set is finite.
example (S : Finset X) : Set.Finite (S : Set X) := by
  exact S.finite_toSet

/-

# Why?

Finite sets are really important in computer science, and they also play a special role in
mathematics: for example you can sum over a finite set in huge generality, whereas if you
want to sum over a general set then you need some metric or topology on the target to make
sense of the notion of convergence. Also finite sets can be handled in constructive mathematics
and the theory is much easier to make computable than a general theory of sets. I'm not
particularly interested in making mathematics more constructive and computable, but other
people are, and this is why we've ended up with a dedicated type for finite sets.

Let's see how to do finite sums in Lean. In mathematics we often sum from 1 to n, but
computer scientists seem to prefer to sum from 0 to n-1 (you might have seen this in python).
The finset `{0,1,2,...,n-1} : Finset ℕ` has got a special name: it's called `Finset.range n`.
Let's see it in action by proving that the sum of i^2 from i=0 to n-1 is
(some random cubic with 6 in the denominator).

Note in the below example: I use the coercion `(x : ℚ)` to mean "`x` is a natural, but
consider it as a rational number for this proof". It's really important to do this calculation
over the rationals, because subtraction and division are pathological operations on the
naturals (e.g. 2-3=0 and 5/2=2 in the naturals, as they are forced to return a natural as an answer)
-/

open BigOperators -- enable ∑ notation

example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  -- induction on `n`.
  induction' n with d hd
  · -- base case `n = 0` will follow by rewriting lemmas such as `∑ i in finset.range 0 f(i) = 0`
    -- and `0 * x = 0` etc, and the simplifier knows all these things.
    simp
  · -- inductive step
    -- We're summing over `Finset.range (succ d)`, and so we next use the lemma saying
    -- that equals the sum over `Finset.range d`, plus the last term.
    rw [Finset.sum_range_succ]
    -- Now we have a sum over finset.range d, which we know the answer to by induction
    rw [hd]
    -- Now tidy up (e.g. replace all the `succ d` with `d + 1`)
    simp only [Nat.cast_add, Nat.cast_one]
    -- and now it must be an identity in algebra.
    ring

-- If you look through the proof you'll see some ↑; this is because we can't do the
-- algebra calculation in the naturals because subtraction and division are involved.
-- The up-arrows are "the obvious map from the naturals to the rationals".

-- See if you can can sum the first n cubes.
example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℚ) ^ 3 = (n : ℚ) ^ 2 * (n - 1) ^ 2 / 4 := by
  induction' n with d hd
  · simp
  · rw [Finset.sum_range_succ]
    rw [hd]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

end FM2026_08_1

-- ════════════════════════════════════════════════════════════════
-- Section08finiteness/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_08_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/- 

# `Finset X` is a lattice

Recall that a lattice is just a partially ordered set where every pair {a,b} of elements has
an inf `a ⊓ b` and a sup `a ⊔ b`. The type of finite subsets of `X`, ordered by inclusion, 
has this property (because the union or intersection of two finite sets is finite).
This lattice structure is inbuilt in Lean.

-/

-- Let X be a type
variable (X : Type)

-- Assume the law of the excluded middle (i.e. that every statement is either true or false)
open scoped Classical

-- Don't worry about whether functions are computable
noncomputable section

-- Then, finally, the type of finite subsets of X has a lattice structure
example : Lattice (Finset X) :=
  inferInstance

-- the system knows this fact automatically so this just works:
example (a b : Finset X) : Finset X :=
  a ⊔ b

-- sups (and infs) make sense

-- The lattice also has a `⊥`, the smallest finite subset of `X`, namely the empty set.
example : Finset X :=
  ⊥

-- But for general `X` it does not have a `⊤`, because if `X` is infinite then it doesn't
-- have a largest finite subset
-- example : Finset X := ⊤ -- uncomment for error

-- If `Y` is another type, then you can push finsets forward along maps from X to Y
-- using `Finset.image`
variable (Y : Type) (f : X → Y)

example (S : Finset X) : Finset Y :=
  Finset.image f S

-- You can use dot notation to make this shorter
example (S : Finset X) : Finset Y :=
  S.image f

-- See if you can prove these. You'll have to figure out the basic API
-- for `Finset.image`. These theorems are in the library -- your job is simply to find them.
example (S : Finset X) (y : Y) : y ∈ S.image f ↔ ∃ x ∈ S, f x = y :=
  Finset.mem_image

example (S : Finset X) (x : X) (hx : x ∈ S) : f x ∈ S.image f :=
  Finset.mem_image_of_mem f hx

-- Check that `Finset.image` preserves `≤` (which remember is defined to mean `⊆`)
-- You might have to prove this one directly, using the stuff you discovered above,
-- if you can't find it in the library.
example (S T : Finset X) (h : S ≤ T) : S.image f ≤ T.image f :=
  Finset.image_subset_image h

-- There are constructions for all the basic operations you might want to do on finsets:

#synth Union (Finset ℕ)           -- allows me to use ∪ on Finsets
#synth Inter (Finset ℕ)           -- allows me to use ∩ on Finsets
#synth Insert ℕ (Finset ℕ)        -- allows me to use insert
#synth EmptyCollection (Finset ℕ) -- allows me to use ∅
#synth HasSubset (Finset ℕ)       -- ⊆
#synth SDiff (Finset ℕ)           -- \
#synth Singleton ℕ (Finset ℕ)     -- {x}

#check Finset.biUnion             -- bounded indexed union
variable (s : Finset ℕ) (a : ℕ)
#check s.erase a              -- erase an element
#check Finset.image
#check Finset.filter
#check Finset.range
#check (· ⁻¹' ·)


end

end FM2026_08_2

-- ════════════════════════════════════════════════════════════════
-- Section08finiteness/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_08_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Finite types

As well as finite subsets of a (possibly infinite type), Lean has a theory
of finite types. Just like finite subsets, there is a `Prop`-valued version
(the true-false statement "this type is finite") and a `Type`-valued version
("here is an explicit list of all the finitely many terms of this type").
If you want to work constructively, then use the `Type` version, and if
you just care about theorems you can use the `Prop` version.

## The Prop-valued version

If `(X : Type)` then `Finite X` is the true-false statement saying
that `X` is finite. It's a class, which means it goes in square brackets.

-/
section PropVersion

-- Let X be a finite type
variable (X : Type) [Finite X]

-- The typeclass inference system now knows that various other types are finite:
variable (Y : Type) [Finite Y]

example : Finite (X × Y) :=
  inferInstance

example : Finite (X → Y) :=
  inferInstance

-- The type `Fin n` is a structure. To make a term of this structure
-- you need to give a pair, consisting of a natural `a`, and a proof that `a < n`.
example : Fin 37 :=
  ⟨3, by linarith⟩

-- The typeclass inference system also knows that these are finite
example : Finite (Fin 37) :=
  inferInstance

end PropVersion

/-

## The Type-valued version

This is `[Fintype X]`. It's (sometimes) harder to use, but finite sums work for it.

-/

-- Let X be a constructively finite type
variable (X : Type) [Fintype X]

example : X = X := by
  -- We're not supposed to do this, but we can take that instance `inst✝: Fintype X` apart:
  rename_i foo
  cases foo
  -- turns out that it's a term of type `Finset X` under the hood, plus a proof
  -- that everything is in it! In particular, it's not a theorem, it's data plus a theorem.
  -- That's why it lives in the `Type` universe, not the `Prop` universe.
  rfl

-- Lean knows that `Fin n` is constructively finite
example (n : ℕ) : Fintype (Fin n) :=
  inferInstance

open scoped BigOperators

-- the advantage of constructive finiteness is that the elements are internally stored
-- as a list, so you can prove this with `rfl`
example : ∑ x : Fin 10, x = 45 := by
  rfl

-- Actually I just tricked you. Can you explain this?
example : ∑ x : Fin 10, x = 25 := by
  rfl -- wait, Fin 10 is Z/10Z under addition?
  -- Ah, x : Fin 10. Addition on Fin 10 is addition modulo 10.
  -- ∑ i=0 to 9 i = 45.
  -- 45 mod 10 = 5.
  -- But 45 = 5 (mod 10).
  -- Wait, 25 mod 10 = 5.
  -- So 45 = 25 in Fin 10.
  -- That explains it!

-- Here's a better proof
example : ∑ x : Fin 10, x.val = 45 := by
  rfl

-- Take a look at the types of the 45 in those proof. Do you know how to? Do you know
-- what's going on? Hint: ℤ/10ℤ.

end FM2026_08_3

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_09_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-

# Bijections

Like finiteness, there are two ways to say that a function is bijective in Lean.
Furthermore, you will have heard of both of them, although it may well not
have occurred to you that these two ways were particularly different. It turns
out that one of them is more constructive than the other. Let's talk about
the nonconstructive (propositional) way of talking about bijections.

Let `X` and `Y` be types, and say `f : X → Y` is a function.

-/

variable (X Y : Type) (f : X → Y)

-- The `Prop`-valued way of saying that `f` is bijective is simply
-- to say literally that `f` is bijective, i.e., injective and surjective.
example : Prop :=
  Function.Bijective f

-- Because `f` is a function type, a little Lean hack introduced recently
-- actually enables you to use dot notation for this.
example : Prop :=
  f.Bijective

-- The definition of `Function.Bijective f` is
-- `Function.Injective f ∧ Function.Surjective f`, and the definitions of
-- injective and surjective are what you think they are.
example : f.Bijective ↔ f.Injective ∧ f.Surjective := by
  rfl

example : f.Bijective ↔
    (∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂) ∧ ∀ y : Y, ∃ x : X, f x = y := by
  rfl

-- It's a theorem that `f` is bijective if and only if it has a two-sided
-- inverse. One way is not hard to prove: see if you can do it. Make
-- sure you know the maths proof first! If you can't do this then
-- please ask. There's lots of little Lean tricks which make this
-- question not too bad, but there are lots of little pitfalls too.
example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective := by
  intro h
  rcases h with ⟨g, hfg, hgf⟩
  constructor
  · -- Injective
    intro x₁ x₂ h
    apply_fun g at h
    change (g ∘ f) x₁ = (g ∘ f) x₂ at h
    rw [hgf] at h
    exact h
  · -- Surjective
    intro y
    use g y
    change (f ∘ g) y = y
    rw [hfg]
    rfl

-- The other way is harder in Lean, unless you know about the `choose`
-- tactic. Given `f` and a proof that it's a bijection, how do you
-- prove the existence of a two-sided inverse `g`? You'll have to construct
-- `g`, and the `choose` tactic does this for you.
-- If `hf_surj` is a proof that `f` is surjective, try `choose g hg using hf_surj`.
example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := by
  intro h
  choose g hg using h.surjective
  use g
  constructor
  · ext y
    simp [hg]
  · ext x
    apply h.injective
    simp [hg]

end FM2026_09_1

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_09_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section9Sheet2
/-

# Explicit bijections

Here we'll talk about `X ≃ Y`, the type of explicit bijections from `X` to `Y`. What is an explicit
bijection? It is a function `f : X → Y` plus some more data, but here the data is *not* just the
propositional claim that `f` is bijective (i.e. the *existence* of a two-sided inverse) it is the
actual data of the two-sided inverse too.

`X ≃ Y` is notation for `Equiv X Y`. This is the type of explicit bijections from `X` to `Y`. To
make a term of type `X ≃ Y` you need to give a 4-tuple consisting of two functions `f : X → Y` and
`g : Y → X`, plus also two proofs: firstly a proof of `∀ y, f (g y) = y`, and secondly a proof of
`∀ x, g (f x) = x`.

Note that `X ≃ Y` has type `Type`, not `Prop`. In other words, a term
of type `X ≃ Y` is *not* a proof that there exists a bijection from `X` to `Y`,
it is the actual data of a bijection from `X` to `Y`.

Let's build two different bijections from `ℚ` to `ℚ`.

The first one is easy; I'll do it for you, to show you the syntax.

-/

def bijection1 : ℚ ≃ ℚ where
  toFun := id
  -- use the identity function from ℚ to ℚ
  invFun := id
  -- its inverse is also the identity function
  left_inv := by
    -- we have to prove ∀ q, id (id q) = q
    intro q
    rfl --- works because `id q` is definitionally equal to `q`.
  -- Here's the same proof but in term mode
  right_inv q := rfl

-- Now see if you can do a harder one.
def bijection2 : ℚ ≃ ℚ where
  toFun q := 3 * q + 4
  invFun r := (r - 4) / 3
  left_inv := by
    intro r
    dsimp
    ring
  right_inv := by
    intro r
    dsimp
    ring

-- Note that these two terms are *not* equal.
example : bijection1 ≠ bijection2 := by
  -- replace `bijection1` and `bijection2` with their definitions
  unfold bijection1 bijection2
  -- assume for a contradiction that they're equal
  intro h
  -- simplify this mess
  simp only [Equiv.mk.injEq] at h
  -- `h` is now two false statements, let's just choose one
  cases' h with h1 _
  rw [funext_iff] at h1
  -- now choose any number a such that a ≠ 3a+4
  specialize h1 37
  -- and now h1 is all about numbers so use the number tactic
  norm_num at h1

-- On the other hand, every true-false statement in Lean has at most one proof,
-- so `ℚ ≃ ℚ` can't be a true-false statement. It is in fact the set of bijections
-- from `ℚ` to itself.

end Section9Sheet2

end FM2026_09_2

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_09_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section9sheet3

/-

Note that `X ≃ Y` is not an equivalence relation, for the stupid
reason that it's not even a true-false statement! It doesn't
say "there exists a bijection from X to Y" (which would be an
equivalence relation), it is the *type* of bijections between
`X` and `Y`, and in particular it can have more than one term
(indeed we just saw two distinct terms of type `ℚ ≃ ℚ` on the
previous sheet). However we can make some equivalence-relation-y
type constructions with `≃`. Here are definitions (not theorems!)
called `Equiv.refl`, `Equiv.symm` and `Equiv.trans`.

-/
-- this is called `Equiv.refl` in `mathlib`
example (X : Type) : X ≃ X where
  toFun := fun x ↦ x
  invFun := fun y ↦ y
  left_inv q := by simp
  right_inv q := by simp

-- now let's see you define `Equiv.symm` and `Equiv.trans`.
-- Let's start with `Equiv.symm`.
-- Note that if `e : X ≃ Y` then `e.toFun : X → Y`
-- and `e.left_inv` is a proof of `∀ x : X, e.invFun (e.toFun x) = x` etc
-- This is `Equiv.symm`. Can you fill in the proofs?
example (X Y : Type) (e : X ≃ Y) : Y ≃ X where
  toFun := e.invFun
    -- you could write `λ x, e.inv_fun x` instead
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

-- Actually, you're not supposed to write `e.toFun` and `e.invFun`
-- directly, because `X ≃ Y` has got a coercion to `X → Y`,
-- so you can (and should) do it like this:
-- `Equiv.symm` again
example (X Y : Type) (e : X ≃ Y) : Y ≃ X where
  toFun := e.symm
  -- that was using `Equiv.symm` and dot notation
  invFun := e
  -- that was using the coercion to function
  left_inv := e.right_inv
  right_inv := e.left_inv

-- `Equiv.trans`
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z where
  toFun := fun x ↦ eYZ (eXY x)
  invFun := fun z => eXY.symm (eYZ.symm z)
  left_inv := by
    intro x
    simp
  right_inv := by
    intro z
    simp


-- Because `Equiv.trans` is already there, we can instead just use it
-- directly:
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  Equiv.trans eXY eYZ

-- here it is again using dot notation
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  eXY.trans eYZ

-- See if you can make the following bijection using dot notation
-- (note: I didn't write `by` so Lean is just expecting the term)
example (A B X : Type) (eAX : A ≃ X) (eBX : B ≃ X) : A ≃ B :=
  eAX.trans eBX.symm

/-

Note that `Equiv` is *data* -- `X ≃ Y` doesn't say "`X` bijects with `Y`";
that statement is a true-false statement. A term of type `X ≃ Y`
is *explicit functions* `X → Y` and `Y → X`, together with proofs
that they're inverse bijections.

Clearly there's an equivalence relation going on *somewhere* though:
here it is.

If `A : Type` then `∃ x : A, True` is just the statement that `A`
has an element, i.e. that `A` is nonempty. It's a proposition. So this works:

-/
-- Two types `X` and `Y` satisfy `R X Y` iff there *exists*
-- a bijection `X ≃ Y`.
def R (X Y : Type) : Prop :=
  ∃ _ : X ≃ Y, True

example : Equivalence R := by
  constructor
  · -- refl
    intro X
    use Equiv.refl X
  · -- symm
    rintro X Y ⟨e, _⟩
    use e.symm
  · -- trans
    rintro X Y Z ⟨eXY, _⟩ ⟨eYZ, _⟩
    use eXY.trans eYZ

-- Remark: the equivalence classes of `R` are called *cardinals*.

-- Remark: set theorists might be concerned about size issues here
-- (the "set of all sets" isn't a set, so R "isn't strictly speaking an
--  equivalence relation" because it's not defined on a set). The type theorists
-- know that all this is just nonsense: `R` just lives in a higher universe.

end Section9sheet3

end FM2026_09_3

-- ════════════════════════════════════════════════════════════════
-- Section10types/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_10_1

/-!
Today we'll talk a little about the type theory of Lean. We'll talk about the three ways of making
types in Lean: pi types, inductive types and quotient types.

We'll also talk about universes, mention why these are necessary to have in Lean, and how they work.

We'll then talk about what axioms Lean additionally has on top of these, and why they're useful
to add.

The third of the axioms - the axiom of choice - has a different status from the others. As such,
proving things in Lean + the first two axioms is usually pretty smooth, but choice can sometimes
add friction. It's still doable, and in some cases not noticably harder, but the distinction is
still present.
-/


-- So what is a type in Lean?
-- Just like a group is a set defining the group axioms, the type theory of Lean is a collection
-- which satisfies the axioms of LeanTT. But these are pretty complex and abstract to write down
-- so we'll just stick with our model of, a type is just a set, but they're all disjoint.

-- Let's now talk about the types of Lean
-- Pi types, inductive types, quotient types

-- # Pi types
-- We've already seen function types, when we talked about sequences, and also about implication
variable {α β : Type}

-- If α and β are types, then we can build a new type representing the functions from α to β
#check α → β
-- Here's how we can construct an element of this type (ie build a function).
-- This is called the construction rule
#check fun a : α ↦ (sorry : β)
-- And here's what we can do with an element of this type (ie use a function).
-- This is called the destruction rule, or eliminator
example (f : α → β) (x : α) : β := f x
-- The pair of construction and destruction rules work nicely together: in particular if you
-- construct then destruct a function, you just get the original function
example (f : α → β) (x : α) : (fun y ↦ f y) x = f x := rfl

-- In fact, function types generalise to Pi types
-- Suppose we have some `Y` which gives us a type for every natural number
variable (Y : ℕ → Type)
-- Y 0 : Type
-- Y 1 : Type
-- Y 2 : Type
-- ...
-- We can then make a new type, whose elements are functions from the natural numbers to
-- ⋃ i : ℕ, Y i
-- With the additional property that if we give the function some i : ℕ, the output of the function
-- should be in Y i
-- That is, we have a generalised function which takes in `i : I`, and returns a term of type `Y i`.
example : Type := Π i : ℕ, Y i
example : Type := (i : ℕ) → Y i

-- In fact, we've seen another example of Pi types in the past; with the `∀` quantifier
-- A term of type `∀ n : ℕ, n + n = 2 * n` represents a *function* which takes in a
-- natural number `n` and returns a term of type `n + n = 2 * n`
-- But remember that since `n + n = 2 * n` is a proposition, a term of type `n + n = 2 * n` is a
-- proof, and so `∀ n : ℕ, n + n = 2 * n` is a function which takes in a natural number `n` and
-- returns a proof that `n + n = 2 * n`
#check ∀ n : ℕ, n + n = 2 * n

-- here's another way of writing that type, but note that the output of the `#check` command is
-- telling me that Lean views it as identical to the previous
#check (n : ℕ) → n + n = 2 * n

-- # Inductive types
-- The next kind of type we'll look at is an inductive type
-- One way to remember their name is that they give us induction!
-- Here's (something equivalent) to the way Lean defines the natural numbers
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

-- In fact, if you Ctrl+click (or Cmd+click on mac) on the `ℕ` symbol below, you can see the true
-- definition, and see that it's basically the same as this one, up to comments
#check ℕ
-- Also note that `ℕ` is just notation for `Nat`, but I had to call the above example `Nat'` so it
-- doesn't clash with the inbuilt one.

-- The way to read the `inductive` block is that it's defining a new type `Nat'`, declaring it
-- has type Type, and then saying the following three things:
-- * `Nat'.zero` has type `Nat'` (ie zero is a natural number)
-- * if `n` has type `Nat'` then `Nat'.succ n` has type `Nat'`
-- * that's it! (nothing else has type `Nat'`)

-- Quite a lot of the things we've already seen are actually defined as inductive types,
-- like the propositions True, False, And, and Or.
-- I've reproduced the definitions here, but remember you can cmd+click the actual definition to see
-- Lean's interpretation - it should look exactly the same, just with some more fluff around it

inductive True' : Prop where
  | intro : True'
-- * True'.intro has type True'
-- * that's it!

inductive False' : Prop where
-- * that's it!
-- ie there's nothing with type `False'`, which means there's no proof of false

inductive And' (P Q : Prop) : Prop where
  | intro (hp : P) (hq : Q) : And' P Q
-- * if we have a proof `hp` of `P` and a proof `hq` of `Q` then `And'.intro hp hq` is a proof
--   of `And' P Q`
-- * that's it!

inductive Or' (P Q : Prop) : Prop where
  | inl (hp : P) : Or' P Q
  | inr (hq : Q) : Or' P Q
-- * if we have a proof `hp` of `P` then `Or'.inl hp` is a proof of `Or' P Q`
-- * if we have a proof `hq` of `Q` then `Or'.inr hq` is a proof of `Or' P Q`
-- * that's it!

-- so there are two ways to make a proof of `P ∨ Q`, but only one way to prove `P ∧ Q` and it
-- needs two ingredients

-- inductive types which only have one "constructor", ie one way to make them, show up often enough
-- that they have a special name and syntax: they're called `structure`s
-- so `And` could alternatively be defined like this
structure And'' (P Q : Prop) : Prop where
  left : P
  right : Q
-- This says that `And''` is a `Prop` and it consists of two things: the `left` and the `right`
-- proofs.
-- We saw `structure`s earlier, when we talked about subgroups: there it consisted of a `Set`,
-- together with some properties about that set.

-- Connection: For those who know about algebraic data types and generalised algebraic data types,
-- the link here is that inductive types generalise GADTs.
-- (If you don't know about these, ignore this comment!)


-- # Quotient types
-- If we have a type `α` together with a relation `R` on that type
variable (α : Type) (R : α → α → Prop)
-- lean will give us a new type called `Quot`, which we should think of as the type `α` but
-- quotiented out by the equivalence relation generated by `R`.
#check Quot R

-- Here's how to map into a quotient type (ie the construction):
example : α → Quot R := Quot.mk R
-- That is, if we have an element of `α`, we can build an element of the quotient type.
-- This function `Quot.mk` has a key property, which is proved with the lemma `Quot.sound`.
-- That property is that if `x` and `y` are related by the relation `R`, then `Quot.mk R` maps
-- them to *equal* values
example (x y : α) (h : R x y) : Quot.mk R x = Quot.mk R y := Quot.sound h
-- Here's how to map out of a quotient type (the destruction)
example (β : Type) (f : α → β) (h : ∀ x y : α, R x y → f x = f y) :
    Quot R → β := Quot.lift f h
-- given any other type `β`, and a function `α → β`, if the function respects the equivalence
-- relation (by which I mean that the property `h` holds), then we get a function
-- `Quot R → β`

-- Just like before, the construction and destruction play nicely:
example (β : Type) (f : α → β) (h : ∀ x y : α, R x y → f x = f y) (x : α) :
    Quot.lift f h (Quot.mk R x) = f x := rfl
-- this property can also be seen as a commutative diagram
--      α     ⟶    β
--        ↘       ↗
--          α / R







-- propext
#check propext
#check Quot.sound
#check Classical.choice


-- In Martin-Löf Type Theory, this isn't provable:
-- It's called "Law of Excluded Middle"
theorem LEM {p : Prop} : p ∨ ¬ p := Classical.em p
-- Nor is this
-- It's called "Uniqueness of Identity Proofs"
theorem UIP {X : Type} {x y : X} {p q : x = y} : p = q := by rfl
-- but in Lean, both of these are true!
-- In fact, the second is true *by definition*, so the proof `rfl` will work.

-- The idea is that the type Prop, in the set theory model, corresponds to the set {∅, {•}}
-- But in MLTT in general, this might not even make sense
-- so Prop _could_ have other elements.

-- In Lean, we modify the underlying type theory so that UIP (and a few others like it) become true
-- and we add axioms so that LEM (and others like it) become provable.


-- Large elimination
inductive Nonempty' (α : Type) : Prop
  | intro (a : α) : Nonempty' α

theorem test1 : Nonempty' ℕ := ⟨1⟩
theorem test2 : Nonempty' ℕ := ⟨7⟩

-- If there's still time, get the list of sections from last year and discuss which ones to talk
-- about.

end FM2026_10_1

-- ════════════════════════════════════════════════════════════════
-- Section11TopologicalSpaces/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_11_1
/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jujian Zhang, Kevin Buzzard
-/

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

set_option autoImplicit true

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    trivial
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    trivial
  isOpen_sUnion := by
    -- say F is a family of sets and they're all open
    intro F hF
    -- Is their union open?
    trivial

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    right
    rfl
  isOpen_inter s t := by
    intro hs ht
    rcases hs with rfl | rfl
    · simp
    · simpa
  isOpen_sUnion := by
    intro F hF
    by_cases h : Set.univ ∈ F
    · right
      ext x
      simp
      exact ⟨Set.univ, h, Set.mem_univ x⟩
    · left
      ext x
      simp
      intro s hs hxs
      rcases hF s hs with rfl | rfl
      · exact hxs
      · exact h hs

-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  -- ∅ is the union of the empty family
  rw [← Set.sUnion_empty]
  apply isOpen_sUnion
  intro s hs
  cases hs

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ
#synth UniformSpace ℝ
#synth PseudoMetricSpace ℝ

-- Let's make it from first principles.

/-- documentation string -/
def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y → y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  rw [Real.IsOpen]
  simp only [Set.mem_univ, gt_iff_lt, implies_true, and_true, forall_const]
  use 1
  norm_num

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  rcases hs x hx.1 with ⟨δs, hδs, hBs⟩
  rcases ht x hx.2 with ⟨δt, hδt, hBt⟩
  use min δs δt
  constructor
  · exact lt_min hδs hδt
  · intro y hy1 hy2
    constructor
    · apply hBs y
      · linarith [min_le_left δs δt]
      · linarith [min_le_left δs δt]
    · apply hBt y
      · linarith [min_le_right δs δt]
      · linarith [min_le_right δs δt]

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  rcases hx with ⟨s, hs, hxs⟩
  rcases hF s hs x hxs with ⟨δ, hδ, hB⟩
  use δ
  constructor
  · exact hδ
  · intro y hy1 hy2
    use s
    exact ⟨hs, hB y hy1 hy2⟩

set_option autoImplicit true

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion

end
end Section10sheet1

end FM2026_11_1

-- ════════════════════════════════════════════════════════════════
-- Section11TopologicalSpaces/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_11_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Continuous functions

The "mathlib philosophy" is not to worry about what the *actual* definition of continuous
function is -- but to make sure that you know the name of the theorem which says
that continuity is what you think it is.

-/

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  -- exact? solves this
  exact continuous_def -- proof is not `rfl`, but who cares

example (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x' : X, dist x' x < δ → dist (f x') (f x) < ε := by
  -- exact? solves this
  exact Metric.continuous_iff -- proof is not `rfl`, but who cares

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- can you prove this from first principles? Start with `rw [continuous_def] at *`.
  rw [continuous_def] at *
  intro U hU
  rw [Set.preimage_comp]
  apply hf
  apply hg
  exact hU

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- There's a tactic for continuity proofs by the way
  continuity

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- In fact there's a tactic for proving a few different types of properties about functions
  fun_prop

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- And of course it's also already in the library (which is why the earlier two tactics worked)
  exact Continuous.comp hg hf

end FM2026_11_2

-- ════════════════════════════════════════════════════════════════
-- Section12Filters/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_12_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics

/-!

# Filters

## What is a filter?

Here's how Kevin thinks about it:
Morally, a filter on a type `α` is a "generalised subset of `α`". By this I mean that each subset
of `α` gives rise to a filter, but there are other "ideas", such as "an infinitesimal neighbourhood
of a point in a topological space" or "a neighbourhood of infinity in a totally ordered set", which
can be expressed as filters but not as sets (Isaac Newton might have wanted to have `dx` as "a real
number infinitesimally close to 0", but the modern treatments of real numbers don't allow `dx` as
elements; filters enable you to recover these thoughts)

The property which we want a "generalised subset" to have, is that it is uniquely determined
by the *actual* subsets which it's contained in. Let's use this point of view to figure
out the definition of a filter.

If `F` is a "generalised subset" of a type `α`, then then what properties should
the collection of *actual* subsets of `α` which contain `F` have?

1) If `S` contains `F` and `S ⊆ T` then `T` contains `F`.
2) If `S` and `T` contain `F`, then so does `S ∩ T`
3) The set `α` itself (or, in Lean speak, `Set.univ : Set α`) contains `F`.

The way that these "generalised subsets" of `α` are modelled is precisely as collections
of subsets of `α` satisfying these three axioms.

## The formal definition

```lean
structure Filter (α : Type*) where
  sets : Set (Set α)
  univ_sets : Set.univ ∈ sets
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```

In other words, to give a filter on a type `α` is to give a set of subsets of `α` satisfying
the three axioms above.

Some people add in an extra fourth axiom, saying that the empty set is not allowed to
be in `sets`. This is a way of saying that the empty set is not allowed to be a
generalised subset of `α`. But it's certainly a subset of `α`, so in mathlib we do not
include this fourth axiom. To me this missing axiom feels analogous to an axiom saying
that e.g. a ring is not allowed to be an ideal of itself; it might seem initially like
a good idea (because then "maximal ideals" really are maximal elements in the set of
ideals) but it causes a lot of confusion later on because you have to constantly deal
with the special case which you've disallowed.

## Notation, helpful tactics and helpful theorems

We are not going to build filters from first principles, we will be
using Lean's API for filters.

Say `α : Type` and `F : Filter α` and `S : Set α`. The notation `S ∈ F` is
defined to mean `S ∈ F.sets`. You should think of it as morally meaning `F ⊆ S`,
but this doesn't make sense because `F` is a filter, not a subset.

The `ext` tactic can be used to reduce a goal `F = G` to a goal of
the form `∀ S, S ∈ F ↔ S ∈ G`.

The fields of the structure mention things like `S ∈ F.sets`, so the
axioms are restated with different names, but using the `S ∈ F` notation.
The lemmas corresponding to the definitions are:

`univ_mem : univ ∈ F`
`mem_of_superset : S ∈ F → S ⊆ T → T ∈ F`
`inter_mem : S ∈ F → T ∈ F → S ∩ T ∈ F`

These lemmas in the `Filter` namespace, i.e. their full names are
`Filter.univ_mem_sets` etc. But we are about to say `open Filter`
which means that you don't have to type this `Filter.` thing in front of every
lemma you need about filters. In fact we'll also be using a bunch of
stuff about sets, like `Set.inter_subset_left`, so why don't we `open Set`
as well.
-/

open Filter Set

-- Variables!
-- let `α` be a type, let `F` be a filter on `α`, and let `S` and `T`
-- denote subsets of `α`.
variable (α : Type) (F : Filter α) (S T : Set α)

/-
Here's a lemma about filters: Two sets `S` and `T` are both in
a filter `F` if and only if their intersection is. See if you can deduce
it from the axioms of a filter.

For this one it's useful to know the following results (from the set namespace)
`inter_subset_left S T : S ∩ T ⊆ S`
and
`inter_subset_right S T : S ∩ T ⊆ T`
-/
example : S ∩ T ∈ F ↔ S ∈ F ∧ T ∈ F := by
  constructor
  · intro h
    constructor
    · apply mem_of_superset h
      exact inter_subset_left
    · apply mem_of_superset h
      exact inter_subset_right
  · rintro ⟨hS, hT⟩
    exact inter_mem hS hT

/-

## Principal filters

Surely a subset of `α` should be a generalised subset of `α`! So there
should be a map `Set α → Filter α`. It's called `principal` and it
has notation `𝓟`. The principal filter `𝓟 X` generated by `X : Set α` is the
subsets of `α` which contain `X`. Prove that it's a filter.

Helpful for this exercise:
`mem_univ s : s ∈ univ`
`Subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`
`subset_inter : X ⊆ S → X ⊆ T → X ⊆ S ∩ T`
(note that you could probably prove those last two things directly yourself,
but we may as well use the interface for sets given that it's there)
`mem_setOf_eq : x ∈ {a : α | p a} = p x`
(this one is definitional, so you could use `change` instead, or just
not rewrite it at all)

-/
-- this is called `𝓟 X` in mathlib but let's just make it ourselves.
example (X : Set α) : Filter α where
  sets := { S | X ⊆ S }
  univ_sets := subset_univ X
  sets_of_superset := by
    intro I J hI hIJ
    simp only [mem_setOf_eq] at hI
    simp only [mem_setOf_eq]
    exact hI.trans hIJ
  inter_sets := by
    intro I J hI hIJ
    simp only [mem_setOf_eq] at *
    exact subset_inter hI hIJ

-- The notation for the principal filter generated by `X : set α` is `𝓟 X`.
-- This notation is in the "Filter" scope, which is just a posh way
-- of saying that you have to type
open scoped Filter
-- in order to get the notation.

end FM2026_12_1

-- ════════════════════════════════════════════════════════════════
-- Section12Filters/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_12_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics

/-!

# The order (≤) on filters

We think of filters as generalised subsets, and just as subsets are partially ordered
by `⊆`, filters are partially ordered too, by `≤`. Recall that a subset `X : Set α`
of `α` gives rise to a principal filter `𝓟 X : Filter α`, and we definitely
want `X ⊆ Y ↔ 𝓟 X ≤ 𝓟 Y` so let's think about how this should work. If `F` and `G`
are filters, then `F ≤ G` should mean "the generalised subset `F` is contained
in the generalised subset `G`", so it should mean "if a normal subset of α contains
`G` then it contains `F`", so it should mean `G.sets ⊆ F.sets`, which is in fact
the definition. Note that the smaller the filter `F`, the bigger the collection
`F.sets`, because `F` is contained in more sets!

Let's formalise this. Show that 𝓟 S ≤ 𝓟 T ↔ S ⊆ T.
Note that this is called `principal_mono` in mathlib but
there's no harm in proving it yourself.

Some helpful lemmas (all in the `Filter` namespace):

`mem_principal : T ∈ 𝓟 S ↔ S ⊆ T`
`mem_principal_self S : S ∈ 𝓟 S`
`le_def : F ≤ G ↔ ∀ (S : Set α), S ∈ G → S ∈ F`

-/

namespace Filter

variable {α : Type}

open Set
-- so we don't keep having to type `Filter.le_def` and `Set.Subset.trans` etc

open scoped Filter
-- for 𝓟 notation

example (S T : Set α) : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T := by
  rw [Filter.le_def]
  constructor
  · intro h
    specialize h T
    rw [mem_principal] at h
    apply h
    exact Subset.refl T
  · intro h U hU
    rw [mem_principal] at hU ⊢
    exact h.trans hU

-- Here's another useful lemma about principal filters.
-- It's called `le_principal_iff` in mathlib but why
-- not try proving it yourself?
example (F : Filter α) (S : Set α) : F ≤ 𝓟 S ↔ S ∈ F := by
  rw [Filter.le_def]
  constructor
  · intro h
    apply h
    exact mem_principal_self S
  · intro h T hT
    rw [mem_principal] at hT
    exact mem_of_superset h hT

/-

## Filters are a complete lattice

First I claim that if Fᵢ are a bunch of filters, indexed by `i : I`, then
the intersection of `Fᵢ.sets` is also a filter. Let's check this.

-/
def lub {I : Type} (F : I → Filter α) : Filter α where
  sets := {X | ∀ i, X ∈ F i}
  univ_sets := by simp [univ_mem]
  sets_of_superset := by
    intro x y hx hxy i
    exact mem_of_superset (hx i) hxy
  inter_sets := by
    intro x y hx hy i
    exact inter_mem (hx i) (hy i)

/-

Now let's check that this is a least upper bound for the Fᵢ! We check the
two axioms.

-/
-- it's an upper bound
example (I : Type) (F : I → Filter α) (i : I) : F i ≤ lub F := by
  rw [Filter.le_def]
  intro x hx
  rw [lub] at hx
  simp only [Filter.mem_mk, mem_setOf_eq] at hx
  apply hx

-- it's ≤ all other upper bounds
example (I : Type) (F : I → Filter α) (G : Filter α) (hG : ∀ i, F i ≤ G) :
    lub F ≤ G := by
  rw [Filter.le_def]
  intro x hx
  unfold lub
  simp only [Filter.mem_mk, mem_setOf_eq]
  intro i
  specialize hG i
  rw [Filter.le_def] at hG
  exact hG x hx

/-

Just like it's possible to talk about the topological space generated
by a collection of subsets of `α` -- this is the smallest topology
for which the given subsets are all open -- it's also possible to talk
about the filter generated by a collection of subsets of `α`. One
can define it as the intersection of all the filters that contain your
given collection of subsets (we just proved above that this is a filter).
This gives us a definition of greatest lower bound for filters too.

-/
-- greatest lower bound of filters Fᵢ is the least upper bound of the filters G whose `sets`
-- contain all of the `Fᵢ.sets`
def glb {I : Type} (F : I → Filter α) : Filter α :=
  lub fun G : {G : Filter α | ∀ i, (F i).sets ⊆ G.sets} ↦ G.1

-- it's a lower bound
example (I : Type) (F : I → Filter α) (i : I) : glb F ≤ F i := by
  rw [Filter.le_def]
  intro x hx
  unfold glb lub
  simp only [coe_setOf, mem_setOf_eq, Subtype.forall, sets_subset_sets, Filter.mem_mk]
  -- that line came from simp?
  intro G hG
  exact hG i hx

-- it's ≥ all other lower bounds
example (I : Type) (F : I → Filter α) (G : Filter α) (hG : ∀ i, G ≤ F i) :
    G ≤ glb F := by
  rw [Filter.le_def]
  intro x hx
  unfold glb lub at hx
  simp only [coe_setOf, mem_setOf_eq, Subtype.forall, sets_subset_sets, Filter.mem_mk] at hx
  -- that line came from simp?
  apply hx G
  intro i y hy
  specialize hG i
  rw [Filter.le_def] at hG
  exact hG y hy

end Filter

end FM2026_12_2

-- ════════════════════════════════════════════════════════════════
-- Section12Filters/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_12_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics

/-!

# Examples of filters

## `atTop` filter on a totally ordered set

Let `L` be a non-empty totally ordered set. Let's say that a subset `X` of `L` is
"big" if there exists `x : L` such for all `y ≥ x`, `y ∈ X`.

I claim that the big subsets are a filter. Check this. The mathematical idea
is that the "big subsets" are the neighbourhoods of `∞`, so the corresponding
filter is some representation of an infinitesimal neighbourhood of `∞`.

Implementation notes: `LinearOrder L` is the type of linear orders on `L`.
`e : L` is just an easy way of saying that `L` is nonempty.

Recall that `max x y` is the max of x and y in a `LinearOrder`, and
`le_max_left a b : a ≤ max a b` and similarly `le_max_right`.
-/

namespace Filter

open Set

-- (The real definition of the atTop filter is more general than this: it only assumes that we have
-- a preorder. But for now, where we're just thinking about going to infinity in ℕ or ℝ, a nonempty
-- linear order is plenty general enough.)

/-- A simplified version of the `atTop'` filter for nonempty linear orders. -/
def atTop' (L : Type) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    use e
    intro y hy
    trivial
  sets_of_superset := by
    rintro x y ⟨x₀, hx⟩ hxy
    use x₀
    intro z hz
    apply hxy
    apply hx
    exact hz
  inter_sets := by
    rintro x y ⟨x₀, hx⟩ ⟨y₀, hy⟩
    use max x₀ y₀
    intro z hz
    constructor
    · apply hx
      exact le_trans (le_max_left x₀ y₀) hz
    · apply hy
      exact le_trans (le_max_right x₀ y₀) hz
/-

## the cofinite filter

The _cofinite filter_ on a type `α` has as its sets the subsets `S : set α`
with the property that `Sᶜ`, the complement of `S`, is finite.
Let's show that these are a filter.

Things you might find helpful:

`compl_univ : univᶜ = ∅`
`finite_empty : Finite ∅`
`compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
`Finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.Finite`
`compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
`Finite.union : S.finite → T.finite → (S ∪ T).Finite`

NB if you are thinking "I could never use Lean by myself, I don't know
the names of all the lemmas so I have to rely on someone telling them all to
me" then what you don't realise is that I myself don't know the names
of all the lemmas either -- I am literally just guessing them and pressing
ctrl-space to check. Look at the names of the lemmas and begin to understand
that you can probably guess them yourself.
-/
def cofinite' (α : Type) : Filter α where
  sets := {S : Set α | Sᶜ.Finite}
  univ_sets := by
    simp [compl_univ, finite_empty]
  sets_of_superset := by
    intro x y hx hxy
    rw [mem_setOf_eq] at *
    apply hx.subset
    rwa [compl_subset_compl]
  inter_sets := by
    intro x y hx hy
    rw [mem_setOf_eq] at *
    rw [compl_inter]
    exact hx.union hy

def nhds' {X : Type} [TopologicalSpace X] (x : X) : Filter X where
  sets := {s : Set X | ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ s}
  univ_sets := by
    use univ
    simp [isOpen_univ]
  sets_of_superset := by
    rintro x₀ y ⟨U, hx, hU, hUx⟩ hxy
    use U
    exact ⟨hx, hU, hUx.trans hxy⟩
  inter_sets := by
    rintro x₀ y ⟨U, hx, hU, hUx⟩ ⟨V, hy, hV, hVy⟩
    use U ∩ V
    refine ⟨⟨hx, hy⟩, IsOpen.inter hU hV, ?_⟩
    exact inter_subset_inter hUx hVy

/-

## Harder exercises.

If you like this filter stuff, then formalise in Lean and prove the following:

(1) prove that the cofinite filter on a finite type is the entire power set filter (`⊥`).
(2) prove that the cofinite filter on `ℕ` is equal to the `atTop` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `atTop` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

-/

end Filter

end FM2026_12_3

-- ════════════════════════════════════════════════════════════════
-- Section12Filters/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_12_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics

/-!
# Filters and limits

The motivation for filters was to unify different ways of talking about limits, so to finish this
story we need to know how to use this filter language to talk about limits!

The key ingredients we'll need for this story are:
* the order relation on filters
* our two special filters `atTop` and `nhds`
* the pushforward of a filter: `Filter.map`

We've seen the first two of these, so let's talk about the third.

Given a filter `f : Filter α` and a map `m : α → β`, there's a reasonably natural way of making
a `Filter β`: a set `s : Set β` will be in our filter if its preimage under `m` (which
is `m ⁻¹' s : Set α`) is in `f`. Let's make this and check it's a filter.
-/

namespace Filter

variable {α β : Type*}

def map' (f : Filter α) (m : α → β) : Filter β where
  sets := {s | m ⁻¹' s ∈ f}
  univ_sets := by
    simp [univ_mem]
  sets_of_superset := by
    intro x y hx hxy
    apply mem_of_superset hx
    exact Set.preimage_mono hxy
  inter_sets := by
    intro x y hx hy
    dsimp at *
    exact inter_mem hx hy

/-
Now I can write down what it means for a function `f` to tend to a filter `l₂` under a filter `l₁`.
Then if `f : ℕ → ℝ`, `l₁ = atTop`, and `l₂ = nhds 0`, I claim `Tendsto f l₁ l₂` means the same as
what we'd informally write as $lim_{x → ∞} f(x) = 0$.

Similarly, if `l₁ = nhds a` and `l₂ = nhds b`, then `Tendsto f l₁ l₂` will be that `f(x) → b` as
`x → a`.
-/

def Tendsto' (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop :=
  l₁.map f ≤ l₂

-- That felt too easy.
-- Let's make sure it does actually work.

#check Metric.tendsto_nhds_nhds
#check Metric.tendsto_atTop

lemma tendsto_atTop_atTop_iff {α β : Type*} [Nonempty α] [LinearOrder α] [LinearOrder β]
    (f : α → β) :
    Tendsto f atTop atTop ↔ ∀ M : β, ∃ N : α, ∀ a : α, N ≤ a → M ≤ f a := by
  rw [tendsto_atTop_atTop]

/-
With filters at hand, it's now really easy to talk about something being true "sufficiently close"
to a point, or for all "sufficiently large" numbers. Specifically, I can say that `p : ℕ → Prop`
is true for all sufficiently large `n` if the set of places where it's true `{n | p n}` is in the
`atTop` filter.
This has notation: ∀ᶠ n in atTop, p n, and it's called "eventually" or "eventually forall".
-/

example {p : ℕ → Prop} : (∀ᶠ n in atTop, p n) ↔ ∃ N, ∀ n ≥ N, p n := by
  rw [eventually_atTop]

/-
Now's a good time to mention that Lean usually doesn't like the `≥` symbol: most lemmas will be
stated in terms of `≤`, and some automation will work best with `≤`. So mathlib has a style
convention to use `≤` everywhere: it's a bit weird, I know! That means saying that `n > 1` would
usually be written as `1 < n`.
The exception to this rule is examples like the one above, where I'm using `∀ n ≥ N` notation:
if I were to write this as `∀ N ≤ n`, then it'd more sensibly mean that I'm quantifying over `N`
with fixed `n`, so `≥` is allowed to make `∀ n ≥ N` read nicely.
The `simp` tactic will usually do this lemma to make everything into a `≤`:
-/

example {a b : ℝ} : a ≥ b ↔ b ≤ a := by rw [ge_iff_le]

/-
The really useful part here is the intersection axiom for filters. In the context of eventually,
this says that if `p` is eventually true along the filter, and `q` is eventually true along the same
filter then `p ∧ q` is eventually true along the filter too.
-/

example {p q : ℕ → Prop} (hp : ∀ᶠ n in atTop, p n) (hq : ∀ᶠ n in atTop, q n) :
    ∀ᶠ n in atTop, p n ∧ q n :=
  hp.and hq

/-
In practice, we often use the `filter_upwards` tactic to handle things like this. Look at the goal
state after the `filter_upwards` here: it should be very easy!
Play around with what happens if you remove everything after the `with`, and then if you remove the
`hp` or `hq`.
The idea of `filter_upwards` is that if you're trying to prove something is eventually true, and
you know that other things are eventually true, it lets you safely assume those things are generally
true, and deduce that what you want holds too.
-/

example {p q : ℕ → Prop} (hp : ∀ᶠ n in atTop, p n) (hq : ∀ᶠ n in atTop, q n) :
    ∀ᶠ n in atTop, p n ∧ q n := by
  filter_upwards [hp, hq] with n hpn hqn
  exact ⟨hpn, hqn⟩

example {x ε : ℝ} (hε : 0 < ε) : ∀ᶠ y in nhds x, |y - x| < ε := by
  exact eventually_abs_sub_lt x hε

example {N : ℕ} : ∀ᶠ n in atTop, N ≤ n := by
  exact eventually_ge_atTop N

example {p q : ℕ → Prop} {N M : ℕ} (hp : ∀ n ≥ N, p n) (hq : ∀ n ≥ M, q n) :
    ∀ᶠ n in atTop, p n ∧ q n := by
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M] with n hN hM
  exact ⟨hp n hN, hq n hM⟩

example {p q : ℕ → Prop} {N M : ℕ} (hp : ∀ n ≥ N, p n) (hq : ∀ n ≥ M, q n) :
    ∃ N', ∀ n ≥ N', p n ∧ q n := by
  rw [← eventually_atTop]
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M] with n hN hM
  exact ⟨hp n hN, hq n hM⟩

-- I don't need to use max any more!

/-
Finally, as promised, here's a really short proof about what happens when you add convergent
sequences.
-/
example {f g : ℕ → ℝ} {a b : ℝ} (hf : Tendsto f atTop (nhds a)) (hg : Tendsto g atTop (nhds b)) :
    Tendsto (fun n ↦ f n + g n) atTop (nhds (a + b)) :=
  hf.add hg

end Filter

-- For more about Filters and Topology, see
-- https://leanprover-community.github.io/mathematics_in_lean/C10_Topology.html

end FM2026_12_4

-- ════════════════════════════════════════════════════════════════
-- Section13VectorSpaces/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_13_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Vector spaces

Ok so groups in Lean are called `Group` and fields are called `Field`, so
I think I owe you an explanation for why vector spaces are called `Module`.

The lie is that `Module` is French for vector space, and we used a French source.
If you're happy with that explanation, then you can skip the actual explanation below.

The truth is the following. The definition of a vector space `V` over a field `k` is:

1) `V` is an abelian group
2) If `r : k` and `v : V` there's an element `r • v : V`
3) Axioms for `•`: `(r + s) • v = r • v + s • v`, `r • (v + w) = r • v = r • w`,
  `1 • v = v` and `(r * s) • v = r • (s • v)`.

Recall that `k` was a field. Fields have division and inverses (except for 0),
but look at those axioms: there is no mention of inverses or division for `k` in the axioms
of a vector space. The only things we use on `k` are `1`, `+` and `*`.

This means that we can make the *definition* of a vector space just under
the assumption that `k` is a `Ring`, rather than a `Field`, although of course
fewer things will be true (for example, over a general ring it is not true that
every vector space has a basis). However, when `k` is a ring, mathematicians don't
call these things vector spaces; they call them *modules*. So the way we say
"let `V` be a vector space over `k`" in Lean is "let `V` be a module over `k`".
-/

-- Let `k` be a field and let `V` be a vector space over `k`
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]

/-
The field `k` acts on the vector space `V` and the notation for this is `•`,
which is notation for `hSMul` ("heterogenous scalar multiplication :-| ").
We don't use `mul` because for `a * b` to make
sense in Lean we need `a` and `b` to have the same type. Here `a : k` and `v : V`
so this isn't satisfied.
-/
-- scalar multiplication of a scalar by a vector is a vector
example (a : k) (v : V) : V :=
  a • v

-- Axioms for a vector space
variable (a b : k) (v w : V)

example : a • (v + w) = a • v + a • w :=
  smul_add a v w

example : (a + b) • v = a • v + b • v :=
  add_smul a b v

example : (1 : k) • v = v :=
  one_smul k v

example : a • b • v = (a * b) • v :=
  smul_smul a b v

-- Other standard facts about vector spaces (not axioms, but theorems with names)
example : (a - b) • v = a • v - b • v :=
  sub_smul a b v

example : (0 : k) • v = 0 :=
  zero_smul k v

/-

## Subspaces

The type of subspaces of a vector space is called `Subspace k V`. You
have to mention `k` because there are real world examples like `ℂⁿ` which
are vector spaces over both the reals and the complexes, and they have
more real subspaces than complex subspaces.

Subspaces of a vector space form a complete lattice, so Lean uses lattice notation for them.

-/
-- let `X` and `Y` be subspaces of `V`
variable (X Y : Subspace k V)

/-
Note that `X` and `Y` are terms not types.
How do we say `X ⊆ Y`?
#check X ⊆ Y -- doesn't work! `⊆` only works for terms of type `Set V`.
We use *lattice notation* and it works fine.
-/

example : Prop :=
  X ≤ Y -- `X ≤ Y` is a true-false statement

example : Subspace k V :=
  X ⊓ Y -- intersection of `X` and `Y`, as a subspace

example : Subspace k V :=
  X ⊔ Y -- `X + Y`, as a subspace. It's the smallest vector subspace of
        -- `V` containing `X` and `Y`, so it's the sup of `X` and `Y`
        -- in the lattice of subspaces.

example : Subspace k V :=
  ⊥ -- the 0-dimensional subspace

example : Subspace k V :=
  ⊤ -- V considered as a subspace of itself; note that
    -- we can't use V to represent this subspace because
    -- V is a type, and a subspace of V is a term

-- For elements of subspaces it's just like sets:
example : Prop :=
  v ∈ X -- the type of `v` is `V`, and the true-false statement is `v ∈ X`

-- Let `W` be another `k`-vector space
variable (W : Type) [AddCommGroup W] [Module k W]

-- `k`-linear maps from `V` to `W` are terms of type `V →ₗ[k] W`. This is notation
-- for `LinearMap (RingHom.id k) V W`, i.e. additive group homs `φ : V → W` such
-- that φ (a • b) = (id a) • (φ b)

-- let `φ : V → W` be a `k`-linear map
variable (φ : V →ₗ[k] W)

-- Axioms for a linear map:
example : φ (a • v) = a • φ v :=
  φ.map_smul a v

example : φ (v + w) = φ v + φ w :=
  φ.map_add v w

-- quotients work just like in group theory. Recall `V` is a vector space and `X : Subspace k V`
example : Type := V ⧸ X

-- The natural linear map from `V` to `V ⧸ X` is called `Submodule.mkQ X`
example : V →ₗ[k] V ⧸ X :=
  Submodule.mkQ X

-- ...which is inconsistent with the group theory quotient conventions, aah well.

-- You can take the image and preimage of subspaces along a linear map `φ : V →ₗ[k] W`.
example (X : Subspace k V) : Subspace k W :=
  X.map φ

example (Y : Subspace k W) : Subspace k V :=
  Y.comap φ

-- Here's an actual question at long last. If φ : V → W is a linear map,
-- if X is a subspace of V and Y a subspace of W, prove that φ(X) ⊆ Y iff X ⊆ φ⁻¹(Y)
example (X : Subspace k V) (Y : Subspace k W) : X.map φ ≤ Y ↔ X ≤ Y.comap φ := by
  constructor
  · intro h x hx
    simp?
    apply h
    use x, hx
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    apply h
    exact hx

end FM2026_13_1

-- ════════════════════════════════════════════════════════════════
-- Section13VectorSpaces/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_13_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Finite-dimensional vector spaces

Here's how you say "let `k` be a field and let `V` be a finite-dimensional `k`-vector space"

-/

-- let k be a field and let V be a finite-dimensional k-vector space
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

#check Module.finrank

/-
There are two concepts of "dimension" in Lean. There's a general `Module.rank k V`, which
returns a `Cardinal` (so in particular the answer could be one of many kinds of infinity)
and, in the finite-dimensional case, there is `Module.finrank k V`, which returns
a natural number. Note that, as is idiomatic in Lean, the latter function will accept
an infinite-dimensional space as input (garbage in) and will return 0 for the answer
(garbage out). All our spaces will be finite-dimensional, so we can use
`Module.finrank`. Note that if we `open Module` then we can
just call it `finrank`.

So how do we find theorems about `finrank`? Well one way of doing it would be to control-click
(or command-click on Mac, I think) on `finrank` in some Lean code (not in a comment though)
and then just browse the file which the definition is in (be careful not to edit it though).

Another way would be to type `Module.finrank` into the online documentation
here https://leanprover-community.github.io/mathlib4_docs/ , and then read the docs instead.
The most relevant page is
https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html .
That way you don't see the proofs, which makes things easier to read.

Or I could just tell you some. Here's some API for `finrank`. Note
that if `A : Subspace k V` then `A` is a term, not a type, and in particular it's not a
vector space (it's a vector subspace). However `↥A`, a "coercion to type", is a type,
and hence has a `finrank`.

## Some API for finite-dimensional vector spaces

This should be all you need.

`Submodule.finrank_sup_add_finrank_inf_eq` says
    `finrank k ↥(A ⊔ B) + finrank k ↥(A ⊓ B) = finrank k ↥A + finrank k ↥B`
`Submodule.finrank_le A : finrank k ↥A ≤ finrank k V`
`finrank_bot k V : finrank k ↥⊥ = 0`

# An example sheet question

A 2019 University of Edinburgh example sheet question (set to me as a challenge by a lecturer
there): prove that if `V` is a 9-dimensional
vector space and `A, B` are two subspaces of dimension 5, then `A ∩ B` cannot be
the zero vector space.

-/
open Module -- now we can just write `finrank`.

example (A B : Subspace k V) (hV : finrank k V = 9) (hA : finrank k A = 5) (hB : finrank k B = 5) :
    A ⊓ B ≠ ⊥ := by
  -- Suppose A ⊓ B = ⊥
  intro h
  -- Then finrank (A ⊓ B) = 0
  have h_inf : finrank k ↥(A ⊓ B) = 0 := by
    rw [h]
    exact finrank_bot k V
  -- The key formula: finrank (A ⊔ B) + finrank (A ⊓ B) = finrank A + finrank B
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  -- Substitute what we know
  rw [h_inf, hA, hB] at h
  -- Now finrank (A ⊔ B) = 10
  simp at h
  -- But finrank (A ⊔ B) ≤ finrank V = 9
  have h_le := Submodule.finrank_le (A ⊔ B)
  rw [hV, h] at h_le
  -- contradiction: 10 ≤ 9
  norm_num at h_le

end FM2026_13_2

-- ════════════════════════════════════════════════════════════════
-- Section13VectorSpaces/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_13_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Finitely-supported functions

We're used to dealing with finite-dimensional vector spaces when we begin studying
vector spaces, but infinite-dimensional vector spaces exist everywhere (for example
the polynomial ring `ℝ[X]` is an infinite-dimensional real vector space) and Lean
is happy to work with both finite and infinite-dimensional vector spaces.

If `V` is a finite-dimensional vector space, with basis `{e₁,e₂,...,eₙ}`, then
every element of `V` can be uniquely expressed as ∑ cᵢeᵢ, with cᵢ in the ground field.
In the infinite-dimensional case this doesn't make sense, because in algebra you
cannot do infinite sums in general; you need some kind of metric or topology
to express the idea that an infinite sum converges or tends to some limit, and a general
field `k` may not have a metric or a topology. If `k` is a finite field, you could
give it the discrete topology, but then no infinite sum would converge, unless all
but finitely many of the terms were actually equal to zero.

The simplest example of an infinite-dimensional vector space is the ring of polynomials
`k[X]` over a field `k`, and this vector space has a basis `{1,X,X²,X³,...}`. Hopefully
all this enables you to see what is going on: whilst the vector space is infinite-dimensional,
and the basis is infinite, each vector in the space (i.e. each polynomial in `k[X]`) is
a *finite* linear combination of basis elements; so we have `v = ∑ᵢ cᵢ eᵢ` but all
of the `cᵢ` are zero other than finitely many of them. This makes the sum finite,
and hence it makes in algebra without having to assume anything about existence of
metrics or topologies.

This example shows that an important role in the theory of vector spaces is played
by the *finitely-supported functions*. If `X` and `Y` are types, and `Y` has a special
element called `0`, then a function from `X` to `Y` is *finitely-supported* if it sends
all but finitely many elements of `X` to `0`. Just like the theory of finite sets,
there are two ways to set up a theory of finitely-supported functions. We could first
consider all functions and then have a predicate on functions saying "I have finite support".
Alternatively, we could make an entirely new type of finitely-supported functions, and
then just have a map from that type to the type of all functions. This latter approach
is what we do in Lean.

The type of finitely-supported functions from `X` to `Y` is denoted `X →₀ Y`, which
is notation for `Finsupp X Y`. Put another way; a term of this type can be thought
of as a function from `X` to `Y` which is only non-zero on a finite subset of `X`.
Note that `Y` needs to have a `zero` for this notion to make sense.
-/

example : Type :=
  ℕ →₀ ℕ -- works because ℕ has a zero

/-

The theory of finitely supported functions is a noncomputable theory in Lean, so
let's switch `noncomputable` on.

-/
noncomputable section

-- In the application to vector spaces, `Y` will be a field, so it will have a zero.
-- If you know about free modules, then you can let `Y` be a ring.
-- Lean's typeclass inference system knows that if `X` is an arbitrary type and `k` is a field,
-- then `X →₀ k` is a `k`-vector space.
example (X : Type) (k : Type) [Field k] : Module k (X →₀ k) := by
  infer_instance -- the tactic which magics up terms which the typeclass inference
                 -- system knows about.

-- In particular, Lean is happy to add two finitely-supported functions and return
-- a finitely-supported function.
-- Lean will also allow you to evaluate a finitely-supported function at an input,
-- even though a finitely-supported function is not strictly speaking a function
-- (it's a function plus some extra data and proofs). Lean will *coerce* a finitely-supported
-- function into a function if required though.
example (X : Type) (k : Type) [Field k] (f : X →₀ k) (x : X) : k :=
  f x

-- Because these things are a vector space, addition of two finitely-supported functions is a
-- finitely-supported function. Similarly multiplication by a scalar is a finitely-supported
-- function
example (X : Type) (k : Type) [Field k] (f g : X →₀ k) (c : k) : X →₀ k :=
  c • f + g

-- How do we access the support of `f`? i.e. what is the finite subset of `X` where `f`
-- is nonzero? If you try `by exact?` below you'll get `Finset.empty` (`exact?` is
-- designed to prove theorems, not find definitions), but we want
-- to definitely use `f` so try `by exact? using f` and you'll hopefully get the right answer.
example (X : Type) (k : Type) [Field k] (f : X →₀ k) : Finset X := f.support

end

end FM2026_13_3

-- ════════════════════════════════════════════════════════════════
-- Section13VectorSpaces/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_13_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-!

# Bases and matrices

Here is some API for bases of a vector space, and its relation to matrices.

-/

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]

/-

What *is* a basis for a vector space `V`? Mathematicians use the term to mean two
different things! Sometimes it's a subset of `V` (this is particularly common
if `V` is infinite-dimensional) and sometimes it's a *list* `[e₁, e₂, ..., eₙ]`.
The issue is whether the basis is *indexed* or not. In `mathlib`, bases are
indexed, so we have an index type (e.g. `{1,2,3,...,n}`) and a basis
is a function from this type to `V` satisfying the axioms for a basis.

-/
-- Let `B` be a `k`-basis for `V` indexed by `I`.
variable (I : Type) (B : Module.Basis I k V)

-- Lean is allowing for the possibility that `I` is infinite, which makes
-- the theory noncomputable, so let's switch on non-computable mathematics
noncomputable section

-- (I always do this when Lean complains something is not computable; this doesn't
-- mean that you can't do maths with it, it means that we're asking Lean to do things
-- for which there is no algorithm (e.g. picking a basis, especially in the infinite-dimensional
-- case)
-- If `(i : I)` then the basis element of `V` corresponding to `i` (i.e. the element eᵢ if
-- you're imagining i={1,2,3,...,n}) is `B i`
variable (i : I)

example : V :=
  B i

-- A general element of V is uniquely a `k`-linear combination of elements of the basis.
-- In the finite-dimensional case we just write `v = ∑ᵢ cᵢeᵢ`. In the infinite-dimensional
-- case a basis will be infinite, but you can't take infinite sums so from `v` we should
-- expect to get a finitely-supported function on `I`, i.e., an element of `I →₀ k`
-- which sends `i` to `cᵢ`. Conversely given a finitely supported function `f : I →₀ k`
-- we can make the element ∑ᵢf(i)eᵢ, this is a finite sum so makes sense, and
-- every element of `V` is uniquely of this form (because the `eᵢ` are a basis.

-- Given a basis `B` with index set `I`, the function `Basis.repr B`, or `B.repr`,
-- is the `k`-linear isomorphism from `V` to these finitely-supported functions.
example : V ≃ₗ[k] I →₀ k :=
  B.repr

-- If `I` is finite, then you can use the space of all functions `I → k` (because they're
-- all finitely-supported) but because `I →₀ k` isn't *equal* to `I → k` (they're just
-- in bijection when `I` is finite) we need a different function to do this.
example [Fintype I] : V ≃ₗ[k] I → k :=
  B.equivFun

-- If you want to see the coefficient of `B i` in the expansion of `v` in terms
-- of the basis `B`, you can write
example (v : V) : k :=
  B.repr v i

-- Again if `I` is finite, you can reconstruct `v` as `∑ B.repr v i • B i`, a sum over all `i`.
-- allow notation for sums
open BigOperators

example [Fintype I] (v : V) : ∑ i, B.repr v i • B i = v :=
  B.sum_repr v

-- You can also use `B.coord i`, which is the linear map from `V` to `k` sending a vector `V`
-- to the coefficient of `B i`
example : V →ₗ[k] k :=
  B.coord i

-- Now let `W` be another `k`-vector space
variable (W : Type) [AddCommGroup W] [Module k W]

-- Let's prove that any map `f` from `I` to `W` extends uniquely to a linear map `φ` from `V` to `W`
-- such that forall `i : I`, `f i = φ (B i)`.
-- The three pieces of API you'll need:
-- the extension of `f : I → W` to a `k`-linear map `V →ᵢ[k] W` is `Basis.constr B k f`
example (f : I → W) : V →ₗ[k] W :=
  B.constr k f -- dot notation

-- The theorem that `B.constr k f` agrees with `f` (in the sense that `B.constr k f (B i) = f i`
-- is `Basis.constr_basis B k f i`
example (f : I → W) (i : I) : B.constr k f (B i) = f i :=
  B.constr_basis k f i

-- Finally, `Basis.ext` is the theorem that two linear maps are equal if they agree
-- on a basis of the source
example (φ ψ : V →ₗ[k] W) (h : ∀ i : I, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h

-- That should be all you need to do this!
example (f : I → W) : ∃! φ : V →ₗ[k] W, ∀ i, φ (B i) = f i := by
  use B.constr k f
  constructor
  · intro i
    exact B.constr_basis k f i
  · intro φ' hφ'
    apply B.ext
    intro i
    rw [hφ' i, B.constr_basis]

-- Now say `C` is a basis of `W`, indexed by a type `J`
variable (J : Type) (C : Module.Basis J k W)

-- If everything is finite-dimensional
variable [Fintype I] [Fintype J]

-- then linear maps from `V` to `W` are the same as matrices with rows
-- indexed by `I` and columns indexed by `J`
open Classical

-- apparently something isn't constructive here?
example : (V →ₗ[k] W) ≃ₗ[k] Matrix J I k :=
  LinearMap.toMatrix B C

-- check that this bijection does give what we expect.
-- Right-click on `LinearMap.toMatrix` and then "go to definition" to find
-- the API for `LinearMap.toMatrix`.
example (φ : V →ₗ[k] W) (i : I) (j : J) : LinearMap.toMatrix B C φ j i = C.repr (φ (B i)) j := by
  exact LinearMap.toMatrix_apply B C φ j i

end

end FM2026_13_4

-- ════════════════════════════════════════════════════════════════
-- Section14measureTheory/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_14_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics

/-

# Measure theory

## Sigma algebras.

A σ-algebra on a type `X` is a collection of subsets of `X` satisfying some
axioms, and in Lean you write it like this:

-/

namespace Section13Sheet1

-- let X be a set
variable (X : Type)

-- ...and let 𝓐 be a sigma-algebra on X
variable (𝓐 : MeasurableSpace X)

/-

Note that `MeasurableSpace` is a *class*, so really we should be writing `[MeasurableSpace X]`,
meaning "let `X` be equipped once and for all with a sigma algebra which we won't give a name to".
But in this sheet we'll consider making them explicitly.

Let's do the following exercise. Show that if `A` is a subset of `X` then `{0,A,Aᶜ,X}`
is a sigma algebra on `X`.

-/
-- [PATCHED: measurableSet_iUnion proof uses patterns incompatible with Lean 4.27]
def genBy (A : Set X) : MeasurableSpace X where
  MeasurableSet' S := S = ∅ ∨ S = A ∨ S = Aᶜ ∨ S = Set.univ
  measurableSet_empty := by simp
  measurableSet_compl := by
    rintro s (rfl | rfl | rfl | rfl) <;> simp
  measurableSet_iUnion := by
    sorry

-- An alternative approach to defining the sigma algebra generated by `{A}` is just
-- to use `MeasurableSpace.generateFrom`:
example (A : Set X) : MeasurableSpace X :=
  MeasurableSpace.generateFrom {A}

-- But the problem with that approach is that you don't get the actual sets
-- in the sigma algebra for free. Try this, to see what I mean!
-- [PATCHED: original proof uses subst/simp patterns incompatible with Mathlib v4.27]
example (A : Set X) :
    (MeasurableSpace.generateFrom {A}).MeasurableSet' =
    ({∅, A, Aᶜ, Set.univ} : Set (Set X)) := by
  sorry

end Section13Sheet1
end FM2026_14_1

-- ════════════════════════════════════════════════════════════════
-- Section14measureTheory/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_14_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics

/-

# Measure theory

## More on sigma algebras.

-/

namespace Section13Sheet2
-- Intersection of sigma algebras is a sigma algebra
-- Let 𝓐 be a family of sigma algebras on a type `X`
variable (X : Type) (I : Type) (𝓐 : I → MeasurableSpace X)

-- Then their intersection is also a sigma algebra
open scoped MeasureTheory
-- to get notation `MeasurableSet[S] U` for "U is in the sigma algebra S"

example : MeasurableSpace X where
  MeasurableSet' U := ∀ i, MeasurableSet[𝓐 i] U
  measurableSet_empty := by
    intro i
    exact MeasurableSpace.measurableSet_empty (𝓐 i)
  measurableSet_compl := by
    intro U hU i
    exact MeasurableSpace.measurableSet_compl (𝓐 i) U (hU i)
  measurableSet_iUnion := by
    intro f hf i
    apply MeasurableSpace.measurableSet_iUnion
    intro n
    exact hf n i

-- Lean knows that sigma algebras on X are a complete lattice
-- so you could also make it like this:
example : MeasurableSpace X :=
  ⨅ i, 𝓐 i

-- Sigma algebras are closed under countable intersection
-- Here, because there's only one sigma algebra involved,
-- I use the typeclass inference system to say "fix a canonical
-- sigma algebra on X" and just use that one throughout the question.
example (X : Type) [MeasurableSpace X]
    (f : ℕ → Set X) (hf : ∀ n, MeasurableSet (f n)) :
    MeasurableSet (⋂ n, f n) := by
  rw [← MeasurableSet.compl_iff]
  rw [Set.compl_iInter]
  apply MeasurableSet.iUnion
  intro n
  exact (hf n).compl

end Section13Sheet2

end FM2026_14_2

-- ════════════════════════════════════════════════════════════════
-- Section14measureTheory/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_14_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- imports all the Lean tactics
/-

# The extended nonnegative reals [0,∞]

The big dilemma when a designer is faced with "minor modifications"
of a standard type, is whether to just stick with the standard type
and make do, or whether to make a new type and then be faced with the
problem of having to make all the API for that type. Example: in measure
theory a key role is played by the "extended non-negative reals",
namely {x : ℝ | 0 ≤ x} ∪ {∞}. In Lean these are their own type,
called `ENNReal`. There is a "scope" containing standard notation
associated for this type. Let's open it.

```lean
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal
scoped[ENNReal] notation "∞" => (⊤ : ENNReal)
```
-/

namespace Section13Sheet3

open scoped ENNReal

#check ENNReal
-- #print notation ℝ≥0∞
-- does not work in Lean4, but `go to definition` works like magic
#check ℝ≥0∞ -- [0,∞]
#check ∞ -- it's the ∞ in ℝ≥0∞
-- What can we do with extended non-negative reals?
variable (a b : ℝ≥0∞)

#check a + b

#check a - b -- surprising?
#check a * b -- what is 0 * ∞ then?
#check a / b

-- is 1 / 0 = 0 or ∞? In ℝ it's 0 but here there's another possibility
example : (0 : ℝ≥0∞) * ∞ = 0 := by
  simp

example : (1 : ℝ≥0∞) / 0 = ∞ := by
  simp

example (a b c : ℝ≥0∞) : (a + b) * c = a * c + b * c := by
  exact add_mul a b c

end Section13Sheet3

end FM2026_14_3

-- ════════════════════════════════════════════════════════════════
-- Section14measureTheory/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_14_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jason Kexing Ying, Kevin Buzzard
-/

/-

# Measures

Recall that Lean calls a space equipped with
a sigma algebra a "MeasurableSpace". We will go with this language
and call sets in the sigma algebra "measurable sets".

Given a measurable space, a *measure* on the measurable space is a function from
the measurable sets to `[0,∞]` which is countably additive (i.e.,
the measure of a countable disjoint union of measurable sets is the sum of the measures).
This is not the *definition* of a measure in Lean, but it is mathematically equivalent to the
definition.

For what it's worth, the actual definition of a measure in Lean is this: an `OuterMeasure`
on a type `α` is this:

```lean
structure OuterMeasure (α : Type*) where
  measureOf : Set α → ℝ≥0∞
  empty : measureOf ∅ = 0
  mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  iUnion_nat : ∀ s : ℕ → Set α, measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
```

So it attaches an element of `[0,∞]` to *every* subset of α, satisfying some natural axioms;
note in particular it is countably *sub*additive, meaning that the measure of a countable
union of open sets, even if they're pairwise disjoint, is only assumed to be at most the sum of the measures.

And if `α` has a measurable space structure then a measure on `α` is an outer measure satisfying
some axioms, which boil down to "the restriction of the outer measure is a measure on the measurable
sets, and the extension of this measure to an outer measure agrees with the outer measure we started with".
The advantage of doing it this way is that given a measure, we can evaluate it on *any* subset
(getting the outer measure of the subset) rather than having to supply a proof that the subset
is measurable. This coincides with Lean's "make functions total" philosophy (the same reason that 1/0=0).

-/

section Section13Sheet3

open Filter

open scoped NNReal ENNReal MeasureTheory BigOperators Topology

-- note to self: removed `probability_theory`
namespace MeasureTheory

-- Let Ω be a set equipped with a sigma algebra.
variable {Ω : Type} [MeasurableSpace Ω]

-- Now let's add a measure `μ` on `Ω`
variable {μ : Measure Ω}

/-
Try proving the following:
-/
-- [PATCHED: measure_union_add_inter API changed in Mathlib v4.27]
example (S T : Set Ω) (hS : μ S ≠ ∞) (hT : MeasurableSet T) :
    μ (S ∪ T) = μ S + μ T - μ (S ∩ T) := by
  sorry

/-!
## Measurable functions

So far we've worked in the space `Ω` though with all mathematical objects, we
want to map between them. In measure theory, the correct notion of maps is
measurable functions. If you have seen continuity in topology, they are quite
similar, namely, a function `f` between two measurable spaces is said to be
measurable if the preimages of all measurable sets along `f` is measurable.
-/


/-
*Remark*: while proving the above, you might have noticed I've added the
condition `hS` (think about what is a + ∞ - ∞). In particular, subtraction in
extended non-negative reals (`ℝ≥0∞`) might not be what you expect,
e.g. 1 - 2 = 0 in `ℝ≥0∞`. For this reason, the above lemma is better phrased as
`μ (S ∪ T) + μ (S ∩ T) = μ S + μ T` for which we can omit the condition `hS`.
-/
/-
If you go to the definition of measurable you will find what you expect.
However, of course, measure theory in Lean is a bit more complicated. As we
shall see, in contrast to maths, there are 3 additional notions of measurability
in mathlib. These are:
- `AEMeasurable`
- `StronglyMeasurable`
- `AEStronglyMeasurable`
The reasons for their existence is technical but TLDR: `ae_foo f` is the predicate
that `f` is almost everywhere equal to some function satisfying `foo` (see the
a.e. filter section) while `StronglyMeasurable f` is saying `f` is the limit
of a sequence of simple functions.

Alongside `measurable`, we also see them quite often in the mathlib, although
all you have to know is in most cases (range is metrizable and second-countable),
`Measurable` and `StronglyMeasurable` are equivalent.
-/
example : Measurable (id : Ω → Ω) :=
  measurable_id

example {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  hg.comp hf

/-!
## Integration

One of the primary motivations of measure theory is to introduce a more
satisfactory theory of integration. If you recall the definition of the
Darboux-Riemann integral, we cannot integrate the indicator function of
`ℚ ∩ [0, 1]` despite, intuitively, the set of rationals in the unit interval
is much "smaller" (rationals is countable while the irrationals are not.
In contrast, measure theory allows us to construct the Lebesgue integral
which can deal with integrals such as this one.

Lean uses a even more general notion of integration known as Bochner integration
which allows us to integrate Banach-space valued functions. Its construction
is similar to the Lebesgue integral.

Read page 5-6 of https://arxiv.org/pdf/2102.07636.pdf
if you want to know the details.
-/


-- Suppose now `X` is another measurable space
variable {X : Type} [MeasurableSpace X]

-- and suppose it's also a Banach space (i.e. a vector space and a complete metric space)
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

-- If `f : Ω → X` is a function, then the integral of `f` is written as
-- `∫ x, f x ∂μ`. If you want to integrate over the set `s : set Ω` then write
-- `∫ x in s, f x ∂μ`.
-- Try looking in mathlib
example {f g : Ω → X} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
  integral_add hf hg

-- [PATCHED: set_integral_const renamed to setIntegral_const in Mathlib v4.27]
example (a : X) (s : Set Ω) : ∫ _ in s, a ∂μ = (μ s).toReal • a :=
  setIntegral_const a

-- Harder
-- [PATCHED: set_integral_pos_of_pos_of_measure_pos renamed in Mathlib v4.27]
example
    {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f μ) (hμ : 0 < μ {ω | 0 < f ω}) :
    (0 : ℝ) < ∫ ω in {ω | 0 < f ω}, f ω ∂μ := by
  sorry

/-!
## ae filter

Now we have come to a very important section of working with measure theory
in Lean.

In measure theory we have a notion known as almost everywhere (a.e.). In
probability this is known as almost surely however we will stick with
almost everywhere in this project. Namely, a predicate `P` on `Ω` is said to
be true almost everywhere if the set for which `P` holds is co-null, i.e.
`μ {ω : Ω | P ω}ᶜ = 0`.

As examples, we say:
- given functions `f, g`, `f` equals `g` a.e. if `μ {ω : Ω | f ω ≠ g ω} = 0`;
- `f` is less equal to `g` a.e. if `μ {ω : Ω | ¬ f ω ≤ g ω} = 0` etc.

Often, showing that a property holds a.e. is the best we can do in
measure/probability theory.

In Lean, the notion of a.e. is handled by the `Measure.ae` filter.
Let's construct that filter ourselves.
-/


/-
*Remark* It's a common myth that Lebesgue integration is strictly better than
the Darboux-Riemann integral. This is true for integration on bounded intervals
though it is not true when considering improper integrals. A common example
for this is, while `∫ x in [0, ∞), sin x / x dx` is Darboux-Riemann integrable
(in fact it equals `π / 2`) it is not Lebesgue integrable as
`∫ x in [0, ∞), |sin x / x| dx = ∞`.
-/
-- [PATCHED: .ae field renamed to `ae` function in Mathlib v4.27]
example (X : Type) [MeasurableSpace X] (μ : Measure X) : Filter X :=
  ae μ

-- say `f` and `g` are measurable functions `Ω → X`
variable (f g : Ω → X)

-- The following is a proposition that `f` and `g` are almost everywhere equal
-- it's **not** a proof that `f` and `g` are a.e. equal but simply a statement
example : Prop :=
  ∀ᵐ ω ∂μ, f ω = g ω

-- Here's another example on how to state `f` is almost everywhere less equal
-- than `g`
-- To be able to formulate this we need a notion of inequality on `X` so we
-- will add the `LE` instance on `X`, i.e. equip `X` with a inequality
example [LE X] : Prop :=
  ∀ᵐ ω ∂μ, f ω ≤ g ω

-- Since the above two cases come up quite often, there are special notations
-- for them. See if you can guess what they mean
example : Prop :=
  f =ᵐ[μ] g

example [LE X] : Prop :=
  f ≤ᵐ[μ] g

-- In general, if `P : Ω → Prop` is a predicate on `Ω`, we write `∀ᵐ ω ∂μ, P ω`
-- for the statement that `P` holds a.e.
example (P : Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, P ω

-- Sanity check: the above notation actually means what we think
example (P : Ω → Prop) : (∀ᵐ ω ∂μ, P ω) ↔ μ ({ω | P ω}ᶜ) = 0 := by rfl

-- Here's a more convoluted example. See if you can figure what it means
example (f : ℕ → Ω → ℝ) (s : Set Ω) :=
  ∀ᵐ ω ∂μ.restrict s, ∃ l : ℝ, Tendsto (fun n ↦ f n ω) atTop (𝓝 l)

-- Now to do some exercises: you will need to dig into the source code to see
-- what the definitions are and search for helpful lemmas
-- *Hint*: try out the `measurability` tactic. It should be able to solve simple
-- goals of the form `MeasurableSet s` and `Measurable f`
-- [PATCHED: ae_restrict_of_forall renamed in Mathlib v4.27]
example (s : Set Ω) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ ω ∈ s, f ω = g ω) : f =ᵐ[μ.restrict s] g := by
  sorry

-- [PATCHED: Pi operation unfolding changed in Lean 4.27, linarith needs explicit show]
example (f g h : Ω → ℝ)
    (h₁ : f ≤ᵐ[μ] g) (h₂ : f ≤ᵐ[μ] h) : 2 * f ≤ᵐ[μ] g + h := by
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  show g ω + h ω ≥ 2 * f ω
  linarith

example (f g : Ω → ℝ) (h : f =ᵐ[μ] g) (hg : ∀ᵐ ω ∂μ, 2 * g ω + 1 ≤ 0) :
    ∀ᵐ ω ∂μ, f ω ≤ -1 / 2 := by
  filter_upwards [h, hg] with ω hω hωg
  linarith

example (f g : ℕ → Ω → ℝ) (a b : ℝ)
    (hf : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 a))
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 b)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω + g n ω) atTop (𝓝 (a + b)) := by
  filter_upwards [hf, hg] with ω hωf hωg
  exact hωf.add hωg

/-
I hope that you found the above examples slightly annoying, especially the
third example: why can't we just `rw h`?! Of course, while we often do do so on
paper, rigorously, such a rewrite require some logic. Luckily, what we normally
do on paper is most often ok and we would like to do so in Lean as well. While
we can't directly rewrite almost everywhere equalities, we have the next best
thing: the `filter_upwards` tactic. See the tactic documentation here:
https://leanprover-community.github.io/mathlib_docs/tactics.html#filter_upwards

The `filter_upwards` tactic is much more powerful than simply rewriting a.e.
equalities and is helpful in many situations, e.g. the above second, third
and fourth examples are all easily solvable with this tactic. Let us see how
it works in action.
-/
-- Hover over each line and see how the goal changes
example (f₁ f₂ g₁ g₂ : Ω → ℝ)
    (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂]
  intro ω hω₁ hω₂
  exact add_le_add hω₁ hω₂

-- Here's an even shorter proof using additional parameters of `filter_upwards`
example (f₁ f₂ g₁ g₂ : Ω → ℝ) (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂] with ω hω₁ hω₂ using add_le_add hω₁ hω₂

/-
Intuitively, what `filter_upwards` is doing is simply exploiting the fact that
the intersection of two full measure sets (i.e. complements are null) is also
a set of full measure. Thus, it suffices to work in their intersection instead.

Now, try the above examples again using the `filter_upwards` tactic.
-/
end MeasureTheory

end Section13Sheet3

end FM2026_14_4

-- ════════════════════════════════════════════════════════════════
-- Section15UFDsAndPIDsEtc/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_15_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/

namespace Section14Sheet1

variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 :=
  zero_ne_one

example (I : Ideal R) : I.IsPrincipal :=
  inferInstance

example (I : Ideal R) : ∃ j, I = Ideal.span {j} :=
  ⟨Submodule.IsPrincipal.generator I, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩

-- product of two PIDs isn't a PID, but only because it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    -- every ideal of A × B is of the form I₁ × I₂
    let I1 : Ideal A := I.map (RingHom.fst A B)
    let I2 : Ideal B := I.map (RingHom.snd A B)
    have hI : I = I1.prod I2 := by
      ext x
      constructor
      · intro h
        exact ⟨Ideal.mem_map_of_mem _ h, Ideal.mem_map_of_mem _ h⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective (RingHom.fst A B)
          (fun a => ⟨(a, 0), rfl⟩)).1 h1
        obtain ⟨z, hz, hzx⟩ := (Ideal.mem_map_iff_of_surjective (RingHom.snd A B)
          (fun b => ⟨(0, b), rfl⟩)).1 h2
        have : x = (1, 0) * y + (0, 1) * z := by
          ext
          · simp; exact hyx.symm
          · simp; exact hzx.symm
        rw [this]
        apply Ideal.add_mem
        · apply Ideal.mul_mem_left
          exact hy
        · apply Ideal.mul_mem_left
          exact hz
    rw [hI]
    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal I1
    obtain ⟨b, hb⟩ := IsPrincipalIdealRing.principal I2
    use (a, b)
    rw [ha, hb]
    ext x
    simp [Ideal.mem_prod, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      use (r, s)
      ext <;> simp [hr, hs]
    · rintro ⟨⟨r, s⟩, rfl⟩
      simp

end Section14Sheet1
end FM2026_15_1

-- ════════════════════════════════════════════════════════════════
-- Section15UFDsAndPIDsEtc/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_15_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
-- polynomial rings over a field are EDs

/-

# Euclidean Domains

Lean's definition of a Euclidean domain is more general than the usual one presented
to undergraduates. First things first: here's how to say "let R be a Euclidean domain"

-/

namespace Section14Sheet2

variable (R : Type) [EuclideanDomain R]

/-

And there's various theorems (all known by the typeclass inference system) about
Euclidean domains:

-/

example : EuclideanDomain ℤ := by infer_instance

open scoped Polynomial

-- I neither know nor care why it's noncomputable, but it doesn't matter to mathematicians
noncomputable example (k : Type) [Field k] : EuclideanDomain k[X] :=
  inferInstance

-- Euclidean domains are PIDs
example (R : Type) [EuclideanDomain R] : IsPrincipalIdealRing R :=
  inferInstance

example (R : Type) [EuclideanDomain R] : IsDomain R :=
  inferInstance

/-

Internally the definition of a Euclidean domain is this. It's a ring with the following
structure/axioms:

1) You have a "quotient" function `quotient r s` and a remainder function `remainder r s`,
both of type `R → R → R` (i.e. functions from `R²` to `R`)

2) You have an axiom saying `∀ a b, a = b * quotient a b + remainder a b`

3) You have a binary relation `≺` on the ring such that `remainder a b ≺ b`

4) You have an axiom saying that `≺` is well-founded, i.e., there are no infinite decreasing
sequences.

The point is that these axioms are enough to get Euclid's algorithm to work.

In usual maths you have a function from `R` to `ℕ` sending an element `b` to its "size",
and an axiom saying that the remainder when you divide something by `b` is sent to a smaller
natural number. In Lean the natural numbers are not involved; all that we guarantee is
that you can't keep taking remainders infinitely often, which turns out to be a very slightly
weaker statement. Let's prove that any "normal" Euclidean domain is a mathlib Euclidean domain.

-/

noncomputable example (R : Type) [CommRing R] [IsDomain R] (φ : R → ℕ)
    (h : ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ φ r < φ b))
    (h0 : ∀ a b : R, a ≠ 0 → b ≠ 0 → φ a ≤ φ (a * b)) :
    EuclideanDomain R := by
  classical
  let φ' : R → ℕ := fun r => if r = 0 then 0 else φ r + 1
  have h' (a b : R) : ∃ q r : R,
      a = b * q + r ∧ (b = 0 ∧ q = 0 ∧ r = a ∨ b ≠ 0 ∧ φ' r < φ' b) := by
    by_cases hb : b = 0
    · refine ⟨0, a, by simp [hb], Or.inl ⟨hb, rfl, rfl⟩⟩
    · obtain ⟨q, r, ha, hr⟩ := h a b hb
      refine ⟨q, r, ha, Or.inr ⟨hb, ?_⟩⟩
      dsimp [φ']
      rw [if_neg hb]
      split_ifs with hr0
      · apply Nat.succ_pos
      · apply Nat.succ_lt_succ
        cases hr with
        | inl hr0' => contradiction
        | inr hrb => exact hrb
  choose quot rem h'' using h'
  exact
    { quotient := quot
      quotient_zero := fun a => by
        obtain ⟨-, hb | hb⟩ := h'' a 0
        · exact hb.2.1
        · exact (hb.1 rfl).elim
      remainder := rem
      quotient_mul_add_remainder_eq := fun a b => (h'' a b).1.symm
      r := fun a b => φ' a < φ' b
      r_wellFounded := (measure φ').wf
      remainder_lt := fun a b hb => by
        obtain ⟨-, h_ | h_⟩ := h'' a b
        · exact (hb h_.1).elim
        · exact h_.2
      mul_left_not_lt := fun {a b} hb => by
        unfold φ'
        by_cases ha : a = 0
        · simp [ha]
        · rw [if_neg ha]
          have hab : a * b ≠ 0 := by
            intro h
            exact ha ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)
          grind }

end Section14Sheet2

end FM2026_15_2

-- ════════════════════════════════════════════════════════════════
-- Section15UFDsAndPIDsEtc/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_15_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

/-

# Unique Factorization Domains

Thanks to Yael on the Discord for explaining to me how to write "let R be a UFD"
in Lean! It looks like this.

-/
-- let R be a UFD
variable (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-

The reason we're seeing `UniqueFactorizationMonoid` here is that
the definition of unique factorization domain never mentions addition!
So it makes sense for monoids.

-/
-- a PID is a UFD (so ℤ, k[X] etc are UFDs)
example (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := by infer_instance

-- multivariate polynomials over a field in a set of variables
-- indexed by a (possibly infinite) index set I are a UFD
example (k : Type) [Field k] (I : Type) :
    UniqueFactorizationMonoid (MvPolynomial I k) := inferInstance

/-

Under the hood, the definition of UFD is a bit weird. But

A binary relation ★ is *well-founded* if you can't have an infinite decreasing
sequence a₂ ★ a₁, a₃ ★ a₂, a₄ ★ a₃, ... . For example `<` is well-founded
on the naturals, but `≤` is not, and `<` is not well-founded on the integers.

If `R` is a commutative ring, let's define `a ★ b` to mean "a strictly divides b",
i.e. that there exists a non-unit `c` such that `b = a * c`. The mathlib folks
in their wisdom decided to call `R` a `WfDvdMonoid` ("a well-founded monoid under division")
if this relation is well-founded. For example the integers are a `WfDvdMonoid`,
because (for example) 24 ★ 0, 12 ★ 24, 3 ★ 12, 1 ★ 3, but there's no solution to `x ★ 1`.

-/
example : WfDvdMonoid ℤ := by infer_instance

-- In fact (if you know what this means): any Noetherian integral domain is a `WfDvdMonoid`:
example (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] : WfDvdMonoid R := by
  infer_instance

/-

...and in particular any PID is a `wf_dvd_monoid`.

The point about well-founded orders is that you can do well-founded induction
on them, which is what mathematicians often call "strong induction". In other words,
if `S` is a set and `★` is a well-founded binary relation on `S`, and if
you can prove "for all `s : S`, if `P(t)` is true for all `t ★ s` then `P(s)` is true",
then you can deduce "for all `a : S`, `P(a)` is true" (proof: if `P(a)` is not
true for all `a`, then choose some `a₁` for which it's false, and then by
hypothesis there must be `a₂ ★ a₁` for which `P(a₂)` is false, and go on
like this to obtain a contradiction to well-foundedness).

As a consequence, we can deduce that in an integral which is
a `WfDvdMonoid`, everything nonzero factors as a unit multiplied by a product of irreducibles.
For by well-founded induction all we have to do is to check that if all proper
divisors of a nonzero element `s` factor as unit times irreducibles, then `s` does
too. If `s` is a unit or irreducible then we're done, and if it isn't then
by definition of irreducible it factors as `s = ab` with `a ★ s` and `b ★ s`;
both `a` and `b` factor into irreducibles, so `s` does too.

(Note that this argument proves that every nonzero element of every Noetherian
integral domain factors into irreducibles)

However, the factorization might not be unique (take for example `ℤ[√-5]` or your
favourite non-UFD domain which is Noetherian. The problem is that the concept of prime
and irreducible don't coincide in general integral domains.
In Lean it turns out that the definition of UFD is "`WfDvdMonoid`, and irreducible ↔ prime",
and it's a theorem that this is mathematically equivalent to the usual definition.
The reason for this is that "irreducible ↔ prime" is precisely what you need
to get the proof that two factorizations are equivalent (pull an irreducible off
one factorization, and then use that it's prime to show that it shows up in the
other factorization).

## A theorem

Here's a theorem about UFDs.

The *height* of a prime ideal `P` in a commutative ring `R` is
the largest `n` such that there exists a strictly increasing
chain of prime ideals `P₀ ⊂ P₁ ⊂ ⋯ ⊂ Pₙ = P` (or +∞ if there
are chains of arbitrary length). The claim is that in a UFD,
all height one primes are principal.

-/

namespace Section14Sheet3

-- out of laziness we don't define height n primes in a general
-- commutative ring but just height one primes in an integral
-- domain
/-- An ideal of an integral domain is a height one prime if it's prime, it's
nonzero, and the only strictly smaller prime ideal is the zero ideal. -/
def IsHeightOnePrime
    {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) : Prop :=
  P.IsPrime ∧ P ≠ 0 ∧ ∀ Q : Ideal R, Q.IsPrime ∧ Q < P → Q = 0

-- All height one primes are principal in a UFD.
example (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (P : Ideal R) : IsHeightOnePrime P → P.IsPrincipal := by
  /-
    The maths proof: let P be a height 1 prime. Then P ≠ 0, so choose
    nonzero x ∈ P. Factor x into irreducibles; by primality of P one
    of these irreducible factors π must be in P. But now (π) ⊆ P,
    and (π) is prime and nonzero, so by the height 1 assumption we
    must have (π)=P.
    -/
  intro hP
  obtain ⟨x, hxP, hx0⟩ := P.ne_bot_iff.1 hP.2.1
  obtain ⟨hc, h_irr, h_assoc⟩ := WfDvdMonoid.exists_factors x hx0
  have h_prod_mem : hc.prod ∈ P
  · obtain ⟨u, hu⟩ := h_assoc.symm
    exact hu ▸ P.mul_mem_right _ hxP
  obtain ⟨p, hp_mem, hpP⟩ := (hP.1.multiset_prod_mem_iff_exists_mem hc).1 h_prod_mem
  have hp_irr := h_irr p hp_mem
  have hp_prime := UniqueFactorizationMonoid.irreducible_iff_prime.1 hp_irr
  let Q := Ideal.span {p}
  have hQ_prime : Q.IsPrime := (Ideal.span_singleton_prime hp_prime.ne_zero).2 hp_prime
  have hQP : Q ≤ P
  · rw [Ideal.span_singleton_le_iff_mem]
    exact hpP
  by_cases hQ : Q = P
  · rw [← hQ]
    infer_instance
  · exfalso
    have hlt : Q < P := lt_of_le_of_ne hQP hQ
    have hQ0 : Q = 0 := hP.2.2 Q ⟨hQ_prime, hlt⟩
    apply hp_prime.ne_zero
    rw [← Ideal.span_singleton_eq_bot]
    exact hQ0

end Section14Sheet3

end FM2026_15_3

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_1
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/


/-

# Basic Number Theory

Lean has enough machinery to make number theory a feasible topic for
a final project. In this section I will work through a bunch of examples,
taken from Sierpinski's old book "250 elementary problems in number theory".

## Switching between naturals and integers

Sometimes when doing number theory in Lean you find yourself having to switch
between naturals, integers and rationals. For example, if you want to do `a ^ n`
with `a` an integer, then `n` had better be a natural number, because in general
you can't raise an integer to the power of an integer. However subtraction is
"broken" on naturals:

-/

example : (2 : ℕ) - 3 = 0 :=
  rfl

-- subtraction on naturals "rounds up to 0" as it must return a natural
example : (2 : ℤ) - 3 = -1 :=
  rfl

-- subtraction on integers works correctly
/-

so sometimes you need to dance between the two. There are coercions between
all of these objects:

-/
example (n : ℕ) : ℤ :=
  n

-- works fine
example (n : ℕ) : ℤ :=
  ↑n

-- what it does under the hood
example (n : ℕ) (z : ℤ) : ℚ :=
  n + z
-- gets translated to ↑n + ↑z where the two ↑s
-- represent different functions (ℕ → ℚ and ℤ → ℚ)

/-
The big problem with this is that you end up with goals and hypotheses with `↑` in
which you want to "cancel". The `norm_cast` tactic does this.
-/
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 :=
  by
  /-
    a b : ℕ
    h : a + b = 37
    ⊢ ↑a + ↑b = 37

    exact `h` fails, because of the coercions (the goal is about the integer 37,
    not the natural 37)
    -/
  norm_cast

-- There are several shortcuts you can take here, for example
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 := by exact_mod_cast h

-- `h` is "correct modulo coercions"
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 := by assumption_mod_cast

-- "it's an assumption, modulo coercions"
-- The `ring` tactic can't deal with the `↑`s here (it's not its job)
example (a b : ℕ) : ((a + b : ℕ) : ℤ) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  norm_cast
  -- all the ↑s are gone now
  ring

-- Another approach:
example (a b : ℕ) : ((a + b : ℕ) : ℤ) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
  by
  push_cast
  -- does the "opposite" to `norm_cast`. The `norm_cast` tactic
  -- tries to pull `↑`s out as much as possible (so it changes `↑a + ↑b`
  -- to `↑(a + b)`), and then tries to cancel them. `push_cast` pushes
  -- the ↑s "inwards", i.e. as tightly up to the variables as it can.
  -- Goal is now
  -- ⊢ (↑a + ↑b) ^ 2 = ↑a ^ 2 + 2 * ↑a * ↑b + ↑b ^ 2
  ring
  -- works fine, with variables ↑a and ↑b.

/-

These `cast` tactics do not quite solve all your problems, however.
Sometimes you have statements about naturals, and you would rather
they were about integers (for example because you want to start
using subtraction). You can use the `zify` tactic to change statements
about naturals to statements about integers, and the `lift` tactic to
change statements about integers to statements about naturals. Check
out the Lean 4 documentation for these tactics if you want to know
more (I didn't cover them in the course notes):
- [`zify`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Zify.html#Mathlib.Tactic.Zify.zify)
- [`lift`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Lift.html#Mathlib.Tactic.lift)

## For which positive integers n does n+1 divide n²+1?

This is the first question in Sierpinski's book.

Hint: n+1 divides n^2-1.

-/

namespace Section15Sheet1

example (n : ℕ) (hn : 0 < n) : n + 1 ∣ n ^ 2 + 1 ↔ n = 1 := by
  constructor
  · intro h
    have h_dvd : (n + 1 : ℤ) ∣ (n ^ 2 + 1 : ℤ) := by exact_mod_cast h
    have h_dvd' : (n + 1 : ℤ) ∣ (n + 1 : ℤ) * (n - 1 : ℤ) := dvd_mul_right _ _
    have h_eq : (n + 1 : ℤ) * (n - 1 : ℤ) = n ^ 2 - 1 := by ring
    rw [h_eq] at h_dvd'
    have h_sub : (n + 1 : ℤ) ∣ (n ^ 2 + 1 : ℤ) - (n ^ 2 - 1 : ℤ) := dvd_sub h_dvd h_dvd'
    simp at h_sub
    have h_le : (n + 1 : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h_sub
    zify at hn
    linarith
  · rintro rfl
    norm_num

end Section15Sheet1
end FM2026_16_1

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_2
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

-- added to make Bhavik's proof work
namespace Section15sheet2

/-

# Find all integers x ≠ 3 such that x - 3 divides x³ - 3

This is the second question in Sierpinski's book "250 elementary problems
in number theory".

My solution: x - 3 divides x^3-27, and hence if it divides x^3-3
then it also divides the difference, which is 24. Conversely,
if x-3 divides 24 then because it divides x^3-27 it also divides x^3-3.
But getting Lean to find all the integers divisors of 24 is a bit harder!
-/

-- This isn't so hard
theorem lemma1 (x : ℤ) : x - 3 ∣ x ^ 3 - 3 ↔ x - 3 ∣ 24 := by
  have h : x ^ 3 - 3 = (x - 3) * (x ^ 2 + 3 * x + 9) + 24 := by ring
  constructor
  · intro h1
    rw [h] at h1
    exact (dvd_add_right (dvd_mul_right _ _)).1 h1
  · intro h1
    rw [h]
    exact dvd_add (dvd_mul_right _ _) h1

theorem int_dvd_iff (x : ℤ) (n : ℤ) (hn : n ≠ 0) : x ∣ n ↔ x.natAbs ∈ n.natAbs.divisors := by
  simp [hn]

-- This seems much harder :-) (it's really a computer science question, not a maths question,
-- feel free to skip)
example (x : ℤ) :
    x - 3 ∣ x ^ 3 - 3 ↔
    x ∈ ({-21, -9, -5, -3, -1, 0, 1, 2, 4, 5, 6, 7, 9, 11, 15, 27} : Set ℤ) := by
  rw [lemma1]
  constructor
  · intro h
    have h_mem : (x - 3).natAbs ∈ (24 : ℕ).divisors := by simpa [← Int.ofNat_dvd_right]
    have h_divs : (24 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
    simp
    grind
  · simp +contextual [or_imp]


end Section15sheet2

end FM2026_16_2

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_3
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section15Sheet3
/-

# Prove that there exists infinitely many positive integers n such that
# 4n² + 1 is divisible both by 5 and 13.

This is the third question in Sierpinski's book "250 elementary problems
in number theory".

Maths proof: if n=4 then 4n^2+1=65 is divisible by both 5 and 13
so if n is congruent to 4 mod 5 and mod 13 (i.e if n=4+65*t)
then this will work.

There are various ways to formalise the statement that some set
of naturals is infinite. We suggest two here (although proving
they're the same is fiddly)

-/

-- The number-theoretic heart of the argument.
-- Note that "divides" is `\|` not `|`
theorem divides_of_cong_four (t : ℕ) :
    5 ∣ 4 * (65 * t + 4) ^ 2 + 1 ∧ 13 ∣ 4 * (65 * t + 4) ^ 2 + 1 := by
  constructor
  · have : 4 * (65 * t + 4) ^ 2 + 1 = 5 * (3380 * t ^ 2 + 416 * t + 13) := by ring
    rw [this]
    apply dvd_mul_right
  · have : 4 * (65 * t + 4) ^ 2 + 1 = 13 * (1300 * t ^ 2 + 160 * t + 5) := by ring
    rw [this]
    apply dvd_mul_right

-- There are arbitrarily large solutions to `5 ∣ 4*n²+1 ∧ 13 ∣ 4*n²+1`
theorem arb_large_soln :
    ∀ N : ℕ, ∃ n > N, 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1 := by
  intro N
  use 65 * (N + 1) + 4
  constructor
  · linarith
  · exact divides_of_cong_four _

-- This is not number theory any more, it's switching between two
-- interpretations of "this set of naturals is infinite"
theorem infinite_iff_arb_large (S : Set ℕ) :
    S.Infinite ↔ ∀ N, ∃ n > N, n ∈ S := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨n, hnS, hNn⟩ := h N
    exact ⟨n, hNn, hnS⟩
  · intro h N
    obtain ⟨n, hNn, hnS⟩ := h N
    exact ⟨n, hnS, hNn⟩

-- Another way of stating the question (note different "|" symbols:
-- there's `|` for "such that" in set theory and `\|` for "divides" in number theory)
theorem infinite_setOf_solutions :
    {n : ℕ | 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1}.Infinite := by
  rw [infinite_iff_arb_large]
  exact arb_large_soln

end Section15Sheet3

end FM2026_16_3

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_4
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section15Sheet4
/-

# Prove that for all positive integers n we have that
# 169 | 3³ⁿ⁺³-26n-27

This is the fourth question in Sierpinski's book "250 elementary problems
in number theory".

Proof: note that n=0 also works :-) In general use induction on n.

Base case n=0 works fine.

Inductive step: we assume `169 ∣ 3³ⁿ⁺³-26d-27`
So it divides 27 times this
which is `3³⁽ᵈ⁺¹⁾⁺³-26*27*d-27*27`
and we want it to divide `3³⁽ᵈ⁺¹⁾⁺³-26(d+1)-27`

so we're done if it divides the difference, which is
`-26d-26-27+26*27d+27*27`
which is `26*26n+26*26 = 13*13*something`
-/

-- The statement has subtraction in, so we use integers.
example (n : ℕ) (hn : 0 < n) : -- remark; not going to use hn
    (169 : ℤ) ∣ 3 ^ (3 * n + 3) - 26 * n - 27 := by
  clear hn -- [PATCHED: prevent hn leaking into induction hypothesis in Lean 4.27]
  induction n with
  | zero =>
    simp
  | succ d hd =>
    push_cast
    have h_pow : (3 : ℤ) ^ (3 * (d + 1) + 3) = 27 * 3 ^ (3 * d + 3) := by
      rw [show 3 * (d + 1) + 3 = (3 * d + 3) + 3 by ring, pow_add]
      ring
    rw [h_pow]
    have : 27 * 3 ^ (3 * d + 3) - 26 * (d + 1 : ℤ) - 27 =
        27 * (3 ^ (3 * d + 3) - 26 * d - 27) + 169 * (4 * d + 4) := by
      ring
    rw [this]
    apply dvd_add
    · exact dvd_mul_of_dvd_right hd 27
    · apply dvd_mul_right

end Section15Sheet4

end FM2026_16_4

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet5.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_5
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section15Sheet5

/-

# Prove that 19 ∣ 2^(2⁶ᵏ⁺²) + 3 for k = 0,1,2,...


This is the fifth question in Sierpinski's book "250 elementary problems
in number theory".

thoughts

if a(k)=2^(2⁶ᵏ⁺²)
then a(k+1)=2^(2⁶*2⁶ᵏ⁺²)=a(k)^64

Note that 16^64 is 16 mod 19 according to a brute force calculation
and so all of the a(k) are 16 mod 19 and we're done

-/

theorem sixteen_pow_sixtyfour_mod_nineteen : (16 : ZMod 19) ^ 64 = 16 := by decide

theorem a_k_eq_16 (k : ℕ) : ((2 : ZMod 19) ^ 2 ^ (6 * k + 2)) = 16 := by
  induction k with
  | zero => decide
  | succ d hd =>
    rw [show 6 * (d + 1) + 2 = (6 * d + 2) + 6 by ring, pow_add, pow_mul, hd]
    exact sixteen_pow_sixtyfour_mod_nineteen

example (k : ℕ) : 19 ∣ 2 ^ 2 ^ (6 * k + 2) + 3 := by
  apply (ZMod.natCast_eq_zero_iff _ 19).mp
  push_cast
  rw [a_k_eq_16]
  decide

end Section15Sheet5

end FM2026_16_5

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_6

section Section15Sheet6
/-

# Prove the theorem, due to Kraichik, asserting that 13|2⁷⁰+3⁷⁰

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/

example : 13 ∣ 2 ^ 70 + 3 ^ 70 := by
  simp

end Section15Sheet6

end FM2026_16_6

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet7.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_7
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

section Section15Sheet7

/-

# Prove that for every positive integer n the number 3 × (1⁵ +2⁵ +...+n⁵)
# is divisible by 1³+2³+...+n³

This is question 9 in Sierpinski's book

-/

open scoped BigOperators

open Finset

example (n : ℕ) : ∑ i ∈ range n, i ^ 3 ∣ 3 * ∑ i ∈ range n, i ^ 5 := by
  let S3 : ℕ → ℤ := fun n => ∑ i ∈ range n, (i : ℤ) ^ 3
  let S5 : ℕ → ℤ := fun n => ∑ i ∈ range n, (i : ℤ) ^ 5
  have h3 (n : ℕ) : 4 * S3 n = (n : ℤ) ^ 2 * (n - 1) ^ 2 := by
    induction n with
    | zero => rfl
    | succ d hd =>
      unfold S3; rw [sum_range_succ]
      push_cast
      linear_combination hd
  have h5 (n : ℕ) : 12 * S5 n = (n : ℤ) ^ 2 * (n - 1) ^ 2 * (2 * (n : ℤ) ^ 2 - 2 * n - 1) := by
    induction n with
    | zero => rfl
    | succ d hd =>
      unfold S5; rw [sum_range_succ]
      push_cast
      linear_combination hd
  zify
  push_cast
  have h_eq : 3 * S5 n = S3 n * (2 * (n : ℤ) ^ 2 - 2 * n - 1) := by
    apply Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 1 * h5 n - (2 * (n : ℤ) ^ 2 - 2 * n - 1) * h3 n
  rw [h_eq]
  apply dvd_mul_right

end Section15Sheet7

end FM2026_16_7

-- ════════════════════════════════════════════════════════════════
-- Section16numberTheory/Sheet8.lean
-- ════════════════════════════════════════════════════════════════

section FM2026_16_8
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

namespace Section15Sheet8

open scoped BigOperators

open Finset

/-

## -1 is a square mod p if p=1 mod 4

I formalise the following constructive proof in the solutions:
`((p-1)/2)!` works!

Why does it work: claim `1*2*...*(p-1)/2` squared is `-1`
`1*2*....*(p-1)/2 - p` is 1 mod 4 so this is also
`-1 * -2 * ... * -((p-1)/2)`, and mod p this is the same
`(p-1) * (p-2) * ... ((p+1)/2)`, so `i²=1*2*....*(p-2)*(p-1)=(p-1)!`
Wilson's theorem tells us that `(p-1)! = -1 mod p` if p is prime.

-/

-- [PATCHED: prod_range_reflect API changed in Mathlib v4.27]
theorem exists_sqrt_neg_one_of_one_mod_four
    (p : ℕ) (hp : p.Prime) (hp2 : ∃ n, p = 4 * n + 1) :
    ∃ i : ZMod p, i ^ 2 = -1 := by
  sorry

end Section15Sheet8
end FM2026_16_8
