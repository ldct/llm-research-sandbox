-- Formalising Mathematics 2024 — Solutions (Kevin Buzzard, Imperial College London)
-- Patched for newer Mathlib REPL
-- Source: https://github.com/ImperialCollegeLondon/formalising-mathematics-2024

set_option warningAsError false

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_00

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

You can read the descriptions of these tactics in Part C of the online course
notes here https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_C/tactics/tactics.html
In this course we'll be learning about 30 tactics in total; the goal of this
first logic section is to get you up to speed with ten very basic ones.

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the comma.
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.
-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P := by
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  exact hP
  done

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
-- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)
  exact fish
  done

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- The goal is of the form `X → Y` so we can use `intro`
  intro h
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.
  done

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q :=
  by
  -- `hP` says that `P` is true, and `h` says that `P` implies `Q`, so `apply h at hP` will change
  -- `hP` to a proof of `Q`.
  apply h at hP
  -- now `hP` is a proof of `Q` so that's exactly what we want.
  exact hP
  done

-- The `apply` tactic always needs a hypothesis of the form `P → Q`. But instead of applying
-- it to a hypothesis `h : P` (which changes the hypothesis to a proof of `Q`), you can instead
-- just use a bare `apply h` and it will apply it to the *goal*, changing it from `Q` to `P`.
-- Here we are "arguing backwards" -- if we know that P implies Q, then to prove Q it suffices to prove P.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q :=
  by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply h
  -- Our goal is now `⊢ P`.
  exact hP
  done

/-

## Examples for you to try

-/

/-- Every proposition implies itself. -/
example : P → P := by
  intro banana
  exact banana

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`.

So the next level is asking you prove that `P → (Q → P)`.

-/
example : P → Q → P := by
  intro hP
  intro hQ
  -- the `assumption` tactic will close a goal if
  -- it's exactly equal to one of the hypotheses.
  assumption

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
example : (P → Q → R) → (P → Q) → P → R :=
  by
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

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
  by
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

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
  by
  intro h1 h2 h3
  apply h2
  intro hQ
  apply h1
  intro hP
  exact hQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
  by
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
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R :=
  by
  intro h1 h2 h3
  apply h2
  intro h1 hP h2
  apply h1
  intro hP
  exact h2

-- another approach
example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R :=
  by tauto

end FM_00

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_01

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

example : True := by trivial

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

example : True → False → True → False → True → False :=
  by
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

end FM_01

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_02

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

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
  intro h
  intro h2
  exact h

example : ¬False → True := by
  intro h
  trivial

example : True → ¬False := by
  intro h
  intro h2
  exact h2

example : False → ¬P := by
  intro h
  intro hP
  exact h

example : P → ¬P → False := by
  intro hP
  intro hnP
  apply hnP
  exact hP

example : P → ¬¬P := by
  intro hP
  intro hnP
  apply hnP
  exact hP

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

end FM_02

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM_03

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro hPaQ
  cases' hPaQ with hP hQ
  exact hP

example : P ∧ Q → Q := by
  rintro ⟨hP, hQ⟩
  assumption

example : (P → Q → R) → P ∧ Q → R := by
  rintro hPQR ⟨hP, hQ⟩
  apply hPQR <;> assumption

example : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  · exact hP
  · exact hQ

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

end FM_03

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet5.lean
-- ════════════════════════════════════════════════════════════════

section FM_04

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
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

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    cases' h with hPaQ hR
    cases' hPaQ with hP hQ
    constructor
    · exact hP
    · constructor
      · exact hQ
      · exact hR
  · rintro ⟨hP, hQ, hR⟩
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

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
  by
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
    cases' h with h1 h2
    intro hP
    apply h1 <;> assumption
  apply hnP
  rw [h]
  exact hnP

end FM_04

-- ════════════════════════════════════════════════════════════════
-- Section01logic/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM_05

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

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

example : P ∨ Q → (P → R) → (Q → R) → R :=
  by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  · apply hPR
    exact hP
  · exact hQR hQ

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  · right; assumption
  · left; assumption

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

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  by
  rintro hPR hQS (hP | hQ)
  · left; apply hPR; exact hP
  · right; exact hQS hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ h
  cases' h with hP hR
  · left; apply hPQ; exact hP
  · right; exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  by
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

end FM_05

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_06

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

example : ∃ x y : ℝ, 2 * x + 3 * y = 7 ∧ x + 2 * y = 4 :=
  by
  use 2, 1
  norm_num

end FM_06

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_07

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 :=
  by
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

end FM_07

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_08

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
of Part B of the course book.

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
theorem tendsTo_thirtyseven : TendsTo (fun n ↦ 37) 37 :=
  by
  rw [tendsTo_def]
  intro ε hε
  use 100
  intro n hn
  norm_num
  exact hε

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun n => c) c :=
  by
  intro ε hε
  dsimp only
  use 37
  intro n hn
  ring_nf
  norm_num
  exact hε

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) :=
  by
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

-- alternative proof (peel tactic changed in newer Mathlib)
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  rw [tendsTo_def] at ha ⊢
  intro ε hε
  obtain ⟨B, hB⟩ := ha ε hε
  exact ⟨B, fun n hn => by rw [show -a n - -t = -(a n - t) by ring]; rw [abs_neg]; exact hB n hn⟩

end Section2sheet3solutions

end FM_08

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM_09

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

end FM_09

-- ════════════════════════════════════════════════════════════════
-- Section02reals/Sheet5.lean
-- ════════════════════════════════════════════════════════════════

section FM_10

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

def f_10 : ℕ → ℝ := fun n ↦ n ^ 2 + 3

/-

Mathematicians might write `n ↦ n^2+3` for this function. You can
read more about function types in the "three kinds of types" section
of Part B of the course book.

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
/-- If `a(n)` is a sequence of reals and `t` is a real, `TendsTo_10 a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo_10 (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-

We've made a definition, so it's our job to now make the API
for the definition, i.e. prove some basic theorems about it.

-/
-- If your goal is `TendsTo_10 a t` and you want to replace it with
-- `∀ ε > 0, ∃ B, …` then you can do this with `rw tendsTo_def_10`.
theorem tendsTo_def_10 {a : ℕ → ℝ} {t : ℝ} :
    TendsTo_10 a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
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
theorem tendsTo_thirtyseven_10 : TendsTo_10 (fun n ↦ 37) 37 :=
  by
  rw [tendsTo_def_10]
  intro ε hε
  use 100
  intro n hn
  norm_num
  exact hε

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const_10 (c : ℝ) : TendsTo_10 (fun n => c) c :=
  by
  intro ε hε
  dsimp only
  use 37
  intro n hn
  ring_nf
  norm_num
  exact hε

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tendsTo_add_const_10 {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo_10 a t) :
    TendsTo_10 (fun n => a n + c) (t + c) :=
  by
  rw [tendsTo_def_10] at h ⊢
  ring_nf
  exact h

/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo_10 a t) : TendsTo_10 (fun n => -a n) (-t) := by
  rw [tendsTo_def_10] at ha ⊢
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

-- alternative proof (peel tactic changed in newer Mathlib)
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo_10 a t) : TendsTo_10 (fun n => -a n) (-t) := by
  rw [tendsTo_def_10] at ha ⊢
  intro ε hε
  obtain ⟨B, hB⟩ := ha ε hε
  exact ⟨B, fun n hn => by rw [show -a n - -t = -(a n - t) by ring]; rw [abs_neg]; exact hB n hn⟩

end Section2sheet3solutions
/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- imports all the Lean tactics
-- import the definition of `TendsTo_10` from a previous sheet

namespace Section2sheet5solutions

open Section2sheet3solutions

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo_10 a t) : TendsTo_10 (fun n ↦ -a n) (-t) :=
  by
  rw [tendsTo_def_10] at *
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
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo_10 a t) (hb : TendsTo_10 b u) :
    TendsTo_10 (fun n ↦ a n + b n) (t + u) :=
  by
  rw [tendsTo_def_10] at *
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
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo_10 a t) (hb : TendsTo_10 b u) :
    TendsTo_10 (fun n ↦ a n - b n) (t - u) := by
  simpa [sub_eq_add_neg] using tendsTo_add ha (tendsTo_neg hb)

end Section2sheet5solutions

end FM_10

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_11

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

example : Surjective (id : X → X) :=
  by
  -- goal is `∀ x, ...` so make progress with `intro` tactic
  intro x
  -- goal is `∃ y, ...` so make progess with `use` tactic
  use x
  -- goal is definitionally `x = x`
  rfl

-- Theorem: if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) :=
  by
  -- By definition of injectivity,
  -- We need to show that if a,b are in X and
  -- (g∘f)(a)=(g∘f)(b), then a=b.
  rw [injective_def] at *
  -- so assume a and b are arbitrary elements of X, and let `h` be the
  -- hypothesis thst `g(f(a))=g(f(b))`
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
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) :=
  by
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
  cases' h with y hy
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
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f :=
  by
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
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g :=
  by
  -- assume gf is surjective
  intro hgf
  -- say z in Z
  intro z
  -- by surjectivity of gf, there's x such that gf(x)=x
  cases' hgf z with x hx
  -- we need to prove there's y in Y with g y = z; use f(x)
  use f x
  -- goal is now exactly hx
  exact hx

end Section3sheet1solutions

end FM_11

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_12

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
and `Y={c}` and define `f_12(a)=f_12(b)=c`. In this sheet we learn how to do this.

## Inductive types

There are three ways to make types in Lean. There are function types, quotient
types, and inductive types. Turns out that all types that mathematicians use
to build mathematics are made in one of these three ways. For more information
about all three kinds of types, see the course notes

https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/threekindsoftypes.html

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
example : a ≠ b :=
  by
  -- `a ≠ b` is definitionally equal to `¬ (a = b)` which is
  -- definitionally equal to `a = b → False`. So `intro` works
  intro h
  -- `h : a = b`
  cases h

-- closes the goal.
-- We defined `X` using the `inductive` keyword and these funny `|` "pipe" symbols.
-- If you want to define a function from `X` to another type you can use `def`
-- and the `|` symbols again.
def f_12 : X → ℕ
  | a => 37
  | b => 42
  | c => 0

example : f_12 a = 37 :=
  by-- true by definition
  rfl

-- Here is a proof that `f_12` is an injective function.
-- At some point in this proof there are 9 goals; you can see them
-- by changing the `;` after `cases y` to a `,`. The <;> means
-- "apply the next tactic to all the goals produced by the last tactic".
example : Function.Injective f_12 := by
  intro x y h
  cases x <;> cases y -- at this point there are 9 goals, and for each goal either the conclusion
    -- is true by refl, or there's a false hypothesis `h`.
  all_goals try rfl
  all_goals cases h

end Section3sheet2solutions

end FM_12

-- ════════════════════════════════════════════════════════════════
-- Section03functions/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_13

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

namespace Section3sheet1solutions

/-

# More on functions

Another question on the Imperial introduction to proof problem sheet on functions
is "If `f_13 : X → Y` and `g : Y → Z` and `g ∘ f_13` is injective, is it true that `g` is injective?"
This is not true. A counterexample could be made by letting `X` and `Z` have one element,
and letting `Y` have two elements; `f_13` and `g` are then not hard to write down. Let's
see how to do this in Lean by making inductive types `X`, `Y` and `Z` and functions
`f_13` and `g` which give an explicit counterexample.

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

-- Define f_13 by f_13(X.a)=Y.b
def f_13 : X → Y
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
theorem gYb_eq_gYc : g Y.b = g Y.c :=
  by-- they're both definitionally `Z.d`
  rfl

open Function

theorem gf_injective : Injective (g ∘ f_13) :=
  by
  -- use `rintro` trick to do `intro, cases` at the same time
  rintro ⟨_⟩ ⟨_⟩ _
  rfl

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet.
-- Recall that if you have a hypothesis of the form `h : ∀ A, ...`, then `specialize h X`
-- will specialize `h` to the specific case `A = X`.
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ :=
  by
  intro h
  specialize h X Y Z f_13 g gf_injective gYb_eq_gYc
  cases h

-- Below is another one. Let's make a sublemma first.
theorem gf_surjective : Surjective (g ∘ f_13) := by
  intro z
  use X.a

-- Another question from IUM
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ :=
  by
  intro h
  specialize h X Y Z f_13 g gf_surjective Y.c
  rcases h with ⟨⟨_⟩, ⟨⟩⟩ -- this line does lots of `cases` all in one go.

end Section3sheet1solutions

end FM_13

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_14

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-!

# Sets in Lean, sheet 1 : ∪ ∩ ⊆ and all that

Lean doesn't have "abstract" sets like `{π, ℝ², {1,2,3}}` whose elements can
be totally random; it only has *subsets* of a type. If `X : Type` is a type
then the type of subsets of `X` is called `Set X`. So for example the
subset `{1,2,3}` of `ℕ` is a term of type `Set ℕ`.

A term of type `set X` can be thought of in four ways:

1) A set of elements of `X` (i.e. a set of elements all of which have type `X`);
2) A subset of `X`;
3) An element of the power set of `X`;
4) A function from `X` to `Prop` (sending the elements of `A` to `True` and the other ones to `False`)

So `Set X` could have been called `Subset X` or `Powerset X`; I guess they chose `Set X`
because it was the shortest.

Note that `X` is a type, but if `A` is a subset of `X` then `A` is a *term*; the type of `A` is `Set X`.
This means that `a : A` doesn't make sense. What we say instead is `a : X` and `a ∈ A`.
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

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
  by
  rintro hBA hCA x (hxB | hxC)
  · exact hBA hxB
  · exact hCA hxC

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
  Set.union_subset_union -- found this with `by exact?` (then deleted `by`)

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D :=
  by
  rintro hAB hCD x ⟨hxA, hxC⟩
  exact ⟨hAB hxA, hCD hxC⟩

end Section4sheet1Solutions

end FM_14

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_15

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

end FM_15

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_16

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

end FM_16

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM_17

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

end FM_17

-- ════════════════════════════════════════════════════════════════
-- Section04sets/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM_18

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

-- pushforward is a little trickier. You might have to `ext x, constructor`.
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

end FM_18

-- ════════════════════════════════════════════════════════════════
-- Section05groups/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_19

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-

# Groups

## How to use Lean's groups

In previous courses I have made groups from scratch, but it's kind of irritating
to do (because all the lemma names like `mul_one` are already taken) and I'm
not entirely sure that most students want to know how to make their own
groups, rings, whatever: what's the point if these things are there already?

So in this sheet I explain how to use Lean's groups.

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
example (a b c : G) : a * b * c = a * (b * c) :=
  mul_assoc a b c

-- can be found with `library_search` if you didn't know the answer already
example (a : G) : a * 1 = a :=
  mul_one a

-- Can you guess the last two?
example (a : G) : 1 * a = a :=
  one_mul a

example (a : G) : a * a⁻¹ = 1 :=
  mul_inv_cancel a

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

-- inv_mul_cancel_left
example : a⁻¹ * (a * b) = b := by rw [← mul_assoc, inv_mul_cancel, one_mul]

-- mul_inv_cancel_left
example : a * (a⁻¹ * b) = b := by rw [← mul_assoc, mul_inv_cancel, one_mul]

-- left_inv_eq_right_inv
example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c :=
  by
  have h : b * (a * c) = b * a * c := by rw [mul_assoc]
  rwa [h1, h2, mul_one, one_mul] at h

-- mul_eq_one_iff_inv_eq
example : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  · intro h
    exact left_inv_eq_right_inv (inv_mul_cancel a) h
  · rintro rfl
    exact mul_inv_cancel a

-- inv_one
example : (1 : G)⁻¹ = 1 := by rw [← mul_eq_one_iff_inv_eq, mul_one]

-- inv_inv
example : a⁻¹⁻¹ = a := by rw [← mul_eq_one_iff_inv_eq, inv_mul_cancel]

-- mul_inv_rev
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_eq_one_iff_inv_eq, ← mul_assoc, mul_assoc a, mul_inv_cancel, mul_one, mul_inv_cancel]

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
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by
  rw [inv_one, inv_one, mul_one, mul_inv_rev, inv_inv, inv_inv, mul_assoc, mul_assoc, mul_assoc,
    mul_inv_cancel_left, mul_assoc, mul_inv_cancel_left, inv_mul_cancel]

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g :=
  by
  have useful : ∀ g : G, g = g⁻¹ := by
    intro g
    rw [← eq_comm, ← mul_eq_one_iff_inv_eq]
    exact h g
  intro g h
  rw [useful (g * h), mul_inv_rev, ← useful g, ← useful h]

end FM_19

-- ════════════════════════════════════════════════════════════════
-- Section05groups/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_20

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

namespace Section5sheet2Solutions


-- removing `mul_one` and `mul_inv_cancel` from the five standard axioms
-- for a group.
class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
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
-- proof using cool `calc` mode
theorem mul_left_cancel (h : a * b = a * c) : b = c :=
  calc
    b = 1 * b := by rw [one_mul]
    _ = a⁻¹ * a * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = a⁻¹ * a * c := by rw [mul_assoc]
    _ = 1 * c := by rw [inv_mul_cancel]
    _ = c := by rw [one_mul]

theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  apply mul_left_cancel a⁻¹
  rwa [← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a :=
  by
  apply mul_eq_of_eq_inv_mul
  rw [inv_mul_cancel]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 :=
  by
  apply mul_eq_of_eq_inv_mul
  rw [mul_one]

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
class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

instance : One Bool :=
  ⟨Bool.true⟩

instance : Mul Bool :=
  ⟨fun x y ↦ x⟩

instance : Inv Bool :=
  ⟨fun x ↦ 1⟩

instance : BadGroup Bool where
  mul_assoc := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

example : ¬∀ a : Bool, 1 * a = a := by decide

end Section5sheet2Solutions

end FM_20

-- ════════════════════════════════════════════════════════════════
-- Section05groups/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_21

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
  -- I built this next line bit by bit
  refine H.mul_mem (H.mul_mem (H.mul_mem ha ?_) H.one_mem) (H.mul_mem ha hc)
  exact H.inv_mem hb

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
  rintro (hH | hK)
  · exact Subgroup.mem_sup_left hH
  · exact Subgroup.mem_sup_right hK

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

example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b -- this is the term: no `by`

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  -- if `φ.map_mul` means that `φ` preserves multiplication
  -- (and you can rewrite with this) then what do you think
  -- the lemmas that `φ` preserves inverse and one are called?
  rw [φ.map_mul, φ.map_mul, φ.map_one, φ.map_inv]

-- Group homomorphisms are extensional: if two group homomorphisms
-- are equal on all inputs the they're the same.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  -- Use the `ext` tactic.
  ext a
  apply h

end Homomorphisms

end FM_21

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_22

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

-- Let a,b,c,d be arbitrary elements of `X`
variable (a b c d : X)

-- See if you can prove these basic facts about partial orders.
example : a ≤ a :=
  le_refl a

example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d :=
  le_trans hab (le_trans hbc hcd)

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  apply le_antisymm hab
  exact le_trans hbc hca

end FM_22

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_23

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

example : a ⊔ b = b ⊔ a :=
  by
  -- you might want to start with `apply le_antisymm` (every lattice is a partial order so this is OK)
  -- You'll then have two goals so use `\.` and indent two spaces.
  apply le_antisymm
  · exact sup_le le_sup_right le_sup_left
  · exact sup_le le_sup_right le_sup_left

example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · apply sup_le (sup_le _ _)
    · trans b ⊔ c
      · exact le_sup_right
      · exact le_sup_right
    · exact le_sup_left
    · trans b ⊔ c
      · exact le_sup_left
      · exact le_sup_right
  · refine' sup_le _ (sup_le _ _)
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right

-- could golf this entire proof into one (long) line
-- `a ⊓ _` preserves `≤`.
-- Note: this is called `inf_le_inf_left a h` in mathlib; see if you can prove it
-- directly without using this.
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  apply le_inf
  · exact inf_le_left
  · trans b
    · exact inf_le_right
    · exact h

-- term mode proof
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
  le_inf inf_le_left <| le_trans inf_le_right h

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
  · apply inf_le_inf_left
    exact le_sup_left
  · apply inf_le_inf_left
    exact le_sup_right

-- use `sup_le_sup_left` for this one.
example : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_inf
  · apply sup_le_sup_left
    exact inf_le_left
  · apply sup_le_sup_left
    exact inf_le_right

-- Bonus question: look up the binding powers of ⊓ and ⊔ (by using crtl-click to jump
-- to their definitions) and figure out which brackets
-- can be removed in the statements of the previous two examples without changing
-- their meaning.

end FM_23

-- ════════════════════════════════════════════════════════════════
-- Section06orderingsAndLattices/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM_24

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
  rintro b ⟨⟩

-- recall `b ∈ ∅` is defined to mean `False`, and `cases'` on a proof of `False`
-- solves the goal.
-- this is called `le_bot_iff`
example : a ≤ ⊥ ↔ a = ⊥ := by
  constructor
  · rw [← sSup_empty]
    intro h
    -- to prove x = y suffices to prove x ≤ y and y ≤ x, and we alreasdy have x ≤ y (it's `h`)
    apply le_antisymm h
    apply sSup_le
    rintro _ ⟨⟩
  · -- quicker than `intro h, rw h`
    rintro rfl
    rfl

-- `sSup` is monotone.
-- this is called sSup_le_sSup
example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T :=
  by
  intro hST
  apply sSup_le
  intro b hb
  apply le_sSup
  apply hST
  -- definitional abuse: S ⊆ T is *defined* to mean `∀ a, a ∈ S → a ∈ T`
  exact hb

end FM_24

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_25

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

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
example (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H :=
  by
  apply mul_mem ha
  exact inv_mem hb

-- Now try these. You might want to remind yourself of the API for groups as explained
-- in an earlier section, or make use of the `group` tactic.
-- This lemma is called `Subgroup.inv_mem_iff` but try proving it yourself
example : a⁻¹ ∈ H ↔ a ∈ H := by
  constructor
  · intro h
    -- a bit of advanced `rw` syntax: instead of `have h2 : a = a⁻¹⁻¹, group, rw h2` you can
    -- do the rewrite without ever defining `h2`.
    rw [show a = a⁻¹⁻¹ by group]
    exact inv_mem h
  -- this is the easier way
  · exact inv_mem

-- this is `mul_mem_cancel_left` but see if you can do it from the axioms of subgroups.
-- Again feel free to use the `group` tactic.
example (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H := by
  constructor
  · intro hab
    rw [← H.inv_mem_iff] -- dot notation
    rw [show b⁻¹ = (a * b)⁻¹ * a by group]
    refine' mul_mem _ ha
    exact inv_mem hab
  · exact mul_mem ha

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
  rcases hy with ⟨g, hg, rfl⟩
  use g⁻¹, inv_mem hg
  group

theorem conjugate.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
    (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  rcases hy with ⟨g, hg, rfl⟩
  rcases hz with ⟨k, hk, rfl⟩
  use g * k, mul_mem hg hk
  group

-- Now here's the way to put everything together:
def conjugate (H : Subgroup G) (x : G) : Subgroup G
    where
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

theorem conjugate_mono (H K : Subgroup G) (h : H ≤ K) : conjugate H x ≤ conjugate K x :=
  by
  -- start with `intro g` because the goal is definitionally
  -- `∀ g, g ∈ conjugate H x → g ∈ conjugate K x`
  intro g
  rintro ⟨t, ht, rfl⟩
  exact ⟨t, h ht, rfl⟩

theorem conjugate_bot : conjugate ⊥ x = ⊥ :=
  by
  -- recall that ⊥ is the trivial subgroup and I showed you the basic API for it above.
  -- Start this proof with `ext a`.
  ext a
  rw [mem_conjugate_iff]
  rw [Subgroup.mem_bot]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Subgroup.mem_bot] at hb
    rw [hb]
    group
  · rintro rfl
    use 1
    constructor
    · rw [Subgroup.mem_bot]
    · group

theorem conjugate_top : conjugate ⊤ x = ⊤ := by
  ext a
  rw [mem_conjugate_iff]
  constructor
  · intro h
    exact Subgroup.mem_top a
  · intro h
    use x⁻¹ * a * x
    constructor
    · apply Subgroup.mem_top
    · group

theorem conjugate_eq_of_abelian (habelian : ∀ a b : G, a * b = b * a) : conjugate H x = H :=
  by
  ext a
  rw [mem_conjugate_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [habelian]
    rwa [show x⁻¹ * (x * b) = b by group]
  · intro ha
    use x⁻¹ * a * x
    refine' ⟨_, by group⟩
    rw [habelian]
    rwa [show x * (x⁻¹ * a) = a by group]

end FM_25

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_26

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

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

-- The identity group homomorphism from `G` to `G` is called `monoid_hom.id G`
example : MonoidHom.id G a = a := by rfl

-- true by definition
-- Let K be a third group.
variable (K : Type) [Group K]

-- Let `ψ : H →* K` be another group homomorphism
variable (ψ : H →* K)

-- The composite of ψ and φ can't be written `ψ ∘ φ` in Lean, because `∘` is notation
-- for function composition, and `φ` and `ψ` aren't functions, they're collections of
-- data containing a function and some other things. So we use `monoid_hom.comp` to
-- compose functions. We can use dot notation for this.
example : G →* K :=
  ψ.comp φ

-- When are two group homomorphisms equal? When they agree on all inputs. The `ext` tactic
-- knows this.
-- The next three lemmas are pretty standard, but they are also in fact
-- the axioms that show that groups form a category.
theorem comp_id : φ.comp (MonoidHom.id G) = φ :=
  by
  ext x
  rfl

theorem id_comp : (MonoidHom.id H).comp φ = φ :=
  by
  ext x
  rfl

theorem comp_assoc {L : Type} [Group L] (ρ : K →* L) : (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) := by
  rfl

-- The kernel of a group homomorphism `φ` is a subgroup of the source group.
-- The elements of the kernel are *defined* to be `{x | φ x = 1}`.
-- Note the use of dot notation to save us having to write `monoid_hom.ker`.
-- `φ.ker` *means* `monoid_hom.ker φ` because `φ` has type `monoid_hom [something]`
example (φ : G →* H) : Subgroup G :=
  φ.ker

-- or `monoid_hom.ker φ`
example (φ : G →* H) (x : G) : x ∈ φ.ker ↔ φ x = 1 := by rfl

-- true by definition
-- Similarly the image is defined in the obvious way, with `monoid_hom.range`
example (φ : G →* H) : Subgroup H :=
  φ.range

example (φ : G →* H) (y : H) : y ∈ φ.range ↔ ∃ x : G, φ x = y := by rfl

-- true by definition
-- `subgroup.map` is used for the image of a subgroup under a group hom
example (φ : G →* H) (S : Subgroup G) : Subgroup H :=
  S.map φ

example (φ : G →* H) (S : Subgroup G) (y : H) : y ∈ S.map φ ↔ ∃ x, x ∈ S ∧ φ x = y := by rfl

-- and `subgroup.comap` is used for the preimage of a subgroup under a group hom.
example (φ : G →* H) (S : Subgroup H) : Subgroup G :=
  S.comap φ

example (φ : G →* H) (T : Subgroup H) (x : G) : x ∈ T.comap φ ↔ φ x ∈ T := by rfl

-- Here are some basic facts about these constructions.
-- Preimage of a subgroup along the identity map is the same subgroup
example (S : Subgroup G) : S.comap (MonoidHom.id G) = S :=
  by
  ext x
  rfl

-- Image of a subgroup along the identity map is the same subgroup
example (S : Subgroup G) : S.map (MonoidHom.id G) = S :=
  by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

-- preimage preserves `≤` (i.e. if `S ≤ T` are subgroups of `H` then `φ⁻¹(S) ≤ φ⁻¹(T)`)
example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ :=
  by
  intro g hg
  apply hST
  exact hg

-- image preserves `≤` (i.e. if `S ≤ T` are subgroups of `G` then `φ(S) ≤ φ(T)`)
example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : S.map φ ≤ T.map φ :=
  by
  rintro h ⟨g, hg, rfl⟩
  refine' ⟨g, _, rfl⟩
  exact hST hg

-- Pulling a subgroup back along one homomorphism and then another, is equal
-- to pulling it back along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : U.comap (ψ.comp φ) = (U.comap ψ).comap φ := by
  rfl

-- Pushing a subgroup along one homomorphism and then another is equal to
--  pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : S.map (ψ.comp φ) = (S.map φ).map ψ :=
  by
  ext c
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine' ⟨φ a, _, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

end FM_26

-- ════════════════════════════════════════════════════════════════
-- Section07subgroupsAndHomomorphisms/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_27

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

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
  done


-- The group homomorphism from `G` to `G ⧸ N`
example : G →* G ⧸ N :=
  QuotientGroup.mk' N

/- Remarks:

(1) Why `QuotientGroup.mk'` and not the unprimed `QuotientGroup.mk`? Because the version without the `'`
is just the bare function, the version with the `'` is the group homomorphism.

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
  ext a
  rw [MonoidHom.mem_ker]
  have h : mk' N 1 = 1 := MonoidHom.map_one _
  rw [← h, eq_comm, QuotientGroup.mk'_eq_mk']
  -- now it's just `one_mul` and logic
  simp

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
    intro g hg
    -- the simplifier can help out with this mess:
    suffices φ g ∈ P by simpa [MonoidHom.mem_ker]
    apply h
    use g
    exact ⟨hg, rfl⟩)

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
  -- this proof does my head in
  rfl

end FM_27

-- ════════════════════════════════════════════════════════════════
-- Section08finiteness/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_28

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
variable (Y : Type) (f : X → Y)

example (S : Finset X) : Finset Y :=
  Finset.image f S

-- You can use dot notation to make this shorter
example (S : Finset X) : Finset Y :=
  S.image f

-- See if you can prove these. You'll have to figure out the basic API
-- for `Finset.image`. These theorems are in the library -- your job is simply to find them.
example (S : Finset X) (y : Y) : y ∈ S.image f ↔ ∃ x ∈ S, f x = y := by
  apply Finset.mem_image

example (S : Finset X) (x : X) (hx : x ∈ S) : f x ∈ S.image f := by
  apply Finset.mem_image_of_mem
  exact hx

-- Check that `Finset.image` preserves `≤` (which remember is defined to mean `⊆`)
-- You might have to prove this one directly, using the stuff you discovered above
example (S T : Finset X) (h : S ≤ T) : S.image f ≤ T.image f := by
  intro x -- I couldn't find it :-/ note defeq abuse here
  simp only [Finset.mem_image] -- repeated rewrite
  rintro ⟨a, haS, rfl⟩
  refine ⟨a, ?_, rfl⟩
  apply h
  exact haS

end

end FM_28

-- ════════════════════════════════════════════════════════════════
-- Section08finiteness/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_29

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

This is `[Fintype X]`. It's (in my opinion) harder to use, but finite sums work
for it, and they don't appear to work for `Finite`.

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
  rfl

-- Here's a better proof
example : ∑ x : Fin 10, x.val = 45 := by
  rfl

-- Take a look at the types of the 45 in those proof. Do you know how to? Do you know
-- what's going on? Hint: ℤ/10ℤ.

end FM_29

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_30

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective :=
  by
  rintro ⟨g, hfg, hgf⟩
  constructor
  · -- injectivity
    intro a b h
    -- want to get from `g ∘ f = id` to `∀ x, g (f x) = x`.
    -- For this we need functional extensionality: two functions are equal
    -- if and only if they take the same values on all inputs.
    simp only [funext_iff, Function.comp_apply, id_eq] at hgf
    -- `apply_fun` can change a hypothesis `x = y` to `g x = g y`.
    apply_fun g at h
    -- now use `hgf` to turn `h` into `a = b`, and then
    -- use `h` to close the goal
    rwa [hgf, hgf] at h -- `rwa` means `rw`, then `assumption`.
  · -- surjectivity
    intro y
    use g y
    -- pretty much the only element of x available!
    -- instead of rewrites let's use `change`
    change (f ∘ g) y = id y
    rw [hfg]

-- The other way is harder in Lean, unless you know about the `choose`
-- tactic. Given `f` and a proof that it's a bijection, how do you
-- prove the existence of a two-sided inverse `g`? You'll have to construct
-- `g`, and the `choose` tactic does this for you.
-- If `hfs` is a proof that `f` is surjective, try `choose g hg using hfs`.
example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := by
  -- f is injective and surjective
  rintro ⟨hfi, hfs⟩
  -- construct `g` a one-sided inverse (because `f` is surjective)
  choose g hg using hfs
  -- now you have to use `hg` to prove both f ∘ g = id and g ∘ f = id
  use g
  constructor
  · -- f ∘ g is straightforward
    ext y
    -- use functional extensionality
    exact hg y
  -- abuse of defeq
  · -- g ∘ f needs a trick
    ext x
    -- here we use injectivity
    apply hfi
    -- and here we abuse definitional equality
    exact hg (f x)

end FM_30

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_31

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

namespace Section9Sheet2Solutions
/-

# Constructive bijections

I'm generally quite anti constructive mathematics; it makes things harder
and more confusing for beginners, whilst typically only providing benefits such as
computational content which I am typically not interested in (I never `#eval` stuff,
I just want to prove theorems and I don't care if the proof isn't `rfl`).

But one example of where I love constructivism is `X ≃ Y`, the class
of constructive bijections from `X` to `Y`. What is a constructive
bijection? It is a function `f : X → Y` plus some more data, but here
the data is *not* just the propositional claim that `f` is bijective
(i.e. the *existence* of a two-sided inverse) -- it is the actual
data of the two-sided inverse too.

`X ≃ Y` is notation for `Equiv X Y`. This is the type of constructive
bijections from `X` to `Y`. To make a term of type `X ≃ Y` you need
to give a 4-tuple consisting of two functions `f : X → Y` and `g : Y → X`,
plus also two proofs: firstly a proof of `∀ y, f (g y) = y`, and secondly
a proof of `∀ x, g (f x) = x`.

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
  left_inv :=
    by
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
    -- start with `intro r`, then use `dsimp` to tidy up the mess
    intro r
    dsimp
    ring
  right_inv := by
    intro s
    ring

-- Note that these two terms are *not* equal.
example : bijection1 ≠ bijection2 := by
  -- replace `bijection1` and `bijection2` with their definitions
  unfold bijection1 bijection2
  -- assume for a contradiction that they're equal
  intro h
  -- simplify this mess
  simp at h
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

end Section9Sheet2Solutions

end FM_31

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_32

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

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
example (X : Type) : X ≃ X :=
  { toFun := fun x ↦ x
    invFun := fun y ↦ y
    left_inv := by
      -- got to check that `∀ x, invFun (toFun x) = x`
      intro x
      -- `dsimp` is a tactic which simplifies `(fun x ↦ f x) t` to `f t`.
      dsimp
    right_inv := by
      -- goal is definitionally `∀ y, to_fun (inv_fun y) = y`.
      intro y
      rfl }

-- now let's see you define `Equiv.symm` and `Equiv.trans`.
-- Let's start with `Equiv.symm`.
-- Note that if `e : X ≃ Y` then `e.toFun : X → Y`
-- and `e.left_inv` is a proof of `∀ x : X, e.invFun (e.toFun x) = x` etc
-- This is `Equiv.symm`. Can you fill in the proofs?
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.invFun
    -- you could write `λ x, e.inv_fun x` instead
    invFun := e.toFun
    left_inv := e.right_inv
    right_inv := e.left_inv }

-- Actually, you're not supposed to write `e.toFun` and `e.invFun`
-- directly, because `X ≃ Y` has got a coercion to `X → Y`,
-- so you can (and should) do it like this:
-- `Equiv.symm` again
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.symm
    -- that was using `equiv.symm` and dot notation
    invFun := e
    -- that was using the coercion to function
    left_inv := e.right_inv
    right_inv := e.left_inv }

-- `Equiv.trans`
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  { toFun := fun x => eYZ (eXY x)
    invFun := fun z => eXY.symm (eYZ.symm z)
    left_inv := by
      intro x
      simp
    right_inv := by
      intro z
      simp }

-- Because `Equiv.trans` is already there, we can instead just use it
-- directly:
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  Equiv.trans eXY eYZ

-- here it is again using dot notation
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  eXY.trans eYZ

-- See if you can make the following bijection using dot notation
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
  ∃ e : X ≃ Y, True

example : Equivalence R := by
  refine' ⟨_, _, _⟩
  · intro X
    exact ⟨Equiv.refl X, trivial⟩
  · rintro X Y ⟨eXY, _⟩
    exact ⟨eXY.symm, trivial⟩
  · rintro X Y Z ⟨eXY, _⟩ ⟨eYZ, _⟩
    exact ⟨eXY.trans eYZ, trivial⟩

-- Remark: the equivalence classes of `R` are called *cardinals*.
-- Remark: set theorists might be concerned about size issues here
-- (the "set of all sets" isn't a set, so R "isn't strictly speaking an
--  equivalence relation" because it's not defined on a set). The type theorists
-- know that all this is just nonsense: `R` just lives in a higher universe.

end FM_32

-- ════════════════════════════════════════════════════════════════
-- Section09bijectionsAndIsomorphisms/Sheet4.lean
-- ════════════════════════════════════════════════════════════════

section FM_33

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-

# Isomorphisms (of groups, rings, etc)

If `X` and `Y` are types, we have a type `X ≃ Y` of bijections
from `X` to `Y`. If `X` and `Y` additionally have the structure
of groups, or rings, or orders, or topological spaces, or...
then we can furthermore ask that the bijections preserves this
structure.

Just like in the homomorphism case, we don't do this by making
new predicates like `is_group_isomorphism : G ≃ H → Prop`, we do this
by making totally new types called things like `G ≃* H` (group
isomorphisms), `A ≃+* B` (ring isomorphisms) and so on.

Let's see how this works in practice.

-/

-- let A and B be rings
variable (A B : Type) [Ring A] [Ring B]

-- Here's the type (i.e. the set) of all ring isomorphisms from A to B
example : Type :=
  A ≃+* B

-- `A ≃+* B` is notation for `RingEquiv A B`.
-- A ring isomorphism is magically a function (there is a secret coercion going on)
example (φ : A ≃+* B) (a : A) : B :=
  φ a

-- A ring isomorphism is magically a ring homomorphism
example (φ : A ≃+* B) (x y : A) : φ (x + y) = φ x + φ y :=
  map_add φ x y

-- let C be another ring
variable (C : Type) [Ring C]

-- You can compose two ring isomorphisms using RingEquiv.trans
-- here using the power of dot notation
example (φ : A ≃+* B) (ψ : B ≃+* C) : A ≃+* C :=
  φ.trans ψ

-- How do you make a ring isomorphism from two invertible ring homomorphisms?
example (φ : A →+* B) (ψ : B →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b) : A ≃+* B :=
  { toFun := φ
    invFun := ψ
    left_inv := h1
    right_inv := h2
    map_add' := φ.map_add
    map_mul' := φ.map_mul }

-- Notice that `RingEquiv` *extends* `Equiv`, so you need to fill in the `Equiv` fields and then
-- add in the proofs that `φ(a+b)=φ(a)+φ(b)` and `φ(ab)=φ(a)φ(b)`.
-- Note that we never used that ψ was a ring homomorphism! It follows from the fact that ψ is
-- a bijection whose inverse is a ring homomorphism. But of course Lean knows that the inverse of a
-- ring isomorphism is a ring homomorphism -- it's just a theorem, rather than an axiom.
example (φ : A ≃+* B) (x y : B) : φ.symm (x * y) = φ.symm x * φ.symm y :=
  map_mul φ.symm x y

end FM_33

-- ════════════════════════════════════════════════════════════════
-- Section10TopologicalSpaces/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_34

/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/

namespace Section10sheet1Solutions

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

variable (X : Type)

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
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    trivial

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
--    dsimp
    right
    rfl
  isOpen_inter := by
    rintro s t (rfl | rfl) (rfl | rfl)
    -- four cases
    · left
      simp
    · left
      simp
    · left
      simp
    · right
      simp
  isOpen_sUnion := by
    intro F hF
    by_cases h : Set.univ ∈ F
    · right
      aesop
    · left
      have foo : ∀ s ∈ F, s = ∅ := by -- key intermediate step
        by_contra! h2
        rcases h2 with ⟨s, hs1, hs2⟩
        specialize hF s hs1
        aesop
      exact Set.sUnion_eq_empty.mpr foo -- found with `exact?`

-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  convert isOpen_sUnion (s := ∅) ?_ <;> simp

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro x hx
  use 37
  norm_num

-- will AI be able to write these proofs one day? The proof feels kind of natural
-- and obvious but I still had to write a lot of it manually
lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  obtain ⟨δs, δspos, hs⟩ := hs x (by aesop)
  obtain ⟨δt, δtpos, ht⟩ := ht x (by aesop)
  use min δs δt, by positivity
  rintro y ⟨h1, h2⟩
  constructor
  · apply hs
    have foo : min δs δt ≤ δs := min_le_left δs δt
    constructor <;> linarith
  · apply ht
    have foo : min δs δt ≤ δt := min_le_right δs δt
    constructor <;> linarith

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  simp_rw [Set.mem_sUnion] at hx ⊢
  rcases hx with ⟨t, htF, hxt⟩
  obtain ⟨δ, hδpos, h⟩ := hF t htF x hxt
  use δ, hδpos
  peel h with h1 y hyt
  use t, htF

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion

-- The "philosophy" of Lean is that one shouldn't ask what "the actual definition"
-- of a concept is, but one should just be aware of the theorem which says that
-- the definition is what you think it is. For example

end
end Section10sheet1Solutions

end FM_34

-- ════════════════════════════════════════════════════════════════
-- Section10TopologicalSpaces/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_35

/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
  intros s hs
  apply hg at hs
  apply hf at hs
  exact hs


example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- There's a tactic for continuity proofs by the way
  continuity

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- And of course it's already in the library.
  exact?

end FM_35

-- ════════════════════════════════════════════════════════════════
-- Section11vectorSpaces/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_36

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
which is notation for `hSMul` ("heterongenous scalar multiplication :-| ").
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
  · intro h v hvX
    rw [Submodule.mem_comap]
    apply h
    use v
    exact ⟨hvX, rfl⟩
  · rintro h w ⟨x, hx, rfl⟩
    apply h
    exact hx

end FM_36

-- ════════════════════════════════════════════════════════════════
-- Section11vectorSpaces/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_37

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-

# Finitely-supported functions

We're used to dealing with finite-dimensional vector spaces when we begin studying
vector spaces, but infinite-dimensional vector spaces exist everywhere (for example
the polynonial ring `ℝ[X]` is an infinite-dimensional real vector space) and Lean
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
example (X : Type) (k : Type) [Field k] (f : X →₀ k) : Finset X := f.support -- hover to check!

end

end FM_37

-- ════════════════════════════════════════════════════════════════
-- Section12Filters/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_38

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- imports all the Lean tactics


/-!

# The order (≤) on filters

We think of filters as generalised subsets, and just as subsets are partially ordered
by `⊆`, filters are partially ordered too, by `≤`. Recall that a subset `X : set α`
of `α` gives rise to a principal filter `𝓟 X : filter α`, and we definitely
want `X ⊆ Y ↔ 𝓟 X ≤ 𝓟 Y` so let's think about how this should work. If `F` and `G`
are filters, then `F ≤ G` should mean "the generalised subset `F` is contained
in the generalised subset `G`", so it should mean "if a normal subset of α contains
`G` then it contains `F`", so it should mean `G.sets ⊆ F.sets`, which is in fact
the definition. Note that the smaller the filter `F`, the bigger the collection
`F.sets`, because `F` is contained in more sets!

In the `Filter` namespace there's a lemma


Let's formalise this. Show that 𝓟 S ≤ 𝓟 T ↔ S ⊆ T.
Note that this is called `principal_mono` in mathlib but
there's no harm in proving it yourself.

Some helpful lemmas (all in the `Filter` namespace):

`mem_principal : T ∈ 𝓟 S ↔ S ⊆ T`
`mem_principal_self S : S ∈ 𝓟 S`
`le_def : F ≤ G ↔ ∀ (S : Set α), S ∈ G → S ∈ F`

-/

namespace Section12Sheet2Solutions

variable {α : Type}

open Filter Set
-- so we don't keep having to type `Filter.le_def` and `Set.Subset.trans` etc

open scoped Filter
-- for 𝓟 notation

example (S T : Set α) : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T := by
  constructor
  · intro h
    rw [le_def] at h
    have hT : T ∈ 𝓟 T := mem_principal_self T
    specialize h T hT
    rwa [mem_principal] at h
  · intro hST
    rw [le_def]
    intro X hX
    rw [mem_principal] at hX ⊢
    exact Subset.trans hST hX

-- Here's another useful lemma about principal filters.
-- It's called `le_principal_iff` in mathlib but why
-- not try proving it yourself?
example (F : Filter α) (S : Set α) : F ≤ 𝓟 S ↔ S ∈ F := by
  rw [le_def]
  constructor
  · intro h
    apply h
    exact mem_principal_self S
  · intro hSF X hX
    rw [mem_principal] at hX
    exact mem_of_superset hSF hX

/-

## Filters are a complete lattice

First I claim that if Fᵢ are a bunch of filters, indexed by `i : I`, then
the intersection of `Fᵢ.sets` is also a filter. Let's check this.

-/
def lub {I : Type} (F : I → Filter α) : Filter α where
  sets := {X | ∀ i, X ∈ F i}
  univ_sets := by
    intro i
    apply univ_mem
  sets_of_superset := by
    intro S T hS hST i
    apply mem_of_superset _ hST
    apply hS
  inter_sets := by
    intro S T hS hT i
    exact inter_mem (hS i) (hT i)

/-

Now let's check that this is a least upper bound for the Fᵢ! We check the
two axioms.

-/
-- it's an upper bound
example (I : Type) (F : I → Filter α) (i : I) : F i ≤ lub F := by
  intro S hS
  apply hS

-- it's ≤ all other upper bounds
example (I : Type) (F : I → Filter α) (G : Filter α) (hG : ∀ i, F i ≤ G) :
    lub F ≤ G := by
  intro S hS i
  apply hG
  exact hS

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
  lub fun G : {G : Filter α | ∀ i, (F i).sets ⊆ G.sets} => G.1

-- it's a lower bound
example (I : Type) (F : I → Filter α) (i : I) : glb F ≤ F i := by
  rintro S hS ⟨G, hG⟩
  dsimp
  apply hG _ hS

-- it's ≥ all other lower bounds
example (I : Type) (F : I → Filter α) (G : Filter α) (hG : ∀ i, G ≤ F i) :
    G ≤ glb F := by
  intro S hS
  unfold glb at hS
  dsimp at hS
  unfold lub at hS
  dsimp at hS
  specialize hS ⟨G, _⟩
  · exact hG
  · exact hS

end Section12Sheet2Solutions

end FM_38

-- ════════════════════════════════════════════════════════════════
-- Section12Filters/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_39

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- imports all the Lean tactics


/-!

# Examples of filters

## `at_top` filter on a totally ordered set

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

namespace Section12Sheet3Solutions

open Set

def atTop (L : Type) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    use e
    intro y hy
    exact mem_univ y
  sets_of_superset := by
    rintro X Y ⟨x, hX⟩ hXY
    --rw mem_set_of_eq,
    use x
    intro y hxy
    --rw subset_def at hXY,
    apply hXY
    exact hX _ hxy
  inter_sets := by
    rintro X Y ⟨x, hX⟩ ⟨y, hY⟩
    use max x y
    intro z hz
    constructor
    · apply hX
      apply le_trans _ hz
      exact le_max_left x y
    · exact hY _ (le_trans (le_max_right _ _) hz)

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
the names of all the lemmas so I have to rely on Kevin telling them all to
me" then what you don't realise is that I myself don't know the names
of all the lemmas either -- I am literally just guessing them and pressing
ctrl-space to check. Look at the names of the lemmas and begin to understand
that you can probably guess them yourself.
-/
def cofinite (α : Type) : Filter α where
  sets := {S : Set α | Sᶜ.Finite}
  univ_sets := by
    rw [mem_setOf_eq]
    rw [compl_univ]
    exact finite_empty
  sets_of_superset := by
    intro S T hS hST
    rw [mem_setOf_eq] at hS ⊢
    rw [← compl_subset_compl] at hST
    exact Finite.subset hS hST
  inter_sets := by
    intro S T hS hT
    rw [mem_setOf_eq] at *
    rw [compl_inter]
    exact Finite.union hS hT

/-

## Harder exercises.

If you like this filter stuff, then formalise in Lean and prove the following:

(1) prove that the cofinite filter on a finite type is the entire power set filter (`⊥`).
(2) prove that the cofinite filter on `ℕ` is equal to the `atTop` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `atTop` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

-/

end Section12Sheet3Solutions

end FM_39

-- ════════════════════════════════════════════════════════════════
-- Section13measureTheory/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_40

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- imports all the Lean tactics

/-

# Measure theory

## Sigma algebras.

A σ-algebra on a type `X` is a collection of subsets of `X` satisfying some
axioms, and in Lean you write it like this:

-/

namespace Section13Sheet1Solutions

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
def genBy (A : Set X) : MeasurableSpace X where
  MeasurableSet' S := S = ∅ ∨ S = A ∨ S = Aᶜ ∨ S = ⊤
  measurableSet_empty := by left; rfl
  measurableSet_compl := by
    rintro s (h | h | h | h)
    · right; right; right; simp [h]
    · right; right; left; rw [h]
    · right; left; rw [h]; simp
    · left; rw [h]; simp
  measurableSet_iUnion := by
    intro f hf
    by_cases h1 : ∃ j, f j = ⊤
    · right; right; right
      rw [eq_top_iff]
      rintro x -
      rw [Set.mem_iUnion]
      cases' h1 with j hj
      use j
      rw [hj]
      trivial
    push_neg at h1
    by_cases h2 : ∃ j k, f j = A ∧ f k = Aᶜ
    · right; right; right; rw [eq_top_iff]; rintro x -
      rw [Set.mem_iUnion]
      rcases h2 with ⟨j, k, hj, hk⟩
      by_cases hxA : x ∈ A
      · use j
        rwa [hj]
      · use k
        rwa [hk]
    push_neg at h2
    by_cases h3 : ∃ j, f j = A
    · right; left
      ext x
      rw [Set.mem_iUnion]
      cases' h3 with j hj
      constructor
      · rintro ⟨i, hi⟩
        suffices f i ⊆ A by exact this hi
        rcases hf i with (h | h | h | h)
        · rw [h]; simp
        · rw [h]
        · cases h2 j i hj h
        · cases h1 i h
      · intro hx
        use j
        rwa [hj]
    by_cases h4 : ∃ j, f j = Aᶜ
    · right; right; left
      ext x
      rw [Set.mem_iUnion]
      cases' h4 with j hj
      constructor
      · rintro ⟨i, hi⟩
        suffices f i ⊆ Aᶜ by exact this hi
        rcases hf i with (h | h | h | h)
        · rw [h]; simp
        · cases h2 i j h hj
        · rw [h]
        · cases h1 i h
      · intro hx
        use j
        rwa [hj]
    push_neg at h3 h4
    left
    apply Set.eq_empty_of_subset_empty
    intro x hx
    rw [Set.mem_iUnion] at hx
    cases' hx with i hi
    rcases hf i with (h | h | h | h)
    · rwa [h] at hi
    · cases h3 _ h
    · cases h4 _ h
    · cases h1 _ h

-- An alternative approach to defining the sigma algebra generated by `{A}` is just
-- to use `MeasurableSpace.generateFrom`:
example (A : Set X) : MeasurableSpace X :=
  MeasurableSpace.generateFrom {A}

-- But the problem with that approach is that you don't get the actual sets
-- in the sigma algebra for free. Try this, to see what I mean!
example (A : Set X) :
    (MeasurableSpace.generateFrom {A}).MeasurableSet' =
    ({∅, A, Aᶜ, ⊤} : Set (Set X)) := by
  ext B
  change MeasurableSpace.GenerateMeasurable _ B ↔
    B ∈ ({∅, A, Aᶜ, ⊤} : Set (Set X))
  simp only [Set.top_eq_univ, Set.mem_insert_iff, Set.mem_singleton_iff]
  fconstructor
  · intro h
    induction' h with A' hA' C hC1 hC2 f hf1 hf2
    · aesop
    · aesop
    · aesop
    · exact (genBy X A).measurableSet_iUnion f hf2
  · rintro (rfl | rfl | rfl | rfl)
    · apply MeasurableSpace.GenerateMeasurable.empty
    · apply MeasurableSpace.GenerateMeasurable.basic; simp
    · apply MeasurableSpace.GenerateMeasurable.compl;
      apply MeasurableSpace.GenerateMeasurable.basic; simp
    · rw [show (Set.univ : Set X) = ∅ᶜ by simp]
      apply MeasurableSpace.GenerateMeasurable.compl
      apply MeasurableSpace.GenerateMeasurable.empty

end Section13Sheet1Solutions

end FM_40

-- ════════════════════════════════════════════════════════════════
-- Section13measureTheory/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_41

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- imports all the Lean tactics

/-

# Measure theory

## More on sigma algebras.

-/

namespace Section13Sheet2Solutions

-- Intersection of sigma algebras is a sigma algebra
-- Let 𝓐 be a family of sigma algebras on a type `X`
variable (X : Type) (I : Type) (𝓐 : I → MeasurableSpace X)

-- Then their intersection is also a sigma algebra
open scoped MeasureTheory
-- to get notation `MeasurableSet[S] U` for "U is in the sigma algebra S"

example : MeasurableSpace X :=
  { MeasurableSet' := fun U ↦ ∀ i : I, MeasurableSet[𝓐 i] U
    measurableSet_empty := by
      intro i
      apply @MeasurableSet.empty _ (𝓐 i)
    measurableSet_compl := by
      intro s hs i
      apply MeasurableSet.compl
      apply hs
    measurableSet_iUnion := by
      intro f h i
      apply MeasurableSet.iUnion
      intro j
      apply h }

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
  intro b
  apply MeasurableSet.compl
  apply hf

end Section13Sheet2Solutions

end FM_41

-- ════════════════════════════════════════════════════════════════
-- Section13measureTheory/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_42

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

section Section13Sheet3Solutions

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
example : (0 : ℝ≥0∞) * ∞ = 0 := by norm_num

example : (1 : ℝ≥0∞) / 0 = ∞ := by simp

example (a b c : ℝ≥0∞) : (a + b) * c = a * c + b * c := by ring

end Section13Sheet3Solutions

end FM_42

-- ════════════════════════════════════════════════════════════════
-- Section14UFDsAndPIDsEtc/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_43

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/

section Section14Sheet1Solutions

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
example : (0 : R) ≠ 1 := by
  -- this is another consequence of being an integral domain
  apply zero_ne_one

example (I : Ideal R) : I.IsPrincipal :=
  -- typeclass inference system finds `IsPrincipalIdealRing` and
  -- uses it automatically
  IsPrincipalIdealRing.principal I

example (I : Ideal R) : ∃ j, I = Ideal.span {j} := by
  -- to make a term of type `IsPrincipal I` you need to give one proof,
  -- but we still need to do `cases` or equivalent (I used `obtain` below)
  -- to get this proof out.
  obtain ⟨h⟩ := IsPrincipalIdealRing.principal I
  exact h

-- Typeclass inference knows a bunch of theorems about PIDs and which things are PIDs.
-- Examples:
-- integers are a PID
example : IsPrincipalIdealRing ℤ :=
  EuclideanDomain.to_principal_ideal_domain

-- just check the domain bit:
example : IsDomain ℤ := by infer_instance

-- a field is a PID
example (k : Type) [Field k] : IsPrincipalIdealRing k := by infer_instance

example (k : Type) [Field k] : IsDomain k := by infer_instance

open scoped Polynomial

-- to get `k[X]` notation instead of `polynomial k`
-- polys over a field are a PID
example (k : Type) [Field k] : IsPrincipalIdealRing k[X] := by infer_instance

example (k : Type) [Field k] : IsDomain k[X] := by infer_instance

-- if all ideals of a ring are principal then the ring is a principal ideal ring
example (A : Type) [CommRing A] (h : ∀ I : Ideal A, I.IsPrincipal) :
    IsPrincipalIdealRing A where
  principal := h

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    obtain ⟨a, hA : _ = Ideal.span _⟩ :=
      IsPrincipalIdealRing.principal (I.map (RingHom.fst A B))
    obtain ⟨b, hB : _ = Ideal.span _⟩ :=
      IsPrincipalIdealRing.principal (I.map (RingHom.snd A B))
    use (a, b)
    ext x
    simp only [Ideal.submodule_span_eq]
    rw [Ideal.mem_span_singleton]
    fconstructor
    · intro h
      have h1 : RingHom.fst A B x ∈ I.map (RingHom.fst A B)
      · apply Ideal.mem_map_of_mem _ h
      rw [hA, Ideal.mem_span_singleton] at h1
      rcases h1 with ⟨r, hr⟩
      have h2 : RingHom.snd A B x ∈ I.map (RingHom.snd A B)
      · apply Ideal.mem_map_of_mem _ h
      rw [hB, Ideal.mem_span_singleton] at h2
      rcases h2 with ⟨s, hs⟩
      use(r, s)
      change x = (a * r, b * s)
      rw [← hr, ← hs]
      simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk.eta]
    · rintro ⟨⟨r, s⟩, rfl⟩
      have ha : a ∈ I.map (RingHom.fst A B) := by rw [hA, Ideal.mem_span_singleton]
      have hb : b ∈ I.map (RingHom.snd A B) := by rw [hB, Ideal.mem_span_singleton]
      rw [Ideal.mem_map_iff_of_surjective] at ha hb
      · rcases ha with ⟨⟨a, b'⟩, haI, rfl⟩
        rcases hb with ⟨⟨a', b⟩, hbI, rfl⟩
        suffices (a, b) ∈ I by exact Ideal.mul_mem_right _ _ this
        convert I.add_mem (I.mul_mem_left (1, 0) haI) (I.mul_mem_left (0, 1) hbI) <;> simp
      · intro b; use (0, b); rfl
      · intro a; use (a, 0); rfl

end Section14Sheet1Solutions

end FM_43

-- ════════════════════════════════════════════════════════════════
-- Section14UFDsAndPIDsEtc/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_44

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- polynomial rings over a field are EDs

/-

# Euclidean Domains

Lean's definition of a Euclidean domain is more general than the usual one presented
to undergraduates. First things first: here's how to say "let R be a Euclidean domain"

-/

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
  let φ' : R → ℕ := fun r => if r = 0 then 0 else 1 + φ r
  have h' (a b : R) : ∃ q r : R,
    a = b * q + r ∧ (b = 0 ∧ q = 0 ∧ r = a ∨ b ≠ 0 ∧ φ' r < φ' b)
  · by_cases hb : b = 0
    · refine ⟨0, a, ?_, ?_⟩ <;> aesop
    · rcases h a b hb with ⟨q, r, h1, h2⟩
      refine ⟨q, r, h1, Or.inr ⟨hb, ?_⟩⟩
      aesop
  choose quot rem h'' using h'
  exact
    { quotient := quot
      quotient_zero := by
        intro a
        rcases h'' a 0 with ⟨-, ⟨-, h1, -⟩ | ⟨h1, -⟩⟩ <;>
        aesop
      remainder := rem
      quotient_mul_add_remainder_eq := by
        intro a b
        rw [← (h'' a b).1]
      r := fun a b => φ' a < φ' b
      r_wellFounded := by
        apply InvImage.wf
        exact IsWellFounded.wf
      remainder_lt := by
        intro a b hb
        rcases h'' a b with ⟨-, ⟨h2, -⟩ | h3⟩
        · contradiction
        exact h3.2
      mul_left_not_lt := by
        intro a b hb
        push_neg
        by_cases ha : a = 0
        · simp [φ']
          subst ha
          simp
        · specialize h0 a b ha hb
          simp [φ']
          rw [if_neg ha, if_neg (by aesop)]
          linarith }

end FM_44

-- ════════════════════════════════════════════════════════════════
-- Section14UFDsAndPIDsEtc/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_45

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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

theorem Ideal.mem_iff_associated {R : Type} [CommRing R] (I : Ideal R) {a b : R}
    (hab : Associated a b) : a ∈ I ↔ b ∈ I := by
  rcases hab with ⟨u, rfl⟩
  refine' ⟨I.mul_mem_right _, _⟩
  intro h
  convert I.mul_mem_right ((u⁻¹ : Rˣ) : R) h
  simp

theorem Ideal.IsPrime.not_one_mem
    {R : Type} [CommRing R] {P : Ideal R} (hI : P.IsPrime) :
    (1 : R) ∉ P := by
  intro h
  apply hI.ne_top
  rwa [Ideal.eq_top_iff_one]

theorem Ideal.IsPrime.mem_of_prod_mem
    {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {L : Multiset R} :
    L.prod ∈ P → ∃ x : R, x ∈ L ∧ x ∈ P := by
  refine L.induction_on ?_ ?_
  · intro h
    rw [Multiset.prod_zero] at h
    cases hP.not_one_mem h
  · intro a L IH h
    simp only [Multiset.prod_cons] at h
    rcases hP.mem_or_mem h with (ha | hL)
    · exact ⟨a, by simp, ha⟩
    · obtain ⟨x, hxL, hxP⟩ := IH hL
      exact ⟨x, Multiset.mem_cons_of_mem hxL, hxP⟩

theorem Prime.ideal_span_singleton_isPrime
    {R : Type} [CommRing R] {p : R} (hp : Prime p) :
    (Ideal.span {p} : Ideal R).IsPrime := by
  rwa [Ideal.span_singleton_prime]
  exact hp.ne_zero

namespace Section14Sheet3Solutions

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
  rintro ⟨hPprime, hPnonzero, hht1⟩
  -- P is nonzero so choose nonzero x ∈ P
  have hnonzero : ∃ x ∈ P, x ≠ (0 : R)
  · by_contra! h
    apply hPnonzero
    ext x
    simp only [Ideal.zero_eq_bot, Ideal.mem_bot]
    refine' ⟨h x, _⟩
    rintro rfl
    apply zero_mem
  -- Now factor x
  rcases hnonzero with ⟨x, hxP, hx0⟩
  -- let L be its list of prime factors (up to units)
  obtain ⟨L, hLprime, hLx⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors x hx0
  -- The product of the prime factors is in P
  rw [← P.mem_iff_associated hLx] at hxP
  -- so one of the prime factors (call it pi) is in P
  rcases hPprime.mem_of_prod_mem hxP with ⟨pi, hpiL, hpiP⟩
  -- so (pi) ⊆ P
  have hpiP : Ideal.span {pi} ≤ P := by rwa [Ideal.span_singleton_le_iff_mem]
  -- So either (pi)=P or (pi) ⊂ P
  rw [le_iff_eq_or_lt] at hpiP
  rcases hpiP with (rfl | hcontra)
  · -- if (pi)=P we're done
    use pi
    rfl
  · -- and if not then pi is prime
    have hpiprime : Prime pi := hLprime pi hpiL
    -- so the ideal (pi) is prime
    have hpi : (Ideal.span {pi}).IsPrime :=
      hpiprime.ideal_span_singleton_isPrime
    -- so by our height 1 assumption (pi)=0
    specialize hht1 _ ⟨hpi, hcontra⟩
    change _ = ⊥ at hht1
    -- which is a contradiction as pi≠0
    rw [Ideal.span_eq_bot] at hht1
    specialize hht1 pi (Set.mem_singleton pi)
    cases hpiprime.ne_zero hht1

end Section14Sheet3Solutions

end FM_45

-- ════════════════════════════════════════════════════════════════
-- Section15numberTheory/Sheet1.lean
-- ════════════════════════════════════════════════════════════════

section FM_46

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
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
example (n : ℕ) (hn : 0 < n) : n + 1 ∣ n ^ 2 + 1 ↔ n = 1 := by
  constructor
  · rintro ⟨c, hc⟩
    -- definitional abuse : `a ∣ b` is *defined* to mean `∃ c, b = a * c`
    zify at hc hn ⊢
    -- I want to work with integers
    have h1 : (n : ℤ) ^ 2 - 1 = (n + 1) * (n - 1) := by ring
    have h2 : (n : ℤ) + 1 ∣ 2 := by
      use c - (n - 1)
      linear_combination hc
    -- found with `polyrith` tactic
    have h3 : (n : ℤ) + 1 ≤ 2 := Int.le_of_dvd zero_lt_two h2
    linarith
  · rintro rfl
    norm_num

end FM_46

-- ════════════════════════════════════════════════════════════════
-- Section15numberTheory/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_47

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/


-- added to make Bhavik's proof work

namespace Section15sheet2Solutions

/-

# Find all integers x ≠ 3 such that x - 3 divides x³ - 3

This is the second question in Sierpinski's book "250 elementary problems
in number theory".

My solution: x - 3 divides x^3-27, and hence if it divides x^3-3
then it also divides the difference, which is 24. Conversely,
if x-3 divides 24 then because it divides x^3-27 it also divides x^3-3.
But getting Lean to find all the integers divisors of 24 is a nightmare!
Bhavik (last year) managed to figure out how to do this.

-/
-- This isn't so hard
theorem lemma1 (x : ℤ) : x - 3 ∣ x ^ 3 - 3 ↔ x - 3 ∣ 24 := by
  have h : x - 3 ∣ x ^ 3 - 27
  · use x ^ 2 + 3 * x + 9
    ring
  constructor
  · intro h1
    have h2 := dvd_sub h1 h
    convert h2
    ring
  · intro h1
    convert dvd_add h h1 using 1
    ring


theorem int_dvd_iff (x : ℤ) (n : ℤ) (hn : n ≠ 0) : x ∣ n ↔ x.natAbs ∈ n.natAbs.divisors := by
  simp [hn]

theorem lemma2 (x : ℤ) :
    x ∣ 24 ↔
    x ∈ ({-24, -12, -8, -6, -4, -3, -2, -1, 1, 2, 3, 4, 6, 8, 12, 24} : Set ℤ) :=
  by
  suffices : x ∣ 24 ↔ x.natAbs ∈ ({1, 2, 3, 4, 6, 8, 12, 24} : Finset ℕ)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [Finset.mem_insert, Int.natAbs_eq_iff, Nat.cast_one,
      Nat.cast_ofNat, Finset.mem_singleton] at this
    tauto
  exact int_dvd_iff _ 24 (by norm_num)


-- This seems much harder :-) (it's really a computer science question, not a maths question,
-- feel free to skip)
example (x : ℤ) :
    x - 3 ∣ x ^ 3 - 3 ↔
    x ∈ ({-21, -9, -5, -3, -1, 0, 1, 2, 4, 5, 6, 7, 9, 11, 15, 27} : Set ℤ) := by
  rw [lemma1]
  rw [lemma2]
  simp only [Set.mem_insert_iff, sub_eq_neg_self, Set.mem_singleton_iff,
    sub_eq_iff_eq_add]
  norm_num

end Section15sheet2Solutions

end FM_47

-- ════════════════════════════════════════════════════════════════
-- Section18graphTheory/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_48

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- paths, cycles etc in graph theory

/-

Cut and pasted directly from the module docstring from the file imported above:

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

(and then there's a warning that in topology some of these words are
used to mean different things)

So of course the question is how to actually do this in Lean. Here's how.
Let `G` be a simple graph with vertex set `V`, and say `v,w,x` in `V`

-/
variable (V : Type) (G : SimpleGraph V) (v w x : V)

-- The type of all walks from `v` to `w`
example : Type :=
  G.Walk v w

-- The empty walk from `v` to `v`
example : G.Walk v v :=
  SimpleGraph.Walk.nil' v

-- oh that's a bit annoying, let's open `SimpleGraph`
open SimpleGraph

example : G.Walk v v :=
  Walk.nil' v

-- Add an edge to the beginning of a walk
example (h : G.Adj v w) (a : G.Walk w x) : G.Walk v x :=
  Walk.cons' v w x h a

-- There's also walk.cons where you don't have to specify the vertices
example (h : G.Adj v w) (a : G.Walk w x) : G.Walk v x :=
  Walk.cons h a

-- concatenation of walks
example (a : G.Walk v w) (b : G.Walk w x) : G.Walk v x :=
  a.append b

-- Let `a` be a walk from `v` to `w`
variable (a : G.Walk v w)

-- length of `a` is a natural
example : ℕ :=
  a.length

-- reverse of `a`
example : G.Walk w v :=
  a.reverse

-- n'th vertex visited in `a`
example (n : ℕ) : V :=
  a.getVert n

-- 0'th vertex is where we start
example : a.getVert 0 = v :=
  Walk.getVert_zero a

-- (Walk length)'th vertex is where we end.
example : a.getVert a.length = w :=
  Walk.getVert_length a

-- Support of `a` is the list of vertices it goes through
example : List V :=
  a.support

-- Edges of `a` is the list of edges it goes through
example : List (Sym2 V) :=
  a.edges

-- A walk is a *trail* if it has no repeating edges.
example : Prop :=
  a.IsTrail

-- A walk is a *path* if it has no repeating vertices.
example : Prop :=
  a.IsPath

-- Paths are sufficiently common that `G.path v w` is defined to be the
-- subtype `{p : G.walk v w // p.is_path}`. So to give a term of type `G.path v w`
-- is to give a pair consisting of a walk `p : G.walk v w` and a proof of `p.is_path`.
-- A walk is a *circuit* at `v : V` if it's a nonempty trail beginning and ending at `v`.
example (b : G.Walk v v) : Prop :=
  b.IsCircuit

-- A walk is a *cycle* at `v : V` if it's a circuit at `v` whose only repeating vertex
-- is `v` (which appears exactly twice).
example (b : G.Walk v v) : Prop :=
  b.IsCycle

-- Exercise : give an example of a circuit which isn't a cycle. Can you do it in Lean?
@[reducible]
def g5 : SimpleGraph (Fin 5) :=
  completeGraph _

instance : DecidableRel g5.Adj := SimpleGraph.Top.adjDecidable _

theorem e10 : g5.Adj 1 0 := by decide

theorem e21 : g5.Adj 2 1 := by decide

theorem e02 : g5.Adj 0 2 := by decide

theorem e30 : g5.Adj 3 0 := by decide

theorem e43 : g5.Adj 4 3 := by decide

theorem e04 : g5.Adj 0 4 := by decide

def a5 : g5.Walk 0 0 :=
  ((((((Walk.nil' 0).cons e10).cons e21).cons e02).cons e30).cons e43).cons e04

example : a5.IsCircuit :=
  { edges_nodup := by decide
    ne_nil := by rintro ⟨⟩ }

example : ¬a5.IsCycle := by
  rintro ⟨-, h⟩
  revert h
  refine' @List.Duplicate.not_nodup _ _ 0 _
  simp [a5]
  decide

-- Example theorem in the API: given a walk `p` from `v` to `u` and an edge from `u` to `v`,
-- putting them together gives a cycle iff `p` is a path and the edge from `u` to `v`
-- is not in the edges of `p`.
example {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ Sym2.mk (u, v) ∉ p.edges :=
  Walk.cons_isCycle_iff p h

-- Given a walk from `v` to `w` and a vertex `u` in the support of the walk,
-- truncate the walk so it starts at `v` and finishes at `u`.
open scoped Classical

noncomputable section

-- don't ask me
example (a : G.Walk v w) (u : V) (hu : u ∈ a.support) : G.Walk v u :=
  a.takeUntil u hu

-- With the same hypotheses, return the rest of the walk from `u` to `w`
example (a : G.Walk v w) (u : V) (hu : u ∈ a.support) : G.Walk u w :=
  a.dropUntil u hu

-- Example in the API : those two walks added together give the original
-- walk again
example (a : G.Walk v w) (u : V) (hu : u ∈ a.support) :
    (a.takeUntil u hu).append (a.dropUntil u hu) = a :=
  Walk.take_spec a hu

-- Two vertices `u` and `v` satisfy `G.Reachable u v : Prop` if there's a walk from `u` to `v`.
example : G.Reachable v w ↔ Nonempty (G.Walk v w) :=
  Iff.rfl

-- true by definition
-- Can you show that `G.Reachable` is an equivalence relation?
example : Equivalence G.Reachable := by
  refine' ⟨_, _, _⟩
  · intro a
    exact ⟨Walk.nil' a⟩
  · rintro v w ⟨a⟩
    exact ⟨a.reverse⟩
  · rintro v w x ⟨a⟩ ⟨b⟩
    exact ⟨a.append b⟩

-- A graph is "preconnected" if `G.Reachable v w` is true for any `v w : V`.
-- Note that this includes the empty graph with `V` empty, for silly logic reasons.
example : G.Preconnected ↔ ∀ v w : V, G.Reachable v w :=
  Iff.rfl

-- true by definition
-- A graph is connected iff it's preconnected and nonempty.
example : G.Connected ↔ G.Preconnected ∧ Nonempty V :=
  connected_iff G

end

end FM_48

-- ════════════════════════════════════════════════════════════════
-- Section18graphTheory/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_49

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- trees and forests

/-

# Trees and forests

A *forest* is a graph with no cycles. A *tree* is a connected forest.

Here's how to do this in Lean. Let `G` be a graph with vertex set `V`.

-/

variable (V : Type) (G : SimpleGraph V)

-- Here's how to say "G is a forest"
example : Prop :=
  G.IsAcyclic

-- It's defined to mean "For all `v : V`, every walk from `v` to `v` is not a cycle. "
example : G.IsAcyclic ↔ ∀ (v : V) (p : G.Walk v v), ¬p.IsCycle := by rfl

-- Here's how to say "G is a tree"
example : Prop :=
  G.IsTree

example : G.IsTree ↔ G.Connected ∧ G.IsAcyclic :=
  G.isTree_iff

-- Here are some harder theorems from the library. Recall that a *path* is a walk
-- with no repeated vertices.
-- A graph is acyclic iff for all `v w : V`, there's at most one path from `v` to `w`.
example : G.IsAcyclic ↔ ∀ (v w : V) (p q : G.Path v w), p = q :=
  SimpleGraph.isAcyclic_iff_path_unique

-- A graph is a tree iff `V` is nonempty and for all `v w : V`,
-- there's exactly one path from `v` to `w`.
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath :=
  SimpleGraph.isTree_iff_existsUnique_path

-- If you want a logic puzzle, rephrase this in terms of `G.path`
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Path v w, True :=
  by
  rw [SimpleGraph.isTree_iff_existsUnique_path]
  apply and_congr Iff.rfl
  apply forall_congr'; intro v
  apply forall_congr'; intro w
  constructor
  · rintro ⟨p, hp, hp2⟩
    refine' ⟨⟨p, hp⟩, True.intro, _⟩
    rintro ⟨q, hq⟩ -
    ext
    exact hp2 _ hq
  · rintro ⟨⟨p, hp⟩, -, h2⟩
    refine' ⟨p, hp, fun q hq => _⟩
    specialize h2 ⟨q, hq⟩ True.intro
    cases h2
    rfl

/-
If you want a hard graph theory puzzle, prove that in a finite tree,
1 + the number of edges equals the number of vertices.
I don't think this is in the library and it would be a neat project.

Because induction on the size of `V` will be messy (it will involve
changing `V` and them moving between graphs on different types)
I think that the best way to do this would be to prove that for
an acyclic graph on a fixed `V`, #connected components + #edges = #vertices,
by induction on number of edges.

Note: the solution to this is not in the solutions!
-/
open scoped Classical

example (V : Type) [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    1 + Finset.card G.edgeFinset = Fintype.card V :=
  sorry

end FM_49

-- ════════════════════════════════════════════════════════════════
-- Section20representationTheory/Sheet2.lean
-- ════════════════════════════════════════════════════════════════

section FM_50

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/


namespace Section20Sheet2Solutions

/-

# Representation theory

Homomorphisms between representations; representations as modules.

-/
-- Let ρ and σ be representations of G on V and W
variable {k : Type} [Field k] {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module k V]
variable {W : Type} [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

-- According to one of my PhD students yesterday, there is no "G-linear map" class!
-- So let's make one.
-- this makes the `ext` tactic work on rep_maps, i.e. it shows that two rep_maps are
-- the same if they are the same underlying function
/-- The G-equivariant linear maps between two representations. -/
@[ext]
structure RepMap (ρ : Representation k G V) (σ : Representation k G W) : Type where
  toLinearMap : V →ₗ[k] W
  map_apply : ∀ (g : G) (v : V), toLinearMap (ρ g v) = σ g (toLinearMap v)

-- What should be now prove about it?
/-

## Categories

A category is a collection of objects, and between any pair of objects there's a collection
of maps or morphisms. Technical point: these maps/morphisms *don't actually have to be functions*,
the definition is more abstract than that. But let's not dwell on this right now.

That's not the end of the definition of a category -- there is a bit more structure,
and some axioms, but let's just give some examples first:

Example: in set theory the collection of all sets is a category; the morphisms between two sets
are just the functions between the sets.

Example: In type theory the collection of all types is a category; the morphisms are again just
the functions between the types.

Example: if we fix a field `k` and a group `G` then we can make a category whose objects
are `k`-vector spaces equipped with an action of `G` (i.e. representations of `G`) and
whose morphisms are the `G`-linear maps. Note that here the morphisms are *certain* maps
between the objects, but not *all* the maps.

Let's get back to the definition of a category. I need to explain the extra
structure and the axioms of a category. The extra structure is:

S1) For every object `X` of the category, there has to be an identity morphism `id_X : X → X`
S2) If we have three objects `X`, `Y`, and `Z` in the category, and two morphisms
`f : X → Y` and `g : Y → Z` then there's a way of composing them to get `g ∘ f : X → Z`.

For example, in the representation theory example above, the category theoretic composition
is just defined to be function composition, and ensuring that this gives a valid morphism
boils down to checking that the composite of two `G`-linear maps is `G`-linear.

The axioms are:

A1) If `f : X → Y` then `id_Y ∘ f = f` and `f ∘ id_X = f`
A2) If `f : W → X`, `g : X → Y` and `h : Y → Z` then `(f ∘ g) ∘ h = f ∘ (g ∘ h)`

The reason I mention these is that they inform us about what we should be proving
about `RepMap`!

-/
namespace RepMap

def id (ρ : Representation k G V) : RepMap ρ ρ where
  toLinearMap := LinearMap.id
  map_apply _ _ := rfl

variable {X : Type} [AddCommGroup X] [Module k X]

variable {ρ σ}

def comp {τ : Representation k G X}
    (ψ : RepMap σ τ) (φ : RepMap ρ σ) : RepMap ρ τ where
  toLinearMap := ψ.toLinearMap.comp φ.toLinearMap
  map_apply := by
    intros
    simp [φ.map_apply, ψ.map_apply]

theorem comp_id_50 (φ : RepMap ρ σ) : φ.comp (id ρ) = φ := by
  ext; rfl

theorem id_comp_50 (φ : RepMap ρ σ) : (id σ).comp φ = φ := by
  ext; rfl

theorem comp_assoc_50
    {τ : Representation k G X} {Y : Type} [AddCommGroup Y] [Module k Y]
    {υ : Representation k G Y}
    (ξ : RepMap τ υ) (ψ : RepMap σ τ) (φ : RepMap ρ σ) :
    (ξ.comp ψ).comp φ = ξ.comp (ψ.comp φ) := by
  rfl

end RepMap

end Section20Sheet2Solutions

end FM_50

-- ════════════════════════════════════════════════════════════════
-- Section20representationTheory/Sheet3.lean
-- ════════════════════════════════════════════════════════════════

section FM_51

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
-- Maschke's theorem

/-

# Representation theory via k[G]-modules

It might have struck you as odd that we have a definition of `representation`
but not a definition of map between representations. One reason for this
is that there's another way of thinking about representations, which is
that they are `k[G]-modules`. Here `k[G]` is the so-called group ring associated
to `k` and `G`; it's a vector space with basis indexed by `G`, and multiplication
given by multiplication on `G` and extended linearly, so (∑ aᵢgᵢ)(∑ bⱼhⱼ) := ∑ᵢⱼ(aᵢbⱼ)(gᵢhⱼ)
for `aᵢ, bⱼ : k` and `gᵢ, hⱼ : G`.

Because the construction works with monoids (note that there's no mention of inverses
in the definition of the group ring), it's called `MonoidAlgebra` in Lean.

-/

variable (k : Type) [Field k] (G : Type) [Group G]

example : Type :=
  MonoidAlgebra k G

noncomputable section

-- Lean moans about various things if you don't switch this on
-- Note that this doesn't matter for mathematicians, this is a computer science thing
example : Ring (MonoidAlgebra k G) :=
  inferInstance

-- Turns out that there's a bijection between modules for the group ring k[G],
-- and representations of G on k-vector spaces. The dictionary works like this.
-- Let ρ be a representation of G on a k-vector space V
variable (V : Type) [AddCommGroup V] [Module k V] (ρ : Representation k G V)

-- Here's the underlying type of the module.
example : Type :=
  ρ.asModule

-- Note that `ρ.as_module` is definitionally equal to `V`, but it knows about `ρ` because `ρ` is in its name.
-- As a result, this works:
example : Module (MonoidAlgebra k G) ρ.asModule :=
  inferInstance

-- This wouldn't work with `ρ.asModule` replaced by `V`, because type class inference wouldn't
-- be able to find `ρ`
-- The other way: let `M` be a `k[G]`-module
variable (M : Type) [AddCommGroup M] [Module (MonoidAlgebra k G) M]

-- Here's the representation
example : Representation k G (RestrictScalars k (MonoidAlgebra k G) M) :=
  Representation.ofModule M
-- What's going on here? The issue is that type class inference can't by default find the k-module
-- structure on `M`, so this `restrict_scalars k (monoid_algebra k G) M` thing means "`M`, but with
-- the `k`-action coming from the monoid_algebra k G action"
-- It's defeq to `M`:
example : RestrictScalars k (MonoidAlgebra k G) M = M :=
  rfl

-- So another way of doing morphisms between representations is as `MonoidAlgebra k G` morphisms.
-- Let σ be another representation
variable (W : Type) [AddCommGroup W] [Module k W] (σ : Representation k G W)

-- The type of G-morphisms between `ρ` and `σ`
example : Type :=
  ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule

-- If you do it this way, then you don't have to make G-morphisms.
-- Let φ be a G-morphism
variable (φ : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule)

-- Then you can evaluate it at elements of `V`
example (v : V) : W :=
  φ v

-- This works because `V = ρ.asModule` definitionally.
-- The k[G]-module language is how Lean expresses Maschke's theorem.
-- Assume `G` is finite, and its order is invertible in `k`
variable [Fintype G] [Invertible (Fintype.card G : k)]

-- Assume `V` and `W` are k[G]-modules (with the k[G]-action compatible with the k-action)
variable [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V]
  [Module (MonoidAlgebra k G) W] [IsScalarTower k (MonoidAlgebra k G) W]

-- Then every injective k[G]-linear map from `V` to `W` has a one-sided inverse
-- (and hence a complement, namely the kernel of the inverse)
example (φ : V →ₗ[MonoidAlgebra k G] W) (hφ : LinearMap.ker φ = ⊥) :
    ∃ ψ : W →ₗ[MonoidAlgebra k G] V, ψ.comp φ = LinearMap.id :=
  MonoidAlgebra.exists_leftInverse_of_injective φ hφ

end

end FM_51

-- ════════════════════════════════════════════════════════════════
-- Section21galoisTheory/Sheet6.lean
-- ════════════════════════════════════════════════════════════════

section FM_52

/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/


/-

## Insolvability of the quintic

There exist polynomials whose solutions cannot be expressed by radicals.

Let `E` be a field and assume `p : E[X]` is a polynomial
-/
/-

## Insolvability of the quintic

There exist polynomials whose solutions cannot be expressed by radicals.

Let `E` be a field and assume `p : E[X]` is a polynomial
-/
open scoped Polynomial

variable (E : Type) [Field E] (p : E[X])

-- The Galois group of `p` is the Galois group of `F/E` where `F` is the splitting field of `p`.
open Polynomial

example : p.Gal = (SplittingField p ≃ₐ[E] SplittingField p) :=
  rfl

/-
If F/E is any field extension at all, then `solvable_by_rad E F` is the intermediate field consisting
of elements which can be built using n'th roots and the field operations, starting from `E`. Here
is the rather beautiful definition of the underlying set of this intermediate field:

```
/-- Inductive definition of solvable by radicals -/
inductive is_solvable_by_rad : E → Prop
| base (a : F) : is_solvable_by_rad (algebra_map F E a)
| add (a b : E) : is_solvable_by_rad a → is_solvable_by_rad b → is_solvable_by_rad (a + b)
| neg (α : E) : is_solvable_by_rad α → is_solvable_by_rad (-α)
| mul (α β : E) : is_solvable_by_rad α → is_solvable_by_rad β → is_solvable_by_rad (α * β)
| inv (α : E) : is_solvable_by_rad α → is_solvable_by_rad α⁻¹
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : is_solvable_by_rad (α^n) → is_solvable_by_rad α
```

-/
variable (F : Type) [Field F] [Algebra E F]

example : IntermediateField E F :=
  solvableByRad E F

-- The Abel-Ruffini theorem is that the min poly of an element in `solvable_by_rad E F` has solvable Galois group
example (a : solvableByRad E F) : IsSolvable (minpoly E a).Gal :=
  solvableByRad.isSolvable a

-- This was hard won! It was only finished a year or so ago.
-- A symmetric group of size 5 or more is known not to be solvable:
example (X : Type) (hX : 5 ≤ Cardinal.mk X) : ¬IsSolvable (Equiv.Perm X) :=
  Equiv.Perm.not_solvable X hX

-- Using a root of x^5-4x+2 and the machinery in this section, Browning proves
example : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x :=
  sorry

-- See the file `archive.100-theorems-list.16_abel_ruffini`.

end FM_52

