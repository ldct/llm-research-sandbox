import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Order.Category.Preord

/-!
# Chapter 1, Section 1.1 — Categories

Formalization of §1.1 of Leinster, *Basic Category Theory*.

We rely on Mathlib's `CategoryTheory.Category` for the definition of a category
(Leinster's Definition 1.1.1). We restate the surrounding notions and prove the
small results of the section.
-/

open CategoryTheory

universe v v₁ v₂ u u₁ u₂

namespace LeinsterCh1

/-! ## Definition 1.1.1 (Category)

In Leinster's formulation, a category `𝒜` consists of:

* a collection `ob(𝒜)` of *objects*;
* for every pair `A, B ∈ ob(𝒜)`, a collection `𝒜(A, B)` of *maps*;
* for every `A, B, C`, a composition function `𝒜(B,C) × 𝒜(A,B) → 𝒜(A,C)`;
* for every `A`, an identity `1_A ∈ 𝒜(A, A)`,

subject to associativity and left/right identity.

This is exactly Mathlib's `Category` typeclass, which we will use throughout.
-/

-- Mathlib writes composition left-to-right: `f ≫ g` means "first `f`, then `g`",
-- the reverse of Leinster's `gf`. All statements below use the Mathlib convention.
example (𝒜 : Type u) [Category.{v} 𝒜] (A B C D : 𝒜)
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  rw [Category.assoc]

example (𝒜 : Type u) [Category.{v} 𝒜] (A B : 𝒜) (f : A ⟶ B) :
    𝟙 A ≫ f = f ∧ f ≫ 𝟙 B = f :=
  ⟨Category.id_comp f, Category.comp_id f⟩

/-! ## Definition 1.1.4 (Isomorphism)

A map `f : A ⟶ B` in `𝒜` is an *isomorphism* if there exists `g : B ⟶ A` such
that `g ∘ f = 1_A` and `f ∘ g = 1_B`. Mathlib packages this data as `Iso`; the
propositional version is `CategoryTheory.IsIso`.
-/

/-- Leinster's definition, unpacked as a proposition.
Translating Leinster's `gf = 1_A` and `fg = 1_B` into Mathlib's left-to-right
composition gives `f ≫ g = 𝟙 A` and `g ≫ f = 𝟙 B`. -/
def IsIsomorphism {𝒜 : Type u} [Category.{v} 𝒜] {A B : 𝒜} (f : A ⟶ B) : Prop :=
  ∃ g : B ⟶ A, f ≫ g = 𝟙 A ∧ g ≫ f = 𝟙 B

/-! ## Exercise 1.1.13

"Show that a map in a category can have at most one inverse." -/

theorem inverse_unique {𝒜 : Type u} [Category.{v} 𝒜] {A B : 𝒜} (f : A ⟶ B)
    (g g' : B ⟶ A)
    (hg : f ≫ g = 𝟙 A ∧ g ≫ f = 𝟙 B)
    (hg' : f ≫ g' = 𝟙 A ∧ g' ≫ f = 𝟙 B) :
    g = g' := by
  -- g = 1_B ≫ g = (g' ≫ f) ≫ g = g' ≫ (f ≫ g) = g' ≫ 𝟙 A = g'.
  calc g = 𝟙 B ≫ g           := by rw [Category.id_comp]
    _ = (g' ≫ f) ≫ g         := by rw [hg'.2]
    _ = g' ≫ (f ≫ g)         := by rw [Category.assoc]
    _ = g' ≫ 𝟙 A             := by rw [hg.1]
    _ = g'                    := by rw [Category.comp_id]

/-! ## Example 1.1.8(d) — Monoids as one-object categories

"A category with one object is essentially the same thing as a monoid."

Mathlib's `SingleObj M` takes a monoid `M` and produces the corresponding one-object
category. We check that its hom-type at the unique object is defeq to the monoid.
-/

example (M : Type u) [Monoid M] :
    (SingleObj.star M ⟶ SingleObj.star M) = M := rfl

/-! ## Example 1.1.8(e) — Preorders as categories

"A preordered set `(S, ≤)` can be regarded as a category in which, for each
`A, B ∈ S`, there is at most one map from `A` to `B`, present iff `A ≤ B`."
Mathlib provides this via the `Preorder`-induced `Category` instance.
-/

example (S : Type u) [Preorder S] (x y : S) :
    Subsingleton (x ⟶ y) := inferInstance

example (S : Type u) [Preorder S] (x y : S) (f : x ⟶ y) :
    x ≤ y := f.le

/-! ## Construction 1.1.9 (Opposite category)

Mathlib's `Cᵒᵖ` gives this for any category `C`. The opposite of the opposite is
(canonically) the original category. -/

example (𝒜 : Type u) [Category.{v} 𝒜] : Category 𝒜ᵒᵖ := inferInstance

/-! ## Construction 1.1.11 (Product category)

Mathlib's `Prod` construction on categories gives `𝒜 × ℬ` with
`ob(𝒜 × ℬ) = ob(𝒜) × ob(ℬ)` and
`(𝒜 × ℬ)((A,B), (A',B')) = 𝒜(A,A') × ℬ(B,B')`. -/

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ] :
    Category (𝒜 × ℬ) := inferInstance

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (A A' : 𝒜) (B B' : ℬ) :
    ((A, B) ⟶ (A', B')) = ((A ⟶ A') × (B ⟶ B')) := rfl

end LeinsterCh1
