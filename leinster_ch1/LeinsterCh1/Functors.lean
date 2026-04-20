import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.SingleObj

/-!
# Chapter 1, Section 1.2 — Functors
-/

open CategoryTheory

universe v v₁ v₂ u u₁ u₂

namespace LeinsterCh1

/-! ## Definition 1.2.1 (Functor)

A functor `F : 𝒜 → ℬ` consists of a function on objects and, for every pair
`A, A'`, a function `𝒜(A,A') → ℬ(F A, F A')`, preserving composition and
identities. This is Mathlib's `Functor` (or `⥤`) typeclass. -/

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F : 𝒜 ⥤ ℬ) (A A' A'' : 𝒜) (f : A ⟶ A') (f' : A' ⟶ A'') :
    F.map (f ≫ f') = F.map f ≫ F.map f' :=
  F.map_comp f f'

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F : 𝒜 ⥤ ℬ) (A : 𝒜) :
    F.map (𝟙 A) = 𝟙 (F.obj A) :=
  F.map_id A

/-! ## Exercise 1.2.21

"Show that functors preserve isomorphism: if `F : 𝒜 ⥤ ℬ` and `A ≅ A'` in `𝒜`,
then `F A ≅ F A'` in `ℬ`." -/

theorem functor_preserves_iso {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℬ : Type u₂} [Category.{v₂} ℬ] (F : 𝒜 ⥤ ℬ) {A A' : 𝒜}
    {f : A ⟶ A'} {g : A' ⟶ A} (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 A') :
    F.map f ≫ F.map g = 𝟙 (F.obj A) ∧ F.map g ≫ F.map f = 𝟙 (F.obj A') := by
  refine ⟨?_, ?_⟩
  · rw [← F.map_comp, hfg, F.map_id]
  · rw [← F.map_comp, hgf, F.map_id]

/-- Packaged version: the image of an iso is an iso. -/
def Functor.mapIso' {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℬ : Type u₂} [Category.{v₂} ℬ] (F : 𝒜 ⥤ ℬ) {A A' : 𝒜} (e : A ≅ A') :
    F.obj A ≅ F.obj A' := F.mapIso e

/-! ## Example 1.2.7 — Functors between one-object categories = monoid homs

"A functor `F : 𝒢 → ℋ` between one-object categories corresponding to monoids
`G` and `H` is just a monoid homomorphism `G → H`." -/

example (G H : Type u) [Monoid G] [Monoid H] (F : SingleObj G ⥤ SingleObj H) :
    F.map (𝟙 (SingleObj.star G)) = 𝟙 (F.obj (SingleObj.star G)) :=
  F.map_id _

/-- Build the functor `SingleObj G ⥤ SingleObj H` from a monoid hom. -/
def singleObjFunctor {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H) :
    SingleObj G ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map g := (φ g : SingleObj.star H ⟶ SingleObj.star H)
  map_id _ := φ.map_one
  map_comp g g' := φ.map_mul g' g
  -- In `SingleObj G`, the hom-type `star ⟶ star` is `G` with composition `g' * g`
  -- (Leinster's `F(g'g) = F(g')F(g)` in the other order due to left-to-right comp).

/-! ## Example 1.2.9 and Exercise 1.2.22 — Functors between preorders = monotone

"A functor between (pre)ordered sets (regarded as categories) is exactly an
order-preserving map." -/

/-- From a monotone map, build the corresponding functor. -/
def Monotone.toFunctor {S T : Type u} [Preorder S] [Preorder T] {f : S → T}
    (hf : Monotone f) : S ⥤ T where
  obj := f
  map h := (homOfLE (hf h.le))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Conversely, the object-part of a functor between preorders is monotone. -/
theorem functor_between_preorders_monotone {S T : Type u} [Preorder S] [Preorder T]
    (F : S ⥤ T) : Monotone F.obj := by
  intro x y hxy
  exact (F.map (homOfLE hxy)).le

/-! ## Definition 1.2.10 (Contravariant functor)

"A contravariant functor from `𝒜` to `ℬ` is a functor `𝒜ᵒᵖ ⥤ ℬ`." -/

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ] :
    (𝒜ᵒᵖ ⥤ ℬ) = (𝒜ᵒᵖ ⥤ ℬ) := rfl

/-! ## Definition 1.2.15 (Presheaf)

"A presheaf on `𝒜` is a functor `𝒜ᵒᵖ ⥤ Set`." -/

abbrev Presheaf (𝒜 : Type u₁) [Category.{v₁} 𝒜] : Type _ :=
  𝒜ᵒᵖ ⥤ Type v₁

/-! ## Definition 1.2.16 (Faithful, full)

A functor is *faithful* if every induced map on hom-sets is injective, and *full*
if every induced map is surjective. These are Mathlib's `Functor.Faithful` and
`Functor.Full`. -/

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Faithful] (A A' : 𝒜) (f g : A ⟶ A')
    (h : F.map f = F.map g) : f = g :=
  F.map_injective h

/-! ## Definition 1.2.18 (Subcategory)

We do not formalize subcategories as a structure here; rather we note that an
inclusion functor of a subcategory is always faithful, and full exactly when the
subcategory is full. Mathlib's analogue is `FullSubcategory` (for full ones). -/

end LeinsterCh1
