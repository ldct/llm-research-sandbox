import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Chapter 1, Section 1.3 — Natural transformations
-/

open CategoryTheory

universe v v₁ v₂ u u₁ u₂

namespace LeinsterCh1

/-! ## Definition 1.3.1 (Natural transformation)

Given functors `F, G : 𝒜 ⥤ ℬ`, a natural transformation `α : F ⟶ G` is a family
`α_A : F A ⟶ G A`, indexed by `A ∈ 𝒜`, such that for every `f : A ⟶ A'` in `𝒜`,

  `F(f) ≫ α_{A'} = α_A ≫ G(f)`.

This is Mathlib's `NatTrans`. -/

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F G : 𝒜 ⥤ ℬ) (α : F ⟶ G) {A A' : 𝒜} (f : A ⟶ A') :
    F.map f ≫ α.app A' = α.app A ≫ G.map f := α.naturality f

/-! ## Construction 1.3.6 (Vertical composition, functor category)

"Given `α : F ⟶ G` and `β : G ⟶ H`, there is a composite `β ∘ α : F ⟶ H`
defined componentwise by `(β ∘ α)_A = β_A ∘ α_A`. There is also an identity
natural transformation `1_F : F ⟶ F`. Hence for any `𝒜, ℬ` the functors
`𝒜 ⥤ ℬ` together with natural transformations form a category — the
*functor category* `[𝒜, ℬ]`." -/

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ] :
    Category (𝒜 ⥤ ℬ) := inferInstance

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F G H : 𝒜 ⥤ ℬ) (α : F ⟶ G) (β : G ⟶ H) (A : 𝒜) :
    (α ≫ β).app A = α.app A ≫ β.app A := rfl

example (𝒜 : Type u₁) [Category.{v₁} 𝒜] (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F : 𝒜 ⥤ ℬ) (A : 𝒜) :
    (𝟙 F : F ⟶ F).app A = 𝟙 (F.obj A) := rfl

/-! ## Example 1.3.3 — Natural transformations out of a discrete category

"If `𝒜` is discrete, a natural transformation `F ⟶ G` is just a family of maps
indexed by `ob(𝒜)`; the naturality axiom is automatic from the identity maps."

We formalize this on the canonical discrete category `Discrete I`. -/

example (I : Type u) (ℬ : Type u₂) [Category.{v₂} ℬ]
    (F G : Discrete I ⥤ ℬ) (f : ∀ i : I, F.obj ⟨i⟩ ⟶ G.obj ⟨i⟩) : F ⟶ G :=
  Discrete.natTrans (fun ⟨i⟩ => f i)

end LeinsterCh1
