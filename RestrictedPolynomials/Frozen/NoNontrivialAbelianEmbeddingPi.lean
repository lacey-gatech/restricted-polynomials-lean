module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Frozen definition: no nontrivial abelian embedding (Definition 1.3)

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- Definition 1.3 for a product `∏ᵢ Aᵢ` of possibly different alphabets: every abelian
embedding of `S` into every abelian group is trivial, i.e. if maps `σᵢ : Aᵢ → G` satisfy
`∑ᵢ σᵢ(aᵢ) = 0` for every `a ∈ S`, then every `σᵢ` is constant. -/
def NoNontrivialAbelianEmbeddingPi {k : ℕ} {A : Fin k → Type*} (S : Set (∀ i, A i)) : Prop :=
  ∀ (G : Type) [AddCommGroup G] (σ : ∀ i, A i → G), (∀ a ∈ S, ∑ i, σ i (a i) = 0) →
    ∀ i (x y : A i), σ i x = σ i y

end RestrictedPolynomials

end
