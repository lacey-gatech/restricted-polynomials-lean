module

public import RestrictedPolynomials.Frozen.StepSet
public import RestrictedPolynomials.Frozen.PolyTerm

/-!
# Frozen definition: restricted progressions in `A`

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- `A` contains a nontrivial restricted `k`-term polynomial progression
`x, x + P_1(y), …, x + P_{k-1}(y)` with `y ∈ Y^n \ {0}`, and its `k` points are pairwise
distinct. -/
def HasRestrictedProgression {ι : Type*} (p M k : ℕ) (A : Set (ι → ZMod p)) : Prop :=
  ∃ x y : ι → ZMod p, (∀ i, ∃ t ∈ stepSet M, y i = t) ∧ y ≠ 0 ∧
    (∀ j : Fin k, x + polyTerm j y ∈ A) ∧ Function.Injective fun j : Fin k => x + polyTerm j y

end RestrictedPolynomials

end
