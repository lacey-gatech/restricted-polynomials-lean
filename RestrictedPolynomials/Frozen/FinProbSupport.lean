module

public import RestrictedPolynomials.FinProb

/-!
# Frozen definition: the support of a distribution

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

namespace FinProb

variable {α : Type*} [Fintype α]

/-- The support `{a : π(a) ≠ 0}`. -/
def support (π : FinProb α) : Set α := {a | π.prob a ≠ 0}

end FinProb

end RestrictedPolynomials

end
