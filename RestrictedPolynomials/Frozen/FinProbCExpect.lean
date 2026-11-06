module

public import RestrictedPolynomials.FinProb

/-!
# Frozen definition: complex expectation

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

namespace FinProb

variable {α : Type*} [Fintype α]

/-- `𝔼_π f = ∑ₓ π(x) f(x)` for a complex-valued `f`. -/
def cexpect (π : FinProb α) (f : α → ℂ) : ℂ := ∑ a, (π.prob a : ℂ) * f a

end FinProb

end RestrictedPolynomials

end
