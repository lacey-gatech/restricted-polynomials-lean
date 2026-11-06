module

public import RestrictedPolynomials.FinProb

/-!
# Frozen definition: the one-coordinate noise kernel

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The one-coordinate `ρ`-correlated kernel: `y = x` with probability `ρ`, and otherwise
`y ∼ π` independently of `x`. -/
def noiseKernel (π : FinProb α) (ρ : ℝ) (a b : α) : ℝ :=
  ρ * (if a = b then 1 else 0) + (1 - ρ) * π.prob b

end RestrictedPolynomials

end
