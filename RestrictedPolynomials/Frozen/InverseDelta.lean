module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Frozen definition: the parameter `δ` of the inverse theorem

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- The parameter `δ = exp(-exp^{(k^{C₀ k})}(ε^{-b}))` of the inverse theorem. -/
def inverseDelta (C₀ k : ℕ) (b ε : ℝ) : ℝ :=
  Real.exp (-(Real.exp^[k ^ (C₀ * k)] (ε ^ (-b))))

end RestrictedPolynomials

end
