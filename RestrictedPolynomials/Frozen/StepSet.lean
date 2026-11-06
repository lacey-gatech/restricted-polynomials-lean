module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Frozen definition: the step set `Y`

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- The step set `Y = {0, 2, 3, …, M}`. -/
def stepSet (M : ℕ) : Finset ℕ := insert 0 (Icc 2 M)

end RestrictedPolynomials

end
