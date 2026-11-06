module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Frozen definition: the polynomial terms `P_j`

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- `P_j(y) = (y₁^j, …, y_n^j)` for `j ≥ 1`, and `P_0(y) = 0`, so that the progression
`x + P_0(y), …, x + P_{k-1}(y)` is `x, x + P_1(y), …, x + P_{k-1}(y)`. -/
def polyTerm {ι : Type*} {p : ℕ} (j : ℕ) (y : ι → ZMod p) : ι → ZMod p :=
  fun i => if j = 0 then 0 else y i ^ j

end RestrictedPolynomials

end
