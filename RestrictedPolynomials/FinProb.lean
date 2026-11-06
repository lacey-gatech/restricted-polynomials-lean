module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Finite probability distributions

`FinProb α` is a probability distribution on a finite set `α`. This structure is part of the meaning
of the frozen statements; like them, it was fixed before any proof work and has not changed since.
-/

@[expose] public section

noncomputable section

namespace RestrictedPolynomials

/-- A probability distribution on a finite set. -/
structure FinProb (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

end RestrictedPolynomials

end
