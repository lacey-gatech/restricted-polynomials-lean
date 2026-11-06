module

public import RestrictedPolynomials.FinProb

/-!
# Frozen definition: marginals of a product of alphabets

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

namespace FinProb

variable {α : Type*} [Fintype α]

/-- The marginal of a distribution on a product `∏ᵢ Aᵢ` of alphabets on its `j`-th factor. -/
def marginalPi {k : ℕ} {A : Fin k → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (μ : FinProb (∀ i, A i)) (j : Fin k) : FinProb (A j) where
  prob a := ∑ t with t j = a, μ.prob t
  nonneg _ := sum_nonneg fun t _ => μ.nonneg t
  sum_eq_one := by
    rw [← μ.sum_eq_one, ← sum_fiberwise univ (fun t => t j) μ.prob]

end FinProb

end RestrictedPolynomials

end
