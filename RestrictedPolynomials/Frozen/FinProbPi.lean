module

public import RestrictedPolynomials.FinProb

/-!
# Frozen definition: the product measure `π^{⊗ι}`

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

namespace FinProb

variable {α : Type*} [Fintype α]

/-- The product measure `π^{⊗ι}` on `ι → α`. -/
def pi (π : FinProb α) (ι : Type*) [Fintype ι] [DecidableEq ι] : FinProb (ι → α) where
  prob x := ∏ i, π.prob (x i)
  nonneg _ := prod_nonneg fun i _ => π.nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum (fun _ a => π.prob a)]
    simp [π.sum_eq_one]

end FinProb

end RestrictedPolynomials

end
