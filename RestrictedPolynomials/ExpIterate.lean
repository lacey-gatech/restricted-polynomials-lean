module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Iterated exponentials

Monotonicity of `exp^{(j)} y` in `y` and in the number of iterates `j`.
-/

@[expose] public section

noncomputable section

namespace RestrictedPolynomials

lemma le_exp_iterate (j : ℕ) (y : ℝ) : y ≤ Real.exp^[j] y := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact le_trans (by linarith [Real.add_one_le_exp y]) (ih (Real.exp y))

lemma exp_iterate_mono (j : ℕ) : Monotone (Real.exp^[j]) := Real.exp_monotone.iterate j

lemma exp_iterate_le_succ (j : ℕ) (y : ℝ) : Real.exp^[j] y ≤ Real.exp^[j + 1] y := by
  rw [Function.iterate_succ_apply]
  exact exp_iterate_mono j (by linarith [Real.add_one_le_exp y])

lemma exp_iterate_le_of_le {j j' : ℕ} (h : j ≤ j') (y : ℝ) : Real.exp^[j] y ≤ Real.exp^[j'] y := by
  induction j', h using Nat.le_induction with
  | base => rfl
  | succ j' _ ih => exact ih.trans (exp_iterate_le_succ j' y)

lemma exp_iterate_lt_of_lt {j j' : ℕ} (h : j < j') (y : ℝ) :
    Real.exp^[j] y < Real.exp^[j'] y := by
  have h1 : Real.exp^[j] y < Real.exp^[j + 1] y := by
    rw [Function.iterate_succ_apply]
    exact (Real.exp_strictMono.iterate j) (by linarith [Real.add_one_le_exp y])
  exact h1.trans_le (exp_iterate_le_of_le h y)

end RestrictedPolynomials

end
