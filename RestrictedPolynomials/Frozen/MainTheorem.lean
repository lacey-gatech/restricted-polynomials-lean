module

public import RestrictedPolynomials.Frozen.StepSet
public import RestrictedPolynomials.Frozen.PolyTerm
public import RestrictedPolynomials.Frozen.HasRestrictedProgression

/-!
# Frozen definition: Theorem 1.1 as a proposition

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- **Theorem 1.1**, as a proposition. There is an absolute constant `C₁` (so `K = k^{C₁ k}` is
`k^{O(k)}`) such that for every `k ≥ 2` there are `M = M_k` and `P = P_k`, with
`M_k ≤ exp(7 k log k) = exp(O(k log k))` and `P_k ≤ exp exp(25 k² log k) = exp exp(O(k² log k))`
(the quantitative proof of Proposition 5.1, which uses Dimitrov's theorem), with the following
property. For every prime `p ≥ P`, the `k` points `x, x + P_1(y), …, x + P_{k-1}(y)` of any
restricted progression with `y ∈ {0, 2, 3, …, M}^n \ {0}` are pairwise distinct, and there are
`C, c > 0` such that if `n > exp^{(K)}(1)` and `A ⊆ 𝔽_p^n` has density at least
`C / (log^{(K)} n)^c`, then `A` contains such a progression. -/
def MainTheorem : Prop :=
  ∃ C₁ : ℕ, ∀ k : ℕ, 2 ≤ k → ∃ M P : ℕ,
    (M : ℝ) ≤ Real.exp (7 * k * Real.log k) ∧
    (P : ℝ) ≤ Real.exp (Real.exp (25 * k ^ 2 * Real.log k)) ∧
    ∀ p : ℕ, p.Prime → P ≤ p →
      (∀ (n : ℕ) (x y : Fin n → ZMod p), (∀ i, ∃ t ∈ stepSet M, y i = t) → y ≠ 0 →
        Function.Injective fun j : Fin k => x + polyTerm j y) ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, Real.exp^[k ^ (C₁ * k)] 1 < n →
        ∀ A : Finset (Fin n → ZMod p),
          C / (Real.log^[k ^ (C₁ * k)] n) ^ c ≤ (A.card : ℝ) / (p : ℝ) ^ n →
          HasRestrictedProgression p M k (A : Set (Fin n → ZMod p))

end RestrictedPolynomials

end
