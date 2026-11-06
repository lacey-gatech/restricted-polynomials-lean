module

public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbSupport
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.InverseDelta
public import RestrictedPolynomials.TrackB.FinalAssembly
public import Mathlib.Analysis.Complex.Order

/-!
# Proof of the frozen statement `inverse_theorem_bklm`

This module proves the frozen statement `RestrictedPolynomials.inverse_theorem_bklm` (Theorem 1.4 =
[CSP_7, Theorem 1]). The frozen file `RestrictedPolynomials/Frozen/InverseTheoremBKLM.lean` proves its
statement by `by exact RestrictedPolynomials.Providers.inverse_theorem_bklm`.

The proof is the Track B final assembly `RestrictedPolynomials.TrackB.trackB_inverse_theorem_bklm`
(`RestrictedPolynomials/TrackB/FinalAssembly.lean`): the K7 recursion `k7_inverse_theorem_bklm_of_Q`
applied to `Q` on every pattern of `𝒯`, which is proved by the maximality induction from the merge
lemma, Theorem 6.5′ and Theorem 7.14′. The statement is closed (no hypotheses, so no auto-params as in
`Providers.dimitrov`).
-/

@[expose] public section

open Finset

namespace RestrictedPolynomials.Providers

open scoped ComplexOrder in
/-- **Theorem 1.4** ([CSP_7, Theorem 1]), the statement of the frozen statement
`RestrictedPolynomials.inverse_theorem_bklm`, proved by `TrackB.trackB_inverse_theorem_bklm`. -/
theorem inverse_theorem_bklm :
    ∃ C₀ : ℕ, ∀ k : ℕ, ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)),
        NoNontrivialAbelianEmbeddingPi μ.support → (∀ a ∈ μ.support, γ ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], n₀ ≤ Fintype.card ι →
        ∀ f : ∀ i, (ι → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, (inverseDelta C₀ k b ε : ℂ) ≤
            cstab (μ.marginalPi i) (1 - inverseDelta C₀ k b ε) (f i) :=
  TrackB.trackB_inverse_theorem_bklm

end RestrictedPolynomials.Providers
