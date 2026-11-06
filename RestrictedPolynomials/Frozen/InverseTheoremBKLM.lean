-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbSupport
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.InverseDelta
public import RestrictedPolynomials.Providers.InverseTheoremBKLM
public import Mathlib.Analysis.Complex.Order

/-!
# Frozen statement: Theorem 1.4 ([CSP_7, Theorem 1])

The statement was fixed and approved by the author before any proof work, and has not changed
since. The proof is `RestrictedPolynomials.Providers.inverse_theorem_bklm`, built in
`RestrictedPolynomials/TrackB/`.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

open scoped ComplexOrder in
/-- **Theorem 1.4** ([CSP_7, Theorem 1]). There is an absolute `C₀` such that for every `k` and
every `γ > 0` there is `b > 0` (the paper's `O_γ(1)`, which may depend on `k`) such
that for every `ε > 0` there is `n₀` with the following property. Let `μ` be a distribution on
`∏ᵢ A i` (finite alphabets) that admits no nontrivial abelian embedding and whose atoms all have
mass `≥ γ`. If `n₀ ≤ |ι|` and `1`-bounded `fᵢ : (ι → A i) → ℂ` satisfy
`|𝔼_{μ^{⊗ι}} ∏ᵢ fᵢ(xᵢ)| ≥ ε`, then `Stab_{1-δ}(fᵢ) ≥ δ` for every `i`, stability being taken
with respect to the marginal `μᵢ`, where `δ = exp(-exp^{(k^{C₀ k})}(ε^{-b}))`. The conclusion is
`≥` as in CSP_7 (the paper prints `>`). The inequality is in `ComplexOrder`: it says
`δ ≤ Re Stab` and `Im Stab = 0`, and the latter holds for every real `ρ`. -/
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact RestrictedPolynomials.Providers.inverse_theorem_bklm
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end RestrictedPolynomials

end
-- FROZEN_ANCHOR_SUFFIX_END
