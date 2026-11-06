-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import RestrictedPolynomials.Providers.Dimitrov

/-!
# Frozen statement: Dimitrov's theorem (Theorem 5.11, [Dim19, Theorem 1])

The statement was fixed and approved by the author before any proof work, and has not changed
since. The proof is `RestrictedPolynomials.Providers.dimitrov`, built in
`RestrictedPolynomials/Dimitrov/`. The paper uses the theorem only for the explicit bounds on
`M_k` and `P_k`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- **Theorem 5.11** ([Dim19, Theorem 1]). If `Q ∈ ℤ[z]` is monic and irreducible of degree
`d > 1` and is not cyclotomic, then some complex root `β` of `Q` has `|β| ≥ 2^{1/(4d)}`. -/
theorem dimitrov (Q : ℤ[X]) (hmon : Q.Monic) (hirr : Irreducible Q) (hdeg : 1 < Q.natDegree)
    (hcyc : ∀ n : ℕ, 0 < n → Q ≠ cyclotomic n ℤ) :
    ∃ β : ℂ, aeval β Q = 0 ∧ (2 : ℝ) ^ (1 / (4 * (Q.natDegree : ℝ))) ≤ ‖β‖ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact RestrictedPolynomials.Providers.dimitrov
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end RestrictedPolynomials

end
-- FROZEN_ANCHOR_SUFFIX_END
