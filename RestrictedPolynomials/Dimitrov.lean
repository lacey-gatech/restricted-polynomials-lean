import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Dimitrov's theorem (Theorem 5.11 of the paper) — ADMITTED

[Dim19, Theorem 1]: V. Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on polynomials*.
If `Q ∈ ℤ[z]` is monic and irreducible of degree `d > 1` and is not cyclotomic, then
`max_{Q(β) = 0} |β| ≥ 2^{1/(4d)}`.

This is the **second and last** admitted statement of the formalization (after
`inverse_theorem`). It is used only in the quantitative proof of Proposition 5.1
(`RootsOfUnity.lean`, Lemma 5.12), which gives the explicit growth rates
`M(ℓ) = exp(O(ℓ log ℓ))`, `P(ℓ) = exp exp(O(ℓ² log ℓ))`.
-/

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- **Theorem 5.11** ([Dim19, Theorem 1]); admitted. -/
theorem dimitrov (Q : ℤ[X]) (hmon : Q.Monic) (hirr : Irreducible Q) (hdeg : 1 < Q.natDegree)
    (hcyc : ∀ n : ℕ, 0 < n → Q ≠ cyclotomic n ℤ) :
    ∃ β : ℂ, aeval β Q = 0 ∧ (2 : ℝ) ^ (1 / (4 * (Q.natDegree : ℝ))) ≤ ‖β‖ := by
  admit

end RestrictedPolynomials

end
