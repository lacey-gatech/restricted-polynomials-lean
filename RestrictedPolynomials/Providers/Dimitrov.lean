module

public import RestrictedPolynomials.Dimitrov.CaseAGlue
public import RestrictedPolynomials.Dimitrov.Polya
public import RestrictedPolynomials.Dimitrov.Dubinin

/-!
# Proof of the frozen statement `dimitrov`

This module proves the frozen statement `RestrictedPolynomials.dimitrov` (Theorem 5.11 = [Dim19,
Theorem 1]). The frozen file `RestrictedPolynomials/Frozen/Dimitrov.lean` proves its statement by
`by exact RestrictedPolynomials.Providers.dimitrov`.

The proof assembles `dimitrov_of_rational_and_dubinin` (the Case A glue together with the reduction to
Case A) with its two analytic inputs:
- `rational_of_transfiniteDiameter_lt_one`, Supplement B, the Pólya–Kronecker rationality for hedgehogs;
- `transfiniteDiameter_hedgehog_le`, Supplement C, Dubinin's bound.

The hypotheses are auto-params (`by assumption`), so
that the frozen proof body is the bare `by exact` of this theorem.
-/

@[expose] public section

open Polynomial

namespace RestrictedPolynomials.Providers

/-- Dimitrov's theorem: a monic irreducible non-cyclotomic `Q ∈ ℤ[X]` of degree `d > 1` has a complex
root `β` with `|β| ≥ 2^{1/(4d)}`. -/
theorem dimitrov {Q : ℤ[X]} (hmon : Q.Monic := by assumption) (hirr : Irreducible Q := by assumption)
    (hdeg : 1 < Q.natDegree := by assumption)
    (hcyc : ∀ n : ℕ, 0 < n → Q ≠ cyclotomic n ℤ := by assumption) :
    ∃ β : ℂ, aeval β Q = 0 ∧ (2 : ℝ) ^ (1 / (4 * (Q.natDegree : ℝ))) ≤ ‖β‖ :=
  dimitrov_of_rational_and_dubinin
    (fun V hV hd a F _ρ₀ hρ hFd hF => rational_of_transfiniteDiameter_lt_one V hV hd a F hρ hFd hF)
    (fun V hV _R hR => transfiniteDiameter_hedgehog_le V hV hR) Q hmon hirr hdeg hcyc

end RestrictedPolynomials.Providers
