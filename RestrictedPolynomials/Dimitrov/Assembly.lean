module

public import RestrictedPolynomials.Dimitrov.EvenSplit
public import RestrictedPolynomials.Dimitrov.CaseB

/-!
# Assembly: reduction of [Dim19, Theorem 1] to Case A

Source: [Dim19], end of the proof of Theorem 1 (l. 788-795).
Strong induction on the degree, with the case split `irreducible_P2_or_even` and Case B from
`dimitrov_caseB`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- Reduction of [Dim19, Theorem 1] to its Case A (`P_2` irreducible), by strong induction on the
degree, with Case B from `dimitrov_caseB`. The hypothesis `hA` is Case A; it is discharged in
`CaseAGlue.lean` (`dimitrov_of_rational_and_dubinin`), which feeds `Providers.dimitrov`. -/
theorem dimitrov_of_caseA
    (hA : ∀ P : ℤ[X], P.Monic → Irreducible P → 1 < P.natDegree →
      (∀ n : ℕ, 0 < n → P ≠ cyclotomic n ℤ) → Irreducible (P2 P) →
      ∃ β : ℂ, aeval β P = 0 ∧ (2 : ℝ) ^ (1 / (4 * (P.natDegree : ℝ))) ≤ ‖β‖)
    (Q : ℤ[X]) (hmon : Q.Monic) (hirr : Irreducible Q) (hdeg : 1 < Q.natDegree)
    (hcyc : ∀ n : ℕ, 0 < n → Q ≠ cyclotomic n ℤ) :
    ∃ β : ℂ, aeval β Q = 0 ∧ (2 : ℝ) ^ (1 / (4 * (Q.natDegree : ℝ))) ≤ ‖β‖ := by
  induction h : Q.natDegree using Nat.strong_induction_on generalizing Q with
  | _ d ih =>
    subst h
    rcases irreducible_P2_or_even Q hmon hirr hdeg with h2 | ⟨R, hR⟩
    · exact hA Q hmon hirr hdeg hcyc h2
    · exact dimitrov_caseB Q R hR hmon hirr hdeg hcyc
        (fun Q' hlt hm hi hd hc => ih Q'.natDegree hlt Q' hm hi hd hc rfl)

end RestrictedPolynomials
