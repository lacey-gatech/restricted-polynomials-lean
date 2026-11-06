module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.Norm

/-!
# Case B of the proof of Dimitrov's theorem: `P = R(X²)`

[Dim19, Theorem 1], end of the proof (arXiv:1912.12545v1 `main.tex`, l. 788-795): if `P_2`
is reducible then `P` is even, `P = R(X²)`, and one passes from `P` to `R` and concludes by
induction on the degree. This covers the steps of [Dim19]'s proof of Theorem 1 in which `P_2` is
reducible: halving the degree, the reduced polynomial is not cyclotomic, the base case of degree
two, the induction step for the root norm, and the case assembly.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

lemma isUnit_of_isUnit_expand_two {a : ℤ[X]} (h : IsUnit (expand ℤ 2 a)) : IsUnit a := by
  obtain ⟨r, hr, hC⟩ := Polynomial.isUnit_iff.mp h
  have : a = C r := (expand_eq_C (by norm_num)).mp hC.symm
  rw [this]; exact hr.map C

lemma not_isUnit_cyclotomic (n : ℕ) (hn : 0 < n) : ¬ IsUnit (cyclotomic n ℤ) := by
  intro h
  have h1 : cyclotomic n ℤ = 1 := (cyclotomic.monic n ℤ).isUnit_iff.mp h
  have := natDegree_cyclotomic n ℤ
  rw [h1, natDegree_one] at this
  exact (Nat.totient_pos.mpr hn).ne this

/-- [Dim19], proof of Theorem 1, case `P_2` reducible: halving the degree, in even form: if
`P = R(X²)` is monic, irreducible, of degree > 1 and not cyclotomic, then so is `R` (except for the
degree), and `2 deg R = deg P`. -/
theorem caseB_reduction (P R : ℤ[X]) (hPR : P = expand ℤ 2 R) (hmon : P.Monic)
    (hirr : Irreducible P) (hdeg : 1 < P.natDegree) (hcyc : ∀ n : ℕ, 0 < n → P ≠ cyclotomic n ℤ) :
    R.Monic ∧ Irreducible R ∧ 2 * R.natDegree = P.natDegree ∧
      (∀ n : ℕ, 0 < n → R ≠ cyclotomic n ℤ) := by
  have _ := hdeg
  subst hPR
  refine ⟨(monic_expand_iff (by norm_num)).mp hmon, ?_, ?_, ?_⟩
  · refine ⟨fun hu => hirr.not_isUnit (hu.map (expand ℤ 2)), fun a b hab => ?_⟩
    have h := hirr.isUnit_or_isUnit (a := expand ℤ 2 a) (b := expand ℤ 2 b)
      (by rw [← map_mul, ← hab])
    exact h.imp isUnit_of_isUnit_expand_two isUnit_of_isUnit_expand_two
  · rw [natDegree_expand]; ring
  · intro n hn hRn
    subst hRn
    by_cases h2 : 2 ∣ n
    · exact hcyc (n * 2) (by positivity) (cyclotomic_expand_eq_cyclotomic Nat.prime_two h2 ℤ)
    · rw [cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two h2] at hirr
      rcases hirr.isUnit_or_isUnit rfl with h | h
      · exact not_isUnit_cyclotomic _ (by positivity) h
      · exact not_isUnit_cyclotomic _ hn h

/-- [Dim19], proof of Theorem 1, induction step: a root `γ` of `R` with the bound in degree `deg R` gives a
root `β = √γ` of `P = R(X²)` with the bound in degree `deg P = 2 deg R`. -/
theorem caseB_step (P R : ℤ[X]) (hPR : P = expand ℤ 2 R) (γ : ℂ) (hγ : aeval γ R = 0)
    (hbd : (2 : ℝ) ^ (1 / (4 * (R.natDegree : ℝ))) ≤ ‖γ‖) :
    ∃ β : ℂ, aeval β P = 0 ∧ (2 : ℝ) ^ (1 / (4 * (P.natDegree : ℝ))) ≤ ‖β‖ := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq γ (n := 2) (by norm_num)
  refine ⟨β, ?_, ?_⟩
  · rw [hPR, expand_aeval, hβ, hγ]
  · have hd : (P.natDegree : ℝ) = 2 * R.natDegree := by
      rw [hPR, natDegree_expand]; push_cast; ring
    have hexp : 1 / (4 * (P.natDegree : ℝ)) = (1 / (4 * (R.natDegree : ℝ))) / 2 := by
      rw [hd]; by_cases h : (R.natDegree : ℝ) = 0
      · simp [h]
      · field_simp
    rw [hexp]
    have hnorm : ‖γ‖ = ‖β‖ ^ 2 := by rw [← hβ, norm_pow]
    have h2 : ((2 : ℝ) ^ ((1 / (4 * (R.natDegree : ℝ))) / 2)) ^ 2 ≤ ‖β‖ ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      push_cast
      rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ← hnorm]
      exact hbd
    exact le_of_sq_le_sq h2 (norm_nonneg β)

/-- [Dim19], proof of Theorem 1, base case: `deg R = 1`, so `P = X² + r` with `|r| ≥ 2`. -/
theorem caseB_base (P R : ℤ[X]) (hPR : P = expand ℤ 2 R) (hmon : P.Monic) (hirr : Irreducible P)
    (hcyc : ∀ n : ℕ, 0 < n → P ≠ cyclotomic n ℤ) (hR : R.natDegree = 1) :
    ∃ β : ℂ, aeval β P = 0 ∧ (2 : ℝ) ^ (1 / (4 * (P.natDegree : ℝ))) ≤ ‖β‖ := by
  have hRm : R.Monic := (monic_expand_iff (by norm_num)).mp (hPR ▸ hmon)
  have hRe : R = X + C (R.coeff 0) := hRm.eq_X_add_C hR
  generalize R.coeff 0 = r at hRe
  have hP : P = X ^ 2 + C r := by rw [hPR, hRe]; simp
  have hdeg : P.natDegree = 2 := by rw [hPR, natDegree_expand, hR]
  have hroot : ∀ x : ℤ, x ^ 2 + r = 0 → False := fun x hx => by
    have := degree_eq_one_of_irreducible_of_root hirr (x := x) (by simp [hP, hx])
    rw [degree_eq_natDegree hirr.ne_zero, hdeg] at this
    norm_num at this
  have h0 : r ≠ 0 := fun h => hroot 0 (by simp [h])
  have h1 : r ≠ -1 := fun h => hroot 1 (by simp [h])
  have h2 : r ≠ 1 := by
    intro h
    refine hcyc 4 (by norm_num) ?_
    have := cyclotomic_expand_eq_cyclotomic (p := 2) (n := 2) Nat.prime_two (dvd_refl 2) ℤ
    rw [cyclotomic_two] at this
    rw [hP, h]; simpa using this
  have hr : 2 ≤ |r| := by
    by_contra hlt
    rw [not_le] at hlt
    have := abs_lt.mp (by omega : |r| < 2)
    omega
  have hrC : (2 : ℝ) ≤ ‖((-r : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast, Int.cast_neg, abs_neg]; exact_mod_cast hr
  refine caseB_step P R hPR ((-r : ℤ) : ℂ) (by simp [hRe]) ?_
  rw [hR]
  calc (2 : ℝ) ^ (1 / (4 * ((1 : ℕ) : ℝ))) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := by simp
    _ ≤ _ := hrC

/-- [Dim19], proof of Theorem 1, case `P_2` reducible: Case B, conditional on the theorem in every smaller degree (the
strong-induction hypothesis `ih`, discharged in the assembly). -/
theorem dimitrov_caseB (P R : ℤ[X]) (hPR : P = expand ℤ 2 R) (hmon : P.Monic)
    (hirr : Irreducible P) (hdeg : 1 < P.natDegree) (hcyc : ∀ n : ℕ, 0 < n → P ≠ cyclotomic n ℤ)
    (ih : ∀ Q : ℤ[X], Q.natDegree < P.natDegree → Q.Monic → Irreducible Q → 1 < Q.natDegree →
      (∀ n : ℕ, 0 < n → Q ≠ cyclotomic n ℤ) →
      ∃ β : ℂ, aeval β Q = 0 ∧ (2 : ℝ) ^ (1 / (4 * (Q.natDegree : ℝ))) ≤ ‖β‖) :
    ∃ β : ℂ, aeval β P = 0 ∧ (2 : ℝ) ^ (1 / (4 * (P.natDegree : ℝ))) ≤ ‖β‖ := by
  obtain ⟨hRm, hRi, hRd, hRc⟩ := caseB_reduction P R hPR hmon hirr hdeg hcyc
  by_cases h1 : R.natDegree = 1
  · exact caseB_base P R hPR hmon hirr hcyc h1
  · obtain ⟨γ, hγ, hbd⟩ := ih R (by omega) hRm hRi (by omega) hRc
    exact caseB_step P R hPR γ hγ hbd

end RestrictedPolynomials
