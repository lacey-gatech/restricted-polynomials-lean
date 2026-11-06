module

public import Mathlib.RingTheory.PowerSeries.Catalan
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic

/-!
# Integrality of square roots of power series

Source: Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on polynomials*
(arXiv:1912.12545v1 `main.tex`), display (2int) (l. 219-222) and Proposition `squarerad`
(l. 224-245).

* `exists_sqrt_one_add_four_mul_X`: `√(1 + 4Y) ∈ ℤ[[Y]]`, built from the Catalan generating
  function as `1 + 2Y c(−Y)`.
* `eq_of_sq_eq_of_constantCoeff`: uniqueness of the square root with constant term `1`.
* `squarerad`: if `Q(0) = 1` and `Q` is a square modulo `4`, then `√Q ∈ 1 + Xℤ[[X]]`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- [Dim19, (2int)]: `√(1 + 4Y)` has integer Taylor coefficients. -/
theorem exists_sqrt_one_add_four_mul_X :
    ∃ s : PowerSeries ℤ, PowerSeries.constantCoeff s = 1 ∧ s ^ 2 = 1 + 4 * PowerSeries.X := by
  set c : PowerSeries ℤ := PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries with hc
  have hc2 : c ^ 2 * PowerSeries.X + 1 = c := by
    have := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa [hc] using this
  set d : PowerSeries ℤ := PowerSeries.evalNegHom c with hd
  have hd2 : d ^ 2 * (-PowerSeries.X) + 1 = d := by
    have := congrArg PowerSeries.evalNegHom hc2
    simpa [hd, PowerSeries.evalNegHom_X] using this
  refine ⟨1 + 2 * PowerSeries.X * d, by simp, ?_⟩
  linear_combination (4 * PowerSeries.X) * hd2.symm

/-- Uniqueness of the square root with constant term 1 in `ℤ[[X]]`. -/
theorem eq_of_sq_eq_of_constantCoeff {f g : PowerSeries ℤ}
    (hf : PowerSeries.constantCoeff f = 1) (hg : PowerSeries.constantCoeff g = 1)
    (h : f ^ 2 = g ^ 2) : f = g := by
  have h1 : (f - g) * (f + g) = 0 := by linear_combination h
  have h2 : f + g ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [hf, hg] at this
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 h2

/-- Lifting step: `Q` is `U² + 4V` for integer polynomials `U`, `V` with `U(0) = 1`, `V(0) = 0`. -/
theorem exists_sq_add_four_mul (Q : ℤ[X]) (h0 : Q.coeff 0 = 1)
    (hsq : ∃ U : (ZMod 4)[X], Q.map (Int.castRingHom (ZMod 4)) = U ^ 2) :
    ∃ U V : ℤ[X], U.coeff 0 = 1 ∧ V.coeff 0 = 0 ∧ Q = U ^ 2 + 4 * V := by
  obtain ⟨U, hU⟩ := hsq
  obtain ⟨U0, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod 4))
    (ZMod.intCast_surjective) U
  -- congruence of Q and U0^2 modulo 4
  have hcong : ∀ i, (4 : ℤ) ∣ (Q - U0 ^ 2).coeff i := by
    intro i
    have h1 : (Q - U0 ^ 2).map (Int.castRingHom (ZMod 4)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, hU, sub_self]
    have h2 := congrArg (fun p => p.coeff i) h1
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h2
  -- the constant term of U0 is odd
  have hodd : (4 : ℤ) ∣ 1 - (U0.coeff 0) ^ 2 := by
    have := hcong 0
    simp only [coeff_sub, h0, Polynomial.coeff_zero_eq_eval_zero (p := U0 ^ 2), eval_pow,
      ← Polynomial.coeff_zero_eq_eval_zero] at this
    exact this
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 - U0.coeff 0 = 2 * k := by
    rcases Int.even_or_odd (U0.coeff 0) with ⟨m, hm⟩ | ⟨m, hm⟩
    · exfalso
      obtain ⟨r, hr⟩ := hodd
      have h4 : (U0.coeff 0) ^ 2 = 4 * (m * m) := by rw [hm]; ring
      generalize m * m = t at h4
      omega
    · exact ⟨-m, by omega⟩
  set U1 : ℤ[X] := U0 + C (2 * k) with hU1
  have hU1c : U1.coeff 0 = 1 := by simp [hU1]; omega
  have hid : Q - U1 ^ 2 = (Q - U0 ^ 2) - C 4 * (C k * U0 + C (k ^ 2)) := by
    rw [hU1]
    simp only [C_mul, C_pow, map_ofNat]
    ring
  have hdiv : C (4 : ℤ) ∣ Q - U1 ^ 2 := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [hid, coeff_sub, coeff_C_mul]
    exact dvd_sub (hcong i) (dvd_mul_right _ _)
  obtain ⟨V, hV⟩ := hdiv
  refine ⟨U1, V, hU1c, ?_, ?_⟩
  · have := congrArg (fun p => p.coeff 0) hV
    simp only [coeff_C_mul, coeff_sub, h0, Polynomial.coeff_zero_eq_eval_zero (p := U1 ^ 2),
      eval_pow, ← Polynomial.coeff_zero_eq_eval_zero, hU1c] at this
    omega
  · have : Q = U1 ^ 2 + C 4 * V := by rw [← hV]; ring
    rw [this, map_ofNat]

/-- [Dim19, Prop squarerad], first sentence: if `Q(0) = 1` and `Q mod 4` is a perfect square in
`(ℤ/4)[X]`, then `√Q ∈ 1 + Xℤ[[X]]`. -/
theorem squarerad (Q : ℤ[X]) (h0 : Q.coeff 0 = 1)
    (hsq : ∃ U : (ZMod 4)[X], Q.map (Int.castRingHom (ZMod 4)) = U ^ 2) :
    ∃ f : PowerSeries ℤ, PowerSeries.constantCoeff f = 1 ∧ f ^ 2 = (Q : PowerSeries ℤ) := by
  obtain ⟨U, V, hU, hV, hQ⟩ := exists_sq_add_four_mul Q h0 hsq
  obtain ⟨s, hs0, hs2⟩ := exists_sqrt_one_add_four_mul_X
  have hu0 : PowerSeries.constantCoeff (U : PowerSeries ℤ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hU]
  have hv0 : PowerSeries.constantCoeff (V : PowerSeries ℤ) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hV]
  obtain ⟨w, hw⟩ : ∃ w : PowerSeries ℤ, (U : PowerSeries ℤ) * w = 1 :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hu0]; exact isUnit_one)).exists_right_inv
  set a : PowerSeries ℤ := (V : PowerSeries ℤ) * w ^ 2 with ha_def
  have ha0 : PowerSeries.constantCoeff a = 0 := by simp [ha_def, hv0]
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  refine ⟨(U : PowerSeries ℤ) * PowerSeries.subst a s, ?_, ?_⟩
  · have h1 : PowerSeries.constantCoeff (PowerSeries.subst a s) = 1 := by
      have := PowerSeries.constantCoeff_subst_of_constantCoeff_zero ha0 s
      have h2 : MvPowerSeries.constantCoeff (PowerSeries.subst a s) = 1 := by
        simpa [hs0] using this
      exact h2
    rw [map_mul, hu0, h1, mul_one]
  · have hsub : (PowerSeries.subst a s) ^ 2 = 1 + 4 * a := by
      rw [← PowerSeries.subst_pow ha, hs2, ← PowerSeries.coe_substAlgHom ha]
      simp only [map_add, map_mul, map_one, map_ofNat, PowerSeries.substAlgHom_X ha]
    have hQ' : (Q : PowerSeries ℤ) = (U : PowerSeries ℤ) ^ 2 + 4 * (V : PowerSeries ℤ) := by
      have h4 : ((4 : ℤ[X]) : PowerSeries ℤ) = 4 := map_ofNat Polynomial.coeToPowerSeries.ringHom 4
      rw [hQ, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_mul, h4]
    rw [hQ', mul_pow, hsub, ha_def]
    linear_combination (4 * (V : PowerSeries ℤ) * ((U : PowerSeries ℤ) * w + 1)) * hw

end RestrictedPolynomials
