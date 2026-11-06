module

public import RestrictedPolynomials.Dimitrov.Mod4
public import RestrictedPolynomials.Dimitrov.SqrtSeries

/-!
# [Dim19, Prop squarerad], "in particular" clause

Source: arXiv:1912.12545v1 `main.tex`, Prop `squarerad`, l. 224-245. For `P(0) = 1` the
product `graeffe P * graeffe (graeffe P)` has constant term `1` and is a square mod `4`
(by Lemma mod4), hence has a square root in `1 + Xℤ[[X]]`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

private lemma graeffe_coeff_zero (P : ℤ[X]) : (graeffe P).coeff 0 = P.coeff 0 ^ 2 := by
  simp [graeffe, pow_two, mul_coeff_zero, coeff_contract]

/-- [Dim19, Prop squarerad], "in particular" clause: for `P ∈ ℤ[X]` with `P(0) = 1`,
`√(P_2 P_4) ∈ ℤ[[X]]`, where for such `P` the ancillary polynomials `∏(1 − α_i^m X)` are the
unsigned `graeffe`. -/
theorem squarerad_graeffe (P : ℤ[X]) (h0 : P.coeff 0 = 1) :
    ∃ f : PowerSeries ℤ, PowerSeries.constantCoeff f = 1 ∧
      f ^ 2 = ((graeffe P * graeffe (graeffe P) : ℤ[X]) : PowerSeries ℤ) := by
  have hg : (graeffe P).coeff 0 = 1 := by rw [graeffe_coeff_zero, h0]; norm_num
  have hgg : (graeffe (graeffe P)).coeff 0 = 1 := by rw [graeffe_coeff_zero, hg]; norm_num
  apply squarerad
  · rw [mul_coeff_zero, hg, hgg]; norm_num
  · refine ⟨(graeffe P).map (Int.castRingHom (ZMod 4)), ?_⟩
    have hmod : (graeffe (graeffe P)).map (Int.castRingHom (ZMod 4)) =
        (graeffe P).map (Int.castRingHom (ZMod 4)) := by
      ext k
      have h4 := graeffe_graeffe_sub_graeffe_coeff P k
      have h5 : ((graeffe (graeffe P)).coeff k : ZMod 4) = (graeffe P).coeff k := by
        rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa [coeff_sub] using h4
      simpa using h5
    rw [Polynomial.map_mul, hmod, pow_two]
