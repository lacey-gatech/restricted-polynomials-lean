module

public import RestrictedPolynomials.Dimitrov.Graeffe
public import Mathlib.FieldTheory.Finite.Basic

/-!
# [Dim19, Lemma mod4]: `P_4 ≡ P_2 (mod 4)`

Source: arXiv:1912.12545v1 `main.tex`, Lemma `mod4`, l. 183-216.

Instead of the symmetric-power argument of the source we use the identity
`graeffe P (X²) = P(X)·P(−X)`: first `graeffe P ≡ P (mod 2)` by Frobenius, so
`graeffe P = P + 2R`; then `graeffe (graeffe P) (X²) = (P + 2R)(X)(P + 2R)(−X) ≡ P(X)P(−X)
(mod 4)`, because the cross term `2(P(X)R(−X) + R(X)P(−X))` is `0 (mod 4)`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

private lemma C_two_dvd_of_map_eq_zero (S : ℤ[X])
    (h : S.map (Int.castRingHom (ZMod 2)) = 0) : (C 2 : ℤ[X]) ∣ S := by
  rw [C_dvd_iff_dvd_coeff]
  intro k
  have := congrArg (fun q => q.coeff k) h
  simp only [coeff_map, coeff_zero, eq_intCast] at this
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (S.coeff k) 2).mp this
  exact_mod_cast h2

/-- Over `ZMod 2`, `graeffe Q = Q` (Frobenius). -/
private lemma graeffe_eq_self_zmod_two (Q : (ZMod 2)[X]) : graeffe Q = Q := by
  have hF : (contract 2 Q) ^ 2 = expand (ZMod 2) 2 (contract 2 Q) :=
    (ZMod.expand_card _).symm
  have hG : (contract 2 Q.divX) ^ 2 = expand (ZMod 2) 2 (contract 2 Q.divX) :=
    (ZMod.expand_card _).symm
  unfold graeffe
  rw [hF, hG]
  conv_rhs => rw [graeffe_decomp Q]
  exact CharTwo.sub_eq_add _ _

private lemma graeffe_sub_self_dvd (P : ℤ[X]) : (C 2 : ℤ[X]) ∣ graeffe P - P := by
  apply C_two_dvd_of_map_eq_zero
  rw [Polynomial.map_sub, graeffe_map, graeffe_eq_self_zmod_two, sub_self]

private lemma cross_dvd (P R : ℤ[X]) :
    (C 2 : ℤ[X]) ∣ P * R.comp (-X) + R * P.comp (-X) := by
  apply C_two_dvd_of_map_eq_zero
  have hX : (-X : (ZMod 2)[X]) = X := CharTwo.neg_eq _
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_comp,
    Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hX, comp_X, comp_X, mul_comm,
    CharTwo.add_self_eq_zero]

/-- The unsigned congruence, valid for every integer polynomial. -/
theorem graeffe_graeffe_sub_graeffe_coeff (P : ℤ[X]) (k : ℕ) :
    (4 : ℤ) ∣ (graeffe (graeffe P) - graeffe P).coeff k := by
  obtain ⟨R, hR⟩ := graeffe_sub_self_dvd P
  have hG : graeffe P = P + C 2 * R := by linear_combination hR
  obtain ⟨T, hT⟩ := cross_dvd P R
  have h4 : (C 4 : ℤ[X]) = C 2 * C 2 := by rw [← C_mul]; norm_num
  have hkey : expand ℤ 2 (graeffe (graeffe P) - graeffe P) =
      C 4 * (T + R * R.comp (-X)) := by
    rw [map_sub, expand_graeffe, expand_graeffe, hG]
    simp only [add_comp, mul_comp, C_comp]
    linear_combination (C 2 : ℤ[X]) * hT - (T + R * R.comp (-X)) * h4
  have hd : (C 4 : ℤ[X]) ∣ expand ℤ 2 (graeffe (graeffe P) - graeffe P) :=
    ⟨_, hkey⟩
  rw [C_dvd_iff_dvd_coeff] at hd
  have := hd (2 * k)
  rwa [coeff_expand_mul' (by norm_num)] at this

/-- [Dim19, Lemma mod4] (Arnold, Smyth): `P_4 ≡ P_2 (mod 4ℤ[X])` for a monic integer polynomial. -/
theorem P4_sub_P2_coeff (P : ℤ[X]) (hP : P.Monic) (k : ℕ) : (4 : ℤ) ∣ (P4 P - P2 P).coeff k := by
  have _ := hP
  have h : P4 P - P2 P = (-1) ^ P.natDegree * (graeffe (graeffe P) - graeffe P) := by
    unfold P4 P2; ring
  rw [h]
  rcases neg_one_pow_eq_or ℤ[X] P.natDegree with h1 | h1
  · rw [h1, one_mul]
    exact graeffe_graeffe_sub_graeffe_coeff P k
  · rw [h1, neg_one_mul, coeff_neg, dvd_neg]
    exact graeffe_graeffe_sub_graeffe_coeff P k

end RestrictedPolynomials
