module

public import RestrictedPolynomials.Dimitrov.Graeffe

/-!
# The case split of the proof of [Dim19, Theorem 1]

Source: arXiv:1912.12545v1 `main.tex`, end of the proof of Theorem 1 (l. 788-795). For a
monic irreducible integer polynomial `P` of degree `> 1`, either `P_2` is irreducible (Case A) or
`P` is even, `P = R(X²)` (Case B).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- `P_2` is monic for monic `P`. -/
theorem P2_monic (P : ℤ[X]) (hP : P.Monic) : (P2 P).Monic := by
  have h := map_P2 P hP
  have hm : (ancillary 2 P).Monic := sqRoots_monic _
  rw [← h] at hm
  exact monic_of_injective (Int.castRingHom ℂ).injective_int hm

theorem natDegree_P2 (P : ℤ[X]) (hP : P.Monic) : (P2 P).natDegree = P.natDegree := by
  have h := map_P2 P hP
  have hm : (P.map (Int.castRingHom ℂ)).Monic := hP.map _
  have hd : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
  have h1 : ancillary 2 P = sqRoots (P.map (Int.castRingHom ℂ)) := rfl
  have h3 := congrArg Polynomial.natDegree h
  rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int, h1, natDegree_sqRoots] at h3
  rw [h3, ← hd]
  exact splits_iff_card_roots.mp (IsAlgClosed.splits _)

private lemma comp_neg_X_expand (A : ℤ[X]) : (expand ℤ 2 A).comp (-X) = expand ℤ 2 A := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp

private lemma irreducible_comp_neg_X {P : ℤ[X]} (hirr : Irreducible P) :
    Irreducible (P.comp (-X)) := by
  have hinv : ∀ p : ℤ[X], (p.comp (-X)).comp (-X) = p := comp_neg_X_comp_neg_X
  refine ⟨fun hu => hirr.not_isUnit ?_, fun a b hab => ?_⟩
  · have := (compRingHom (-X : ℤ[X])).isUnit_map hu
    rwa [coe_compRingHom_apply, hinv] at this
  · have h2 : P = a.comp (-X) * b.comp (-X) := by
      rw [← mul_comp, ← hab, hinv]
    rcases hirr.isUnit_or_isUnit h2 with h | h
    · left
      have := (compRingHom (-X : ℤ[X])).isUnit_map h
      rwa [coe_compRingHom_apply, hinv] at this
    · right
      have := (compRingHom (-X : ℤ[X])).isUnit_map h
      rwa [coe_compRingHom_apply, hinv] at this

/-- If `P` divides an even polynomial `expand 2 A` of too small degree, then `P` is even. -/
private lemma even_of_dvd_expand (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) (A : ℤ[X]) (hA0 : A ≠ 0) (hAn : A.natDegree < P.natDegree)
    (hd : P ∣ expand ℤ 2 A) : ∃ R : ℤ[X], P = expand ℤ 2 R := by
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hPc : Irreducible (P.comp (-X)) := irreducible_comp_neg_X hirr
  have hd2 : P.comp (-X) ∣ expand ℤ 2 A := by
    have := map_dvd (compRingHom (-X : ℤ[X])) hd
    rwa [coe_compRingHom_apply, coe_compRingHom_apply, comp_neg_X_expand] at this
  have hA'0 : expand ℤ 2 A ≠ 0 := fun h => hA0 ((expand_eq_zero (by norm_num)).mp h)
  obtain ⟨Q, hQ⟩ := hd
  have hS : ((-1) ^ P.natDegree * P.comp (-X)).Monic := hmon.neg_one_pow_natDegree_mul_comp_neg_X
  have hSdeg : ((-1) ^ P.natDegree * P.comp (-X)).natDegree = P.natDegree := by
    have : ((-1 : ℤ[X]) ^ P.natDegree) = C ((-1) ^ P.natDegree) := by simp
    rw [this, natDegree_C_mul (pow_ne_zero _ (by norm_num)), natDegree_comp]
    simp
  have hPeven : P = (-1) ^ P.natDegree * P.comp (-X) := by
    rcases hPc.prime.dvd_or_dvd (hQ ▸ hd2 : P.comp (-X) ∣ P * Q) with h | h
    · refine (eq_of_monic_of_dvd_of_natDegree_le hS hmon ?_ (by rw [hSdeg]))
      rcases neg_one_pow_eq_or ℤ[X] P.natDegree with h' | h' <;> rw [h']
      · simpa using h
      · simpa using h
    · exfalso
      obtain ⟨T, hT⟩ := h
      have hdv : P * P.comp (-X) ∣ expand ℤ 2 A := ⟨T, by rw [hQ, hT]; ring⟩
      have h1 := natDegree_le_of_dvd hdv hA'0
      have hc0 : P.comp (-X) ≠ 0 := fun h => hP0 (comp_neg_X_eq_zero_iff.mp h)
      rw [natDegree_mul hP0 hc0, natDegree_comp, natDegree_expand] at h1
      simp at h1
      omega
  have hco : ∀ k, P.coeff k = (-1) ^ P.natDegree * (P.coeff k * (-1) ^ k) := by
    intro k
    have e1 : (-X : ℤ[X]) = C (-1) * X := by simp
    have e2 : ((-1 : ℤ[X]) ^ P.natDegree) = C ((-1) ^ P.natDegree) := by simp
    conv_lhs => rw [hPeven]
    rw [e2, coeff_C_mul, e1, comp_C_mul_X_coeff]
  rcases neg_one_pow_eq_or ℤ P.natDegree with h | h
  · refine ⟨contract 2 P, ?_⟩
    ext k
    rw [coeff_expand (by norm_num)]
    split_ifs with hk
    · rw [coeff_contract (by norm_num), Nat.div_mul_cancel hk]
    · have hodd : Odd k := by
        rcases Nat.even_or_odd k with he | ho
        · exact absurd (even_iff_two_dvd.mp he) hk
        · exact ho
      have := hco k
      rw [h, hodd.neg_one_pow] at this
      omega
  · exfalso
    have h0 := hco 0
    rw [h] at h0
    simp at h0
    replace h0 : P.coeff 0 = 0 := by omega
    have hX : X ∣ P := X_dvd_iff.mpr h0
    obtain ⟨c, hc⟩ := hX
    rcases hirr.isUnit_or_isUnit hc with hu | hu
    · exact not_isUnit_X hu
    · obtain ⟨u, hu', rfl⟩ := Polynomial.isUnit_iff.mp hu
      rw [hc, mul_comm, natDegree_C_mul_X _ hu'.ne_zero] at hdeg
      omega

/-- A non-unit factor of a monic integer polynomial has positive degree. -/
private lemma natDegree_pos_of_not_isUnit {a b : ℤ[X]} (h : (a * b).Monic) (ha : ¬IsUnit a) :
    0 < a.natDegree := by
  by_contra hn
  have h0 : a.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero h0] at h ha
  apply ha
  rw [eq_C_of_natDegree_eq_zero h0]
  refine isUnit_C.mpr (IsUnit.of_mul_eq_one (b.leadingCoeff) ?_)
  have := h
  rw [Monic, leadingCoeff_mul] at this
  rw [leadingCoeff_C] at this
  simpa using this

/-- Case split of the proof of [Dim19, Theorem 1] (its case split on `P_2`), in the form used
here: either `P_2` is irreducible (Case A), or `P` is even, `P = R(X²)` (Case B). -/
theorem irreducible_P2_or_even (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) :
    Irreducible (P2 P) ∨ ∃ R : ℤ[X], P = expand ℤ 2 R := by
  by_cases hirr2 : Irreducible (P2 P)
  · exact Or.inl hirr2
  right
  have hm2 := P2_monic P hmon
  have hd2 := natDegree_P2 P hmon
  have hnu : ¬IsUnit (P2 P) := by
    intro hu
    obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
    rw [← hr, natDegree_C] at hd2
    omega
  obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b, P2 P = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    by_contra hne
    apply hirr2
    refine ⟨hnu, fun a b hab => ?_⟩
    by_contra hh
    push Not at hh
    exact hne ⟨a, b, hab, hh.1, hh.2⟩
  have hmab : (a * b).Monic := hab ▸ hm2
  have ha0 : a ≠ 0 := fun h => by simp [h] at hmab
  have hb0 : b ≠ 0 := fun h => by simp [h] at hmab
  have hapos := natDegree_pos_of_not_isUnit hmab ha
  have hbpos := natDegree_pos_of_not_isUnit (by rwa [mul_comm] at hmab) hb
  have hsum : a.natDegree + b.natDegree = P.natDegree := by
    rw [← natDegree_mul ha0 hb0, ← hab, hd2]
  have hdvd : P ∣ expand ℤ 2 a * expand ℤ 2 b := by
    rw [← map_mul, ← hab, P2, map_mul, map_pow, map_neg, map_one, expand_graeffe]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  rcases hirr.prime.dvd_or_dvd hdvd with h | h
  · exact even_of_dvd_expand P hmon hirr hdeg a ha0 (by omega) h
  · exact even_of_dvd_expand P hmon hirr hdeg b hb0 (by omega) h

end RestrictedPolynomials
