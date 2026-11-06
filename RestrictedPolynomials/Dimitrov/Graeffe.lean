module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Graeffe transform and the ancillary polynomials `P_2`, `P_4`

Arithmetic layer of [Dim19, Lemma mod4] (arXiv:1912.12545v1 `main.tex`, l. 183-216):
the Graeffe root-squaring transform `graeffe`, its identity
`graeffe P (X²) = P(X)·P(−X)`, and the fact that for monic `P ∈ ℤ[X]` the signed transforms
`P2 P`, `P4 P` are the integer polynomials `∏ (X − α_i^m)` for `m = 2, 4`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- Graeffe root-squaring transform: writing `P = E(X²) + X·O(X²)`, `graeffe P = E² − X·O²`, so that
`graeffe P (X²) = P(X)·P(−X)`. -/
noncomputable def graeffe {R : Type*} [CommRing R] (P : R[X]) : R[X] :=
  (contract 2 P) ^ 2 - X * (contract 2 P.divX) ^ 2

/-- Even/odd decomposition `P = E(X²) + X·O(X²)`. -/
lemma graeffe_decomp {R : Type*} [CommRing R] (P : R[X]) :
    P = expand R 2 (contract 2 P) + X * expand R 2 (contract 2 P.divX) := by
  ext n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [coeff_add, coeff_expand (by norm_num), coeff_contract (by norm_num)]
    rcases m with _ | k
    · simp
    · have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, coeff_X_mul, coeff_expand (by norm_num)]
      have h3 : (2 * k + 1 + 1) / 2 * 2 = 2 * k + 1 + 1 := by omega
      have h4 : ¬ (2 ∣ 2 * k + 1) := by omega
      simp [h3, h4]
  · rw [coeff_add, coeff_expand (by norm_num), coeff_X_mul, coeff_expand (by norm_num)]
    have h1 : ¬ (2 ∣ 2 * m + 1) := by omega
    have h2 : (2 ∣ 2 * m) := ⟨m, rfl⟩
    simp only [h1, h2, ↓reduceIte, zero_add]
    rw [coeff_contract (by norm_num), coeff_divX]
    have h5 : 2 * m / 2 * 2 + 1 = 2 * m + 1 := by omega
    rw [h5]

private lemma expand_comp_neg_X {R : Type*} [CommRing R] (f : R[X]) :
    (expand R 2 f).comp (-X) = expand R 2 f := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp

theorem expand_graeffe {R : Type*} [CommRing R] (P : R[X]) :
    expand R 2 (graeffe P) = P * P.comp (-X) := by
  set e := expand R 2 (contract 2 P) with he
  set o := expand R 2 (contract 2 P.divX) with ho
  have hP : P = e + X * o := graeffe_decomp P
  have hc : P.comp (-X) = e - X * o := by
    conv_lhs => rw [hP]
    rw [add_comp, mul_comp, X_comp, he, ho, expand_comp_neg_X, expand_comp_neg_X]
    ring
  rw [hc]
  conv_rhs => rw [hP]
  simp only [graeffe, map_sub, map_pow, map_mul, expand_X, ← he, ← ho]
  ring

theorem graeffe_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : R[X]) :
    (graeffe P).map f = graeffe (P.map f) := by
  simp only [graeffe, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, map_X,
    map_contract (by norm_num : (2:ℕ) ≠ 0)]
  congr 3
  ext n
  simp [coeff_contract, coeff_divX, coeff_map]

lemma graeffe_neg {R : Type*} [CommRing R] (P : R[X]) : graeffe (-P) = graeffe P := by
  have h1 : contract 2 (-P) = - contract 2 P := by
    ext n; simp [coeff_contract]
  have h2 : (-P).divX = - P.divX := by
    ext n; simp [coeff_divX]
  have h3 : contract 2 (-P.divX) = - contract 2 P.divX := by
    ext n; simp [coeff_contract]
  rw [graeffe, graeffe, h2, h1, h3]
  ring

/-- Squaring the roots of a monic polynomial over `ℂ`. -/
def sqRoots (Q : ℂ[X]) : ℂ[X] :=
  (((Q.roots.map (· ^ 2)).map (fun a => X - C a))).prod

private lemma expand_prod_sq (s : Multiset ℂ) :
    expand ℂ 2 ((s.map (fun a => X - C (a ^ 2))).prod) =
      (-1) ^ Multiset.card s * ((s.map (fun a => X - C a)).prod *
        (s.map (fun a => X - C a)).prod.comp (-X)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have hf : expand ℂ 2 (X - C (a ^ 2)) = -1 * ((X - C a) * (X - C a).comp (-X)) := by
      rw [map_sub, expand_X, expand_C]
      simp only [sub_comp, X_comp, C_comp, C_pow]
      ring
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul,
      ih, hf, mul_comp, Multiset.card_cons, pow_succ]
    ring

lemma sqRoots_eq {Q : ℂ[X]} (hQ : Q.Monic) :
    sqRoots Q = (-1) ^ Q.natDegree * graeffe Q := by
  have hs := IsAlgClosed.splits Q
  have hprod := hs.eq_prod_roots_of_monic hQ
  have hcard : Multiset.card Q.roots = Q.natDegree := splits_iff_card_roots.mp hs
  apply expand_injective (R := ℂ) (n := 2) (by norm_num)
  rw [map_mul, map_pow, map_neg, map_one, expand_graeffe]
  have : sqRoots Q = (Q.roots.map (fun a => X - C (a ^ 2))).prod := by
    simp [sqRoots, Multiset.map_map]
  rw [this, expand_prod_sq, hcard]
  rw [← hprod]

lemma sqRoots_monic (Q : ℂ[X]) : (sqRoots Q).Monic := by
  unfold sqRoots
  exact monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)

lemma roots_sqRoots (Q : ℂ[X]) : (sqRoots Q).roots = Q.roots.map (· ^ 2) :=
  roots_multiset_prod_X_sub_C _

lemma natDegree_sqRoots (Q : ℂ[X]) : (sqRoots Q).natDegree = Multiset.card Q.roots := by
  unfold sqRoots
  rw [natDegree_multiset_prod_X_sub_C_eq_card]
  simp

/-- The ancillary polynomial `P_m = ∏ (X − α_i^m)` of [Dim19, Lemma mod4], over `ℂ`. -/
noncomputable def ancillary (m : ℕ) (P : ℤ[X]) : ℂ[X] :=
  (((P.map (Int.castRingHom ℂ)).roots.map (· ^ m)).map (fun a => X - C a)).prod

/-- Integer polynomials `P_2`, `P_4` (signed so that they are monic for monic `P`). -/
noncomputable def P2 (P : ℤ[X]) : ℤ[X] := (-1) ^ P.natDegree * graeffe P
noncomputable def P4 (P : ℤ[X]) : ℤ[X] := (-1) ^ P.natDegree * graeffe (graeffe P)

private lemma map_neg_one_pow_mul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) (Q : R[X]) : ((-1) ^ n * Q).map f = (-1) ^ n * Q.map f := by
  simp [Polynomial.map_mul, Polynomial.map_pow]

/-- `P_2 ∈ ℤ[X]` ([Dim19, Lemma mod4], integrality of `P_m`, `m = 2`). -/
theorem map_P2 (P : ℤ[X]) (hP : P.Monic) : (P2 P).map (Int.castRingHom ℂ) = ancillary 2 P := by
  have hm : (P.map (Int.castRingHom ℂ)).Monic := hP.map _
  have hd : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
  have := sqRoots_eq hm
  rw [hd] at this
  unfold P2 ancillary
  rw [map_neg_one_pow_mul, graeffe_map]
  exact this.symm

lemma ancillary_four (P : ℤ[X]) :
    ancillary 4 P = sqRoots (sqRoots (P.map (Int.castRingHom ℂ))) := by
  unfold ancillary sqRoots
  rw [roots_multiset_prod_X_sub_C]
  simp [Multiset.map_map, ← pow_mul]

/-- `P_4 ∈ ℤ[X]` ([Dim19, Lemma mod4], integrality of `P_m`, `m = 4`). -/
theorem map_P4 (P : ℤ[X]) (hP : P.Monic) : (P4 P).map (Int.castRingHom ℂ) = ancillary 4 P := by
  have hm : (P.map (Int.castRingHom ℂ)).Monic := hP.map _
  have hd : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
  have h1 := sqRoots_eq hm
  have h2 := sqRoots_eq (sqRoots_monic (P.map (Int.castRingHom ℂ)))
  have hn : (sqRoots (P.map (Int.castRingHom ℂ))).natDegree = P.natDegree := by
    rw [natDegree_sqRoots, ← hd]
    exact (splits_iff_card_roots.mp (IsAlgClosed.splits _))
  rw [ancillary_four, h2, hn, h1, hd]
  unfold P4
  rw [map_neg_one_pow_mul, graeffe_map, graeffe_map]
  rcases neg_one_pow_eq_or ℂ[X] P.natDegree with h | h <;>
    rw [h] <;> simp [graeffe_neg]

end RestrictedPolynomials
