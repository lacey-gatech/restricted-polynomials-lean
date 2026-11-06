module

public import RestrictedPolynomials.Dimitrov.Graeffe
public import RestrictedPolynomials.Dimitrov.EvenSplit
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Case A: the algebraic lemmas (S0, S9, reversal identities, S7)

Source: Supplement A, §2 (Lemma `lem:S0`, Lemma `lem:S9`),
§4 (Lemmas `lem:rev1` to `lem:ident`) and Theorem `thm:S7`.

* `caseA_S0`: for monic irreducible `P` of degree `> 1`: `P(0) ≠ 0`, all roots are nonzero and some
  root has modulus `≥ 1`.
* `caseA_S9`: the numerics `M² ≤ M⁴` and `M⁴ · 4^(-1/(2n)) < 1` for `1 ≤ M < 2^(1/(4n))`.
* `reverse_P2`, `reverse_P4`: `reverse (P2 P) = graeffe P*` and `reverse (P4 P) = graeffe (graeffe P*)`,
  where `P* = P.reverse`. No hypothesis `P(0) ≠ 0` is needed.
* `caseA_S7`: if `√(P2* · P4*)` is a rational power series then `P4 = P2`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-! ### S0 -/

/-- [A, Lemma lem:S0] -/
theorem caseA_S0 (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P) (hdeg : 1 < P.natDegree) :
    P.coeff 0 ≠ 0 ∧ (∀ α ∈ (P.map (Int.castRingHom ℂ)).roots, α ≠ 0) ∧
      ∃ α ∈ (P.map (Int.castRingHom ℂ)).roots, 1 ≤ ‖α‖ := by
  have hP0 : P ≠ 0 := hmon.ne_zero
  have ha : P.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr h0
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      exact hP0 (by simpa using hQ)
    rcases hirr.isUnit_or_isUnit hQ with hX | hu
    · exact not_isUnit_X hX
    · have := natDegree_eq_zero_of_isUnit hu
      rw [hQ, natDegree_X_mul hQ0, this] at hdeg
      omega
  have hm : (P.map (Int.castRingHom ℂ)).Monic := hmon.map _
  have hspl := IsAlgClosed.splits (P.map (Int.castRingHom ℂ))
  have hc0 : (P.map (Int.castRingHom ℂ)).coeff 0 ≠ 0 := by
    rw [coeff_map]; simpa using ha
  have hb : ∀ α ∈ (P.map (Int.castRingHom ℂ)).roots, α ≠ 0 := by
    intro α hα h0
    subst h0
    have := (mem_roots hm.ne_zero).mp hα
    rw [IsRoot, ← coeff_zero_eq_eval_zero] at this
    exact hc0 this
  refine ⟨ha, hb, ?_⟩
  by_contra hcon
  push Not at hcon
  have hprod := hspl.coeff_zero_eq_prod_roots_of_monic hm
  have hnorm : ‖(P.map (Int.castRingHom ℂ)).coeff 0‖ ≥ 1 := by
    rw [coeff_map]
    have : (P.coeff 0 : ℤ) ≠ 0 := ha
    simp only [eq_intCast, Complex.norm_intCast]
    have h1 : (1 : ℝ) ≤ |(P.coeff 0 : ℝ)| := by
      have : (1 : ℤ) ≤ |P.coeff 0| := Int.one_le_abs ha
      exact_mod_cast this
    exact h1
  have key : ∀ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < 1) → s ≠ 0 → ‖s.prod‖ < 1 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _ h; exact absurd rfl h
    | cons a t ih =>
      intro hs _
      rw [Multiset.prod_cons, norm_mul]
      have ha1 : ‖a‖ < 1 := hs a (Multiset.mem_cons_self _ _)
      have ht : ‖t.prod‖ ≤ 1 := by
        by_cases ht0 : t = 0
        · simp [ht0]
        · exact (ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb)) ht0).le
      calc ‖a‖ * ‖t.prod‖ ≤ ‖a‖ * 1 := by gcongr
        _ < 1 := by simpa using ha1
  have hne : (P.map (Int.castRingHom ℂ)).roots ≠ 0 := by
    intro h0
    have hcard := splits_iff_card_roots.mp hspl
    rw [h0] at hcard
    have hd : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
      natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
    simp at hcard
    omega
  have := key _ (fun a ha => hcon a ha) hne
  rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hnorm
  linarith

/-! ### S9 -/

/-- [A, Lemma lem:S9] numerics. -/
theorem caseA_S9 {M : ℝ} {n : ℕ} (hn : 0 < n) (hM1 : 1 ≤ M)
    (hM : M < (2 : ℝ) ^ (1 / (4 * (n : ℝ)))) :
    M ^ 2 ≤ M ^ 4 ∧ M ^ 4 * (4 : ℝ) ^ (-(1 / (2 * (n : ℝ)))) < 1 := by
  refine ⟨pow_le_pow_right₀ hM1 (by norm_num), ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have e1 : ((2 : ℝ) ^ (1 / (4 * (n : ℝ)))) ^ 4 = (2 : ℝ) ^ (1 / (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2]
    congr 1
    push_cast
    field_simp
  have e2 : (4 : ℝ) ^ (1 / (2 * (n : ℝ))) = (2 : ℝ) ^ (1 / (n : ℝ)) := by
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [this, ← Real.rpow_mul h2]
    congr 1
    field_simp
  have h4 : M ^ 4 < (4 : ℝ) ^ (1 / (2 * (n : ℝ))) := by
    rw [e2, ← e1]
    exact pow_lt_pow_left₀ hM (by linarith) (by norm_num)
  rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv]
  exact (div_lt_one (Real.rpow_pos_of_pos (by norm_num) _)).mpr h4

/-! ### Reversal identities -/

/-- `Π(B) = ∏_{b ∈ B} (1 - b X)` over `ℂ`. -/
def piC (B : Multiset ℂ) : ℂ[X] := (B.map fun b => 1 - C b * X).prod

private lemma reverse_one' : (1 : ℂ[X]).reverse = 1 := by
  rw [← C_1, reverse_C]

private lemma reverse_X_sub_C' (a : ℂ) : (X - C a).reverse = 1 - C a * X := by
  have : (X - C a : ℂ[X]) = X + C (-a) := by simp [sub_eq_add_neg]
  rw [this, reverse_add_C]
  have h1 : (X : ℂ[X]).reverse = 1 := by
    have h := reverse_mul_X (1 : ℂ[X])
    rw [one_mul, reverse_one'] at h
    exact h
  rw [h1, natDegree_X]
  simp [sub_eq_add_neg]

private lemma reverse_prod_X_sub_C' (s : Multiset ℂ) :
    ((s.map fun a => X - C a).prod).reverse = piC s := by
  induction s using Multiset.induction_on with
  | empty => simp [piC, reverse_one']
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, reverse_X_sub_C']
    simp [piC]

private lemma piC_graeffe_aux (B : Multiset ℂ) :
    expand ℂ 2 (piC (B.map (· ^ 2))) = piC B * (piC B).comp (-X) := by
  induction B using Multiset.induction_on with
  | empty => simp [piC]
  | cons b t ih =>
    have e : piC (b ::ₘ t) = (1 - C b * X) * piC t := by simp [piC]
    have e2 : piC ((b ::ₘ t).map (· ^ 2)) = (1 - C (b ^ 2) * X) * piC (t.map (· ^ 2)) := by
      simp [piC]
    rw [e2, e, map_mul, ih, mul_comp]
    simp only [map_sub, map_one, map_mul, expand_C, expand_X, sub_comp, one_comp, mul_comp,
      C_comp, X_comp]
    simp only [C_pow]
    ring

private lemma graeffe_piC (B : Multiset ℂ) : graeffe (piC B) = piC (B.map (· ^ 2)) := by
  apply expand_injective (R := ℂ) (n := 2) (by norm_num)
  rw [expand_graeffe, piC_graeffe_aux]

private lemma reverse_map_int (P : ℤ[X]) :
    (P.reverse).map (Int.castRingHom ℂ) = (P.map (Int.castRingHom ℂ)).reverse := by
  unfold reverse
  rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int, reflect_map]

private lemma map_eq_prod_roots (P : ℤ[X]) (hmon : P.Monic) :
    P.map (Int.castRingHom ℂ) = (((P.map (Int.castRingHom ℂ)).roots).map fun a => X - C a).prod :=
  (IsAlgClosed.splits _).eq_prod_roots_of_monic (hmon.map _)

private lemma reverse_ancillary (m : ℕ) (P : ℤ[X]) :
    (ancillary m P).reverse = piC ((P.map (Int.castRingHom ℂ)).roots.map (· ^ m)) := by
  unfold ancillary
  exact reverse_prod_X_sub_C' _

private lemma reverse_map_eq_piC (P : ℤ[X]) (hmon : P.Monic) :
    (P.reverse).map (Int.castRingHom ℂ) = piC ((P.map (Int.castRingHom ℂ)).roots) := by
  rw [reverse_map_int, map_eq_prod_roots P hmon]
  rw [reverse_prod_X_sub_C']
  -- the roots of the product are the original roots
  rw [← map_eq_prod_roots P hmon]

/-- [A, Lemmas lem:rev1–lem:ident] reversal identities. The supplement assumes `P(0) ≠ 0`; the
proof below does not need it, so no hypothesis is added. -/
theorem reverse_P2 (P : ℤ[X]) (hmon : P.Monic) : (P2 P).reverse = graeffe P.reverse := by
  apply Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int
  rw [reverse_map_int, map_P2 P hmon, reverse_ancillary, graeffe_map, reverse_map_eq_piC P hmon,
    graeffe_piC]

theorem reverse_P4 (P : ℤ[X]) (hmon : P.Monic) :
    (P4 P).reverse = graeffe (graeffe P.reverse) := by
  apply Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int
  rw [reverse_map_int, map_P4 P hmon, reverse_ancillary, graeffe_map, graeffe_map,
    reverse_map_eq_piC P hmon, graeffe_piC, graeffe_piC, Multiset.map_map]
  congr 2
  funext x
  simp only [Function.comp, ← pow_mul]


/-! ### S7 -/

private lemma graeffe_coeff_zero' (Q : ℤ[X]) : (graeffe Q).coeff 0 = Q.coeff 0 ^ 2 := by
  simp [graeffe, coeff_contract, pow_two, mul_coeff_zero]

private lemma reverse_reverse_of_coeff_zero (T : ℤ[X]) (h : T.coeff 0 ≠ 0) :
    T.reverse.reverse = T := by
  have hd : T.reverse.natDegree = T.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h)]; simp
  ext i
  rw [coeff_reverse, coeff_reverse, hd, revAt_invol]

private lemma coe_map_ps (ι : ℤ →+* ℚ) (G : ℤ[X]) :
    PowerSeries.map ι (G : PowerSeries ℤ) = ((G.map ι : ℚ[X]) : PowerSeries ℚ) := by
  ext k
  simp [PowerSeries.coeff_map, Polynomial.coeff_coe]


private lemma P4_monic_natDegree (P : ℤ[X]) (hP : P.Monic) :
    (P4 P).Monic ∧ (P4 P).natDegree = P.natDegree := by
  have h := map_P4 P hP
  have hm : (P.map (Int.castRingHom ℂ)).Monic := hP.map _
  have hd : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
  have h4 : ancillary 4 P = sqRoots (sqRoots (P.map (Int.castRingHom ℂ))) := ancillary_four P
  have hmon : (ancillary 4 P).Monic := by
    rw [h4]; exact sqRoots_monic _
  have hdeg : (ancillary 4 P).natDegree = P.natDegree := by
    rw [h4, natDegree_sqRoots, roots_sqRoots, Multiset.card_map, ← hd]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits (P.map (Int.castRingHom ℂ)))
  constructor
  · rw [← h] at hmon
    exact monic_of_injective (Int.castRingHom ℂ).injective_int hmon
  · have := congrArg Polynomial.natDegree h
    rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int, hdeg] at this
    exact this

/-- [A, Theorem thm:S7] rational and square ⇒ `P_4 = P_2`. -/
theorem caseA_S7 (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P) (hdeg : 1 < P.natDegree)
    (hirr2 : Irreducible (P2 P)) (f : PowerSeries ℤ) (_hf0 : PowerSeries.constantCoeff f = 1)
    (hf : f ^ 2 = ((graeffe P.reverse * graeffe (graeffe P.reverse) : ℤ[X]) : PowerSeries ℤ))
    (B A : ℚ[X]) (hB : B.coeff 0 = 1)
    (hBA : (B : PowerSeries ℚ) * PowerSeries.map (Int.castRingHom ℚ) f = (A : PowerSeries ℚ)) :
    P4 P = P2 P := by
  have hP0 := (caseA_S0 P hmon hirr hdeg).1
  set ι := Int.castRingHom ℚ with hι
  set G : ℤ[X] := graeffe P.reverse * graeffe (graeffe P.reverse) with hG
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  have hBps : (B : PowerSeries ℚ) ≠ 0 := fun h => hB0 (by apply Polynomial.coe_injective; simpa using h)
  -- Step 1
  have hfQ : (PowerSeries.map ι f) ^ 2 = ((G.map ι : ℚ[X]) : PowerSeries ℚ) := by
    rw [← coe_map_ps, ← map_pow, hf]
  have hA2 : A ^ 2 = B ^ 2 * G.map ι := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_pow, ← hBA, mul_pow, hfQ, Polynomial.coe_mul, Polynomial.coe_pow]
  have hdiv : B ∣ A :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (two_ne_zero)).mp ⟨_, hA2⟩
  obtain ⟨g, hg⟩ := hdiv
  have hfg : PowerSeries.map ι f = (g : PowerSeries ℚ) := by
    have : (B : PowerSeries ℚ) * PowerSeries.map ι f = (B : PowerSeries ℚ) * g := by
      rw [hBA, hg, Polynomial.coe_mul]
    exact mul_left_cancel₀ hBps this
  -- Step 2
  have hl : g ∈ lifts ι := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨PowerSeries.coeff n f, ?_⟩
    have := congrArg (PowerSeries.coeff n) hfg
    simpa [PowerSeries.coeff_map, Polynomial.coeff_coe] using this
  obtain ⟨h, hh⟩ := (mem_lifts g).mp hl
  have hfh : f = (h : PowerSeries ℤ) := by
    ext k
    apply ι.injective_int
    have := congrArg (PowerSeries.coeff k) hfg
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe, ← hh, coeff_map] at this
    simpa [Polynomial.coeff_coe] using this
  have hhG : h ^ 2 = G := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_pow, ← hfh, hf]
  -- Step 3
  have hTrev : (P2 P * P4 P).reverse = G := by
    rw [reverse_mul_of_domain, reverse_P2 P hmon, reverse_P4 P hmon]
  have hT0 : (P2 P * P4 P).coeff 0 ≠ 0 := by
    have e2 : (P2 P).coeff 0 = (-1) ^ P.natDegree * P.coeff 0 ^ 2 := by
      have : P2 P = C ((-1 : ℤ) ^ P.natDegree) * graeffe P := by simp [P2]
      rw [this, coeff_C_mul, graeffe_coeff_zero']
    have e4 : (P4 P).coeff 0 = (-1) ^ P.natDegree * P.coeff 0 ^ 4 := by
      have : P4 P = C ((-1 : ℤ) ^ P.natDegree) * graeffe (graeffe P) := by simp [P4]
      rw [this, coeff_C_mul, graeffe_coeff_zero', graeffe_coeff_zero']
      ring
    rw [mul_coeff_zero, e2, e4]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hP0))
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hP0))
  have hT : P2 P * P4 P = h.reverse ^ 2 := by
    rw [← reverse_reverse_of_coeff_zero _ hT0, hTrev, ← hhG, pow_two, reverse_mul_of_domain,
      pow_two]
  -- Step 4
  have hP2prime : Prime (P2 P) := hirr2.prime
  have hdvd : P2 P ∣ h.reverse := by
    refine hP2prime.dvd_of_dvd_pow (n := 2) ?_
    rw [← hT]
    exact dvd_mul_right _ _
  obtain ⟨q, hq⟩ := hdvd
  have hP2ne : P2 P ≠ 0 := (P2_monic P hmon).ne_zero
  have hP4 : P4 P = P2 P * q ^ 2 := by
    apply mul_left_cancel₀ hP2ne
    rw [hT, hq]; ring
  obtain ⟨hm4, hd4⟩ := P4_monic_natDegree P hmon
  have hm2 := P2_monic P hmon
  have hd2 := natDegree_P2 P hmon
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hP4] at hm4
    simp at hm4
  have hq2 : q ^ 2 = 1 := by
    have hdq : (q ^ 2).natDegree = 0 := by
      have := natDegree_mul hP2ne (pow_ne_zero 2 hq0)
      rw [← hP4, hd4, hd2] at this
      omega
    have hlc : (q ^ 2).leadingCoeff = 1 := by
      have := leadingCoeff_mul (P2 P) (q ^ 2)
      rw [← hP4, hm4.leadingCoeff, hm2.leadingCoeff, one_mul] at this
      exact this.symm
    rw [eq_C_of_natDegree_eq_zero hdq]
    have : (q ^ 2).coeff 0 = 1 := by rw [← hlc, leadingCoeff, hdq]
    rw [this, C_1]
  rw [hP4, hq2, mul_one]

end RestrictedPolynomials
