module

public import RestrictedPolynomials.QuantDefs
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Lemma 5.13 (core): prime orders of roots of `D = z^a ∏ Φ_m^{e_m}`

If every nonzero complex root of a monic `D ∈ ℤ[z]` is a root of unity, then `D = z^a ∏ Φ_m^{e_m}`
and a root `λ` of `D` of prime multiplicative order `p` in any field is a root of some `Φ_m`
(so `λ^m = 1`, `p ∣ m`) with `p - 1 ≤ φ(m) ≤ deg D`.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials


lemma eq_X_pow_of_no_roots {D : ℤ[X]} (hDm : D.Monic)
    (h : ∀ β : ℂ, β ≠ 0 → aeval β D ≠ 0) : D = X ^ D.natDegree := by
  have hm : (D.map (Int.castRingHom ℂ)).Monic := hDm.map _
  have hs := IsAlgClosed.splits (D.map (Int.castRingHom ℂ))
  have hprod := hs.eq_prod_roots_of_monic hm
  have hdeg : (D.map (Int.castRingHom ℂ)).natDegree = D.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
  have hroots : (D.map (Int.castRingHom ℂ)).roots = Multiset.replicate (D.natDegree) 0 := by
    have hcard : Multiset.card (D.map (Int.castRingHom ℂ)).roots = D.natDegree := by
      rw [← hdeg]; exact splits_iff_card_roots.mp hs
    rw [← hcard, Multiset.eq_replicate_card]
    intro b hb
    by_contra hb0
    apply h b hb0
    have := (mem_roots'.mp hb).2
    rw [IsRoot, eval_map] at this
    rw [aeval_def]
    exact this
  apply Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int
  rw [hprod, hroots]
  simp

lemma key_claim : ∀ (n : ℕ) (D : ℤ[X]), D.Monic → D.natDegree = n →
    (∀ β : ℂ, β ≠ 0 → aeval β D = 0 → ∃ n : ℕ, 0 < n ∧ β ^ n = 1) →
    ∀ {F : Type*} [Field F] (lam : F), lam ≠ 0 → aeval lam D = 0 →
      ∃ m : ℕ, 0 < m ∧ aeval lam (cyclotomic m ℤ) = 0 ∧ m.totient ≤ D.natDegree := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hDm hn hroots F _ lam hlam hD
  by_cases hex : ∃ β : ℂ, β ≠ 0 ∧ aeval β D = 0
  · obtain ⟨β, hβ0, hβ⟩ := hex
    obtain ⟨m, hm, hβm⟩ := hroots β hβ0 hβ
    have hord : 0 < orderOf β := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hβm⟩)
    have hprim : IsPrimitiveRoot β (orderOf β) := IsPrimitiveRoot.orderOf β
    set k := orderOf β with hk
    have hdvdQ : toQ (cyclotomic k ℤ) ∣ toQ D := by
      rw [toQ_apply, toQ_apply, map_cyclotomic_int, cyclotomic_eq_minpoly_rat hprim hord]
      apply minpoly.dvd
      rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]
      exact hβ
    have hdvd : cyclotomic k ℤ ∣ D := dvd_of_toQ_dvd (cyclotomic.monic k ℤ) hdvdQ
    obtain ⟨D', hD'⟩ := hdvd
    have hΦm := cyclotomic.monic k ℤ
    have hD'm : D'.Monic := by
      have : (cyclotomic k ℤ * D').Monic := hD' ▸ hDm
      exact (Monic.of_mul_monic_left hΦm this)
    have hdeg : D.natDegree = (cyclotomic k ℤ).natDegree + D'.natDegree := by
      rw [hD', natDegree_mul hΦm.ne_zero hD'm.ne_zero]
    have hφ : (cyclotomic k ℤ).natDegree = k.totient := natDegree_cyclotomic k ℤ
    have hpos : 0 < k.totient := Nat.totient_pos.mpr hord
    have hev : aeval lam (cyclotomic k ℤ) * aeval lam D' = 0 := by
      rw [← map_mul, ← hD']; exact hD
    rcases mul_eq_zero.mp hev with h1 | h2
    · exact ⟨k, hord, h1, by omega⟩
    · obtain ⟨m, hm0, hm1, hm2⟩ := ih D'.natDegree (by omega) D' hD'm rfl
        (fun γ hγ0 hγ => hroots γ hγ0 (by rw [hD', map_mul, hγ, mul_zero])) lam hlam h2
      exact ⟨m, hm0, hm1, by omega⟩
  · exfalso
    push Not at hex
    have := eq_X_pow_of_no_roots hDm hex
    rw [this] at hD
    simp at hD
    exact hlam hD.1

/-- **Lemma 5.13** (core). -/
theorem prime_order_le {D : ℤ[X]} (hDm : D.Monic)
    (hroots : ∀ β : ℂ, β ≠ 0 → aeval β D = 0 → ∃ n : ℕ, 0 < n ∧ β ^ n = 1)
    {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) {lam : F} (hlam : lam ^ p = 1) (hlam1 : lam ≠ 1)
    (hDlam : aeval lam D = 0) : p ≤ D.natDegree + 1 := by
  have hl0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hlam
    exact zero_ne_one hlam
  obtain ⟨m, hm0, hm1, hm2⟩ := key_claim _ D hDm rfl hroots lam hl0 hDlam
  have hlm : lam ^ m = 1 := by
    obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one m ℤ
    have : aeval lam (X ^ m - 1 : ℤ[X]) = 0 := by
      rw [hg, map_mul, hm1, zero_mul]
    simpa [sub_eq_zero] using this
  have := Fact.mk hp
  have hord : orderOf lam = p := orderOf_eq_prime hlam hlam1
  have hpm : p ∣ m := hord ▸ orderOf_dvd_of_pow_eq_one hlm
  have h1 := Nat.totient_dvd_of_dvd hpm
  have h2 : p.totient ≤ m.totient := Nat.le_of_dvd (Nat.totient_pos.mpr hm0) h1
  rw [Nat.totient_prime hp] at h2
  omega

end RestrictedPolynomials

end
