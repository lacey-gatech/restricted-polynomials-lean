module

public import RestrictedPolynomials.FullRank
public import RestrictedPolynomials.QuantParams
public import RestrictedPolynomials.DetEstimate
public import RestrictedPolynomials.EffBezout
public import RestrictedPolynomials.RootsOfUnity
public import RestrictedPolynomials.CyclotomicOrder

/-!
# Proposition 5.1, quantitative proof (Section 5.3)

With `M = Mℓ ℓ = exp(O(ℓ log ℓ))` and `P = Pℓ ℓ = exp exp(O(ℓ² log ℓ))` the matrix
`A_{ℓ,M}(λ)` has full rank for every `λ` of prime order `p > P` in any field.

* `gcd_data` : the monic gcd `D ∈ ℤ[z]` of the minors of `A_{ℓ,M}` and its Bézout combination.
* Lemma 5.12 (`root_of_unity_of_gcd`, using Dimitrov's theorem) : every nonzero root of `D`
  is a root of unity.
* Effective Bézout (`effective_bezout`) : `B D = ∑ V_i Δ_i`, `B ≤ Bbd ℓ`.
* Lemma 5.13 (`prime_order_le`) in characteristics `q ∤ B`; Lemma 5.14 (Frobenius orbit) when
  `q ∣ B`.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

variable {ℓ : ℕ}

/-- The monic gcd `D ∈ ℤ[z]` of the minors with rows in `rowsFin ℓ M`, with a `ℚ[z]`-Bézout
identity `D = ∑ U_a Δ_a`. -/
theorem gcd_data {M : ℕ} (hM : ℓ + 1 ≤ M) :
    ∃ D : ℤ[X], D.Monic ∧ D.natDegree ≤ dℓ ℓ ∧ (∀ a ∈ rowsFin ℓ M, D ∣ minor ℓ a) ∧
      ∃ U : (Fin ℓ → ℕ) → ℚ[X], toQ D = ∑ a ∈ rowsFin ℓ M, U a * toQ (minor ℓ a) := by
  classical
  set F := rowsFin ℓ M with hF
  have hstd : stdRows ℓ ∈ F := by
    rw [hF, mem_rowsFin]
    refine ⟨fun r r' h => by simpa [stdRows] using h, fun r => ⟨by simp [stdRows], ?_⟩⟩
    have := r.2
    simp only [stdRows]
    omega
  have hmon : ∀ a ∈ F, (minor ℓ a).Monic := fun a ha => by
    rw [hF, mem_rowsFin] at ha
    exact minor_monic a ha.1 fun r => (ha.2 r).1
  set φ : (Fin ℓ → ℕ) → ℚ[X] := fun a => toQ (minor ℓ a) with hφ
  set I : Ideal ℚ[X] := Ideal.span (φ '' (F : Set (Fin ℓ → ℕ))) with hI
  set g₀ := Submodule.IsPrincipal.generator I with hg₀
  have hIg : I = Ideal.span {g₀} := (Ideal.span_singleton_generator I).symm
  have hg₀mem : g₀ ∈ I := Submodule.IsPrincipal.generator_mem I
  have hdvd₀ : ∀ a ∈ F, g₀ ∣ φ a := by
    intro a ha
    have : φ a ∈ I := Ideal.subset_span ⟨a, ha, rfl⟩
    rwa [hIg, Ideal.mem_span_singleton] at this
  have hstdφ : φ (stdRows ℓ) ≠ 0 := (minor_stdRows_monic.map _).ne_zero
  have hg₀0 : g₀ ≠ 0 := by
    intro h0
    apply hstdφ
    have := hdvd₀ _ hstd
    rwa [h0, zero_dvd_iff] at this
  set g₁ := g₀ * C (leadingCoeff g₀)⁻¹ with hg₁
  have hg₁monic : g₁.Monic := monic_mul_leadingCoeff_inv hg₀0
  have hg₁g₀ : g₁ ∣ g₀ := by
    refine ⟨C (leadingCoeff g₀), ?_⟩
    rw [hg₁, mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hg₀0), C_1, mul_one]
  have hdvd₁ : ∀ a ∈ F, g₁ ∣ φ a := fun a ha => hg₁g₀.trans (hdvd₀ a ha)
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ minor_stdRows_monic
    (hdvd₁ _ hstd)
  rw [hg₁monic.leadingCoeff, C_1, mul_one, algebraMap_int_eq] at hg
  have hgmonic : g.Monic :=
    monic_of_injective (RingHom.injective_int (Int.castRingHom ℚ)) (hg ▸ hg₁monic)
  have hgg₁ : toQ g = g₁ := by rw [toQ_apply]; exact hg
  have hgdvd : ∀ a ∈ F, g ∣ minor ℓ a := fun a ha =>
    dvd_of_toQ_dvd hgmonic (by rw [hgg₁]; exact hdvd₁ a ha)
  refine ⟨g, hgmonic, ?_, hgdvd, ?_⟩
  · rw [← minor_stdRows_natDegree ℓ]
    exact natDegree_le_of_dvd (hgdvd _ hstd) minor_stdRows_monic.ne_zero
  · -- the Bézout identity
    obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := ℚ[X])).1 hg₀mem
    have hsupp : l.support ⊆ F := fun a ha => by simpa using hl ha
    have hsum : g₀ = ∑ a ∈ F, l a * φ a := by
      rw [← hlc, Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset l hsupp (fun i a => a • φ i) (fun a _ => zero_smul _ _)]
      exact sum_congr rfl fun a _ => smul_eq_mul _ _
    refine ⟨fun a => l a * C (leadingCoeff g₀)⁻¹, ?_⟩
    generalize leadingCoeff g₀ = lc at *
    rw [hgg₁, hg₁, hsum, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    simp only [hφ]
    ring

lemma stdRows_mem_rowsFin {M : ℕ} (hM : ℓ + 1 ≤ M) : stdRows ℓ ∈ rowsFin ℓ M := by
  rw [mem_rowsFin]
  refine ⟨fun r r' h => by simpa [stdRows] using h, fun r => ⟨by simp [stdRows], ?_⟩⟩
  have := r.2
  simp only [stdRows]
  omega

/-- **Proposition 5.1, quantitative form.** With `M = Mℓ ℓ = exp(O(ℓ log ℓ))` and
`P = Pℓ ℓ = exp exp(O(ℓ² log ℓ))` (see `Mℓ_growth`, `Pℓ_growth`): if `p > P` is prime and `λ`
has multiplicative order `p` in a field `L`, the matrix `(λ^{y^j} - 1)_{2 ≤ y ≤ M, 1 ≤ j ≤ ℓ}`
has trivial kernel. -/
theorem full_rank_quant (hℓ : 1 ≤ ℓ) (L : Type) [Field L] (p : ℕ) (hp : p.Prime)
    (hPp : Pℓ ℓ < p) (lam : L) (hlamp : lam ^ p = 1) (hlam1 : lam ≠ 1) (c : Fin ℓ → L)
    (hc : ∀ y ∈ Icc 2 (Mℓ ℓ), ∑ j, c j * (lam ^ (y ^ ((j : ℕ) + 1)) - 1) = 0) : c = 0 := by
  classical
  by_contra hc0
  set M := Mℓ ℓ with hMdef
  have hM : ℓ + 1 ≤ M := Mℓ_ge ℓ
  obtain ⟨D, hDm, hDdeg, hDdvd, U, hU⟩ := gcd_data (ℓ := ℓ) hM
  have hroots : ∀ β : ℂ, β ≠ 0 → aeval β D = 0 → ∃ n : ℕ, 0 < n ∧ β ^ n = 1 :=
    fun β hβ h => root_of_unity_of_gcd hℓ hM (Mℓ_big ℓ) hDm hDdeg hDdvd hβ h
  -- the effective Bézout identity
  set F := rowsFin ℓ M with hF
  have hstd : stdRows ℓ ∈ F := stdRows_mem_rowsFin hM
  let e : F ≃ Fin F.card := F.equivFin
  let Δ : Fin F.card → ℤ[X] := fun i => minor ℓ (e.symm i : F)
  let i₀ : Fin F.card := e ⟨stdRows ℓ, hstd⟩
  have hΔi₀ : Δ i₀ = minor ℓ (stdRows ℓ) := by simp [Δ, i₀]
  have hmonic : (Δ i₀).Monic := hΔi₀ ▸ minor_stdRows_monic
  have hdeg : ∀ i, (Δ i).natDegree ≤ nℓ ℓ M := fun i => minor_natDegree_le (e.symm i).2
  set x : ℕ := 2 ^ ℓ * ℓ.factorial with hx
  have hx1 : 1 ≤ x := Nat.mul_pos (pow_pos two_pos _) (Nat.factorial_pos _)
  have hcoeff : ∀ i j, |(Δ i).coeff j| ≤ (x : ℤ) := fun i j => by
    have := minor_coeff_abs_le (ℓ := ℓ) (e.symm i : F).1 j
    simpa [hx] using this
  have hDdeg' : D.natDegree ≤ (Δ i₀).natDegree := by
    rw [hΔi₀, minor_stdRows_natDegree]; exact hDdeg
  have hbez : ∃ U' : Fin F.card → ℚ[X], toQ D = ∑ i, U' i * toQ (Δ i) := by
    refine ⟨fun i => U (e.symm i : F), ?_⟩
    rw [hU, ← Finset.sum_coe_sort F]
    exact (Equiv.sum_comp e.symm (fun a : F => U a * toQ (minor ℓ a))).symm
  obtain ⟨B, hB0, hBle, V, hV⟩ := effective_bezout Δ (nℓ ℓ M) x (one_le_nℓ hℓ) hx1 i₀ hmonic
    hdeg hcoeff D hDdeg' hbez
  have hBbd : B ≤ Bbd ℓ := hBle
  -- every minor vanishes at `λ`
  have hminor : ∀ a ∈ F, aeval lam (minor ℓ a) = 0 := by
    intro a ha
    have ha' := mem_rowsFin.1 ha
    rw [aeval_minor, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨c, hc0, funext fun r => ?_⟩
    simp only [Matrix.mulVec, dotProduct, evalMat, Matrix.of_apply, Pi.zero_apply]
    rw [← hc (a r) (mem_Icc.2 (ha'.2 r))]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hord : ∀ m : ℕ, lam ^ m = 1 → p ∣ m := by
    have : Fact p.Prime := ⟨hp⟩
    intro m hm
    rw [← orderOf_eq_prime hlamp hlam1]
    exact orderOf_dvd_of_pow_eq_one hm
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hlamp
    exact zero_ne_one hlamp
  have hBD : (B : L) * aeval lam D = 0 := by
    have := congrArg (aeval lam) hV
    simpa [map_sum, map_mul, hminor _ (e.symm _).2, Δ] using this
  have hPd : dℓ ℓ + 1 ≤ Pℓ ℓ := le_max_left _ _
  have hd1 : 1 ≤ dℓ ℓ := one_le_dℓ hℓ
  by_cases hBL : (B : L) ≠ 0
  · -- good characteristic: `D(λ) = 0` and `p ≤ deg D + 1`
    have hDlam : aeval lam D = 0 := (mul_eq_zero.1 hBD).resolve_left hBL
    have := prime_order_le hDm hroots hp hlamp hlam1 hDlam
    omega
  · -- exceptional characteristic `q ∣ B`: the Frobenius orbit of `λ`
    push Not at hBL
    set q := ringChar L with hqdef
    have : CharP L q := ringChar.charP L
    have hqB : q ∣ B := (CharP.cast_eq_zero_iff L q B).1 hBL
    have hq0 : q ≠ 0 := by
      rintro h0
      rw [h0, zero_dvd_iff] at hqB
      exact hB0.ne' hqB
    have hqp : q.Prime := CharP.char_prime_of_ne_zero L hq0
    have : Fact q.Prime := ⟨hqp⟩
    have hqle : q ≤ B := Nat.le_of_dvd hB0 hqB
    have hBd : B ^ dℓ ℓ ≤ Pℓ ℓ :=
      (Nat.pow_le_pow_left hBbd _).trans (le_max_right _ _)
    have hBB : B ≤ B ^ dℓ ℓ := Nat.le_self_pow (by omega) B
    set f : L[X] := (minor ℓ (stdRows ℓ)).map (Int.castRingHom L) with hf
    have hfm : f.Monic := minor_stdRows_monic.map _
    have hfd : f.natDegree = dℓ ℓ := by
      rw [hf, minor_stdRows_monic.natDegree_map, minor_stdRows_natDegree]
    have hroot : ∀ i : ℕ, lam ^ (q ^ i) ∈ f.roots.toFinset := by
      intro i
      rw [Multiset.mem_toFinset, mem_roots hfm.ne_zero, IsRoot, hf, eval_map,
        ← algebraMap_int_eq, ← aeval_def]
      induction i with
      | zero => simpa using hminor _ hstd
      | succ i ih => rw [pow_succ, pow_mul, aeval_pow_char, ih, zero_pow hqp.ne_zero]
    have hcard : f.roots.toFinset.card < (range (dℓ ℓ + 1)).card := by
      rw [card_range]
      have := (Multiset.toFinset_card_le f.roots).trans (card_roots' f)
      omega
    obtain ⟨i, hi, j, hj, hij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun i => lam ^ (q ^ i)) fun i _ => hroot i
    simp only [mem_range] at hi hj
    have key : ∀ i j : ℕ, i < j → j ≤ dℓ ℓ → lam ^ (q ^ i) = lam ^ (q ^ j) → False := by
      intro i j hij hjd heq
      set μ := lam ^ (q ^ i)
      have hμ0 : μ ≠ 0 := pow_ne_zero _ hlam0
      have hqj : q ^ j = q ^ i * q ^ (j - i) := by rw [← pow_add]; congr 1; omega
      have hpos : 1 ≤ q ^ (j - i) := Nat.one_le_pow _ _ hqp.pos
      have h1 : μ ^ (q ^ (j - i) - 1) = 1 := by
        have h2 : μ * μ ^ (q ^ (j - i) - 1) = μ * 1 := by
          rw [mul_one, ← pow_succ', Nat.sub_add_cancel hpos, ← pow_mul, ← hqj, ← heq]
        exact mul_left_cancel₀ hμ0 h2
      rw [← pow_mul] at h1
      rcases (Nat.Prime.dvd_mul hp).1 (hord _ h1) with h3 | h3
      · have := Nat.le_of_dvd hqp.pos (hp.dvd_of_dvd_pow h3)
        omega
      · have hq2 : 2 ≤ q ^ (j - i) := by
          calc 2 ≤ q := hqp.two_le
            _ = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ (j - i) := Nat.pow_le_pow_right hqp.pos (by omega)
        have h4 := Nat.le_of_dvd (by omega) h3
        have : q ^ (j - i) ≤ B ^ dℓ ℓ :=
          (Nat.pow_le_pow_left hqle _).trans (Nat.pow_le_pow_right hB0 (by omega))
        omega
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h (by omega) heq
    · exact key j i h (by omega) heq.symm

end RestrictedPolynomials

end
