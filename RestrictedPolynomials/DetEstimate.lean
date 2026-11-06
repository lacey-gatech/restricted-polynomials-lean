module

public import RestrictedPolynomials.QuantDefs

/-!
# Lemma 5.10: the determinant estimate, and coefficient bounds for the minors
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

variable {ℓ : ℕ}

/-- Bernoulli-type inequality: `m^(k+1) + k m^k ≤ m (m+1)^k`. -/
lemma bernoulli_aux (m : ℕ) : ∀ k : ℕ, m ^ (k + 1) + k * m ^ k ≤ m * (m + 1) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m * (m + 1) ^ (k + 1) = (m + 1) * (m * (m + 1) ^ k) := by ring
    rw [h1]
    calc m ^ (k + 1 + 1) + (k + 1) * m ^ (k + 1)
        ≤ (m + 1) * (m ^ (k + 1) + k * m ^ k) := by
          have h2 : m ^ (k + 1 + 1) = m * m ^ (k + 1) := by ring
          have h3 : m ^ (k + 1) = m * m ^ k := by ring
          rw [h2]
          nlinarith [Nat.zero_le (k * m ^ k), Nat.zero_le (m ^ k), Nat.zero_le (k * m ^ k * m)]
      _ ≤ (m + 1) * (m * (m + 1) ^ k) := Nat.mul_le_mul_left _ ih

lemma two_mul_pow_le (n : ℕ) : 2 * (n + 1) ^ (n + 1) ≤ (n + 2) ^ (n + 1) := by
  have h := bernoulli_aux (n + 1) (n + 1)
  have h2 : (n + 1) * (n + 1 + 1) ^ (n + 1) = (n + 1) * (n + 2) ^ (n + 1) := rfl
  have h3 : (n + 1) ^ (n + 1 + 1) = (n + 1) * (n + 1) ^ (n + 1) := by ring
  rw [h2, h3] at h
  have h4 : (n + 1) * (n + 1) ^ (n + 1) + (n + 1) * (n + 1) ^ (n + 1) =
      (n + 1) * (2 * (n + 1) ^ (n + 1)) := by ring
  rw [h4] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.succ_pos n)

/-- `2^ℓ ℓ! ≤ (ℓ+1)^ℓ` (AM–GM). -/
theorem two_pow_mul_factorial_le (ℓ : ℕ) : 2 ^ ℓ * ℓ.factorial ≤ (ℓ + 1) ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ n ih =>
    have h1 : 2 ^ (n + 1) * (n + 1).factorial = 2 * (n + 1) * (2 ^ n * n.factorial) := by
      rw [Nat.factorial_succ]; ring
    rw [h1]
    calc 2 * (n + 1) * (2 ^ n * n.factorial) ≤ 2 * (n + 1) * (n + 1) ^ n :=
          Nat.mul_le_mul_left _ ih
      _ = 2 * (n + 1) ^ (n + 1) := by ring
      _ ≤ (n + 2) ^ (n + 1) := two_mul_pow_le n

/-- Coefficientwise domination `|p_i| ≤ q_i`. -/
def Dom (p q : ℤ[X]) : Prop := ∀ i, |p.coeff i| ≤ q.coeff i

lemma Dom.add {p p' q q' : ℤ[X]} (h : Dom p q) (h' : Dom p' q') : Dom (p + p') (q + q') := by
  intro i
  simp only [coeff_add]
  exact (abs_add_le _ _).trans (add_le_add (h i) (h' i))

lemma Dom.mul {p p' q q' : ℤ[X]} (h : Dom p q) (h' : Dom p' q') : Dom (p * p') (q * q') := by
  intro n
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) ((abs_nonneg _).trans (h _))

lemma Dom.sum {ι : Type*} (s : Finset ι) {f g : ι → ℤ[X]} (h : ∀ i ∈ s, Dom (f i) (g i)) :
    Dom (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro n
  simp only [finsetSum_coeff]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => h i hi n)

lemma Dom.one : Dom (1 : ℤ[X]) 1 := by
  intro i
  simp only [coeff_one]
  split_ifs <;> simp

lemma Dom.prod {ι : Type*} (s : Finset ι) {f g : ι → ℤ[X]} (h : ∀ i ∈ s, Dom (f i) (g i)) :
    Dom (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Dom.one
  | insert r s hr ih =>
    rw [prod_insert hr, prod_insert hr]
    exact (h r (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

lemma Dom.smul_unit {p q : ℤ[X]} (h : Dom p q) (u : ℤˣ) : Dom (u • p) q := by
  intro i
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using h i
  · simpa using h i

lemma dom_binom (e : ℕ) : Dom (X ^ e - 1 : ℤ[X]) (X ^ e + 1) := by
  intro i
  simp only [coeff_sub, coeff_add, coeff_one, coeff_X_pow]
  split_ifs <;> simp_all

lemma minor_eq_sum (a : Fin ℓ → ℕ) : minor ℓ a =
    ∑ σ : Equiv.Perm (Fin ℓ), Equiv.Perm.sign σ •
      ∏ i, (X ^ (a (σ i) ^ ((i : ℕ) + 1)) - 1 : ℤ[X]) := by
  rw [minor, Matrix.det_apply]
  simp [minorMat]

lemma minor_dom (a : Fin ℓ → ℕ) : Dom (minor ℓ a)
    (∑ σ : Equiv.Perm (Fin ℓ), ∏ i, (X ^ (a (σ i) ^ ((i : ℕ) + 1)) + 1 : ℤ[X])) := by
  rw [minor_eq_sum]
  exact Dom.sum _ fun σ _ => (Dom.prod _ fun i _ => dom_binom _).smul_unit _

lemma sum_abs_le_eval {p q : ℤ[X]} (h : Dom p q) :
    ∑ i ∈ range (p.natDegree + 1), |p.coeff i| ≤ q.eval 1 := by
  have h1 : ∑ i ∈ range (p.natDegree + 1), |p.coeff i| = ∑ i ∈ p.support, |p.coeff i| := by
    symm
    refine sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
    · rw [mem_range, Nat.lt_succ_iff]; exact le_natDegree_of_mem_supp i hi
    · rw [notMem_support_iff.1 hi]; simp
  rw [h1, eval_eq_sum, Polynomial.sum]
  simp only [one_pow, mul_one]
  calc ∑ i ∈ p.support, |p.coeff i| ≤ ∑ i ∈ p.support, q.coeff i := sum_le_sum fun i _ => h i
    _ ≤ ∑ i ∈ q.support, q.coeff i := by
      refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i _ _ => ?_)
      · rw [mem_support_iff] at hi ⊢
        intro h0
        have := h i
        rw [h0] at this
        exact hi (abs_nonpos_iff.1 this)
      · exact (abs_nonneg _).trans (h i)

/-- The sum of the absolute values of the coefficients of any `ℓ × ℓ` minor is at most
`2^ℓ ℓ!` (Leibniz formula: `ℓ!` products of `ℓ` binomials `z^e - 1`). -/
theorem minor_coeff_sum_le (a : Fin ℓ → ℕ) :
    ∑ i ∈ range ((minor ℓ a).natDegree + 1), |(minor ℓ a).coeff i| ≤ 2 ^ ℓ * (ℓ.factorial : ℤ) := by
  refine (sum_abs_le_eval (minor_dom a)).trans_eq ?_
  simp [eval_finsetSum, eval_prod, Fintype.card_perm, mul_comm]

/-- Every coefficient of a minor has absolute value at most `2^ℓ ℓ!`. -/
theorem minor_coeff_abs_le (a : Fin ℓ → ℕ) (i : ℕ) :
    |(minor ℓ a).coeff i| ≤ 2 ^ ℓ * (ℓ.factorial : ℤ) := by
  by_cases hi : i ≤ (minor ℓ a).natDegree
  · exact (single_le_sum (f := fun i => |(minor ℓ a).coeff i|) (fun _ _ => abs_nonneg _)
      (mem_range.2 (Nat.lt_succ_of_le hi))).trans (minor_coeff_sum_le a)
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    simp only [abs_zero]
    positivity

/-- Exchange inequality with a gap of `A`. -/
lemma exchange_gap {A W s m : ℕ} (hA : 1 ≤ A) (hAW : A < W) (hsm : s < m) :
    W ^ (s + 1) + A ^ (m + 1) + A ≤ A ^ (s + 1) + W ^ (m + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = s + 1 + d := ⟨m - s - 1, by omega⟩
  have hP : A ^ (s + 1) < W ^ (s + 1) := Nat.pow_lt_pow_left hAW (by omega)
  have hAP : A ≤ A ^ (s + 1) := Nat.le_self_pow (by omega) A
  have hab : A ^ (d + 1) < W ^ (d + 1) := Nat.pow_lt_pow_left hAW (by omega)
  have ha' : 1 ≤ A ^ (d + 1) := Nat.one_le_pow _ _ hA
  have e1 : A ^ (s + 1 + d + 1) = A ^ (s + 1) * A ^ (d + 1) := by rw [← pow_add]; ring_nf
  have e2 : W ^ (s + 1 + d + 1) = W ^ (s + 1) * W ^ (d + 1) := by rw [← pow_add]; ring_nf
  rw [e1, e2]
  set P := A ^ (s + 1)
  set Q := W ^ (s + 1)
  set a' := A ^ (d + 1)
  set b' := W ^ (d + 1)
  zify at hP ha' hab hAP ⊢
  nlinarith [mul_le_mul_of_nonneg_right hP.le (show (0 : ℤ) ≤ b' - 1 by linarith),
    mul_le_mul_of_nonneg_left (show (a' : ℤ) + 1 ≤ b' by linarith)
      (show (0 : ℤ) ≤ (P : ℤ) by positivity)]

/-- For `σ ≠ 1`, `e(σ) + g ≤ e(1)` when all rows are `≥ g`. -/
lemma permExp_gap (a : Fin ℓ → ℕ) (ha : StrictMono a) (ha2 : ∀ r, 2 ≤ a r) (g : ℕ)
    (hg : ∀ r, g ≤ a r) :
    ∀ σ : Equiv.Perm (Fin ℓ), σ ≠ 1 → permExp a σ + g ≤ permExp a 1 := by
  suffices h : ∀ n : ℕ, ∀ σ : Equiv.Perm (Fin ℓ), σ.support.card ≤ n →
      permExp a σ ≤ permExp a 1 ∧ (σ ≠ 1 → permExp a σ + g ≤ permExp a 1) from
    fun σ hσ => (h _ σ le_rfl).2 hσ
  intro n
  induction n with
  | zero =>
    intro σ hσ
    have : σ = 1 := Equiv.Perm.support_eq_empty_iff.1 (card_eq_zero.1 (Nat.le_zero.1 hσ))
    subst this
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  | succ n ih =>
    intro σ hσ
    by_cases h1 : σ = 1
    · subst h1; exact ⟨le_rfl, fun h => absurd rfl h⟩
    have hne : σ.support.Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, Equiv.Perm.support_eq_empty_iff]; exact h1
    set m := σ.support.max' hne with hm
    have hmS : m ∈ σ.support := max'_mem _ _
    have hσm : σ m ≠ m := Equiv.Perm.mem_support.1 hmS
    have hu : σ m < m := by
      have h1 : σ m ∈ σ.support := Equiv.Perm.apply_mem_support.2 hmS
      exact lt_of_le_of_ne (le_max' _ _ h1) hσm
    set s := σ⁻¹ m with hs
    have hσs : σ s = m := by simp [hs]
    have hsm : s ≠ m := by
      intro h
      have := hσs
      rw [h] at this
      exact hσm this
    have hsS : s ∈ σ.support := by
      rw [Equiv.Perm.mem_support, hσs]; exact fun h => hsm h.symm
    have hs_lt : s < m := lt_of_le_of_ne (le_max' _ _ hsS) hsm
    set τ := σ * Equiv.swap s m with hτ
    have hτm : τ m = m := by simp [hτ, Equiv.swap_apply_right, hσs]
    have hτs : τ s = σ m := by simp [hτ, Equiv.swap_apply_left]
    have hτi : ∀ i, i ≠ s → i ≠ m → τ i = σ i := by
      intro i his him
      simp [hτ, Equiv.swap_apply_of_ne_of_ne his him]
    have hsupp : τ.support ⊆ σ.support.erase m := by
      intro i hi
      rw [Equiv.Perm.mem_support] at hi
      refine mem_erase.2 ⟨fun h => hi (h ▸ hτm), ?_⟩
      by_cases his : i = s
      · rw [his]; exact hsS
      · have him : i ≠ m := fun h => hi (h ▸ hτm)
        rw [Equiv.Perm.mem_support, ← hτi i his him]; exact hi
    have hcard : τ.support.card ≤ n := by
      have := card_le_card hsupp
      rw [card_erase_of_mem hmS] at this
      omega
    have hτle := (ih τ hcard).1
    have hlt : permExp a σ + g ≤ permExp a τ := by
      unfold permExp
      have hpair : ({s, m} : Finset (Fin ℓ)) ⊆ univ := subset_univ _
      rw [← sum_sdiff hpair, ← sum_sdiff hpair (f := fun i => a (τ i) ^ ((i : ℕ) + 1)),
        sum_pair hsm, sum_pair hsm]
      have hrest : ∑ i ∈ univ \ {s, m}, a (σ i) ^ ((i : ℕ) + 1) =
          ∑ i ∈ univ \ {s, m}, a (τ i) ^ ((i : ℕ) + 1) := by
        refine sum_congr rfl fun i hi => ?_
        simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hi
        rw [hτi i hi.2.1 hi.2.2]
      rw [hrest, hσs, hτs, hτm]
      have hA : a (σ m) < a m := ha hu
      have := exchange_gap (A := a (σ m)) (by have := ha2 (σ m); omega) hA
        (show (s : ℕ) < m from hs_lt)
      have := hg (σ m)
      omega
    exact ⟨(le_of_add_le_left hlt).trans hτle, fun _ => hlt.trans hτle⟩

lemma prod_sub_one_decomp (g : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, g ≤ e i) :
    ∃ R : ℤ[X], ∏ i ∈ s, (X ^ e i - 1 : ℤ[X]) = X ^ (∑ i ∈ s, e i) + R ∧
      ∀ k, ∑ i ∈ s, e i < k + g → R.coeff k = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert r s hr ih =>
    obtain ⟨R, hR, hc⟩ := ih (fun i hi => he i (mem_insert_of_mem hi))
    have her := he r (mem_insert_self _ _)
    refine ⟨X ^ (e r) * R - X ^ (∑ i ∈ s, e i) - R, ?_, ?_⟩
    · rw [prod_insert hr, sum_insert hr, hR, pow_add]; ring
    · intro k hk
      rw [sum_insert hr] at hk
      have h1 : e r ≤ k → R.coeff (k - e r) = 0 := fun h => hc _ (by omega)
      have h2 : k ≠ ∑ i ∈ s, e i := by omega
      have h3 : R.coeff k = 0 := hc k (by omega)
      simp only [coeff_sub, coeff_X_pow_mul', coeff_X_pow, h3, h2, ite_false]
      split_ifs with h
      · simp [h1 h]
      · simp

lemma minor_decomp (a : Fin ℓ → ℕ) (ha : StrictMono a) (ha2 : ∀ r, 2 ≤ a r) (g : ℕ)
    (hg : ∀ r, g ≤ a r) :
    ∃ R : ℤ[X], minor ℓ a = X ^ (permExp a 1) + R ∧
      ∀ k, permExp a 1 < k + g → R.coeff k = 0 := by
  classical
  set P : Equiv.Perm (Fin ℓ) → ℤ[X] := fun σ => ∏ i, (X ^ (a (σ i) ^ ((i : ℕ) + 1)) - 1)
    with hP
  have hdeg : ∀ σ, (P σ).natDegree = permExp a σ := by
    intro σ
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_pow_sub_C 1 (pow_ne_zero _ (by
      have := ha2 (σ i); omega))]
    refine sum_congr rfl fun i _ => ?_
    exact natDegree_X_pow_sub_C
  obtain ⟨R₀, hR₀, hc₀⟩ := prod_sub_one_decomp g (univ : Finset (Fin ℓ))
    (fun i => a i ^ ((i : ℕ) + 1))
    (fun i _ => (hg i).trans (Nat.le_self_pow (by omega) _))
  have hP1 : P 1 = X ^ (permExp a 1) + R₀ := by
    have : permExp a 1 = ∑ i, a i ^ ((i : ℕ) + 1) := by simp [permExp]
    rw [this, ← hR₀]
    simp [hP]
  refine ⟨R₀ + ∑ σ ∈ univ.erase 1, Equiv.Perm.sign σ • P σ, ?_, ?_⟩
  · rw [minor_eq_sum, ← add_sum_erase _ _ (mem_univ 1)]
    have : (Equiv.Perm.sign (1 : Equiv.Perm (Fin ℓ))) • ∏ i, (X ^ (a ((1 : Equiv.Perm (Fin ℓ)) i) ^
        ((i : ℕ) + 1)) - 1 : ℤ[X]) = P 1 := by simp [hP]
    rw [this, hP1]
    ring
  · intro k hk
    rw [coeff_add, hc₀ k hk, zero_add, finsetSum_coeff]
    refine sum_eq_zero fun σ hσ => ?_
    have hgap := permExp_gap a ha ha2 g hg σ (mem_erase.1 hσ).1
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), smul_zero]

lemma minor_natDegree_eq (a : Fin ℓ → ℕ) (ha : StrictMono a) (ha2 : ∀ r, 2 ≤ a r) :
    (minor ℓ a).natDegree = permExp a 1 := by
  obtain ⟨R, hR, hc⟩ := minor_decomp a ha ha2 1 (fun r => by have := ha2 r; omega)
  rw [hR]
  have : R.degree < (permExp a 1 : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]; intro m hm; exact hc m (by omega)
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact this)]
  simp

/-- **Lemma 5.10.** If the minor with the last `ℓ` rows `L-ℓ+1, …, L` vanishes at `α ∈ ℂ`,
then `|α|^{L-ℓ} ≤ 2^ℓ ℓ!` (equivalently `log |α| ≤ ℓ log(ℓ+1) / (L-ℓ)`). -/
theorem det_estimate (hℓ : 1 ≤ ℓ) {L : ℕ} (hL : ℓ + 1 ≤ L) (α : ℂ)
    (hα : aeval α (minor ℓ fun r : Fin ℓ => L - ℓ + 1 + (r : ℕ)) = 0) :
    ‖α‖ ^ (L - ℓ) ≤ 2 ^ ℓ * (ℓ.factorial : ℝ) := by
  set g := L - ℓ with hg
  set a : Fin ℓ → ℕ := fun r : Fin ℓ => L - ℓ + 1 + (r : ℕ) with ha_def
  have hα' : aeval α (minor ℓ a) = 0 := hα
  have hsm : StrictMono a := fun r s h => by
    have : (r : ℕ) < s := h
    simp only [ha_def]; omega
  have ha2 : ∀ r, 2 ≤ a r := fun r => by simp only [ha_def]; omega
  have hga : ∀ r, g ≤ a r := fun r => by simp only [ha_def]; omega
  obtain ⟨R, hR, hc⟩ := minor_decomp a hsm ha2 g hga
  have hdeg := minor_natDegree_eq a hsm ha2
  have hmon := minor_monic a hsm ha2
  have hsum := minor_coeff_sum_le a
  rw [hdeg] at hsum
  set d := permExp a 1 with hd_def
  have hgd : g ≤ d := by
    have h0 : (0 : ℕ) < ℓ := hℓ
    have : a ⟨0, h0⟩ ^ (((⟨0, h0⟩ : Fin ℓ) : ℕ) + 1) ≤ d := by
      rw [hd_def]; simp only [permExp, Equiv.Perm.coe_one, id]
      exact single_le_sum (f := fun i : Fin ℓ => a i ^ ((i : ℕ) + 1))
        (fun _ _ => Nat.zero_le _) (mem_univ (⟨0, h0⟩ : Fin ℓ))
    have h2 := hga ⟨0, h0⟩
    simp only [zero_add, pow_one] at this
    omega
  have hone : (minor ℓ a).coeff d = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  by_cases h1 : ‖α‖ ≤ 1
  · calc ‖α‖ ^ g ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
      _ ≤ 2 ^ ℓ * (ℓ.factorial : ℝ) := by
        have h2 : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ ℓ.factorial := by exact_mod_cast Nat.factorial_pos ℓ
        nlinarith
  · rw [not_le] at h1
    have hex : ∑ i ∈ range (d + 1), ((minor ℓ a).coeff i : ℂ) * α ^ i = 0 := by
      have := hα'
      rw [aeval_eq_sum_range, hdeg] at this
      simpa [zsmul_eq_mul] using this
    rw [sum_range_succ, hone] at hex
    have hpow : ‖α‖ ^ d ≤ ∑ i ∈ range d, |((minor ℓ a).coeff i : ℝ)| * ‖α‖ ^ (d - g) := by
      have h2 : α ^ d = -∑ i ∈ range d, ((minor ℓ a).coeff i : ℂ) * α ^ i := by
        simp at hex
        linear_combination hex
      calc ‖α‖ ^ d = ‖α ^ d‖ := by rw [norm_pow]
        _ = ‖∑ i ∈ range d, ((minor ℓ a).coeff i : ℂ) * α ^ i‖ := by rw [h2, norm_neg]
        _ ≤ ∑ i ∈ range d, ‖((minor ℓ a).coeff i : ℂ) * α ^ i‖ := norm_sum_le _ _
        _ ≤ _ := by
          refine sum_le_sum fun i hi => ?_
          rw [norm_mul, norm_pow, Complex.norm_intCast]
          by_cases hz : (minor ℓ a).coeff i = 0
          · simp [hz]
          · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            have hi' : i < d := mem_range.1 hi
            have : i + g ≤ d := by
              by_contra hcon
              apply hz
              rw [hR, coeff_add, coeff_X_pow, if_neg (show ¬ i = d by omega), zero_add]
              exact hc i (by omega)
            exact pow_le_pow_right₀ h1.le (by omega)
    rw [← sum_mul] at hpow
    have hS : ∑ i ∈ range d, |((minor ℓ a).coeff i : ℝ)| ≤ 2 ^ ℓ * (ℓ.factorial : ℝ) := by
      have h2 := hsum
      rw [sum_range_succ, hone] at h2
      have h3 : ∑ i ∈ range d, |(minor ℓ a).coeff i| ≤ 2 ^ ℓ * (ℓ.factorial : ℤ) := by
        simp at h2; linarith
      exact_mod_cast h3
    have hpos : 0 < ‖α‖ ^ (d - g) := pow_pos (by linarith) _
    have h4 : ‖α‖ ^ d = ‖α‖ ^ (d - g) * ‖α‖ ^ g := by rw [← pow_add]; congr 1; omega
    rw [h4] at hpow
    have := le_of_mul_le_mul_left (hpow.trans_eq (mul_comm _ _)) hpos
    exact this.trans hS

/-- The degree of a minor with increasing rows `≤ M` is at most `n_ℓ` (it is monic with leading
term `z^{∑ a_r^{r+1}}`). -/
theorem minor_natDegree_le {M : ℕ} {a : Fin ℓ → ℕ} (ha : a ∈ rowsFin ℓ M) :
    (minor ℓ a).natDegree ≤ nℓ ℓ M := by
  obtain ⟨hsm, hb⟩ := mem_rowsFin.1 ha
  rw [minor_natDegree_eq a hsm fun r => (hb r).1]
  have key : ∀ k r : ℕ, ∀ h : r + k < ℓ, a ⟨r, by omega⟩ + k ≤ a ⟨r + k, h⟩ := by
    intro k
    induction k with
    | zero => intro r h; simp
    | succ k ih =>
      intro r h
      have h1 := ih r (by omega)
      have h2 : a ⟨r + k, by omega⟩ < a ⟨r + (k + 1), h⟩ := hsm (by simp [Fin.lt_def])
      omega
  have hle : ∀ r : Fin ℓ, a r ≤ M - ℓ + 1 + (r : ℕ) := by
    intro r
    have h1 := key (ℓ - 1 - r) r (by omega)
    have h2 := (hb ⟨r + (ℓ - 1 - r), by omega⟩).2
    simp only [Fin.eta] at h1
    have h3 := (hb r).1
    omega
  unfold nℓ
  rw [← Fin.sum_univ_eq_sum_range (fun r => (M - ℓ + 1 + r) ^ (r + 1)) ℓ]
  simp only [permExp, Equiv.Perm.coe_one, id]
  exact sum_le_sum fun r _ => Nat.pow_le_pow_left (hle r) _

/-- The minor with rows `2, …, ℓ+1` has degree `d_ℓ`. -/
theorem minor_stdRows_natDegree (ℓ : ℕ) : (minor ℓ (stdRows ℓ)).natDegree = dℓ ℓ := by
  rw [minor_natDegree_eq _ (fun r r' h => by simpa [stdRows] using h) fun r => by simp [stdRows]]
  unfold dℓ
  rw [← Fin.sum_univ_eq_sum_range (fun r => (r + 2) ^ (r + 1)) ℓ]
  simp [permExp, stdRows]

end RestrictedPolynomials

end
