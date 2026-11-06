module

public import RestrictedPolynomials.TrackB.K7KcspPair
public import RestrictedPolynomials.TrackB.K6Lowering
public import RestrictedPolynomials.TrackB.K6MainUniform
public import RestrictedPolynomials.TrackB.RestrictCompose
public import RestrictedPolynomials.Defs

/-!
# Track B: the restricted-correlation event of CSP_7 `lemma:kcsp`

Source: CSP_7, l. 600-613: `lemma:kcsp#combine-restrictions` (the event `k7EventProb`) and
`#convert-to-mu1` (the lowering and monotonicity used with it).

This file holds the `hconv`-independent part: `k7EventProb`, `k7_goodRestr_iff_eventProb`,
`k7_eventProb_lowering` and `k7_eventProb_mono`. The rest of this step, `k7_apply_3csp` (with three
independent alphabets and two functions) and `k7_combine_restrictions`, is in `K7KcspCombine`, in
the form of Supplement H, which proves the step `convert-to-mu1` instead of assuming it.

`k7_eventProb_lowering` carries `hF : ∀ x, ‖F x‖ ≤ 1`: without it the statement is false
(`F` a large multiple of an indicator).
-/

@[expose] public section

open Finset
open scoped BigOperators
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Event
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- the probability `Pr_{I ∼_{1-ρ}[ι], z ∼ ν^I}[∃ {P_i}_{i ∈ Ī}, ‖P_i‖_∞ ≤ 1, |𝔼_{x ∼ π^{Ī}} F_{I→z}(x) ∏ P_i(x_i)| ≥ η]`
of the restricted-correlation event of CSP_7 `lemma:kcsp` (`ρ` = free rate, `ν` the fixing law, `π` the free
law; `π = uniform` is the `GoodRestr` of `K6Lowering`). A real number, not a bundled `Prop`. -/
def k7EventProb (ν π : FinProb α) (ρ η : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (F : (ι → α) → ℂ) : ℝ :=
  (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
    (ν.pi ↥I).cexpect fun z =>
      if ∃ P : ↥Iᶜ → α → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
          η ≤ ‖(π.pi ↥Iᶜ).cexpect fun x => restrictFix I z F x * ∏ i, P i (x i)‖
        then (1 : ℂ) else 0).re

/-! ### Private helpers -/

/-- the event inside `k7EventProb` (free law `π`). -/
private def k7lBad (π : FinProb α) (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) : Prop :=
  ∃ P : ↥Jᶜ → α → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
    η ≤ ‖(π.pi ↥Jᶜ).cexpect fun x => restrictFix J v F x * ∏ i, P i (x i)‖

open scoped Classical in
/-- its indicator. -/
private def k7lInd (π : FinProb α) (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) : ℂ :=
  if k7lBad π F η J v then 1 else 0

omit [DecidableEq α] in
private theorem k7l_eventProb_eq (ν π : FinProb α) (ρ η : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → α) → ℂ) :
    k7EventProb ν π ρ η h0 h1 F =
      (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (ν.pi ↥I).cexpect fun z => k7lInd π F η I z).re :=
  rfl

omit [DecidableEq α] in
private theorem k7l_ind_re_nonneg (π : FinProb α) (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι)
    (v : J → α) : 0 ≤ (k7lInd π F η J v).re := by
  unfold k7lInd
  split_ifs <;> simp

omit [DecidableEq α] in
private theorem k7l_ind_re_of (π : FinProb α) (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι)
    (v : J → α) (h : k7lBad π F η J v) : (k7lInd π F η J v).re = 1 := by
  unfold k7lInd
  simp [h]

omit [DecidableEq α] in
private theorem k7l_ind_re_of_not (π : FinProb α) (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι)
    (v : J → α) (h : ¬ k7lBad π F η J v) : (k7lInd π F η J v).re = 0 := by
  unfold k7lInd
  simp [h]

omit [DecidableEq α] in
private theorem k7l_ind_re_mono (π : FinProb α) (F : (ι → α) → ℂ) {η η' : ℝ} (hη : η' ≤ η)
    (J : Finset ι) (v : J → α) : (k7lInd π F η J v).re ≤ (k7lInd π F η' J v).re := by
  by_cases h : k7lBad π F η J v
  · have h' : k7lBad π F η' J v := by
      obtain ⟨P, hP, hn⟩ := h
      exact ⟨P, hP, hη.trans hn⟩
    rw [k7l_ind_re_of π F η J v h, k7l_ind_re_of π F η' J v h']
  · rw [k7l_ind_re_of_not π F η J v h]
    exact k7l_ind_re_nonneg π F η' J v

private theorem k7l_re_cexpect_scaled {κ : Type} [Fintype κ] (P : FinProb κ) (c : ℝ)
    (f g : κ → ℂ) (h : ∀ k, c * (f k).re ≤ (g k).re) : c * (P.cexpect f).re ≤ (P.cexpect g).re := by
  unfold FinProb.cexpect
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

private theorem k7l_re_cexpect_ge {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) (c : ℝ)
    (h : ∀ k, c ≤ (f k).re) : c ≤ (P.cexpect f).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
  calc c = ∑ k, P.prob k * c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

omit [DecidableEq α] in
private theorem k7l_re_nested_scaled {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (ν : FinProb α) (c : ℝ)
    (f g : ∀ I : Finset ι, (↥I → α) → ℂ) (h : ∀ I z, c * (f I z).re ≤ (g I z).re) :
    c * (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (f I)).re ≤
      (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (g I)).re := by
  unfold subsetExpect
  exact k7l_re_cexpect_scaled _ c _ _ fun s =>
    k7l_re_cexpect_scaled _ c _ _ fun z => h _ z

private theorem k7l_norm_cexpect_le_one {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ)
    (hf : ∀ k, ‖f k‖ ≤ 1) : ‖P.cexpect f‖ ≤ 1 := by
  unfold FinProb.cexpect
  calc ‖∑ k, (P.prob k : ℂ) * f k‖ ≤ ∑ k, ‖(P.prob k : ℂ) * f k‖ := norm_sum_le _ _
    _ ≤ ∑ k, P.prob k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P.nonneg k)]
        exact mul_le_of_le_one_right (P.nonneg k) (hf k)
    _ = 1 := P.sum_eq_one

private theorem k7l_cexpect_const_mul {κ : Type} [Fintype κ] (P : FinProb κ) (c : ℂ)
    (f : κ → ℂ) : P.cexpect (fun k => c * f k) = c * P.cexpect f := by
  unfold FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- the product law splits along a fixed set: `𝔼_{π^κ} G = 𝔼_{w ∼ π^I} 𝔼_{y ∼ π^{Iᶜ}} G(w, y)`. -/
private theorem k7l_cexpect_glue (π : FinProb α) {κ : Type} [Fintype κ] [DecidableEq κ]
    (I : Finset κ) (G : (κ → α) → ℂ) :
    (π.pi κ).cexpect G =
      (π.pi ↥I).cexpect fun w => (π.pi ↥Iᶜ).cexpect fun y => G (glueFix I w y) := by
  rw [← cexpect_comm]
  have h := inner_glue π π I G
  have h2 : (π.pi ↥Iᶜ).cexpect (fun z => (π.pi ↥I).cexpect
      fun y => G (glueFix I y z)) = (π.pi κ).cexpect G := by
    refine h.trans ?_
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [FinProb.pi]
  exact h2.symm

omit [DecidableEq α] in
/-- `𝔼_{π^{Ī}}` of the uniform law is the Mathlib average. -/
private theorem k7l_cexpect_uniform [Nonempty α] {κ : Type} [Fintype κ] [DecidableEq κ]
    (G : (κ → α) → ℂ) : ((FinProb.uniform (α := α)).pi κ).cexpect G = 𝔼 x, G x := by
  unfold FinProb.cexpect
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : (Fintype.card α : ℂ) ≠ 0 := by
    have := Fintype.card_pos (α := α)
    exact_mod_cast this.ne'
  simp only [FinProb.pi, FinProb.uniform, Finset.prod_const, Finset.card_univ, Fintype.card_fun]
  push_cast
  rw [div_pow, one_pow]
  field_simp

/-- the key step of the lowering: for a fixed good `(I, w)` with witness `P` and every second fixed
set `I'`, the second fixed values (law `π`) make the event at level `η/2` occur with probability
`≥ η/2` (Markov, `prob_ge_half_of_expect_ge`). -/
private theorem k7l_key_inner (π : FinProb α) (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) {η : ℝ}
    (I : Finset ι) (w : I → α) (hb : k7lBad π F η I w) (I' : Finset ↥Iᶜ) :
    η / 2 ≤ ((π.pi ↥I').cexpect fun w' =>
      k7lInd π F (η / 2) (composeSet I I') (composeVals I I' w w')).re := by
  classical
  obtain ⟨P, hP, hnorm⟩ := hb
  set g : (↥Iᶜ → α) → ℂ := restrictFix I w F with hg
  let c : (I' → α) → ℝ := fun w' =>
    ‖(π.pi ↥I'ᶜ).cexpect fun y => restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)‖
  have hc0 : ∀ w', 0 ≤ c w' := fun _ => norm_nonneg _
  have hc1 : ∀ w', c w' ≤ 1 := by
    intro w'
    refine k7l_norm_cexpect_le_one _ _ fun y => ?_
    rw [norm_mul, norm_prod]
    have h1 : ‖restrictFix I' w' g y‖ ≤ 1 := hF _
    have h2 : ∏ i : ↥I'ᶜ, ‖P i.1 (y i)‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hP _ _
    calc ‖restrictFix I' w' g y‖ * ∏ i : ↥I'ᶜ, ‖P i.1 (y i)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- the decomposition of the expectation
  have hE : ((π.pi ↥Iᶜ).cexpect fun x => g x * ∏ i, P i (x i)) =
      ∑ w', ((π.pi ↥I').prob w' : ℂ) *
        ((∏ i : I', P i.1 (w' i)) *
          (π.pi ↥I'ᶜ).cexpect fun y => restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)) := by
    rw [k7l_cexpect_glue π I']
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hsplit : ∏ i : ↥Iᶜ, P i (glueFix I' w' y i) =
        (∏ i : I', P i.1 (w' i)) * ∏ i : ↥I'ᶜ, P i.1 (y i) := by
      rw [← Finset.prod_mul_prod_compl I' (fun i => P i (glueFix I' w' y i))]
      congr 1
      · rw [← Finset.prod_coe_sort I']
        exact Finset.prod_congr rfl fun i _ => by simp [glueFix, i.2]
      · rw [← Finset.prod_coe_sort I'ᶜ]
        refine Finset.prod_congr rfl fun i _ => ?_
        have : (i : ↥Iᶜ) ∉ I' := mem_compl.1 i.2
        simp [glueFix, this]
    dsimp only
    rw [hsplit]
    have : g (glueFix I' w' y) = restrictFix I' w' g y := rfl
    rw [this]
    ring
  have hsum : η ≤ ∑ w', (π.pi ↥I').prob w' * c w' := by
    refine hnorm.trans ?_
    rw [hE]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ((π.pi ↥I').nonneg w')]
    refine mul_le_mul_of_nonneg_left ?_ ((π.pi ↥I').nonneg w')
    rw [norm_mul]
    have h2 : ‖∏ i : I', P i.1 (w' i)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hP _ _)
    calc ‖∏ i : I', P i.1 (w' i)‖ * ‖(π.pi ↥I'ᶜ).cexpect
          fun y => restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)‖
        ≤ 1 * c w' := mul_le_mul h2 le_rfl (hc0 w') zero_le_one
      _ = c w' := one_mul _
  have hmk := prob_ge_half_of_expect_ge (π.pi ↥I') c hc0 hc1 hsum
  refine hmk.trans ?_
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
  refine (Finset.sum_le_sum (fun k hk => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => mul_nonneg ((π.pi ↥I').nonneg k) (k7l_ind_re_nonneg _ _ _ _ _)))
  have hk' : η / 2 ≤ c k := (Finset.mem_filter.1 hk).2
  have hbad : k7lBad π F (η / 2) (composeSet I I') (composeVals I I' w k) := by
    refine ⟨fun j => P (composeEquiv I I' j).1, fun j a => hP _ a, ?_⟩
    have hEq : ((π.pi ↥(composeSet I I')ᶜ).cexpect fun x => restrictFix (composeSet I I')
        (composeVals I I' w k) F x * ∏ j, P (composeEquiv I I' j).1 (x j)) =
        (π.pi ↥I'ᶜ).cexpect fun y => restrictFix I' k g y * ∏ i : ↥I'ᶜ, P i.1 (y i) := by
      rw [cexpect_pi_composeEquiv π I I']
      congr 1
      funext y
      rw [hg, restrictFix_compose I I' w k F]
      congr 1
      exact (Fintype.prod_equiv (composeEquiv I I') (fun j => P (composeEquiv I I' j).1
          (y j)) (fun i => P i.1 (y ((composeEquiv I I').symm i)))
          fun j => by simp only [Equiv.symm_apply_apply])
    rw [hEq]
    exact hk'
  rw [k7l_ind_re_of _ _ _ _ _ hbad, mul_one]

/-! ### Targets -/

/-- bridge to the K6 event: `GoodRestr` is `k7EventProb` with the uniform free law. -/
theorem k7_goodRestr_iff_eventProb [Nonempty α] (ν : FinProb α) {ρ η p : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (F : (ι → α) → ℂ) :
    GoodRestr ν ρ η p h0 h1 F ↔ p ≤ k7EventProb ν (FinProb.uniform (α := α)) ρ η h0 h1 F := by
  classical
  unfold GoodRestr k7EventProb
  simp only [k7l_cexpect_uniform]

/-- lowering inside the `(π, π)`-form (the analogue of `goodRestr_lowering`; same-law nested
restrictions, `nested_restriction_expect` with all laws `π`, and Markov's inequality). The
hypothesis `hF` (`F` is `1`-bounded) is a source premise; without it the statement is false. -/
theorem k7_eventProb_lowering (π : FinProb α) {ρ ρ' η q : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρ'0 : 0 < ρ') (hρ' : ρ' ≤ ρ) (hη : 0 < η) (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (h : q ≤ k7EventProb π π ρ η hρ0.le hρ1 F) :
    q * η / 2 ≤ k7EventProb π π ρ' (η / 2) hρ'0.le (hρ'.trans hρ1) F := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, ρ' = ρ * t := ⟨ρ' / ρ, by field_simp⟩
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have ht1 : t ≤ 1 := by
    by_contra hgt
    push Not at hgt
    nlinarith
  have hbar : ∀ a, (1 - ρ * t) * π.prob a =
      (1 - ρ) * π.prob a + ρ * (1 - t) * π.prob a := fun a => by ring
  have hnest := nested_restriction_law (ι := ι) hρ0.le hρ1 ht0 ht1 π π π hbar
    (fun J v => k7lInd π F (η / 2) J v)
  rw [k7l_eventProb_eq] at h ⊢
  have key := k7l_re_nested_scaled (ι := ι) (by linarith : 0 ≤ 1 - ρ) (by linarith) π (η / 2)
    (fun I z => k7lInd π F η I z)
    (fun I w => subsetExpect (ι := ↥Iᶜ) (1 - t) (by linarith) (by linarith) fun I' =>
      (π.pi ↥I').cexpect fun w' => k7lInd π F (η / 2) (composeSet I I') (composeVals I I' w w'))
    (fun I w => by
      by_cases hb : k7lBad π F η I w
      · rw [k7l_ind_re_of π F η I w hb, mul_one]
        unfold subsetExpect
        exact k7l_re_cexpect_ge _ _ _ fun s => k7l_key_inner π F hF I w hb _
      · rw [k7l_ind_re_of_not π F η I w hb, mul_zero]
        unfold subsetExpect
        exact k7l_re_cexpect_ge _ _ _ fun s => k7l_re_cexpect_ge _ _ _ fun w' =>
          k7l_ind_re_nonneg _ _ _ _ _)
  rw [hnest] at key
  calc q * η / 2 = η / 2 * q := by ring
    _ ≤ η / 2 * (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (π.pi ↥I).cexpect fun z => k7lInd π F η I z).re :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ _ := key

/-- the event is monotone in `η`. -/
theorem k7_eventProb_mono (ν π : FinProb α) {ρ η η' : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hη : η' ≤ η) (F : (ι → α) → ℂ) :
    k7EventProb ν π ρ η h0 h1 F ≤ k7EventProb ν π ρ η' h0 h1 F := by
  rw [k7l_eventProb_eq, k7l_eventProb_eq]
  have := k7l_re_nested_scaled (ι := ι) (by linarith : 0 ≤ 1 - ρ) (by linarith) ν 1
    (fun I z => k7lInd π F η I z) (fun I z => k7lInd π F η' I z)
    (fun I z => by rw [one_mul]; exact k7l_ind_re_mono π F hη I z)
  rwa [one_mul] at this

end Event

end TrackB
end RestrictedPolynomials
end
