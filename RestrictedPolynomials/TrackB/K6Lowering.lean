module

public import RestrictedPolynomials.TrackB.RestrictCompose
public import RestrictedPolynomials.TrackB.Restrict
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Track B: the lowering lemma (Supplement D)

`GoodRestr ν ρ η p` is the event `S_π(F; ρ, η, p)` of Supplement D Def. S, with the fixed-value law
`ν = ν_ρ` explicit; `goodRestr_lowering` is Supplement D's Lemma lowering and
`goodRestr_lowering_delta` its corollary `δ ↦ δ' ≤ δ²/2`.

The hypothesis `0 < η` is added to `goodRestr_lowering`: the printed statement is false for `η < 0`.
-/

@[expose] public section

open Finset
open scoped BigOperators
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Lowering
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- Supplement D Def. S: the event `S_π(F; ρ, η, p)` with `ν = ν_ρ` the law of the fixed values
(`π = (1-ρ) ν + ρ U` is a hypothesis of each statement that uses it, never part of the definition):
`Pr_{I ∼_{1-ρ}[ι], z ∼ ν^I}[∃ P_i, ‖P_i‖_∞ ≤ 1, |𝔼_x F_{I→z}(x) ∏ P_i(x_i)| ≥ η] ≥ p`. -/
def GoodRestr (ν : FinProb α) (ρ η p : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (F : (ι → α) → ℂ) : Prop :=
  p ≤ (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
    (ν.pi ↥I).cexpect fun z =>
      if ∃ P : ↥Iᶜ → α → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
          η ≤ ‖𝔼 x : ↥Iᶜ → α, restrictFix I z F x * ∏ i, P i (x i)‖ then (1 : ℂ) else 0).re

/-! ### Helpers -/

/-- the event inside `GoodRestr` -/
private def Bad (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) : Prop :=
  ∃ P : ↥Jᶜ → α → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
    η ≤ ‖𝔼 x : ↥Jᶜ → α, restrictFix J v F x * ∏ i, P i (x i)‖

open scoped Classical in
/-- its indicator -/
private def indBad (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) : ℂ :=
  if Bad F η J v then 1 else 0

private theorem goodRestr_iff (ν : FinProb α) (ρ η p : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → α) → ℂ) :
    GoodRestr ν ρ η p h0 h1 F ↔
      p ≤ (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (ν.pi ↥I).cexpect fun z => indBad F η I z).re :=
  Iff.rfl

private theorem indBad_re_nonneg (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) :
    0 ≤ (indBad F η J v).re := by
  unfold indBad
  split_ifs <;> simp

private theorem indBad_re_of (F : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α)
    (h : Bad F η J v) : (indBad F η J v).re = 1 := by
  unfold indBad
  rw [if_pos h]
  simp

private theorem indBad_re_mono (F : (ι → α) → ℂ) {η η' : ℝ} (hη : η' ≤ η) (J : Finset ι)
    (v : J → α) : (indBad F η J v).re ≤ (indBad F η' J v).re := by
  by_cases h : Bad F η J v
  · have h' : Bad F η' J v := by
      obtain ⟨P, hP, hn⟩ := h
      exact ⟨P, hP, hη.trans hn⟩
    rw [indBad_re_of F η J v h, indBad_re_of F η' J v h']
  · have : (indBad F η J v).re = 0 := by
      unfold indBad
      rw [if_neg h]
      simp
    rw [this]
    exact indBad_re_nonneg F η' J v

private theorem re_cexpect_ge {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) (c : ℝ)
    (h : ∀ k, c ≤ (f k).re) : c ≤ (P.cexpect f).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
  calc c = ∑ k, P.prob k * c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

private theorem re_subsetExpect_ge {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (G : Finset ι → ℂ) (c : ℝ)
    (h : ∀ I, c ≤ (G I).re) : c ≤ (subsetExpect q h0 h1 G).re := by
  unfold subsetExpect
  exact re_cexpect_ge _ _ _ fun s => h _

private theorem re_nested_scaled (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (ν : FinProb α) (c : ℝ)
    (f g : ∀ I : Finset ι, (↥I → α) → ℂ) (h : ∀ I z, c * (f I z).re ≤ (g I z).re) :
    c * (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (f I)).re ≤
      (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (g I)).re := by
  unfold subsetExpect FinProb.cexpect
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (((bernoulli q h0 h1).pi ι).nonneg s)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h _ _) ((ν.pi _).nonneg z)

/-- `GoodRestr` is monotone: the event grows with smaller `η'`, and the threshold lowers. -/
theorem goodRestr_mono (ν : FinProb α) {ρ η p η' p' : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → α) → ℂ) (hη : η' ≤ η) (hp : p' ≤ p) (h : GoodRestr ν ρ η p h0 h1 F) :
    GoodRestr ν ρ η' p' h0 h1 F := by
  rw [goodRestr_iff] at h ⊢
  have key := re_nested_scaled (ι := ι) (1 - ρ) (by linarith) (by linarith) ν 1
    (fun I z => indBad F η I z) (fun I z => indBad F η' I z)
    (fun I z => by rw [one_mul]; exact indBad_re_mono F hη I z)
  rw [one_mul] at key
  exact hp.trans (h.trans key)

/-- Markov-type inequality of Lemma lowering: `0 ≤ c ≤ 1` with `𝔼 c ≥ η` has `Pr[c ≥ η/2] ≥ η/2`. -/
theorem prob_ge_half_of_expect_ge {κ : Type} [Fintype κ] (π : FinProb κ) (c : κ → ℝ)
    (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1) {η : ℝ} (h : η ≤ ∑ k, π.prob k * c k) :
    η / 2 ≤ ∑ k ∈ univ.filter (fun k => η / 2 ≤ c k), π.prob k := by
  classical
  by_cases hη : η ≤ 0
  · have : 0 ≤ ∑ k ∈ univ.filter (fun k => η / 2 ≤ c k), π.prob k :=
      Finset.sum_nonneg fun k _ => π.nonneg k
    linarith
  · push Not at hη
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun k => η / 2 ≤ c k)] at h
    have h1 : ∑ k ∈ univ.filter (fun k => η / 2 ≤ c k), π.prob k * c k ≤
        ∑ k ∈ univ.filter (fun k => η / 2 ≤ c k), π.prob k :=
      Finset.sum_le_sum fun k _ => by
        calc π.prob k * c k ≤ π.prob k * 1 :=
              mul_le_mul_of_nonneg_left (hc1 k) (π.nonneg k)
          _ = π.prob k := mul_one _
    have h2 : ∑ k ∈ univ.filter (fun k => ¬ η / 2 ≤ c k), π.prob k * c k ≤
        ∑ k ∈ univ.filter (fun k => ¬ η / 2 ≤ c k), π.prob k * (η / 2) :=
      Finset.sum_le_sum fun k hk => by
        have : c k < η / 2 := by
          have := (Finset.mem_filter.1 hk).2
          exact not_le.1 this
        exact mul_le_mul_of_nonneg_left this.le (π.nonneg k)
    have h3 : ∑ k ∈ univ.filter (fun k => ¬ η / 2 ≤ c k), π.prob k * (η / 2) ≤ η / 2 := by
      rw [← Finset.sum_mul]
      have hs : ∑ k ∈ univ.filter (fun k => ¬ η / 2 ≤ c k), π.prob k ≤ 1 := by
        rw [← π.sum_eq_one]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => π.nonneg k)
      nlinarith
    linarith

/-! ### The uniform law and splitting of a uniform expectation -/

/-- the uniform law on a finite nonempty `α` -/
private def unifP (α : Type) [Fintype α] [Nonempty α] : FinProb α where
  prob _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  sum_eq_one := by
    have : (Fintype.card α : ℝ) ≠ 0 := by
      have := Fintype.card_pos (α := α)
      positivity
    simp [Finset.sum_const, Finset.card_univ]

private theorem cexpect_unif [Nonempty α] {κ : Type} [Fintype κ] [DecidableEq κ]
    (G : (κ → α) → ℂ) : ((unifP α).pi κ).cexpect G = 𝔼 x, G x := by
  unfold FinProb.cexpect
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : (Fintype.card α : ℂ) ≠ 0 := by
    have := Fintype.card_pos (α := α)
    exact_mod_cast this.ne'
  simp only [FinProb.pi, unifP, Finset.prod_const, Finset.card_univ, Fintype.card_fun]
  push_cast
  rw [div_pow, one_pow]
  field_simp

private theorem cexpect_unif_glue [Nonempty α] {κ : Type} [Fintype κ] [DecidableEq κ]
    (I : Finset κ) (G : (κ → α) → ℂ) :
    ((unifP α).pi κ).cexpect G =
      ((unifP α).pi ↥I).cexpect fun w => ((unifP α).pi ↥Iᶜ).cexpect fun y => G (glueFix I w y) := by
  rw [← cexpect_comm]
  have h := inner_glue (unifP α) (unifP α) I G
  have h2 : ((unifP α).pi ↥Iᶜ).cexpect (fun z => ((unifP α).pi ↥I).cexpect
      fun y => G (glueFix I y z)) = ((unifP α).pi κ).cexpect G := by
    refine h.trans ?_
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [FinProb.pi]
  exact h2.symm

/-- the key step: for a fixed `(I, w)` that is good with witness `P`, and every second fixed set
`I'`, the uniform law of the second fixed values makes the event at level `η/2` occur with
probability `≥ η/2`. -/
private theorem key_inner [Nonempty α] (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) {η : ℝ}
    (I : Finset ι) (w : I → α) (hb : Bad F η I w) (I' : Finset ↥Iᶜ) :
    η / 2 ≤ (((unifP α).pi ↥I').cexpect fun w' =>
      indBad F (η / 2) (composeSet I I') (composeVals I I' w w')).re := by
  classical
  obtain ⟨P, hP, hnorm⟩ := hb
  set g : (↥Iᶜ → α) → ℂ := restrictFix I w F with hg
  let c : (I' → α) → ℝ := fun w' =>
    ‖𝔼 y : ↥I'ᶜ → α, restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)‖
  have hc0 : ∀ w', 0 ≤ c w' := fun _ => norm_nonneg _
  have hc1 : ∀ w', c w' ≤ 1 := by
    intro w'
    show ‖𝔼 y : ↥I'ᶜ → α, restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)‖ ≤ 1
    refine (RCLike.norm_expect_le (K := ℂ)).trans ?_
    calc 𝔼 y : ↥I'ᶜ → α, ‖restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)‖
        ≤ 𝔼 _y : ↥I'ᶜ → α, (1 : ℝ) := by
          refine Finset.expect_le_expect fun y _ => ?_
          rw [norm_mul, norm_prod]
          have h1 : ‖restrictFix I' w' g y‖ ≤ 1 := hF _
          have h2 : ∏ i : ↥I'ᶜ, ‖P i.1 (y i)‖ ≤ 1 :=
            Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hP _ _
          calc ‖restrictFix I' w' g y‖ * ∏ i : ↥I'ᶜ, ‖P i.1 (y i)‖ ≤ 1 * 1 :=
                mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = 1 := Finset.expect_const Finset.univ_nonempty _
  -- the decomposition of the expectation
  have hE : (𝔼 x : ↥Iᶜ → α, g x * ∏ i, P i (x i)) =
      ∑ w', (((unifP α).pi ↥I').prob w' : ℂ) *
        𝔼 y : ↥I'ᶜ → α, (∏ i : I', P i.1 (w' i)) *
          (restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)) := by
    rw [← cexpect_unif (κ := ↥Iᶜ), cexpect_unif_glue I']
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    refine (cexpect_unif (κ := ↥I'ᶜ) _).trans ?_
    refine Finset.expect_congr rfl fun y _ => ?_
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
    rw [hsplit]
    show g (glueFix I' w' y) * _ = _
    have : g (glueFix I' w' y) = restrictFix I' w' g y := rfl
    rw [this]
    ring
  have hsum : η ≤ ∑ w', ((unifP α).pi ↥I').prob w' * c w' := by
    refine hnorm.trans ?_
    rw [hE]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (((unifP α).pi ↥I').nonneg w')]
    refine mul_le_mul_of_nonneg_left ?_ (((unifP α).pi ↥I').nonneg w')
    rw [← Finset.mul_expect, norm_mul]
    have h2 : ‖∏ i : I', P i.1 (w' i)‖ ≤ 1 := by
      rw [norm_prod]
      refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
      exact hP _ _
    calc ‖∏ i : I', P i.1 (w' i)‖ * ‖𝔼 y : ↥I'ᶜ → α,
          restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P i.1 (y i)‖
        ≤ 1 * c w' := mul_le_mul h2 le_rfl (hc0 w') zero_le_one
      _ = c w' := one_mul _
  have hmk := prob_ge_half_of_expect_ge ((unifP α).pi ↥I') c hc0 hc1 hsum
  refine hmk.trans ?_
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
  refine (Finset.sum_le_sum (fun k hk => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => mul_nonneg (((unifP α).pi ↥I').nonneg k) (indBad_re_nonneg _ _ _ _)))
  have hk' : η / 2 ≤ c k := (Finset.mem_filter.1 hk).2
  have hbad : Bad F (η / 2) (composeSet I I') (composeVals I I' w k) := by
    refine ⟨fun j => P (composeEquiv I I' j).1, fun j a => hP _ a, ?_⟩
    have hEq : (𝔼 x : ↥(composeSet I I')ᶜ → α, restrictFix (composeSet I I')
        (composeVals I I' w k) F x * ∏ j, P (composeEquiv I I' j).1 (x j)) =
        𝔼 y : ↥I'ᶜ → α, restrictFix I' k g y * ∏ i : ↥I'ᶜ, P i.1 (y i) := by
      symm
      refine Fintype.expect_equiv
        (Equiv.arrowCongr (composeEquiv I I').symm (Equiv.refl α)) _ _ fun y => ?_
      have hy : (Equiv.arrowCongr (composeEquiv I I').symm (Equiv.refl α)) y =
          fun j => y (composeEquiv I I' j) := by
        funext j
        simp [Equiv.arrowCongr_apply]
      rw [hy, hg, restrictFix_compose I I' w k F y]
      congr 1
      exact (Fintype.prod_equiv (composeEquiv I I') (fun j => P (composeEquiv I I' j).1
        (y (composeEquiv I I' j))) (fun i => P i.1 (y i)) fun j => rfl).symm
    rw [hEq]
    exact hk'
  rw [indBad_re_of _ _ _ _ hbad, mul_one]

/-- Lemma lowering (Supplement D): if `S_π(F; ρ, η, p)` holds then
`S_π(F; ρ', η/2, pη/2)` for every `0 < ρ' ≤ ρ`; `ν`, `ν'` are the fixed-value laws at `ρ`, `ρ'`. -/
theorem goodRestr_lowering (π ν ν' : FinProb α) {ρ ρ' η p : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρ'0 : 0 < ρ') (hρ' : ρ' ≤ ρ) (hη : 0 < η)
    (hν : ∀ a, π.prob a = (1 - ρ) * ν.prob a + ρ * (1 / (Fintype.card α : ℝ)))
    (hν' : ∀ a, π.prob a = (1 - ρ') * ν'.prob a + ρ' * (1 / (Fintype.card α : ℝ)))
    (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (h : GoodRestr ν ρ η p hρ0.le hρ1.le F) :
    GoodRestr ν' ρ' (η / 2) (p * η / 2) hρ'0.le (hρ'.trans hρ1.le) F := by
  classical
  have : Nonempty α := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := ν.sum_eq_one
    simp at this
  obtain ⟨t, rfl⟩ : ∃ t, ρ' = ρ * t := ⟨ρ' / ρ, by field_simp⟩
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have ht1 : t ≤ 1 := by
    by_contra hgt
    push Not at hgt
    nlinarith
  have hbar : ∀ a, (1 - ρ * t) * ν'.prob a =
      (1 - ρ) * ν.prob a + ρ * (1 - t) * (unifP α).prob a := by
    intro a
    have e : (unifP α).prob a = 1 / (Fintype.card α : ℝ) := rfl
    rw [e]
    linear_combination hν a - hν' a
  have hnest := nested_restriction_law (ι := ι) hρ0.le hρ1.le ht0 ht1 ν (unifP α) ν' hbar
    (fun J v => indBad F (η / 2) J v)
  rw [goodRestr_iff] at h ⊢
  have key := re_nested_scaled (ι := ι) (1 - ρ) (by linarith) (by linarith) ν (η / 2)
    (fun I z => indBad F η I z)
    (fun I w => subsetExpect (ι := ↥Iᶜ) (1 - t) (by linarith) (by linarith) fun I' =>
      ((unifP α).pi ↥I').cexpect fun w' => indBad F (η / 2) (composeSet I I') (composeVals I I' w w'))
    (fun I w => by
      by_cases hb : Bad F η I w
      · rw [indBad_re_of F η I w hb, mul_one]
        exact re_subsetExpect_ge _ _ _ _ fun I' => key_inner F hF I w hb I'
      · have : (indBad F η I w).re = 0 := by
          unfold indBad
          rw [if_neg hb]
          simp
        rw [this, mul_zero]
        exact re_subsetExpect_ge _ _ _ _ fun I' => re_cexpect_ge _ _ _ fun w' =>
          indBad_re_nonneg _ _ _ _)
  rw [hnest] at key
  calc p * η / 2 = η / 2 * p := by ring
    _ ≤ η / 2 * (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (ν.pi ↥I).cexpect fun z => indBad F η I z).re :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ _ := key

/-- Corollary lowering `δ ↦ δ' ≤ δ²/2`: `S_π(F; δ, δ, δ) ⇒ S_π(F; δ', δ', δ')`. -/
theorem goodRestr_lowering_delta (π ν ν' : FinProb α) {δ δ' : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ'0 : 0 < δ') (hδ' : δ' ≤ δ ^ 2 / 2)
    (hν : ∀ a, π.prob a = (1 - δ) * ν.prob a + δ * (1 / (Fintype.card α : ℝ)))
    (hν' : ∀ a, π.prob a = (1 - δ') * ν'.prob a + δ' * (1 / (Fintype.card α : ℝ)))
    (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) (h : GoodRestr ν δ δ δ hδ0.le hδ1.le F) :
    GoodRestr ν' δ' δ' δ' hδ'0.le (by nlinarith) F := by
  have hle : δ' ≤ δ := by nlinarith
  have h1 := goodRestr_lowering π ν ν' hδ0 hδ1 hδ'0 hle hδ0 hν hν' F hF h
  exact goodRestr_mono ν' hδ'0.le (by nlinarith) F (by nlinarith) (by nlinarith) h1

end Lowering

end TrackB
end RestrictedPolynomials
end
