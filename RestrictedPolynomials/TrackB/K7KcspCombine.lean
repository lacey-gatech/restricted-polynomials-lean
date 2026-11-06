module

public import RestrictedPolynomials.TrackB.K7KcspLemma
public import RestrictedPolynomials.TrackB.K6MainUniform
public import RestrictedPolynomials.TrackB.RestrictCompose
public import RestrictedPolynomials.TrackB.MergeLayer
public import RestrictedPolynomials.TrackB.Embedding

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Apply3csp

/-- CSP_7 `lemma:kcsp#apply-3csp` (= `thm:3csp#from-K6-main`), restated: `k6_main_uniform`
at the derived law `ξ'` on three INDEPENDENT types `X Y Z` and the three slots `f₁_{J→a}`,
`conj f₂_{J→b}`, `conj g_{J→c}` of two DIFFERENT functions (`f₁ : (ι → X) → ℂ`, `f₂ : (ι → Y) → ℂ`).
`C` depends on the atom bound `α'` only; `δ` is any parameter `≤ exp(-C ε'^{-C})`; the fixing law `ν_ξ`
is chosen after `ξ'` and `δ` and before `(ι, J, a, b, c)` and `f₁, f₂, g`. The old single-type,
single-function form cannot be applied to a lifted first alphabet. -/
theorem k7_apply_3csp {α' : ℝ} (hα' : 0 < α') :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z] (ξ' : FinProb (X × Y × Z)), PairwiseConnected3 ξ'.support →
        (∀ p ∈ ξ'.support, α' ≤ ξ'.prob p) → ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
        ∀ δ : ℝ, (hδ0 : 0 < δ) → (hδ1 : δ ≤ 1) → δ ≤ Real.exp (-C * ε' ^ (-C)) →
        ∃ νξ : FinProb X,
          (∀ a, (mergePush ξ' fun p => p.1).prob a =
            (1 - δ) * νξ.prob a + δ * (1 / (Fintype.card X : ℝ))) ∧
          ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : Finset ι) (a : ↥J → X) (b : ↥J → Y)
            (c : ↥J → Z) (f₁ : (ι → X) → ℂ) (f₂ : (ι → Y) → ℂ) (g : (ι → Z) → ℂ),
            (∀ x, ‖f₁ x‖ ≤ 1) → (∀ y, ‖f₂ y‖ ≤ 1) → (∀ z, ‖g z‖ ≤ 1) →
            ε' ≤ ‖(ξ'.pi ↥Jᶜ).cexpect fun w => restrictFix J a f₁ (fun t => (w t).1) *
              star (restrictFix J b f₂ (fun t => (w t).2.1)) *
              star (restrictFix J c g (fun t => (w t).2.2))‖ →
            GoodRestr νξ δ δ δ hδ0.le hδ1 (restrictFix J a f₁) := by
  obtain ⟨C, hC1, H⟩ := k6_main_uniform hα'
  refine ⟨C, hC1, fun X Y Z _ _ _ _ _ _ ξ' hpc hat ε' hε0 hε1 δ hδ0 hδ1 hδ => ?_⟩
  obtain ⟨ν, hν, hG⟩ := H X Y Z ξ' hpc hat ε' hε0 hε1 δ hδ0 hδ1 hδ
  refine ⟨ν, hν, fun ι _ _ J a b c f₁ f₂ g hf1 hf2 hg hcorr => ?_⟩
  exact hG ↥Jᶜ (restrictFix J a f₁) (fun y => star (restrictFix J b f₂ y))
    (fun z => star (restrictFix J c g z)) (fun x => hf1 _) (fun y => by rw [norm_star]; exact hf2 _)
    (fun z => by rw [norm_star]; exact hg _) hcorr

end Apply3csp

section Combine
variable {A0 : Type} [Fintype A0] [DecidableEq A0] [Nonempty A0] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Private helpers for `k7_combine_restrictions` -/

open scoped Classical in
/-- the indicator of the restricted-correlation event inside `k7EventProb`. -/
private def k7cInd (π : FinProb A0) (F : (ι → A0) → ℂ) (η : ℝ) (J : Finset ι) (v : J → A0) : ℂ :=
  if ∃ P : ↥Jᶜ → A0 → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      η ≤ ‖(π.pi ↥Jᶜ).cexpect fun x => restrictFix J v F x * ∏ i, P i (x i)‖ then 1 else 0

omit [DecidableEq A0] [Nonempty A0] in
private theorem k7c_eventProb_eq (ν π : FinProb A0) (ρ η : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → A0) → ℂ) :
    k7EventProb ν π ρ η h0 h1 F =
      (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (ν.pi ↥I).cexpect fun z => k7cInd π F η I z).re :=
  rfl

omit [DecidableEq A0] [Nonempty A0] in
private theorem k7c_ind_re_nonneg (π : FinProb A0) (F : (ι → A0) → ℂ) (η : ℝ) (J : Finset ι)
    (v : J → A0) : 0 ≤ (k7cInd π F η J v).re := by
  unfold k7cInd
  split_ifs <;> simp

omit [DecidableEq A0] [Nonempty A0] in
private theorem k7c_ind_re_of (π : FinProb A0) (F : (ι → A0) → ℂ) (η : ℝ) (J : Finset ι)
    (v : J → A0)
    (h : ∃ P : ↥Jᶜ → A0 → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      η ≤ ‖(π.pi ↥Jᶜ).cexpect fun x => restrictFix J v F x * ∏ i, P i (x i)‖) :
    (k7cInd π F η J v).re = 1 := by
  unfold k7cInd
  rw [if_pos h]
  simp

omit [Nonempty A0] in
/-- the event for `F_{I→w}` at `(I', w')` implies the event for `F` at the composite `(I ∪ I', (w, w'))`. -/
private theorem k7c_event_compose (π : FinProb A0) (f : (ι → A0) → ℂ) (η : ℝ) (I : Finset ι)
    (w : I → A0) (I' : Finset ↥Iᶜ) (w' : I' → A0)
    (h : ∃ P : ↥I'ᶜ → A0 → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      η ≤ ‖(π.pi ↥I'ᶜ).cexpect fun y => restrictFix I' w' (restrictFix I w f) y *
        ∏ i, P i (y i)‖) :
    ∃ P : ↥(composeSet I I')ᶜ → A0 → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      η ≤ ‖(π.pi ↥(composeSet I I')ᶜ).cexpect fun x =>
        restrictFix (composeSet I I') (composeVals I I' w w') f x * ∏ i, P i (x i)‖ := by
  obtain ⟨P, hP, hn⟩ := h
  refine ⟨fun j => P (composeEquiv I I' j), fun j a => hP _ a, ?_⟩
  have hEq : ((π.pi ↥(composeSet I I')ᶜ).cexpect fun x => restrictFix (composeSet I I')
      (composeVals I I' w w') f x * ∏ j, P (composeEquiv I I' j) (x j)) =
      (π.pi ↥I'ᶜ).cexpect fun y => restrictFix I' w' (restrictFix I w f) y *
        ∏ i, P i (y i) := by
    rw [cexpect_pi_composeEquiv π I I' (fun y => restrictFix I' w' (restrictFix I w f) y *
      ∏ i, P i (y i))]
    congr 1
    funext y
    beta_reduce
    rw [restrictFix_compose I I' w w' f]
    congr 1
    exact Fintype.prod_equiv (composeEquiv I I') (fun j => P (composeEquiv I I' j) (y j))
      (fun i => P i (y ((composeEquiv I I').symm i))) fun j => by simp only [Equiv.symm_apply_apply]
  rw [hEq]
  exact hn

omit [DecidableEq A0] [Nonempty A0] in
private theorem k7c_re_cexpect_scaled {κ : Type} [Fintype κ] (P : FinProb κ) (c : ℝ)
    (f g : κ → ℂ) (h : ∀ k, c * (f k).re ≤ (g k).re) : c * (P.cexpect f).re ≤ (P.cexpect g).re := by
  unfold FinProb.cexpect
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

omit [DecidableEq A0] [Nonempty A0] in
private theorem k7c_re_cexpect_ge {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) (c : ℝ)
    (h : ∀ k, c ≤ (f k).re) : c ≤ (P.cexpect f).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
  calc c = ∑ k, P.prob k * c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

omit [DecidableEq A0] [Nonempty A0] in
private theorem k7c_re_nested_scaled {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ν : FinProb A0) (c : ℝ)
    (f g : ∀ I : Finset κ, (↥I → A0) → ℂ) (h : ∀ I z, c * (f I z).re ≤ (g I z).re) :
    c * (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (f I)).re ≤
      (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (g I)).re := by
  unfold subsetExpect
  exact k7c_re_cexpect_scaled _ c _ _ fun s =>
    k7c_re_cexpect_scaled _ c _ _ fun z => h _ z


omit [DecidableEq A0] in
/-- `lem:combined` as the hypothesis `hbar` of `k7_combine_restrictions` with `νbar := FinProb.uniform`:
if the first marginal of the fixing law of the restriction is the uniform law (`π = Ũ`), and `ξ₁' =
(1-δ) νξ + δ U`, then `(1 - ζδ) U = (1-ζ) ξ₁'' + ζ (1-δ) νξ` (linear arithmetic; no division, so
`ζ δ < 1` is not needed). -/
theorem k7_combined_law_unif (ξ1' ξ1'' νξ : FinProb A0) {ζ δ : ℝ}
    (hπ : ∀ a, (FinProb.uniform (α := A0)).prob a = (1 - ζ) * ξ1''.prob a + ζ * ξ1'.prob a)
    (hξ1' : ∀ a, ξ1'.prob a = (1 - δ) * νξ.prob a + δ * (1 / (Fintype.card A0 : ℝ))) :
    ∀ a, (1 - ζ * δ) * (FinProb.uniform (α := A0)).prob a =
      (1 - ζ) * ξ1''.prob a + ζ * (1 - δ) * νξ.prob a := by
  intro a
  have h1 := hπ a
  rw [hξ1' a] at h1
  have hu : (FinProb.uniform (α := A0)).prob a = 1 / (Fintype.card A0 : ℝ) := rfl
  rw [hu] at h1 ⊢
  linear_combination h1

open scoped Classical in
/-- CSP_7 `lemma:kcsp#combine-restrictions` (the fixing law `ν̄` is fixed before `f`; instantiate
`π := νbar := FinProb.uniform` with `k7_combined_law_unif`; checked by the `example` below). If with probability `≥ p` over `J ∼_{1-ζ}`,
`a ∼ ξ''₁^J` the restricted function `f_{J→a}` satisfies the CSP_6 event at `(νξ; δ)`, then the composite
restriction (`ν̄` at rate `ζδ`, uniform free law) satisfies the event with probability `≥ p δ`. -/
theorem k7_combine_restrictions (π ξ1' ξ1'' νξ νbar : FinProb A0) {ζ δ p : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hπ : ∀ a, π.prob a = (1 - ζ) * ξ1''.prob a + ζ * ξ1'.prob a)
    (hξ1' : ∀ a, ξ1'.prob a = (1 - δ) * νξ.prob a + δ * (1 / (Fintype.card A0 : ℝ)))
    (hbar : ∀ a, (1 - ζ * δ) * νbar.prob a =
      (1 - ζ) * ξ1''.prob a + ζ * (1 - δ) * νξ.prob a)
    (f : (ι → A0) → ℂ)
    (hout : p ≤ (subsetExpect (1 - ζ) (by linarith) (by linarith) fun J =>
      (ξ1''.pi ↥J).cexpect fun a =>
        if GoodRestr νξ δ δ δ hδ0.le hδ1 (restrictFix J a f) then (1 : ℂ) else 0).re) :
    p * δ ≤ k7EventProb νbar (FinProb.uniform (α := A0)) (ζ * δ) δ (by positivity)
      (by nlinarith [mul_pos hζ0 hδ0]) f := by
  rw [k7c_eventProb_eq]
  have hnest := nested_restriction_law (ι := ι) hζ0.le hζ1 hδ0.le hδ1 ξ1'' νξ νbar hbar
    (fun J v => k7cInd (FinProb.uniform (α := A0)) f δ J v)
  rw [← hnest]
  have key := k7c_re_nested_scaled (κ := ι) (by linarith : 0 ≤ 1 - ζ) (by linarith) ξ1'' δ
    (fun I w => if GoodRestr νξ δ δ δ hδ0.le hδ1 (restrictFix I w f) then (1 : ℂ) else 0)
    (fun I w => subsetExpect (ι := ↥Iᶜ) (1 - δ) (by linarith) (by linarith) fun I' =>
      (νξ.pi ↥I').cexpect fun w' =>
        k7cInd (FinProb.uniform (α := A0)) f δ (composeSet I I') (composeVals I I' w w'))
    (fun I w => by
      by_cases hg : GoodRestr νξ δ δ δ hδ0.le hδ1 (restrictFix I w f)
      · rw [if_pos hg, Complex.one_re, mul_one]
        have h1 := (k7_goodRestr_iff_eventProb νξ hδ0.le hδ1 (restrictFix I w f)).1 hg
        refine h1.trans ?_
        rw [k7c_eventProb_eq]
        have := k7c_re_nested_scaled (κ := ↥Iᶜ) (by linarith : 0 ≤ 1 - δ) (by linarith) νξ 1
          (fun I' z => k7cInd (FinProb.uniform (α := A0)) (restrictFix I w f) δ I' z)
          (fun I' z => k7cInd (FinProb.uniform (α := A0)) f δ (composeSet I I')
            (composeVals I I' w z))
          (fun I' z => by
            rw [one_mul]
            by_cases hb : ∃ P : ↥I'ᶜ → A0 → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
                δ ≤ ‖((FinProb.uniform (α := A0)).pi ↥I'ᶜ).cexpect fun y =>
                  restrictFix I' z (restrictFix I w f) y * ∏ i, P i (y i)‖
            · rw [k7c_ind_re_of _ _ _ _ _ hb, k7c_ind_re_of _ _ _ _ _ (k7c_event_compose _ f δ I w I' z hb)]
            · have h0 : (k7cInd (FinProb.uniform (α := A0)) (restrictFix I w f) δ I' z).re = 0 := by
                unfold k7cInd
                rw [if_neg hb]
                simp
              rw [h0]
              exact k7c_ind_re_nonneg _ _ _ _ _)
        rwa [one_mul] at this
      · rw [if_neg hg, Complex.zero_re, mul_zero]
        unfold subsetExpect
        exact k7c_re_cexpect_ge _ _ _ fun s => k7c_re_cexpect_ge _ _ _ fun w' =>
          k7c_ind_re_nonneg _ _ _ _ _)
  calc p * δ = δ * p := mul_comm _ _
    _ ≤ δ * (subsetExpect (1 - ζ) (by linarith) (by linarith) fun J =>
      (ξ1''.pi ↥J).cexpect fun a =>
        if GoodRestr νξ δ δ δ hδ0.le hδ1 (restrictFix J a f) then (1 : ℂ) else 0).re :=
        mul_le_mul_of_nonneg_left hout hδ0.le
    _ ≤ _ := key

open scoped Classical in
/-- the instantiation used by `thm:kcsp-rat` (Step 4): `π := νbar := FinProb.uniform` gives the
`(Ũ, Ũ)` event. A compile-time check that `k7_combine_restrictions` needs no change. -/
example (ξ1' ξ1'' νξ : FinProb A0) {ζ δ p : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    (hπ : ∀ a, (FinProb.uniform (α := A0)).prob a = (1 - ζ) * ξ1''.prob a + ζ * ξ1'.prob a)
    (hξ1' : ∀ a, ξ1'.prob a = (1 - δ) * νξ.prob a + δ * (1 / (Fintype.card A0 : ℝ)))
    (f : (ι → A0) → ℂ)
    (hout : p ≤ (subsetExpect (1 - ζ) (by linarith) (by linarith) fun J =>
      (ξ1''.pi ↥J).cexpect fun a =>
        if GoodRestr νξ δ δ δ hδ0.le hδ1 (restrictFix J a f) then (1 : ℂ) else 0).re) :
    p * δ ≤ k7EventProb (FinProb.uniform (α := A0)) (FinProb.uniform (α := A0)) (ζ * δ) δ
      (by positivity) (by nlinarith [mul_pos hζ0 hδ0]) f :=
  k7_combine_restrictions (FinProb.uniform (α := A0)) ξ1' ξ1'' νξ (FinProb.uniform (α := A0)) hζ0 hζ1
    hδ0 hδ1 hπ hξ1' (k7_combined_law_unif ξ1' ξ1'' νξ hπ hξ1') f hout

end Combine

section Project
variable {Ã A : Type} [Fintype Ã] [Fintype A] [DecidableEq Ã] [DecidableEq A] {ι : Type}
  [Fintype ι] [DecidableEq ι]

/-- a coordinatewise map commutes with restriction. -/
private theorem k7c_restrictFix_map (q : Ã → A) (I : Finset ι) (z : ↥I → Ã) (F : (ι → A) → ℂ)
    (w : ↥Iᶜ → Ã) :
    restrictFix I z (fun x : ι → Ã => F fun t => q (x t)) w =
      restrictFix I (fun t => q (z t)) F (fun t => q (w t)) := by
  unfold restrictFix glueFix
  beta_reduce
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [hi]

/-- expectation of a pushforward, coordinatewise. -/
private theorem k7c_pushforward_pi (π : FinProb Ã) (q : Ã → A) {κ : Type} [Fintype κ]
    [DecidableEq κ] (Φ : (κ → A) → ℂ) :
    ((π.pi κ).cexpect fun w => Φ fun t => q (w t)) =
      (((mergePush π q).pi κ).cexpect Φ) := by
  unfold FinProb.cexpect
  rw [← Finset.sum_fiberwise Finset.univ (fun w : κ → Ã => fun t => q (w t))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∀ w ∈ Finset.univ.filter (fun w : κ → Ã => (fun t => q (w t)) = u),
      ((π.pi κ).prob w : ℂ) * Φ (fun t => q (w t)) = ((π.pi κ).prob w : ℂ) * Φ u := by
    intro w hw
    rw [(Finset.mem_filter.1 hw).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  have hfib : (Finset.univ.filter fun w : κ → Ã => (fun t => q (w t)) = u) =
      Fintype.piFinset fun t => Finset.univ.filter fun b => q b = u t := by
    ext w
    simp [funext_iff, Fintype.mem_piFinset]
  rw [hfib, ← Complex.ofReal_sum]
  congr 1
  exact (Finset.prod_univ_sum (fun t => Finset.univ.filter fun b => q b = u t)
    (fun _ b => π.prob b)).symm

/-- the weighted pushforward identity: if `ψ_t` is the conditional average of `φ_t` over the fibres of
`q`, then `𝔼_{πt^κ} H(q x) ∏ φ_t(x_t) = 𝔼_{(q_* πt)^κ} H(x) ∏ ψ_t(x_t)`. -/
private theorem k7c_expect_weighted (π : FinProb Ã) (q : Ã → A) {κ : Type} [Fintype κ]
    [DecidableEq κ] (φ : κ → Ã → ℂ) (ψ : κ → A → ℂ)
    (hψ : ∀ t a, (((mergePush π q).prob a : ℝ) : ℂ) * ψ t a =
      ∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ t b)
    (H : (κ → A) → ℂ) :
    (π.pi κ).cexpect (fun x => H (fun t => q (x t)) * ∏ t, φ t (x t)) =
      ((mergePush π q).pi κ).cexpect (fun x => H x * ∏ t, ψ t (x t)) := by
  unfold FinProb.cexpect
  rw [← Finset.sum_fiberwise Finset.univ (fun w : κ → Ã => fun t => q (w t))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∀ w ∈ Finset.univ.filter (fun w : κ → Ã => (fun t => q (w t)) = u),
      ((π.pi κ).prob w : ℂ) * (H (fun t => q (w t)) * ∏ t, φ t (w t)) =
        H u * ∏ t, ((π.prob (w t) : ℂ) * φ t (w t)) := by
    intro w hw
    rw [← (Finset.mem_filter.1 hw).2, FinProb.pi_prob]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hfib : (Finset.univ.filter fun w : κ → Ã => (fun t => q (w t)) = u) =
      Fintype.piFinset fun t => Finset.univ.filter fun b => q b = u t := by
    ext w
    simp [funext_iff, Fintype.mem_piFinset]
  have hp := Finset.prod_univ_sum (fun t => Finset.univ.filter fun b => q b = u t)
    (fun t b => (π.prob b : ℂ) * φ t b)
  rw [hfib, ← hp]
  rw [Finset.prod_congr rfl fun t _ => (hψ t (u t)).symm, FinProb.pi_prob]
  push_cast
  rw [Finset.prod_mul_distrib]
  ring

/-- the conditional average `P_i(a) = πt(q⁻¹ a)⁻¹ Σ_{q ã = a} πt(ã) P̃_i(ã)`. -/
private theorem k7c_condavg (π : FinProb Ã) (q : Ã → A) (φ : Ã → ℂ) (hφ : ∀ b, ‖φ b‖ ≤ 1) (a : A) :
    ‖(∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ b) /
      (((mergePush π q).prob a : ℝ) : ℂ)‖ ≤ 1 ∧
    (((mergePush π q).prob a : ℝ) : ℂ) *
      ((∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ b) /
        (((mergePush π q).prob a : ℝ) : ℂ)) =
      ∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ b := by
  have hS : ‖∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ b‖ ≤
      (mergePush π q).prob a := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (π.nonneg b)]
    exact mul_le_of_le_one_right (π.nonneg b) (hφ b)
  by_cases h0 : (mergePush π q).prob a = 0
  · have hS0 : ∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ b = 0 := by
      have : ‖∑ b ∈ Finset.univ.filter (fun b => q b = a), (π.prob b : ℂ) * φ b‖ ≤ 0 := h0 ▸ hS
      exact norm_le_zero_iff.1 this
    rw [h0, hS0]
    simp
  · have hc : (((mergePush π q).prob a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    refine ⟨?_, by field_simp⟩
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ((mergePush π q).nonneg a)]
    rw [div_le_one (lt_of_le_of_ne ((mergePush π q).nonneg a) (Ne.symm h0))]
    exact hS

/-- `lem:project` (2), pointwise: for every `(I, z)` the event at `(I, z)` for `(F ∘ q^ι; πt)` holds iff
the event at `(I, q z)` for `(F; q_* πt)` holds, for every `η` (any law `πt`, no `1`-boundedness: the
witness is the conditional expectation `P_i(a) = πt(q⁻¹a)⁻¹ Σ_{q ã = a} πt(ã) P̃_i(ã)`, and conversely
`P̃_i = P_i ∘ q`). -/
theorem k7_event_project_iff (q : Ã → A) (πt : FinProb Ã) (η : ℝ) (F : (ι → A) → ℂ)
    (I : Finset ι) (z : ↥I → Ã) :
    (∃ P : ↥Iᶜ → Ã → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
        η ≤ ‖(πt.pi ↥Iᶜ).cexpect fun x =>
          restrictFix I z (fun x : ι → Ã => F fun t => q (x t)) x * ∏ i, P i (x i)‖) ↔
      (∃ P : ↥Iᶜ → A → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
        η ≤ ‖((mergePush πt q).pi ↥Iᶜ).cexpect fun x =>
          restrictFix I (fun t => q (z t)) F x * ∏ i, P i (x i)‖) := by
  constructor
  · rintro ⟨P', hP', hη⟩
    refine ⟨fun i a => (∑ b ∈ Finset.univ.filter (fun b => q b = a), (πt.prob b : ℂ) * P' i b) /
      (((mergePush πt q).prob a : ℝ) : ℂ), fun i a => (k7c_condavg πt q (P' i) (hP' i) a).1, ?_⟩
    have hw := k7c_expect_weighted πt q (fun (i : ↥Iᶜ) => P' i)
      (fun i a => (∑ b ∈ Finset.univ.filter (fun b => q b = a), (πt.prob b : ℂ) * P' i b) /
        (((mergePush πt q).prob a : ℝ) : ℂ))
      (fun i a => (k7c_condavg πt q (P' i) (hP' i) a).2)
      (restrictFix I (fun t => q (z t)) F)
    simp only [k7c_restrictFix_map] at hη
    rw [hw] at hη
    exact hη
  · rintro ⟨P, hP, hη⟩
    refine ⟨fun i b => P i (q b), fun i b => hP i _, ?_⟩
    have hw := k7c_pushforward_pi πt q (κ := ↥Iᶜ)
      (fun x => restrictFix I (fun t => q (z t)) F x * ∏ i, P i (x i))
    simp only [k7c_restrictFix_map]
    rw [hw]
    exact hη

/-- `lem:project` (3): `Ev_{πt,πt}(F ∘ q^ι; ρ, η) = Ev_{π,π}(F; ρ, η)` for `π = q_* πt`, every `F`,
every law `πt`, every `ρ, η`. With `q_* Ũ = μ₁` (`k7_lift_pushU`) this is the `(μ₁, μ₁)` event of
`lemma:kcsp` with `(c, C) = (1, 1)`. -/
theorem k7_event_project (q : Ã → A) (πt : FinProb Ã) {ρ η : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → A) → ℂ) :
    k7EventProb πt πt ρ η h0 h1 (fun x : ι → Ã => F fun t => q (x t)) =
      k7EventProb (mergePush πt q) (mergePush πt q) ρ η h0 h1 F := by
  classical
  unfold k7EventProb
  have hI : ∀ I : Finset ι,
      ((πt.pi ↥I).cexpect fun z =>
        if ∃ P : ↥Iᶜ → Ã → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
          η ≤ ‖(πt.pi ↥Iᶜ).cexpect fun x =>
            restrictFix I z (fun x : ι → Ã => F fun t => q (x t)) x * ∏ i, P i (x i)‖
          then (1 : ℂ) else 0) =
      ((mergePush πt q).pi ↥I).cexpect fun z =>
        if ∃ P : ↥Iᶜ → A → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
          η ≤ ‖((mergePush πt q).pi ↥Iᶜ).cexpect fun x =>
            restrictFix I z F x * ∏ i, P i (x i)‖
          then (1 : ℂ) else 0 := by
    intro I
    rw [← k7c_pushforward_pi πt q (κ := ↥I)]
    congr 1
    funext z
    exact if_congr (k7_event_project_iff q πt η F I z) rfl rfl
  simp only [hI]

end Project

end TrackB
end RestrictedPolynomials
end
