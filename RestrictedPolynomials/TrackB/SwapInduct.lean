module

public import RestrictedPolynomials.TrackB.SwapSvdCalculus
public import RestrictedPolynomials.TrackB.SwapIterScheme
public import RestrictedPolynomials.TrackB.SwapTlarge
public import RestrictedPolynomials.TrackB.SwapSvdInc
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.TrackB.SwapInductAux

/-!
# Track B: the induction of `thm:swap` (CSP_6)

Source: CSP6 (arXiv:2411.15133v1 `main.tex`) L353-358 (`thm:swap`), L1136-1170 (its proof:
`eq:inductswap`, the base case `ε ≥ 0.99`, Case 1 and Case 2 recursions, the closure of the
induction, the recursion solution and the passage from expectation to probability).
Covers CSP_6 `thm:swap` with `#base-case-99`, `#case1-recursion`, `#case2-recursion`,
`#induction-closure`, `#recursion-solution`, `#expectation-to-probability`, and `eq:inductswap`.

Readings of the source used here:
* the induction claim is proved in the family form `∀ ρ ≤ ρ₀` (density free below `ρ₀`);
* the potential of the scheme carries the weight `θ = 2·10⁻¹²`, so that both
  recursions give `ε' = ε + θε⁴/4`;
* the explicit absolute constants are `c = 10⁻¹³`, `γ = c²ε⁸`, `T = ⌈8/γ²⌉`, `x = γ²θε⁵/18`;
* the outcomes of `lemma:tlarge` are split into the `3T` classes `R(τ₀)`, `H1(τ₀)`, `H2(τ₀)`
  (the live set of the recursion is `R_τ₀`, `S_τ₀`, `T_τ₀`), each class carrying its own law
  identity at the density `2^{τ₀}ρ` resp. `2^{τ₀+1}ρ`; the inequality is summed over the classes
  (a pigeonhole in summed form);
* the quantitative form is `(ε/(2B))^{K⌈1/ε⌉^K}` with an absolute `K`, and one `δ` for density,
  threshold and probability in `swap_theorem`.

Route of `swap_theorem` (the printed `s ≤ ‖f_{I→z}‖₂ ≤ 1` is false for `B > √2`):
here the pointwise bound `s ≤ B` is used, `𝔼 s ≤ B·Pr[s ≥ δ₀/2] + δ₀/2`, with
`δ := min(ρ₀, δ₀/(2B), δ₀/4)` and `K' = K + 2` (statement unchanged).
The proof infrastructure is in `SwapInductAux.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapInduct
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|⟨u, ∏ᵢ Pᵢ⟩|`. -/
def swapProdCorr {κ : Type} [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) (P : κ → α → ℂ) : ℝ :=
  ‖𝔼 x : κ → α, u x * star (∏ i, P i (x i))‖

/-- `sup { |⟨u, ∏ Pᵢ⟩| : ‖Pᵢ‖₂ ≤ 1 }`. -/
def swapCorrSup {κ : Type} [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ P : κ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧ r = swapProdCorr u P}

/-- `𝔼_{I ∼_{1-ρ} [n], z ∼ U(Σ^I)} sup_P |⟨f_{I→z}, ∏ Pᵢ⟩|` (`I` fixed, live density `ρ`). -/
def swapRestrExp [Nonempty α] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f : (ι → α) → ℂ) : ℝ :=
  (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
    ((FinProb.uniform (α := α)).pi ↥I).cexpect fun z =>
      ((swapCorrSup (restrictFix I z f) : ℝ) : ℂ)).re

/-- the absolute constants of the recursion (see the module docstring). -/
def swapC : ℝ := 1 / 10 ^ 13
def swapTheta : ℝ := 2 / 10 ^ 12
def swapGamma (ε : ℝ) : ℝ := swapC ^ 2 * ε ^ 8
def swapT (ε : ℝ) : ℕ := ⌈8 / swapGamma ε ^ 2⌉₊
def swapX (ε : ℝ) : ℝ := swapGamma ε ^ 2 * swapTheta * ε ^ 5 / 18
def swapEpsNext (ε : ℝ) : ℝ := ε + swapTheta * ε ^ 4 / 4
def swapBNext (ε B : ℝ) : ℝ := 27 * B / (swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε))
def swapRhoNext (ε ρ₁ : ℝ) : ℝ := ρ₁ / 2 ^ swapT ε
def swapPGood (ε B : ℝ) : ℝ :=
  (swapGamma ε ^ 4 * swapX ε ^ swapT ε * ε ^ 2 * (swapTheta * ε ^ 5) / (36 * B ^ 2)) ^ swapT ε
def swapDeltaNext (ε B δ' : ℝ) : ℝ :=
  swapPGood ε B / (3 * swapT ε) * (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B))

/-! ### `swapRestrExp` through the correlations `swapIndCorr` of the ambient cube -/

/-- `swapRestrExp` as the law of one coordinate-wise restriction (`swapFixLaw`). -/
private theorem si_restrExp_fixLaw [Nonempty α] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → α) → ℂ) :
    swapRestrExp ρ h0 h1 F = ((swapFixLaw ρ h0 h1).pi ι).expect (fun s =>
      swapIndCorr (swapFixLive s) (swapIterFun F (swapFixLive s) (swapFixZ s))) := by
  rw [swapInd_fixLaw_expect ρ h0 h1 (fun L z => swapIndCorr L (swapIterFun F L z))]
  unfold swapRestrExp
  congr 2
  funext I
  congr 1
  funext z
  congr 1
  rw [swapIndCorr_eq_subtype Iᶜ _ (swapInd_iterFun_dep F Iᶜ _) (fun _ => Classical.arbitrary α)]
  unfold swapCorrSup swapProdCorr
  have hpt : ∀ y : ↥Iᶜ → α, swapIterFun F Iᶜ
      (fun i => if h : i ∈ I then z ⟨i, h⟩ else Classical.arbitrary α)
      (glueFree Iᶜ y (fun _ => Classical.arbitrary α)) = restrictFix I z F y := by
    intro y
    unfold swapIterFun restrictFix
    congr 1
    funext i
    by_cases hi : i ∈ I
    · simp [glueFix, hi]
    · simp [glueFix, glueFree, hi]
  simp_rw [hpt]

/-- `swapRestrExp` with the fixing `w` and the live coins `b` drawn separately. -/
private theorem si_restrExp_bw [Nonempty α] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → α) → ℂ) :
    swapRestrExp ρ h0 h1 F = 𝔼 w : ι → α, ((bernoulli ρ h0 h1).pi ι).expect (fun b =>
      swapIndCorr (swapIterLive univ b) (swapIterFun F (swapIterLive univ b) w)) := by
  rw [si_restrExp_fixLaw, ← swapIterRun_law_R F (K := 0) (t := 0) le_rfl h0 h1 h0 h1 (by simp)
    swapIndCorr]
  have h : ∀ (c₀ : SwapCoins ι α) (ω : Fin 0 → SwapCoins ι α),
      (𝔼 w : ι → α, ((bernoulli ρ h0 h1).pi ι).expect (fun b =>
        swapIndCorr (swapIterLive (swapIterRun c₀ ω 0).R b)
          (swapIterFun F (swapIterLive (swapIterRun c₀ ω 0).R b)
            (swapIterZ (swapIterRun c₀ ω 0) (swapIterLive (swapIterRun c₀ ω 0).R b) w)))) =
      𝔼 w : ι → α, ((bernoulli ρ h0 h1).pi ι).expect (fun b =>
        swapIndCorr (swapIterLive univ b) (swapIterFun F (swapIterLive univ b) w)) := by
    intro c₀ ω
    refine Finset.expect_congr rfl fun w _ => FinProb.expect_congr _ fun b => ?_
    have e : swapIterFun F (swapIterLive univ b)
        (swapIterZ (swapIterRun c₀ ω 0) (swapIterLive univ b) w) =
        swapIterFun F (swapIterLive univ b) w := by
      funext x
      unfold swapIterFun
      congr 1
      funext i
      by_cases hi : i ∈ swapIterLive univ b
      · simp [hi]
      · simp [hi, swapIterZ, swapIterRun, swapIterInit]
    show swapIndCorr (swapIterLive univ b)
        (swapIterFun F (swapIterLive univ b)
          (swapIterZ (swapIterRun c₀ ω 0) (swapIterLive univ b) w)) = _
    rw [e]
  simp_rw [h]
  rw [Fintype.expect_const, Fintype.expect_const]

/-- for a function of the coordinates of `A`, `swapRestrExp` is at most the average over restrictions
whose live set is taken inside `A`. -/
private theorem si_restrExp_le_base [Nonempty α] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (F : (ι → α) → ℂ) (A : Finset ι) (hF : SwapDependsOn A F) :
    swapRestrExp ρ h0 h1 F ≤ 𝔼 w : ι → α, ((bernoulli ρ h0 h1).pi ι).expect (fun b =>
      swapIndCorr (swapIterLive A b) (swapIterFun F (swapIterLive A b) w)) := by
  rw [si_restrExp_bw]
  refine Finset.expect_le_expect fun w _ => FinProb.expect_mono _ fun b => ?_
  have e : swapIterFun F (swapIterLive univ b) w = swapIterFun F (swapIterLive A b) w := by
    funext x
    unfold swapIterFun
    refine hF _ _ fun i hi => ?_
    by_cases hb : b i = true <;> simp [swapIterLive, hi, hb]
  rw [e]
  refine swapIndCorr_mono (fun i hi => ?_) (swapInd_iterFun_dep F _ w)
  simp only [swapIterLive, mem_filter] at hi ⊢
  exact ⟨mem_univ i, hi.2⟩

/-! ### The base case -/

/-- CSP_6 `thm:swap#base-case-99` for one live set `L`. -/
private theorem si_base_L [Nonempty α] {ε B : ℝ} (hB0 : 0 < B) (hε : 99 / 100 ≤ ε)
    (f : (ι → α) → ℂ) (hB : ∀ x, ‖f x‖ ≤ B) (hl2 : l2sq f ≤ 1)
    (hv : ε ^ 4 ≤ (val f f f f).re) (L : Finset ι) :
    (3 / 4) / B ≤ 𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) := by
  have hε4 : (99 / 100 : ℝ) ^ 4 ≤ ε ^ 4 := pow_le_pow_left₀ (by norm_num) hε 4
  obtain ⟨P, hP1, hP⟩ := swapNine f (c := 1 - ε ^ 4) (by norm_num at hε4; linarith) hl2
    (by linarith)
  have hPa : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1 := fun i => (hP1 i).le
  have h88 : 88 / 100 ≤ 1 - 3 * (1 - ε ^ 4) := by norm_num at hε4; linarith
  -- split the coordinates into `L` and `Lᶜ`
  have hsplit : 𝔼 x : ι → α, f x * star (∏ i, P i (x i)) =
      𝔼 w : ι → α, star (∏ i ∈ Lᶜ, P i (w i)) *
        𝔼 x : ι → α, swapIterFun f L w x * star (∏ i ∈ L, P i (x i)) := by
    rw [← expect_expect_piecewise L (fun x => f x * star (∏ i, P i (x i))),
      Finset.expect_comm]
    refine Finset.expect_congr rfl fun w _ => ?_
    rw [Finset.mul_expect]
    refine Finset.expect_congr rfl fun x _ => ?_
    have h1 : ∏ i, P i (L.piecewise x w i) = (∏ i ∈ L, P i (x i)) * ∏ i ∈ Lᶜ, P i (w i) := by
      rw [← Finset.prod_mul_prod_compl L]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by simp [hi]
      · exact Finset.prod_congr rfl fun i hi => by simp [mem_compl.1 hi]
    have h2 : f (L.piecewise x w) = swapIterFun f L w x := by
      unfold swapIterFun
      congr 1
    rw [h1, h2, star_mul']
    ring
  have hC0 : ∀ w, 0 ≤ swapIndCorr L (swapIterFun f L w) := fun w => swapIndCorr_nonneg _ _
  have hCB : ∀ w, swapIndCorr L (swapIterFun f L w) ≤ B := fun w =>
    swapIndCorr_le_bound _ _ hB0.le fun x => hB _
  have hQ : 𝔼 w : ι → α, ‖star (∏ i ∈ Lᶜ, P i (w i))‖ ^ 2 ≤ 1 := by
    have e : ∀ w : ι → α, ‖star (∏ i ∈ Lᶜ, P i (w i))‖ ^ 2 = ∏ i ∈ Lᶜ, ‖P i (w i)‖ ^ 2 := by
      intro w
      rw [norm_star, norm_prod, Finset.prod_pow]
    simp_rw [e]
    exact swapInd_expect_prod_sq_le P hPa Lᶜ
  have hle : 88 / 100 ≤ 𝔼 w : ι → α,
      ‖star (∏ i ∈ Lᶜ, P i (w i))‖ * swapIndCorr L (swapIterFun f L w) := by
    refine h88.trans (hP.trans ?_)
    rw [hsplit]
    refine (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le_expect fun w _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (le_swapIndCorr P hPa) (norm_nonneg _)
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq univ (fun w : ι → α => ‖star (∏ i ∈ Lᶜ, P i (w i))‖)
    (fun w => swapIndCorr L (swapIterFun f L w))
  have hsq : 𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) ^ 2 ≤
      B * 𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) := by
    rw [Finset.mul_expect]
    refine Finset.expect_le_expect fun w _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hCB w) (hC0 w)
  have hE0 : 0 ≤ 𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) ^ 2 :=
    Finset.expect_nonneg fun w _ => sq_nonneg _
  have h1 : (88 / 100 : ℝ) ^ 2 ≤ B * 𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) := by
    calc (88 / 100 : ℝ) ^ 2 ≤ (𝔼 w : ι → α,
          ‖star (∏ i ∈ Lᶜ, P i (w i))‖ * swapIndCorr L (swapIterFun f L w)) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) hle 2
      _ ≤ (𝔼 w : ι → α, ‖star (∏ i ∈ Lᶜ, P i (w i))‖ ^ 2) *
          𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) ^ 2 := hcs
      _ ≤ 1 * 𝔼 w : ι → α, swapIndCorr L (swapIterFun f L w) ^ 2 :=
          mul_le_mul_of_nonneg_right hQ hE0
      _ ≤ _ := by rw [one_mul]; exact hsq
  rw [div_le_iff₀ hB0]
  nlinarith

/-- CSP_6 `thm:swap#base-case-99` (all densities `ρ`, correlation `≥ (3/4)/B`). -/
theorem swap_base_case {ε B : ℝ} (hB0 : 0 < B) (hε : 99 / 100 ≤ ε) [Nonempty α] (ρ : ℝ)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f : (ι → α) → ℂ) (hB : ∀ x, ‖f x‖ ≤ B) (hl2 : l2sq f ≤ 1)
    (hv : ε ^ 4 ≤ (val f f f f).re) :
    (3 / 4) / B ≤ swapRestrExp ρ h0 h1 f := by
  rw [si_restrExp_bw, swapInd_expect_comm]
  exact FinProb.const_le_expect _ fun b => si_base_L hB0 hε f hB hl2 hv _

/-! ### The constants of the recursion -/

private theorem si_c_pos : 0 < swapC := by unfold swapC; norm_num

private theorem si_c_le_one : swapC ≤ 1 := by unfold swapC; norm_num

private theorem si_θ_pos : 0 < swapTheta := by unfold swapTheta; norm_num

private theorem si_θ_le : swapTheta ≤ 1 := by unfold swapTheta; norm_num

private theorem si_γ_pos {ε : ℝ} (hε : 0 < ε) : 0 < swapGamma ε := by
  unfold swapGamma
  have := si_c_pos
  positivity

private theorem si_γ_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : swapGamma ε ≤ 1 := by
  unfold swapGamma swapC
  have h8 : ε ^ 8 ≤ 1 := pow_le_one₀ hε0.le hε1
  calc (1 / 10 ^ 13 : ℝ) ^ 2 * ε ^ 8 ≤ (1 / 10 ^ 13) ^ 2 * 1 := by gcongr
    _ ≤ 1 := by norm_num

private theorem si_γ_lt {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : swapGamma ε < ε ^ 2 := by
  unfold swapGamma swapC
  have h8 : ε ^ 8 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h2 : 0 < ε ^ 2 := by positivity
  calc (1 / 10 ^ 13 : ℝ) ^ 2 * ε ^ 8 ≤ (1 / 10 ^ 13) ^ 2 * ε ^ 2 := by gcongr
    _ < ε ^ 2 := by nlinarith

private theorem si_T_ge (ε : ℝ) : 8 / swapGamma ε ^ 2 ≤ (swapT ε : ℝ) := Nat.le_ceil _

private theorem si_T_pos {ε : ℝ} (hε0 : 0 < ε) : 0 < swapT ε := by
  have h : (0 : ℝ) < 8 / swapGamma ε ^ 2 := by
    have := si_γ_pos hε0
    positivity
  exact_mod_cast h.trans_le (si_T_ge ε)

private theorem si_t_small {ε : ℝ} (hε0 : 0 < ε) {t : ℕ} (ht : t < swapT ε) :
    (t : ℝ) * (swapC ^ 4 * ε ^ 16) ≤ 9 := by
  have h := Nat.lt_ceil.1 ht
  have hγ := si_γ_pos hε0
  have e : swapGamma ε ^ 2 = swapC ^ 4 * ε ^ 16 := by unfold swapGamma; ring
  rw [lt_div_iff₀ (by positivity), e] at h
  linarith

private theorem si_X_eq {ε : ℝ} (hε : 0 < ε) :
    swapGamma ε ^ 2 / (18 * (swapTheta * ε ^ 5)⁻¹) = swapX ε := by
  unfold swapX
  have := si_θ_pos
  field_simp

private theorem si_X_pos {ε : ℝ} (hε0 : 0 < ε) : 0 < swapX ε := by
  unfold swapX
  have := si_γ_pos hε0
  have := si_θ_pos
  positivity

private theorem si_X_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : swapX ε ≤ 1 := by
  unfold swapX
  have hγ0 := si_γ_pos hε0
  have hγ2 : swapGamma ε ^ 2 ≤ 1 := pow_le_one₀ hγ0.le (si_γ_le hε0 hε1)
  have h5 : ε ^ 5 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hθ0 := si_θ_pos
  have hθ := si_θ_le
  calc swapGamma ε ^ 2 * swapTheta * ε ^ 5 / 18 ≤ 1 * 1 * 1 / 18 := by gcongr
    _ ≤ 1 := by norm_num

private theorem si_XT_pos {ε : ℝ} (hε0 : 0 < ε) : 0 < swapX ε ^ swapT ε :=
  pow_pos (si_X_pos hε0) _

private theorem si_XT_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : swapX ε ^ swapT ε ≤ 1 :=
  pow_le_one₀ (si_X_pos hε0).le (si_X_le hε0 hε1)

private theorem si_eps_ge {ε : ℝ} (hε0 : 0 < ε) : ε ≤ swapEpsNext ε := by
  unfold swapEpsNext
  have := si_θ_pos
  have : 0 ≤ swapTheta * ε ^ 4 / 4 := by positivity
  linarith

private theorem si_eps_sq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    swapEpsNext ε ^ 2 ≤ ε ^ 2 + swapTheta * ε ^ 5 := by
  unfold swapEpsNext swapTheta
  have h8 : ε ^ 8 ≤ ε ^ 5 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h5 : 0 ≤ ε ^ 5 := by positivity
  have e : (ε + 2 / 10 ^ 12 * ε ^ 4 / 4) ^ 2 =
      ε ^ 2 + 2 / 10 ^ 12 * ε ^ 5 / 2 + (2 / 10 ^ 12) ^ 2 * ε ^ 8 / 16 := by ring
  rw [e]
  nlinarith

private theorem si_eps_le_99 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100) :
    swapEpsNext ε ^ 2 ≤ 99 / 100 := by
  have h4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le (by linarith)
  have hle : swapEpsNext ε ≤ 99 / 100 + 1 / 10 ^ 12 := by
    unfold swapEpsNext swapTheta
    nlinarith
  have h0 : 0 ≤ swapEpsNext ε := (hε0.le).trans (si_eps_ge hε0)
  nlinarith

private theorem si_eps_le_one {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100) : swapEpsNext ε ≤ 1 := by
  have h4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le (by linarith)
  unfold swapEpsNext swapTheta
  nlinarith

/-! ### Facts on the run of the scheme -/

private theorem si_NV0 {ε : ℝ} (hε0 : 0 < ε) (f : (ι → α) → ℂ) (hl2 : l2sq f ≤ 1)
    (hv : ε ^ 4 ≤ (val f f f f).re) (c₀ : SwapCoins ι α) {K : ℕ}
    (ω : Fin K → SwapCoins ι α) : ε ^ 2 ≤ swapIterNV f (swapIterRun c₀ ω 0) := by
  unfold swapIterNV
  rw [swapInd_F_init]
  have hv2 := swapInd_v2 hε0 f hv
  have hL := swapInd_l2 hε0 f hv
  have hLpos : 0 < l2sq f := lt_of_lt_of_le (by positivity) hL
  rw [le_div_iff₀ hLpos]
  have : ε ^ 2 * l2sq f ≤ ε ^ 2 := by
    have := sq_nonneg ε
    nlinarith
  linarith

/-! ### The claim `(inductswap)` in the family form, and the value of one class -/

/-- the claim `(inductswap)` at `(ε, B)` in the family form: density `≤ ρ₀`, bound `δ`. -/
private def SiClaim (ε B ρ₀ δ : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → α) → ℂ), (∀ x, ‖f x‖ ≤ B) → l2sq f ≤ 1 →
    ε ^ 4 ≤ (val f f f f).re →
    ∀ (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), ρ ≤ ρ₀ → δ ≤ swapRestrExp ρ h0 h1 f

/-- `ε √(x^T) ≤ ‖f_τ‖₂` and the bound `‖·‖∞ ≤ 27B/(c⁷ε²⁸‖f_τ‖₂) ≤ B'`. -/
private theorem si_sqrt_bounds {ε B L : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεB : ε ≤ B)
    (hL : swapX ε ^ swapT ε * ε ^ 2 ≤ L) :
    ε * swapX ε ^ swapT ε ≤ Real.sqrt L ∧ ε * Real.sqrt (swapX ε ^ swapT ε) ≤ Real.sqrt L ∧
      27 * B / (swapC ^ 7 * ε ^ 28 * Real.sqrt L) ≤ swapBNext ε B ∧
      B / Real.sqrt L ≤ swapBNext ε B := by
  have hx0 := si_XT_pos hε0
  have hx1 := si_XT_le hε0 hε1
  have hc0 := si_c_pos
  have hc1 := si_c_le_one
  have hB0 : 0 < B := hε0.trans_le hεB
  have hsx : swapX ε ^ swapT ε ≤ Real.sqrt (swapX ε ^ swapT ε) := by
    have h1 := Real.mul_self_sqrt hx0.le
    have h2 : Real.sqrt (swapX ε ^ swapT ε) ≤ 1 := Real.sqrt_le_one.2 hx1
    have h3 := Real.sqrt_nonneg (swapX ε ^ swapT ε)
    nlinarith
  have h2 : ε * Real.sqrt (swapX ε ^ swapT ε) ≤ Real.sqrt L := by
    have e : ε * Real.sqrt (swapX ε ^ swapT ε) = Real.sqrt (swapX ε ^ swapT ε * ε ^ 2) := by
      rw [Real.sqrt_mul hx0.le, Real.sqrt_sq hε0.le, mul_comm]
    rw [e]
    exact Real.sqrt_le_sqrt hL
  have hsx0 : 0 < Real.sqrt (swapX ε ^ swapT ε) := Real.sqrt_pos.2 hx0
  have hs0 : 0 < Real.sqrt L := lt_of_lt_of_le (by positivity) h2
  have hden : swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) ≤
      swapC ^ 7 * ε ^ 28 * Real.sqrt L := by
    calc swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) =
        swapC ^ 7 * ε ^ 28 * (ε * Real.sqrt (swapX ε ^ swapT ε)) := by ring
      _ ≤ swapC ^ 7 * ε ^ 28 * Real.sqrt L := by gcongr
  refine ⟨?_, h2, ?_, ?_⟩
  · calc ε * swapX ε ^ swapT ε ≤ ε * Real.sqrt (swapX ε ^ swapT ε) := by gcongr
      _ ≤ Real.sqrt L := h2
  · unfold swapBNext
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  · have hc7 : swapC ^ 7 * ε ^ 28 ≤ 1 := by
      have : swapC ^ 7 ≤ 1 := pow_le_one₀ hc0.le hc1
      have : ε ^ 28 ≤ 1 := pow_le_one₀ hε0.le hε1
      nlinarith [pow_pos hc0 7, pow_pos hε0 28]
    unfold swapBNext
    calc B / Real.sqrt L = 27 * B / (27 * Real.sqrt L) := by field_simp
      _ ≤ 27 * B / (swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε)) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) (hden.trans ?_)
          have : 0 ≤ Real.sqrt L := hs0.le
          nlinarith

/-- the value of a class `R(τ₀)`: the restricted run, renormalised, satisfies the induction
hypothesis, so `X ≥ ‖f_τ‖₂ δ' ≥ V`. -/
private theorem si_value_R [Nonempty α] {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100)
    (hεB : ε ≤ B) (hδ' : 0 < δ') (hIH : SiClaim (swapEpsNext ε) (swapBNext ε B) ρ₁ δ')
    (f : (ι → α) → ℂ) (hB : ∀ x, ‖f x‖ ≤ B) (st : SwapIterState ι α)
    (hNV : swapEpsNext ε ^ 2 ≤ swapIterNV f st)
    (hL : swapX ε ^ swapT ε * ε ^ 2 ≤ l2sq (swapIterF f st))
    (ρ' : ℝ) (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1) (hρ' : ρ' ≤ ρ₁) :
    swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B) ≤
      𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
        swapIndCorr (swapIterLive st.R b)
          (swapIterFun f (swapIterLive st.R b) (swapIterZ st (swapIterLive st.R b) w))) := by
  have hε1' : ε ≤ 1 := by linarith
  have hB0 : 0 < B := hε0.trans_le hεB
  obtain ⟨hsL, -, -, hBf⟩ := si_sqrt_bounds hε0 hε1' hεB hL
  have hx0 := si_XT_pos hε0
  have hLpos : 0 < l2sq (swapIterF f st) := lt_of_lt_of_le (by positivity) hL
  set F := swapIterF f st with hF
  set s := Real.sqrt (l2sq F) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hLpos
  have hss : s ^ 2 = l2sq F := Real.sq_sqrt hLpos.le
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  set g : (ι → α) → ℂ := fun x => (s : ℂ)⁻¹ * F x with hg
  have hFg : ∀ x, F x = (s : ℂ) * g x := fun x => by
    rw [hg]
    field_simp
  have hnk : ‖((s : ℂ)⁻¹)‖ = s⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  -- the induction hypothesis applies to `g`
  have hgB : ∀ x, ‖g x‖ ≤ swapBNext ε B := by
    intro x
    rw [hg, norm_mul, hnk]
    calc s⁻¹ * ‖F x‖ ≤ s⁻¹ * B := mul_le_mul_of_nonneg_left (hB _) (by positivity)
      _ = B / s := by ring
      _ ≤ swapBNext ε B := hBf
  have hgl : l2sq g = 1 := by
    rw [hg, swapInd_l2sq_smul, hnk, inv_pow, hss, inv_mul_cancel₀ hLpos.ne']
  have hgv : swapEpsNext ε ^ 4 ≤ (val g g g g).re := by
    rw [hg, swapInd_val_smul, Complex.re_ofReal_mul, hnk]
    have hNV2 : (swapEpsNext ε ^ 2) ^ 2 ≤ (val F F F F).re / l2sq F ^ 2 := by
      rw [← swapInd_NV_sq]
      exact pow_le_pow_left₀ (by positivity) hNV 2
    have e : s⁻¹ ^ 4 = (l2sq F ^ 2)⁻¹ := by rw [← hss]; ring
    rw [e, ← div_eq_inv_mul]
    calc swapEpsNext ε ^ 4 = (swapEpsNext ε ^ 2) ^ 2 := by ring
      _ ≤ _ := hNV2
  have hgdep : SwapDependsOn st.R g := fun x y h => by
    simp only [hg]
    congr 1
    exact swapInd_F_dep f st x y h
  have hIHg := hIH α ι g hgB hgl.le hgv ρ' h0' h1' hρ'
  have hbase := si_restrExp_le_base ρ' h0' h1' g st.R hgdep
  -- the value
  have hX : s * δ' ≤ 𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
      swapIndCorr (swapIterLive st.R b)
        (swapIterFun f (swapIterLive st.R b) (swapIterZ st (swapIterLive st.R b) w))) := by
    calc s * δ' ≤ s * 𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
          swapIndCorr (swapIterLive st.R b) (swapIterFun g (swapIterLive st.R b) w)) :=
          mul_le_mul_of_nonneg_left (hIHg.trans hbase) hs0.le
      _ = 𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
          s * swapIndCorr (swapIterLive st.R b) (swapIterFun g (swapIterLive st.R b) w)) := by
          rw [Finset.mul_expect]
          refine Finset.expect_congr rfl fun w _ => ?_
          rw [FinProb.expect_const_mul]
      _ ≤ _ := by
          refine Finset.expect_le_expect fun w _ => FinProb.expect_mono _ fun b => ?_
          rw [swapInd_fun_Z f st (swapIterLive st.R b) (filter_subset _ _) w, ← hF]
          have e : swapIterFun F (swapIterLive st.R b) w =
              fun x => (s : ℂ) * swapIterFun g (swapIterLive st.R b) w x := by
            funext x
            unfold swapIterFun
            rw [hFg]
          rw [e]
          exact swapIndCorr_mul _ _ hs0
  refine le_trans ?_ hX
  have hc0 := si_c_pos
  have hcε : swapC ^ 9 * ε ^ 38 ≤ 162 * B := by
    have h1 : swapC ^ 9 ≤ 1 := pow_le_one₀ hc0.le si_c_le_one
    have h2 : ε ^ 37 ≤ 1 := pow_le_one₀ hε0.le hε1'
    have h3 : ε ^ 38 ≤ ε := by
      calc ε ^ 38 = ε ^ 37 * ε := by ring
        _ ≤ 1 * ε := by gcongr
        _ = ε := one_mul ε
    have h4 : swapC ^ 9 * ε ^ 38 ≤ 1 * ε := mul_le_mul h1 h3 (by positivity) zero_le_one
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' =
      (swapC ^ 9 * ε ^ 38) * (ε * swapX ε ^ swapT ε) * δ' := by ring
    _ ≤ (162 * B) * s * δ' := by gcongr
    _ = s * δ' * (162 * B) := by ring

/-- the value of a class `H1(τ₀)` / `H2(τ₀)`: `lemma:svdinc` produces a unit function `u` on the live
part `A` (`S_τ` or `T_τ`) with a larger swap value, which satisfies the induction hypothesis, and the
identity of item 1 / item 2 transfers its correlations to `f`: `X ≥ ‖η‖ ‖f_τ‖₂ δ'/‖v‖_∞ ≥ V`. -/
private theorem si_value_H [Nonempty α] {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100)
    (hεB : ε ≤ B) (hδ' : 0 < δ') (hIH : SiClaim (swapEpsNext ε) (swapBNext ε B) ρ₁ δ')
    (f : (ι → α) → ℂ) (st : SwapIterState ι α)
    (A A' : Finset ι) (hAA : ∀ i ∈ A, i ∉ A') (hAR : A ⊆ st.R)
    (hRAA : ∀ i ∈ st.R, i ∈ A ∨ i ∈ A')
    (hL : swapX ε ^ swapT ε * ε ^ 2 ≤ l2sq (swapIterF f st))
    (hNV : ε ^ 2 - swapTheta * ε ^ 5 ≤ swapIterNV f st)
    (u v : (ι → α) → ℂ) (η : ℂ) (hu1 : l2sq u = 1)
    (hub : ∀ x, ‖u x‖ ≤ 27 * B / (swapC ^ 7 * ε ^ 28 * Real.sqrt (l2sq (swapIterF f st))))
    (hvb : ∀ x, ‖v x‖ ≤ 27 * B / (swapC ^ 7 * ε ^ 28 * Real.sqrt (l2sq (swapIterF f st))))
    (hη : swapC ^ 2 * ε ^ 9 / 6 ≤ ‖η‖) (hudep : SwapDependsOn A u) (hvdep : SwapDependsOn A' v)
    (huval : (1 + ε ^ 2 / 10 ^ 11) * ((val (swapIterF f st) (swapIterF f st) (swapIterF f st)
      (swapIterF f st)).re / l2sq (swapIterF f st) ^ 2) ≤ (val u u u u).re)
    (hid : ∀ I : Finset ι, I ⊆ A → ∀ (z : ι → α) (P : (ι → α) → ℂ), SwapDependsOn (A \ I) P →
      uinner (fun x => swapIterF f st (swapFixAt I z x)) (fun x => P x * v x) =
        η * (Real.sqrt (l2sq (swapIterF f st)) : ℂ) * uinner (fun x => u (swapFixAt I z x)) P)
    (ρ' : ℝ) (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1) (hρ' : ρ' ≤ ρ₁) :
    swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B) ≤
      𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
        swapIndCorr (swapIterLive A b)
          (swapIterFun f (swapIterLive A b) (swapIterZ st (swapIterLive A b) w))) := by
  have hε1' : ε ≤ 1 := by linarith
  have hB0 : 0 < B := hε0.trans_le hεB
  obtain ⟨-, -, hBnd, -⟩ := si_sqrt_bounds hε0 hε1' hεB hL
  have hx0 := si_XT_pos hε0
  have hc0 := si_c_pos
  have hLpos : 0 < l2sq (swapIterF f st) := lt_of_lt_of_le (by positivity) hL
  set F := swapIterF f st with hF
  set s := Real.sqrt (l2sq F) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hLpos
  have hss : s * s = l2sq F := Real.mul_self_sqrt hLpos.le
  set Bd := 27 * B / (swapC ^ 7 * ε ^ 28 * s) with hBd
  have hBd0 : 0 < Bd := by positivity
  -- the induction hypothesis for `u`
  have huv : swapEpsNext ε ^ 4 ≤ (val u u u u).re := by
    have hθ := si_θ_pos
    have hm := swapInd_mr32 hε0 hε1'
    have e1 : swapEpsNext ε = ε + 2 / 10 ^ 12 * ε ^ 4 / 4 := by unfold swapEpsNext swapTheta; rfl
    have hNV0 : 0 ≤ ε ^ 2 - 2 / 10 ^ 12 * ε ^ 5 := by
      have : ε ^ 5 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1' (by norm_num)
      nlinarith
    have hNV' : ε ^ 2 - 2 / 10 ^ 12 * ε ^ 5 ≤ swapIterNV f st := by
      have : swapTheta = 2 / 10 ^ 12 := rfl
      rw [← this]
      exact hNV
    have hsq : (ε ^ 2 - 2 / 10 ^ 12 * ε ^ 5) ^ 2 ≤
        (val F F F F).re / l2sq F ^ 2 := by
      rw [← swapInd_NV_sq]
      exact pow_le_pow_left₀ hNV0 hNV' 2
    rw [e1]
    refine hm.trans (le_trans ?_ huval)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hIHu := hIH α ι u (fun x => (hub x).trans hBnd) hu1.le huv ρ' h0' h1' hρ'
  have hbase := si_restrExp_le_base ρ' h0' h1' u A hudep
  -- the transfer, for every live coin vector `b`
  have hFdep : ∀ x y : ι → α, (∀ i ∈ A, x i = y i) → (∀ i ∈ A', x i = y i) → F x = F y :=
    fun x y h h' => swapInd_F_dep f st x y fun i hi => by
      rcases hRAA i hi with hA | hA'
      · exact h i hA
      · exact h' i hA'
  have htr : ∀ b : ι → Bool,
      ‖η * (s : ℂ)‖ * 𝔼 w : ι → α, swapIndCorr (swapIterLive A b)
          (swapIterFun u (swapIterLive A b) w) ≤
        Bd * 𝔼 w : ι → α, swapIndCorr (swapIterLive A b)
          (swapIterFun f (swapIterLive A b) (swapIterZ st (swapIterLive A b) w)) := by
    intro b
    have hLA : swapIterLive A b ⊆ A := filter_subset _ _
    have hX : ∀ w : ι → α, swapIterFun f (swapIterLive A b) (swapIterZ st (swapIterLive A b) w) =
        swapIterFun F (swapIterLive A b) w := fun w => by
      rw [swapInd_fun_Z f st (swapIterLive A b) (hLA.trans hAR) w, ← hF]
    simp_rw [hX]
    exact swapInd_transfer A A' hAA F u v (η * (s : ℂ)) hBd0.le hvb hvdep hudep hFdep hid _ hLA
  have hnk : ‖η * (s : ℂ)‖ = ‖η‖ * s := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  -- combine
  have hmain : ‖η‖ * s * δ' ≤ Bd * 𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
      swapIndCorr (swapIterLive A b)
        (swapIterFun f (swapIterLive A b) (swapIterZ st (swapIterLive A b) w))) := by
    have hns : 0 ≤ ‖η‖ * s := by positivity
    calc ‖η‖ * s * δ' ≤ ‖η‖ * s * 𝔼 w : ι → α, ((bernoulli ρ' h0' h1').pi ι).expect (fun b =>
          swapIndCorr (swapIterLive A b) (swapIterFun u (swapIterLive A b) w)) :=
          mul_le_mul_of_nonneg_left (hIHu.trans hbase) hns
      _ = ((bernoulli ρ' h0' h1').pi ι).expect (fun b => ‖η * (s : ℂ)‖ *
          𝔼 w : ι → α, swapIndCorr (swapIterLive A b) (swapIterFun u (swapIterLive A b) w)) := by
          rw [swapInd_expect_comm, FinProb.expect_const_mul, hnk]
      _ ≤ ((bernoulli ρ' h0' h1').pi ι).expect (fun b => Bd *
          𝔼 w : ι → α, swapIndCorr (swapIterLive A b)
            (swapIterFun f (swapIterLive A b) (swapIterZ st (swapIterLive A b) w))) :=
          FinProb.expect_mono _ htr
      _ = _ := by rw [FinProb.expect_const_mul, swapInd_expect_comm]
  -- the constants
  have hkey : swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B) * Bd ≤ ‖η‖ * s * δ' := by
    have e : swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B) * Bd =
        swapC ^ 2 * ε ^ 9 / 6 * δ' * (ε ^ 2 * swapX ε ^ swapT ε / s) := by
      rw [hBd]
      field_simp
      ring
    have h2 : ε ^ 2 * swapX ε ^ swapT ε / s ≤ s := by
      rw [div_le_iff₀ hs0, hss]
      linarith
    rw [e]
    calc swapC ^ 2 * ε ^ 9 / 6 * δ' * (ε ^ 2 * swapX ε ^ swapT ε / s) ≤
        swapC ^ 2 * ε ^ 9 / 6 * δ' * s := by gcongr
      _ ≤ ‖η‖ * δ' * s := by gcongr
      _ = ‖η‖ * s * δ' := by ring
  have := hkey.trans hmain
  rw [mul_comm _ Bd] at this
  exact le_of_mul_le_mul_left this hBd0

/-! ### The classes of outcomes of `lemma:tlarge` -/

/-- item 1 of `lemma:svdinc` (the swap value increases on `S`). -/
private def siItem1 (c ε B : ℝ) (R S : Finset ι) (f : (ι → α) → ℂ) : Prop :=
  ∃ (g h : (ι → α) → ℂ) (η : ℂ),
    l2sq g = 1 ∧ l2sq h = 1 ∧
    (∀ x, ‖g x‖ ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f))) ∧
    (∀ x, ‖h x‖ ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f))) ∧
    c ^ 2 * ε ^ 9 / 6 ≤ ‖η‖ ∧
    (SwapDependsOn S g ∧ SwapDependsOn (R \ S) h ∧
      (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) ≤ (val g g g g).re ∧
      ∀ (I : Finset ι), I ⊆ S → ∀ (z : ι → α) (P : (ι → α) → ℂ), SwapDependsOn (S \ I) P →
        uinner (fun x => f (swapFixAt I z x)) (fun x => P x * h x) =
          η * (Real.sqrt (l2sq f) : ℂ) * uinner (fun x => g (swapFixAt I z x)) P)

/-- item 2 of `lemma:svdinc` (the swap value increases on `T = R \ S`). -/
private def siItem2 (c ε B : ℝ) (R S : Finset ι) (f : (ι → α) → ℂ) : Prop :=
  ∃ (g h : (ι → α) → ℂ) (η : ℂ),
    l2sq g = 1 ∧ l2sq h = 1 ∧
    (∀ x, ‖g x‖ ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f))) ∧
    (∀ x, ‖h x‖ ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f))) ∧
    c ^ 2 * ε ^ 9 / 6 ≤ ‖η‖ ∧
    (SwapDependsOn S g ∧ SwapDependsOn (R \ S) h ∧
      (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) ≤ (val h h h h).re ∧
      ∀ (I : Finset ι), I ⊆ R \ S → ∀ (z : ι → α) (P : (ι → α) → ℂ),
        SwapDependsOn ((R \ S) \ I) P →
        uinner (fun x => f (swapFixAt I z x)) (fun x => g x * P x) =
          η * (Real.sqrt (l2sq f) : ℂ) * uinner (fun x => h (swapFixAt I z x)) P)

omit [DecidableEq α] in
private theorem si_out_split {c ε B : ℝ} {R S : Finset ι} {f : (ι → α) → ℂ}
    (h : SwapSvdIncOut c ε B R S f) : siItem1 c ε B R S f ∨ siItem2 c ε B R S f := by
  obtain ⟨g, h, η, h1, h2, h3, h4, h5, h6 | h6⟩ := h
  · exact Or.inl ⟨g, h, η, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inr ⟨g, h, η, h1, h2, h3, h4, h5, h6⟩

/-- class `R(t)`: the normalized value at time `t` reaches `ε'²` (Case 1, or Case 2 with a large
normalized value), with the norm bound. -/
private def siClR (ε : ℝ) (f : (ι → α) → ℂ) (t : ℕ) (c₀ : SwapCoins ι α)
    (ω : Fin (swapT ε) → SwapCoins ι α) : Prop :=
  swapEpsNext ε ^ 2 ≤ swapIterNV f (swapIterRun c₀ ω t) ∧
    swapX ε ^ swapT ε * ε ^ 2 ≤ l2sq (swapIterF f (swapIterRun c₀ ω t))

/-- class `H1(t)`: Case 2 stopped at `t < T`, item 1 of `lemma:svdinc`. -/
private def siClH1 (ε B : ℝ) (f : (ι → α) → ℂ) (t : ℕ) (c₀ : SwapCoins ι α)
    (ω : Fin (swapT ε) → SwapCoins ι α) : Prop :=
  t < swapT ε ∧ swapX ε ^ swapT ε * ε ^ 2 ≤ l2sq (swapIterF f (swapIterRun c₀ ω t)) ∧
    ε ^ 2 - swapTheta * ε ^ 5 ≤ swapIterNV f (swapIterRun c₀ ω t) ∧
    siItem1 swapC ε B (swapIterRun c₀ ω t).R (swapIterRun c₀ ω t).S
      (swapIterF f (swapIterRun c₀ ω t))

/-- class `H2(t)`: Case 2 stopped at `t < T`, item 2 of `lemma:svdinc`. -/
private def siClH2 (ε B : ℝ) (f : (ι → α) → ℂ) (t : ℕ) (c₀ : SwapCoins ι α)
    (ω : Fin (swapT ε) → SwapCoins ι α) : Prop :=
  t < swapT ε ∧ swapX ε ^ swapT ε * ε ^ 2 ≤ l2sq (swapIterF f (swapIterRun c₀ ω t)) ∧
    ε ^ 2 - swapTheta * ε ^ 5 ≤ swapIterNV f (swapIterRun c₀ ω t) ∧
    siItem2 swapC ε B (swapIterRun c₀ ω t).R (swapIterRun c₀ ω t).S
      (swapIterF f (swapIterRun c₀ ω t))

/-- every outcome of `lemma:tlarge` lies in one of the `3T` classes. -/
private theorem si_cover {ε B : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100) (f : (ι → α) → ℂ)
    (hB : ∀ x, ‖f x‖ ≤ B) (hl2 : l2sq f ≤ 1) (hv : ε ^ 4 ≤ (val f f f f).re)
    (c₀ : SwapCoins ι α) (ω : Fin (swapT ε) → SwapCoins ι α)
    (hO : swapIterOutcome swapTheta ε (swapGamma ε) (swapT ε) swapSvdChoice f c₀ ω) :
    ∃ k ∈ range (swapT ε), siClR ε f (k + 1) c₀ ω ∨ siClH1 ε B f (k + 1) c₀ ω ∨
      siClH2 ε B f (k + 1) c₀ ω := by
  have hε1' : ε ≤ 1 := by linarith
  have hNV0 := si_NV0 hε0 f hl2 hv c₀ ω
  have hL2 := swapInd_l2 hε0 f hv
  have hx := si_X_eq hε0
  have hx0 := si_X_pos hε0
  have hx1 := si_X_le hε0 hε1'
  have hTpos := si_T_pos hε0
  have hθ := si_θ_pos
  rcases hO with ⟨hτ, hNVT, hnorm⟩ | ⟨hτ1, hτT, hstop, hNVτ, hnorm⟩
  · refine ⟨swapT ε - 1, mem_range.2 (by omega), Or.inl ?_⟩
    have e : swapT ε - 1 + 1 = swapT ε := by omega
    rw [e]
    refine ⟨(si_eps_sq hε0 hε1').trans (by linarith), ?_⟩
    have h := hnorm (swapT ε) le_rfl
    rw [hx] at h
    calc swapX ε ^ swapT ε * ε ^ 2 ≤ swapX ε ^ swapT ε * l2sq f :=
          mul_le_mul_of_nonneg_left hL2 (pow_nonneg hx0.le _)
      _ ≤ _ := h
  · obtain ⟨τ, hτd⟩ : ∃ τ, τ = swapIterTau (swapGamma ε) (swapT ε) swapSvdChoice f c₀ ω :=
      ⟨_, rfl⟩
    rw [← hτd] at hτ1 hτT hstop hNVτ hnorm
    refine ⟨τ - 1, mem_range.2 (by omega), ?_⟩
    have e : τ - 1 + 1 = τ := by omega
    rw [e]
    have hLτ : swapX ε ^ swapT ε * ε ^ 2 ≤ l2sq (swapIterF f (swapIterRun c₀ ω τ)) := by
      have h := hnorm τ le_rfl
      rw [hx] at h
      calc swapX ε ^ swapT ε * ε ^ 2 ≤ swapX ε ^ τ * l2sq f :=
            mul_le_mul (pow_le_pow_of_le_one hx0.le hx1 hτT.le) hL2 (by positivity)
              (pow_nonneg hx0.le _)
        _ ≤ _ := h
    by_cases hR : swapEpsNext ε ^ 2 ≤ swapIterNV f (swapIterRun c₀ ω τ)
    · exact Or.inl ⟨hR, hLτ⟩
    right
    have hNVτ' : ε ^ 2 - swapTheta * ε ^ 5 ≤ swapIterNV f (swapIterRun c₀ ω τ) := by linarith
    have hnv : ε ^ 2 / 2 ≤ swapIterNV f (swapIterRun c₀ ω τ) := by
      have : swapTheta * ε ^ 5 ≤ ε ^ 2 / 2 := by
        have h5 : ε ^ 5 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1' (by norm_num)
        unfold swapTheta
        nlinarith [pow_pos hε0 5]
      linarith
    have hnv' : swapIterNV f (swapIterRun c₀ ω τ) ≤ 99 / 100 :=
      (le_of_not_ge hR).trans (si_eps_le_99 hε0 hε1)
    have hout := swap_svdinc (c := swapC) (ε := ε) (B := B) si_c_pos (by unfold swapC; rfl) hε0
      hε1' (swapIterF f (swapIterRun c₀ ω τ)) (swapIterRun c₀ ω τ).S (swapIterRun c₀ ω τ).R
      (swapIterRun_S_subset c₀ ω τ) (swapInd_F_dep f _) (fun x => hB _)
      (swapSvdChoice (swapIterRun c₀ ω τ).S (swapIterF f (swapIterRun c₀ ω τ))) τ
      (si_t_small hε0 hτT) hstop.le hnv hnv'
    rcases si_out_split hout with h1 | h2
    · exact Or.inl ⟨hτT, hLτ, hNVτ', h1⟩
    · exact Or.inr ⟨hτT, hLτ, hNVτ', h2⟩

open scoped Classical in
/-- the indicator of an outcome is at most the sum of the indicators of the classes. -/
private theorem si_ind_le {ε B : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100) (f : (ι → α) → ℂ)
    (hB : ∀ x, ‖f x‖ ≤ B) (hl2 : l2sq f ≤ 1) (hv : ε ^ 4 ≤ (val f f f f).re)
    (c₀ : SwapCoins ι α) (ω : Fin (swapT ε) → SwapCoins ι α) :
    (if swapIterOutcome swapTheta ε (swapGamma ε) (swapT ε) swapSvdChoice f c₀ ω then (1 : ℝ)
      else 0) ≤ ∑ k ∈ range (swapT ε),
        ((if siClR ε f (k + 1) c₀ ω then (1 : ℝ) else 0) +
          (if siClH1 ε B f (k + 1) c₀ ω then (1 : ℝ) else 0) +
          (if siClH2 ε B f (k + 1) c₀ ω then (1 : ℝ) else 0)) := by
  have hnn : ∀ k ∈ range (swapT ε), (0 : ℝ) ≤
      (if siClR ε f (k + 1) c₀ ω then (1 : ℝ) else 0) +
        (if siClH1 ε B f (k + 1) c₀ ω then (1 : ℝ) else 0) +
        (if siClH2 ε B f (k + 1) c₀ ω then (1 : ℝ) else 0) := fun k _ => by
    split_ifs <;> norm_num
  split_ifs with hO
  · obtain ⟨k, hk, hc⟩ := si_cover hε0 hε1 f hB hl2 hv c₀ ω hO
    refine le_trans ?_ (Finset.single_le_sum hnn hk)
    rcases hc with h | h | h <;> simp only [h, ite_true] <;> split_ifs <;> norm_num
  · exact Finset.sum_nonneg hnn

/-- the densities of the classes: `2^t ρ ≤ ρ₁` for `t ≤ T`. -/
private theorem si_density {ε ρ ρ₁ : ℝ} (h0 : 0 ≤ ρ) (hρ : ρ ≤ swapRhoNext ε ρ₁) {t : ℕ}
    (ht : t ≤ swapT ε) : (2 : ℝ) ^ t * ρ ≤ ρ₁ := by
  unfold swapRhoNext at hρ
  rw [le_div_iff₀ (by positivity)] at hρ
  calc (2 : ℝ) ^ t * ρ ≤ 2 ^ swapT ε * ρ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ht) h0
    _ = ρ * 2 ^ swapT ε := mul_comm _ _
    _ ≤ ρ₁ := hρ

open scoped Classical in
private theorem si_prob_R [Nonempty α] {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100)
    (hεB : ε ≤ B) (hρ1 : ρ₁ ≤ 1) (hδ' : 0 < δ')
    (hIH : SiClaim (swapEpsNext ε) (swapBNext ε B) ρ₁ δ') (f : (ι → α) → ℂ)
    (hB : ∀ x, ‖f x‖ ≤ B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ ≤ swapRhoNext ε ρ₁)
    (t : ℕ) (ht : t ≤ swapT ε) :
    (𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α,
        if siClR ε f t c₀ ω then (1 : ℝ) else 0) *
      (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B)) ≤ swapRestrExp ρ h0 h1 f := by
  have h2 := si_density h0 hρ ht
  have h0' : 0 ≤ (2 : ℝ) ^ t * ρ := by positivity
  have h1' : (2 : ℝ) ^ t * ρ ≤ 1 := h2.trans hρ1
  rw [si_restrExp_fixLaw, ← swapIterRun_law_R f ht h0' h1' h0 h1 (swapInd_half_pow t ρ) swapIndCorr]
  refine swapInd_class_bound _ _ (fun c ω => ?_) (fun c ω hc => ?_)
  · exact Finset.expect_nonneg fun w _ => FinProb.expect_nonneg _ fun b => swapIndCorr_nonneg _ _
  · exact si_value_R hε0 hε1 hεB hδ' hIH f hB _ hc.1 hc.2 _ h0' h1' h2

open scoped Classical in
private theorem si_prob_H1 [Nonempty α] {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100)
    (hεB : ε ≤ B) (hρ1 : ρ₁ ≤ 1) (hδ' : 0 < δ')
    (hIH : SiClaim (swapEpsNext ε) (swapBNext ε B) ρ₁ δ') (f : (ι → α) → ℂ)
    (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ ≤ swapRhoNext ε ρ₁) (t : ℕ) :
    (𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α,
        if siClH1 ε B f t c₀ ω then (1 : ℝ) else 0) *
      (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B)) ≤ swapRestrExp ρ h0 h1 f := by
  by_cases htT : t < swapT ε
  swap
  · have : ∀ c₀ ω, ¬ siClH1 ε B f t c₀ ω := fun c₀ ω h => htT h.1
    simp only [this, ite_false, Finset.expect_const_zero, zero_mul]
    rw [si_restrExp_bw]
    exact Finset.expect_nonneg fun w _ => FinProb.expect_nonneg _ fun b => swapIndCorr_nonneg _ _
  have h2 := si_density h0 hρ (Nat.succ_le_of_lt htT)
  have h0' : 0 ≤ (2 : ℝ) ^ (t + 1) * ρ := by positivity
  have h1' : (2 : ℝ) ^ (t + 1) * ρ ≤ 1 := h2.trans hρ1
  rw [si_restrExp_fixLaw, ← swapIterRun_law_S f htT.le h0' h1' h0 h1 (swapInd_half_pow (t + 1) ρ)
    swapIndCorr]
  refine swapInd_class_bound _ _ (fun c ω => ?_) (fun c ω hc => ?_)
  · exact Finset.expect_nonneg fun w _ => FinProb.expect_nonneg _ fun b => swapIndCorr_nonneg _ _
  · obtain ⟨-, hL, hNV, g, h, η, hg1, -, hgb, hhb, hη, hgdep, hhdep, hval, hid⟩ := hc
    have hSR := swapIterRun_S_subset c ω t
    refine si_value_H hε0 hε1 hεB hδ' hIH f _ _ _ (fun i hi h' => (mem_sdiff.1 h').2 hi) hSR
      (fun i hi => ?_) hL hNV g h η hg1 hgb hhb hη hgdep hhdep hval hid _ h0' h1' h2
    by_cases hS : i ∈ (swapIterRun c ω t).S
    · exact Or.inl hS
    · exact Or.inr (mem_sdiff.2 ⟨hi, hS⟩)

open scoped Classical in
private theorem si_prob_H2 [Nonempty α] {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100)
    (hεB : ε ≤ B) (hρ1 : ρ₁ ≤ 1) (hδ' : 0 < δ')
    (hIH : SiClaim (swapEpsNext ε) (swapBNext ε B) ρ₁ δ') (f : (ι → α) → ℂ)
    (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ ≤ swapRhoNext ε ρ₁) (t : ℕ) :
    (𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α,
        if siClH2 ε B f t c₀ ω then (1 : ℝ) else 0) *
      (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B)) ≤ swapRestrExp ρ h0 h1 f := by
  by_cases htT : t < swapT ε
  swap
  · have : ∀ c₀ ω, ¬ siClH2 ε B f t c₀ ω := fun c₀ ω h => htT h.1
    simp only [this, ite_false, Finset.expect_const_zero, zero_mul]
    rw [si_restrExp_bw]
    exact Finset.expect_nonneg fun w _ => FinProb.expect_nonneg _ fun b => swapIndCorr_nonneg _ _
  have h2 := si_density h0 hρ (Nat.succ_le_of_lt htT)
  have h0' : 0 ≤ (2 : ℝ) ^ (t + 1) * ρ := by positivity
  have h1' : (2 : ℝ) ^ (t + 1) * ρ ≤ 1 := h2.trans hρ1
  rw [si_restrExp_fixLaw, ← swapIterRun_law_T f htT.le h0' h1' h0 h1 (swapInd_half_pow (t + 1) ρ)
    swapIndCorr]
  refine swapInd_class_bound _ _ (fun c ω => ?_) (fun c ω hc => ?_)
  · exact Finset.expect_nonneg fun w _ => FinProb.expect_nonneg _ fun b => swapIndCorr_nonneg _ _
  · obtain ⟨-, hL, hNV, g, h, η, -, hh1, hgb, hhb, hη, hgdep, hhdep, hval, hid⟩ := hc
    have hid' : ∀ I : Finset ι, I ⊆ (swapIterRun c ω t).R \ (swapIterRun c ω t).S →
        ∀ (z : ι → α) (P : (ι → α) → ℂ),
        SwapDependsOn (((swapIterRun c ω t).R \ (swapIterRun c ω t).S) \ I) P →
        uinner (fun x => swapIterF f (swapIterRun c ω t) (swapFixAt I z x)) (fun x => P x * g x) =
          η * (Real.sqrt (l2sq (swapIterF f (swapIterRun c ω t))) : ℂ) *
            uinner (fun x => h (swapFixAt I z x)) P := by
      intro I hI z P hP
      rw [← hid I hI z P hP]
      congr 1
      funext x
      ring
    refine si_value_H hε0 hε1 hεB hδ' hIH f _ _ _ (fun i hi h' => (mem_sdiff.1 hi).2 h')
      sdiff_subset (fun i hi => ?_) hL hNV h g η hh1 hhb hgb hη hhdep hgdep hval hid' _ h0' h1' h2
    by_cases hS : i ∈ (swapIterRun c ω t).S
    · exact Or.inr hS
    · exact Or.inl (mem_sdiff.2 ⟨hi, hS⟩)

/-- CSP_6 `thm:swap#case1-recursion`, `#case2-recursion`, `#induction-closure` (the inductive step). -/
theorem swap_step {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100) (hεB : ε ≤ B)
    (hρ0 : 0 < ρ₁) (hρ1 : ρ₁ ≤ 1) (hδ' : 0 < δ')
    (hIH : ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι]
        [DecidableEq ι] (f : (ι → α) → ℂ), (∀ x, ‖f x‖ ≤ swapBNext ε B) → l2sq f ≤ 1 →
        swapEpsNext ε ^ 4 ≤ (val f f f f).re →
        ∀ (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), ρ ≤ ρ₁ → δ' ≤ swapRestrExp ρ h0 h1 f)
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (hB : ∀ x, ‖f x‖ ≤ B) (hl2 : l2sq f ≤ 1) (hv : ε ^ 4 ≤ (val f f f f).re)
    (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ ≤ swapRhoNext ε ρ₁) :
    swapDeltaNext ε B δ' ≤ swapRestrExp ρ h0 h1 f := by
  classical
  have := hρ0
  have hε1' : ε ≤ 1 := by linarith
  have hB0 : 0 < B := hε0.trans_le hεB
  have hc0 := si_c_pos
  have hθ0 := si_θ_pos
  have hγ0 := si_γ_pos hε0
  have hTpos := si_T_pos hε0
  have hx0 := si_XT_pos hε0
  set V := swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * δ' / (162 * B) with hV
  have hV0 : 0 ≤ V := by positivity
  have hL2 := swapInd_l2 hε0 f hv
  -- `lemma:tlarge`
  have hlarge := swapTlarge swapSvdChoice f hB hε0 (by linarith) hθ0 si_θ_le hγ0
    (si_γ_le hε0 hε1') (si_γ_lt hε0 hε1') (si_T_ge ε) hl2 (swapInd_v2 hε0 f hv)
  rw [si_X_eq hε0] at hlarge
  have hPG : swapPGood ε B ≤ (swapGamma ε ^ 4 * swapX ε ^ swapT ε * l2sq f /
      (36 * (swapTheta * ε ^ 5)⁻¹ * B ^ 2)) ^ swapT ε := by
    unfold swapPGood
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have e : swapGamma ε ^ 4 * swapX ε ^ swapT ε * l2sq f / (36 * (swapTheta * ε ^ 5)⁻¹ * B ^ 2) =
        swapGamma ε ^ 4 * swapX ε ^ swapT ε * l2sq f * (swapTheta * ε ^ 5) / (36 * B ^ 2) := by
      field_simp
    rw [e]
    gcongr
  -- the classes
  set Pr : (SwapCoins ι α → (Fin (swapT ε) → SwapCoins ι α) → Prop) → ℝ := fun C =>
    𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α, if C c₀ ω then (1 : ℝ) else 0
    with hPr
  have hsum : (𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α,
      if swapIterOutcome swapTheta ε (swapGamma ε) (swapT ε) swapSvdChoice f c₀ ω then (1 : ℝ)
        else 0) ≤ ∑ k ∈ range (swapT ε),
          (Pr (siClR ε f (k + 1)) + Pr (siClH1 ε B f (k + 1)) + Pr (siClH2 ε B f (k + 1))) := by
    calc _ ≤ 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α,
          ∑ k ∈ range (swapT ε),
            ((if siClR ε f (k + 1) c₀ ω then (1 : ℝ) else 0) +
              (if siClH1 ε B f (k + 1) c₀ ω then (1 : ℝ) else 0) +
              (if siClH2 ε B f (k + 1) c₀ ω then (1 : ℝ) else 0)) :=
          Finset.expect_le_expect fun c₀ _ => Finset.expect_le_expect fun ω _ =>
            si_ind_le hε0 hε1 f hB hl2 hv c₀ ω
      _ = _ := by
          simp only [hPr, Finset.expect_sum_comm, Finset.expect_add_distrib]
  have hcl : ∀ k ∈ range (swapT ε),
      (Pr (siClR ε f (k + 1)) + Pr (siClH1 ε B f (k + 1)) + Pr (siClH2 ε B f (k + 1))) * V ≤
        3 * swapRestrExp ρ h0 h1 f := by
    intro k hk
    have h1' := si_prob_R hε0 hε1 hεB hρ1 hδ' hIH f hB ρ h0 h1 hρ (k + 1)
      (Nat.succ_le_of_lt (mem_range.1 hk))
    have h2' := si_prob_H1 hε0 hε1 hεB hρ1 hδ' hIH f ρ h0 h1 hρ (k + 1)
    have h3' := si_prob_H2 hε0 hε1 hεB hρ1 hδ' hIH f ρ h0 h1 hρ (k + 1)
    simp only [hPr] at h1' h2' h3' ⊢
    linarith
  have htot : swapPGood ε B * V ≤ swapT ε * (3 * swapRestrExp ρ h0 h1 f) := by
    calc swapPGood ε B * V ≤ (𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin (swapT ε) → SwapCoins ι α,
          if swapIterOutcome swapTheta ε (swapGamma ε) (swapT ε) swapSvdChoice f c₀ ω then (1 : ℝ)
            else 0) * V := mul_le_mul_of_nonneg_right (hPG.trans hlarge) hV0
      _ ≤ (∑ k ∈ range (swapT ε),
          (Pr (siClR ε f (k + 1)) + Pr (siClH1 ε B f (k + 1)) + Pr (siClH2 ε B f (k + 1)))) * V :=
          mul_le_mul_of_nonneg_right hsum hV0
      _ = ∑ k ∈ range (swapT ε),
          (Pr (siClR ε f (k + 1)) + Pr (siClH1 ε B f (k + 1)) + Pr (siClH2 ε B f (k + 1))) * V :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _k ∈ range (swapT ε), 3 * swapRestrExp ρ h0 h1 f := Finset.sum_le_sum hcl
      _ = swapT ε * (3 * swapRestrExp ρ h0 h1 f) := by
          rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have hT0 : (0 : ℝ) < swapT ε := by exact_mod_cast hTpos
  unfold swapDeltaNext
  rw [← hV, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

end SwapInduct

section SwapInductFinal

/-! ### The recursion solution -/

private theorem si_claim_base {ε B : ℝ} (hB0 : 0 < B) (hε : 99 / 100 ≤ ε) :
    SiClaim ε B 1 ((3 / 4) / B) := by
  intro α _ _ _ ι _ _ f hB hl2 hv ρ h0 h1 _
  exact swap_base_case hB0 hε ρ h0 h1 f hB hl2 hv

private theorem si_claim_step {ε B ρ₁ δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 99 / 100) (hεB : ε ≤ B)
    (hρ0 : 0 < ρ₁) (hρ1 : ρ₁ ≤ 1) (hδ' : 0 < δ')
    (hIH : SiClaim (swapEpsNext ε) (swapBNext ε B) ρ₁ δ') :
    SiClaim ε B (swapRhoNext ε ρ₁) (swapDeltaNext ε B δ') := by
  intro α _ _ _ ι _ _ f hB hl2 hv ρ h0 h1 hρ
  exact swap_step hε0 hε1 hεB hρ0 hρ1 hδ' hIH α ι f hB hl2 hv ρ h0 h1 hρ

/-- the unit `q = 2^{-(M+50)}` is below every elementary factor of the recursion for `ε ≥ 1/M`. -/
private theorem si_q_facts {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 1 / (M : ℝ) ≤ ε) {q : ℝ}
    (hq : q = (1 / 2 : ℝ) ^ (M + 50)) :
    0 < q ∧ q ≤ 1 / 2 ∧ q ≤ ε ∧ q ≤ swapC ∧ q ≤ swapTheta ∧ q ≤ 1 / 162 := by
  have h50 : (1 / 2 : ℝ) ^ (M + 50) ≤ (1 / 2) ^ 50 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hM2 : (1 / 2 : ℝ) ^ (M + 50) ≤ (1 / 2) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hMM : (1 / 2 : ℝ) ^ M ≤ 1 / M := by
    have h : M < 2 ^ M := Nat.lt_two_pow_self
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    rw [one_div_pow, one_div_le_one_div (by positivity) hMpos]
    exact_mod_cast h.le
  subst hq
  refine ⟨by positivity, ?_, hM2.trans (hMM.trans hε), ?_, ?_, ?_⟩
  · exact h50.trans (by norm_num)
  · unfold swapC
    exact h50.trans (by norm_num)
  · unfold swapTheta
    exact h50.trans (by norm_num)
  · exact h50.trans (by norm_num)

private theorem si_T_le {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε : 1 / (M : ℝ) ≤ ε) :
    swapT ε ≤ swapIndT0 M := by
  unfold swapT
  rw [Nat.ceil_le]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMε : 1 ≤ (M : ℝ) * ε := by
    rw [div_le_iff₀ hMpos] at hε
    linarith
  have hγ := si_γ_pos hε0
  rw [div_le_iff₀ (by positivity)]
  have e : ((swapIndT0 M : ℕ) : ℝ) * swapGamma ε ^ 2 = 8 * ((M : ℝ) * ε) ^ 16 := by
    unfold swapIndT0 swapGamma swapC
    push_cast
    ring
  rw [e]
  have : 1 ≤ ((M : ℝ) * ε) ^ 16 := one_le_pow₀ hMε
  linarith

private theorem si_XT_ge {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hε : 1 / (M : ℝ) ≤ ε) {q : ℝ} (hq : q = (1 / 2 : ℝ) ^ (M + 50)) :
    q ^ (27 * swapIndT0 M) ≤ swapX ε ^ swapT ε := by
  obtain ⟨hq0, -, hqε, hqc, hqθ, hqk⟩ := si_q_facts hM hε hq
  have h18 : q ≤ 1 / 18 := hqk.trans (by norm_num)
  have hc0 := si_c_pos
  have hθ0 := si_θ_pos
  have hX : q ^ 27 ≤ swapX ε := by
    calc q ^ 27 = q ^ 4 * q ^ 16 * q * q ^ 5 * q := by ring
      _ ≤ swapC ^ 4 * ε ^ 16 * swapTheta * ε ^ 5 * (1 / 18) := by gcongr
      _ = swapX ε := by unfold swapX swapGamma; ring
  calc q ^ (27 * swapIndT0 M) = (q ^ 27) ^ swapIndT0 M := pow_mul _ _ _
    _ ≤ swapX ε ^ swapIndT0 M := pow_le_pow_left₀ (by positivity) hX _
    _ ≤ swapX ε ^ swapT ε := pow_le_pow_of_le_one (si_X_pos hε0).le (si_X_le hε0 hε1)
        (si_T_le hM hε0 hε)

private theorem si_mu_ge {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hε : 1 / (M : ℝ) ≤ ε) {q : ℝ} (hq : q = (1 / 2 : ℝ) ^ (M + 50)) :
    q ^ swapIndV0 M ≤ swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) / 27 := by
  obtain ⟨hq0, -, hqε, hqc, -, hqk⟩ := si_q_facts hM hε hq
  have h27 : q ≤ 1 / 27 := hqk.trans (by norm_num)
  have hc0 := si_c_pos
  have hx0 := si_XT_pos hε0
  have hx1 := si_XT_le hε0 hε1
  have hsx : swapX ε ^ swapT ε ≤ Real.sqrt (swapX ε ^ swapT ε) := by
    have h1 := Real.mul_self_sqrt hx0.le
    have h2 : Real.sqrt (swapX ε ^ swapT ε) ≤ 1 := Real.sqrt_le_one.2 hx1
    have h3 := Real.sqrt_nonneg (swapX ε ^ swapT ε)
    nlinarith
  have hxT := (si_XT_ge hM hε0 hε1 hε hq).trans hsx
  unfold swapIndV0
  calc q ^ (37 + 27 * swapIndT0 M) = q ^ 7 * q ^ 29 * q ^ (27 * swapIndT0 M) * q := by ring
    _ ≤ swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) * (1 / 27) := by gcongr
    _ = _ := by ring

/-- one step of the recursion in terms of the exponents of `q` and of `a = ε₀/(2B)`. -/
private theorem si_step_bounds {M : ℕ} (hM : 1 ≤ M) {ε₀ ε B ρ₁ δ' q : ℝ} {e h : ℕ}
    (hq : q = (1 / 2 : ℝ) ^ (M + 50)) (hε₀ : 0 < ε₀) (hM' : 1 / (M : ℝ) ≤ ε₀) (hε₀1 : ε₀ ≤ 1)
    (hε₀ε : ε₀ ≤ ε) (hε1 : ε < 99 / 100) (hεB : ε ≤ B)
    (hρ₁ : q ^ e * (ε₀ / (2 * swapBNext ε B)) ^ h ≤ ρ₁)
    (hδ₁ : q ^ e * (ε₀ / (2 * swapBNext ε B)) ^ h ≤ δ') :
    q ^ (e + swapIndV0 M * h + swapIndW0 M) * (ε₀ / (2 * B)) ^ (h + 2 * swapIndT0 M + 1) ≤
        swapRhoNext ε ρ₁ ∧
      q ^ (e + swapIndV0 M * h + swapIndW0 M) * (ε₀ / (2 * B)) ^ (h + 2 * swapIndT0 M + 1) ≤
        swapDeltaNext ε B δ' := by
  have hε0 : 0 < ε := hε₀.trans_le hε₀ε
  have hε1' : ε ≤ 1 := by linarith
  have hB0 : 0 < B := hε0.trans_le hεB
  have hMε : 1 / (M : ℝ) ≤ ε := hM'.trans hε₀ε
  obtain ⟨hq0, hq2, hqε, hqc, hqθ, hqk⟩ := si_q_facts hM hMε hq
  have hq1 : q ≤ 1 := hq2.trans (by norm_num)
  have hc0 := si_c_pos
  have hθ0 := si_θ_pos
  have hT := si_T_le hM hε0 hMε
  have hTpos := si_T_pos hε0
  have hx0 := si_XT_pos hε0
  have hxT := si_XT_ge hM hε0 hε1' hMε hq
  have hμ := si_mu_ge hM hε0 hε1' hMε hq
  obtain ⟨T0, hT0⟩ : ∃ T0, T0 = swapIndT0 M := ⟨_, rfl⟩
  rw [← hT0] at hT hxT ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = ε₀ / (2 * B) := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]
    linarith
  have hsx0 : 0 < Real.sqrt (swapX ε ^ swapT ε) := Real.sqrt_pos.2 hx0
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) / 27 := ⟨_, rfl⟩
  rw [← hμd] at hμ
  have hB' : ε₀ / (2 * swapBNext ε B) = a * μ := by
    unfold swapBNext
    rw [ha, hμd]
    field_simp
  have hlow : q ^ (e + swapIndV0 M * h) * a ^ h ≤ q ^ e * (ε₀ / (2 * swapBNext ε B)) ^ h := by
    rw [hB', mul_pow, pow_add, pow_mul]
    calc q ^ e * (q ^ swapIndV0 M) ^ h * a ^ h = q ^ e * (a ^ h * (q ^ swapIndV0 M) ^ h) := by
          ring
      _ ≤ q ^ e * (a ^ h * μ ^ h) := by gcongr
  have hW : T0 ≤ swapIndW0 M := by
    unfold swapIndW0
    rw [← hT0]
    calc T0 ≤ 3 * T0 := by omega
      _ ≤ (49 + 27 * T0) * T0 + 3 * T0 := Nat.le_add_left _ _
      _ ≤ _ := Nat.le_add_right _ _
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) hμ
  have hρ0 : 0 ≤ ρ₁ := by
    refine le_trans ?_ hρ₁
    rw [hB']
    positivity
  constructor
  · unfold swapRhoNext
    have h2T : q ^ T0 ≤ 1 / 2 ^ swapT ε := by
      calc q ^ T0 ≤ (1 / 2) ^ T0 := pow_le_pow_left₀ hq0.le hq2 _
        _ ≤ (1 / 2) ^ swapT ε := pow_le_pow_of_le_one (by norm_num) (by norm_num) hT
        _ = 1 / 2 ^ swapT ε := by rw [one_div_pow]
    calc q ^ (e + swapIndV0 M * h + swapIndW0 M) * a ^ (h + 2 * T0 + 1) ≤
        q ^ (e + swapIndV0 M * h + T0) * a ^ h :=
          mul_le_mul (pow_le_pow_of_le_one hq0.le hq1 (by omega))
            (pow_le_pow_of_le_one ha0.le ha1 (by omega)) (by positivity) (by positivity)
      _ = (q ^ (e + swapIndV0 M * h) * a ^ h) * q ^ T0 := by rw [pow_add]; ring
      _ ≤ ρ₁ * (1 / 2 ^ swapT ε) :=
          mul_le_mul (hlow.trans hρ₁) h2T (by positivity) hρ0
      _ = ρ₁ / 2 ^ swapT ε := by ring
  · -- the four factors of `swapDeltaNext`
    have hP1 : (a ^ 2 * q ^ (49 + 27 * T0)) ^ T0 ≤ swapPGood ε B := by
      have hbase : a ^ 2 * q ^ (49 + 27 * T0) ≤ swapGamma ε ^ 4 * swapX ε ^ swapT ε * ε ^ 2 *
          (swapTheta * ε ^ 5) / (36 * B ^ 2) := by
        have e1 : swapGamma ε ^ 4 * swapX ε ^ swapT ε * ε ^ 2 * (swapTheta * ε ^ 5) /
            (36 * B ^ 2) = (swapC ^ 8 * ε ^ 39 * swapX ε ^ swapT ε * swapTheta * (1 / 9)) *
              (1 / (4 * B ^ 2)) := by
          unfold swapGamma
          field_simp
          ring
        have e2 : a ^ 2 = ε₀ ^ 2 * (1 / (4 * B ^ 2)) := by
          rw [ha]
          field_simp
          ring
        have h9 : q ≤ 1 / 9 := hqk.trans (by norm_num)
        have hcore : q ^ (49 + 27 * T0) ≤
            swapC ^ 8 * ε ^ 39 * swapX ε ^ swapT ε * swapTheta * (1 / 9) := by
          calc q ^ (49 + 27 * T0) = q ^ 8 * q ^ 39 * q ^ (27 * T0) * q * q := by ring
            _ ≤ swapC ^ 8 * ε ^ 39 * swapX ε ^ swapT ε * swapTheta * (1 / 9) := by gcongr
        have hε₀2 : ε₀ ^ 2 ≤ 1 := pow_le_one₀ hε₀.le hε₀1
        rw [e1, e2]
        calc ε₀ ^ 2 * (1 / (4 * B ^ 2)) * q ^ (49 + 27 * T0) =
            (1 / (4 * B ^ 2)) * (ε₀ ^ 2 * q ^ (49 + 27 * T0)) := by ring
          _ ≤ (1 / (4 * B ^ 2)) *
              (1 * (swapC ^ 8 * ε ^ 39 * swapX ε ^ swapT ε * swapTheta * (1 / 9))) := by
              gcongr
          _ = _ := by ring
      have hb1 : a ^ 2 * q ^ (49 + 27 * T0) ≤ 1 :=
        calc a ^ 2 * q ^ (49 + 27 * T0) ≤ 1 * 1 :=
              mul_le_mul (pow_le_one₀ ha0.le ha1) (pow_le_one₀ hq0.le hq1) (by positivity)
                zero_le_one
          _ = 1 := one_mul 1
      unfold swapPGood
      calc (a ^ 2 * q ^ (49 + 27 * T0)) ^ T0 ≤ (a ^ 2 * q ^ (49 + 27 * T0)) ^ swapT ε :=
            pow_le_pow_of_le_one (by positivity) hb1 hT
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase _
    have hP2 : q ^ (3 * T0) ≤ 1 / (3 * (swapT ε : ℝ)) := by
      have h3 : (3 * swapT ε : ℕ) < 2 ^ (3 * T0) :=
        lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
      have h3' : (3 * (swapT ε : ℝ)) ≤ 2 ^ (3 * T0) := by exact_mod_cast h3.le
      have hT3 : (0 : ℝ) < 3 * (swapT ε : ℝ) := by
        have : (0 : ℝ) < swapT ε := by exact_mod_cast hTpos
        positivity
      calc q ^ (3 * T0) ≤ (1 / 2) ^ (3 * T0) := pow_le_pow_left₀ hq0.le hq2 _
        _ = 1 / 2 ^ (3 * T0) := by rw [one_div_pow]
        _ ≤ 1 / (3 * (swapT ε : ℝ)) := one_div_le_one_div_of_le hT3 h3'
    have hP3 : a * q ^ (49 + 27 * T0) ≤ swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε / (162 * B) := by
      have e1 : swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε / (162 * B) =
          (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * (1 / 81)) * (1 / (2 * B)) := by
        field_simp
        ring
      have e2 : a = ε₀ * (1 / (2 * B)) := by rw [ha]; ring
      have h81 : q ≤ 1 / 81 := hqk.trans (by norm_num)
      have hcore : q ^ (49 + 27 * T0) ≤ swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * (1 / 81) := by
        calc q ^ (49 + 27 * T0) = q ^ 9 * q ^ 39 * q ^ (27 * T0) * q := by ring
          _ ≤ _ := by gcongr
      rw [e1, e2]
      calc ε₀ * (1 / (2 * B)) * q ^ (49 + 27 * T0) =
          (1 / (2 * B)) * (ε₀ * q ^ (49 + 27 * T0)) := by ring
        _ ≤ (1 / (2 * B)) * (1 * (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε * (1 / 81))) := by
            gcongr
        _ = _ := by ring
    have hP4 : q ^ (e + swapIndV0 M * h) * a ^ h ≤ δ' := hlow.trans hδ₁
    have e3 : swapDeltaNext ε B δ' = swapPGood ε B * (1 / (3 * (swapT ε : ℝ))) *
        (swapC ^ 9 * ε ^ 39 * swapX ε ^ swapT ε / (162 * B)) * δ' := by
      unfold swapDeltaNext
      ring
    have e4 : q ^ (e + swapIndV0 M * h + swapIndW0 M) * a ^ (h + 2 * T0 + 1) =
        (a ^ 2 * q ^ (49 + 27 * T0)) ^ T0 * q ^ (3 * T0) * (a * q ^ (49 + 27 * T0)) *
          (q ^ (e + swapIndV0 M * h) * a ^ h) := by
      unfold swapIndW0
      rw [← hT0]
      ring
    rw [e3, e4]
    have hPG0 : 0 ≤ swapPGood ε B := le_trans (by positivity) hP1
    gcongr

private theorem si_EE_step (M n : ℕ) :
    swapIndEE M n + swapIndV0 M * swapIndHH M n + swapIndW0 M ≤ swapIndEE M (n + 1) := by
  have hH : swapIndHH M n ≤ swapIndHH M (n + 1) := by
    unfold swapIndHH
    have := Nat.mul_le_mul_right (2 * swapIndT0 M + 1) (Nat.le_add_right n 1)
    omega
  unfold swapIndEE
  calc n * (swapIndW0 M + swapIndV0 M * swapIndHH M n) + swapIndV0 M * swapIndHH M n +
        swapIndW0 M = (n + 1) * (swapIndW0 M + swapIndV0 M * swapIndHH M n) := by ring
    _ ≤ (n + 1) * (swapIndW0 M + swapIndV0 M * swapIndHH M (n + 1)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hH) _)

private theorem si_HH_step (M n : ℕ) :
    swapIndHH M (n + 1) = swapIndHH M n + 2 * swapIndT0 M + 1 := by
  unfold swapIndHH
  ring

/-- the induction on the number of steps `ε ↦ ε + θε⁴/4` (with `ε ≥ ε₀ ≥ 1/M` throughout). -/
private theorem si_induction {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) {M : ℕ} (hM : 1 ≤ M)
    (hM' : 1 / (M : ℝ) ≤ ε₀) {q : ℝ} (hq : q = (1 / 2 : ℝ) ^ (M + 50)) :
    ∀ n : ℕ, ∀ ε : ℝ, ε₀ ≤ ε → ε ≤ 1 → 99 / 100 - n * (swapTheta * ε₀ ^ 4 / 4) ≤ ε →
      ∀ B : ℝ, ε ≤ B → ∃ ρ₀ δ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ 0 < δ ∧
        q ^ swapIndEE M n * (ε₀ / (2 * B)) ^ swapIndHH M n ≤ ρ₀ ∧
        q ^ swapIndEE M n * (ε₀ / (2 * B)) ^ swapIndHH M n ≤ δ ∧ SiClaim ε B ρ₀ δ := by
  obtain ⟨hq0, hq2, -, -, -, -⟩ := si_q_facts hM hM' hq
  have hq1 : q ≤ 1 := hq2.trans (by norm_num)
  -- the base case, at any level
  have hbase : ∀ n : ℕ, ∀ ε : ℝ, ε₀ ≤ ε → 99 / 100 ≤ ε → ∀ B : ℝ, ε ≤ B →
      ∃ ρ₀ δ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ 0 < δ ∧
        q ^ swapIndEE M n * (ε₀ / (2 * B)) ^ swapIndHH M n ≤ ρ₀ ∧
        q ^ swapIndEE M n * (ε₀ / (2 * B)) ^ swapIndHH M n ≤ δ ∧ SiClaim ε B ρ₀ δ := by
    intro n ε hε₀ε hε B hεB
    have hB0 : 0 < B := (hε₀.trans_le hε₀ε).trans_le hεB
    have ha0 : 0 ≤ ε₀ / (2 * B) := by positivity
    have ha1 : ε₀ / (2 * B) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hle : q ^ swapIndEE M n * (ε₀ / (2 * B)) ^ swapIndHH M n ≤ ε₀ / (2 * B) := by
      have h1 : (ε₀ / (2 * B)) ^ swapIndHH M n ≤ ε₀ / (2 * B) :=
        pow_le_of_le_one ha0 (by linarith) (by unfold swapIndHH; omega)
      calc q ^ swapIndEE M n * (ε₀ / (2 * B)) ^ swapIndHH M n ≤
          1 * (ε₀ / (2 * B)) := mul_le_mul (pow_le_one₀ hq0.le hq1) h1 (by positivity) zero_le_one
        _ = ε₀ / (2 * B) := one_mul _
    refine ⟨1, (3 / 4) / B, one_pos, le_rfl, by positivity, hle.trans (by linarith), ?_,
      si_claim_base hB0 hε⟩
    refine hle.trans ?_
    rw [div_le_div_iff₀ (by positivity) hB0]
    nlinarith
  intro n
  induction n with
  | zero =>
    intro ε hε₀ε _ hεn B hεB
    exact hbase 0 ε hε₀ε (by simpa using hεn) B hεB
  | succ n ih =>
    intro ε hε₀ε hε1 hεn B hεB
    by_cases h99 : 99 / 100 ≤ ε
    · exact hbase (n + 1) ε hε₀ε h99 B hεB
    push Not at h99
    have hε0 : 0 < ε := hε₀.trans_le hε₀ε
    have hB0 : 0 < B := hε0.trans_le hεB
    have hθ0 := si_θ_pos
    -- the next level
    have hε'1 := si_eps_le_one hε0 h99
    have hε'0 := si_eps_ge hε0
    have hε'n : 99 / 100 - n * (swapTheta * ε₀ ^ 4 / 4) ≤ swapEpsNext ε := by
      have h4 : ε₀ ^ 4 ≤ ε ^ 4 := pow_le_pow_left₀ hε₀.le hε₀ε 4
      have : swapTheta * ε₀ ^ 4 / 4 ≤ swapTheta * ε ^ 4 / 4 := by gcongr
      unfold swapEpsNext
      push_cast at hεn
      nlinarith
    have hB' : swapEpsNext ε ≤ swapBNext ε B := by
      have hx0 := si_XT_pos hε0
      have hD0 : 0 < swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) := by
        have := si_c_pos
        have := Real.sqrt_pos.2 hx0
        positivity
      have hD1 : swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) ≤ 1 := by
        have h1 : swapC ^ 7 ≤ 1 := pow_le_one₀ si_c_pos.le si_c_le_one
        have h2 : ε ^ 29 ≤ 1 := pow_le_one₀ hε0.le hε1
        have h3 : Real.sqrt (swapX ε ^ swapT ε) ≤ 1 :=
          Real.sqrt_le_one.2 (si_XT_le hε0 hε1)
        calc swapC ^ 7 * ε ^ 29 * Real.sqrt (swapX ε ^ swapT ε) ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
      have h27 : 27 * B ≤ swapBNext ε B := by
        unfold swapBNext
        rw [le_div_iff₀ hD0]
        nlinarith
      have h2 : swapEpsNext ε ≤ 2 * ε := by
        unfold swapEpsNext
        have h4 : ε ^ 4 ≤ ε := by
          calc ε ^ 4 = ε ^ 3 * ε := by ring
            _ ≤ 1 * ε := by gcongr; exact pow_le_one₀ hε0.le hε1
            _ = ε := one_mul ε
        have : swapTheta ≤ 1 := si_θ_le
        nlinarith
      linarith
    obtain ⟨ρ₁, δ', hρ0, hρ1, hδ0, hbρ, hbδ, hcl⟩ :=
      ih (swapEpsNext ε) (hε₀ε.trans hε'0) hε'1 hε'n (swapBNext ε B) hB'
    obtain ⟨hr, hd⟩ := si_step_bounds hM hq hε₀ hM' hε₀1 hε₀ε h99 hεB hbρ hbδ
    have hTpos : (0 : ℝ) < swapT ε := by exact_mod_cast si_T_pos hε0
    refine ⟨swapRhoNext ε ρ₁, swapDeltaNext ε B δ', ?_, ?_, ?_, ?_, ?_,
      si_claim_step hε0 h99 hεB hρ0 hρ1 hδ0 hcl⟩
    · unfold swapRhoNext
      positivity
    · unfold swapRhoNext
      rw [div_le_one (by positivity)]
      exact hρ1.trans (one_le_pow₀ (by norm_num))
    · unfold swapDeltaNext swapPGood
      have := si_γ_pos hε0
      have := si_XT_pos hε0
      have := si_c_pos
      positivity
    · refine le_trans ?_ hr
      rw [si_HH_step]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0.le hq1 (si_EE_step M n))
        (by positivity)
    · refine le_trans ?_ hd
      rw [si_HH_step]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0.le hq1 (si_EE_step M n))
        (by positivity)

/-- the induction of CSP_6 `thm:swap` closed: `(inductswap)` in the family form, with the
quantitative bound `thm:swap#recursion-solution`. -/
theorem swap_induction : ∃ K : ℕ, ∀ ε B : ℝ, 0 < ε → ε ≤ 1 → ε ≤ B →
    ∃ (ρ₀ δ : ℝ) (_ : 0 < ρ₀) (_ : ρ₀ ≤ 1) (_ : 0 < δ),
      (ε / (2 * B)) ^ (K * ⌈1 / ε⌉₊ ^ K) ≤ ρ₀ ∧ (ε / (2 * B)) ^ (K * ⌈1 / ε⌉₊ ^ K) ≤ δ ∧
      ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι]
        [DecidableEq ι] (f : (ι → α) → ℂ), (∀ x, ‖f x‖ ≤ B) → l2sq f ≤ 1 →
        ε ^ 4 ≤ (val f f f f).re →
        ∀ (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), ρ ≤ ρ₀ → δ ≤ swapRestrExp ρ h0 h1 f := by
  obtain ⟨K, hK1, hK⟩ := swapInd_poly
  refine ⟨K, fun ε B hε0 hε1 hεB => ?_⟩
  have hB0 : 0 < B := hε0.trans_le hεB
  obtain ⟨M, hMd⟩ : ∃ M, M = ⌈1 / ε⌉₊ := ⟨_, rfl⟩
  rw [← hMd]
  have hM : 1 ≤ M := by
    rw [hMd]
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM' : 1 / (M : ℝ) ≤ ε := by
    have h := Nat.le_ceil (1 / ε)
    rw [← hMd] at h
    rw [div_le_iff₀ hMpos]
    rw [div_le_iff₀ hε0] at h
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = ε / (2 * B) := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1 : a ≤ 1 := ha2.trans (by norm_num)
  have hKM : 1 ≤ K * M ^ K := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  by_cases h99 : 99 / 100 ≤ ε
  · have hle : a ^ (K * M ^ K) ≤ a := pow_le_of_le_one ha0.le ha1 (by omega)
    refine ⟨1, (3 / 4) / B, one_pos, le_rfl, by positivity, hle.trans ha1, ?_, ?_⟩
    · refine hle.trans ?_
      rw [ha, div_le_div_iff₀ (by positivity) hB0]
      nlinarith
    · intro α _ _ _ ι _ _ f hB hl2 hv ρ h0 h1 _
      exact swap_base_case hB0 h99 ρ h0 h1 f hB hl2 hv
  push Not at h99
  obtain ⟨q, hq⟩ : ∃ q, q = (1 / 2 : ℝ) ^ (M + 50) := ⟨_, rfl⟩
  have hN : 99 / 100 - (swapIndN M : ℕ) * (swapTheta * ε ^ 4 / 4) ≤ ε := by
    have e : ((swapIndN M : ℕ) : ℝ) * (swapTheta * ε ^ 4 / 4) = ((M : ℝ) * ε) ^ 4 := by
      unfold swapIndN swapTheta
      push_cast
      ring
    have hMε : 1 ≤ (M : ℝ) * ε := by
      rw [div_le_iff₀ hMpos] at hM'
      linarith
    have : 1 ≤ ((M : ℝ) * ε) ^ 4 := one_le_pow₀ hMε
    rw [e]
    linarith
  obtain ⟨ρ₀, δ, hρ0, hρ1, hδ0, hbρ, hbδ, hcl⟩ :=
    si_induction hε0 hε1 hM hM' hq (swapIndN M) ε le_rfl hε1 hN B hεB
  rw [← ha] at hbρ hbδ
  have hfin : a ^ (K * M ^ K) ≤ q ^ swapIndEE M (swapIndN M) * a ^ swapIndHH M (swapIndN M) := by
    have hqa : a ^ (M + 50) ≤ q := by
      rw [hq]
      exact pow_le_pow_left₀ ha0.le ha2 _
    calc a ^ (K * M ^ K) ≤ a ^ ((M + 50) * swapIndEE M (swapIndN M) +
          swapIndHH M (swapIndN M)) := pow_le_pow_of_le_one ha0.le ha1 (hK M hM)
      _ = (a ^ (M + 50)) ^ swapIndEE M (swapIndN M) * a ^ swapIndHH M (swapIndN M) := by
          rw [pow_add, pow_mul]
      _ ≤ q ^ swapIndEE M (swapIndN M) * a ^ swapIndHH M (swapIndN M) := by gcongr
  exact ⟨ρ₀, δ, hρ0, hρ1, hδ0, hfin.trans hbρ, hfin.trans hbδ, hcl⟩

/-! ### From expectation to probability -/

/-- `swapCorrSup u ≤ B` and the witness property for a `B`-bounded `u`. -/
private theorem si_corrSup_facts {α κ : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖u x‖ ≤ B) :
    swapCorrSup u ≤ B ∧ ∀ r : ℝ, r < swapCorrSup u →
      ∃ P : κ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧ r < swapProdCorr u P := by
  have hne : {r : ℝ | ∃ P : κ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
      r = swapProdCorr u P}.Nonempty := ⟨_, fun _ _ => 0, fun i => by simp, rfl⟩
  constructor
  · refine csSup_le hne ?_
    rintro r ⟨P, hP, rfl⟩
    exact (swapInd_corr_le_sqrt u P hP univ).trans (swapInd_sqrt_l2sq_le u hB0 hB)
  · intro r hr
    obtain ⟨r', ⟨P, hP, rfl⟩, hr'⟩ := exists_lt_of_lt_csSup hne hr
    exact ⟨P, hP, hr'⟩

open scoped Classical in
/-- CSP_6 `thm:swap` with `thm:swap#expectation-to-probability` and `#recursion-solution`. -/
theorem swap_theorem : ∃ K : ℕ, ∀ ε B : ℝ, 0 < ε → ε ≤ 1 → ε ≤ B →
    ∃ (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1), (ε / (2 * B)) ^ (K * ⌈1 / ε⌉₊ ^ K) ≤ δ ∧
      ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι]
        [DecidableEq ι] (f : (ι → α) → ℂ), (∀ x, ‖f x‖ ≤ B) → l2sq f ≤ 1 →
        ε ^ 4 ≤ (val f f f f).re →
        δ ≤ (subsetExpect (1 - δ) (by linarith) (by linarith) fun I =>
          ((FinProb.uniform (α := α)).pi ↥I).cexpect fun z =>
            if ∃ P : ↥Iᶜ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
                δ ≤ swapProdCorr (restrictFix I z f) P then (1 : ℂ) else 0).re := by
  obtain ⟨K, hK⟩ := swap_induction
  refine ⟨K + 2, fun ε B hε0 hε1 hεB => ?_⟩
  obtain ⟨ρ₀, δ₀, hρ0, hρ1, hδ0, hbρ, hbδ, hcl⟩ := hK ε B hε0 hε1 hεB
  have hB0 : 0 < B := hε0.trans_le hεB
  obtain ⟨a, ha⟩ : ∃ a, a = ε / (2 * B) := ⟨_, rfl⟩
  rw [← ha] at hbρ hbδ ⊢
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1 : a ≤ 1 := ha2.trans (by norm_num)
  have haB : a ≤ 1 / (2 * B) := by
    rw [ha]
    exact div_le_div_of_nonneg_right hε1 (by positivity)
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = min ρ₀ (min (δ₀ / (2 * B)) (δ₀ / 4)) := ⟨_, rfl⟩
  have hδρ : δ ≤ ρ₀ := hδd ▸ min_le_left _ _
  have hδB : δ ≤ δ₀ / (2 * B) := hδd ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ δ₀ / 4 := hδd ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hδ0 : 0 < δ := by
    rw [hδd]
    exact lt_min hρ0 (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  refine ⟨δ, hδ0, hδ1, ?_, ?_⟩
  · -- the quantitative bound
    obtain ⟨M, hMd⟩ : ∃ M, M = ⌈1 / ε⌉₊ := ⟨_, rfl⟩
    rw [← hMd] at hbρ hbδ ⊢
    have hM : 1 ≤ M := by
      rw [hMd]
      exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
    have hexp : K * M ^ K + 2 ≤ (K + 2) * M ^ (K + 2) := by
      have h1 : M ^ K ≤ M ^ (K + 2) := Nat.pow_le_pow_right hM (by omega)
      have h2 : 1 ≤ M ^ K := Nat.one_le_pow _ _ hM
      nlinarith
    have hlow : a ^ (K * M ^ K) * a ^ 2 ≤ δ := by
      have hA0 : 0 ≤ a ^ (K * M ^ K) := by positivity
      have ha22 : a ^ 2 ≤ 1 / 4 := by nlinarith
      rw [hδd]
      refine le_min ?_ (le_min ?_ ?_)
      · exact le_trans (mul_le_of_le_one_right hA0 (pow_le_one₀ ha0.le ha1)) hbρ
      · calc a ^ (K * M ^ K) * a ^ 2 ≤ δ₀ * (1 / (2 * B)) := by
              refine mul_le_mul hbδ ?_ (by positivity) (hA0.trans hbδ)
              calc a ^ 2 ≤ a := by nlinarith
                _ ≤ 1 / (2 * B) := haB
          _ = δ₀ / (2 * B) := by ring
      · calc a ^ (K * M ^ K) * a ^ 2 ≤ δ₀ * (1 / 4) :=
              mul_le_mul hbδ ha22 (by positivity) (hA0.trans hbδ)
          _ = δ₀ / 4 := by ring
    calc a ^ ((K + 2) * M ^ (K + 2)) ≤ a ^ (K * M ^ K + 2) :=
          pow_le_pow_of_le_one ha0.le ha1 hexp
      _ = a ^ (K * M ^ K) * a ^ 2 := pow_add _ _ _
      _ ≤ δ := hlow
  · -- the probability
    intro α _ _ _ ι _ _ f hB hl2 hv
    have hmain := hcl α ι f hB hl2 hv δ hδ0.le hδ1 hδρ
    have hδ0' : 0 < δ₀ := lt_of_lt_of_le (by positivity) hbδ
    have hpt : ∀ (I : Finset ι) (z : ↥I → α),
        swapCorrSup (restrictFix I z f) ≤
          B * (if ∃ P : ↥Iᶜ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
            δ ≤ swapProdCorr (restrictFix I z f) P then (1 : ℝ) else 0) + δ₀ / 2 := by
      intro I z
      obtain ⟨hsB, hwit⟩ := si_corrSup_facts (restrictFix I z f) hB0.le fun y => hB _
      split_ifs with hev
      · linarith
      · by_contra hlt
        push Not at hlt
        obtain ⟨P, hP, hr⟩ := hwit δ (by linarith)
        exact hev ⟨P, hP, hr.le⟩
    have hind : ∀ (I : Finset ι) (z : ↥I → α),
        (if ∃ P : ↥Iᶜ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
            δ ≤ swapProdCorr (restrictFix I z f) P then (1 : ℂ) else 0) =
          (((if ∃ P : ↥Iᶜ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
            δ ≤ swapProdCorr (restrictFix I z f) P then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      intro I z
      split_ifs <;> simp
    simp_rw [hind]
    unfold swapRestrExp at hmain
    rw [swapInd_subsetExpect_re] at hmain ⊢
    have hle := FinProb.expect_mono ((bernoulli (1 - δ) (by linarith) (by linarith)).pi ι)
      (fun b => FinProb.expect_mono ((FinProb.uniform (α := α)).pi ↥(trueSet b))
        (hpt (trueSet b)))
    simp only [FinProb.expect_add, FinProb.expect_const_mul, FinProb.expect_const] at hle
    have h2 := hmain.trans hle
    refine hδB.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith

end SwapInductFinal
end TrackB
end RestrictedPolynomials
end
