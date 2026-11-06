module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import RestrictedPolynomials.Dimitrov.DubininDefs
public import RestrictedPolynomials.Dimitrov.DubininLevel
public import RestrictedPolynomials.Dimitrov.DubininArcsine
public import RestrictedPolynomials.Dimitrov.DubininPairing

/-!
# The symmetric test function `u*` (Supplement C, Proposition 5.2, `prop:symtest`)

Source: Supplement C, Proposition `prop:symtest` (for `|z₀| > r'` the bound `U^ν ≤ -log(|z| - R)` gives
`G > β` strictly).

With `G = -log c* - U^ν`, `β = log((r' - R)/c*)` and `u* = min 1 (max 0 ((β - G)/(β - α)))`:

* (i) `u* = 1` on the open set `{G < α} ⊇ K*` (lower semicontinuity of `U^ν`, `U^ν = -log c*` on `K*`);
* (ii) `u* = 0` for `‖z‖ ≥ r'`;
* (iii) `u*` is Lipschitz: it has locally a uniform Lipschitz constant (constant near `K*`, constant
  where `G > β`, and `G` is `C¹` near the compact set `{G ≥ α} ∩ B̄(0,r') ⊆ K*ᶜ`), and a uniform local
  constant gives a global one along segments (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`);
* (iv) `D_N`-invariance, from `arcsinePotential_rootN_mul` and `arcsinePotential_conj`;
* (v) `Dir(u*) = 2π/(β-α)`: a.e. on `K*ᶜ`, `⟨∇u*, ∇U⟩ = (β-α) |∇u*|²`, and `arcsine_pairing` gives
  `∫_{K*ᶜ} ⟨∇u*, ∇U⟩ = 2π`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Real ContDiff

noncomputable section

namespace RestrictedPolynomials

/-- `G = -log c* - U^ν`. -/
private def Gfun (N : ℕ) (R : ℝ) (z : ℂ) : ℝ :=
  -Real.log (starRadius N R) - arcsinePotential N R z

/-- `β = log((r' - R)/c*)`. -/
private def betaOf (N : ℕ) (R r' : ℝ) : ℝ := Real.log ((r' - R) / starRadius N R)

private lemma symTest_eq (N : ℕ) (R r' α : ℝ) (z : ℂ) :
    symTest N R r' α z =
      min 1 (max 0 ((betaOf N R r' - Gfun N R z) / (betaOf N R r' - α))) := rfl

private lemma starRadius_pos {N : ℕ} {R : ℝ} (hR : 0 < R) : 0 < starRadius N R := by
  unfold starRadius; positivity

/-- A uniform local Lipschitz constant gives a global one. -/
private lemma lipschitzWith_of_local {f : ℂ → ℝ} {M : NNReal}
    (h : ∀ z₀, ∃ ε > 0, LipschitzOnWith M f (Metric.ball z₀ ε)) : LipschitzWith M f := by
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro z₀
    obtain ⟨ε, hε, hl⟩ := h z₀
    exact hl.continuousOn.continuousAt (Metric.ball_mem_nhds _ hε)
  have key : ∀ p q : ℂ, f q - f p ≤ M * dist q p := by
    intro p q
    let g : ℝ → ℂ := fun t => p + t • (q - p)
    have hg : Continuous g := by fun_prop
    let S : Set ℝ := {t | f (g t) - f (g 0) ≤ M * t * ‖q - p‖}
    have hSc : IsClosed (S ∩ Set.Icc (0 : ℝ) 1) :=
      (isClosed_le ((hcont.comp hg).sub continuous_const)
        ((continuous_const.mul continuous_id).mul continuous_const)).inter isClosed_Icc
    have h0 : (0 : ℝ) ∈ S := by simp [S]
    have hgt : ∀ x ∈ S ∩ Set.Ico (0 : ℝ) 1, S ∈ 𝓝[>] x := by
      rintro x ⟨hx2, hx3⟩
      obtain ⟨ε, hε, hl⟩ := h (g x)
      have hnb : ∀ᶠ t in 𝓝 x, g t ∈ Metric.ball (g x) ε :=
        hg.continuousAt.eventually (Metric.ball_mem_nhds _ hε)
      have h1 : ∀ᶠ t in 𝓝[>] x, g t ∈ Metric.ball (g x) ε := nhdsWithin_le_nhds hnb
      have h2 : ∀ᶠ t in 𝓝[>] x, t ∈ Set.Ico x 1 := Ico_mem_nhdsGT hx3.2
      have h3 : ∀ᶠ t in 𝓝[>] x, x < t := self_mem_nhdsWithin
      filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
      show f (g t) - f (g 0) ≤ M * t * ‖q - p‖
      have hd : dist (g t) (g x) = |t - x| * ‖q - p‖ := by
        simp only [g, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have := hl.dist_le_mul (g t) ht1 (g x) (Metric.mem_ball_self hε)
      rw [hd, Real.dist_eq] at this
      have habs : |t - x| = t - x := abs_of_pos (by linarith)
      rw [habs] at this
      have := (le_abs_self _).trans this
      have hx2' : f (g x) - f (g 0) ≤ M * x * ‖q - p‖ := hx2
      have e : (M : ℝ) * ((t - x) * ‖q - p‖) = M * t * ‖q - p‖ - M * x * ‖q - p‖ := by ring
      linarith
    have hsub := hSc.Icc_subset_of_forall_mem_nhdsWithin h0 hgt
    have h1S : (1 : ℝ) ∈ S := hsub ⟨zero_le_one, le_rfl⟩
    have this : f (g 1) - f (g 0) ≤ M * (1 : ℝ) * ‖q - p‖ := h1S
    simp only [g, zero_smul, add_zero, one_smul, add_sub_cancel, mul_one] at this
    rw [dist_eq_norm]
    exact this
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.dist_eq, abs_le]
  constructor
  · have := key p q
    rw [dist_comm] at this
    linarith
  · exact key q p

private lemma clamp_lipschitz (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have h : LipschitzWith 1 (fun t : ℝ => min 1 (max 0 t)) :=
    (LipschitzWith.id.const_max 0).const_min 1
  have := h.dist_le_mul a b
  simpa [Real.dist_eq] using this

private lemma gradient_inner_of_smul {u U : ℂ → ℝ} {z : ℂ} {a : ℝ}
    (h : fderiv ℝ u z = a • fderiv ℝ U z) :
    inner ℝ (gradient u z) (gradient U z) = a * ‖fderiv ℝ U z‖ ^ 2 := by
  have h1 : gradient u z = a • gradient U z := by
    simp only [gradient, h, map_smul]
  have h2 : ‖gradient U z‖ = ‖fderiv ℝ U z‖ := by
    simp only [gradient]
    exact (InnerProductSpace.toDual ℝ ℂ).symm.norm_map _
  rw [h1, real_inner_smul_left, real_inner_self_eq_norm_sq, h2]

private lemma gradient_eq_zero_of_fderiv {u : ℂ → ℝ} {z : ℂ} (h : fderiv ℝ u z = 0) :
    gradient u z = 0 := by
  simp [gradient, h]

section C7
variable {N : ℕ} {R : ℝ}

private lemma Gfun_eq_zero_of_mem (hN : 1 ≤ N) (hR : 0 < R) {z : ℂ} (hz : z ∈ starSet N R) :
    Gfun N R z = 0 := by
  simp [Gfun, arcsinePotential_of_mem_starSet hN hR hz]

private lemma beta_le_Gfun (hN : 1 ≤ N) (hR : 0 < R) {r' : ℝ} (hr : R < r') {z : ℂ}
    (hz : r' ≤ ‖z‖) : betaOf N R r' ≤ Gfun N R z := by
  have hc := starRadius_pos (N := N) hR
  have h1 := arcsinePotential_le hN hR (z := z) (by linarith)
  have h2 : Real.log (r' - R) ≤ Real.log (‖z‖ - R) :=
    Real.log_le_log (by linarith) (by linarith)
  unfold betaOf Gfun
  rw [Real.log_div (by linarith) hc.ne']
  linarith

private lemma beta_lt_Gfun (hN : 1 ≤ N) (hR : 0 < R) {r' : ℝ} (hr : R < r') {z : ℂ}
    (hz : r' < ‖z‖) : betaOf N R r' < Gfun N R z := by
  have hc := starRadius_pos (N := N) hR
  have h1 := arcsinePotential_le hN hR (z := z) (by linarith)
  have h2 : Real.log (r' - R) < Real.log (‖z‖ - R) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold betaOf Gfun
  rw [Real.log_div (by linarith) hc.ne']
  linarith

private lemma symTest_eq_zero_of_beta_le {r' α : ℝ} (hD : 0 < betaOf N R r' - α) {z : ℂ}
    (h : betaOf N R r' ≤ Gfun N R z) : symTest N R r' α z = 0 := by
  rw [symTest_eq]
  have : (betaOf N R r' - Gfun N R z) / (betaOf N R r' - α) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
  rw [max_eq_left this]
  simp

private lemma symTest_eq_one_of_lt {r' α : ℝ} (hD : 0 < betaOf N R r' - α) {z : ℂ}
    (h : Gfun N R z < α) : symTest N R r' α z = 1 := by
  rw [symTest_eq]
  have : 1 ≤ (betaOf N R r' - Gfun N R z) / (betaOf N R r' - α) := by
    rw [le_div_iff₀ hD]; linarith
  rw [max_eq_right (by linarith)]
  exact min_eq_left this

private lemma isOpen_Gfun_lt (hN : 1 ≤ N) (hR : 0 < R) (α : ℝ) : IsOpen {z | Gfun N R z < α} := by
  have := (lowerSemicontinuous_iff_isOpen_preimage.mp
    (lowerSemicontinuous_arcsinePotential hN hR)) (-Real.log (starRadius N R) - α)
  convert this using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, Gfun]
  constructor <;> intro h <;> linarith

private lemma symTest_lipschitz (hN : 1 ≤ N) (hR : 0 < R) {r' α : ℝ} (hr : R + starRadius N R < r')
    (hα0 : 0 < α) (hαβ : α < betaOf N R r') :
    ∃ K : NNReal, LipschitzWith K (symTest N R r' α) := by
  have hc := starRadius_pos (N := N) hR
  have hRr : R < r' := by linarith
  set β := betaOf N R r' with hβdef
  have hD : 0 < β - α := by linarith
  set W : Set ℂ := (starSet N R)ᶜ with hWdef
  have hW : IsOpen W := (isClosed_starSet hN).isOpen_compl
  have hUcd : ContDiffOn ℝ ∞ (arcsinePotential N R) W := contDiffOn_arcsinePotential hN hR
  have hdiffW : ∀ z ∈ W, DifferentiableAt ℝ (arcsinePotential N R) z := fun z hz =>
    (hUcd.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
  have hGdiffW : ∀ z ∈ W, DifferentiableAt ℝ (Gfun N R) z := fun z hz =>
    (differentiableAt_const _).sub (hdiffW z hz)
  have hfdU : ContinuousOn (fun z => fderiv ℝ (arcsinePotential N R) z) W :=
    hUcd.continuousOn_fderiv_of_isOpen hW (by simp)
  have hfdG : ∀ z ∈ W, fderiv ℝ (Gfun N R) z = -fderiv ℝ (arcsinePotential N R) z := by
    intro z hz
    have := ((hasFDerivAt_const (-Real.log (starRadius N R)) z).sub
      (hdiffW z hz).hasFDerivAt).fderiv
    rw [show Gfun N R = (fun _ => -Real.log (starRadius N R)) - arcsinePotential N R from rfl]
    simpa using this
  have hfdGc : ContinuousOn (fun z => fderiv ℝ (Gfun N R) z) W :=
    (hfdU.neg).congr fun z hz => hfdG z hz
  have hGcont : ContinuousOn (Gfun N R) W := fun z hz => (hGdiffW z hz).continuousAt.continuousWithinAt
  -- the compact set T
  have hTcl : IsClosed {z | α ≤ Gfun N R z} := by
    have := (lowerSemicontinuous_arcsinePotential hN hR).isClosed_preimage
      (-Real.log (starRadius N R) - α)
    convert this using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, Gfun]
    constructor <;> intro h <;> linarith
  have hTc : IsCompact ({z | α ≤ Gfun N R z} ∩ Metric.closedBall (0 : ℂ) r') :=
    (isCompact_closedBall (0 : ℂ) r').inter_left hTcl
  have hTW : {z | α ≤ Gfun N R z} ∩ Metric.closedBall (0 : ℂ) r' ⊆ W := by
    rintro z ⟨hz, -⟩ hzK
    have := Gfun_eq_zero_of_mem hN hR hzK
    simp only [Set.mem_ofPred_eq] at hz
    linarith
  obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn (hfdGc.mono hTW)
  set Mg : NNReal := Real.toNNReal (max C 0 + 1) with hMg
  have hMgr : (Mg : ℝ) = max C 0 + 1 := Real.coe_toNNReal _ (by positivity)
  set K : NNReal := Real.toNNReal ((max C 0 + 1) / (β - α)) with hK
  have hKr : (K : ℝ) = (max C 0 + 1) / (β - α) := Real.coe_toNNReal _ (by positivity)
  refine ⟨K, lipschitzWith_of_local fun z₀ => ?_⟩
  by_cases hA : Gfun N R z₀ < α
  · -- constant near `z₀`
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_Gfun_lt hN hR α) z₀ hA
    refine ⟨ε, hε, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [symTest_eq_one_of_lt hD (hball hx), symTest_eq_one_of_lt hD (hball hy)]
    simp only [dist_self]
    positivity
  by_cases hB : β < Gfun N R z₀
  · have hz0W : z₀ ∈ W := by
      intro hzK
      have := Gfun_eq_zero_of_mem hN hR hzK
      linarith
    have hnb : ∀ᶠ z in 𝓝 z₀, β ≤ Gfun N R z :=
      ((hGcont z₀ hz0W).continuousAt (hW.mem_nhds hz0W)).eventually (lt_mem_nhds hB) |>.mono
        fun z hz => hz.le
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnb
    refine ⟨ε, hε, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [symTest_eq_zero_of_beta_le hD (hball x hx), symTest_eq_zero_of_beta_le hD (hball y hy)]
    simp only [dist_self]
    positivity
  · push Not at hA hB
    have hz0W : z₀ ∈ W := by
      intro hzK
      have := Gfun_eq_zero_of_mem hN hR hzK
      linarith
    have hz0r : ‖z₀‖ ≤ r' := by
      by_contra hcon
      push Not at hcon
      have := beta_lt_Gfun hN hR hRr hcon
      linarith
    have hz0T : z₀ ∈ {z | α ≤ Gfun N R z} ∩ Metric.closedBall (0 : ℂ) r' :=
      ⟨hA, by simpa using hz0r⟩
    have hbd := hC z₀ hz0T
    have hcn : ContinuousAt (fun z => ‖fderiv ℝ (Gfun N R) z‖) z₀ :=
      ((hfdGc.continuousAt (hW.mem_nhds hz0W)).norm)
    have hev1 : ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ (Gfun N R) z‖ < ‖fderiv ℝ (Gfun N R) z₀‖ + 1 :=
      hcn.eventually (gt_mem_nhds (by linarith))
    have hev2 : ∀ᶠ z in 𝓝 z₀, z ∈ W := hW.mem_nhds hz0W
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev1.and hev2)
    have hlipG : LipschitzOnWith Mg (Gfun N R) (Metric.ball z₀ ε) := by
      refine (convex_ball z₀ ε).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun z hz => hGdiffW z (hball z hz).2) (fun z hz => ?_)
      have h1 := (hball z hz).1
      rw [← NNReal.coe_le_coe, coe_nnnorm, hMgr]
      have : C ≤ max C 0 := le_max_left _ _
      linarith
    refine ⟨ε, hε, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    have h1 := hlipG.dist_le_mul x hx y hy
    rw [Real.dist_eq] at h1 ⊢
    rw [symTest_eq, symTest_eq]
    refine (clamp_lipschitz _ _).trans ?_
    have : (β - Gfun N R x) / (β - α) - (β - Gfun N R y) / (β - α) =
        (Gfun N R y - Gfun N R x) / (β - α) := by ring
    rw [this, abs_div, abs_of_pos hD, hKr, div_le_iff₀ hD]
    have h2 : |Gfun N R y - Gfun N R x| ≤ Mg * dist x y := by
      rw [abs_sub_comm]; simpa [Real.dist_eq] using h1
    rw [hMgr] at h2
    calc |Gfun N R y - Gfun N R x| ≤ (max C 0 + 1) * dist x y := h2
      _ = _ := by field_simp

/-- The Dirichlet integrand of a Lipschitz function vanishing outside a ball is integrable. -/
lemma integrable_dirichlet_integrand {u : ℂ → ℝ} {L : NNReal} (hu : LipschitzWith L u) {r' : ℝ}
    (h0 : ∀ z, r' ≤ ‖z‖ → u z = 0) : Integrable (fun z => ‖fderiv ℝ u z‖ ^ 2) := by
  have hmeas : Measurable fun z => ‖fderiv ℝ u z‖ ^ 2 :=
    ((measurable_fderiv ℝ u).norm).pow_const 2
  have hzero : ∀ z ∉ Metric.closedBall (0 : ℂ) r', fderiv ℝ u z = 0 := by
    intro z hz
    have hz' : r' < ‖z‖ := by simpa using hz
    have hev : u =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      have : ∀ᶠ y in 𝓝 z, r' < ‖y‖ := (continuous_norm.continuousAt).eventually (lt_mem_nhds hz')
      filter_upwards [this] with y hy using h0 y hy.le
    rw [hev.fderiv_eq]; simp
  refine Integrable.mono' (g := (Metric.closedBall (0 : ℂ) r').indicator fun _ => (L : ℝ) ^ 2)
    ((integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const measure_closedBall_lt_top.ne)) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) r'
  · rw [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ‖fderiv ℝ u z‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hu
    gcongr
  · rw [Set.indicator_of_notMem hz, hzero z hz]; simp

/-- Proposition 5.2 of Supplement C (`prop:symtest`). -/
theorem symTest_spec (hN : 1 ≤ N) (hR : 0 < R) {r' α : ℝ} (hr : R + starRadius N R < r')
    (hα0 : 0 < α) (hαβ : α < Real.log ((r' - R) / starRadius N R)) :
    (IsOpen {z | -Real.log (starRadius N R) - arcsinePotential N R z < α} ∧
      starSet N R ⊆ {z | -Real.log (starRadius N R) - arcsinePotential N R z < α} ∧
      ∀ z, -Real.log (starRadius N R) - arcsinePotential N R z < α → symTest N R r' α z = 1) ∧
    (∀ z, r' ≤ ‖z‖ → symTest N R r' α z = 0) ∧
    (∃ K : NNReal, LipschitzWith K (symTest N R r' α)) ∧
    (∀ z, symTest N R r' α (rootN N * z) = symTest N R r' α z ∧
      symTest N R r' α (starRingEnd ℂ z) = symTest N R r' α z) ∧
    dirichletEnergy (symTest N R r' α) =
      2 * Real.pi / (Real.log ((r' - R) / starRadius N R) - α) := by
  have hc := starRadius_pos (N := N) hR
  have hRr : R < r' := by linarith
  have hαβ' : α < betaOf N R r' := hαβ
  have hD : 0 < betaOf N R r' - α := by linarith
  have hopen := isOpen_Gfun_lt hN hR α
  have hsub : starSet N R ⊆ {z | Gfun N R z < α} := fun z hz => by
    show Gfun N R z < α
    rw [Gfun_eq_zero_of_mem hN hR hz]; exact hα0
  have hone : ∀ z, Gfun N R z < α → symTest N R r' α z = 1 := fun z hz =>
    symTest_eq_one_of_lt hD hz
  have hzero : ∀ z, r' ≤ ‖z‖ → symTest N R r' α z = 0 := fun z hz =>
    symTest_eq_zero_of_beta_le hD (beta_le_Gfun hN hR hRr hz)
  obtain ⟨K, hK⟩ := symTest_lipschitz hN hR hr hα0 hαβ'
  refine ⟨⟨hopen, hsub, hone⟩, hzero, ⟨K, hK⟩, ?_, ?_⟩
  · intro z
    constructor
    · simp only [symTest_eq, Gfun, arcsinePotential_rootN_mul hN hR]
    · simp only [symTest_eq, Gfun, arcsinePotential_conj hN hR]
  -- Dirichlet energy
  set u := symTest N R r' α with hu
  set β := betaOf N R r' with hβ
  have hcs : HasCompactSupport u := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r') fun z hz => ?_
    refine hzero z ?_
    by_contra hcon
    exact hz (by simpa using (not_le.mp hcon).le)
  obtain ⟨-, hpair⟩ := arcsine_pairing hN hR hK hcs hopen hsub (fun z hz => hone z hz)
  set W : Set ℂ := (starSet N R)ᶜ with hWdef
  have hW : IsOpen W := (isClosed_starSet hN).isOpen_compl
  have hUcd : ContDiffOn ℝ ∞ (arcsinePotential N R) W := contDiffOn_arcsinePotential hN hR
  have hdiffW : ∀ z ∈ W, DifferentiableAt ℝ (arcsinePotential N R) z := fun z hz =>
    (hUcd.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
  have hxcont : ∀ z ∈ W, ContinuousAt (fun y => (β - Gfun N R y) / (β - α)) z := by
    intro z hz
    have := (hdiffW z hz).continuousAt
    unfold Gfun
    fun_prop
  -- the pointwise identity a.e. on `W`
  have hae : ∀ᵐ z : ℂ, z ∈ W →
      inner ℝ (gradient u z) (gradient (arcsinePotential N R) z) =
        (β - α) * ‖fderiv ℝ u z‖ ^ 2 := by
    filter_upwards [fderiv_eq_zero_ae_level hK 1, fderiv_eq_zero_ae_level hK 0] with z h1 h0 hz
    by_cases e1 : u z = 1
    · have := h1 e1
      rw [gradient_eq_zero_of_fderiv this, this]; simp
    by_cases e0 : u z = 0
    · have := h0 e0
      rw [gradient_eq_zero_of_fderiv this, this]; simp
    set x : ℂ → ℝ := fun y => (β - Gfun N R y) / (β - α) with hx
    have hxz : 0 < x z ∧ x z < 1 := by
      constructor
      · by_contra hcon
        push Not at hcon
        apply e0
        show min 1 (max 0 (x z)) = 0
        rw [max_eq_left hcon]; simp
      · by_contra hcon
        push Not at hcon
        apply e1
        show min 1 (max 0 (x z)) = 1
        rw [max_eq_right (by linarith)]; exact min_eq_left hcon
    have hev : ∀ᶠ y in 𝓝 z, 0 < x y ∧ x y < 1 := by
      have hc := hxcont z hz
      exact (hc.eventually (lt_mem_nhds hxz.1)).and (hc.eventually (gt_mem_nhds hxz.2))
    have heq : u =ᶠ[𝓝 z] x := by
      filter_upwards [hev] with y hy
      show min 1 (max 0 (x y)) = x y
      rw [max_eq_right hy.1.le]; exact min_eq_right hy.2.le
    have hfx : fderiv ℝ x z = (β - α)⁻¹ • fderiv ℝ (arcsinePotential N R) z := by
      have := (((hasFDerivAt_const β z).sub ((hasFDerivAt_const (-Real.log (starRadius N R)) z).sub
        (hdiffW z hz).hasFDerivAt)).const_mul (β - α)⁻¹).fderiv
      rw [show x = fun y => (β - α)⁻¹ * (β - (-Real.log (starRadius N R) - arcsinePotential N R y))
        from funext fun y => by simp only [hx, Gfun, div_eq_inv_mul]]
      simpa using this
    have hfu : fderiv ℝ u z = (β - α)⁻¹ • fderiv ℝ (arcsinePotential N R) z := by
      rw [heq.fderiv_eq, hfx]
    rw [gradient_inner_of_smul hfu, hfu, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    field_simp
  have h1 : ∫ z in W, inner ℝ (gradient u z) (gradient (arcsinePotential N R) z) =
      (β - α) * ∫ z in W, ‖fderiv ℝ u z‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_ae hW.measurableSet hae
  have h2 : ∫ z in W, ‖fderiv ℝ u z‖ ^ 2 = dirichletEnergy u := by
    unfold dirichletEnergy
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    have hzK : z ∈ starSet N R := by simpa [hWdef] using hz
    have hev : u =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hopen.mem_nhds (hsub hzK)) fun y hy => hone y hy
    rw [hev.fderiv_eq]; simp
  have hfinal : (β - α) * dirichletEnergy u = 2 * Real.pi := by
    rw [← h2, ← h1]; exact hpair
  show dirichletEnergy u = 2 * Real.pi / (β - α)
  rw [eq_div_iff hD.ne']
  linarith

end C7

end RestrictedPolynomials
