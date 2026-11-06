module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Track B: auxiliary lemmas for the bounded-product theorem

Source: CSP_6, l. 1183-1223.
* the classical fact `plancherel-R` (`bprod_plancherel_L1_L2`, general `L¹ ∩ L²` form; proved here from
  Mathlib's `L²` Fourier transform via tempered distributions);
* CSP_6 `lemma:exp` (`bprod_exists_smoothed_indicator`, l. 1186-1205; the Fourier transform on `ℝ`
  is Mathlib's `𝓕`);
* CSP_6 `thm:boundedprod#reduce-positive` (`boundedprod_reduce_positive`, l. 1183-1184, 1205-1206;
  strict hypothesis `δ < ‖𝔼 f ∏ Pᵢ‖`);
* CSP_6 `lemma:ad` (`bprodA`, `boundedprod_ad`, l. 1207-1223; modulus,
  upper tail `P > 16/δ²`, Hölder bound `(δ/4)(𝔼P²)^{3/4}`), with the stronger tail form
  `boundedprod_ad_tail`.

From Supplement F, `bprod_expect_prod_sq` and `boundedprod_tail_abs` are added as public lemmas.

The uniform measure on `ι → α` is `Finset.expect` over `Finset.univ`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexOrder FourierTransform
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section ExpSmoothed

open scoped SchwartzMap ContDiff Convolution

/-- `b(x) := ∫ c(θ) e^{2πiθx} dθ` (K6 `main.tex` l. 1188). -/
def bprodFourierSynth (c : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ θ : ℝ, c θ * Complex.exp (2 * Real.pi * Complex.I * ((θ : ℂ) * (x : ℂ)))

/-! ### Plancherel for `L¹ ∩ L²(ℝ)` -/

/-- `‖f‖² = ∫ ‖f x‖²` for `f ∈ L²(ℝ)`. -/
private theorem L2_norm_sq_eq_integral (f : Lp (α := ℝ) ℂ 2) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h1 : (inner ℂ f f : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [MeasureTheory.L2.inner_def] at h1
  have h2 : ∀ a, (inner ℂ (f a) (f a) : ℂ) = ((‖f a‖ ^ 2 : ℝ) : ℂ) := by
    intro a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [h2] at h1
  rw [integral_complex_ofReal] at h1
  exact_mod_cast h1.symm

/-- Self-adjointness of `𝓕` for an integrable `g` against a Schwartz function. -/
private theorem integral_smul_fourier_eq_flip (g : ℝ → ℂ) (h1 : Integrable g) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ θ, ψ θ • 𝓕 g θ = ∫ x, 𝓕 ψ x • g x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner h1 (ψ.integrable (μ := volume))
  simp only [smul_eq_mul] at this ⊢
  simp_rw [mul_comm (ψ _)]
  convert this using 1
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hflip]
  congr 1; ext x; rw [mul_comm, SchwartzMap.fourier_coe]; rfl

/-- For `g ∈ L¹ ∩ L²`, the pointwise transform `𝓕 g` agrees a.e. with the `L²` transform of the
class of `g` (both define the same tempered distribution). -/
private theorem fourier_ae_eq_fourier_toLp (g : ℝ → ℂ) (h1 : Integrable g) (h2 : MemLp g 2) :
    𝓕 g =ᵐ[volume] ((𝓕 (h2.toLp g) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) := by
  set G : Lp (α := ℝ) ℂ 2 := h2.toLp g with hG
  have hc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  refine ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    ((Lp.memLp (𝓕 G)).locallyIntegrable (by norm_num)) ?_
  intro φ hφ hφc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  set ψ : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hψdef
  have hψ : ∀ x, ψ x = (φ x : ℂ) := fun x => rfl
  have hsmul : ∀ (x : ℝ) (z : ℂ), φ x • z = ψ x • z := by
    intro x z; rw [hψ, Complex.real_smul]; rfl
  simp_rw [hsmul]
  rw [integral_smul_fourier_eq_flip g h1 ψ]
  have e1 : ∫ θ, ψ θ • (𝓕 G) θ =
      Lp.toTemperedDistribution (𝓕 G) ψ := by
    rw [Lp.toTemperedDistribution_apply]
  rw [e1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with x hx
  rw [hx]

/-- Classical fact `plancherel-R`: `∫|ĝ|² = ∫|g|²` for `g ∈ L¹ ∩ L²(ℝ)`,
`ĝ(θ) = ∫ g(x) e^{-2πiθx} dx` (Mathlib's `𝓕`). -/
theorem bprod_plancherel_L1_L2 (g : ℝ → ℂ) (h1 : Integrable g) (h2 : MemLp g 2) :
    MemLp (𝓕 g) 2 ∧ ∫ θ : ℝ, ‖𝓕 g θ‖ ^ 2 = ∫ x : ℝ, ‖g x‖ ^ 2 := by
  have hae := fourier_ae_eq_fourier_toLp g h1 h2
  refine ⟨(Lp.memLp _).ae_eq hae.symm, ?_⟩
  rw [integral_congr_ae (hae.mono fun x hx => by rw [hx]), ← L2_norm_sq_eq_integral,
    Lp.norm_fourier_eq, L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with x hx
  rw [hx]

/-! ### The smoothed indicator (CSP_6 `lemma:exp`) -/

/-- the indicator `I_{[A,B]}`, complex valued -/
private def bInd (A B : ℝ) : ℝ → ℂ := Set.indicator (Set.Icc A B) (fun _ => (1 : ℂ))

private theorem bInd_memLp (A B : ℝ) (p : ENNReal) : MemLp (bInd A B) p :=
  memLp_indicator_const p measurableSet_Icc.nullMeasurableSet _ (Or.inr (by simp))

private theorem bInd_integrable (A B : ℝ) : Integrable (bInd A B) :=
  memLp_one_iff_integrable.1 (bInd_memLp A B 1)

private theorem integral_norm_sq_bInd {A B : ℝ} (hAB : A ≤ B) :
    ∫ x, ‖bInd A B x‖ ^ 2 = B - A := by
  have : (fun x => ‖bInd A B x‖ ^ 2) = Set.indicator (Set.Icc A B) (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc A B <;> simp [bInd, hx]
  rw [this, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hAB]
  simp

/-- `(I_{[L,R]} * I_{[-η/2,η/2]})(x) = |[L,R] ∩ [x-η/2,x+η/2]|` (the trapezoid). -/
private theorem conv_bInd_eq (L R η x : ℝ) :
    (bInd L R ⋆[ContinuousLinearMap.mul ℂ ℂ] bInd (-(η / 2)) (η / 2)) x =
      ((max (min R (x + η / 2) - max L (x - η / 2)) 0 : ℝ) : ℂ) := by
  rw [MeasureTheory.convolution_def]
  have : ∀ t, (ContinuousLinearMap.mul ℂ ℂ) (bInd L R t) (bInd (-(η / 2)) (η / 2) (x - t)) =
      Set.indicator (Set.Icc (max L (x - η / 2)) (min R (x + η / 2))) (fun _ => (1 : ℂ)) t := by
    intro t
    simp only [ContinuousLinearMap.mul_apply', bInd, Set.indicator_apply, Set.mem_Icc,
      max_le_iff, le_min_iff]
    split_ifs with h1 h2 h3 h3 h2 h3 h3
    all_goals first
      | (exfalso; exact h3 ⟨⟨h1.1, by linarith [h2.2]⟩, h1.2, by linarith [h2.1]⟩)
      | (exfalso; exact h2 ⟨by linarith [h3.2.2], by linarith [h3.1.2]⟩)
      | (exfalso; exact h1 ⟨h3.1.1, h3.2.1⟩)
      | norm_num
  simp_rw [this]
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
  simp

/-- the trapezoid `|[L,R] ∩ [x-η/2,x+η/2]|` -/
private def bTrap (L R η x : ℝ) : ℝ := max (min R (x + η / 2) - max L (x - η / 2)) 0

private theorem bTrap_nonneg (L R η x : ℝ) : 0 ≤ bTrap L R η x := le_max_right _ _

private theorem bTrap_le {L R η : ℝ} (hη : 0 < η) (x : ℝ) : bTrap L R η x ≤ η := by
  unfold bTrap
  refine max_le ?_ hη.le
  have := min_le_right R (x + η / 2)
  have := le_max_right L (x - η / 2)
  linarith

private theorem bTrap_eq_eta {L R η x : ℝ} (hη : 0 < η) (h1 : L + η / 2 ≤ x)
    (h2 : x ≤ R - η / 2) : bTrap L R η x = η := by
  unfold bTrap
  have e1 : min R (x + η / 2) = x + η / 2 := min_eq_right (by linarith)
  have e2 : max L (x - η / 2) = x - η / 2 := max_eq_right (by linarith)
  rw [e1, e2, max_eq_left (by linarith)]
  ring

private theorem bTrap_eq_zero {L R η x : ℝ} (h : x ≤ L - η / 2 ∨ R + η / 2 ≤ x) :
    bTrap L R η x = 0 := by
  unfold bTrap
  apply max_eq_right
  rcases h with h | h
  · have := min_le_right R (x + η / 2)
    have := le_max_left L (x - η / 2)
    linarith
  · have := min_le_left R (x + η / 2)
    have := le_max_right L (x - η / 2)
    linarith

private theorem bTrap_continuous (L R η : ℝ) : Continuous (bTrap L R η) := by
  unfold bTrap
  fun_prop

/-- CSP_6 `lemma:exp` (l. 1186-1195). -/
theorem bprod_exists_smoothed_indicator {L R η : ℝ} (hLR : L ≤ R) (hη : 0 < η) :
    ∃ c : ℝ → ℂ, Integrable c ∧
      ∫ θ : ℝ, ‖c θ‖ ≤ ((R - L) / η) ^ (1 / 2 : ℝ) ∧
      (∀ x : ℝ, L + η / 2 ≤ x → x ≤ R - η / 2 → bprodFourierSynth c x = 1) ∧
      (∀ x : ℝ, x ≤ L - η / 2 ∨ R + η / 2 ≤ x → bprodFourierSynth c x = 0) ∧
      (∀ x : ℝ, 0 ≤ bprodFourierSynth c x ∧ bprodFourierSynth c x ≤ 1) := by
  set g := bInd L R with hg
  set h := bInd (-(η / 2)) (η / 2) with hh
  -- `b = η⁻¹ I_{[L,R]} * I_{[-η/2,η/2]}`, the trapezoid
  set b : ℝ → ℂ := fun x => ((η⁻¹ * bTrap L R η x : ℝ) : ℂ) with hbdef
  have hb_conv : b = (η⁻¹ : ℂ) • (g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) := by
    funext x
    simp only [hbdef, Pi.smul_apply, smul_eq_mul, hg, hh, conv_bInd_eq, bTrap]
    push_cast
    rfl
  have hgi : Integrable g := bInd_integrable L R
  have hhi : Integrable h := bInd_integrable _ _
  have hb_int : Integrable b := by
    rw [hb_conv]
    exact (hgi.integrable_convolution _ hhi).smul _
  have hb_cont : Continuous b := by
    have := bTrap_continuous L R η
    simp only [hbdef]
    fun_prop
  -- `c := 𝓕 b = η⁻¹ Î_{[L,R]} Î_{[-η/2,η/2]}` (convolution theorem)
  have hFb : 𝓕 b = fun θ => (η⁻¹ : ℂ) * (𝓕 g θ * 𝓕 h θ) := by
    rw [hb_conv]
    funext θ
    change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) ((η⁻¹ : ℂ) • _) θ = _
    rw [VectorFourier.fourierIntegral_const_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    exact Real.fourier_mul_convolution_eq hgi hhi θ
  obtain ⟨hFg2, hFg⟩ := bprod_plancherel_L1_L2 g hgi (bInd_memLp L R 2)
  obtain ⟨hFh2, hFh⟩ := bprod_plancherel_L1_L2 h hhi (bInd_memLp _ _ 2)
  rw [hg, integral_norm_sq_bInd hLR] at hFg
  rw [hh, integral_norm_sq_bInd (by linarith)] at hFh
  have hprod_int : Integrable (fun θ => 𝓕 g θ * 𝓕 h θ) := hFg2.integrable_mul hFh2
  have hc_int : Integrable (𝓕 b) := by
    rw [hFb]
    exact hprod_int.const_mul _
  -- Fourier inversion: `b(x) = ∫ c(θ) e^{2πiθx} dθ`
  have hinv : ∀ x, bprodFourierSynth (𝓕 b) x = b x := by
    intro x
    have := congrFun (Continuous.fourierInv_fourier_eq hb_cont hb_int hc_int) x
    rw [← this, Real.fourierInv_eq']
    unfold bprodFourierSynth
    congr 1
    funext θ
    rw [smul_eq_mul, mul_comm]
    congr 2
    simp
    ring
  refine ⟨𝓕 b, hc_int, ?_, ?_, ?_, ?_⟩
  · -- Cauchy-Schwarz and Plancherel for the two indicators
    rw [hFb]
    have hnorm : ∀ θ, ‖(η⁻¹ : ℂ) * (𝓕 g θ * 𝓕 h θ)‖ = η⁻¹ * (‖𝓕 g θ‖ * ‖𝓕 h θ‖) := by
      intro θ
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hη.le]
    simp_rw [hnorm]
    rw [integral_const_mul]
    have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (by simpa using hFg2) (by simpa using hFh2)
    simp only [Real.rpow_two] at hH
    rw [hFg, hFh] at hH
    have he : η / 2 - -(η / 2) = η := by ring
    rw [he] at hH
    calc η⁻¹ * ∫ θ, ‖𝓕 g θ‖ * ‖𝓕 h θ‖ ≤ η⁻¹ * ((R - L) ^ (1 / 2 : ℝ) * η ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hH (inv_nonneg.2 hη.le)
      _ = ((R - L) / η) ^ (1 / 2 : ℝ) := by
          rw [Real.div_rpow (sub_nonneg.2 hLR) hη.le]
          have hs : η ^ (1 / 2 : ℝ) * η ^ (1 / 2 : ℝ) = η := by
            rw [← Real.rpow_add hη]; norm_num
          have hspos : 0 < η ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hη _
          field_simp
          rw [sq, hs]
          ring
  · intro x h1 h2
    rw [hinv, hbdef]
    simp only
    rw [bTrap_eq_eta hη h1 h2, inv_mul_cancel₀ hη.ne']
    simp
  · intro x hx
    rw [hinv, hbdef]
    simp only
    rw [bTrap_eq_zero hx]
    simp
  · intro x
    rw [hinv, hbdef]
    have h0 : 0 ≤ η⁻¹ * bTrap L R η x := mul_nonneg (inv_nonneg.2 hη.le) (bTrap_nonneg _ _ _ _)
    have h1 : η⁻¹ * bTrap L R η x ≤ 1 := by
      rw [inv_mul_le_iff₀ hη, mul_one]
      exact bTrap_le hη x
    show (0 : ℂ) ≤ ((η⁻¹ * bTrap L R η x : ℝ) : ℂ) ∧ ((η⁻¹ * bTrap L R η x : ℝ) : ℂ) ≤ 1
    constructor
    · exact_mod_cast h0
    · exact_mod_cast h1

end ExpSmoothed

section BoundedProd
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- CSP_6 `thm:boundedprod#reduce-positive` (l. 1183-1184, 1205-1206): perturb `P` to a nowhere
vanishing `P̃ = QR` (with `R > 0`, `|Q| = 1`, `‖R_i‖₂ ≤ 1`) and absorb `ΠQ_i` into `f`. -/
theorem boundedprod_reduce_positive (f : (ι → α) → ℂ) (P : ι → α → ℂ)
    (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) {δ : ℝ}
    (hδ : δ < ‖𝔼 x : ι → α, f x * ∏ i, P i (x i)‖) :
    ∃ (Q : ι → α → ℂ) (R : ι → α → ℝ),
      (∀ i a, ‖Q i a‖ = 1) ∧ (∀ i a, 0 < R i a) ∧ (∀ i, 𝔼 a : α, R i a ^ 2 ≤ 1) ∧
      δ ≤ ‖𝔼 x : ι → α, (f x * ∏ i, Q i (x i)) * ∏ i, (R i (x i) : ℂ)‖ ∧
      (∀ x, ‖f x * ∏ i, Q i (x i)‖ = ‖f x‖) ∧
      (∀ P' : ι → α → ℂ, 𝔼 x : ι → α, f x * ∏ i, (Q i (x i) * P' i (x i)) =
        𝔼 x : ι → α, (f x * ∏ i, Q i (x i)) * ∏ i, P' i (x i)) := by
  -- the perturbation `P̃ = (1 - t) P + t`
  set Pt : ℝ → ι → α → ℂ := fun t i a => ((1 - t : ℝ) : ℂ) * P i a + (t : ℂ) with hPt
  set F : ℝ → ℂ := fun t => 𝔼 x : ι → α, f x * ∏ i, Pt t i (x i) with hF
  have hFcont : Continuous F := by
    simp only [hF, hPt, Fintype.expect_eq_sum_div_card]
    fun_prop
  have hF0 : F 0 = 𝔼 x : ι → α, f x * ∏ i, P i (x i) := by
    simp [hF, hPt]
  have hev1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < ‖F t‖ := by
    have hc : ContinuousAt (fun t => ‖F t‖) 0 := hFcont.norm.continuousAt
    have h0 : δ < ‖F 0‖ := by rw [hF0]; exact hδ
    exact nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds h0))
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i a, Pt t i a ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro a
    by_cases h0 : P i a = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [hPt, h0, mul_zero, zero_add, ne_eq, Complex.ofReal_eq_zero]
      exact ht.ne'
    · have hc : ContinuousAt (fun t : ℝ => Pt t i a) 0 := by
        simp only [hPt]
        fun_prop
      have hne : Pt 0 i a ≠ 0 := by simpa [hPt] using h0
      exact nhdsWithin_le_nhds (hc.eventually_ne hne)
  have hev3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  have hev4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  have hnorm_pos : ∀ i a, 0 < ‖Pt t i a‖ := fun i a => norm_pos_iff.2 (h2 i a)
  have hQR : ∀ i a, Pt t i a / (‖Pt t i a‖ : ℂ) * (‖Pt t i a‖ : ℂ) = Pt t i a := by
    intro i a
    have : (‖Pt t i a‖ : ℂ) ≠ 0 := by exact_mod_cast (hnorm_pos i a).ne'
    field_simp
  -- `Q = P̃/|P̃|`, `R = |P̃|`
  refine ⟨fun i a => Pt t i a / (‖Pt t i a‖ : ℂ), fun i a => ‖Pt t i a‖, ?_, hnorm_pos, ?_, ?_,
    ?_, ?_⟩
  · intro i a
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (hnorm_pos i a).ne']
  · intro i
    rcases isEmpty_or_nonempty α with hα | hα
    · simp [Finset.univ_eq_empty]
    have hpt : ∀ a, ‖Pt t i a‖ ^ 2 ≤ (1 - t) * ‖P i a‖ ^ 2 + t := by
      intro a
      have hle : ‖Pt t i a‖ ≤ (1 - t) * ‖P i a‖ + t := by
        simp only [hPt]
        calc ‖((1 - t : ℝ) : ℂ) * P i a + (t : ℂ)‖
            ≤ ‖((1 - t : ℝ) : ℂ) * P i a‖ + ‖(t : ℂ)‖ := norm_add_le _ _
          _ = (1 - t) * ‖P i a‖ + t := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
              Real.norm_of_nonneg h4.le]
      have h0 : 0 ≤ ‖Pt t i a‖ := norm_nonneg _
      have hp0 : 0 ≤ ‖P i a‖ := norm_nonneg _
      have hsq : ‖Pt t i a‖ ^ 2 ≤ ((1 - t) * ‖P i a‖ + t) ^ 2 := pow_le_pow_left₀ h0 hle 2
      nlinarith [mul_nonneg (mul_nonneg h4.le (by linarith : (0 : ℝ) ≤ 1 - t))
        (sq_nonneg (‖P i a‖ - 1))]
    calc 𝔼 a : α, ‖Pt t i a‖ ^ 2 ≤ 𝔼 a : α, ((1 - t) * ‖P i a‖ ^ 2 + t) :=
          Finset.expect_le_expect fun a _ => hpt a
      _ = (1 - t) * 𝔼 a : α, ‖P i a‖ ^ 2 + t := by
          rw [Finset.expect_add_distrib, Finset.mul_expect, Finset.expect_const univ_nonempty]
      _ ≤ (1 - t) * 1 + t := by
          have := mul_le_mul_of_nonneg_left (hP i) (by linarith : (0 : ℝ) ≤ 1 - t)
          linarith
      _ = 1 := by ring
  · have heq : 𝔼 x : ι → α, (f x * ∏ i, Pt t i (x i) / (‖Pt t i (x i)‖ : ℂ)) *
        ∏ i, ((‖Pt t i (x i)‖ : ℝ) : ℂ) = F t := by
      simp only [hF]
      refine Finset.expect_congr rfl fun x _ => ?_
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp_rw [hQR]
    rw [heq]
    exact h1.le
  · intro x
    rw [norm_mul, norm_prod]
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [Finset.prod_eq_one fun i _ => div_self (hnorm_pos i (x i)).ne', mul_one]
  · intro P'
    refine Finset.expect_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]

/-- `A_{L,R} := 𝔼_x[f(x) P(x) 1_{e^L ≤ P(x) ≤ e^R}]` (K6 `main.tex` l. 1208), `P(x) = ∏ᵢ Pᵢ(xᵢ)`. -/
def bprodA (f : (ι → α) → ℂ) (P : ι → α → ℝ) (L R : ℝ) : ℂ :=
  𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ) *
    (if Real.exp L ≤ ∏ i, P i (x i) ∧ ∏ i, P i (x i) ≤ Real.exp R then 1 else 0)

/-- `𝔼_x ∏ᵢ gᵢ(xᵢ) = ∏ᵢ 𝔼_a gᵢ(a)` for the uniform measure on `ι → α`. -/
private theorem expect_prod_eq (g : ι → α → ℝ) :
    𝔼 x : ι → α, ∏ i, g i (x i) = ∏ i, 𝔼 a : α, g i a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, ← Fintype.prod_sum, Finset.prod_const, Fintype.card_fun]
  simp

/-- `𝔼 P² ≤ 1` for `P = ∏ Pᵢ` with `𝔼 Pᵢ² ≤ 1`. -/
private theorem expect_prod_sq_le_one (P : ι → α → ℝ) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1) :
    𝔼 x : ι → α, (∏ i, P i (x i)) ^ 2 ≤ 1 := by
  simp_rw [← Finset.prod_pow]
  rw [expect_prod_eq (fun i a => P i a ^ 2)]
  exact Finset.prod_le_one₀ (fun i _ => Finset.expect_nonneg fun a _ => sq_nonneg _)
    fun i _ => hP i

/-- pointwise bound on the two tails (lower tail `p < δ²/16`: `‖f‖ ≤ 3/4 + ‖f‖⁴/4`; upper tail
`16/δ² < p`: two AM-GM steps replacing the Hölder step `(𝔼|f|⁴)^{1/4}(𝔼 P^{4/3})^{3/4}`). -/
private theorem tail_pointwise {δ F p : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hp : 0 < p)
    (h : p < δ ^ 2 / 16 ∨ 16 / δ ^ 2 < p) :
    F * p ≤ δ ^ 2 / 16 * (3 / 4 + F ^ 4 / 4) + δ / 16 * F ^ 4 + 3 * δ / 16 * p ^ 2 := by
  have hF4 : 0 ≤ F ^ 4 := by positivity
  have hp2 : 0 ≤ p ^ 2 := by positivity
  rcases h with h | h
  · have h1 : F * p ≤ F * (δ ^ 2 / 16) := mul_le_mul_of_nonneg_left h.le hF
    have h2 : F ≤ 3 / 4 + F ^ 4 / 4 := by
      nlinarith [mul_nonneg (sq_nonneg (F - 1)) (by positivity : (0 : ℝ) ≤ F ^ 2 + 2 * F + 3)]
    have h3 : F * (δ ^ 2 / 16) ≤ δ ^ 2 / 16 * (3 / 4 + F ^ 4 / 4) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 0 ≤ δ / 16 * F ^ 4 + 3 * δ / 16 * p ^ 2 := by positivity
    linarith
  · -- (i) `F p ≤ (2/δ) F² + (δ/8) p²`
    have i1 : F * p ≤ 2 / δ * F ^ 2 + δ / 8 * p ^ 2 := by
      have : 0 ≤ 2 / δ * (F - δ * p / 4) ^ 2 := by positivity
      have e : 2 / δ * (F - δ * p / 4) ^ 2 = 2 / δ * F ^ 2 + δ / 8 * p ^ 2 - F * p := by
        field_simp
        ring
      linarith
    -- (ii) `F² ≤ (δ²/32) F⁴ + 8/δ²`
    have i2 : F ^ 2 ≤ δ ^ 2 / 32 * F ^ 4 + 8 / δ ^ 2 := by
      have : 0 ≤ δ ^ 2 / 32 * (F ^ 2 - 16 / δ ^ 2) ^ 2 := by positivity
      have e : δ ^ 2 / 32 * (F ^ 2 - 16 / δ ^ 2) ^ 2 =
          δ ^ 2 / 32 * F ^ 4 + 8 / δ ^ 2 - F ^ 2 := by
        field_simp
        ring
      linarith
    -- (iii) `8/δ² ≤ (δ²/32) p²` on the upper tail
    have i3 : 8 / δ ^ 2 ≤ δ ^ 2 / 32 * p ^ 2 := by
      have hp' : 16 / δ ^ 2 ≤ p := h.le
      have hsq : (16 / δ ^ 2) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by positivity) hp' 2
      have e : δ ^ 2 / 32 * (16 / δ ^ 2) ^ 2 = 8 / δ ^ 2 := by
        field_simp
        ring
      have : δ ^ 2 / 32 * (16 / δ ^ 2) ^ 2 ≤ δ ^ 2 / 32 * p ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      linarith
    have i4 : 2 / δ * F ^ 2 ≤ 2 / δ * (δ ^ 2 / 32 * F ^ 4 + δ ^ 2 / 32 * p ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 2 / δ * (δ ^ 2 / 32 * F ^ 4 + δ ^ 2 / 32 * p ^ 2) =
        δ / 16 * F ^ 4 + δ / 16 * p ^ 2 := by
      field_simp
      ring
    have h0 : 0 ≤ δ ^ 2 / 16 * (3 / 4 + F ^ 4 / 4) := by positivity
    linarith

/-- the tail bound with the modulus inside the expectation (proof of `boundedprod_tail_abs`) -/
private theorem tail_abs_aux (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) :
    (𝔼 x : ι → α, if (∏ i, P i (x i) < Real.exp (-D) ∨ Real.exp D < ∏ i, P i (x i))
        then ‖f x‖ * ∏ i, P i (x i) else 0) ≤ δ / 2 := by
  rcases isEmpty_or_nonempty (ι → α) with hne | hne
  · simp [Finset.univ_eq_empty]
    positivity
  have hpos16 : 0 < 16 / δ ^ 2 := by positivity
  have hexpD : Real.exp D = 16 / δ ^ 2 := by rw [hD, Real.exp_log hpos16]
  have hexpnD : Real.exp (-D) = δ ^ 2 / 16 := by
    rw [Real.exp_neg, hexpD, inv_div]
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  have hpt : ∀ x : ι → α,
      (if (∏ i, P i (x i) < Real.exp (-D) ∨ Real.exp D < ∏ i, P i (x i))
        then ‖f x‖ * ∏ i, P i (x i) else 0) ≤
      δ ^ 2 / 16 * (3 / 4 + ‖f x‖ ^ 4 / 4) + δ / 16 * ‖f x‖ ^ 4 +
        3 * δ / 16 * (∏ i, P i (x i)) ^ 2 := by
    intro x
    split_ifs with h
    · rw [hexpD, hexpnD] at h
      exact tail_pointwise hδ (norm_nonneg _) (hp x) h
    · positivity
  calc _ ≤ 𝔼 x : ι → α, (δ ^ 2 / 16 * (3 / 4 + ‖f x‖ ^ 4 / 4) + δ / 16 * ‖f x‖ ^ 4 +
        3 * δ / 16 * (∏ i, P i (x i)) ^ 2) := Finset.expect_le_expect fun x _ => hpt x
    _ = δ ^ 2 / 16 * (3 / 4 + (𝔼 x : ι → α, ‖f x‖ ^ 4) / 4) +
        δ / 16 * 𝔼 x : ι → α, ‖f x‖ ^ 4 +
        3 * δ / 16 * 𝔼 x : ι → α, (∏ i, P i (x i)) ^ 2 := by
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
        ← Finset.mul_expect, ← Finset.mul_expect, Finset.expect_add_distrib,
        Finset.expect_const univ_nonempty, ← Finset.expect_div]
    _ ≤ δ ^ 2 / 16 * (3 / 4 + 1 / 4) + δ / 16 * 1 + 3 * δ / 16 * 1 := by
      have h2 := expect_prod_sq_le_one P hP
      gcongr
    _ ≤ δ / 2 := by nlinarith

/-- `‖𝔼 f P‖ ≤ 1` from `𝔼|f|⁴ ≤ 1` and `𝔼 P² ≤ 1` (so `δ ≤ 1` in `lemma:ad`). -/
private theorem expect_norm_mul_le_one (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1) :
    ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (ι → α) with hne | hne
  · simp [Finset.univ_eq_empty]
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  calc _ ≤ 𝔼 x : ι → α, ‖f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖ := RCLike.norm_expect_le (K := ℝ)
    _ ≤ 𝔼 x : ι → α, (1 / 4 + ‖f x‖ ^ 4 / 4 + (∏ i, P i (x i)) ^ 2 / 2) := by
      refine Finset.expect_le_expect fun x _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp x).le]
      have hF := norm_nonneg (f x)
      nlinarith [sq_nonneg (‖f x‖ - ∏ i, P i (x i)), sq_nonneg (‖f x‖ ^ 2 - 1)]
    _ = 1 / 4 + (𝔼 x : ι → α, ‖f x‖ ^ 4) / 4 + (𝔼 x : ι → α, (∏ i, P i (x i)) ^ 2) / 2 := by
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Finset.expect_const univ_nonempty,
        ← Finset.expect_div, ← Finset.expect_div]
    _ ≤ 1 / 4 + 1 / 4 + 1 / 2 := by
      have h2 := expect_prod_sq_le_one P hP
      gcongr
    _ = 1 := by norm_num

/-- The tail form (`boundedprod_ad_tail`, stronger than CSP_6 `lemma:ad`): the two removed
tails of `P` have modulus at most `δ/2`, so `A_{-D,D}` keeps the phase of `𝔼 f P`. -/
theorem boundedprod_ad_tail (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hcorr : δ ≤ ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖)
    (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) :
    ‖(𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)) - bprodA f P (-D) D‖ ≤ δ / 2 := by
  have hδ1 : δ ≤ 1 := hcorr.trans (expect_norm_mul_le_one f hf4 P hPpos hP)
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  unfold bprodA
  rw [← Finset.expect_sub_distrib]
  refine (RCLike.norm_expect_le (K := ℝ)).trans (le_trans (le_of_eq ?_)
    (tail_abs_aux f hf4 P hPpos hP hδ hδ1 D hD))
  refine Finset.expect_congr rfl fun x _ => ?_
  by_cases h : Real.exp (-D) ≤ ∏ i, P i (x i) ∧ ∏ i, P i (x i) ≤ Real.exp D
  · have h' : ¬(∏ i, P i (x i) < Real.exp (-D) ∨ Real.exp D < ∏ i, P i (x i)) := by
      rintro (h'' | h'') <;> linarith [h.1, h.2]
    simp [h, h']
  · have h' : ∏ i, P i (x i) < Real.exp (-D) ∨ Real.exp D < ∏ i, P i (x i) := by
      rcases not_and_or.1 h with h1 | h1
      · exact Or.inl (lt_of_not_ge h1)
      · exact Or.inr (lt_of_not_ge h1)
    simp only [h, h', ite_false, ite_true, mul_zero, sub_zero]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp x).le]

/-- CSP_6 `lemma:ad` (l. 1210-1223): `|A_{-D,D}| ≥ δ/2` for `D = log(16/δ²)`. -/
theorem boundedprod_ad (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hcorr : δ ≤ ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖)
    (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) :
    δ / 2 ≤ ‖bprodA f P (-D) D‖ := by
  have h := boundedprod_ad_tail f hf4 P hPpos hP hδ hcorr D hD
  have h2 := norm_sub_norm_le (𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)) (bprodA f P (-D) D)
  linarith

/-! ### Supplement F: `bprod_expect_prod_sq` and `boundedprod_tail_abs` -/

/-- Supplement F, item F3a: `𝔼_{x : ι → α} ∏ᵢ Pᵢ(xᵢ)² = ∏ᵢ 𝔼_a Pᵢ(a)²`. -/
theorem bprod_expect_prod_sq (P : ι → α → ℝ) :
    𝔼 x : ι → α, ∏ i, P i (x i) ^ 2 = ∏ i, 𝔼 a : α, P i a ^ 2 :=
  expect_prod_eq (fun i a => P i a ^ 2)

/-- Supplement F (Lemma `lem:tails`(c)): with the hypotheses of `boundedprod_ad` minus
`hcorr`, plus `δ ≤ 1`, the two tails of `P` (with the modulus inside the expectation) have mass at
most `δ/2`. -/
theorem boundedprod_tail_abs (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) :
    (𝔼 x : ι → α, if (∏ i, P i (x i) < Real.exp (-D) ∨ Real.exp D < ∏ i, P i (x i))
        then ‖f x‖ * ∏ i, P i (x i) else 0) ≤ δ / 2 :=
  tail_abs_aux f hf4 P hPpos hP hδ hδ1 D hD

end BoundedProd
end TrackB
end RestrictedPolynomials
end
