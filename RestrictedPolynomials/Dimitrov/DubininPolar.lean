module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The polar identity (Supplement C, Lemma 2.2, `lem:polar`)

Source: Supplement C, Lemma `lem:polar`.  For a Lipschitz function `W` with compact support,
`∫_{|z-c|>δ} ⟨∇W, (z-c)/|z-c|²⟩ = -∫_0^{2π} W(c + δ e^{iθ}) dθ`.

Route: Rademacher (`LipschitzWith.ae_differentiableAt`); polar coordinates
(`Complex.integral_comp_polarCoord_symm`), the Rademacher null set being transferred to polar
coordinates by `Complex.lintegral_comp_polarCoord_symm` applied to the indicator of the null set; the
fundamental theorem of calculus along each ray for the Lipschitz radial slice
(`LipschitzOnWith.absolutelyContinuousOnInterval`,
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`); the boundary term at infinity vanishes since
`W` has compact support.  The proof is reduced to `c = 0` by translation.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

noncomputable section

namespace RestrictedPolynomials

namespace DubininPolar

/-- Measurability of `a ↦ fderiv ℝ W (g a) (v a)`. -/
lemma measurable_fderiv_apply_comp (W : ℂ → ℝ) {α : Type*} [MeasurableSpace α] {g v : α → ℂ}
    (hg : Measurable g) (hv : Measurable v) :
    Measurable fun a => fderiv ℝ W (g a) (v a) := by
  have h : ∀ a, fderiv ℝ W (g a) (v a) =
      (v a).re * fderiv ℝ W (g a) 1 + (v a).im * fderiv ℝ W (g a) Complex.I := by
    intro a
    have hz : v a = (v a).re • (1 : ℂ) + (v a).im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
  simp_rw [h]
  have h1 : Measurable fun a => fderiv ℝ W (g a) 1 :=
    (measurable_fderiv_apply_const ℝ W 1).comp hg
  have h2 : Measurable fun a => fderiv ℝ W (g a) Complex.I :=
    (measurable_fderiv_apply_const ℝ W Complex.I).comp hg
  exact ((Complex.measurable_re.comp hv).mul h1).add ((Complex.measurable_im.comp hv).mul h2)

/-- The polar-coordinate point `ρ e^{iθ}`. -/
def pt (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

lemma continuous_pt : Continuous pt := by unfold pt; fun_prop

lemma polarCoord_symm_eq (p : ℝ × ℝ) : Complex.polarCoord.symm p = pt p := by
  simp [pt, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma norm_pt (p : ℝ × ℝ) : ‖pt p‖ = |p.1| := by
  simp [pt, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_mul_I (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- `fderiv W` vanishes far away if `W` does. -/
lemma fderiv_eq_zero_of_far {W : ℂ → ℝ} {T : ℝ} (hzero : ∀ z, T ≤ ‖z‖ → W z = 0) {z : ℂ}
    (hz : T < ‖z‖) : fderiv ℝ W z = 0 := by
  have h : W =ᶠ[nhds z] fun _ => (0 : ℝ) := by
    have : {w : ℂ | T < ‖w‖} ∈ nhds z := (isOpen_lt continuous_const continuous_norm).mem_nhds hz
    filter_upwards [this] with w hw using hzero w hw.le
  rw [h.fderiv_eq]; simp

/-- A radius beyond which a compactly supported `W` vanishes. -/
lemma exists_far {W : ℂ → ℝ} (hc : HasCompactSupport W) (δ : ℝ) :
    ∃ T, δ < T ∧ ∀ z, T ≤ ‖z‖ → W z = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max R δ + 1, by linarith [le_max_right R δ], fun z hz => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R δ]

/-- Transfer of the Rademacher null set to polar coordinates: almost every point of
the polar target is sent to a differentiability point of `W`. -/
lemma ae_polar_differentiableAt {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W) :
    ∀ᵐ p ∂(volume.restrict Complex.polarCoord.target), DifferentiableAt ℝ W (pt p) := by
  set Z : Set ℂ := {z | ¬ DifferentiableAt ℝ W z} with hZdef
  have hZm : MeasurableSet Z :=
    (measurableSet_of_differentiableAt ℝ W).compl
  have hZ0 : (volume : Measure ℂ) Z = 0 := by
    have := hW.ae_differentiableAt (μ := (volume : Measure ℂ))
    rw [ae_iff] at this
    simpa [hZdef] using this
  have key := Complex.lintegral_comp_polarCoord_symm (Z.indicator (1 : ℂ → ENNReal))
  rw [lintegral_indicator_one hZm, hZ0] at key
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • Z.indicator (1 : ℂ → ENNReal) (pt p) := by
    refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
    exact (measurable_one.indicator hZm).comp continuous_pt.measurable
  have h0 := (lintegral_eq_zero_iff hmeas).1 (by
    simpa only [polarCoord_symm_eq] using key)
  filter_upwards [h0, ae_restrict_mem Complex.polarCoord.open_target.measurableSet] with p hp hpt
  by_contra hnd
  have hpZ : pt p ∈ Z := hnd
  have hpos : 0 < p.1 := hpt.1
  simp only [Pi.zero_apply, Set.indicator_of_mem hpZ, smul_eq_mul] at hp
  exact absurd hp (by simpa using hpos)

/-- The fundamental theorem of calculus along a ray. -/
lemma ray_integral {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W) {δ T θ : ℝ} (hδ : 0 < δ)
    (hT : δ < T) (hzero : ∀ z, T ≤ ‖z‖ → W z = 0)
    (hae : ∀ᵐ ρ : ℝ ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      DifferentiableAt ℝ W ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :
    ∫ ρ in δ..T, fderiv ℝ W ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        (Complex.exp ((θ : ℂ) * Complex.I)) =
      -W ((δ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  set e : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with he
  have he1 : ‖e‖ = 1 := norm_exp_mul_I θ
  set g : ℝ → ℝ := fun ρ => W ((ρ : ℂ) * e) with hg
  have hgL : LipschitzWith K g := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    have := hW.dist_le_mul ((a : ℂ) * e) ((b : ℂ) * e)
    simpa [hg, dist_eq_norm, ← sub_mul, norm_mul, he1, Complex.dist_eq, Real.dist_eq, ← Complex.ofReal_sub, Complex.norm_real] using this
  have hac : AbsolutelyContinuousOnInterval g δ T :=
    (hgL.lipschitzOnWith).absolutelyContinuousOnInterval
  have hftc := hac.integral_deriv_eq_sub
  have hgT : g T = 0 := by
    apply hzero
    simp [he1, abs_of_pos (hδ.trans hT)]
  have hcongr : ∫ ρ in δ..T, fderiv ℝ W ((ρ : ℂ) * e) e = ∫ ρ in δ..T, deriv g ρ := by
    apply intervalIntegral.integral_congr_ae
    rw [ae_restrict_iff' measurableSet_Ioi] at hae
    filter_upwards [hae] with ρ hρ hρmem
    rw [Set.uIoc_of_le hT.le] at hρmem
    have hd := hρ (hδ.trans hρmem.1)
    have h2 : HasDerivAt (fun ρ : ℝ => (ρ : ℂ) * e) e ρ := by
      simpa using ((hasDerivAt_id ρ).ofReal_comp).mul_const e
    have h3 := hd.hasFDerivAt.comp_hasDerivAt ρ h2
    exact h3.deriv.symm
  rw [hcongr, hftc, hgT]
  simp [hg]

/-- The integrand of the polar identity for `c = 0`. -/
def hfun (W : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ W z ((‖z‖ ^ 2)⁻¹ • z)

lemma measurable_hfun (W : ℂ → ℝ) : Measurable (hfun W) := by
  unfold hfun
  exact measurable_fderiv_apply_comp W measurable_id
    ((by fun_prop : Measurable fun z : ℂ => ((‖z‖ ^ 2)⁻¹ : ℝ)).smul measurable_id)

lemma norm_hfun_le {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W) {δ : ℝ} (hδ : 0 < δ)
    {z : ℂ} (hz : δ < ‖z‖) : ‖hfun W z‖ ≤ K * δ⁻¹ := by
  have hz0 : 0 < ‖z‖ := hδ.trans hz
  have h1 : ‖fderiv ℝ W z‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hW
  have h2 : ‖(‖z‖ ^ 2)⁻¹ • z‖ = ‖z‖⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  calc ‖hfun W z‖ ≤ ‖fderiv ℝ W z‖ * ‖(‖z‖ ^ 2)⁻¹ • z‖ := (fderiv ℝ W z).le_opNorm _
    _ ≤ K * δ⁻¹ := by
        rw [h2]
        exact mul_le_mul h1 (inv_anti₀ hδ hz.le) (by positivity) (by positivity)

lemma integrableOn_hfun {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W)
    (hc : HasCompactSupport W) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (hfun W) {z : ℂ | δ < ‖z‖} := by
  have hSm : MeasurableSet {z : ℂ | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hTfin : (volume : Measure ℂ) ({z : ℂ | δ < ‖z‖} ∩ tsupport W) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_right).trans_lt hc.isCompact.measure_lt_top).ne
  have hT : IntegrableOn (hfun W) ({z : ℂ | δ < ‖z‖} ∩ tsupport W) := by
    refine Measure.integrableOn_of_bounded (M := K * δ⁻¹) hTfin
      (measurable_hfun W).aestronglyMeasurable ?_
    rw [ae_restrict_iff' (hSm.inter hc.isCompact.measurableSet)]
    exact Filter.Eventually.of_forall fun z hz => norm_hfun_le hW hδ hz.1
  refine hT.of_forall_sdiff_eq_zero hSm fun z hz => ?_
  have : z ∉ tsupport W := fun h => hz.2 ⟨hz.1, h⟩
  simp [hfun, fderiv_of_notMem_tsupport (𝕜 := ℝ) this]

/-- The radial integrand in polar coordinates. -/
def Phi (W : ℂ → ℝ) (δ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if δ < p.1 then fderiv ℝ W (pt p) (Complex.exp ((p.2 : ℂ) * Complex.I)) else 0

lemma measurable_Phi (W : ℂ → ℝ) (δ : ℝ) : Measurable (Phi W δ) := by
  unfold Phi
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  exact measurable_fderiv_apply_comp W continuous_pt.measurable
    (by fun_prop : Measurable fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I))

lemma Phi_eq_zero {W : ℂ → ℝ} {δ T : ℝ} (hzero : ∀ z, T ≤ ‖z‖ → W z = 0) {p : ℝ × ℝ}
    (hp : T < p.1) (hp0 : 0 < p.1) : Phi W δ p = 0 := by
  have : T < ‖pt p‖ := by rw [norm_pt, abs_of_pos hp0]; exact hp
  simp [Phi, fderiv_eq_zero_of_far hzero this]

lemma norm_Phi_le {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W) (δ : ℝ) (p : ℝ × ℝ) :
    ‖Phi W δ p‖ ≤ K := by
  unfold Phi
  split_ifs
  · calc _ ≤ ‖fderiv ℝ W (pt p)‖ * ‖Complex.exp ((p.2 : ℂ) * Complex.I)‖ :=
          (fderiv ℝ W (pt p)).le_opNorm _
      _ ≤ K * 1 := by
          rw [norm_exp_mul_I]
          exact mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hW) zero_le_one
      _ = K := mul_one _
  · simp

lemma integrableOn_Phi {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W) (δ : ℝ) {T : ℝ}
    (hzero : ∀ z, T ≤ ‖z‖ → W z = 0) :
    IntegrableOn (Phi W δ) (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
  have hB : IsCompact (Icc (0 : ℝ) T ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hBfin : (volume : Measure (ℝ × ℝ)) (Icc (0 : ℝ) T ×ˢ Icc (-π) π) ≠ ⊤ :=
    hB.measure_lt_top.ne
  have h1 : IntegrableOn (Phi W δ) (Icc (0 : ℝ) T ×ˢ Icc (-π) π) :=
    Measure.integrableOn_of_bounded (M := K) hBfin (measurable_Phi W δ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => norm_Phi_le hW δ p)
  refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨⟨hp1, hp2⟩, hnot⟩ := hp
  refine Phi_eq_zero hzero ?_ hp1
  by_contra hle
  push Not at hle
  exact hnot ⟨⟨hp1.le, hle⟩, ⟨hp2.1.le, hp2.2.le⟩⟩

/-- The change of variables to polar coordinates. -/
lemma integral_hfun_eq {W : ℂ → ℝ} {δ : ℝ} :
    ∫ z in {z : ℂ | δ < ‖z‖}, hfun W z =
      ∫ p in Complex.polarCoord.target, Phi W δ p := by
  have hSm : MeasurableSet {z : ℂ | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  rw [← integral_indicator hSm, ← Complex.integral_comp_polarCoord_symm]
  refine setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet fun p hp => ?_
  have hρ : 0 < p.1 := hp.1
  rw [polarCoord_symm_eq]
  have hn : ‖pt p‖ = p.1 := by rw [norm_pt, abs_of_pos hρ]
  by_cases hδρ : δ < p.1
  · have hmem : pt p ∈ {z : ℂ | δ < ‖z‖} := by simpa [hn] using hδρ
    rw [Set.indicator_of_mem hmem]
    simp only [Phi, hδρ, ite_true, hfun, hn]
    have : ((p.1 ^ 2)⁻¹ • pt p : ℂ) = p.1⁻¹ • Complex.exp ((p.2 : ℂ) * Complex.I) := by
      simp only [pt, Complex.real_smul]
      push_cast
      field_simp
    rw [this, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
  · have hnmem : pt p ∉ {z : ℂ | δ < ‖z‖} := by simpa [hn] using hδρ
    simp [Set.indicator_of_notMem hnmem, Phi, hδρ]

/-- The polar identity for `c = 0`. -/
lemma polar_zero {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W) (hc : HasCompactSupport W)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ z in {z : ℂ | δ < ‖z‖}, hfun W z =
      -∫ θ in (0 : ℝ)..2 * π, W ((δ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  obtain ⟨T, hδT, hzero⟩ := exists_far hc δ
  rw [integral_hfun_eq]
  have hint := integrableOn_Phi hW δ hzero
  have e1 : (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) =
      ((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hint' : Integrable (Phi W δ)
      (((volume : Measure ℝ).restrict (Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Ioo (-π) π))) := by
    rw [← e1]; exact hint
  have h3 : ∫ p in Complex.polarCoord.target, Phi W δ p =
      ∫ θ in Ioo (-π) π, ∫ ρ in Ioi (0 : ℝ), Phi W δ (ρ, θ) := by
    rw [Complex.polarCoord_target, e1]
    exact integral_prod_symm (Phi W δ) hint'
  rw [h3]
  -- almost every ray meets only differentiability points
  have hae1 : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Ioo (-π) π))), DifferentiableAt ℝ W (pt p) := by
    rw [← e1, ← Complex.polarCoord_target]
    exact ae_polar_differentiableAt hW
  have hae2 : ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Ioo (-π) π)),
      ∀ᵐ ρ ∂((volume : Measure ℝ).restrict (Ioi 0)), DifferentiableAt ℝ W (pt (ρ, θ)) := by
    exact (Measure.ae_ae_comm (p := fun ρ θ => DifferentiableAt ℝ W (pt (ρ, θ)))
      ((measurableSet_of_differentiableAt ℝ W).preimage continuous_pt.measurable)).1
      (Measure.ae_ae_of_ae_prod hae1)
  have h4 : ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Ioo (-π) π)),
      ∫ ρ in Ioi (0 : ℝ), Phi W δ (ρ, θ) =
        -W ((δ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    filter_upwards [hae2] with θ hθ
    have hphi : (fun ρ : ℝ => Phi W δ (ρ, θ)) = (Ioi δ).indicator
        (fun ρ : ℝ => fderiv ℝ W ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.exp ((θ : ℂ) * Complex.I))) := by
      funext ρ
      simp only [Phi, Set.indicator_apply, Set.mem_Ioi]
      rfl
    rw [hphi, setIntegral_indicator measurableSet_Ioi,
      show Ioi (0 : ℝ) ∩ Ioi δ = Ioi δ from Set.inter_eq_right.2 (Ioi_subset_Ioi hδ.le)]
    have h5 : ∫ ρ in Ioi δ, fderiv ℝ W ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.exp ((θ : ℂ) * Complex.I)) =
        ∫ ρ in Ioc δ T, fderiv ℝ W ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.exp ((θ : ℂ) * Complex.I)) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Ioc_subset_Ioi_self fun ρ hρ => ?_
      have hρT : T < ρ := by
        by_contra h
        exact hρ.2 ⟨hρ.1, not_lt.1 h⟩
      have hρ0 : 0 < ρ := hδ.trans hρ.1
      have := Phi_eq_zero (δ := δ) hzero (p := (ρ, θ)) hρT hρ0
      have hfd : fderiv ℝ W ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 :=
        fderiv_eq_zero_of_far hzero (by
          have : T < ‖pt (ρ, θ)‖ := by rw [norm_pt, abs_of_pos hρ0]; exact hρT
          exact this)
      simp [hfd]
    rw [h5, ← intervalIntegral.integral_of_le hδT.le]
    exact ray_integral hW hδ hδT hzero hθ
  rw [integral_congr_ae h4]
  -- the angular integral
  set F : ℝ → ℝ := fun θ => W ((δ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hF
  have hper : Function.Periodic F (2 * π) := by
    intro θ
    have : ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast; ring
    simp only [hF]
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hpi : ∫ θ in (-π)..(-π + 2 * π), F θ = ∫ θ in (0 : ℝ)..(0 + 2 * π), F θ :=
    hper.intervalIntegral_add_eq (-π) 0
  rw [show (-π + 2 * π) = π by ring, zero_add,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π),
    integral_Ioc_eq_integral_Ioo] at hpi
  rw [integral_neg, hpi]

end DubininPolar

/-- [Supplement C, Lemma 2.2 (`lem:polar`)] The polar identity: for a Lipschitz function `W` with
compact support, `∫_{|z-c|>δ} ⟨∇W(z), (z-c)/|z-c|²⟩ dA = -∫_0^{2π} W(c + δ e^{iθ}) dθ`, the
integrand being integrable. -/
theorem polar_identity {W : ℂ → ℝ} {K : NNReal} (hW : LipschitzWith K W)
    (hc : HasCompactSupport W) (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun z => fderiv ℝ W z ((‖z - c‖ ^ 2)⁻¹ • (z - c))) {z | δ < ‖z - c‖} ∧
    ∫ z in {z | δ < ‖z - c‖}, fderiv ℝ W z ((‖z - c‖ ^ 2)⁻¹ • (z - c)) =
      -∫ θ in (0 : ℝ)..2 * Real.pi, W (c + δ * Complex.exp (θ * Complex.I)) := by
  set W₀ : ℂ → ℝ := fun y => W (c + y) with hW₀
  have hW₀L : LipschitzWith K W₀ := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [hW₀, dist_add_left] using hW.dist_le_mul (c + a) (c + b)
  have hc₀ : HasCompactSupport W₀ := hc.comp_homeomorph (Homeomorph.addLeft c)
  set F : ℂ → ℝ := fun z => fderiv ℝ W z ((‖z - c‖ ^ 2)⁻¹ • (z - c)) with hF
  set e : ℂ ≃ᵐ ℂ := MeasurableEquiv.addLeft c with he
  have hmp : MeasurePreserving e (volume : Measure ℂ) volume :=
    measurePreserving_add_left volume c
  have hset : e ⁻¹' {z : ℂ | δ < ‖z - c‖} = {y : ℂ | δ < ‖y‖} := by
    ext y; simp [he]
  have hfun : DubininPolar.hfun W₀ = F ∘ e := by
    funext y
    simp [DubininPolar.hfun, hW₀, hF, he, fderiv_comp_add_left]
  have hint := DubininPolar.integrableOn_hfun hW₀L hc₀ hδ
  have hint' : IntegrableOn F {z : ℂ | δ < ‖z - c‖} := by
    rw [← hmp.integrableOn_comp_preimage e.measurableEmbedding, hset, ← hfun]
    exact hint
  refine ⟨hint', ?_⟩
  have h1 := hmp.setIntegral_preimage_emb e.measurableEmbedding F {z : ℂ | δ < ‖z - c‖}
  have h2 : ∫ x in {y : ℂ | δ < ‖y‖}, F (e x) = ∫ x in {y : ℂ | δ < ‖y‖}, DubininPolar.hfun W₀ x := by
    rw [hfun]; rfl
  rw [hset, h2, DubininPolar.polar_zero hW₀L hc₀ hδ] at h1
  rw [← h1]

end RestrictedPolynomials
