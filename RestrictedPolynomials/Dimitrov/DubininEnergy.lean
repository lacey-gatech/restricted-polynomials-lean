module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import RestrictedPolynomials.Dimitrov.Fekete
public import RestrictedPolynomials.Dimitrov.DubininLevel
public import RestrictedPolynomials.Dimitrov.DubininPolar
public import RestrictedPolynomials.Dimitrov.DubininCircle
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# The energy lower bound

Supplement C, Proposition 3.1 (`prop:energy`), Steps 2, 3, 5 and 6.

Let `K ⊆ B̄(0,R)` be compact with `d(K) > 0`, and `u` Lipschitz with `u = 1` on an open set
`O ⊇ K` and `u = 0` off `B(0,r')`.  For a Fekete tuple `zs` of `K` and `0 < δ` small, put
`U = circlePotential m δ zs`, `L = log (r' + R + δ)`, `W = max (U + L) 0`.  The polar identity
(`polar_identity`) gives the pairing formula `∫ ⟨∇φ, ∇U⟩ = (1/m) ∑_a ∫ φ(z_a + δ e^{iθ}) dθ`; with it
`∫ |∇W|² = 2π (J + L)` and `∫ ⟨∇u, ∇U⟩ = 2π`.  Cauchy–Schwarz gives `2π ≤ Dir(u) (J + L)`, and the
limits `m → ∞`, `δ → 0` finish the proof.
-/

@[expose] public section

open MeasureTheory Metric Filter
open scoped Real Topology

noncomputable section

namespace RestrictedPolynomials

/-- The vector field `-(1/m) ∑_{a : ‖z - z_a‖ > δ} (z - z_a)/‖z - z_a‖²`, the a.e. gradient of the
circle potential. -/
def circleGradField (m : ℕ) (δ : ℝ) (zs : Fin m → ℂ) (z : ℂ) : ℂ :=
  -(1 / (m : ℝ)) • ∑ a, if δ < ‖z - zs a‖ then (‖z - zs a‖ ^ 2)⁻¹ • (z - zs a) else 0

lemma fderiv_circleGradField (m : ℕ) (δ : ℝ) (zs : Fin m → ℂ) (φ : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ φ z (circleGradField m δ zs z) =
      -(1 / (m : ℝ)) * ∑ a, Set.indicator {w : ℂ | δ < ‖w - zs a‖}
        (fun y => fderiv ℝ φ y ((‖y - zs a‖ ^ 2)⁻¹ • (y - zs a))) z := by
  unfold circleGradField
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : δ < ‖z - zs a‖
  · simp [h, Set.indicator_of_mem]
  · simp [h]

/-- The pairing formula `∫ ⟨∇φ, ∇U⟩ = (1/m) ∑_a ∫ φ(z_a + δ e^{iθ}) dθ`
([Supplement C, (3.1)]). -/
lemma pairing_circle {m : ℕ} {δ : ℝ} (hδ : 0 < δ) (zs : Fin m → ℂ) {φ : ℂ → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => fderiv ℝ φ z (circleGradField m δ zs z)) ∧
    ∫ z, fderiv ℝ φ z (circleGradField m δ zs z) =
      (1 / (m : ℝ)) * ∑ a, ∫ θ in (0 : ℝ)..2 * Real.pi,
        φ (zs a + δ * Complex.exp (θ * Complex.I)) := by
  have hpol := fun a => polar_identity hφ hc (zs a) hδ
  have hmeas : ∀ a, MeasurableSet {w : ℂ | δ < ‖w - zs a‖} := fun a =>
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hint : ∀ a, Integrable (Set.indicator {w : ℂ | δ < ‖w - zs a‖}
      (fun y => fderiv ℝ φ y ((‖y - zs a‖ ^ 2)⁻¹ • (y - zs a)))) := fun a =>
    (integrable_indicator_iff (hmeas a)).2 (hpol a).1
  have hfun : (fun z => fderiv ℝ φ z (circleGradField m δ zs z)) = fun z =>
      -(1 / (m : ℝ)) * ∑ a, Set.indicator {w : ℂ | δ < ‖w - zs a‖}
        (fun y => fderiv ℝ φ y ((‖y - zs a‖ ^ 2)⁻¹ • (y - zs a))) z :=
    funext fun z => fderiv_circleGradField m δ zs φ z
  rw [hfun]
  have hsum : Integrable (fun z => ∑ a, Set.indicator {w : ℂ | δ < ‖w - zs a‖}
        (fun y => fderiv ℝ φ y ((‖y - zs a‖ ^ 2)⁻¹ • (y - zs a))) z) :=
    integrable_finsetSum _ fun a _ => hint a
  refine ⟨hsum.const_mul _, ?_⟩
  · rw [integral_const_mul, integral_finsetSum _ fun a _ => hint a]
    have : ∀ a, ∫ z, Set.indicator {w : ℂ | δ < ‖w - zs a‖}
        (fun y => fderiv ℝ φ y ((‖y - zs a‖ ^ 2)⁻¹ • (y - zs a))) z =
        -∫ θ in (0 : ℝ)..2 * Real.pi, φ (zs a + δ * Complex.exp (θ * Complex.I)) := fun a => by
      rw [integral_indicator (hmeas a)]
      exact (hpol a).2
    simp_rw [this]
    rw [Finset.sum_neg_distrib]
    ring

/-- Off the (null) circles, the circle potential has gradient `circleGradField`. -/
lemma ae_fderiv_circlePotential (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (zs : Fin m → ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      fderiv ℝ (circlePotential m δ zs) z = innerSL ℝ (circleGradField m δ zs z) := by
  have h : ∀ᵐ z ∂(volume : Measure ℂ), ∀ a, ‖z - zs a‖ ≠ δ := by
    rw [ae_all_iff]
    intro a
    have h0 : (volume : Measure ℂ) (sphere (zs a) δ) = 0 := Measure.addHaar_sphere _ _ _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz
    intro h
    exact hz (by rw [mem_sphere, dist_eq_norm]; exact h)
  filter_upwards [h] with z hz
  ext w
  rw [(hasGradient_circlePotential m hδ zs hz).2 w, innerSL_apply_apply]
  unfold circleGradField
  rw [real_inner_smul_left, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [real_inner_smul_left]; ring
  · simp

/-- The truncated potential `W = max (U + L) 0` has a.e. the gradient `1_{U + L > 0} ∇U`. -/
lemma ae_fderiv_trunc (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (zs : Fin m → ℂ) (c : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      fderiv ℝ (fun y => max (circlePotential m δ zs y + c) 0) z =
        if 0 < circlePotential m δ zs z + c then innerSL ℝ (circleGradField m δ zs z) else 0 := by
  obtain ⟨KU, hKU⟩ := lipschitz_circlePotential m hδ zs
  have hV : LipschitzWith KU (fun y => circlePotential m δ zs y + c) := by
    simpa using hKU.add (LipschitzWith.const c)
  filter_upwards [fderiv_max_const_ae hV 0, ae_fderiv_circlePotential m hδ zs] with z h1 h2
  rw [h1, fderiv_add_const, h2]

/-- Cauchy–Schwarz for square-integrable functions. -/
lemma integral_mul_sq_le {f g : ℂ → ℝ} (hf : Integrable (fun z => f z ^ 2))
    (hg : Integrable (fun z => g z ^ 2)) (hfg : Integrable (fun z => f z * g z)) :
    (∫ z, f z * g z) ^ 2 ≤ (∫ z, f z ^ 2) * ∫ z, g z ^ 2 := by
  have key : ∀ t : ℝ,
      0 ≤ (∫ z, f z ^ 2) * (t * t) + (-2 * ∫ z, f z * g z) * t + ∫ z, g z ^ 2 := by
    intro t
    have h0 : 0 ≤ ∫ z, (t * f z - g z) ^ 2 := integral_nonneg fun z => sq_nonneg _
    have h1 : ∫ z, (t * f z - g z) ^ 2 =
        t * t * (∫ z, f z ^ 2) - 2 * t * (∫ z, f z * g z) + ∫ z, g z ^ 2 := by
      have : (fun z => (t * f z - g z) ^ 2) =
          fun z => ((t * t) * f z ^ 2 + (-(2 * t)) * (f z * g z)) + g z ^ 2 := by
        funext z; ring
      have hi : Integrable (fun z => (t * t) * f z ^ 2 + (-(2 * t)) * (f z * g z)) :=
        (hf.const_mul (t * t)).add (hfg.const_mul (-(2 * t)))
      rw [this, integral_add hi hg, integral_add (hf.const_mul (t * t)) (hfg.const_mul (-(2 * t))),
        integral_const_mul, integral_const_mul]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- A Lipschitz function with compact support has square-integrable derivative norm. -/
lemma integrable_sq_norm_fderiv {φ : ℂ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hc : HasCompactSupport φ) : Integrable (fun z => ‖fderiv ℝ φ z‖ ^ 2) := by
  have hS : IsCompact (tsupport (fderiv ℝ φ)) := hc.fderiv (𝕜 := ℝ)
  have hint : Integrable ((tsupport (fderiv ℝ φ)).indicator (fun _ => (K : ℝ) ^ 2)) :=
    (integrable_indicator_iff hS.measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  refine hint.mono' ((measurable_fderiv (𝕜 := ℝ) (f := φ)).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport (fderiv ℝ φ)
  · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hφ) 2
  · rw [Set.indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz]
    simp

/-- One step of [Supplement C, Prop. 3.1] (Steps 2, 3, 5): for `m` points `zs` in `B̄(0,R)` and a
small `δ`, `2π ≤ Dir(u) (B + log (r' + R + δ))` as soon as the circle average bound `J ≤ B`
holds. -/
lemma energy_step {m : ℕ} (hm : 2 ≤ m) {R r' δ B : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hδr : δ < r' - R) {zs : Fin m → ℂ} (hzs : ∀ a, ‖zs a‖ ≤ R)
    {u : ℂ → ℝ} {L : NNReal} (hu : LipschitzWith L u)
    (hu1 : ∀ a (θ : ℝ), u (zs a + δ * Complex.exp (θ * Complex.I)) = 1)
    (hu0 : ∀ z, r' ≤ ‖z‖ → u z = 0)
    (hJ : (1 / (m : ℝ)) * ∑ a, Real.circleAverage (circlePotential m δ zs) (zs a) δ ≤ B) :
    2 * Real.pi ≤ dirichletEnergy u * (B + Real.log (r' + R + δ)) := by
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  obtain ⟨KU, hKU⟩ := lipschitz_circlePotential m hδ zs
  set U := circlePotential m δ zs with hUdef
  set Lg := Real.log (r' + R + δ) with hLg
  have hV : LipschitzWith KU (fun y => U y + Lg) := by
    simpa using hKU.add (LipschitzWith.const Lg)
  set W : ℂ → ℝ := fun y => max (U y + Lg) 0 with hWdef
  have hW : LipschitzWith KU W := by simpa using hV.max_const 0
  have hWcs : HasCompactSupport W := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (r' + 2 * R + δ)) fun z hz => ?_
    have hz' : r' + 2 * R + δ < ‖z‖ := by
      simpa [mem_closedBall, dist_zero_right] using hz
    have h1 := circlePotential_le hm1 hδ hzs (z := z) (by linarith)
    have hlog : Lg ≤ Real.log (‖z‖ - R) := Real.log_le_log (by linarith) (by linarith)
    show max (U z + Lg) 0 = 0
    exact max_eq_right (by linarith)
  have hucs : HasCompactSupport u := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r') fun z hz => hu0 z ?_
    have : r' < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hz
    exact this.le
  obtain ⟨hIW, hEW⟩ := pairing_circle hδ zs hW hWcs
  obtain ⟨hIu, hEu⟩ := pairing_circle hδ zs hu hucs
  have hcirc_norm : ∀ a (θ : ℝ), ‖zs a + δ * Complex.exp (θ * Complex.I)‖ < r' := by
    intro a θ
    calc ‖zs a + δ * Complex.exp (θ * Complex.I)‖
        ≤ ‖zs a‖ + ‖(δ : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_add_le _ _
      _ ≤ R + δ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hδ.le]
        linarith [hzs a]
      _ < r' := by linarith
  have hcircW : ∀ a (θ : ℝ), W (zs a + δ * Complex.exp (θ * Complex.I)) =
      U (zs a + δ * Complex.exp (θ * Complex.I)) + Lg := by
    intro a θ
    have h1 := circlePotential_ge hm1 hδ hzs (z := zs a + δ * Complex.exp (θ * Complex.I))
      (r' := r') (hcirc_norm a θ)
    exact max_eq_left (by linarith)
  have hintU : ∀ a, ∫ θ in (0 : ℝ)..2 * Real.pi, U (zs a + δ * Complex.exp (θ * Complex.I)) =
      2 * Real.pi * Real.circleAverage U (zs a) δ := by
    intro a
    rw [Real.circleAverage_def, smul_eq_mul]
    have : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    rw [← mul_assoc, this, one_mul]
    rfl
  -- energy of `W`
  have hEWval : ∫ z, ‖fderiv ℝ W z‖ ^ 2 =
      2 * Real.pi * ((1 / (m : ℝ)) * ∑ a, Real.circleAverage U (zs a) δ + Lg) := by
    have h1 : ∫ z, ‖fderiv ℝ W z‖ ^ 2 = ∫ z, fderiv ℝ W z (circleGradField m δ zs z) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_fderiv_trunc m hδ zs Lg] with z hz
      by_cases h : 0 < U z + Lg
      · have h' : 0 < circlePotential m δ zs z + Lg := h
        have hz' : fderiv ℝ W z = innerSL ℝ (circleGradField m δ zs z) := by
          rw [show fderiv ℝ W z = _ from hz]
          simp only [h', ↓reduceIte]
        rw [hz', innerSL_apply_norm, innerSL_apply_apply, real_inner_self_eq_norm_sq]
      · have h' : ¬ 0 < circlePotential m δ zs z + Lg := h
        have hz' : fderiv ℝ W z = 0 := by
          rw [show fderiv ℝ W z = _ from hz]
          simp only [h', ↓reduceIte]
        simp [hz']
    rw [h1, hEW]
    have h2 : ∀ a, ∫ θ in (0 : ℝ)..2 * Real.pi, W (zs a + δ * Complex.exp (θ * Complex.I)) =
        2 * Real.pi * Real.circleAverage U (zs a) δ + 2 * Real.pi * Lg := by
      intro a
      have hc : Continuous fun θ : ℝ => U (zs a + δ * Complex.exp (θ * Complex.I)) :=
        hKU.continuous.comp (by fun_prop)
      simp_rw [hcircW]
      rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const,
        hintU]
      simp
    simp_rw [h2]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
  have hEuval : ∫ z, fderiv ℝ u z (circleGradField m δ zs z) = 2 * Real.pi := by
    rw [hEu]
    simp_rw [hu1]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- integrability
  have hA := integrable_sq_norm_fderiv hu hucs
  have hB := integrable_sq_norm_fderiv hW hWcs
  have hAB : Integrable (fun z => ‖fderiv ℝ u z‖ * ‖fderiv ℝ W z‖) := by
    refine ((hA.add hB).div_const 2).mono'
      (((measurable_fderiv (𝕜 := ℝ) (f := u)).norm.mul
        (measurable_fderiv (𝕜 := ℝ) (f := W)).norm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖fderiv ℝ u z‖ - ‖fderiv ℝ W z‖)]
  -- pointwise estimate
  have hae : ∀ᵐ z ∂(volume : Measure ℂ),
      fderiv ℝ u z (circleGradField m δ zs z) ≤ ‖fderiv ℝ u z‖ * ‖fderiv ℝ W z‖ := by
    have hsph : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ ≠ r' := by
      have h0 : (volume : Measure ℂ) (sphere (0 : ℂ) r') = 0 := Measure.addHaar_sphere _ _ _
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz h
      exact hz (by rw [mem_sphere, dist_zero_right]; exact h)
    filter_upwards [ae_fderiv_trunc m hδ zs Lg, ae_fderiv_circlePotential m hδ zs,
      fderiv_eq_zero_ae_level hV 0, hsph] with z h1 h2 h3 h4
    rcases lt_or_gt_of_ne h4 with h | h
    · have hge := circlePotential_ge hm1 hδ hzs (z := z) (r' := r') h
      have hgW : ‖circleGradField m δ zs z‖ ≤ ‖fderiv ℝ W z‖ := by
        by_cases hp : 0 < U z + Lg
        · have hp' : 0 < circlePotential m δ zs z + Lg := hp
          rw [show fderiv ℝ W z = _ from h1]
          simp only [hp', ↓reduceIte, innerSL_apply_norm, le_refl]
        · have h0 : (fun y => U y + Lg) z = 0 := by
            show U z + Lg = 0
            linarith
          have h5 := h3 h0
          rw [fderiv_add_const, h2] at h5
          have h6 : ‖circleGradField m δ zs z‖ = 0 := by
            rw [← innerSL_apply_norm ℝ, h5, norm_zero]
          rw [h6]
          exact norm_nonneg _
      calc fderiv ℝ u z (circleGradField m δ zs z)
          ≤ ‖fderiv ℝ u z (circleGradField m δ zs z)‖ := Real.le_norm_self _
        _ ≤ ‖fderiv ℝ u z‖ * ‖circleGradField m δ zs z‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hgW (norm_nonneg _)
    · have hev : u =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        have : {w : ℂ | r' < ‖w‖} ∈ 𝓝 z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds h
        filter_upwards [this] with w hw
        exact hu0 w hw.le
      have : fderiv ℝ u z = 0 := by rw [hev.fderiv_eq]; simp
      simp [this]
  have hC : 2 * Real.pi ≤ ∫ z, ‖fderiv ℝ u z‖ * ‖fderiv ℝ W z‖ := by
    rw [← hEuval]
    exact integral_mono_ae hIu hAB hae
  have hCS := integral_mul_sq_le hA hB hAB
  have hA0 : 0 ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 := integral_nonneg fun z => sq_nonneg _
  have hP : 0 < 2 * Real.pi := by positivity
  have hdir : dirichletEnergy u = ∫ z, ‖fderiv ℝ u z‖ ^ 2 := rfl
  rw [hdir]
  rw [hEWval] at hCS
  have h1 : (2 * Real.pi) ^ 2 ≤ (∫ z, ‖fderiv ℝ u z‖ ^ 2) *
      (2 * Real.pi * ((1 / (m : ℝ)) * ∑ a, Real.circleAverage U (zs a) δ + Lg)) :=
    le_trans (pow_le_pow_left₀ hP.le hC 2) hCS
  have h2 : (∫ z, ‖fderiv ℝ u z‖ ^ 2) *
      (2 * Real.pi * ((1 / (m : ℝ)) * ∑ a, Real.circleAverage U (zs a) δ + Lg)) ≤
      (∫ z, ‖fderiv ℝ u z‖ ^ 2) * (2 * Real.pi * (B + Lg)) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    apply mul_le_mul_of_nonneg_left _ hP.le
    linarith
  refine le_of_mul_le_mul_left ?_ hP
  nlinarith

/-- [Supplement C, Prop. 3.1 (`prop:energy`)] Energy lower bound: a Lipschitz function equal to `1`
near a compact `K ⊆ B̄(0,R)` of positive transfinite diameter and `0` off `B(0,r')` has Dirichlet
energy at least `2π / (log (r' + R) - log d(K))`. -/
theorem energy_lower_bound {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {R : ℝ}
    (hKR : K ⊆ Metric.closedBall 0 R) (hd : 0 < transfiniteDiameter K) {r' : ℝ} (hr : R < r')
    {u : ℂ → ℝ} {L : NNReal} (hu : LipschitzWith L u) {O : Set ℂ} (hO : IsOpen O) (hKO : K ⊆ O)
    (hu1 : ∀ z ∈ O, u z = 1) (hu0 : ∀ z, r' ≤ ‖z‖ → u z = 0) :
    2 * Real.pi ≤ dirichletEnergy u * (Real.log (r' + R) - Real.log (transfiniteDiameter K)) := by
  have hR : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hne
    exact (norm_nonneg x).trans (by simpa using hKR hx)
  set D := transfiniteDiameter K with hDdef
  have hDir0 : 0 ≤ dirichletEnergy u := integral_nonneg fun z => sq_nonneg _
  obtain ⟨δ₀, hδ₀, hth⟩ := hK.exists_thickening_subset_open hO hKO
  have key : ∀ δ : ℝ, 0 < δ → δ < δ₀ → δ < r' - R →
      2 * Real.pi ≤ dirichletEnergy u * (Real.log (r' + R + δ) - Real.log D) := by
    intro δ hδ h1 h2
    have hm : ∀ m : ℕ, 2 ≤ m → 2 * Real.pi ≤ dirichletEnergy u *
        ((1 / (m : ℝ)) * Real.log (1 / δ) - (((m : ℝ) - 1) / m) * Real.log (feketeDiam m K) +
          Real.log (r' + R + δ)) := by
      intro m hm
      obtain ⟨zs, hzsK, hmax, -⟩ := exists_fekete_tuple hK hne m
      have hDm : D ≤ feketeDiam m K := ciInf_le (bddBelow_feketeDiam K) ⟨m, hm⟩
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have hpos : 0 < vandermondeNorm zs := by
        rw [hmax]
        refine lt_of_le_of_ne (feketeDelta_nonneg m K) fun h0 => ?_
        have hexp : (2 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≠ 0 := by
          have : (0 : ℝ) < (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
          positivity
        have : feketeDiam m K = 0 := by
          unfold feketeDiam
          rw [← h0]
          exact Real.zero_rpow hexp
        linarith
      refine energy_step hm hR hδ h2 (fun a => by simpa using hKR (hzsK a)) hu ?_ hu0
        (circleAverage_circlePotential_le hm hδ hzsK hmax hpos)
      intro a θ
      apply hu1
      apply hth
      rw [mem_thickening_iff]
      refine ⟨zs a, hzsK a, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg hδ.le]
      exact h1
    have t1 : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have t2 : Tendsto (fun m : ℕ => ((m : ℝ) - 1) / m) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub t1
      rw [sub_zero] at this
      refine this.congr' (eventually_atTop.2 ⟨1, fun m hm => ?_⟩)
      have : (m : ℝ) ≠ 0 := by positivity
      field_simp
    have t3 : Tendsto (fun m : ℕ => Real.log (feketeDiam m K)) atTop (𝓝 (Real.log D)) :=
      (Real.continuousAt_log hd.ne').tendsto.comp (tendsto_feketeDiam hK hne)
    have hlim := (((t1.mul_const (Real.log (1 / δ))).sub (t2.mul t3)).add_const
      (Real.log (r' + R + δ))).const_mul (dirichletEnergy u)
    have := ge_of_tendsto hlim (eventually_atTop.2 ⟨2, hm⟩)
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using this
  have hδ₁ : 0 < min δ₀ (r' - R) := lt_min hδ₀ (by linarith)
  have hcont : ContinuousAt (fun δ : ℝ => dirichletEnergy u * (Real.log (r' + R + δ) -
      Real.log D)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.sub ?_ continuousAt_const)
    refine ContinuousAt.log (continuousAt_const.add continuousAt_id) ?_
    simp only [add_zero]
    linarith
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₁] with δ hδ
  exact key δ hδ.1 (lt_of_lt_of_le hδ.2 (min_le_left _ _)) (lt_of_lt_of_le hδ.2 (min_le_right _ _))

end RestrictedPolynomials
