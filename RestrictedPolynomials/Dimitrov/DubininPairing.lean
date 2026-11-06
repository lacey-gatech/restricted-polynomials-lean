module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import RestrictedPolynomials.Dimitrov.DubininPolar
public import RestrictedPolynomials.Dimitrov.DubininArcsine
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Pairing of a Lipschitz test function with `∇U^ν` (Supplement C, Lemma 5.1, `lem:nupair`)

Source: Supplement C, Lemma `lem:nupair`.  If `u` is Lipschitz with compact support and `u = 1` on an open set
`O ⊇ K*`, then `∫_{ℂ \ K*} ⟨∇u, ∇U^ν⟩ = 2π`.

Route: with `δ₀` such that the `δ₀`-thickening of the compact set `K*` lies in `O` and `δ = δ₀/2`, the
integrand equals `-∫ 1_{δ < |z-w|} ⟨∇u(z), (z-w)/|z-w|²⟩ dν(w)`, because `∇u = 0` on `O`.  Fubini
(`MeasureTheory.integral_integral_swap`) and the polar identity at center `w ∈ K*` (the circle
`C(w, δ)` lies in `O`) give `-2π` for each `w`; `ν` is a probability measure.
-/

@[expose] public section

open MeasureTheory
open scoped Real

noncomputable section

namespace RestrictedPolynomials

section C6
variable {N : ℕ} {R : ℝ}

/-- The pairing kernel `z, v ↦ ∇u(z) · (z-v)/|z-v|²`, cut off to `|z-v| > δ`. -/
private def pairKer (u : ℂ → ℝ) (δ : ℝ) (z v : ℂ) : ℝ :=
  Set.indicator {p : ℂ × ℂ | δ < ‖p.1 - p.2‖}
    (fun p => fderiv ℝ u p.1 ((‖p.1 - p.2‖ ^ 2)⁻¹ • (p.1 - p.2))) (z, v)

private lemma measurable_pairKer (u : ℂ → ℝ) (δ : ℝ) :
    Measurable (Function.uncurry (pairKer u δ)) := by
  unfold pairKer
  refine Measurable.indicator ?_ ?_
  · have hA : Measurable fun p : ℂ × ℂ => fderiv ℝ u p.1 :=
      (measurable_fderiv ℝ u).comp measurable_fst
    have hy : Measurable fun p : ℂ × ℂ => (‖p.1 - p.2‖ ^ 2)⁻¹ • (p.1 - p.2) := by fun_prop
    have hdec : ∀ (ℓ : ℂ →L[ℝ] ℝ) (y : ℂ), ℓ y = y.re * ℓ 1 + y.im * ℓ Complex.I := by
      intro ℓ y
      have : y = y.re • (1 : ℂ) + y.im • Complex.I := by apply Complex.ext <;> simp
      calc ℓ y = ℓ (y.re • (1 : ℂ) + y.im • Complex.I) := congrArg ℓ this
        _ = _ := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 : Measurable fun p : ℂ × ℂ => fderiv ℝ u p.1 1 :=
      (measurable_fderiv_apply_const ℝ u 1).comp measurable_fst
    have h2 : Measurable fun p : ℂ × ℂ => fderiv ℝ u p.1 Complex.I :=
      (measurable_fderiv_apply_const ℝ u Complex.I).comp measurable_fst
    have : (fun p : ℂ × ℂ => fderiv ℝ u p.1 ((‖p.1 - p.2‖ ^ 2)⁻¹ • (p.1 - p.2))) =
        fun p => ((‖p.1 - p.2‖ ^ 2)⁻¹ • (p.1 - p.2)).re * fderiv ℝ u p.1 1 +
          ((‖p.1 - p.2‖ ^ 2)⁻¹ • (p.1 - p.2)).im * fderiv ℝ u p.1 Complex.I :=
      funext fun p => hdec _ _
    rw [this]
    exact ((Complex.measurable_re.comp hy).mul h1).add ((Complex.measurable_im.comp hy).mul h2)
  · exact measurableSet_lt measurable_const (by fun_prop)

/-- The pairing kernel vanishes if `u` has zero derivative at `z`. -/
private lemma pairKer_eq_zero_of_fderiv {u : ℂ → ℝ} {δ : ℝ} {z : ℂ} (h : fderiv ℝ u z = 0) (v : ℂ) :
    pairKer u δ z v = 0 := by
  unfold pairKer
  simp [Set.indicator, h]

/-- Bound on the pairing kernel. -/
private lemma norm_pairKer_le {u : ℂ → ℝ} {L : NNReal} (hu : LipschitzWith L u) {δ : ℝ}
    (hδ : 0 < δ) (z v : ℂ) : ‖pairKer u δ z v‖ ≤ L / δ := by
  unfold pairKer
  by_cases hz : δ < ‖z - v‖
  · have hz' : (z, v) ∈ {p : ℂ × ℂ | δ < ‖p.1 - p.2‖} := hz
    rw [Set.indicator_of_mem hz']
    have h1 : ‖fderiv ℝ u z‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hu
    have hpos : 0 < ‖z - v‖ := hδ.trans hz
    calc ‖fderiv ℝ u z ((‖z - v‖ ^ 2)⁻¹ • (z - v))‖
        ≤ ‖fderiv ℝ u z‖ * ‖(‖z - v‖ ^ 2)⁻¹ • (z - v)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * (1 / δ) := by
          have : ‖(‖z - v‖ ^ 2)⁻¹ • (z - v)‖ = (‖z - v‖)⁻¹ := by
            rw [norm_smul, norm_inv, norm_pow, norm_norm]
            field_simp
          rw [this]
          refine mul_le_mul h1 ?_ (by positivity) (by positivity)
          rw [← one_div]
          exact one_div_le_one_div_of_le hδ hz.le
      _ = L / δ := by ring
  · have hz' : (z, v) ∉ {p : ℂ × ℂ | δ < ‖p.1 - p.2‖} := hz
    rw [Set.indicator_of_notMem hz']
    simp only [norm_zero]
    positivity

/-- [Supplement C, Lemma 5.1] The pairing of a Lipschitz test function that is `1` near `K*` with the
gradient of the arcsine potential is `2π`. -/
theorem arcsine_pairing (hN : 1 ≤ N) (hR : 0 < R) {u : ℂ → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (hc : HasCompactSupport u) {O : Set ℂ} (hO : IsOpen O)
    (hKO : starSet N R ⊆ O) (h1 : ∀ z ∈ O, u z = 1) :
    IntegrableOn (fun z => inner ℝ (gradient u z) (gradient (arcsinePotential N R) z))
        (starSet N R)ᶜ ∧
    ∫ z in (starSet N R)ᶜ, inner ℝ (gradient u z) (gradient (arcsinePotential N R) z) =
      2 * Real.pi := by
  have : IsProbabilityMeasure (arcsineMeasure N R) := isProbabilityMeasure_arcsineMeasure hN hR
  set ν := arcsineMeasure N R with hν
  set Ks := starSet N R with hKs
  have hKclosed : IsClosed Ks := isClosed_starSet hN
  have hKcpt : IsCompact Ks :=
    Metric.isCompact_of_isClosed_isBounded hKclosed
      (Metric.isBounded_closedBall.subset (starSet_subset_closedBall hN hR.le))
  obtain ⟨δ₀, hδ₀, hth⟩ := hKcpt.exists_thickening_subset_open hO hKO
  set δ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδlt : δ < δ₀ := by rw [hδdef]; linarith
  -- points within `δ₀` of `K*` lie in `O`
  have hnear : ∀ z w, w ∈ Ks → ‖z - w‖ < δ₀ → z ∈ O := by
    intro z w hw hzw
    refine hth (Metric.mem_thickening_iff.2 ⟨w, hw, ?_⟩)
    rwa [dist_eq_norm]
  -- the derivative of `u` vanishes on `O`
  have hder0 : ∀ z ∈ O, fderiv ℝ u z = 0 := by
    intro z hz
    have : u =ᶠ[nhds z] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hO.mem_nhds hz) (fun y hy => h1 y hy)
    rw [this.fderiv_eq]
    simp
  -- pointwise formula for the integrand off `K*`
  have hpt : ∀ z, z ∉ Ks →
      inner ℝ (gradient u z) (gradient (arcsinePotential N R) z) =
        -∫ v, pairKer u δ z v ∂ν := by
    intro z hz
    have e1 : inner ℝ (gradient u z) (gradient (arcsinePotential N R) z) =
        fderiv ℝ (arcsinePotential N R) z (gradient u z) := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    rw [e1, fderiv_arcsinePotential hN hR hz]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_starSet hN hR] with v hv
    have e2 : inner ℝ (z - v) (gradient u z) = fderiv ℝ u z (z - v) := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    rw [e2]
    unfold pairKer
    by_cases hzv : δ < ‖z - v‖
    · have hzv' : (z, v) ∈ {p : ℂ × ℂ | δ < ‖p.1 - p.2‖} := hzv
      rw [Set.indicator_of_mem hzv']
      simp only [map_smul, smul_eq_mul]
      ring
    · have hzv' : (z, v) ∉ {p : ℂ × ℂ | δ < ‖p.1 - p.2‖} := hzv
      rw [Set.indicator_of_notMem hzv']
      have hzO : z ∈ O := hnear z v hv (lt_of_le_of_lt (not_lt.1 hzv) hδlt)
      rw [hder0 z hzO]
      simp
  -- integrability of the kernel on the product
  have hint : Integrable (Function.uncurry (pairKer u δ)) ((volume : Measure ℂ).prod ν) := by
    set C := tsupport (fderiv ℝ u) with hC
    have hCc : IsCompact C := (hc.fderiv (𝕜 := ℝ)).isCompact
    have hsupp : ∀ z v, z ∉ C → pairKer u δ z v = 0 := by
      intro z v hz
      exact pairKer_eq_zero_of_fderiv (image_eq_zero_of_notMem_tsupport hz) v
    have hmeas : MeasurableSet (C ×ˢ (Set.univ : Set ℂ)) :=
      hCc.isClosed.measurableSet.prod MeasurableSet.univ
    have hfin : ((volume : Measure ℂ).prod ν) (C ×ˢ (Set.univ : Set ℂ)) ≠ ⊤ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hCc.measure_lt_top.ne (measure_ne_top _ _)
    have hbd : Integrable (Set.indicator (C ×ˢ (Set.univ : Set ℂ))
        (fun _ => (L : ℝ) / δ)) ((volume : Measure ℂ).prod ν) :=
      (integrable_indicator_iff hmeas).2 (integrableOn_const hfin)
    refine hbd.mono' (measurable_pairKer u δ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p.1 ∈ C
    · have : p ∈ C ×ˢ (Set.univ : Set ℂ) := ⟨hp, Set.mem_univ _⟩
      rw [Set.indicator_of_mem this]
      exact norm_pairKer_le hu hδ p.1 p.2
    · have h0 : pairKer u δ p.1 p.2 = 0 := hsupp _ _ hp
      have : p ∉ C ×ˢ (Set.univ : Set ℂ) := fun h => hp h.1
      rw [Set.indicator_of_notMem this]
      simp [Function.uncurry, h0]
  -- the function `z ↦ -∫ v, pairKer z v` vanishes on `K*`
  have hKzero : ∀ z, z ∉ Ksᶜ → -∫ v, pairKer u δ z v ∂ν = 0 := by
    intro z hz
    have hzK : z ∈ Ks := by simpa using hz
    have : ∀ v, pairKer u δ z v = 0 := pairKer_eq_zero_of_fderiv (hder0 z (hKO hzK))
    simp [this]
  have hKmeas : MeasurableSet Ksᶜ := hKclosed.measurableSet.compl
  refine ⟨?_, ?_⟩
  · have h2 : Integrable (fun z => -∫ v, pairKer u δ z v ∂ν) (volume : Measure ℂ) :=
      hint.integral_prod_left.neg
    refine (h2.integrableOn).congr_fun (fun z hz => ?_) hKmeas
    exact (hpt z hz).symm
  · calc ∫ z in Ksᶜ, inner ℝ (gradient u z) (gradient (arcsinePotential N R) z)
        = ∫ z in Ksᶜ, -∫ v, pairKer u δ z v ∂ν :=
          setIntegral_congr_fun hKmeas (fun z hz => hpt z hz)
      _ = ∫ z, -∫ v, pairKer u δ z v ∂ν :=
          setIntegral_eq_integral_of_forall_compl_eq_zero hKzero
      _ = -∫ z, ∫ v, pairKer u δ z v ∂ν := integral_neg _
      _ = -∫ v, ∫ z, pairKer u δ z v ∂(volume : Measure ℂ) ∂ν := by
          rw [integral_integral_swap hint]
      _ = -∫ v, (-(2 * Real.pi)) ∂ν := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [ae_mem_starSet hN hR] with w hw
          have hp := polar_identity hu hc w hδ
          have hset : MeasurableSet {z : ℂ | δ < ‖z - w‖} :=
            measurableSet_lt measurable_const (by fun_prop)
          have e3 : ∫ z, pairKer u δ z w ∂(volume : Measure ℂ) =
              ∫ z in {z : ℂ | δ < ‖z - w‖},
                fderiv ℝ u z ((‖z - w‖ ^ 2)⁻¹ • (z - w)) := by
            rw [← integral_indicator hset]
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            unfold pairKer
            beta_reduce
            by_cases hz : δ < ‖z - w‖
            · have hz' : (z, w) ∈ {p : ℂ × ℂ | δ < ‖p.1 - p.2‖} := hz
              rw [Set.indicator_of_mem hz', Set.indicator_of_mem (show z ∈ _ from hz)]
            · have hz' : (z, w) ∉ {p : ℂ × ℂ | δ < ‖p.1 - p.2‖} := hz
              rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem (show z ∉ _ from hz)]
          have e4 : ∫ θ in (0 : ℝ)..2 * Real.pi, u (w + δ * Complex.exp (θ * Complex.I)) =
              2 * Real.pi := by
            have : ∀ θ : ℝ, u (w + δ * Complex.exp (θ * Complex.I)) = 1 := by
              intro θ
              refine h1 _ (hnear _ w hw ?_)
              have : w + δ * Complex.exp (θ * Complex.I) - w = δ * Complex.exp (θ * Complex.I) := by
                ring
              rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
                Complex.norm_real, Real.norm_of_nonneg hδ.le]
              exact hδlt
            simp [this]
          rw [e3, hp.2, e4]
      _ = 2 * Real.pi := by
          simp

end C6

end RestrictedPolynomials
