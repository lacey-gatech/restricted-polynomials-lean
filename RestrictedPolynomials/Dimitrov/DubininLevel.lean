module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Level sets of Lipschitz functions (Supplement C, Lemma 2.1, `lem:level`)

Source: Supplement C, Lemma 2.1 (`lem:level`), with the countability of isolated points and the
transfer `ℂ ≃ ℝ × ℝ` for Tonelli made explicit.

A Lipschitz function `f : ℂ → ℝ` has `fderiv ℝ f = 0` almost everywhere on `{f = c}`, and consequently
`fderiv ℝ (max f c) = 1_{f > c} • fderiv ℝ f` almost everywhere.

Plan: along each horizontal (or vertical) line, the points of `{f = c}` at which the directional
derivative is nonzero are isolated points of the level set of the restriction, hence countable. Tonelli
on `ℝ × ℝ` makes the corresponding subset of `ℂ` null.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

noncomputable section

namespace RestrictedPolynomials

/-- Along a line `t ↦ z₀ + t v`, the parameters at which `f` is differentiable, takes the value `c`,
and has nonzero directional derivative form a countable set (they are isolated in the level set). -/
lemma countable_line_bad {f : ℂ → ℝ} (c : ℝ) (z₀ v : ℂ) :
    {t : ℝ | DifferentiableAt ℝ f (z₀ + t • v) ∧ f (z₀ + t • v) = c ∧
      fderiv ℝ f (z₀ + t • v) v ≠ 0}.Countable := by
  set T : Set ℝ := {t | f (z₀ + t • v) = c} with hT
  refine (countable_setOfPred_isolated_right_within (s := T)).mono ?_
  rintro t ⟨hd, hc, hne⟩
  refine ⟨hc, ?_⟩
  have hder : HasDerivAt (fun s : ℝ => f (z₀ + s • v)) (fderiv ℝ f (z₀ + t • v) v) t := by
    have h1 : HasDerivAt (fun s : ℝ => z₀ + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z₀
    exact hd.hasFDerivAt.comp_hasDerivAt t h1
  have hev : ∀ᶠ s in 𝓝[≠] t, f (z₀ + s • v) ≠ c := hder.eventually_ne hne
  have hle : 𝓝[T ∩ Ioi t] t ≤ 𝓝[≠] t := by
    refine nhdsWithin_mono _ ?_
    intro s hs
    exact ne_of_gt hs.2
  have h1 : ∀ᶠ s in 𝓝[T ∩ Ioi t] t, f (z₀ + s • v) ≠ c := hle hev
  have h2 : ∀ᶠ s in 𝓝[T ∩ Ioi t] t, s ∈ T := by
    filter_upwards [self_mem_nhdsWithin] with s hs using hs.1
  rw [← Filter.eventually_false_iff_eq_bot]
  filter_upwards [h1, h2] with s hs1 hs2
  exact hs1 hs2

/-- Measurability of the bad set in a fixed direction. -/
lemma measurableSet_bad {f : ℂ → ℝ} (hf : Continuous f) (c : ℝ) (v : ℂ) :
    MeasurableSet {z : ℂ | DifferentiableAt ℝ f z ∧ f z = c ∧ fderiv ℝ f z v ≠ 0} := by
  have h1 : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} := measurableSet_of_differentiableAt ℝ f
  have h2 : MeasurableSet {z : ℂ | f z = c} := hf.measurable (measurableSet_singleton c)
  have h3 : MeasurableSet {z : ℂ | fderiv ℝ f z v ≠ 0} :=
    ((measurable_fderiv ℝ f).apply_continuousLinearMap v) (measurableSet_singleton 0).compl
  exact h1.inter (h2.inter h3)

/-- Tonelli, vertical slices: a measurable set of `ℂ` all of whose vertical slices are null is null. -/
lemma volume_eq_zero_of_vslices {S : Set ℂ} (hS : MeasurableSet S)
    (h : ∀ x : ℝ, volume {y : ℝ | (⟨x, y⟩ : ℂ) ∈ S} = 0) : volume S = 0 := by
  have hB : MeasurableSet {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ S} :=
    Complex.measurableEquivRealProd.symm.measurable hS
  have hpre : Complex.measurableEquivRealProd ⁻¹' {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ S} = S := by
    ext z; simp
  have h0 : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ S} = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hB]
    exact Eventually.of_forall fun x => h x
  rw [← hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage hB.nullMeasurableSet]
  exact h0

/-- Tonelli, horizontal slices: a measurable set of `ℂ` all of whose horizontal slices are null is
null. -/
lemma volume_eq_zero_of_hslices {S : Set ℂ} (hS : MeasurableSet S)
    (h : ∀ y : ℝ, volume {x : ℝ | (⟨x, y⟩ : ℂ) ∈ S} = 0) : volume S = 0 := by
  have hB : MeasurableSet {p : ℝ × ℝ | (⟨p.2, p.1⟩ : ℂ) ∈ S} :=
    (Complex.measurableEquivRealProd.symm.measurable.comp measurable_swap) hS
  have hpre : (Prod.swap ∘ Complex.measurableEquivRealProd) ⁻¹'
      {p : ℝ × ℝ | (⟨p.2, p.1⟩ : ℂ) ∈ S} = S := by
    ext z; simp
  have h0 : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | (⟨p.2, p.1⟩ : ℂ) ∈ S} = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hB]
    exact Eventually.of_forall fun x => h x
  have hmp : MeasurePreserving (Prod.swap ∘ Complex.measurableEquivRealProd) volume
      (volume : Measure (ℝ × ℝ)) := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).comp
      Complex.volume_preserving_equiv_real_prod
    simpa [Measure.volume_eq_prod] using this
  rw [← hpre, hmp.measure_preimage hB.nullMeasurableSet]
  exact h0

/-- The first directional-derivative bad set is null. -/
lemma volume_bad_one {f : ℂ → ℝ} (hf : Continuous f) (c : ℝ) :
    volume {z : ℂ | DifferentiableAt ℝ f z ∧ f z = c ∧ fderiv ℝ f z 1 ≠ 0} = 0 := by
  refine volume_eq_zero_of_hslices (measurableSet_bad hf c 1) fun y => ?_
  have h := (countable_line_bad (f := f) c ((y : ℂ) * Complex.I) 1).measure_zero
    (volume : Measure ℝ)
  convert h using 2
  ext x
  have : (⟨x, y⟩ : ℂ) = (y : ℂ) * Complex.I + (x : ℝ) • (1 : ℂ) := by
    apply Complex.ext <;> simp
  simp [this]

/-- The second directional-derivative bad set is null. -/
lemma volume_bad_I {f : ℂ → ℝ} (hf : Continuous f) (c : ℝ) :
    volume {z : ℂ | DifferentiableAt ℝ f z ∧ f z = c ∧ fderiv ℝ f z Complex.I ≠ 0} = 0 := by
  refine volume_eq_zero_of_vslices (measurableSet_bad hf c Complex.I) fun x => ?_
  have h := (countable_line_bad (f := f) c (x : ℂ) Complex.I).measure_zero
    (volume : Measure ℝ)
  convert h using 2
  ext y
  have : (⟨x, y⟩ : ℂ) = (x : ℂ) + (y : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  simp [this]

/-- [Supplement C, Lemma 2.1] A Lipschitz function has zero derivative a.e. on each level set. -/
theorem fderiv_eq_zero_ae_level {f : ℂ → ℝ} {K : NNReal} (hf : LipschitzWith K f) (c : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), f z = c → fderiv ℝ f z = 0 := by
  have hd : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ f z := hf.ae_differentiableAt
  have h1 := measure_eq_zero_iff_ae_notMem.1 (volume_bad_one hf.continuous c)
  have h2 := measure_eq_zero_iff_ae_notMem.1 (volume_bad_I hf.continuous c)
  filter_upwards [hd, h1, h2] with z hz hz1 hz2 hzc
  have e1 : fderiv ℝ f z 1 = 0 := by
    by_contra h; exact hz1 ⟨hz, hzc, h⟩
  have e2 : fderiv ℝ f z Complex.I = 0 := by
    by_contra h; exact hz2 ⟨hz, hzc, h⟩
  ext w
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  rw [hw, map_add, map_smul, map_smul, e1, e2]
  simp

/-- [Supplement C, Lemma 2.1, consequence] a.e. `∇ max(f, c) = 1_{f > c} ∇ f`. -/
theorem fderiv_max_const_ae {f : ℂ → ℝ} {K : NNReal} (hf : LipschitzWith K f) (c : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      fderiv ℝ (fun y => max (f y) c) z = if c < f z then fderiv ℝ f z else 0 := by
  have hW : LipschitzWith K (fun y => max (f y) c) :=
    hf.max (LipschitzWith.const c) |>.weaken (by simp)
  filter_upwards [fderiv_eq_zero_ae_level hW c] with z hz
  rcases lt_trichotomy (f z) c with h | h | h
  · have hev : (fun y => max (f y) c) =ᶠ[𝓝 z] fun _ => c := by
      filter_upwards [hf.continuous.continuousAt.eventually_lt continuousAt_const h] with y hy
      exact max_eq_right hy.le
    rw [hev.fderiv_eq]
    simp [not_lt.2 h.le]
  · have := hz (by simp [h])
    rw [this]
    simp [h]
  · have hev : (fun y => max (f y) c) =ᶠ[𝓝 z] f := by
      filter_upwards [continuousAt_const.eventually_lt hf.continuous.continuousAt h] with y hy
      exact max_eq_left hy.le
    rw [hev.fderiv_eq]
    simp [h]

end RestrictedPolynomials
