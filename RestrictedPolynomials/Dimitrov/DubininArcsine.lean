module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import RestrictedPolynomials.Dimitrov.DubininDefs

/-!
# The arcsine potential of the symmetric star (Supplement C, Lemma 4.1)

Source: Supplement C, section 4 (`lem:arcsine`).  For `K* = {z : z^N ∈ [0, R^N]}` and the probability measure `ν`
(`arcsineMeasure`) we prove the closedness and size of `K*`, that `ν` is a probability measure
supported on `K*`, and the parts (a)-(e) of the lemma for `U^ν` (`arcsinePotential`):

* (a) `arcsinePotential_eq_integral`: the explicit integral, via `∏_k (z - ω^k y) = z^N - y^N`;
* (b) `arcsinePotential_of_mem_starSet`: `U^ν = -log c*` on `K*`, via the factorisation
  `|x(t) - x(s)| = (R^N/4) |e^{it} - e^{is}| |e^{it} - e^{-is}|` and
  `circleAverage_log_norm_sub_const₁`;
* (c) `arcsinePotential_le`: `U^ν(z) ≤ -log(|z| - R)`;
* (d) `arcsinePotential_rootN_mul`, `arcsinePotential_conj`: invariance under `D_N`;
* (e) `lowerSemicontinuous_arcsinePotential` (monotone truncation and dominated convergence),
  `contDiffOn_arcsinePotential` (the potential is the real part of a holomorphic function of
  `z^N` off `[0, R^N]`) and `fderiv_arcsinePotential` (differentiation under the integral,
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`).

Helper lemmas are `private` unless a downstream Dubinin file may use them.
-/

@[expose] public section

open MeasureTheory
open scoped Real ContDiff

noncomputable section
namespace RestrictedPolynomials

section C5
variable {N : ℕ} {R : ℝ}

/-- The symmetric star `K*` is closed. -/
theorem isClosed_starSet (hN : 1 ≤ N) : IsClosed (starSet N R) := by
  have _ := hN
  have h : starSet N R = (fun z : ℂ => z ^ N) ⁻¹' (Complex.ofReal '' Set.Icc (0 : ℝ) (R ^ N)) := by
    ext z; simp [starSet, eq_comm]
  rw [h]
  exact (isCompact_Icc.image Complex.continuous_ofReal).isClosed.preimage (continuous_pow N)

/-- `K* ⊆ B̄(0, R)`. -/
theorem starSet_subset_closedBall (hN : 1 ≤ N) (hR : 0 ≤ R) :
    starSet N R ⊆ Metric.closedBall 0 R := by
  rintro z ⟨x, ⟨hx0, hx1⟩, hz⟩
  have h1 : ‖z‖ ^ N = x := by
    rw [← norm_pow, hz, Complex.norm_real, Real.norm_of_nonneg hx0]
  rw [mem_closedBall_zero_iff]
  exact le_of_pow_le_pow_left₀ (by omega) hR (h1 ▸ hx1)

/-- The segment `[0, R]` lies in `K*`. -/
theorem segment_subset_starSet (hN : 1 ≤ N) (hR : 0 ≤ R) :
    segment ℝ (0 : ℂ) (R : ℂ) ⊆ starSet N R := by
  have _ := hN
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  have hb1 : b ≤ 1 := by linarith
  refine ⟨(b * R) ^ N, ⟨by positivity, ?_⟩, ?_⟩
  · rw [mul_pow]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hb hb1)
  · simp


/-- The real number `x(s) = (R^N/2)(1 + cos s)`. -/
private def arcX (N : ℕ) (R s : ℝ) : ℝ := R ^ N / 2 * (1 + Real.cos s)

/-- `x(s) ≥ 0`. -/
private lemma arcX_nonneg (hR : 0 ≤ R) (s : ℝ) : 0 ≤ arcX N R s := by
  unfold arcX
  have := Real.neg_one_le_cos s
  have : 0 ≤ R ^ N := pow_nonneg hR N
  exact mul_nonneg (by positivity) (by linarith)

/-- `x(s) ≤ R^N`. -/
private lemma arcX_le (hR : 0 ≤ R) (s : ℝ) : arcX N R s ≤ R ^ N := by
  unfold arcX
  have := Real.cos_le_one s
  have : 0 ≤ R ^ N := pow_nonneg hR N
  nlinarith

/-- `x` is continuous. -/
private lemma continuous_arcX : Continuous (arcX N R) := by
  unfold arcX; fun_prop

/-- The `N`-th power of `ω^k x(s)^{1/N}` is `x(s)`. -/
private lemma starPoint_pow (hN : 1 ≤ N) (hR : 0 ≤ R) (k : Fin N) (s : ℝ) :
    starPoint N R k s ^ N = (arcX N R s : ℂ) := by
  unfold starPoint
  rw [mul_pow, ← Complex.ofReal_pow]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [show (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)) =
      (k : ℕ) * (2 * Real.pi * Complex.I) by field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I _
  rw [h1, one_mul]
  congr 1
  change (arcX N R s ^ (1 / (N : ℝ))) ^ N = arcX N R s
  rw [← Real.rpow_natCast, ← Real.rpow_mul (arcX_nonneg hR s)]
  have : (1 : ℝ) / N * N = 1 := by
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  rw [this, Real.rpow_one]

/-- The points `ω^k x(s)^{1/N}` lie in `K*`. -/
lemma starPoint_mem (hN : 1 ≤ N) (hR : 0 ≤ R) (k : Fin N) (s : ℝ) :
    starPoint N R k s ∈ starSet N R :=
  ⟨arcX N R s, ⟨arcX_nonneg hR s, arcX_le hR s⟩, starPoint_pow hN hR k s⟩

/-- `s ↦ ω^k x(s)^{1/N}` is continuous. -/
lemma continuous_starPoint (hN : 1 ≤ N) (k : Fin N) : Continuous (starPoint N R k) := by
  unfold starPoint
  have : (0 : ℝ) ≤ 1 / N := by positivity
  refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
  exact (Real.continuous_rpow_const this).comp (by fun_prop)

/-- `s ↦ ω^k x(s)^{1/N}` is measurable. -/
lemma measurable_starPoint (hN : 1 ≤ N) (k : Fin N) : Measurable (starPoint N R k) :=
  (continuous_starPoint hN k).measurable

/-- The arcsine measure of a measurable set, in terms of the parameter measure. -/
lemma arcsineMeasure_apply (hN : 1 ≤ N) (S : Set ℂ) (hS : MeasurableSet S) :
    arcsineMeasure N R S = ENNReal.ofReal (1 / (Real.pi * N)) *
      ∑ k : Fin N, volume (Set.Ioc 0 Real.pi ∩ starPoint N R k ⁻¹' S) := by
  unfold arcsineMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Measure.map_apply (measurable_starPoint hN k) hS, Measure.restrict_apply
    ((measurable_starPoint hN k) hS)]
  rw [Set.inter_comm]

/-- [Supplement C, Lemma 4.1, definition of `ν`] `ν` is a probability measure. -/
theorem isProbabilityMeasure_arcsineMeasure (hN : 1 ≤ N) (hR : 0 < R) :
    IsProbabilityMeasure (arcsineMeasure N R) := by
  have _ := hR
  refine ⟨?_⟩
  rw [arcsineMeasure_apply hN _ MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.inter_univ, Real.volume_Ioc, sub_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show 1 / (Real.pi * N) * (N * Real.pi) = 1 by field_simp]
  simp

/-- `ν` is supported on `K*`. -/
theorem arcsineMeasure_compl_starSet (hN : 1 ≤ N) (hR : 0 < R) :
    arcsineMeasure N R (starSet N R)ᶜ = 0 := by
  rw [arcsineMeasure_apply hN _ (isClosed_starSet hN).measurableSet.compl]
  have : ∀ k : Fin N, Set.Ioc 0 Real.pi ∩ starPoint N R k ⁻¹' (starSet N R)ᶜ = ∅ := by
    intro k
    ext s
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro _ h
    exact h (starPoint_mem hN hR.le k s)
  simp only [this, measure_empty, Finset.sum_const_zero, mul_zero]


/-- Integrability against one pushforward summand. -/
private lemma integrable_map_starPoint (hN : 1 ≤ N) {f : ℂ → ℝ} (hfm : Measurable f) (k : Fin N)
    (hf : IntegrableOn (fun s => f (starPoint N R k s)) (Set.Ioc 0 Real.pi)) :
    Integrable f ((volume.restrict (Set.Ioc 0 Real.pi)).map (starPoint N R k)) :=
  (integrable_map_measure hfm.aestronglyMeasurable
    (measurable_starPoint hN k).aemeasurable).2 hf

/-- Integrability against `ν` from integrability along the parametrisations. -/
lemma integrable_arcsineMeasure (hN : 1 ≤ N) {f : ℂ → ℝ} (hfm : Measurable f)
    (hf : ∀ k : Fin N, IntegrableOn (fun s => f (starPoint N R k s)) (Set.Ioc 0 Real.pi)) :
    Integrable f (arcsineMeasure N R) := by
  unfold arcsineMeasure
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  exact integrable_finsetSum_measure.2 fun k _ => integrable_map_starPoint hN hfm k (hf k)

/-- The integral against `ν` as an average of parameter integrals. -/
lemma integral_arcsineMeasure (hN : 1 ≤ N) {f : ℂ → ℝ} (hfm : Measurable f)
    (hf : ∀ k : Fin N, IntegrableOn (fun s => f (starPoint N R k s)) (Set.Ioc 0 Real.pi)) :
    ∫ w, f w ∂(arcsineMeasure N R) =
      (1 / (Real.pi * N)) * ∑ k : Fin N, ∫ s in Set.Ioc 0 Real.pi, f (starPoint N R k s) := by
  unfold arcsineMeasure
  rw [integral_smul_measure, integral_finsetSum_measure
    (fun k _ => integrable_map_starPoint hN hfm k (hf k))]
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_map (measurable_starPoint hN k).aemeasurable hfm.aestronglyMeasurable


/-- `e^{2πik/N} = (e^{2πi/N})^k`. -/
private lemma exp_rootN_pow (N : ℕ) (k : Fin N) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / N) ^ (k : ℕ) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- `∏_k (z - ω^k y) = z^N - y^N`. -/
private lemma prod_sub_rootN_mul (hN : 1 ≤ N) (z y : ℂ) :
    ∏ k : Fin N, (z - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)) * y) =
      z ^ N - y ^ N := by
  have hN0 : N ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp N hN0
  have : NeZero N := ⟨hN0⟩
  rw [hprim.pow_sub_pow_eq_prod_sub_mul z y (by omega)]
  refine Finset.prod_nbij (fun k : Fin N => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)))
    ?_ ?_ ?_ ?_
  · intro k _
    rw [Polynomial.mem_nthRootsFinset (by omega), exp_rootN_pow, pow_right_comm,
      hprim.pow_eq_one, one_pow]
  · intro k _ l _ h
    simp only [exp_rootN_pow] at h
    exact Fin.ext (hprim.pow_inj k.2 l.2 h)
  · intro ζ hζ
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (by omega)] at hζ
    obtain ⟨i, hi, hiζ⟩ := hprim.eq_pow_of_pow_eq_one hζ
    exact ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), (exp_rootN_pow N ⟨i, hi⟩).trans hiζ⟩
  · intro k _; rfl


/-- Sum of logs over the `N` roots, away from the singular point. -/
private lemma sum_log_starPoint (hN : 1 ≤ N) (hR : 0 ≤ R) (z : ℂ) (s : ℝ)
    (h : z ^ N ≠ (arcX N R s : ℂ)) :
    ∑ k : Fin N, Real.log ‖z - starPoint N R k s‖ =
      Real.log ‖z ^ N - (arcX N R s : ℂ)‖ := by
  have hy : (((arcX N R s) ^ ((1 : ℝ) / N) : ℝ) : ℂ) ^ N = (arcX N R s : ℂ) := by
    rw [← Complex.ofReal_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (arcX_nonneg hR s)]
    have : (1 : ℝ) / N * N = 1 := by
      have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp
    rw [this, Real.rpow_one]
  have hprod := prod_sub_rootN_mul hN z (((arcX N R s) ^ ((1 : ℝ) / N) : ℝ) : ℂ)
  rw [hy] at hprod
  rw [← hprod, norm_prod, Real.log_prod]
  · rfl
  · intro k _ hk
    rw [norm_eq_zero] at hk
    exact h (sub_eq_zero.1 (by rw [← hprod]; exact Finset.prod_eq_zero (Finset.mem_univ k) hk))


/-- The unit-circle log kernel `θ ↦ log ‖e^{iθ} - a‖`. -/
private def circLog (a : ℂ) (θ : ℝ) : ℝ := Real.log ‖Complex.exp (θ * Complex.I) - a‖

/-- `circLog a` is `2π`-periodic. -/
private lemma circLog_periodic (a : ℂ) : Function.Periodic (circLog a) (2 * Real.pi) := by
  intro θ
  unfold circLog
  congr 3
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `circLog a` is interval integrable. -/
private lemma intervalIntegrable_circLog {a : ℂ} (_a1 : ‖a‖ = 1) (x y : ℝ) :
    IntervalIntegrable (circLog a) volume x y := by
  refine (circLog_periodic a).intervalIntegrable₀ (by positivity) ?_ x y
  have := circleIntegrable_log_norm_sub_const (a := a) (c := 0) 1
  unfold circLog
  simpa [CircleIntegrable, circleMap_zero, Function.comp_def] using this

/-- `∫_0^π circLog a θ dθ + ∫_0^π circLog a (-θ) dθ = 0` for `‖a‖ = 1` (circle average). -/
private lemma integral_circLog_pair {a : ℂ} (a1 : ‖a‖ = 1) :
    (∫ s in (0 : ℝ)..Real.pi, circLog a s) + ∫ s in (0 : ℝ)..Real.pi, circLog a (-s) = 0 := by
  have h2 : ∫ s in (0 : ℝ)..Real.pi, circLog a (-s) = ∫ s in (-Real.pi)..0, circLog a s := by
    rw [intervalIntegral.integral_comp_neg (fun s => circLog a s)]; simp
  rw [h2, add_comm, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_circLog a1 _ _) (intervalIntegrable_circLog a1 _ _)]
  have h3 := (circLog_periodic a).intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h3
  rw [h3]
  have h4 := circleAverage_log_norm_sub_const₁ (a := a) a1
  rw [Real.circleAverage_def] at h4
  simp only [circleMap_zero, smul_eq_mul, mul_eq_zero, inv_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact absurd h4 (by push Not; exact ⟨two_ne_zero, Real.pi_ne_zero⟩)
  · simpa [circLog, circleMap_zero] using h4


/-- `θ ↦ circLog a (-θ)` is interval integrable. -/
private lemma intervalIntegrable_circLog_neg {a : ℂ} (a1 : ‖a‖ = 1) :
    IntervalIntegrable (fun s => circLog a (-s)) volume 0 Real.pi := by
  have := (IntervalIntegrable.iff_comp_neg (a := -0) (b := -Real.pi)
    (f := circLog a)).mp (intervalIntegrable_circLog a1 _ _)
  simpa using this

/-- `|e^{it} - e^{is}| |e^{it} - e^{-is}| = 2 |cos t - cos s|`. -/
private lemma norm_exp_factor (t s : ℝ) :
    ‖Complex.exp (t * Complex.I) - Complex.exp (s * Complex.I)‖ *
      ‖Complex.exp (t * Complex.I) - Complex.exp (-(s : ℂ) * Complex.I)‖ =
      2 * |Real.cos t - Real.cos s| := by
  have h1 : (Complex.exp (t * Complex.I) - Complex.exp (s * Complex.I)) *
      (Complex.exp (t * Complex.I) - Complex.exp (-(s : ℂ) * Complex.I)) =
      Complex.exp (t * Complex.I) * (((2 * (Real.cos t - Real.cos s) : ℝ)) : ℂ) := by
    have e1 : Complex.exp (t * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    have e2 : Complex.exp (s * Complex.I) * Complex.exp (-(s : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    have c1 := Complex.two_cos (x := (t : ℂ))
    have c2 := Complex.two_cos (x := (s : ℂ))
    push_cast
    linear_combination (-Complex.exp (t * Complex.I)) * c1 + Complex.exp (t * Complex.I) * c2 + e2 - e1
  have h2 := congrArg norm h1
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul] at h2
  rw [h2]; norm_num


/-- Factorisation of `log |x(t) - x(s)|` as `log (R^N/4)` plus two circle kernels. -/
private lemma log_arc_self_eq (hR : 0 < R) {t s : ℝ} (ht : t ∈ Set.Icc 0 Real.pi)
    (hs : s ∈ Set.Icc 0 Real.pi) (hne : s ≠ t) :
    Real.log ‖(arcX N R t : ℂ) - (arcX N R s : ℂ)‖ =
      Real.log (R ^ N / 4) + circLog (Complex.exp (t * Complex.I)) s +
        circLog (Complex.exp (t * Complex.I)) (-s) := by
  have hcos : Real.cos t ≠ Real.cos s := fun h => hne (Real.injOn_cos hs ht h.symm)
  have hfac := norm_exp_factor t s
  have hpos : 0 < 2 * |Real.cos t - Real.cos s| :=
    by have := abs_pos.2 (sub_ne_zero.2 hcos); positivity
  rw [← hfac] at hpos
  have hn1 : ‖Complex.exp (t * Complex.I) - Complex.exp (s * Complex.I)‖ ≠ 0 :=
    left_ne_zero_of_mul hpos.ne'
  have hn2 : ‖Complex.exp (t * Complex.I) - Complex.exp (-(s : ℂ) * Complex.I)‖ ≠ 0 :=
    right_ne_zero_of_mul hpos.ne'
  have hRN : 0 < R ^ N := pow_pos hR N
  have hnorm : ‖(arcX N R t : ℂ) - (arcX N R s : ℂ)‖ = (R ^ N / 4) *
      (‖Complex.exp (t * Complex.I) - Complex.exp (s * Complex.I)‖ *
      ‖Complex.exp (t * Complex.I) - Complex.exp (-(s : ℂ) * Complex.I)‖) := by
    rw [hfac, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    unfold arcX
    rw [show R ^ N / 2 * (1 + Real.cos t) - R ^ N / 2 * (1 + Real.cos s) =
      R ^ N / 2 * (Real.cos t - Real.cos s) by ring, abs_mul, abs_of_pos (by positivity)]
    ring
  rw [hnorm, Real.log_mul (by positivity) (mul_ne_zero hn1 hn2), Real.log_mul hn1 hn2]
  unfold circLog
  push_cast
  rw [norm_sub_rev (Complex.exp (↑s * Complex.I)) (Complex.exp (↑t * Complex.I)),
    norm_sub_rev (Complex.exp (-↑s * Complex.I)) (Complex.exp (↑t * Complex.I))]
  ring

/-- `∫_0^π log |x(t) - x(s)| ds = π log (R^N/4)`, with integrability. -/
private lemma integral_log_arc_self (hR : 0 < R) {t : ℝ} (ht : t ∈ Set.Icc 0 Real.pi) :
    IntervalIntegrable (fun s => Real.log ‖(arcX N R t : ℂ) - (arcX N R s : ℂ)‖) volume 0 Real.pi ∧
    ∫ s in (0 : ℝ)..Real.pi, Real.log ‖(arcX N R t : ℂ) - (arcX N R s : ℂ)‖ =
      Real.pi * Real.log (R ^ N / 4) := by
  set A := Complex.exp (t * Complex.I) with hA
  have a1 : ‖A‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 Real.pi →
      Real.log (R ^ N / 4) + circLog A s + circLog A (-s) =
        Real.log ‖(arcX N R t : ℂ) - (arcX N R s : ℂ)‖ := by
    filter_upwards [Measure.ae_ne volume t] with s hst hs
    rw [Set.uIoc_of_le Real.pi_pos.le] at hs
    exact (log_arc_self_eq hR ht ⟨hs.1.le, hs.2⟩ hst).symm
  have hI : IntervalIntegrable (fun s => Real.log (R ^ N / 4) + circLog A s + circLog A (-s))
      volume 0 Real.pi :=
    ((intervalIntegrable_const).add (intervalIntegrable_circLog a1 _ _)).add
      (intervalIntegrable_circLog_neg a1)
  refine ⟨hI.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hae), ?_⟩
  rw [← intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_add
    ((intervalIntegrable_const).add (intervalIntegrable_circLog a1 _ _))
    (intervalIntegrable_circLog_neg a1),
    intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_circLog a1 _ _),
    add_assoc, integral_circLog_pair a1]
  simp


/-- `x` is injective on `[0, π]`. -/
private lemma arcX_inj (hR : 0 < R) {s t : ℝ} (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi)
    (h : arcX N R s = arcX N R t) : s = t := by
  unfold arcX at h
  have hRN : 0 < R ^ N := pow_pos hR N
  have : Real.cos s = Real.cos t := by
    have := mul_left_cancel₀ (by positivity : R ^ N / 2 ≠ 0) h
    linarith
  exact Real.injOn_cos hs ht this

/-- Almost everywhere in `(0, π]`, `x(s) ≠ ζ`. -/
private lemma ae_arc_ne (hR : 0 < R) (ζ : ℂ) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 Real.pi)), ζ ≠ (arcX N R s : ℂ) := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  by_cases h : ∃ t ∈ Set.Icc 0 Real.pi, ζ = (arcX N R t : ℂ)
  · obtain ⟨t, ht, rfl⟩ := h
    filter_upwards [Measure.ae_ne volume t] with s hst hs heq
    exact hst (arcX_inj hR ⟨hs.1.le, hs.2⟩ ht (Complex.ofReal_injective heq).symm)
  · push Not at h
    exact Filter.Eventually.of_forall fun s hs => h s ⟨hs.1.le, hs.2⟩

/-- The key integrability: `s ↦ log ‖ζ - x(s)‖` is integrable on `[0, π]` for every `ζ`. -/
private lemma intervalIntegrable_log_arc (hR : 0 < R) (ζ : ℂ) :
    IntervalIntegrable (fun s => Real.log ‖ζ - (arcX N R s : ℂ)‖) volume 0 Real.pi := by
  by_cases h : ∃ t ∈ Set.Icc 0 Real.pi, ζ = (arcX N R t : ℂ)
  · obtain ⟨t, ht, rfl⟩ := h
    exact (integral_log_arc_self hR ht).1
  · push Not at h
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le Real.pi_pos.le]
    refine ContinuousOn.log (Continuous.continuousOn ?_) ?_
    · exact (continuous_const.sub (Complex.continuous_ofReal.comp continuous_arcX)).norm
    · intro s hs
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact h s hs

/-- `IntegrableOn` form of `intervalIntegrable_log_arc`. -/
private lemma integrableOn_log_arc (hR : 0 < R) (ζ : ℂ) :
    IntegrableOn (fun s => Real.log ‖ζ - (arcX N R s : ℂ)‖) (Set.Ioc 0 Real.pi) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).1 (intervalIntegrable_log_arc hR ζ)


/-- `‖ω^k x(s)^{1/N}‖ ≤ R`. -/
lemma norm_starPoint_le (hN : 1 ≤ N) (hR : 0 ≤ R) (k : Fin N) (s : ℝ) :
    ‖starPoint N R k s‖ ≤ R :=
  mem_closedBall_zero_iff.1 (starSet_subset_closedBall hN hR (starPoint_mem hN hR k s))

/-- Each summand `s ↦ log ‖z - ω^k x(s)^{1/N}‖` is integrable. -/
private lemma integrableOn_log_starPoint (hN : 1 ≤ N) (hR : 0 < R) (z : ℂ) (k : Fin N) :
    IntegrableOn (fun s => Real.log ‖z - starPoint N R k s‖) (Set.Ioc 0 Real.pi) := by
  set C := Real.log (‖z‖ + R + 1) with hC
  have hC0 : 0 ≤ C := Real.log_nonneg (by have := norm_nonneg z; linarith)
  set h : Fin N → ℝ → ℝ := fun j s => Real.log ‖z - starPoint N R j s‖ with hh
  have hle : ∀ j s, h j s ≤ C := by
    intro j s
    simp only [hh]
    rcases (norm_nonneg (z - starPoint N R j s)).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hC0
    · refine Real.log_le_log h0 ?_
      calc ‖z - starPoint N R j s‖ ≤ ‖z‖ + ‖starPoint N R j s‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + R + 1 := by linarith [norm_starPoint_le hN hR.le j s]
  have hmeas : ∀ j, Measurable (h j) := fun j =>
    Real.measurable_log.comp ((measurable_const.sub (measurable_starPoint hN j)).norm)
  have hH := integrableOn_log_arc (N := N) (R := R) hR (z ^ N)
  have hsum : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 Real.pi)),
      ∑ j, h j s = Real.log ‖z ^ N - (arcX N R s : ℂ)‖ := by
    filter_upwards [ae_arc_ne (N := N) hR (z ^ N)] with s hs
    exact sum_log_starPoint hN hR.le z s hs
  have hG : Integrable (fun s => (N : ℝ) * C - Real.log ‖z ^ N - (arcX N R s : ℂ)‖)
      (volume.restrict (Set.Ioc 0 Real.pi)) := (integrable_const _).sub hH
  have hg : Integrable (fun s => C - h k s) (volume.restrict (Set.Ioc 0 Real.pi)) := by
    refine hG.mono' ((measurable_const.sub (hmeas k)).aestronglyMeasurable) ?_
    filter_upwards [hsum] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hle k s)), ← hs]
    have : ∑ j, (C - h j s) = N * C - ∑ j, h j s := by
      simp [Finset.sum_sub_distrib]
    rw [← this]
    exact Finset.single_le_sum (f := fun j => C - h j s) (fun j _ => sub_nonneg.2 (hle j s))
      (Finset.mem_univ k)
  have := (integrable_const C).sub hg
  exact this.congr (Filter.Eventually.of_forall fun s => by simp [hh])

/-- [Supplement C, Lemma 4.1(a)] Explicit formula for `U^ν`. -/
theorem arcsinePotential_eq_integral (hN : 1 ≤ N) (hR : 0 < R) (z : ℂ) :
    arcsinePotential N R z =
      -(1 / ((N : ℝ) * Real.pi)) *
        ∫ s in (0 : ℝ)..Real.pi, Real.log ‖z ^ N - ((R ^ N / 2 * (1 + Real.cos s) : ℝ) : ℂ)‖ := by
  have hmeas : Measurable fun w : ℂ => -Real.log ‖z - w‖ :=
    (Real.measurable_log.comp (measurable_const.sub measurable_id).norm).neg
  have hint : ∀ k : Fin N, IntegrableOn (fun s => -Real.log ‖z - starPoint N R k s‖)
      (Set.Ioc 0 Real.pi) := fun k => (integrableOn_log_starPoint hN hR z k).neg
  unfold arcsinePotential
  rw [integral_arcsineMeasure hN hmeas hint]
  rw [← integral_finsetSum _ (fun k _ => hint k)]
  have : ∫ s in Set.Ioc 0 Real.pi, ∑ k : Fin N, -Real.log ‖z - starPoint N R k s‖ =
      -∫ s in Set.Ioc 0 Real.pi, Real.log ‖z ^ N - (arcX N R s : ℂ)‖ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_arc_ne (N := N) hR (z ^ N)] with s hs
    rw [Finset.sum_neg_distrib, sum_log_starPoint hN hR.le z s hs]
  rw [this, intervalIntegral.integral_of_le Real.pi_pos.le]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [show (1 : ℝ) / (Real.pi * N) = 1 / (N * Real.pi) by ring]
  unfold arcX
  ring


/-- Every `x ∈ [0, R^N]` is some `x(t)`, `t ∈ [0, π]`. -/
private lemma exists_arcX_eq (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (R ^ N)) :
    ∃ t ∈ Set.Icc 0 Real.pi, arcX N R t = x := by
  have hRN : 0 < R ^ N := pow_pos hR N
  refine ⟨Real.arccos (2 * x / R ^ N - 1), ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  have h1 : -1 ≤ 2 * x / R ^ N - 1 := by
    have : 0 ≤ 2 * x / R ^ N := by have := hx.1; positivity
    linarith
  have h2 : 2 * x / R ^ N - 1 ≤ 1 := by
    have : 2 * x / R ^ N ≤ 2 := by
      rw [div_le_iff₀ hRN]; linarith [hx.2]
    linarith
  unfold arcX
  rw [Real.cos_arccos h1 h2]
  field_simp
  ring

/-- [Supplement C, Lemma 4.1(b)] `U^ν = -log c*` on `K*`. -/
theorem arcsinePotential_of_mem_starSet (hN : 1 ≤ N) (hR : 0 < R) {z : ℂ} (hz : z ∈ starSet N R) :
    arcsinePotential N R z = -Real.log (starRadius N R) := by
  obtain ⟨x, hx, hzx⟩ := hz
  obtain ⟨t, ht, hxt⟩ := exists_arcX_eq (N := N) hR hx
  rw [arcsinePotential_eq_integral hN hR z, hzx]
  have := (integral_log_arc_self (N := N) hR ht).2
  rw [← hxt]
  change -(1 / ((N : ℝ) * Real.pi)) *
      ∫ s in (0 : ℝ)..Real.pi, Real.log ‖(arcX N R t : ℂ) - (arcX N R s : ℂ)‖ = _
  rw [this]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hRN : 0 < R ^ N := pow_pos hR N
  unfold starRadius
  rw [Real.log_mul hR.ne' (by positivity), Real.log_rpow (by norm_num), Real.log_div hRN.ne'
    (by norm_num), Real.log_pow]
  field_simp
  ring

/-- `ν`-almost every point lies in `K*`. -/
lemma ae_mem_starSet (hN : 1 ≤ N) (hR : 0 < R) :
    ∀ᵐ w ∂(arcsineMeasure N R), w ∈ starSet N R := by
  have := arcsineMeasure_compl_starSet hN hR
  rw [measure_eq_zero_iff_ae_notMem] at this
  filter_upwards [this] with w hw
  simpa using hw

/-- The logarithmic kernel is `ν`-integrable. -/
lemma integrable_kernel (hN : 1 ≤ N) (hR : 0 < R) (z : ℂ) :
    Integrable (fun w : ℂ => -Real.log ‖z - w‖) (arcsineMeasure N R) :=
  integrable_arcsineMeasure hN
    ((Real.measurable_log.comp (measurable_const.sub measurable_id).norm).neg)
    (fun k => (integrableOn_log_starPoint hN hR z k).neg)

/-- [Supplement C, Lemma 4.1(c)] `U^ν(z) ≤ -log(|z| - R)`. -/
theorem arcsinePotential_le (hN : 1 ≤ N) (hR : 0 < R) {z : ℂ} (hz : R < ‖z‖) :
    arcsinePotential N R z ≤ -Real.log (‖z‖ - R) := by
  have := isProbabilityMeasure_arcsineMeasure hN hR
  have key : arcsinePotential N R z ≤ ∫ _w, -Real.log (‖z‖ - R) ∂(arcsineMeasure N R) := by
    unfold arcsinePotential
    refine integral_mono_ae (integrable_kernel hN hR z) (integrable_const _) ?_
    filter_upwards [ae_mem_starSet hN hR] with w hw
    have hw' := mem_closedBall_zero_iff.1 (starSet_subset_closedBall hN hR.le hw)
    have h1 : ‖z‖ - R ≤ ‖z - w‖ := by
      have := norm_sub_norm_le z w
      linarith
    simp only [neg_le_neg_iff]
    exact Real.log_le_log (by linarith) h1
  simpa using key

/-- `ω^N = 1`. -/
private lemma rootN_pow (hN : 1 ≤ N) : rootN N ^ N = 1 :=
  (Complex.isPrimitiveRoot_exp N (by omega)).pow_eq_one

/-- [Supplement C, Lemma 4.1(d)] Rotation invariance. -/
theorem arcsinePotential_rootN_mul (hN : 1 ≤ N) (hR : 0 < R) (z : ℂ) :
    arcsinePotential N R (rootN N * z) = arcsinePotential N R z := by
  rw [arcsinePotential_eq_integral hN hR, arcsinePotential_eq_integral hN hR, mul_pow,
    rootN_pow hN, one_mul]

/-- [Supplement C, Lemma 4.1(d)] Conjugation invariance. -/
theorem arcsinePotential_conj (hN : 1 ≤ N) (hR : 0 < R) (z : ℂ) :
    arcsinePotential N R (starRingEnd ℂ z) = arcsinePotential N R z := by
  rw [arcsinePotential_eq_integral hN hR, arcsinePotential_eq_integral hN hR]
  congr 2
  ext s
  congr 1
  conv_lhs => rw [← map_pow, ← Complex.conj_ofReal (R ^ N / 2 * (1 + Real.cos s)), ← map_sub,
    Complex.norm_conj]


/-- Derivative of `y ↦ -log ‖y - v‖` away from `v`. -/
private lemma hasFDerivAt_negLogNorm {z v : ℂ} (h : z ≠ v) :
    HasFDerivAt (fun y : ℂ => -Real.log ‖y - v‖)
      (-((‖z - v‖ ^ 2)⁻¹ • innerSL ℝ (z - v))) z := by
  have hne : ‖z - v‖ ^ 2 ≠ 0 := by
    have : z - v ≠ 0 := sub_ne_zero.2 h
    positivity
  have h1 : HasFDerivAt (fun y : ℂ => ‖y - v‖ ^ 2)
      (2 • (innerSL ℝ (z - v)).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    ((hasFDerivAt_id z).sub_const v).norm_sq
  have h2 := (h1.log hne).const_mul (-(1 / 2 : ℝ))
  convert h2 using 1
  · funext y
    simp only [Real.log_pow]
    push_cast
    ring
  · ext w
    simp only [neg_apply, smul_apply, innerSL_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul]
    ring


/-- `0 ∈ K*`. -/
lemma zero_mem_starSet (hN : 1 ≤ N) (hR : 0 ≤ R) : (0 : ℂ) ∈ starSet N R :=
  segment_subset_starSet hN hR (left_mem_segment ℝ _ _)

/-- A ball around `z ∉ K*` on which `‖z' - v‖ ≥ ε` for all `v ∈ K*`. -/
lemma exists_ball_lower (hN : 1 ≤ N) (hR : 0 ≤ R) {z : ℂ} (hz : z ∉ starSet N R) :
    ∃ ε > 0, ∀ z' ∈ Metric.ball z ε, ∀ v ∈ starSet N R, ε ≤ ‖z' - v‖ := by
  have hd : 0 < Metric.infDist z (starSet N R) :=
    ((isClosed_starSet hN).notMem_iff_infDist_pos ⟨0, zero_mem_starSet hN hR⟩).1 hz
  refine ⟨Metric.infDist z (starSet N R) / 2, by positivity, fun z' hz' v hv => ?_⟩
  have h1 := Metric.infDist_le_dist_of_mem (x := z) hv
  have h2 := dist_triangle z z' v
  rw [Metric.mem_ball] at hz'
  rw [← dist_eq_norm]
  linarith [dist_comm z z']

/-- Differentiation under the integral sign off `K*`. -/
lemma hasFDerivAt_arcsinePotential (hN : 1 ≤ N) (hR : 0 < R) {z : ℂ} (hz : z ∉ starSet N R) :
    HasFDerivAt (arcsinePotential N R)
      (∫ v, -((‖z - v‖ ^ 2)⁻¹ • innerSL ℝ (z - v)) ∂(arcsineMeasure N R)) z := by
  have := isProbabilityMeasure_arcsineMeasure hN hR
  obtain ⟨ε, hε, hlow⟩ := exists_ball_lower hN hR.le hz
  have hmem := ae_mem_starSet hN hR
  have hmeasF' : ∀ y : ℂ, AEStronglyMeasurable
      (fun v : ℂ => -((‖y - v‖ ^ 2)⁻¹ • innerSL ℝ (y - v))) (arcsineMeasure N R) := by
    intro y
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.neg (Measurable.fun_smul ?_ ?_)
    · exact ((measurable_const.sub measurable_id).norm.pow_const 2).inv
    · exact (innerSL ℝ).continuous.measurable.comp (measurable_const.sub measurable_id)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Metric.ball z ε)
    (bound := fun _ => 1 / ε) (F := fun y v => -Real.log ‖y - v‖)
    (F' := fun y v => -((‖y - v‖ ^ 2)⁻¹ • innerSL ℝ (y - v)))
    (Metric.ball_mem_nhds z hε) ?_ (integrable_kernel hN hR z) (hmeasF' z) ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((Real.measurable_log.comp (measurable_const.sub measurable_id).norm).neg).aestronglyMeasurable
  · filter_upwards [hmem] with v hv y hy
    have h1 := hlow y hy v hv
    have hpos : 0 < ‖y - v‖ := lt_of_lt_of_le hε h1
    rw [norm_neg, norm_smul, innerSL_apply_norm, norm_inv, norm_pow, norm_norm]
    rw [show (‖y - v‖ ^ 2)⁻¹ * ‖y - v‖ = (‖y - v‖)⁻¹ by field_simp]
    rw [one_div]
    exact inv_anti₀ hε h1
  · filter_upwards [hmem] with v hv y hy
    have hpos : 0 < ‖y - v‖ := lt_of_lt_of_le hε (hlow y hy v hv)
    exact hasFDerivAt_negLogNorm (sub_ne_zero.1 (norm_pos_iff.1 hpos))


/-- [Supplement C, Lemma 4.1(e)] The gradient formula for `U^ν` off `K*`. -/
theorem fderiv_arcsinePotential (hN : 1 ≤ N) (hR : 0 < R) {z : ℂ} (hz : z ∉ starSet N R) (w : ℂ) :
    fderiv ℝ (arcsinePotential N R) z w =
      -∫ v, inner ℝ (z - v) w / ‖z - v‖ ^ 2 ∂(arcsineMeasure N R) := by
  have := isProbabilityMeasure_arcsineMeasure hN hR
  rw [(hasFDerivAt_arcsinePotential hN hR hz).fderiv]
  obtain ⟨ε, hε, hlow⟩ := exists_ball_lower hN hR.le hz
  have hmem := ae_mem_starSet hN hR
  have hint : Integrable (fun v : ℂ => -((‖z - v‖ ^ 2)⁻¹ • innerSL ℝ (z - v)))
      (arcsineMeasure N R) := by
    refine Integrable.mono' (integrable_const (1 / ε)) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.neg (Measurable.fun_smul ?_ ?_)
      · exact ((measurable_const.sub measurable_id).norm.pow_const 2).inv
      · exact (innerSL ℝ).continuous.measurable.comp (measurable_const.sub measurable_id)
    · filter_upwards [hmem] with v hv
      have h1 := hlow z (Metric.mem_ball_self hε) v hv
      have hpos : 0 < ‖z - v‖ := lt_of_lt_of_le hε h1
      rw [norm_neg, norm_smul, innerSL_apply_norm, norm_inv, norm_pow, norm_norm]
      rw [show (‖z - v‖ ^ 2)⁻¹ * ‖z - v‖ = (‖z - v‖)⁻¹ by field_simp]
      rw [one_div]
      exact inv_anti₀ hε h1
  rw [ContinuousLinearMap.integral_apply hint, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [neg_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [inv_mul_eq_div]


/-- The `n`-th truncation of the kernel `-log ‖ζ - x(s)‖`. -/
private def truncKer (N : ℕ) (R : ℝ) (n : ℕ) (ζ : ℂ) (s : ℝ) : ℝ :=
  -Real.log (max ‖ζ - (arcX N R s : ℂ)‖ (1 / ((n : ℝ) + 1)))

/-- The truncation level is positive. -/
private lemma truncKer_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- The truncated kernel is measurable. -/
private lemma measurable_truncKer (n : ℕ) (ζ : ℂ) : Measurable (truncKer N R n ζ) := by
  unfold truncKer
  refine (Real.measurable_log.comp ?_).neg
  exact (((measurable_const.sub (Complex.measurable_ofReal.comp
    (continuous_arcX).measurable)).norm).max measurable_const)

/-- The truncated kernel is dominated by the kernel. -/
private lemma abs_truncKer_le {ζ : ℂ} {s : ℝ} (n : ℕ) (h : ζ ≠ (arcX N R s : ℂ)) :
    |truncKer N R n ζ s| ≤ |Real.log ‖ζ - (arcX N R s : ℂ)‖| := by
  have hr : 0 < ‖ζ - (arcX N R s : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
  set r := ‖ζ - (arcX N R s : ℂ)‖
  have hε := truncKer_pos n
  set ε := 1 / ((n : ℝ) + 1) with hεdef
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  unfold truncKer
  rw [abs_neg]
  rcases le_total ε r with h1 | h1
  · rw [max_eq_left h1]
  · rw [max_eq_right h1]
    have h2 : Real.log r ≤ Real.log ε := Real.log_le_log hr h1
    have h3 : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
    rw [abs_of_nonpos h3, abs_of_nonpos (h2.trans h3)]
    linarith

/-- Almost everywhere on `[0, π]`, `x(s) ≠ ζ`. -/
private lemma ae_arc_ne_Icc (hR : 0 < R) (ζ : ℂ) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc 0 Real.pi → ζ ≠ (arcX N R s : ℂ) := by
  by_cases h : ∃ t ∈ Set.Icc 0 Real.pi, ζ = (arcX N R t : ℂ)
  · obtain ⟨t, ht, rfl⟩ := h
    filter_upwards [Measure.ae_ne volume t] with s hst hs heq
    exact hst (arcX_inj hR hs ht (Complex.ofReal_injective heq).symm)
  · push Not at h
    exact Filter.Eventually.of_forall fun s hs => h s hs

/-- The truncated kernel is interval integrable. -/
private lemma intervalIntegrable_truncKer (hR : 0 < R) (n : ℕ) (ζ : ℂ) :
    IntervalIntegrable (truncKer N R n ζ) volume 0 Real.pi := by
  refine (intervalIntegrable_log_arc (N := N) hR ζ).abs.mono_fun'
    (measurable_truncKer n ζ).aestronglyMeasurable ?_
  rw [Set.uIoc_of_le Real.pi_pos.le]
  have h2 : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 Real.pi)), ζ ≠ (arcX N R s : ℂ) :=
    ae_arc_ne hR ζ
  filter_upwards [h2] with s hs
  simpa using abs_truncKer_le (N := N) (R := R) n hs


/-- The truncated integrals converge (dominated convergence). -/
private lemma tendsto_integral_truncKer (hR : 0 < R) (ζ : ℂ) :
    Filter.Tendsto (fun n : ℕ => ∫ s in (0 : ℝ)..Real.pi, truncKer N R n ζ s) Filter.atTop
      (nhds (∫ s in (0 : ℝ)..Real.pi, -Real.log ‖ζ - (arcX N R s : ℂ)‖)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => |Real.log ‖ζ - (arcX N R s : ℂ)‖|)
    (Filter.Eventually.of_forall fun n => ?_) (Filter.Eventually.of_forall fun n => ?_)
    (intervalIntegrable_log_arc (N := N) hR ζ).abs ?_
  · exact (measurable_truncKer n ζ).aestronglyMeasurable
  · rw [Set.uIoc_of_le Real.pi_pos.le]
    have h2 := ae_arc_ne (N := N) hR ζ
    rw [ae_restrict_iff' measurableSet_Ioc] at h2
    filter_upwards [h2] with s hs hs'
    simpa using abs_truncKer_le (N := N) (R := R) n (hs hs')
  · rw [Set.uIoc_of_le Real.pi_pos.le]
    have h2 := ae_arc_ne (N := N) hR ζ
    rw [ae_restrict_iff' measurableSet_Ioc] at h2
    filter_upwards [h2] with s hs hs'
    have hr : 0 < ‖ζ - (arcX N R s : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hs hs'))
    have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < ‖ζ - (arcX N R s : ℂ)‖ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (Iio_mem_nhds hr)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    unfold truncKer
    rw [max_eq_left hn.le]

/-- The truncated kernel is below the kernel. -/
private lemma truncKer_le {ζ : ℂ} {s : ℝ} (n : ℕ) (h : ζ ≠ (arcX N R s : ℂ)) :
    truncKer N R n ζ s ≤ -Real.log ‖ζ - (arcX N R s : ℂ)‖ := by
  have hr : 0 < ‖ζ - (arcX N R s : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
  unfold truncKer
  rw [neg_le_neg_iff]
  exact Real.log_le_log hr (le_max_left _ _)

/-- The truncated integral is below the full one. -/
private lemma integral_truncKer_le (hR : 0 < R) (n : ℕ) (ζ : ℂ) :
    ∫ s in (0 : ℝ)..Real.pi, truncKer N R n ζ s ≤
      ∫ s in (0 : ℝ)..Real.pi, -Real.log ‖ζ - (arcX N R s : ℂ)‖ := by
  refine intervalIntegral.integral_mono_ae_restrict Real.pi_pos.le
    (intervalIntegrable_truncKer hR n ζ) (intervalIntegrable_log_arc (N := N) hR ζ).neg ?_
  have := ae_arc_ne_Icc (N := N) hR ζ
  rw [← ae_restrict_iff' measurableSet_Icc] at this
  filter_upwards [this] with s hs
  exact truncKer_le n hs


/-- The truncated integral is continuous in `ζ`. -/
private lemma continuousAt_integral_truncKer (hR : 0 < R) (n : ℕ) (ζ₀ : ℂ) :
    ContinuousAt (fun ζ => ∫ s in (0 : ℝ)..Real.pi, truncKer N R n ζ s) ζ₀ := by
  have hε := truncKer_pos n
  set ε := 1 / ((n : ℝ) + 1) with hεdef
  set M := max (‖ζ₀‖ + 1 + R ^ N) ε with hM
  have hεM : ε ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le hε hεM
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => |Real.log ε| + |Real.log M|) ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun ζ =>
      (measurable_truncKer n ζ).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds ζ₀ one_pos] with ζ hζ
    refine Filter.Eventually.of_forall fun s _ => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    have h1 : ‖ζ - (arcX N R s : ℂ)‖ ≤ ‖ζ₀‖ + 1 + R ^ N := by
      have a1 : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
        have := norm_sub_norm_le ζ ζ₀
        linarith
      have a2 : ‖(arcX N R s : ℂ)‖ ≤ R ^ N := by
        rw [Complex.norm_real, Real.norm_of_nonneg (arcX_nonneg hR.le s)]
        exact arcX_le hR.le s
      calc ‖ζ - (arcX N R s : ℂ)‖ ≤ ‖ζ‖ + ‖(arcX N R s : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    set u := max ‖ζ - (arcX N R s : ℂ)‖ ε with hu
    have hu1 : ε ≤ u := le_max_right _ _
    have hu2 : u ≤ M := max_le (h1.trans (le_max_left _ _)) hεM
    have l1 : Real.log ε ≤ Real.log u := Real.log_le_log hε hu1
    have l2 : Real.log u ≤ Real.log M := Real.log_le_log (lt_of_lt_of_le hε hu1) hu2
    show ‖truncKer N R n ζ s‖ ≤ _
    unfold truncKer
    rw [← hu, Real.norm_eq_abs, abs_neg, abs_le]
    constructor
    · linarith [l1, neg_abs_le (Real.log ε), abs_nonneg (Real.log M)]
    · linarith [l2, le_abs_self (Real.log M), abs_nonneg (Real.log ε)]
  · refine Filter.Eventually.of_forall fun s _ => ?_
    unfold truncKer
    refine ContinuousAt.neg ?_
    have hc : ContinuousAt (fun ζ : ℂ => max ‖ζ - (arcX N R s : ℂ)‖ ε) ζ₀ := by
      fun_prop
    exact hc.log (lt_of_lt_of_le hε (le_max_right _ _)).ne'


/-- `U^ν(z) = (1/(Nπ)) ∫_0^π -log ‖z^N - x(s)‖ ds`. -/
private lemma arcsinePotential_eq_const_mul (hN : 1 ≤ N) (hR : 0 < R) (z : ℂ) :
    arcsinePotential N R z = (1 / ((N : ℝ) * Real.pi)) *
      ∫ s in (0 : ℝ)..Real.pi, -Real.log ‖z ^ N - (arcX N R s : ℂ)‖ := by
  rw [arcsinePotential_eq_integral hN hR z, intervalIntegral.integral_neg]
  unfold arcX
  ring

/-- [Supplement C, Lemma 4.1(e)] `U^ν` is lower semicontinuous. -/
theorem lowerSemicontinuous_arcsinePotential (hN : 1 ≤ N) (hR : 0 < R) :
    LowerSemicontinuous (arcsinePotential N R) := by
  intro z₀ y hy
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < 1 / ((N : ℝ) * Real.pi) := by positivity
  set c := 1 / ((N : ℝ) * Real.pi) with hcdef
  rw [arcsinePotential_eq_const_mul hN hR] at hy
  have h1 : y / c < ∫ s in (0 : ℝ)..Real.pi, -Real.log ‖z₀ ^ N - (arcX N R s : ℂ)‖ := by
    rw [div_lt_iff₀ hc]; linarith
  obtain ⟨n, hn⟩ := ((tendsto_integral_truncKer (N := N) hR (z₀ ^ N)).eventually
    (lt_mem_nhds h1)).exists
  have hcont : ContinuousAt (fun z : ℂ => ∫ s in (0 : ℝ)..Real.pi, truncKer N R n (z ^ N) s) z₀ :=
    ContinuousAt.comp (f := fun z : ℂ => z ^ N) (x := z₀)
      (continuousAt_integral_truncKer hR n (z₀ ^ N)) (continuous_pow N).continuousAt
  filter_upwards [hcont.eventually (lt_mem_nhds hn)] with z hz
  rw [arcsinePotential_eq_const_mul hN hR z]
  have h2 := integral_truncKer_le (N := N) hR n (z ^ N)
  have h3 : y / c < ∫ s in (0 : ℝ)..Real.pi, -Real.log ‖z ^ N - (arcX N R s : ℂ)‖ :=
    lt_of_lt_of_le hz h2
  rwa [div_lt_iff₀ hc, mul_comm] at h3


/-- Measurability of the complex-log kernel. -/
private lemma measurable_clogKer (e ζ : ℂ) :
    Measurable (fun s : ℝ => Complex.log (e * (ζ - (arcX N R s : ℂ)))) := by
  refine Measurable.clog ?_
  exact measurable_const.mul (measurable_const.sub
    (Complex.measurable_ofReal.comp continuous_arcX.measurable))

/-- Integrability of the complex-log kernel. -/
private lemma integrable_clogKer (hR : 0 < R) {e : ℂ} (he : ‖e‖ = 1) (ζ : ℂ) :
    Integrable (fun s : ℝ => Complex.log (e * (ζ - (arcX N R s : ℂ))))
      (volume.restrict (Set.Ioc 0 Real.pi)) := by
  refine Integrable.mono' ((integrableOn_log_arc (N := N) hR ζ).abs.add (integrable_const Real.pi))
    (measurable_clogKer e ζ).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im, norm_mul, he, one_mul]
  exact add_le_add le_rfl (Complex.abs_arg_le_pi _)

/-- Smoothness of `ζ ↦ ∫ log ‖ζ - x(s)‖` near a point where a branch of the logarithm is holomorphic. -/
private lemma contDiffAt_logIntegral (hR : 0 < R) {e : ℂ} (he : ‖e‖ = 1) (ζ₀ : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hslit : ∀ ζ ∈ Metric.ball ζ₀ ε, ∀ s : ℝ, e * (ζ - (arcX N R s : ℂ)) ∈ Complex.slitPlane)
    (hlow : ∀ ζ ∈ Metric.ball ζ₀ ε, ∀ s : ℝ, ε ≤ ‖ζ - (arcX N R s : ℂ)‖) :
    ContDiffAt ℝ ∞ (fun ζ : ℂ => ∫ s in Set.Ioc 0 Real.pi, Real.log ‖ζ - (arcX N R s : ℂ)‖) ζ₀ := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  set μ : Measure ℝ := volume.restrict (Set.Ioc 0 Real.pi) with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set G : ℂ → ℂ := fun ζ => ∫ s, Complex.log (e * (ζ - (arcX N R s : ℂ))) ∂μ with hG
  have hderiv : ∀ ζ₁ ∈ Metric.ball ζ₀ ε, DifferentiableAt ℂ G ζ₁ := by
    intro ζ₁ hζ₁
    have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := μ)
      (s := Metric.ball ζ₀ ε) (bound := fun _ => 1 / ε)
      (F := fun ζ s => Complex.log (e * (ζ - (arcX N R s : ℂ))))
      (F' := fun ζ s => (ζ - (arcX N R s : ℂ))⁻¹)
      (Metric.isOpen_ball.mem_nhds hζ₁)
      (Filter.Eventually.of_forall fun ζ => (measurable_clogKer e ζ).aestronglyMeasurable)
      (integrable_clogKer hR he ζ₁)
      (((measurable_const.sub (Complex.measurable_ofReal.comp
        continuous_arcX.measurable)).inv).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun s ζ hζ => ?_) (integrable_const _)
      (Filter.Eventually.of_forall fun s ζ hζ => ?_)).2
    · exact this.differentiableAt
    · rw [norm_inv, one_div]
      exact inv_anti₀ hε (hlow ζ hζ s)
    · have h1 : HasDerivAt (fun ζ : ℂ => e * (ζ - (arcX N R s : ℂ))) e ζ := by
        simpa using ((hasDerivAt_id ζ).sub_const (arcX N R s : ℂ)).const_mul e
      have h2 := h1.clog (hslit ζ hζ s)
      rwa [div_mul_cancel_left₀ he0] at h2
  have hOn : ContDiffOn ℂ ∞ G (Metric.ball ζ₀ ε) :=
    DifferentiableOn.contDiffOn (fun ζ hζ => (hderiv ζ hζ).differentiableWithinAt)
      Metric.isOpen_ball
  have hCD : ContDiffAt ℂ ∞ G ζ₀ := hOn.contDiffAt (Metric.ball_mem_nhds ζ₀ hε)
  have hCD' : ContDiffAt ℝ ∞ (fun ζ => (G ζ).re) ζ₀ :=
    (Complex.reCLM.contDiff.contDiffAt).comp ζ₀ (hCD.restrict_scalars ℝ)
  refine hCD'.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun ζ => ?_
  have := integral_re (integrable_clogKer (N := N) hR he ζ)
  simp only [RCLike.re_to_complex] at this
  simp only [hG]
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp [Complex.log_re, he]


/-- Branch and radius for smoothness at `ζ ∉ [0, b]`. -/
private lemma exists_smooth_data {b : ℝ} {ζ₀ : ℂ} (h : ∀ x ∈ Set.Icc (0 : ℝ) b, ζ₀ ≠ (x : ℂ)) :
    ∃ (e : ℂ) (ε : ℝ), ‖e‖ = 1 ∧ 0 < ε ∧
      (∀ ζ ∈ Metric.ball ζ₀ ε, ∀ x ∈ Set.Icc (0 : ℝ) b, e * (ζ - (x : ℂ)) ∈ Complex.slitPlane) ∧
      (∀ ζ ∈ Metric.ball ζ₀ ε, ∀ x ∈ Set.Icc (0 : ℝ) b, ε ≤ ‖ζ - (x : ℂ)‖) := by
  by_cases h1 : ζ₀.im = 0
  · by_cases h2 : b < ζ₀.re
    · refine ⟨1, (ζ₀.re - b) / 2, by simp, by linarith, ?_, ?_⟩
      · intro ζ hζ x hx
        rw [Metric.mem_ball, dist_eq_norm] at hζ
        have := (abs_le.1 ((Complex.abs_re_le_norm (ζ - ζ₀)).trans hζ.le)).1
        have := (Complex.abs_re_le_norm (ζ - ζ₀))
        rw [Complex.mem_slitPlane_iff]
        left
        simp only [one_mul, Complex.sub_re, Complex.ofReal_re]
        have := (abs_lt.1 (this.trans_lt hζ)).1
        simp only [Complex.sub_re] at this
        linarith [hx.2]
      · intro ζ hζ x hx
        rw [Metric.mem_ball, dist_eq_norm] at hζ
        have h3 := Complex.abs_re_le_norm (ζ - ζ₀)
        have h4 := (abs_lt.1 (h3.trans_lt hζ)).1
        simp only [Complex.sub_re] at h4
        have h5 := Complex.re_le_norm (ζ - (x : ℂ))
        simp only [Complex.sub_re, Complex.ofReal_re] at h5
        linarith [hx.2]
    · by_cases h3 : ζ₀.re < 0
      · refine ⟨-1, -ζ₀.re / 2, by simp, by linarith, ?_, ?_⟩
        · intro ζ hζ x hx
          rw [Metric.mem_ball, dist_eq_norm] at hζ
          have h4 := Complex.abs_re_le_norm (ζ - ζ₀)
          have h5 := (abs_lt.1 (h4.trans_lt hζ)).2
          simp only [Complex.sub_re] at h5
          rw [Complex.mem_slitPlane_iff]
          left
          simp only [neg_mul, one_mul, Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
          linarith [hx.1]
        · intro ζ hζ x hx
          rw [Metric.mem_ball, dist_eq_norm] at hζ
          have h4 := Complex.abs_re_le_norm (ζ - ζ₀)
          have h5 := (abs_lt.1 (h4.trans_lt hζ)).2
          simp only [Complex.sub_re] at h5
          have h6 := Complex.abs_re_le_norm (ζ - (x : ℂ))
          simp only [Complex.sub_re, Complex.ofReal_re] at h6
          have := neg_abs_le (ζ.re - x)
          linarith [hx.1]
      · exfalso
        refine h ζ₀.re ⟨by linarith, by linarith⟩ ?_
        apply Complex.ext <;> simp [h1]
  · have hpos : 0 < |ζ₀.im| := abs_pos.2 h1
    have key : ∀ ζ ∈ Metric.ball ζ₀ (|ζ₀.im| / 2), |ζ₀.im| / 2 < |ζ.im| := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_eq_norm] at hζ
      have h3 := Complex.abs_im_le_norm (ζ - ζ₀)
      simp only [Complex.sub_im] at h3
      have h4 := abs_sub_abs_le_abs_sub ζ₀.im ζ.im
      rw [abs_sub_comm] at h4
      linarith
    refine ⟨1, |ζ₀.im| / 2, by simp, by linarith, ?_, ?_⟩
    · intro ζ hζ x hx
      have := key ζ hζ
      rw [Complex.mem_slitPlane_iff]
      right
      simp only [one_mul, Complex.sub_im, Complex.ofReal_im, sub_zero]
      intro h0
      rw [h0, abs_zero] at this
      linarith
    · intro ζ hζ x hx
      have := key ζ hζ
      have h6 := Complex.abs_im_le_norm (ζ - (x : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h6
      linarith


/-- [Supplement C, Lemma 4.1(e)] `U^ν` is `C^∞` off `K*`. -/
theorem contDiffOn_arcsinePotential (hN : 1 ≤ N) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (arcsinePotential N R) (starSet N R)ᶜ := by
  intro z₀ hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  have hz : z₀ ∉ starSet N R := hz₀
  obtain ⟨e, ε, he, hε, hslit, hlow⟩ := exists_smooth_data (b := R ^ N) (ζ₀ := z₀ ^ N)
    (fun x hx h => hz ⟨x, hx, h⟩)
  have hcd := contDiffAt_logIntegral (N := N) hR he (z₀ ^ N) hε
    (fun ζ hζ s => hslit ζ hζ _ ⟨arcX_nonneg hR.le s, arcX_le hR.le s⟩)
    (fun ζ hζ s => hlow ζ hζ _ ⟨arcX_nonneg hR.le s, arcX_le hR.le s⟩)
  have hpow : ContDiffAt ℝ ∞ (fun z : ℂ => z ^ N) z₀ := (contDiff_id.pow N).contDiffAt
  have hcomp := hcd.comp z₀ hpow
  have := (contDiffAt_const (c := -(1 / ((N : ℝ) * Real.pi)))).mul hcomp
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  rw [arcsinePotential_eq_integral hN hR z, intervalIntegral.integral_of_le Real.pi_pos.le]
  rfl


end C5
end RestrictedPolynomials
