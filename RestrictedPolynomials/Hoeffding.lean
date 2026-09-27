import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding's lemma for a Bernoulli random variable

The real inequality `(1 - q) e^{tq} + q e^{t(q-1)} ≤ e^{t²/8}` for `q ∈ [0, 1]`, obtained from
Mathlib's Hoeffding lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) applied to the
two-point measure `(1 - q) δ₀ + q δ₁`.
-/

open MeasureTheory ProbabilityTheory

namespace RestrictedPolynomials

lemma integral_twoPoint {c₀ c₁ : ℝ} (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) (f : ℝ → ℝ) :
    ∫ ω, f ω ∂(ENNReal.ofReal c₀ • Measure.dirac 0 + ENNReal.ofReal c₁ • Measure.dirac 1) =
      c₀ * f 0 + c₁ * f 1 := by
  have hi0 : Integrable f (ENNReal.ofReal c₀ • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hi1 : Integrable f (ENNReal.ofReal c₁ • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure hi0 hi1, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h₀, ENNReal.toReal_ofReal h₁]
  simp [smul_eq_mul]

/-- **Hoeffding's lemma** for a Bernoulli variable. -/
lemma hoeffding_bernoulli {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℝ) :
    (1 - q) * Real.exp (t * q) + q * Real.exp (t * (q - 1)) ≤ Real.exp (t ^ 2 / 8) := by
  set μ : Measure ℝ :=
    ENNReal.ofReal (1 - q) • Measure.dirac 0 + ENNReal.ofReal q • Measure.dirac 1 with hμ
  have : IsProbabilityMeasure μ := ⟨by
    simp only [hμ, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hq0]
    simp⟩
  have hb : ∀ᵐ ω ∂μ, (id ω : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hμ, ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq]
      simp
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq]
      simp
  have hsub := hasSubgaussianMGF_of_mem_Icc (X := id) (μ := μ) aemeasurable_id hb
  have hmean : μ[id] = q := by
    rw [hμ, integral_twoPoint (by linarith) hq0]
    simp
  have hmgf := hsub.mgf_le (-t)
  rw [hmean] at hmgf
  unfold mgf at hmgf
  rw [hμ, integral_twoPoint (by linarith) hq0] at hmgf
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : ℝ) := by
    simp only [sub_zero, nnnorm_one]
    push_cast
    norm_num
  rw [hc] at hmgf
  convert hmgf using 2
  · simp only [id, zero_sub]
    ring_nf
  · simp only [id]
    ring_nf
  · ring_nf

end RestrictedPolynomials
