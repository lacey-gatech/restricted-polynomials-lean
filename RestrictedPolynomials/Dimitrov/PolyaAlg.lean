module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Basic
public import RestrictedPolynomials.Dimitrov.Kronecker

/-!
# Algebraic part of the Pólya bound

Source: Supplement B, §3, Lemmas `lem:abel`,
`lem:laurent` and `lem:basis`.

* `circleIntegral_mul_pow_eq_coeff`: Laurent coefficients at `∞` as circle integrals
  (Abel step plus termwise integration).
* `det_linearFunctional_monic_basis`: the change of basis `(L (pᵢ pⱼ)) = U M Uᵀ` with `U`
  unitriangular, so `det (L (pᵢ pⱼ)) = det (a_{i+j+1})`.
-/

@[expose] public section

open Polynomial
open scoped Matrix

noncomputable section

namespace RestrictedPolynomials

/-- Abel step [B, Lemma lem:abel]: the series converges absolutely at every larger radius. -/
theorem summable_norm_mul_inv_pow_of_hasSum (a : ℕ → ℂ) (F : ℂ → ℂ) {ρ₀ R₀ : ℝ} (hρ : 0 ≤ ρ₀)
    (hR : ρ₀ < R₀)
    (hF : ∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => a k * z⁻¹ ^ k) (F z)) :
    Summable (fun k : ℕ => ‖a k‖ * (R₀⁻¹) ^ k) := by
  obtain ⟨R₁, h1, h2⟩ := exists_between hR
  have hR₁ : 0 < R₁ := lt_of_le_of_lt hρ h1
  have hR₀ : 0 < R₀ := hR₁.trans h2
  have hs := hF (R₁ : ℂ) (by simpa [abs_of_pos hR₁] using h1)
  have ht := hs.summable.tendsto_atTop_zero.norm
  rw [norm_zero] at ht
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  have hb : ∀ k : ℕ, ‖a k‖ * (R₀⁻¹) ^ k ≤ M * (R₁ / R₀) ^ k := by
    intro k
    have hk : ‖a k * (R₁ : ℂ)⁻¹ ^ k‖ ≤ M := hM ⟨k, rfl⟩
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR₁.le] at hk
    calc ‖a k‖ * (R₀⁻¹) ^ k = (‖a k‖ * R₁⁻¹ ^ k) * (R₁ / R₀) ^ k := by
          rw [div_eq_mul_inv, mul_pow, inv_pow R₁]
          field_simp
      _ ≤ M * (R₁ / R₀) ^ k := by gcongr
  refine Summable.of_nonneg_of_le (fun k => by positivity) hb ?_
  exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one hR₀).2 h2)).mul_left M

/-- The circle integral of `z ^ (n - k)` over `|z| = R₀`: `2πi` iff `k = n + 1`. -/
theorem circleIntegral_zpow_sub (R₀ : ℝ) (hR₀ : 0 < R₀) (n k : ℕ) :
    (∮ z in C(0, R₀), (z⁻¹ ^ k * z ^ n)) =
      if k = n + 1 then 2 * Real.pi * Complex.I else 0 := by
  have hcongr : (∮ z in C(0, R₀), (z⁻¹ ^ k * z ^ n)) =
      ∮ z in C(0, R₀), (z - 0) ^ ((n : ℤ) - k) := by
    apply circleIntegral.integral_congr hR₀.le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
      linarith
    simp only [sub_zero]
    rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow, mul_comm]
  rw [hcongr]
  split_ifs with h
  · have : ((n : ℤ) - k) = -1 := by omega
    rw [this]
    have hm : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R₀ := by simpa using hR₀
    simpa using circleIntegral.integral_sub_inv_of_mem_ball hm
  · exact circleIntegral.integral_sub_zpow_of_ne (by omega) 0 0 R₀

/-- [B, Lemmas lem:abel and lem:laurent] Laurent coefficients at ∞ as circle integrals:
`(2πi)⁻¹ ∮_{|z|=R₀} F(z) z^n dz = a_{n+1}`. -/
theorem circleIntegral_mul_pow_eq_coeff (a : ℕ → ℂ) (F : ℂ → ℂ) {ρ₀ R₀ : ℝ} (hρ : 0 ≤ ρ₀)
    (hR : ρ₀ < R₀) (hF : ∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => a k * z⁻¹ ^ k) (F z)) (n : ℕ) :
    (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(0, R₀), F z * z ^ n) = a (n + 1) := by
  have hR₀ : 0 < R₀ := lt_of_le_of_lt hρ hR
  have hab := summable_norm_mul_inv_pow_of_hasSum a F hρ hR hF
  set Φ : ℕ → ℝ → ℂ := fun k θ =>
    deriv (circleMap 0 R₀) θ • (a k * (circleMap 0 R₀ θ)⁻¹ ^ k * (circleMap 0 R₀ θ) ^ n) with hΦ
  have hz : ∀ θ : ℝ, ‖circleMap 0 R₀ θ‖ = R₀ := fun θ => by
    simp [abs_of_pos hR₀]
  have hmeas : Measurable (circleMap 0 R₀) := (continuous_circleMap 0 R₀).measurable
  have hlim := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := 2 * Real.pi) (μ := MeasureTheory.volume)
    (F := Φ) (f := fun θ => deriv (circleMap 0 R₀) θ • (F (circleMap 0 R₀ θ) *
      (circleMap 0 R₀ θ) ^ n))
    (fun k _ => R₀ ^ (n + 1) * (‖a k‖ * (R₀⁻¹) ^ k))
    (fun k => by
      apply Measurable.aestronglyMeasurable
      simp only [hΦ, deriv_circleMap]
      fun_prop)
    (fun k => Filter.Eventually.of_forall fun θ _ => by
      simp only [hΦ, norm_smul, norm_mul, norm_pow, norm_inv, deriv_circleMap, hz,
        Complex.norm_I]
      apply le_of_eq
      ring)
    (Filter.Eventually.of_forall fun θ _ => hab.mul_left _)
    (by simp)
    (Filter.Eventually.of_forall fun θ _ => by
      have := ((hF (circleMap 0 R₀ θ) (by rw [hz]; exact hR)).mul_right
        ((circleMap 0 R₀ θ) ^ n)).const_smul (deriv (circleMap 0 R₀) θ)
      exact this)
  have hterm : ∀ k, (∫ θ in (0 : ℝ)..2 * Real.pi, Φ k θ) =
      if k = n + 1 then a (n + 1) * (2 * Real.pi * Complex.I) else 0 := by
    intro k
    have h1 : (∫ θ in (0 : ℝ)..2 * Real.pi, Φ k θ) =
        ∮ z in C(0, R₀), a k * (z⁻¹ ^ k * z ^ n) := by
      simp only [circleIntegral, hΦ, mul_assoc]
    rw [h1, circleIntegral.integral_const_mul, circleIntegral_zpow_sub R₀ hR₀]
    split_ifs with h
    · rw [h]
    · simp
  have hsum : HasSum (fun k => ∫ θ in (0 : ℝ)..2 * Real.pi, Φ k θ)
      (a (n + 1) * (2 * Real.pi * Complex.I)) := by
    have : (fun k => ∫ θ in (0 : ℝ)..2 * Real.pi, Φ k θ) =
        fun k => if k = n + 1 then a (n + 1) * (2 * Real.pi * Complex.I) else 0 := _root_.funext hterm
    rw [this]
    simpa using hasSum_ite_eq (n + 1) (a (n + 1) * (2 * Real.pi * Complex.I))
  have hI := hsum.unique hlim
  have hne : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (∮ z in C(0, R₀), F z * z ^ n) = a (n + 1) * (2 * Real.pi * Complex.I) := by
    rw [hI]; rfl
  rw [this]
  field_simp

/-- Expansion of `L (p * q)` for polynomials of degree `≤ N`. -/
theorem linearFunctional_mul_eq_sum (L : ℂ[X] →ₗ[ℂ] ℂ) (a : ℕ → ℂ)
    (hL : ∀ n, L (X ^ n) = a (n + 1)) (N : ℕ) (p q : ℂ[X]) (hp : p.natDegree ≤ N)
    (hq : q.natDegree ≤ N) :
    L (p * q) = ∑ k : Fin (N + 1), ∑ l : Fin (N + 1),
      p.coeff k * a ((k : ℕ) + l + 1) * q.coeff l := by
  conv_lhs => rw [p.as_sum_range' (N + 1) (by omega), q.as_sum_range' (N + 1) (by omega)]
  rw [Finset.sum_mul_sum, map_sum]
  simp only [map_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [monomial_mul_monomial, ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul,
    LinearMap.map_smul, hL, smul_eq_mul]
  ring

/-- [B, Lemma lem:basis] change of basis: for a linear functional `L` with `L(X^n) = a_{n+1}` and monic
`p_i` of degree `i`, `det(L(p_i p_j)) = det(a_{i+j+1})`. -/
theorem det_linearFunctional_monic_basis (L : ℂ[X] →ₗ[ℂ] ℂ) (a : ℕ → ℂ)
    (hL : ∀ n, L (X ^ n) = a (n + 1)) (N : ℕ) (p : Fin (N + 1) → ℂ[X])
    (hp : ∀ i, (p i).Monic ∧ (p i).natDegree = i) :
    Matrix.det (Matrix.of fun i j => L (p i * p j)) = hankelDet a 1 (N + 1) := by
  set U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.of fun i k => (p i).coeff k with hU
  set M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
    Matrix.of fun k l => a ((k : ℕ) + l + 1) with hM
  have hfac : (Matrix.of fun i j => L (p i * p j)) = U * M * Uᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hU, hM]
    rw [linearFunctional_mul_eq_sum L a hL N _ _ (by rw [(hp i).2]; exact Nat.lt_succ_iff.1 i.2)
      (by rw [(hp j).2]; exact Nat.lt_succ_iff.1 j.2)]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp only [hU, Matrix.of_apply]
      have := (hp i).1.coeff_natDegree
      rwa [(hp i).2] at this
    · intro i k hik
      simp only [hU, Matrix.of_apply]
      exact coeff_eq_zero_of_natDegree_lt (by rw [(hp i).2]; exact hik)
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUdet]
  simp [hankelDet, hM]

end RestrictedPolynomials
