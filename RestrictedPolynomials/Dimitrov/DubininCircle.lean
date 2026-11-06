module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import RestrictedPolynomials.Dimitrov.Fekete
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic

/-!
# Circle potentials of Fekete points

Supplement C, Proposition 3.1, Steps 1 and 4.

For `m` points `zs` and a radius `δ > 0`, the potential of the `m` circles is
`U(z) = -(1/m) ∑ log max(‖z - zs a‖, δ)`.  We prove that `U` is Lipschitz, that it is differentiable
off the circles with the explicit gradient, the two-sided bounds on `U` away from and near the points,
and the bound on the average of the circle averages of `U` at a Fekete tuple:
`(1/m) ∑ circleAverage U (zs a) δ ≤ (1/m) log (1/δ) - ((m-1)/m) log d_m(K)`.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace RestrictedPolynomials

/-! ### Lipschitz continuity -/

/-- One-sided bound for the logarithm on `[δ, ∞)`. -/
private lemma log_sub_log_le_of_le {δ p q : ℝ} (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ q) :
    Real.log p - Real.log q ≤ |p - q| / δ := by
  have hp0 : 0 < p := hδ.trans_le hp
  have hq0 : 0 < q := hδ.trans_le hq
  have h1 : Real.log p - Real.log q = Real.log (p / q) := (Real.log_div hp0.ne' hq0.ne').symm
  have h2 : Real.log (p / q) ≤ p / q - 1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have h3 : p / q - 1 = (p - q) / q := by field_simp
  have h4 : (p - q) / q ≤ |p - q| / δ := by
    calc (p - q) / q ≤ |p - q| / q := div_le_div_of_nonneg_right (le_abs_self _) hq0.le
      _ ≤ |p - q| / δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ hq
  linarith

private lemma abs_log_max_sub_le {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |Real.log (max x δ) - Real.log (max y δ)| ≤ |x - y| / δ := by
  have hx : δ ≤ max x δ := le_max_right _ _
  have hy : δ ≤ max y δ := le_max_right _ _
  have hm : |max x δ - max y δ| ≤ |x - y| := abs_max_sub_max_le_abs x y δ
  have hm' : |max x δ - max y δ| / δ ≤ |x - y| / δ := div_le_div_of_nonneg_right hm hδ.le
  rw [abs_le]
  have h1 := log_sub_log_le_of_le hδ hx hy
  have h2 := log_sub_log_le_of_le hδ hy hx
  rw [abs_sub_comm (max y δ)] at h2
  constructor <;> linarith [neg_le_neg h2]

/-- Each term `z ↦ log max(‖z - c‖, δ)` is `1/δ`-Lipschitz. -/
private lemma abs_log_max_norm_sub_le {δ : ℝ} (hδ : 0 < δ) (c z w : ℂ) :
    |Real.log (max ‖z - c‖ δ) - Real.log (max ‖w - c‖ δ)| ≤ ‖z - w‖ / δ := by
  refine (abs_log_max_sub_le hδ _ _).trans ?_
  refine div_le_div_of_nonneg_right ?_ hδ.le
  calc |‖z - c‖ - ‖w - c‖| ≤ ‖(z - c) - (w - c)‖ := abs_norm_sub_norm_le _ _
    _ = ‖z - w‖ := by rw [sub_sub_sub_cancel_right]

/-- [Supplement C, Prop. 3.1, Step 1] The circle potential is Lipschitz. -/
theorem lipschitz_circlePotential (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (zs : Fin m → ℂ) :
    ∃ K : NNReal, LipschitzWith K (circlePotential m δ zs) := by
  refine ⟨Real.toNNReal ((m : ℝ) / δ), LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have hK : ((Real.toNNReal ((m : ℝ) / δ) : NNReal) : ℝ) = (m : ℝ) / δ :=
    Real.coe_toNNReal _ (by positivity)
  rw [hK, Real.dist_eq, dist_eq_norm]
  have hsum : |∑ a, (Real.log (max ‖z - zs a‖ δ) - Real.log (max ‖w - zs a‖ δ))| ≤
      (m : ℝ) * (‖z - w‖ / δ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a, |Real.log (max ‖z - zs a‖ δ) - Real.log (max ‖w - zs a‖ δ)|
        ≤ ∑ _a : Fin m, ‖z - w‖ / δ :=
          Finset.sum_le_sum fun a _ => abs_log_max_norm_sub_le hδ _ _ _
      _ = (m : ℝ) * (‖z - w‖ / δ) := by simp
  have hcoef : |1 / (m : ℝ)| ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [abs_of_nonneg (by positivity)]
      rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast h
  have heq : circlePotential m δ zs z - circlePotential m δ zs w =
      -(1 / (m : ℝ)) * ∑ a, (Real.log (max ‖z - zs a‖ δ) - Real.log (max ‖w - zs a‖ δ)) := by
    unfold circlePotential
    rw [Finset.sum_sub_distrib]; ring
  rw [heq, abs_mul, abs_neg]
  calc |1 / (m : ℝ)| * |∑ a, (Real.log (max ‖z - zs a‖ δ) - Real.log (max ‖w - zs a‖ δ))|
      ≤ 1 * ((m : ℝ) * (‖z - w‖ / δ)) :=
        mul_le_mul hcoef hsum (abs_nonneg _) zero_le_one
    _ = (m : ℝ) / δ * ‖z - w‖ := by ring

/-! ### The gradient -/

/-- The derivative of a single term away from the circle. -/
private lemma hasFDerivAt_log_max_norm_sub {δ : ℝ} (hδ : 0 < δ) (c z : ℂ) (hz : ‖z - c‖ ≠ δ) :
    HasFDerivAt (fun y : ℂ => Real.log (max ‖y - c‖ δ))
      (if δ < ‖z - c‖ then (‖z - c‖ ^ 2)⁻¹ • innerSL ℝ (z - c) else 0) z := by
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · -- inside: locally constant
    have hev : ∀ᶠ y in nhds z, ‖y - c‖ < δ :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.eventually_lt
        continuousAt_const hlt
    have hconst : (fun y : ℂ => Real.log (max ‖y - c‖ δ)) =ᶠ[nhds z] fun _ => Real.log δ :=
      hev.mono fun y hy => by simp [max_eq_right hy.le]
    simp only [show ¬ δ < ‖z - c‖ from not_lt.mpr hlt.le, ite_false]
    exact (hasFDerivAt_const (Real.log δ) z).congr_of_eventuallyEq hconst
  · -- outside: log of the norm
    have hev : ∀ᶠ y in nhds z, δ < ‖y - c‖ :=
      continuousAt_const.eventually_lt
        (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt hgt
    have hpos : 0 < ‖z - c‖ := hδ.trans hgt
    have hn : HasFDerivAt (fun y : ℂ => ‖y - c‖ ^ 2) (2 • innerSL ℝ (z - c)) z := by
      have := (hasStrictFDerivAt_norm_sq (z - c)).hasFDerivAt
      have h2 : HasFDerivAt (fun y : ℂ => y - c) (ContinuousLinearMap.id ℝ ℂ) z :=
        (hasFDerivAt_id z).sub_const c
      have h3 := this.comp z h2
      rw [ContinuousLinearMap.comp_id] at h3
      exact h3
    have hl : HasFDerivAt (fun y : ℂ => Real.log (‖y - c‖ ^ 2))
        ((‖z - c‖ ^ 2)⁻¹ • (2 • innerSL ℝ (z - c))) z :=
      hn.log (by positivity)
    have hl2 := hl.const_mul (1 / 2 : ℝ)
    have hconst : (fun y : ℂ => Real.log (max ‖y - c‖ δ)) =ᶠ[nhds z]
        fun y => (1 / 2 : ℝ) * Real.log (‖y - c‖ ^ 2) := by
      filter_upwards [hev] with y hy
      rw [max_eq_left hy.le, Real.log_pow]
      push_cast; ring
    simp only [hgt, ite_true]
    refine (hl2.congr_of_eventuallyEq hconst).congr_fderiv ?_
    ext w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul, nsmul_eq_mul]
    ring

/-- [Supplement C, Prop. 3.1, Step 1] The explicit gradient of the circle potential off the
circles. -/
theorem hasGradient_circlePotential (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (zs : Fin m → ℂ) {z : ℂ}
    (hz : ∀ a, ‖z - zs a‖ ≠ δ) :
    DifferentiableAt ℝ (circlePotential m δ zs) z ∧ ∀ w : ℂ,
      fderiv ℝ (circlePotential m δ zs) z w =
        -(1 / (m : ℝ)) * ∑ a, if δ < ‖z - zs a‖ then
          inner ℝ (z - zs a) w / ‖z - zs a‖ ^ 2 else 0 := by
  have hsum : HasFDerivAt (fun y : ℂ => ∑ a, Real.log (max ‖y - zs a‖ δ))
      (∑ a, (if δ < ‖z - zs a‖ then (‖z - zs a‖ ^ 2)⁻¹ • innerSL ℝ (z - zs a) else 0)) z :=
    HasFDerivAt.fun_sum fun a _ => hasFDerivAt_log_max_norm_sub hδ (zs a) z (hz a)
  have hU : HasFDerivAt (circlePotential m δ zs)
      (-(1 / (m : ℝ)) • ∑ a, (if δ < ‖z - zs a‖ then (‖z - zs a‖ ^ 2)⁻¹ • innerSL ℝ (z - zs a)
        else 0)) z := by
    have := hsum.const_smul (-(1 / (m : ℝ)))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [circlePotential]
  refine ⟨hU.differentiableAt, fun w => ?_⟩
  rw [hU.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, inv_mul_eq_div]
  · simp

/-! ### Bounds for the potential -/

/-- [Supplement C, Prop. 3.1, Step 1] Upper bound away from the points. -/
theorem circlePotential_le {m : ℕ} (hm : 1 ≤ m) {δ R : ℝ} (hδ : 0 < δ) {zs : Fin m → ℂ}
    (hzs : ∀ a, ‖zs a‖ ≤ R) {z : ℂ} (hz : R < ‖z‖) :
    circlePotential m δ zs z ≤ -Real.log (‖z‖ - R) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ a, -Real.log (max ‖z - zs a‖ δ) ≤ -Real.log (‖z‖ - R) := by
    intro a
    have h1 : ‖z‖ - R ≤ ‖z - zs a‖ := by
      have := norm_sub_norm_le z (zs a) |>.trans_eq' rfl
      have h2 : ‖z‖ - ‖zs a‖ ≤ ‖z - zs a‖ := norm_sub_norm_le z (zs a)
      linarith [hzs a]
    have h0 : 0 < ‖z‖ - R := by linarith
    have h3 : ‖z‖ - R ≤ max ‖z - zs a‖ δ := h1.trans (le_max_left _ _)
    have := Real.log_le_log h0 h3
    linarith
  unfold circlePotential
  have : ∑ a, Real.log (max ‖z - zs a‖ δ) ≥ ∑ _a : Fin m, Real.log (‖z‖ - R) := by
    refine Finset.sum_le_sum fun a _ => ?_
    have := hterm a; linarith
  have hsum : ∑ _a : Fin m, Real.log (‖z‖ - R) = (m : ℝ) * Real.log (‖z‖ - R) := by simp
  have : -(1 / (m : ℝ)) * ∑ a, Real.log (max ‖z - zs a‖ δ) ≤
      -(1 / (m : ℝ)) * ((m : ℝ) * Real.log (‖z‖ - R)) := by
    apply mul_le_mul_of_nonpos_left (by linarith) (by
      have : 0 ≤ 1 / (m : ℝ) := by positivity
      linarith)
  calc _ ≤ _ := this
    _ = -Real.log (‖z‖ - R) := by field_simp

/-- [Supplement C, Prop. 3.1, Step 1] Lower bound near the points. -/
theorem circlePotential_ge {m : ℕ} (hm : 1 ≤ m) {δ R r' : ℝ} (hδ : 0 < δ) {zs : Fin m → ℂ}
    (hzs : ∀ a, ‖zs a‖ ≤ R) {z : ℂ} (hz : ‖z‖ < r') :
    -Real.log (r' + R + δ) ≤ circlePotential m δ zs z := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hR0 : 0 ≤ R := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact (norm_nonneg _).trans (hzs (Classical.arbitrary _))
  have hr0 : 0 < r' := (norm_nonneg z).trans_lt hz
  have hterm : ∀ a, Real.log (max ‖z - zs a‖ δ) ≤ Real.log (r' + R + δ) := by
    intro a
    have h1 : ‖z - zs a‖ ≤ r' + R + δ := by
      have := norm_sub_le z (zs a)
      linarith [hzs a]
    have h2 : max ‖z - zs a‖ δ ≤ r' + R + δ := max_le h1 (by linarith)
    exact Real.log_le_log (lt_max_of_lt_right hδ) h2
  unfold circlePotential
  have hs : ∑ a, Real.log (max ‖z - zs a‖ δ) ≤ (m : ℝ) * Real.log (r' + R + δ) := by
    calc _ ≤ ∑ _a : Fin m, Real.log (r' + R + δ) := Finset.sum_le_sum fun a _ => hterm a
      _ = _ := by simp
  have h1 : 0 ≤ 1 / (m : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hs h1
  have h2 : 1 / (m : ℝ) * ((m : ℝ) * Real.log (r' + R + δ)) = Real.log (r' + R + δ) := by
    field_simp
  rw [neg_mul, ← neg_le_neg_iff, neg_neg]
  linarith

/-! ### The circle averages at a Fekete tuple -/

/-- A single term `log max(‖· - c‖, δ)` is continuous. -/
private lemma continuous_log_max_norm_sub {δ : ℝ} (hδ : 0 < δ) (c : ℂ) :
    Continuous fun z : ℂ => Real.log (max ‖z - c‖ δ) :=
  Continuous.log (by fun_prop) fun z => (lt_max_of_lt_right hδ).ne'

private lemma circleIntegrable_log_max_norm_sub {δ : ℝ} (hδ : 0 < δ) (c c' : ℂ) (r : ℝ) :
    CircleIntegrable (fun z : ℂ => Real.log (max ‖z - c‖ δ)) c' r :=
  ContinuousOn.circleIntegrable' (continuous_log_max_norm_sub hδ c).continuousOn

/-- Each circle average of the `b`-th term is bounded below by `log ‖c' - c‖` (for `c' ≠ c`). -/
private lemma log_norm_le_circleAverage_log_max {δ : ℝ} (hδ : 0 < δ) {c c' : ℂ} (hne : c' ≠ c) :
    Real.log ‖c' - c‖ ≤ Real.circleAverage (fun z : ℂ => Real.log (max ‖z - c‖ δ)) c' δ := by
  set g : ℂ → ℝ := fun z => Real.log ‖z - c‖ with hg
  set h : ℂ → ℝ := fun z => Real.log (max ‖z - c‖ δ) with hh
  set g' : ℂ → ℝ := fun z => min (g z) (h z) with hg'
  have hcod : g =ᶠ[Filter.codiscreteWithin (sphere c' |δ|)] g' :=
    Filter.mem_of_superset (compl_singleton_mem_codiscreteWithin c) fun z hz => by
      have hz' : z ≠ c := hz
      have hpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz')
      have : g z ≤ h z := Real.log_le_log hpos (le_max_left _ _)
      show g z = g' z
      simp [hg', min_eq_left this]
  have hgint : CircleIntegrable g c' δ := circleIntegrable_log_norm_sub_const δ
  have hg'int : CircleIntegrable g' c' δ := hgint.congr_codiscreteWithin hcod
  have hmono : Real.circleAverage g' c' δ ≤ Real.circleAverage h c' δ :=
    Real.circleAverage_mono hg'int (circleIntegrable_log_max_norm_sub hδ c c' δ)
      fun x _ => min_le_right _ _
  rw [← Real.circleAverage_congr_codiscreteWithin hcod hδ.ne'] at hmono
  refine le_trans ?_ hmono
  rw [hg, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hδ.ne']
  have hpos : 0 < ‖c' - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h1 : Real.log (δ⁻¹ * ‖c' - c‖) ≤ Real.posLog (δ⁻¹ * ‖c' - c‖) := le_max_right _ _
  have h2 : Real.log (δ⁻¹ * ‖c' - c‖) = Real.log ‖c' - c‖ - Real.log δ := by
    rw [Real.log_mul (inv_pos.mpr hδ).ne' hpos.ne', Real.log_inv]; ring
  linarith

/-- The circle average of the term `a` over its own circle is `log δ`. -/
private lemma circleAverage_log_max_self {δ : ℝ} (hδ : 0 < δ) (c : ℂ) :
    Real.circleAverage (fun z : ℂ => Real.log (max ‖z - c‖ δ)) c δ = Real.log δ := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  have : ‖x - c‖ = δ := by
    rw [mem_sphere, dist_eq_norm, abs_of_pos hδ] at hx; exact hx
  simp [this]

/-- The off-diagonal logarithm sum is twice the logarithm of the Vandermonde norm. -/
private lemma sum_offDiag_log_norm {m : ℕ} (zs : Fin m → ℂ) (hpos : 0 < vandermondeNorm zs) :
    ∑ a, ∑ b, (if a = b then (0 : ℝ) else Real.log ‖zs a - zs b‖) =
      2 * Real.log (vandermondeNorm zs) := by
  set P : Finset (Fin m × Fin m) :=
    (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2) with hP
  have hne : ∀ p ∈ P, ‖zs p.1 - zs p.2‖ ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (show ∏ p ∈ P, ‖zs p.1 - zs p.2‖ ≠ 0 from hpos.ne')
  have hlog : Real.log (vandermondeNorm zs) = ∑ p ∈ P, Real.log ‖zs p.1 - zs p.2‖ :=
    Real.log_prod hne
  set L : Fin m → Fin m → ℝ := fun a b => Real.log ‖zs a - zs b‖ with hL
  have hsymm : ∀ a b, L a b = L b a := fun a b => by simp only [hL, norm_sub_rev]
  have h1 : ∑ a, ∑ b, (if a = b then (0 : ℝ) else L a b) =
      ∑ p : Fin m × Fin m, (if p.1 = p.2 then (0 : ℝ) else L p.1 p.2) :=
    (Fintype.sum_prod_type' (fun a b => if a = b then (0 : ℝ) else L a b)).symm
  have h2 : ∀ p : Fin m × Fin m, (if p.1 = p.2 then (0 : ℝ) else L p.1 p.2) =
      (if p.1 < p.2 then L p.1 p.2 else 0) + (if p.2 < p.1 then L p.2 p.1 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h, zero_add, hsymm p.1 p.2]
  rw [h1, Finset.sum_congr rfl fun p _ => h2 p, Finset.sum_add_distrib]
  have h3 : ∑ p : Fin m × Fin m, (if p.2 < p.1 then L p.2 p.1 else 0) =
      ∑ p : Fin m × Fin m, (if p.1 < p.2 then L p.1 p.2 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      congr
  rw [h3, ← two_mul, ← Finset.sum_filter, hlog]

/-- [Supplement C, Prop. 3.1, Step 4] The average over the circles of the circle averages of `U`
at a Fekete tuple. -/
theorem circleAverage_circlePotential_le {K : Set ℂ} {m : ℕ} (hm : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    {zs : Fin m → ℂ} (hmem : ∀ a, zs a ∈ K) (hmax : vandermondeNorm zs = feketeDelta m K)
    (hpos : 0 < vandermondeNorm zs) :
    (1 / (m : ℝ)) * ∑ a, Real.circleAverage (circlePotential m δ zs) (zs a) δ ≤
      (1 / (m : ℝ)) * Real.log (1 / δ) - (((m : ℝ) - 1) / m) * Real.log (feketeDiam m K) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  -- distinctness of the points
  have hdist : ∀ a b : Fin m, a ≠ b → zs a ≠ zs b := by
    intro a b hab heq
    have hne : ∀ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2),
        ‖zs p.1 - zs p.2‖ ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (show vandermondeNorm zs ≠ 0 from hpos.ne')
    rcases lt_or_gt_of_ne hab with h | h
    · exact hne (a, b) (by simp [h]) (by simp [heq])
    · exact hne (b, a) (by simp [h]) (by simp [heq])
  -- the diagonal/off-diagonal lower bound for the circle averages of the terms
  set c : Fin m → Fin m → ℝ := fun a b =>
    (if a = b then Real.log δ else 0) + (if a = b then (0 : ℝ) else Real.log ‖zs a - zs b‖)
    with hc
  have hT : ∀ a b, c a b ≤
      Real.circleAverage (fun z : ℂ => Real.log (max ‖z - zs b‖ δ)) (zs a) δ := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp [hc, circleAverage_log_max_self hδ]
    · simp only [hc, if_neg hab, zero_add]
      exact log_norm_le_circleAverage_log_max hδ (hdist a b hab)
  -- circle average of `U` at `zs a`
  have hU : ∀ a, Real.circleAverage (circlePotential m δ zs) (zs a) δ =
      -(1 / (m : ℝ)) * ∑ b, Real.circleAverage (fun z : ℂ => Real.log (max ‖z - zs b‖ δ)) (zs a) δ := by
    intro a
    have : circlePotential m δ zs =
        fun z => (-(1 / (m : ℝ))) • ∑ b, Real.log (max ‖z - zs b‖ δ) := by
      funext z; simp [circlePotential]
    rw [this, Real.circleAverage_fun_smul, smul_eq_mul,
      Real.circleAverage_fun_sum fun b _ => circleIntegrable_log_max_norm_sub hδ (zs b) (zs a) δ]
  have hbound : ∀ a, Real.circleAverage (circlePotential m δ zs) (zs a) δ ≤
      -(1 / (m : ℝ)) * ∑ b, c a b := by
    intro a
    rw [hU a]
    have h1 : 0 ≤ 1 / (m : ℝ) := by positivity
    have : ∑ b, c a b ≤ ∑ b, Real.circleAverage
        (fun z : ℂ => Real.log (max ‖z - zs b‖ δ)) (zs a) δ :=
      Finset.sum_le_sum fun b _ => hT a b
    nlinarith
  -- the sum of the constants
  have hsumc : ∑ a, ∑ b, c a b = (m : ℝ) * Real.log δ + 2 * Real.log (vandermondeNorm zs) := by
    simp only [hc, Finset.sum_add_distrib]
    rw [sum_offDiag_log_norm zs hpos]
    simp
  -- the Fekete diameter
  have hdiam : Real.log (feketeDiam m K) =
      (2 / ((m : ℝ) * ((m : ℝ) - 1))) * Real.log (vandermondeNorm zs) := by
    unfold feketeDiam
    rw [← hmax, Real.log_rpow hpos]
  have h1 : 0 ≤ 1 / (m : ℝ) := by positivity
  calc (1 / (m : ℝ)) * ∑ a, Real.circleAverage (circlePotential m δ zs) (zs a) δ
      ≤ (1 / (m : ℝ)) * ∑ a, (-(1 / (m : ℝ)) * ∑ b, c a b) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hbound a) h1
    _ = (1 / (m : ℝ)) * Real.log (1 / δ) - (((m : ℝ) - 1) / m) * Real.log (feketeDiam m K) := by
        rw [← Finset.mul_sum, hsumc, hdiam, one_div δ, Real.log_inv]
        have : (m : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring

end RestrictedPolynomials
