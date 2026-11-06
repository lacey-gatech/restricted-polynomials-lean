module

public import RestrictedPolynomials.Dimitrov.Graeffe
public import RestrictedPolynomials.Dimitrov.SqrtSeries
public import RestrictedPolynomials.Dimitrov.Radical
public import RestrictedPolynomials.Dimitrov.CaseAAlg
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Binomial

/-!
# Case A: analytic continuation of `√(P₂* P₄*)(1/z)` off the hedgehog

Source: Supplement A, §3 (Lemma `lem:f`) and §5 (Lemmas
`lem:holo`, `lem:S2`, `lem:evmul`, `lem:onefactor`, `lem:uniq` and Theorem `thm:S5`).

* `caseA_S5`: the function `F(z) = ∏_{v ∈ V} exp (½ Log (1 - v/z))` is holomorphic off the hedgehog
  `⋃ [0, v]`, satisfies `F² = ∏ (1 - v/z)` there, and has the absolutely convergent expansion
  `∑ f_k z⁻ᵏ` for `|z| > max |v|`, where `f` is an integer square root series.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-! ### Holomorphy (Lemma `lem:holo`) -/

/-- For `z` off the segment `[0, v]`: `z ≠ 0` and `1 - v/z` lies in the slit plane. -/
lemma slit_of_not_mem_segment {v z : ℂ} (hz : z ∉ segment ℝ (0 : ℂ) v) :
    z ≠ 0 ∧ (1 - v / z) ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz (left_mem_segment ℝ _ _)
  refine ⟨hz0, ?_⟩
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  apply hz
  -- `v / z = r` is real and `≥ 1`
  have hre' : 1 ≤ (v / z).re := by
    have : (1 - v / z).re = 1 - (v / z).re := by simp
    linarith
  have him' : (v / z).im = 0 := by
    have : (1 - v / z).im = -(v / z).im := by simp
    linarith
  set r : ℝ := (v / z).re with hr
  have hrpos : 0 < r := by linarith
  have hvz : v / z = (r : ℂ) := Complex.ext (by simp [hr]) (by simpa using him')
  have hzv : z = ((1 / r : ℝ) : ℂ) * v := by
    have hvz' : v = (r : ℂ) * z := by
      rw [← hvz]; field_simp
    rw [hvz']
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    push_cast
    field_simp
  rw [segment_eq_image']
  refine ⟨1 / r, ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hrpos]; exact hre'
  · rw [hzv]
    simp [Complex.real_smul]

/-- The `v`-factor `g_v(z) = exp (½ Log (1 - v/z))`. -/
def gFactor (v z : ℂ) : ℂ := Complex.exp ((1 / 2 : ℂ) * Complex.log (1 - v / z))

lemma gFactor_differentiableAt {v z : ℂ} (hz : z ∉ segment ℝ (0 : ℂ) v) :
    DifferentiableAt ℂ (gFactor v) z := by
  obtain ⟨hz0, hslit⟩ := slit_of_not_mem_segment hz
  unfold gFactor
  have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 - v / z) z :=
    (differentiableAt_const _).sub ((differentiableAt_const _).div differentiableAt_id hz0)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.log (1 - v / z)) z :=
    h1.clog hslit
  exact ((differentiableAt_const _).mul h2).cexp

lemma gFactor_sq {v z : ℂ} (hz : z ∉ segment ℝ (0 : ℂ) v) :
    gFactor v z ^ 2 = 1 - v / z := by
  obtain ⟨hz0, hslit⟩ := slit_of_not_mem_segment hz
  unfold gFactor
  rw [← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * ((1 / 2 : ℂ) * Complex.log (1 - v / z)) = Complex.log (1 - v / z) := by
    push_cast; ring
  rw [this, Complex.exp_log]
  exact Complex.slitPlane_ne_zero hslit

lemma multiset_prod_differentiableAt (V : Multiset ℂ) (g : ℂ → ℂ → ℂ) {z : ℂ}
    (h : ∀ v ∈ V, DifferentiableAt ℂ (g v) z) :
    DifferentiableAt ℂ (fun z => (V.map fun v => g v z).prod) z := by
  induction V using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a t)).mul
      (ih fun v hv => h v (Multiset.mem_cons_of_mem hv))

/-- The function `F` of the supplement. -/
def bigF (V : Multiset ℂ) (z : ℂ) : ℂ := (V.map fun v => gFactor v z).prod

lemma not_mem_hedgehog {V : Multiset ℂ} {z : ℂ}
    (hz : z ∉ ⋃ v ∈ V, segment ℝ (0 : ℂ) v) {v : ℂ} (hv : v ∈ V) :
    z ∉ segment ℝ (0 : ℂ) v := by
  intro h
  exact hz (Set.mem_biUnion hv h)

lemma bigF_differentiableOn (V : Multiset ℂ) :
    DifferentiableOn ℂ (bigF V) (⋃ v ∈ V, segment ℝ (0 : ℂ) v)ᶜ := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact multiset_prod_differentiableAt V gFactor
    fun v hv => gFactor_differentiableAt (not_mem_hedgehog hz hv)

lemma bigF_sq (V : Multiset ℂ) {z : ℂ} (hz : z ∉ ⋃ v ∈ V, segment ℝ (0 : ℂ) v) :
    bigF V z ^ 2 = (V.map fun v => 1 - v / z).prod := by
  unfold bigF
  rw [← Multiset.prod_map_pow]
  congr 1
  apply Multiset.map_congr rfl
  intro v hv
  exact gFactor_sq (not_mem_hedgehog hz hv)

/-! ### The binomial series (Lemma `lem:S2`) -/

/-- The series `S = ∑ binom(1/2, k) X^k`. -/
def halfSeries : PowerSeries ℂ := PowerSeries.mk fun k => Ring.choose (1 / 2 : ℂ) k

/-- `s_v = S(-v w)`. -/
def sSeries (v : ℂ) : PowerSeries ℂ := PowerSeries.rescale (-v) halfSeries

lemma halfSeries_sq : halfSeries ^ 2 = 1 + PowerSeries.X := by
  ext k
  rw [pow_two, PowerSeries.coeff_mul]
  simp only [halfSeries, PowerSeries.coeff_mk]
  rw [← Ring.add_choose_eq k (Commute.all _ _)]
  have : (1 / 2 : ℂ) + 1 / 2 = ((1 : ℕ) : ℂ) := by norm_num
  rw [this, Ring.choose_natCast]
  rcases k with _ | _ | k
  · simp
  · simp [PowerSeries.coeff_X]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp [PowerSeries.coeff_X, PowerSeries.coeff_one]

lemma sSeries_sq (v : ℂ) : sSeries v ^ 2 = 1 - PowerSeries.C v * PowerSeries.X := by
  unfold sSeries
  rw [← map_pow, halfSeries_sq, map_add, map_one, PowerSeries.rescale_X, map_neg]
  ring

lemma sSeries_coeff_zero (v : ℂ) : PowerSeries.constantCoeff (sSeries v) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [sSeries, halfSeries, PowerSeries.coeff_rescale]

/-! ### Evaluation of power series at a point (Lemma `lem:evmul`) -/

/-- `a` is `t`-summable with value `x`: `∑ ‖a_k t^k‖ < ∞` and `∑ a_k t^k = x`. -/
def AbsEval (a : PowerSeries ℂ) (t x : ℂ) : Prop :=
  Summable (fun k => ‖PowerSeries.coeff k a * t ^ k‖) ∧
    HasSum (fun k => PowerSeries.coeff k a * t ^ k) x

lemma AbsEval.mul {a b : PowerSeries ℂ} {t x y : ℂ} (ha : AbsEval a t x) (hb : AbsEval b t y) :
    AbsEval (a * b) t (x * y) := by
  have key : ∀ k, PowerSeries.coeff k (a * b) * t ^ k =
      ∑ kl ∈ Finset.antidiagonal k,
        (PowerSeries.coeff kl.1 a * t ^ kl.1) * (PowerSeries.coeff kl.2 b * t ^ kl.2) := by
    intro k
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp, pow_add]
    ring
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm ha.1 hb.1
  refine ⟨?_, ?_⟩
  · simpa only [key] using hsum
  · have h2 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha.1 hb.1
    have hs := hsum.of_norm.hasSum
    rw [← h2, ha.2.tsum_eq, hb.2.tsum_eq] at hs
    simpa only [key] using hs

lemma AbsEval.one (t : ℂ) : AbsEval 1 t 1 := by
  have h : (fun k => PowerSeries.coeff k (1 : PowerSeries ℂ) * t ^ k) =
      fun k => if k = 0 then (1 : ℂ) else 0 := by
    funext k
    rcases k with _ | k <;> simp [PowerSeries.coeff_one]
  refine ⟨?_, ?_⟩
  · have h' : ∀ k, PowerSeries.coeff k (1 : PowerSeries ℂ) * t ^ k = if k = 0 then (1 : ℂ) else 0 :=
      fun k => congrFun h k
    simp only [h']
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp at hk
    simp [hk]
  · rw [h]
    simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)

lemma AbsEval.multiset_prod {ι : Type*} (V : Multiset ι) (s : ι → PowerSeries ℂ) (g : ι → ℂ) {t : ℂ}
    (h : ∀ v ∈ V, AbsEval (s v) t (g v)) :
    AbsEval (V.map s).prod t (V.map g).prod := by
  induction V using Multiset.induction_on with
  | empty => simpa using AbsEval.one t
  | cons a V ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a V)).mul (ih fun v hv => h v (Multiset.mem_cons_of_mem hv))

/-! ### One factor (Lemma `lem:onefactor`) -/

lemma sSeries_absEval {v z : ℂ} (hvz : ‖v‖ < ‖z‖) : AbsEval (sSeries v) z⁻¹ (gFactor v z) := by
  have hz : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg _) hvz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  set y : ℂ := -(v * z⁻¹) with hy
  have hy1 : ‖y‖ < 1 := by
    rw [hy, norm_neg, norm_mul, norm_inv]
    rw [← div_eq_mul_inv, div_lt_one hz]
    exact hvz
  have hmem : y ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right]
    have : (‖y‖₊ : ENNReal) < 1 := by
      rw [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact_mod_cast hy1
    exact this
  have hcoeff : ∀ k, PowerSeries.coeff k (sSeries v) * z⁻¹ ^ k =
      binomialSeries ℂ (1 / 2 : ℂ) k (fun _ => y) := by
    intro k
    rw [binomialSeries_apply]
    simp only [sSeries, PowerSeries.coeff_rescale, halfSeries, PowerSeries.coeff_mk, hy,
      List.ofFn_const, List.prod_replicate, smul_eq_mul]
    rw [neg_pow v, neg_pow (v * z⁻¹), mul_pow]
    ring
  have hrad : (‖y‖₊ : ENNReal) < (binomialSeries ℂ (1 / 2 : ℂ)).radius :=
    lt_of_lt_of_le (by exact_mod_cast hy1) binomialSeries_radius_ge_one
  refine ⟨?_, ?_⟩
  · simp only [hcoeff]
    exact (binomialSeries ℂ (1 / 2 : ℂ)).summable_norm_apply
      (by rw [Metric.mem_eball, edist_zero_right]; exact hrad)
  · simp only [hcoeff]
    have h := Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℂ)) |>.hasSum hmem
    simp only [zero_add] at h
    convert h using 1
    have h1 : 1 + y = 1 - v / z := by rw [hy, div_eq_mul_inv]; ring
    have hne : 1 + y ≠ 0 := by
      have := Complex.mem_slitPlane_of_norm_lt_one hy1
      exact Complex.slitPlane_ne_zero this
    rw [Complex.cpow_def_of_ne_zero hne, h1, gFactor, mul_comm]

/-! ### Uniqueness (Lemma `lem:uniq`) -/

lemma complex_sqrt_series_unique {c g : PowerSeries ℂ}
    (hc : PowerSeries.constantCoeff c = 1) (hg : PowerSeries.constantCoeff g = 1)
    (h : c ^ 2 = g ^ 2) : c = g := by
  have h1 : (c - g) * (c + g) = 0 := by
    have : (c - g) * (c + g) = c ^ 2 - g ^ 2 := by ring
    rw [this, h, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exfalso
    have := congrArg PowerSeries.constantCoeff h2
    simp [hc, hg] at this

/-! ### Identification of the series (Lemma `lem:f`) -/

lemma map_coe_powerSeries (p : ℤ[X]) :
    PowerSeries.map (Int.castRingHom ℂ) (p : PowerSeries ℤ) = ((p.map (Int.castRingHom ℂ) : ℂ[X]) : PowerSeries ℂ) := by
  ext k
  simp [PowerSeries.coeff_map, Polynomial.coeff_coe]

private lemma reverse_map_int' (P : ℤ[X]) :
    (P.reverse).map (Int.castRingHom ℂ) = (P.map (Int.castRingHom ℂ)).reverse := by
  unfold reverse
  rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int, reflect_map]

private lemma reverse_one'' : (1 : ℂ[X]).reverse = 1 := by
  rw [← C_1, reverse_C]

private lemma reverse_X_sub_C'' (a : ℂ) : (X - C a).reverse = 1 - C a * X := by
  have : (X - C a : ℂ[X]) = X + C (-a) := by simp [sub_eq_add_neg]
  rw [this, reverse_add_C]
  have h1 : (X : ℂ[X]).reverse = 1 := by
    have h := reverse_mul_X (1 : ℂ[X])
    rw [one_mul, reverse_one''] at h
    exact h
  rw [h1, natDegree_X]
  simp [sub_eq_add_neg]

private lemma reverse_prod_X_sub_C'' (s : Multiset ℂ) :
    ((s.map fun a => X - C a).prod).reverse = piC s := by
  induction s using Multiset.induction_on with
  | empty => simp [piC, reverse_one'']
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, reverse_X_sub_C'']
    simp [piC]

private lemma map_reverse_P2 (P : ℤ[X]) (hmon : P.Monic) :
    (graeffe P.reverse).map (Int.castRingHom ℂ) =
      piC ((P.map (Int.castRingHom ℂ)).roots.map (· ^ 2)) := by
  rw [← reverse_P2 P hmon, reverse_map_int', map_P2 P hmon]
  exact reverse_prod_X_sub_C'' _

private lemma map_reverse_P4 (P : ℤ[X]) (hmon : P.Monic) :
    (graeffe (graeffe P.reverse)).map (Int.castRingHom ℂ) =
      piC ((P.map (Int.castRingHom ℂ)).roots.map (· ^ 4)) := by
  rw [← reverse_P4 P hmon, reverse_map_int', map_P4 P hmon]
  exact reverse_prod_X_sub_C'' _

/-- [A, Lemma lem:f] over `ℂ`: `f_ℂ² = ∏_{v ∈ V} (1 - v w)`. -/
lemma sqrt_series_sq_map (P : ℤ[X]) (hmon : P.Monic) (f : PowerSeries ℤ)
    (hf : f ^ 2 = ((graeffe P.reverse * graeffe (graeffe P.reverse) : ℤ[X]) : PowerSeries ℤ)) :
    (PowerSeries.map (Int.castRingHom ℂ) f) ^ 2 =
      (((P.map (Int.castRingHom ℂ)).roots.map (· ^ 2) +
          (P.map (Int.castRingHom ℂ)).roots.map (· ^ 4)).map
        fun v => 1 - PowerSeries.C v * PowerSeries.X).prod := by
  rw [← map_pow, hf, map_coe_powerSeries, Polynomial.map_mul, map_reverse_P2 P hmon,
    map_reverse_P4 P hmon]
  set B := (P.map (Int.castRingHom ℂ)).roots
  have : ∀ s : Multiset ℂ, ((piC s : ℂ[X]) : PowerSeries ℂ) =
      (s.map fun v => 1 - PowerSeries.C v * PowerSeries.X).prod := by
    intro s
    unfold piC
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro v _
    simp [Polynomial.coeToPowerSeries.ringHom_apply]
  rw [Polynomial.coe_mul, this, this, Multiset.map_add, Multiset.prod_add]

/-! ### The theorem (Theorem `thm:S5`) -/

/-- [Supplement A, Lemma lem:holo and Theorem thm:S5] analytic continuation of `√(P_2* P_4*)(1/z)` off
the hedgehog of the squared and fourth-powered roots, and its Laurent expansion at ∞. Here `f` is any
square root of `P_2* P_4*` in `ℤ[[w]]` with constant term 1; the one given by `squarerad_graeffe`
applied to `P.reverse` is such an `f`. -/
theorem caseA_S5 (P : ℤ[X]) (hmon : P.Monic) (_hirr : Irreducible P) (_hdeg : 1 < P.natDegree)
    (f : PowerSeries ℤ) (hf0 : PowerSeries.constantCoeff f = 1)
    (hf : f ^ 2 = ((graeffe P.reverse * graeffe (graeffe P.reverse) : ℤ[X]) : PowerSeries ℤ)) :
    let A := (P.map (Int.castRingHom ℂ)).roots
    let V := A.map (· ^ 2) + A.map (· ^ 4)
    let F : ℂ → ℂ := fun z =>
      (V.map fun v => Complex.exp ((1 / 2 : ℂ) * Complex.log (1 - v / z))).prod
    DifferentiableOn ℂ F (⋃ v ∈ V, segment ℝ (0 : ℂ) v)ᶜ ∧
      (∀ z ∉ (⋃ v ∈ V, segment ℝ (0 : ℂ) v), F z ^ 2 = (V.map fun v => 1 - v / z).prod) ∧
      ∀ z : ℂ, (∀ v ∈ V, ‖v‖ < ‖z‖) →
        HasSum (fun k => ((PowerSeries.coeff k f : ℤ) : ℂ) * z⁻¹ ^ k) (F z) := by
  intro A V F
  have hFeq : F = bigF V := rfl
  refine ⟨bigF_differentiableOn V, fun z hz => bigF_sq V hz, ?_⟩
  intro z hz
  set fC := PowerSeries.map (Int.castRingHom ℂ) f with hfC
  have hfC0 : PowerSeries.constantCoeff fC = 1 := by
    rw [hfC, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
    simp
  set c : PowerSeries ℂ := (V.map sSeries).prod with hc
  have hc0 : PowerSeries.constantCoeff c = 1 := by
    rw [hc, map_multiset_prod, Multiset.map_map]
    have : (V.map (PowerSeries.constantCoeff ∘ sSeries)) = V.map fun _ => (1 : ℂ) :=
      Multiset.map_congr rfl fun v _ => sSeries_coeff_zero v
    rw [this]
    simp
  have hc2 : c ^ 2 = fC ^ 2 := by
    rw [hfC, sqrt_series_sq_map P hmon f hf, hc, ← Multiset.prod_map_pow]
    congr 1
    apply Multiset.map_congr rfl
    intro v _
    exact sSeries_sq v
  have hcf : c = fC := complex_sqrt_series_unique hc0 hfC0 hc2
  have hev := AbsEval.multiset_prod V sSeries (fun v => gFactor v z) (t := z⁻¹)
    (fun v hv => sSeries_absEval (hz v hv))
  rw [← hc, hcf] at hev
  have h := hev.2
  have hk : ∀ k, ((PowerSeries.coeff k f : ℤ) : ℂ) = PowerSeries.coeff k fC := fun k => by
    rw [hfC, PowerSeries.coeff_map]; rfl
  simp only [hk]
  exact h

end RestrictedPolynomials
