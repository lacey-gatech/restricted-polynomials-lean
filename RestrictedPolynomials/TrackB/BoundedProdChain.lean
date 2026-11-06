module

public import RestrictedPolynomials.TrackB.BoundedProductAux
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Track B: the real-analysis chain of Supplement F (`thm:boundedprod`, repaired)

Source: Supplement F; the repaired chain `eq:1bdd_corr1` of CSP_6.

* `bprod_plancherel_interval` (`lem:plancherel-interval`);
* `bprod_window_bound` (`lem:window`);
* `bprod_PL` ((PL) in modulus form, every `L ≤ D`);
* `bprod_rhoT_bounds`, `bprod_window_density` (`lem:L-average` (a), (b));
* `bprod_strip_identity` (`lem:strip`, exact strip identity);
* `bprodPsi`, `bprod_psi_measurable`, `bprod_avg_bound`, `bprod_avg_exists` (`prop:avg`);
* `bprod_choose_theta` (`lem:theta`, with the repair `0 < M`: the printed lemma is false at `M = 0`);
* `bprodB`, `bprodB_ge`, `bprodB_ge_pow42` (`lem:B-lower`, `cor:42`).

Formalization choices: `0 < M` in `bprod_choose_theta`; setting (S) without a `δ ≤ 1`
binder, `W · 𝔼_L Ψ` as an interval integral, (E2)-(E4) written out, `b` complex valued with
`0 ≤ b ≤ 1` in `ComplexOrder`; `S_L`, `N_L` written through `exp`/`log`.
All proof helpers are `private`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexOrder FourierTransform
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-- `B(δ₀) = (δ₀/2)^{15/2} / (2·10⁶ (4 ln(8/δ₀) + 1))`: the constant of `thm:general`
(`= δ^{15/2}/(2·10⁶ (2D+1))` at `δ = δ₀/2`, `D = ln(16/δ²)`). -/
def bprodB (δ : ℝ) : ℝ :=
  (δ / 2) ^ (15 / 2 : ℝ) / (2 * 10 ^ 6 * (4 * Real.log (8 / δ) + 1))

/-- `ρ̃(u) = |[u-a,u] ∩ [-D-1, D]| / a` (Lemma `lem:L-average`, `I = [-D-1, D]`, strip width `a`). -/
def bprodRhoT (D a u : ℝ) : ℝ :=
  (volume (Set.Icc (u - a) u ∩ Set.Icc (-D - 1) D)).toReal / a

/-- `lem:plancherel-interval`: `∫|𝓕 1_{[A,B]}|² = B - A`. -/
theorem bprod_plancherel_interval {A B : ℝ} (hAB : A ≤ B) :
    ∫ θ : ℝ, ‖𝓕 (Set.indicator (Set.Icc A B) (fun _ => (1 : ℂ))) θ‖ ^ 2 = B - A := by
  have h2 : MemLp (Set.indicator (Set.Icc A B) (fun _ => (1 : ℂ))) 2 :=
    memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet _ (Or.inr (by simp))
  have h1 : Integrable (Set.indicator (Set.Icc A B) (fun _ => (1 : ℂ))) :=
    memLp_one_iff_integrable.1 (memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet _ (Or.inr (by simp)))
  rw [(bprod_plancherel_L1_L2 _ h1 h2).2]
  have : (fun x => ‖Set.indicator (Set.Icc A B) (fun _ => (1 : ℂ)) x‖ ^ 2) =
      Set.indicator (Set.Icc A B) (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc A B <;> simp [hx]
  rw [this, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hAB]
  simp

/-- `lem:L-average` (a): the strip density `ρ̃` is in `[0,1]`, supported in `[-D-1, D+a]` and
equal to `1` on `[-D, D]` (here `0 < a ≤ 1`; no `0 ≤ D` is needed). -/
theorem bprod_rhoT_bounds {D a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∀ u : ℝ, 0 ≤ bprodRhoT D a u ∧ bprodRhoT D a u ≤ 1) ∧
    (∀ u : ℝ, u ∉ Set.Icc (-D - 1) (D + a) → bprodRhoT D a u = 0) ∧
    (∀ u ∈ Set.Icc (-D) D, bprodRhoT D a u = 1) := by
  refine ⟨fun u => ⟨div_nonneg ENNReal.toReal_nonneg ha0.le, ?_⟩, fun u hu => ?_, fun u hu => ?_⟩
  · unfold bprodRhoT
    rw [div_le_one ha0]
    have h1 : volume (Set.Icc (u - a) u ∩ Set.Icc (-D - 1) D) ≤ ENNReal.ofReal a := by
      calc _ ≤ volume (Set.Icc (u - a) u) := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal a := by rw [Real.volume_Icc]; congr 1; ring
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans (by rw [ENNReal.toReal_ofReal ha0.le])
  · have : Set.Icc (u - a) u ∩ Set.Icc (-D - 1) D = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2 h3
      exact hu ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩
    simp [bprodRhoT, this]
  · have hsub : Set.Icc (u - a) u ⊆ Set.Icc (-D - 1) D := by
      intro x hx; exact ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hu.2]⟩
    rw [bprodRhoT, Set.inter_eq_left.2 hsub, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    field_simp
    ring

/-- `lem:L-average` (b): the window `{L : |u - s - L| < η/2}` meets `I` in length at most `η`. -/
theorem bprod_window_density {D η : ℝ} (hη : 0 < η) (u s : ℝ) :
    (volume (Set.Ioo (u - s - η / 2) (u - s + η / 2) ∩ Set.Icc (-D - 1) D)).toReal ≤ η := by
  have h1 : volume (Set.Ioo (u - s - η / 2) (u - s + η / 2) ∩ Set.Icc (-D - 1) D) ≤
      ENNReal.ofReal η := by
    calc _ ≤ volume (Set.Ioo (u - s - η / 2) (u - s + η / 2)) :=
          measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal η := by rw [Real.volume_Ioo]; congr 1; ring
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans (by rw [ENNReal.toReal_ofReal hη.le])

/-- `lem:theta` with the repair `0 < M`: `c ∈ L¹`, `h` bounded
continuous, `∫|c| ≤ M`, `|∫ c h| ≥ s M` give `θ` with `|h θ| ≥ s`. -/
theorem bprod_choose_theta {c h : ℝ → ℂ} (hc : Integrable c) (hh : Continuous h)
    (hhb : ∃ B : ℝ, ∀ θ, ‖h θ‖ ≤ B) {M s : ℝ} (hM0 : 0 < M) (hM : ∫ θ : ℝ, ‖c θ‖ ≤ M) (hs : 0 < s)
    (hcs : s * M ≤ ‖∫ θ : ℝ, c θ * h θ‖) : ∃ θ : ℝ, s ≤ ‖h θ‖ := by
  have _ := hhb
  by_contra hcon
  push Not at hcon
  have hsM : 0 < s * M := mul_pos hs hM0
  have hch : Integrable (fun θ => c θ * h θ) :=
    Integrable.mul_bdd hc hh.aestronglyMeasurable (c := s)
      (Filter.Eventually.of_forall fun θ => (hcon θ).le)
  have hnorm : Integrable (fun θ => ‖c θ‖ * ‖h θ‖) := by
    simpa [norm_mul] using hch.norm
  have hint : Integrable (fun θ => ‖c θ‖ * (s - ‖h θ‖)) := by
    have : (fun θ => ‖c θ‖ * (s - ‖h θ‖)) = fun θ => s * ‖c θ‖ - ‖c θ‖ * ‖h θ‖ := by
      funext θ; ring
    rw [this]
    exact (hc.norm.const_mul s).sub hnorm
  have hnn : 0 ≤ᵐ[volume] fun θ => ‖c θ‖ * (s - ‖h θ‖) :=
    Filter.Eventually.of_forall fun θ => mul_nonneg (norm_nonneg _) (sub_nonneg.2 (hcon θ).le)
  have hpos : 0 < ∫ θ, ‖c θ‖ * (s - ‖h θ‖) := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    by_contra hz
    rw [not_lt, nonpos_iff_eq_zero] at hz
    have hc0 : c =ᵐ[volume] 0 := by
      have : ∀ᵐ θ, θ ∉ Function.support (fun θ => ‖c θ‖ * (s - ‖h θ‖)) := by
        exact measure_eq_zero_iff_ae_notMem.1 hz
      filter_upwards [this] with θ hθ
      simp only [Function.mem_support, not_not] at hθ
      have hpos' : 0 < s - ‖h θ‖ := sub_pos.2 (hcon θ)
      have := (mul_eq_zero.1 hθ).resolve_right hpos'.ne'
      simpa using this
    have : ∫ θ, c θ * h θ = 0 := by
      have : (fun θ => c θ * h θ) =ᵐ[volume] 0 := by
        filter_upwards [hc0] with θ hθ
        simp [hθ]
      rw [integral_congr_ae this]; simp
    rw [this] at hcs
    simp at hcs
    linarith
  have h1 : ‖∫ θ, c θ * h θ‖ ≤ ∫ θ, ‖c θ‖ * ‖h θ‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp
  have h2 : ∫ θ, ‖c θ‖ * (s - ‖h θ‖) = s * (∫ θ, ‖c θ‖) - ∫ θ, ‖c θ‖ * ‖h θ‖ := by
    have : (fun θ => ‖c θ‖ * (s - ‖h θ‖)) = fun θ => s * ‖c θ‖ - ‖c θ‖ * ‖h θ‖ := by
      funext θ; ring
    rw [this, integral_sub (hc.norm.const_mul s) hnorm, integral_const_mul]
  have h3 : s * (∫ θ, ‖c θ‖) ≤ s * M := mul_le_mul_of_nonneg_left hM hs.le
  linarith

/-- `lem:B-lower`: `B(δ₀) ≥ 2.96·10⁻¹⁰ δ₀^{17/2}` for `δ₀ ∈ (0,1]`. -/
theorem bprodB_ge {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    (2.96 * 10 ^ (-10 : ℝ)) * δ ^ (17 / 2 : ℝ) ≤ bprodB δ := by
  unfold bprodB
  have hlog2 := Real.log_two_lt_d9
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlogδ : δ * (-Real.log δ) ≤ 1 - δ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 h0)
    rw [Real.log_inv] at this
    have h2 : δ * (-Real.log δ) ≤ δ * (δ⁻¹ - 1) := mul_le_mul_of_nonneg_left this h0.le
    rw [mul_sub, mul_inv_cancel₀ h0.ne'] at h2
    linarith
  have hQ : δ * (4 * Real.log (8 / δ) + 1) ≤ 4 * (3 * 0.6931471808) + 1 := by
    rw [Real.log_div (by norm_num) h0.ne', hl8]
    nlinarith
  have hQpos : 0 < 4 * Real.log (8 / δ) + 1 := by
    rw [Real.log_div (by norm_num) h0.ne', hl8]
    have := Real.log_nonneg (show (1:ℝ) ≤ 1 / δ by rw [le_div_iff₀ h0]; linarith)
    have h3 : 0 ≤ Real.log (1/δ) := this
    rw [one_div, Real.log_inv] at h3
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
    linarith
  have hpow : (δ / 2) ^ (15 / 2 : ℝ) = δ ^ (15 / 2 : ℝ) / (128 * Real.sqrt 2) := by
    rw [Real.div_rpow h0.le (by norm_num)]
    congr 1
    rw [show (15 / 2 : ℝ) = 7 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
      ← Real.sqrt_eq_rpow]
    norm_num
  have hδ17 : δ ^ (17 / 2 : ℝ) = δ ^ (15 / 2 : ℝ) * δ := by
    rw [show (17 / 2 : ℝ) = 15 / 2 + 1 by norm_num, Real.rpow_add h0, Real.rpow_one]
  have hs2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have h10 : (10 : ℝ) ^ (-10 : ℝ) = 1 / 10 ^ 10 := by
    rw [Real.rpow_neg (by norm_num)]
    rw [show (10 : ℝ) ^ (10 : ℝ) = 10 ^ (10 : ℕ) by exact_mod_cast Real.rpow_natCast 10 10]
    simp
  rw [hpow, hδ17, h10]
  have hp : 0 < δ ^ (15 / 2 : ℝ) := Real.rpow_pos_of_pos h0 _
  rw [div_div, le_div_iff₀ (by positivity)]
  have key : 2.96 * (1 / 10 ^ 10) * (2 * 10 ^ 6 * (4 * Real.log (8 / δ) + 1)) * (128 * Real.sqrt 2) * δ ≤ 1 := by
    have e : 2.96 * (1 / (10:ℝ) ^ 10) * (2 * 10 ^ 6 * (4 * Real.log (8 / δ) + 1)) *
        (128 * Real.sqrt 2) * δ =
        (2.96 * (1 / (10:ℝ) ^ 10) * (2 * 10 ^ 6) * (128 * Real.sqrt 2)) *
          (δ * (4 * Real.log (8 / δ) + 1)) := by ring
    rw [e]
    have hc : 2.96 * (1 / (10:ℝ) ^ 10) * (2 * 10 ^ 6) * (128 * Real.sqrt 2) ≤
        2.96 * (1 / (10:ℝ) ^ 10) * (2 * 10 ^ 6) * (128 * 1.4143) := by gcongr
    calc _ ≤ (2.96 * (1 / (10:ℝ) ^ 10) * (2 * 10 ^ 6) * (128 * 1.4143)) *
          (4 * (3 * 0.6931471808) + 1) := by
          apply mul_le_mul hc hQ (by positivity) (by positivity)
      _ ≤ 1 := by norm_num
  calc 2.96 * (1 / 10 ^ 10) * (δ ^ (15 / 2 : ℝ) * δ) *
        (128 * Real.sqrt 2 * (2 * 10 ^ 6 * (4 * Real.log (8 / δ) + 1))) = δ ^ (15 / 2 : ℝ) *
        (2.96 * (1 / (10:ℝ) ^ 10) * (2 * 10 ^ 6 * (4 * Real.log (8 / δ) + 1)) *
        (128 * Real.sqrt 2) * δ) := by ring
    _ ≤ δ ^ (15 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left key hp.le
    _ = _ := mul_one _

/-- `cor:42`: `B(δ₀) ≥ (δ₀/2)^{42}` for `δ₀ ∈ (0,1]`. -/
theorem bprodB_ge_pow42 {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) : (δ / 2) ^ 42 ≤ bprodB δ := by
  unfold bprodB
  set x := δ / 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; linarith
  have hδx : δ = 2 * x := by rw [hx]; ring
  have h8 : 8 / δ = 4 / x := by rw [hδx]; field_simp; ring
  rw [h8]
  have hlog : Real.log (4 / x) ≤ 4 / x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 4 / x by positivity)
    linarith
  have hlogn : 0 ≤ Real.log (4 / x) :=
    Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  have hQpos : 0 < 4 * Real.log (4 / x) + 1 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hsplit : x ^ 42 = x ^ (15 / 2 : ℝ) * x ^ 34 * x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast x 34, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have h72 : x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx0.le (by linarith) (by norm_num)
  have h33 : x ^ 33 ≤ (1 / 2) ^ 33 := pow_le_pow_left₀ hx0.le hx1 33
  have hpos : 0 < x ^ (15 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have h34 : x ^ 34 * (4 * Real.log (4 / x) + 1) ≤ 17 * x ^ 33 := by
    have e1 : x ^ 34 * (4 * Real.log (4 / x) + 1) ≤ x ^ 34 * (4 * (4 / x) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : x ^ 34 * (4 * (4 / x) + 1) = 16 * x ^ 33 + x ^ 34 := by
      field_simp; ring
    have e3 : x ^ 34 ≤ x ^ 33 := pow_le_pow_of_le_one hx0.le (by linarith) (by norm_num)
    linarith
  have hfin : 2 * 10 ^ 6 * (17 * x ^ 33) ≤ 1 := by
    have : 2 * 10 ^ 6 * (17 * x ^ 33) ≤ 2 * 10 ^ 6 * (17 * (1 / 2) ^ 33) := by gcongr
    refine this.trans ?_
    norm_num
  calc x ^ 42 * (2 * 10 ^ 6 * (4 * Real.log (4 / x) + 1))
      = x ^ (15 / 2 : ℝ) * (x ^ (1 / 2 : ℝ)) * (2 * 10 ^ 6 * (x ^ 34 * (4 * Real.log (4 / x) + 1))) := by
        rw [hsplit]; ring
    _ ≤ x ^ (15 / 2 : ℝ) * 1 * (2 * 10 ^ 6 * (17 * x ^ 33)) := by
        gcongr
    _ ≤ x ^ (15 / 2 : ℝ) * 1 * 1 := by
        apply mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = _ := by ring

/-- `lem:window`: `|b - 1_{[L,R]}| ≤ 1_N`, `N` the two open `η/2`-windows. -/
theorem bprod_window_bound {L R η : ℝ} (hLR : L ≤ R) (hη : 0 < η) (b : ℝ → ℂ)
    (hb2 : ∀ x : ℝ, L + η / 2 ≤ x → x ≤ R - η / 2 → b x = 1)
    (hb3 : ∀ x : ℝ, x ≤ L - η / 2 ∨ R + η / 2 ≤ x → b x = 0)
    (hb4 : ∀ x : ℝ, 0 ≤ b x ∧ b x ≤ 1) (y : ℝ) :
    ‖b y - (if L ≤ y ∧ y ≤ R then (1 : ℂ) else 0)‖ ≤
      (if |y - L| < η / 2 ∨ |y - R| < η / 2 then (1 : ℝ) else 0) := by
  have _ := hLR
  have h0 := Complex.le_def.1 (hb4 y).1
  have h1 := Complex.le_def.1 (hb4 y).2
  simp only [Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] at h0 h1
  have hby : b y = (((b y).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h0.2])
  set r := (b y).re with hr
  have hc : (if L ≤ y ∧ y ≤ R then (1 : ℂ) else 0) =
      (((if L ≤ y ∧ y ≤ R then (1 : ℝ) else 0 : ℝ)) : ℂ) := by
    split_ifs <;> simp
  rw [hc, hby, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_cases hN : |y - L| < η / 2 ∨ |y - R| < η / 2
  · simp only [hN, ↓reduceIte]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [h0.1, h1.1]
  · simp only [hN, ↓reduceIte]
    push Not at hN
    obtain ⟨hN1, hN2⟩ := hN
    have hN1' := hN1; have hN2' := hN2
    rw [le_abs'] at hN1' hN2'
    by_cases hout : y ≤ L - η / 2 ∨ R + η / 2 ≤ y
    · have hr0 : r = 0 := by rw [hr, hb3 y hout]; simp
      have hnot : ¬ (L ≤ y ∧ y ≤ R) := by
        rintro ⟨a, b⟩; rcases hout with h | h <;> linarith
      simp only [hnot, ↓reduceIte, hr0]; simp
    · push Not at hout
      have hy1 : L + η / 2 ≤ y := by
        rcases hN1' with h | h
        · linarith [hout.1]
        · linarith
      have hy2 : y ≤ R - η / 2 := by
        rcases hN2' with h | h
        · linarith [hout.2]
        · linarith
      have hr1 : r = 1 := by rw [hr, hb2 y hy1 hy2]; simp
      have hin : L ≤ y ∧ y ≤ R := ⟨by linarith, by linarith⟩
      simp only [hin, and_self, ↓reduceIte, hr1]; simp

section PLaux
variable {X : Type*} [Fintype X]

private theorem PL_aux (F : X → ℂ) (p : X → ℝ) (hpos : ∀ x, 0 < p x)
    {L D a η : ℝ} (hLD : L ≤ D) (ha : 0 < a) (hη : 0 < η) (b : ℝ → ℂ)
    (hb2 : ∀ x : ℝ, L + η / 2 ≤ x → x ≤ L + a - η / 2 → b x = 1)
    (hb3 : ∀ x : ℝ, x ≤ L - η / 2 ∨ L + a + η / 2 ≤ x → b x = 0)
    (hb4 : ∀ x : ℝ, 0 ≤ b x ∧ b x ≤ 1) :
    Real.exp (-D) * ‖𝔼 x : X, F x * ((p x : ℝ) : ℂ) *
        (if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℂ) else 0)‖ -
      (Real.exp a - 1) * (𝔼 x : X, ‖F x‖ *
          (if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℝ) else 0)) -
      𝔼 x : X, ‖F x‖ *
          (if |Real.log (p x) - L| < η / 2 ∨ |Real.log (p x) - (L + a)| < η / 2
            then (1 : ℝ) else 0) ≤
      ‖𝔼 x : X, F x * b (Real.log (p x))‖ := by
  set SC : X → ℂ := fun x => if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℂ) else 0
    with hSC
  set SR : X → ℝ := fun x => if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℝ) else 0
    with hSR
  set NR : X → ℝ := fun x => if |Real.log (p x) - L| < η / 2 ∨ |Real.log (p x) - (L + a)| < η / 2
    then (1 : ℝ) else 0 with hNR
  have hSCR : ∀ x, SC x = ((SR x : ℝ) : ℂ) := by
    intro x; simp only [hSC, hSR]; split_ifs <;> simp
  have hSiff : ∀ x, (Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a)) ↔
      (L ≤ Real.log (p x) ∧ Real.log (p x) ≤ L + a) := by
    intro x
    rw [Real.le_log_iff_exp_le (hpos x), Real.log_le_iff_le_exp (hpos x)]
  -- Step 1: window
  have hwin : ∀ x, ‖b (Real.log (p x)) - SC x‖ ≤ NR x := by
    intro x
    have := bprod_window_bound (L := L) (R := L + a) (η := η) (by linarith) hη b
      (fun y h1 h2 => hb2 y h1 (by linarith)) (fun y h => hb3 y (by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith))) hb4 (Real.log (p x))
    have e : SC x = if L ≤ Real.log (p x) ∧ Real.log (p x) ≤ L + a then (1 : ℂ) else 0 := by
      simp only [hSC, hSiff x]
    rw [e]
    simpa [hNR, add_sub_assoc] using this
  have hstep1 : ‖𝔼 x : X, F x * SC x‖ - 𝔼 x : X, ‖F x‖ * NR x ≤
      ‖𝔼 x : X, F x * b (Real.log (p x))‖ := by
    have hsplit : 𝔼 x : X, F x * SC x = (𝔼 x : X, F x * b (Real.log (p x))) -
        𝔼 x : X, F x * (b (Real.log (p x)) - SC x) := by
      rw [← Finset.expect_sub_distrib]
      refine Finset.expect_congr rfl fun x _ => ?_
      ring
    have h1 : ‖𝔼 x : X, F x * (b (Real.log (p x)) - SC x)‖ ≤ 𝔼 x : X, ‖F x‖ * NR x := by
      refine (RCLike.norm_expect_le (K := ℝ)).trans (Finset.expect_le_expect fun x _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hwin x) (norm_nonneg _)
    have h2 := norm_sub_le (𝔼 x : X, F x * b (Real.log (p x)))
      (𝔼 x : X, F x * (b (Real.log (p x)) - SC x))
    rw [← hsplit] at h2
    linarith
  -- Step 2: replace 1 by e^{-L} p
  have hstep2 : Real.exp (-L) * ‖𝔼 x : X, F x * ((p x : ℝ) : ℂ) * SC x‖ -
      (Real.exp a - 1) * 𝔼 x : X, ‖F x‖ * SR x ≤ ‖𝔼 x : X, F x * SC x‖ := by
    have hsplit : ((Real.exp (-L) : ℝ) : ℂ) * 𝔼 x : X, F x * ((p x : ℝ) : ℂ) * SC x =
        (𝔼 x : X, F x * SC x) +
          𝔼 x : X, F x * ((Real.exp (-L) * p x - 1 : ℝ) : ℂ) * SC x := by
      rw [Finset.mul_expect, ← Finset.expect_add_distrib]
      refine Finset.expect_congr rfl fun x _ => ?_
      push_cast
      ring
    have h1 : ‖𝔼 x : X, F x * ((Real.exp (-L) * p x - 1 : ℝ) : ℂ) * SC x‖ ≤
        (Real.exp a - 1) * 𝔼 x : X, ‖F x‖ * SR x := by
      rw [Finset.mul_expect]
      refine (RCLike.norm_expect_le (K := ℝ)).trans (Finset.expect_le_expect fun x _ => ?_)
      rw [norm_mul, norm_mul, hSCR x, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      by_cases hx : Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a)
      · have hS1 : SR x = 1 := by simp [hSR, hx]
        rw [hS1, abs_one, mul_one, mul_one]
        have e1 : 1 ≤ Real.exp (-L) * p x := by
          have := mul_le_mul_of_nonneg_left hx.1 (Real.exp_pos (-L)).le
          rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
        have e2 : Real.exp (-L) * p x ≤ Real.exp a := by
          have := mul_le_mul_of_nonneg_left hx.2 (Real.exp_pos (-L)).le
          rwa [← Real.exp_add, show -L + (L + a) = a by ring] at this
        rw [abs_of_nonneg (by linarith)]
        have := norm_nonneg (F x)
        nlinarith
      · have hS0 : SR x = 0 := by simp [hSR, hx]
        simp [hS0]
    have h2 := norm_add_le (𝔼 x : X, F x * SC x)
      (𝔼 x : X, F x * ((Real.exp (-L) * p x - 1 : ℝ) : ℂ) * SC x)
    rw [← hsplit, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    linarith
  have hexp : Real.exp (-D) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-D) * ‖𝔼 x : X, F x * ((p x : ℝ) : ℂ) * SC x‖ ≤
      Real.exp (-L) * ‖𝔼 x : X, F x * ((p x : ℝ) : ℂ) * SC x‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  linarith

end PLaux

section IntAux
variable {X : Type*} [Fintype X]

private theorem integral_expect_ind {𝕜 : Type*} [RCLike 𝕜] {lo hi : ℝ}
    (c : X → 𝕜) (s : X → Set ℝ) (hs : ∀ x, MeasurableSet (s x)) :
    (∫ L in Set.Icc lo hi, 𝔼 x : X, Set.indicator (s x) (fun _ => c x) L) =
      𝔼 x : X, ((volume (s x ∩ Set.Icc lo hi)).toReal : 𝕜) * c x := by
  have hint : ∀ x, Integrable (fun L => Set.indicator (s x) (fun _ => c x) L)
      (volume.restrict (Set.Icc lo hi)) := fun x =>
    (integrable_const (c x)).indicator (hs x)
  simp only [Fintype.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ (fun x _ => hint x)]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_indicator_const _ (hs x), measureReal_def, Measure.restrict_apply (hs x),
    RCLike.real_smul_eq_coe_mul]

private theorem integrable_expect_ind {𝕜 : Type*} [RCLike 𝕜] {lo hi : ℝ}
    (c : X → 𝕜) (s : X → Set ℝ) (hs : ∀ x, MeasurableSet (s x)) :
    IntegrableOn (fun L => 𝔼 x : X, Set.indicator (s x) (fun _ => c x) L) (Set.Icc lo hi) := by
  have hint : ∀ x, Integrable (fun L => Set.indicator (s x) (fun _ => c x) L)
      (volume.restrict (Set.Icc lo hi)) := fun x =>
    (integrable_const (c x)).indicator (hs x)
  simp only [Fintype.expect_eq_sum_div_card]
  exact (integrable_finsetSum _ (fun x _ => hint x)).div_const _

end IntAux

section StripAux
variable {X : Type*} [Fintype X]

private theorem ind_strip_eq (p : ℝ) (hp : 0 < p) (a L : ℝ) {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) :
    c * (if Real.exp L ≤ p ∧ p ≤ Real.exp (L + a) then (1 : 𝕜) else 0) =
      Set.indicator (Set.Icc (Real.log p - a) (Real.log p)) (fun _ => c) L := by
  have hiff : (Real.exp L ≤ p ∧ p ≤ Real.exp (L + a)) ↔ L ∈ Set.Icc (Real.log p - a) (Real.log p) := by
    rw [← Real.le_log_iff_exp_le hp, ← Real.log_le_iff_le_exp hp, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  by_cases h : L ∈ Set.Icc (Real.log p - a) (Real.log p)
  · have h' := hiff.2 h
    simp [h', h]
  · have h' : ¬ (Real.exp L ≤ p ∧ p ≤ Real.exp (L + a)) := fun h' => h (hiff.1 h')
    simp [h', h]

private theorem strip_integral_aux (F : X → ℂ) (p : X → ℝ) (hpos : ∀ x, 0 < p x)
    {lo hi a : ℝ} (hlh : lo ≤ hi) (ha : 0 < a) :
    (∫ L in lo..hi, 𝔼 x : X, F x * ((p x : ℝ) : ℂ) *
        (if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℂ) else 0)) =
      (a : ℂ) * 𝔼 x : X, (F x * ((p x : ℝ) : ℂ)) *
        (((volume (Set.Icc (Real.log (p x) - a) (Real.log (p x)) ∩ Set.Icc lo hi)).toReal / a : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le hlh, ← integral_Icc_eq_integral_Ioc]
  have : ∀ L, (𝔼 x : X, F x * ((p x : ℝ) : ℂ) *
        (if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℂ) else 0)) =
      𝔼 x : X, Set.indicator (Set.Icc (Real.log (p x) - a) (Real.log (p x)))
        (fun _ => F x * ((p x : ℝ) : ℂ)) L := by
    intro L
    refine Finset.expect_congr rfl fun x _ => ?_
    exact ind_strip_eq (p x) (hpos x) a L _
  simp_rw [this]
  rw [integral_expect_ind (fun x => F x * ((p x : ℝ) : ℂ))
    (fun x => Set.Icc (Real.log (p x) - a) (Real.log (p x))) (fun x => measurableSet_Icc),
    Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ => ?_
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp
  generalize ((volume (Set.Icc (Real.log (p x) - a) (Real.log (p x)) ∩ Set.Icc lo hi)).toReal) = r
  change (r : ℂ) * _ * _ = _
  ring1

end StripAux

section PsiAux
variable {X : Type*} [Fintype X]

private def cA (F : X → ℂ) (p : X → ℝ) (a L : ℝ) : ℂ :=
  𝔼 x : X, F x * ((p x : ℝ) : ℂ) *
    (if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℂ) else 0)

private def cS (F : X → ℂ) (p : X → ℝ) (a L : ℝ) : ℝ :=
  𝔼 x : X, ‖F x‖ * (if Real.exp L ≤ p x ∧ p x ≤ Real.exp (L + a) then (1 : ℝ) else 0)

private def cN (F : X → ℂ) (p : X → ℝ) (a η L : ℝ) : ℝ :=
  𝔼 x : X, ‖F x‖ * (if |Real.log (p x) - L| < η / 2 ∨ |Real.log (p x) - (L + a)| < η / 2
    then (1 : ℝ) else 0)

private def nSet (u a η : ℝ) : Set ℝ :=
  Set.Ioo (u - 0 - η / 2) (u - 0 + η / 2) ∪ Set.Ioo (u - a - η / 2) (u - a + η / 2)

private theorem nSet_measurable (u a η : ℝ) : MeasurableSet (nSet u a η) :=
  measurableSet_Ioo.union measurableSet_Ioo

private theorem ite_N_eq (u a η L : ℝ) {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) :
    c * (if |u - L| < η / 2 ∨ |u - (L + a)| < η / 2 then (1 : 𝕜) else 0) =
      Set.indicator (nSet u a η) (fun _ => c) L := by
  have hiff : (|u - L| < η / 2 ∨ |u - (L + a)| < η / 2) ↔ L ∈ nSet u a η := by
    simp only [nSet, Set.mem_union, Set.mem_Ioo, abs_sub_lt_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
  by_cases h : L ∈ nSet u a η
  · have h' := hiff.2 h
    simp [h', h]
  · have h' : ¬ (|u - L| < η / 2 ∨ |u - (L + a)| < η / 2) := fun h' => h (hiff.1 h')
    simp [h', h]

private theorem cA_eq (F : X → ℂ) (p : X → ℝ) (hpos : ∀ x, 0 < p x) (a : ℝ) :
    cA F p a = fun L => 𝔼 x : X, Set.indicator (Set.Icc (Real.log (p x) - a) (Real.log (p x)))
      (fun _ => F x * ((p x : ℝ) : ℂ)) L := by
  funext L
  exact Finset.expect_congr rfl fun x _ => ind_strip_eq (p x) (hpos x) a L _

private theorem cS_eq (F : X → ℂ) (p : X → ℝ) (hpos : ∀ x, 0 < p x) (a : ℝ) :
    cS F p a = fun L => 𝔼 x : X, Set.indicator (Set.Icc (Real.log (p x) - a) (Real.log (p x)))
      (fun _ => ‖F x‖) L := by
  funext L
  exact Finset.expect_congr rfl fun x _ => ind_strip_eq (p x) (hpos x) a L (‖F x‖ : ℝ)

private theorem cN_eq (F : X → ℂ) (p : X → ℝ) (a η : ℝ) :
    cN F p a η = fun L => 𝔼 x : X, Set.indicator (nSet (Real.log (p x)) a η)
      (fun _ => ‖F x‖) L := by
  funext L
  exact Finset.expect_congr rfl fun x _ => ite_N_eq (Real.log (p x)) a η L (‖F x‖ : ℝ)

private theorem measurable_expect_ind {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (c : X → 𝕜) (s : X → Set ℝ) (hs : ∀ x, MeasurableSet (s x)) :
    Measurable fun L => 𝔼 x : X, Set.indicator (s x) (fun _ => c x) L := by
  simp only [Fintype.expect_eq_sum_div_card]
  exact (Finset.measurable_sum _ fun x _ => measurable_const.indicator (hs x)).div_const _

private theorem cA_measurable (F : X → ℂ) (p : X → ℝ) (a : ℝ) :
    Measurable (cA F p a) := by
  unfold cA
  simp only [Fintype.expect_eq_sum_div_card]
  refine (Finset.measurable_sum _ fun x _ => ?_).div_const _
  refine Measurable.const_mul (Measurable.ite ?_ measurable_const measurable_const) _
  exact (measurableSet_le Real.measurable_exp measurable_const).inter
    (measurableSet_le measurable_const
      (Real.measurable_exp.comp (measurable_id.add_const a)))

private theorem cS_measurable (F : X → ℂ) (p : X → ℝ) (a : ℝ) :
    Measurable (cS F p a) := by
  unfold cS
  simp only [Fintype.expect_eq_sum_div_card]
  refine (Finset.measurable_sum _ fun x _ => ?_).div_const _
  refine Measurable.const_mul (Measurable.ite ?_ measurable_const measurable_const) _
  exact (measurableSet_le Real.measurable_exp measurable_const).inter
    (measurableSet_le measurable_const
      (Real.measurable_exp.comp (measurable_id.add_const a)))

private theorem cN_measurable (F : X → ℂ) (p : X → ℝ) (a η : ℝ) :
    Measurable (cN F p a η) := by
  unfold cN
  simp only [Fintype.expect_eq_sum_div_card]
  refine (Finset.measurable_sum _ fun x _ => ?_).div_const _
  refine Measurable.const_mul (Measurable.ite ?_ measurable_const measurable_const) _
  exact (measurableSet_lt (by fun_prop : Measurable fun L : ℝ => |Real.log (p x) - L|)
      measurable_const).union
    (measurableSet_lt (by fun_prop : Measurable fun L : ℝ => |Real.log (p x) - (L + a)|)
      measurable_const)

private theorem cA_bound (F : X → ℂ) (p : X → ℝ) (a L : ℝ) :
    ‖cA F p a L‖ ≤ 𝔼 x : X, ‖F x‖ * |p x| := by
  unfold cA
  refine (RCLike.norm_expect_le (K := ℝ)).trans (Finset.expect_le_expect fun x _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := norm_nonneg (F x)
  have := abs_nonneg (p x)
  split_ifs
  · simp
  · simp; positivity

private theorem cS_bound (F : X → ℂ) (p : X → ℝ) (a L : ℝ) :
    0 ≤ cS F p a L ∧ cS F p a L ≤ 𝔼 x : X, ‖F x‖ := by
  unfold cS
  refine ⟨Finset.expect_nonneg fun x _ => by split_ifs <;> simp, Finset.expect_le_expect fun x _ => ?_⟩
  have := norm_nonneg (F x)
  split_ifs <;> simp

private theorem cN_bound (F : X → ℂ) (p : X → ℝ) (a η L : ℝ) :
    0 ≤ cN F p a η L ∧ cN F p a η L ≤ 𝔼 x : X, ‖F x‖ := by
  unfold cN
  refine ⟨Finset.expect_nonneg fun x _ => by split_ifs <;> simp, Finset.expect_le_expect fun x _ => ?_⟩
  have := norm_nonneg (F x)
  split_ifs <;> simp

private theorem integrableOn_of_bdd {g : ℝ → ℝ} (hm : Measurable g) {C : ℝ}
    (hC : ∀ L, |g L| ≤ C) (s : Set ℝ) (hs : volume s < ⊤) : IntegrableOn g s := by
  refine Measure.integrableOn_of_bounded (M := C) hs.ne hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun L => by simpa [Real.norm_eq_abs] using hC L

end PsiAux

section Chain
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Ψ(L) = e^{-D}‖A_L‖ - (e^a - 1) 𝔼|f|1_{S_L} - 𝔼|f|1_{N_L}` (Proposition `prop:avg`). -/
def bprodPsi (f : (ι → α) → ℂ) (P : ι → α → ℝ) (D a η L : ℝ) : ℝ :=
  Real.exp (-D) * ‖bprodA f P L (L + a)‖ -
        (Real.exp a - 1) * (𝔼 x : ι → α, ‖f x‖ *
          (if Real.exp L ≤ ∏ i, P i (x i) ∧ ∏ i, P i (x i) ≤ Real.exp (L + a) then (1 : ℝ) else 0)) -
        𝔼 x : ι → α, ‖f x‖ *
          (if |Real.log (∏ i, P i (x i)) - L| < η / 2 ∨
              |Real.log (∏ i, P i (x i)) - (L + a)| < η / 2 then (1 : ℝ) else 0)

/-- `𝔼 P² ≤ 1` for `P = ∏ Pᵢ` with `𝔼 Pᵢ² ≤ 1` (private re-proof). -/
private theorem chain_expect_prod_sq_le_one (P : ι → α → ℝ) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1) :
    𝔼 x : ι → α, (∏ i, P i (x i)) ^ 2 ≤ 1 := by
  simp_rw [← Finset.prod_pow]
  rw [bprod_expect_prod_sq P]
  exact Finset.prod_le_one₀ (fun i _ => Finset.expect_nonneg fun a _ => sq_nonneg _)
    fun i _ => hP i

/-- `‖𝔼 f P‖ ≤ 1` (private re-proof of the `private` lemma of `BoundedProductAux`). -/
private theorem chain_expect_norm_mul_le_one (f : (ι → α) → ℂ)
    (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
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
      have h2 := chain_expect_prod_sq_le_one P hP
      gcongr
    _ = 1 := by norm_num

/-- `𝔼 ‖f‖ ≤ 1` from `𝔼 ‖f‖⁴ ≤ 1`. -/
private theorem chain_expect_norm_le_one (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1) :
    𝔼 x : ι → α, ‖f x‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (ι → α) with hne | hne
  · simp [Finset.univ_eq_empty]
  calc 𝔼 x : ι → α, ‖f x‖ ≤ 𝔼 x : ι → α, (3 / 4 + ‖f x‖ ^ 4 / 4) := by
        refine Finset.expect_le_expect fun x _ => ?_
        have hF := norm_nonneg (f x)
        nlinarith [mul_nonneg (sq_nonneg (‖f x‖ - 1)) (by positivity : (0 : ℝ) ≤ ‖f x‖ ^ 2 + 2 * ‖f x‖ + 3)]
    _ = 3 / 4 + (𝔼 x : ι → α, ‖f x‖ ^ 4) / 4 := by
        rw [Finset.expect_add_distrib, Finset.expect_const univ_nonempty, ← Finset.expect_div]
    _ ≤ 3 / 4 + 1 / 4 := by gcongr
    _ = 1 := by norm_num

private theorem chain_D_facts {δ D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : D = Real.log (16 / δ ^ 2)) : 0 ≤ D ∧ Real.exp (-D) = δ ^ 2 / 16 := by
  have hpos : 0 < 16 / δ ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [hD]
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hD, Real.exp_neg, Real.exp_log hpos, inv_div]

/-- `lem:strip`: the exact strip identity `∫_I A_L dL = a 𝔼[w ρ̃(u)]` and the lower bound
`|𝔼_L A_L| ≥ aδ/(2W)`, `W = 2D+1`. -/
theorem bprod_strip_identity (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hcorr : δ ≤ ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖)
    (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∫ L in (-D - 1)..D, bprodA f P L (L + a)) =
        (a : ℂ) * 𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
          ((bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ) : ℂ) ∧
      a / (2 * D + 1) * (δ / 2) ≤ ‖((2 * D + 1 : ℝ)⁻¹ : ℂ) * ∫ L in (-D - 1)..D, bprodA f P L (L + a)‖ := by
  have hδ1 : δ ≤ 1 := hcorr.trans (chain_expect_norm_mul_le_one f hf4 P hPpos hP)
  obtain ⟨hD0, -⟩ := chain_D_facts hδ hδ1 hD
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  have hid : (∫ L in (-D - 1)..D, bprodA f P L (L + a)) =
        (a : ℂ) * 𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
          ((bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ) : ℂ) :=
    strip_integral_aux f (fun x => ∏ i, P i (x i)) hp (lo := -D - 1) (hi := D) (by linarith) ha0
  refine ⟨hid, ?_⟩
  rw [hid]
  obtain ⟨hρ1, hρ2, hρ3⟩ := bprod_rhoT_bounds (D := D) ha0 ha1
  have hW : 0 < 2 * D + 1 := by linarith
  -- the weight `ρ̃` removes at most the tail mass
  have htail := boundedprod_tail_abs f hf4 P hPpos hP hδ hδ1 D hD
  have hdiff : ‖𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
      (((1 - bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ)) : ℂ)‖ ≤ δ / 2 := by
    refine (RCLike.norm_expect_le (K := ℝ)).trans (le_trans (Finset.expect_le_expect fun x _ => ?_) htail)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hp x).le]
    by_cases hT : ∏ i, P i (x i) < Real.exp (-D) ∨ Real.exp D < ∏ i, P i (x i)
    · simp only [hT, ↓reduceIte]
      have h1 := hρ1 (Real.log (∏ i, P i (x i)))
      have : ‖1 - bprodRhoT D a (Real.log (∏ i, P i (x i)))‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h1.1, h1.2]
      calc ‖f x‖ * (∏ i, P i (x i)) * ‖1 - bprodRhoT D a (Real.log (∏ i, P i (x i)))‖
          ≤ ‖f x‖ * (∏ i, P i (x i)) * 1 :=
            mul_le_mul_of_nonneg_left this (by have := norm_nonneg (f x); have := hp x; positivity)
        _ = _ := mul_one _
    · simp only [hT, ↓reduceIte]
      push Not at hT
      have hmem : Real.log (∏ i, P i (x i)) ∈ Set.Icc (-D) D := by
        constructor
        · have := Real.log_le_log (Real.exp_pos _) hT.1
          rwa [Real.log_exp] at this
        · have := Real.log_le_log (hp x) hT.2
          rwa [Real.log_exp] at this
      rw [hρ3 _ hmem]; simp
  have hsplit : (𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
        ((bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ) : ℂ)) =
      (𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)) -
        𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
          (((1 - bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ)) : ℂ) := by
    rw [← Finset.expect_sub_distrib]
    refine Finset.expect_congr rfl fun x _ => ?_
    push_cast; ring
  have hlow : δ / 2 ≤ ‖𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
        ((bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ) : ℂ)‖ := by
    rw [hsplit]
    have := norm_sub_norm_le (𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ))
      (𝔼 x : ι → α, (f x * ((∏ i, P i (x i) : ℝ) : ℂ)) *
          (((1 - bprodRhoT D a (Real.log (∏ i, P i (x i))) : ℝ)) : ℂ))
    linarith
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hW.le, Real.norm_of_nonneg ha0.le]
  calc a / (2 * D + 1) * (δ / 2) = (2 * D + 1)⁻¹ * (a * (δ / 2)) := by ring
    _ ≤ _ := by gcongr


/-- the strip has volume at most `a` -/
private theorem vol_strip_le {u a : ℝ} (ha : 0 ≤ a) (S : Set ℝ) :
    (volume (Set.Icc (u - a) u ∩ S)).toReal ≤ a := by
  have h1 : volume (Set.Icc (u - a) u ∩ S) ≤ ENNReal.ofReal a := by
    calc _ ≤ volume (Set.Icc (u - a) u) := measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal a := by rw [Real.volume_Icc]; congr 1; ring
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans (by rw [ENNReal.toReal_ofReal ha])

/-- the two windows have total volume at most `2η` -/
private theorem vol_nSet_le {D η : ℝ} (hη : 0 < η) (u a : ℝ) :
    (volume (nSet u a η ∩ Set.Icc (-D - 1) D)).toReal ≤ 2 * η := by
  have hfin : ∀ A : Set ℝ, volume (A ∩ Set.Icc (-D - 1) D) ≠ ⊤ := fun A =>
    (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_Icc_lt_top).ne
  unfold nSet
  rw [Set.union_inter_distrib_right]
  have h1 := bprod_window_density (D := D) hη u 0
  have h2 := bprod_window_density (D := D) hη u a
  calc _ ≤ (volume (Set.Ioo (u - 0 - η / 2) (u - 0 + η / 2) ∩ Set.Icc (-D - 1) D) +
        volume (Set.Ioo (u - a - η / 2) (u - a + η / 2) ∩ Set.Icc (-D - 1) D)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) (measure_union_le _ _)
    _ = _ := ENNReal.toReal_add (hfin _) (hfin _)
    _ ≤ 2 * η := by linarith

/-- `Ψ` is a bounded measurable function of `L` (a step function). -/
theorem bprod_psi_measurable (f : (ι → α) → ℂ) (P : ι → α → ℝ) (D a η : ℝ) :
    Measurable (bprodPsi f P D a η) ∧ ∃ C : ℝ, ∀ L, |bprodPsi f P D a η L| ≤ C := by
  have hΨ : bprodPsi f P D a η = fun L =>
      Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖ -
        (Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L -
        cN f (fun x => ∏ i, P i (x i)) a η L := rfl
  rw [hΨ]
  refine ⟨((((cA_measurable f _ a).norm).const_mul _).sub
    ((cS_measurable f _ a).const_mul _)).sub (cN_measurable f _ a η), ?_⟩
  refine ⟨Real.exp (-D) * (𝔼 x : ι → α, ‖f x‖ * |∏ i, P i (x i)|) +
    |Real.exp a - 1| * (𝔼 x : ι → α, ‖f x‖) + 𝔼 x : ι → α, ‖f x‖, fun L => ?_⟩
  have hA := cA_bound f (fun x => ∏ i, P i (x i)) a L
  obtain ⟨hS0, hS1⟩ := cS_bound f (fun x => ∏ i, P i (x i)) a L
  obtain ⟨hN0, hN1⟩ := cN_bound f (fun x => ∏ i, P i (x i)) a η L
  have e1 : |Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖| ≤
      Real.exp (-D) * (𝔼 x : ι → α, ‖f x‖ * |∏ i, P i (x i)|) := by
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
  have e2 : |(Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L| ≤
      |Real.exp a - 1| * (𝔼 x : ι → α, ‖f x‖) := by
    rw [abs_mul, abs_of_nonneg hS0]
    exact mul_le_mul_of_nonneg_left hS1 (abs_nonneg _)
  have e3 : |cN f (fun x => ∏ i, P i (x i)) a η L| ≤ 𝔼 x : ι → α, ‖f x‖ := by
    rw [abs_of_nonneg hN0]; exact hN1
  have t1 := abs_sub (Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖ -
    (Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L) (cN f (fun x => ∏ i, P i (x i)) a η L)
  have t2 := abs_sub (Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖)
    ((Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L)
  linarith


/-- (PL), moduli first: for every `L ≤ D`, `|Φ(L)| ≥ e^{-D}|A_L| - (e^a-1)𝔼|f|1_{S_L} -
𝔼|f|1_{N_L}`. -/
theorem bprod_PL (f : (ι → α) → ℂ) (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a)
    {L D a η : ℝ} (hLD : L ≤ D) (ha : 0 < a) (hη : 0 < η) (b : ℝ → ℂ)
    (hb2 : ∀ x : ℝ, L + η / 2 ≤ x → x ≤ L + a - η / 2 → b x = 1)
    (hb3 : ∀ x : ℝ, x ≤ L - η / 2 ∨ L + a + η / 2 ≤ x → b x = 0)
    (hb4 : ∀ x : ℝ, 0 ≤ b x ∧ b x ≤ 1) :
    Real.exp (-D) * ‖bprodA f P L (L + a)‖ -
        (Real.exp a - 1) * (𝔼 x : ι → α, ‖f x‖ *
          (if Real.exp L ≤ ∏ i, P i (x i) ∧ ∏ i, P i (x i) ≤ Real.exp (L + a) then (1 : ℝ) else 0)) -
        𝔼 x : ι → α, ‖f x‖ *
          (if |Real.log (∏ i, P i (x i)) - L| < η / 2 ∨
              |Real.log (∏ i, P i (x i)) - (L + a)| < η / 2 then (1 : ℝ) else 0) ≤
      ‖𝔼 x : ι → α, f x * b (Real.log (∏ i, P i (x i)))‖ :=
  PL_aux f (fun x => ∏ i, P i (x i)) (fun x => Finset.prod_pos fun i _ => hPpos i (x i))
    hLD ha hη b hb2 hb3 hb4

/-- (AVG): `W · 𝔼_L Ψ ≥ aδ³/32 - (e^a-1)a - 2η`, as an interval integral. -/
theorem bprod_avg_bound (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hcorr : δ ≤ ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖)
    (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) {a η : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hη : 0 < η) :
    a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η ≤ ∫ L in (-D - 1)..D, bprodPsi f P D a η L := by
  have hδ1 : δ ≤ 1 := hcorr.trans (chain_expect_norm_mul_le_one f hf4 P hPpos hP)
  obtain ⟨hD0, hexp⟩ := chain_D_facts hδ hδ1 hD
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  have hlh : -D - 1 ≤ D := by linarith
  have hW : 0 < 2 * D + 1 := by linarith
  obtain ⟨-, hstrip⟩ := bprod_strip_identity f hf4 P hPpos hP hδ hcorr D hD ha0 ha1
  have hconv : ∀ g : ℝ → ℝ, (∫ L in (-D - 1)..D, g L) = ∫ L in Set.Icc (-D - 1) D, g L := by
    intro g
    rw [intervalIntegral.integral_of_le hlh, ← integral_Icc_eq_integral_Ioc]
  have hconvC : (∫ L in (-D - 1)..D, bprodA f P L (L + a)) =
      ∫ L in Set.Icc (-D - 1) D, cA f (fun x => ∏ i, P i (x i)) a L := by
    rw [intervalIntegral.integral_of_le hlh, ← integral_Icc_eq_integral_Ioc]; rfl
  have hΨ : ∀ L, bprodPsi f P D a η L =
      Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖ -
        (Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L -
        cN f (fun x => ∏ i, P i (x i)) a η L := fun L => rfl
  simp_rw [hΨ]
  rw [hconv]
  -- integrability
  have hIA : IntegrableOn (cA f (fun x => ∏ i, P i (x i)) a) (Set.Icc (-D - 1) D) := by
    rw [cA_eq f _ hp a]
    exact integrable_expect_ind _ _ fun x => measurableSet_Icc
  have hIS : IntegrableOn (cS f (fun x => ∏ i, P i (x i)) a) (Set.Icc (-D - 1) D) := by
    rw [cS_eq f _ hp a]
    exact integrable_expect_ind _ _ fun x => measurableSet_Icc
  have hIN : IntegrableOn (cN f (fun x => ∏ i, P i (x i)) a η) (Set.Icc (-D - 1) D) := by
    rw [cN_eq f _ a η]
    exact integrable_expect_ind _ _ fun x => nSet_measurable _ _ _
  have hsplit : (∫ L in Set.Icc (-D - 1) D,
      (Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖ -
        (Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L -
        cN f (fun x => ∏ i, P i (x i)) a η L)) =
      Real.exp (-D) * (∫ L in Set.Icc (-D - 1) D, ‖cA f (fun x => ∏ i, P i (x i)) a L‖) -
        (Real.exp a - 1) * (∫ L in Set.Icc (-D - 1) D, cS f (fun x => ∏ i, P i (x i)) a L) -
        ∫ L in Set.Icc (-D - 1) D, cN f (fun x => ∏ i, P i (x i)) a η L := by
    have hI0 : Integrable (fun L => Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖)
        (volume.restrict (Set.Icc (-D - 1) D)) := hIA.norm.const_mul _
    have hI1 : Integrable (fun L => (Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L)
        (volume.restrict (Set.Icc (-D - 1) D)) := hIS.const_mul _
    have hI2 : Integrable (fun L => Real.exp (-D) * ‖cA f (fun x => ∏ i, P i (x i)) a L‖ -
        (Real.exp a - 1) * cS f (fun x => ∏ i, P i (x i)) a L)
        (volume.restrict (Set.Icc (-D - 1) D)) := hI0.sub hI1
    rw [integral_sub hI2 hIN, integral_sub hI0 hI1, integral_const_mul, integral_const_mul]
  rw [hsplit]
  -- (1) the `A`-term
  have hJ : a * (δ / 2) ≤ ‖∫ L in Set.Icc (-D - 1) D, cA f (fun x => ∏ i, P i (x i)) a L‖ := by
    rw [← hconvC]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hW.le] at hstrip
    rw [div_mul_eq_mul_div, div_eq_inv_mul] at hstrip
    exact le_of_mul_le_mul_left hstrip (inv_pos.2 hW)
  have hA : a * (δ / 2) ≤ ∫ L in Set.Icc (-D - 1) D, ‖cA f (fun x => ∏ i, P i (x i)) a L‖ :=
    hJ.trans (norm_integral_le_integral_norm _)
  -- (2) the `S`-term
  have hf1 := chain_expect_norm_le_one f hf4
  have hS : (∫ L in Set.Icc (-D - 1) D, cS f (fun x => ∏ i, P i (x i)) a L) ≤ a := by
    rw [cS_eq f _ hp a, integral_expect_ind (fun x => ‖f x‖)
      (fun x => Set.Icc (Real.log (∏ i, P i (x i)) - a) (Real.log (∏ i, P i (x i))))
      (fun x => measurableSet_Icc)]
    calc _ ≤ 𝔼 x : ι → α, a * ‖f x‖ := by
          refine Finset.expect_le_expect fun x _ => ?_
          have h1 := vol_strip_le (u := Real.log (∏ i, P i (x i))) ha0.le (Set.Icc (-D - 1) D)
          have h2 := norm_nonneg (f x)
          simp only [RCLike.ofReal_real_eq_id, id]
          exact mul_le_mul_of_nonneg_right h1 h2
      _ = a * 𝔼 x : ι → α, ‖f x‖ := by rw [Finset.mul_expect]
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hf1 ha0.le
      _ = a := mul_one a
  -- (3) the `N`-term
  have hN : (∫ L in Set.Icc (-D - 1) D, cN f (fun x => ∏ i, P i (x i)) a η L) ≤ 2 * η := by
    rw [cN_eq f _ a η, integral_expect_ind (fun x => ‖f x‖)
      (fun x => nSet (Real.log (∏ i, P i (x i))) a η) (fun x => nSet_measurable _ _ _)]
    calc _ ≤ 𝔼 x : ι → α, (2 * η) * ‖f x‖ := by
          refine Finset.expect_le_expect fun x _ => ?_
          have h1 := vol_nSet_le (D := D) hη (Real.log (∏ i, P i (x i))) a
          have h2 := norm_nonneg (f x)
          simp only [RCLike.ofReal_real_eq_id, id]
          exact mul_le_mul_of_nonneg_right h1 h2
      _ = (2 * η) * 𝔼 x : ι → α, ‖f x‖ := by rw [Finset.mul_expect]
      _ ≤ (2 * η) * 1 := mul_le_mul_of_nonneg_left hf1 (by linarith)
      _ = 2 * η := mul_one _
  have hexp0 : 0 ≤ Real.exp (-D) := (Real.exp_pos _).le
  have hea : 0 ≤ Real.exp a - 1 := by linarith [Real.add_one_le_exp a]
  have e1 : Real.exp (-D) * (a * (δ / 2)) ≤
      Real.exp (-D) * ∫ L in Set.Icc (-D - 1) D, ‖cA f (fun x => ∏ i, P i (x i)) a L‖ :=
    mul_le_mul_of_nonneg_left hA hexp0
  have e2 : (Real.exp a - 1) * (∫ L in Set.Icc (-D - 1) D, cS f (fun x => ∏ i, P i (x i)) a L) ≤
      (Real.exp a - 1) * a := mul_le_mul_of_nonneg_left hS hea
  have e3 : Real.exp (-D) * (a * (δ / 2)) = a * δ ^ 3 / 32 := by rw [hexp]; ring
  linarith

/-- `prop:avg`: there is one `L ∈ [-D-1, D]` serving every smoothing function `b` with (E2)-(E4). -/
theorem bprod_avg_exists (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hcorr : δ ≤ ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖)
    (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) {a η : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hη : 0 < η) :
    ∃ L ∈ Set.Icc (-D - 1) D, ∀ b : ℝ → ℂ,
      (∀ x : ℝ, L + η / 2 ≤ x → x ≤ L + a - η / 2 → b x = 1) →
      (∀ x : ℝ, x ≤ L - η / 2 ∨ L + a + η / 2 ≤ x → b x = 0) →
      (∀ x : ℝ, 0 ≤ b x ∧ b x ≤ 1) →
      (a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η) / (2 * D + 1) ≤
        ‖𝔼 x : ι → α, f x * b (Real.log (∏ i, P i (x i)))‖ := by
  have hδ1 : δ ≤ 1 := hcorr.trans (chain_expect_norm_mul_le_one f hf4 P hPpos hP)
  obtain ⟨hD0, -⟩ := chain_D_facts hδ hδ1 hD
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  have hlh : -D - 1 ≤ D := by linarith
  have hW : 0 < 2 * D + 1 := by linarith
  have havg := bprod_avg_bound f hf4 P hPpos hP hδ hcorr D hD ha0 ha1 hη
  have hΨm := (bprod_psi_measurable f P D a η).1
  obtain ⟨C, hC⟩ := (bprod_psi_measurable f P D a η).2
  have hint : IntegrableOn (bprodPsi f P D a η) (Set.Icc (-D - 1) D) :=
    integrableOn_of_bdd hΨm hC _ measure_Icc_lt_top
  have hvol : volume (Set.Icc (-D - 1) D) = ENNReal.ofReal (2 * D + 1) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hne0 : volume (Set.Icc (-D - 1) D) ≠ 0 := by
    rw [hvol]; simpa using hW
  have hnetop : volume (Set.Icc (-D - 1) D) ≠ ⊤ := measure_Icc_lt_top.ne
  obtain ⟨L, hL, hLle⟩ := exists_setAverage_le hne0 hnetop hint
  refine ⟨L, hL, fun b hb2 hb3 hb4 => ?_⟩
  have hPL := bprod_PL f P hPpos (L := L) (D := D) (a := a) (η := η) hL.2 ha0 hη b hb2 hb3 hb4
  have hΨL : bprodPsi f P D a η L ≤ ‖𝔼 x : ι → α, f x * b (Real.log (∏ i, P i (x i)))‖ := hPL
  refine le_trans ?_ (le_trans hLle hΨL)
  rw [setAverage_eq, measureReal_def, hvol, ENNReal.toReal_ofReal hW.le, smul_eq_mul]
  have hconv : (∫ L in (-D - 1)..D, bprodPsi f P D a η L) =
      ∫ L in Set.Icc (-D - 1) D, bprodPsi f P D a η L := by
    rw [intervalIntegral.integral_of_le hlh, ← integral_Icc_eq_integral_Ioc]
  rw [hconv] at havg
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left havg (inv_pos.2 hW).le

end Chain

end TrackB
end RestrictedPolynomials
end
