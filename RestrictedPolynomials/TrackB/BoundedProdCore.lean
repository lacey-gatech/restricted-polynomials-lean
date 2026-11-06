module

public import RestrictedPolynomials.TrackB.BoundedProdChain
public import RestrictedPolynomials.Frozen.FinProbCExpect

/-!
# Track B: the top results of Supplement F

Source: Supplement F.

* `boundedprod_core` (`thm:core`);
* `boundedprod_general` (`thm:general`);
* `n1_near_one` (`lem:N1`, constant `20`);
* `boundedprod_near_one` (`prop:near-one`);
* `boundedprod_one_bounded` (`thm:bounded1`): input (I4) of Supplement D with `C_b = 1400`.

All proof helpers are `private`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexOrder
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Helpers
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `‖𝔼 f P‖ ≤ 1` from `𝔼|f|⁴ ≤ 1` and `𝔼 P² ≤ 1` (re-proved: the built helper is private). -/
private theorem core_expect_norm_mul_le_one (f : (ι → α) → ℂ)
    (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1) :
    ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (ι → α) with hne | hne
  · simp [Finset.univ_eq_empty]
  have hp : ∀ x : ι → α, 0 < ∏ i, P i (x i) :=
    fun x => Finset.prod_pos fun i _ => hPpos i (x i)
  have hsq : 𝔼 x : ι → α, (∏ i, P i (x i)) ^ 2 ≤ 1 := by
    simp_rw [← Finset.prod_pow]
    rw [bprod_expect_prod_sq P]
    exact Finset.prod_le_one₀ (fun i _ => Finset.expect_nonneg fun a _ => sq_nonneg _)
      fun i _ => hP i
  calc _ ≤ 𝔼 x : ι → α, ‖f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖ := RCLike.norm_expect_le (K := ℝ)
    _ ≤ 𝔼 x : ι → α, (1 / 4 + ‖f x‖ ^ 4 / 4 + (∏ i, P i (x i)) ^ 2 / 2) := by
      refine Finset.expect_le_expect fun x _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp x).le]
      have hF := norm_nonneg (f x)
      nlinarith [sq_nonneg (‖f x‖ - ∏ i, P i (x i)), sq_nonneg (‖f x‖ ^ 2 - 1)]
    _ = 1 / 4 + (𝔼 x : ι → α, ‖f x‖ ^ 4) / 4 + (𝔼 x : ι → α, (∏ i, P i (x i)) ^ 2) / 2 := by
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Finset.expect_const univ_nonempty,
        ← Finset.expect_div, ← Finset.expect_div]
    _ ≤ 1 / 4 + 1 / 4 + 1 / 2 := by gcongr
    _ = 1 := by norm_num

/-- a nonempty sample space from a positive correlation. -/
private theorem nonempty_of_corr (F : (ι → α) → ℂ) (P : ι → α → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hcorr : δ ≤ ‖𝔼 x : ι → α, F x * ∏ i, P i (x i)‖) : Nonempty (ι → α) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : (𝔼 x : ι → α, F x * ∏ i, P i (x i)) = 0 := by
    simp [Finset.univ_eq_empty]
  rw [this] at hcorr
  simp at hcorr
  linarith

end Helpers

section Core
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem norm_phase (θ t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((θ : ℂ) * (t : ℂ)))‖ = 1 := by
  have : 2 * Real.pi * Complex.I * ((θ : ℂ) * (t : ℂ)) = ((2 * Real.pi * (θ * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- the Fourier-side exchange `𝔼 f (b∘u) = ∫ c(θ) 𝔼 f e^{2πiθu} dθ` (finite sum, integrable `c`). -/
private theorem core_exchange {X : Type} [Fintype X] (f : X → ℂ) (u : X → ℝ) (c : ℝ → ℂ)
    (hc : Integrable c) :
    (𝔼 x : X, f x * bprodFourierSynth c (u x)) =
      ∫ θ : ℝ, c θ * 𝔼 x : X, f x * Complex.exp (2 * Real.pi * Complex.I * ((θ : ℂ) * (u x : ℂ))) := by
  have hint : ∀ x : X, Integrable (fun θ : ℝ =>
      c θ * Complex.exp (2 * Real.pi * Complex.I * ((θ : ℂ) * (u x : ℂ)))) := by
    intro x
    refine hc.norm.mono' (hc.1.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (ae_of_all _ fun θ => ?_)
    rw [norm_mul, norm_phase, mul_one]
  have h1 : ∀ θ : ℝ, c θ * (𝔼 x : X, f x * Complex.exp (2 * Real.pi * Complex.I *
      ((θ : ℂ) * (u x : ℂ)))) = (∑ x : X, f x * (c θ * Complex.exp (2 * Real.pi * Complex.I *
      ((θ : ℂ) * (u x : ℂ))))) / (Fintype.card X : ℂ) := by
    intro θ
    rw [Fintype.expect_eq_sum_div_card, mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  simp_rw [h1]
  rw [integral_div, integral_finsetSum _ (fun x _ => (hint x).const_mul (f x)),
    Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_const_mul]
  rfl

private theorem core_h_cont {X : Type} [Fintype X] (f : X → ℂ) (u : X → ℝ) :
    Continuous fun θ : ℝ => 𝔼 x : X, f x * Complex.exp (2 * Real.pi * Complex.I *
      ((θ : ℂ) * (u x : ℂ))) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  exact Continuous.div_const (continuous_finsetSum _ fun x _ => by fun_prop) _

private theorem core_h_bdd {X : Type} [Fintype X] (f : X → ℂ) (u : X → ℝ) :
    ∃ B : ℝ, ∀ θ : ℝ, ‖𝔼 x : X, f x * Complex.exp (2 * Real.pi * Complex.I *
      ((θ : ℂ) * (u x : ℂ)))‖ ≤ B := by
  refine ⟨𝔼 x : X, ‖f x‖, fun θ => ?_⟩
  refine (RCLike.norm_expect_le (K := ℝ)).trans (le_of_eq ?_)
  exact Finset.expect_congr rfl fun x _ => by rw [norm_mul, norm_phase, mul_one]

private theorem core_arith {δ D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hW : 0 < 2 * D + 1) :
    let a := δ ^ 3 / 1000
    let η := δ ^ 6 / 400000
    0 < (a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η) / (2 * D + 1) ∧
    δ ^ (15 / 2 : ℝ) / (2 * 10 ^ 6 * (2 * D + 1)) ≤
      (a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η) / (2 * D + 1) / (a / η) ^ (1 / 2 : ℝ) := by
  intro a η
  have hd3 : 0 < δ ^ 3 := pow_pos hδ 3
  have hd6 : 0 < δ ^ 6 := pow_pos hδ 6
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by
    have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
    show δ ^ 3 / 1000 ≤ 1 / 2
    linarith
  have hexp : Real.exp a - 1 ≤ 2 * a := by
    have h := Real.exp_bound_div_one_sub_of_interval' ha0 (by linarith : a < 1)
    have h2 : 1 / (1 - a) ≤ 1 + 2 * a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hnum : δ ^ 6 / 100000 ≤ a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η := by
    have h1 : (Real.exp a - 1) * a ≤ 2 * a * a := mul_le_mul_of_nonneg_right hexp ha0.le
    have h2 : a * a = δ ^ 6 / 10 ^ 6 := by
      show δ ^ 3 / 1000 * (δ ^ 3 / 1000) = _
      ring
    have h3 : a * δ ^ 3 / 32 = δ ^ 6 / 32000 := by
      show δ ^ 3 / 1000 * δ ^ 3 / 32 = _
      ring
    have h4 : η = δ ^ 6 / 400000 := rfl
    rw [h3, h4]
    nlinarith
  have hnum0 : 0 < a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η := by
    have : 0 < δ ^ 6 / 100000 := by positivity
    linarith
  refine ⟨div_pos hnum0 hW, ?_⟩
  set t : ℝ := δ ^ (3 / 2 : ℝ) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hδ _
  have htt : t * t = δ ^ 3 := by
    rw [ht, ← Real.rpow_add hδ]
    norm_num
  have h15 : δ ^ (15 / 2 : ℝ) = δ ^ 6 * t := by
    rw [ht, ← Real.rpow_natCast δ 6, ← Real.rpow_add hδ]
    norm_num
  have hM : (a / η) ^ (1 / 2 : ℝ) = 20 / t := by
    have hsq : (20 / t) ^ 2 = a / η := by
      rw [div_pow, sq t, htt]
      show _ = δ ^ 3 / 1000 / (δ ^ 6 / 400000)
      have : δ ^ 6 = δ ^ 3 * δ ^ 3 := by ring
      rw [this]
      field_simp
      norm_num
    rw [← hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rw [hM, h15]
  have e : (a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η) / (2 * D + 1) / (20 / t) =
      (a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η) * t / (20 * (2 * D + 1)) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hnum (mul_pos htpos hW).le
  nlinarith

/-- Theorem `thm:core` (Supplement F). -/
theorem boundedprod_core (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℝ) (hPpos : ∀ i a, 0 < P i a) (hP : ∀ i, 𝔼 a : α, P i a ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hcorr : δ ≤ ‖𝔼 x : ι → α, f x * ((∏ i, P i (x i) : ℝ) : ℂ)‖)
    (D : ℝ) (hD : D = Real.log (16 / δ ^ 2)) :
    ∃ θ : ℝ, δ ^ (15 / 2 : ℝ) / (2 * 10 ^ 6 * (2 * D + 1)) ≤
      ‖𝔼 x : ι → α, f x * Complex.exp (2 * Real.pi * Complex.I *
        ((θ : ℂ) * ((Real.log (∏ i, P i (x i)) : ℝ) : ℂ)))‖ := by
  have hδ1 : δ ≤ 1 := hcorr.trans (core_expect_norm_mul_le_one f hf4 P hPpos hP)
  have hD0 : 0 < D := by
    rw [hD]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hW : 0 < 2 * D + 1 := by linarith
  obtain ⟨hσ, hfin⟩ := core_arith hδ hδ1 hW
  set a : ℝ := δ ^ 3 / 1000 with ha
  set η : ℝ := δ ^ 6 / 400000 with hη
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
    rw [ha]; linarith
  have hη0 : 0 < η := by positivity
  obtain ⟨L, -, hb⟩ := bprod_avg_exists f hf4 P hPpos hP hδ hcorr D hD ha0 ha1 hη0
  obtain ⟨c, hc, hcM, hb2, hb3, hb4⟩ :=
    bprod_exists_smoothed_indicator (L := L) (R := L + a) (by linarith) hη0
  have hbound := hb (bprodFourierSynth c) hb2 hb3 hb4
  rw [core_exchange f (fun x => Real.log (∏ i, P i (x i))) c hc] at hbound
  have hLa : L + a - L = a := by ring
  rw [hLa] at hcM
  have hM0 : 0 < (a / η) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨θ, hθ⟩ := bprod_choose_theta (c := c)
    (h := fun θ => 𝔼 x : ι → α, f x * Complex.exp (2 * Real.pi * Complex.I *
      ((θ : ℂ) * ((Real.log (∏ i, P i (x i)) : ℝ) : ℂ)))) hc
    (core_h_cont f _) (core_h_bdd f _) hM0 hcM
    (s := (a * δ ^ 3 / 32 - (Real.exp a - 1) * a - 2 * η) / (2 * D + 1) / (a / η) ^ (1 / 2 : ℝ))
    (div_pos hσ hM0)
    (by rw [div_mul_cancel₀ _ hM0.ne']; exact hbound)
  exact ⟨θ, hfin.trans hθ⟩

omit [DecidableEq ι] in
private theorem phase_prod (θ : ℝ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∏ i, Complex.exp (2 * Real.pi * Complex.I * ((θ : ℂ) * ((Real.log (r i) : ℝ) : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((θ : ℂ) * ((Real.log (∏ i, r i) : ℝ) : ℂ))) := by
  rw [← Complex.exp_sum, Real.log_prod (fun i _ => (hr i).ne')]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]

private theorem bprodB_arg {δ₀ : ℝ} (h0 : 0 < δ₀) :
    (δ₀ / 2) ^ (15 / 2 : ℝ) / (2 * 10 ^ 6 * (2 * Real.log (16 / (δ₀ / 2) ^ 2) + 1)) =
      bprodB δ₀ := by
  unfold bprodB
  have : (16 / (δ₀ / 2) ^ 2 : ℝ) = (8 / δ₀) ^ 2 := by
    field_simp
    ring
  rw [this, Real.log_pow]
  push_cast
  ring_nf

/-- Theorem `thm:general` (Supplement F). -/
theorem boundedprod_general (f : (ι → α) → ℂ) (hf4 : 𝔼 x : ι → α, ‖f x‖ ^ 4 ≤ 1)
    (P : ι → α → ℂ) (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) {δ₀ : ℝ} (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (hcorr : δ₀ ≤ ‖𝔼 x : ι → α, f x * ∏ i, P i (x i)‖) :
    ∃ P' : ι → α → ℂ, (∀ i a, ‖P' i a‖ = 1) ∧
      bprodB δ₀ ≤ ‖𝔼 x : ι → α, f x * ∏ i, P' i (x i)‖ := by
  have _ := hδ1
  obtain ⟨Q, R, hQ, hRpos, hR2, hcor', hnorm, hmul⟩ :=
    boundedprod_reduce_positive f P hP (δ := δ₀ / 2) (by linarith)
  have hf4' : 𝔼 x : ι → α, ‖f x * ∏ i, Q i (x i)‖ ^ 4 ≤ 1 := by
    have : (𝔼 x : ι → α, ‖f x * ∏ i, Q i (x i)‖ ^ 4) = 𝔼 x : ι → α, ‖f x‖ ^ 4 :=
      Finset.expect_congr rfl fun x _ => by rw [hnorm x]
    rw [this]; exact hf4
  have hcor'' : δ₀ / 2 ≤ ‖𝔼 x : ι → α, (f x * ∏ i, Q i (x i)) * ((∏ i, R i (x i) : ℝ) : ℂ)‖ := by
    simpa only [Complex.ofReal_prod] using hcor'
  obtain ⟨θ, hθ⟩ := boundedprod_core (fun x => f x * ∏ i, Q i (x i)) hf4' R hRpos hR2
    (δ := δ₀ / 2) (by positivity) hcor'' _ rfl
  refine ⟨fun i a => Q i a * Complex.exp (2 * Real.pi * Complex.I *
    ((θ : ℂ) * ((Real.log (R i a) : ℝ) : ℂ))), ?_, ?_⟩
  · intro i a
    rw [norm_mul, hQ, norm_phase, mul_one]
  · rw [hmul (fun i a => Complex.exp (2 * Real.pi * Complex.I *
      ((θ : ℂ) * ((Real.log (R i a) : ℝ) : ℂ))))]
    have : (𝔼 x : ι → α, (f x * ∏ i, Q i (x i)) * ∏ i, Complex.exp (2 * Real.pi * Complex.I *
        ((θ : ℂ) * ((Real.log (R i (x i)) : ℝ) : ℂ)))) =
        𝔼 x : ι → α, (f x * ∏ i, Q i (x i)) * Complex.exp (2 * Real.pi * Complex.I *
          ((θ : ℂ) * ((Real.log (∏ i, R i (x i)) : ℝ) : ℂ))) :=
      Finset.expect_congr rfl fun x _ => by rw [phase_prod θ (fun i => R i (x i)) (fun i => hRpos _ _)]
    rw [this, ← bprodB_arg hδ0]
    exact hθ

end Core

section NearOne

/-- pointwise inequality behind Lemma N1 (the Chebyshev and Cauchy-Schwarz steps combined). -/
private theorem n1_pointwise {x a R : ℝ} (hxa : x ≤ a) (hxa' : -a ≤ x) (ha1 : a ≤ 1) (hR : 0 ≤ R) :
    2 * x * R - 9 * R ^ 2 + 16 * R - 8 ≤ x := by
  have ha0 : 0 ≤ a := by linarith
  have hg : 0 ≤ a - x := sub_nonneg.2 hxa
  by_cases hR2 : 1 / 2 ≤ R
  · nlinarith [mul_nonneg hg (by linarith : 0 ≤ 2 * R - 1), sq_nonneg (a - R),
      mul_nonneg ha0 (sub_nonneg.2 ha1), sq_nonneg (R - 1)]
  · push Not at hR2
    have h8 : 2 ≤ 8 * (R - 1) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hg hR, sq_nonneg (a - R), mul_nonneg ha0 (sub_nonneg.2 ha1)]

/-- Lemma N1 (Supplement F, `lem:N1`, constant `20`) on a finite probability space. -/
theorem n1_near_one {Y : Type} [Fintype Y] (π : FinProb Y) (F : Y → ℂ) (hF : ∀ y, ‖F y‖ ≤ 1)
    (R : Y → ℝ) (hR : ∀ y, 0 ≤ R y) (hR2 : ∑ y, π.prob y * R y ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hcorr : 1 - ε ≤ (π.cexpect fun y => F y * (R y : ℂ)).re) :
    1 - 20 * ε ≤ (π.cexpect F).re := by
  have _ := hε1
  have hre : ∀ G : Y → ℂ, (π.cexpect G).re = ∑ y, π.prob y * (G y).re := by
    intro G
    simp [FinProb.cexpect, Complex.re_sum, Complex.mul_re]
  rw [hre] at hcorr ⊢
  have hw := π.nonneg
  have hs := π.sum_eq_one
  have hfR : ∀ y, (F y * (R y : ℂ)).re = (F y).re * R y := by
    intro y; simp [Complex.mul_re]
  simp_rw [hfR] at hcorr
  have hpt : ∀ y, 2 * (F y).re * R y - 9 * R y ^ 2 + 16 * R y - 8 ≤ (F y).re := fun y =>
    n1_pointwise (Complex.re_le_norm (F y)) (by linarith [neg_le_of_abs_le (Complex.abs_re_le_norm (F y))]) (hF y) (hR y)
  have hsum : ∑ y, π.prob y * (2 * (F y).re * R y - 9 * R y ^ 2 + 16 * R y - 8) ≤
      ∑ y, π.prob y * (F y).re :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hw y)
  have hexp : ∑ y, π.prob y * (2 * (F y).re * R y - 9 * R y ^ 2 + 16 * R y - 8) =
      2 * ∑ y, π.prob y * ((F y).re * R y) - 9 * ∑ y, π.prob y * R y ^ 2 +
        16 * ∑ y, π.prob y * R y - 8 := by
    have h1 : ∀ y, π.prob y * (2 * (F y).re * R y - 9 * R y ^ 2 + 16 * R y - 8) =
        2 * (π.prob y * ((F y).re * R y)) - 9 * (π.prob y * R y ^ 2) +
          16 * (π.prob y * R y) - 8 * π.prob y := fun y => by ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hs]
    ring
  have hRX : ∑ y, π.prob y * ((F y).re * R y) ≤ ∑ y, π.prob y * R y := by
    refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hw y)
    have := Complex.re_le_norm (F y)
    have := hF y
    nlinarith [hR y]
  linarith

end NearOne

section NearOneAux

/-- the uniform probability law on a nonempty finite type. -/
private def unifProb (Y : Type) [Fintype Y] [Nonempty Y] : FinProb Y where
  prob _ := (Fintype.card Y : ℝ)⁻¹
  nonneg _ := inv_nonneg.2 (Nat.cast_nonneg _)
  sum_eq_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

private theorem unifProb_cexpect {Y : Type} [Fintype Y] [Nonempty Y] (G : Y → ℂ) :
    (unifProb Y).cexpect G = 𝔼 y, G y := by
  rw [Fintype.expect_eq_sum_div_card, FinProb.cexpect, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [unifProb, div_eq_inv_mul]

private theorem unifProb_sum_sq {Y : Type} [Fintype Y] [Nonempty Y] (R : Y → ℝ) :
    ∑ y, (unifProb Y).prob y * R y ^ 2 = 𝔼 y, R y ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [unifProb, div_eq_inv_mul]

variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

end NearOneAux

section NearOne2
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem near_one_numerics {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 60) :
    (1 - ε) ^ 60 ≤ 1 - 20 * ε ∧ (1 - ε) ^ 1400 ≤ (1 - ε) ^ 60 := by
  have h1ε : 0 ≤ 1 - ε := by linarith
  refine ⟨?_, pow_le_pow_of_le_one h1ε (by linarith) (by norm_num)⟩
  have hb : 1 + 60 * ε ≤ (1 + ε) ^ 60 := by
    have := one_add_mul_le_pow (a := ε) (by linarith) 60
    simpa using this
  have hq : (1 - ε) ^ 60 * (1 + ε) ^ 60 ≤ 1 := by
    rw [← mul_pow]
    refine pow_le_one₀ (mul_nonneg h1ε (by linarith)) ?_
    nlinarith
  have hq0 : 0 ≤ (1 - ε) ^ 60 := pow_nonneg h1ε _
  have h2 : (1 - ε) ^ 60 * (1 + 60 * ε) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hb hq0).trans hq
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos (sub_pos.2 hcon) (by linarith : (0 : ℝ) < 1 + 60 * ε)]

omit [Fintype α] [Fintype ι] [DecidableEq ι] in
/-- polar decomposition `P = Q R`, `|Q| = 1`, `R = |P|`. -/
private theorem polar_exists (P : ι → α → ℂ) :
    ∃ (Q : ι → α → ℂ) (R : ι → α → ℝ), (∀ i a, ‖Q i a‖ = 1) ∧ (∀ i a, R i a = ‖P i a‖) ∧
      ∀ i a, P i a = Q i a * (R i a : ℂ) := by
  refine ⟨fun i a => if P i a = 0 then 1 else P i a / (‖P i a‖ : ℂ), fun i a => ‖P i a‖,
    ?_, fun _ _ => rfl, ?_⟩
  · intro i a
    by_cases h : P i a = 0
    · simp [h]
    · simp [h]
  · intro i a
    by_cases h : P i a = 0
    · simp [h]
    · have : (‖P i a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
      simp only [h, ite_false]
      field_simp

private theorem exists_phase {z : ℂ} (hz : z ≠ 0) : ∃ φ : ℂ, ‖φ‖ = 1 ∧ φ * z = (‖z‖ : ℂ) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine ⟨(starRingEnd ℂ) z / (‖z‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, RCLike.norm_conj, Complex.norm_real, norm_norm]
    exact div_self hzpos.ne'
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
    rw [div_mul_eq_mul_div, Complex.conj_mul']
    field_simp

private theorem near_one_core [Nonempty (ι → α)] [Nonempty ι] (F : (ι → α) → ℂ)
    (hF : ∀ x, ‖F x‖ ≤ 1)
    (Q : ι → α → ℂ) (R : ι → α → ℝ) (hQ : ∀ i a, ‖Q i a‖ = 1) (hR0 : ∀ i a, 0 ≤ R i a)
    (hR2 : ∀ i, 𝔼 a : α, R i a ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (φ : ℂ) (hφ : ‖φ‖ = 1)
    (hcorr : 1 - ε ≤ (φ * 𝔼 x : ι → α, (F x * ∏ i, Q i (x i)) * ∏ i, (R i (x i) : ℂ)).re) :
    1 - 20 * ε ≤ (𝔼 x : ι → α, φ * (F x * ∏ i, Q i (x i))).re := by
  have hF1 : ∀ x : ι → α, ‖φ * (F x * ∏ i, Q i (x i))‖ ≤ 1 := by
    intro x
    rw [norm_mul, norm_mul, hφ, norm_prod]
    simp only [hQ, Finset.prod_const_one, mul_one, one_mul]
    exact hF x
  have hRp0 : ∀ x : ι → α, 0 ≤ ∏ i, R i (x i) := fun x => Finset.prod_nonneg fun i _ => hR0 _ _
  have hRsum : ∑ y : ι → α, (unifProb (ι → α)).prob y * (∏ i, R i (y i)) ^ 2 ≤ 1 := by
    rw [unifProb_sum_sq]
    simp_rw [← Finset.prod_pow]
    rw [bprod_expect_prod_sq R]
    exact Finset.prod_le_one₀ (fun i _ => Finset.expect_nonneg fun a _ => sq_nonneg _)
      fun i _ => hR2 i
  have hn1 := n1_near_one (unifProb (ι → α)) (fun x => φ * (F x * ∏ i, Q i (x i))) hF1
    (fun x => ∏ i, R i (x i)) hRp0 hRsum hε0 hε1
    (by
      rw [unifProb_cexpect]
      have : (𝔼 x : ι → α, φ * (F x * ∏ i, Q i (x i)) * (((∏ i, R i (x i) : ℝ)) : ℂ)) =
          φ * 𝔼 x : ι → α, (F x * ∏ i, Q i (x i)) * ∏ i, (R i (x i) : ℂ) := by
        rw [Finset.mul_expect]
        refine Finset.expect_congr rfl fun x _ => ?_
        rw [Complex.ofReal_prod]; ring
      rw [this]
      exact hcorr)
  rwa [unifProb_cexpect] at hn1

/-- Proposition `prop:near-one` (Supplement F). -/
theorem boundedprod_near_one [Nonempty ι] (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (P : ι → α → ℂ) (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 60)
    (hcorr : 1 - ε ≤ ‖𝔼 x : ι → α, F x * ∏ i, P i (x i)‖) :
    ∃ P' : ι → α → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
      1 - 20 * ε ≤ ‖𝔼 x : ι → α, F x * ∏ i, P' i (x i)‖ ∧ (1 - ε) ^ 60 ≤ 1 - 20 * ε ∧
        (1 - ε) ^ 1400 ≤ (1 - ε) ^ 60 := by
  have hε1' : ε ≤ 1 := by linarith
  obtain ⟨hnum1, hnum2⟩ := near_one_numerics hε0 hε1
  have hne : Nonempty (ι → α) := nonempty_of_corr F P (by linarith : 0 < 1 - ε) hcorr
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨Q, R, hQ, hRP, hPQR⟩ := polar_exists P
  have hR0 : ∀ i a, 0 ≤ R i a := fun i a => by rw [hRP]; exact norm_nonneg _
  have hR2 : ∀ i, 𝔼 a : α, R i a ^ 2 ≤ 1 := fun i => by simpa [hRP] using hP i
  have hz : (𝔼 x : ι → α, (F x * ∏ i, Q i (x i)) * ∏ i, (R i (x i) : ℂ)) =
      𝔼 x : ι → α, F x * ∏ i, P i (x i) := by
    refine Finset.expect_congr rfl fun x _ => ?_
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (hPQR i (x i)).symm
  have hzpos : 0 < ‖𝔼 x : ι → α, F x * ∏ i, P i (x i)‖ := by linarith
  obtain ⟨φ, hφ, hφz⟩ := exists_phase (norm_pos_iff.1 hzpos)
  have _ := hne
  have hmain := near_one_core F hF Q R hQ hR0 hR2 hε0 hε1' φ hφ
    (by rw [hz, hφz, Complex.ofReal_re]; exact hcorr)
  refine ⟨fun i a => (if i = i0 then φ else 1) * Q i a, ?_, ?_, hnum1, hnum2⟩
  · intro i a
    rw [norm_mul, hQ, mul_one]
    split_ifs
    · exact hφ.le
    · simp
  · have hprod : ∀ x : ι → α, ∏ i, ((if i = i0 then φ else 1) * Q i (x i)) =
        φ * ∏ i, Q i (x i) := fun x => by
      rw [Finset.prod_mul_distrib]
      congr 1
      simp
    have : (𝔼 x : ι → α, F x * ∏ i, ((if i = i0 then φ else 1) * Q i (x i))) =
        𝔼 x : ι → α, φ * (F x * ∏ i, Q i (x i)) := by
      refine Finset.expect_congr rfl fun x _ => ?_
      rw [hprod]; ring
    rw [this]
    exact hmain.trans (Complex.re_le_norm _)

end NearOne2

section Bounded
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem pow1400_le_bprodB {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 59 / 60) :
    δ ^ 1400 ≤ bprodB δ := by
  refine le_trans ?_ (bprodB_ge h0 (by linarith))
  have hnum : ((59 : ℝ) / 60) ^ 1391 ≤ 2.96 * 10 ^ (-10 : ℝ) := by
    have : (10 : ℝ) ^ (-10 : ℝ) = ((10 : ℝ) ^ 10)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
      norm_cast
    rw [this]
    have hnat : 59 ^ 1391 * 125000000000 ≤ 37 * 60 ^ 1391 := by decide +kernel
    have hr : (59 : ℝ) ^ 1391 * 125000000000 ≤ 37 * 60 ^ 1391 := by exact_mod_cast hnat
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : (2.96 : ℝ) * ((10 : ℝ) ^ 10)⁻¹ * 60 ^ 1391 = 37 * 60 ^ 1391 / 125000000000 := by
      norm_num
      rw [div_mul_eq_mul_div]
    rw [this, le_div_iff₀ (by norm_num)]
    exact hr
  have h2 : δ ^ ((2783 / 2 : ℝ)) ≤ δ ^ (1391 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge h0 (by linarith) (by norm_num)
  have h3 : δ ^ (1391 : ℕ) ≤ ((59 : ℝ) / 60) ^ 1391 := pow_le_pow_left₀ h0.le h1 _
  have h4 : δ ^ 1400 = δ ^ (17 / 2 : ℝ) * δ ^ (2783 / 2 : ℝ) := by
    rw [← Real.rpow_add h0, ← Real.rpow_natCast]
    norm_num
  rw [h4, mul_comm]
  exact mul_le_mul_of_nonneg_right ((h2.trans h3).trans hnum) (Real.rpow_nonneg h0.le _)

/-- Theorem `thm:bounded1` (Supplement F): input (I4) of Supplement D with `C_b = 1400`. -/
theorem boundedprod_one_bounded (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (P : ι → α → ℂ) (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : δ ≤ ‖𝔼 x : ι → α, F x * ∏ i, P i (x i)‖) :
    ∃ P' : ι → α → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
      δ ^ 1400 ≤ ‖𝔼 x : ι → α, F x * ∏ i, P' i (x i)‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨P, fun i => hι.elim i, (pow_le_of_le_one hδ0.le hδ1 (by norm_num)).trans hcorr⟩
  by_cases hbig : 59 / 60 < δ
  · obtain ⟨P', hP', h1, h2, h3⟩ := boundedprod_near_one F hF P hP (ε := 1 - δ)
      (by linarith) (by linarith) (by rw [sub_sub_cancel]; exact hcorr)
    refine ⟨P', hP', ?_⟩
    rw [sub_sub_cancel] at h2 h3
    calc δ ^ 1400 ≤ δ ^ 60 := h3
      _ ≤ 1 - 20 * (1 - δ) := h2
      _ ≤ _ := h1
  · push Not at hbig
    have hne := nonempty_of_corr F P hδ0 hcorr
    have hf4 : 𝔼 x : ι → α, ‖F x‖ ^ 4 ≤ 1 := by
      calc (𝔼 x : ι → α, ‖F x‖ ^ 4) ≤ 𝔼 x : ι → α, (1 : ℝ) :=
            Finset.expect_le_expect fun x _ => pow_le_one₀ (norm_nonneg _) (hF x)
        _ = 1 := Finset.expect_const univ_nonempty _
    obtain ⟨P', hP', hB⟩ := boundedprod_general F hf4 P hP hδ0 hδ1 hcorr
    exact ⟨P', fun i a => (hP' i a).le, (pow1400_le_bprodB hδ0 hbig).trans hB⟩

end Bounded

end TrackB
end RestrictedPolynomials
end
