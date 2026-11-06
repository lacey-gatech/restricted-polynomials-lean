module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import RestrictedPolynomials.ExpIterate

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Rate

/-- the rate `τ = min(ζ δ₆, δ₆/2, ε₁ δ₆²/2)` of `lem:rate`, with `ζ = α² δ'` and `ε₁ = ε² δ'/4`
(data; characterised by `k7_rateTau_le` and `k7_rateTau_bounds`). -/
def k7RateTau (α ε δ' δ₆ : ℝ) : ℝ :=
  min (α ^ 2 * δ' * δ₆) (min (δ₆ / 2) (ε ^ 2 * δ' / 4 * δ₆ ^ 2 / 2))

/-- the three upper bounds that Steps 4 and 6 of `thm:kcsp-rat` use: `τ ≤ ζ δ₆`, `τ ≤ δ₆/2`,
`τ ≤ ε₁ δ₆²/2`. -/
theorem k7_rateTau_le (α ε δ' δ₆ : ℝ) :
    k7RateTau α ε δ' δ₆ ≤ α ^ 2 * δ' * δ₆ ∧ k7RateTau α ε δ' δ₆ ≤ δ₆ / 2 ∧
      k7RateTau α ε δ' δ₆ ≤ ε ^ 2 * δ' / 4 * δ₆ ^ 2 / 2 :=
  ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

/-- `lem:rate` (the exponent of `δ₆` is `2`): `0 < τ ≤ 1/2` and
`τ ≥ (α²/8) ε² δ' δ₆²`. -/
theorem k7_rateTau_bounds {α ε δ' δ₆ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1 / 2) (h60 : 0 < δ₆) (h61 : δ₆ ≤ 1) :
    0 < k7RateTau α ε δ' δ₆ ∧ k7RateTau α ε δ' δ₆ ≤ 1 / 2 ∧
      α ^ 2 / 8 * (ε ^ 2 * δ') * δ₆ ^ 2 ≤ k7RateTau α ε δ' δ₆ := by
  unfold k7RateTau
  have h1 : 0 < α ^ 2 * δ' * δ₆ := by positivity
  have h2 : 0 < δ₆ / 2 := by positivity
  have h3 : 0 < ε ^ 2 * δ' / 4 * δ₆ ^ 2 / 2 := by positivity
  refine ⟨lt_min h1 (lt_min h2 h3), (min_le_of_right_le (min_le_left _ _)).trans (by linarith), ?_⟩
  refine le_min ?_ (le_min ?_ ?_)
  · have : α ^ 2 / 8 * (ε ^ 2 * δ') * δ₆ ^ 2 ≤ α ^ 2 * δ' * δ₆ := by
      have hε2 : ε ^ 2 ≤ 1 := by nlinarith
      have hd : δ₆ ^ 2 ≤ δ₆ := by nlinarith
      have : α ^ 2 / 8 * (ε ^ 2 * δ') * δ₆ ^ 2 ≤ α ^ 2 * δ' * δ₆ := by
        have h4 : 0 ≤ α ^ 2 * δ' := by positivity
        nlinarith [mul_nonneg h4 (sub_nonneg.2 hd), mul_nonneg h4 h60.le, mul_nonneg (mul_nonneg h4 h60.le) (sub_nonneg.2 hε2)]
      exact this
    exact this
  · have hd : δ₆ ^ 2 ≤ δ₆ := by nlinarith
    have : α ^ 2 * (ε ^ 2 * δ') / 8 ≤ 1 / 2 := by
      have : ε ^ 2 ≤ 1 := by nlinarith
      have : α ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg ε)]
    nlinarith [sq_nonneg δ₆]
  · have : α ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg ε) hδ0.le, sq_nonneg δ₆, mul_nonneg (mul_nonneg (sq_nonneg ε) hδ0.le) (sq_nonneg δ₆)]


/-- `lem:rate`, the exponent half: with `B = 2 C₆ 4^{C₆}`, `x = ε² δ' ≤ 1` and
`δ₆ = exp(-C₆ (x/4)^{-C₆})`: `exp(-B x^{-B}) ≤ δ₆²`. -/
theorem k7_rate_exp {C₆ : ℝ} (hC : 1 ≤ C₆) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.exp (-(2 * C₆ * (4 : ℝ) ^ C₆) * x ^ (-(2 * C₆ * (4 : ℝ) ^ C₆))) ≤
      (Real.exp (-C₆ * (x / 4) ^ (-C₆))) ^ 2 := by
  have hx4 : 0 < x / 4 := by positivity
  have hpow : (x / 4) ^ (-C₆) = (4 : ℝ) ^ C₆ * x ^ (-C₆) := by
    rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), div_inv_eq_mul,
      mul_comm]
  have h4 : 1 ≤ (4 : ℝ) ^ C₆ := Real.one_le_rpow (by norm_num) (by linarith)
  have hB : C₆ ≤ 2 * C₆ * (4 : ℝ) ^ C₆ := by nlinarith
  have hxB : x ^ (-C₆) ≤ x ^ (-(2 * C₆ * (4 : ℝ) ^ C₆)) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hBpos : 0 ≤ 2 * C₆ * (4 : ℝ) ^ C₆ := by nlinarith
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.2 ?_
  rw [hpow]
  push_cast
  have : 0 ≤ x ^ (-C₆) := Real.rpow_nonneg hx0.le _
  nlinarith [mul_le_mul_of_nonneg_left hxB hBpos]

/-- `B = 2 C₆ 4^{C₆} ≥ 1` for `C₆ ≥ 1`. -/
theorem k7_rate_B_ge {C₆ : ℝ} (hC : 1 ≤ C₆) : 1 ≤ 2 * C₆ * (4 : ℝ) ^ C₆ := by
  have h4 : 1 ≤ (4 : ℝ) ^ C₆ := Real.one_le_rpow (by norm_num) (by linarith)
  nlinarith

end Rate

section Absorb

section Aux

private lemma iter_add_le_aux (j : ℕ) :
    ∀ (u c : ℝ), 0 ≤ u → 0 ≤ c → Real.exp^[j] u + c ≤ Real.exp^[j] (u + c) := by
  induction j with
  | zero => intro u c _ _; simp
  | succ j ih =>
    intro u c hu hc
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih u c hu hc
    have h2 : 1 ≤ Real.exp (Real.exp^[j] u) := Real.one_le_exp (hu.trans (le_exp_iterate j u))
    have h3 : Real.exp (Real.exp^[j] u + c) ≤ Real.exp (Real.exp^[j] (u + c)) :=
      Real.exp_le_exp.2 h1
    rw [Real.exp_add] at h3
    have h4 := Real.add_one_le_exp c
    nlinarith [mul_nonneg (sub_nonneg.2 h2) hc,
      mul_nonneg (Real.exp_pos (Real.exp^[j] u)).le (sub_nonneg.2 h4)]

private lemma one_le_rpow_neg_aux {ε b : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hb : 0 ≤ b) :
    1 ≤ ε ^ (-b) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε (by linarith) (by linarith)

private lemma neg_log_ge_aux {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Real.log 2 ≤ -Real.log ε := by
  have := Real.log_le_log hε hε2
  rw [one_div, Real.log_inv] at this
  linarith

private lemma absorb_aux {ε a b : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    a * ε ^ (-b) ≤ ε ^ (-(b + Real.log a / Real.log 2)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlε := neg_log_ge_aux hε hε2
  rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hε]
  have h2 : Real.log a ≤ (-Real.log ε) * (Real.log a / Real.log 2) := by
    calc Real.log a = Real.log 2 * (Real.log a / Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlε (div_nonneg hla hl2.le)
  calc a * Real.exp (Real.log ε * -b) = Real.exp (Real.log a + Real.log ε * -b) := by
        rw [Real.exp_add, Real.exp_log (by linarith)]
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end Aux

/-- `lem:absorb` (any `N`, the printed `N ≥ 1` is not needed): for `α ∈ (0, 1]` and `b' > 0` there is
`b''` (depending on `(α, b')` only) such that `exp(-exp^{[N]}(ε^{-b''})) ≤ (α ε/2)
exp(-exp^{[N]}((ε/2)^{-b'}))` for all `ε ∈ (0, 1/2]`. -/
theorem k7_absorb_half (N : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {b' : ℝ} (hb' : 0 < b') :
    ∃ b'' : ℝ, 0 < b'' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      Real.exp (-(Real.exp^[N] (ε ^ (-b'')))) ≤
        α * ε / 2 * Real.exp (-(Real.exp^[N] ((ε / 2) ^ (-b')))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log (2 / α) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith)
  set a : ℝ := (2 : ℝ) ^ b' + c + 1 with ha
  have h2b : 1 ≤ (2 : ℝ) ^ b' := Real.one_le_rpow (by norm_num) hb'.le
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  refine ⟨b' + 1 + Real.log a / Real.log 2, by
    have := Real.log_nonneg ha1; positivity, fun ε hε0 hε1 => ?_⟩
  have hεinv : 0 ≤ Real.log (ε⁻¹) := Real.log_nonneg (by
    rw [one_le_inv₀ hε0]; linarith)
  -- the three pieces
  set t : ℝ := ε ^ (-(b' + 1)) with ht
  have ht1 : 1 ≤ t := one_le_rpow_neg_aux hε0 hε1 (by linarith)
  have hu : (ε / 2) ^ (-b') = (2 : ℝ) ^ b' * ε ^ (-b') := by
    rw [Real.div_rpow hε0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul,
      mul_comm]
  have hεb : ε ^ (-b') ≤ t :=
    Real.rpow_le_rpow_of_exponent_ge hε0 (by linarith) (by linarith)
  have hlogt : Real.log (ε⁻¹) ≤ t := by
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hε0)
    have h2 : ε ^ (-(1 : ℝ)) ≤ t := Real.rpow_le_rpow_of_exponent_ge hε0 (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h2
    linarith
  have hεb0 : 0 ≤ ε ^ (-b') := Real.rpow_nonneg hε0.le _
  set u : ℝ := (ε / 2) ^ (-b') with hudef
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hL : -Real.log (α * ε / 2) = c + Real.log (ε⁻¹) := by
    rw [hc, Real.log_inv, div_eq_mul_inv, Real.log_mul (by positivity) (by norm_num),
      Real.log_mul hα0.ne' hε0.ne', Real.log_div (by norm_num) hα0.ne']
    rw [Real.log_inv]; ring
  have hL0 : 0 ≤ c + Real.log (ε⁻¹) := by linarith
  have hsum : u + (c + Real.log (ε⁻¹)) ≤ a * t := by
    rw [hu, ha]
    nlinarith [mul_le_mul_of_nonneg_left hεb (by linarith : (0:ℝ) ≤ 2 ^ b')]
  have habs : a * t ≤ ε ^ (-(b' + 1 + Real.log a / Real.log 2)) :=
    absorb_aux hε0 hε1 ha1 (by linarith)
  have hmain := iter_add_le_aux N u (c + Real.log (ε⁻¹)) hu0 hL0
  have hmono := exp_iterate_mono N (hsum.trans habs)
  have hrhs : α * ε / 2 * Real.exp (-(Real.exp^[N] u)) =
      Real.exp (-(Real.exp^[N] u + (c + Real.log (ε⁻¹)))) := by
    rw [neg_add, Real.exp_add, ← hL, neg_neg, Real.exp_log (by positivity)]
    ring
  rw [hrhs]
  exact Real.exp_le_exp.2 (by linarith)

end Absorb

end TrackB
end RestrictedPolynomials
end
