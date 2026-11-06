module

public import RestrictedPolynomials.ExpIterate
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# K7: the tower side of the `kcsp` recursion

CSP_7 `sec:solve-rec`.  Pure real analysis on iterated exponentials `Real.exp^[j]`: the height count
`k7Height`, the bound `N_k ≤ k^k`, and the three tower estimates (`tau`, `rounds`, `final`) that carry
the exponent bookkeeping of the recursion.  Reuses `ExpIterate` (`le_exp_iterate`,
`exp_iterate_mono`, `exp_iterate_le_of_le`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-- CSP_7 `sec:solve-rec`: the number of exponentials (not counting the outermost one) of `δ_k` in
`δ_k = exp(-exp^{[N_k]}(ε^{-b}))`. Base `N_3 = 0` (`δ₃ = exp(-ε^{-O(1)})`, `thm:3csp-bkm2`); the step of this
formalization is `N_{k+1} = k (N_k + 3) + 1` (`+1`; `k` rounds of `lemma:replace`: each adds `N + 3`
with the halving and the `η^{-b}` powers absorbed; the final `+1`). The printed count `H(k) ≤ (k-1)(H(k-1)+1)`
ignores the powers and the halving (the paper's `exact-tower-small-eps`). Values `k < 3` are `0`
(junk, never used). -/
def k7Height : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | (n + 4) => (n + 3) * (k7Height (n + 3) + 3) + 1

/-- CSP_7 `sec:solve-rec`: the recursion and the bound `N_k ≤ k^k` for `k ≥ 3` (so one absolute `C₀ = 1` serves
the frozen height `k^{C₀ k}`). -/
theorem k7_height_succ (k : ℕ) (hk : 3 ≤ k) : k7Height (k + 1) = k * (k7Height k + 3) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  rfl

theorem k7_height_le_pow (k : ℕ) (hk : 3 ≤ k) : k7Height k ≤ k ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [k7_height_succ k hk]
    have h2 : k ^ k ≤ (k + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ k) k
    have h3 : k ^ 3 ≤ k ^ k := Nat.pow_le_pow_right (by omega) hk
    have h5 : 9 * k ≤ k ^ 3 := by nlinarith [Nat.mul_le_mul hk hk]
    have h4 : (k + 1) ^ (k + 1) = (k + 1) * (k + 1) ^ k := pow_succ' _ _
    have h6 : k * (k7Height k + 3) ≤ k * (k ^ k + 3) := Nat.mul_le_mul_left _ (by omega)
    have h7 : (k + 1) * k ^ k ≤ (k + 1) * (k + 1) ^ k := Nat.mul_le_mul_left _ h2
    nlinarith

/-! ### Helpers on iterated exponentials -/

private lemma iter_add_le (j : ℕ) :
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

private lemma mul_iter_le (j : ℕ) {B u : ℝ} (hB : 1 ≤ B) (hu : 1 ≤ u) :
    B * Real.exp^[j] u ≤ Real.exp^[j] (B * u) := by
  cases j with
  | zero => simp
  | succ j =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := iter_add_le j u ((B - 1) * u) (by linarith) (by nlinarith)
    have h2 : u + (B - 1) * u = B * u := by ring
    rw [h2] at h1
    have h3 : Real.log B ≤ (B - 1) * u := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < B)
      nlinarith
    calc B * Real.exp (Real.exp^[j] u) = Real.exp (Real.log B + Real.exp^[j] u) := by
          rw [Real.exp_add, Real.exp_log (by linarith)]
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)

private lemma one_le_rpow_neg {ε b : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hb : 0 ≤ b) :
    1 ≤ ε ^ (-b) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε (by linarith) (by linarith)

private lemma neg_log_ge {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Real.log 2 ≤ -Real.log ε := by
  have := Real.log_le_log hε hε2
  rw [one_div, Real.log_inv] at this
  linarith

private lemma rpow_neg_mono {ε b b' : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (h : b ≤ b') :
    ε ^ (-b) ≤ ε ^ (-b') :=
  Real.rpow_le_rpow_of_exponent_ge hε (by linarith) (by linarith)

private lemma absorb {ε a b : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    a * ε ^ (-b) ≤ ε ^ (-(b + Real.log a / Real.log 2)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlε := neg_log_ge hε hε2
  rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hε]
  have h2 : Real.log a ≤ (-Real.log ε) * (Real.log a / Real.log 2) := by
    calc Real.log a = Real.log 2 * (Real.log a / Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlε (div_nonneg hla hl2.le)
  calc a * Real.exp (Real.log ε * -b) = Real.exp (Real.log a + Real.log ε * -b) := by
        rw [Real.exp_add, Real.exp_log (by linarith)]
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

private lemma exp_neg_one_le : Real.exp (-1) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_neg]
  calc (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
    _ = 1 / 2 := by norm_num

private lemma exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  rw [Real.exp_neg]
  calc (Real.exp 2)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) h2
    _ = 1 / 4 := by norm_num

private lemma tau_alg {B L ℓ X : ℝ} (hB : 1 ≤ B) (hL0 : 0 ≤ L) (hℓ0 : 0 ≤ ℓ) (hX0 : 0 ≤ X) :
    L + 2 * ℓ + X + B * Real.exp (B * (2 * ℓ + X)) ≤
      Real.exp (Real.log (L + 3) + (Real.log B + B * (2 * ℓ + X))) := by
  have hlogB := Real.log_nonneg hB
  have hW0 : 0 ≤ Real.log B + B * (2 * ℓ + X) := by nlinarith
  have hV : B * Real.exp (B * (2 * ℓ + X)) = Real.exp (Real.log B + B * (2 * ℓ + X)) := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
  have hVge := Real.add_one_le_exp (Real.log B + B * (2 * ℓ + X))
  rw [Real.exp_add, Real.exp_log (by linarith), ← hV]
  have hV1 : 1 ≤ B * Real.exp (B * (2 * ℓ + X)) := by rw [hV]; exact Real.one_le_exp hW0
  have h2ℓ : 2 * ℓ ≤ B * (2 * ℓ + X) := by nlinarith
  have hX : X ≤ B * (2 * ℓ + X) := by nlinarith
  have hVge' : B * (2 * ℓ + X) + 1 ≤ B * Real.exp (B * (2 * ℓ + X)) := by rw [hV]; linarith
  nlinarith

private lemma tau_arith {b B K C ℓ : ℝ} (hb : 0 < b) (hB : 1 ≤ B) (hK0 : 0 ≤ K)
    (hC : C = B * Real.exp (b * Real.log 2) + K + 2 * B) (hC1 : 1 ≤ C)
    (hℓ : Real.log 2 ≤ ℓ) :
    B * Real.exp (b * (2 * ℓ + Real.log 2)) + (K + 2 * B * ℓ) ≤
      Real.exp ((2 * b + 1 + Real.log C / Real.log 2) * ℓ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ0 : 0 ≤ ℓ := hl2.le.trans hℓ
  have e1 : B * Real.exp (b * (2 * ℓ + Real.log 2)) ≤
      B * Real.exp (b * Real.log 2) * Real.exp ((2 * b + 1) * ℓ) := by
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.2
    nlinarith
  have hexpm : 1 ≤ Real.exp ((2 * b + 1) * ℓ) := Real.one_le_exp (by positivity)
  have e2 : K ≤ K * Real.exp ((2 * b + 1) * ℓ) := le_mul_of_one_le_right hK0 hexpm
  have e3 : 2 * B * ℓ ≤ 2 * B * Real.exp ((2 * b + 1) * ℓ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have := Real.add_one_le_exp ℓ
    have h4 : Real.exp ℓ ≤ Real.exp ((2 * b + 1) * ℓ) :=
      Real.exp_le_exp.2 (by nlinarith)
    linarith
  have e4 : C * Real.exp ((2 * b + 1) * ℓ) ≤
      Real.exp ((2 * b + 1 + Real.log C / Real.log 2) * ℓ) := by
    have hlC : Real.log C ≤ (Real.log C / Real.log 2) * ℓ := by
      calc Real.log C = (Real.log C / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hℓ (div_nonneg (Real.log_nonneg hC1) hl2.le)
    calc C * Real.exp ((2 * b + 1) * ℓ)
        = Real.exp (Real.log C + (2 * b + 1) * ℓ) := by
          rw [Real.exp_add, Real.exp_log (by linarith)]
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
  have e5 : B * Real.exp (b * Real.log 2) * Real.exp ((2 * b + 1) * ℓ) + K * Real.exp ((2 * b + 1) * ℓ)
      + 2 * B * Real.exp ((2 * b + 1) * ℓ) = C * Real.exp ((2 * b + 1) * ℓ) := by
    rw [hC]; ring
  linarith


/-- CSP_7 `eq:recursion1`, second inequality, made explicit (the `h`-th level): the lower bound of
`lemma:kcsp` is a tower of one more exponential. With `δ' = exp(-exp^{[h]}((ε²/2)^{-b}))`:
`δ' ≤ 1/2` and `c₁ ε² δ' exp(-B (ε² δ')^{-B}) ≥ exp(-exp^{[h+1]}(ε^{-b₁}))` for all `ε ∈ (0, 1/2]`. -/
theorem k7_tower_tau (h : ℕ) {b B c₁ : ℝ} (hb : 0 < b) (hB : 1 ≤ B) (hc0 : 0 < c₁)
    (hc1 : c₁ ≤ 1) :
    ∃ b₁ : ℝ, 0 < b₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ δ' : ℝ, δ' = Real.exp (-(Real.exp^[h] ((ε ^ 2 / 2) ^ (-b)))) →
        δ' ≤ 1 / 2 ∧
        Real.exp (-(Real.exp^[h + 1] (ε ^ (-b₁)))) ≤
          c₁ * (ε ^ 2 * δ') * Real.exp (-B * (ε ^ 2 * δ') ^ (-B)) := by
  have hL0 : 0 ≤ -Real.log c₁ := by
    have := Real.log_nonpos hc0.le hc1
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = -Real.log c₁ := ⟨_, rfl⟩
  rw [← hL] at hL0
  obtain ⟨K, hK⟩ : ∃ K, K = Real.log (L + 3) + Real.log B := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg hB)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp1 : 1 ≤ Real.exp (b * Real.log 2) := Real.one_le_exp (by positivity)
  obtain ⟨C, hC⟩ : ∃ C, C = B * Real.exp (b * Real.log 2) + K + 2 * B := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  refine ⟨2 * b + 1 + Real.log C / Real.log 2, by
    have := div_nonneg (Real.log_nonneg hC1) hl2.le
    linarith, ?_⟩
  intro ε hε hε2 δ' hδ'
  have hℓ₀ := neg_log_ge hε hε2
  obtain ⟨ℓ, hℓ, hεℓ⟩ : ∃ ℓ, Real.log 2 ≤ ℓ ∧ ε = Real.exp (-ℓ) :=
    ⟨-Real.log ε, hℓ₀, by rw [neg_neg, Real.exp_log hε]⟩
  subst hεℓ
  have hℓ0 : 0 ≤ ℓ := hl2.le.trans hℓ
  have hsq : Real.exp (-ℓ) ^ 2 = Real.exp (-(2 * ℓ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hu : (Real.exp (-ℓ) ^ 2 / 2) ^ (-b) = Real.exp (b * (2 * ℓ + Real.log 2)) := by
    have : Real.exp (-ℓ) ^ 2 / 2 = Real.exp (-(2 * ℓ + Real.log 2)) := by
      rw [hsq, neg_add, Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)]
      ring
    rw [this, ← Real.exp_mul]
    congr 1; ring
  obtain ⟨u, hu'⟩ : ∃ u, u = Real.exp (b * (2 * ℓ + Real.log 2)) := ⟨_, rfl⟩
  rw [hu, ← hu'] at hδ'
  have hu1 : 1 ≤ u := by
    rw [hu']; exact Real.one_le_exp (by positivity)
  have hX1 : 1 ≤ Real.exp^[h] u := hu1.trans (le_exp_iterate h u)
  obtain ⟨X, hXdef⟩ : ∃ X, X = Real.exp^[h] u := ⟨_, rfl⟩
  rw [← hXdef] at hX1 hδ'
  refine ⟨?_, ?_⟩
  · rw [hδ']
    calc Real.exp (-X) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 1 / 2 := exp_neg_one_le
  -- the main inequality
  have hq : Real.exp (-ℓ) ^ 2 * δ' = Real.exp (-(2 * ℓ + X)) := by
    rw [hδ', hsq, ← Real.exp_add]; congr 1; ring
  have hqB : (Real.exp (-(2 * ℓ + X))) ^ (-B) = Real.exp (B * (2 * ℓ + X)) := by
    rw [← Real.exp_mul]; congr 1; ring
  have hZ : Real.exp (-ℓ) ^ (-(2 * b + 1 + Real.log C / Real.log 2)) =
      Real.exp ((2 * b + 1 + Real.log C / Real.log 2) * ℓ) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [hq, hqB, hZ]
  -- V = B * exp (B (2ℓ + X))
  have hW0 : 0 ≤ Real.log B + B * (2 * ℓ + X) := by
    have := Real.log_nonneg hB
    nlinarith
  have hV : B * Real.exp (B * (2 * ℓ + X)) = Real.exp (Real.log B + B * (2 * ℓ + X)) := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
  have hVge := Real.add_one_le_exp (Real.log B + B * (2 * ℓ + X))
  have hlogB := Real.log_nonneg hB
  have hS := tau_alg hB hL0 hℓ0 (by linarith : 0 ≤ X)
  -- the iterated-exponential bound
  have hmain : Real.log (L + 3) + (Real.log B + B * (2 * ℓ + X)) ≤
      Real.exp^[h] (Real.exp ((2 * b + 1 + Real.log C / Real.log 2) * ℓ)) := by
    have hM : B * X ≤ Real.exp^[h] (B * u) := by rw [hXdef]; exact mul_iter_le h hB hu1
    have hc0' : 0 ≤ K + 2 * B * ℓ := by positivity
    have hA := iter_add_le h (B * u) (K + 2 * B * ℓ) (by positivity) hc0'
    have hmono : B * u + (K + 2 * B * ℓ) ≤
        Real.exp ((2 * b + 1 + Real.log C / Real.log 2) * ℓ) := by
      rw [hu']; exact tau_arith hb hB hK0 hC hC1 hℓ
    have hlast := exp_iterate_mono h hmono
    have hK' : Real.log (L + 3) + (Real.log B + B * (2 * ℓ + X)) = K + 2 * B * ℓ + B * X := by
      rw [hK]; ring
    rw [hK']
    linarith
  -- assemble
  have hfinal : L + 2 * ℓ + X + B * Real.exp (B * (2 * ℓ + X)) ≤
      Real.exp^[h + 1] (Real.exp ((2 * b + 1 + Real.log C / Real.log 2) * ℓ)) := by
    rw [Function.iterate_succ_apply']
    exact hS.trans (Real.exp_le_exp.2 hmain)
  have hrhs : c₁ * Real.exp (-(2 * ℓ + X)) * Real.exp (-B * Real.exp (B * (2 * ℓ + X))) =
      Real.exp (-(L + 2 * ℓ + X + B * Real.exp (B * (2 * ℓ + X)))) := by
    rw [hL, ← Real.exp_log hc0, ← Real.exp_add, ← Real.exp_add, Real.exp_log hc0]
    congr 1
    ring
  rw [hrhs]
  exact Real.exp_le_exp.2 (by linarith)

/-! ### Rounds -/

private lemma round_step (h' : ℕ) {b₁ : ℝ} (hb₁ : 0 < b₁) (g : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ b' : ℝ, b ≤ b' ∧ ∀ τfun : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        Real.exp (-(Real.exp^[h'] (η ^ (-b₁)))) ≤ τfun η ∧ τfun η ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        Real.exp (-(Real.exp^[g] (ε ^ (-b)))) ≤ η →
        Real.exp (-(Real.exp^[g + h' + 2] (ε ^ (-b')))) ≤ τfun η / 2 ∧ τfun η / 2 ≤ 1 / 2 := by
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, B₁ = max b₁ 1 := ⟨_, rfl⟩
  have hB₁1 : 1 ≤ B₁ := by rw [hB₁]; exact le_max_right _ _
  have hB₁b : b₁ ≤ B₁ := by rw [hB₁]; exact le_max_left _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨b + Real.log B₁ / Real.log 2, ?_, ?_⟩
  · have := div_nonneg (Real.log_nonneg hB₁1) hl2.le
    linarith
  intro τfun hτ ε hε hε2 η hη hη2 hηE
  obtain ⟨hτ1, hτ2⟩ := hτ η hη hη2
  refine ⟨?_, by linarith⟩
  have hz1 : 1 ≤ ε ^ (-b) := one_le_rpow_neg hε hε2 hb.le
  have hS1 : 1 ≤ Real.exp^[g] (ε ^ (-b)) := hz1.trans (le_exp_iterate g _)
  have hlog : -(Real.exp^[g] (ε ^ (-b))) ≤ Real.log η := (Real.le_log_iff_exp_le hη).2 hηE
  have h1 : η ^ (-b₁) ≤ Real.exp (Real.exp^[g] (B₁ * ε ^ (-b))) := by
    rw [Real.rpow_def_of_pos hη]
    apply Real.exp_le_exp.2
    have h2 : B₁ * Real.exp^[g] (ε ^ (-b)) ≤ Real.exp^[g] (B₁ * ε ^ (-b)) :=
      mul_iter_le g hB₁1 hz1
    have h3 : b₁ * Real.exp^[g] (ε ^ (-b)) ≤ B₁ * Real.exp^[g] (ε ^ (-b)) :=
      mul_le_mul_of_nonneg_right hB₁b (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlog hb₁.le]
  have h3 : Real.exp^[h'] (η ^ (-b₁)) ≤ Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)) := by
    rw [Function.iterate_add_apply, Function.iterate_succ_apply']
    exact exp_iterate_mono h' h1
  have e1 : Real.exp (Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b))) =
      Real.exp^[g + h' + 2] (B₁ * ε ^ (-b)) := by
    rw [show g + h' + 2 = (h' + (g + 1)) + 1 by ring, Function.iterate_succ_apply']
  have e2 : Real.exp^[g + h' + 2] (B₁ * ε ^ (-b)) ≤
      Real.exp^[g + h' + 2] (ε ^ (-(b + Real.log B₁ / Real.log 2))) :=
    exp_iterate_mono _ (absorb hε hε2 hB₁1 hb.le)
  have e3 : Real.exp (-(Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)))) ≤ τfun η :=
    (Real.exp_le_exp.2 (by linarith)).trans hτ1
  have e4 : Real.exp (-(Real.exp (Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b))))) ≤
      Real.exp (-(Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)))) / 2 := by
    have h5 := Real.add_one_le_exp (Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)))
    calc Real.exp (-(Real.exp (Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)))))
        ≤ Real.exp (-(Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b))) + -1) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)))) * Real.exp (-1) :=
          Real.exp_add _ _
      _ ≤ Real.exp (-(Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b)))) * (1 / 2) :=
          mul_le_mul_of_nonneg_left exp_neg_one_le (Real.exp_pos _).le
      _ = _ := by ring
  calc Real.exp (-(Real.exp^[g + h' + 2] (ε ^ (-(b + Real.log B₁ / Real.log 2)))))
      ≤ Real.exp (-(Real.exp (Real.exp^[h' + (g + 1)] (B₁ * ε ^ (-b))))) :=
        Real.exp_le_exp.2 (by rw [e1]; linarith)
    _ ≤ _ := e4
    _ ≤ τfun η / 2 := by linarith

private lemma rounds_aux (h' : ℕ) {b₁ : ℝ} (hb₁ : 0 < b₁) (r : ℕ) :
    ∃ b : ℝ, 0 < b ∧ ∀ τfun : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        Real.exp (-(Real.exp^[h'] (η ^ (-b₁)))) ≤ τfun η ∧ τfun η ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        Real.exp (-(Real.exp^[r * (h' + 2)] (ε ^ (-b)))) ≤ (fun x => τfun x / 2)^[r] ε ∧
        (fun x => τfun x / 2)^[r] ε ≤ 1 / 2 := by
  induction r with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    intro τfun _ ε hε hε2
    simp only [zero_mul, Function.iterate_zero, id_eq]
    refine ⟨?_, hε2⟩
    rw [Real.rpow_neg_one]
    have h1 : ε⁻¹ ≤ Real.exp ε⁻¹ := by linarith [Real.add_one_le_exp ε⁻¹]
    calc Real.exp (-ε⁻¹) = (Real.exp ε⁻¹)⁻¹ := Real.exp_neg _
      _ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hε) h1
      _ = ε := inv_inv ε
  | succ r ih =>
    obtain ⟨b, hb, hih⟩ := ih
    obtain ⟨b', hbb', hstep⟩ := round_step h' hb₁ (r * (h' + 2)) hb
    refine ⟨b', hb.trans_le hbb', ?_⟩
    intro τfun hτ ε hε hε2
    obtain ⟨hlow, hup⟩ := hih τfun hτ ε hε hε2
    have hpos : 0 < (fun x => τfun x / 2)^[r] ε := lt_of_lt_of_le (Real.exp_pos _) hlow
    obtain ⟨s1, s2⟩ := hstep τfun hτ ε hε hε2 _ hpos hup hlow
    rw [Function.iterate_succ_apply']
    have : (r + 1) * (h' + 2) = r * (h' + 2) + h' + 2 := by ring
    rw [this]
    exact ⟨s1, s2⟩

/-- CSP_7 `cor:replace`, step `iterate-replace` (tower side): if the round parameter satisfies
`exp(-exp^{[h']}(η^{-b₁})) ≤ τ(η) ≤ 1` on `(0, 1/2]`, then after `m` rounds (`η₀ = ε`, `η_{r+1} = τ(η_r)/2`) the
free rate `R = ∏ τ(η_r)`, the probability `p = ∏ τ(η_r)²/2` and the correlation `η_m` are all
`≥ exp(-exp^{[m (h'+2)]}(ε^{-b₂}))`, `b₂` independent of `τ`. -/
theorem k7_tower_rounds (h' m : ℕ) {b₁ : ℝ} (hb₁ : 0 < b₁) :
    ∃ b₂ : ℝ, 0 < b₂ ∧ ∀ τfun : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        Real.exp (-(Real.exp^[h'] (η ^ (-b₁)))) ≤ τfun η ∧ τfun η ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₂)))) ≤
          ∏ r ∈ Finset.range m, τfun ((fun x => τfun x / 2)^[r] ε) ∧
        Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₂)))) ≤
          ∏ r ∈ Finset.range m, (τfun ((fun x => τfun x / 2)^[r] ε) ^ 2 / 2) ∧
        Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₂)))) ≤ (fun x => τfun x / 2)^[m] ε ∧
        (fun x => τfun x / 2)^[m] ε ≤ 1 / 2 := by
  choose bs hbs hmain using fun r => rounds_aux h' hb₁ r
  obtain ⟨b₃, hb₃⟩ : ∃ b₃, b₃ = ∑ r ∈ Finset.range (m + 1), bs r := ⟨_, rfl⟩
  have hbr : ∀ r ≤ m, bs r ≤ b₃ := fun r hr => by
    rw [hb₃]
    exact Finset.single_le_sum (f := bs) (fun i _ => (hbs i).le)
      (Finset.mem_range.2 (by omega))
  have hb₃pos : 0 ≤ b₃ := by
    rw [hb₃]; exact Finset.sum_nonneg (fun i _ => (hbs i).le)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : 0 ≤ Real.log (2 * (m : ℝ) + 1) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  refine ⟨b₃ + Real.log (2 * (m : ℝ) + 1) / Real.log 2, by
    have : 0 < bs 0 := hbs 0
    have := hbr 0 (Nat.zero_le m)
    linarith, ?_⟩
  intro τfun hτ ε hε hε2
  have hz₃1 : 1 ≤ ε ^ (-b₃) := one_le_rpow_neg hε hε2 hb₃pos
  have hS1 : 1 ≤ Real.exp^[m * (h' + 2)] (ε ^ (-b₃)) := hz₃1.trans (le_exp_iterate _ _)
  have hE : ∀ r ≤ m, Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ≤
      (fun x => τfun x / 2)^[r] ε := by
    intro r hr
    obtain ⟨hl, _⟩ := hmain r τfun hτ ε hε hε2
    refine le_trans ?_ hl
    apply Real.exp_le_exp.2
    have : Real.exp^[r * (h' + 2)] (ε ^ (-bs r)) ≤ Real.exp^[m * (h' + 2)] (ε ^ (-b₃)) :=
      (exp_iterate_mono _ (rpow_neg_mono hε hε2 (hbr r hr))).trans
        (exp_iterate_le_of_le (Nat.mul_le_mul_right _ hr) _)
    linarith
  have hup : (fun x => τfun x / 2)^[m] ε ≤ 1 / 2 := (hmain m τfun hτ ε hε hε2).2
  have hE1 : Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hpow : (Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ^ 2) ^ m =
      Real.exp (-((2 * (m : ℝ)) * Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) := by
    rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hfin : Real.exp (-(Real.exp^[m * (h' + 2)]
      (ε ^ (-(b₃ + Real.log (2 * (m : ℝ) + 1) / Real.log 2))))) ≤
      Real.exp (-((2 * (m : ℝ)) * Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) := by
    apply Real.exp_le_exp.2
    have h1 : (2 * (m : ℝ) + 1) * Real.exp^[m * (h' + 2)] (ε ^ (-b₃)) ≤
        Real.exp^[m * (h' + 2)] ((2 * (m : ℝ) + 1) * ε ^ (-b₃)) :=
      mul_iter_le _ (by linarith) hz₃1
    have h2 := exp_iterate_mono (m * (h' + 2)) (absorb hε hε2 (a := 2 * (m : ℝ) + 1)
      (by linarith) hb₃pos)
    nlinarith
  have hfin2 : Real.exp (-(Real.exp^[m * (h' + 2)]
      (ε ^ (-(b₃ + Real.log (2 * (m : ℝ) + 1) / Real.log 2))))) ≤
      Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) := by
    apply Real.exp_le_exp.2
    have := exp_iterate_mono (m * (h' + 2))
      (rpow_neg_mono hε hε2 (by linarith : b₃ ≤ b₃ + Real.log (2 * (m : ℝ) + 1) / Real.log 2))
    linarith
  have hfac : ∀ r ∈ Finset.range m,
      Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ≤
        τfun ((fun x => τfun x / 2)^[r] ε) / 2 := by
    intro r hr
    have := hE (r + 1) (by have := Finset.mem_range.1 hr; omega)
    rwa [Function.iterate_succ_apply'] at this
  refine ⟨?_, ?_, hfin2.trans (hE m le_rfl), hup⟩
  · calc _ ≤ (Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ^ 2) ^ m := hpow ▸ hfin
      _ = ∏ r ∈ Finset.range m, Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ^ 2 := by
        rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun r hr => ?_)
        have h1 := hfac r hr
        have h0 := Real.exp_pos (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃))))
        nlinarith
  · calc _ ≤ (Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ^ 2) ^ m := hpow ▸ hfin
      _ = ∏ r ∈ Finset.range m, Real.exp (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃)))) ^ 2 := by
        rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun r hr => ?_)
        have h1 := hfac r hr
        have h0 := Real.exp_pos (-(Real.exp^[m * (h' + 2)] (ε ^ (-b₃))))
        nlinarith

/-- CSP_7 `eq:recursion2` (tower side) and the final choice of CSP_7 `thm:kcsp`, step `uniformize-delta`: from
`R, p, η' ≥ exp(-exp^{[g]}(ε^{-b₂}))` (`η' ≤ 1/2`) and `c > 0`, the parameter
`δ'' = exp(-exp^{[g+1]}(ε^{-b₃}))` is `≤ γ R` with `γ = min(1/2, c η'²/log(1/η'))` and `≤ p η'²/4`
(the two bounds that `Stab_{1-δ''} ≥ Stab_{1-γR} ≥ p η'²/4 ≥ δ''` needs). -/
theorem k7_tower_final (g : ℕ) {b₂ c : ℝ} (hb₂ : 0 < b₂) (hc : 0 < c) :
    ∃ b₃ : ℝ, 0 < b₃ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ R p η' : ℝ,
      Real.exp (-(Real.exp^[g] (ε ^ (-b₂)))) ≤ R → Real.exp (-(Real.exp^[g] (ε ^ (-b₂)))) ≤ p →
      Real.exp (-(Real.exp^[g] (ε ^ (-b₂)))) ≤ η' → η' ≤ 1 / 2 → R ≤ 1 → p ≤ 1 →
        Real.exp (-(Real.exp^[g + 1] (ε ^ (-b₃)))) ≤
          min (1 / 2) (c * η' ^ 2 / Real.log (1 / η')) * R ∧
        Real.exp (-(Real.exp^[g + 1] (ε ^ (-b₃)))) ≤ p * (η' ^ 2 / 4) := by
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = min (1 / 2 : ℝ) c := ⟨_, rfl⟩
  have hm0pos : 0 < m0 := by rw [hm0]; exact lt_min (by norm_num) hc
  have hm0le : m0 ≤ 1 / 2 := by rw [hm0]; exact min_le_left _ _
  have hm0c : m0 ≤ c := by rw [hm0]; exact min_le_right _ _
  obtain ⟨L0, hL0def⟩ : ∃ L0, L0 = -Real.log m0 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L0 := by
    have := Real.log_nonpos hm0pos.le (by linarith : m0 ≤ 1)
    linarith
  obtain ⟨A, hAdef⟩ : ∃ A, A = 5 + L0 := ⟨_, rfl⟩
  have hA : 1 ≤ A := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log A / Real.log 2 := div_nonneg (Real.log_nonneg hA) hl2.le
  refine ⟨b₂ + Real.log A / Real.log 2, by linarith, ?_⟩
  intro ε hε hε2 R p η' hR hp hη hη2 hR1 hp1
  have hz1 : 1 ≤ ε ^ (-b₂) := one_le_rpow_neg hε hε2 hb₂.le
  have hS1 : 1 ≤ Real.exp^[g] (ε ^ (-b₂)) := hz1.trans (le_exp_iterate g _)
  have hT : Real.exp^[g] (A * ε ^ (-b₂)) ≤
      Real.exp^[g] (ε ^ (-(b₂ + Real.log A / Real.log 2))) :=
    exp_iterate_mono g (absorb hε hε2 hA hb₂.le)
  have hM : A * Real.exp^[g] (ε ^ (-b₂)) ≤ Real.exp^[g] (A * ε ^ (-b₂)) :=
    mul_iter_le g hA hz1
  have hbig : A * Real.exp^[g] (ε ^ (-b₂)) ≤
      Real.exp^[g + 1] (ε ^ (-(b₂ + Real.log A / Real.log 2))) := by
    rw [Function.iterate_succ_apply']
    exact (hM.trans hT).trans
      (by linarith [Real.add_one_le_exp (Real.exp^[g] (ε ^ (-(b₂ + Real.log A / Real.log 2))))])
  have hηpos : 0 < η' := lt_of_lt_of_le (Real.exp_pos _) hη
  obtain ⟨S, hSdef⟩ : ∃ S, S = Real.exp^[g] (ε ^ (-b₂)) := ⟨_, rfl⟩
  rw [← hSdef] at hS1 hbig hR hp hη
  obtain ⟨T', hT'⟩ : ∃ T', T' = Real.exp^[g + 1] (ε ^ (-(b₂ + Real.log A / Real.log 2))) :=
    ⟨_, rfl⟩
  rw [← hT'] at hbig ⊢
  have hE0 := Real.exp_pos (-S)
  have hE1 : Real.exp (-S) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hexp3 : Real.exp (-S) ^ 3 ≤ η' ^ 3 := pow_le_pow_left₀ hE0.le hη 3
  have hη3 : η' ^ 3 ≤ 1 := pow_le_one₀ hηpos.le (by linarith)
  constructor
  · have hℓ' : 0 < Real.log (1 / η') := Real.log_pos (by
      rw [lt_div_iff₀ hηpos]; linarith)
    have hℓle : Real.log (1 / η') ≤ η'⁻¹ := by
      have := Real.log_le_sub_one_of_pos (one_div_pos.2 hηpos)
      rw [one_div] at this ⊢
      linarith
    have hmin : m0 * η' ^ 3 ≤ min (1 / 2) (c * η' ^ 2 / Real.log (1 / η')) := by
      apply le_min
      · nlinarith [pow_nonneg hηpos.le 3]
      · rw [le_div_iff₀ hℓ']
        have h1 : η' ^ 3 * Real.log (1 / η') ≤ η' ^ 2 := by
          calc η' ^ 3 * Real.log (1 / η') ≤ η' ^ 3 * η'⁻¹ :=
                mul_le_mul_of_nonneg_left hℓle (pow_nonneg hηpos.le 3)
            _ = η' ^ 2 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left h1 hm0pos.le,
          mul_le_mul_of_nonneg_right hm0c (pow_nonneg hηpos.le 2)]
    have h2 : m0 * Real.exp (-S) ^ 4 ≤ min (1 / 2) (c * η' ^ 2 / Real.log (1 / η')) * R := by
      have h3 : Real.exp (-S) ^ 4 ≤ η' ^ 3 * R := by
        calc Real.exp (-S) ^ 4 = Real.exp (-S) ^ 3 * Real.exp (-S) := by ring
          _ ≤ η' ^ 3 * R := mul_le_mul hexp3 hR hE0.le (pow_nonneg hηpos.le 3)
      calc m0 * Real.exp (-S) ^ 4 ≤ m0 * (η' ^ 3 * R) := mul_le_mul_of_nonneg_left h3 hm0pos.le
        _ = (m0 * η' ^ 3) * R := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmin (hE0.le.trans hR)
    have h4 : m0 * Real.exp (-S) ^ 4 = Real.exp (-(L0 + 4 * S)) := by
      rw [hL0def, neg_add, Real.exp_add, neg_neg, Real.exp_log hm0pos]
      rw [show -(4 * S) = ((4 : ℕ) : ℝ) * (-S) by push_cast; ring, Real.exp_nat_mul]
    refine le_trans ?_ (h4 ▸ h2)
    apply Real.exp_le_exp.2
    nlinarith
  · have h2 : Real.exp (-S) ^ 3 / 4 ≤ p * (η' ^ 2 / 4) := by
      have h3 : Real.exp (-S) ^ 3 ≤ p * η' ^ 2 :=
        calc Real.exp (-S) ^ 3 = Real.exp (-S) * Real.exp (-S) ^ 2 := by ring
          _ ≤ p * η' ^ 2 := mul_le_mul hp (pow_le_pow_left₀ hE0.le hη 2) (by positivity)
            (hE0.le.trans hp)
      linarith
    have h4 : Real.exp (-(3 * S + 2)) ≤ Real.exp (-S) ^ 3 / 4 := by
      have : Real.exp (-(3 * S + 2)) = Real.exp (-S) ^ 3 * Real.exp (-2) := by
        rw [neg_add, Real.exp_add,
          show -(3 * S) = ((3 : ℕ) : ℝ) * (-S) by push_cast; ring, Real.exp_nat_mul]
      rw [this]
      have := exp_neg_two_le
      have h5 : 0 < Real.exp (-S) ^ 3 := by positivity
      nlinarith
    refine le_trans ?_ (h4.trans h2)
    apply Real.exp_le_exp.2
    nlinarith

end TrackB
end RestrictedPolynomials
end
