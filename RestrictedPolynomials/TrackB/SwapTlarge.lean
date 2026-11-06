module

public import RestrictedPolynomials.TrackB.SwapIterScheme

/-!
# Track B: `lemma:tlarge` of CSP_6

Source: CSP6 (arXiv:2411.15133v1 `main.tex`) L915-929 (`lemma:tlarge`): the iterative scheme
of `subsec:iter` either runs for `T` steps and raises the normalized value, or stops early with a small
residual and loses little normalized value; with an explicit lower bound on the probability.
Covers CSP_6 `lemma:tlarge` and `lemma:tlarge#success-probability`.

Readings of the source used here:
* the potential carries the weight `C = (θε⁵)⁻¹`, `θ ∈ (0,1]` (`θ = 1` is the
  source), so that the two cases read `NV_T ≥ NV_0 + θε⁵` and `NV_τ ≥ NV_0 - θε⁵`;
* the cases are `τ = T` versus `1 ≤ τ < T`; the norm bound carries the factor `‖f‖₂²` with the
  explicit rate `x^t`, `x = γ²/(18C)`; the probability is the explicit chained product
  `(γ⁴ x^T ‖f‖₂² / (36 C B²))^T`;
* `swapTlarge_good_prob` assumes `0 < T` (the printed form is false at `T = 0`).

The probability bound chains `lemma:iter` (`swapIter_step_success`) along the adaptive stopping time:
with `E_k` the event that every step before `min(τ, k)` succeeds, `P[E_{k+1}] ≥ P[E_k] · p` where `p`
is the product above; the conditioning on the first `k` step coins is done by resampling the `k`-th
coin, which the run before step `k` does not read.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapTlarge
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the event `E` of CSP_6 `lemma:tlarge#success-probability`: the conclusion of `lemma:iter` holds at
every step `t < τ` before the stopping time. -/
def swapIterGood (C γ : ℝ) (T : ℕ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (c₀ : SwapCoins ι α) (ω : Fin T → SwapCoins ι α) : Prop :=
  ∀ t, t < swapIterTau γ T sel f c₀ ω →
    swapIterPhi C sel f (swapIterRun c₀ ω t) t + γ ^ 2 / 4 ≤
        swapIterPhi C sel f (swapIterRun c₀ ω (t + 1)) (t + 1) ∧
      γ ^ 2 / (18 * C) * l2sq (swapIterF f (swapIterRun c₀ ω t)) ≤
        l2sq (swapIterF f (swapIterRun c₀ ω (t + 1)))

/-- CSP_6 `lemma:tlarge`, the two cases (with the weight `C = (θ ε⁵)⁻¹`): Case 1 is `τ = T`, Case 2 is
`1 ≤ τ < T`. -/
def swapIterOutcome (θ ε γ : ℝ) (T : ℕ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (c₀ : SwapCoins ι α) (ω : Fin T → SwapCoins ι α) : Prop :=
  (swapIterTau γ T sel f c₀ ω = T ∧
      swapIterNV f (swapIterRun c₀ ω 0) + θ * ε ^ 5 ≤ swapIterNV f (swapIterRun c₀ ω T) ∧
      ∀ t, t ≤ T → (γ ^ 2 / (18 * (θ * ε ^ 5)⁻¹)) ^ t * l2sq f ≤
        l2sq (swapIterF f (swapIterRun c₀ ω t))) ∨
    (1 ≤ swapIterTau γ T sel f c₀ ω ∧ swapIterTau γ T sel f c₀ ω < T ∧
      ((val (swapIterDelta sel f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))
          (swapIterTau γ T sel f c₀ ω))
        (swapIterDelta sel f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))
          (swapIterTau γ T sel f c₀ ω))
        (swapIterDelta sel f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))
          (swapIterTau γ T sel f c₀ ω))
        (swapIterDelta sel f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))
          (swapIterTau γ T sel f c₀ ω))).re) ^ (1 / 2 : ℝ) <
        γ * l2sq (swapIterF f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))) ∧
      swapIterNV f (swapIterRun c₀ ω 0) - θ * ε ^ 5 ≤
        swapIterNV f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω)) ∧
      ∀ t, t ≤ swapIterTau γ T sel f c₀ ω → (γ ^ 2 / (18 * (θ * ε ^ 5)⁻¹)) ^ t * l2sq f ≤
        l2sq (swapIterF f (swapIterRun c₀ ω t)))

/-! ### Helpers: the run, the stopping time, the potential -/

/-- the success event of step `t` (the conclusion of `lemma:iter` at time `t`). -/
private def tlSucc (C γ : ℝ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (t : ℕ) : Prop :=
  swapIterPhi C sel f (swapIterRun c₀ ω t) t + γ ^ 2 / 4 ≤
      swapIterPhi C sel f (swapIterRun c₀ ω (t + 1)) (t + 1) ∧
    γ ^ 2 / (18 * C) * l2sq (swapIterF f (swapIterRun c₀ ω t)) ≤
      l2sq (swapIterF f (swapIterRun c₀ ω (t + 1)))

/-- the event `E_k`: every step before `min(τ, k)` succeeds. -/
private def tlEvent (C γ : ℝ) (T : ℕ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) (k : ℕ)
    (c₀ : SwapCoins ι α) (ω : Fin T → SwapCoins ι α) : Prop :=
  ∀ t, t < k → t < swapIterTau γ T sel f c₀ ω → tlSucc C γ sel f c₀ ω t

/-- monotonicity of indicators. -/
private lemma tl_ind_mono {A₁ A₂ : Prop} {d₁ : Decidable A₁} {d₂ : Decidable A₂} (h : A₁ → A₂) :
    (@ite ℝ A₁ d₁ 1 0) ≤ (@ite ℝ A₂ d₂ 1 0) := by
  by_cases hA : A₁
  · rw [ite_eq_left hA, ite_eq_left (h hA)]
  · rw [ite_eq_right hA]; split_ifs <;> norm_num

private lemma tl_l2sq_le_of_bound {κ β : Type} [Fintype κ] [DecidableEq κ] [Fintype β]
    [DecidableEq β] (F : (κ → β) → ℂ) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) : l2sq F ≤ B ^ 2 := by
  rw [l2sq]
  rcases isEmpty_or_nonempty (κ → β) with hn | hn
  · simp only [Finset.univ_eq_empty, Finset.expect_empty]
    positivity
  · calc 𝔼 x : κ → β, ‖F x‖ ^ 2 ≤ 𝔼 _x : κ → β, B ^ 2 :=
          Finset.expect_le_expect (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)
      _ = B ^ 2 := Fintype.expect_const _

private lemma tl_val_rpow_half_le_l2sq {κ β : Type} [Fintype κ] [DecidableEq κ] [Fintype β]
    [DecidableEq β] (F : (κ → β) → ℂ) : ((val F F F F).re) ^ (1 / 2 : ℝ) ≤ l2sq F := by
  rw [← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_iff.2 ⟨l2sq_nonneg F, ?_⟩
  refine (Complex.re_le_norm _).trans ((norm_val_le F F F F).trans_eq ?_)
  have h2 : Real.sqrt (l2sq F) * Real.sqrt (l2sq F) = l2sq F :=
    Real.mul_self_sqrt (l2sq_nonneg F)
  calc _ = (Real.sqrt (l2sq F) * Real.sqrt (l2sq F)) *
        (Real.sqrt (l2sq F) * Real.sqrt (l2sq F)) := by ring
    _ = _ := by rw [h2]; ring

omit [Fintype α] [DecidableEq α] in
/-- `f_0 = f`. -/
private lemma tl_F_zero (f : (ι → α) → ℂ) {K : ℕ} (c₀ : SwapCoins ι α)
    (ω : Fin K → SwapCoins ι α) : swapIterF f (swapIterRun c₀ ω 0) = f := by
  funext x
  simp [swapIterF, swapIterFun, swapIterRun, swapIterInit]

omit [DecidableEq α] in
/-- the empty truncation vanishes. -/
private lemma tl_trunc_zero {J : Finset ι} {g : (ι → α) → ℂ} (d : SwapSvdData J g) :
    d.trunc 0 = 0 := by
  funext x
  simp [SwapSvdData.trunc, SwapSvdData.truncOn]

/-- `Δ_0 = f_0`. -/
private lemma tl_delta_zero (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) (st : SwapIterState ι α) :
    swapIterDelta sel f st 0 = swapIterF f st := by
  funext x
  simp only [swapIterDelta, tl_trunc_zero, Pi.zero_apply, sub_zero]

omit [Fintype α] [DecidableEq α] in
/-- the run up to time `k` does not read the `k`-th step coin. -/
private lemma tl_run_update {K : ℕ} (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) {k : ℕ}
    (hk : k < K) (v : SwapCoins ι α) :
    ∀ s ≤ k, swapIterRun c₀ (Function.update ω ⟨k, hk⟩ v) s = swapIterRun c₀ ω s := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have h1 : s < K := by omega
    simp only [swapIterRun, h1, ↓reduceDIte]
    rw [ih (by omega), Function.update_of_ne]
    intro h
    rw [Fin.ext_iff] at h
    simp only at h
    omega

omit [Fintype α] [DecidableEq α] in
/-- step `k` with a resampled `k`-th coin. -/
private lemma tl_run_update_succ {K : ℕ} (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) {k : ℕ}
    (hk : k < K) (v : SwapCoins ι α) :
    swapIterRun c₀ (Function.update ω ⟨k, hk⟩ v) (k + 1) = swapIterStep (swapIterRun c₀ ω k) v := by
  simp only [swapIterRun, hk, ↓reduceDIte]
  rw [tl_run_update c₀ ω hk v k le_rfl, Function.update_self]

/-- `t < τ` iff the scheme has not stopped at any time `s ≤ t`. -/
private lemma tl_lt_tau_iff (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {γ : ℝ} {T K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (t : ℕ) :
    t < swapIterTau γ T sel f c₀ ω ↔
      ∀ s ≤ t, ¬ swapIterStopped γ T sel f (swapIterRun c₀ ω s) s := by
  have hne : {s | swapIterStopped γ T sel f (swapIterRun c₀ ω s) s}.Nonempty :=
    ⟨T, show swapIterStopped γ T sel f (swapIterRun c₀ ω T) T from Or.inr le_rfl⟩
  constructor
  · intro ht s hs hstop
    have := Nat.sInf_le (s := {s | swapIterStopped γ T sel f (swapIterRun c₀ ω s) s}) hstop
    unfold swapIterTau at ht
    omega
  · intro h
    by_contra hcon
    exact h _ (not_lt.1 hcon) (Nat.sInf_mem hne)

/-- `τ ≤ T`. -/
private lemma tl_tau_le (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {γ : ℝ} {T K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) : swapIterTau γ T sel f c₀ ω ≤ T :=
  Nat.sInf_le (show swapIterStopped γ T sel f (swapIterRun c₀ ω T) T from Or.inr le_rfl)

/-- the scheme is stopped at `τ`. -/
private lemma tl_tau_stopped (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {γ : ℝ} {T K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) :
    swapIterStopped γ T sel f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))
      (swapIterTau γ T sel f c₀ ω) :=
  Nat.sInf_mem (s := {s | swapIterStopped γ T sel f (swapIterRun c₀ ω s) s})
    ⟨T, show swapIterStopped γ T sel f (swapIterRun c₀ ω T) T from Or.inr le_rfl⟩

/-- two runs that agree up to time `k` have the same `t < τ` for `t ≤ k`. -/
private lemma tl_lt_tau_congr (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {γ : ℝ} {T K : ℕ}
    (c₀ : SwapCoins ι α) (ω₁ ω₂ : Fin K → SwapCoins ι α) (k : ℕ)
    (h : ∀ s ≤ k, swapIterRun c₀ ω₁ s = swapIterRun c₀ ω₂ s) (t : ℕ) (ht : t ≤ k) :
    t < swapIterTau γ T sel f c₀ ω₁ ↔ t < swapIterTau γ T sel f c₀ ω₂ := by
  rw [tl_lt_tau_iff, tl_lt_tau_iff]
  constructor
  · intro H s hs
    rw [← h s (hs.trans ht)]
    exact H s hs
  · intro H s hs
    rw [h s (hs.trans ht)]
    exact H s hs

/-- the norm rate along successful steps: `‖f_t‖₂² ≥ x^t ‖f‖₂²`. -/
private lemma tl_norm_chain (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {C γ : ℝ} {K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (hx0 : 0 ≤ γ ^ 2 / (18 * C)) (k : ℕ)
    (h : ∀ t < k, tlSucc C γ sel f c₀ ω t) :
    ∀ t ≤ k, (γ ^ 2 / (18 * C)) ^ t * l2sq f ≤ l2sq (swapIterF f (swapIterRun c₀ ω t)) := by
  intro t
  induction t with
  | zero => intro _; rw [pow_zero, one_mul, tl_F_zero]
  | succ t ih =>
    intro ht
    have h1 := (h t ht).2
    calc (γ ^ 2 / (18 * C)) ^ (t + 1) * l2sq f
        = γ ^ 2 / (18 * C) * ((γ ^ 2 / (18 * C)) ^ t * l2sq f) := by ring
      _ ≤ γ ^ 2 / (18 * C) * l2sq (swapIterF f (swapIterRun c₀ ω t)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hx0
      _ ≤ _ := h1

/-- the potential rises by `γ²/4` at each successful step. -/
private lemma tl_phi_chain (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {C γ : ℝ} {K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (k : ℕ)
    (h : ∀ t < k, tlSucc C γ sel f c₀ ω t) :
    ∀ t ≤ k, swapIterPhi C sel f (swapIterRun c₀ ω 0) 0 + (t : ℝ) * (γ ^ 2 / 4) ≤
      swapIterPhi C sel f (swapIterRun c₀ ω t) t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := (h t ht).1
    have h2 := ih (by omega)
    push_cast
    linarith

/-- `Φ_t ≤ C · NV_t` (as `‖Δ_t‖₂² ≥ 0`). -/
private lemma tl_phi_le (C : ℝ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (st : SwapIterState ι α) (t : ℕ) : swapIterPhi C sel f st t ≤ C * swapIterNV f st := by
  unfold swapIterPhi swapIterNV
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (by linarith [l2sq_nonneg (swapIterDelta sel f st t)]) (l2sq_nonneg _)

/-- `Φ_0 = C · NV_0 - 1` (as `Δ_0 = f_0 = f`). -/
private lemma tl_phi_zero (C : ℝ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (hL : 0 < l2sq f) :
    swapIterPhi C sel f (swapIterRun c₀ ω 0) 0 = C * swapIterNV f (swapIterRun c₀ ω 0) - 1 := by
  unfold swapIterPhi swapIterNV
  rw [tl_delta_zero, tl_F_zero]
  field_simp

/-- rescaling by `P = C⁻¹`. -/
private lemma tl_scale {P C a b d : ℝ} (hP : 0 < P) (hCP : C * P = 1) (h : C * a + d ≤ C * b) :
    a + P * d ≤ b := by
  have h1 := mul_le_mul_of_nonneg_left h hP.le
  have e1 : P * (C * a + d) = a + P * d := by
    rw [mul_add, ← mul_assoc, mul_comm P C, hCP, one_mul]
  have e2 : P * (C * b) = b := by rw [← mul_assoc, mul_comm P C, hCP, one_mul]
  linarith

/-- resampling one coordinate of a uniform vector does not change expectations. -/
private lemma tl_resample {X : Type} [Fintype X] [Nonempty X] {n : ℕ} (i : Fin n)
    (G : (Fin n → X) → ℝ) :
    𝔼 ω : Fin n → X, 𝔼 v : X, G (Function.update ω i v) = 𝔼 ω : Fin n → X, G ω := by
  let e : (Fin n → X) × X ≃ (Fin n → X) × X :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  calc 𝔼 ω : Fin n → X, 𝔼 v : X, G (Function.update ω i v)
      = 𝔼 p : (Fin n → X) × X, G (Function.update p.1 i p.2) := by
        rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = 𝔼 p : (Fin n → X) × X, G p.1 := Fintype.expect_equiv e _ _ (fun p => rfl)
    _ = 𝔼 ω : Fin n → X, G ω := by
        rw [← Finset.univ_product_univ, Finset.expect_product]
        simp only [Fintype.expect_const]

open scoped Classical in
/-- one step of the chaining: conditionally on the first `k` step coins, on `E_k`, the event
`E_{k+1}` has probability at least `p = γ⁴ x^T ‖f‖₂² / (36 C B²)` over the `k`-th coin. -/
private lemma tl_step (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {B C γ : ℝ} {T : ℕ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hC : 1 < C) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hq1 : γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f / (36 * C * B ^ 2) ≤ 1)
    (k : ℕ) (hk : k < T) (c₀ : SwapCoins ι α) (ω : Fin T → SwapCoins ι α)
    (hE : tlEvent C γ T sel f k c₀ ω) :
    γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f / (36 * C * B ^ 2) ≤
      𝔼 v : SwapCoins ι α,
        if tlEvent C γ T sel f (k + 1) c₀ (Function.update ω ⟨k, hk⟩ v) then (1 : ℝ) else 0 := by
  have hC0 : 0 < C := by linarith
  have hx0 : 0 ≤ γ ^ 2 / (18 * C) := by positivity
  have hx1 : γ ^ 2 / (18 * C) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have : Nonempty (SwapCoins ι α) := ⟨ω ⟨k, hk⟩⟩
  -- the run before step `k` does not see the resampled coin
  have hrun : ∀ v, ∀ s ≤ k,
      swapIterRun c₀ (Function.update ω ⟨k, hk⟩ v) s = swapIterRun c₀ ω s :=
    fun v s hs => tl_run_update c₀ ω hk v s hs
  have hsucc : ∀ v, ∀ t < k, tlSucc C γ sel f c₀ ω t →
      tlSucc C γ sel f c₀ (Function.update ω ⟨k, hk⟩ v) t := by
    intro v t ht h
    unfold tlSucc at h ⊢
    rw [hrun v t ht.le, hrun v (t + 1) ht]
    exact h
  have htau : ∀ v, ∀ t ≤ k, (t < swapIterTau γ T sel f c₀ (Function.update ω ⟨k, hk⟩ v) ↔
      t < swapIterTau γ T sel f c₀ ω) :=
    fun v t ht => tl_lt_tau_congr sel f c₀ _ ω k (hrun v) t ht
  by_cases hτ : k < swapIterTau γ T sel f c₀ ω
  · -- the step is taken: `lemma:iter`
    have hall : ∀ t < k, tlSucc C γ sel f c₀ ω t := fun t ht => hE t ht (lt_trans ht hτ)
    have hnorm : (γ ^ 2 / (18 * C)) ^ k * l2sq f ≤ l2sq (swapIterF f (swapIterRun c₀ ω k)) :=
      tl_norm_chain sel f c₀ ω hx0 k hall k le_rfl
    have hstop : γ * l2sq (swapIterF f (swapIterRun c₀ ω k)) ≤
        ((val (swapIterDelta sel f (swapIterRun c₀ ω k) k)
          (swapIterDelta sel f (swapIterRun c₀ ω k) k)
          (swapIterDelta sel f (swapIterRun c₀ ω k) k)
          (swapIterDelta sel f (swapIterRun c₀ ω k) k)).re) ^ (1 / 2 : ℝ) := by
      have h := (tl_lt_tau_iff sel f c₀ ω k).1 hτ k le_rfl
      unfold swapIterStopped at h
      exact not_lt.1 fun h' => h (Or.inl h')
    have hstep := swapIter_step_success sel f hB hC hγ0 hγ1 (swapIterRun c₀ ω k)
      (swapIterRun_S_subset c₀ ω k) k hstop
    refine le_trans ?_ (hstep.trans (Finset.expect_le_expect fun v _ => tl_ind_mono ?_))
    · -- `p ≤ γ⁴ ‖f_k‖₂² / (36 C B²)`
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hxk : (γ ^ 2 / (18 * C)) ^ T ≤ (γ ^ 2 / (18 * C)) ^ k :=
        pow_le_pow_of_le_one hx0 hx1 hk.le
      have hL0 := l2sq_nonneg f
      calc γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f
          ≤ γ ^ 4 * ((γ ^ 2 / (18 * C)) ^ k * l2sq f) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxk hL0) (by positivity)
        _ ≤ γ ^ 4 * l2sq (swapIterF f (swapIterRun c₀ ω k)) :=
            mul_le_mul_of_nonneg_left hnorm (by positivity)
    · intro hs t ht htv
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | rfl
      · exact hsucc v t ht' (hE t ht' ((htau v t ht'.le).1 htv))
      · unfold tlSucc
        rw [hrun v t le_rfl, tl_run_update_succ c₀ ω hk v]
        exact hs
  · -- already stopped: the event holds for every coin
    have hone : ∀ v, tlEvent C γ T sel f (k + 1) c₀ (Function.update ω ⟨k, hk⟩ v) := by
      intro v t ht htv
      have ht' : t ≤ k := Nat.lt_succ_iff.1 ht
      have h1 : t < swapIterTau γ T sel f c₀ ω := (htau v t ht').1 htv
      have h2 : t < k := lt_of_lt_of_le h1 (not_lt.1 hτ)
      exact hsucc v t h2 (hE t h2 h1)
    have h1 : (𝔼 v : SwapCoins ι α,
        if tlEvent C γ T sel f (k + 1) c₀ (Function.update ω ⟨k, hk⟩ v) then (1 : ℝ) else 0) = 1 := by
      rw [Finset.expect_congr rfl (fun v _ => ite_eq_left (hone v)), Fintype.expect_const]
    rw [h1]
    exact hq1

/-! ### The targets -/

open scoped Classical in
/-- CSP_6 `lemma:tlarge#success-probability` (with `0 < T`). -/
theorem swapTlarge_good_prob (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {B C γ : ℝ} (T : ℕ)
    (hT : 0 < T) (hB : ∀ x, ‖f x‖ ≤ B) (hC : 1 < C) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f / (36 * C * B ^ 2)) ^ T ≤
      𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α,
        if swapIterGood C γ T sel f c₀ ω then (1 : ℝ) else 0 := by
  have hC0 : 0 < C := by linarith
  have hL0 := l2sq_nonneg f
  have hq0 : 0 ≤ γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f / (36 * C * B ^ 2) := by positivity
  rcases hL0.eq_or_lt with hL0' | hLpos
  · rw [← hL0', mul_zero, zero_div, zero_pow hT.ne']
    exact Finset.expect_nonneg fun c₀ _ => Finset.expect_nonneg fun ω _ => by
      split_ifs <;> norm_num
  obtain ⟨w₀⟩ : Nonempty (ι → α) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [l2sq] at hLpos
  have : Nonempty (SwapCoins ι α) := ⟨(fun _ => true, w₀)⟩
  have hLB : l2sq f ≤ B ^ 2 := tl_l2sq_le_of_bound f hB
  have hB2 : 0 < B ^ 2 := lt_of_lt_of_le hLpos hLB
  have hx0 : 0 ≤ γ ^ 2 / (18 * C) := by positivity
  have hx1 : γ ^ 2 / (18 * C) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hq1 : γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f / (36 * C * B ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hγ4 : γ ^ 4 ≤ 1 := pow_le_one₀ hγ0.le hγ1
    have hxT : (γ ^ 2 / (18 * C)) ^ T ≤ 1 := pow_le_one₀ hx0 hx1
    have h1 : γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T ≤ 1 :=
      calc γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T ≤ 1 * 1 :=
            mul_le_mul hγ4 hxT (by positivity) zero_le_one
        _ = 1 := one_mul 1
    calc γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f ≤ 1 * l2sq f :=
          mul_le_mul_of_nonneg_right h1 hL0
      _ ≤ 36 * C * B ^ 2 := by nlinarith
  set q := γ ^ 4 * (γ ^ 2 / (18 * C)) ^ T * l2sq f / (36 * C * B ^ 2) with hq
  have key : ∀ k, k ≤ T → q ^ k ≤ 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α,
      if tlEvent C γ T sel f k c₀ ω then (1 : ℝ) else 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      have h1 : ∀ c₀ ω, (if tlEvent C γ T sel f 0 c₀ ω then (1 : ℝ) else 0) = 1 :=
        fun c₀ ω => ite_eq_left (fun t ht => absurd ht (Nat.not_lt_zero t))
      simp only [h1, Fintype.expect_const, pow_zero, le_refl]
    | succ k ih =>
      intro hk
      have hkT : k < T := hk
      calc q ^ (k + 1) = q * q ^ k := pow_succ' q k
        _ ≤ q * 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α,
              (if tlEvent C γ T sel f k c₀ ω then (1 : ℝ) else 0) :=
            mul_le_mul_of_nonneg_left (ih hkT.le) hq0
        _ = 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α,
              q * (if tlEvent C γ T sel f k c₀ ω then (1 : ℝ) else 0) := by
            simp_rw [Finset.mul_expect]
        _ ≤ 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α, 𝔼 v : SwapCoins ι α,
              (if tlEvent C γ T sel f (k + 1) c₀ (Function.update ω ⟨k, hkT⟩ v)
                then (1 : ℝ) else 0) := by
            refine Finset.expect_le_expect fun c₀ _ => Finset.expect_le_expect fun ω _ => ?_
            by_cases hE : tlEvent C γ T sel f k c₀ ω
            · rw [ite_eq_left hE, mul_one]
              exact tl_step sel f hB hC hγ0 hγ1 hq1 k hkT c₀ ω hE
            · rw [ite_eq_right hE, mul_zero]
              exact Finset.expect_nonneg fun v _ => by split_ifs <;> norm_num
        _ = 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α,
              (if tlEvent C γ T sel f (k + 1) c₀ ω then (1 : ℝ) else 0) := by
            refine Finset.expect_congr rfl fun c₀ _ => ?_
            exact tl_resample ⟨k, hkT⟩
              (fun ω => if tlEvent C γ T sel f (k + 1) c₀ ω then (1 : ℝ) else 0)
  refine (key T le_rfl).trans ?_
  refine Finset.expect_le_expect fun c₀ _ => Finset.expect_le_expect fun ω _ => ?_
  exact tl_ind_mono fun hE t ht => hE t (lt_of_lt_of_le ht (tl_tau_le sel f c₀ ω)) ht

/-- CSP_6 `lemma:tlarge`, the deterministic part: on the event `E`, Case 1 or Case 2. -/
theorem swapTlarge_cases (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {B ε θ γ : ℝ} {T : ℕ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hε0 : 0 < ε) (hε1 : ε < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hγ0 : 0 < γ) (hγε : γ < ε ^ 2) (hT : 8 / γ ^ 2 ≤ (T : ℝ)) (hl2 : l2sq f ≤ 1)
    (hv : ε ^ 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ))
    (c₀ : SwapCoins ι α) (ω : Fin T → SwapCoins ι α)
    (hG : swapIterGood (θ * ε ^ 5)⁻¹ γ T sel f c₀ ω) :
    swapIterOutcome θ ε γ T sel f c₀ ω := by
  have hP0 : 0 < θ * ε ^ 5 := by positivity
  have hCP : (θ * ε ^ 5)⁻¹ * (θ * ε ^ 5) = 1 := inv_mul_cancel₀ hP0.ne'
  have hC0 : 0 < (θ * ε ^ 5)⁻¹ := inv_pos.2 hP0
  have hall : ∀ t < swapIterTau γ T sel f c₀ ω, tlSucc (θ * ε ^ 5)⁻¹ γ sel f c₀ ω t :=
    fun t ht => hG t ht
  have hvl := tl_val_rpow_half_le_l2sq f
  have hε2 : 0 < ε ^ 2 := by positivity
  have hLf : 0 < l2sq f := by linarith
  have hx0 : 0 ≤ γ ^ 2 / (18 * (θ * ε ^ 5)⁻¹) := by positivity
  have hnorm := tl_norm_chain sel f c₀ ω hx0 _ hall
  have hphi := tl_phi_chain sel f c₀ ω _ hall
  have hphi0 := tl_phi_zero (θ * ε ^ 5)⁻¹ sel f c₀ ω hLf
  have hτT := tl_tau_le sel f (γ := γ) (T := T) c₀ ω
  have hstopτ := tl_tau_stopped sel f (γ := γ) (T := T) c₀ ω
  -- `C (NV_τ - NV_0) ≥ τ γ²/4 - 1`
  have hmain : (θ * ε ^ 5)⁻¹ * swapIterNV f (swapIterRun c₀ ω 0) +
      ((swapIterTau γ T sel f c₀ ω : ℝ) * (γ ^ 2 / 4) - 1) ≤
      (θ * ε ^ 5)⁻¹ * swapIterNV f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω)) := by
    have h1 := hphi _ le_rfl
    have h2 := tl_phi_le (θ * ε ^ 5)⁻¹ sel f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))
      (swapIterTau γ T sel f c₀ ω)
    rw [hphi0] at h1
    linarith
  have hγT : 8 ≤ (T : ℝ) * γ ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hT
    linarith
  rcases Nat.lt_or_ge (swapIterTau γ T sel f c₀ ω) T with hlt | hge
  · -- Case 2: `1 ≤ τ < T`
    right
    refine ⟨?_, hlt, ?_, ?_, fun t ht => hnorm t ht⟩
    · by_contra h0
      have hτ0 : swapIterTau γ T sel f c₀ ω = 0 := by omega
      have hs := hstopτ
      rw [hτ0] at hs
      unfold swapIterStopped at hs
      rw [tl_delta_zero, tl_F_zero] at hs
      rcases hs with hs | hs
      · have : γ * l2sq f ≤ γ := mul_le_of_le_one_right hγ0.le hl2
        linarith
      · omega
    · rcases hstopτ with hs | hs
      · exact hs
      · omega
    · have hτ0 : (0 : ℝ) ≤ (swapIterTau γ T sel f c₀ ω : ℝ) * (γ ^ 2 / 4) := by positivity
      have h := tl_scale hP0 hCP (a := swapIterNV f (swapIterRun c₀ ω 0))
        (b := swapIterNV f (swapIterRun c₀ ω (swapIterTau γ T sel f c₀ ω))) (d := -1)
        (by linarith)
      linarith
  · -- Case 1: `τ = T`
    have hτ : swapIterTau γ T sel f c₀ ω = T := le_antisymm hτT hge
    left
    refine ⟨hτ, ?_, fun t ht => hnorm t (le_of_le_of_eq ht hτ.symm)⟩
    rw [hτ] at hmain
    have h := tl_scale hP0 hCP (a := swapIterNV f (swapIterRun c₀ ω 0))
      (b := swapIterNV f (swapIterRun c₀ ω T)) (d := 1) (by linarith)
    linarith

open scoped Classical in
/-- CSP_6 `lemma:tlarge`: with probability at least `(…)^T`, Case 1 or Case 2. -/
theorem swapTlarge (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {B ε θ γ : ℝ} {T : ℕ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hε0 : 0 < ε) (hε1 : ε < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγε : γ < ε ^ 2) (hT : 8 / γ ^ 2 ≤ (T : ℝ))
    (hl2 : l2sq f ≤ 1) (hv : ε ^ 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ)) :
    (γ ^ 4 * (γ ^ 2 / (18 * (θ * ε ^ 5)⁻¹)) ^ T * l2sq f / (36 * (θ * ε ^ 5)⁻¹ * B ^ 2)) ^ T ≤
      𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin T → SwapCoins ι α,
        if swapIterOutcome θ ε γ T sel f c₀ ω then (1 : ℝ) else 0 := by
  have hT0 : 0 < T := by
    have h8 : (0 : ℝ) < 8 / γ ^ 2 := by positivity
    exact_mod_cast h8.trans_le hT
  have hP0 : 0 < θ * ε ^ 5 := by positivity
  have hC : 1 < (θ * ε ^ 5)⁻¹ := by
    have h5 : ε ^ 5 < 1 := pow_lt_one₀ hε0.le hε1 (by norm_num)
    have hP1 : θ * ε ^ 5 < 1 :=
      calc θ * ε ^ 5 ≤ 1 * ε ^ 5 := mul_le_mul_of_nonneg_right hθ1 (by positivity)
        _ < 1 := by rw [one_mul]; exact h5
    exact (one_lt_inv₀ hP0).2 hP1
  refine (swapTlarge_good_prob sel f T hT0 hB hC hγ0 hγ1).trans ?_
  refine Finset.expect_le_expect fun c₀ _ => Finset.expect_le_expect fun ω _ => ?_
  exact tl_ind_mono (swapTlarge_cases sel f hB hε0 hε1 hθ0 hθ1 hγ0 hγε hT hl2 hv c₀ ω)

end SwapTlarge
end TrackB
end RestrictedPolynomials
end
