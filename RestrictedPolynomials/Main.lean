import RestrictedPolynomials.Increment
import RestrictedPolynomials.NoEmbedding
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Proof of Theorem 1.1

The parameters of Section 6: given the density `α₀`,
* `ε₀ = α₀^k / (2(2^k - 1))`;
* `δ₀ = exp(-exp^{(K)}(ε₀^{-b}))`, `K = k^{C₀ k}`, with `b ≥ 1` (enlarging `b` is harmless);
* `d = max(2, ⌈δ₀⁻¹ log(2/δ₀)⌉)`;
* `N = max(⌈2d² log(32/δ₀)⌉, ⌈log₂ α₀^{1-k}⌉ + 1)`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-! ### Iterated exponentials and logarithms -/

lemma le_exp_iterate (j : ℕ) (y : ℝ) : y ≤ Real.exp^[j] y := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact le_trans (by linarith [Real.add_one_le_exp y]) (ih (Real.exp y))

lemma exp_iterate_mono (j : ℕ) : Monotone (Real.exp^[j]) := Real.exp_monotone.iterate j

lemma exp_iterate_le_succ (j : ℕ) (y : ℝ) : Real.exp^[j] y ≤ Real.exp^[j + 1] y := by
  rw [Function.iterate_succ_apply]
  exact exp_iterate_mono j (by linarith [Real.add_one_le_exp y])

lemma exp_iterate_le_of_le {j j' : ℕ} (h : j ≤ j') (y : ℝ) : Real.exp^[j] y ≤ Real.exp^[j'] y := by
  induction j', h using Nat.le_induction with
  | base => rfl
  | succ j' _ ih => exact ih.trans (exp_iterate_le_succ j' y)

lemma exp_add_two_ge {a : ℝ} (ha : 0 ≤ a) : Real.exp a + 2 ≤ Real.exp (a + 2) := by
  rw [Real.exp_add]
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h1 : (1 : ℝ) ≤ Real.exp a := Real.one_le_exp ha
  nlinarith

lemma exp_iterate_add_two (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp^[j] y + 2 ≤ Real.exp^[j] (y + 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc Real.exp (Real.exp^[j] y) + 2 ≤ Real.exp (Real.exp^[j] y + 2) :=
          exp_add_two_ge (hy.trans (le_exp_iterate j y))
      _ ≤ Real.exp (Real.exp^[j] (y + 2)) := Real.exp_le_exp.2 ih

/-- If `exp^{(j)}(1) ≤ a < exp^{(j)}(y)`, then `1 ≤ log^{(j)} a < y`. -/
lemma log_iterate_bounds (j : ℕ) {a y : ℝ} (h1 : Real.exp^[j] 1 ≤ a) (h2 : a < Real.exp^[j] y) :
    1 ≤ Real.log^[j] a ∧ Real.log^[j] a < y := by
  induction j generalizing a with
  | zero => exact ⟨h1, h2⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at h1 h2
    have ha : 0 < a := lt_of_lt_of_le (Real.exp_pos _) h1
    rw [Function.iterate_succ_apply]
    refine ih ?_ ?_
    · rw [← Real.log_exp (Real.exp^[j] 1)]
      exact Real.log_le_log (Real.exp_pos _) h1
    · rw [← Real.log_exp (Real.exp^[j] y)]
      exact Real.log_lt_log ha h2

/-! ### Monotonicity of the inverse-theorem parameter -/

lemma inverseDelta_pos (C₀ k : ℕ) (b ε : ℝ) : 0 < inverseDelta C₀ k b ε := Real.exp_pos _

lemma inverseDelta_anti {C₀ k : ℕ} {b b' ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hbb' : b ≤ b') :
    inverseDelta C₀ k b' ε ≤ inverseDelta C₀ k b ε := by
  unfold inverseDelta
  rw [Real.exp_le_exp, neg_le_neg_iff]
  refine exp_iterate_mono _ ?_
  exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (neg_le_neg hbb')

/-! ### The quantitative estimate -/

/-- The chain of elementary estimates at the end of Section 6: with `X = 1/δ₀ = exp(E)`,
`E = exp^{(K)}(x)`, `x ≥ 1`, one has `(2d)^m N < exp^{(K+2)}(3x)`. -/
lemma tower_bound {K : ℕ} (hK : 1 ≤ K) {x : ℝ} (hx : 1 ≤ x) {d m N : ℕ}
    (hd : (d : ℝ) ≤ 2 * Real.exp (Real.exp^[K] x) ^ 2)
    (hm : (m : ℝ) ≤ 33 * Real.exp (Real.exp^[K] x))
    (hN : (N : ℝ) ≤ 257 * Real.exp (Real.exp^[K] x) ^ 5) :
    (2 * d : ℝ) ^ m * N ≤ Real.exp^[K + 2] (3 * x) := by
  set E := Real.exp^[K] x with hE
  set X := Real.exp E with hX
  have hE1 : 1 ≤ E := hx.trans (le_exp_iterate K x)
  have hX1 : 1 ≤ X := Real.one_le_exp (by linarith)
  -- `2d ≤ e^{2X}`
  have h2d : (2 * d : ℝ) ≤ Real.exp (2 * X) := by
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ X by linarith)
    have : 2 * X ≤ Real.exp X := by nlinarith
    calc (2 * d : ℝ) ≤ 4 * X ^ 2 := by linarith
      _ = (2 * X) ^ 2 := by ring
      _ ≤ Real.exp X ^ 2 := by gcongr
      _ = Real.exp (2 * X) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2d0 : (0 : ℝ) ≤ 2 * d := by positivity
  have hpow : (2 * d : ℝ) ^ m ≤ Real.exp (66 * X ^ 2) := by
    calc (2 * d : ℝ) ^ m ≤ Real.exp (2 * X) ^ m := pow_le_pow_left₀ h2d0 h2d m
      _ = Real.exp (m * (2 * X)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (66 * X ^ 2) := by
          rw [Real.exp_le_exp]; nlinarith
  have hN' : (N : ℝ) ≤ Real.exp (5 * X + 6) := by
    have hXe : X ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
    have h6 : (257 : ℝ) ≤ Real.exp 6 := by
      have := Real.exp_one_gt_d9
      have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) (by linarith : (2.7 : ℝ) ≤ Real.exp 1) 6]
    calc (N : ℝ) ≤ 257 * X ^ 5 := hN
      _ ≤ Real.exp 6 * Real.exp X ^ 5 := by gcongr
      _ = Real.exp (5 * X + 6) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have hprod : (2 * d : ℝ) ^ m * N ≤ Real.exp (77 * X ^ 2) := by
    calc (2 * d : ℝ) ^ m * N ≤ Real.exp (66 * X ^ 2) * Real.exp (5 * X + 6) :=
          mul_le_mul hpow hN' (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (66 * X ^ 2 + (5 * X + 6)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (77 * X ^ 2) := by rw [Real.exp_le_exp]; nlinarith
  -- `77 X² ≤ exp(2E + 5)`
  have h77 : 77 * X ^ 2 ≤ Real.exp (2 * E + 5) := by
    have h5 : (77 : ℝ) ≤ Real.exp 5 := by
      have := Real.exp_one_gt_d9
      have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) (by linarith : (2.7 : ℝ) ≤ Real.exp 1) 5]
    calc 77 * X ^ 2 ≤ Real.exp 5 * X ^ 2 := by gcongr
      _ = Real.exp (2 * E + 5) := by
          rw [hX, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  -- `2E + 5 ≤ exp^{(K)}(x + 2)`
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hEK : 2 * E + 5 ≤ Real.exp^[K' + 1] (x + 2) := by
    rw [hE, Function.iterate_succ_apply', Function.iterate_succ_apply']
    set E' := Real.exp^[K'] x
    have hE'1 : 1 ≤ E' := hx.trans (le_exp_iterate K' x)
    have h1 : 2 * Real.exp E' + 5 ≤ Real.exp (E' + 2) := by
      rw [Real.exp_add]
      have h2 : (7 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_one_gt_d9
        have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]; nlinarith
      have := Real.one_le_exp (show (0 : ℝ) ≤ E' by linarith)
      nlinarith
    exact h1.trans (Real.exp_le_exp.2 (exp_iterate_add_two K' (by linarith)))
  calc (2 * d : ℝ) ^ m * N ≤ Real.exp (77 * X ^ 2) := hprod
    _ ≤ Real.exp (Real.exp (2 * E + 5)) := Real.exp_le_exp.2 h77
    _ ≤ Real.exp (Real.exp (Real.exp^[K' + 1] (x + 2))) :=
        Real.exp_le_exp.2 (Real.exp_le_exp.2 hEK)
    _ = Real.exp^[K' + 1 + 2] (x + 2) := by
        show _ = Real.exp^[K' + 1 + 1 + 1] (x + 2)
        conv_rhs => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    _ ≤ Real.exp^[K' + 1 + 2] (3 * x) := exp_iterate_mono _ (by linarith)

lemma one_le_log_iterate (j : ℕ) {a : ℝ} (h : Real.exp^[j] 1 ≤ a) : 1 ≤ Real.log^[j] a :=
  (log_iterate_bounds j h (lt_of_lt_of_le (lt_add_one a) (le_exp_iterate j (a + 1)))).1

/-! ### Elementary estimates for the parameters -/

lemma bound_d {X δ : ℝ} (hX1 : 1 ≤ X) (hδX : 1 / δ = X) :
    ((max 2 ⌈1 / δ * Real.log (2 / δ)⌉₊ : ℕ) : ℝ) ≤ 2 * X ^ 2 := by
  have h2δ : 2 / δ = 2 * X := by rw [← hδX]; ring
  rw [Nat.cast_max, hδX, h2δ]
  refine max_le (by push_cast; nlinarith) ?_
  have hlog : Real.log (2 * X) ≤ 2 * X - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hpos : 0 ≤ X * Real.log (2 * X) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have h1 := Nat.ceil_lt_add_one hpos
  have h2 : X * Real.log (2 * X) ≤ X * (2 * X - 1) := mul_le_mul_of_nonneg_left hlog (by linarith)
  nlinarith

lemma bound_m {X δ : ℝ} (hX1 : 1 ≤ X) (hδX : 1 / δ = X) : (⌈32 / δ⌉₊ : ℝ) ≤ 33 * X := by
  have h32 : 32 / δ = 32 * X := by rw [← hδX]; ring
  rw [h32]
  have := Nat.ceil_lt_add_one (show 0 ≤ 32 * X by linarith)
  linarith

lemma bound_N₁ {X δ : ℝ} {d : ℕ} (hX1 : 1 ≤ X) (hδX : 1 / δ = X) (hd : (d : ℝ) ≤ 2 * X ^ 2) :
    (⌈2 * (d : ℝ) ^ 2 * Real.log (32 / δ)⌉₊ : ℝ) ≤ 257 * X ^ 5 := by
  have h32 : 32 / δ = 32 * X := by rw [← hδX]; ring
  rw [h32]
  have hlog : Real.log (32 * X) ≤ 32 * X := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 32 * X by linarith)]
  have hl0 : 0 ≤ Real.log (32 * X) := Real.log_nonneg (by linarith)
  have hpos : 0 ≤ 2 * (d : ℝ) ^ 2 * Real.log (32 * X) := by positivity
  have h1 := Nat.ceil_lt_add_one hpos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h2 : 2 * (d : ℝ) ^ 2 * Real.log (32 * X) ≤ 2 * (2 * X ^ 2) ^ 2 * (32 * X) := by
    gcongr
  have hX5 : (1 : ℝ) ≤ X ^ 5 := one_le_pow₀ hX1
  have : 2 * (2 * X ^ 2) ^ 2 * (32 * X) = 256 * X ^ 5 := by ring
  linarith

lemma bound_N₂ {α : ℝ} {k : ℕ} (hk : 1 ≤ k) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ((⌈Real.logb 2 ((1 / α) ^ (k - 1))⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * k / α := by
  have h1α : 1 ≤ 1 / α := by rw [le_div_iff₀ hα0]; linarith
  have hL0 : 0 ≤ Real.logb 2 ((1 / α) ^ (k - 1)) :=
    Real.logb_nonneg (by norm_num) (one_le_pow₀ h1α)
  have h1 := Nat.ceil_lt_add_one hL0
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl : Real.log (1 / α) ≤ 1 / α := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 / α by positivity)]
  have hl0 : 0 ≤ Real.log (1 / α) := Real.log_nonneg h1α
  have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by push_cast [hk]; ring
  have hL : Real.logb 2 ((1 / α) ^ (k - 1)) ≤ 2 * ((k : ℝ) - 1) * (1 / α) := by
    rw [Real.logb, Real.log_pow, hk', div_le_iff₀ (Real.log_pos (by norm_num))]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have := mul_le_mul_of_nonneg_left hl hk0
    nlinarith [mul_nonneg hk0 hl0]
  push_cast
  have h2 : 2 * ((k : ℝ) - 1) * (1 / α) + 2 ≤ 2 * k / α := by
    rw [mul_one_div, div_add' _ _ _ hα0.ne', div_le_div_iff_of_pos_right hα0]
    nlinarith
  linarith

/-! ### The dimension bound -/

/-- If `A ⊆ 𝔽_p^n` has density `α₀ > 0` and no nontrivial restricted progression, then
`n < exp^{(K+2)}(3 ε₀^{-b})` with `ε₀ = α₀^k / (2(2^k-1))`. -/
theorem dimension_bound {p k M : ℕ} [NeZero p] (hM : 2 ≤ M) (hk : 2 ≤ k) (hMp : M < p)
    {C₀ : ℕ} {b : ℝ} (hb : 1 ≤ b)
    (hinv : ∀ ε, 0 < ε → ε ≤ 1 → InverseHolds p k M hM ε (inverseDelta C₀ k b ε))
    {n : ℕ} (A : Finset (Fin n → ZMod p)) (hA : NoProgression p M k (A : Set (Fin n → ZMod p)))
    (hα : 0 < density A) :
    (n : ℝ) < Real.exp^[k ^ (C₀ * k) + 2] (3 * (density A ^ k / (2 * (2 ^ k - 1))) ^ (-b)) := by
  set α₀ := density A with hα₀
  have hα1 : α₀ ≤ 1 := density_le_one A
  have hk1 : 1 ≤ k := by omega
  have hk2 : (1 : ℝ) ≤ 2 ^ k - 1 := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
    linarith
  set ε₀ := α₀ ^ k / (2 * (2 ^ k - 1)) with hε₀
  have hε0 : 0 < ε₀ := by positivity
  have hε1 : ε₀ ≤ 1 := by
    rw [hε₀, div_le_one (by positivity)]
    have : α₀ ^ k ≤ 1 := pow_le_one₀ hα.le hα1
    linarith
  set x := ε₀ ^ (-b) with hx
  -- `x ≥ ε₀⁻¹ ≥ 2k/α₀ ≥ 1`
  have hxinv : ε₀⁻¹ ≤ x := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hkα : 2 * k / α₀ ≤ ε₀⁻¹ := by
    rw [hε₀, inv_div, div_le_div_iff₀ hα (by positivity)]
    have h2k : (k : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have hαk : α₀ ^ k ≤ α₀ := by
      calc α₀ ^ k ≤ α₀ ^ 1 := pow_le_pow_of_le_one hα.le hα1 hk1
        _ = α₀ := pow_one α₀
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith [pow_pos hα k, mul_le_mul_of_nonneg_left hαk hk0]
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ 2 * k / α₀ := by
      rw [le_div_iff₀ hα]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      nlinarith
    linarith
  -- the parameters
  set K := k ^ (C₀ * k) with hK
  have hK1 : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  set E := Real.exp^[K] x with hE
  have hE1 : 1 ≤ E := hx1.trans (le_exp_iterate K x)
  set δ₀ := inverseDelta C₀ k b ε₀ with hδ₀
  have hδE : δ₀ = Real.exp (-E) := rfl
  set X := Real.exp E with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (by linarith)
  have hδX : 1 / δ₀ = X := by rw [hδE, Real.exp_neg, one_div, inv_inv]
  have hδ0 : 0 < δ₀ := inverseDelta_pos _ _ _ _
  have hδ1 : δ₀ < 1 / 2 := by
    rw [hδE]
    have : Real.exp (-E) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9
      norm_num
      linarith
    linarith
  set d := max 2 ⌈1 / δ₀ * Real.log (2 / δ₀)⌉₊ with hd
  have hd2 : 2 ≤ d := le_max_left _ _
  have hdδ : 1 / δ₀ * Real.log (2 / δ₀) ≤ d := by
    have : ⌈1 / δ₀ * Real.log (2 / δ₀)⌉₊ ≤ d := le_max_right _ _
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr this)
  set N₁ := ⌈2 * (d : ℝ) ^ 2 * Real.log (32 / δ₀)⌉₊ with hN₁
  set L₀ := Real.logb 2 ((1 / α₀) ^ (k - 1)) with hL₀
  set N₂ := ⌈L₀⌉₊ + 1 with hN₂
  set N := max N₁ N₂ with hN
  have hN1 : 2 * (d : ℝ) ^ 2 * Real.log (32 / δ₀) ≤ N := by
    have : N₁ ≤ N := le_max_left _ _
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr this)
  have hz : 0 < (1 / α₀) ^ (k - 1) := by positivity
  have hN2 : 2 * (1 / α₀) ^ (k - 1) ≤ 2 ^ N := by
    calc 2 * (1 / α₀) ^ (k - 1) = 2 * (2 : ℝ) ^ L₀ := by
          rw [hL₀, Real.rpow_logb (by norm_num) (by norm_num) hz]
      _ ≤ 2 * (2 : ℝ) ^ ((⌈L₀⌉₊ : ℕ) : ℝ) := by
          gcongr
          · norm_num
          · exact Nat.le_ceil _
      _ = 2 ^ N₂ := by rw [Real.rpow_natCast, hN₂, pow_succ]; ring
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
  set m := ⌈32 / δ₀⌉₊ with hm
  -- run the iteration
  have hinc := fun (ι : Type) [Fintype ι] [DecidableEq ι] (B : Finset (ι → ZMod p))
      (hB : NoProgression p M k (B : Set (ι → ZMod p))) (hαB : α₀ ≤ density B)
      (hn : N ≤ Fintype.card ι) =>
    density_increment hM hk1 hMp (hinv ε₀ hε0 hε1) hδ0 hδ1 hd2 hdδ hα le_rfl hN1 hN2 ι hn B hB hαB
  have hmδ : 1 ≤ m * (δ₀ / 32) := by
    have h1 : 32 / δ₀ ≤ m := Nat.le_ceil _
    rw [div_le_iff₀ hδ0] at h1
    linarith
  have hiter := iteration (d := d) (N := N) hδ0 (by omega) hinc m (Fin n) A hA le_rfl
    (by linarith)
  rw [Fintype.card_fin] at hiter
  -- the tower estimate
  have hdX : (d : ℝ) ≤ 2 * X ^ 2 := bound_d hX1 hδX
  have hmX : (m : ℝ) ≤ 33 * X := bound_m hX1 hδX
  have hN₁X : (N₁ : ℝ) ≤ 257 * X ^ 5 := bound_N₁ hX1 hδX hdX
  have hN₂X : (N₂ : ℝ) ≤ 257 * X ^ 5 := by
    have h1 : (N₂ : ℝ) ≤ 2 * k / α₀ := bound_N₂ hk1 hα hα1
    have hxX : x ≤ X := (le_exp_iterate K x).trans (by linarith [Real.add_one_le_exp E])
    have hX5 : X ≤ X ^ 5 := le_self_pow₀ hX1 (by norm_num)
    linarith
  have hNX : (N : ℝ) ≤ 257 * X ^ 5 := by
    rw [hN, Nat.cast_max]; exact max_le hN₁X hN₂X
  exact lt_of_lt_of_le hiter (tower_bound hK1 hx1 hdX hmX hNX)

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1.** -/
theorem main_theorem : MainTheorem := by
  obtain ⟨C₀, hC₀⟩ := inverse_theorem_all_dims
  refine ⟨C₀ + 2, fun k hk => ?_⟩
  obtain ⟨M, P, hM, hMP⟩ := exists_M_P k hk
  refine ⟨M, P, fun p hp hPp => ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hMp1, hemb⟩ := hMP p hp hPp
  have hMp : M < p := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ < p := hMp1
  obtain ⟨b₀, hb₀, hinv₀⟩ := hC₀ k (ZMod p) (countingDist p k M hM) hemb
  set b := max b₀ 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hbpos : 0 < b := by linarith
  -- enlarging `b` only decreases `δ`
  have hinv : ∀ ε, 0 < ε → ε ≤ 1 → InverseHolds p k M hM ε (inverseDelta C₀ k b ε) := by
    intro ε hε0 hε1 ι _ _ f hf hcorr i
    have h := hinv₀ ε hε0 ι f hf hcorr i
    have hle : inverseDelta C₀ k b ε ≤ inverseDelta C₀ k b₀ ε :=
      inverseDelta_anti hε0 hε1 (le_max_left _ _)
    have hδ1 : inverseDelta C₀ k b₀ ε ≤ 1 := by
      unfold inverseDelta
      rw [← Real.exp_zero, Real.exp_le_exp, neg_nonpos]
      exact (Real.rpow_nonneg hε0.le _).trans (le_exp_iterate _ _)
    calc inverseDelta C₀ k b ε ≤ inverseDelta C₀ k b₀ ε := hle
      _ < _ := h
      _ ≤ _ := stab_mono _ (by linarith) (by linarith) _
  -- the constants `C` and `c`
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk2 : (1 : ℝ) ≤ 2 ^ k - 1 := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  set B : ℝ := 2 * (2 ^ k - 1) * (3 : ℝ) ^ (1 / b) with hB
  have hBpos : 0 < B := by positivity
  set C : ℝ := B ^ (1 / (k : ℝ)) with hC
  set c : ℝ := 1 / (b * k) with hc
  refine ⟨C, c, by positivity, by positivity, fun n hn A hdens => ?_⟩
  by_contra hno
  have hA : NoProgression p M k (A : Set (Fin n → ZMod p)) := by
    intro x y hy hy0
    by_contra! h
    exact hno ⟨x, y, hy, hy0, h, progression_injective hMp1 x y hy hy0⟩
  set K₁ := k ^ ((C₀ + 2) * k) with hK₁
  set K := k ^ (C₀ * k) with hK
  have hKK : K + 2 ≤ K₁ := by
    rw [hK₁, hK, add_mul, pow_add]
    have h1 : 1 ≤ k ^ (C₀ * k) := Nat.one_le_pow _ _ (by omega)
    have h2 : 4 ≤ k ^ (2 * k) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
        _ ≤ k ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  set ℓ := Real.log^[K₁] (n : ℝ) with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log_iterate K₁ hn.le
  have hℓpos : 0 < ℓ := by linarith
  -- the density is positive
  have hdensA : C / ℓ ^ c ≤ density A := by
    unfold density; rw [Fintype.card_fin]; exact hdens
  have hαpos : 0 < density A := lt_of_lt_of_le (by positivity) hdensA
  -- the dimension bound
  have hdim := dimension_bound hM hk hMp hb1 hinv A hA hαpos
  set x := (density A ^ k / (2 * (2 ^ k - 1))) ^ (-b) with hx
  have hdim' : (n : ℝ) < Real.exp^[K₁] (3 * x) :=
    lt_of_lt_of_le hdim (exp_iterate_le_of_le hKK _)
  have hℓx : ℓ < 3 * x := (log_iterate_bounds K₁ hn.le hdim').2
  -- but the density hypothesis gives `3x ≤ ℓ`
  have hε : (3 / ℓ) ^ (1 / b) ≤ density A ^ k / (2 * (2 ^ k - 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (C / ℓ ^ c) ^ k ≤ density A ^ k := pow_le_pow_left₀ (by positivity) hdensA k
    have hCk : C ^ k = B := by
      rw [hC, ← Real.rpow_natCast, ← Real.rpow_mul hBpos.le, one_div_mul_cancel hk0,
        Real.rpow_one]
    have hℓk : (ℓ ^ c) ^ k = ℓ ^ (1 / b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hℓpos.le, hc]
      congr 1
      field_simp
    rw [div_pow, hCk, hℓk] at h1
    calc (3 / ℓ) ^ (1 / b) * (2 * (2 ^ k - 1))
        = B / ℓ ^ (1 / b) := by
          rw [hB, Real.div_rpow (by norm_num) hℓpos.le]; ring
      _ ≤ density A ^ k := h1
  have h3x : 3 * x ≤ ℓ := by
    have hxle : x ≤ ((3 / ℓ) ^ (1 / b)) ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hε (by linarith)
    rw [← Real.rpow_mul (by positivity), show 1 / b * -b = -1 by field_simp,
      Real.rpow_neg_one, inv_div] at hxle
    linarith
  linarith

end RestrictedPolynomials

end
