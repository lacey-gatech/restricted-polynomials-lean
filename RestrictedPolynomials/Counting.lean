import RestrictedPolynomials.Expect
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Chebyshev

/-!
# The counting distribution (Lemma 6.3) and fibers (Lemma 6.4)

`countingDist p k M` is the distribution `μ` of Lemma 6.3 on `𝔽_p^k`: with probability `1/2` a
uniformly random diagonal tuple `(x, …, x)`, and otherwise `(x, x + y, …, x + y^{k-1})` with
`x ∈ 𝔽_p` and `y ∈ {2, …, M}` uniform. It is written as the pushforward of the weight
`wt y` on pairs `(x, y) ∈ 𝔽_p × Y`, `Y = {0, 2, …, M}`, which makes expectations under
`μ^{⊗n}` easy to compute.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {p : ℕ}

/-- `pw j a = a^j` for `j ≥ 1`, and `pw 0 a = 0`. -/
def pw (j : ℕ) (a : ZMod p) : ZMod p := if j = 0 then 0 else a ^ j

lemma polyTerm_apply {ι : Type*} (j : ℕ) (y : ι → ZMod p) (i : ι) :
    polyTerm j y i = pw j (y i) := rfl

@[simp] lemma pw_zero_left (a : ZMod p) : pw 0 a = 0 := by simp [pw]

@[simp] lemma pw_zero_right (j : ℕ) : pw j (0 : ZMod p) = 0 := by
  unfold pw; split_ifs with h
  · rfl
  · exact zero_pow h

/-- The tuple `(x, x + y, x + y², …, x + y^{k-1})`. -/
def progTuple (k : ℕ) (x y : ZMod p) : Fin k → ZMod p := fun j => x + pw j y

/-- The weight of a step `y`: `1/(2p)` for `y = 0` and `1/(2p(M-1))` for `y ∈ {2, …, M}`. -/
def wt (p M : ℕ) (y : ℕ) : ℝ := if y = 0 then 1 / (2 * p) else 1 / (2 * p * ((M : ℝ) - 1))

/-- The index set `𝔽_p × Y` of the pushforward. -/
def stepPairs (p M : ℕ) [NeZero p] : Finset (ZMod p × ℕ) := univ ×ˢ stepSet M

lemma sum_wt (M : ℕ) (hM : 2 ≤ M) [NeZero p] :
    ∑ y ∈ stepSet M, wt p M y = 1 / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  rw [stepSet, sum_insert (by simp)]
  have hcard : ((Icc 2 M).card : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.card_Icc, show M + 1 - 2 = M - 1 by omega, Nat.cast_sub (by omega : 1 ≤ M)]
    simp
  rw [sum_congr rfl fun y hy => (show wt p M y = 1 / (2 * p * ((M : ℝ) - 1)) by
    simp [wt, show y ≠ 0 by simp at hy; omega]), sum_const, nsmul_eq_mul, hcard]
  simp only [wt, ite_true]
  field_simp
  ring

lemma sum_stepPairs_wt (M : ℕ) (hM : 2 ≤ M) [NeZero p] :
    ∑ z ∈ stepPairs p M, wt p M z.2 = 1 := by
  simp only [stepPairs, sum_product, sum_wt M hM, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

/-- The probability `μ(t) = ∑_{(x,y) : progTuple x y = t} wt y`. -/
def countingProb (p k M : ℕ) [NeZero p] (t : Fin k → ZMod p) : ℝ :=
  ∑ z ∈ stepPairs p M, wt p M z.2 * if progTuple k z.1 (z.2 : ZMod p) = t then 1 else 0

lemma wt_nonneg (M : ℕ) (hM : 2 ≤ M) (y : ℕ) : 0 ≤ wt p M y := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold wt; split_ifs <;> [positivity; exact div_nonneg zero_le_one (by
    have := (Nat.cast_nonneg p : (0 : ℝ) ≤ p); nlinarith)]

lemma sum_countingProb_mul (k M : ℕ) [NeZero p] (F : (Fin k → ZMod p) → ℝ) :
    ∑ t, countingProb p k M t * F t =
      ∑ z ∈ stepPairs p M, wt p M z.2 * F (progTuple k z.1 (z.2 : ZMod p)) := by
  unfold countingProb
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  simp [ite_mul]

/-- The counting distribution `μ` of Lemma 6.3. -/
def countingDist (p k M : ℕ) [NeZero p] (hM : 2 ≤ M) : FinProb (Fin k → ZMod p) where
  prob := countingProb p k M
  nonneg t := sum_nonneg fun z _ => mul_nonneg (wt_nonneg M hM _) (by split_ifs <;> norm_num)
  sum_eq_one := by
    have := sum_countingProb_mul (p := p) k M fun _ => 1
    simp only [mul_one] at this
    rw [this, sum_stepPairs_wt M hM]

section

variable [NeZero p] {k M : ℕ} (hM : 2 ≤ M)

lemma expect_countingDist (F : (Fin k → ZMod p) → ℝ) :
    (countingDist p k M hM).expect F =
      ∑ z ∈ stepPairs p M, wt p M z.2 * F (progTuple k z.1 (z.2 : ZMod p)) :=
  sum_countingProb_mul k M F

/-- Every progression tuple with step in `Y` lies in the support of `μ`. -/
lemma progTuple_mem_support (x : ZMod p) {y : ℕ} (hy : y ∈ stepSet M) :
    progTuple k x (y : ZMod p) ∈ (countingDist p k M hM).support := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hwpos : 0 < wt p M y := by
    have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    unfold wt; split_ifs
    · positivity
    · exact div_pos one_pos (by nlinarith)
  show countingProb p k M _ ≠ 0
  refine ne_of_gt (lt_of_lt_of_le ?_ (single_le_sum (f := fun z : ZMod p × ℕ =>
    wt p M z.2 * if progTuple k z.1 (z.2 : ZMod p) = progTuple k x (y : ZMod p) then 1 else 0)
    (fun z _ => mul_nonneg (wt_nonneg M hM _) (by split_ifs <;> norm_num))
    (show (x, y) ∈ stepPairs p M by simp [stepPairs, hy])))
  simpa using hwpos

/-- Every point of the support of `μ` is a progression tuple with step in `Y`. -/
lemma exists_of_mem_support {t : Fin k → ZMod p} (ht : t ∈ (countingDist p k M hM).support) :
    ∃ x, ∃ y ∈ stepSet M, t = progTuple k x (y : ZMod p) := by
  by_contra! h
  apply ht
  show countingProb p k M t = 0
  refine sum_eq_zero fun z hz => ?_
  simp only [stepPairs, mem_product, mem_univ, true_and] at hz
  rw [ite_eq_right (fun h' => h z.1 z.2 hz h'.symm), mul_zero]

end

/-! ### Marginals -/

section Marginal

variable [NeZero p] {k M : ℕ} (hM : 2 ≤ M)

lemma sum_pw_shift (j : ℕ) (a b : ZMod p) :
    ∑ x : ZMod p, (if x + pw j b = a then (1 : ℝ) else 0) = 1 := by
  have : ∀ x : ZMod p, (x + pw j b = a) ↔ (x = a - pw j b) := fun x => eq_sub_iff_add_eq.symm
  simp only [this, sum_ite_eq', mem_univ, ite_true]

/-- **Lemma 6.3**, the marginals: every marginal of `μ` is the uniform distribution. -/
lemma marginal_countingDist (j : Fin k) (a : ZMod p) :
    ((countingDist p k M hM).marginal j).prob a = 1 / p := by
  show ∑ t with t j = a, countingProb p k M t = 1 / p
  calc ∑ t with t j = a, countingProb p k M t
      = ∑ t, countingProb p k M t * (if t j = a then 1 else 0) := by
        rw [sum_filter]; exact sum_congr rfl fun t _ => by split_ifs <;> simp
    _ = ∑ z ∈ stepPairs p M, wt p M z.2 *
          (if progTuple k z.1 (z.2 : ZMod p) j = a then 1 else 0) :=
        sum_countingProb_mul k M _
    _ = ∑ y ∈ stepSet M, wt p M y *
          ∑ x : ZMod p, (if x + pw (j : ℕ) (y : ZMod p) = a then (1 : ℝ) else 0) := by
        rw [stepPairs, sum_product, sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [mul_sum]
        rfl
    _ = ∑ y ∈ stepSet M, wt p M y := by simp only [sum_pw_shift, mul_one]
    _ = 1 / p := sum_wt M hM

/-- The marginals of `μ` are uniform, as distributions. -/
lemma marginal_countingDist_eq (j : Fin k) :
    (countingDist p k M hM).marginal j = FinProb.uniform := by
  have : ((countingDist p k M hM).marginal j).prob = (FinProb.uniform : FinProb (ZMod p)).prob := by
    ext a
    rw [marginal_countingDist hM j a]
    simp [FinProb.uniform, ZMod.card]
  cases h1 : (countingDist p k M hM).marginal j
  cases h2 : (FinProb.uniform : FinProb (ZMod p))
  rw [h1, h2] at this
  simp only at this
  subst this
  rfl

end Marginal

/-! ### Expectations under `μ^{⊗n}` -/

section Tensor

variable [NeZero p] {k M : ℕ} (hM : 2 ≤ M) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An expectation under `μ^{⊗ι}` as a sum over the pairs `(x_i, y_i)` of every coordinate. -/
lemma expect_pi_countingDist (G : (ι → Fin k → ZMod p) → ℝ) :
    ((countingDist p k M hM).pi ι).expect G =
      ∑ Z ∈ Fintype.piFinset fun _ : ι => stepPairs p M,
        (∏ i, wt p M (Z i).2) * G fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p) := by
  unfold FinProb.expect
  simp only [FinProb.pi_prob]
  change ∑ X : ι → Fin k → ZMod p, (∏ i, countingProb p k M (X i)) * G X = _
  simp only [countingProb]
  simp only [prod_univ_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun Z _ => ?_
  simp only [prod_mul_distrib, mul_assoc]
  rw [← mul_sum]
  congr 1
  have hind : ∀ X : ι → Fin k → ZMod p,
      (∏ i, if progTuple k (Z i).1 ((Z i).2 : ZMod p) = X i then (1 : ℝ) else 0) =
        if (fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p)) = X then 1 else 0 := by
    intro X
    by_cases h : (fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p)) = X
    · subst h; simp
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp only [hind, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

end Tensor

end RestrictedPolynomials

end
