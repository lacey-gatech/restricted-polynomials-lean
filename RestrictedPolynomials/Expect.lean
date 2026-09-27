import RestrictedPolynomials.Defs

/-!
# Expectations under finite product measures

Basic facts about `FinProb.expect` and the product measure `FinProb.pi`: linearity, positivity,
independence of coordinates, the "swap" symmetry used for conditional expectations, and
marginalization onto a subset of the coordinates.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

namespace FinProb

variable {α : Type*} [Fintype α] (π : FinProb α)

/-! ### Linearity and positivity -/

@[simp] lemma expect_const (c : ℝ) : π.expect (fun _ => c) = c := by
  simp [expect, ← sum_mul, π.sum_eq_one]

lemma expect_add (f g : α → ℝ) : π.expect (fun a => f a + g a) = π.expect f + π.expect g := by
  simp [expect, mul_add, sum_add_distrib]

lemma expect_sub (f g : α → ℝ) : π.expect (fun a => f a - g a) = π.expect f - π.expect g := by
  simp [expect, mul_sub, sum_sub_distrib]

lemma expect_const_mul (c : ℝ) (f : α → ℝ) :
    π.expect (fun a => c * f a) = c * π.expect f := by
  simp [expect, mul_sum, mul_left_comm]

lemma expect_mul_const (c : ℝ) (f : α → ℝ) :
    π.expect (fun a => f a * c) = π.expect f * c := by
  simp [expect, sum_mul, mul_assoc]

lemma expect_neg (f : α → ℝ) : π.expect (fun a => -f a) = -π.expect f := by
  simp [expect]

lemma expect_sum {β : Type*} (s : Finset β) (f : β → α → ℝ) :
    π.expect (fun a => ∑ b ∈ s, f b a) = ∑ b ∈ s, π.expect (f b) := by
  simp only [expect, mul_sum]
  exact sum_comm

lemma expect_congr {f g : α → ℝ} (h : ∀ a, f a = g a) : π.expect f = π.expect g := by
  simp [expect, h]

lemma expect_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : π.expect f ≤ π.expect g :=
  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (π.nonneg a)

lemma expect_nonneg {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ π.expect f :=
  sum_nonneg fun a _ => mul_nonneg (π.nonneg a) (h a)

lemma expect_le_const {f : α → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) : π.expect f ≤ c := by
  simpa using π.expect_mono h

lemma const_le_expect {f : α → ℝ} {c : ℝ} (h : ∀ a, c ≤ f a) : c ≤ π.expect f := by
  simpa using π.expect_mono h

lemma abs_expect_le (f : α → ℝ) : |π.expect f| ≤ π.expect fun a => |f a| := by
  unfold expect
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  simp [abs_mul, abs_of_nonneg (π.nonneg _)]

/-- If the expectation of a nonnegative function is positive, the function is positive
somewhere. -/
lemma exists_pos_of_expect_pos {f : α → ℝ} (h : 0 < π.expect f) : ∃ a, 0 < f a := by
  by_contra! hf
  have : π.expect f ≤ 0 := π.expect_le_const hf
  linarith

/-- A function whose expectation is at least `c` exceeds `c` somewhere, or equals it. -/
lemma exists_ge_of_le_expect {f : α → ℝ} {c : ℝ} (h : c ≤ π.expect f) : ∃ a, c ≤ f a := by
  by_contra! hf
  have hne : Nonempty α := by
    by_contra hα
    rw [not_nonempty_iff] at hα
    have := π.sum_eq_one
    simp at this
  obtain ⟨a₀⟩ := hne
  have hlt : π.expect f < c := by
    have hpos : ∃ a, 0 < π.prob a := by
      by_contra! h0
      have : ∑ a, π.prob a ≤ 0 := sum_nonpos fun a _ => h0 a
      linarith [π.sum_eq_one]
    obtain ⟨a, ha⟩ := hpos
    have : π.expect f < π.expect fun _ => c := by
      unfold expect
      refine sum_lt_sum (fun b _ => mul_le_mul_of_nonneg_left (hf b).le (π.nonneg b))
        ⟨a, mem_univ _, mul_lt_mul_of_pos_left (hf a) ha⟩
    simpa using this
  linarith

/-! ### The product measure -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pi_prob (x : ι → α) : (π.pi ι).prob x = ∏ i, π.prob (x i) := rfl

/-- Independence: the expectation of a product of functions of distinct coordinates is the
product of the expectations. -/
lemma expect_pi_prod (g : ι → α → ℝ) :
    (π.pi ι).expect (fun x => ∏ i, g i (x i)) = ∏ i, π.expect (g i) := by
  simp only [expect, pi_prob, ← prod_mul_distrib]
  exact (Fintype.prod_sum fun i a => π.prob a * g i a).symm

/-- Double expectations under `π^{⊗ι} ⊗ π^{⊗ι}` as a single sum over pairs. -/
lemma expect_expect (F : (ι → α) → (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => (π.pi ι).expect fun y => F x y) =
      ∑ z : (ι → α) × (ι → α), (π.pi ι).prob z.1 * (π.pi ι).prob z.2 * F z.1 z.2 := by
  simp only [expect, mul_sum, Fintype.sum_prod_type, mul_assoc]

/-- The involution `(x, y) ↦ (x_T y_{Tᶜ}, y_T x_{Tᶜ})`, which exchanges the coordinates of `x`
and `y` outside `T`. -/
def swapOutside (T : Finset ι) : ((ι → α) × (ι → α)) ≃ ((ι → α) × (ι → α)) where
  toFun z := (T.piecewise z.1 z.2, T.piecewise z.2 z.1)
  invFun z := (T.piecewise z.1 z.2, T.piecewise z.2 z.1)
  left_inv z := by
    ext i <;> by_cases hi : i ∈ T <;> simp [hi]
  right_inv z := by
    ext i <;> by_cases hi : i ∈ T <;> simp [hi]

omit [Fintype α] [Fintype ι] in
@[simp] lemma swapOutside_apply (T : Finset ι) (z : (ι → α) × (ι → α)) :
    swapOutside T z = (T.piecewise z.1 z.2, T.piecewise z.2 z.1) := rfl

/-- The swap symmetry: exchanging the coordinates of two independent samples outside `T`
preserves the product measure. -/
lemma expect_expect_swap (T : Finset ι) (F : (ι → α) → (ι → α) → ℝ) :
    ((π.pi ι).expect fun x => (π.pi ι).expect fun y =>
        F (T.piecewise x y) (T.piecewise y x)) =
      (π.pi ι).expect fun x => (π.pi ι).expect fun y => F x y := by
  rw [expect_expect, expect_expect]
  refine Fintype.sum_equiv (swapOutside T) _ _ fun z => ?_
  simp only [swapOutside_apply]
  congr 1
  simp only [pi_prob, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ T <;> simp [hi, mul_comm]

/-- Averaging over the coordinates outside `T` of a second sample reproduces the expectation. -/
lemma expect_expect_piecewise (T : Finset ι) (g : (ι → α) → ℝ) :
    ((π.pi ι).expect fun x => (π.pi ι).expect fun y => g (T.piecewise x y)) =
      (π.pi ι).expect g := by
  rw [π.expect_expect_swap T fun x _ => g x]
  simp

/-! ### Restricting to a subset of the coordinates -/

/-- The point of `ι → α` that agrees with `v` on `S` and with `u` off `S`. -/
def extend (S : Finset ι) (v : S → α) (u : ι → α) : ι → α :=
  fun i => if h : i ∈ S then v ⟨i, h⟩ else u i

omit [Fintype α] [Fintype ι] in
lemma extend_restrict (S : Finset ι) (x u : ι → α) :
    extend S (fun i => x i) u = S.piecewise x u := by
  ext i
  by_cases hi : i ∈ S <;> simp [extend, hi]

/-- Marginalization: the expectation of a function of the coordinates in `S` only. -/
lemma expect_restrict (S : Finset ι) (g : (S → α) → ℝ) :
    (π.pi ι).expect (fun x => g fun i => x i) = (π.pi S).expect g := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) fun _ => α
  unfold expect
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [pi_prob]
  have hsplit : ∀ z : (S → α) × ({i // i ∉ S} → α),
      ∏ i, π.prob (e.symm z i) = (∏ i : S, π.prob (z.1 i)) * ∏ i : {i // i ∉ S}, π.prob (z.2 i) := by
    intro z
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
    congr 1
    · exact prod_congr (ext fun _ => by simp) fun i _ => by
        simp [e, Equiv.piEquivPiSubtypeProd, i.2]
    · exact prod_congr (ext fun _ => by simp) fun i _ => by
        simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  have hrestr : ∀ z : (S → α) × ({i // i ∉ S} → α), (fun i : S => e.symm z i) = z.1 := by
    intro z
    ext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  simp only [hsplit, hrestr]
  refine sum_congr rfl fun v _ => ?_
  have hsum : ∑ w : {i // i ∉ S} → α, ∏ i : {i // i ∉ S}, π.prob (w i) = 1 := by
    rw [← Fintype.prod_sum (fun _ a => π.prob a)]
    simp [π.sum_eq_one]
  calc ∑ w : {i // i ∉ S} → α, (∏ i : S, π.prob (v i)) * (∏ i : {i // i ∉ S}, π.prob (w i)) *
          g v
      = (∏ i : S, π.prob (v i)) * g v * ∑ w : {i // i ∉ S} → α, ∏ i : {i // i ∉ S}, π.prob (w i) := by
        rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
    _ = _ := by rw [hsum, mul_one]

/-- The average of `f` over the free coordinates `S`, with the coordinates outside `S` frozen
to those of `u`, is the average of the restricted function on `α^S`. -/
lemma expect_piecewise_eq_expect_extend (S : Finset ι) (f : (ι → α) → ℝ) (u : ι → α) :
    (π.pi ι).expect (fun x => f (S.piecewise x u)) =
      (π.pi S).expect (fun v => f (extend S v u)) := by
  rw [← π.expect_restrict S fun v => f (extend S v u)]
  simp only [extend_restrict]

/-! ### Padding with extra coordinates -/

/-- Adding coordinates on which a function does not depend does not change its expectation. -/
lemma expect_sumInl {κ : Type*} [Fintype κ] [DecidableEq κ] (g : (ι → α) → ℝ) :
    (π.pi (ι ⊕ κ)).expect (fun x => g (x ∘ Sum.inl)) = (π.pi ι).expect g := by
  unfold expect
  rw [← (Equiv.sumArrowEquivProdArrow ι κ α).symm.sum_comp, Fintype.sum_prod_type]
  simp only [pi_prob, Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  refine sum_congr rfl fun v _ => ?_
  have hsum : ∑ w : κ → α, ∏ i, π.prob (w i) = 1 := by
    rw [← Fintype.prod_sum (fun _ a => π.prob a)]
    simp [π.sum_eq_one]
  have hcomp : ∀ w : κ → α, (Equiv.sumArrowEquivProdArrow ι κ α).symm (v, w) ∘ Sum.inl = v := by
    intro w; ext i; simp
  simp only [hcomp]
  calc ∑ w : κ → α, (∏ i, π.prob (v i)) * (∏ i, π.prob (w i)) * g v
      = (∏ i, π.prob (v i)) * g v * ∑ w : κ → α, ∏ i, π.prob (w i) := by
        rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
    _ = _ := by rw [hsum, mul_one]

end FinProb

end RestrictedPolynomials

end
