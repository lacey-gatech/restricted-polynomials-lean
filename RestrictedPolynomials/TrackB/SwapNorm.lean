module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Track B, file 3: the box inner product and the swap norm

Source: CSP_6 (arXiv:2411.15133v1 `main.tex`), l. 329-342 (`def:swap`, `def:swapnorm`),
l. 519-527 (`def:box`), l. 532-541 (`lemma:boxstuff`), l. 586-590 (`lemma:box`),
l. 598-601 (`lemma:l2`), l. 620-637 (`lemma:cs1`, `eq:iden`), l. 648-651 (`cor:norm`).
Covers CSP_6 `def:swapnorm` (with `def:swap`, `def:box`), `lemma:boxstuff`,
`lemma:box`, `lemma:l2`, `lemma:cs1`, `eq:iden` and `cor:norm`.

**Source correction.** The first assertion of `lemma:boxstuff` is false as printed:
the Cauchy-Schwarz grouping by the `S`-coordinates yields
`‖box S f₁ f₂ f₃ f₄‖² ≤ box S f₁ f₃ f₃ f₁ * box S f₂ f₄ f₄ f₂` (not `box S f₁ f₃ f₁ f₃ * ...`).
This is `box_sq_le`. The source's second coupling (grouping by `S̄`) is true as printed and is
`box_sq_le'`.

The uniform measure on `ι → α` is `Finset.expect` over `Finset.univ`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat

noncomputable section

namespace RestrictedPolynomials

namespace TrackB

section SwapNorm

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- squared `L²` norm w.r.t. the uniform measure -/
def l2sq (f : (ι → α) → ℂ) : ℝ := 𝔼 x : ι → α, ‖f x‖ ^ 2

/-- Box inner product (CSP6 Def `box`, l.519-527). -/
def box (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) : ℂ :=
  𝔼 x : ι → α, 𝔼 y : ι → α,
    f₁ x * f₂ y * star (f₃ (S.piecewise y x)) * star (f₄ (S.piecewise x y))

/-- The swap `(x', y')` of `(x, y)` by a coordinatewise coin vector `b` (CSP6 Def `swap`, l.329-332). -/
def swapL (b : ι → Bool) (x y : ι → α) : (ι → α) := fun i => if b i then y i else x i
def swapR (b : ι → Bool) (x y : ι → α) : (ι → α) := fun i => if b i then x i else y i

/-- Swap inner product (CSP6 Def `swapnorm`, l.335-342). -/
def val (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) : ℂ :=
  𝔼 x : ι → α, 𝔼 y : ι → α, 𝔼 b : ι → Bool,
    f₁ x * f₂ y * star (f₃ (swapL b x y)) * star (f₄ (swapR b x y))

/-! ### Elementary lemmas on the swap -/

lemma swapL_swapL (b : ι → Bool) (x y : ι → α) :
    swapL b (swapL b x y) (swapR b x y) = x := by
  funext i; cases h : b i <;> simp [swapL, swapR, h]

lemma swapR_swapL (b : ι → Bool) (x y : ι → α) :
    swapR b (swapL b x y) (swapR b x y) = y := by
  funext i; cases h : b i <;> simp [swapL, swapR, h]

/-- the swap by `b` as an involutive bijection of pairs -/
def swapE (b : ι → Bool) : (ι → α) × (ι → α) ≃ (ι → α) × (ι → α) where
  toFun p := (swapL b p.1 p.2, swapR b p.1 p.2)
  invFun p := (swapL b p.1 p.2, swapR b p.1 p.2)
  left_inv p := by simp [swapL_swapL, swapR_swapL]
  right_inv p := by simp [swapL_swapL, swapR_swapL]

section expect_lemmas
variable {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]

lemma expect_expect_swap (b : ι → Bool) (g : (ι → α) → (ι → α) → M) :
    𝔼 x : ι → α, 𝔼 y : ι → α, g (swapL b x y) (swapR b x y) = 𝔼 x : ι → α, 𝔼 y : ι → α, g x y := by
  rw [← Finset.expect_product' (f := fun x y => g (swapL b x y) (swapR b x y)),
    ← Finset.expect_product' (f := g)]
  exact Fintype.expect_equiv (swapE b) _ _ (fun p => rfl)

lemma expect_expect_const (h : (ι → α) → M) :
    𝔼 x : ι → α, 𝔼 _y : ι → α, h x = 𝔼 x : ι → α, h x := by
  rcases isEmpty_or_nonempty (ι → α) with hn | hn
  · simp
  · simp

lemma expect_swapL (b : ι → Bool) (h : (ι → α) → M) :
    𝔼 x : ι → α, 𝔼 y : ι → α, h (swapL b x y) = 𝔼 x : ι → α, h x := by
  rw [expect_expect_swap b (fun x _ => h x), expect_expect_const]

lemma expect_swapR (b : ι → Bool) (h : (ι → α) → M) :
    𝔼 x : ι → α, 𝔼 y : ι → α, h (swapR b x y) = 𝔼 x : ι → α, h x := by
  rw [expect_expect_swap b (fun _ y => h y), Finset.expect_comm, expect_expect_const]

end expect_lemmas

/-- the coin vector of a set `S` -/
def ind (S : Finset ι) : ι → Bool := fun i => decide (i ∈ S)

lemma swapL_ind (S : Finset ι) (x y : ι → α) : swapL (ind S) x y = S.piecewise y x := by
  funext i; by_cases h : i ∈ S <;> simp [swapL, ind, h]

lemma swapR_ind (S : Finset ι) (x y : ι → α) : swapR (ind S) x y = S.piecewise x y := by
  funext i; by_cases h : i ∈ S <;> simp [swapR, ind, h]

lemma piecewise_piecewise_piecewise (S : Finset ι) (a b c d : ι → α) :
    S.piecewise (S.piecewise a b) (S.piecewise c d) = S.piecewise a d := by
  funext i; by_cases h : i ∈ S <;> simp [h]

/-- `box` as an expectation over the swap by `ind S`. -/
lemma box_eq_swap (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    box S f₁ f₂ f₃ f₄ = 𝔼 x : ι → α, 𝔼 y : ι → α,
      f₁ x * f₂ y * star (f₃ (swapL (ind S) x y)) * star (f₄ (swapR (ind S) x y)) := by
  simp only [box, swapL_ind, swapR_ind]

section expect_lemmas
variable {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]

/-- averaging out the `S̄`-coordinates: `x = S.piecewise p z` -/
lemma expect_expect_piecewise (S : Finset ι) (h : (ι → α) → M) :
    𝔼 p : ι → α, 𝔼 z : ι → α, h (S.piecewise p z) = 𝔼 x : ι → α, h x := by
  rw [Finset.expect_comm]
  have := expect_swapL (ind S) h
  simpa only [swapL_ind] using this

lemma expect_four_piecewise (S : Finset ι) (Φ : (ι → α) → (ι → α) → M) :
    𝔼 p : ι → α, 𝔼 q : ι → α, 𝔼 z : ι → α, 𝔼 w : ι → α,
      Φ (S.piecewise p z) (S.piecewise q w) = 𝔼 x : ι → α, 𝔼 y : ι → α, Φ x y := by
  have h1 : ∀ p z : ι → α, 𝔼 q : ι → α, 𝔼 w : ι → α, Φ (S.piecewise p z) (S.piecewise q w) =
      𝔼 y : ι → α, Φ (S.piecewise p z) y := fun p z =>
    expect_expect_piecewise S (fun y => Φ (S.piecewise p z) y)
  have h2 : ∀ p : ι → α, 𝔼 q : ι → α, 𝔼 z : ι → α, 𝔼 w : ι → α,
      Φ (S.piecewise p z) (S.piecewise q w) =
      𝔼 z : ι → α, 𝔼 y : ι → α, Φ (S.piecewise p z) y := fun p => by
    rw [Finset.expect_comm]
    exact Finset.expect_congr rfl (fun z _ => h1 p z)
  simp_rw [h2]
  exact expect_expect_piecewise S (fun x => 𝔼 y : ι → α, Φ x y)

end expect_lemmas

lemma star_expect {κ : Type*} (s : Finset κ) (f : κ → ℂ) :
    star (𝔼 i ∈ s, f i) = 𝔼 i ∈ s, star (f i) :=
  map_expect (starRingEnd ℂ) f s

/-- Cauchy-Schwarz for the uniform expectation of a product of complex functions. -/
lemma norm_expect_mul_sq_le {κ : Type*} (s : Finset κ) (u w : κ → ℂ) :
    ‖𝔼 i ∈ s, u i * w i‖ ^ 2 ≤ (𝔼 i ∈ s, ‖u i‖ ^ 2) * 𝔼 i ∈ s, ‖w i‖ ^ 2 := by
  calc ‖𝔼 i ∈ s, u i * w i‖ ^ 2 ≤ (𝔼 i ∈ s, ‖u i * w i‖) ^ 2 := by
        gcongr; exact RCLike.norm_expect_le (K := ℂ)
    _ = (𝔼 i ∈ s, ‖u i‖ * ‖w i‖) ^ 2 := by simp only [norm_mul]
    _ ≤ _ := Finset.expect_mul_sq_le_sq_mul_sq s _ _

/-- The auxiliary function of the Cauchy-Schwarz proof of `box_sq_le`. -/
def boxA (S : Finset ι) (f g : (ι → α) → ℂ) (p q : ι → α) : ℂ :=
  𝔼 z : ι → α, f (S.piecewise p z) * star (g (S.piecewise q z))

lemma box_eq_expect_boxA (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    box S f₁ f₂ f₃ f₄ = 𝔼 p : ι → α, 𝔼 q : ι → α,
      boxA S f₁ f₃ p q * boxA S f₂ f₄ q p := by
  have key : ∀ p q : ι → α, boxA S f₁ f₃ p q * boxA S f₂ f₄ q p =
      𝔼 z : ι → α, 𝔼 w : ι → α, (fun x y : ι → α =>
        f₁ x * f₂ y * star (f₃ (S.piecewise y x)) * star (f₄ (S.piecewise x y)))
          (S.piecewise p z) (S.piecewise q w) := by
    intro p q
    simp only [boxA, Finset.expect_mul_expect]
    refine Finset.expect_congr rfl (fun z _ => Finset.expect_congr rfl (fun w _ => ?_))
    simp only [piecewise_piecewise_piecewise]
    ring
  simp_rw [key]
  rw [expect_four_piecewise S (fun x y => f₁ x * f₂ y * star (f₃ (S.piecewise y x)) *
    star (f₄ (S.piecewise x y)))]
  rfl

lemma box_swap_eq_expect_norm_sq (S : Finset ι) (f g : (ι → α) → ℂ) :
    box S f g g f = ((𝔼 p : ι → α, 𝔼 q : ι → α, ‖boxA S f g p q‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ p q : ι → α, ((‖boxA S f g p q‖ ^ 2 : ℝ) : ℂ) =
      𝔼 z : ι → α, 𝔼 w : ι → α, (fun x y : ι → α =>
        f x * g y * star (g (S.piecewise y x)) * star (f (S.piecewise x y)))
          (S.piecewise p z) (S.piecewise q w) := by
    intro p q
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    have : (starRingEnd ℂ) (boxA S f g p q) = 𝔼 w : ι → α,
        star (f (S.piecewise p w)) * g (S.piecewise q w) := by
      simp only [boxA]
      rw [show (starRingEnd ℂ) (𝔼 z : ι → α, f (S.piecewise p z) * star (g (S.piecewise q z)))
        = star (𝔼 z : ι → α, f (S.piecewise p z) * star (g (S.piecewise q z))) from rfl,
        star_expect]
      simp [star_mul']
    rw [this]
    simp only [boxA, Finset.expect_mul_expect]
    refine Finset.expect_congr rfl (fun z _ => Finset.expect_congr rfl (fun w _ => ?_))
    simp only [piecewise_piecewise_piecewise]
    ring
  rw [Complex.ofReal_expect]
  simp_rw [Complex.ofReal_expect, key]
  rw [expect_four_piecewise S (fun x y => f x * g y * star (g (S.piecewise y x)) *
    star (f (S.piecewise x y)))]
  rfl

lemma norm_expect_expect_mul_sq_le {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (u w : κ₁ → κ₂ → ℂ) :
    ‖𝔼 p : κ₁, 𝔼 q : κ₂, u p q * w p q‖ ^ 2 ≤
      (𝔼 p : κ₁, 𝔼 q : κ₂, ‖u p q‖ ^ 2) * 𝔼 p : κ₁, 𝔼 q : κ₂, ‖w p q‖ ^ 2 := by
  have h := norm_expect_mul_sq_le (Finset.univ ×ˢ (Finset.univ : Finset κ₂))
    (fun r => u r.1 r.2) (fun r => w r.1 r.2)
  rw [← Finset.expect_product' (f := fun p q => u p q * w p q),
    ← Finset.expect_product' (f := fun p q => ‖u p q‖ ^ 2),
    ← Finset.expect_product' (f := fun p q => ‖w p q‖ ^ 2)]
  exact h

/-- `lemma:boxstuff`, assertion 1, CORRECTED pairing (source error, see the module
docstring). -/
lemma box_sq_le (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    ‖box S f₁ f₂ f₃ f₄‖ ^ 2 ≤ (box S f₁ f₃ f₃ f₁).re * (box S f₂ f₄ f₄ f₂).re := by
  rw [box_swap_eq_expect_norm_sq, box_swap_eq_expect_norm_sq, Complex.ofReal_re,
    Complex.ofReal_re, box_eq_expect_boxA]
  refine (norm_expect_expect_mul_sq_le _ _).trans_eq ?_
  congr 1
  exact Finset.expect_comm _ _ _

lemma box_compl (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    box S f₁ f₂ f₃ f₄ = box Sᶜ f₁ f₂ f₄ f₃ := by
  simp only [box, Finset.piecewise_compl]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ => ?_))
  ring

/-- the source's second coupling (grouping by `S̄`); true as printed. -/
lemma box_sq_le' (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    ‖box S f₁ f₂ f₃ f₄‖ ^ 2 ≤ (box S f₁ f₄ f₁ f₄).re * (box S f₂ f₃ f₂ f₃).re := by
  have h := box_sq_le Sᶜ f₁ f₂ f₄ f₃
  rw [← box_compl] at h
  rw [box_compl S f₁ f₄ f₁ f₄, box_compl S f₂ f₃ f₂ f₃]
  simpa using h

lemma box_pair_sq_le (S : Finset ι) (f g : (ι → α) → ℂ) :
    (box S f g f g).re ^ 2 ≤ (box S f f f f).re * (box S g g g g).re := by
  refine le_trans ?_ (box_sq_le S f g f g)
  have h1 := Complex.abs_re_le_norm (box S f g f g)
  nlinarith [abs_nonneg (box S f g f g).re, sq_abs (box S f g f g).re]

lemma l2sq_nonneg (f : (ι → α) → ℂ) : 0 ≤ l2sq f :=
  Finset.expect_nonneg (fun _ _ => sq_nonneg _)

lemma box_eq_ofReal_pair (S : Finset ι) (f g : (ι → α) → ℂ) :
    box S f g f g = ((𝔼 p : ι → α, 𝔼 q : ι → α, ‖boxA Sᶜ f g p q‖ ^ 2 : ℝ) : ℂ) := by
  rw [box_compl S f g f g]
  exact box_swap_eq_expect_norm_sq _ f g

lemma box_re_nonneg_pair (S : Finset ι) (f g : (ι → α) → ℂ) : 0 ≤ (box S f g f g).re := by
  rw [box_eq_ofReal_pair, Complex.ofReal_re]
  exact Finset.expect_nonneg (fun p _ => Finset.expect_nonneg (fun q _ => sq_nonneg _))

open scoped ComplexOrder in
lemma box_nonneg_pair (S : Finset ι) (f g : (ι → α) → ℂ) : 0 ≤ box S f g f g := by
  rw [box_eq_ofReal_pair, Complex.zero_le_real]
  exact Finset.expect_nonneg (fun p _ => Finset.expect_nonneg (fun q _ => sq_nonneg _))

lemma box_pow4_le (S : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    ‖box S f₁ f₂ f₃ f₄‖ ^ 4 ≤
      (box S f₁ f₁ f₁ f₁).re * (box S f₂ f₂ f₂ f₂).re * (box S f₃ f₃ f₃ f₃).re *
        (box S f₄ f₄ f₄ f₄).re := by
  have h := box_sq_le' S f₁ f₂ f₃ f₄
  have hx := box_pair_sq_le S f₁ f₄
  have hy := box_pair_sq_le S f₂ f₃
  have n1 := box_re_nonneg_pair S f₁ f₁
  have n2 := box_re_nonneg_pair S f₂ f₂
  have n3 := box_re_nonneg_pair S f₃ f₃
  have n4 := box_re_nonneg_pair S f₄ f₄
  calc ‖box S f₁ f₂ f₃ f₄‖ ^ 4 = (‖box S f₁ f₂ f₃ f₄‖ ^ 2) ^ 2 := by ring
    _ ≤ ((box S f₁ f₄ f₁ f₄).re * (box S f₂ f₃ f₂ f₃).re) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h 2
    _ = (box S f₁ f₄ f₁ f₄).re ^ 2 * (box S f₂ f₃ f₂ f₃).re ^ 2 := by ring
    _ ≤ ((box S f₁ f₁ f₁ f₁).re * (box S f₄ f₄ f₄ f₄).re) *
          ((box S f₂ f₂ f₂ f₂).re * (box S f₃ f₃ f₃ f₃).re) :=
        mul_le_mul hx hy (sq_nonneg _) (mul_nonneg n1 n4)
    _ = _ := by ring

lemma box_self_le_l2sq_sq (S : Finset ι) (f : (ι → α) → ℂ) : (box S f f f f).re ≤ l2sq f ^ 2 := by
  have hL : 0 ≤ l2sq f ^ 2 := sq_nonneg _
  have key : ‖box S f f f f‖ ^ 2 ≤ (l2sq f ^ 2) ^ 2 := by
    rw [box_eq_swap]
    have h := norm_expect_expect_mul_sq_le (fun x y : ι → α => f x * f y)
      (fun x y : ι → α => star (f (swapL (ind S) x y)) * star (f (swapR (ind S) x y)))
    have e1 : 𝔼 x : ι → α, 𝔼 y : ι → α, ‖f x * f y‖ ^ 2 = l2sq f ^ 2 := by
      simp only [l2sq, norm_mul, mul_pow]
      rw [← Finset.expect_mul_expect, sq]
    have e2 : 𝔼 x : ι → α, 𝔼 y : ι → α,
        ‖star (f (swapL (ind S) x y)) * star (f (swapR (ind S) x y))‖ ^ 2 = l2sq f ^ 2 := by
      simp only [norm_mul, mul_pow, norm_star]
      rw [expect_expect_swap (ind S) (fun x y => ‖f x‖ ^ 2 * ‖f y‖ ^ 2)]
      simp only [l2sq]
      rw [← Finset.expect_mul_expect, sq]
    rw [e1, e2] at h
    refine le_trans (le_of_eq ?_) (h.trans_eq ?_)
    · simp only [mul_assoc]
    · ring
  exact (Complex.re_le_norm _).trans ((sq_le_sq₀ (norm_nonneg _) hL).1 key)

/-- sets of coordinates versus coin vectors -/
def coinEquiv : Finset ι ≃ (ι → Bool) where
  toFun := ind
  invFun b := Finset.univ.filter (fun i => b i = true)
  left_inv S := by ext i; simp [ind]
  right_inv b := by funext i; simp [ind]

/-- Lemma `box` (l.586-590). -/
lemma val_eq_expect_box (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = 𝔼 S : Finset ι, box S f₁ f₂ f₃ f₄ := by
  have h1 : (𝔼 b : ι → Bool, 𝔼 x : ι → α, 𝔼 y : ι → α,
      f₁ x * f₂ y * star (f₃ (swapL b x y)) * star (f₄ (swapR b x y))) = val f₁ f₂ f₃ f₄ := by
    rw [Finset.expect_comm]
    refine Finset.expect_congr rfl (fun x _ => Finset.expect_comm _ _ _)
  rw [← h1]
  symm
  refine Fintype.expect_equiv coinEquiv _ _ (fun S => ?_)
  rw [box_eq_swap]
  rfl

lemma val_eq_ofReal_pair (f g : (ι → α) → ℂ) :
    val f g f g = ((𝔼 S : Finset ι, (box S f g f g).re : ℝ) : ℂ) := by
  rw [val_eq_expect_box, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun S _ => ?_)
  rw [box_eq_ofReal_pair, Complex.ofReal_re]

lemma val_re_nonneg_pair (f g : (ι → α) → ℂ) : 0 ≤ (val f g f g).re := by
  rw [val_eq_ofReal_pair, Complex.ofReal_re]
  exact Finset.expect_nonneg (fun S _ => box_re_nonneg_pair S f g)

open scoped ComplexOrder in
lemma val_nonneg_pair (f g : (ι → α) → ℂ) : 0 ≤ val f g f g := by
  rw [val_eq_ofReal_pair, Complex.zero_le_real]
  exact Finset.expect_nonneg (fun S _ => box_re_nonneg_pair S f g)

lemma val_pair_re_eq (f g : (ι → α) → ℂ) :
    (val f g f g).re = 𝔼 S : Finset ι, (box S f g f g).re := by
  rw [val_eq_ofReal_pair, Complex.ofReal_re]

/-- Lemma `l2` (l.598-601), with the implicit absolute value. -/
lemma norm_val_le (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    ‖val f₁ f₂ f₃ f₄‖ ≤
      Real.sqrt (l2sq f₁) * Real.sqrt (l2sq f₂) * Real.sqrt (l2sq f₃) * Real.sqrt (l2sq f₄) := by
  set C := Real.sqrt (l2sq f₁) * Real.sqrt (l2sq f₂) * Real.sqrt (l2sq f₃) *
    Real.sqrt (l2sq f₄) with hC
  have hC0 : 0 ≤ C := by positivity
  have hC4 : C ^ 4 = l2sq f₁ ^ 2 * l2sq f₂ ^ 2 * l2sq f₃ ^ 2 * l2sq f₄ ^ 2 := by
    have : ∀ g : (ι → α) → ℂ, Real.sqrt (l2sq g) ^ 4 = l2sq g ^ 2 := fun g => by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (l2sq_nonneg g)]
    rw [hC]
    simp only [mul_pow, this]
  have hS : ∀ S : Finset ι, ‖box S f₁ f₂ f₃ f₄‖ ≤ C := by
    intro S
    have h := box_pow4_le S f₁ f₂ f₃ f₄
    have n1 := box_re_nonneg_pair S f₁ f₁
    have n2 := box_re_nonneg_pair S f₂ f₂
    have n3 := box_re_nonneg_pair S f₃ f₃
    have n4 := box_re_nonneg_pair S f₄ f₄
    have u1 := box_self_le_l2sq_sq S f₁
    have u2 := box_self_le_l2sq_sq S f₂
    have u3 := box_self_le_l2sq_sq S f₃
    have u4 := box_self_le_l2sq_sq S f₄
    have : ‖box S f₁ f₂ f₃ f₄‖ ^ 4 ≤ C ^ 4 := by
      rw [hC4]
      refine h.trans ?_
      gcongr
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC0 (by norm_num)).1 this
  rw [val_eq_expect_box]
  refine (RCLike.norm_expect_le (K := ℂ)).trans ?_
  exact Finset.expect_le Finset.univ_nonempty (fun S _ => hS S)

/-- composing two swaps: the coin vectors add (xor) -/
def xorE (c : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun b := fun i => xor (b i) (c i)
  invFun b := fun i => xor (b i) (c i)
  left_inv b := by
    funext i
    show xor (xor (b i) (c i)) (c i) = b i
    cases b i <;> cases c i <;> rfl
  right_inv b := by
    funext i
    show xor (xor (b i) (c i)) (c i) = b i
    cases b i <;> cases c i <;> rfl

lemma swapL_swapL_swapR (b c : ι → Bool) (x y : ι → α) :
    swapL b (swapL c x y) (swapR c x y) = swapL (fun i => xor (b i) (c i)) x y := by
  funext i; cases hb : b i <;> cases hc : c i <;> simp [swapL, swapR, hb, hc]

lemma swapR_swapL_swapR (b c : ι → Bool) (x y : ι → α) :
    swapR b (swapL c x y) (swapR c x y) = swapR (fun i => xor (b i) (c i)) x y := by
  funext i; cases hb : b i <;> cases hc : c i <;> simp [swapL, swapR, hb, hc]

/-- the conditional expectation of `f g` over the swap of `(x, y)` -/
def swapU (f g : (ι → α) → ℂ) (x y : ι → α) : ℂ :=
  𝔼 b : ι → Bool, f (swapL b x y) * g (swapR b x y)

lemma swapU_swap (f g : (ι → α) → ℂ) (c : ι → Bool) (x y : ι → α) :
    swapU f g (swapL c x y) (swapR c x y) = swapU f g x y := by
  simp only [swapU, swapL_swapL_swapR, swapR_swapL_swapR]
  exact (Fintype.expect_equiv (xorE c) (fun b => f (swapL (fun i => xor (b i) (c i)) x y) *
    g (swapR (fun i => xor (b i) (c i)) x y)) (fun b => f (swapL b x y) * g (swapR b x y))
    (fun b => rfl))

/-- `eq:iden`. -/
lemma val_eq_expect_swap_swap (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = 𝔼 x : ι → α, 𝔼 y : ι → α,
      (𝔼 b : ι → Bool, f₁ (swapL b x y) * f₂ (swapR b x y)) *
        (𝔼 b : ι → Bool, star (f₃ (swapL b x y) * f₄ (swapR b x y))) := by
  have hG : ∀ x y : ι → α, (𝔼 b : ι → Bool, star (f₃ (swapL b x y) * f₄ (swapR b x y))) =
      star (swapU f₃ f₄ x y) := fun x y => by
    rw [swapU, star_expect]
  simp only [hG]
  have hA : val f₁ f₂ f₃ f₄ = 𝔼 x : ι → α, 𝔼 y : ι → α,
      f₁ x * f₂ y * star (swapU f₃ f₄ x y) := by
    simp only [val, swapU, star_expect]
    refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ => ?_))
    rw [Finset.mul_expect]
    refine Finset.expect_congr rfl (fun b _ => ?_)
    simp only [star_mul']
    ring
  have hB : ∀ c : ι → Bool, (𝔼 x : ι → α, 𝔼 y : ι → α, f₁ x * f₂ y * star (swapU f₃ f₄ x y)) =
      𝔼 x : ι → α, 𝔼 y : ι → α,
        f₁ (swapL c x y) * f₂ (swapR c x y) * star (swapU f₃ f₄ x y) := fun c => by
    rw [← expect_expect_swap c (fun x y => f₁ x * f₂ y * star (swapU f₃ f₄ x y))]
    simp only [swapU_swap]
  have hC : (𝔼 x : ι → α, 𝔼 y : ι → α, f₁ x * f₂ y * star (swapU f₃ f₄ x y)) =
      𝔼 c : ι → Bool, 𝔼 x : ι → α, 𝔼 y : ι → α,
        f₁ (swapL c x y) * f₂ (swapR c x y) * star (swapU f₃ f₄ x y) := by
    rw [Finset.expect_congr rfl (fun c _ => (hB c).symm), Fintype.expect_const]
  rw [hA, hC, Finset.expect_comm]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl (fun y _ => ?_)
  rw [Finset.expect_mul]

lemma val_pair_eq_expect_norm_sq (f g : (ι → α) → ℂ) :
    val f g f g = ((𝔼 x : ι → α, 𝔼 y : ι → α, ‖swapU f g x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [val_eq_expect_swap_swap, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun y _ => ?_)
  have hG : (𝔼 b : ι → Bool, star (f (swapL b x y) * g (swapR b x y))) =
      star (swapU f g x y) := by rw [swapU, star_expect]
  rw [hG, Complex.ofReal_pow]
  have := Complex.mul_conj' (swapU f g x y)
  rw [Complex.star_def, swapU]
  exact this

/-- Lemma `cs1`, eq:part1. -/
lemma val_sq_le (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    ‖val f₁ f₂ f₃ f₄‖ ^ 2 ≤ (val f₁ f₂ f₁ f₂).re * (val f₃ f₄ f₃ f₄).re := by
  have h := norm_expect_expect_mul_sq_le (fun x y : ι → α => swapU f₁ f₂ x y)
    (fun x y : ι → α => star (swapU f₃ f₄ x y))
  have e : val f₁ f₂ f₃ f₄ = 𝔼 x : ι → α, 𝔼 y : ι → α,
      swapU f₁ f₂ x y * star (swapU f₃ f₄ x y) := by
    rw [val_eq_expect_swap_swap]
    refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ => ?_))
    rw [swapU, swapU, star_expect]
  rw [e, val_pair_eq_expect_norm_sq, val_pair_eq_expect_norm_sq, Complex.ofReal_re,
    Complex.ofReal_re]
  simpa only [norm_star] using h

/-- Lemma `cs1`, eq:part2. -/
lemma val_pair_sq_le (f₁ f₂ : (ι → α) → ℂ) :
    (val f₁ f₂ f₁ f₂).re ^ 2 ≤ (val f₁ f₁ f₁ f₁).re * (val f₂ f₂ f₂ f₂).re := by
  rw [val_pair_re_eq, val_pair_re_eq, val_pair_re_eq]
  have hr : ∀ S : Finset ι, (box S f₁ f₂ f₁ f₂).re ≤
      Real.sqrt (box S f₁ f₁ f₁ f₁).re * Real.sqrt (box S f₂ f₂ f₂ f₂).re := fun S => by
    rw [← Real.sqrt_mul (box_re_nonneg_pair S f₁ f₁)]
    exact Real.le_sqrt_of_sq_le (box_pair_sq_le S f₁ f₂)
  have h0 : 0 ≤ 𝔼 S : Finset ι, (box S f₁ f₂ f₁ f₂).re :=
    Finset.expect_nonneg (fun S _ => box_re_nonneg_pair S f₁ f₂)
  calc (𝔼 S : Finset ι, (box S f₁ f₂ f₁ f₂).re) ^ 2
      ≤ (𝔼 S : Finset ι, Real.sqrt (box S f₁ f₁ f₁ f₁).re *
          Real.sqrt (box S f₂ f₂ f₂ f₂).re) ^ 2 :=
        pow_le_pow_left₀ h0 (Finset.expect_le_expect (fun S _ => hr S)) 2
    _ ≤ (𝔼 S : Finset ι, Real.sqrt (box S f₁ f₁ f₁ f₁).re ^ 2) *
          𝔼 S : Finset ι, Real.sqrt (box S f₂ f₂ f₂ f₂).re ^ 2 :=
        Finset.expect_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by
        simp only [Real.sq_sqrt (box_re_nonneg_pair _ _ _)]

/-- The swap norm `val(f)^{1/4}`. -/
def swapNorm (f : (ι → α) → ℂ) : ℝ := ((val f f f f).re) ^ (1 / 4 : ℝ)

lemma swapNorm_nonneg (f : (ι → α) → ℂ) : 0 ≤ swapNorm f :=
  Real.rpow_nonneg (val_re_nonneg_pair f f) _

lemma swapNorm_pow_four (f : (ι → α) → ℂ) : swapNorm f ^ 4 = (val f f f f).re := by
  rw [swapNorm, ← Real.rpow_natCast, ← Real.rpow_mul (val_re_nonneg_pair f f)]
  norm_num

/-- the four-slot bound by the swap norms -/
lemma norm_val_le_swapNorm (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    ‖val f₁ f₂ f₃ f₄‖ ≤ swapNorm f₁ * swapNorm f₂ * swapNorm f₃ * swapNorm f₄ := by
  have pair : ∀ g h : (ι → α) → ℂ,
      (val g h g h).re ≤ (swapNorm g * swapNorm h) ^ 2 := fun g h => by
    have h1 := val_pair_sq_le g h
    rw [← swapNorm_pow_four g, ← swapNorm_pow_four h] at h1
    have hg := swapNorm_nonneg g
    have hh := swapNorm_nonneg h
    have h2 : (val g h g h).re ^ 2 ≤ ((swapNorm g * swapNorm h) ^ 2) ^ 2 := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact (sq_le_sq₀ (val_re_nonneg_pair g h) (sq_nonneg _)).1 h2
  have h := val_sq_le f₁ f₂ f₃ f₄
  have n1 := swapNorm_nonneg f₁
  have n2 := swapNorm_nonneg f₂
  have n3 := swapNorm_nonneg f₃
  have n4 := swapNorm_nonneg f₄
  have hb : ‖val f₁ f₂ f₃ f₄‖ ^ 2 ≤ (swapNorm f₁ * swapNorm f₂ * swapNorm f₃ * swapNorm f₄) ^ 2 := by
    calc _ ≤ _ := h
      _ ≤ (swapNorm f₁ * swapNorm f₂) ^ 2 * (swapNorm f₃ * swapNorm f₄) ^ 2 :=
          mul_le_mul (pair f₁ f₂) (pair f₃ f₄) (val_re_nonneg_pair f₃ f₄) (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4)).1 hb

/-! ### Multilinearity of `val` -/

lemma val_add₁ (f g f₂ f₃ f₄ : (ι → α) → ℂ) :
    val (f + g) f₂ f₃ f₄ = val f f₂ f₃ f₄ + val g f₂ f₃ f₄ := by
  simp only [val, Pi.add_apply, Finset.expect_add_distrib, add_mul]

lemma val_add₂ (f₁ f g f₃ f₄ : (ι → α) → ℂ) :
    val f₁ (f + g) f₃ f₄ = val f₁ f f₃ f₄ + val f₁ g f₃ f₄ := by
  simp only [val, Pi.add_apply, mul_add, add_mul, Finset.expect_add_distrib]

lemma val_add₃ (f₁ f₂ f g f₄ : (ι → α) → ℂ) :
    val f₁ f₂ (f + g) f₄ = val f₁ f₂ f f₄ + val f₁ f₂ g f₄ := by
  simp only [val, Pi.add_apply, star_add, mul_add, add_mul, Finset.expect_add_distrib]

lemma val_add₄ (f₁ f₂ f₃ f g : (ι → α) → ℂ) :
    val f₁ f₂ f₃ (f + g) = val f₁ f₂ f₃ f + val f₁ f₂ f₃ g := by
  simp only [val, Pi.add_apply, star_add, mul_add, Finset.expect_add_distrib]

/-- `val` is additive in each slot, packaged as additive homomorphisms. -/
def valHom₁ (f₂ f₃ f₄ : (ι → α) → ℂ) : ((ι → α) → ℂ) →+ ℂ where
  toFun f := val f f₂ f₃ f₄
  map_zero' := by simp [val]
  map_add' f g := val_add₁ f g f₂ f₃ f₄

def valHom₂ (f₁ f₃ f₄ : (ι → α) → ℂ) : ((ι → α) → ℂ) →+ ℂ where
  toFun f := val f₁ f f₃ f₄
  map_zero' := by simp [val]
  map_add' f g := val_add₂ f₁ f g f₃ f₄

def valHom₃ (f₁ f₂ f₄ : (ι → α) → ℂ) : ((ι → α) → ℂ) →+ ℂ where
  toFun f := val f₁ f₂ f f₄
  map_zero' := by simp [val]
  map_add' f g := val_add₃ f₁ f₂ f g f₄

def valHom₄ (f₁ f₂ f₃ : (ι → α) → ℂ) : ((ι → α) → ℂ) →+ ℂ where
  toFun f := val f₁ f₂ f₃ f
  map_zero' := by simp [val]
  map_add' f g := val_add₄ f₁ f₂ f₃ f g

lemma val_sum_four (u : Fin 2 → (ι → α) → ℂ) :
    val (∑ a, u a) (∑ a, u a) (∑ a, u a) (∑ a, u a) =
      ∑ a, ∑ b, ∑ c, ∑ d, val (u a) (u b) (u c) (u d) := by
  have e1 := map_sum (valHom₁ (∑ a, u a) (∑ a, u a) (∑ a, u a)) u Finset.univ
  simp only [valHom₁, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e1
  rw [e1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have e2 := map_sum (valHom₂ (u a) (∑ a, u a) (∑ a, u a)) u Finset.univ
  simp only [valHom₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e2
  rw [e2]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have e3 := map_sum (valHom₃ (u a) (u b) (∑ a, u a)) u Finset.univ
  simp only [valHom₃, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e3
  rw [e3]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have e4 := map_sum (valHom₄ (u a) (u b) (u c)) u Finset.univ
  simp only [valHom₄, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e4
  exact e4

/-- Corollary `norm` (l.648-651): triangle inequality, homogeneity, definiteness. -/
lemma swapNorm_add_le (f g : (ι → α) → ℂ) : swapNorm (f + g) ≤ swapNorm f + swapNorm g := by
  have hs0 := swapNorm_nonneg f
  have hs1 := swapNorm_nonneg g
  let u : Fin 2 → (ι → α) → ℂ := ![f, g]
  have hu : f + g = ∑ a, u a := by simp [u, Fin.sum_univ_two]
  have hnorm : (val (f + g) (f + g) (f + g) (f + g)).re ≤ (swapNorm f + swapNorm g) ^ 4 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hu, val_sum_four]
    calc ‖∑ a, ∑ b, ∑ c, ∑ d, val (u a) (u b) (u c) (u d)‖
        ≤ ∑ a, ∑ b, ∑ c, ∑ d, ‖val (u a) (u b) (u c) (u d)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => ?_))
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
          exact norm_sum_le _ _
      _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
            swapNorm (u a) * swapNorm (u b) * swapNorm (u c) * swapNorm (u d) := by
          gcongr with a _ b _ c _ d _
          exact norm_val_le_swapNorm _ _ _ _
      _ = (swapNorm f + swapNorm g) ^ 4 := by
          simp only [Fin.sum_univ_two, u]
          simp
          ring
  have h4 : swapNorm (f + g) ^ 4 ≤ (swapNorm f + swapNorm g) ^ 4 := by
    rw [swapNorm_pow_four]; exact hnorm
  exact (pow_le_pow_iff_left₀ (swapNorm_nonneg _) (add_nonneg hs0 hs1) (by norm_num)).1 h4

lemma val_smul_four (c : ℂ) (f : (ι → α) → ℂ) :
    val (c • f) (c • f) (c • f) (c • f) = ((‖c‖ ^ 4 : ℝ) : ℂ) * val f f f f := by
  have hK : ((‖c‖ ^ 4 : ℝ) : ℂ) = (c * star c) * (c * star c) := by
    have := Complex.mul_conj' c
    rw [Complex.star_def, this]
    push_cast
    ring
  rw [hK, val, val, Finset.mul_expect]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl (fun y _ => ?_)
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl (fun b _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

lemma swapNorm_smul (c : ℂ) (f : (ι → α) → ℂ) : swapNorm (c • f) = ‖c‖ * swapNorm f := by
  have hre : (val (c • f) (c • f) (c • f) (c • f)).re = ‖c‖ ^ 4 * (val f f f f).re := by
    rw [val_smul_four, Complex.re_ofReal_mul]
  rw [swapNorm, hre, Real.mul_rpow (by positivity) (val_re_nonneg_pair f f)]
  congr 1
  rw [one_div]
  exact_mod_cast Real.pow_rpow_inv_natCast (norm_nonneg c) (by norm_num : (4 : ℕ) ≠ 0)

lemma box_empty_self (f : (ι → α) → ℂ) : box ∅ f f f f = ((l2sq f ^ 2 : ℝ) : ℂ) := by
  have hp : ∀ x y : ι → α, f x * f y * star (f x) * star (f y) =
      ((‖f x‖ ^ 2 * ‖f y‖ ^ 2 : ℝ) : ℂ) := by
    intro x y
    rw [show f x * f y * star (f x) * star (f y) = (f x * star (f x)) * (f y * star (f y)) by
      ring, Complex.star_def, Complex.mul_conj', Complex.mul_conj']
    push_cast
    ring
  simp only [box, Finset.piecewise_empty, hp]
  have h2 : l2sq f ^ 2 = 𝔼 x : ι → α, 𝔼 y : ι → α, (‖f x‖ ^ 2 * ‖f y‖ ^ 2) := by
    rw [sq, l2sq, Finset.expect_mul_expect]
  rw [h2, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [Complex.ofReal_expect]

lemma swapNorm_eq_zero_iff (f : (ι → α) → ℂ) : swapNorm f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hN : (val f f f f).re = 0 := by
      have := (Real.rpow_eq_zero (val_re_nonneg_pair f f) (by norm_num : (1 / 4 : ℝ) ≠ 0)).1 h
      exact this
    rw [val_pair_re_eq, Finset.expect_eq_zero_iff_of_nonneg
      (fun S _ => box_re_nonneg_pair S f f)] at hN
    have h0 := hN ∅ (Finset.mem_univ _)
    rw [box_empty_self, Complex.ofReal_re] at h0
    have hl : l2sq f = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h0
    have := (Fintype.expect_eq_zero_iff_of_nonneg (f := fun x : ι → α => ‖f x‖ ^ 2)
      (fun x => sq_nonneg _)).1 hl
    funext x
    have hx := congrFun this x
    simpa using hx
  · rintro rfl
    have : val (0 : (ι → α) → ℂ) 0 0 0 = 0 := by simp [val]
    rw [swapNorm, this]
    simp

end SwapNorm

end TrackB

end RestrictedPolynomials
