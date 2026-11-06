module

public import RestrictedPolynomials.TrackB.SwapNorm
public import RestrictedPolynomials.TrackB.Restrict

/-!
# Track B: swap norm and restrictions

Source: CSP_6 (arXiv:2411.15133v1 `main.tex`) l. 662-675 (`lemma:valrr`), l. 790-802
(`lemma:valperp`), l. 857-874 (`lemma:phirr`), l. 991 (`val-multiplicative`).
Covers CSP_6 `lemma:valperp`, `lemma:valrr`, `lemma:svdinc#val-multiplicative`,
`lemma:phirr` and `lemma:phirr#averaging-bound`.

**Source correction.** The printed probability
`δ‖f‖²/(CB²)` of `phirr` is false (it needs `X ≤ CB²`, which fails when `Φ - 2δ < 0`). It is
replaced by the source's own constant `δ‖f‖²/((C + 2δ + ‖g‖²/‖f‖²)B²)`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapRestrict
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `x ↦ g(x|_S) · h(x|_{Sᶜ})`, the product function on complementary coordinate sets. -/
def prodSplit (S : Finset ι) (g : (↥S → α) → ℂ) (h : (↥Sᶜ → α) → ℂ) : (ι → α) → ℂ :=
  fun x => g (fun i => x i) * h (fun i => x i)

/-! ### Helpers: splitting coordinates -/

private def splitEquiv {β : Type} (S : Finset ι) : (ι → β) ≃ (↥S → β) × (↥Sᶜ → β) where
  toFun x := (fun i => x i, fun i => x i)
  invFun p := glueFree S p.1 p.2
  left_inv x := by
    funext i; by_cases h : i ∈ S <;> simp [glueFree, h]
  right_inv := by
    rintro ⟨y, z⟩
    refine Prod.ext ?_ ?_
    · funext i; simp [glueFree, i.2]
    · funext i
      have : (i : ι) ∉ S := mem_compl.1 i.2
      simp [glueFree, this]

private lemma expect_split {β : Type} [Fintype β] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (S : Finset ι) (h : (ι → β) → M) :
    𝔼 x : ι → β, h x = 𝔼 u : ↥S → β, 𝔼 v : ↥Sᶜ → β, h (glueFree S u v) := by
  rw [← Finset.expect_product' (f := fun u v => h (glueFree S u v)), Finset.univ_product_univ]
  exact Fintype.expect_equiv (splitEquiv S) _ _
    (fun x => congrArg h ((splitEquiv S).symm_apply_apply x).symm)

private lemma glue_restrS {β : Type} (S : Finset ι) (u : ↥S → β) (v : ↥Sᶜ → β) :
    (fun i : ↥S => glueFree S u v i) = u := by
  funext i; simp [glueFree, i.2]

private lemma glue_restrT {β : Type} (S : Finset ι) (u : ↥S → β) (v : ↥Sᶜ → β) :
    (fun i : ↥Sᶜ => glueFree S u v i) = v := by
  funext i
  have : (i : ι) ∉ S := mem_compl.1 i.2
  simp [glueFree, this]

omit [Fintype α] [DecidableEq α] in
private lemma glue_swapL (S : Finset ι) (c : ↥S → Bool) (d : ↥Sᶜ → Bool) (p q : ↥S → α)
    (u v : ↥Sᶜ → α) :
    swapL (glueFree S c d) (glueFree S p u) (glueFree S q v) =
      glueFree S (swapL c p q) (swapL d u v) := by
  funext i
  by_cases h : i ∈ S <;> simp [swapL, glueFree, h]

omit [Fintype α] [DecidableEq α] in
private lemma glue_swapR (S : Finset ι) (c : ↥S → Bool) (d : ↥Sᶜ → Bool) (p q : ↥S → α)
    (u v : ↥Sᶜ → α) :
    swapR (glueFree S c d) (glueFree S p u) (glueFree S q v) =
      glueFree S (swapR c p q) (swapR d u v) := by
  funext i
  by_cases h : i ∈ S <;> simp [swapR, glueFree, h]

omit [DecidableEq α] in
/-- the triple expectation `𝔼 x y b` split along `S` and `Sᶜ`. -/
private lemma expect3_split (S : Finset ι)
    (Φ : (ι → α) → (ι → α) → (ι → Bool) → ℂ) :
    𝔼 x : ι → α, 𝔼 y : ι → α, 𝔼 b : ι → Bool, Φ x y b =
      𝔼 p : ↥S → α, 𝔼 u : ↥Sᶜ → α, 𝔼 q : ↥S → α, 𝔼 v : ↥Sᶜ → α,
        𝔼 c : ↥S → Bool, 𝔼 d : ↥Sᶜ → Bool,
          Φ (glueFree S p u) (glueFree S q v) (glueFree S c d) := by
  rw [expect_split S]
  refine Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun u _ => ?_))
  rw [expect_split S]
  refine Finset.expect_congr rfl (fun q _ => Finset.expect_congr rfl (fun v _ => ?_))
  rw [expect_split S]

private lemma expect3_mul {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type} [Fintype X₁] [Fintype X₂] [Fintype Y₁]
    [Fintype Y₂] [Fintype Z₁] [Fintype Z₂]
    (A : X₁ → Y₁ → Z₁ → ℂ) (B : X₂ → Y₂ → Z₂ → ℂ) :
    (𝔼 x₁, 𝔼 y₁, 𝔼 z₁, A x₁ y₁ z₁) * (𝔼 x₂, 𝔼 y₂, 𝔼 z₂, B x₂ y₂ z₂) =
      𝔼 x₁, 𝔼 x₂, 𝔼 y₁, 𝔼 y₂, 𝔼 z₁, 𝔼 z₂, A x₁ y₁ z₁ * B x₂ y₂ z₂ := by
  rw [Finset.expect_mul_expect]
  refine Finset.expect_congr rfl (fun x₁ _ => Finset.expect_congr rfl (fun x₂ _ => ?_))
  rw [Finset.expect_mul_expect]
  refine Finset.expect_congr rfl (fun y₁ _ => Finset.expect_congr rfl (fun y₂ _ => ?_))
  rw [Finset.expect_mul_expect]

omit [DecidableEq α] in
/-- CSP_6 `lemma:svdinc#val-multiplicative`, four-function form. -/
theorem val_prodSplit (S : Finset ι) (g₁ g₂ g₃ g₄ : (↥S → α) → ℂ)
    (h₁ h₂ h₃ h₄ : (↥Sᶜ → α) → ℂ) :
    val (prodSplit S g₁ h₁) (prodSplit S g₂ h₂) (prodSplit S g₃ h₃) (prodSplit S g₄ h₄) =
      val g₁ g₂ g₃ g₄ * val h₁ h₂ h₃ h₄ := by
  rw [val, val, val, expect3_mul]
  rw [expect3_split S (fun x y b => prodSplit S g₁ h₁ x * prodSplit S g₂ h₂ y *
    star (prodSplit S g₃ h₃ (swapL b x y)) * star (prodSplit S g₄ h₄ (swapR b x y)))]
  refine Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun u _ =>
    Finset.expect_congr rfl (fun q _ => Finset.expect_congr rfl (fun v _ =>
      Finset.expect_congr rfl (fun c _ => Finset.expect_congr rfl (fun d _ => ?_))))))
  simp only [prodSplit, glue_swapL, glue_swapR, glue_restrS, glue_restrT, star_mul']
  ring

omit [DecidableEq α] in
/-- CSP_6 `lemma:svdinc#val-multiplicative`, as printed: `val(g·h) = val(g)·val(h)`. -/
theorem val_prodSplit_self (S : Finset ι) (g : (↥S → α) → ℂ) (h : (↥Sᶜ → α) → ℂ) :
    val (prodSplit S g h) (prodSplit S g h) (prodSplit S g h) (prodSplit S g h) =
      val g g g g * val h h h h :=
  val_prodSplit S g g g g h h h h

/-! ### `valperp` -/

omit [DecidableEq α] in
private lemma val_swap_xy (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = val f₂ f₁ f₄ f₃ := by
  simp only [val]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ =>
    Finset.expect_congr rfl (fun b _ => ?_)))
  show f₁ y * f₂ x * star (f₃ (swapR b x y)) * star (f₄ (swapL b x y)) =
    f₂ x * f₁ y * star (f₄ (swapL b x y)) * star (f₃ (swapR b x y))
  ring

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
private lemma swapL_not (b : ι → Bool) (x y : ι → α) :
    swapL (fun i => !b i) x y = swapR b x y := by
  funext i; cases h : b i <;> simp [swapL, swapR, h]

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
private lemma swapR_not (b : ι → Bool) (x y : ι → α) :
    swapR (fun i => !b i) x y = swapL b x y := by
  funext i; cases h : b i <;> simp [swapL, swapR, h]

omit [DecidableEq α] in
private lemma val_swap_34 (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = val f₁ f₂ f₄ f₃ := by
  simp only [val]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ => ?_))
  let e : (ι → Bool) ≃ (ι → Bool) :=
    Equiv.piCongrRight fun _ => (⟨not, not, Bool.not_not, Bool.not_not⟩ : Bool ≃ Bool)
  refine Fintype.expect_equiv e _ _ (fun b => ?_)
  show _ = f₁ x * f₂ y * star (f₄ (swapL (fun i => !b i) x y)) *
    star (f₃ (swapR (fun i => !b i) x y))
  rw [swapL_not, swapR_not]
  ring

omit [DecidableEq α] in
private lemma val_smul_slots (a b c d : ℂ) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val (a • f₁) (b • f₂) (c • f₃) (d • f₄) = a * b * star c * star d * val f₁ f₂ f₃ f₄ := by
  rw [val, val, Finset.mul_expect]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl (fun y _ => ?_)
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl (fun z _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

private lemma norm_add_sq_aux (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (a * star b).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

omit [DecidableEq α] in
private lemma l2sq_add_smul (h₁ h₂ : (ι → α) → ℂ)
    (horth : 𝔼 x : ι → α, h₁ x * star (h₂ x) = 0) (c : ℂ) :
    l2sq (h₁ + c • h₂) = l2sq h₁ + ‖c‖ ^ 2 * l2sq h₂ := by
  have hx : ∀ x, ‖(h₁ + c • h₂) x‖ ^ 2 =
      ‖h₁ x‖ ^ 2 + ‖c‖ ^ 2 * ‖h₂ x‖ ^ 2 + 2 * ((star c * (h₁ x * star (h₂ x))).re) := by
    intro x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [norm_add_sq_aux, norm_mul, mul_pow]
    congr 2
    simp only [star_mul']
    ring_nf
  have hz : (𝔼 x : ι → α, 2 * ((star c * (h₁ x * star (h₂ x))).re)) = 0 := by
    rw [← Finset.mul_expect, ← Complex.re_expect, ← Finset.mul_expect, horth]
    simp
  rw [l2sq, l2sq, l2sq]
  simp only [hx]
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, hz, ← Finset.mul_expect]
  ring

private lemma val_expand (h₁ h₂ : (ι → α) → ℂ) (c : ℂ) :
    val (h₁ + c • h₂) (h₁ + c • h₂) (h₁ + c • h₂) (h₁ + c • h₂) =
      val h₁ h₁ h₁ h₁ + star c * val h₁ h₁ h₁ h₂ +
        (star c * val h₁ h₁ h₂ h₁ + star c * star c * val h₁ h₁ h₂ h₂) +
          (c * val h₁ h₂ h₁ h₁ + c * star c * val h₁ h₂ h₁ h₂ +
            (c * star c * val h₁ h₂ h₂ h₁ + c * star c * star c * val h₁ h₂ h₂ h₂)) +
        (c * val h₂ h₁ h₁ h₁ + c * star c * val h₂ h₁ h₁ h₂ +
            (c * star c * val h₂ h₁ h₂ h₁ + c * star c * star c * val h₂ h₁ h₂ h₂) +
          (c * c * val h₂ h₂ h₁ h₁ + c * c * star c * val h₂ h₂ h₁ h₂ +
            (c * c * star c * val h₂ h₂ h₂ h₁ + c * c * star c * star c * val h₂ h₂ h₂ h₂))) := by
  have e := val_sum_four ![(1 : ℂ) • h₁, c • h₂]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    val_smul_slots] at e
  simp only [one_smul] at e
  simp only [one_mul, mul_one, star_one] at e
  exact e

private lemma val_re_le_four (h₁ h₂ : (ι → α) → ℂ)
    (horth : 𝔼 x : ι → α, h₁ x * star (h₂ x) = 0) (hn₁ : l2sq h₁ = 1) (hn₂ : l2sq h₂ = 1)
    (c : ℂ) (hc : ‖c‖ = 1) :
    (val (h₁ + c • h₂) (h₁ + c • h₂) (h₁ + c • h₂) (h₁ + c • h₂)).re ≤ 4 := by
  have hl : l2sq (h₁ + c • h₂) = 2 := by
    rw [l2sq_add_smul h₁ h₂ horth, hn₁, hn₂, hc]; norm_num
  refine (Complex.re_le_norm _).trans ((norm_val_le _ _ _ _).trans ?_)
  rw [hl]
  have : Real.sqrt 2 * Real.sqrt 2 * Real.sqrt 2 * Real.sqrt 2 = 4 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc _ = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt 2) := by ring
      _ = 4 := by rw [h2]; norm_num
  rw [this]

/-- CSP_6 `lemma:valperp`. -/
theorem val_orthonormal_le (h₁ h₂ : (ι → α) → ℂ)
    (horth : 𝔼 x : ι → α, h₁ x * star (h₂ x) = 0) (hn₁ : l2sq h₁ = 1) (hn₂ : l2sq h₂ = 1) :
    (val h₁ h₂ h₁ h₂).re ≤ 2 / 3 := by
  have s1 : val h₁ h₂ h₂ h₁ = val h₁ h₂ h₁ h₂ := (val_swap_34 h₁ h₂ h₁ h₂).symm
  have s2 : val h₂ h₁ h₁ h₂ = val h₁ h₂ h₁ h₂ := by
    rw [← s1]; exact (val_swap_xy h₁ h₂ h₂ h₁).symm
  have s3 : val h₂ h₁ h₂ h₁ = val h₁ h₂ h₁ h₂ := (val_swap_xy h₁ h₂ h₁ h₂).symm
  have b1 := val_re_le_four h₁ h₂ horth hn₁ hn₂ 1 (by simp)
  have b2 := val_re_le_four h₁ h₂ horth hn₁ hn₂ Complex.I (by simp)
  have b3 := val_re_le_four h₁ h₂ horth hn₁ hn₂ (-1) (by simp)
  have b4 := val_re_le_four h₁ h₂ horth hn₁ hn₂ (-Complex.I) (by simp)
  have hsum : val (h₁ + (1 : ℂ) • h₂) (h₁ + (1 : ℂ) • h₂) (h₁ + (1 : ℂ) • h₂) (h₁ + (1 : ℂ) • h₂) +
      val (h₁ + Complex.I • h₂) (h₁ + Complex.I • h₂) (h₁ + Complex.I • h₂) (h₁ + Complex.I • h₂) +
      val (h₁ + (-1 : ℂ) • h₂) (h₁ + (-1 : ℂ) • h₂) (h₁ + (-1 : ℂ) • h₂) (h₁ + (-1 : ℂ) • h₂) +
      val (h₁ + (-Complex.I) • h₂) (h₁ + (-Complex.I) • h₂) (h₁ + (-Complex.I) • h₂)
        (h₁ + (-Complex.I) • h₂) =
      4 * (val h₁ h₁ h₁ h₁ + val h₂ h₂ h₂ h₂ + 4 * val h₁ h₂ h₁ h₂) := by
    rw [val_expand, val_expand, val_expand, val_expand, s1, s2, s3]
    simp only [star_one, star_neg, Complex.star_def, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring_nf
  have e4 : ∀ z : ℂ, (4 * z).re = 4 * z.re := fun z => by simp [Complex.mul_re]
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, e4] at hre
  have hx := val_re_nonneg_pair h₁ h₂
  have hy1 := val_re_nonneg_pair h₁ h₁
  have hy2 := val_re_nonneg_pair h₂ h₂
  have hcs := val_pair_sq_le h₁ h₂
  nlinarith [sq_nonneg ((val h₁ h₁ h₁ h₁).re - (val h₂ h₂ h₂ h₂).re)]

/-! ### `valrr` -/

omit [DecidableEq α] in
private lemma expect_l2sq_restrict (I : Finset ι) (f : (ι → α) → ℂ) :
    𝔼 z : ↥I → α, l2sq (restrictFix I z f) = l2sq f := by
  rw [l2sq, expect_split I]
  rfl

private lemma expect6_reorder {P U Q V C D : Type} [Fintype P] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype C] [Fintype D] (G : P → U → Q → V → C → D → ℂ) :
    𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, 𝔼 c, 𝔼 d, G p u q v c d =
      𝔼 c, 𝔼 p, 𝔼 q, 𝔼 u, 𝔼 v, 𝔼 d, G p u q v c d := by
  calc 𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, 𝔼 c, 𝔼 d, G p u q v c d
      = 𝔼 p, 𝔼 u, 𝔼 q, 𝔼 c, 𝔼 v, 𝔼 d, G p u q v c d :=
        Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun u _ =>
          Finset.expect_congr rfl (fun q _ => Finset.expect_comm _ _ _)))
    _ = 𝔼 p, 𝔼 u, 𝔼 c, 𝔼 q, 𝔼 v, 𝔼 d, G p u q v c d :=
        Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun u _ =>
          Finset.expect_comm _ _ _))
    _ = 𝔼 p, 𝔼 c, 𝔼 u, 𝔼 q, 𝔼 v, 𝔼 d, G p u q v c d :=
        Finset.expect_congr rfl (fun p _ => Finset.expect_comm _ _ _)
    _ = 𝔼 c, 𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, 𝔼 d, G p u q v c d := Finset.expect_comm _ _ _
    _ = 𝔼 c, 𝔼 p, 𝔼 q, 𝔼 u, 𝔼 v, 𝔼 d, G p u q v c d :=
        Finset.expect_congr rfl (fun c _ => Finset.expect_congr rfl (fun p _ =>
          Finset.expect_comm _ _ _))

omit [DecidableEq α] in
/-- the source's first display in `valrr`: `val f` as an average of `val` of restrictions. -/
private lemma val_eq_expect_restrict (I : Finset ι) (f : (ι → α) → ℂ) :
    val f f f f = 𝔼 c : ↥I → Bool, 𝔼 p : ↥I → α, 𝔼 q : ↥I → α,
      val (restrictFix I p f) (restrictFix I q f) (restrictFix I (swapL c p q) f)
        (restrictFix I (swapR c p q) f) := by
  rw [val]
  rw [expect3_split I (fun x y b => f x * f y * star (f (swapL b x y)) * star (f (swapR b x y)))]
  rw [expect6_reorder]
  refine Finset.expect_congr rfl (fun c _ => Finset.expect_congr rfl (fun p _ =>
    Finset.expect_congr rfl (fun q _ => ?_)))
  rw [val]
  refine Finset.expect_congr rfl (fun u _ => Finset.expect_congr rfl (fun v _ =>
    Finset.expect_congr rfl (fun d _ => ?_)))
  rw [glue_swapL, glue_swapR]
  rfl

private lemma cs_expect2 {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (u w : κ₁ → κ₂ → ℝ) :
    (𝔼 p, 𝔼 q, u p q * w p q) ^ 2 ≤ (𝔼 p, 𝔼 q, u p q ^ 2) * 𝔼 p, 𝔼 q, w p q ^ 2 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ (Finset.univ : Finset κ₂))
    (fun r => u r.1 r.2) (fun r => w r.1 r.2)
  rw [← Finset.expect_product' (f := fun p q => u p q * w p q),
    ← Finset.expect_product' (f := fun p q => u p q ^ 2),
    ← Finset.expect_product' (f := fun p q => w p q ^ 2)]
  exact h

private lemma swapNorm_sq_eq (f : (ι → α) → ℂ) :
    swapNorm f ^ 2 = ((val f f f f).re) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← swapNorm_pow_four f, show swapNorm f ^ 4 = (swapNorm f ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg _)]

/-- CSP_6 `lemma:valrr`. -/
theorem val_rpow_half_le_expect_restrict (I : Finset ι) (f : (ι → α) → ℂ) :
    ((val f f f f).re) ^ (1 / 2 : ℝ) ≤
      𝔼 z : ↥I → α, ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
        (restrictFix I z f)).re) ^ (1 / 2 : ℝ) := by
  set N : (↥I → α) → ℝ := fun z => swapNorm (restrictFix I z f) with hN
  have hN0 : ∀ z, 0 ≤ N z := fun z => swapNorm_nonneg _
  set A : ℝ := 𝔼 z, N z ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.expect_nonneg (fun z _ => sq_nonneg _)
  have hc : ∀ c : ↥I → Bool, (𝔼 p : ↥I → α, 𝔼 q : ↥I → α,
      (val (restrictFix I p f) (restrictFix I q f) (restrictFix I (swapL c p q) f)
        (restrictFix I (swapR c p q) f)).re) ≤ A ^ 2 := by
    intro c
    set u : (↥I → α) → (↥I → α) → ℝ := fun p q => N p * N q with hu
    set w : (↥I → α) → (↥I → α) → ℝ := fun p q => N (swapL c p q) * N (swapR c p q) with hw
    have h1 : (𝔼 p : ↥I → α, 𝔼 q : ↥I → α,
        (val (restrictFix I p f) (restrictFix I q f) (restrictFix I (swapL c p q) f)
          (restrictFix I (swapR c p q) f)).re) ≤ 𝔼 p : ↥I → α, 𝔼 q : ↥I → α, u p q * w p q := by
      refine Finset.expect_le_expect (fun p _ => Finset.expect_le_expect (fun q _ => ?_))
      refine (Complex.re_le_norm _).trans ((norm_val_le_swapNorm _ _ _ _).trans_eq ?_)
      simp only [hu, hw, hN]
      ring
    have h0 : 0 ≤ 𝔼 p : ↥I → α, 𝔼 q : ↥I → α, u p q * w p q :=
      Finset.expect_nonneg (fun p _ => Finset.expect_nonneg (fun q _ =>
        mul_nonneg (mul_nonneg (hN0 _) (hN0 _)) (mul_nonneg (hN0 _) (hN0 _))))
    have h2 := cs_expect2 u w
    have e1 : (𝔼 p : ↥I → α, 𝔼 q : ↥I → α, u p q ^ 2) = A * A := by
      rw [hA, Finset.expect_mul_expect]
      refine Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun q _ => ?_))
      simp only [hu]; ring
    have e2 : (𝔼 p : ↥I → α, 𝔼 q : ↥I → α, w p q ^ 2) = A * A := by
      have := expect_expect_swap c (fun p q : ↥I → α => N p ^ 2 * N q ^ 2)
      rw [hA, Finset.expect_mul_expect, ← this]
      refine Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun q _ => ?_))
      simp only [hw]; ring
    rw [e1, e2] at h2
    refine h1.trans ((sq_le_sq₀ h0 (sq_nonneg A)).1 ?_)
    calc _ ≤ _ := h2
      _ = _ := by ring
  have key : (val f f f f).re ≤ A ^ 2 := by
    rw [val_eq_expect_restrict I f]
    simp only [Complex.re_expect]
    calc _ ≤ 𝔼 _c : ↥I → Bool, A ^ 2 := Finset.expect_le_expect (fun c _ => hc c)
      _ = A ^ 2 := Fintype.expect_const _
  calc ((val f f f f).re) ^ (1 / 2 : ℝ) ≤ (A ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (val_re_nonneg_pair f f) key (by norm_num)
    _ = A := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hA0]
    _ = _ := Finset.expect_congr rfl (fun z _ => swapNorm_sq_eq _)

/-! ### `phirr` -/

private lemma val_rpow_half_le_l2sq (f : (ι → α) → ℂ) :
    ((val f f f f).re) ^ (1 / 2 : ℝ) ≤ l2sq f := by
  rw [← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_iff.2 ⟨l2sq_nonneg f, ?_⟩
  refine (Complex.re_le_norm _).trans ((norm_val_le f f f f).trans_eq ?_)
  have h2 : Real.sqrt (l2sq f) * Real.sqrt (l2sq f) = l2sq f :=
    Real.mul_self_sqrt (l2sq_nonneg f)
  calc _ = (Real.sqrt (l2sq f) * Real.sqrt (l2sq f)) * (Real.sqrt (l2sq f) * Real.sqrt (l2sq f)) := by
        ring
    _ = _ := by rw [h2]; ring

private lemma l2sq_le_of_bound {κ : Type} [Fintype κ] [DecidableEq κ] {β : Type} [Fintype β]
    [DecidableEq β] (f : (κ → β) → ℂ) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) : l2sq f ≤ B ^ 2 := by
  rw [l2sq]
  rcases isEmpty_or_nonempty (κ → β) with hn | hn
  · simp only [Finset.univ_eq_empty, Finset.expect_empty]
    positivity
  · calc 𝔼 x : κ → β, ‖f x‖ ^ 2 ≤ 𝔼 _x : κ → β, B ^ 2 :=
          Finset.expect_le_expect (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)
      _ = B ^ 2 := Fintype.expect_const _

private lemma X_le_aux {C δ v Lz Gz Φ r : ℝ} (hC : 0 ≤ C) (hv : v ≤ Lz) (hG : 0 ≤ Gz)
    (hL : 0 ≤ Lz) (hΦ : -r ≤ Φ) :
    C * v - Gz - (Φ - 2 * δ) * Lz ≤ (C + 2 * δ + r) * Lz := by
  nlinarith [mul_le_mul_of_nonneg_left hv hC, mul_le_mul_of_nonneg_right hΦ hL]

open scoped Classical in
private lemma averaging_core {κ : Type} [Fintype κ] (X : κ → ℝ) (a M : ℝ) (ha : 0 < a)
    (hX : ∀ z, X z ≤ M) (hE : 2 * a ≤ 𝔼 z, X z) :
    a / M ≤ 𝔼 z, if a ≤ X z then (1 : ℝ) else 0 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp at hE
    linarith
  set p : ℝ := 𝔼 z, if a ≤ X z then (1 : ℝ) else 0 with hp
  have hp0 : 0 ≤ p := Finset.expect_nonneg (fun z _ => by split_ifs <;> norm_num)
  have hpt : ∀ z, X z ≤ a + (M - a) * (if a ≤ X z then (1 : ℝ) else 0) := by
    intro z
    by_cases h : a ≤ X z
    · simp only [h, ↓reduceIte]; linarith [hX z]
    · simp only [h, ↓reduceIte]; linarith [not_le.1 h]
  have h2 : 𝔼 z, X z ≤ a + (M - a) * p := by
    calc 𝔼 z, X z ≤ 𝔼 z, (a + (M - a) * (if a ≤ X z then (1 : ℝ) else 0)) :=
          Finset.expect_le_expect (fun z _ => hpt z)
      _ = a + (M - a) * p := by
          rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
  have hMa : 0 < M - a := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  have hM : 0 < M := by linarith
  rw [div_le_iff₀ hM]
  nlinarith [mul_nonneg ha.le hp0]

open scoped Classical in
/-- CSP_6 `lemma:phirr#averaging-bound`, with the corrected probability.

The probability printed in the source, `δ‖f‖²/(CB²)`, is false (the averaged variable is not bounded
by `CB²` when `Φ - 2δ < 0`). It is
replaced by the source's own constant: the probability is `δ‖f‖²/((C + 2δ + ‖g‖²/‖f‖²)B²)`. -/
theorem phirr_averaging_bound (I : Finset ι) (f g : (ι → α) → ℂ) {B C δ : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hC : 1 < C) (hδ : 0 < δ)
    (Φ : ℝ) (hΦ : Φ = (C * ((val f f f f).re) ^ (1 / 2 : ℝ) - l2sq g) / l2sq f)
    (hEX : 2 * δ * l2sq f ≤ 𝔼 z : ↥I → α,
      (C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
          (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)
        - (Φ - 2 * δ) * l2sq (restrictFix I z f))) :
    δ * l2sq f / ((C + 2 * δ + l2sq g / l2sq f) * B ^ 2) ≤
      𝔼 z : ↥I → α, if δ * l2sq f ≤
        C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
          (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)
          - (Φ - 2 * δ) * l2sq (restrictFix I z f) then (1 : ℝ) else 0 := by
  have hp0 : 0 ≤ 𝔼 z : ↥I → α, if δ * l2sq f ≤
        C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
          (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)
          - (Φ - 2 * δ) * l2sq (restrictFix I z f) then (1 : ℝ) else 0 :=
    Finset.expect_nonneg (fun z _ => by split_ifs <;> norm_num)
  rcases (l2sq_nonneg f).eq_or_lt with h0 | hpos
  · refine le_trans (le_of_eq ?_) hp0
    rw [← h0, mul_zero, zero_div]
  have hr : 0 ≤ l2sq g / l2sq f := div_nonneg (l2sq_nonneg g) hpos.le
  have hK : 0 < C + 2 * δ + l2sq g / l2sq f := by linarith
  have hLB : l2sq f ≤ B ^ 2 := l2sq_le_of_bound f hB
  have hB2 : 0 < B ^ 2 := lt_of_lt_of_le hpos hLB
  have hΦr : -(l2sq g / l2sq f) ≤ Φ := by
    have hv0 : 0 ≤ C * ((val f f f f).re) ^ (1 / 2 : ℝ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (val_re_nonneg_pair f f) _)
    rw [hΦ, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  refine averaging_core (fun z => C * ((val (restrictFix I z f) (restrictFix I z f)
      (restrictFix I z f) (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)
      - (Φ - 2 * δ) * l2sq (restrictFix I z f)) (δ * l2sq f)
    ((C + 2 * δ + l2sq g / l2sq f) * B ^ 2) (mul_pos hδ hpos) (fun z => ?_) (by linarith [hEX])
  have h1 := X_le_aux (C := C) (δ := δ) (Gz := l2sq (restrictFix I z g)) (Φ := Φ)
    (r := l2sq g / l2sq f) (by linarith) (val_rpow_half_le_l2sq (restrictFix I z f))
    (l2sq_nonneg _) (l2sq_nonneg _) hΦr
  have h2 : l2sq (restrictFix I z f) ≤ B ^ 2 := by
    refine l2sq_le_of_bound _ (fun y => hB _)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK.le)

open scoped Classical in
/-- CSP_6 `lemma:phirr`, with the corrected probability.

The probability printed in the source, `δ‖f‖²/(CB²)`, is false. It is replaced by the source's own constant: the probability is
`δ‖f‖²/((C + 2δ + ‖g‖²/‖f‖²)B²)`. Both conclusions on the event are the printed ones. -/
theorem phirr (I : Finset ι) (f g : (ι → α) → ℂ) {B C δ : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hC : 1 < C) (hδ : 0 < δ) :
    δ * l2sq f / ((C + 2 * δ + l2sq g / l2sq f) * B ^ 2) ≤
      𝔼 z : ↥I → α, if
        ((C * ((val f f f f).re) ^ (1 / 2 : ℝ) - l2sq g) / l2sq f - 2 * δ ≤
          (C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
            (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)) /
              l2sq (restrictFix I z f)) ∧
        δ * l2sq f / (C + 2 * δ + l2sq g / l2sq f) ≤ l2sq (restrictFix I z f)
        then (1 : ℝ) else 0 := by
  have hp0 : 0 ≤ 𝔼 z : ↥I → α, if
        ((C * ((val f f f f).re) ^ (1 / 2 : ℝ) - l2sq g) / l2sq f - 2 * δ ≤
          (C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
            (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)) /
              l2sq (restrictFix I z f)) ∧
        δ * l2sq f / (C + 2 * δ + l2sq g / l2sq f) ≤ l2sq (restrictFix I z f)
        then (1 : ℝ) else 0 :=
    Finset.expect_nonneg (fun z _ => by split_ifs <;> norm_num)
  rcases (l2sq_nonneg f).eq_or_lt with h0 | hpos
  · refine le_trans (le_of_eq ?_) hp0
    rw [← h0, mul_zero, zero_div]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = (C * ((val f f f f).re) ^ (1 / 2 : ℝ) - l2sq g) / l2sq f :=
    ⟨_, rfl⟩
  rw [← hΦ]
  have hr : 0 ≤ l2sq g / l2sq f := div_nonneg (l2sq_nonneg g) hpos.le
  have hK : 0 < C + 2 * δ + l2sq g / l2sq f := by linarith
  have hΦL : Φ * l2sq f = C * ((val f f f f).re) ^ (1 / 2 : ℝ) - l2sq g := by
    rw [hΦ]; field_simp
  have hEX : 2 * δ * l2sq f ≤ 𝔼 z : ↥I → α,
      (C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
          (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)
        - (Φ - 2 * δ) * l2sq (restrictFix I z f)) := by
    simp only [Finset.expect_sub_distrib, ← Finset.mul_expect]
    rw [expect_l2sq_restrict I f, expect_l2sq_restrict I g]
    have hv := val_rpow_half_le_expect_restrict I f
    have := mul_le_mul_of_nonneg_left hv (by linarith : (0 : ℝ) ≤ C)
    nlinarith
  refine (phirr_averaging_bound I f g hB hC hδ Φ hΦ hEX).trans
    (Finset.expect_le_expect (fun z _ => ?_))
  by_cases hE : δ * l2sq f ≤
      C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
        (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)
        - (Φ - 2 * δ) * l2sq (restrictFix I z f)
  · have hΦr : -(l2sq g / l2sq f) ≤ Φ := by
      have hv0 : 0 ≤ C * ((val f f f f).re) ^ (1 / 2 : ℝ) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg (val_re_nonneg_pair f f) _)
      rw [hΦ, ← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hpos.le
    have h1 := X_le_aux (C := C) (δ := δ) (Gz := l2sq (restrictFix I z g)) (Φ := Φ)
      (r := l2sq g / l2sq f) (by linarith) (val_rpow_half_le_l2sq (restrictFix I z f))
      (l2sq_nonneg _) (l2sq_nonneg _) hΦr
    have ha : 0 < δ * l2sq f := mul_pos hδ hpos
    have hLz : 0 < l2sq (restrictFix I z f) := by
      by_contra hn
      have hn' : l2sq (restrictFix I z f) ≤ 0 := not_lt.1 hn
      have := mul_le_mul_of_nonneg_left hn' hK.le
      linarith
    have hc1 : Φ - 2 * δ ≤
        (C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
          (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)) /
            l2sq (restrictFix I z f) := by
      rw [le_div_iff₀ hLz]
      linarith
    have hc2 : δ * l2sq f / (C + 2 * δ + l2sq g / l2sq f) ≤ l2sq (restrictFix I z f) := by
      rw [div_le_iff₀ hK]
      linarith
    have hev : (Φ - 2 * δ ≤
          (C * ((val (restrictFix I z f) (restrictFix I z f) (restrictFix I z f)
            (restrictFix I z f)).re) ^ (1 / 2 : ℝ) - l2sq (restrictFix I z g)) /
              l2sq (restrictFix I z f)) ∧
        δ * l2sq f / (C + 2 * δ + l2sq g / l2sq f) ≤ l2sq (restrictFix I z f) := ⟨hc1, hc2⟩
    simp only [hE, hev, ↓reduceIte]
    simp
  · simp only [hE, ↓reduceIte]
    split_ifs <;> norm_num

end SwapRestrict
end TrackB
end RestrictedPolynomials
end
