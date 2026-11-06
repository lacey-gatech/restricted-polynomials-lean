module

public import RestrictedPolynomials.TrackB.SwapSvd
public import RestrictedPolynomials.TrackB.SwapRestrict
public import RestrictedPolynomials.TrackB.SwapNorm
public import RestrictedPolynomials.TrackB.Restrict

/-!
# Track B: the calculus of the SVD of one function under the swap

Source: CSP6 (arXiv:2411.15133v1 `main.tex`) L444-446 and L824-831 (`thm:swapnine`),
L780-821 (`lemma:99induct`), L892-895 (`lemma:iter`, `box-schatten4`), L997-1008 (`eq:valf`).
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapSvdCalc
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the partial-swap inner product `val_T`: only the coordinates in `T` are swapped. -/
def swapValOn (T : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) : ℂ :=
  𝔼 x : ι → α, 𝔼 y : ι → α, 𝔼 b : ι → Bool,
    f₁ x * f₂ y * star (f₃ (swapL (fun i => decide (i ∈ T) && b i) x y)) *
      star (f₄ (swapR (fun i => decide (i ∈ T) && b i) x y))

/-- a `J`-SVD of `f`, as data. -/
structure SwapSvdData (J : Finset ι) (f : (ι → α) → ℂ) where
  r : ℕ
  lam : Fin r → ℝ
  g : Fin r → (↥J → α) → ℂ
  h : Fin r → (↥Jᶜ → α) → ℂ
  isJSVD : IsJSVD J f r lam g h

/-- the partial sum `∑_{i ∈ s} λᵢ gᵢ hᵢ` of the `J`-SVD over an index set `s`, on `ι → α`. -/
def SwapSvdData.truncOn {J : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData J f)
    (s : Finset (Fin d.r)) : (ι → α) → ℂ :=
  fun x => ∑ i ∈ s, (d.lam i : ℂ) * prodSplit J (d.g i) (d.h i) x

/-- the sum of the first `t` terms `∑_{i < t} λᵢ gᵢ hᵢ` of the `J`-SVD, on `ι → α`. -/
def SwapSvdData.trunc {J : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData J f) (t : ℕ) :
    (ι → α) → ℂ :=
  d.truncOn (Finset.univ.filter fun i => i.val < t)

/-- a choice of `J`-SVD for every `(J, f)`; the scheme is run for an arbitrary such choice. -/
abbrev SwapSvdChoice (ι α : Type) [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] : Type :=
  ∀ (J : Finset ι) (f : (ι → α) → ℂ), SwapSvdData J f

/-- a choice exists (`jsvd_exists`). -/
def swapSvdChoice : SwapSvdChoice ι α := fun J f =>
  let hex := jsvd_exists J f
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.choose,
    hex.choose_spec.choose_spec.choose_spec.choose,
    hex.choose_spec.choose_spec.choose_spec.choose_spec⟩


omit [DecidableEq α] in
theorem swapValOn_univ (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    swapValOn Finset.univ f₁ f₂ f₃ f₄ = val f₁ f₂ f₃ f₄ := by
  simp [swapValOn, val]

/-! ### `val ≤ val_T` -/

private abbrev maskT (T : Finset ι) (b : ι → Bool) : ι → Bool := fun i => decide (i ∈ T) && b i

private abbrev maskC (T : Finset ι) (e : ι → Bool) : ι → Bool := fun i => decide (i ∉ T) && e i

/-- the `T`-partial average `W(x,y) = 𝔼_b f(swapL (mask b)) f(swapR (mask b))` -/
private def Wpart (T : Finset ι) (f : (ι → α) → ℂ) (x y : ι → α) : ℂ :=
  𝔼 b : ι → Bool, f (swapL (maskT T b) x y) * f (swapR (maskT T b) x y)

omit [DecidableEq α] in
private lemma swapValOn_eq_Wpart (T : Finset ι) (f : (ι → α) → ℂ) :
    swapValOn T f f f f = 𝔼 x : ι → α, 𝔼 y : ι → α, f x * f y * star (Wpart T f x y) := by
  simp only [swapValOn, Wpart, star_expect]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ => ?_))
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl (fun b _ => ?_)
  simp only [star_mul']
  ring

omit [Fintype ι] in
private lemma maskT_xor (T : Finset ι) (b c : ι → Bool) :
    (fun i => xor (maskT T b i) (maskT T c i)) = maskT T (fun i => xor (b i) (c i)) := by
  funext i
  by_cases h : i ∈ T <;> simp [maskT, h]

private lemma Wpart_swap (T : Finset ι) (f : (ι → α) → ℂ) (c : ι → Bool) (x y : ι → α) :
    Wpart T f (swapL (maskT T c) x y) (swapR (maskT T c) x y) = Wpart T f x y := by
  simp only [Wpart, swapL_swapL_swapR, swapR_swapL_swapR, maskT_xor]
  exact Fintype.expect_equiv (xorE c) _ _ (fun b => rfl)

private lemma swapValOn_eq_norm_sq (T : Finset ι) (f : (ι → α) → ℂ) :
    swapValOn T f f f f = ((𝔼 x : ι → α, 𝔼 y : ι → α, ‖Wpart T f x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [swapValOn_eq_Wpart]
  have hB : ∀ c : ι → Bool, (𝔼 x : ι → α, 𝔼 y : ι → α, f x * f y * star (Wpart T f x y)) =
      𝔼 x : ι → α, 𝔼 y : ι → α,
        f (swapL (maskT T c) x y) * f (swapR (maskT T c) x y) * star (Wpart T f x y) := fun c => by
    rw [← expect_expect_swap (maskT T c) (fun x y => f x * f y * star (Wpart T f x y))]
    simp only [Wpart_swap]
  have hC : (𝔼 x : ι → α, 𝔼 y : ι → α, f x * f y * star (Wpart T f x y)) =
      𝔼 c : ι → Bool, 𝔼 x : ι → α, 𝔼 y : ι → α,
        f (swapL (maskT T c) x y) * f (swapR (maskT T c) x y) * star (Wpart T f x y) := by
    rw [Finset.expect_congr rfl (fun c _ => (hB c).symm), Fintype.expect_const]
  rw [hC, Finset.expect_comm, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [Finset.expect_comm, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun y _ => ?_)
  rw [← Finset.expect_mul, Complex.ofReal_pow, ← Complex.mul_conj']
  rfl

private lemma swapU_eq_expect_Wpart (T : Finset ι) (f : (ι → α) → ℂ) (x y : ι → α) :
    swapU f f x y =
      𝔼 e : ι → Bool, Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y) := by
  have h1 : ∀ e : ι → Bool, Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y) =
      𝔼 b : ι → Bool, (fun c : ι → Bool => f (swapL c x y) * f (swapR c x y))
        (T.piecewise b e) := by
    intro e
    simp only [Wpart, swapL_swapL_swapR, swapR_swapL_swapR]
    refine Finset.expect_congr rfl (fun b _ => ?_)
    have : (fun i => xor (maskT T b i) (maskC T e i)) = T.piecewise b e := by
      funext i
      by_cases h : i ∈ T <;> simp [maskT, maskC, h]
    rw [this]
  simp_rw [h1]
  rw [Finset.expect_comm]
  have := expect_expect_piecewise (α := Bool) T (fun c : ι → Bool => f (swapL c x y) * f (swapR c x y))
  rw [swapU]
  exact this.symm

theorem val_le_swapValOn (T : Finset ι) (f : (ι → α) → ℂ) :
    (val f f f f).re ≤ (swapValOn T f f f f).re := by
  rw [swapValOn_eq_norm_sq, val_pair_eq_expect_norm_sq, Complex.ofReal_re, Complex.ofReal_re]
  have hj : ∀ x y : ι → α, ‖swapU f f x y‖ ^ 2 ≤
      𝔼 e : ι → Bool, ‖Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y)‖ ^ 2 := by
    intro x y
    rw [swapU_eq_expect_Wpart T f x y]
    have h := norm_expect_mul_sq_le (Finset.univ : Finset (ι → Bool)) (fun _ => (1 : ℂ))
      (fun e => Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y))
    simpa using h
  calc (𝔼 x : ι → α, 𝔼 y : ι → α, ‖swapU f f x y‖ ^ 2)
      ≤ 𝔼 x : ι → α, 𝔼 y : ι → α,
        𝔼 e : ι → Bool, ‖Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y)‖ ^ 2 :=
        Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun y _ => hj x y))
    _ = 𝔼 x : ι → α, 𝔼 e : ι → Bool, 𝔼 y : ι → α,
        ‖Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y)‖ ^ 2 :=
        Finset.expect_congr rfl (fun x _ => Finset.expect_comm _ _ _)
    _ = 𝔼 e : ι → Bool, 𝔼 x : ι → α, 𝔼 y : ι → α,
        ‖Wpart T f (swapL (maskC T e) x y) (swapR (maskC T e) x y)‖ ^ 2 :=
        Finset.expect_comm _ _ _
    _ = 𝔼 e : ι → Bool, 𝔼 x : ι → α, 𝔼 y : ι → α, ‖Wpart T f x y‖ ^ 2 := by
        refine Finset.expect_congr rfl (fun e _ => ?_)
        exact expect_expect_swap (maskC T e) (fun x y => ‖Wpart T f x y‖ ^ 2)
    _ = _ := Fintype.expect_const _

/-! ### Helpers: the four-slot form with a fixed coin vector, and splitting coordinates -/

/-- the swap form with a fixed coin vector `c` -/
private def val4 (c : ι → Bool) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) : ℂ :=
  𝔼 x : ι → α, 𝔼 y : ι → α,
    f₁ x * f₂ y * star (f₃ (swapL c x y)) * star (f₄ (swapR c x y))

private lemma expect3_rotate {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (G : X → Y → Z → ℂ) :
    𝔼 x, 𝔼 y, 𝔼 z, G x y z = 𝔼 z, 𝔼 x, 𝔼 y, G x y z :=
  (Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)).trans (Finset.expect_comm _ _ _)

omit [DecidableEq α] in
private lemma swapValOn_eq_expect_val4 (T : Finset ι) (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    swapValOn T f₁ f₂ f₃ f₄ = 𝔼 b : ι → Bool, val4 (maskT T b) f₁ f₂ f₃ f₄ := by
  simp only [swapValOn, val4]
  exact expect3_rotate _

omit [DecidableEq α] in
private lemma val_eq_expect_val4 (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = 𝔼 b : ι → Bool, val4 b f₁ f₂ f₃ f₄ := by
  simp only [val, val4]
  exact expect3_rotate _

omit [DecidableEq α] in
private lemma val4_sum (c : ι → Bool) {κ : Type} (s : Finset κ) (a : κ → ℂ)
    (u : κ → (ι → α) → ℂ) :
    val4 c (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x)
        (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x) =
      ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s,
        a i * a j * star (a k) * star (a l) * val4 c (u i) (u j) (u k) (u l) := by
  have key : ∀ x y : ι → α, (∑ i ∈ s, a i * u i x) * (∑ j ∈ s, a j * u j y) *
      star (∑ k ∈ s, a k * u k (swapL c x y)) * star (∑ l ∈ s, a l * u l (swapR c x y)) =
      ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, a i * a j * star (a k) * star (a l) *
        (u i x * u j y * star (u k (swapL c x y)) * star (u l (swapR c x y))) := by
    intro x y
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [val4, key]
  simp only [Finset.expect_sum_comm, Finset.mul_expect]

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
private lemma swapL_false (x y : ι → α) : swapL (fun _ => false) x y = x := by
  funext i; simp [swapL]

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
private lemma swapR_false (x y : ι → α) : swapR (fun _ => false) x y = y := by
  funext i; simp [swapR]

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
private lemma swapL_true (x y : ι → α) : swapL (fun _ => true) x y = y := by
  funext i; simp [swapL]

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
private lemma swapR_true (x y : ι → α) : swapR (fun _ => true) x y = x := by
  funext i; simp [swapR]

private def scSplitEquiv {β : Type} (S : Finset ι) : (ι → β) ≃ (↥S → β) × (↥Sᶜ → β) where
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

private lemma sc_expect_split {β : Type} [Fintype β] {M : Type*} [AddCommMonoid M]
    [Module ℚ≥0 M] (S : Finset ι) (h : (ι → β) → M) :
    𝔼 x : ι → β, h x = 𝔼 u : ↥S → β, 𝔼 v : ↥Sᶜ → β, h (glueFree S u v) := by
  rw [← Finset.expect_product' (f := fun u v => h (glueFree S u v)), Finset.univ_product_univ]
  exact Fintype.expect_equiv (scSplitEquiv S) _ _
    (fun x => congrArg h ((scSplitEquiv S).symm_apply_apply x).symm)

omit [Fintype α] [DecidableEq α] in
private lemma sc_glue_restrS {β : Type} (S : Finset ι) (u : ↥S → β) (v : ↥Sᶜ → β) :
    (fun i : ↥S => glueFree S u v i) = u := by
  funext i; simp [glueFree, i.2]

omit [Fintype α] [DecidableEq α] in
private lemma sc_glue_restrT {β : Type} (S : Finset ι) (u : ↥S → β) (v : ↥Sᶜ → β) :
    (fun i : ↥Sᶜ => glueFree S u v i) = v := by
  funext i
  have : (i : ι) ∉ S := mem_compl.1 i.2
  simp [glueFree, this]

omit [Fintype α] [DecidableEq α] in
private lemma sc_glue_swapL (S : Finset ι) (c : ↥S → Bool) (d : ↥Sᶜ → Bool) (p q : ↥S → α)
    (u v : ↥Sᶜ → α) :
    swapL (glueFree S c d) (glueFree S p u) (glueFree S q v) =
      glueFree S (swapL c p q) (swapL d u v) := by
  funext i
  by_cases h : i ∈ S <;> simp [swapL, glueFree, h]

omit [Fintype α] [DecidableEq α] in
private lemma sc_glue_swapR (S : Finset ι) (c : ↥S → Bool) (d : ↥Sᶜ → Bool) (p q : ↥S → α)
    (u v : ↥Sᶜ → α) :
    swapR (glueFree S c d) (glueFree S p u) (glueFree S q v) =
      glueFree S (swapR c p q) (swapR d u v) := by
  funext i
  by_cases h : i ∈ S <;> simp [swapR, glueFree, h]

omit [DecidableEq α] in
private lemma sc_expect_split_two (J : Finset ι) (Φ : (ι → α) → (ι → α) → ℂ) :
    𝔼 x : ι → α, 𝔼 y : ι → α, Φ x y =
      𝔼 p : ↥J → α, 𝔼 u : ↥Jᶜ → α, 𝔼 q : ↥J → α, 𝔼 v : ↥Jᶜ → α,
        Φ (glueFree J p u) (glueFree J q v) := by
  have h1 := sc_expect_split J (fun x : ι → α => 𝔼 y : ι → α, Φ x y)
  have h2 : ∀ (p : ↥J → α) (u : ↥Jᶜ → α), (𝔼 y : ι → α, Φ (glueFree J p u) y) =
      𝔼 q : ↥J → α, 𝔼 v : ↥Jᶜ → α, Φ (glueFree J p u) (glueFree J q v) :=
    fun p u => sc_expect_split J (fun y => Φ (glueFree J p u) y)
  rw [h1]
  simp only [h2]

private lemma expect_mul_expect2 {P Q U V : Type} [Fintype P] [Fintype Q] [Fintype U] [Fintype V]
    (A : P → Q → ℂ) (B : U → V → ℂ) :
    (𝔼 p, 𝔼 q, A p q) * (𝔼 u, 𝔼 v, B u v) = 𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, A p q * B u v := by
  simp only [Finset.expect_mul, Finset.mul_expect]
  calc (𝔼 u, 𝔼 v, 𝔼 p, 𝔼 q, A p q * B u v)
      = 𝔼 u, 𝔼 p, 𝔼 v, 𝔼 q, A p q * B u v :=
        Finset.expect_congr rfl fun u _ => Finset.expect_comm _ _ _
    _ = 𝔼 p, 𝔼 u, 𝔼 v, 𝔼 q, A p q * B u v := Finset.expect_comm _ _ _
    _ = _ := Finset.expect_congr rfl fun p _ => Finset.expect_congr rfl fun u _ =>
        Finset.expect_comm _ _ _

omit [DecidableEq α] in
private lemma val4_split (J : Finset ι) (c : ↥J → Bool) (d : ↥Jᶜ → Bool)
    (g₁ g₂ g₃ g₄ : (↥J → α) → ℂ) (h₁ h₂ h₃ h₄ : (↥Jᶜ → α) → ℂ) :
    val4 (glueFree J c d) (prodSplit J g₁ h₁) (prodSplit J g₂ h₂) (prodSplit J g₃ h₃)
        (prodSplit J g₄ h₄) = val4 c g₁ g₂ g₃ g₄ * val4 d h₁ h₂ h₃ h₄ := by
  have hΦ : ∀ (p q : ↥J → α) (u v : ↥Jᶜ → α),
      prodSplit J g₁ h₁ (glueFree J p u) * prodSplit J g₂ h₂ (glueFree J q v) *
        star (prodSplit J g₃ h₃ (swapL (glueFree J c d) (glueFree J p u) (glueFree J q v))) *
        star (prodSplit J g₄ h₄ (swapR (glueFree J c d) (glueFree J p u) (glueFree J q v))) =
      (g₁ p * g₂ q * star (g₃ (swapL c p q)) * star (g₄ (swapR c p q))) *
        (h₁ u * h₂ v * star (h₃ (swapL d u v)) * star (h₄ (swapR d u v))) := by
    intro p q u v
    simp only [prodSplit, sc_glue_swapL, sc_glue_swapR, sc_glue_restrS, sc_glue_restrT,
      star_mul']
    ring
  unfold val4
  refine (sc_expect_split_two J _).trans ?_
  rw [expect_mul_expect2]
  refine Finset.expect_congr rfl (fun p _ => Finset.expect_congr rfl (fun u _ =>
    Finset.expect_congr rfl (fun q _ => Finset.expect_congr rfl (fun v _ => ?_))))
  exact hΦ p q u v

private lemma fold_sym {κ : Type} [LinearOrder κ] (s : Finset κ) (X : κ → κ → ℝ)
    (hX : ∀ i j, X i j = X j i) :
    ∑ i ∈ s, ∑ j ∈ s, X i j =
      ∑ i ∈ s, X i i + 2 * ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), X i j := by
  have h1 : ∀ i j, X i j = (if i < j then X i j else 0) + (if i = j then X i j else 0) +
      (if j < i then X i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h; simp
    · simp [h, h.ne', h.not_gt]
  have hC : ∑ i ∈ s, ∑ j ∈ s, (if j < i then X i j else 0) =
      ∑ i ∈ s, ∑ j ∈ s, (if i < j then X i j else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hX i j]
  calc ∑ i ∈ s, ∑ j ∈ s, X i j
      = ∑ i ∈ s, ∑ j ∈ s, ((if i < j then X i j else 0) + (if i = j then X i j else 0) +
          (if j < i then X i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
    _ = ∑ i ∈ s, ∑ j ∈ s, (if i < j then X i j else 0) + ∑ i ∈ s, ∑ j ∈ s, (if i = j then X i j else 0) +
          ∑ i ∈ s, ∑ j ∈ s, (if j < i then X i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by
        rw [hC]
        have hB : ∑ i ∈ s, ∑ j ∈ s, (if i = j then X i j else 0) = ∑ i ∈ s, X i i :=
          Finset.sum_congr rfl fun i hi => by simp [hi]
        rw [hB]
        simp only [Finset.sum_filter]
        ring

/-! ### The partial swap of a product of split functions -/

omit [DecidableEq α] in
private lemma val4_false (g₁ g₂ g₃ g₄ : (ι → α) → ℂ) :
    val4 (fun _ => false) g₁ g₂ g₃ g₄ =
      (𝔼 x : ι → α, g₁ x * star (g₃ x)) * 𝔼 y : ι → α, g₂ y * star (g₄ y) := by
  simp only [val4, swapL_false, swapR_false]
  rw [Finset.expect_mul_expect]
  exact Finset.expect_congr rfl fun x _ => Finset.expect_congr rfl fun y _ => by ring

private lemma expect_restrict_coins (J : Finset ι) (Ψ : (↥Jᶜ → Bool) → ℂ) :
    𝔼 b : ι → Bool, Ψ (fun i : ↥Jᶜ => b i) = 𝔼 d : ↥Jᶜ → Bool, Ψ d := by
  rw [sc_expect_split J (fun b : ι → Bool => Ψ (fun i : ↥Jᶜ => b i))]
  simp only [sc_glue_restrT]
  exact Fintype.expect_const _

omit [DecidableEq α] in
private lemma swapValOn_prodSplit (J : Finset ι) (g₁ g₂ g₃ g₄ : (↥J → α) → ℂ)
    (h₁ h₂ h₃ h₄ : (↥Jᶜ → α) → ℂ) :
    swapValOn Jᶜ (prodSplit J g₁ h₁) (prodSplit J g₂ h₂) (prodSplit J g₃ h₃) (prodSplit J g₄ h₄) =
      uinner g₁ g₃ * uinner g₂ g₄ * val h₁ h₂ h₃ h₄ := by
  have hm : ∀ b : ι → Bool, maskT Jᶜ b =
      glueFree J (fun _ => false) (fun i : ↥Jᶜ => b i) := by
    intro b; funext i
    by_cases h : i ∈ J <;> simp [maskT, glueFree, h]
  rw [swapValOn_eq_expect_val4]
  simp only [hm, val4_split, val4_false]
  rw [← Finset.mul_expect, expect_restrict_coins J (fun d => val4 d h₁ h₂ h₃ h₄),
    val_eq_expect_val4]
  rfl

omit [DecidableEq α] in
private lemma swapValOn_sum (T : Finset ι) {κ : Type} (s : Finset κ) (a : κ → ℂ)
    (u : κ → (ι → α) → ℂ) :
    swapValOn T (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x)
        (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x) =
      ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s,
        a i * a j * star (a k) * star (a l) * swapValOn T (u i) (u j) (u k) (u l) := by
  simp only [swapValOn_eq_expect_val4, val4_sum, Finset.expect_sum_comm, Finset.mul_expect]

omit [DecidableEq α] in
private lemma val_swap_xy' (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = val f₂ f₁ f₄ f₃ := by
  simp only [val]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ =>
    Finset.expect_congr rfl (fun b _ => ?_)))
  show f₁ y * f₂ x * star (f₃ (swapR b x y)) * star (f₄ (swapL b x y)) =
    f₂ x * f₁ y * star (f₄ (swapL b x y)) * star (f₃ (swapR b x y))
  ring

omit [DecidableEq α] in
theorem swapValOn_svd_expansion (J : Finset ι) {r : ℕ} (lam : Fin r → ℝ)
    (g : Fin r → (↥J → α) → ℂ) (h : Fin r → (↥Jᶜ → α) → ℂ)
    (hg : ∀ i j, uinner (g i) (g j) = if i = j then 1 else 0) (s : Finset (Fin r)) :
    (swapValOn Jᶜ (fun x => ∑ i ∈ s, (lam i : ℂ) * prodSplit J (g i) (h i) x)
        (fun x => ∑ i ∈ s, (lam i : ℂ) * prodSplit J (g i) (h i) x)
        (fun x => ∑ i ∈ s, (lam i : ℂ) * prodSplit J (g i) (h i) x)
        (fun x => ∑ i ∈ s, (lam i : ℂ) * prodSplit J (g i) (h i) x)).re =
      ∑ i ∈ s, lam i ^ 4 * (val (h i) (h i) (h i) (h i)).re +
        2 * ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j),
          lam i ^ 2 * lam j ^ 2 * (val (h i) (h j) (h i) (h j)).re := by
  rw [swapValOn_sum]
  simp only [swapValOn_prodSplit, hg]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  have hc : ∀ l ∈ s, ∀ k ∈ s, (∑ j ∈ s, ∑ i ∈ s, if j = l then
      (if i = k then (lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
        val (h i) (h j) (h k) (h l) else 0) else 0) =
      ((lam k ^ 2 * lam l ^ 2 : ℝ) : ℂ) * val (h k) (h l) (h k) (h l) := by
    intro l hl k hk
    simp [hk, hl]
    left
    ring
  have key : (∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, if j = l then
      (if i = k then (lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
        val (h i) (h j) (h k) (h l) else 0) else 0) =
      ∑ l ∈ s, ∑ k ∈ s, ((lam k ^ 2 * lam l ^ 2 : ℝ) : ℂ) * val (h k) (h l) (h k) (h l) :=
    Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun k hk => hc l hl k hk
  rw [key]
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have hsym : ∀ k l : Fin r, (val (h k) (h l) (h k) (h l)).re = (val (h l) (h k) (h l) (h k)).re :=
    fun k l => by rw [val_swap_xy' (h k) (h l) (h k) (h l)]
  rw [fold_sym s (fun l k => lam k ^ 2 * lam l ^ 2 * (val (h k) (h l) (h k) (h l)).re)
    (fun i j => by simp only [hsym j i]; ring)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => by ring
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring

/-! ### The full swap on a single coordinate, and the singleton expansion -/

omit [DecidableEq α] in
private lemma val4_true (g₁ g₂ g₃ g₄ : (ι → α) → ℂ) :
    val4 (fun _ => true) g₁ g₂ g₃ g₄ =
      (𝔼 x : ι → α, g₁ x * star (g₄ x)) * 𝔼 y : ι → α, g₂ y * star (g₃ y) := by
  simp only [val4, swapL_true, swapR_true]
  rw [Finset.expect_mul_expect]
  exact Finset.expect_congr rfl fun x _ => Finset.expect_congr rfl fun y _ => by ring

omit [DecidableEq α] in
private lemma val_one_coord {ι' : Type} [Fintype ι'] [DecidableEq ι'] [Unique ι']
    (g₁ g₂ g₃ g₄ : (ι' → α) → ℂ) :
    val g₁ g₂ g₃ g₄ = (1 / 2 : ℂ) * (uinner g₁ g₃ * uinner g₂ g₄ + uinner g₁ g₄ * uinner g₂ g₃) := by
  rw [val_eq_expect_val4]
  have h1 : (𝔼 b : ι' → Bool, val4 b g₁ g₂ g₃ g₄) =
      𝔼 t : Bool, val4 (fun _ => t) g₁ g₂ g₃ g₄ :=
    Fintype.expect_equiv (Equiv.funUnique ι' Bool) _ _ (fun b => by
      have : b = fun _ => b default := funext fun i => by rw [Subsingleton.elim i default]
      conv_lhs => rw [this]
      rfl)
  rw [h1, Fintype.expect_eq_sum_div_card, Fintype.sum_bool, val4_true, val4_false]
  simp only [uinner, Fintype.card_bool]
  push_cast
  ring

omit [DecidableEq α] in
private lemma jsvd_apply {J : Finset ι} {f : (ι → α) → ℂ} {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥J → α) → ℂ} {h : Fin r → (↥Jᶜ → α) → ℂ} (hsvd : IsJSVD J f r lam g h) :
    f = fun x => ∑ i, (lam i : ℂ) * prodSplit J (g i) (h i) x := by
  funext x
  have hx : glueFree J (fun i : ↥J => x i) (fun i : ↥Jᶜ => x i) = x := by
    funext i; by_cases hi : i ∈ J <;> simp [glueFree, hi]
  have := hsvd.decomp (fun i : ↥J => x i) (fun i : ↥Jᶜ => x i)
  simp only [jMatrix, hx] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by simp only [prodSplit]; ring

omit [DecidableEq α] in
private lemma val_sum {κ : Type} (s : Finset κ) (a : κ → ℂ) (u : κ → (ι → α) → ℂ) :
    val (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x)
        (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x) =
      ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s,
        a i * a j * star (a k) * star (a l) * val (u i) (u j) (u k) (u l) := by
  simp only [val_eq_expect_val4, val4_sum, Finset.expect_sum_comm, Finset.mul_expect]

omit [DecidableEq α] in
private lemma val_swap_34' (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = val f₁ f₂ f₄ f₃ := by
  simp only [val]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ => ?_))
  let e : (ι → Bool) ≃ (ι → Bool) :=
    Equiv.piCongrRight fun _ => (⟨not, not, Bool.not_not, Bool.not_not⟩ : Bool ≃ Bool)
  refine Fintype.expect_equiv e _ _ (fun b => ?_)
  show _ = f₁ x * f₂ y * star (f₄ (swapL (fun i => !b i) x y)) *
    star (f₃ (swapR (fun i => !b i) x y))
  have h1 : swapL (fun i => !b i) x y = swapR b x y := by
    funext i; cases h : b i <;> simp [swapL, swapR, h]
  have h2 : swapR (fun i => !b i) x y = swapL b x y := by
    funext i; cases h : b i <;> simp [swapL, swapR, h]
  rw [h1, h2]
  ring

omit [Fintype ι] [DecidableEq ι] in
private lemma unique_singleton (j : ι) : Nonempty (Unique ↥({j} : Finset ι)) :=
  ⟨⟨⟨⟨j, by simp⟩⟩, fun a => Subtype.ext (Finset.mem_singleton.1 a.2)⟩⟩

private lemma collA {r : ℕ} (F : Fin r → Fin r → Fin r → Fin r → ℂ) :
    ∑ l, ∑ k, ∑ j, ∑ i, ((if i = k then (1 : ℂ) else 0) * (if j = l then 1 else 0)) * F i j k l =
      ∑ l, ∑ k, F k l k l := by
  simp

private lemma collB {r : ℕ} (F : Fin r → Fin r → Fin r → Fin r → ℂ) :
    ∑ l, ∑ k, ∑ j, ∑ i, ((if i = l then (1 : ℂ) else 0) * (if j = k then 1 else 0)) * F i j k l =
      ∑ l, ∑ k, F l k k l := by
  simp

omit [DecidableEq α] in
private lemma val_singleton_full (j : ι) (f : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥({j} : Finset ι) → α) → ℂ} {h : Fin r → (↥({j} : Finset ι)ᶜ → α) → ℂ}
    (hsvd : IsJSVD ({j} : Finset ι) f r lam g h) :
    (val f f f f).re =
      ∑ l, ∑ k, lam k ^ 2 * lam l ^ 2 * (val (h k) (h l) (h k) (h l)).re := by
  have : Unique ↥({j} : Finset ι) := (unique_singleton j).some
  have hg := hsvd.orth_g
  rw [jsvd_apply hsvd, val_sum]
  simp only [val_prodSplit, val_one_coord, hg]
  have hterm : ∀ (i j k l : Fin r),
      (lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
        (1 / 2 * (((if i = k then (1 : ℂ) else 0) * if j = l then 1 else 0) +
          (if i = l then 1 else 0) * if j = k then 1 else 0) * val (h i) (h j) (h k) (h l)) =
      (1 / 2 : ℂ) * (((if i = k then (1 : ℂ) else 0) * (if j = l then 1 else 0)) *
        ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
          val (h i) (h j) (h k) (h l))) +
      (1 / 2 : ℂ) * (((if i = l then (1 : ℂ) else 0) * (if j = k then 1 else 0)) *
        ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
          val (h i) (h j) (h k) (h l))) := fun i j k l => by ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [collA (fun i j k l => (lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
          val (h i) (h j) (h k) (h l)),
      collB (fun i j k l => (lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
          val (h i) (h j) (h k) (h l))]
  have hS : ∀ l k : Fin r, (lam l : ℂ) * (lam k : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
      val (h l) (h k) (h k) (h l) =
      ((lam k ^ 2 * lam l ^ 2 : ℝ) : ℂ) * val (h k) (h l) (h k) (h l) := by
    intro l k
    rw [val_swap_34' (h l) (h k) (h k) (h l), val_swap_xy' (h l) (h k) (h l) (h k)]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have hS' : ∀ l k : Fin r, (lam k : ℂ) * (lam l : ℂ) * star (lam k : ℂ) * star (lam l : ℂ) *
      val (h k) (h l) (h k) (h l) =
      ((lam k ^ 2 * lam l ^ 2 : ℝ) : ℂ) * val (h k) (h l) (h k) (h l) := by
    intro l k
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hS, hS']
  have h2 : ∀ X : ℂ, 1 / 2 * X + 1 / 2 * X = X := fun X => by ring
  rw [h2]
  simp only [Complex.re_sum, Complex.re_ofReal_mul]

omit [DecidableEq α] in
theorem val_svd_expansion_singleton (j : ι) (f : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥({j} : Finset ι) → α) → ℂ} {h : Fin r → (↥({j} : Finset ι)ᶜ → α) → ℂ}
    (hsvd : IsJSVD ({j} : Finset ι) f r lam g h) :
    (val f f f f).re =
      ∑ i, lam i ^ 4 * (val (h i) (h i) (h i) (h i)).re +
        2 * ∑ i, ∑ k ∈ Finset.Ioi i,
          lam i ^ 2 * lam k ^ 2 * (val (h i) (h k) (h i) (h k)).re := by
  have hsym : ∀ k l : Fin r, (val (h k) (h l) (h k) (h l)).re = (val (h l) (h k) (h l) (h k)).re :=
    fun k l => by rw [val_swap_xy' (h k) (h l) (h k) (h l)]
  rw [val_singleton_full j f hsvd,
    fold_sym Finset.univ (fun l k => lam k ^ 2 * lam l ^ 2 * (val (h k) (h l) (h k) (h l)).re)
      (fun i j => by simp only [hsym j i]; ring)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Finset.univ.filter (fun k : Fin r => i < k) = Finset.Ioi i := by
      ext k; simp
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym k i]; ring

/-! ### The box identity -/

private lemma expect4_reverse {P U Q V : Type} [Fintype P] [Fintype U] [Fintype Q] [Fintype V]
    (F : P → U → Q → V → ℂ) :
    𝔼 v, 𝔼 q, 𝔼 u, 𝔼 p, F p u q v = 𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, F p u q v := by
  calc 𝔼 v, 𝔼 q, 𝔼 u, 𝔼 p, F p u q v
      = 𝔼 v, 𝔼 q, 𝔼 p, 𝔼 u, F p u q v :=
        Finset.expect_congr rfl fun v _ => Finset.expect_congr rfl fun q _ => Finset.expect_comm _ _ _
    _ = 𝔼 v, 𝔼 p, 𝔼 q, 𝔼 u, F p u q v :=
        Finset.expect_congr rfl fun v _ => Finset.expect_comm _ _ _
    _ = 𝔼 v, 𝔼 p, 𝔼 u, 𝔼 q, F p u q v :=
        Finset.expect_congr rfl fun v _ => Finset.expect_congr rfl fun p _ => Finset.expect_comm _ _ _
    _ = 𝔼 p, 𝔼 v, 𝔼 u, 𝔼 q, F p u q v := Finset.expect_comm _ _ _
    _ = 𝔼 p, 𝔼 u, 𝔼 v, 𝔼 q, F p u q v :=
        Finset.expect_congr rfl fun p _ => Finset.expect_comm _ _ _
    _ = 𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, F p u q v :=
        Finset.expect_congr rfl fun p _ => Finset.expect_congr rfl fun u _ => Finset.expect_comm _ _ _

private lemma expect4_prod {P U Q V : Type} [Fintype P] [Fintype U] [Fintype Q] [Fintype V]
    (A : P → ℂ) (B : U → ℂ) (C : Q → ℂ) (D : V → ℂ) :
    𝔼 p, 𝔼 u, 𝔼 q, 𝔼 v, A p * B u * C q * D v = (𝔼 p, A p) * (𝔼 u, B u) * (𝔼 q, C q) * 𝔼 v, D v := by
  simp only [Finset.expect_mul, Finset.mul_expect]
  exact (expect4_reverse (fun p u q v => A p * B u * C q * D v)).symm

omit [Fintype α] [DecidableEq α] in
private lemma piecewise_glue_left (S : Finset ι) (q : ↥S → α) (u : ↥Sᶜ → α) (p : ↥S → α)
    (v : ↥Sᶜ → α) :
    S.piecewise (glueFree S q v) (glueFree S p u) = glueFree S q u := by
  funext i; by_cases hi : i ∈ S <;> simp [glueFree, hi]

omit [Fintype α] [DecidableEq α] in
private lemma piecewise_glue_right (S : Finset ι) (p : ↥S → α) (v : ↥Sᶜ → α) (q : ↥S → α)
    (u : ↥Sᶜ → α) :
    S.piecewise (glueFree S p u) (glueFree S q v) = glueFree S p v := by
  funext i; by_cases hi : i ∈ S <;> simp [glueFree, hi]

private lemma collC {r : ℕ} (F : Fin r → Fin r → Fin r → Fin r → ℂ) :
    ∑ l, ∑ k, ∑ j, ∑ i, ((if i = l then (1 : ℂ) else 0) * (if i = k then 1 else 0) *
      (if j = k then 1 else 0) * (if j = l then 1 else 0)) * F i j k l = ∑ i, F i i i i := by
  simp

omit [DecidableEq α] in
theorem box_svd_eq_sum_pow4 (S : Finset ι) (f : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥S → α) → ℂ} {h : Fin r → (↥Sᶜ → α) → ℂ}
    (hsvd : IsJSVD S f r lam g h) :
    box S f f f f = ((∑ i, lam i ^ 4 : ℝ) : ℂ) := by
  have hf : ∀ p u, f (glueFree S p u) = ∑ i, (lam i : ℂ) * g i p * h i u :=
    fun p u => hsvd.decomp p u
  have key : ∀ (p q : ↥S → α) (u v : ↥Sᶜ → α),
      (∑ i, (lam i : ℂ) * g i p * h i u) * (∑ j, (lam j : ℂ) * g j q * h j v) *
        star (∑ k, (lam k : ℂ) * g k q * h k u) * star (∑ l, (lam l : ℂ) * g l p * h l v) =
      ∑ l, ∑ k, ∑ j, ∑ i, ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ)) *
        ((g i p * star (g l p)) * (h i u * star (h k u)) * (g j q * star (g k q)) *
          (h j v * star (h l v))) := by
    intro p q u v
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold box
  rw [sc_expect_split_two S]
  simp only [piecewise_glue_left, hf, key]
  simp only [Finset.expect_sum_comm]
  have hterm : ∀ l k j i : Fin r,
      (𝔼 p : ↥S → α, 𝔼 u : ↥Sᶜ → α, 𝔼 q : ↥S → α, 𝔼 v : ↥Sᶜ → α,
        ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ)) *
        ((g i p * star (g l p)) * (h i u * star (h k u)) * (g j q * star (g k q)) *
          (h j v * star (h l v)))) =
      ((if i = l then (1 : ℂ) else 0) * (if i = k then 1 else 0) *
        (if j = k then 1 else 0) * (if j = l then 1 else 0)) *
        ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ)) := by
    intro l k j i
    have e1 : (𝔼 p : ↥S → α, g i p * star (g l p)) = if i = l then 1 else 0 := hsvd.orth_g i l
    have e2 : (𝔼 u : ↥Sᶜ → α, h i u * star (h k u)) = if i = k then 1 else 0 := hsvd.orth_h i k
    have e3 : (𝔼 q : ↥S → α, g j q * star (g k q)) = if j = k then 1 else 0 := hsvd.orth_g j k
    have e4 : (𝔼 v : ↥Sᶜ → α, h j v * star (h l v)) = if j = l then 1 else 0 := hsvd.orth_h j l
    have hx : (𝔼 p : ↥S → α, 𝔼 u : ↥Sᶜ → α, 𝔼 q : ↥S → α, 𝔼 v : ↥Sᶜ → α,
        ((g i p * star (g l p)) * (h i u * star (h k u)) * (g j q * star (g k q)) *
          (h j v * star (h l v)))) =
        (if i = l then 1 else 0) * (if i = k then 1 else 0) * (if j = k then 1 else 0) *
          (if j = l then 1 else 0) := by
      rw [expect4_prod (fun p => g i p * star (g l p)) (fun u => h i u * star (h k u))
        (fun q => g j q * star (g k q)) (fun v => h j v * star (h l v)), e1, e2, e3, e4]
    calc (𝔼 p : ↥S → α, 𝔼 u : ↥Sᶜ → α, 𝔼 q : ↥S → α, 𝔼 v : ↥Sᶜ → α,
        ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ)) *
        ((g i p * star (g l p)) * (h i u * star (h k u)) * (g j q * star (g k q)) *
          (h j v * star (h l v))))
        = ((lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ)) *
          (𝔼 p : ↥S → α, 𝔼 u : ↥Sᶜ → α, 𝔼 q : ↥S → α, 𝔼 v : ↥Sᶜ → α,
        ((g i p * star (g l p)) * (h i u * star (h k u)) * (g j q * star (g k q)) *
          (h j v * star (h l v)))) := by simp only [Finset.mul_expect]
      _ = _ := by rw [hx]; ring
  simp only [hterm]
  rw [collC (fun i j k l => (lam i : ℂ) * (lam j : ℂ) * star (lam k : ℂ) * star (lam l : ℂ))]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem box_svd_pow4_le_top (S : Finset ι) (f : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥S → α) → ℂ} {h : Fin r → (↥Sᶜ → α) → ℂ}
    (hsvd : IsJSVD S f r lam g h) (hr : 0 < r) (hf : l2sq f = 1) :
    ∑ i, lam i ^ 4 ≤ lam ⟨0, hr⟩ ^ 2 := by
  have hsum : ∑ i, lam i ^ 2 = 1 := by
    rw [hsvd.sum_sq_lam, matL2sq_jMatrix, hf]
  calc ∑ i, lam i ^ 4 ≤ ∑ i, lam ⟨0, hr⟩ ^ 2 * lam i ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h0 : lam i ≤ lam ⟨0, hr⟩ := hsvd.antitone (Nat.zero_le _ : (⟨0, hr⟩ : Fin r) ≤ i)
        have hp := hsvd.pos i
        have : lam i ^ 2 ≤ lam ⟨0, hr⟩ ^ 2 := pow_le_pow_left₀ hp.le h0 2
        nlinarith [sq_nonneg (lam i)]
    _ = lam ⟨0, hr⟩ ^ 2 := by rw [← Finset.mul_sum, hsum, mul_one]

/-! ### `lemma:99induct` -/

private lemma sum_pair {r : ℕ} (s : Finset (Fin r)) (a : Fin r → ℝ) :
    ∑ l ∈ s, ∑ k ∈ s, ((2 / 3) * (a k * a l) + (if k = l then (1 / 3) * (a k * a k) else 0)) =
      (2 / 3) * (∑ i ∈ s, a i) ^ 2 + (1 / 3) * ∑ i ∈ s, a i ^ 2 := by
  have h1 : ∑ l ∈ s, ∑ k ∈ s, a k * a l = (∑ i ∈ s, a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_comm]
  have h2 : ∑ l ∈ s, ∑ k ∈ s, (if k = l then (1 / 3) * (a k * a k) else 0) =
      (1 / 3) * ∑ i ∈ s, a i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_ite_eq']
    simp [hl, sq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2]

private lemma sum_bound_full {r : ℕ} (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (w : Fin r → Fin r → ℝ)
    (hoff : ∀ k l, k ≠ l → w k l ≤ 2 / 3) (hdiag : ∀ k, w k k ≤ 1) :
    ∑ l, ∑ k, a k * a l * w k l ≤ (2 / 3) * (∑ i, a i) ^ 2 + (1 / 3) * ∑ i, a i ^ 2 := by
  have pt : ∀ k l, a k * a l * w k l ≤
      (2 / 3) * (a k * a l) + (if k = l then (1 / 3) * (a k * a k) else 0) := by
    intro k l
    by_cases h : k = l
    · subst h
      have := mul_nonneg (ha k) (ha k)
      simp only [ite_true]
      nlinarith [hdiag k]
    · simp only [h, ite_false, add_zero]
      have := mul_nonneg (ha k) (ha l)
      nlinarith [hoff k l h]
  calc ∑ l, ∑ k, a k * a l * w k l
      ≤ ∑ l, ∑ k, ((2 / 3) * (a k * a l) + (if k = l then (1 / 3) * (a k * a k) else 0)) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => pt k l
    _ = (2 / 3) * (∑ i, a i) ^ 2 + (1 / 3) * ∑ i, a i ^ 2 := sum_pair _ a

private lemma sum_bound {r : ℕ} (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (w : Fin r → Fin r → ℝ)
    (hoff : ∀ k l, k ≠ l → w k l ≤ 2 / 3) (hdiag : ∀ k, w k k ≤ 1) (i₀ : Fin r) :
    ∑ l, ∑ k, a k * a l * w k l ≤
      a i₀ ^ 2 * w i₀ i₀ + (4 / 3) * a i₀ * (∑ i ∈ Finset.univ.erase i₀, a i) +
        (2 / 3) * (∑ i ∈ Finset.univ.erase i₀, a i) ^ 2 +
        (1 / 3) * ∑ i ∈ Finset.univ.erase i₀, a i ^ 2 := by
  set R := (Finset.univ : Finset (Fin r)).erase i₀ with hR
  have hmem : ∀ k ∈ R, k ≠ i₀ := fun k hk => Finset.ne_of_mem_erase hk
  have e1 : ∑ l, ∑ k, a k * a l * w k l =
      (a i₀ * a i₀ * w i₀ i₀ + ∑ k ∈ R, a k * a i₀ * w k i₀) +
        ∑ l ∈ R, (a i₀ * a l * w i₀ l + ∑ k ∈ R, a k * a l * w k l) := by
    have h1 : ∀ l : Fin r, ∑ k, a k * a l * w k l =
        a i₀ * a l * w i₀ l + ∑ k ∈ R, a k * a l * w k l := fun l =>
      (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    simp only [h1]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have b2 : ∑ k ∈ R, a k * a i₀ * w k i₀ ≤ ∑ k ∈ R, (2 / 3) * a i₀ * a k := by
    refine Finset.sum_le_sum fun k hk => ?_
    have := mul_nonneg (ha k) (ha i₀)
    nlinarith [hoff k i₀ (hmem k hk)]
  have b3 : ∑ l ∈ R, a i₀ * a l * w i₀ l ≤ ∑ l ∈ R, (2 / 3) * a i₀ * a l := by
    refine Finset.sum_le_sum fun l hl => ?_
    have := mul_nonneg (ha i₀) (ha l)
    nlinarith [hoff i₀ l (hmem l hl).symm]
  have pt : ∀ k l, a k * a l * w k l ≤
      (2 / 3) * (a k * a l) + (if k = l then (1 / 3) * (a k * a k) else 0) := by
    intro k l
    by_cases h : k = l
    · subst h
      have := mul_nonneg (ha k) (ha k)
      simp only [ite_true]
      nlinarith [hdiag k]
    · simp only [h, ite_false, add_zero]
      have := mul_nonneg (ha k) (ha l)
      nlinarith [hoff k l h]
  have b4 : ∑ l ∈ R, ∑ k ∈ R, a k * a l * w k l ≤
      (2 / 3) * (∑ i ∈ R, a i) ^ 2 + (1 / 3) * ∑ i ∈ R, a i ^ 2 := by
    calc ∑ l ∈ R, ∑ k ∈ R, a k * a l * w k l
        ≤ ∑ l ∈ R, ∑ k ∈ R, ((2 / 3) * (a k * a l) + (if k = l then (1 / 3) * (a k * a k) else 0)) :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => pt k l
      _ = (2 / 3) * (∑ i ∈ R, a i) ^ 2 + (1 / 3) * ∑ i ∈ R, a i ^ 2 := sum_pair _ a
  rw [e1, Finset.sum_add_distrib]
  have c1 : ∑ k ∈ R, (2 / 3) * a i₀ * a k = (2 / 3) * a i₀ * ∑ k ∈ R, a k := by
    rw [Finset.mul_sum]
  have c2 : ∑ l ∈ R, (2 / 3) * a i₀ * a l = (2 / 3) * a i₀ * ∑ k ∈ R, a k := by
    rw [Finset.mul_sum]
  nlinarith [b2, b3, b4, c1, c2]

private lemma aux_ineq (ε a v s Q : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 20) (ha1 : 1 - 3 * ε ≤ a)
    (ha : a ≤ 1) (hs0 : 0 ≤ s) (hsa : a + s ≤ 1) (_hQ0 : 0 ≤ Q) (hQ : Q ≤ s ^ 2)
    (hmain : 1 - ε ≤ a ^ 2 * v + (4 / 3) * a * s + (2 / 3) * s ^ 2 + (1 / 3) * Q) :
    (1 - ε) * (1 + (1 / 4) * (1 - a)) ≤ v := by
  have hδ0 : 0 ≤ 1 - a := by linarith
  have hδ : 1 - a ≤ 3 * ε := by linarith
  have hsd : s ≤ 1 - a := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : a ^ 2 * v ≥ 1 - ε - (4 / 3) * a * (1 - a) - (1 - a) ^ 2 := by
    have : s ^ 2 ≤ (1 - a) ^ 2 := pow_le_pow_left₀ hs0 hsd 2
    have : a * s ≤ a * (1 - a) := mul_le_mul_of_nonneg_left hsd ha0.le
    nlinarith
  have h2 : (1 - ε) * (1 + (1 / 4) * (1 - a)) * a ^ 2 ≤
      1 - ε - (4 / 3) * a * (1 - a) - (1 - a) ^ 2 := by
    set d := 1 - a with hd
    have had : a = 1 - d := by rw [hd]; ring
    rw [had]
    have hu : 19 / 20 ≤ 1 - ε := by linarith
    have hd15 : d ≤ 3 / 20 := by linarith
    have hP : (4 / 3 : ℝ) ≤ (1 - ε) * (7 / 4 - d / 2 - d ^ 2 / 4) := by
      have : (1 : ℝ) + 2 / 3 ≤ 7 / 4 - d / 2 - d ^ 2 / 4 := by nlinarith
      nlinarith
    have hq : d * (4 / 3) ≤ d * ((1 - ε) * (7 / 4 - d / 2 - d ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_left hP hδ0
    nlinarith [hq, mul_nonneg hδ0 hδ0, mul_nonneg (mul_nonneg hδ0 hδ0) hδ0]
  have ha2 : 0 < a ^ 2 := by positivity
  by_contra hcon
  rw [not_le] at hcon
  have := mul_lt_mul_of_pos_right hcon ha2
  linarith


omit [DecidableEq α] in
private lemma l2sq_eq_one_of_uinner {ι' : Type} [Fintype ι'] [DecidableEq ι'] (u : (ι' → α) → ℂ)
    (hu : uinner u u = 1) : l2sq u = 1 := by
  have : ((l2sq u : ℝ) : ℂ) = 1 := by
    rw [← hu]
    simp only [l2sq, Complex.ofReal_expect, uinner]
    refine Finset.expect_congr rfl fun t _ => ?_
    rw [Complex.ofReal_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  exact_mod_cast this

private lemma val_re_le_of_l2sq {ι' : Type} [Fintype ι'] [DecidableEq ι'] (u : (ι' → α) → ℂ)
    (hu : l2sq u = 1) : (val u u u u).re ≤ 1 := by
  have := norm_val_le u u u u
  rw [hu] at this
  simp only [Real.sqrt_one, mul_one] at this
  exact (Complex.re_le_norm _).trans this

theorem swap99induct (j : ι) (f : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥({j} : Finset ι) → α) → ℂ} {h : Fin r → (↥({j} : Finset ι)ᶜ → α) → ℂ}
    (hsvd : IsJSVD ({j} : Finset ι) f r lam g h) (hr : 0 < r) {ε : ℝ} (hε : ε ≤ 1 / 20)
    (hf : l2sq f ≤ 1) (hv : (val f f f f).re = 1 - ε) :
    1 - 3 * ε ≤ lam ⟨0, hr⟩ ^ 2 ∧
      (1 - ε) * (1 + (1 / 4) * (1 - lam ⟨0, hr⟩ ^ 2)) ≤
        (val (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩)).re := by
  have hE : 1 - ε = ∑ l, ∑ k, (lam k ^ 2) * (lam l ^ 2) * (val (h k) (h l) (h k) (h l)).re := by
    rw [← hv, val_singleton_full j f hsvd]
  have hn : ∀ i, l2sq (h i) = 1 := fun i =>
    l2sq_eq_one_of_uinner _ (by rw [hsvd.orth_h]; simp)
  have hoff : ∀ k l : Fin r, k ≠ l → (val (h k) (h l) (h k) (h l)).re ≤ 2 / 3 := by
    intro k l hkl
    refine val_orthonormal_le (h k) (h l) ?_ (hn k) (hn l)
    have := hsvd.orth_h k l
    simpa [uinner, hkl] using this
  have hdiag : ∀ k : Fin r, (val (h k) (h k) (h k) (h k)).re ≤ 1 := fun k =>
    val_re_le_of_l2sq _ (hn k)
  have hsum : ∑ i, lam i ^ 2 = l2sq f := by rw [hsvd.sum_sq_lam, matL2sq_jMatrix]
  have ha0 : ∀ i, 0 ≤ lam i ^ 2 := fun i => sq_nonneg _
  have hfull := sum_bound_full (fun i => lam i ^ 2) ha0 (fun k l => (val (h k) (h l) (h k) (h l)).re)
    hoff hdiag
  try simp only at hfull
  rw [← hE] at hfull
  set σ := ∑ i, lam i ^ 2 with hσ
  have hσ1 : σ ≤ 1 := by rw [hsum]; exact hf
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun i _ => ha0 i
  have hle0 : ∀ i, lam i ^ 2 ≤ lam ⟨0, hr⟩ ^ 2 := fun i =>
    pow_le_pow_left₀ (hsvd.pos i).le (hsvd.antitone (Nat.zero_le _ : (⟨0, hr⟩ : Fin r) ≤ i)) 2
  have hQ : ∑ i, (lam i ^ 2) ^ 2 ≤ lam ⟨0, hr⟩ ^ 2 * σ := by
    rw [hσ, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := hle0 i
      nlinarith [ha0 i]
  have hQ1 : ∑ i, (lam i ^ 2) ^ 2 ≤ 1 := by
    have : lam ⟨0, hr⟩ ^ 2 ≤ σ := Finset.single_le_sum (f := fun i => lam i ^ 2)
      (fun i _ => ha0 i) (Finset.mem_univ _)
    nlinarith [ha0 ⟨0, hr⟩]
  have hε0 : 0 ≤ ε := by nlinarith
  have hb1 : 1 - 3 * ε ≤ lam ⟨0, hr⟩ ^ 2 := by nlinarith [ha0 ⟨0, hr⟩]
  refine ⟨hb1, ?_⟩
  have hb := sum_bound (fun i => lam i ^ 2) ha0 (fun k l => (val (h k) (h l) (h k) (h l)).re)
    hoff hdiag ⟨0, hr⟩
  try simp only at hb
  rw [← hE] at hb
  set s := ∑ i ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), lam i ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => ha0 i
  have hsa : lam ⟨0, hr⟩ ^ 2 + s ≤ 1 := by
    have := Finset.add_sum_erase Finset.univ (fun i => lam i ^ 2) (Finset.mem_univ (⟨0, hr⟩ : Fin r))
    try simp only at this
    linarith
  have hQ'0 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), (lam i ^ 2) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ' : ∑ i ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), (lam i ^ 2) ^ 2 ≤ s ^ 2 := by
    rw [sq, hs, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have : lam i ^ 2 ≤ s := Finset.single_le_sum (f := fun i => lam i ^ 2)
      (fun i _ => ha0 i) hi
    nlinarith [ha0 i]
  exact aux_ineq ε (lam ⟨0, hr⟩ ^ 2) _ s _ hε0 (by linarith) hb1 (by linarith) hs0 hsa hQ'0 hQ' hb

/-! ### `thm:swapnine` -/

private lemma aux9 (c ε c' x : ℝ) (hεc : ε ≤ c) (hc : c ≤ 1 / 20) (_hε0 : 0 ≤ ε) (hx : 0 < x)
    (hA : 1 - 3 * ε ≤ x ^ 2) (hA1 : x ^ 2 ≤ 1) (hc'nn : 0 ≤ c')
    (hc' : c' ≤ ε - (1 / 4) * (1 - x ^ 2) * (1 - ε)) (hc'0 : c' ≤ 1 / 20) :
    1 - 3 * c ≤ x * (1 - 3 * c') := by
  have hx1 : x ≤ 1 := by nlinarith
  have hd0 : 0 ≤ 1 - x ^ 2 := by linarith
  have hd1 : 1 - x ^ 2 ≤ 3 * ε := by linarith
  have hlow : 1 - (3 / 5) * (1 - x ^ 2) ≤ x := by
    by_contra hcon
    rw [not_le] at hcon
    have hp : 0 < 1 - (3 / 5) * (1 - x ^ 2) := by nlinarith
    have : x ^ 2 < (1 - (3 / 5) * (1 - x ^ 2)) ^ 2 := by nlinarith
    nlinarith
  have h13 : 0 ≤ 1 - 3 * c' := by linarith
  have h1 := mul_le_mul_of_nonneg_right hlow h13
  have h2 : (1 / 4) * (1 - x ^ 2) * (1 - ε) ≥ (19 / 80) * (1 - x ^ 2) := by
    nlinarith [mul_nonneg hd0 (by linarith : (0:ℝ) ≤ 1 - ε - 19 / 20)]
  nlinarith [mul_nonneg hd0 hc'nn]


private lemma prod_split_coord (j : ι) {M : Type*} [CommMonoid M] (F : ι → M) :
    ∏ i, F i = F j * ∏ i : ↥(({j} : Finset ι)ᶜ), F i := by
  rw [Finset.prod_coe_sort (({j} : Finset ι)ᶜ) F, Finset.compl_singleton,
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)]

private lemma swapNine_base (hι : IsEmpty ι) (f : (ι → α) → ℂ) (c : ℝ) (hf : l2sq f ≤ 1)
    (hv : 1 - c ≤ (val f f f f).re) :
    ∃ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 = 1) ∧
      1 - 3 * c ≤ ‖𝔼 x : ι → α, f x * star (∏ i, P i (x i))‖ := by
  refine ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, ?_⟩
  have hU : Unique (ι → α) := Pi.uniqueOfIsEmpty _
  have hL : l2sq f = ‖f default‖ ^ 2 := by
    simp [l2sq, Finset.expect_eq_sum_div_card]
  have hval := norm_val_le f f f f
  have hre : (val f f f f).re ≤ l2sq f ^ 2 := by
    refine (Complex.re_le_norm _).trans (hval.trans ?_)
    have h0 := l2sq_nonneg f
    have : Real.sqrt (l2sq f) * Real.sqrt (l2sq f) = l2sq f := Real.mul_self_sqrt h0
    refine le_of_eq ?_
    calc _ = (Real.sqrt (l2sq f) * Real.sqrt (l2sq f)) * (Real.sqrt (l2sq f) * Real.sqrt (l2sq f)) := by ring
      _ = l2sq f ^ 2 := by rw [this]; ring
  have hE : (𝔼 x : ι → α, f x * star (∏ i, (fun i => (isEmptyElim i : α → ℂ)) i (x i))) = f default := by
    simp [Finset.expect_eq_sum_div_card]
  rw [hE]
  have h0 := l2sq_nonneg f
  have hn0 : 0 ≤ ‖f default‖ := norm_nonneg _
  rw [hL] at hf hre
  nlinarith [sq_nonneg (‖f default‖ - 1), sq_nonneg (‖f default‖ ^ 2 - 1)]

private lemma val_re_le_l2sq_sq {ι' : Type} [Fintype ι'] [DecidableEq ι'] (u : (ι' → α) → ℂ) :
    (val u u u u).re ≤ l2sq u ^ 2 := by
  have hval := norm_val_le u u u u
  refine (Complex.re_le_norm _).trans (hval.trans ?_)
  have h0 := l2sq_nonneg u
  have : Real.sqrt (l2sq u) * Real.sqrt (l2sq u) = l2sq u := Real.mul_self_sqrt h0
  refine le_of_eq ?_
  calc _ = (Real.sqrt (l2sq u) * Real.sqrt (l2sq u)) * (Real.sqrt (l2sq u) * Real.sqrt (l2sq u)) := by
        ring
    _ = l2sq u ^ 2 := by rw [this]; ring

private lemma swapNine_step (j : ι) (f : (ι → α) → ℂ) (c : ℝ) (hc : c ≤ 1 / 20)
    (hf : l2sq f ≤ 1) (hv : 1 - c ≤ (val f f f f).re)
    (ih : ∀ (f' : (↥(({j} : Finset ι)ᶜ) → α) → ℂ) (c' : ℝ), c' ≤ 1 / 20 → l2sq f' ≤ 1 →
      1 - c' ≤ (val f' f' f' f').re →
      ∃ P' : ↥(({j} : Finset ι)ᶜ) → α → ℂ, (∀ i, 𝔼 a : α, ‖P' i a‖ ^ 2 = 1) ∧
        1 - 3 * c' ≤ ‖𝔼 x : ↥(({j} : Finset ι)ᶜ) → α, f' x * star (∏ i, P' i (x i))‖) :
    ∃ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 = 1) ∧
      1 - 3 * c ≤ ‖𝔼 x : ι → α, f x * star (∏ i, P i (x i))‖ := by
  have hU : Unique ↥({j} : Finset ι) := (unique_singleton j).some
  obtain ⟨r, lam, g, h, hsvd⟩ := jsvd_exists ({j} : Finset ι) f
  have hvle : (val f f f f).re ≤ 1 := by
    have := val_re_le_l2sq_sq f
    nlinarith [l2sq_nonneg f]
  have hε0 : 0 ≤ c := by linarith
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      have := val_singleton_full j f hsvd
      simp at this
      linarith
    · exact h0
  set ε := 1 - (val f f f f).re with hε
  have hεc : ε ≤ c := by linarith
  have hε0' : 0 ≤ ε := by linarith
  have hv' : (val f f f f).re = 1 - ε := by rw [hε]; ring
  obtain ⟨b1, b2⟩ := swap99induct j f hsvd hr (by linarith) hf hv'
  have hn0 : l2sq (h ⟨0, hr⟩) = 1 :=
    l2sq_eq_one_of_uinner _ (by rw [hsvd.orth_h]; simp)
  have hg0 : l2sq (g ⟨0, hr⟩) = 1 :=
    l2sq_eq_one_of_uinner _ (by rw [hsvd.orth_g]; simp)
  have hlam0 : 0 < lam ⟨0, hr⟩ := hsvd.pos _
  have hlam1 : lam ⟨0, hr⟩ ^ 2 ≤ 1 := by
    have hsum : ∑ i, lam i ^ 2 = l2sq f := by rw [hsvd.sum_sq_lam, matL2sq_jMatrix]
    have : lam ⟨0, hr⟩ ^ 2 ≤ ∑ i, lam i ^ 2 := Finset.single_le_sum (f := fun i => lam i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    linarith
  have hvh : (val (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩)).re ≤ 1 :=
    val_re_le_of_l2sq _ hn0
  obtain ⟨P', hP'n, hP'c⟩ := ih (h ⟨0, hr⟩) (1 - (val (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩)
    (h ⟨0, hr⟩)).re) (by nlinarith) hn0.le (by linarith)
  have hmem : ∀ i : ι, i ≠ j → i ∈ (({j} : Finset ι)ᶜ) := fun i hi => by simpa using hi
  let P : ι → α → ℂ := fun i a =>
    if hi : i = j then g ⟨0, hr⟩ (fun _ => a) else P' ⟨i, hmem i hi⟩ a
  refine ⟨P, ?_, ?_⟩
  · intro i
    by_cases hi : i = j
    · simp only [P, hi, ↓reduceDIte]
      have e := Fintype.expect_equiv (Equiv.funUnique ↥({j} : Finset ι) α).symm
        (fun a : α => ‖g ⟨0, hr⟩ (fun _ => a)‖ ^ 2) (fun u => ‖g ⟨0, hr⟩ u‖ ^ 2) (fun a => rfl)
      rw [e]
      exact hg0
    · simp only [P, hi, ↓reduceDIte]
      exact hP'n _
  · have hprod : ∀ (u : ↥({j} : Finset ι) → α) (v : ↥(({j} : Finset ι)ᶜ) → α),
        ∏ i, P i (glueFree ({j} : Finset ι) u v i) =
          g ⟨0, hr⟩ u * ∏ i', P' i' (v i') := by
      intro u v
      rw [prod_split_coord j (fun i => P i (glueFree ({j} : Finset ι) u v i))]
      congr 1
      · simp only [P, ↓reduceDIte]
        have : (fun _ : ↥({j} : Finset ι) => glueFree ({j} : Finset ι) u v j) = u := by
          funext i
          simp only [glueFree, Finset.mem_singleton_self, ↓reduceDIte]
          exact congrArg u (Subsingleton.elim _ _)
        rw [this]
      · refine Finset.prod_congr rfl fun i' _ => ?_
        have hne : (i' : ι) ≠ j := by
          have := i'.2
          rw [Finset.mem_compl, Finset.mem_singleton] at this
          exact this
        simp only [P, hne, ↓reduceDIte]
        have : glueFree ({j} : Finset ι) u v (i' : ι) = v i' := by
          simp only [glueFree, Finset.mem_singleton, hne, ↓reduceDIte]
        rw [this]
    have hexp : (𝔼 x : ι → α, f x * star (∏ i, P i (x i))) = (lam ⟨0, hr⟩ : ℂ) *
        𝔼 v : ↥(({j} : Finset ι)ᶜ) → α, h ⟨0, hr⟩ v * star (∏ i', P' i' (v i')) := by
      rw [sc_expect_split ({j} : Finset ι)]
      have hpt : ∀ u v, f (glueFree ({j} : Finset ι) u v) *
          star (∏ i, P i (glueFree ({j} : Finset ι) u v i)) =
          ∑ k, (lam k : ℂ) * ((g k u * star (g ⟨0, hr⟩ u)) *
            (h k v * star (∏ i', P' i' (v i')))) := by
        intro u v
        rw [hprod]
        have e : f (glueFree ({j} : Finset ι) u v) = ∑ k, (lam k : ℂ) * g k u * h k v :=
          hsvd.decomp u v
        rw [e, star_mul', Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [hpt]
      simp only [Finset.expect_sum_comm]
      have hk : ∀ k : Fin r, (𝔼 u : ↥({j} : Finset ι) → α, 𝔼 v : ↥(({j} : Finset ι)ᶜ) → α,
          (lam k : ℂ) * ((g k u * star (g ⟨0, hr⟩ u)) *
            (h k v * star (∏ i', P' i' (v i'))))) =
          (lam k : ℂ) * ((if k = ⟨0, hr⟩ then (1 : ℂ) else 0) *
            𝔼 v : ↥(({j} : Finset ι)ᶜ) → α, h k v * star (∏ i', P' i' (v i'))) := by
        intro k
        have e : (𝔼 u : ↥({j} : Finset ι) → α, g k u * star (g ⟨0, hr⟩ u)) =
            if k = ⟨0, hr⟩ then 1 else 0 := hsvd.orth_g k ⟨0, hr⟩
        rw [← e]
        simp only [← Finset.mul_expect, ← Finset.expect_mul]
      simp only [hk]
      simp [mul_ite, Finset.sum_ite_eq']
    rw [hexp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam0.le]
    have hc' : 1 - (val (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩)).re ≤
        ε - (1 / 4) * (1 - lam ⟨0, hr⟩ ^ 2) * (1 - ε) := by nlinarith [b2]
    have hd0 : (0 : ℝ) ≤ 1 - lam ⟨0, hr⟩ ^ 2 := by linarith
    have hd1 : (0 : ℝ) ≤ 1 - ε := by linarith
    have hprod0 := mul_nonneg hd0 hd1
    have hc'0 : 1 - (val (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩) (h ⟨0, hr⟩)).re ≤ 1 / 20 := by
      nlinarith
    have key := aux9 c ε _ (lam ⟨0, hr⟩) hεc hc hε0' hlam0 b1 hlam1 (by linarith) hc' hc'0
    exact key.trans (mul_le_mul_of_nonneg_left hP'c hlam0.le)

private lemma swapNine_aux (n : ℕ) : ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    Fintype.card κ = n → ∀ (f : (κ → α) → ℂ) (c : ℝ), c ≤ 1 / 20 → l2sq f ≤ 1 →
      1 - c ≤ (val f f f f).re →
      ∃ P : κ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 = 1) ∧
        1 - 3 * c ≤ ‖𝔼 x : κ → α, f x * star (∏ i, P i (x i))‖ := by
  induction n with
  | zero =>
    intro κ _ _ hcard f c _ hf hv
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 hcard
    exact swapNine_base this f c hf hv
  | succ n ih =>
    intro κ _ _ hcard f c hc hf hv
    obtain ⟨j⟩ := Fintype.card_pos_iff.1 (by omega : 0 < Fintype.card κ)
    refine swapNine_step j f c hc hf hv (fun f' c' hc' hf' hv' => ?_)
    refine ih (↥(({j} : Finset κ)ᶜ)) ?_ f' c' hc' hf' hv'
    rw [Fintype.card_coe, Finset.card_compl, Finset.card_singleton]
    omega

theorem swapNine (f : (ι → α) → ℂ) {c : ℝ} (hc : c ≤ 1 / 20) (hf : l2sq f ≤ 1)
    (hv : 1 - c ≤ (val f f f f).re) :
    ∃ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 = 1) ∧
      1 - 3 * c ≤ ‖𝔼 x : ι → α, f x * star (∏ i, P i (x i))‖ :=
  swapNine_aux _ ι rfl f c hc hf hv

end SwapSvdCalc
end TrackB
end RestrictedPolynomials
end
