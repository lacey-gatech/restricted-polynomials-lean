module

public import RestrictedPolynomials.TrackB.SwapSvdCalculus
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Track B (auxiliary part): infrastructure for `SwapSvdInc`

Source: CSP6 (arXiv:2411.15133v1 `main.tex`) L937-1035 (`lemma:svdinc` and its cases).

This module holds the proof infrastructure used by `SwapSvdInc.lean` (split because of length):
the ambient singular functions `svdIncG`, `svdIncH`, the product rule for functions depending on
complementary coordinate sets, the singular-vector bounds, the Parseval formula for partial sums,
and the finite phase averaging (over cube roots of unity) behind Case 2a.
All names carry the prefix `svdInc`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapSvdIncAux
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Splitting the coordinates -/

private def sicSplit (S : Finset ι) : (ι → α) ≃ (↥S → α) × (↥Sᶜ → α) where
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

theorem svdInc_expect_split (S : Finset ι) (Φ : (ι → α) → ℂ) :
    𝔼 x : ι → α, Φ x = 𝔼 u : ↥S → α, 𝔼 v : ↥Sᶜ → α, Φ (glueFree S u v) := by
  rw [← Finset.expect_product' (f := fun u v => Φ (glueFree S u v)), Finset.univ_product_univ]
  exact Fintype.expect_equiv (sicSplit S) _ _
    (fun x => congrArg Φ ((sicSplit S).symm_apply_apply x).symm)

omit [Fintype α] [DecidableEq α] in
theorem svdInc_glue_restrS (S : Finset ι) (u : ↥S → α) (v : ↥Sᶜ → α) :
    (fun i : ↥S => glueFree S u v i) = u := by
  funext i; simp [glueFree, i.2]

omit [Fintype α] [DecidableEq α] in
theorem svdInc_glue_restrT (S : Finset ι) (u : ↥S → α) (v : ↥Sᶜ → α) :
    (fun i : ↥Sᶜ => glueFree S u v i) = v := by
  funext i
  have : (i : ι) ∉ S := mem_compl.1 i.2
  simp [glueFree, this]

omit [Fintype α] [DecidableEq α] in
theorem svdInc_glue_self (S : Finset ι) (x : ι → α) :
    glueFree S (fun i : ↥S => x i) (fun i : ↥Sᶜ => x i) = x := by
  funext i; by_cases hi : i ∈ S <;> simp [glueFree, hi]

theorem svdInc_uinner_prodSplit (S : Finset ι) (a c : (↥S → α) → ℂ) (b d : (↥Sᶜ → α) → ℂ) :
    uinner (prodSplit S a b) (prodSplit S c d) = uinner a c * uinner b d := by
  unfold uinner
  rw [svdInc_expect_split S, Finset.expect_mul_expect]
  refine Finset.expect_congr rfl fun u _ => Finset.expect_congr rfl fun v _ => ?_
  simp only [prodSplit, svdInc_glue_restrS, svdInc_glue_restrT, star_mul']
  ring

theorem svdInc_ofReal_l2sq {κ : Type} [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) :
    ((l2sq u : ℝ) : ℂ) = uinner u u := by
  simp only [l2sq, Complex.ofReal_expect, uinner]
  refine Finset.expect_congr rfl fun t _ => ?_
  rw [Complex.ofReal_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- product rule for functions depending on complementary coordinate sets -/
theorem svdInc_expect_mul_dep (S : Finset ι) (x₀ : ι → α) (A B : (ι → α) → ℂ)
    (hA : ∀ x y : ι → α, (∀ i ∈ S, x i = y i) → A x = A y)
    (hB : ∀ x y : ι → α, (∀ i ∈ Sᶜ, x i = y i) → B x = B y) :
    𝔼 x, A x * B x = (𝔼 x, A x) * (𝔼 x, B x) := by
  have hA' : ∀ (u : ↥S → α) (v : ↥Sᶜ → α),
      A (glueFree S u v) = A (glueFree S u (fun i : ↥Sᶜ => x₀ i)) := fun u v =>
    hA _ _ (fun i hi => by simp [glueFree, hi])
  have hB' : ∀ (u : ↥S → α) (v : ↥Sᶜ → α),
      B (glueFree S u v) = B (glueFree S (fun i : ↥S => x₀ i) v) := fun u v =>
    hB _ _ (fun i hi => by
      have : i ∉ S := mem_compl.1 hi
      simp [glueFree, this])
  haveI : Nonempty (↥Sᶜ → α) := ⟨fun i => x₀ i⟩
  haveI : Nonempty (↥S → α) := ⟨fun i => x₀ i⟩
  rw [svdInc_expect_split S (fun x => A x * B x), svdInc_expect_split S A,
    svdInc_expect_split S B]
  simp only [hA', hB', Fintype.expect_const]
  rw [Finset.expect_mul_expect]

/-! ### Linearity of the inner product -/

theorem svdInc_uinner_lin {κ : Type} (s s' : Finset κ) (a b : κ → ℂ) (u w : κ → (ι → α) → ℂ) :
    uinner (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ j ∈ s', b j * w j x) =
      ∑ i ∈ s, ∑ j ∈ s', a i * star (b j) * uinner (u i) (w j) := by
  have key : ∀ x : ι → α, (∑ i ∈ s, a i * u i x) * star (∑ j ∈ s', b j * w j x) =
      ∑ i ∈ s, ∑ j ∈ s', a i * star (b j) * (u i x * star (w j x)) := by
    intro x
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [star_mul']
    ring
  unfold uinner
  simp only [key, Finset.expect_sum_comm, Finset.mul_expect]

/-! ### The ambient singular functions -/

variable {S : Finset ι} {f : (ι → α) → ℂ}

/-- the left singular function `x ↦ gᵢ(x|_S)`, as a function on `ι → α` -/
def svdIncG (d : SwapSvdData S f) (i : Fin d.r) : (ι → α) → ℂ :=
  prodSplit S (d.g i) (fun _ => 1)

/-- the right singular function `x ↦ hᵢ(x|_{Sᶜ})`, as a function on `ι → α` -/
def svdIncH (d : SwapSvdData S f) (i : Fin d.r) : (ι → α) → ℂ :=
  prodSplit S (fun _ => 1) (d.h i)

theorem svdIncG_apply (d : SwapSvdData S f) (i : Fin d.r) (x : ι → α) :
    svdIncG d i x = d.g i (fun k : ↥S => x k) := by
  simp [svdIncG, prodSplit]

theorem svdIncH_apply (d : SwapSvdData S f) (i : Fin d.r) (x : ι → α) :
    svdIncH d i x = d.h i (fun k : ↥Sᶜ => x k) := by
  simp [svdIncH, prodSplit]

theorem svdInc_GH (d : SwapSvdData S f) (i : Fin d.r) (x : ι → α) :
    svdIncG d i x * svdIncH d i x = prodSplit S (d.g i) (d.h i) x := by
  simp [svdIncG_apply, svdIncH_apply, prodSplit]

theorem svdInc_decomp (d : SwapSvdData S f) (x : ι → α) :
    f x = ∑ i, (d.lam i : ℂ) * (svdIncG d i x * svdIncH d i x) := by
  have := d.isJSVD.decomp (fun i : ↥S => x i) (fun i : ↥Sᶜ => x i)
  simp only [jMatrix, svdInc_glue_self] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [svdIncG_apply, svdIncH_apply]
  ring

theorem svdInc_truncOn_apply (d : SwapSvdData S f) (s : Finset (Fin d.r)) (x : ι → α) :
    d.truncOn s x = ∑ i ∈ s, (d.lam i : ℂ) * (svdIncG d i x * svdIncH d i x) := by
  simp only [SwapSvdData.truncOn, svdInc_GH]

theorem svdInc_f_eq_truncOn (d : SwapSvdData S f) (x : ι → α) :
    f x = d.truncOn Finset.univ x := by
  rw [svdInc_truncOn_apply]; exact svdInc_decomp d x

theorem svdInc_G_dep (d : SwapSvdData S f) (i : Fin d.r) (x y : ι → α)
    (h : ∀ k ∈ S, x k = y k) : svdIncG d i x = svdIncG d i y := by
  rw [svdIncG_apply, svdIncG_apply]
  congr 1
  funext k
  exact h k k.2

theorem svdInc_H_dep_compl (d : SwapSvdData S f) (i : Fin d.r) (x y : ι → α)
    (h : ∀ k ∈ Sᶜ, x k = y k) : svdIncH d i x = svdIncH d i y := by
  rw [svdIncH_apply, svdIncH_apply]
  congr 1
  funext k
  exact h k k.2

theorem svdInc_lam_pos (d : SwapSvdData S f) (i : Fin d.r) : 0 < d.lam i :=
  d.isJSVD.pos i

theorem svdInc_sum_lam_sq (d : SwapSvdData S f) : ∑ i, d.lam i ^ 2 = l2sq f :=
  d.isJSVD.sum_sq_lam.trans (matL2sq_jMatrix S f)

theorem svdInc_lam_sq_le (d : SwapSvdData S f) (i : Fin d.r) : d.lam i ^ 2 ≤ l2sq f := by
  rw [← svdInc_sum_lam_sq d]
  exact Finset.single_le_sum (f := fun j => d.lam j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- nonemptiness of the ambient space from `l2sq f > 0` -/
theorem svdInc_nonempty_of_l2sq_pos (h : 0 < l2sq f) : Nonempty (ι → α) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  simp [l2sq] at h

theorem svdInc_uinner_one (x₀ : ι → α) :
    uinner (fun _ : ↥Sᶜ → α => (1 : ℂ)) (fun _ => 1) = 1 := by
  haveI : Nonempty (↥Sᶜ → α) := ⟨fun i => x₀ i⟩
  simp [uinner]

theorem svdInc_uinner_one' (x₀ : ι → α) :
    uinner (fun _ : ↥S → α => (1 : ℂ)) (fun _ => 1) = 1 := by
  haveI : Nonempty (↥S → α) := ⟨fun i => x₀ i⟩
  simp [uinner]

theorem svdInc_orth_G (d : SwapSvdData S f) (x₀ : ι → α) (i j : Fin d.r) :
    uinner (svdIncG d i) (svdIncG d j) = if i = j then 1 else 0 := by
  unfold svdIncG
  rw [svdInc_uinner_prodSplit, svdInc_uinner_one x₀, mul_one]
  exact d.isJSVD.orth_g i j

theorem svdInc_orth_H (d : SwapSvdData S f) (x₀ : ι → α) (i j : Fin d.r) :
    uinner (svdIncH d i) (svdIncH d j) = if i = j then 1 else 0 := by
  unfold svdIncH
  rw [svdInc_uinner_prodSplit, svdInc_uinner_one' x₀, one_mul]
  exact d.isJSVD.orth_h i j

/-- sup-norm bounds of the singular vectors -/
theorem svdInc_bounds {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (i : Fin d.r) :
    (∀ x, ‖svdIncG d i x‖ ≤ B / d.lam i) ∧ (∀ x, ‖svdIncH d i x‖ ≤ B / d.lam i) := by
  have hg : uinner (d.g i) (d.g i) = 1 := by simpa using d.isJSVD.orth_g i i
  have hh : uinner (d.h i) (d.h i) = 1 := by simpa using d.isJSVD.orth_h i i
  have := svd_vectors_bounded (M := jMatrix S f) (B := B) (lam := d.lam i)
    (fun s t => hB _) (svdInc_lam_pos d i) (d.g i) (d.h i) hg hh
    (d.isJSVD.singular_pair i).1 (d.isJSVD.singular_pair i).2
  exact ⟨fun x => by rw [svdIncG_apply]; exact this.1 _, fun x => by
    rw [svdIncH_apply]; exact this.2 _⟩

/-- `hᵢ` only sees the coordinates of `R \ S` when `f` only sees `R`. -/
theorem svdInc_H_dep {R : Finset ι} (hdep : ∀ x y : ι → α, (∀ i ∈ R, x i = y i) → f x = f y)
    (d : SwapSvdData S f) (i : Fin d.r) (x y : ι → α) (h : ∀ k ∈ R \ S, x k = y k) :
    svdIncH d i x = svdIncH d i y := by
  have hs := (d.isJSVD.singular_pair i).2
  have hpos := svdInc_lam_pos d i
  have hxy : d.h i (fun k : ↥Sᶜ => x k) = d.h i (fun k : ↥Sᶜ => y k) := by
    have e1 := hs (fun k : ↥Sᶜ => x k)
    have e2 := hs (fun k : ↥Sᶜ => y k)
    have hM : ∀ s : ↥S → α, jMatrix S f s (fun k : ↥Sᶜ => x k) =
        jMatrix S f s (fun k : ↥Sᶜ => y k) := by
      intro s
      simp only [jMatrix]
      refine hdep _ _ (fun k hk => ?_)
      by_cases hkS : k ∈ S
      · simp [glueFree, hkS]
      · have hkc : k ∈ Sᶜ := mem_compl.2 hkS
        simp only [glueFree, hkS, dite_false]
        exact h k (Finset.mem_sdiff.2 ⟨hk, hkS⟩)
    simp only [hM] at e1
    rw [e1] at e2
    have : (d.lam i : ℂ) * d.h i (fun k : ↥Sᶜ => x k) = (d.lam i : ℂ) * d.h i (fun k : ↥Sᶜ => y k) :=
      e2
    exact mul_left_cancel₀ (by exact_mod_cast hpos.ne') this
  rw [svdIncH_apply, svdIncH_apply]
  exact hxy

/-! ### Swap norm estimates -/

theorem svdInc_val_re_le {κ : Type} [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) :
    (val u u u u).re ≤ l2sq u ^ 2 := by
  have := norm_val_le u u u u
  have h0 := l2sq_nonneg u
  have e : Real.sqrt (l2sq u) * Real.sqrt (l2sq u) * Real.sqrt (l2sq u) * Real.sqrt (l2sq u) =
      l2sq u ^ 2 := by
    have := Real.mul_self_sqrt h0
    calc _ = (Real.sqrt (l2sq u) * Real.sqrt (l2sq u)) * (Real.sqrt (l2sq u) * Real.sqrt (l2sq u)) := by ring
      _ = _ := by rw [this]; ring
  rw [e] at this
  exact (Complex.re_le_norm _).trans this

theorem svdInc_swapNorm_le_sqrt {κ : Type} [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) :
    swapNorm u ≤ Real.sqrt (l2sq u) := by
  have h0 := l2sq_nonneg u
  have h4 : swapNorm u ^ 4 ≤ Real.sqrt (l2sq u) ^ 4 := by
    rw [swapNorm_pow_four]
    have : Real.sqrt (l2sq u) ^ 4 = l2sq u ^ 2 := by
      have := Real.sq_sqrt h0
      calc Real.sqrt (l2sq u) ^ 4 = (Real.sqrt (l2sq u) ^ 2) ^ 2 := by ring
        _ = _ := by rw [this]
    rw [this]
    exact svdInc_val_re_le u
  exact (pow_le_pow_iff_left₀ (swapNorm_nonneg _) (Real.sqrt_nonneg _) (by norm_num)).1 h4

theorem svdInc_swapNorm_zero {κ : Type} [Fintype κ] [DecidableEq κ] :
    swapNorm (fun _ : κ → α => (0 : ℂ)) = 0 :=
  (swapNorm_eq_zero_iff _).2 rfl

theorem svdInc_swapNorm_sum_le {κ : Type} {κ' : Type} [Fintype κ'] [DecidableEq κ']
    (s : Finset κ) (u : κ → (κ' → α) → ℂ) :
    swapNorm (fun x => ∑ i ∈ s, u i x) ≤ ∑ i ∈ s, swapNorm (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [svdInc_swapNorm_zero]
  | insert a s ha ih =>
    have e : (fun x => ∑ i ∈ insert a s, u i x) = u a + fun x => ∑ i ∈ s, u i x := by
      funext x; simp [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact (swapNorm_add_le _ _).trans (by linarith)

theorem svdInc_swapNorm_prodSplit_le_one (g : (↥S → α) → ℂ) (h : (↥Sᶜ → α) → ℂ)
    (hg : l2sq g = 1) (hh : l2sq h = 1) : swapNorm (prodSplit S g h) ≤ 1 := by
  have h4 : swapNorm (prodSplit S g h) ^ 4 ≤ 1 := by
    rw [swapNorm_pow_four, val_prodSplit_self]
    have e1 : val g g g g = (((val g g g g).re : ℝ) : ℂ) := by
      rw [val_eq_ofReal_pair, Complex.ofReal_re]
    have e2 : val h h h h = (((val h h h h).re : ℝ) : ℂ) := by
      rw [val_eq_ofReal_pair, Complex.ofReal_re]
    rw [e1, e2, ← Complex.ofReal_mul, Complex.ofReal_re]
    have a1 := svdInc_val_re_le g
    have a2 := svdInc_val_re_le h
    have b1 := val_re_nonneg_pair g g
    have b2 := val_re_nonneg_pair h h
    rw [hg] at a1; rw [hh] at a2
    nlinarith
  by_contra hlt
  push_neg at hlt
  have := one_lt_pow₀ hlt (by norm_num : (4:ℕ) ≠ 0)
  linarith

theorem svdInc_l2sq_truncOn (d : SwapSvdData S f) (x₀ : ι → α) (s : Finset (Fin d.r)) :
    l2sq (d.truncOn s) = ∑ i ∈ s, d.lam i ^ 2 := by
  have e : d.truncOn s = fun x => ∑ i ∈ s, (d.lam i : ℂ) * prodSplit S (d.g i) (d.h i) x := rfl
  have := svdInc_ofReal_l2sq (d.truncOn s)
  rw [e, svdInc_uinner_lin s s (fun i => (d.lam i : ℂ)) (fun i => (d.lam i : ℂ))
    (fun i => prodSplit S (d.g i) (d.h i)) (fun i => prodSplit S (d.g i) (d.h i))] at this
  simp only [svdInc_uinner_prodSplit, d.isJSVD.orth_g, d.isJSVD.orth_h] at this
  have h2 : ((∑ i ∈ s, d.lam i ^ 2 : ℝ) : ℂ) = ∑ i ∈ s, ∑ j ∈ s, (d.lam i : ℂ) * star (d.lam j : ℂ) *
      ((if i = j then (1:ℂ) else 0) * if i = j then 1 else 0) := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · simp [sq]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd hi h
  exact_mod_cast this.trans h2.symm

/-! ### Expansion of `val` of a sum -/

private lemma sic_val_sum {κ : Type} (s : Finset κ) (a : κ → ℂ) (u : κ → (ι → α) → ℂ) :
    val (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x)
        (fun x => ∑ i ∈ s, a i * u i x) (fun x => ∑ i ∈ s, a i * u i x) =
      ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s,
        a i * a j * star (a k) * star (a l) * val (u i) (u j) (u k) (u l) := by
  have key : ∀ (x y : ι → α) (b : ι → Bool), (∑ i ∈ s, a i * u i x) * (∑ j ∈ s, a j * u j y) *
      star (∑ k ∈ s, a k * u k (swapL b x y)) * star (∑ l ∈ s, a l * u l (swapR b x y)) =
      ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, a i * a j * star (a k) * star (a l) *
        (u i x * u j y * star (u k (swapL b x y)) * star (u l (swapR b x y))) := by
    intro x y b
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [val, key]
  simp only [Finset.expect_sum_comm, Finset.mul_expect]

private lemma sic_fold_sym {κ : Type} [LinearOrder κ] (s : Finset κ) (X : κ → κ → ℝ)
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

private lemma sic_val_swap_xy (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
    val f₁ f₂ f₃ f₄ = val f₂ f₁ f₄ f₃ := by
  simp only [val]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_congr rfl (fun y _ =>
    Finset.expect_congr rfl (fun b _ => ?_)))
  show f₁ y * f₂ x * star (f₃ (swapR b x y)) * star (f₄ (swapL b x y)) =
    f₂ x * f₁ y * star (f₄ (swapL b x y)) * star (f₃ (swapR b x y))
  ring

private lemma sic_val_swap_34 (f₁ f₂ f₃ f₄ : (ι → α) → ℂ) :
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

/-! ### Phase averaging over cube roots of unity -/

private lemma sic_exists_m {κ : Type} [DecidableEq κ] (i j k l : κ)
    (h : ¬((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    ∃ m, ((if i = m then 1 else 0) + (if j = m then 1 else 0) - (if k = m then 1 else 0)
      - (if l = m then 1 else 0) : ZMod 3) ≠ 0 := by
  by_contra hc
  push Not at hc
  have hi := hc i
  have hj := hc j
  clear hc
  apply h
  by_cases h1 : i = j <;> by_cases h2 : i = k <;> by_cases h3 : i = l <;>
    by_cases h4 : j = k <;> by_cases h5 : j = l <;> by_cases h6 : k = l <;>
    simp [h1, h2, h3, h4, h5, h6, eq_comm] at hi hj ⊢ <;> revert hi hj <;> decide

private lemma sic_ψ_one_ne : (ZMod.stdAddChar : AddChar (ZMod 3) ℂ) 1 ≠ 1 := by
  intro h
  apply ZMod.isPrimitive_stdAddChar 3 (a := 1) one_ne_zero
  ext x
  simp only [AddChar.mulShift_apply, one_mul, AddChar.coe_one, Pi.one_apply]
  fin_cases x
  · exact AddChar.map_zero_eq_one _
  · exact h
  · have : ((2 : ZMod 3)) = 1 + 1 := by decide
    show (ZMod.stdAddChar : AddChar (ZMod 3) ℂ) 2 = 1
    rw [this, AddChar.map_add_eq_mul, h, one_mul]

private lemma sic_ψ_mul_star (x : ZMod 3) :
    (ZMod.stdAddChar : AddChar (ZMod 3) ℂ) x * star ((ZMod.stdAddChar : AddChar (ZMod 3) ℂ) x) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
  simp

private lemma sic_phase_avg {κ : Type} [Fintype κ] [DecidableEq κ] (i j k l : κ) :
    𝔼 e : κ → ZMod 3, ((ZMod.stdAddChar : AddChar (ZMod 3) ℂ) (e i) *
        (ZMod.stdAddChar : AddChar (ZMod 3) ℂ) (e j) *
        star ((ZMod.stdAddChar : AddChar (ZMod 3) ℂ) (e k)) *
        star ((ZMod.stdAddChar : AddChar (ZMod 3) ℂ) (e l))) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then 1 else 0 := by
  set ψ : AddChar (ZMod 3) ℂ := ZMod.stdAddChar with hψ
  split_ifs with hc
  · have : ∀ e : κ → ZMod 3, ψ (e i) * ψ (e j) * star (ψ (e k)) * star (ψ (e l)) = 1 := by
      intro e
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        calc _ = (ψ (e i) * star (ψ (e i))) * (ψ (e j) * star (ψ (e j))) := by ring
          _ = 1 := by rw [sic_ψ_mul_star, sic_ψ_mul_star]; ring
      · subst h1; subst h2
        calc _ = (ψ (e i) * star (ψ (e i))) * (ψ (e j) * star (ψ (e j))) := by ring
          _ = 1 := by rw [sic_ψ_mul_star, sic_ψ_mul_star]; ring
    rw [Finset.expect_congr rfl (fun e _ => this e)]
    simp
  · obtain ⟨m, hm⟩ := sic_exists_m i j k l hc
    obtain ⟨n, hn⟩ : ∃ n : ZMod 3, n = ((if i = m then 1 else 0) + (if j = m then 1 else 0)
        - (if k = m then 1 else 0) - (if l = m then 1 else 0)) := ⟨_, rfl⟩
    rw [← hn] at hm
    have hΦ : ∀ e : κ → ZMod 3, ψ (e i) * ψ (e j) * star (ψ (e k)) * star (ψ (e l)) =
        ψ (e i + e j + -e k + -e l) := by
      intro e
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        AddChar.map_neg_eq_conj, AddChar.map_neg_eq_conj]
      rfl
    have hn2 : n * n = 1 := by
      clear hn hΦ; revert hm; revert n; decide
    have hs : ∀ x : κ, (Pi.single m n : κ → ZMod 3) x = n * (if x = m then 1 else 0) := by
      intro x; simp [Pi.single_apply]
    have hshift : ∀ e : κ → ZMod 3, ψ ((e + (Pi.single m n : κ → ZMod 3)) i +
        (e + (Pi.single m n : κ → ZMod 3)) j + -(e + (Pi.single m n : κ → ZMod 3)) k +
        -(e + (Pi.single m n : κ → ZMod 3)) l) = ψ (e i + e j + -e k + -e l) * ψ 1 := by
      intro e
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Pi.add_apply, hs]
      calc _ = (e i + e j + -e k + -e l) + n * ((if i = m then 1 else 0) + (if j = m then 1 else 0)
            - (if k = m then 1 else 0) - (if l = m then 1 else 0)) := by ring
        _ = (e i + e j + -e k + -e l) + n * n := by rw [← hn]
        _ = _ := by rw [hn2]
    simp only [hΦ]
    set A : (κ → ZMod 3) → ℂ := fun e => ψ (e i + e j + -e k + -e l) with hA
    have h1 : 𝔼 e : κ → ZMod 3, A (e + (Pi.single m n : κ → ZMod 3)) = 𝔼 e : κ → ZMod 3, A e :=
      Fintype.expect_equiv (Equiv.addRight (Pi.single m n : κ → ZMod 3)) _ _ (fun e => rfl)
    have h2 : 𝔼 e : κ → ZMod 3, A (e + (Pi.single m n : κ → ZMod 3)) =
        (𝔼 e : κ → ZMod 3, A e) * ψ 1 := by
      rw [Finset.expect_mul]
      exact Finset.expect_congr rfl fun e _ => hshift e
    rw [h2] at h1
    have h3 : (𝔼 e : κ → ZMod 3, A e) * (ψ 1 - 1) = 0 := by rw [mul_sub, h1]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) sic_ψ_one_ne

private lemma sic_sum4 {κ : Type} [DecidableEq κ] (s : Finset κ) (w : κ → κ → κ → κ → ℂ) :
    ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, (if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then w i j k l else 0) =
      ∑ j ∈ s, ∑ i ∈ s, w i j i j + ∑ j ∈ s, ∑ i ∈ s, w i j j i - ∑ i ∈ s, w i i i i := by
  have h : ∀ i j k l : κ, (if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then w i j k l else 0) =
      (if i = k ∧ j = l then w i j k l else 0) + (if i = l ∧ j = k then w i j k l else 0)
      - (if i = k ∧ j = l ∧ i = l ∧ j = k then w i j k l else 0) := by
    intro i j k l
    by_cases a : i = k <;> by_cases b : j = l <;> by_cases c : i = l <;> by_cases d : j = k <;>
      simp [a, b, c, d]
  have e1 : ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, (if i = k ∧ j = l then w i j k l else 0) =
      ∑ j ∈ s, ∑ i ∈ s, w i j i j := by
    have h1 : ∀ l k j, ∑ i ∈ s, (if i = k ∧ j = l then w i j k l else 0) =
        if j = l ∧ k ∈ s then w k j k l else 0 := by
      intro l k j
      by_cases hjl : j = l <;> by_cases hk : k ∈ s <;> simp [hjl, hk, Finset.sum_ite_eq']
    simp only [h1]
    have h2 : ∀ l k, ∑ j ∈ s, (if j = l ∧ k ∈ s then w k j k l else 0) =
        if l ∈ s ∧ k ∈ s then w k l k l else 0 := by
      intro l k
      by_cases hl : l ∈ s <;> by_cases hk : k ∈ s <;> simp [hl, hk, Finset.sum_ite_eq']
    simp only [h2]
    exact Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun k hk => by simp [hl, hk]
  have e2 : ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, (if i = l ∧ j = k then w i j k l else 0) =
      ∑ j ∈ s, ∑ i ∈ s, w i j j i := by
    have h1 : ∀ l k j, ∑ i ∈ s, (if i = l ∧ j = k then w i j k l else 0) =
        if j = k ∧ l ∈ s then w l j k l else 0 := by
      intro l k j
      by_cases hjl : j = k <;> by_cases hk : l ∈ s <;> simp [hjl, hk, Finset.sum_ite_eq']
    simp only [h1]
    have h2 : ∀ l k, ∑ j ∈ s, (if j = k ∧ l ∈ s then w l j k l else 0) =
        if k ∈ s ∧ l ∈ s then w l k k l else 0 := by
      intro l k
      by_cases hl : k ∈ s <;> by_cases hk : l ∈ s <;> simp [hl, hk, Finset.sum_ite_eq']
    simp only [h2]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun k hk => by simp [hl, hk]
  have e3 : ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s,
      (if i = k ∧ j = l ∧ i = l ∧ j = k then w i j k l else 0) = ∑ i ∈ s, w i i i i := by
    have h1 : ∀ l k j, ∑ i ∈ s, (if i = k ∧ j = l ∧ i = l ∧ j = k then w i j k l else 0) =
        if j = l ∧ j = k ∧ l ∈ s then w l j k l else 0 := by
      intro l k j
      by_cases hjl : j = l <;> by_cases hjk : j = k <;> by_cases hl : l ∈ s <;>
        by_cases hk : k = l <;> simp_all [Finset.sum_ite_eq', eq_comm]
    simp only [h1]
    have h2 : ∀ l k, ∑ j ∈ s, (if j = l ∧ j = k ∧ l ∈ s then w l j k l else 0) =
        if l = k ∧ l ∈ s then w l l l l else 0 := by
      intro l k
      by_cases hlk : l = k
      · subst hlk
        by_cases hl : l ∈ s
        · simp [hl]
        · simp [hl]
      · rw [if_neg (fun h => hlk h.1), Finset.sum_eq_zero]
        intro j _
        rw [if_neg]
        rintro ⟨h1, h2, _⟩
        exact hlk (h1.symm.trans h2)
    simp only [h2]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp [hl]
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e1, e2, e3]

theorem svdInc_exists_phases {κ : Type} [LinearOrder κ] [Fintype κ] {ι' : Type} [Fintype ι']
    [DecidableEq ι'] (s : Finset κ) (c : κ → ℝ) (v : κ → (ι' → α) → ℂ) :
    ∃ β : κ → ℂ, (∀ i, ‖β i‖ = 1) ∧
      ∑ i ∈ s, c i ^ 4 * (val (v i) (v i) (v i) (v i)).re +
        4 * ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j),
          c i ^ 2 * c j ^ 2 * (val (v i) (v j) (v i) (v j)).re ≤
      (val (fun x => ∑ i ∈ s, (β i * (c i : ℂ)) * v i x)
        (fun x => ∑ i ∈ s, (β i * (c i : ℂ)) * v i x)
        (fun x => ∑ i ∈ s, (β i * (c i : ℂ)) * v i x)
        (fun x => ∑ i ∈ s, (β i * (c i : ℂ)) * v i x)).re := by
  set ψ : AddChar (ZMod 3) ℂ := ZMod.stdAddChar with hψ
  let w : κ → κ → κ → κ → ℂ := fun i j k l =>
    ((c i * c j * c k * c l : ℝ) : ℂ) * val (v i) (v j) (v k) (v l)
  let Vc : (κ → ZMod 3) → ℂ := fun e =>
    val (fun x => ∑ i ∈ s, (ψ (e i) * (c i : ℂ)) * v i x)
      (fun x => ∑ i ∈ s, (ψ (e i) * (c i : ℂ)) * v i x)
      (fun x => ∑ i ∈ s, (ψ (e i) * (c i : ℂ)) * v i x)
      (fun x => ∑ i ∈ s, (ψ (e i) * (c i : ℂ)) * v i x)
  have hstar : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  have hterm : ∀ (e : κ → ZMod 3) (i j k l : κ),
      (ψ (e i) * (c i : ℂ)) * (ψ (e j) * (c j : ℂ)) * star (ψ (e k) * (c k : ℂ)) *
        star (ψ (e l) * (c l : ℂ)) * val (v i) (v j) (v k) (v l) =
      (ψ (e i) * ψ (e j) * star (ψ (e k)) * star (ψ (e l))) * w i j k l := by
    intro e i j k l
    simp only [w, star_mul', hstar]
    push_cast
    ring
  have hVc : ∀ e, Vc e = ∑ l ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s,
      (ψ (e i) * ψ (e j) * star (ψ (e k)) * star (ψ (e l))) * w i j k l := by
    intro e
    simp only [Vc]
    rw [sic_val_sum s (fun i => ψ (e i) * (c i : ℂ)) v]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hterm e i j k l
  have hE : 𝔼 e : κ → ZMod 3, Vc e = ∑ j ∈ s, ∑ i ∈ s, w i j i j + ∑ j ∈ s, ∑ i ∈ s, w i j j i -
      ∑ i ∈ s, w i i i i := by
    have hav : ∀ i j k l : κ, (𝔼 e : κ → ZMod 3, ψ (e i) * ψ (e j) * star (ψ (e k)) *
        star (ψ (e l))) = if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then 1 else 0 :=
      fun i j k l => sic_phase_avg i j k l
    simp only [hVc, Finset.expect_sum_comm, ← Finset.expect_mul, hav, ite_mul, one_mul, zero_mul]
    exact sic_sum4 s w
  have hre : (𝔼 e : κ → ZMod 3, Vc e).re =
      ∑ i ∈ s, c i ^ 4 * (val (v i) (v i) (v i) (v i)).re +
        4 * ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j),
          c i ^ 2 * c j ^ 2 * (val (v i) (v j) (v i) (v j)).re := by
    rw [hE]
    set Y : κ → κ → ℝ := fun i j => c i ^ 2 * c j ^ 2 * (val (v i) (v j) (v i) (v j)).re with hY
    have hsym : ∀ i j, Y i j = Y j i := by
      intro i j
      simp only [hY]
      rw [sic_val_swap_xy (v i) (v j) (v i) (v j)]
      ring
    have hw1 : ∀ i j, (w i j i j).re = Y i j := by
      intro i j
      simp only [w, hY, Complex.re_ofReal_mul]
      ring
    have hw2 : ∀ i j, (w i j j i).re = Y i j := by
      intro i j
      simp only [w, hY, Complex.re_ofReal_mul]
      rw [sic_val_swap_34 (v i) (v j) (v j) (v i)]
      ring
    have hw3 : ∀ i, (w i i i i).re = c i ^ 4 * (val (v i) (v i) (v i) (v i)).re := by
      intro i
      simp only [w, Complex.re_ofReal_mul]
      ring
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, hw1, hw2, hw3]
    have hf := sic_fold_sym s Y hsym
    rw [Finset.sum_comm (s := s) (t := s) (f := fun j i => Y i j), hf]
    have hD : ∑ i ∈ s, Y i i = ∑ i ∈ s, c i ^ 4 * (val (v i) (v i) (v i) (v i)).re :=
      Finset.sum_congr rfl fun i _ => by simp only [hY]; ring
    rw [hD]
    ring
  have hex : ∃ e : κ → ZMod 3, (𝔼 e : κ → ZMod 3, Vc e).re ≤ (Vc e).re := by
    rw [Complex.re_expect]
    obtain ⟨e, -, he⟩ := Finset.exists_le_of_le_expect (s := (Finset.univ : Finset (κ → ZMod 3)))
      (f := fun e => (Vc e).re) Finset.univ_nonempty le_rfl
    exact ⟨e, he⟩
  obtain ⟨e, he⟩ := hex
  refine ⟨fun i => ψ (e i), fun i => AddChar.norm_apply _ _, ?_⟩
  rw [← hre]
  exact he

/-! ### The real-number core of Case 2b -/

theorem svdInc_case2b_abstract {r : ℕ} (K : Finset (Fin r)) (a V : Fin r → ℝ) (a0 ν δ : ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) (hle : ∀ i, a i ≤ a0) (hδ : δ = 1 - a0)
    (hV0 : ∀ i, 0 ≤ V i) (hV1 : ∀ i, V i ≤ 1) (hν : 0 < ν) (hδpos : 0 < δ)
    (hE : (1 - δ / 3) * ν ≤ ∑ i ∈ K, a i ^ 2 * V i) :
    ∃ i ∈ K, δ * ν / 10 < a i ∧ (1 + δ / 2) * ν ≤ V i := by
  have ha0pos : 0 < a0 := by
    by_contra h
    push Not at h
    have : ∑ i, a i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm ((hle i).trans h) (ha0 i)
    linarith
  have hδ1 : δ < 1 := by linarith
  set Kb := K.filter (fun i => δ * ν / 10 < a i) with hKb
  have hsplit := Finset.sum_filter_add_sum_filter_not K (fun i => δ * ν / 10 < a i)
    (fun i => a i ^ 2 * V i)
  have hsmall : ∑ i ∈ K.filter (fun i => ¬ δ * ν / 10 < a i), a i ^ 2 * V i ≤ δ * ν / 10 := by
    calc ∑ i ∈ K.filter (fun i => ¬ δ * ν / 10 < a i), a i ^ 2 * V i
        ≤ ∑ i ∈ K.filter (fun i => ¬ δ * ν / 10 < a i), (δ * ν / 10) * a i := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := (Finset.mem_filter.1 hi).2
          push Not at hi'
          have := ha0 i
          have := hV0 i
          have := hV1 i
          nlinarith [mul_nonneg (ha0 i) (hV0 i), mul_le_mul_of_nonneg_left (hV1 i) (sq_nonneg (a i))]
      _ = (δ * ν / 10) * ∑ i ∈ K.filter (fun i => ¬ δ * ν / 10 < a i), a i := by
          rw [Finset.mul_sum]
      _ ≤ (δ * ν / 10) * ∑ i, a i := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => ha0 i)
      _ = δ * ν / 10 := by rw [hsum]; ring
  have hbig : (1 - δ / 2) * ν ≤ ∑ i ∈ Kb, a i ^ 2 * V i := by
    have : δ * ν ≥ 0 := by positivity
    nlinarith
  have hne : Kb.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hbig
    simp only [Finset.sum_empty] at hbig
    have : 0 < (1 - δ / 2) * ν := by
      apply mul_pos _ hν; linarith
    linarith
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Kb V hne
  have hsq : ∑ i, a i ^ 2 ≤ a0 := by
    calc ∑ i, a i ^ 2 ≤ ∑ i, a0 * a i :=
          Finset.sum_le_sum fun j _ => by nlinarith [ha0 j, hle j]
      _ = a0 := by rw [← Finset.mul_sum, hsum]; ring
  have hup : ∑ j ∈ Kb, a j ^ 2 * V j ≤ V i * a0 := by
    calc ∑ j ∈ Kb, a j ^ 2 * V j ≤ ∑ j ∈ Kb, a j ^ 2 * V i :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hmax j hj) (sq_nonneg _)
      _ = V i * ∑ j ∈ Kb, a j ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ V i * ∑ j, a j ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (hV0 i)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
      _ ≤ V i * a0 := mul_le_mul_of_nonneg_left hsq (hV0 i)
  have hKi := Finset.mem_filter.1 hi
  refine ⟨i, hKi.1, hKi.2, ?_⟩
  have h1 : (1 - δ / 2) * ν ≤ V i * (1 - δ) := by rw [hδ] at *; nlinarith
  have h2 : (1 + δ / 2) * ν * (1 - δ) ≤ (1 - δ / 2) * ν := by nlinarith [mul_pos hδpos hν]
  have h3 : (1 + δ / 2) * ν * (1 - δ) ≤ V i * (1 - δ) := h2.trans h1
  exact le_of_mul_le_mul_right h3 (by linarith)

end SwapSvdIncAux

end TrackB
end RestrictedPolynomials
end
