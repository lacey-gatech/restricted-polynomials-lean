module

public import RestrictedPolynomials.TrackB.AppBSetting
public import RestrictedPolynomials.TrackB.MergeGeneric
public import RestrictedPolynomials.TrackB.MarkovChain
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Frozen.FinProbPi
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Track B, Appendix B: the chain targets

Supplement I, `lem:chain` (b)-(e), `lem:one-component` (with the
disconnected control of `rmk:control`: the hypothesis `PairwiseConnected3` cannot be dropped),
`lem:gap` and `lem:loewner`. This file holds the six chain targets that use
nothing from `AppBTrunc1Aux`:

* `appB_t1_chain_stoch` (the excess `hat` and `al` are dropped);
* `appB_t1_chain_atoms` (`0 ≤ al` is added, the printed statement is false for `al < 0`);
* `appB_t1_chain_psd`, `appB_t1_one_component`;
* `appB_t1_gap`, with `κ = min 1 (c_MC α²)` and `c_MC` from the `∃ c C` of the built `mossel_MC`;
* `appB_loewner_tensor` (plain real matrix; it needs `S ⪰ 0`, which is `hnn`).

The chain formula `mgenS μbar a b = ∑_z (ν_{xz}(a,z)/ν_x(a)) (ν_{xz}(b,z)/ν_z(z))` is proved here as
the private helper `chn_formula` (the public `appB_t1_chain_formula` lives in `AppBTrunc1`, which
imports this file).

Proof route of `appB_loewner_tensor`: with `w_j(a) = π(a) g_j(a)` the completeness of the
orthonormal family gives `π(a) S(a,c) = ∑_j λ_j w_j(a) conj w_j(c)` and
`π(a) N_{1-κ}(a,c) = ∑_j μ_j w_j(a) conj w_j(c)` with `μ_j = 1` at `j₀` and `1 - κ` elsewhere; the
tensor power expands over `J : ι → A` (`Fintype.prod_sum`) into `∑_J (∏ ν(J_i)) |⟨W_J, F⟩|²`, and
the two sums are compared termwise. All helpers are `private`.
-/

@[expose] public section

open Finset
open scoped ComplexOrder
open scoped Matrix
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section LoewnerAux
variable {A : Type} [Fintype A] [DecidableEq A]

private theorem lw_complete (π : FinProb A) (hπ : ∀ a, 0 < π.prob a) (g : A → A → ℂ)
    (hon : ∀ i j, ∑ a, (π.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) =
      if i = j then 1 else 0) (b c : A) :
    ∑ j, g j b * (starRingEnd ℂ) (g j c) * (π.prob c : ℂ) = if b = c then 1 else 0 := by
  let U : Matrix A A ℂ := Matrix.of fun j a => ((Real.sqrt (π.prob a) : ℝ) : ℂ) * g j a
  have hs : ∀ a, ((Real.sqrt (π.prob a) : ℝ) : ℂ) * ((Real.sqrt (π.prob a) : ℝ) : ℂ) =
      (π.prob a : ℂ) := fun a => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (π.nonneg a)]
  have hs0 : ∀ a, ((Real.sqrt (π.prob a) : ℝ) : ℂ) ≠ 0 := fun a => by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (hπ a)).ne'
  have h1 : U * Uᴴ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.of_apply,
      Matrix.one_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← hon i j]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hs a]
    ring
  have h2 : Uᴴ * U = 1 := mul_eq_one_comm.1 h1
  have h3 : ∀ b c, ∑ j, g j b * (starRingEnd ℂ) (g j c) =
      (((Real.sqrt (π.prob b) : ℝ) : ℂ) * ((Real.sqrt (π.prob c) : ℝ) : ℂ))⁻¹ *
        (if b = c then 1 else 0) := by
    intro b c
    have h := congrFun (congrFun h2 c) b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.of_apply,
      Matrix.one_apply, star_mul', Complex.star_def, Complex.conj_ofReal] at h
    have h' : ((Real.sqrt (π.prob b) : ℝ) : ℂ) * ((Real.sqrt (π.prob c) : ℝ) : ℂ) *
        ∑ j, g j b * (starRingEnd ℂ) (g j c) = if c = b then 1 else 0 := by
      rw [← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hne : ((Real.sqrt (π.prob b) : ℝ) : ℂ) * ((Real.sqrt (π.prob c) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (hs0 b) (hs0 c)
    rw [eq_inv_mul_iff_mul_eq₀ hne, h']
    simp only [eq_comm]
  rw [← Finset.sum_mul, h3]
  by_cases hbc : b = c
  · subst hbc
    simp only [ite_true, mul_one]
    rw [hs b]
    exact inv_mul_cancel₀ (by exact_mod_cast (hπ b).ne')
  · simp [hbc]

private theorem lw_Smat (π : FinProb A) (hπ : ∀ a, 0 < π.prob a) (S : A → A → ℝ)
    (lam : A → ℝ) (g : A → A → ℂ)
    (heig : ∀ j a, ∑ b, (S a b : ℂ) * g j b = lam j * g j a)
    (hon : ∀ i j, ∑ a, (π.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) =
      if i = j then 1 else 0) (a c : A) :
    (π.prob a : ℂ) * (S a c : ℂ) =
      ∑ j, (lam j : ℂ) * (((π.prob a : ℂ) * g j a) * (starRingEnd ℂ) ((π.prob c : ℂ) * g j c)) := by
  have hc := lw_complete π hπ g hon
  have h1 : (S a c : ℂ) = ∑ b, (S a b : ℂ) * ∑ j, g j b * (starRingEnd ℂ) (g j c) * (π.prob c : ℂ) := by
    rw [Finset.sum_eq_single c]
    · rw [hc c c]; simp
    · intro b _ hbc
      rw [hc b c]; simp [hbc]
    · intro h; exact absurd (Finset.mem_univ c) h
  have h2 : (S a c : ℂ) = ∑ j, (lam j : ℂ) * (g j a * (starRingEnd ℂ) (g j c) * (π.prob c : ℂ)) := by
    rw [h1]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := heig j a
    calc ∑ b, (S a b : ℂ) * (g j b * (starRingEnd ℂ) (g j c) * (π.prob c : ℂ))
        = (∑ b, (S a b : ℂ) * g j b) * ((starRingEnd ℂ) (g j c) * (π.prob c : ℂ)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = _ := by rw [this]; ring
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

private theorem lw_Nmat (π : FinProb A) (hπ : ∀ a, 0 < π.prob a) (ρ : ℝ)
    (g : A → A → ℂ) (j0 : A)
    (hon : ∀ i j, ∑ a, (π.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) =
      if i = j then 1 else 0)
    (hconst : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ a, g j0 a = c) (a c : A) :
    (π.prob a : ℂ) * ((ρ * (if a = c then 1 else 0) + (1 - ρ) * π.prob c : ℝ) : ℂ) =
      ∑ j, ((ρ + if j = j0 then 1 - ρ else 0 : ℝ) : ℂ) *
        (((π.prob a : ℂ) * g j a) * (starRingEnd ℂ) ((π.prob c : ℂ) * g j c)) := by
  obtain ⟨c0, hc0, hg0⟩ := hconst
  have hcomp := lw_complete π hπ g hon
  have hn : c0 * (starRingEnd ℂ) c0 = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc0]; simp
  have e1 : ∑ j, (((π.prob a : ℂ) * g j a) * (starRingEnd ℂ) ((π.prob c : ℂ) * g j c)) =
      (π.prob a : ℂ) * (if a = c then 1 else 0) := by
    have := hcomp a c
    calc _ = (π.prob a : ℂ) * ∑ j, g j a * (starRingEnd ℂ) (g j c) * (π.prob c : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, Complex.conj_ofReal]; ring
      _ = _ := by rw [this]
  have e2 : (((π.prob a : ℂ) * g j0 a) * (starRingEnd ℂ) ((π.prob c : ℂ) * g j0 c)) =
      (π.prob a : ℂ) * (π.prob c : ℂ) := by
    rw [hg0 a, hg0 c, map_mul, Complex.conj_ofReal]
    calc _ = (π.prob a : ℂ) * (π.prob c : ℂ) * (c0 * (starRingEnd ℂ) c0) := by ring
      _ = _ := by rw [hn, mul_one]
  have hsplit : ∀ j, ((ρ + if j = j0 then 1 - ρ else 0 : ℝ) : ℂ) *
        (((π.prob a : ℂ) * g j a) * (starRingEnd ℂ) ((π.prob c : ℂ) * g j c)) =
      (ρ : ℂ) * (((π.prob a : ℂ) * g j a) * (starRingEnd ℂ) ((π.prob c : ℂ) * g j c)) +
        (if j = j0 then ((1 - ρ : ℝ) : ℂ) * ((π.prob a : ℂ) * (π.prob c : ℂ)) else 0) := by
    intro j
    by_cases hj : j = j0
    · subst hj
      simp only [ite_true]
      rw [e2]; push_cast; ring
    · simp [hj]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, Finset.sum_ite_eq' ]
  simp only [Finset.mem_univ, ite_true]
  push_cast
  by_cases hac : a = c
  · subst hac; simp; ring
  · simp [hac]; ring

omit [DecidableEq A] in
private theorem lw_form_op (π : FinProb A) (M : A → A → ℝ) (ν : A → ℝ) (w : A → A → ℂ)
    (hM : ∀ a c, (π.prob a : ℂ) * (M a c : ℂ) =
      ∑ j, (ν j : ℂ) * (w j a * (starRingEnd ℂ) (w j c)))
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → A) → ℂ) :
    (π.pi ι).cexpect (fun x => F x * star (∑ x', ((∏ i, M (x i) (x' i) : ℝ) : ℂ) * F x')) =
      ((∑ J : ι → A, (∏ i, ν (J i)) * ‖∑ x, (∏ i, w (J i) (x i)) * F x‖ ^ 2 : ℝ) : ℂ) := by
  have hK : ∀ x x' : ι → A, ((π.pi ι).prob x : ℂ) * ((∏ i, M (x i) (x' i) : ℝ) : ℂ) =
      ∑ J : ι → A, (∏ i, (ν (J i) : ℂ)) *
        ((∏ i, w (J i) (x i)) * (starRingEnd ℂ) (∏ i, w (J i) (x' i))) := by
    intro x x'
    have h0 : ((π.pi ι).prob x : ℂ) * ((∏ i, M (x i) (x' i) : ℝ) : ℂ) =
        ∏ i, ((π.prob (x i) : ℂ) * (M (x i) (x' i) : ℂ)) := by
      show ((∏ i, π.prob (x i) : ℝ) : ℂ) * _ = _
      push_cast
      rw [Finset.prod_mul_distrib]
    rw [h0]
    simp_rw [hM]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.prod_mul_distrib, map_prod, Finset.prod_mul_distrib]
  have hsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq' : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * (starRingEnd ℂ) z := fun z => by
    have := hsq z
    push_cast at this
    exact this
  have h1 : (π.pi ι).cexpect (fun x => F x * star (∑ x', ((∏ i, M (x i) (x' i) : ℝ) : ℂ) * F x')) =
      ∑ x, ∑ x', ((π.pi ι).prob x : ℂ) * ((∏ i, M (x i) (x' i) : ℝ) : ℂ) *
        (F x * (starRingEnd ℂ) (F x')) := by
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun x _ => ?_
    beta_reduce
    rw [star_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  rw [h1]
  simp_rw [hK]
  have h2 : ∀ J : ι → A, ∑ x, ∑ x', (∏ i, (ν (J i) : ℂ)) *
        ((∏ i, w (J i) (x i)) * (starRingEnd ℂ) (∏ i, w (J i) (x' i))) *
        (F x * (starRingEnd ℂ) (F x')) =
      (∏ i, (ν (J i) : ℂ)) * (((∑ x, (∏ i, w (J i) (x i)) * F x)) *
        (starRingEnd ℂ) (∑ x, (∏ i, w (J i) (x i)) * F x)) := by
    intro J
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [map_mul]
    ring
  calc ∑ x, ∑ x', (∑ J : ι → A, (∏ i, (ν (J i) : ℂ)) *
        ((∏ i, w (J i) (x i)) * (starRingEnd ℂ) (∏ i, w (J i) (x' i)))) *
        (F x * (starRingEnd ℂ) (F x'))
      = ∑ x, ∑ x', ∑ J : ι → A, (∏ i, (ν (J i) : ℂ)) *
        ((∏ i, w (J i) (x i)) * (starRingEnd ℂ) (∏ i, w (J i) (x' i))) *
        (F x * (starRingEnd ℂ) (F x')) := by simp_rw [Finset.sum_mul]
    _ = ∑ x, ∑ J : ι → A, ∑ x', (∏ i, (ν (J i) : ℂ)) *
        ((∏ i, w (J i) (x i)) * (starRingEnd ℂ) (∏ i, w (J i) (x' i))) *
        (F x * (starRingEnd ℂ) (F x')) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ J : ι → A, ∑ x, ∑ x', (∏ i, (ν (J i) : ℂ)) *
        ((∏ i, w (J i) (x i)) * (starRingEnd ℂ) (∏ i, w (J i) (x' i))) *
        (F x * (starRingEnd ℂ) (F x')) := Finset.sum_comm
    _ = _ := by
        push_cast
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [h2 J, hsq']

end LoewnerAux

section Loewner

/-- `lem:loewner` (Supplement I, §7), the Loewner tensor step: if `S` has an `L²(π)`-orthonormal real
eigenbasis with eigenvalues in `[0, 1 - κ]` off one distinguished unimodular-constant eigenvector
(eigenvalue `1`), then `0 ≤ Re ⟨F, S^{⊗ι} F⟩_{π^ι} ≤ Re Stab_{1-κ}(F; π)` for every `F`. `S` is a
plain real matrix: stochasticity is not used (the eigenbasis carries it). -/
theorem appB_loewner_tensor {A : Type} [Fintype A] [DecidableEq A] (π : FinProb A)
    (hπ : ∀ a, 0 < π.prob a) (S : A → A → ℝ) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (lam : A → ℝ) (g : A → A → ℂ) (j0 : A)
    (heig : ∀ j a, ∑ b, (S a b : ℂ) * g j b = lam j * g j a)
    (hon : ∀ i j, ∑ a, (π.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) =
      if i = j then 1 else 0)
    (hnn : ∀ j, 0 ≤ lam j) (h1 : lam j0 = 1) (hconst : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ a, g j0 a = c)
    (hgap : ∀ j, j ≠ j0 → lam j ≤ 1 - κ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → A) → ℂ) :
    0 ≤ ((π.pi ι).cinner F (fun x => ∑ x', ((∏ i, S (x i) (x' i) : ℝ) : ℂ) * F x')).re ∧
      ((π.pi ι).cinner F (fun x => ∑ x', ((∏ i, S (x i) (x' i) : ℝ) : ℂ) * F x')).re ≤
        (cstab π (1 - κ) F).re := by
  have _ := hκ0
  have _ := hκ1
  have hSf := lw_form_op π S lam (fun j a => (π.prob a : ℂ) * g j a)
    (lw_Smat π hπ S lam g heig hon) F
  have hNf := lw_form_op π (noiseKernel π (1 - κ))
    (fun j => (1 - κ) + if j = j0 then 1 - (1 - κ) else 0)
    (fun j a => (π.prob a : ℂ) * g j a) (lw_Nmat π hπ (1 - κ) g j0 hon hconst) F
  have e1 : (π.pi ι).cinner F (fun x => ∑ x', ((∏ i, S (x i) (x' i) : ℝ) : ℂ) * F x') =
      ((∑ J : ι → A, (∏ i, lam (J i)) *
        ‖∑ x, (∏ i, (fun j a => (π.prob a : ℂ) * g j a) (J i) (x i)) * F x‖ ^ 2 : ℝ) : ℂ) := hSf
  have e2 : cstab π (1 - κ) F =
      ((∑ J : ι → A, (∏ i, ((1 - κ) + if J i = j0 then 1 - (1 - κ) else 0)) *
        ‖∑ x, (∏ i, (fun j a => (π.prob a : ℂ) * g j a) (J i) (x i)) * F x‖ ^ 2 : ℝ) : ℂ) :=
    hNf
  rw [e1, e2, Complex.ofReal_re, Complex.ofReal_re]
  refine ⟨Finset.sum_nonneg fun J _ =>
      mul_nonneg (Finset.prod_nonneg fun i _ => hnn _) (sq_nonneg _),
    Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun i _ => hnn _) fun i _ => ?_) (sq_nonneg _)⟩
  by_cases hj : J i = j0
  · simp only [hj, h1, ite_true]
    linarith
  · simp only [hj, ite_false, add_zero]
    exact hgap _ hj

end Loewner

section ChainAux
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the `(x, z)` marginal weight `ν_{xz}(a, z) = ∑_y ν(a, y, z)`. -/
private def chnN (ν : FinProb (X × Y × Z)) (a : X) (z : Z) : ℝ := ∑ y, ν.prob (a, y, z)

private theorem chn_lawX_prob (ν : FinProb (X × Y × Z)) (a : X) :
    (lawX ν).prob a = ∑ z, chnN ν a z := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.1 = a), ν.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [if_true, chnN]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  · intro b _ hb
    simp [hb]
  · simp

private theorem chn_lawZ_prob (ν : FinProb (X × Y × Z)) (z : Z) :
    (lawZ ν).prob z = ∑ a, chnN ν a z := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.2 = z), ν.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [chnN]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private theorem chn_nonneg (ν : FinProb (X × Y × Z)) (a : X) (z : Z) : 0 ≤ chnN ν a z :=
  Finset.sum_nonneg fun y _ => ν.nonneg _

private theorem chn_le_lawX (ν : FinProb (X × Y × Z)) (a : X) (z : Z) :
    chnN ν a z ≤ (lawX ν).prob a := by
  rw [chn_lawX_prob]
  exact Finset.single_le_sum (f := fun z => chnN ν a z) (fun z _ => chn_nonneg ν a z)
    (Finset.mem_univ z)

private theorem chn_le_lawZ (ν : FinProb (X × Y × Z)) (a : X) (z : Z) :
    chnN ν a z ≤ (lawZ ν).prob z := by
  rw [chn_lawZ_prob]
  exact Finset.single_le_sum (f := fun a => chnN ν a z) (fun a _ => chn_nonneg ν a z)
    (Finset.mem_univ a)

private theorem chn_mu (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (x : X) (y : Y) (z : Z) : μbar.prob (x, y, z) = chnN ν x z * (lawY ν).prob y := hμ (x, y, z)

private theorem chn_lawX_mu (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a : X) :
    (lawX μbar).prob a = (lawX ν).prob a := by
  rw [chn_lawX_prob, chn_lawX_prob]
  refine Finset.sum_congr rfl fun z _ => ?_
  show ∑ y, μbar.prob (a, y, z) = chnN ν a z
  simp_rw [chn_mu ν μbar hμ]
  rw [← Finset.mul_sum, (lawY ν).sum_eq_one, mul_one]

private theorem chn_sumx_mu (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (y : Y) (z : Z) :
    ∑ x, μbar.prob (x, y, z) = (lawZ ν).prob z * (lawY ν).prob y := by
  simp_rw [chn_mu ν μbar hμ]
  rw [← Finset.sum_mul, ← chn_lawZ_prob]

private theorem chn_mul_div (ν : FinProb (X × Y × Z)) (a : X) (z : Z) :
    (lawX ν).prob a * (chnN ν a z / (lawX ν).prob a) = chnN ν a z := by
  by_cases h : (lawX ν).prob a = 0
  · have h1 := chn_le_lawX ν a z
    have h2 := chn_nonneg ν a z
    rw [h] at h1 ⊢
    have : chnN ν a z = 0 := le_antisymm h1 h2
    simp [this]
  · field_simp

private theorem chn_formula (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a b : X) :
    mgenS μbar a b = ∑ z, (chnN ν a z / (lawX ν).prob a) * (chnN ν b z / (lawZ ν).prob z) := by
  unfold mgenS
  simp_rw [chn_lawX_mu ν μbar hμ, chn_sumx_mu ν μbar hμ, chn_mu ν μbar hμ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have : ∀ y, chnN ν a z * (lawY ν).prob y / (lawX ν).prob a *
      (chnN ν b z * (lawY ν).prob y / ((lawZ ν).prob z * (lawY ν).prob y)) =
      (lawY ν).prob y * ((chnN ν a z / (lawX ν).prob a) * (chnN ν b z / (lawZ ν).prob z)) := by
    intro y
    by_cases hy : (lawY ν).prob y = 0
    · simp [hy]
    · rw [mul_div_mul_right _ _ hy]
      ring
  simp_rw [this]
  rw [← Finset.sum_mul, (lawY ν).sum_eq_one, one_mul]

private theorem chn_pos_N (ν : FinProb (X × Y × Z)) {a : X} {y : Y} {z : Z}
    (h : (a, y, z) ∈ ν.support) : 0 < chnN ν a z := by
  have h0 : ν.prob (a, y, z) ≠ 0 := h
  have h1 : 0 < ν.prob (a, y, z) := lt_of_le_of_ne (ν.nonneg _) (Ne.symm h0)
  exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun y => ν.prob (a, y, z))
    (fun y _ => ν.nonneg _) (Finset.mem_univ y))

private theorem chn_pos_x (ν : FinProb (X × Y × Z)) (hT : PairwiseConnected3 ν.support) (a : X) :
    0 < (lawX ν).prob a := by
  obtain ⟨y, z, h⟩ := MaxT.PairwiseConnected3.exists_atom_x hT a
  exact lt_of_lt_of_le (chn_pos_N ν h) (chn_le_lawX ν a z)

private theorem chn_pos_z (ν : FinProb (X × Y × Z)) (hT : PairwiseConnected3 ν.support) (z : Z) :
    0 < (lawZ ν).prob z := by
  obtain ⟨x, y, h⟩ := MaxT.PairwiseConnected3.exists_atom_z hT z
  exact lt_of_lt_of_le (chn_pos_N ν h) (chn_le_lawZ ν x z)

private theorem chn_key (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a b : X) :
    (lawX ν).prob a * mgenS μbar a b = ∑ z, chnN ν a z * chnN ν b z / (lawZ ν).prob z := by
  rw [chn_formula ν μbar hμ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← mul_assoc, chn_mul_div, mul_div_assoc]

private theorem chn_prob_le_one {α : Type} [Fintype α] (π : FinProb α) (a : α) : π.prob a ≤ 1 := by
  rw [← π.sum_eq_one]
  exact Finset.single_le_sum (f := π.prob) (fun b _ => π.nonneg b) (Finset.mem_univ a)

private theorem chn_trans_pos (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (a b : X) (z : Z) (ha : 0 < chnN ν a z) (hb : 0 < chnN ν b z) :
    0 < mgenS μbar a b := by
  rw [chn_formula ν μbar hμ]
  have hx : 0 < (lawX ν).prob a := lt_of_lt_of_le ha (chn_le_lawX ν a z)
  have hz : 0 < (lawZ ν).prob z := lt_of_lt_of_le hb (chn_le_lawZ ν b z)
  refine lt_of_lt_of_le (mul_pos (div_pos ha hx) (div_pos hb hz)) ?_
  exact Finset.single_le_sum (f := fun z => (chnN ν a z / (lawX ν).prob a) *
    (chnN ν b z / (lawZ ν).prob z)) (fun z _ => mul_nonneg
      (div_nonneg (chn_nonneg ν a z) ((lawX ν).nonneg a))
      (div_nonneg (chn_nonneg ν b z) ((lawZ ν).nonneg z))) (Finset.mem_univ z)

private theorem chn_connected (ν μbar : FinProb (X × Y × Z)) (hT : PairwiseConnected3 ν.support)
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (T : StochMat X) (hTm : ∀ a b, T.prob a b = mgenS μbar a b) : T.graph.Connected := by
  obtain ⟨⟨x0⟩, -, -, -⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hT
  have hG := ((pairwiseConnected3_iff _).1 hT).2.1
  -- two letters sharing a `z` are reachable in the chain graph
  have hshare : ∀ (a b : X) (z : Z), 0 < chnN ν a z → 0 < chnN ν b z → T.graph.Reachable a b := by
    intro a b z ha hb
    by_cases hab : a = b
    · subst hab; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [graph_adj_iff]
      exact ⟨hab, Or.inl (by rw [hTm]; exact chn_trans_pos ν μbar hμ a b z ha hb)⟩
  let P : X ⊕ Z → Prop := fun v => match v with
    | Sum.inl x => T.graph.Reachable x0 x
    | Sum.inr z => ∀ x, (∃ y, (x, y, z) ∈ ν.support) → T.graph.Reachable x0 x
  have hP : ∀ v, Relation.ReflTransGen
      (SimpleGraph.fromRel fun (a : X ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ ν.support ∧ a = Sum.inl x ∧ b = Sum.inr z).Adj (Sum.inl x0) v → P v := by
    intro v hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hadj ih =>
      rename_i u w
      rw [SimpleGraph.fromRel_adj] at hadj
      obtain ⟨-, hr | hr⟩ := hadj
      · obtain ⟨x, y, z, hxyz, rfl, rfl⟩ := hr
        intro x' ⟨y', hx'⟩
        exact ih.trans (hshare x x' z (chn_pos_N ν hxyz) (chn_pos_N ν hx'))
      · obtain ⟨x, y, z, hxyz, rfl, rfl⟩ := hr
        exact ih x ⟨y, hxyz⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨x0⟩⟩
  have ha : T.graph.Reachable x0 a :=
    hP _ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (hG.preconnected (Sum.inl x0) (Sum.inl a)))
  have hb : T.graph.Reachable x0 b :=
    hP _ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (hG.preconnected (Sum.inl x0) (Sum.inl b)))
  exact ha.symm.trans hb

end ChainAux

section Chain
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `lem:chain` (b), (c): `mgenS μbar` is a `StochMat`, stationary and reversible for `ν_x`
(the hypotheses of the built `mossel_MC`). Positivity of `ν_x` comes from the occurrence half of
`PairwiseConnected3`. -/
theorem appB_t1_chain_stoch (ν μbar : FinProb (X × Y × Z))
    (hT : PairwiseConnected3 ν.support)
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) :
    ∃ T : StochMat X, (∀ a b, T.prob a b = mgenS μbar a b) ∧ T.IsStationary (lawX ν) ∧
      T.IsReversible (lawX ν) := by
  have hx : ∀ a, 0 < (lawX ν).prob a := chn_pos_x ν hT
  have hz : ∀ z, 0 < (lawZ ν).prob z := chn_pos_z ν hT
  have hf := chn_formula ν μbar hμ
  have hnn : ∀ a b, 0 ≤ mgenS μbar a b := fun a b => by
    rw [hf]
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (div_nonneg (chn_nonneg ν a z) (hx a).le) (div_nonneg (chn_nonneg ν b z) (hz z).le)
  have hrow : ∀ a, ∑ b, mgenS μbar a b = 1 := by
    intro a
    simp_rw [hf]
    rw [Finset.sum_comm]
    have h1 : ∀ z, ∑ b, (chnN ν a z / (lawX ν).prob a) * (chnN ν b z / (lawZ ν).prob z) =
        chnN ν a z / (lawX ν).prob a := by
      intro z
      rw [← Finset.mul_sum, ← Finset.sum_div, ← chn_lawZ_prob, div_self (hz z).ne', mul_one]
    simp_rw [h1]
    rw [← Finset.sum_div, ← chn_lawX_prob, div_self (hx a).ne']
  refine ⟨⟨fun a b => mgenS μbar a b, hnn, hrow⟩, fun a b => rfl, ?_, ?_⟩
  · intro b
    show ∑ a, (lawX ν).prob a * mgenS μbar a b = (lawX ν).prob b
    simp_rw [chn_key ν μbar hμ]
    rw [Finset.sum_comm]
    have h1 : ∀ z, ∑ a, chnN ν a z * chnN ν b z / (lawZ ν).prob z = chnN ν b z := by
      intro z
      rw [← Finset.sum_div, ← Finset.sum_mul, ← chn_lawZ_prob, mul_div_cancel_left₀ _ (hz z).ne']
    simp_rw [h1]
    rw [chn_lawX_prob]
  · intro a b
    show (lawX ν).prob a * mgenS μbar a b = (lawX ν).prob b * mgenS μbar b a
    rw [chn_key ν μbar hμ, chn_key ν μbar hμ]
    exact Finset.sum_congr rfl fun z _ => by ring

/-- `lem:chain` (d): minimal positive transition `≥ α²`, for `al ≥ 0`. -/
theorem appB_t1_chain_atoms {al : ℝ} (hal : 0 ≤ al) (ν μbar : FinProb (X × Y × Z))
    (hat : ∀ p ∈ ν.support, al ≤ ν.prob p)
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a b : X)
    (hpos : 0 < mgenS μbar a b) : al ^ 2 ≤ mgenS μbar a b := by
  rw [chn_formula ν μbar hμ] at hpos ⊢
  have hterm : ∀ z, 0 ≤ (chnN ν a z / (lawX ν).prob a) * (chnN ν b z / (lawZ ν).prob z) :=
    fun z => mul_nonneg (div_nonneg (chn_nonneg ν a z) ((lawX ν).nonneg a))
      (div_nonneg (chn_nonneg ν b z) ((lawZ ν).nonneg z))
  obtain ⟨z0, -, h0⟩ : ∃ z ∈ (Finset.univ : Finset Z),
      0 < (chnN ν a z / (lawX ν).prob a) * (chnN ν b z / (lawZ ν).prob z) := by
    by_contra h
    push Not at h
    exact absurd (Finset.sum_nonpos fun z hz => h z hz) (not_le.2 hpos)
  have hA0 : 0 ≤ chnN ν a z0 / (lawX ν).prob a :=
    div_nonneg (chn_nonneg ν a z0) ((lawX ν).nonneg a)
  have hB0 : 0 ≤ chnN ν b z0 / (lawZ ν).prob z0 :=
    div_nonneg (chn_nonneg ν b z0) ((lawZ ν).nonneg z0)
  have hApos : 0 < chnN ν a z0 / (lawX ν).prob a :=
    lt_of_le_of_ne hA0 (fun h => by rw [← h, zero_mul] at h0; exact lt_irrefl _ h0)
  have hBpos : 0 < chnN ν b z0 / (lawZ ν).prob z0 :=
    lt_of_le_of_ne hB0 (fun h => by rw [← h, mul_zero] at h0; exact lt_irrefl _ h0)
  have hAp : 0 < chnN ν a z0 := by
    by_contra hc
    have : chnN ν a z0 = 0 := le_antisymm (not_lt.1 hc) (chn_nonneg ν a z0)
    rw [this, zero_div] at hApos
    exact lt_irrefl _ hApos
  have hBp : 0 < chnN ν b z0 := by
    by_contra hc
    have : chnN ν b z0 = 0 := le_antisymm (not_lt.1 hc) (chn_nonneg ν b z0)
    rw [this, zero_div] at hBpos
    exact lt_irrefl _ hBpos
  have hal_le : ∀ c : X, 0 < chnN ν c z0 → al ≤ chnN ν c z0 := by
    intro c hc
    obtain ⟨y, -, hy⟩ : ∃ y ∈ (Finset.univ : Finset Y), 0 < ν.prob (c, y, z0) := by
      by_contra h
      push Not at h
      exact absurd (Finset.sum_nonpos h) (not_le.2 hc)
    exact (hat _ hy.ne').trans (Finset.single_le_sum (f := fun y => ν.prob (c, y, z0))
      (fun y _ => ν.nonneg _) (Finset.mem_univ y))
  have hxpos : 0 < (lawX ν).prob a := lt_of_lt_of_le hAp (chn_le_lawX ν a z0)
  have hzpos : 0 < (lawZ ν).prob z0 := lt_of_lt_of_le hBp (chn_le_lawZ ν b z0)
  have hA : al ≤ chnN ν a z0 / (lawX ν).prob a := by
    refine (hal_le a hAp).trans ?_
    rw [le_div_iff₀ hxpos]
    nlinarith [chn_prob_le_one (lawX ν) a]
  have hB : al ≤ chnN ν b z0 / (lawZ ν).prob z0 := by
    refine (hal_le b hBp).trans ?_
    rw [le_div_iff₀ hzpos]
    nlinarith [chn_prob_le_one (lawZ ν) z0]
  calc al ^ 2 = al * al := sq al
    _ ≤ (chnN ν a z0 / (lawX ν).prob a) * (chnN ν b z0 / (lawZ ν).prob z0) :=
        mul_le_mul hA hB hal hA0
    _ ≤ _ := Finset.single_le_sum (f := fun z => (chnN ν a z / (lawX ν).prob a) *
        (chnN ν b z / (lawZ ν).prob z)) (fun z _ => hterm z) (Finset.mem_univ z0)

/-- `lem:chain` (e): `S = T*T` is positive semidefinite on `L²(ν_x)`:
`⟨f, S f⟩ = Σ_z ν_z |E_z f|² ≥ 0`. -/
theorem appB_t1_chain_psd (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (f : X → ℂ) :
    0 ≤ ((lawX ν).cinner f (fun a => ∑ b, (mgenS μbar a b : ℂ) * f b)).re := by
  have hsq : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e : ∀ a b, (((lawX ν).prob a : ℂ) * (mgenS μbar a b : ℂ)) =
      ∑ z, ((chnN ν a z : ℂ) * (chnN ν b z : ℂ)) / ((lawZ ν).prob z : ℂ) := by
    intro a b
    rw [← Complex.ofReal_mul, chn_key ν μbar hμ]
    push_cast
    rfl
  have h1 : (lawX ν).cinner f (fun a => ∑ b, (mgenS μbar a b : ℂ) * f b) =
      ∑ a, ∑ b, (((lawX ν).prob a : ℂ) * (mgenS μbar a b : ℂ)) * (f a * (starRingEnd ℂ) (f b)) := by
    unfold FinProb.cinner FinProb.cexpect
    refine Finset.sum_congr rfl fun a _ => ?_
    beta_reduce
    rw [star_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have h2 : (lawX ν).cinner f (fun a => ∑ b, (mgenS μbar a b : ℂ) * f b) =
      ((∑ z, ‖∑ a, (chnN ν a z : ℂ) * f a‖ ^ 2 / (lawZ ν).prob z : ℝ) : ℂ) := by
    rw [h1]
    simp_rw [e, Finset.sum_mul]
    calc ∑ a, ∑ b, ∑ z, ((chnN ν a z : ℂ) * (chnN ν b z : ℂ)) / ((lawZ ν).prob z : ℂ) *
          (f a * (starRingEnd ℂ) (f b))
        = ∑ a, ∑ z, ∑ b, ((chnN ν a z : ℂ) * (chnN ν b z : ℂ)) / ((lawZ ν).prob z : ℂ) *
          (f a * (starRingEnd ℂ) (f b)) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ z, ∑ a, ∑ b, ((chnN ν a z : ℂ) * (chnN ν b z : ℂ)) / ((lawZ ν).prob z : ℂ) *
          (f a * (starRingEnd ℂ) (f b)) := Finset.sum_comm
      _ = _ := by
        push_cast
        refine Finset.sum_congr rfl fun z _ => ?_
        have hq : ((‖∑ a, (chnN ν a z : ℂ) * f a‖ : ℝ) : ℂ) ^ 2 =
            (∑ a, (chnN ν a z : ℂ) * f a) * (starRingEnd ℂ) (∑ a, (chnN ν a z : ℂ) * f a) := by
          have := hsq (∑ a, (chnN ν a z : ℂ) * f a)
          push_cast at this
          exact this
        rw [hq, map_sum, Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, Complex.conj_ofReal]
        ring
  rw [h2, Complex.ofReal_re]
  exact Finset.sum_nonneg fun z _ => div_nonneg (sq_nonneg _) ((lawZ ν).nonneg z)

/-- `lem:one-component` (Supplement I, §7): ONE component, from the `(x, z)` pair of
`PairwiseConnected3` alone (built `pairwiseConnected3_iff`, first projection for `X ⊕ Z`). -/
theorem appB_t1_one_component (ν μbar : FinProb (X × Y × Z))
    (hT : PairwiseConnected3 ν.support)
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (T : StochMat X) (hTm : ∀ a b, T.prob a b = mgenS μbar a b) : T.numComponents = 1 := by
  have hc := chn_connected ν μbar hT hμ T hTm
  have := hc.preconnected.subsingleton_connectedComponent
  have : Nonempty T.graph.ConnectedComponent := ⟨T.graph.connectedComponentMk hc.nonempty.some⟩
  unfold StochMat.numComponents
  exact Nat.card_unique

end Chain

section Gap

/-- `lem:gap` (Supplement I, §7): `κ = min 1 (c_MC α²)`, `c_MC` from the `∃ c C` of the built
`mossel_MC α hal m` (obtained). Under (A), (B) the chain `mgenS μbar` has an `L²(ν_x)`-orthonormal
real eigenbasis (built `spectral_data`) with non-negative eigenvalues, one eigenvalue `1` whose
eigenvector is a unimodular constant, and all others `≤ 1 - κ`. -/
theorem appB_t1_gap (m : ℕ) {al : ℝ} (hal : 0 < al) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
      ∀ (ν μbar : FinProb (X × Y × Z)), (∀ p ∈ ν.support, al ≤ ν.prob p) →
        PairwiseConnected3 ν.support →
        (∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) →
        ∃ (lam : X → ℝ) (g : X → X → ℂ) (j0 : X),
          (∀ j a, ∑ b, (mgenS μbar a b : ℂ) * g j b = lam j * g j a) ∧
          (∀ i j, ∑ a, ((lawX ν).prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) =
            if i = j then 1 else 0) ∧
          (∀ j, 0 ≤ lam j) ∧ lam j0 = 1 ∧ (∃ c : ℂ, ‖c‖ = 1 ∧ ∀ a, g j0 a = c) ∧
          (∀ j, j ≠ j0 → lam j ≤ 1 - κ) := by
  obtain ⟨c, C, hc, hC, H⟩ := mossel_MC al hal m
  have hcal : 0 < c * al ^ 2 := by positivity
  refine ⟨min 1 (c * al ^ 2), lt_min one_pos hcal, min_le_left _ _, ?_⟩
  intro X Y Z _ _ _ _ _ _ hcard ν μbar hat hT hμ
  obtain ⟨T, hTm, hTs, hTr⟩ := appB_t1_chain_stoch ν μbar hT hμ
  have hx : ∀ a, 0 < (lawX ν).prob a := chn_pos_x ν hT
  have hxal : ∀ a, al ≤ (lawX ν).prob a := by
    intro a
    obtain ⟨y, z, h⟩ := MaxT.PairwiseConnected3.exists_atom_x hT a
    refine (hat _ h).trans ((Finset.single_le_sum (f := fun y => ν.prob (a, y, z))
      (fun y _ => ν.nonneg _) (Finset.mem_univ y)).trans (chn_le_lawX ν a z))
  obtain ⟨hmult, hξ, -⟩ := H X hcard (lawX ν) hxal T hTs hTr
  have hbound := hξ (al ^ 2) (fun a b hpos => by
    rw [hTm] at hpos ⊢
    exact appB_t1_chain_atoms hal.le ν μbar hat hμ a b hpos)
  have hncomp := appB_t1_one_component ν μbar hT hμ T hTm
  have hconn := chn_connected ν μbar hT hμ T hTm
  obtain ⟨lam, g, hM, hgeig, hgorth⟩ := spectral_data T (lawX ν) hx hTr
  have hgeig' : ∀ j a, ∑ b, (mgenS μbar a b : ℂ) * g j b = lam j * g j a := by
    intro j a
    have := hgeig j a
    simp_rw [hTm] at this
    exact this
  -- the number of eigenvalues equal to `1`
  have hcount : (Finset.univ.filter fun j => lam j = 1).card ≥ 1 := by
    have h1 := numComponents_le_count T
    rw [hM, count_one_eigenvalues, hncomp] at h1
    exact h1
  obtain ⟨j0, hj0⟩ := Finset.card_pos.1 hcount
  have hj0' : lam j0 = 1 := (Finset.mem_filter.1 hj0).2
  -- nonnegativity of the eigenvalues, from `S ⪰ 0`
  have hnn : ∀ j, 0 ≤ lam j := by
    intro j
    have hpsd := appB_t1_chain_psd ν μbar hμ (g j)
    have hfun : (fun a => ∑ b, (mgenS μbar a b : ℂ) * g j b) = fun a => (lam j : ℂ) * g j a :=
      funext fun a => hgeig' j a
    rw [hfun] at hpsd
    have hci : (lawX ν).cinner (g j) (fun a => (lam j : ℂ) * g j a) = (lam j : ℂ) := by
      unfold FinProb.cinner FinProb.cexpect
      calc ∑ a, ((lawX ν).prob a : ℂ) * (g j a * star ((lam j : ℂ) * g j a))
          = (lam j : ℂ) * ∑ a, ((lawX ν).prob a : ℂ) * g j a * (starRingEnd ℂ) (g j a) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
            ring
        _ = (lam j : ℂ) := by rw [hgorth j j]; simp
    rw [hci, Complex.ofReal_re] at hpsd
    exact hpsd
  -- every eigenvalue other than the distinguished one is `≤ 1 - c α²`
  have hgap : ∀ j, j ≠ j0 → lam j ≤ 1 - c * al ^ 2 := by
    intro j hj
    have hmem : ((lam j : ℝ) : ℂ) ∈ T.eigenvalues - Multiset.replicate T.numComponents (1 : ℂ) := by
      rw [← Multiset.count_pos, Multiset.count_sub, Multiset.count_replicate, hncomp]
      have hin : 0 < T.eigenvalues.count ((lam j : ℝ) : ℂ) := by
        rw [Multiset.count_pos, hM, Multiset.mem_map]
        exact ⟨j, Finset.mem_univ j, rfl⟩
      by_cases h1 : lam j = 1
      · have h2 : 2 ≤ T.eigenvalues.count ((lam j : ℝ) : ℂ) := by
          rw [h1, Complex.ofReal_one, hM, count_one_eigenvalues]
          have hsub : ({j0, j} : Finset X) ⊆ Finset.univ.filter fun j => lam j = 1 :=
            fun i hi => by
              rcases Finset.mem_insert.1 hi with rfl | hi
              · exact hj0
              · rw [Finset.mem_singleton.1 hi]
                exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
          have := Finset.card_le_card hsub
          rwa [Finset.card_pair (Ne.symm hj)] at this
        rw [h1, Complex.ofReal_one] at h2 ⊢
        simp only [if_true]
        omega
      · have h0 : (if (1 : ℂ) = ((lam j : ℝ) : ℂ) then 1 else 0) = 0 := by
          rw [if_neg]
          intro h
          exact h1 (by exact_mod_cast h.symm)
        rw [h0]
        omega
    have := hbound _ hmem
    exact_mod_cast this
  refine ⟨lam, g, j0, hgeig', hgorth, hnn, hj0', ?_, fun j hj => ?_⟩
  · have hg0 : ∀ a, ∑ b, (T.prob a b : ℂ) * g j0 b = g j0 a := by
      intro a
      rw [hgeig j0 a, hj0']
      simp
    have hconst := harmonic_const T (lawX ν) hx hTs (g j0) hg0
    obtain ⟨a0⟩ := hconn.nonempty
    have hcst : ∀ a, g j0 a = g j0 a0 := fun a => hconst a a0 (hconn.preconnected a a0)
    refine ⟨g j0 a0, ?_, hcst⟩
    have h1 := hgorth j0 j0
    simp only [if_true] at h1
    simp_rw [hcst] at h1
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, (lawX ν).sum_eq_one] at h1
    have h2 : g j0 a0 * (starRingEnd ℂ) (g j0 a0) = 1 := by simpa using h1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖g j0 a0‖ ^ 2 = 1 := by exact_mod_cast h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  · exact (hgap j hj).trans (by linarith [min_le_right 1 (c * al ^ 2)])

end Gap

end TrackB
end RestrictedPolynomials
end
