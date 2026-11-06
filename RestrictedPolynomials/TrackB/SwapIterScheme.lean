module

public import RestrictedPolynomials.TrackB.SwapSvdCalculus

/-!
# Track B: the iterative scheme of CSP_6 and `lemma:iter`

Source: CSP6 (arXiv:2411.15133v1 `main.tex`) L839-854 (`subsec:iter`, the scheme), L857-874
(`lemma:phirr`, used through `phirr` of `SwapRestrict`), L879-909 (`lemma:iter`), L1136-1170
(`thm:swap#restriction-composition`).
Covers CSP_6 `subsec:iter`, `lemma:iter` (with `#box-schatten4` and
`#restricted-svd-comparison`), the classical Eckart-Young theorem, and `thm:swap#restriction-composition`.

Readings of the source used here:
* `lemma:iter` with the corrected `phirr` (the printed one has a typo) absorbed, `C ↦ C + 2δ + 1 ≤ (9/4)C`,
  and the explicit probability `γ⁴‖f_t‖²/(36CB²)`;
* the potential carries an arbitrary weight `C > 1` (`C = (θε⁵)⁻¹`);
* the scheme is a deterministic function of its coins, for an arbitrary SVD choice `sel`, and
  runs `K` steps unconditionally;
* Eckart-Young (Frobenius norm, expectation normalisation) and the restricted comparison with an
  arbitrary extra peel `(a, G, H)` (no hypothesis on `H`).

Eckart-Young is proved from an orthonormal basis of the span of the `Hᵢ` (Bessel's inequality twice and
a rearrangement bound); the laws of the scheme are proved coordinate by coordinate (the scheme acts on
each coordinate independently).
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapIter
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the state `(R_t, S_t, z_t)` of the scheme: the live coordinates `R_t = S_t ⊔ T_t`
(with `T_t = R_t \ S_t`) and the fixed values `z_t` (read only outside `R_t`). -/
structure SwapIterState (ι α : Type) where
  R : Finset ι
  S : Finset ι
  z : ι → α

/-- the random choices of one step: the coins of the partition `(S', T')` and the fixing values. -/
abbrev SwapCoins (ι α : Type) : Type := (ι → Bool) × (ι → α)

/-- `f_t`, as a function on `ι → α` that ignores the coordinates outside `R`:
`f_t(x) = f(x_R, z_{Rᶜ})`. -/
def swapIterFun (f : (ι → α) → ℂ) (R : Finset ι) (z : ι → α) : (ι → α) → ℂ :=
  fun x => f (fun i => if i ∈ R then x i else z i)

/-- step 0: `R_0 = [n]`, `S_0` the coins of the first coin vector. -/
def swapIterInit (c : SwapCoins ι α) : SwapIterState ι α :=
  ⟨Finset.univ, Finset.univ.filter fun i => c.1 i = true, c.2⟩

/-- step `t → t+1`: `S' = {c.1 = true}`, `T' = R_t \ S'`, `S_{t+1} = S_t ∩ S'`, `T_{t+1} = T_t ∩ T'`,
`R_{t+1} = S_{t+1} ∪ T_{t+1}`, and the coordinates of `R_t \ R_{t+1}` are fixed to `c.2`. -/
def swapIterStep (st : SwapIterState ι α) (c : SwapCoins ι α) : SwapIterState ι α :=
  ⟨(st.S.filter fun i => c.1 i = true) ∪ ((st.R \ st.S).filter fun i => c.1 i = false),
    st.S.filter fun i => c.1 i = true,
    fun i => if i ∈ st.R \ ((st.S.filter fun i => c.1 i = true) ∪
      ((st.R \ st.S).filter fun i => c.1 i = false)) then c.2 i else st.z i⟩

/-- the scheme for `K` steps (after `K` it stays put): initial coins `c₀`, step coins `ω`. -/
def swapIterRun {K : ℕ} (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) :
    ℕ → SwapIterState ι α
  | 0 => swapIterInit c₀
  | t + 1 => if h : t < K then swapIterStep (swapIterRun c₀ ω t) (ω ⟨t, h⟩)
      else swapIterRun c₀ ω t

omit [Fintype α] [DecidableEq α] in
theorem swapIterRun_S_subset {K : ℕ} (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (t : ℕ) :
    (swapIterRun c₀ ω t).S ⊆ (swapIterRun c₀ ω t).R := by
  induction t with
  | zero => intro i hi; simp [swapIterRun, swapIterInit] at hi ⊢
  | succ t ih =>
    simp only [swapIterRun]
    split_ifs with h
    · exact Finset.subset_union_left
    · exact ih

/-- `f_t` of the state. -/
def swapIterF (f : (ι → α) → ℂ) (st : SwapIterState ι α) : (ι → α) → ℂ :=
  swapIterFun f st.R st.z

/-- `Δ_t = f_t - ∑_{i ≤ t} λᵢ gᵢ hᵢ` (top `t` terms of the `S_t`-SVD of `f_t`). -/
def swapIterDelta (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) (st : SwapIterState ι α)
    (t : ℕ) : (ι → α) → ℂ :=
  fun x => swapIterF f st x - ((sel st.S (swapIterF f st)).trunc t) x

/-- the potential `Φ_t = (C val(f_t)^{1/2} - ‖Δ_t‖₂²) / ‖f_t‖₂²` (source: `C = ε^{-5}`). -/
def swapIterPhi (C : ℝ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) (st : SwapIterState ι α)
    (t : ℕ) : ℝ :=
  (C * ((val (swapIterF f st) (swapIterF f st) (swapIterF f st) (swapIterF f st)).re) ^ (1 / 2 : ℝ) -
    l2sq (swapIterDelta sel f st t)) / l2sq (swapIterF f st)

/-- the normalized value `val(f_t)^{1/2} / ‖f_t‖₂²`. -/
def swapIterNV (f : (ι → α) → ℂ) (st : SwapIterState ι α) : ℝ :=
  ((val (swapIterF f st) (swapIterF f st) (swapIterF f st) (swapIterF f st)).re) ^ (1 / 2 : ℝ) /
    l2sq (swapIterF f st)

/-- the termination rule at time `t`: `val(Δ_t)^{1/2} < γ ‖f_t‖₂²` or `T ≤ t`. -/
def swapIterStopped (γ : ℝ) (T : ℕ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (st : SwapIterState ι α) (t : ℕ) : Prop :=
  ((val (swapIterDelta sel f st t) (swapIterDelta sel f st t) (swapIterDelta sel f st t)
    (swapIterDelta sel f st t)).re) ^ (1 / 2 : ℝ) < γ * l2sq (swapIterF f st) ∨ T ≤ t

/-- the stopping time `τ`. -/
def swapIterTau (γ : ℝ) (T : ℕ) (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {K : ℕ}
    (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) : ℕ :=
  sInf {t | swapIterStopped γ T sel f (swapIterRun c₀ ω t) t}

omit [Fintype α] [DecidableEq α] [Fintype ι] in
/-- the step identity: `f_{t+1}` is `f_t` with the coordinates of `I = R_t \ R_{t+1}` fixed to `c.2`. -/
theorem swapIterF_step (f : (ι → α) → ℂ) (st : SwapIterState ι α) (hSR : st.S ⊆ st.R)
    (c : SwapCoins ι α) :
    swapIterF f (swapIterStep st c) =
      fun x => swapIterF f st (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else x i) := by
  funext x
  simp only [swapIterF, swapIterFun]
  congr 1
  funext i
  have hSRi := @hSR i
  by_cases hR : i ∈ st.R <;> by_cases hS : i ∈ st.S <;> cases hc : c.1 i <;>
    simp_all [swapIterStep]


/-- `S'`: the part of `R_t` chosen by the coins of a step. -/
def swapIterPart (st : SwapIterState ι α) (c : SwapCoins ι α) : Finset ι :=
  st.R.filter fun i => c.1 i = true

/-! ### Eckart-Young -/

private lemma ey_normsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma ey_uinner_symm {T : Type*} [Fintype T] (u v : T → ℂ) :
    uinner v u = star (uinner u v) := by
  unfold uinner
  rw [star_expect]
  refine Finset.expect_congr rfl fun s _ => ?_
  rw [star_mul', star_star, mul_comm]

/-- the basic identity behind Bessel's inequality and the projection bound. -/
private lemma ey_identity {T κ : Type*} [Fintype T] [Fintype κ] [DecidableEq κ]
    (e : κ → T → ℂ) (he : ∀ i j, uinner (e i) (e j) = if i = j then 1 else 0)
    (v : T → ℂ) (d : κ → ℂ) :
    𝔼 u, ‖v u - ∑ j, d j * e j u‖ ^ 2 =
      𝔼 u, ‖v u‖ ^ 2 - ∑ j, ‖uinner v (e j)‖ ^ 2 + ∑ j, ‖d j - uinner v (e j)‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_expect, Complex.ofReal_sum,
    ey_normsq]
  have key : ∀ u, (v u - ∑ j, d j * e j u) * star (v u - ∑ j, d j * e j u) =
      v u * star (v u) - ∑ k, star (d k) * (v u * star (e k u)) -
        ∑ j, d j * (e j u * star (v u)) +
        ∑ j, ∑ k, (d j * star (d k)) * (e j u * star (e k u)) := by
    intro u
    have h1 : v u * star (∑ k, d k * e k u) = ∑ k, star (d k) * (v u * star (e k u)) := by
      rw [star_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [star_mul']; ring
    have h2 : (∑ j, d j * e j u) * star (v u) = ∑ j, d j * (e j u * star (v u)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : (∑ j, d j * e j u) * star (∑ k, d k * e k u) =
        ∑ j, ∑ k, (d j * star (d k)) * (e j u * star (e k u)) := by
      rw [star_sum, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
        rw [star_mul']; ring
    rw [star_sub, sub_mul, mul_sub, mul_sub, h1, h2, h3]
    ring
  simp only [key]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, Finset.expect_sub_distrib]
  simp only [Finset.expect_sum_comm, ← Finset.mul_expect]
  have hu : ∀ k, (𝔼 u, v u * star (e k u)) = uinner v (e k) := fun k => rfl
  have hu' : ∀ j, (𝔼 u, e j u * star (v u)) = star (uinner v (e j)) := fun j => by
    rw [← ey_uinner_symm]; rfl
  have hee : ∀ j k, (𝔼 u, e j u * star (e k u)) = if j = k then 1 else 0 := fun j k => he j k
  simp only [hu, hu', hee, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  have h4 : ∀ j, (d j - uinner v (e j)) * star (d j - uinner v (e j)) =
      d j * star (d j) - star (d j) * uinner v (e j) - d j * star (uinner v (e j)) +
        uinner v (e j) * star (uinner v (e j)) := fun j => by
    rw [star_sub]; ring
  simp only [h4, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private lemma ey_lower {T κ : Type*} [Fintype T] [Fintype κ] [DecidableEq κ]
    (e : κ → T → ℂ) (he : ∀ i j, uinner (e i) (e j) = if i = j then 1 else 0)
    (v : T → ℂ) (d : κ → ℂ) :
    𝔼 u, ‖v u‖ ^ 2 - ∑ j, ‖uinner v (e j)‖ ^ 2 ≤ 𝔼 u, ‖v u - ∑ j, d j * e j u‖ ^ 2 := by
  rw [ey_identity e he v d]
  have : 0 ≤ ∑ j, ‖d j - uinner v (e j)‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

private lemma ey_bessel {T κ : Type*} [Fintype T] [Fintype κ] [DecidableEq κ]
    (e : κ → T → ℂ) (he : ∀ i j, uinner (e i) (e j) = if i = j then 1 else 0) (v : T → ℂ) :
    ∑ j, ‖uinner v (e j)‖ ^ 2 ≤ 𝔼 u, ‖v u‖ ^ 2 := by
  have h := ey_identity e he v (fun j => uinner v (e j))
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero] at h
  have : 0 ≤ 𝔼 u, ‖v u - ∑ j, uinner v (e j) * e j u‖ ^ 2 :=
    Finset.expect_nonneg fun u _ => sq_nonneg _
  linarith

private lemma ey_parseval {T κ : Type*} [Fintype T] [Fintype κ] [DecidableEq κ]
    (e : κ → T → ℂ) (he : ∀ i j, uinner (e i) (e j) = if i = j then 1 else 0) (d : κ → ℂ) :
    𝔼 u, ‖∑ j, d j * e j u‖ ^ 2 = ∑ j, ‖d j‖ ^ 2 := by
  have h := ey_identity e he (fun _ => 0) d
  have h0 : ∀ j, uinner (fun _ : T => (0 : ℂ)) (e j) = 0 := fun j => by simp [uinner]
  simp only [h0, zero_sub, norm_neg, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.expect_const_zero, Finset.sum_const_zero, zero_add] at h
  exact h

private lemma ey_l2_eq_one {T : Type*} [Fintype T] (v : T → ℂ) (hv : uinner v v = 1) :
    𝔼 u, ‖v u‖ ^ 2 = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_expect, Complex.ofReal_one, ← hv]
  simp only [ey_normsq]
  rfl

/-- an orthonormal family (expectation inner product) of at most `|κ|` vectors spanning the `Hₖ`. -/
private lemma ey_onb {T κ : Type*} [Fintype T] [Fintype κ] (H : κ → T → ℂ) :
    ∃ (m : ℕ) (e : Fin m → T → ℂ), m ≤ Fintype.card κ ∧
      (∀ i j, uinner (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ k, ∃ c : Fin m → ℂ, ∀ u, H k u = ∑ j, c j * e j u := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨0, fun i => Fin.elim0 i, Nat.zero_le _, fun i => Fin.elim0 i,
      fun k => ⟨fun i => Fin.elim0 i, fun u => (IsEmpty.false u).elim⟩⟩
  let V : Submodule ℂ (EuclideanSpace ℂ T) :=
    Submodule.span ℂ (Set.range fun k => WithLp.toLp 2 (H k))
  let b := stdOrthonormalBasis ℂ V
  have hcard : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  let s : ℂ := ((Real.sqrt (Fintype.card T) : ℝ) : ℂ)
  have hs : s * star s = (Fintype.card T : ℂ) := by
    simp only [s, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hcard.le]
    simp
  have hs0 : s ≠ 0 := by
    simp only [s, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.2 hcard).ne'
  refine ⟨Module.finrank ℂ V, fun j u => s * ((b j : EuclideanSpace ℂ T)).ofLp u,
    finrank_range_le_card _, ?_, ?_⟩
  · intro i j
    have horth := orthonormal_iff_ite.mp b.orthonormal j i
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at horth
    unfold uinner
    have : (𝔼 u, s * (b i : EuclideanSpace ℂ T).ofLp u *
        star (s * (b j : EuclideanSpace ℂ T).ofLp u)) =
        (s * star s) * ((∑ u, (b i : EuclideanSpace ℂ T).ofLp u *
          star ((b j : EuclideanSpace ℂ T).ofLp u)) / (Fintype.card T : ℂ)) := by
      rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Finset.sum_div, Finset.sum_div,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [star_mul']
      ring
    rw [this, hs]
    have hdot : (∑ u, (b i : EuclideanSpace ℂ T).ofLp u *
        star ((b j : EuclideanSpace ℂ T).ofLp u)) =
        (b i : EuclideanSpace ℂ T).ofLp ⬝ᵥ star ((b j : EuclideanSpace ℂ T).ofLp) := rfl
    rw [hdot, horth]
    have hc : (Fintype.card T : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
    by_cases hij : i = j
    · subst hij; simp [hc]
    · simp [hij, Ne.symm hij]
  · intro k
    have hmem : WithLp.toLp 2 (H k) ∈ V := Submodule.subset_span ⟨k, rfl⟩
    refine ⟨fun j => b.repr ⟨_, hmem⟩ j / s, fun u => ?_⟩
    have hsum := b.sum_repr ⟨_, hmem⟩
    have h2 := congrArg (fun x : V => ((x : EuclideanSpace ℂ T)).ofLp u) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

/-- a rearrangement bound: weights in `[0, 1]` with total mass `≤ t` against a decreasing sequence. -/
private lemma ey_knapsack {r : ℕ} (μ : Fin r → ℝ) (hμ : Antitone μ) (hμ0 : ∀ i, 0 ≤ μ i)
    (w : Fin r → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (t : ℕ)
    (hwt : ∑ i, w i ≤ t) :
    ∑ i, μ i * w i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), μ i := by
  by_cases ht : r ≤ t
  · have hf : Finset.univ.filter (fun i : Fin r => i.val < t) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.2 ht
    rw [hf]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (hw1 i) (hμ0 i)
      linarith
  push Not at ht
  set i₀ : Fin r := ⟨t, ht⟩
  set c := μ i₀
  have hc0 : 0 ≤ c := hμ0 i₀
  have hcard : (Finset.univ.filter (fun i : Fin r => i.val < t)).card = t := by
    have : Finset.univ.filter (fun i : Fin r => i.val < t) = Finset.Iio i₀ := by
      ext i; simp [Fin.lt_def, i₀]
    rw [this, Fin.card_Iio]
  have key : ∀ i, μ i * w i ≤ (if i.val < t then μ i else 0) +
      c * (w i - if i.val < t then 1 else 0) := by
    intro i
    by_cases hi : i.val < t
    · have hle : i ≤ i₀ := Fin.le_def.2 (le_of_lt hi)
      have h1 : c ≤ μ i := hμ hle
      simp only [hi, ↓reduceIte]
      nlinarith [hw1 i]
    · have hle : i₀ ≤ i := Fin.le_def.2 (not_lt.1 hi)
      have h1 : μ i ≤ c := hμ hle
      simp only [hi, ↓reduceIte]
      nlinarith [hw0 i]
  calc ∑ i, μ i * w i ≤ ∑ i, ((if i.val < t then μ i else 0) +
        c * (w i - if i.val < t then 1 else 0)) := Finset.sum_le_sum fun i _ => key i
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), μ i +
        c * (∑ i, w i - t) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter]
      congr 2
      rw [← Finset.sum_filter, Finset.sum_const, hcard]
      simp
    _ ≤ _ := by nlinarith

/-- Eckart-Young for an arbitrary finite index type of the approximant. -/
private theorem ey_gen {S T κ : Type*} [Fintype S] [Fintype T] [Fintype κ] (M : S → T → ℂ)
    {r : ℕ} {lam : Fin r → ℝ} {g : Fin r → S → ℂ} {h : Fin r → T → ℂ} (hM : IsSVD M r lam g h)
    (t : ℕ) (hκ : Fintype.card κ ≤ t) (a : κ → ℂ) (G : κ → S → ℂ) (H : κ → T → ℂ) :
    matL2sq (fun s u => M s u -
        ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), (lam i : ℂ) * g i s * h i u) ≤
      matL2sq (fun s u => M s u - ∑ k, a k * G k s * H k u) := by
  classical
  obtain ⟨m, e, hm, he, hspan⟩ := ey_onb H
  choose C hC using hspan
  -- the projection bound, row by row
  have hrow : ∀ s, 𝔼 u, ‖M s u‖ ^ 2 - ∑ j, ‖uinner (M s) (e j)‖ ^ 2 ≤
      𝔼 u, ‖M s u - ∑ k, a k * G k s * H k u‖ ^ 2 := by
    intro s
    have hX : ∀ u, ∑ k, a k * G k s * H k u = ∑ j, (∑ k, a k * G k s * C k j) * e j u := by
      intro u
      simp_rw [hC, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hX]
    exact ey_lower e he (M s) _
  -- `⟨M s, eⱼ⟩` in the SVD coordinates
  have hMe : ∀ s j, uinner (M s) (e j) = ∑ i, ((lam i : ℂ) * uinner (h i) (e j)) * g i s := by
    intro s j
    unfold uinner
    simp_rw [hM.decomp s, Finset.sum_mul]
    rw [Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_expect, Finset.expect_mul]
    refine Finset.expect_congr rfl fun u _ => ?_
    ring
  have hpars : ∀ j, 𝔼 s, ‖uinner (M s) (e j)‖ ^ 2 =
      ∑ i, lam i ^ 2 * ‖uinner (h i) (e j)‖ ^ 2 := by
    intro j
    simp_rw [hMe]
    rw [ey_parseval g hM.orth_g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the weights
  set w : Fin r → ℝ := fun i => ∑ j, ‖uinner (h i) (e j)‖ ^ 2 with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hw1 : ∀ i, w i ≤ 1 := fun i => by
    have := ey_bessel e he (h i)
    rwa [ey_l2_eq_one (h i) (by simp [hM.orth_h i i])] at this
  have hwt : ∑ i, w i ≤ t := by
    calc ∑ i, w i = ∑ j, ∑ i, ‖uinner (e j) (h i)‖ ^ 2 := by
          rw [hw, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [ey_uinner_symm (h i) (e j), norm_star]
      _ ≤ ∑ _j : Fin m, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
          have := ey_bessel h hM.orth_h (e j)
          rwa [ey_l2_eq_one (e j) (by simp [he j j])] at this
      _ = m := by simp
      _ ≤ t := by exact_mod_cast hm.trans hκ
  have hknap := ey_knapsack (fun i => lam i ^ 2)
    (fun i j hij => pow_le_pow_left₀ (hM.pos j).le (hM.antitone hij) 2)
    (fun i => sq_nonneg _) w hw0 hw1 t hwt
  -- the left side
  have hL : matL2sq (fun s u => M s u -
      ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), (lam i : ℂ) * g i s * h i u) =
      ∑ i, lam i ^ 2 - ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), lam i ^ 2 := by
    have hfun : ∀ s u, M s u -
        ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), (lam i : ℂ) * g i s * h i u =
        ∑ i, ((if i.val < t then (0 : ℂ) else (lam i : ℂ)) * g i s) * h i u := by
      intro s u
      rw [hM.decomp s u, Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    unfold matL2sq
    simp_rw [hfun]
    simp_rw [ey_parseval h hM.orth_h]
    simp_rw [norm_mul, mul_pow]
    rw [Finset.expect_sum_comm]
    have hg1 : ∀ i, 𝔼 s, ‖g i s‖ ^ 2 = 1 := fun i => ey_l2_eq_one (g i) (by simp [hM.orth_g i i])
    simp_rw [← Finset.mul_expect, hg1, mul_one]
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [Complex.norm_real, sq_abs]
  -- assembly
  have hR : ∑ i, lam i ^ 2 - ∑ i, lam i ^ 2 * w i ≤
      matL2sq (fun s u => M s u - ∑ k, a k * G k s * H k u) := by
    have h1 : 𝔼 s, (𝔼 u, ‖M s u‖ ^ 2 - ∑ j, ‖uinner (M s) (e j)‖ ^ 2) ≤
        matL2sq (fun s u => M s u - ∑ k, a k * G k s * H k u) :=
      Finset.expect_le_expect fun s _ => hrow s
    rw [Finset.expect_sub_distrib, Finset.expect_sum_comm] at h1
    simp_rw [hpars] at h1
    rw [Finset.sum_comm] at h1
    have h2 : (𝔼 s, 𝔼 u, ‖M s u‖ ^ 2) = ∑ i, lam i ^ 2 := hM.sum_sq_lam.symm
    rw [h2] at h1
    simpa [hw, Finset.mul_sum] using h1
  rw [hL]
  linarith

/-- The classical Eckart-Young theorem (Frobenius norm, expectation normalisation): the first `t` terms of an
SVD are a best approximation among all sums of `t` products. -/
theorem eckart_young {S T : Type*} [Fintype S] [Fintype T] (M : S → T → ℂ) {r : ℕ}
    {lam : Fin r → ℝ} {g : Fin r → S → ℂ} {h : Fin r → T → ℂ} (hM : IsSVD M r lam g h) (t : ℕ)
    (a : Fin t → ℂ) (G : Fin t → S → ℂ) (H : Fin t → T → ℂ) :
    matL2sq (fun s u => M s u -
        ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < t), (lam i : ℂ) * g i s * h i u) ≤
      matL2sq (fun s u => M s u - ∑ i : Fin t, a i * G i s * H i u) :=
  ey_gen M hM t (le_of_eq (Fintype.card_fin t)) a G H

/-! ### The restricted comparison -/

private lemma it_glue_restrS {β : Type} (S : Finset ι) (u : ↥S → β) (v : ↥Sᶜ → β) :
    (fun i : ↥S => glueFree S u v i) = u := by
  funext i; simp [glueFree, i.2]

private lemma it_glue_restrT {β : Type} (S : Finset ι) (u : ↥S → β) (v : ↥Sᶜ → β) :
    (fun i : ↥Sᶜ => glueFree S u v i) = v := by
  funext i
  have : (i : ι) ∉ S := Finset.mem_compl.1 i.2
  simp [glueFree, this]

omit [Fintype α] [DecidableEq α] in
private lemma it_prodSplit_glue (S : Finset ι) (g : (↥S → α) → ℂ) (h : (↥Sᶜ → α) → ℂ)
    (u : ↥S → α) (v : ↥Sᶜ → α) : prodSplit S g h (glueFree S u v) = g u * h v := by
  simp only [prodSplit, it_glue_restrS, it_glue_restrT]

omit [Fintype α] [DecidableEq α] [Fintype ι] in
/-- membership in the sets of one step. -/
private lemma it_mem_step (st : SwapIterState ι α) (hSR : st.S ⊆ st.R) (c : SwapCoins ι α)
    (i : ι) :
    (i ∈ (swapIterStep st c).S ↔ i ∈ st.S ∧ c.1 i = true) ∧
    (i ∈ swapIterPart st c ↔ i ∈ st.R ∧ c.1 i = true) ∧
    (i ∈ st.R \ (swapIterStep st c).R ↔
      i ∈ st.R ∧ ((i ∈ st.S ∧ c.1 i = false) ∨ (i ∉ st.S ∧ c.1 i = true))) := by
  have hSRi := @hSR i
  refine ⟨by simp [swapIterStep], by simp [swapIterPart], ?_⟩
  by_cases hR : i ∈ st.R <;> by_cases hS : i ∈ st.S <;> cases hc : c.1 i <;>
    simp_all [swapIterStep]

/-- the `S_t`-matrix of `Δ_t`. -/
private lemma it_jMatrix_delta (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (st : SwapIterState ι α) (t : ℕ) :
    jMatrix st.S (swapIterDelta sel f st t) = fun p q =>
      jMatrix st.S (swapIterF f st) p q -
        ∑ i ∈ Finset.univ.filter (fun i : Fin (sel st.S (swapIterF f st)).r => i.val < t),
          ((sel st.S (swapIterF f st)).lam i : ℂ) * (sel st.S (swapIterF f st)).g i p *
            (sel st.S (swapIterF f st)).h i q := by
  funext p q
  simp only [jMatrix, swapIterDelta, SwapSvdData.trunc, SwapSvdData.truncOn,
    it_prodSplit_glue, mul_assoc]

private lemma it_card_filter_lt (r t : ℕ) :
    (Finset.univ.filter (fun i : Fin r => i.val < t)).card ≤ t := by
  have := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun i : Fin r => i.val < t))
    (t := Finset.range t) (fun i => i.val)
    (fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2)
    (fun i _ j _ hij => Fin.ext hij)
  simpa using this

/-- CSP_6 `lemma:iter#restricted-svd-comparison`. -/
theorem swapIter_restricted_comparison (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (st : SwapIterState ι α) (hSR : st.S ⊆ st.R) (t : ℕ) (c : SwapCoins ι α) (a : ℂ)
    (G : (↥(swapIterPart st c) → α) → ℂ) (H : (↥(swapIterPart st c)ᶜ → α) → ℂ) :
    l2sq (swapIterDelta sel f (swapIterStep st c) (t + 1)) ≤
      l2sq (fun x =>
        swapIterDelta sel f st t
            (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else x i) -
          a * prodSplit (swapIterPart st c) G H
            (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else x i)) := by
  classical
  have hmem := it_mem_step st hSR c
  -- membership facts (`S₁ = S_{t+1}`, `P = S'`, `I = R_t \ R_{t+1}`)
  have hS₁S : ∀ i, i ∈ (swapIterStep st c).S → i ∈ st.S := fun i hi => ((hmem i).1.1 hi).1
  have hS₁I : ∀ i, i ∈ (swapIterStep st c).S → i ∉ st.R \ (swapIterStep st c).R :=
    fun i hi hiI => by
      have h1 := (hmem i).1.1 hi
      have h2 := (hmem i).2.2.1 hiI
      rcases h2.2 with h | h
      · rw [h1.2] at h; exact absurd h.2 (by decide)
      · exact h.1 h1.1
  have hSI : ∀ i, i ∈ st.S → i ∉ (swapIterStep st c).S → i ∈ st.R \ (swapIterStep st c).R :=
    fun i hi hi1 => by
      refine (hmem i).2.2.2 ⟨hSR hi, Or.inl ⟨hi, ?_⟩⟩
      cases hc : c.1 i
      · rfl
      · exact absurd ((hmem i).1.2 ⟨hi, hc⟩) hi1
  have hS₁P : ∀ i, i ∈ (swapIterStep st c).S → i ∈ swapIterPart st c := fun i hi => by
    have h1 := (hmem i).1.1 hi
    exact (hmem i).2.1.2 ⟨hSR h1.1, h1.2⟩
  have hPI : ∀ i, i ∈ swapIterPart st c → i ∉ (swapIterStep st c).S →
      i ∈ st.R \ (swapIterStep st c).R := fun i hi hi1 => by
    have h1 := (hmem i).2.1.1 hi
    exact (hmem i).2.2.2 ⟨h1.1, Or.inr ⟨fun hS => hi1 ((hmem i).1.2 ⟨hS, h1.2⟩), h1.2⟩⟩
  -- the factors of the peeled terms after fixing `I`
  let rS : (↥(swapIterStep st c).S → α) → (↥st.S → α) := fun p j =>
    if hj : (j : ι) ∈ (swapIterStep st c).S then p ⟨j, hj⟩ else c.2 j
  let rSc : (↥(swapIterStep st c).Sᶜ → α) → (↥st.Sᶜ → α) := fun q j =>
    if (j : ι) ∈ st.R \ (swapIterStep st c).R then c.2 j else
      q ⟨j, Finset.mem_compl.2 fun h => (Finset.mem_compl.1 j.2) (hS₁S _ h)⟩
  let rP : (↥(swapIterStep st c).S → α) → (↥(swapIterPart st c) → α) := fun p j =>
    if hj : (j : ι) ∈ (swapIterStep st c).S then p ⟨j, hj⟩ else c.2 j
  let rPc : (↥(swapIterStep st c).Sᶜ → α) → (↥(swapIterPart st c)ᶜ → α) := fun q j =>
    if (j : ι) ∈ st.R \ (swapIterStep st c).R then c.2 j else
      q ⟨j, Finset.mem_compl.2 fun h => (Finset.mem_compl.1 j.2) (hS₁P _ h)⟩
  have e1 : ∀ p q, (fun j : ↥st.S =>
      (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else
        glueFree (swapIterStep st c).S p q i) (j : ι)) = rS p := by
    intro p q; funext j
    by_cases hj : (j : ι) ∈ (swapIterStep st c).S
    · simp [rS, hj, hS₁I _ hj, glueFree]
    · simp [rS, hj, hSI _ j.2 hj]
  have e2 : ∀ p q, (fun j : ↥st.Sᶜ =>
      (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else
        glueFree (swapIterStep st c).S p q i) (j : ι)) = rSc q := by
    intro p q; funext j
    have hj : (j : ι) ∉ (swapIterStep st c).S := fun h => (Finset.mem_compl.1 j.2) (hS₁S _ h)
    by_cases hjI : (j : ι) ∈ st.R \ (swapIterStep st c).R
    · simp only [rSc, ite_eq_left hjI]
    · simp only [rSc, ite_eq_right hjI, glueFree, dite_eq_right hj]
  have e3 : ∀ p q, (fun j : ↥(swapIterPart st c) =>
      (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else
        glueFree (swapIterStep st c).S p q i) (j : ι)) = rP p := by
    intro p q; funext j
    by_cases hj : (j : ι) ∈ (swapIterStep st c).S
    · simp [rP, hj, hS₁I _ hj, glueFree]
    · simp [rP, hj, hPI _ j.2 hj]
  have e4 : ∀ p q, (fun j : ↥(swapIterPart st c)ᶜ =>
      (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else
        glueFree (swapIterStep st c).S p q i) (j : ι)) = rPc q := by
    intro p q; funext j
    have hj : (j : ι) ∉ (swapIterStep st c).S := fun h => (Finset.mem_compl.1 j.2) (hS₁P _ h)
    by_cases hjI : (j : ι) ∈ st.R \ (swapIterStep st c).R
    · simp only [rPc, ite_eq_left hjI]
    · simp only [rPc, ite_eq_right hjI, glueFree, dite_eq_right hj]
  -- Eckart-Young for the `S₁`-matrix of `f_{t+1}` with `t + 1` products
  let F := Finset.univ.filter (fun i : Fin (sel st.S (swapIterF f st)).r => i.val < t)
  have hκ : Fintype.card (Option ↥F) ≤ t + 1 := by
    rw [Fintype.card_option, Fintype.card_coe]
    exact Nat.add_le_add_right (it_card_filter_lt _ t) 1
  let A : Option ↥F → ℂ := fun o =>
    Option.elim o a fun i => ((sel st.S (swapIterF f st)).lam i : ℂ)
  let G' : Option ↥F → (↥(swapIterStep st c).S → α) → ℂ := fun o p =>
    Option.elim o (G (rP p)) fun i => (sel st.S (swapIterF f st)).g i (rS p)
  let H' : Option ↥F → (↥(swapIterStep st c).Sᶜ → α) → ℂ := fun o q =>
    Option.elim o (H (rPc q)) fun i => (sel st.S (swapIterF f st)).h i (rSc q)
  have key := ey_gen (jMatrix (swapIterStep st c).S (swapIterF f (swapIterStep st c)))
    (sel (swapIterStep st c).S (swapIterF f (swapIterStep st c))).isJSVD (t + 1) hκ A G' H'
  have hstep := swapIterF_step f st hSR c
  rw [← matL2sq_jMatrix (swapIterStep st c).S, ← matL2sq_jMatrix (swapIterStep st c).S]
  have hL := it_jMatrix_delta sel f (swapIterStep st c) (t + 1)
  have hR : jMatrix (swapIterStep st c).S (fun x =>
        swapIterDelta sel f st t
            (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else x i) -
          a * prodSplit (swapIterPart st c) G H
            (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else x i)) = fun p q =>
      jMatrix (swapIterStep st c).S (swapIterF f (swapIterStep st c)) p q -
        ∑ o, A o * G' o p * H' o q := by
    funext p q
    rw [Fintype.sum_option]
    have h1 : swapIterF f st (fun i => if i ∈ st.R \ (swapIterStep st c).R then c.2 i else
        glueFree (swapIterStep st c).S p q i) =
        swapIterF f (swapIterStep st c) (glueFree (swapIterStep st c).S p q) := by rw [hstep]
    simp only [jMatrix, swapIterDelta, SwapSvdData.trunc, SwapSvdData.truncOn, prodSplit, h1,
      e1, e2, e3, e4, A, G', H', Option.elim]
    rw [Finset.sum_coe_sort F (fun i => ((sel st.S (swapIterF f st)).lam i : ℂ) *
      (sel st.S (swapIterF f st)).g i (rS p) * (sel st.S (swapIterF f st)).h i (rSc q))]
    have h2 : ∑ i ∈ F, ((sel st.S (swapIterF f st)).lam i : ℂ) *
        ((sel st.S (swapIterF f st)).g i (rS p) * (sel st.S (swapIterF f st)).h i (rSc q)) =
        ∑ i ∈ F, ((sel st.S (swapIterF f st)).lam i : ℂ) *
          (sel st.S (swapIterF f st)).g i (rS p) * (sel st.S (swapIterF f st)).h i (rSc q) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    ring
  rw [hL, hR]
  exact key

/-! ### `lemma:iter` -/

private def itSplitEquiv {β : Type} (S : Finset ι) : (ι → β) ≃ (↥S → β) × (↥Sᶜ → β) where
  toFun x := (fun i => x i, fun i => x i)
  invFun p := glueFree S p.1 p.2
  left_inv x := by
    funext i; by_cases h : i ∈ S <;> simp [glueFree, h]
  right_inv := by
    rintro ⟨y, z⟩
    exact Prod.ext (it_glue_restrS S y z) (it_glue_restrT S y z)

private lemma it_expect_split {β : Type} [Fintype β] {M : Type*} [AddCommMonoid M]
    [Module ℚ≥0 M] (S : Finset ι) (h : (ι → β) → M) :
    𝔼 x : ι → β, h x = 𝔼 u : ↥S → β, 𝔼 v : ↥Sᶜ → β, h (glueFree S u v) := by
  rw [← Finset.expect_product' (f := fun u v => h (glueFree S u v)), Finset.univ_product_univ]
  exact Fintype.expect_equiv (itSplitEquiv S) _ _
    (fun x => congrArg h ((itSplitEquiv S).symm_apply_apply x).symm)

omit [DecidableEq α] in
/-- the uniform law of `w` restricted to `I` is uniform. -/
private lemma it_marginal (I : Finset ι) (Φ : (↥I → α) → ℝ) (w₀ : ι → α) :
    𝔼 w : ι → α, Φ (fun i : ↥I => w i) = 𝔼 z : ↥I → α, Φ z := by
  have : Nonempty (↥Iᶜ → α) := ⟨fun i => w₀ i⟩
  rw [it_expect_split I]
  refine Finset.expect_congr rfl fun u _ => ?_
  simp only [it_glue_restrS]
  exact Fintype.expect_const _

omit [Fintype α] [DecidableEq α] in
/-- fixing the coordinates of `I` to `w` as a restriction. -/
private lemma it_fix_eq (F : (ι → α) → ℂ) (I : Finset ι) (w : ι → α) :
    (fun x => F (fun i => if i ∈ I then w i else x i)) =
      prodSplit Iᶜ (restrictFix I (fun i : ↥I => w i) F) (fun _ => 1) := by
  funext x
  simp only [prodSplit, restrictFix, mul_one]
  congr 1

omit [DecidableEq α] in
private lemma it_fix_l2sq (F : (ι → α) → ℂ) (I : Finset ι) (w : ι → α) :
    l2sq (fun x => F (fun i => if i ∈ I then w i else x i)) =
      l2sq (restrictFix I (fun i : ↥I => w i) F) := by
  have : Nonempty (↥Iᶜᶜ → α) := ⟨fun i => w i⟩
  rw [it_fix_eq, l2sq, l2sq, it_expect_split Iᶜ, Finset.expect_comm]
  simp only [prodSplit, it_glue_restrS, mul_one]
  exact Fintype.expect_const _

omit [DecidableEq α] in
private lemma it_fix_val (F : (ι → α) → ℂ) (I : Finset ι) (w : ι → α) :
    val (fun x => F (fun i => if i ∈ I then w i else x i))
        (fun x => F (fun i => if i ∈ I then w i else x i))
        (fun x => F (fun i => if i ∈ I then w i else x i))
        (fun x => F (fun i => if i ∈ I then w i else x i)) =
      val (restrictFix I (fun i : ↥I => w i) F) (restrictFix I (fun i : ↥I => w i) F)
        (restrictFix I (fun i : ↥I => w i) F) (restrictFix I (fun i : ↥I => w i) F) := by
  have : Nonempty (↥Iᶜᶜ → α) := ⟨fun i => w i⟩
  rw [it_fix_eq, val_prodSplit]
  have h1 : val (fun _ : ↥Iᶜᶜ → α => (1 : ℂ)) (fun _ => 1) (fun _ => 1) (fun _ => 1) = 1 := by
    simp [val]
  rw [h1, mul_one]

private lemma it_l2sq_le_of_bound {κ β : Type} [Fintype κ] [DecidableEq κ] [Fintype β]
    [DecidableEq β] (F : (κ → β) → ℂ) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) : l2sq F ≤ B ^ 2 := by
  rw [l2sq]
  rcases isEmpty_or_nonempty (κ → β) with hn | hn
  · simp only [Finset.univ_eq_empty, Finset.expect_empty]
    positivity
  · calc 𝔼 x : κ → β, ‖F x‖ ^ 2 ≤ 𝔼 _x : κ → β, B ^ 2 :=
          Finset.expect_le_expect (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)
      _ = B ^ 2 := Fintype.expect_const _

private lemma it_val_rpow_half_le_l2sq {κ β : Type} [Fintype κ] [DecidableEq κ] [Fintype β]
    [DecidableEq β] (F : (κ → β) → ℂ) : ((val F F F F).re) ^ (1 / 2 : ℝ) ≤ l2sq F := by
  rw [← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_iff.2 ⟨l2sq_nonneg F, ?_⟩
  refine (Complex.re_le_norm _).trans ((norm_val_le F F F F).trans_eq ?_)
  have h2 : Real.sqrt (l2sq F) * Real.sqrt (l2sq F) = l2sq F :=
    Real.mul_self_sqrt (l2sq_nonneg F)
  calc _ = (Real.sqrt (l2sq F) * Real.sqrt (l2sq F)) *
        (Real.sqrt (l2sq F) * Real.sqrt (l2sq F)) := by ring
    _ = _ := by rw [h2]; ring

open scoped Classical in
/-- reverse Markov: a variable bounded by `M` with mean `≥ 2a` exceeds `a` with probability
`≥ a / M`. -/
private lemma it_averaging {κ : Type} [Fintype κ] (X : κ → ℝ) (a M : ℝ) (ha : 0 < a)
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

/-- the singular vectors `hᵢ` of `f_t` ignore the coordinates outside `R_t`. -/
private lemma it_h_congr (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) (st : SwapIterState ι α)
    (i : Fin (sel st.S (swapIterF f st)).r) (u v : ↥st.Sᶜ → α)
    (huv : ∀ j : ↥st.Sᶜ, (j : ι) ∈ st.R → u j = v j) :
    (sel st.S (swapIterF f st)).h i u = (sel st.S (swapIterF f st)).h i v := by
  have hd := (sel st.S (swapIterF f st)).isJSVD
  have hu := (hd.singular_pair i).2 u
  have hv := (hd.singular_pair i).2 v
  have hM : ∀ p, jMatrix st.S (swapIterF f st) p u = jMatrix st.S (swapIterF f st) p v := by
    intro p
    simp only [jMatrix, swapIterF, swapIterFun]
    congr 1
    funext k
    by_cases hk : k ∈ st.R
    · simp only [hk, ↓reduceIte, glueFree]
      split_ifs with hkS
      · rfl
      · exact huv ⟨k, Finset.mem_compl.2 hkS⟩ hk
    · simp only [hk, ↓reduceIte]
  simp_rw [hM] at hu
  have hl : ((sel st.S (swapIterF f st)).lam i : ℂ) ≠ 0 := by
    exact_mod_cast (hd.pos i).ne'
  exact mul_left_cancel₀ hl (hu.symm.trans hv)

/-- `Δ_t` ignores the coordinates outside `R_t`. -/
private lemma it_delta_congr (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (st : SwapIterState ι α) (hSR : st.S ⊆ st.R) (t : ℕ) (x y : ι → α)
    (hxy : ∀ i ∈ st.R, x i = y i) :
    swapIterDelta sel f st t x = swapIterDelta sel f st t y := by
  simp only [swapIterDelta, SwapSvdData.trunc, SwapSvdData.truncOn, prodSplit]
  congr 1
  · simp only [swapIterF, swapIterFun]
    congr 1
    funext i
    split_ifs with h
    · exact hxy i h
    · rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hg : (fun j : ↥st.S => x j) = (fun j : ↥st.S => y j) := by
      funext j; exact hxy j (hSR j.2)
    rw [hg, it_h_congr sel f st i _ _ (fun j hj => hxy j hj)]

/-- `𝔼_{S'} box_{S'} = val` for the uniform part `S' = R ∩ {b}` and a function ignoring `Rᶜ`. -/
private lemma it_expect_box_part (R : Finset ι) (F : (ι → α) → ℂ)
    (hF : ∀ x y : ι → α, (∀ i ∈ R, x i = y i) → F x = F y) :
    𝔼 b : ι → Bool, box (R.filter fun i => b i = true) F F F F = val F F F F := by
  have hL : ∀ (b : ι → Bool) (x y : ι → α),
      F (swapL (ind (R.filter fun i => b i = true)) x y) = F (swapL b x y) := by
    intro b x y
    refine hF _ _ fun i hi => ?_
    simp [swapL, ind, hi]
  have hR : ∀ (b : ι → Bool) (x y : ι → α),
      F (swapR (ind (R.filter fun i => b i = true)) x y) = F (swapR b x y) := by
    intro b x y
    refine hF _ _ fun i hi => ?_
    simp [swapR, ind, hi]
  simp only [box_eq_swap, hL, hR]
  rw [val, Finset.expect_comm]
  refine Finset.expect_congr rfl (fun x _ => Finset.expect_comm _ _ _)

/-- `∑ κᵢ⁴ ≤ κ₁² ∑ κᵢ²` (unnormalised form of `box_svd_pow4_le_top`). -/
private lemma it_pow4_le_top (S : Finset ι) (F : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥S → α) → ℂ} {h : Fin r → (↥Sᶜ → α) → ℂ}
    (hsvd : IsJSVD S F r lam g h) (hr : 0 < r) :
    ∑ i, lam i ^ 4 ≤ lam ⟨0, hr⟩ ^ 2 * l2sq F := by
  have hsum : ∑ i, lam i ^ 2 = l2sq F := by
    rw [hsvd.sum_sq_lam, matL2sq_jMatrix]
  calc ∑ i, lam i ^ 4 ≤ ∑ i, lam ⟨0, hr⟩ ^ 2 * lam i ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h0 : lam i ≤ lam ⟨0, hr⟩ := hsvd.antitone (Nat.zero_le _ : (⟨0, hr⟩ : Fin r) ≤ i)
        have hp := hsvd.pos i
        have : lam i ^ 2 ≤ lam ⟨0, hr⟩ ^ 2 := pow_le_pow_left₀ hp.le h0 2
        nlinarith [sq_nonneg (lam i)]
    _ = lam ⟨0, hr⟩ ^ 2 * l2sq F := by rw [← Finset.mul_sum, hsum]

/-- peeling the top singular triple off `F` lowers `‖F‖₂²` by `κ₁²`. -/
private lemma it_l2sq_peel (S : Finset ι) (F : (ι → α) → ℂ) {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → (↥S → α) → ℂ} {h : Fin r → (↥Sᶜ → α) → ℂ}
    (hsvd : IsJSVD S F r lam g h) (i : Fin r) :
    l2sq (fun x => F x - (lam i : ℂ) * prodSplit S (g i) (h i) x) = l2sq F - lam i ^ 2 := by
  rw [← matL2sq_jMatrix S, ← matL2sq_jMatrix S F, ← hsvd.matL2sq_sub_rank_one i]
  congr 1
  funext p q
  simp only [jMatrix, it_prodSplit_glue, mul_assoc]

/-- `‖Δ_t‖₂ ≤ ‖f_t‖₂` (Eckart-Young against the empty approximant). -/
private lemma it_l2sq_delta_le (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ)
    (st : SwapIterState ι α) (t : ℕ) :
    l2sq (swapIterDelta sel f st t) ≤ l2sq (swapIterF f st) := by
  rw [← matL2sq_jMatrix st.S, ← matL2sq_jMatrix st.S (swapIterF f st), it_jMatrix_delta]
  have := ey_gen (jMatrix st.S (swapIterF f st)) (sel st.S (swapIterF f st)).isJSVD t
    (κ := Fin 0) (by simp) 0 0 0
  simpa using this

/-- monotonicity of indicators. -/
private lemma it_ind_mono {A₁ A₂ : Prop} {d₁ : Decidable A₁} {d₂ : Decidable A₂} (h : A₁ → A₂) :
    (@ite ℝ A₁ d₁ 1 0) ≤ (@ite ℝ A₂ d₂ 1 0) := by
  by_cases hA : A₁
  · rw [ite_eq_left hA, ite_eq_left (h hA)]
  · rw [ite_eq_right hA]; split_ifs <;> norm_num

omit [DecidableEq α] in
/-- the coins of one step: the partition coins and the fixing values are independent. -/
private lemma it_expect_coins {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : SwapCoins ι α → M) :
    𝔼 c : SwapCoins ι α, F c = 𝔼 b : ι → Bool, 𝔼 w : ι → α, F (b, w) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

open scoped Classical in
/-- CSP_6 `lemma:iter`, with the corrected `phirr` and the probability made explicit. -/
theorem swapIter_step_success (sel : SwapSvdChoice ι α) (f : (ι → α) → ℂ) {B C γ : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hC : 1 < C) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (st : SwapIterState ι α) (hSR : st.S ⊆ st.R) (t : ℕ)
    (hstop : γ * l2sq (swapIterF f st) ≤
      ((val (swapIterDelta sel f st t) (swapIterDelta sel f st t) (swapIterDelta sel f st t)
        (swapIterDelta sel f st t)).re) ^ (1 / 2 : ℝ)) :
    γ ^ 4 * l2sq (swapIterF f st) / (36 * C * B ^ 2) ≤
      𝔼 c : SwapCoins ι α,
        if swapIterPhi C sel f st t + γ ^ 2 / 4 ≤ swapIterPhi C sel f (swapIterStep st c) (t + 1) ∧
          γ ^ 2 / (18 * C) * l2sq (swapIterF f st) ≤ l2sq (swapIterF f (swapIterStep st c))
        then (1 : ℝ) else 0 := by
  rcases (l2sq_nonneg (swapIterF f st)).eq_or_lt with hL0 | hLpos
  · rw [← hL0, mul_zero, zero_div]
    exact Finset.expect_nonneg fun c _ => by split_ifs <;> norm_num
  -- notation: `L = ‖f_t‖₂²`, `D = ‖Δ_t‖₂²`, `V = val(f_t)^{1/2}`
  obtain ⟨L, hLd⟩ : ∃ L, l2sq (swapIterF f st) = L := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D, l2sq (swapIterDelta sel f st t) = D := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V, ((val (swapIterF f st) (swapIterF f st) (swapIterF f st)
      (swapIterF f st)).re) ^ (1 / 2 : ℝ) = V := ⟨_, rfl⟩
  obtain ⟨w₀⟩ : Nonempty (ι → α) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [l2sq] at hLpos
  rw [hLd] at hLpos hstop
  rw [hLd]
  have hLB : L ≤ B ^ 2 := hLd ▸ it_l2sq_le_of_bound _ (fun x => hB _)
  have hDL : D ≤ L := hDd ▸ hLd ▸ it_l2sq_delta_le sel f st t
  have hD0 : 0 ≤ D := hDd ▸ l2sq_nonneg _
  have hvD := it_val_rpow_half_le_l2sq (swapIterDelta sel f st t)
  rw [hDd] at hvD
  have hv0 := val_re_nonneg_pair (swapIterDelta sel f st t) (swapIterDelta sel f st t)
  have hγL : 0 < γ * L := mul_pos hγ0 hLpos
  have hDpos : 0 < D := lt_of_lt_of_le (lt_of_lt_of_le hγL hstop) hvD
  have hvsq : (γ * L) ^ 2 ≤ (val (swapIterDelta sel f st t) (swapIterDelta sel f st t)
      (swapIterDelta sel f st t) (swapIterDelta sel f st t)).re := by
    have h := pow_le_pow_left₀ hγL.le hstop 2
    rwa [← Real.sqrt_eq_rpow, Real.sq_sqrt hv0] at h
  have hB2 : 0 < B ^ 2 := lt_of_lt_of_le hLpos hLB
  have hC0 : 0 < C := by linarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hγ21 : γ ^ 2 ≤ 1 := by nlinarith
  -- first stage: the partition `S'` (Markov on `box_{S'}(Δ_t)`)
  let X : (ι → Bool) → ℝ := fun b =>
    (box (st.R.filter fun i => b i = true) (swapIterDelta sel f st t) (swapIterDelta sel f st t)
      (swapIterDelta sel f st t) (swapIterDelta sel f st t)).re
  have hXle : ∀ b, X b ≤ D ^ 2 := fun b => hDd ▸ box_self_le_l2sq_sq _ _
  have hEX : 𝔼 b, X b = (val (swapIterDelta sel f st t) (swapIterDelta sel f st t)
      (swapIterDelta sel f st t) (swapIterDelta sel f st t)).re := by
    rw [← it_expect_box_part st.R _ (it_delta_congr sel f st hSR t), Complex.re_expect]
  have hp1 : γ ^ 2 / 2 ≤ 𝔼 b, if γ ^ 2 * L ^ 2 / 2 ≤ X b then (1 : ℝ) else 0 := by
    have h := it_averaging X (γ ^ 2 * L ^ 2 / 2) (D ^ 2) (by positivity) hXle
      (by rw [hEX]; nlinarith [hvsq])
    refine le_trans ?_ h
    rw [le_div_iff₀ (by positivity)]
    have : D ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hD0 hDL 2
    nlinarith
  -- second stage: the restriction, for a fixed good partition
  set K : ℝ := γ ^ 2 * L / (18 * C * B ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hstage : ∀ b : ι → Bool, (if γ ^ 2 * L ^ 2 / 2 ≤ X b then (1 : ℝ) else 0) * K ≤
      𝔼 w : ι → α, if swapIterPhi C sel f st t + γ ^ 2 / 4 ≤
          swapIterPhi C sel f (swapIterStep st (b, w)) (t + 1) ∧
          γ ^ 2 / (18 * C) * L ≤ l2sq (swapIterF f (swapIterStep st (b, w)))
        then (1 : ℝ) else 0 := by
    intro b
    by_cases h1 : γ ^ 2 * L ^ 2 / 2 ≤ X b
    swap
    · rw [ite_eq_right h1, zero_mul]
      exact Finset.expect_nonneg fun w _ => by split_ifs <;> norm_num
    rw [ite_eq_left h1, one_mul]
    -- the top singular triple of `Δ_t` for the partition `S' = R_t ∩ {b}`
    let P : Finset ι := st.R.filter fun i => b i = true
    let dd := swapSvdChoice P (swapIterDelta sel f st t)
    have hsvd := dd.isJSVD
    have hXb : X b = ∑ i, dd.lam i ^ 4 := by
      simp only [X]
      rw [box_svd_eq_sum_pow4 P _ hsvd, Complex.ofReal_re]
    have hr : 0 < dd.r := by
      rcases Nat.eq_zero_or_pos dd.r with h | h
      · exfalso
        have : IsEmpty (Fin dd.r) := ⟨fun i => by have := i.2; omega⟩
        rw [hXb, Finset.univ_eq_empty, Finset.sum_empty] at h1
        have : 0 < γ ^ 2 * L ^ 2 / 2 := by positivity
        linarith
      · exact h
    have htop := it_pow4_le_top P _ hsvd hr
    rw [hDd, ← hXb] at htop
    set κ₁ := dd.lam ⟨0, hr⟩ with hκ₁
    have hκ : γ ^ 2 * L / 2 ≤ κ₁ ^ 2 := by
      by_contra hcon
      push Not at hcon
      have h2 : κ₁ ^ 2 * D < γ ^ 2 * L / 2 * D := mul_lt_mul_of_pos_right hcon hDpos
      have h3 : γ ^ 2 * L / 2 * D ≤ γ ^ 2 * L / 2 * L :=
        mul_le_mul_of_nonneg_left hDL (by positivity)
      nlinarith
    -- the peeled `Δ_t'`
    let Δ' : (ι → α) → ℂ := fun x => swapIterDelta sel f st t x -
      (κ₁ : ℂ) * prodSplit P (dd.g ⟨0, hr⟩) (dd.h ⟨0, hr⟩) x
    have hD' : l2sq Δ' = D - κ₁ ^ 2 := by
      rw [← hDd]; exact it_l2sq_peel P _ hsvd ⟨0, hr⟩
    have hD'le : l2sq Δ' ≤ D - γ ^ 2 * L / 2 := by rw [hD']; linarith
    have hD'0 : 0 ≤ l2sq Δ' := l2sq_nonneg _
    have hγL2 : 0 ≤ γ ^ 2 * L / 2 := by positivity
    have hr1 : l2sq Δ' / L ≤ 1 := (div_le_one hLpos).2 (by linarith)
    have hr0 : 0 ≤ l2sq Δ' / L := div_nonneg hD'0 hLpos.le
    have hden : C + 2 * (γ ^ 2 / 8) + l2sq Δ' / L ≤ 9 / 4 * C := by linarith
    have hden0 : 0 < C + 2 * (γ ^ 2 / 8) + l2sq Δ' / L := by linarith
    -- `I = R_t \ R_{t+1}` (a function of `b` only), and `lemma:phirr`
    let I : Finset ι := st.R \ ((st.S.filter fun i => b i = true) ∪
      ((st.R \ st.S).filter fun i => b i = false))
    have hph := phirr I (swapIterF f st) Δ' (fun x => hB _) hC
      (show (0 : ℝ) < γ ^ 2 / 8 by positivity)
    rw [hVd, hLd] at hph
    have hp2 : K ≤ γ ^ 2 / 8 * L / ((C + 2 * (γ ^ 2 / 8) + l2sq Δ' / L) * B ^ 2) := by
      rw [hK]
      have e : γ ^ 2 * L / (18 * C * B ^ 2) = γ ^ 2 / 8 * L / (9 / 4 * C * B ^ 2) := by
        field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hden hB2.le)
    refine hp2.trans (hph.trans (le_of_eq_of_le (it_marginal I _ w₀).symm ?_))
    refine Finset.expect_le_expect fun w _ => ?_
    -- on the event of `phirr`, the step succeeds
    have hF1 : swapIterF f (swapIterStep st (b, w)) =
        fun x => swapIterF f st (fun i => if i ∈ I then w i else x i) :=
      swapIterF_step f st hSR (b, w)
    have hLz : l2sq (swapIterF f (swapIterStep st (b, w))) =
        l2sq (restrictFix I (fun i : ↥I => w i) (swapIterF f st)) := by
      rw [hF1]; exact it_fix_l2sq _ I w
    have hVz : val (swapIterF f (swapIterStep st (b, w))) (swapIterF f (swapIterStep st (b, w)))
        (swapIterF f (swapIterStep st (b, w))) (swapIterF f (swapIterStep st (b, w))) =
        val (restrictFix I (fun i : ↥I => w i) (swapIterF f st))
          (restrictFix I (fun i : ↥I => w i) (swapIterF f st))
          (restrictFix I (fun i : ↥I => w i) (swapIterF f st))
          (restrictFix I (fun i : ↥I => w i) (swapIterF f st)) := by
      rw [hF1]; exact it_fix_val _ I w
    have hcomp : l2sq (swapIterDelta sel f (swapIterStep st (b, w)) (t + 1)) ≤
        l2sq (fun x => Δ' (fun i => if i ∈ I then w i else x i)) :=
      swapIter_restricted_comparison sel f st hSR t (b, w) κ₁ (dd.g ⟨0, hr⟩) (dd.h ⟨0, hr⟩)
    rw [it_fix_l2sq Δ' I w] at hcomp
    refine it_ind_mono fun hc => ?_
    obtain ⟨hc1, hc2⟩ := hc
    set Lz := l2sq (restrictFix I (fun i : ↥I => w i) (swapIterF f st)) with hLzd
    set Gz := l2sq (restrictFix I (fun i : ↥I => w i) Δ') with hGzd
    set Vz := ((val (restrictFix I (fun i : ↥I => w i) (swapIterF f st))
      (restrictFix I (fun i : ↥I => w i) (swapIterF f st))
      (restrictFix I (fun i : ↥I => w i) (swapIterF f st))
      (restrictFix I (fun i : ↥I => w i) (swapIterF f st))).re) ^ (1 / 2 : ℝ) with hVzd
    have hLz0 : 0 < Lz := lt_of_lt_of_le (by positivity) hc2
    unfold swapIterPhi
    rw [hLz, hVz, hLd, hVd, hDd]
    constructor
    · have s1 : (C * Vz - Gz) / Lz ≤
          (C * Vz - l2sq (swapIterDelta sel f (swapIterStep st (b, w)) (t + 1))) / Lz :=
        div_le_div_of_nonneg_right (by linarith) hLz0.le
      have s2 : (C * V - D) / L + γ ^ 2 / 2 ≤ (C * V - l2sq Δ') / L := by
        have e : (C * V - D) / L + γ ^ 2 / 2 = (C * V - D + γ ^ 2 * L / 2) / L := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) hLpos.le
      linarith
    · have e : γ ^ 2 / (18 * C) * L = γ ^ 2 / 8 * L / (9 / 4 * C) := by
        field_simp; ring
      rw [e]
      exact le_trans (div_le_div_of_nonneg_left (by positivity) hden0 hden) hc2
  -- assembly
  rw [it_expect_coins]
  calc γ ^ 4 * L / (36 * C * B ^ 2) = γ ^ 2 / 2 * K := by
        rw [hK]; field_simp; ring
    _ ≤ (𝔼 b, if γ ^ 2 * L ^ 2 / 2 ≤ X b then (1 : ℝ) else 0) * K :=
        mul_le_mul_of_nonneg_right hp1 hK0
    _ = 𝔼 b, (if γ ^ 2 * L ^ 2 / 2 ≤ X b then (1 : ℝ) else 0) * K := by
        rw [Finset.expect_mul]
    _ ≤ _ := Finset.expect_le_expect fun b _ => hstage b

/-! ### The laws: the scheme on one coordinate

The scheme acts on each coordinate separately: the state of a coordinate is
`(i ∈ R_t, i ∈ S_t, z_t i)`, a Markov chain driven by the coins of that coordinate only. -/

/-- one step of the scheme on one coordinate. -/
private def itLocStep (l : Bool × Bool × α) (c : Bool × α) : Bool × Bool × α :=
  ((l.2.1 && c.1) || (l.1 && !l.2.1 && !c.1), l.2.1 && c.1,
    if (l.1 && !((l.2.1 && c.1) || (l.1 && !l.2.1 && !c.1))) = true then c.2 else l.2.2)

/-- the scheme on one coordinate. -/
private def itLocRun {K : ℕ} (c₀ : Bool × α) (ω : Fin K → Bool × α) : ℕ → Bool × Bool × α
  | 0 => (true, c₀.1, c₀.2)
  | t + 1 => if h : t < K then itLocStep (itLocRun c₀ ω t) (ω ⟨t, h⟩) else itLocRun c₀ ω t

omit [Fintype α] [DecidableEq α] [Fintype ι] in
private lemma it_step_loc (st : SwapIterState ι α) (c : SwapCoins ι α) (i : ι) :
    (decide (i ∈ (swapIterStep st c).R), decide (i ∈ (swapIterStep st c).S),
      (swapIterStep st c).z i) =
      itLocStep (decide (i ∈ st.R), decide (i ∈ st.S), st.z i) (c.1 i, c.2 i) := by
  by_cases hR : i ∈ st.R <;> by_cases hS : i ∈ st.S <;> cases hc : c.1 i <;>
    simp [swapIterStep, itLocStep, hR, hS, hc]

omit [Fintype α] [DecidableEq α] in
private lemma it_run_loc {K : ℕ} (c₀ : SwapCoins ι α) (ω : Fin K → SwapCoins ι α) (i : ι)
    (t : ℕ) :
    (decide (i ∈ (swapIterRun c₀ ω t).R), decide (i ∈ (swapIterRun c₀ ω t).S),
      (swapIterRun c₀ ω t).z i) =
      itLocRun (c₀.1 i, c₀.2 i) (fun s => ((ω s).1 i, (ω s).2 i)) t := by
  induction t with
  | zero => simp [swapIterRun, swapIterInit, itLocRun]
  | succ t ih =>
    simp only [swapIterRun, itLocRun]
    split_ifs with h
    · rw [it_step_loc, ih]
    · exact ih

omit [Fintype α] [DecidableEq α] in
/-- the run up to time `t` only reads the first `t` step coins. -/
private lemma it_locRun_prefix {K t : ℕ} (ht : t ≤ K) (c₀ : Bool × α) (ω : Fin K → Bool × α) :
    ∀ t' ≤ t, itLocRun c₀ ω t' = itLocRun c₀ (fun s : Fin t => ω (Fin.castLE ht s)) t' := by
  intro t' ht'
  induction t' with
  | zero => rfl
  | succ t' ih =>
    have h1 : t' < K := by omega
    have h2 : t' < t := by omega
    simp only [itLocRun, h1, h2, ↓reduceDIte]
    rw [ih (by omega)]
    rfl

private lemma it_expect_snoc {X : Type} [Fintype X] {n : ℕ} {M : Type*} [AddCommMonoid M]
    [Module ℚ≥0 M] (G : (Fin (n + 1) → X) → M) :
    𝔼 ω : Fin (n + 1) → X, G ω = 𝔼 ω' : Fin n → X, 𝔼 v : X, G (Fin.snoc ω' v) := by
  rw [← Fintype.expect_equiv (Fin.snocEquiv fun _ => X) (fun p => G (Fin.snoc p.2 p.1)) G
    (fun p => rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]

private lemma it_expect_castLE {X : Type} [Fintype X] [Nonempty X] {K t : ℕ} (ht : t ≤ K)
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (G : (Fin t → X) → M) :
    𝔼 ω : Fin K → X, G (fun s => ω (Fin.castLE ht s)) = 𝔼 ω' : Fin t → X, G ω' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction d with
  | zero => rfl
  | succ d ih =>
    show 𝔼 ω : Fin (t + d + 1) → X, G (fun s => ω (Fin.castLE ht s)) = _
    rw [it_expect_snoc]
    have e : ∀ (ω' : Fin (t + d) → X) (v : X),
        (fun s : Fin t => (Fin.snoc ω' v : Fin (t + d + 1) → X) (Fin.castLE ht s)) =
          fun s => ω' (Fin.castLE (Nat.le_add_right t d) s) := by
      intro ω' v
      funext s
      have : Fin.castLE ht s = Fin.castSucc (Fin.castLE (Nat.le_add_right t d) s) := rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [e, Fintype.expect_const]
    exact ih (Nat.le_add_right t d)

/-- the law of one coordinate at time `t`: `(r, s)` with the weights `2^{-(t+1)}`, `2^{-(t+1)}`,
`0`, `1 - 2^{-t}` and `z` uniform and independent. -/
private def itLaw (t : ℕ) (l : Bool × Bool × α) : ℝ :=
  (if l.1 = true then (1 / 2 : ℝ) ^ (t + 1) else if l.2.1 = true then 0 else 1 - (1 / 2 : ℝ) ^ t) /
    Fintype.card α

omit [DecidableEq α] in
private lemma it_law_zero [Nonempty α] (H : Bool × Bool × α → ℝ) :
    𝔼 c₀ : Bool × α, H (true, c₀.1, c₀.2) = ∑ l, itLaw 0 l * H l := by
  rw [Finset.expect_eq_sum_div_card]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, itLaw, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool]
  have hA : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp only [↓reduceIte, Bool.false_eq_true, pow_zero, zero_add, pow_one, sub_self, zero_div,
    zero_mul, Finset.sum_const_zero, add_zero, ← Finset.mul_sum]
  push_cast
  field_simp

omit [DecidableEq α] in
private lemma it_law_succ [Nonempty α] (t : ℕ) (H : Bool × Bool × α → ℝ) :
    ∑ l, itLaw t l * 𝔼 v : Bool × α, H (itLocStep l v) = ∑ l, itLaw (t + 1) l * H l := by
  simp only [Finset.expect_eq_sum_div_card, Fintype.sum_prod_type, Fintype.sum_bool, itLaw,
    Finset.card_univ, Fintype.card_prod, Fintype.card_bool, itLocStep]
  simp only [Bool.and_true, Bool.and_false, Bool.not_true,
    Bool.not_false, Bool.or_false, Bool.false_or, ↓reduceIte, Bool.false_eq_true]
  have hA : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_div, zero_div, zero_mul]
  rw [pow_succ (1 / 2 : ℝ) (t + 1)]
  push_cast
  field_simp
  ring

omit [DecidableEq α] in
private lemma it_law_run [Nonempty α] (t : ℕ) (H : Bool × Bool × α → ℝ) :
    𝔼 c₀ : Bool × α, 𝔼 ω : Fin t → Bool × α, H (itLocRun c₀ ω t) = ∑ l, itLaw t l * H l := by
  induction t generalizing H with
  | zero =>
    simp only [itLocRun, Fintype.expect_const]
    exact it_law_zero H
  | succ t ih =>
    have key : ∀ (c₀ : Bool × α) (ω : Fin (t + 1) → Bool × α),
        itLocRun c₀ ω (t + 1) = itLocStep (itLocRun c₀ (Fin.init ω) t) (ω (Fin.last t)) := by
      intro c₀ ω
      simp only [itLocRun, Nat.lt_succ_self, ↓reduceDIte]
      rw [it_locRun_prefix (Nat.le_succ t) c₀ ω t le_rfl]
      rfl
    simp_rw [key, it_expect_snoc, Fin.init_snoc, Fin.snoc_last]
    rw [← it_law_succ]
    exact ih (fun l => 𝔼 v : Bool × α, H (itLocStep l v))

omit [DecidableEq α] in
private lemma it_law_runK [Nonempty α] {K t : ℕ} (ht : t ≤ K) (H : Bool × Bool × α → ℝ) :
    𝔼 c₀ : Bool × α, 𝔼 ω : Fin K → Bool × α, H (itLocRun c₀ ω t) = ∑ l, itLaw t l * H l := by
  rw [← it_law_run t H]
  refine Finset.expect_congr rfl fun c₀ _ => ?_
  simp_rw [it_locRun_prefix ht c₀ _ t le_rfl]
  exact it_expect_castLE ht (fun ω' => H (itLocRun c₀ ω' t))

/-! ### The law of the scheme composed with a further restriction (`#restriction-composition`) -/

/-- one coordinate of a restriction: fixed to `a` (probability `(1-ρ)/|α|` each) or live (`ρ`). -/
def swapFixLaw [Nonempty α] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : FinProb (α ⊕ Unit) where
  prob s := Sum.elim (fun _ => (1 - ρ) / Fintype.card α) (fun _ => ρ) s
  nonneg s := by
    rcases s with a | u
    · exact div_nonneg (by linarith) (by positivity)
    · exact h0
  sum_eq_one := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_unit, Nat.cast_one]
    have : (Fintype.card α : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- the live coordinates of a vector of coordinate states. -/
def swapFixLive (s : ι → α ⊕ Unit) : Finset ι := Finset.univ.filter fun i => (s i).isRight

/-- the fixed values of a vector of coordinate states (arbitrary on the live coordinates). -/
def swapFixZ [Nonempty α] (s : ι → α ⊕ Unit) : ι → α :=
  fun i => Sum.elim id (fun _ => Classical.arbitrary α) (s i)

/-- a further restriction inside `base ⊆ R_t`: the live coordinates `base ∩ {b = true}`. -/
def swapIterLive (base : Finset ι) (b : ι → Bool) : Finset ι := base.filter fun i => b i = true

/-- the fixing after a further restriction: `w` on `R_t \ L`, `z_t` outside `R_t`. -/
def swapIterZ (st : SwapIterState ι α) (L : Finset ι) (w : ι → α) : ι → α :=
  fun i => if i ∈ st.R \ L then w i else st.z i

/-! ### The laws: reduction to one coordinate -/

/-- the state of a coordinate after a further restriction inside the base set `{P r s}`:
live, or fixed (to the fresh value `w` inside `R_t`, to `z_t` outside). -/
private def itPhi (P : Bool → Bool → Bool) (l : Bool × Bool × α) (w : α) (b : Bool) : α ⊕ Unit :=
  if (P l.1 l.2.1 && b) = true then Sum.inr () else Sum.inl (if l.1 = true then w else l.2.2)

omit [Fintype α] [DecidableEq α] in
/-- the integrand only depends on the coordinate states. -/
private lemma it_integrand [Nonempty α] (f : (ι → α) → ℂ)
    (Ψ : Finset ι → ((ι → α) → ℂ) → ℝ) (P : Bool → Bool → Bool) (st : SwapIterState ι α)
    (base : Finset ι) (hbase : ∀ i, i ∈ base ↔ P (decide (i ∈ st.R)) (decide (i ∈ st.S)) = true)
    (w : ι → α) (b : ι → Bool) :
    Ψ (swapIterLive base b)
        (swapIterFun f (swapIterLive base b) (swapIterZ st (swapIterLive base b) w)) =
      Ψ (swapFixLive fun i => itPhi P (decide (i ∈ st.R), decide (i ∈ st.S), st.z i) (w i) (b i))
        (swapIterFun f (swapFixLive fun i =>
            itPhi P (decide (i ∈ st.R), decide (i ∈ st.S), st.z i) (w i) (b i))
          (swapFixZ fun i => itPhi P (decide (i ∈ st.R), decide (i ∈ st.S), st.z i) (w i) (b i))) := by
  have hmem : ∀ i, i ∈ swapIterLive base b ↔
      (P (decide (i ∈ st.R)) (decide (i ∈ st.S)) && b i) = true := by
    intro i
    simp [swapIterLive, hbase]
  have hL : swapFixLive (fun i => itPhi P (decide (i ∈ st.R), decide (i ∈ st.S), st.z i)
      (w i) (b i)) = swapIterLive base b := by
    ext i
    rw [hmem]
    simp only [swapFixLive, Finset.mem_filter, Finset.mem_univ, true_and, itPhi]
    split_ifs with h <;> simp [h]
  rw [hL]
  congr 1
  funext x
  simp only [swapIterFun]
  congr 1
  funext i
  by_cases hi : i ∈ swapIterLive base b
  · simp [hi]
  · have h2 : (P (decide (i ∈ st.R)) (decide (i ∈ st.S)) && b i) = false := by
      rw [hmem] at hi; simpa using hi
    simp only [hi, ↓reduceIte, swapIterZ, swapFixZ, itPhi, h2, Bool.false_eq_true,
      Sum.elim_inl, id, Finset.mem_sdiff, not_false_eq_true, and_true]
    by_cases hR : i ∈ st.R <;> simp [hR]

omit [DecidableEq α] in
/-- reindexing the coins of the scheme coordinate by coordinate. -/
private lemma it_factor [Nonempty α] {K : ℕ} {ρ₁ : ℝ} (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1)
    (Ξ : (ι → (Bool × α) × (Fin K → Bool × α) × α × Bool) → ℝ) :
    𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
        ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
          Ξ (fun i => ((c₀.1 i, c₀.2 i), (fun s => ((ω s).1 i, (ω s).2 i)), w i, b i))) =
      ∑ x : ι → (Bool × α) × (Fin K → Bool × α) × α × Bool,
        (∏ i, (1 / (Fintype.card (Bool × α) : ℝ)) * (1 / (Fintype.card (Fin K → Bool × α) : ℝ)) *
          (1 / (Fintype.card α : ℝ)) * (bernoulli ρ₁ h0' h1').prob (x i).2.2.2) * Ξ x := by
  let E : SwapCoins ι α × (Fin K → SwapCoins ι α) × (ι → α) × (ι → Bool) ≃
      (ι → (Bool × α) × (Fin K → Bool × α) × α × Bool) :=
    { toFun := fun p i => ((p.1.1 i, p.1.2 i), (fun s => ((p.2.1 s).1 i, (p.2.1 s).2 i)),
        p.2.2.1 i, p.2.2.2 i)
      invFun := fun x => ((fun i => (x i).1.1, fun i => (x i).1.2),
        (fun s => (fun i => ((x i).2.1 s).1, fun i => ((x i).2.1 s).2)),
        (fun i => (x i).2.2.1), (fun i => (x i).2.2.2))
      left_inv := fun p => rfl
      right_inv := fun x => rfl }
  rw [← Fintype.sum_equiv E (fun p => (∏ i, (1 / (Fintype.card (Bool × α) : ℝ)) *
      (1 / (Fintype.card (Fin K → Bool × α) : ℝ)) * (1 / (Fintype.card α : ℝ)) *
        (bernoulli ρ₁ h0' h1').prob (E p i).2.2.2) * Ξ (E p)) _ (fun p => rfl)]
  simp only [Fintype.sum_prod_type, FinProb.expect, FinProb.pi, Finset.expect_eq_sum_div_card,
    Finset.card_univ, Finset.sum_div]
  refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ =>
    Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun b _ => ?_
  simp only [E, Equiv.coe_fn_mk]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hN₁ : (Fintype.card ((ι → Bool) × (ι → α)) : ℝ) =
      (Fintype.card (Bool × α) : ℝ) ^ Fintype.card ι := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool]; push_cast; ring
  have hN₂ : (Fintype.card (Fin K → (ι → Bool) × (ι → α)) : ℝ) =
      (Fintype.card (Fin K → Bool × α) : ℝ) ^ Fintype.card ι := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast; ring
  have hN₃ : (Fintype.card (ι → α) : ℝ) = (Fintype.card α : ℝ) ^ Fintype.card ι := by
    simp only [Fintype.card_fun]; push_cast; ring
  rw [hN₁, hN₂, hN₃]
  have h₁ : (0 : ℝ) < Fintype.card (Bool × α) := Nat.cast_pos.2 Fintype.card_pos
  have h₂ : (0 : ℝ) < Fintype.card (Fin K → Bool × α) := Nat.cast_pos.2 Fintype.card_pos
  have h₃ : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  simp only [one_div, mul_pow, inv_pow]
  field_simp

/-- the law of a coordinatewise image of a product measure. -/
private lemma it_sum_pi_push {κ β γ : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [Fintype γ]
    [DecidableEq γ] (ν : β → ℝ) (ψ : β → γ) (Φ : (κ → γ) → ℝ) :
    ∑ x : κ → β, (∏ i, ν (x i)) * Φ (fun i => ψ (x i)) =
      ∑ s : κ → γ, (∏ i, ∑ a ∈ Finset.univ.filter (fun a => ψ a = s i), ν a) * Φ s := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : κ → β => fun i => ψ (x i))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_univ_sum, Finset.sum_mul]
  have hfib : (Finset.univ.filter fun x : κ → β => (fun i => ψ (x i)) = s) =
      Fintype.piFinset fun i => Finset.univ.filter fun a => ψ a = s i := by
    ext x
    simp [Fintype.mem_piFinset, funext_iff]
  rw [hfib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have : (fun i => ψ (x i)) = s := by
    funext i
    exact (Finset.mem_filter.1 (Fintype.mem_piFinset.1 hx i)).2
  rw [this]

omit [DecidableEq α] in
private lemma it_sum_loc (F : Bool × Bool × α → ℝ) :
    ∑ l, F l = ∑ z, F (true, true, z) + ∑ z, F (true, false, z) + ∑ z, F (false, true, z) +
      ∑ z, F (false, false, z) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

private lemma it_H_inr [Nonempty α] (P : Bool → Bool → Bool) {ρ₁ : ℝ} (h0' : 0 ≤ ρ₁)
    (h1' : ρ₁ ≤ 1) (l : Bool × Bool × α) :
    (1 / (Fintype.card α : ℝ)) * ∑ w : α, ∑ b : Bool,
        (bernoulli ρ₁ h0' h1').prob b * (if itPhi P l w b = Sum.inr () then 1 else 0) =
      if P l.1 l.2.1 = true then ρ₁ else 0 := by
  have hA : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have hb : ∀ w : α, ∑ b : Bool,
      (bernoulli ρ₁ h0' h1').prob b * (if itPhi P l w b = Sum.inr () then 1 else 0) =
        if P l.1 l.2.1 = true then ρ₁ else 0 := by
    intro w
    rw [Fintype.sum_bool]
    cases h : P l.1 l.2.1 <;> simp [itPhi, h, bernoulli]
  simp only [hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma it_H_inl [Nonempty α] (P : Bool → Bool → Bool) (hP : ∀ s, P false s = false)
    {ρ₁ : ℝ} (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) (l : Bool × Bool × α) (a : α) :
    (1 / (Fintype.card α : ℝ)) * ∑ w : α, ∑ b : Bool,
        (bernoulli ρ₁ h0' h1').prob b * (if itPhi P l w b = Sum.inl a then 1 else 0) =
      if l.1 = true then (1 - if P true l.2.1 = true then ρ₁ else 0) / Fintype.card α
      else if l.2.2 = a then 1 else 0 := by
  have hA : (Fintype.card α : ℝ) ≠ 0 := by positivity
  obtain ⟨r, s, z⟩ := l
  cases r
  · have hb : ∀ w : α, ∑ b : Bool,
        (bernoulli ρ₁ h0' h1').prob b * (if itPhi P (false, s, z) w b = Sum.inl a then 1 else 0) =
          if z = a then 1 else 0 := by
      intro w
      rw [Fintype.sum_bool]
      by_cases hz : z = a <;> simp [itPhi, hP, hz, bernoulli]
    simp only [hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Bool.false_eq_true,
      ↓reduceIte]
    field_simp
  · have hb : ∀ w : α, ∑ b : Bool,
        (bernoulli ρ₁ h0' h1').prob b * (if itPhi P (true, s, z) w b = Sum.inl a then 1 else 0) =
          (1 - if P true s = true then ρ₁ else 0) * (if w = a then 1 else 0) := by
      intro w
      rw [Fintype.sum_bool]
      by_cases hw : w = a <;> cases h : P true s <;> simp [itPhi, h, hw, bernoulli]
    simp only [hb, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    field_simp

/-- the law of one coordinate after the further restriction. -/
private lemma it_coord_law [Nonempty α] (P : Bool → Bool → Bool) (hP : ∀ s, P false s = false)
    (t : ℕ) {ρ₁ : ℝ} (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hρ : ρ = ((if P true true = true then (1 / 2 : ℝ) ^ (t + 1) else 0) +
      (if P true false = true then (1 / 2 : ℝ) ^ (t + 1) else 0)) * ρ₁)
    (v : α ⊕ Unit) :
    ∑ l, itLaw t l * ((1 / (Fintype.card α : ℝ)) * ∑ w : α, ∑ b : Bool,
        (bernoulli ρ₁ h0' h1').prob b * (if itPhi P l w b = v then 1 else 0)) =
      (swapFixLaw ρ h0 h1).prob v := by
  have hA : (Fintype.card α : ℝ) ≠ 0 := by positivity
  obtain ⟨p, hp⟩ : ∃ p, (1 / 2 : ℝ) ^ (t + 1) = p := ⟨_, rfl⟩
  have e2 : (1 / 2 : ℝ) ^ t = 2 * p := by rw [← hp, pow_succ]; ring
  rw [hp] at hρ
  rw [it_sum_loc]
  simp only [itLaw, ↓reduceIte, Bool.false_eq_true, hp, e2, zero_div, zero_mul,
    Finset.sum_const_zero, add_zero]
  rcases v with a | u
  · simp only [it_H_inl P hP h0' h1', ↓reduceIte, Bool.false_eq_true, swapFixLaw,
      Sum.elim_inl, hρ]
    by_cases hTT : P true true = true <;> by_cases hTF : P true false = true <;>
      simp only [hTT, hTF, Bool.false_eq_true, ↓reduceIte, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ] <;>
      field_simp <;> ring
  · simp only [it_H_inr P h0' h1', hP, Bool.false_eq_true, ↓reduceIte, mul_zero,
      swapFixLaw, Sum.elim_inr, hρ]
    by_cases hTT : P true true = true <;> by_cases hTF : P true false = true <;>
      simp only [hTT, hTF, Bool.false_eq_true, ↓reduceIte, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_zero, add_zero, zero_add] <;>
      (field_simp; try ring)

/-- the weight of each coordinate state. -/
private lemma it_weight [Nonempty α] {K t : ℕ} (ht : t ≤ K) (P : Bool → Bool → Bool)
    (hP : ∀ s, P false s = false) {ρ₁ : ℝ} (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1)
    (hρ : ρ = ((if P true true = true then (1 / 2 : ℝ) ^ (t + 1) else 0) +
      (if P true false = true then (1 / 2 : ℝ) ^ (t + 1) else 0)) * ρ₁)
    (v : α ⊕ Unit) :
    ∑ a ∈ Finset.univ.filter (fun a : (Bool × α) × (Fin K → Bool × α) × α × Bool =>
        itPhi P (itLocRun a.1 a.2.1 t) a.2.2.1 a.2.2.2 = v),
      (1 / (Fintype.card (Bool × α) : ℝ)) * (1 / (Fintype.card (Fin K → Bool × α) : ℝ)) *
        (1 / (Fintype.card α : ℝ)) * (bernoulli ρ₁ h0' h1').prob a.2.2.2 =
      (swapFixLaw ρ h0 h1).prob v := by
  rw [← it_coord_law P hP t h0' h1' h0 h1 hρ v, ← it_law_runK ht, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ =>
    Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-- the three laws in one: a further restriction inside the base set `{P r s}`. -/
private lemma it_law_general [Nonempty α] (f : (ι → α) → ℂ) {K t : ℕ} (ht : t ≤ K) {ρ₁ ρ : ℝ}
    (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (P : Bool → Bool → Bool)
    (hP : ∀ s, P false s = false)
    (hρ : ρ = ((if P true true = true then (1 / 2 : ℝ) ^ (t + 1) else 0) +
      (if P true false = true then (1 / 2 : ℝ) ^ (t + 1) else 0)) * ρ₁)
    (base : SwapIterState ι α → Finset ι)
    (hbase : ∀ st : SwapIterState ι α, st.S ⊆ st.R →
      ∀ i, i ∈ base st ↔ P (decide (i ∈ st.R)) (decide (i ∈ st.S)) = true)
    (Ψ : Finset ι → ((ι → α) → ℂ) → ℝ) :
    𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
        ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
          Ψ (swapIterLive (base (swapIterRun c₀ ω t)) b)
            (swapIterFun f (swapIterLive (base (swapIterRun c₀ ω t)) b)
              (swapIterZ (swapIterRun c₀ ω t) (swapIterLive (base (swapIterRun c₀ ω t)) b) w))) =
      ((swapFixLaw ρ h0 h1).pi ι).expect (fun s =>
        Ψ (swapFixLive s) (swapIterFun f (swapFixLive s) (swapFixZ s))) := by
  let ψ : (Bool × α) × (Fin K → Bool × α) × α × Bool → α ⊕ Unit :=
    fun a => itPhi P (itLocRun a.1 a.2.1 t) a.2.2.1 a.2.2.2
  let Φ : (ι → α ⊕ Unit) → ℝ := fun s =>
    Ψ (swapFixLive s) (swapIterFun f (swapFixLive s) (swapFixZ s))
  let ν : (Bool × α) × (Fin K → Bool × α) × α × Bool → ℝ := fun a =>
    (1 / (Fintype.card (Bool × α) : ℝ)) * (1 / (Fintype.card (Fin K → Bool × α) : ℝ)) *
      (1 / (Fintype.card α : ℝ)) * (bernoulli ρ₁ h0' h1').prob a.2.2.2
  have hstep : 𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
      ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
        Ψ (swapIterLive (base (swapIterRun c₀ ω t)) b)
          (swapIterFun f (swapIterLive (base (swapIterRun c₀ ω t)) b)
            (swapIterZ (swapIterRun c₀ ω t) (swapIterLive (base (swapIterRun c₀ ω t)) b) w))) =
      𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
        ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
          (fun x : ι → (Bool × α) × (Fin K → Bool × α) × α × Bool => Φ (fun i => ψ (x i)))
            (fun i => ((c₀.1 i, c₀.2 i), (fun s => ((ω s).1 i, (ω s).2 i)), w i, b i))) := by
    refine Finset.expect_congr rfl fun c₀ _ => Finset.expect_congr rfl fun ω _ =>
      Finset.expect_congr rfl fun w _ => ?_
    unfold FinProb.expect
    refine Finset.sum_congr rfl fun b _ => ?_
    beta_reduce
    rw [it_integrand f Ψ P (swapIterRun c₀ ω t) _
      (hbase _ (swapIterRun_S_subset c₀ ω t)) w b]
    simp only [it_run_loc, Φ, ψ]
  rw [hstep, it_factor h0' h1' (fun x => Φ (fun i => ψ (x i)))]
  refine (it_sum_pi_push ν ψ Φ).trans ?_
  simp only [FinProb.expect, FinProb.pi]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => it_weight ht P hP h0' h1' h0 h1 hρ (s i)

/-- the scheme at time `t`, then a fresh restriction of `R_t` with live density `ρ₁`, has the law of one
restriction with live density `2^{-t} ρ₁`. -/
theorem swapIterRun_law_R [Nonempty α] (f : (ι → α) → ℂ) {K t : ℕ} (ht : t ≤ K) {ρ₁ ρ : ℝ}
    (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ = (1 / 2) ^ t * ρ₁)
    (Ψ : Finset ι → ((ι → α) → ℂ) → ℝ) :
    𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
        ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
          Ψ (swapIterLive (swapIterRun c₀ ω t).R b)
            (swapIterFun f (swapIterLive (swapIterRun c₀ ω t).R b)
              (swapIterZ (swapIterRun c₀ ω t) (swapIterLive (swapIterRun c₀ ω t).R b) w))) =
      ((swapFixLaw ρ h0 h1).pi ι).expect (fun s =>
        Ψ (swapFixLive s) (swapIterFun f (swapFixLive s) (swapFixZ s))) := by
  refine it_law_general f ht h0' h1' h0 h1 (fun r _ => r) (fun _ => rfl) ?_
    (fun st => st.R) (fun st _ i => by simp) Ψ
  rw [hρ, pow_succ]
  simp only [↓reduceIte]
  ring

/-- the same inside `S_t` (the coordinates of `T_t` and `Rᶜ` are fixed): live density `2^{-(t+1)} ρ₁`. -/
theorem swapIterRun_law_S [Nonempty α] (f : (ι → α) → ℂ) {K t : ℕ} (ht : t ≤ K) {ρ₁ ρ : ℝ}
    (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ = (1 / 2) ^ (t + 1) * ρ₁)
    (Ψ : Finset ι → ((ι → α) → ℂ) → ℝ) :
    𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
        ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
          Ψ (swapIterLive (swapIterRun c₀ ω t).S b)
            (swapIterFun f (swapIterLive (swapIterRun c₀ ω t).S b)
              (swapIterZ (swapIterRun c₀ ω t) (swapIterLive (swapIterRun c₀ ω t).S b) w))) =
      ((swapFixLaw ρ h0 h1).pi ι).expect (fun s =>
        Ψ (swapFixLive s) (swapIterFun f (swapFixLive s) (swapFixZ s))) := by
  refine it_law_general f ht h0' h1' h0 h1 (fun r s => r && s) (fun _ => rfl) ?_
    (fun st => st.S) (fun st hSR i => ?_) Ψ
  · rw [hρ]
    simp
  · by_cases h : i ∈ st.S
    · simp [h, hSR h]
    · simp [h]

/-- the same inside `T_t = R_t \ S_t` (the coordinates of `S_t` and `Rᶜ` are fixed). -/
theorem swapIterRun_law_T [Nonempty α] (f : (ι → α) → ℂ) {K t : ℕ} (ht : t ≤ K) {ρ₁ ρ : ℝ}
    (h0' : 0 ≤ ρ₁) (h1' : ρ₁ ≤ 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ = (1 / 2) ^ (t + 1) * ρ₁)
    (Ψ : Finset ι → ((ι → α) → ℂ) → ℝ) :
    𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, 𝔼 w : ι → α,
        ((bernoulli ρ₁ h0' h1').pi ι).expect (fun b =>
          Ψ (swapIterLive ((swapIterRun c₀ ω t).R \ (swapIterRun c₀ ω t).S) b)
            (swapIterFun f (swapIterLive ((swapIterRun c₀ ω t).R \ (swapIterRun c₀ ω t).S) b)
              (swapIterZ (swapIterRun c₀ ω t)
                (swapIterLive ((swapIterRun c₀ ω t).R \ (swapIterRun c₀ ω t).S) b) w))) =
      ((swapFixLaw ρ h0 h1).pi ι).expect (fun s =>
        Ψ (swapFixLive s) (swapIterFun f (swapFixLive s) (swapFixZ s))) := by
  refine it_law_general f ht h0' h1' h0 h1 (fun r s => r && !s) (fun _ => rfl) ?_
    (fun st => st.R \ st.S) (fun st _ i => by simp) Ψ
  rw [hρ]
  simp

end SwapIter
end TrackB
end RestrictedPolynomials
end
