module

public import RestrictedPolynomials.TrackB.SwapSvdInc
public import RestrictedPolynomials.TrackB.SwapIterScheme
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect

/-!
# Track B (auxiliary part): infrastructure for `SwapInduct`

Source: CSP6 (arXiv:2411.15133v1 `main.tex`) L1136-1170 (proof of `thm:swap`).

This module holds the proof infrastructure used by `SwapInduct.lean` (split because of length):
* `swapIndCorr L u`: the correlation of `u : (ι → α) → ℂ` with product functions of the coordinates
  in `L`, computed on the ambient cube `ι → α`; its bounds, scaling, monotonicity in `L` (for `u`
  depending only on the smaller set) and its identification with the correlation of the restriction
  of `u` to the subcube `↥L → α`;
* the law of one coordinate-wise restriction (`swapFixLaw`, file 2) as the Bernoulli restriction
  `subsetExpect` of file `Restrict` with uniform fixed values;
* the transfer of item 1 / item 2 of `lemma:svdinc` (`SwapSvdIncOut`, file 4) to correlations of
  restrictions (`swapInd_transfer`);
* the arithmetic of the potential weight `θ = 2·10⁻¹²` and the polynomial bound on the exponent
  of the recursion solution.
All names carry the prefix `swapInd`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapInductAux
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Products of one-coordinate functions -/

omit [DecidableEq α] in
/-- `𝔼_x ∏ᵢ gᵢ(xᵢ) = ∏ᵢ 𝔼_a gᵢ(a)` for the uniform measure on `ι → α`. -/
theorem swapInd_expect_prod (g : ι → α → ℝ) :
    𝔼 x : ι → α, ∏ i, g i (x i) = ∏ i, 𝔼 a : α, g i a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, ← Fintype.prod_sum, Finset.prod_const, Fintype.card_fun]
  simp

omit [DecidableEq α] in
/-- `𝔼_x ∏_{i ∈ s} ‖Pᵢ(xᵢ)‖² ≤ 1` when every `𝔼‖Pᵢ‖² ≤ 1`. -/
theorem swapInd_expect_prod_sq_le [Nonempty α] (P : ι → α → ℂ)
    (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) (s : Finset ι) :
    𝔼 x : ι → α, ∏ i ∈ s, ‖P i (x i)‖ ^ 2 ≤ 1 := by
  have h := swapInd_expect_prod (fun i a => if i ∈ s then ‖P i a‖ ^ 2 else 1)
  have e : 𝔼 x : ι → α, ∏ i ∈ s, ‖P i (x i)‖ ^ 2 =
      𝔼 x : ι → α, ∏ i, (if i ∈ s then ‖P i (x i)‖ ^ 2 else 1) :=
    Finset.expect_congr rfl fun x _ => (Fintype.prod_ite_mem s _).symm
  rw [e, h]
  refine Finset.prod_le_one₀ (fun i _ => Finset.expect_nonneg fun a _ => ?_) fun i _ => ?_
  · split_ifs <;> positivity
  · by_cases hi : i ∈ s
    · simp only [hi, ite_true]
      exact hP i
    · simp [hi]

/-- Cauchy-Schwarz: `‖𝔼_x u(x) conj ∏_{i ∈ s} Pᵢ(xᵢ)‖ ≤ ‖u‖₂` when every `𝔼‖Pᵢ‖² ≤ 1`. -/
theorem swapInd_corr_le_sqrt {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty α]
    (u : (κ → α) → ℂ) (P : κ → α → ℂ) (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) (s : Finset κ) :
    ‖𝔼 x : κ → α, u x * star (∏ i ∈ s, P i (x i))‖ ≤ Real.sqrt (l2sq u) := by
  have h := norm_expect_mul_sq_le univ u (fun x => star (∏ i ∈ s, P i (x i)))
  have e : ∀ x : κ → α, ‖star (∏ i ∈ s, P i (x i))‖ ^ 2 = ∏ i ∈ s, ‖P i (x i)‖ ^ 2 := by
    intro x
    rw [norm_star, norm_prod, Finset.prod_pow]
  simp_rw [e] at h
  have h2 := swapInd_expect_prod_sq_le P hP s
  have hl := l2sq_nonneg u
  have h3 : ‖𝔼 x : κ → α, u x * star (∏ i ∈ s, P i (x i))‖ ^ 2 ≤ l2sq u := by
    refine h.trans ?_
    calc (𝔼 x : κ → α, ‖u x‖ ^ 2) * 𝔼 x : κ → α, ∏ i ∈ s, ‖P i (x i)‖ ^ 2 ≤ l2sq u * 1 :=
          mul_le_mul_of_nonneg_left h2 hl
      _ = l2sq u := mul_one _
  have := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (norm_nonneg _)] at this

omit [DecidableEq α] in
/-- `‖u‖₂ ≤ B` for a `B`-bounded `u`. -/
theorem swapInd_sqrt_l2sq_le {κ : Type} [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ‖u x‖ ≤ B) : Real.sqrt (l2sq u) ≤ B := by
  have h : l2sq u ≤ B ^ 2 := by
    unfold l2sq
    rcases isEmpty_or_nonempty (κ → α) with hn | hn
    · simp [Finset.univ_eq_empty]; positivity
    · calc 𝔼 x : κ → α, ‖u x‖ ^ 2 ≤ 𝔼 _x : κ → α, B ^ 2 :=
            Finset.expect_le_expect fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
        _ = B ^ 2 := Fintype.expect_const _
  calc Real.sqrt (l2sq u) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := Real.sqrt_sq hB0

/-! ### The correlation with product functions of the coordinates of `L` -/

/-- `sup_P ‖𝔼_x u(x) conj ∏_{i ∈ L} Pᵢ(xᵢ)‖` over `P` with `𝔼‖Pᵢ‖² ≤ 1`, on the cube `ι → α`. -/
def swapIndCorr (L : Finset ι) (u : (ι → α) → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
    r = ‖𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i))‖}

theorem swapIndCorr_bdd [Nonempty α] (L : Finset ι) (u : (ι → α) → ℂ) :
    BddAbove {r : ℝ | ∃ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
      r = ‖𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i))‖} := by
  refine ⟨Real.sqrt (l2sq u), ?_⟩
  rintro r ⟨P, hP, rfl⟩
  exact swapInd_corr_le_sqrt u P hP L

omit [DecidableEq α] in
theorem swapIndCorr_nonempty (L : Finset ι) (u : (ι → α) → ℂ) :
    {r : ℝ | ∃ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
      r = ‖𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i))‖}.Nonempty :=
  ⟨_, fun _ _ => 0, fun i => by simp, rfl⟩

theorem le_swapIndCorr [Nonempty α] {L : Finset ι} {u : (ι → α) → ℂ} (P : ι → α → ℂ)
    (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) :
    ‖𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i))‖ ≤ swapIndCorr L u :=
  le_csSup (swapIndCorr_bdd L u) ⟨P, hP, rfl⟩

omit [DecidableEq α] in
theorem swapIndCorr_le {L : Finset ι} {u : (ι → α) → ℂ} {M : ℝ}
    (h : ∀ P : ι → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) →
      ‖𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i))‖ ≤ M) :
    swapIndCorr L u ≤ M :=
  csSup_le (swapIndCorr_nonempty L u) (by rintro r ⟨P, hP, rfl⟩; exact h P hP)

theorem swapIndCorr_nonneg [Nonempty α] (L : Finset ι) (u : (ι → α) → ℂ) :
    0 ≤ swapIndCorr L u :=
  (norm_nonneg _).trans (le_swapIndCorr (u := u) (L := L) (fun _ _ => 0) (fun i => by simp))

theorem swapIndCorr_le_bound [Nonempty α] (L : Finset ι) (u : (ι → α) → ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ‖u x‖ ≤ B) : swapIndCorr L u ≤ B :=
  swapIndCorr_le fun P hP =>
    (swapInd_corr_le_sqrt u P hP L).trans (swapInd_sqrt_l2sq_le u hB0 hB)

/-- scaling by a positive real. -/
theorem swapIndCorr_mul [Nonempty α] (L : Finset ι) (u : (ι → α) → ℂ) {k : ℝ} (hk : 0 < k) :
    k * swapIndCorr L u ≤ swapIndCorr L (fun x => (k : ℂ) * u x) := by
  rw [← le_div_iff₀' hk]
  refine swapIndCorr_le fun P hP => ?_
  rw [le_div_iff₀' hk]
  have e : 𝔼 x : ι → α, (k : ℂ) * u x * star (∏ i ∈ L, P i (x i)) =
      (k : ℂ) * 𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i)) := by
    rw [Finset.mul_expect]
    exact Finset.expect_congr rfl fun x _ => by ring
  have h := le_swapIndCorr (u := fun x => (k : ℂ) * u x) (L := L) P hP
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le] at h
  exact h

/-- `u ↦ ‖𝔼 u · conj Q‖` is bounded by `1` for `Q = ∏_{i ∈ s} Pᵢ` (the case `u = 1`). -/
theorem swapInd_norm_expect_prod_le [Nonempty α] (P : ι → α → ℂ)
    (hP : ∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) (s : Finset ι) :
    ‖𝔼 x : ι → α, star (∏ i ∈ s, P i (x i))‖ ≤ 1 := by
  have h := swapInd_corr_le_sqrt (fun _ : ι → α => (1 : ℂ)) P hP s
  have hl : l2sq (fun _ : ι → α => (1 : ℂ)) = 1 := by simp [l2sq]
  simpa [hl] using h

/-- monotonicity in `L` for a function of the coordinates of the smaller set `L'`. -/
theorem swapIndCorr_mono [Nonempty α] {L L' : Finset ι} (hLL : L' ⊆ L) {u : (ι → α) → ℂ}
    (hu : ∀ x y : ι → α, (∀ i ∈ L', x i = y i) → u x = u y) :
    swapIndCorr L u ≤ swapIndCorr L' u := by
  refine swapIndCorr_le fun P hP => ?_
  let x₀ : ι → α := fun _ => Classical.arbitrary α
  have hsplit := svdInc_expect_mul_dep L' x₀
    (fun x => u x * star (∏ i ∈ L', P i (x i))) (fun x => star (∏ i ∈ L \ L', P i (x i)))
    (fun x y hxy => by
      rw [hu x y hxy, Finset.prod_congr rfl fun i hi => by rw [hxy i hi]])
    (fun x y hxy => by
      rw [Finset.prod_congr rfl fun i hi => by rw [hxy i (mem_compl.2 (mem_sdiff.1 hi).2)]])
  have e : 𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i)) =
      𝔼 x : ι → α, (u x * star (∏ i ∈ L', P i (x i))) * star (∏ i ∈ L \ L', P i (x i)) := by
    refine Finset.expect_congr rfl fun x _ => ?_
    rw [← Finset.prod_sdiff hLL, star_mul']
    ring
  rw [e, hsplit, norm_mul]
  calc ‖𝔼 x : ι → α, u x * star (∏ i ∈ L', P i (x i))‖ *
        ‖𝔼 x : ι → α, star (∏ i ∈ L \ L', P i (x i))‖ ≤
        ‖𝔼 x : ι → α, u x * star (∏ i ∈ L', P i (x i))‖ * 1 :=
        mul_le_mul_of_nonneg_left (swapInd_norm_expect_prod_le P hP _) (norm_nonneg _)
    _ ≤ swapIndCorr L' u := by rw [mul_one]; exact le_swapIndCorr P hP

/-- the correlation on the cube equals the correlation of the restriction to the subcube `↥L → α`, for
a function of the coordinates of `L`. -/
theorem swapIndCorr_eq_subtype [Nonempty α] (L : Finset ι) (u : (ι → α) → ℂ)
    (hu : ∀ x y : ι → α, (∀ i ∈ L, x i = y i) → u x = u y) (z₀ : ↥Lᶜ → α) :
    swapIndCorr L u = sSup {r : ℝ | ∃ P : ↥L → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
      r = ‖𝔼 y : ↥L → α, u (glueFree L y z₀) * star (∏ i, P i (y i))‖} := by
  have key : ∀ P : ι → α → ℂ, 𝔼 x : ι → α, u x * star (∏ i ∈ L, P i (x i)) =
      𝔼 y : ↥L → α, u (glueFree L y z₀) * star (∏ i : ↥L, P i (y i)) := by
    intro P
    rw [svdInc_expect_split L]
    refine Finset.expect_congr rfl fun y _ => ?_
    have h1 : ∀ v : ↥Lᶜ → α, u (glueFree L y v) * star (∏ i ∈ L, P i (glueFree L y v i)) =
        u (glueFree L y z₀) * star (∏ i : ↥L, P i (y i)) := by
      intro v
      have hu' : u (glueFree L y v) = u (glueFree L y z₀) :=
        hu _ _ fun i hi => by simp [glueFree, hi]
      have hp : ∏ i ∈ L, P i (glueFree L y v i) = ∏ i : ↥L, P i (y i) := by
        rw [← Finset.prod_coe_sort L]
        exact Finset.prod_congr rfl fun i _ => by simp [glueFree, i.2]
      rw [hu', hp]
    simp_rw [h1]
    exact Fintype.expect_const _
  unfold swapIndCorr
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨fun i => P i, fun i => hP i, by rw [key]⟩
  · rintro ⟨P, hP, rfl⟩
    refine ⟨fun i => if h : i ∈ L then P ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
    · by_cases h : i ∈ L
      · simp only [h, ↓reduceDIte]
        exact hP _
      · simp [h]
    · rw [key]
      congr 1
      refine Finset.expect_congr rfl fun y _ => ?_
      congr 2
      exact Finset.prod_congr rfl fun i _ => by simp [i.2]

/-! ### One restriction, coordinate by coordinate -/

/-- the uniform law on `α`, carried to `α ⊕ Unit` by `inl`. -/
private def swapIndUnifInl [Nonempty α] : FinProb (α ⊕ Unit) where
  prob s := Sum.elim (fun _ => 1 / (Fintype.card α : ℝ)) (fun _ => 0) s
  nonneg s := by rcases s with a | u <;> simp
  sum_eq_one := by
    rw [Fintype.sum_sum_type]
    simp

/-- the Dirac mass at `inr ()`. -/
private def swapIndDiracInr : FinProb (α ⊕ Unit) where
  prob s := Sum.elim (fun _ => 0) (fun _ => 1) s
  nonneg s := by rcases s with a | u <;> simp
  sum_eq_one := by
    rw [Fintype.sum_sum_type]
    simp

omit [DecidableEq α] in
private theorem swapInd_cexpect_unifInl [Nonempty α] {κ : Type} [Fintype κ] [DecidableEq κ]
    (H : (κ → α ⊕ Unit) → ℂ) :
    ((swapIndUnifInl (α := α)).pi κ).cexpect H =
      ((FinProb.uniform (α := α)).pi κ).cexpect fun w => H (fun i => Sum.inl (w i)) := by
  unfold FinProb.cexpect
  symm
  refine Fintype.sum_of_injective (fun (w : κ → α) (i : κ) => Sum.inl (w i)) ?_ _ _ ?_ ?_
  · intro w w' h
    funext i
    exact Sum.inl_injective (congrFun h i)
  · intro y hy
    have : ∃ i, ∀ a, y i ≠ Sum.inl a := by
      by_contra hne
      push Not at hne
      exact hy ⟨fun i => (hne i).choose, funext fun i => (hne i).choose_spec.symm⟩
    obtain ⟨i, hi⟩ := this
    have h0 : (swapIndUnifInl (α := α)).prob (y i) = 0 := by
      rcases h : y i with a | u
      · exact absurd h (hi a)
      · simp [swapIndUnifInl]
    rw [FinProb.pi_prob, Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simp
  · intro w
    simp [FinProb.pi_prob, swapIndUnifInl, FinProb.uniform]

omit [DecidableEq α] in
private theorem swapInd_cexpect_diracInr {κ : Type} [Fintype κ] [DecidableEq κ]
    (H : (κ → α ⊕ Unit) → ℂ) :
    ((swapIndDiracInr (α := α)).pi κ).cexpect H = H (fun _ => Sum.inr ()) := by
  unfold FinProb.cexpect
  rw [Finset.sum_eq_single (fun _ => Sum.inr ())]
  · simp [FinProb.pi_prob, swapIndDiracInr]
  · intro y _ hy
    have : ∃ i, y i ≠ Sum.inr () := by
      by_contra hne
      push Not at hne
      exact hy (funext hne)
    obtain ⟨i, hi⟩ := this
    have h0 : (swapIndDiracInr (α := α)).prob (y i) = 0 := by
      rcases h : y i with a | u
      · simp [swapIndDiracInr]
      · exact absurd h hi
    rw [FinProb.pi_prob, Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simp
  · simp

/-- the real expectation as the real part of the complex one. -/
theorem swapInd_expect_eq_re {β : Type} [Fintype β] (π : FinProb β) (g : β → ℝ) :
    π.expect g = (π.cexpect fun b => ((g b : ℝ) : ℂ)).re := by
  simp only [FinProb.expect, FinProb.cexpect, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- one restriction drawn coordinate by coordinate (`swapFixLaw`) is the Bernoulli restriction
(`subsetExpect`, each coordinate fixed with probability `1 - ρ`) with uniform fixed values. -/
theorem swapInd_fixLaw_expect [Nonempty α] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (G : Finset ι → (ι → α) → ℝ) :
    ((swapFixLaw ρ h0 h1).pi ι).expect (fun s => G (swapFixLive s) (swapFixZ s)) =
      (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        ((FinProb.uniform (α := α)).pi ↥I).cexpect fun z =>
          ((G Iᶜ (fun i => if h : i ∈ I then z ⟨i, h⟩ else Classical.arbitrary α) : ℝ) : ℂ)).re := by
  have hmix : ∀ s, (swapFixLaw ρ h0 h1).prob s =
      (1 - ρ) * (swapIndUnifInl (α := α)).prob s +
        (1 - (1 - ρ)) * (swapIndDiracInr (α := α)).prob s := by
    rintro (a | u)
    · simp [swapFixLaw, swapIndUnifInl, swapIndDiracInr]
      ring
    · simp [swapFixLaw, swapIndUnifInl, swapIndDiracInr]
  rw [swapInd_expect_eq_re, ← restrict_key (by linarith) (by linarith) _ _ _ hmix]
  congr 2
  funext I
  rw [swapInd_cexpect_diracInr, swapInd_cexpect_unifInl]
  congr 1
  funext z
  have hL : swapFixLive (glueFree I (fun j => Sum.inl (z j))
      (fun _ => (Sum.inr () : α ⊕ Unit))) = Iᶜ := by
    ext i
    by_cases hi : i ∈ I <;> simp [swapFixLive, glueFree, hi]
  have hZ : swapFixZ (glueFree I (fun j => Sum.inl (z j)) (fun _ => (Sum.inr () : α ⊕ Unit))) =
      fun i => if h : i ∈ I then z ⟨i, h⟩ else Classical.arbitrary α := by
    funext i
    by_cases hi : i ∈ I <;> simp [swapFixZ, glueFree, hi]
  rw [hL, hZ]

/-! ### Item 1 / item 2 of `lemma:svdinc` against restrictions -/

omit [Fintype α] [DecidableEq α] [Fintype ι] in
/-- `swapIterFun F L z` reads `x` only on `L`. -/
theorem swapInd_iterFun_dep (F : (ι → α) → ℂ) (L : Finset ι) (z : ι → α) :
    ∀ x y : ι → α, (∀ i ∈ L, x i = y i) → swapIterFun F L z x = swapIterFun F L z y := by
  intro x y h
  unfold swapIterFun
  congr 1
  funext i
  by_cases hi : i ∈ L
  · simp [hi, h i hi]
  · simp [hi]

/-- item 1 / item 2 of `lemma:svdinc` transferred to the correlations of restrictions: if
`⟨F_{I→z}, P·v⟩ = κ ⟨u_{I→z}, P⟩` for every `I ⊆ A`, `z`, and every `P` of the coordinates of
`A \ I`, then for a live set `L ⊆ A` (the rest fixed to `w`)
`‖κ‖ 𝔼_w corr_L(u_w) ≤ ‖v‖_∞ 𝔼_w corr_L(F_w)`. -/
theorem swapInd_transfer [Nonempty α] (A A' : Finset ι) (hAA : ∀ i ∈ A, i ∉ A')
    (F u v : (ι → α) → ℂ) (κ : ℂ) {Hb : ℝ} (hHb : 0 ≤ Hb) (hv : ∀ x, ‖v x‖ ≤ Hb)
    (hvdep : SwapDependsOn A' v) (hudep : SwapDependsOn A u)
    (hFdep : ∀ x y : ι → α, (∀ i ∈ A, x i = y i) → (∀ i ∈ A', x i = y i) → F x = F y)
    (hid : ∀ I : Finset ι, I ⊆ A → ∀ (z : ι → α) (P : (ι → α) → ℂ), SwapDependsOn (A \ I) P →
      uinner (fun x => F (swapFixAt I z x)) (fun x => P x * v x) =
        κ * uinner (fun x => u (swapFixAt I z x)) P)
    (L : Finset ι) (hL : L ⊆ A) :
    ‖κ‖ * 𝔼 w : ι → α, swapIndCorr L (swapIterFun u L w) ≤
      Hb * 𝔼 w : ι → α, swapIndCorr L (swapIterFun F L w) := by
  have hw : ∀ w : ι → α, ‖κ‖ * swapIndCorr L (swapIterFun u L w) ≤
      Hb * 𝔼 v' : ι → α, swapIndCorr L (swapIterFun F L (A'.piecewise v' w)) := by
    intro w
    have hE0 : 0 ≤ 𝔼 v' : ι → α, swapIndCorr L (swapIterFun F L (A'.piecewise v' w)) :=
      Finset.expect_nonneg fun _ _ => swapIndCorr_nonneg _ _
    rcases eq_or_ne κ 0 with hκ | hκ
    · rw [hκ, norm_zero, zero_mul]
      positivity
    have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
    rw [← le_div_iff₀' hκ']
    refine swapIndCorr_le fun P hP => ?_
    rw [le_div_iff₀' hκ']
    have hQdep : ∀ x y : ι → α, (∀ i ∈ L, x i = y i) →
        ∏ i ∈ L, P i (x i) = ∏ i ∈ L, P i (y i) := fun x y h =>
      Finset.prod_congr rfl fun i hi => by rw [h i hi]
    have ha : 𝔼 x : ι → α, swapIterFun u L w x * star (∏ i ∈ L, P i (x i)) =
        uinner (fun x => u (swapFixAt (A \ L) w x)) (fun x => ∏ i ∈ L, P i (x i)) := by
      unfold uinner
      refine Finset.expect_congr rfl fun x _ => ?_
      congr 1
      refine hudep _ _ fun i hi => ?_
      by_cases hiL : i ∈ L
      · simp [swapFixAt, hiL]
      · simp [swapFixAt, hiL, hi]
    have hb := hid (A \ L) sdiff_subset w (fun x => ∏ i ∈ L, P i (x i))
      (fun x y h => hQdep x y fun i hi =>
        h i (mem_sdiff.2 ⟨hL hi, fun h' => (mem_sdiff.1 h').2 hi⟩))
    have hc : uinner (fun x => F (swapFixAt (A \ L) w x))
        (fun x => (∏ i ∈ L, P i (x i)) * v x) =
        𝔼 v' : ι → α, star (v v') *
          𝔼 x : ι → α, swapIterFun F L (A'.piecewise v' w) x * star (∏ i ∈ L, P i (x i)) := by
      unfold uinner
      rw [← expect_expect_piecewise A' (fun x => F (swapFixAt (A \ L) w x) *
        star ((∏ i ∈ L, P i (x i)) * v x))]
      refine Finset.expect_congr rfl fun v' _ => ?_
      rw [Finset.mul_expect]
      refine Finset.expect_congr rfl fun x _ => ?_
      have h1 : F (swapFixAt (A \ L) w (A'.piecewise v' x)) =
          swapIterFun F L (A'.piecewise v' w) x := by
        unfold swapIterFun
        refine hFdep _ _ (fun i hi => ?_) (fun i hi => ?_)
        · have hi' : i ∉ A' := hAA i hi
          by_cases hiL : i ∈ L
          · simp [swapFixAt, hiL, hi']
          · simp [swapFixAt, hiL, hi, hi']
        · have hiA : i ∉ A := fun h => hAA i h hi
          have hiL : i ∉ L := fun h => hiA (hL h)
          simp [swapFixAt, hiL, hiA, hi]
      have h2 : ∏ i ∈ L, P i ((A'.piecewise v' x) i) = ∏ i ∈ L, P i (x i) :=
        hQdep _ _ fun i hi => by
          have : i ∉ A' := hAA i (hL hi)
          simp [this]
      have h3 : v (A'.piecewise v' x) = v v' := hvdep _ _ fun i hi => by simp [hi]
      rw [h1, h2, h3, star_mul']
      ring
    calc ‖κ‖ * ‖𝔼 x : ι → α, swapIterFun u L w x * star (∏ i ∈ L, P i (x i))‖
        = ‖𝔼 v' : ι → α, star (v v') *
            𝔼 x : ι → α, swapIterFun F L (A'.piecewise v' w) x *
              star (∏ i ∈ L, P i (x i))‖ := by
          rw [ha, ← norm_mul, ← hb, hc]
      _ ≤ 𝔼 v' : ι → α, ‖star (v v') *
            𝔼 x : ι → α, swapIterFun F L (A'.piecewise v' w) x *
              star (∏ i ∈ L, P i (x i))‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 v' : ι → α, Hb * swapIndCorr L (swapIterFun F L (A'.piecewise v' w)) := by
          refine Finset.expect_le_expect fun v' _ => ?_
          rw [norm_mul, norm_star]
          exact mul_le_mul (hv v') (le_swapIndCorr P hP) (norm_nonneg _) hHb
      _ = Hb * 𝔼 v' : ι → α, swapIndCorr L (swapIterFun F L (A'.piecewise v' w)) :=
          (Finset.mul_expect _ _ _).symm
  calc ‖κ‖ * 𝔼 w : ι → α, swapIndCorr L (swapIterFun u L w)
      = 𝔼 w : ι → α, ‖κ‖ * swapIndCorr L (swapIterFun u L w) := Finset.mul_expect _ _ _
    _ ≤ 𝔼 w : ι → α, Hb * 𝔼 v' : ι → α,
          swapIndCorr L (swapIterFun F L (A'.piecewise v' w)) :=
        Finset.expect_le_expect fun w _ => hw w
    _ = Hb * 𝔼 w : ι → α, 𝔼 v' : ι → α,
          swapIndCorr L (swapIterFun F L (A'.piecewise v' w)) := by
        rw [Finset.mul_expect]
    _ = Hb * 𝔼 x : ι → α, swapIndCorr L (swapIterFun F L x) := by
        rw [Finset.expect_comm,
          expect_expect_piecewise A' (fun x => swapIndCorr L (swapIterFun F L x))]

/-! ### Generic helpers for `SwapInduct` -/

omit [DecidableEq α] in
/-- exchanging the fixing average and a `FinProb` average. -/
theorem swapInd_expect_comm {β : Type} [Fintype β] (π : FinProb β) (φ : β → (ι → α) → ℝ) :
    𝔼 w : ι → α, π.expect (fun b => φ b w) = π.expect (fun b => 𝔼 w : ι → α, φ b w) := by
  simp only [FinProb.expect]
  rw [Finset.expect_sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_expect]

omit [DecidableEq α] in
theorem swapInd_l2sq_smul (k : ℂ) (F : (ι → α) → ℂ) :
    l2sq (fun x => k * F x) = ‖k‖ ^ 2 * l2sq F := by
  unfold l2sq
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [norm_mul, mul_pow]

omit [DecidableEq α] in
theorem swapInd_val_smul (k : ℂ) (F : (ι → α) → ℂ) :
    val (fun x => k * F x) (fun x => k * F x) (fun x => k * F x) (fun x => k * F x) =
      ((‖k‖ ^ 4 : ℝ) : ℂ) * val F F F F := by
  have hk1 : k * star k = ((‖k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hk : k * k * star k * star k = ((‖k‖ ^ 4 : ℝ) : ℂ) := by
    calc k * k * star k * star k = (k * star k) * (k * star k) := by ring
      _ = _ := by rw [hk1]; push_cast; ring
  unfold val
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun y _ => ?_
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun b _ => ?_
  rw [← hk, star_mul', star_mul']
  ring

omit [DecidableEq α] in
open scoped Classical in
theorem swapInd_class_bound {K : ℕ} (C : SwapCoins ι α → (Fin K → SwapCoins ι α) → Prop)
    (X : SwapCoins ι α → (Fin K → SwapCoins ι α) → ℝ) {V : ℝ}
    (hX0 : ∀ c ω, 0 ≤ X c ω) (hXV : ∀ c ω, C c ω → V ≤ X c ω) :
    (𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, if C c₀ ω then (1 : ℝ) else 0) * V ≤
      𝔼 c₀ : SwapCoins ι α, 𝔼 ω : Fin K → SwapCoins ι α, X c₀ ω := by
  rw [Finset.expect_mul]
  refine Finset.expect_le_expect fun c₀ _ => ?_
  rw [Finset.expect_mul]
  refine Finset.expect_le_expect fun ω _ => ?_
  split_ifs with h
  · rw [one_mul]
    exact hXV c₀ ω h
  · rw [zero_mul]
    exact hX0 c₀ ω

theorem swapInd_half_pow (t : ℕ) (ρ : ℝ) : ρ = (1 / 2) ^ t * (2 ^ t * ρ) := by
  rw [← mul_assoc, ← mul_pow]
  norm_num

omit [DecidableEq α] in
/-- `ε² ≤ val(f)^{1/2}` from `ε⁴ ≤ val(f)`. -/
theorem swapInd_v2 {ε : ℝ} (hε0 : 0 < ε) (f : (ι → α) → ℂ) (hv : ε ^ 4 ≤ (val f f f f).re) :
    ε ^ 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) := by
  have h := Real.rpow_le_rpow (by positivity) hv (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e : (ε ^ 4) ^ (1 / 2 : ℝ) = ε ^ 2 := by
    rw [show ε ^ 4 = (ε ^ 2) ^ 2 by ring, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rwa [e] at h

theorem swapInd_l2 {ε : ℝ} (hε0 : 0 < ε) (f : (ι → α) → ℂ) (hv : ε ^ 4 ≤ (val f f f f).re) :
    ε ^ 2 ≤ l2sq f := by
  have h := hv.trans (svdInc_val_re_le f)
  have h' : (ε ^ 2) ^ 2 ≤ l2sq f ^ 2 := by rw [← pow_mul]; exact h
  exact (pow_le_pow_iff_left₀ (by positivity) (l2sq_nonneg f) (by norm_num)).1 h'

/-- `NV² = val/‖·‖₂⁴`. -/
theorem swapInd_NV_sq (F : (ι → α) → ℂ) :
    (((val F F F F).re) ^ (1 / 2 : ℝ) / l2sq F) ^ 2 = (val F F F F).re / l2sq F ^ 2 := by
  rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (val_re_nonneg_pair F F)]

/-- the real part of a restriction average of real values. -/
theorem swapInd_subsetExpect_re {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι]
    [DecidableEq ι] (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (π : FinProb α)
    (g : ∀ I : Finset ι, (↥I → α) → ℝ) :
    (subsetExpect q h0 h1 fun I => (π.pi ↥I).cexpect fun z => ((g I z : ℝ) : ℂ)).re =
      ((bernoulli q h0 h1).pi ι).expect
        (fun b => (π.pi ↥(trueSet b)).expect (g (trueSet b))) := by
  simp only [subsetExpect, FinProb.cexpect, FinProb.expect, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : (∑ z, ((π.pi ↥(trueSet b)).prob z : ℂ) * ((g (trueSet b) z : ℝ) : ℂ)) =
      ((∑ z, (π.pi ↥(trueSet b)).prob z * g (trueSet b) z : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e, ← Complex.ofReal_mul, Complex.ofReal_re]

omit [DecidableEq α] [Fintype α] in
theorem swapInd_F_init (f : (ι → α) → ℂ) (c₀ : SwapCoins ι α) {K : ℕ}
    (ω : Fin K → SwapCoins ι α) : swapIterF f (swapIterRun c₀ ω 0) = f := by
  funext x
  simp [swapIterF, swapIterFun, swapIterRun, swapIterInit]

omit [Fintype α] [DecidableEq α] [Fintype ι] in
theorem swapInd_F_dep (f : (ι → α) → ℂ) (st : SwapIterState ι α) :
    SwapDependsOn st.R (swapIterF f st) := by
  intro x y h
  unfold swapIterF swapIterFun
  congr 1
  funext i
  by_cases hi : i ∈ st.R
  · simp [hi, h i hi]
  · simp [hi]

omit [Fintype α] [DecidableEq α] [Fintype ι] in
theorem swapInd_fun_Z (f : (ι → α) → ℂ) (st : SwapIterState ι α) (L : Finset ι)
    (hL : L ⊆ st.R) (w : ι → α) :
    swapIterFun f L (swapIterZ st L w) = swapIterFun (swapIterF f st) L w := by
  funext x
  simp only [swapIterFun, swapIterF, swapIterZ]
  congr 1
  funext i
  by_cases hiL : i ∈ L
  · simp [hiL, hL hiL]
  · by_cases hiR : i ∈ st.R <;> simp [hiL, hiR]

end SwapInductAux

/-! ### Arithmetic -/

/-- the polynomial core of the `θ`-weight chain (`swapInd_mr32`). -/
theorem swapInd_mr32_poly {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 5) :
    (1 + a / 4) ^ 4 ≤ (1 + 5 * a) * (1 - a) ^ 2 := by
  have h1 : 0 ≤ a * (1 / 5 - a) := mul_nonneg ha0 (by linarith)
  have h3 : 0 ≤ a ^ 3 := by positivity
  have h4 : 0 ≤ a ^ 3 * (1 / 5 - a) := mul_nonneg h3 (by linarith)
  nlinarith [h1, h3, h4]

/-- The weight `θ`: with `θ = 2·10⁻¹²`, `(1 + ε²/10¹¹)(ε² - θε⁵)² ≥ (ε + θε⁴/4)⁴` for
`0 < ε ≤ 1`. -/
theorem swapInd_mr32 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (ε + 2 / 10 ^ 12 * ε ^ 4 / 4) ^ 4 ≤
      (1 + ε ^ 2 / 10 ^ 11) * (ε ^ 2 - 2 / 10 ^ 12 * ε ^ 5) ^ 2 := by
  have hε3 : ε ^ 3 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hε32 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a, a = 2 / 10 ^ 12 * ε ^ 3 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a ≤ 1 / 5 := by rw [ha]; nlinarith
  have h5 : 1 + 5 * a ≤ 1 + ε ^ 2 / 10 ^ 11 := by rw [ha]; nlinarith
  have e1 : ε + 2 / 10 ^ 12 * ε ^ 4 / 4 = ε * (1 + a / 4) := by rw [ha]; ring
  have e2 : ε ^ 2 - 2 / 10 ^ 12 * ε ^ 5 = ε ^ 2 * (1 - a) := by rw [ha]; ring
  rw [e1, e2]
  have hp := swapInd_mr32_poly ha0 ha1
  have hε4 : 0 ≤ ε ^ 4 := by positivity
  have h1a : 0 ≤ (1 - a) ^ 2 := sq_nonneg _
  calc (ε * (1 + a / 4)) ^ 4 = ε ^ 4 * (1 + a / 4) ^ 4 := by ring
    _ ≤ ε ^ 4 * ((1 + 5 * a) * (1 - a) ^ 2) := mul_le_mul_of_nonneg_left hp hε4
    _ ≤ ε ^ 4 * ((1 + ε ^ 2 / 10 ^ 11) * (1 - a) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 h1a) hε4
    _ = (1 + ε ^ 2 / 10 ^ 11) * (ε ^ 2 * (1 - a)) ^ 2 := by ring

/-! ### The exponent of the recursion solution -/

/-- a uniform bound `T₀ = 8·10⁵² M¹⁶` on the number of steps `T = ⌈8/(c⁴ε¹⁶)⌉` for `ε ≥ 1/M`. -/
def swapIndT0 (M : ℕ) : ℕ := 8 * 10 ^ 52 * M ^ 16

/-- the exponent increment per unit of the `a`-exponent. -/
def swapIndV0 (M : ℕ) : ℕ := 37 + 27 * swapIndT0 M

/-- the exponent increment per step. -/
def swapIndW0 (M : ℕ) : ℕ :=
  (49 + 27 * swapIndT0 M) * swapIndT0 M + 3 * swapIndT0 M + (49 + 27 * swapIndT0 M)

/-- the number of steps `ε ↦ ε + θε⁴/4` needed from `ε ≥ 1/M` to `0.99`. -/
def swapIndN (M : ℕ) : ℕ := 2 * 10 ^ 12 * M ^ 4

/-- the exponent of `ε₀/(2B)` after `n` steps. -/
def swapIndHH (M n : ℕ) : ℕ := 1 + n * (2 * swapIndT0 M + 1)

/-- the exponent of `2^{-(M+50)}` after `n` steps. -/
def swapIndEE (M n : ℕ) : ℕ := n * (swapIndW0 M + swapIndV0 M * swapIndHH M n)

/-- `E ≤ A M^d` for all `M ≥ 1`. -/
private def SwapIndPolyBdd (E : ℕ → ℕ) : Prop := ∃ A d : ℕ, ∀ M : ℕ, 1 ≤ M → E M ≤ A * M ^ d

private theorem pb_const (c : ℕ) : SwapIndPolyBdd (fun _ => c) := ⟨c, 0, fun M _ => by simp⟩

private theorem pb_id : SwapIndPolyBdd (fun M => M) := ⟨1, 1, fun M _ => by simp⟩

private theorem pb_add {E F : ℕ → ℕ} (hE : SwapIndPolyBdd E) (hF : SwapIndPolyBdd F) :
    SwapIndPolyBdd (fun M => E M + F M) := by
  obtain ⟨A, d, h⟩ := hE
  obtain ⟨A', d', h'⟩ := hF
  refine ⟨A + A', d + d', fun M hM => ?_⟩
  have h1 : M ^ d ≤ M ^ (d + d') := Nat.pow_le_pow_right hM (by omega)
  have h2 : M ^ d' ≤ M ^ (d + d') := Nat.pow_le_pow_right hM (by omega)
  calc E M + F M ≤ A * M ^ d + A' * M ^ d' := Nat.add_le_add (h M hM) (h' M hM)
    _ ≤ A * M ^ (d + d') + A' * M ^ (d + d') :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (A + A') * M ^ (d + d') := by ring

private theorem pb_mul {E F : ℕ → ℕ} (hE : SwapIndPolyBdd E) (hF : SwapIndPolyBdd F) :
    SwapIndPolyBdd (fun M => E M * F M) := by
  obtain ⟨A, d, h⟩ := hE
  obtain ⟨A', d', h'⟩ := hF
  refine ⟨A * A', d + d', fun M hM => ?_⟩
  calc E M * F M ≤ (A * M ^ d) * (A' * M ^ d') := Nat.mul_le_mul (h M hM) (h' M hM)
    _ = A * A' * M ^ (d + d') := by ring

private theorem pb_pow {E : ℕ → ℕ} (hE : SwapIndPolyBdd E) (k : ℕ) :
    SwapIndPolyBdd (fun M => E M ^ k) := by
  induction k with
  | zero => simpa using pb_const 1
  | succ k ih =>
    have e : (fun M => E M ^ (k + 1)) = fun M => E M ^ k * E M := funext fun M => pow_succ _ _
    rw [e]
    exact pb_mul ih hE

/-- the exponent of the solved recursion is polynomial in `M = ⌈1/ε⌉`: an absolute `K` with
`(M + 50) e_N + h_N ≤ K M^K`. -/
theorem swapInd_poly : ∃ K : ℕ, 1 ≤ K ∧ ∀ M : ℕ, 1 ≤ M →
    (M + 50) * swapIndEE M (swapIndN M) + swapIndHH M (swapIndN M) ≤ K * M ^ K := by
  have hT : SwapIndPolyBdd swapIndT0 := pb_mul (pb_const _) (pb_pow pb_id 16)
  have hN : SwapIndPolyBdd swapIndN := pb_mul (pb_const _) (pb_pow pb_id 4)
  have hV : SwapIndPolyBdd swapIndV0 := pb_add (pb_const _) (pb_mul (pb_const _) hT)
  have hW : SwapIndPolyBdd swapIndW0 :=
    pb_add (pb_add (pb_mul (pb_add (pb_const _) (pb_mul (pb_const _) hT)) hT)
      (pb_mul (pb_const _) hT)) (pb_add (pb_const _) (pb_mul (pb_const _) hT))
  have hH : SwapIndPolyBdd (fun M => swapIndHH M (swapIndN M)) :=
    pb_add (pb_const _) (pb_mul hN (pb_add (pb_mul (pb_const _) hT) (pb_const _)))
  have hE : SwapIndPolyBdd (fun M => swapIndEE M (swapIndN M)) :=
    pb_mul hN (pb_add hW (pb_mul hV hH))
  obtain ⟨A, d, h⟩ := pb_add (pb_mul (pb_add pb_id (pb_const 50)) hE) hH
  refine ⟨A + d + 1, by omega, fun M hM => ?_⟩
  calc (M + 50) * swapIndEE M (swapIndN M) + swapIndHH M (swapIndN M) ≤ A * M ^ d := h M hM
    _ ≤ (A + d + 1) * M ^ (A + d + 1) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hM (by omega))

end TrackB
end RestrictedPolynomials
end
