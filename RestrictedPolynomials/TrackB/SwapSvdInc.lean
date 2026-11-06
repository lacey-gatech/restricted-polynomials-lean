module

public import RestrictedPolynomials.TrackB.SwapSvdIncAux

/-!
# Track B: `lemma:svdinc` (CSP_6)

Source: CSP_6 (arXiv:2411.15133v1 `main.tex`) L937-1035 (`lemma:svdinc` with its three cases),
L959-981 (`eq:lowerF`), L997-1009 (`eq:valf`).
Covers CSP_6 `eq:lowerF`, `eq:valf`, `lemma:svdinc` and `#case1`, `#case2a`, `#case2b`.

Reading of the source used here: explicit constants, raw `f`, Case 2a renormalises `h`.
The proof infrastructure is in `SwapSvdIncAux.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SwapSvdInc
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `u` depends only on the coordinates in `A`. -/
def SwapDependsOn (A : Finset ι) (u : (ι → α) → ℂ) : Prop :=
  ∀ x y : ι → α, (∀ i ∈ A, x i = y i) → u x = u y

/-- the point `x` with the coordinates of `I` fixed to `z`. -/
def swapFixAt (I : Finset ι) (z : ι → α) (x : ι → α) : ι → α :=
  fun i => if i ∈ I then z i else x i

/-- the conclusion of CSP_6 `lemma:svdinc` for `f = f_t` with live set `R`, `S = S_t`, `T = R \ S`: unit
vectors `g` (on `S`) and `h` (on `T`) and a constant `η` such that item 1 or item 2 holds. -/
def SwapSvdIncOut (c ε B : ℝ) (R S : Finset ι) (f : (ι → α) → ℂ) : Prop :=
  ∃ (g h : (ι → α) → ℂ) (η : ℂ),
    l2sq g = 1 ∧ l2sq h = 1 ∧
    (∀ x, ‖g x‖ ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f))) ∧
    (∀ x, ‖h x‖ ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f))) ∧
    c ^ 2 * ε ^ 9 / 6 ≤ ‖η‖ ∧
    ((SwapDependsOn S g ∧ SwapDependsOn (R \ S) h ∧
      (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) ≤ (val g g g g).re ∧
      ∀ (I : Finset ι), I ⊆ S → ∀ (z : ι → α) (P : (ι → α) → ℂ), SwapDependsOn (S \ I) P →
        uinner (fun x => f (swapFixAt I z x)) (fun x => P x * h x) =
          η * (Real.sqrt (l2sq f) : ℂ) * uinner (fun x => g (swapFixAt I z x)) P) ∨
     (SwapDependsOn S g ∧ SwapDependsOn (R \ S) h ∧
      (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) ≤ (val h h h h).re ∧
      ∀ (I : Finset ι), I ⊆ R \ S → ∀ (z : ι → α) (P : (ι → α) → ℂ),
        SwapDependsOn ((R \ S) \ I) P →
        uinner (fun x => f (swapFixAt I z x)) (fun x => g x * P x) =
          η * (Real.sqrt (l2sq f) : ℂ) * uinner (fun x => h (swapFixAt I z x)) P))

/-! ### Helpers -/

private lemma sic_swapNorm_sq (u : (ι → α) → ℂ) :
    swapNorm u ^ 2 = ((val u u u u).re) ^ (1 / 2 : ℝ) := by
  rw [swapNorm, ← Real.rpow_natCast, ← Real.rpow_mul (val_re_nonneg_pair u u)]
  norm_num

/-- consequences of `hnv` -/
private lemma sic_hnv {ε : ℝ} (hε0 : 0 < ε) (f : (ι → α) → ℂ)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f) :
    0 < l2sq f ∧ ε * Real.sqrt (l2sq f) ≤ 2 * swapNorm f := by
  have h0 := l2sq_nonneg f
  have hpos : 0 < l2sq f := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hnv; simp at hnv; nlinarith [sq_nonneg ε]
  refine ⟨hpos, ?_⟩
  have h1 : ε ^ 2 / 2 * l2sq f ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) := by
    rwa [le_div_iff₀ hpos] at hnv
  rw [← sic_swapNorm_sq] at h1
  have hs := swapNorm_nonneg f
  have hL := Real.sq_sqrt h0
  have h2 : (ε * Real.sqrt (l2sq f)) ^ 2 ≤ (2 * swapNorm f) ^ 2 := by
    rw [mul_pow, hL]; nlinarith [sq_nonneg (swapNorm f)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h2

/-- consequence of `hΔ` -/
private lemma sic_hΔ {c ε : ℝ} (hc0 : 0 < c) (f Δ : (ι → α) → ℂ)
    (hΔ : ((val Δ Δ Δ Δ).re) ^ (1 / 2 : ℝ) ≤ c ^ 2 * ε ^ 8 * l2sq f) :
    swapNorm Δ ≤ c * ε ^ 4 * Real.sqrt (l2sq f) := by
  have h0 := l2sq_nonneg f
  rw [← sic_swapNorm_sq] at hΔ
  have h2 : swapNorm Δ ^ 2 ≤ (c * ε ^ 4 * Real.sqrt (l2sq f)) ^ 2 := by
    calc swapNorm Δ ^ 2 ≤ _ := hΔ
      _ = _ := by rw [mul_pow, Real.sq_sqrt h0]; ring
  exact (pow_le_pow_iff_left₀ (swapNorm_nonneg _) (by positivity) (by norm_num)).1 h2

/-- the kept index set of the scheme -/
private def sicK (c ε : ℝ) {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (t : ℕ) :
    Finset (Fin d.r) :=
  Finset.univ.filter fun i : Fin d.r => i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i

private lemma sic_card_lt (r t : ℕ) : (Finset.univ.filter fun i : Fin r => i.val < t).card ≤ t := by
  calc _ ≤ (Finset.range t).card :=
        Finset.card_le_card_of_injOn (fun i : Fin r => i.val)
          (fun i hi => by simpa using (Finset.mem_filter.1 hi).2)
          (fun i _ j _ h => Fin.ext h)
    _ = t := Finset.card_range t

private lemma sic_swapNorm_truncOn_le {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f)
    (x₀ : ι → α) (s : Finset (Fin d.r)) : swapNorm (d.truncOn s) ≤ ∑ i ∈ s, d.lam i := by
  have e : d.truncOn s = fun x => ∑ i ∈ s, (d.lam i : ℂ) * prodSplit S (d.g i) (d.h i) x := rfl
  rw [e]
  refine (svdInc_swapNorm_sum_le s (fun i => fun x => (d.lam i : ℂ) * prodSplit S (d.g i) (d.h i) x)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (fun x => (d.lam i : ℂ) * prodSplit S (d.g i) (d.h i) x) =
      (d.lam i : ℂ) • prodSplit S (d.g i) (d.h i) := rfl
  rw [h1, swapNorm_smul]
  have hg : l2sq (d.g i) = 1 := by
    have := svdInc_ofReal_l2sq (d.g i)
    rw [d.isJSVD.orth_g i i, if_pos rfl] at this
    exact_mod_cast this
  have hh : l2sq (d.h i) = 1 := by
    have := svdInc_ofReal_l2sq (d.h i)
    rw [d.isJSVD.orth_h i i, if_pos rfl] at this
    exact_mod_cast this
  have := svdInc_swapNorm_prodSplit_le_one (S := S) (d.g i) (d.h i) hg hh
  rw [Complex.norm_real, Real.norm_of_nonneg (svdInc_lam_pos d i).le]
  nlinarith [svdInc_lam_pos d i]

private lemma sic_lowerF_core {c ε : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S : Finset ι) (d : SwapSvdData S f) (t : ℕ)
    (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f) :
    swapNorm (fun x => f x - d.truncOn (sicK c ε d t) x) ≤
        2 * c * ε ^ 4 * Real.sqrt (l2sq f) ∧
      (1 - 4 * c * ε ^ 2) * swapNorm f ≤ swapNorm (d.truncOn (sicK c ε d t)) ∧
      ∀ i ∈ sicK c ε d t, c ^ 5 * ε ^ 20 / 9 * Real.sqrt (l2sq f) ≤ d.lam i := by
  obtain ⟨hpos, hε⟩ := sic_hnv hε0 f hnv
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  set L := Real.sqrt (l2sq f) with hLdef
  have hL : 0 < L := Real.sqrt_pos.2 hpos
  have hA : swapNorm (fun x => f x - d.truncOn (sicK c ε d t) x) ≤ 2 * c * ε ^ 4 * L := by
    set Tt : Finset (Fin d.r) := Finset.univ.filter fun i : Fin d.r => i.val < t with hTt
    set A : Finset (Fin d.r) := Tt.filter fun i => ¬ (c * ε ^ 4 * L / t ≤ d.lam i) with hAdef
    have hK : Tt.filter (fun i => c * ε ^ 4 * L / t ≤ d.lam i) = sicK c ε d t := by
      ext i; simp [sicK, hTt, hLdef]
    have hpt : ∀ x, f x - d.truncOn (sicK c ε d t) x =
        (f x - d.trunc t x) + d.truncOn A x := by
      intro x
      have h1 := Finset.sum_filter_add_sum_filter_not Tt (fun i => c * ε ^ 4 * L / t ≤ d.lam i)
        (fun i => (d.lam i : ℂ) * (svdIncG d i x * svdIncH d i x))
      rw [hK] at h1
      have e1 : d.trunc t x = ∑ i ∈ Tt, (d.lam i : ℂ) * (svdIncG d i x * svdIncH d i x) :=
        svdInc_truncOn_apply d _ x
      have e2 : d.truncOn (sicK c ε d t) x =
          ∑ i ∈ sicK c ε d t, (d.lam i : ℂ) * (svdIncG d i x * svdIncH d i x) :=
        svdInc_truncOn_apply d _ x
      have e3 : d.truncOn A x = ∑ i ∈ A, (d.lam i : ℂ) * (svdIncG d i x * svdIncH d i x) :=
        svdInc_truncOn_apply d _ x
      rw [e1, e2, e3, ← h1]
      ring
    have hfun : (fun x => f x - d.truncOn (sicK c ε d t) x) =
        (fun x => f x - d.trunc t x) + d.truncOn A := by
      funext x; exact hpt x
    rw [hfun]
    refine (swapNorm_add_le _ _).trans ?_
    have h1 := sic_hΔ hc0 f _ hΔ
    have h2 := sic_swapNorm_truncOn_le d x₀ A
    have h3 : ∑ i ∈ A, d.lam i ≤ c * ε ^ 4 * L := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · have : A = ∅ := by
          ext i; simp [hAdef, hTt, h0]
        rw [this]; simp; positivity
      · have htpos : (0 : ℝ) < t := by exact_mod_cast h0
        calc ∑ i ∈ A, d.lam i ≤ ∑ i ∈ A, c * ε ^ 4 * L / t := by
              refine Finset.sum_le_sum fun i hi => ?_
              have := (Finset.mem_filter.1 hi).2
              exact (not_le.1 this).le
          _ = A.card * (c * ε ^ 4 * L / t) := by simp
          _ ≤ t * (c * ε ^ 4 * L / t) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have : A.card ≤ t := (Finset.card_filter_le _ _).trans (sic_card_lt d.r t)
              exact_mod_cast this
          _ = c * ε ^ 4 * L := by field_simp
    linarith
  refine ⟨hA, ?_, ?_⟩
  · have hdec : f = fun x => (fun x => f x - d.truncOn (sicK c ε d t) x) x + d.truncOn (sicK c ε d t) x := by
      funext x; ring
    have h1 : swapNorm f ≤ swapNorm (fun x => f x - d.truncOn (sicK c ε d t) x) +
        swapNorm (d.truncOn (sicK c ε d t)) := by
      conv_lhs => rw [hdec]
      exact swapNorm_add_le (fun x => f x - d.truncOn (sicK c ε d t) x) _
    have h2 : 2 * c * ε ^ 4 * L ≤ 4 * c * ε ^ 2 * swapNorm f := by
      have : ε ^ 2 * L ≤ 2 * swapNorm f := by
        have : ε ^ 2 * L ≤ ε * L := by
          have := mul_le_mul_of_nonneg_right (show ε ^ 2 ≤ ε by nlinarith) hL.le
          exact this
        linarith
      have h5 := mul_le_mul_of_nonneg_left this (show 0 ≤ c * ε ^ 2 by positivity)
      nlinarith [h5]
    nlinarith
  · intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    have htpos : (0 : ℝ) < t := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hi'.1)
    refine le_trans ?_ hi'.2
    rw [le_div_iff₀ htpos]
    have : c ^ 5 * ε ^ 20 / 9 * L * t = c * ε ^ 4 * L * ((t : ℝ) * (c ^ 4 * ε ^ 16) / 9) := by ring
    rw [this]
    have h9 : (t : ℝ) * (c ^ 4 * ε ^ 16) / 9 ≤ 1 := by linarith
    have : 0 ≤ c * ε ^ 4 * L := by positivity
    nlinarith

/-- CSP_6 `eq:lowerF`. -/
theorem swap_lowerF {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f) :
    swapNorm (fun x => f x - d.truncOn (Finset.univ.filter fun i : Fin d.r =>
        i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i) x) ≤
        2 * c * ε ^ 4 * Real.sqrt (l2sq f) ∧
      (1 - 4 * c * ε ^ 2) * swapNorm f ≤
        swapNorm (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
          i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i)) ∧
      ∀ i ∈ Finset.univ.filter (fun i : Fin d.r =>
          i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i),
        c ^ 5 * ε ^ 20 / 9 * Real.sqrt (l2sq f) ≤ d.lam i := by
  exact sic_lowerF_core hc0 hc1 hε0 hε1 f S d t ht hΔ hnv

/-- CSP_6 `eq:valf`. -/
theorem swap_valf {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f) :
    (val f f f f).re * (1 - 16 * c * ε ^ 2) ≤
        (val (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))).re ∧
      (val (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))).re ≤
        (swapValOn Sᶜ (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))
          (d.truncOn (Finset.univ.filter fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i))).re := by
  obtain ⟨-, h2, -⟩ := sic_lowerF_core hc0 hc1 hε0 hε1 f S d t ht hΔ hnv
  refine ⟨?_, val_le_swapValOn _ _⟩
  have hs := swapNorm_nonneg f
  have hx : 0 ≤ 1 - 4 * c * ε ^ 2 := by nlinarith [mul_pos hc0 (sq_pos_of_pos hε0), pow_le_one₀ hε0.le hε1 (n := 2)]
  have h4 := pow_le_pow_left₀ (mul_nonneg hx hs) h2 4
  rw [swapNorm_pow_four, mul_pow, swapNorm_pow_four] at h4
  have hb : 1 + (4 : ℕ) * (-(4 * c * ε ^ 2)) ≤ (1 + -(4 * c * ε ^ 2)) ^ 4 :=
    one_add_mul_le_pow (by nlinarith [mul_pos hc0 (sq_pos_of_pos hε0), pow_le_one₀ hε0.le hε1 (n := 2)]) 4
  have hv := val_re_nonneg_pair f f
  calc (val f f f f).re * (1 - 16 * c * ε ^ 2) ≤ (val f f f f).re * (1 + -(4 * c * ε ^ 2)) ^ 4 := by
        apply mul_le_mul_of_nonneg_left _ hv; push_cast at hb; linarith
    _ = (1 - 4 * c * ε ^ 2) ^ 4 * (val f f f f).re := by ring
    _ ≤ _ := h4


/-! ### The two identities -/

private lemma sic_fix_agree_S {S I : Finset ι} (hI : I ⊆ Sᶜ) (z x : ι → α) :
    ∀ k ∈ S, swapFixAt I z x k = x k := by
  intro k hk
  simp only [swapFixAt]
  rw [if_neg]
  intro h
  exact (Finset.mem_compl.1 (hI h)) hk

private lemma sic_fix_agree_C {S I : Finset ι} (hI : I ⊆ S) (z x : ι → α) :
    ∀ k ∈ Sᶜ, swapFixAt I z x k = x k := by
  intro k hk
  simp only [swapFixAt]
  rw [if_neg]
  intro h
  exact (Finset.mem_compl.1 hk) (hI h)

private lemma sic_uinner_GH {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (j i : Fin d.r) (A B : (ι → α) → ℂ)
    (hA : ∀ x y : ι → α, (∀ k ∈ Sᶜ, x k = y k) → A x = A y)
    (hB : ∀ x y : ι → α, (∀ k ∈ Sᶜ, x k = y k) → B x = B y) :
    uinner (fun x => svdIncG d j x * A x) (fun x => svdIncG d i x * B x) =
      (if j = i then 1 else 0) * uinner A B := by
  have hk : ∀ x, svdIncG d j x * A x * star (svdIncG d i x * B x) =
      (svdIncG d j x * star (svdIncG d i x)) * (A x * star (B x)) := by
    intro x; rw [star_mul']; ring
  have ho := svdInc_orth_G d x₀ j i
  unfold uinner at ho ⊢
  simp only [hk]
  rw [svdInc_expect_mul_dep S x₀ _ _
    (fun x y h => by rw [svdInc_G_dep d j x y h, svdInc_G_dep d i x y h])
    (fun x y h => by rw [hA x y h, hB x y h]), ho]

private lemma sic_uinner_HG {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (j i : Fin d.r) (A B : (ι → α) → ℂ)
    (hA : ∀ x y : ι → α, (∀ k ∈ S, x k = y k) → A x = A y)
    (hB : ∀ x y : ι → α, (∀ k ∈ S, x k = y k) → B x = B y) :
    uinner (fun x => A x * svdIncH d j x) (fun x => B x * svdIncH d i x) =
      uinner A B * (if j = i then 1 else 0) := by
  have hk : ∀ x, A x * svdIncH d j x * star (B x * svdIncH d i x) =
      (A x * star (B x)) * (svdIncH d j x * star (svdIncH d i x)) := by
    intro x; rw [star_mul']; ring
  have ho := svdInc_orth_H d x₀ j i
  unfold uinner at ho ⊢
  simp only [hk]
  rw [svdInc_expect_mul_dep S x₀ _ _
    (fun x y h => by rw [hA x y h, hB x y h])
    (fun x y h => by rw [svdInc_H_dep_compl d j x y h, svdInc_H_dep_compl d i x y h]), ho]

/-- item 2 identity, for a combination `g = ∑_{i ∈ s} aᵢ Gᵢ` -/
private lemma sic_id2 {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (s : Finset (Fin d.r)) (a : Fin d.r → ℂ) (I : Finset ι) (hI : I ⊆ Sᶜ) (z : ι → α)
    (P : (ι → α) → ℂ) (hP : ∀ x y : ι → α, (∀ k ∈ Sᶜ, x k = y k) → P x = P y) :
    uinner (fun x => f (swapFixAt I z x)) (fun x => (∑ i ∈ s, a i * svdIncG d i x) * P x) =
      ∑ i ∈ s, (d.lam i : ℂ) * star (a i) *
        uinner (fun x => svdIncH d i (swapFixAt I z x)) P := by
  have h1 : (fun x => f (swapFixAt I z x)) = fun x => ∑ j, (d.lam j : ℂ) *
      (svdIncG d j x * svdIncH d j (swapFixAt I z x)) := by
    funext x
    rw [svdInc_decomp d (swapFixAt I z x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [svdInc_G_dep d j _ x (sic_fix_agree_S hI z x)]
  have h2 : (fun x => (∑ i ∈ s, a i * svdIncG d i x) * P x) =
      fun x => ∑ i ∈ s, a i * (svdIncG d i x * P x) := by
    funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, svdInc_uinner_lin Finset.univ s (fun j => (d.lam j : ℂ)) a
    (fun j x => svdIncG d j x * svdIncH d j (swapFixAt I z x)) (fun i x => svdIncG d i x * P x)]
  have hdep : ∀ j : Fin d.r, ∀ x y : ι → α, (∀ k ∈ Sᶜ, x k = y k) →
      svdIncH d j (swapFixAt I z x) = svdIncH d j (swapFixAt I z y) := by
    intro j x y h
    apply svdInc_H_dep_compl
    intro k hk
    simp only [swapFixAt]
    by_cases hkI : k ∈ I <;> simp [hkI, h k hk]
  simp only [sic_uinner_GH d x₀ _ _ _ _ (hdep _) hP]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- item 1 identity for a single singular index -/
private lemma sic_id1 {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (i : Fin d.r) (I : Finset ι) (hI : I ⊆ S) (z : ι → α) (P : (ι → α) → ℂ)
    (hP : ∀ x y : ι → α, (∀ k ∈ S, x k = y k) → P x = P y) :
    uinner (fun x => f (swapFixAt I z x)) (fun x => P x * svdIncH d i x) =
      (d.lam i : ℂ) * uinner (fun x => svdIncG d i (swapFixAt I z x)) P := by
  have h1 : (fun x => f (swapFixAt I z x)) = fun x => ∑ j, (d.lam j : ℂ) *
      (svdIncG d j (swapFixAt I z x) * svdIncH d j x) := by
    funext x
    rw [svdInc_decomp d (swapFixAt I z x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [svdInc_H_dep_compl d j _ x (sic_fix_agree_C hI z x)]
  have h2 : (fun x => P x * svdIncH d i x) = fun x => ∑ j ∈ ({i} : Finset (Fin d.r)),
      (1 : ℂ) * (P x * svdIncH d j x) := by
    funext x; simp
  rw [h1, h2, svdInc_uinner_lin Finset.univ {i} (fun j => (d.lam j : ℂ)) (fun _ => (1 : ℂ))
    (fun j x => svdIncG d j (swapFixAt I z x) * svdIncH d j x) (fun j x => P x * svdIncH d j x)]
  have hdep : ∀ j : Fin d.r, ∀ x y : ι → α, (∀ k ∈ S, x k = y k) →
      svdIncG d j (swapFixAt I z x) = svdIncG d j (swapFixAt I z y) := by
    intro j x y h
    apply svdInc_G_dep
    intro k hk
    simp only [swapFixAt]
    by_cases hkI : k ∈ I <;> simp [hkI, h k hk]
  simp only [sic_uinner_HG d x₀ _ _ _ _ (hdep _) hP]
  simp

/-! ### Assembling the output for a single singular pair -/

private lemma sic_val_one {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty (κ → α)] :
    val (fun _ : κ → α => (1 : ℂ)) (fun _ => 1) (fun _ => 1) (fun _ => 1) = 1 := by
  simp [val]

private lemma sic_val_G {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (i : Fin d.r) :
    val (svdIncG d i) (svdIncG d i) (svdIncG d i) (svdIncG d i) =
      val (d.g i) (d.g i) (d.g i) (d.g i) := by
  haveI : Nonempty (↥Sᶜ → α) := ⟨fun k => x₀ k⟩
  unfold svdIncG
  rw [val_prodSplit_self, sic_val_one, mul_one]

private lemma sic_val_H {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (i : Fin d.r) :
    val (svdIncH d i) (svdIncH d i) (svdIncH d i) (svdIncH d i) =
      val (d.h i) (d.h i) (d.h i) (d.h i) := by
  haveI : Nonempty (↥S → α) := ⟨fun k => x₀ k⟩
  unfold svdIncH
  rw [val_prodSplit_self, sic_val_one, one_mul]

private lemma sic_l2sq_G {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (i : Fin d.r) : l2sq (svdIncG d i) = 1 := by
  have := svdInc_ofReal_l2sq (svdIncG d i)
  rw [svdInc_orth_G d x₀ i i, if_pos rfl] at this
  exact_mod_cast this

private lemma sic_l2sq_H {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (i : Fin d.r) : l2sq (svdIncH d i) = 1 := by
  have := svdInc_ofReal_l2sq (svdIncH d i)
  rw [svdInc_orth_H d x₀ i i, if_pos rfl] at this
  exact_mod_cast this

private lemma sic_out_of_single {c ε B : ℝ} {f : (ι → α) → ℂ} (R S : Finset ι)
    (hdep : SwapDependsOn R f) (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f)
    (hpos : 0 < l2sq f) (i : Fin d.r)
    (hη : c ^ 2 * ε ^ 9 / 6 ≤ d.lam i / Real.sqrt (l2sq f))
    (hbd : B / d.lam i ≤ 27 * B / (c ^ 7 * ε ^ 28 * Real.sqrt (l2sq f)))
    (hgain : (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) ≤
        (val (d.g i) (d.g i) (d.g i) (d.g i)).re ∨
      (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) ≤
        (val (d.h i) (d.h i) (d.h i) (d.h i)).re) :
    SwapSvdIncOut c ε B R S f := by
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  have hL : 0 < Real.sqrt (l2sq f) := Real.sqrt_pos.2 hpos
  have hlam := svdInc_lam_pos d i
  have hbs := svdInc_bounds hB d i
  have hLc : ((d.lam i / Real.sqrt (l2sq f) : ℝ) : ℂ) * (Real.sqrt (l2sq f) : ℂ) = (d.lam i : ℂ) := by
    have : (Real.sqrt (l2sq f) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
  have hdS : SwapDependsOn S (svdIncG d i) := fun x y h => svdInc_G_dep d i x y h
  have hdH : SwapDependsOn (R \ S) (svdIncH d i) := fun x y h => svdInc_H_dep hdep d i x y h
  have hid1 : ∀ (I : Finset ι), I ⊆ S → ∀ (z : ι → α) (P : (ι → α) → ℂ), SwapDependsOn (S \ I) P →
      uinner (fun x => f (swapFixAt I z x)) (fun x => P x * svdIncH d i x) =
        ((d.lam i / Real.sqrt (l2sq f) : ℝ) : ℂ) * (Real.sqrt (l2sq f) : ℂ) *
          uinner (fun x => svdIncG d i (swapFixAt I z x)) P := by
    intro I hI z P hP
    rw [hLc]
    refine sic_id1 d x₀ i I hI z P (fun x y h => hP x y (fun k hk => h k ?_))
    exact (Finset.mem_sdiff.1 hk).1
  have hid2 : ∀ (I : Finset ι), I ⊆ R \ S → ∀ (z : ι → α) (P : (ι → α) → ℂ),
      SwapDependsOn ((R \ S) \ I) P →
      uinner (fun x => f (swapFixAt I z x)) (fun x => svdIncG d i x * P x) =
        ((d.lam i / Real.sqrt (l2sq f) : ℝ) : ℂ) * (Real.sqrt (l2sq f) : ℂ) *
          uinner (fun x => svdIncH d i (swapFixAt I z x)) P := by
    intro I hI z P hP
    rw [hLc]
    have hIc : I ⊆ Sᶜ := fun k hk => Finset.mem_compl.2 (Finset.mem_sdiff.1 (hI hk)).2
    have := sic_id2 d x₀ {i} (fun _ => 1) I hIc z P (fun x y h => hP x y (fun k hk => h k (by
      have := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hk).1).2
      exact Finset.mem_compl.2 this)))
    simpa using this
  refine ⟨svdIncG d i, svdIncH d i, ((d.lam i / Real.sqrt (l2sq f) : ℝ) : ℂ), sic_l2sq_G d x₀ i,
    sic_l2sq_H d x₀ i, fun x => (hbs.1 x).trans hbd, fun x => (hbs.2 x).trans hbd, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; exact hη
  · rcases hgain with hg | hg
    · left
      refine ⟨hdS, hdH, ?_, hid1⟩
      rw [sic_val_G d x₀ i]; exact hg
    · right
      refine ⟨hdS, hdH, ?_, hid2⟩
      rw [sic_val_H d x₀ i]; exact hg

/-! ### Numerical helpers -/

private lemma sic_bd {c ε B lam L : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hB : 0 ≤ B) (hL : 0 < L) (hlam : 0 < lam)
    (hη : c ^ 2 * ε ^ 9 / 6 ≤ lam / L) : B / lam ≤ 27 * B / (c ^ 7 * ε ^ 28 * L) := by
  have h1 : c ^ 2 * ε ^ 9 / 6 * L ≤ lam := by rwa [le_div_iff₀ hL] at hη
  have hc1' : c ≤ 1 := by linarith
  have h5 : c ^ 5 * ε ^ 19 ≤ 1 := by
    have a := pow_le_one₀ hc0.le hc1' (n := 5)
    have b := pow_le_one₀ hε0.le hε1 (n := 19)
    nlinarith [pow_pos hc0 5, pow_pos hε0 19]
  rw [div_le_div_iff₀ hlam (by positivity)]
  have h6 : c ^ 7 * ε ^ 28 = c ^ 2 * ε ^ 9 * (c ^ 5 * ε ^ 19) := by ring
  have h7 : c ^ 7 * ε ^ 28 ≤ c ^ 2 * ε ^ 9 := by
    rw [h6]
    have := mul_le_mul_of_nonneg_left h5 (show 0 ≤ c ^ 2 * ε ^ 9 by positivity)
    linarith
  calc B * (c ^ 7 * ε ^ 28 * L) ≤ B * (c ^ 2 * ε ^ 9 * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7 hL.le) hB
    _ ≤ 27 * B * lam := by nlinarith [mul_nonneg hB (mul_nonneg (show 0 ≤ c ^ 2 * ε ^ 9 by positivity) hL.le)]

private lemma sic_nu {ε : ℝ} (hε0 : 0 < ε) (f : (ι → α) → ℂ)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100) :
    0 < l2sq f ∧ ε ^ 4 / 4 ≤ (val f f f f).re / l2sq f ^ 2 ∧
      (val f f f f).re / l2sq f ^ 2 ≤ 9801 / 10000 := by
  obtain ⟨hpos, -⟩ := sic_hnv hε0 f hnv
  have hv := val_re_nonneg_pair f f
  have hsq : (((val f f f f).re) ^ (1 / 2 : ℝ)) ^ 2 = (val f f f f).re := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv]; norm_num
  have hr0 : 0 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hv _
  refine ⟨hpos, ?_, ?_⟩
  · have h1 : ε ^ 2 / 2 * l2sq f ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) := by
      rwa [le_div_iff₀ hpos] at hnv
    have h2 : (ε ^ 2 / 2 * l2sq f) ^ 2 ≤ (val f f f f).re := by
      rw [← hsq]; exact pow_le_pow_left₀ (by positivity) h1 2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have h1 : ((val f f f f).re) ^ (1 / 2 : ℝ) ≤ 99 / 100 * l2sq f := by
      rwa [div_le_iff₀ hpos] at hnv'
    have h2 : (val f f f f).re ≤ (99 / 100 * l2sq f) ^ 2 := by
      rw [← hsq]; exact pow_le_pow_left₀ hr0 h1 2
    rw [div_le_iff₀ (by positivity)]
    nlinarith

private lemma sic_valf_norm {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f) :
    (val f f f f).re / l2sq f ^ 2 * (1 - 16 * c * ε ^ 2) ≤
      ∑ i ∈ sicK c ε d t, (d.lam i ^ 2 / l2sq f) ^ 2 *
          (val (d.h i) (d.h i) (d.h i) (d.h i)).re +
        2 * ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re := by
  obtain ⟨hpos, -⟩ := sic_hnv hε0 f hnv
  obtain ⟨h1, h2⟩ := swap_valf hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv
  have hexp := swapValOn_svd_expansion S d.lam d.g d.h d.isJSVD.orth_g (sicK c ε d t)
  have h3 : (val f f f f).re * (1 - 16 * c * ε ^ 2) ≤
      ∑ i ∈ sicK c ε d t, d.lam i ^ 4 * (val (d.h i) (d.h i) (d.h i) (d.h i)).re +
        2 * ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
          d.lam i ^ 2 * d.lam j ^ 2 * (val (d.h i) (d.h j) (d.h i) (d.h j)).re := by
    rw [← hexp]; exact h1.trans h2
  have hn : 0 < l2sq f ^ 2 := by positivity
  have e : ∑ i ∈ sicK c ε d t, (d.lam i ^ 2 / l2sq f) ^ 2 *
          (val (d.h i) (d.h i) (d.h i) (d.h i)).re +
        2 * ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re =
      (∑ i ∈ sicK c ε d t, d.lam i ^ 4 * (val (d.h i) (d.h i) (d.h i) (d.h i)).re +
        2 * ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
          d.lam i ^ 2 * d.lam j ^ 2 * (val (d.h i) (d.h j) (d.h i) (d.h j)).re) / l2sq f ^ 2 := by
    rw [add_div, mul_div_assoc, Finset.sum_div, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
  rw [e, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h3 hn.le

private lemma sic_l2sq_h {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (i : Fin d.r) :
    l2sq (d.h i) = 1 := by
  have := svdInc_ofReal_l2sq (d.h i)
  rw [d.isJSVD.orth_h i i, if_pos rfl] at this
  exact_mod_cast this

private lemma sic_eta_of_a {c ε a lam L : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hL : 0 < L) (hlam : 0 < lam) (ha : a = lam ^ 2 / L ^ 2)
    (hge : ε ^ 6 / (4 * 10 ^ 11) ≤ a) : c ^ 2 * ε ^ 9 / 6 ≤ lam / L := by
  have hc4 : c ^ 4 ≤ 1 / 10 ^ 52 := by
    have := pow_le_pow_left₀ hc0.le hc1 4
    norm_num at this ⊢; linarith
  have h18 : ε ^ 18 ≤ ε ^ 6 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h1 : (c ^ 2 * ε ^ 9 / 6) ^ 2 ≤ (lam / L) ^ 2 := by
    have e : (c ^ 2 * ε ^ 9 / 6) ^ 2 = c ^ 4 * ε ^ 18 / 36 := by ring
    rw [e, div_pow, ← ha]
    have : c ^ 4 * ε ^ 18 ≤ (1 / 10 ^ 52) * ε ^ 6 :=
      mul_le_mul hc4 h18 (by positivity) (by norm_num)
    have h6 : 0 ≤ ε ^ 6 := by positivity
    calc c ^ 4 * ε ^ 18 / 36 ≤ (1 / 10 ^ 52) * ε ^ 6 / 36 := by linarith
      _ ≤ ε ^ 6 / (4 * 10 ^ 11) := by
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
      _ ≤ a := hge
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1

/-- the bookkeeping of the normalised quantities of an SVD -/
private lemma sic_norm_facts {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f)
    (hpos : 0 < l2sq f) :
    (∀ i, 0 ≤ d.lam i ^ 2 / l2sq f) ∧ ∑ i, d.lam i ^ 2 / l2sq f = 1 ∧
      ∀ i j : Fin d.r, i ≤ j → d.lam j ^ 2 / l2sq f ≤ d.lam i ^ 2 / l2sq f := by
  refine ⟨fun i => by positivity, ?_, ?_⟩
  · rw [← Finset.sum_div, svdInc_sum_lam_sq]; exact div_self hpos.ne'
  · intro i j hij
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have h := d.isJSVD.antitone hij
    have := svdInc_lam_pos d j
    nlinarith

private lemma sic_case2b_proof {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100)
    (hr : 0 < d.r) (hcase : d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f) ≤ 1 - ε ^ 2 / 10 ^ 10)
    (hcross :
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i),
        ∑ j ∈ (Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i)).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re ≤
      (1 - (d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) ^ 2) / 4 * ((val f f f f).re / l2sq f ^ 2)) :
    SwapSvdIncOut c ε B R S f := by
  obtain ⟨hpos, hν1, hν2⟩ := sic_nu hε0 f hnv hnv'
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  have hL : 0 < Real.sqrt (l2sq f) := Real.sqrt_pos.2 hpos
  have hL2 : Real.sqrt (l2sq f) ^ 2 = l2sq f := Real.sq_sqrt hpos.le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x₀)
  have hv1 := sic_valf_norm hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv
  obtain ⟨hna0, hnsum, hnanti⟩ := sic_norm_facts d hpos
  set ν := (val f f f f).re / l2sq f ^ 2 with hνdef
  have hνpos : 0 < ν := lt_of_lt_of_le (by positivity) hν1
  set a0 := d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f) with ha0def
  have ha0 : 0 ≤ a0 := div_nonneg (svdInc_lam_pos d _).le hL.le
  have ha0sq : a0 ^ 2 = d.lam ⟨0, hr⟩ ^ 2 / l2sq f := by
    rw [ha0def, div_pow, hL2]
  set δ := 1 - a0 ^ 2 with hδdef
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hx : ε ^ 2 / 10 ^ 10 ≤ δ := by
    have h1 : a0 ≤ 1 - ε ^ 2 / 10 ^ 10 := hcase
    have h2 : 0 ≤ ε ^ 2 / 10 ^ 10 := by positivity
    have h3 : ε ^ 2 / 10 ^ 10 ≤ 1 := by linarith
    nlinarith
  have hδ16 : 16 * c * ε ^ 2 ≤ δ / 12 := by
    have : 16 * c * ε ^ 2 ≤ 16 * (1 / 10 ^ 13) * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ 16 * ε ^ 2 by positivity)
      linarith
    have h4 : 16 * (1 / 10 ^ 13) * ε ^ 2 ≤ ε ^ 2 / 10 ^ 10 / 12 := by
      nlinarith [sq_nonneg ε]
    linarith
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hx
  have hcross' : 2 * ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
      (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
        (val (d.h i) (d.h j) (d.h i) (d.h j)).re ≤ δ / 4 * ν := hcross
  have hE : (1 - δ / 3) * ν ≤ ∑ i ∈ sicK c ε d t, (d.lam i ^ 2 / l2sq f) ^ 2 *
      (val (d.h i) (d.h i) (d.h i) (d.h i)).re := by
    have := mul_le_mul_of_nonneg_left hδ16 hνpos.le
    nlinarith
  obtain ⟨i, hiK, hai, hVi⟩ := svdInc_case2b_abstract (sicK c ε d t) (fun i => d.lam i ^ 2 / l2sq f)
    (fun i => (val (d.h i) (d.h i) (d.h i) (d.h i)).re) (a0 ^ 2) ν δ hna0 hnsum
    (fun i => by rw [ha0sq]; exact hnanti ⟨0, hr⟩ i (Nat.zero_le _))
    rfl (fun i => val_re_nonneg_pair _ _)
    (fun i => by have := svdInc_val_re_le (d.h i); rwa [sic_l2sq_h d i, one_pow] at this)
    hνpos hδpos hE
  have hlam := svdInc_lam_pos d i
  have hηa : ε ^ 6 / (4 * 10 ^ 11) ≤ d.lam i ^ 2 / l2sq f := by
    have h1 : ε ^ 2 / 10 ^ 10 * (ε ^ 4 / 4) ≤ δ * ν :=
      mul_le_mul hx hν1 (by positivity) hδpos.le
    have h2 : δ * ν / 10 ≤ d.lam i ^ 2 / l2sq f := hai.le
    have h3 : ε ^ 2 / 10 ^ 10 * (ε ^ 4 / 4) = ε ^ 6 / (4 * 10 ^ 10) := by ring
    rw [h3] at h1
    have : ε ^ 6 / (4 * 10 ^ 11) = ε ^ 6 / (4 * 10 ^ 10) / 10 := by ring
    rw [this]; linarith
  have hη : c ^ 2 * ε ^ 9 / 6 ≤ d.lam i / Real.sqrt (l2sq f) :=
    sic_eta_of_a hc0 hc1 hε0 hε1 hL hlam (by rw [hL2]) hηa
  refine sic_out_of_single R S hdep hB d hpos i hη (sic_bd hc0 hc1 hε0 hε1 hB0 hL hlam hη)
    (Or.inr ?_)
  have hg : 1 + ε ^ 2 / 10 ^ 11 ≤ 1 + δ / 2 := by linarith
  exact le_trans (mul_le_mul_of_nonneg_right hg hνpos.le) hVi

private lemma sic_case1_prod {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (f : (ι → α) → ℂ)
    (S : Finset ι) (d : SwapSvdData S f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hr : 0 < d.r) (hcase : 1 - ε ^ 2 / 10 ^ 10 ≤ d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) :
    0.999 ^ 4 * ((val f f f f).re / l2sq f ^ 2) ≤
      (val (d.g ⟨0, hr⟩) (d.g ⟨0, hr⟩) (d.g ⟨0, hr⟩) (d.g ⟨0, hr⟩)).re *
        (val (d.h ⟨0, hr⟩) (d.h ⟨0, hr⟩) (d.h ⟨0, hr⟩) (d.h ⟨0, hr⟩)).re := by
  obtain ⟨hpos', hε⟩ := sic_hnv hε0 f hnv
  have hpos := hpos'
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  have hL : 0 < Real.sqrt (l2sq f) := Real.sqrt_pos.2 hpos
  have hL2 : Real.sqrt (l2sq f) ^ 2 = l2sq f := Real.sq_sqrt hpos.le
  set i0 : Fin d.r := ⟨0, hr⟩ with hi0
  set x := ε ^ 2 / 10 ^ 10 with hxdef
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 10 ^ 10 := by
    rw [hxdef]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hlam := svdInc_lam_pos d i0
  have ha0 : 1 - x ≤ d.lam i0 / Real.sqrt (l2sq f) := hcase
  have hlamL : (1 - x) * Real.sqrt (l2sq f) ≤ d.lam i0 := by rwa [le_div_iff₀ hL] at ha0
  -- the remainder `f - λ₀ g₀ h₀`
  set u : (ι → α) → ℂ := fun y => (d.lam i0 : ℂ) * prodSplit S (d.g i0) (d.h i0) y with hu
  set r : (ι → α) → ℂ := fun y => f y - u y with hr_def
  have hrfun : r = d.truncOn (Finset.univ.erase i0) := by
    funext y
    have h1 := Finset.add_sum_erase Finset.univ
      (fun i => (d.lam i : ℂ) * (svdIncG d i y * svdIncH d i y)) (Finset.mem_univ i0)
    simp only [hr_def, hu]
    rw [svdInc_decomp d y, svdInc_truncOn_apply, ← h1, svdInc_GH]
    ring
  have hl2r : l2sq r = l2sq f - d.lam i0 ^ 2 := by
    rw [hrfun, svdInc_l2sq_truncOn d x₀, Finset.sum_erase_eq_sub (Finset.mem_univ i0),
      svdInc_sum_lam_sq]
  have hsr : swapNorm r ^ 2 ≤ 2 * x * l2sq f := by
    have h1 := svdInc_swapNorm_le_sqrt r
    have h2 : swapNorm r ^ 2 ≤ l2sq r := by
      calc swapNorm r ^ 2 ≤ Real.sqrt (l2sq r) ^ 2 := pow_le_pow_left₀ (swapNorm_nonneg _) h1 2
        _ = l2sq r := Real.sq_sqrt (l2sq_nonneg r)
    rw [hl2r] at h2
    have h3 : d.lam i0 ^ 2 ≥ (1 - x) ^ 2 * l2sq f := by
      have := pow_le_pow_left₀ (by nlinarith) hlamL 2
      rw [mul_pow, hL2] at this
      exact this
    nlinarith [mul_pos hx0 hpos]
  have hsf := swapNorm_nonneg f
  have hsfpos : 0 < swapNorm f := by
    have : 0 < ε * Real.sqrt (l2sq f) := by positivity
    linarith
  have hsr2 : swapNorm r ≤ 3 / 10 ^ 5 * swapNorm f := by
    have h1 : swapNorm r ^ 2 ≤ (3 / 10 ^ 5 * swapNorm f) ^ 2 := by
      have h4 : (ε * Real.sqrt (l2sq f)) ^ 2 ≤ (2 * swapNorm f) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hε 2
      rw [mul_pow, hL2] at h4
      have h5 : 2 * x * l2sq f = 2 * (ε ^ 2 * l2sq f) / 10 ^ 10 := by rw [hxdef]; ring
      rw [h5] at hsr
      nlinarith
    exact (pow_le_pow_iff_left₀ (swapNorm_nonneg _) (by positivity) (by norm_num)).1 h1
  have hfu : f = u + r := by funext y; simp [hr_def]
  have hsu : 0.999 * swapNorm f ≤ swapNorm u := by
    have := swapNorm_add_le u r
    rw [← hfu] at this
    linarith
  -- the swap norm of `λ₀ g₀ h₀`
  have hVg := val_re_nonneg_pair (d.g i0) (d.g i0)
  have hVh := val_re_nonneg_pair (d.h i0) (d.h i0)
  have hp4 : swapNorm (prodSplit S (d.g i0) (d.h i0)) ^ 4 =
      (val (d.g i0) (d.g i0) (d.g i0) (d.g i0)).re * (val (d.h i0) (d.h i0) (d.h i0) (d.h i0)).re := by
    rw [swapNorm_pow_four, val_prodSplit_self]
    have e1 : val (d.g i0) (d.g i0) (d.g i0) (d.g i0) =
        (((val (d.g i0) (d.g i0) (d.g i0) (d.g i0)).re : ℝ) : ℂ) := by
      rw [val_eq_ofReal_pair, Complex.ofReal_re]
    have e2 : val (d.h i0) (d.h i0) (d.h i0) (d.h i0) =
        (((val (d.h i0) (d.h i0) (d.h i0) (d.h i0)).re : ℝ) : ℂ) := by
      rw [val_eq_ofReal_pair, Complex.ofReal_re]
    conv_lhs => rw [e1, e2, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsu4 : swapNorm u ^ 4 = d.lam i0 ^ 4 *
      ((val (d.g i0) (d.g i0) (d.g i0) (d.g i0)).re *
        (val (d.h i0) (d.h i0) (d.h i0) (d.h i0)).re) := by
    have : u = (d.lam i0 : ℂ) • prodSplit S (d.g i0) (d.h i0) := rfl
    rw [this, swapNorm_smul, mul_pow, hp4, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  have hineq : 0.999 ^ 4 * (val f f f f).re ≤ d.lam i0 ^ 4 *
      ((val (d.g i0) (d.g i0) (d.g i0) (d.g i0)).re *
        (val (d.h i0) (d.h i0) (d.h i0) (d.h i0)).re) := by
    rw [← hsu4, ← swapNorm_pow_four f, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsu 4
  have hlam4 : d.lam i0 ^ 4 ≤ l2sq f ^ 2 := by
    have := svdInc_lam_sq_le d i0
    calc d.lam i0 ^ 4 = (d.lam i0 ^ 2) ^ 2 := by ring
      _ ≤ l2sq f ^ 2 := pow_le_pow_left₀ (sq_nonneg _) this 2
  set ν := (val f f f f).re / l2sq f ^ 2 with hνdef
  set Vg := (val (d.g i0) (d.g i0) (d.g i0) (d.g i0)).re
  set Vh := (val (d.h i0) (d.h i0) (d.h i0) (d.h i0)).re
  show 0.999 ^ 4 * ν ≤ Vg * Vh
  have hprod : 0.999 ^ 4 * ν ≤ Vg * Vh := by
    have hn : 0 < l2sq f ^ 2 := by positivity
    have h1 : 0.999 ^ 4 * (val f f f f).re ≤ l2sq f ^ 2 * (Vg * Vh) :=
      hineq.trans (mul_le_mul_of_nonneg_right hlam4 (mul_nonneg hVg hVh))
    rw [hνdef, mul_div_assoc', div_le_iff₀ hn]
    linarith
  exact hprod

private lemma sic_case1_proof {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100)
    (hr : 0 < d.r) (hcase : 1 - ε ^ 2 / 10 ^ 10 ≤ d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) :
    SwapSvdIncOut c ε B R S f := by
  obtain ⟨hpos, hν1, hν2⟩ := sic_nu hε0 f hnv hnv'
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  have hL : 0 < Real.sqrt (l2sq f) := Real.sqrt_pos.2 hpos
  have hL2 : Real.sqrt (l2sq f) ^ 2 = l2sq f := Real.sq_sqrt hpos.le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x₀)
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hprod := sic_case1_prod hε0 hε1 f S d hnv hr hcase
  set i0 : Fin d.r := ⟨0, hr⟩ with hi0
  have hlam := svdInc_lam_pos d i0
  have hVg := val_re_nonneg_pair (d.g i0) (d.g i0)
  have hVh := val_re_nonneg_pair (d.h i0) (d.h i0)
  set ν := (val f f f f).re / l2sq f ^ 2 with hνdef
  set Vg := (val (d.g i0) (d.g i0) (d.g i0) (d.g i0)).re
  set Vh := (val (d.h i0) (d.h i0) (d.h i0) (d.h i0)).re
  have hνpos : 0 < ν := lt_of_lt_of_le (by positivity) hν1
  have hη : c ^ 2 * ε ^ 9 / 6 ≤ d.lam i0 / Real.sqrt (l2sq f) := by
    have hc1' : c ≤ 1 := by linarith
    have h1 : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1' (n := 2)
    have h2 : ε ^ 9 ≤ 1 := pow_le_one₀ hε0.le hε1 (n := 9)
    have h3 : c ^ 2 * ε ^ 9 ≤ 1 := by nlinarith [pow_pos hc0 2, pow_pos hε0 9]
    have h4 : 1 / 2 ≤ d.lam i0 / Real.sqrt (l2sq f) := by
      have : ε ^ 2 / 10 ^ 10 ≤ 1 / 10 ^ 10 := div_le_div_of_nonneg_right hε2 (by positivity)
      norm_num at this ⊢
      linarith
    linarith
  have hbd := sic_bd hc0 hc1 hε0 hε1 hB0 hL hlam hη
  have hsq : (1.001 * ν) ^ 2 ≤ Vg * Vh := by
    have h1 : ν * ν ≤ (9801 / 10000) * ν := mul_le_mul_of_nonneg_right hν2 hνpos.le
    have : (1.001 * ν) ^ 2 ≤ 0.999 ^ 4 * ν := by
      calc (1.001 * ν) ^ 2 = 1.002001 * (ν * ν) := by ring
        _ ≤ 1.002001 * ((9801 / 10000) * ν) := by gcongr
        _ = (1.002001 * (9801 / 10000)) * ν := by ring
        _ ≤ 0.999 ^ 4 * ν := mul_le_mul_of_nonneg_right (by norm_num) hνpos.le
    linarith
  have hg : 1 + ε ^ 2 / 10 ^ 11 ≤ 1.001 := by
    have : ε ^ 2 / 10 ^ 11 ≤ 1 / 10 ^ 11 := div_le_div_of_nonneg_right hε2 (by positivity)
    norm_num at this ⊢
    linarith
  refine sic_out_of_single R S hdep hB d hpos i0 hη hbd ?_
  rcases le_total Vh Vg with h | h
  · left
    have h2 : (1.001 * ν) ^ 2 ≤ Vg ^ 2 := by
      have := mul_le_mul_of_nonneg_left h hVg
      nlinarith
    have h3 := (pow_le_pow_iff_left₀ (by positivity) hVg (by norm_num)).1 h2
    exact le_trans (mul_le_mul_of_nonneg_right hg hνpos.le) h3
  · right
    have h2 : (1.001 * ν) ^ 2 ≤ Vh ^ 2 := by
      have := mul_le_mul_of_nonneg_left h hVh
      nlinarith
    have h3 := (pow_le_pow_iff_left₀ (by positivity) hVh (by norm_num)).1 h2
    exact le_trans (mul_le_mul_of_nonneg_right hg hνpos.le) h3

/-! ### Case 2a: the combined singular functions -/

private lemma sic_l2sq_comb {κ ι' : Type} [DecidableEq κ] [Fintype ι'] [DecidableEq ι'] (K : Finset κ) (a : κ → ℂ)
    (u : κ → (ι' → α) → ℂ) (horth : ∀ i j, uinner (u i) (u j) = if i = j then 1 else 0) :
    l2sq (fun x => ∑ i ∈ K, a i * u i x) = ∑ i ∈ K, ‖a i‖ ^ 2 := by
  have h := svdInc_ofReal_l2sq (fun x => ∑ i ∈ K, a i * u i x)
  rw [svdInc_uinner_lin K K a a u u] at h
  simp only [horth, mul_ite, mul_one, mul_zero] at h
  have h2 : ((∑ i ∈ K, ‖a i‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ K, ∑ j ∈ K,
      if i = j then a i * star (a j) else 0 := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    · intro j _ hj; rw [if_neg (Ne.symm hj)]
    · intro h; exact absurd hi h
  exact Complex.ofReal_injective (h.trans h2.symm)

private lemma sic_uinner_sum_left {κ ι' : Type} [Fintype ι'] [DecidableEq ι'] (K : Finset κ)
    (a : κ → ℂ) (u : κ → (ι' → α) → ℂ) (P : (ι' → α) → ℂ) :
    uinner (fun x => ∑ i ∈ K, a i * u i x) P = ∑ i ∈ K, a i * uinner (u i) P := by
  unfold uinner
  simp only [Finset.sum_mul, Finset.expect_sum_comm, Finset.mul_expect, mul_assoc]

private lemma sic_l2sq_smul {ι' : Type} [Fintype ι'] [DecidableEq ι'] (r : ℝ) (u : (ι' → α) → ℂ) :
    l2sq (fun x => (r : ℂ) * u x) = r ^ 2 * l2sq u := by
  unfold l2sq
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

private lemma sic_l2sq_prodSplit_one {S : Finset ι} (x₀ : ι → α) (w : (↥Sᶜ → α) → ℂ) :
    l2sq (prodSplit S (fun _ => 1) w) = l2sq w := by
  have h := svdInc_ofReal_l2sq (prodSplit S (fun _ => 1) w)
  rw [svdInc_uinner_prodSplit, svdInc_uinner_one' x₀, one_mul, ← svdInc_ofReal_l2sq] at h
  exact_mod_cast h

private lemma sic_val_prodSplit_one {S : Finset ι} (x₀ : ι → α) (w : (↥Sᶜ → α) → ℂ) :
    val (prodSplit S (fun _ => 1) w) (prodSplit S (fun _ => 1) w) (prodSplit S (fun _ => 1) w)
        (prodSplit S (fun _ => 1) w) = val w w w w := by
  haveI : Nonempty (↥S → α) := ⟨fun k => x₀ k⟩
  rw [val_prodSplit_self, sic_val_one, one_mul]

/-- `∑_{i ∈ K} βᵢ λᵢ hᵢ` (on `Σ^{Sᶜ}`) -/
private def sicHb {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (K : Finset (Fin d.r))
    (β : Fin d.r → ℂ) : (↥Sᶜ → α) → ℂ :=
  fun y => ∑ i ∈ K, (β i * (d.lam i : ℂ)) * d.h i y

/-- the normalised right function `Λ⁻¹ ∑_{i ∈ K} βᵢ λᵢ hᵢ`, on `ι → α` -/
private def sicHt {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (K : Finset (Fin d.r))
    (β : Fin d.r → ℂ) (Λ : ℝ) : (ι → α) → ℂ :=
  prodSplit S (fun _ => 1) (fun y => ((1 / Λ : ℝ) : ℂ) * sicHb d K β y)

/-- the left function `∑_{i ∈ K} conj(αᵢ) gᵢ` with `αᵢ = βᵢ / √t'`, on `ι → α` -/
private def sicGc {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (K : Finset (Fin d.r))
    (β : Fin d.r → ℂ) : (ι → α) → ℂ :=
  fun x => ∑ i ∈ K, (((1 / Real.sqrt (K.card : ℝ) : ℝ) : ℂ) * star (β i)) * svdIncG d i x

private lemma sicGc_l2sq {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (hβ : ∀ i, ‖β i‖ = 1) (hK : 0 < K.card) :
    l2sq (sicGc d K β) = 1 := by
  unfold sicGc
  rw [sic_l2sq_comb K _ (svdIncG d) (svdInc_orth_G d x₀)]
  have hc : (0 : ℝ) < K.card := by exact_mod_cast hK
  have : ∀ i ∈ K, ‖((1 / Real.sqrt (K.card : ℝ) : ℝ) : ℂ) * star (β i)‖ ^ 2 = 1 / (K.card : ℝ) := by
    intro i _
    rw [norm_mul, norm_star, hβ, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Real.sq_sqrt hc.le]
    simp
  rw [Finset.sum_congr rfl this]
  simp
  field_simp

private lemma sicGc_dep {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) : SwapDependsOn S (sicGc d K β) := by
  intro x y h
  unfold sicGc
  exact Finset.sum_congr rfl fun i _ => by rw [svdInc_G_dep d i x y h]

private lemma sicGc_bound {S : Finset ι} {f : (ι → α) → ℂ} {B m : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (d : SwapSvdData S f) (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (hβ : ∀ i, ‖β i‖ = 1)
    (hB0 : 0 ≤ B) (hm : 0 < m) (hlow : ∀ i ∈ K, m ≤ d.lam i) (x : ι → α) :
    ‖sicGc d K β x‖ ≤ Real.sqrt (K.card : ℝ) * (B / m) := by
  unfold sicGc
  rcases Nat.eq_zero_or_pos K.card with h0 | hK
  · have : K = ∅ := Finset.card_eq_zero.1 h0
    subst this; simp
  have hc : (0 : ℝ) < K.card := by exact_mod_cast hK
  have hs : 0 < Real.sqrt (K.card : ℝ) := Real.sqrt_pos.2 hc
  calc ‖∑ i ∈ K, ((1 / Real.sqrt (K.card : ℝ) : ℝ) : ℂ) * star (β i) * svdIncG d i x‖
      ≤ ∑ i ∈ K, ‖((1 / Real.sqrt (K.card : ℝ) : ℝ) : ℂ) * star (β i) * svdIncG d i x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ K, (1 / Real.sqrt (K.card : ℝ)) * (B / m) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_mul, norm_star, hβ, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine ((svdInc_bounds hB d i).1 x).trans ?_
        exact div_le_div_of_nonneg_left hB0 hm (hlow i hi)
    _ = Real.sqrt (K.card : ℝ) * (B / m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have h := Real.mul_self_sqrt hc.le
        calc (K.card : ℝ) * (1 / Real.sqrt (K.card : ℝ) * (B / m)) =
            (Real.sqrt (K.card : ℝ) * Real.sqrt (K.card : ℝ)) *
              (1 / Real.sqrt (K.card : ℝ) * (B / m)) := by rw [h]
          _ = Real.sqrt (K.card : ℝ) * (B / m) := by field_simp

private lemma sicHb_l2sq {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (hβ : ∀ i, ‖β i‖ = 1) :
    l2sq (sicHb d K β) = ∑ i ∈ K, d.lam i ^ 2 := by
  unfold sicHb
  rw [sic_l2sq_comb K _ d.h d.isJSVD.orth_h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, hβ, one_mul, Complex.norm_real, Real.norm_of_nonneg (svdInc_lam_pos d i).le]

private lemma sicHt_apply {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (Λ : ℝ) (x : ι → α) :
    sicHt d K β Λ x = ∑ i ∈ K, (((1 / Λ : ℝ) : ℂ) * (β i * (d.lam i : ℂ))) * svdIncH d i x := by
  simp only [sicHt, sicHb, prodSplit, one_mul, Finset.mul_sum, svdIncH_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma sicHt_l2sq {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (hβ : ∀ i, ‖β i‖ = 1)
    (hΛ : 0 < ∑ i ∈ K, d.lam i ^ 2) :
    l2sq (sicHt d K β (Real.sqrt (∑ i ∈ K, d.lam i ^ 2))) = 1 := by
  unfold sicHt
  rw [sic_l2sq_prodSplit_one x₀, sic_l2sq_smul, sicHb_l2sq d K β hβ, one_div, inv_pow,
    Real.sq_sqrt hΛ.le]
  exact inv_mul_cancel₀ hΛ.ne'

private lemma sicHt_bound {S : Finset ι} {f : (ι → α) → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (d : SwapSvdData S f) (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (hβ : ∀ i, ‖β i‖ = 1)
    (Λ : ℝ) (hΛ : 0 < Λ) (x : ι → α) : ‖sicHt d K β Λ x‖ ≤ K.card * B / Λ := by
  rw [sicHt_apply]
  have h1 : ∀ i ∈ K, ‖(((1 / Λ : ℝ) : ℂ) * (β i * (d.lam i : ℂ))) * svdIncH d i x‖ ≤ B / Λ := by
    intro i hi
    have hl := svdInc_lam_pos d i
    rw [norm_mul, norm_mul, norm_mul, hβ, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hl.le, Real.norm_eq_abs, abs_of_pos (by positivity), one_mul]
    have := (svdInc_bounds hB d i).2 x
    calc 1 / Λ * d.lam i * ‖svdIncH d i x‖ ≤ 1 / Λ * d.lam i * (B / d.lam i) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = B / Λ := by field_simp
  calc _ ≤ ∑ i ∈ K, ‖(((1 / Λ : ℝ) : ℂ) * (β i * (d.lam i : ℂ))) * svdIncH d i x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ K, B / Λ := Finset.sum_le_sum h1
    _ = K.card * B / Λ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private lemma sicHt_dep {S R : Finset ι} {f : (ι → α) → ℂ} (hdep : SwapDependsOn R f)
    (d : SwapSvdData S f) (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (Λ : ℝ) :
    SwapDependsOn (R \ S) (sicHt d K β Λ) := by
  intro x y h
  rw [sicHt_apply, sicHt_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [svdInc_H_dep hdep d i x y h]

private lemma sicHt_val {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (Λ : ℝ) (hΛ : 0 < Λ) :
    (val (sicHt d K β Λ) (sicHt d K β Λ) (sicHt d K β Λ) (sicHt d K β Λ)).re =
      (val (sicHb d K β) (sicHb d K β) (sicHb d K β) (sicHb d K β)).re / Λ ^ 4 := by
  unfold sicHt
  rw [sic_val_prodSplit_one x₀]
  have e : (fun y => ((1 / Λ : ℝ) : ℂ) * sicHb d K β y) = ((1 / Λ : ℝ) : ℂ) • sicHb d K β := rfl
  rw [e, val_smul_four, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  field_simp

/-- the item-2 identity of Case 2a -/
private lemma sic_id_2a {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f) (x₀ : ι → α)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (Λ L t' : ℝ) (hΛ : 0 < Λ) (hL : 0 < L)
    (ht' : 0 < t') (I : Finset ι) (hI : I ⊆ Sᶜ) (z : ι → α) (P : (ι → α) → ℂ)
    (hP : ∀ x y : ι → α, (∀ k ∈ Sᶜ, x k = y k) → P x = P y) (hcard : t' = (K.card : ℝ)) :
    uinner (fun x => f (swapFixAt I z x)) (fun x => sicGc d K β x * P x) =
      ((Λ / (Real.sqrt t' * L) : ℝ) : ℂ) * (L : ℂ) *
        uinner (fun x => sicHt d K β Λ (swapFixAt I z x)) P := by
  have h1 := sic_id2 d x₀ K (fun i => ((1 / Real.sqrt (K.card : ℝ) : ℝ) : ℂ) * star (β i)) I hI z P hP
  have h2 : (fun x => sicGc d K β x * P x) =
      fun x => (∑ i ∈ K, (((1 / Real.sqrt (K.card : ℝ) : ℝ) : ℂ) * star (β i)) *
        svdIncG d i x) * P x := rfl
  rw [h2, h1]
  have h3 : (fun x => sicHt d K β Λ (swapFixAt I z x)) = fun x => ∑ i ∈ K,
      (((1 / Λ : ℝ) : ℂ) * (β i * (d.lam i : ℂ))) * svdIncH d i (swapFixAt I z x) := by
    funext x; exact sicHt_apply d K β Λ _
  rw [h3, sic_uinner_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : Real.sqrt t' ≠ 0 := (Real.sqrt_pos.2 ht').ne'
  rw [← hcard]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, star_star, Complex.conj_conj]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hΛ' : (Λ : ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  have hs' : (Real.sqrt t' : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp

private lemma sic_2a_num {c ε B L Λ2 t' : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hB0 : 0 ≤ B) (hL : 0 < L) (ht' : 0 < t') (hcard : t' * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΛ2 : ε ^ 2 / 3 * L ^ 2 ≤ Λ2) :
    Real.sqrt t' * (B / (c ^ 5 * ε ^ 20 / 9 * L)) ≤ 27 * B / (c ^ 7 * ε ^ 28 * L) ∧
      t' * B / Real.sqrt Λ2 ≤ 27 * B / (c ^ 7 * ε ^ 28 * L) ∧
      c ^ 2 * ε ^ 9 / 6 ≤ Real.sqrt Λ2 / (Real.sqrt t' * L) := by
  have hc1' : c ≤ 1 := by linarith
  have hcε : 0 < c ^ 2 * ε ^ 8 := by positivity
  have hs : 0 < Real.sqrt t' := Real.sqrt_pos.2 ht'
  have hst : Real.sqrt t' * (c ^ 2 * ε ^ 8) ≤ 3 := by
    have h2 : (Real.sqrt t' * (c ^ 2 * ε ^ 8)) ^ 2 ≤ 3 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht'.le]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).1 h2
  have hΛpos : 0 < Λ2 := lt_of_lt_of_le (by positivity) hΛ2
  have hΛs : 0 < Real.sqrt Λ2 := Real.sqrt_pos.2 hΛpos
  have hΛge : ε * L / 2 ≤ Real.sqrt Λ2 := by
    have h2 : (ε * L / 2) ^ 2 ≤ Λ2 := by nlinarith [sq_nonneg (ε * L), sq_nonneg L, sq_nonneg ε]
    exact Real.le_sqrt_of_sq_le h2
  refine ⟨?_, ?_, ?_⟩
  · have e : 27 * B / (c ^ 7 * ε ^ 28 * L) =
        (3 / (c ^ 2 * ε ^ 8)) * (B / (c ^ 5 * ε ^ 20 / 9 * L)) := by
      field_simp; ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [le_div_iff₀ hcε]; exact hst
  · have h1 : t' ≤ 9 / (c ^ 4 * ε ^ 16) := by rw [le_div_iff₀ (by positivity)]; exact hcard
    have h2 : 1 / Real.sqrt Λ2 ≤ 2 / (ε * L) := by
      rw [div_le_div_iff₀ hΛs (by positivity)]; nlinarith
    calc t' * B / Real.sqrt Λ2 = (t' * B) * (1 / Real.sqrt Λ2) := by ring
      _ ≤ (9 / (c ^ 4 * ε ^ 16) * B) * (2 / (ε * L)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hB0) h2 (by positivity) (by positivity)
      _ = 18 * B / (c ^ 4 * ε ^ 17 * L) := by field_simp; ring
      _ ≤ 27 * B / (c ^ 7 * ε ^ 28 * L) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h3 : c ^ 3 * ε ^ 11 ≤ 1 := by
            have a := pow_le_one₀ hc0.le hc1' (n := 3)
            have b := pow_le_one₀ hε0.le hε1 (n := 11)
            nlinarith [pow_pos hc0 3, pow_pos hε0 11]
          have h4 : 18 * B * (c ^ 7 * ε ^ 28 * L) = (18 * B * (c ^ 4 * ε ^ 17 * L)) * (c ^ 3 * ε ^ 11) := by
            ring
          rw [h4]
          have h5 : 0 ≤ 18 * B * (c ^ 4 * ε ^ 17 * L) := by positivity
          nlinarith
  · have e : (Real.sqrt Λ2 / (Real.sqrt t' * L)) ^ 2 = Λ2 / (t' * L ^ 2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hΛpos.le, Real.sq_sqrt ht'.le]
    have hsq : (c ^ 2 * ε ^ 9 / 6) ^ 2 ≤ (Real.sqrt Λ2 / (Real.sqrt t' * L)) ^ 2 := by
      rw [e, le_div_iff₀ (by positivity)]
      have h1 : (c ^ 2 * ε ^ 9 / 6) ^ 2 * (t' * L ^ 2) =
          (t' * (c ^ 4 * ε ^ 16)) * (ε ^ 2 * L ^ 2) / 36 := by ring
      have h2 := mul_le_mul_of_nonneg_right hcard (show 0 ≤ ε ^ 2 * L ^ 2 by positivity)
      have h3 : 0 ≤ ε ^ 2 * L ^ 2 := by positivity
      rw [h1]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hsq

private lemma sic_out_2a {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) {f : (ι → α) → ℂ} (R S : Finset ι) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (hpos : 0 < l2sq f)
    (K : Finset (Fin d.r)) (β : Fin d.r → ℂ) (hβ : ∀ i, ‖β i‖ = 1)
    (hΛ : ε ^ 2 / 3 * l2sq f ≤ ∑ i ∈ K, d.lam i ^ 2)
    (hcard : (K.card : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hlow : ∀ i ∈ K, c ^ 5 * ε ^ 20 / 9 * Real.sqrt (l2sq f) ≤ d.lam i)
    (hgain : (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) * l2sq f ^ 2 ≤
      (val (sicHb d K β) (sicHb d K β) (sicHb d K β) (sicHb d K β)).re) :
    SwapSvdIncOut c ε B R S f := by
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  have hL : 0 < Real.sqrt (l2sq f) := Real.sqrt_pos.2 hpos
  have hL2 : Real.sqrt (l2sq f) ^ 2 = l2sq f := Real.sq_sqrt hpos.le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x₀)
  have hΛ2pos : 0 < ∑ i ∈ K, d.lam i ^ 2 := lt_of_lt_of_le (by positivity) hΛ
  have hK : 0 < K.card := by
    rcases Nat.eq_zero_or_pos K.card with h0 | h0
    · have : K = ∅ := Finset.card_eq_zero.1 h0
      rw [this] at hΛ2pos; simp at hΛ2pos
    · exact h0
  have hct : (0 : ℝ) < K.card := by exact_mod_cast hK
  have hΛs : 0 < Real.sqrt (∑ i ∈ K, d.lam i ^ 2) := Real.sqrt_pos.2 hΛ2pos
  have hm : 0 < c ^ 5 * ε ^ 20 / 9 * Real.sqrt (l2sq f) := by positivity
  obtain ⟨n1, n2, n3⟩ := sic_2a_num hc0 hc1 hε0 hε1 hB0 hL hct hcard (Λ2 := ∑ i ∈ K, d.lam i ^ 2)
    (by rw [hL2]; exact hΛ)
  have hΛle : ∑ i ∈ K, d.lam i ^ 2 ≤ l2sq f := by
    rw [← svdInc_sum_lam_sq d]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  refine ⟨sicGc d K β, sicHt d K β (Real.sqrt (∑ i ∈ K, d.lam i ^ 2)),
    ((Real.sqrt (∑ i ∈ K, d.lam i ^ 2) / (Real.sqrt (K.card : ℝ) * Real.sqrt (l2sq f)) : ℝ) : ℂ),
    sicGc_l2sq d x₀ K β hβ hK, sicHt_l2sq d x₀ K β hβ hΛ2pos,
    fun x => (sicGc_bound hB d K β hβ hB0 hm hlow x).trans n1,
    fun x => (sicHt_bound hB d K β hβ _ hΛs x).trans n2, ?_, Or.inr ⟨sicGc_dep d K β,
      sicHt_dep hdep d K β _, ?_, ?_⟩⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; exact n3
  · have h4 : Real.sqrt (∑ i ∈ K, d.lam i ^ 2) ^ 4 = (∑ i ∈ K, d.lam i ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hΛ2pos.le]
    rw [sicHt_val d x₀ K β _ hΛs, h4]
    have hv := val_re_nonneg_pair (sicHb d K β) (sicHb d K β)
    have hn : 0 < l2sq f ^ 2 := by positivity
    calc (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) =
        (1 + ε ^ 2 / 10 ^ 11) * ((val f f f f).re / l2sq f ^ 2) * l2sq f ^ 2 / l2sq f ^ 2 := by
          field_simp
      _ ≤ (val (sicHb d K β) (sicHb d K β) (sicHb d K β) (sicHb d K β)).re / l2sq f ^ 2 :=
          div_le_div_of_nonneg_right hgain hn.le
      _ ≤ _ := div_le_div_of_nonneg_left hv (by positivity)
          (pow_le_pow_left₀ hΛ2pos.le hΛle 2)
  · intro I hI z P hP
    have hIc : I ⊆ Sᶜ := fun k hk => Finset.mem_compl.2 (Finset.mem_sdiff.1 (hI hk)).2
    exact sic_id_2a d x₀ K β _ _ _ hΛs hL hct I hIc z P
      (fun x y h => hP x y (fun k hk => h k (Finset.mem_compl.2 (Finset.mem_sdiff.1
        (Finset.mem_sdiff.1 hk).1).2))) rfl

private lemma sic_KLam {c ε : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S : Finset ι) (d : SwapSvdData S f) (t : ℕ)
    (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f) :
    ε ^ 2 / 3 * l2sq f ≤ ∑ i ∈ sicK c ε d t, d.lam i ^ 2 := by
  obtain ⟨hpos, -⟩ := sic_hnv hε0 f hnv
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  obtain ⟨-, h2, -⟩ := sic_lowerF_core hc0 hc1 hε0 hε1 f S d t ht hΔ hnv
  have h1 : ε ^ 2 / 2 * l2sq f ≤ swapNorm f ^ 2 := by
    rw [sic_swapNorm_sq]
    rwa [le_div_iff₀ hpos] at hnv
  have hsF := svdInc_swapNorm_le_sqrt (d.truncOn (sicK c ε d t))
  have hl2 := svdInc_l2sq_truncOn d x₀ (sicK c ε d t)
  have hs := swapNorm_nonneg f
  have hx : 4 * c * ε ^ 2 ≤ 1 / 1000 := by
    have : c * ε ^ 2 ≤ 1 / 10 ^ 13 * 1 :=
      mul_le_mul hc1 (pow_le_one₀ hε0.le hε1) (by positivity) (by norm_num)
    norm_num at this ⊢; linarith
  have h3 : (999 / 1000) * swapNorm f ≤ swapNorm (d.truncOn (sicK c ε d t)) := by
    refine le_trans ?_ h2
    nlinarith
  have h4 : ((999 / 1000) * swapNorm f) ^ 2 ≤ swapNorm (d.truncOn (sicK c ε d t)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hs) h3 2
  have h5 : swapNorm (d.truncOn (sicK c ε d t)) ^ 2 ≤ l2sq (d.truncOn (sicK c ε d t)) := by
    calc _ ≤ Real.sqrt (l2sq (d.truncOn (sicK c ε d t))) ^ 2 :=
          pow_le_pow_left₀ (swapNorm_nonneg _) hsF 2
      _ = _ := Real.sq_sqrt (l2sq_nonneg _)
  rw [hl2] at h5
  nlinarith [sq_nonneg (swapNorm f), mul_pos (sq_pos_of_pos hε0) hpos]

private lemma sic_EQ_eq {S : Finset ι} {f : (ι → α) → ℂ} (d : SwapSvdData S f)
    (K : Finset (Fin d.r)) (hpos : 0 < l2sq f) :
    ∑ i ∈ K, (d.lam i ^ 2 / l2sq f) ^ 2 * (val (d.h i) (d.h i) (d.h i) (d.h i)).re =
        (∑ i ∈ K, d.lam i ^ 4 * (val (d.h i) (d.h i) (d.h i) (d.h i)).re) / l2sq f ^ 2 ∧
      2 * ∑ i ∈ K, ∑ j ∈ K.filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re =
        2 * (∑ i ∈ K, ∑ j ∈ K.filter (fun j => i < j),
          d.lam i ^ 2 * d.lam j ^ 2 * (val (d.h i) (d.h j) (d.h i) (d.h j)).re) / l2sq f ^ 2 := by
  constructor
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · rw [mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

private lemma sic_2a_gain {c ε ν δ n2 E Q U1 U2 V : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13)
    (hν : 0 < ν) (hn2 : 0 < n2) (hx : ε ^ 2 / 10 ^ 10 ≤ δ)
    (hv1 : ν * (1 - 16 * c * ε ^ 2) ≤ E + Q) (hq : δ / 4 * ν ≤ Q) (hU1 : U1 = n2 ^ 2 * E)
    (hU2 : 4 * U2 = n2 ^ 2 * (2 * Q)) (hV : U1 + 4 * U2 ≤ V) :
    (1 + ε ^ 2 / 10 ^ 11) * ν * n2 ^ 2 ≤ V := by
  have hcε : c * ε ^ 2 ≤ 1 / 10 ^ 13 * ε ^ 2 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg ε)
  have hg : 1 + ε ^ 2 / 10 ^ 11 ≤ 1 - 16 * c * ε ^ 2 + δ / 4 := by
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    norm_num at hcε hx ⊢
    nlinarith
  have h1 : ν * (1 - 16 * c * ε ^ 2 + δ / 4) ≤ E + 2 * Q := by nlinarith
  have h2 : U1 + 4 * U2 = n2 ^ 2 * (E + 2 * Q) := by rw [hU1, hU2]; ring
  have h3 : (1 + ε ^ 2 / 10 ^ 11) * ν ≤ E + 2 * Q :=
    le_trans (by nlinarith [mul_le_mul_of_nonneg_left hg hν.le]) h1
  calc (1 + ε ^ 2 / 10 ^ 11) * ν * n2 ^ 2 = n2 ^ 2 * ((1 + ε ^ 2 / 10 ^ 11) * ν) := by ring
    _ ≤ n2 ^ 2 * (E + 2 * Q) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = U1 + 4 * U2 := h2.symm
    _ ≤ V := hV

private lemma sic_case2a_proof {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100)
    (hr : 0 < d.r) (hcase : d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f) ≤ 1 - ε ^ 2 / 10 ^ 10)
    (hcross : (1 - (d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) ^ 2) / 4 *
        ((val f f f f).re / l2sq f ^ 2) ≤
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i),
        ∑ j ∈ (Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i)).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re) :
    SwapSvdIncOut c ε B R S f := by
  obtain ⟨hpos, hν1, hν2⟩ := sic_nu hε0 f hnv hnv'
  obtain ⟨x₀⟩ := svdInc_nonempty_of_l2sq_pos hpos
  have hL : 0 < Real.sqrt (l2sq f) := Real.sqrt_pos.2 hpos
  have hL2 : Real.sqrt (l2sq f) ^ 2 = l2sq f := Real.sq_sqrt hpos.le
  have hv1 := sic_valf_norm hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv
  obtain ⟨-, -, hlow⟩ := sic_lowerF_core hc0 hc1 hε0 hε1 f S d t ht hΔ hnv
  have hKL := sic_KLam hc0 hc1 hε0 hε1 f S d t ht hΔ hnv
  set ν := (val f f f f).re / l2sq f ^ 2 with hνdef
  have hνpos : 0 < ν := lt_of_lt_of_le (by positivity) hν1
  set a0 := d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f) with ha0def
  have ha0 : 0 ≤ a0 := div_nonneg (svdInc_lam_pos d _).le hL.le
  set δ := 1 - a0 ^ 2 with hδdef
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hx : ε ^ 2 / 10 ^ 10 ≤ δ := by
    have h1 : a0 ≤ 1 - ε ^ 2 / 10 ^ 10 := hcase
    have h2 : 0 ≤ ε ^ 2 / 10 ^ 10 := by positivity
    have h3 : ε ^ 2 / 10 ^ 10 ≤ 1 := by linarith
    nlinarith
  have hc16 : 16 * c * ε ^ 2 ≤ 16 * (1 / 10 ^ 13) * ε ^ 2 := by
    have := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ 16 * ε ^ 2 by positivity)
    linarith
  have hcard : (((sicK c ε d t).card : ℕ) : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9 := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) ht
    exact_mod_cast (Finset.card_le_card (fun i hi => by
      have := (Finset.mem_filter.1 hi).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this.1⟩)).trans (sic_card_lt d.r t)
  obtain ⟨β, hβ, hph⟩ := svdInc_exists_phases (sicK c ε d t) d.lam d.h
  obtain ⟨e1, e2⟩ := sic_EQ_eq d (sicK c ε d t) hpos
  have hn : 0 < l2sq f ^ 2 := by positivity
  refine sic_out_2a hc0 hc1 hε0 hε1 R S hdep hB d hpos (sicK c ε d t) β hβ hKL hcard hlow ?_
  exact sic_2a_gain (c := c) (ε := ε) (ν := ν) (δ := δ) (n2 := l2sq f) hc0 hc1 hνpos hpos hx
    (E := ∑ i ∈ sicK c ε d t, (d.lam i ^ 2 / l2sq f) ^ 2 * (val (d.h i) (d.h i) (d.h i) (d.h i)).re)
    (Q := 2 * ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re)
    (U1 := ∑ i ∈ sicK c ε d t, d.lam i ^ 4 * (val (d.h i) (d.h i) (d.h i) (d.h i)).re)
    (U2 := ∑ i ∈ sicK c ε d t, ∑ j ∈ (sicK c ε d t).filter (fun j => i < j),
      d.lam i ^ 2 * d.lam j ^ 2 * (val (d.h i) (d.h j) (d.h i) (d.h j)).re)
    hv1 hcross (by rw [e1]; field_simp)
    (by rw [e2]; field_simp; ring) hph

/-- CSP_6 `lemma:svdinc#case1`: `λ₁ ≥ 1 - ε²/10^{10}`. -/
theorem swap_svdinc_case1 {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100)
    (hr : 0 < d.r) (hcase : 1 - ε ^ 2 / 10 ^ 10 ≤ d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) :
    SwapSvdIncOut c ε B R S f := by
  exact sic_case1_proof hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv hnv' hr hcase

/-- CSP_6 `lemma:svdinc#case2a`: `λ₁ ≤ 1 - ε²/10^{10}` and the cross term is large. -/
theorem swap_svdinc_case2a {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100)
    (hr : 0 < d.r) (hcase : d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f) ≤ 1 - ε ^ 2 / 10 ^ 10)
    (hcross : (1 - (d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) ^ 2) / 4 *
        ((val f f f f).re / l2sq f ^ 2) ≤
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i),
        ∑ j ∈ (Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i)).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re) :
    SwapSvdIncOut c ε B R S f := by
  exact sic_case2a_proof hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv hnv' hr hcase hcross

/-- CSP_6 `lemma:svdinc#case2b`: `λ₁ ≤ 1 - ε²/10^{10}` and the cross term is small. -/
theorem swap_svdinc_case2b {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100)
    (hr : 0 < d.r) (hcase : d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f) ≤ 1 - ε ^ 2 / 10 ^ 10)
    (hcross :
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i),
        ∑ j ∈ (Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i)).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re ≤
      (1 - (d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) ^ 2) / 4 * ((val f f f f).re / l2sq f ^ 2)) :
    SwapSvdIncOut c ε B R S f := by
  exact sic_case2b_proof hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv hnv' hr hcase hcross

/-- CSP_6 `lemma:svdinc`. -/
theorem swap_svdinc {c ε B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 10 ^ 13) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (f : (ι → α) → ℂ) (S R : Finset ι) (hSR : S ⊆ R) (hdep : SwapDependsOn R f)
    (hB : ∀ x, ‖f x‖ ≤ B) (d : SwapSvdData S f) (t : ℕ) (ht : (t : ℝ) * (c ^ 4 * ε ^ 16) ≤ 9)
    (hΔ : ((val (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)
        (fun x => f x - d.trunc t x) (fun x => f x - d.trunc t x)).re) ^ (1 / 2 : ℝ) ≤
        c ^ 2 * ε ^ 8 * l2sq f)
    (hnv : ε ^ 2 / 2 ≤ ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f)
    (hnv' : ((val f f f f).re) ^ (1 / 2 : ℝ) / l2sq f ≤ 99 / 100) :
    SwapSvdIncOut c ε B R S f := by
  obtain ⟨hpos, -⟩ := sic_hnv hε0 f hnv
  have hr : 0 < d.r := by
    by_contra h
    have h0 : d.r = 0 := Nat.le_zero.1 (not_lt.1 h)
    haveI : IsEmpty (Fin d.r) := by rw [h0]; infer_instance
    have hf : ∀ x, f x = 0 := fun x => by rw [svdInc_decomp d x]; simp
    have : l2sq f = 0 := by simp [l2sq, hf]
    linarith
  rcases le_or_gt (1 - ε ^ 2 / 10 ^ 10) (d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) with h1 | h1
  · exact swap_svdinc_case1 hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv hnv' hr h1
  · rcases le_total ((1 - (d.lam ⟨0, hr⟩ / Real.sqrt (l2sq f)) ^ 2) / 4 *
        ((val f f f f).re / l2sq f ^ 2))
      (2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i),
        ∑ j ∈ (Finset.univ.filter (fun i : Fin d.r =>
            i.val < t ∧ c * ε ^ 4 * Real.sqrt (l2sq f) / t ≤ d.lam i)).filter (fun j => i < j),
          (d.lam i ^ 2 / l2sq f) * (d.lam j ^ 2 / l2sq f) *
            (val (d.h i) (d.h j) (d.h i) (d.h j)).re) with h2 | h2
    · exact swap_svdinc_case2a hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv hnv' hr h1.le h2
    · exact swap_svdinc_case2b hc0 hc1 hε0 hε1 f S R hSR hdep hB d t ht hΔ hnv hnv' hr h1.le h2

end SwapSvdInc
end TrackB
end RestrictedPolynomials
end
