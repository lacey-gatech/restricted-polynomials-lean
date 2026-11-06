module

public import RestrictedPolynomials.TrackB.K7KcspPair
public import RestrictedPolynomials.TrackB.K7KcspLemma
public import RestrictedPolynomials.TrackB.K7KcspLift
public import RestrictedPolynomials.TrackB.K7KcspCombine
public import RestrictedPolynomials.TrackB.K7KcspArith
public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.CStab

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section LemmaKcspRat

/-! ### Private helpers: finite expectations -/

private theorem k7r_re_cexpect {β : Type} [Fintype β] (P : FinProb β) (g : β → ℂ) :
    (P.cexpect g).re = ∑ a, P.prob a * (g a).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => Complex.re_ofReal_mul _ _

private theorem k7r_re_cexpect_le_add {β : Type} [Fintype β] (P : FinProb β) (f g : β → ℂ)
    (c : ℝ) (h : ∀ a, (f a).re ≤ c + (g a).re) :
    (P.cexpect f).re ≤ c + (P.cexpect g).re := by
  rw [k7r_re_cexpect, k7r_re_cexpect]
  calc ∑ a, P.prob a * (f a).re ≤ ∑ a, P.prob a * (c + (g a).re) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)
    _ = c + ∑ a, P.prob a * (g a).re := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_eq_one, one_mul]

private theorem k7r_re_cexpect_mono {β : Type} [Fintype β] (P : FinProb β) (f g : β → ℂ)
    (h : ∀ a, (f a).re ≤ (g a).re) : (P.cexpect f).re ≤ (P.cexpect g).re := by
  have := k7r_re_cexpect_le_add P f g 0 fun a => by rw [zero_add]; exact h a
  rwa [zero_add] at this

private theorem k7r_sub_le_add {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℝ} (h0 : 0 ≤ q)
    (h1 : q ≤ 1) (G H : Finset ι → ℂ) (c : ℝ) (h : ∀ I, (G I).re ≤ c + (H I).re) :
    (subsetExpect q h0 h1 G).re ≤ c + (subsetExpect q h0 h1 H).re :=
  k7r_re_cexpect_le_add _ _ _ c fun _ => h _

private theorem k7r_sub_mono {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℝ} (h0 : 0 ≤ q)
    (h1 : q ≤ 1) (G H : Finset ι → ℂ) (h : ∀ I, (G I).re ≤ (H I).re) :
    (subsetExpect q h0 h1 G).re ≤ (subsetExpect q h0 h1 H).re :=
  k7r_re_cexpect_mono _ _ _ fun _ => h _

private theorem k7r_norm_cexpect_le_one {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ)
    (hf : ∀ k, ‖f k‖ ≤ 1) : ‖P.cexpect f‖ ≤ 1 := by
  unfold FinProb.cexpect
  calc ‖∑ k, (P.prob k : ℂ) * f k‖ ≤ ∑ k, ‖(P.prob k : ℂ) * f k‖ := norm_sum_le _ _
    _ ≤ ∑ k, P.prob k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P.nonneg k)]
        exact mul_le_of_le_one_right (P.nonneg k) (hf k)
    _ = 1 := P.sum_eq_one

/-- a coordinatewise map commutes with gluing. -/
private theorem k7r_glue_map {ι α β : Type} [Fintype ι] [DecidableEq ι] (I : Finset ι)
    (g : α → β) (z : ↥I → α) (y : ↥Iᶜ → α) :
    (fun t => g (glueFix I z y t)) = glueFix I (fun t => g (z t)) (fun t => g (y t)) := by
  funext t
  unfold glueFix
  by_cases h : t ∈ I <;> simp [h]

private theorem k7r_finProb_ext {α : Type} [Fintype α] (π ρ : FinProb α)
    (h : ∀ a, π.prob a = ρ.prob a) : π = ρ := by
  cases π; cases ρ
  simp only [FinProb.mk.injEq]
  exact funext h

/-- expectation of a pushforward, coordinatewise on `κ`. -/
private theorem k7r_push_pi {B C : Type} [Fintype B] [Fintype C] [DecidableEq C]
    (π : FinProb B) (F : B → C) {κ : Type} [Fintype κ] [DecidableEq κ] (Φ : (κ → C) → ℂ) :
    ((π.pi κ).cexpect fun w => Φ fun t => F (w t)) =
      (((mergePush π F).pi κ).cexpect Φ) := by
  unfold FinProb.cexpect
  rw [← Finset.sum_fiberwise Finset.univ (fun w : κ → B => fun t => F (w t))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∀ w ∈ Finset.univ.filter (fun w : κ → B => (fun t => F (w t)) = u),
      ((π.pi κ).prob w : ℂ) * Φ (fun t => F (w t)) = ((π.pi κ).prob w : ℂ) * Φ u := by
    intro w hw
    rw [(Finset.mem_filter.1 hw).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  have hfib : (Finset.univ.filter fun w : κ → B => (fun t => F (w t)) = u) =
      Fintype.piFinset fun t => Finset.univ.filter fun b => F b = u t := by
    ext w
    simp [funext_iff, Fintype.mem_piFinset]
  rw [hfib, ← Complex.ofReal_sum]
  congr 1
  exact (Finset.prod_univ_sum (fun t => Finset.univ.filter fun b => F b = u t)
    (fun _ b => π.prob b)).symm

private theorem k7r_push_mix {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π ρ σ : FinProb α) (f : α → β) (c d : ℝ)
    (h : ∀ p, π.prob p = c * ρ.prob p + d * σ.prob p) (b : β) :
    (mergePush π f).prob b = c * (mergePush ρ f).prob b + d * (mergePush σ f).prob b := by
  show ∑ a ∈ Finset.univ.filter (fun a => f a = b), π.prob a =
    c * ∑ a ∈ Finset.univ.filter (fun a => f a = b), ρ.prob a +
      d * ∑ a ∈ Finset.univ.filter (fun a => f a = b), σ.prob a
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => h a

/-! ### Private helpers: the restricted correlation -/

/-- the restricted three-slot correlation `𝔼_{ξ'^{J̄}} f_{J→a} conj f_{J→b} conj g_{J→c}` with
`w = (a, b, c)`. -/
private def k7rCorr {B0 Z ι : Type} [Fintype B0] [DecidableEq B0] [Fintype Z] [DecidableEq Z]
    [Fintype ι] [DecidableEq ι] (ξ' : FinProb (B0 × B0 × Z)) (f₀ : (ι → B0) → ℂ)
    (g : (ι → Z) → ℂ) (J : Finset ι) (w : ↥J → B0 × B0 × Z) : ℂ :=
  (ξ'.pi ↥Jᶜ).cexpect fun x =>
    restrictFix J (fun t => (w t).1) f₀ (fun t => (x t).1) *
      star (restrictFix J (fun t => (w t).2.1) f₀ (fun t => (x t).2.1)) *
      star (restrictFix J (fun t => (w t).2.2) g (fun t => (x t).2.2))

/-- the same correlation for the lifted law and the lifted first function. -/
private def k7rCorrL {B0 Z ι : Type} [Fintype B0] [DecidableEq B0] [Fintype Z] [DecidableEq Z]
    [Fintype ι] [DecidableEq ι] (n : B0 → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ' : FinProb (B0 × B0 × Z))
    (f₀ : (ι → B0) → ℂ) (g : (ι → Z) → ℂ) (J : Finset ι) (a : ↥J → K7Lift n) (b : ↥J → B0)
    (c : ↥J → Z) : ℂ :=
  ((k7LiftFirst n hn1 ξ').pi ↥Jᶜ).cexpect fun w =>
    restrictFix J a (fun x : ι → K7Lift n => f₀ fun t => (x t).1) (fun t => (w t).1) *
      star (restrictFix J b f₀ (fun t => (w t).2.1)) *
      star (restrictFix J c g (fun t => (w t).2.2))

private theorem k7r_corrL_eq {B0 Z ι : Type} [Fintype B0] [DecidableEq B0] [Fintype Z]
    [DecidableEq Z] [Fintype ι] [DecidableEq ι] (n : B0 → ℕ) (hn1 : ∀ a, 1 ≤ n a)
    (ξ' : FinProb (B0 × B0 × Z)) (f₀ : (ι → B0) → ℂ) (g : (ι → Z) → ℂ) (J : Finset ι)
    (a : ↥J → K7Lift n) (b : ↥J → B0) (c : ↥J → Z) :
    k7rCorrL n hn1 ξ' f₀ g J a b c = k7rCorr ξ' f₀ g J (fun t => ((a t).1, b t, c t)) :=
  k7_lift_first_corr n hn1 ξ' J a b c f₀ f₀ g

/-- Step 1 of `thm:kcsp-rat` (Markov at the unlifted level): the mixture calculus for
`ξ = ζ ξ' + (1-ζ) ξ''` and the pointwise bound `Re c ≤ ε₁ + 1[|c| ≥ ε₁]` for `|c| ≤ 1`. -/
private theorem k7r_markov_step {B0 Z ι : Type} [Fintype B0] [DecidableEq B0] [Fintype Z]
    [DecidableEq Z] [Fintype ι] [DecidableEq ι] (f₀ : (ι → B0) → ℂ) (g : (ι → Z) → ℂ)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hg : ∀ w, ‖g w‖ ≤ 1) (ξ ξ' ξ'' : FinProb (B0 × B0 × Z))
    {ζ ε₁ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hε₁ : 0 ≤ ε₁)
    (hmix : ∀ p, ξ.prob p = (1 - ζ) * ξ''.prob p + ζ * ξ'.prob p)
    (hE : 2 * ε₁ ≤ ((ξ.pi ι).cexpect fun w => f₀ (fun t => (w t).1) *
      star (f₀ (fun t => (w t).2.1)) * star (g (fun t => (w t).2.2))).re) :
    ε₁ ≤ (subsetExpect (1 - ζ) (by linarith) (by linarith) fun J =>
      (ξ''.pi ↥J).cexpect fun w =>
        if ε₁ ≤ ‖k7rCorr ξ' f₀ g J w‖ then (1 : ℂ) else 0).re := by
  classical
  rw [mixture_calculus hζ0 hζ1 ξ ξ'' ξ' hmix] at hE
  let F : (ι → B0 × B0 × Z) → ℂ := fun w => f₀ (fun t => (w t).1) *
    star (f₀ (fun t => (w t).2.1)) * star (g (fun t => (w t).2.2))
  have hres : ∀ (J : Finset ι) (w : ↥J → B0 × B0 × Z), restrictFix J w F = fun x =>
      restrictFix J (fun t => (w t).1) f₀ (fun t => (x t).1) *
        star (restrictFix J (fun t => (w t).2.1) f₀ (fun t => (x t).2.1)) *
        star (restrictFix J (fun t => (w t).2.2) g (fun t => (x t).2.2)) := by
    intro J w
    funext x
    have e1 := k7r_glue_map J (fun p : B0 × B0 × Z => p.1) w x
    have e2 := k7r_glue_map J (fun p : B0 × B0 × Z => p.2.1) w x
    have e3 := k7r_glue_map J (fun p : B0 × B0 × Z => p.2.2) w x
    show f₀ (fun t => (glueFix J w x t).1) * star (f₀ (fun t => (glueFix J w x t).2.1)) *
        star (g (fun t => (glueFix J w x t).2.2)) =
      f₀ (glueFix J (fun t => (w t).1) (fun t => (x t).1)) *
        star (f₀ (glueFix J (fun t => (w t).2.1) (fun t => (x t).2.1))) *
        star (g (glueFix J (fun t => (w t).2.2) (fun t => (x t).2.2)))
    rw [← e1, ← e2, ← e3]
  have hEb : ∀ (J : Finset ι) (w : ↥J → B0 × B0 × Z),
      (ξ'.pi ↥Jᶜ).cexpect (restrictFix J w F) = k7rCorr ξ' f₀ g J w := by
    intro J w
    rw [hres]
    rfl
  have key := k7r_sub_le_add (q := 1 - ζ) (by linarith) (by linarith)
    (fun J => (ξ''.pi ↥J).cexpect fun w => (ξ'.pi ↥Jᶜ).cexpect (restrictFix J w F))
    (fun J => (ξ''.pi ↥J).cexpect fun w =>
      if ε₁ ≤ ‖k7rCorr ξ' f₀ g J w‖ then (1 : ℂ) else 0) ε₁ ?_
  · linarith
  intro J
  refine k7r_re_cexpect_le_add _ _ _ ε₁ fun w => ?_
  rw [hEb]
  have hnorm : ‖k7rCorr ξ' f₀ g J w‖ ≤ 1 := by
    rw [← hEb]
    refine k7r_norm_cexpect_le_one _ _ fun x => ?_
    rw [hres]
    simp only []
    rw [norm_mul, norm_mul, norm_star, norm_star]
    have h12 : ‖restrictFix J (fun t => (w t).1) f₀ (fun t => (x t).1)‖ *
        ‖restrictFix J (fun t => (w t).2.1) f₀ (fun t => (x t).2.1)‖ ≤ 1 :=
      (mul_le_mul (hf₀ _) (hf₀ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    exact (mul_le_mul h12 (hg _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hre := Complex.re_le_norm (k7rCorr ξ' f₀ g J w)
  by_cases hc : ε₁ ≤ ‖k7rCorr ξ' f₀ g J w‖
  · simp only [hc, ↓reduceIte, Complex.one_re]
    linarith
  · push Not at hc
    simp only [hc.not_ge, ↓reduceIte, Complex.zero_re]
    linarith

open scoped Classical in
/-- Steps 2 and 3 of `thm:kcsp-rat`: the unlifted good restrictions lift to good restrictions of
the lifted first function, at every lift `ã` of the first slot, and the probability transfers to
the first marginal of the lifted `ξ̃''`. -/
private theorem k7r_lift_step {B0 Z ι : Type} [Fintype B0] [DecidableEq B0] [Fintype Z]
    [DecidableEq Z] [Fintype ι] [DecidableEq ι] (n : B0 → ℕ) (hn1 : ∀ a, 1 ≤ n a)
    (f₀ : (ι → B0) → ℂ) (g : (ι → Z) → ℂ) (ξ' ξ'' : FinProb (B0 × B0 × Z))
    (νξ : FinProb (K7Lift n)) {ζ ε₁ δ₆ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hδ60 : 0 < δ₆)
    (hδ61 : δ₆ ≤ 1)
    (hG : ∀ (J : Finset ι) (a : ↥J → K7Lift n) (b : ↥J → B0) (c : ↥J → Z),
      ε₁ ≤ ‖k7rCorrL n hn1 ξ' f₀ g J a b c‖ →
        GoodRestr νξ δ₆ δ₆ δ₆ hδ60.le hδ61
          (restrictFix J a (fun x : ι → K7Lift n => f₀ fun t => (x t).1))) :
    (subsetExpect (1 - ζ) (by linarith) (by linarith) fun J =>
      (ξ''.pi ↥J).cexpect fun w =>
        if ε₁ ≤ ‖k7rCorr ξ' f₀ g J w‖ then (1 : ℂ) else 0).re ≤
    (subsetExpect (1 - ζ) (by linarith) (by linarith) fun J =>
      ((mergePush (k7LiftFirst n hn1 ξ'') fun p => p.1).pi ↥J).cexpect fun a =>
        if GoodRestr νξ δ₆ δ₆ δ₆ hδ60.le hδ61
          (restrictFix J a (fun x : ι → K7Lift n => f₀ fun t => (x t).1))
        then (1 : ℂ) else 0).re := by
  refine k7r_sub_mono (by linarith) (by linarith) _ _ fun J => ?_
  have e1 := k7_lift_first_expect n hn1 ξ'' (κ := ↥J) fun w =>
    if ε₁ ≤ ‖k7rCorr ξ' f₀ g J w‖ then (1 : ℂ) else 0
  have e3 := k7r_push_pi (k7LiftFirst n hn1 ξ'') (fun p : K7Lift n × B0 × Z => p.1) (κ := ↥J)
    fun a => if GoodRestr νξ δ₆ δ₆ δ₆ hδ60.le hδ61
      (restrictFix J a (fun x : ι → K7Lift n => f₀ fun t => (x t).1)) then (1 : ℂ) else 0
  refine le_of_eq_of_le (congrArg Complex.re e1.symm)
    (le_of_le_of_eq (k7r_re_cexpect_mono _ _ _ ?_) (congrArg Complex.re e3))
  intro w
  by_cases hc : ε₁ ≤ ‖k7rCorr ξ' f₀ g J fun t => ((w t).1.1, (w t).2.1, (w t).2.2)‖
  · have hg := hG J (fun t => (w t).1) (fun t => (w t).2.1) (fun t => (w t).2.2)
      (by rw [k7r_corrL_eq]; exact hc)
    simp only [hc, hg, ↓reduceIte]
    exact le_rfl
  · simp only [hc, ↓reduceIte]
    split_ifs <;> simp

/-- the numerical constants of `thm:kcsp-rat` (Lemma `lem:rate`): `δ₆ ≤ exp(-C₆ ε₁^{-C₆})` and `τ`
with the three upper bounds and the lower bound `(α²/8) ε² δ' δ₆²`. -/
private theorem k7r_consts {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {C₆ : ℝ} (hC : 1 ≤ C₆)
    {ε δ' : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1 / 2) :
    ∃ δ₆ τ : ℝ, 0 < δ₆ ∧ δ₆ ≤ 1 ∧ δ₆ ≤ Real.exp (-C₆ * (ε ^ 2 * δ' / 4) ^ (-C₆)) ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ τ ≤ α ^ 2 * δ' * δ₆ ∧ τ ≤ δ₆ / 2 ∧
      τ ≤ ε ^ 2 * δ' / 4 * δ₆ ^ 2 / 2 ∧ α ^ 2 / 8 * (ε ^ 2 * δ') * δ₆ ^ 2 ≤ τ ∧
      Real.exp (-(2 * C₆ * (4 : ℝ) ^ C₆) * (ε ^ 2 * δ') ^ (-(2 * C₆ * (4 : ℝ) ^ C₆))) ≤
        δ₆ ^ 2 := by
  have hx0 : 0 < ε ^ 2 * δ' := by positivity
  have hx1 : ε ^ 2 * δ' ≤ 1 := by
    have : ε ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hδ60 : 0 < Real.exp (-C₆ * (ε ^ 2 * δ' / 4) ^ (-C₆)) := Real.exp_pos _
  have hδ61 : Real.exp (-C₆ * (ε ^ 2 * δ' / 4) ^ (-C₆)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (ε ^ 2 * δ' / 4) ^ (-C₆) := Real.rpow_nonneg (by positivity) _
    nlinarith
  obtain ⟨hτ0, hτh, hτl⟩ := k7_rateTau_bounds hα0 hα1 hε0 hε1 hδ0 hδ1 hδ60 hδ61
  obtain ⟨h1, h2, h3⟩ := k7_rateTau_le α ε δ' (Real.exp (-C₆ * (ε ^ 2 * δ' / 4) ^ (-C₆)))
  exact ⟨_, _, hδ60, hδ61, le_rfl, hτ0, hτh, h1, h2, h3, hτl, k7_rate_exp hC hx0 hx1⟩

/-! ### The target -/

/-- CSP_7 `lemma:kcsp` in the RATIONAL CLASS with CSP_7 `eq:recursion1` (Supplement H, `thm:kcsp-rat`;
no convexity hypothesis `hconv` is needed). The name is never the
unconditional `k7_lemma_kcsp`: `lemma:kcsp` is proved only when the first marginal of the surviving
coordinate is rational with `M ≤ 1/α` (`hrat`, Def. `def:hrat`).

`thm:kcsp` for `k` enters as `ih`, the induction hypothesis in the GENERAL class and the
single-parameter form `(ε²/2, δ')` (`V_k(α, ε²/2, δ')`). The constants `B, c₁` depend on `α` only and are
chosen BEFORE `ε, δ'`, the alphabets, `μ`, `ι`, `f` (the proof gives `B = 2 C₆ 4^{C₆}`,
`c₁ = α²/8`, `C₆` the constant of `k7_apply_3csp` at `α³/2`); `τ` depends on `(α, ε, δ')` only and is
chosen before the alphabets. The conclusion is the `(π, π)` event of `lemma:kcsp` for the coordinate
`j.succAbove s` of the `(k+1)`-ary `μ`, `π = μ_{j.succAbove s}`, the removed coordinate being `j`.
`hrat` is a predicate of the first marginal only; its data `(M, n)` enter no constant except through
`M ≤ 1/α`. -/
theorem k7_lemma_kcsp_rat_of_ih {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ B c₁ : ℝ, 1 ≤ B ∧ 0 < c₁ ∧ c₁ ≤ 1 ∧
      ∀ ε δ' : ℝ, 0 < ε → ε ≤ 1 → 0 < δ' → δ' ≤ 1 / 2 →
        (∀ (A' : Fin k → Type) [∀ i, Fintype (A' i)] [∀ i, DecidableEq (A' i)]
          (μ' : FinProb (∀ i, A' i)), NoNontrivialAbelianEmbeddingPi μ'.support →
          (∀ a ∈ μ'.support, α ≤ μ'.prob a) →
          ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (f' : ∀ i, (ι' → A' i) → ℂ),
            (∀ i x, ‖f' i x‖ ≤ 1) →
            ε ^ 2 / 2 ≤ ‖(μ'.pi ι').cexpect fun X => ∏ i, f' i fun t => X t i‖ →
            ∀ i, δ' ≤ (cstab (μ'.marginalPi i) (1 - δ') (f' i)).re) →
        ∃ (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1),
          c₁ * (ε ^ 2 * δ') * Real.exp (-B * (ε ^ 2 * δ') ^ (-B)) ≤ τ ∧
          ∀ (A : Fin (k + 1) → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
            (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k),
            PairwiseConnectedDist μ → (∀ a ∈ μ.support, α ≤ μ.prob a) →
            NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support →
            (∃ (M : ℕ) (n : A (j.succAbove s) → ℕ), (∀ a, 1 ≤ n a ∧ n a ≤ M) ∧ (M : ℝ) ≤ 1 / α ∧
              ∀ a, (μ.marginalPi (j.succAbove s)).prob a = (n a : ℝ) / M) →
            ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ),
              (∀ i x, ‖f i x‖ ≤ 1) →
              ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
              τ ≤ k7EventProb (μ.marginalPi (j.succAbove s)) (μ.marginalPi (j.succAbove s)) τ τ
                hτ0 hτ1 (f (j.succAbove s)) := by
  classical
  obtain ⟨C₆, hC₆, H6⟩ := k7_apply_3csp (α' := α ^ 3 / 2) (by positivity)
  refine ⟨2 * C₆ * (4 : ℝ) ^ C₆, α ^ 2 / 8, k7_rate_B_ge hC₆, by positivity, by nlinarith, ?_⟩
  intro ε δ' hε0 hε1 hδ0 hδ1 ih
  obtain ⟨δ₆, τ, hδ60, hδ61, hδ6, hτ0, hτh, hτ1, hτ2, hτ3, hτlow, hτexp⟩ :=
    k7r_consts hα0 hα1 hC₆ hε0 hε1 hδ0 hδ1
  refine ⟨τ, hτ0.le, by linarith, ?_, ?_⟩
  · have hx0 : 0 < ε ^ 2 * δ' := by positivity
    calc α ^ 2 / 8 * (ε ^ 2 * δ') *
          Real.exp (-(2 * C₆ * (4 : ℝ) ^ C₆) * (ε ^ 2 * δ') ^ (-(2 * C₆ * (4 : ℝ) ^ C₆)))
        ≤ α ^ 2 / 8 * (ε ^ 2 * δ') * δ₆ ^ 2 :=
          mul_le_mul_of_nonneg_left hτexp (by positivity)
      _ ≤ τ := hτlow
  intro A _ _ μ j s hpc hatom hno hrat ι _ _ f hf hε
  obtain ⟨M, n, hn, hM, hπ⟩ := hrat
  have hn1 : ∀ a, 1 ≤ n a := fun a => (hn a).1
  have hne : Nonempty (A (j.succAbove s)) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := (μ.marginalPi (j.succAbove s)).sum_eq_one
    simp at this
  have : Nonempty (K7Lift n) := k7_lift_nonempty n hn1
  have hf₀ := hf (j.succAbove s)
  -- the inputs of `K7KcspPair`
  obtain ⟨ν, hν⟩ := k7_diagonal_mixture μ j hα0 hatom
  obtain ⟨ξ, hξ⟩ := k7_exists_xi (μ.marginalPi (j.succAbove s)) (k7NuPair j s ν) hα0.le hα1
    hδ0.le (by linarith : δ' ≤ 1)
  obtain ⟨ξ', ξ'', hsupp, hat', hsplit⟩ :=
    k7_xi_split μ j s hα0 hα1 hδ0 hδ1 hatom hno ν hν ξ hξ
  have hξ1 := k7_xi_marginal μ j s hα0 hα1 hδ0.le (by linarith) ν hν ξ hξ
  have hpcξ := k7_obs_pcxi μ j s hα0 hα1 hδ0 (by linarith : δ' < 1) hatom hpc hno ν hν ξ hξ
  have h3 := k7_obs_3wisexi (μ.marginalPi (j.succAbove s)) (k7NuPair j s ν) hα0.le hα1 hδ0.le
    (by linarith) ξ hξ (f (j.succAbove s))
  have hf1 := k7_eq_f1 μ j s hα0 hα1 hatom hno ν hν hε0 hδ0 (by linarith) ih f hf hε
  have hζ0 : 0 ≤ α ^ 2 * δ' := by positivity
  have hζ1 : α ^ 2 * δ' ≤ 1 := by nlinarith [sq_nonneg α]
  have hε₁0 : 0 < ε ^ 2 * δ' / 4 := by positivity
  have hε₁1 : ε ^ 2 * δ' / 4 ≤ 1 := by nlinarith [sq_nonneg ε]
  have hg : ∀ w : ι → Option ↥(k7PairSet (k7NuPair j s ν)),
      ‖k7G (μ.marginalPi (j.succAbove s)) (f (j.succAbove s)) w‖ ≤ 1 :=
    fun w => k7_g_norm_le _ _ hf₀ w
  -- Step 1
  have hE : 2 * (ε ^ 2 * δ' / 4) ≤ ((ξ.pi ι).cexpect fun w =>
      f (j.succAbove s) (fun t => (w t).1) * star (f (j.succAbove s) (fun t => (w t).2.1)) *
        star (k7G (μ.marginalPi (j.succAbove s)) (f (j.succAbove s))
          (fun t => (w t).2.2))).re := by
    rw [h3]
    linarith
  have hmix : ∀ p, ξ.prob p = (1 - α ^ 2 * δ') * ξ''.prob p + α ^ 2 * δ' * ξ'.prob p :=
    fun p => by rw [hsplit p]; ring
  have hstep1 := k7r_markov_step (f (j.succAbove s))
    (fun w => k7G (μ.marginalPi (j.succAbove s)) (f (j.succAbove s)) w) hf₀ hg ξ ξ' ξ'' hζ0 hζ1
    hε₁0.le hmix hE
  -- Step 2: the lift and `k7_apply_3csp`
  have hpc3 : PairwiseConnected3 (k7LiftFirst n hn1 ξ').support :=
    k7_lift_first_pairwiseConnected3 n hn1 ξ' (hsupp ▸ hpcξ)
  have hat3 : ∀ p ∈ (k7LiftFirst n hn1 ξ').support, α ^ 3 / 2 ≤ (k7LiftFirst n hn1 ξ').prob p :=
    fun p hp => (k7_atom_cube hα0 hα1).trans
      (k7_lift_first_atom hα0 (by positivity) M n hn1 (fun a => (hn a).2) hM ξ' hat' p hp)
  obtain ⟨νξ, hνξ, hG6⟩ := H6 (K7Lift n) (A (j.succAbove s))
    (Option ↥(k7PairSet (k7NuPair j s ν))) (k7LiftFirst n hn1 ξ') hpc3 hat3
    (ε ^ 2 * δ' / 4) hε₁0 hε₁1 δ₆ hδ60 hδ61 hδ6
  have hGL : ∀ (J : Finset ι) (a : ↥J → K7Lift n) (b : ↥J → A (j.succAbove s))
      (c : ↥J → Option ↥(k7PairSet (k7NuPair j s ν))),
      ε ^ 2 * δ' / 4 ≤ ‖k7rCorrL n hn1 ξ' (f (j.succAbove s))
        (fun w => k7G (μ.marginalPi (j.succAbove s)) (f (j.succAbove s)) w) J a b c‖ →
        GoodRestr νξ δ₆ δ₆ δ₆ hδ60.le hδ61
          (restrictFix J a (fun x : ι → K7Lift n => f (j.succAbove s) fun t => (x t).1)) :=
    fun J a b c h => hG6 ι J a b c (fun x => f (j.succAbove s) fun t => (x t).1)
      (f (j.succAbove s)) (fun w => k7G (μ.marginalPi (j.succAbove s)) (f (j.succAbove s)) w)
      (fun x => hf₀ _) hf₀ hg h
  -- Step 3
  have hout := hstep1.trans (k7r_lift_step n hn1 (f (j.succAbove s))
    (fun w => k7G (μ.marginalPi (j.succAbove s)) (f (j.succAbove s)) w) ξ' ξ'' νξ hζ0 hζ1 hδ60
    hδ61 hGL)
  -- Step 4: combine
  have hxtmix : ∀ p, (k7LiftFirst n hn1 ξ).prob p =
      (1 - α ^ 2 * δ') * (k7LiftFirst n hn1 ξ'').prob p +
        α ^ 2 * δ' * (k7LiftFirst n hn1 ξ').prob p := by
    intro p
    simp only [k7LiftFirst_prob]
    rw [hmix]
    ring
  have hπ' : ∀ a, (FinProb.uniform (α := K7Lift n)).prob a =
      (1 - α ^ 2 * δ') * (mergePush (k7LiftFirst n hn1 ξ'') fun p => p.1).prob a +
        α ^ 2 * δ' * (mergePush (k7LiftFirst n hn1 ξ') fun p => p.1).prob a := by
    intro a
    rw [← k7_lift_first_marginal (μ.marginalPi (j.succAbove s)) M n hn hπ ξ hξ1 a]
    exact k7r_push_mix _ _ _ _ _ _ hxtmix a
  have hbar := k7_combined_law_unif (mergePush (k7LiftFirst n hn1 ξ') fun p => p.1)
    (mergePush (k7LiftFirst n hn1 ξ'') fun p => p.1) νξ (ζ := α ^ 2 * δ') (δ := δ₆) hπ' hνξ
  have hcomb := k7_combine_restrictions (ι := ι) (FinProb.uniform (α := K7Lift n))
    (mergePush (k7LiftFirst n hn1 ξ') fun p => p.1)
    (mergePush (k7LiftFirst n hn1 ξ'') fun p => p.1) νξ (FinProb.uniform (α := K7Lift n))
    (ζ := α ^ 2 * δ') (δ := δ₆) (p := ε ^ 2 * δ' / 4) (by positivity) hζ1 hδ60 hδ61 hπ' hνξ hbar
    (fun x : ι → K7Lift n => f (j.succAbove s) fun t => (x t).1) hout
  -- Step 5: project
  have hproj := k7_event_project (ι := ι) (k7LiftProj n) (FinProb.uniform (α := K7Lift n))
    (ρ := α ^ 2 * δ' * δ₆) (η := δ₆) (by positivity) (by nlinarith [mul_pos hδ0 hδ60])
    (f (j.succAbove s))
  have hpush : mergePush (FinProb.uniform (α := K7Lift n)) (k7LiftProj n) =
      μ.marginalPi (j.succAbove s) :=
    k7r_finProb_ext _ _ (k7_lift_pushU _ M n hn hπ)
  rw [hpush] at hproj
  have hlow0 : 0 < α ^ 2 * δ' * δ₆ := by positivity
  have hlow1 : α ^ 2 * δ' * δ₆ ≤ 1 := by nlinarith [mul_pos hδ0 hδ60]
  have hev : ε ^ 2 * δ' / 4 * δ₆ ≤ k7EventProb (μ.marginalPi (j.succAbove s))
      (μ.marginalPi (j.succAbove s)) (α ^ 2 * δ' * δ₆) δ₆ hlow0.le hlow1
      (f (j.succAbove s)) := by
    rw [← hproj]
    exact hcomb
  -- Step 6: lower the rate
  have hlow := k7_eventProb_lowering (μ.marginalPi (j.succAbove s)) hlow0 hlow1 hτ0 hτ1 hδ60
    (f (j.succAbove s)) hf₀ hev
  have hmono := k7_eventProb_mono (μ.marginalPi (j.succAbove s)) (μ.marginalPi (j.succAbove s))
    hτ0.le (by linarith : τ ≤ 1) (by linarith : τ ≤ δ₆ / 2) (f (j.succAbove s))
  calc τ ≤ ε ^ 2 * δ' / 4 * δ₆ * δ₆ / 2 := by nlinarith
    _ ≤ _ := hlow
    _ ≤ _ := hmono

end LemmaKcspRat

end TrackB
end RestrictedPolynomials
end
