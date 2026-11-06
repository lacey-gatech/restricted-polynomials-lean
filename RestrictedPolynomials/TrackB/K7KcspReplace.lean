module

public import RestrictedPolynomials.TrackB.K7KcspLemma
public import RestrictedPolynomials.TrackB.K7ProductFunctions
public import RestrictedPolynomials.TrackB.ProductFunctionsAux
public import RestrictedPolynomials.TrackB.RestrictCompose
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Track B: CSP_7 `lemma:replace` and `cor:replace`

Source: CSP7 `kcsp.tex` l. 640-680 and 765-780. Steps:
CSP_7 `lemma:replace` (`apply-lemma-kcsp`, `averaging`), CSP_7 `cor:replace` (`iterate-replace`),
CSP_7 `thm:kcsp` (`all-coordinates-by-symmetry`, `apply-cor-replace-and-fstab`). (`lemma:replace` has
probability `τ²/2`, not the printed `τ/2`.)

The event `k7ReplEventProb` covers `lemma:replace` (`T = {i₁}`) and `cor:replace` (`T` = all
coordinates but the survivor). The averaging step is Markov's inequality over the conditional law of
the other coordinates of `z` given `z_{i₁}` (written without division: fibres of `z ↦ z_{i₁}`); the
iteration composes nested restrictions by `nested_restriction_law` with all laws `μ`.

`k7_cor_replace_iterate` carries `(hp' : 0 ≤ p')`: without it the statement is
false (both `q` and `p'` negative make `q * p'` exceed `1`, while every event probability is at most
`1`). `k7_cor_replace_of_kcsp` uses it with `p' = τ²/2`.
-/

@[expose] public section

open Finset
open scoped BigOperators
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### Private helpers on finite expectations -/

section Helpers

private theorem k7r_re_cexpect_eq {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) :
    (P.cexpect f).re = ∑ k, P.prob k * (f k).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => Complex.re_ofReal_mul _ _

private theorem k7r_re_cexpect_scaled {κ : Type} [Fintype κ] (P : FinProb κ) (c : ℝ)
    (f g : κ → ℂ) (h : ∀ k, c * (f k).re ≤ (g k).re) : c * (P.cexpect f).re ≤ (P.cexpect g).re := by
  rw [k7r_re_cexpect_eq, k7r_re_cexpect_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

private theorem k7r_re_cexpect_ge {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) (c : ℝ)
    (h : ∀ k, c ≤ (f k).re) : c ≤ (P.cexpect f).re := by
  rw [k7r_re_cexpect_eq]
  calc c = ∑ k, P.prob k * c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

private theorem k7r_norm_cexpect_le_one {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ)
    (hf : ∀ k, ‖f k‖ ≤ 1) : ‖P.cexpect f‖ ≤ 1 := by
  unfold FinProb.cexpect
  calc ‖∑ k, (P.prob k : ℂ) * f k‖ ≤ ∑ k, ‖(P.prob k : ℂ) * f k‖ := norm_sum_le _ _
    _ ≤ ∑ k, P.prob k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P.nonneg k)]
        exact mul_le_of_le_one_right (P.nonneg k) (hf k)
    _ = 1 := P.sum_eq_one

private theorem k7r_cexpect_const_mul {κ : Type} [Fintype κ] (P : FinProb κ) (c : ℂ)
    (f : κ → ℂ) : P.cexpect (fun k => c * f k) = c * P.cexpect f := by
  unfold FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem k7r_star_cexpect {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) :
    star (P.cexpect f) = P.cexpect (fun k => star (f k)) := by
  unfold FinProb.cexpect
  rw [star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]

private theorem k7r_cexpect_indicator {κ : Type} [Fintype κ] [DecidableEq κ] (P : FinProb κ)
    (w : κ) (K : ℂ) : P.cexpect (fun w' => (if w' = w then (1 : ℂ) else 0) * K) = (P.prob w : ℂ) * K := by
  unfold FinProb.cexpect
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private theorem k7r_re_nested_scaled {β : Type} [Fintype β] {κ : Type} [Fintype κ]
    [DecidableEq κ] {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (ν : FinProb β) (c : ℝ)
    (f g : ∀ I : Finset κ, (↥I → β) → ℂ) (h : ∀ I z, c * (f I z).re ≤ (g I z).re) :
    c * (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (f I)).re ≤
      (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (g I)).re := by
  unfold subsetExpect
  exact k7r_re_cexpect_scaled _ c _ _ fun s => k7r_re_cexpect_scaled _ c _ _ fun z => h _ z

/-- Markov's inequality on a sub-measure `m` (a fibre): `τ M ≤ ∑ m c` with `0 ≤ c ≤ 1` gives
`(τ/2) M ≤ ∑ m e` for any `e ≥ 0` that is `≥ 1` where `c ≥ τ/2`. -/
private theorem k7r_markov {κ : Type} [Fintype κ] (m c e : κ → ℝ) (hm : ∀ z, 0 ≤ m z)
    (hc1 : ∀ z, c z ≤ 1) (he0 : ∀ z, 0 ≤ e z) {τ : ℝ} (hτ : 0 ≤ τ)
    (he : ∀ z, τ / 2 ≤ c z → 1 ≤ e z) (h : τ * ∑ z, m z ≤ ∑ z, m z * c z) :
    τ / 2 * ∑ z, m z ≤ ∑ z, m z * e z := by
  have hpt : ∀ z, m z * c z ≤ m z * e z + τ / 2 * m z := by
    intro z
    by_cases hz : τ / 2 ≤ c z
    · have h1 := he z hz
      have := mul_nonneg (hm z) (sub_nonneg.2 (hc1 z))
      have := mul_nonneg (hm z) (sub_nonneg.2 h1)
      have := mul_nonneg (hm z) hτ
      nlinarith
    · push Not at hz
      have := mul_le_mul_of_nonneg_left hz.le (hm z)
      have := mul_nonneg (hm z) (he0 z)
      nlinarith
  have := Finset.sum_le_sum fun z (_ : z ∈ (univ : Finset κ)) => hpt z
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  linarith

/-- the product law splits along a fixed set: `𝔼_{π^κ} G = 𝔼_{w ∼ π^I} 𝔼_{y ∼ π^{Iᶜ}} G(w, y)`. -/
private theorem k7r_cexpect_glue {β : Type} [Fintype β] [DecidableEq β] (π : FinProb β) {κ : Type}
    [Fintype κ] [DecidableEq κ] (I : Finset κ) (G : (κ → β) → ℂ) :
    (π.pi κ).cexpect G =
      (π.pi ↥I).cexpect fun w => (π.pi ↥Iᶜ).cexpect fun y => G (glueFix I w y) := by
  rw [← cexpect_comm]
  have h := inner_glue π π I G
  have h2 : (π.pi ↥Iᶜ).cexpect (fun z => (π.pi ↥I).cexpect
      fun y => G (glueFix I y z)) = (π.pi κ).cexpect G := by
    refine h.trans ?_
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [FinProb.pi]
  exact h2.symm

private theorem k7r_glue_fst {β : Type} [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    [DecidableEq κ] (I : Finset κ) (w : ↥I → β) (y : ↥Iᶜ → β) :
    (fun t : ↥I => glueFix I w y t) = w := by
  funext t
  simp [glueFix, t.2]

private theorem k7r_glue_snd {β : Type} [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    [DecidableEq κ] (I : Finset κ) (w : ↥I → β) (y : ↥Iᶜ → β) :
    (fun t : ↥Iᶜ => glueFix I w y t) = y := by
  funext t
  have : (t : κ) ∉ I := mem_compl.1 t.2
  simp [glueFix, this]

/-- a product over `κ` of a glued point splits along `I'`. -/
private theorem k7r_prod_glue_split {β : Type} [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    [DecidableEq κ] (I' : Finset κ) (Q : κ → β → ℂ) (w : ↥I' → β) (y : ↥I'ᶜ → β) :
    ∏ t, Q t (glueFix I' w y t) = (∏ t : ↥I', Q t.1 (w t)) * ∏ t : ↥I'ᶜ, Q t.1 (y t) := by
  rw [← Finset.prod_mul_prod_compl I' (fun t => Q t (glueFix I' w y t))]
  congr 1
  · rw [← Finset.prod_coe_sort I']
    exact Finset.prod_congr rfl fun t _ => by simp [glueFix, t.2]
  · rw [← Finset.prod_coe_sort I'ᶜ]
    refine Finset.prod_congr rfl fun t _ => ?_
    have : (t : κ) ∉ I' := mem_compl.1 t.2
    simp [glueFix, this]

/-- `𝔼_{I ∼_0} G(I) = G(∅)`. -/
private theorem k7r_subsetExpect_one_sub_one {κ : Type} [Fintype κ] [DecidableEq κ]
    (h0 : (0 : ℝ) ≤ 1 - 1) (h1 : (1 : ℝ) - 1 ≤ 1) (G : Finset κ → ℂ) :
    subsetExpect (1 - 1) h0 h1 G = G ∅ := by
  unfold subsetExpect FinProb.cexpect
  rw [Finset.sum_eq_single (fun _ => false)]
  · have hp : ((bernoulli (1 - 1) h0 h1).pi κ).prob (fun _ => false) = 1 := by
      simp [FinProb.pi, bernoulli]
    have ht : trueSet (fun _ : κ => false) = ∅ := by
      ext
      simp [trueSet]
    simp only [hp, ht, Complex.ofReal_one, one_mul]
  · intro s _ hs
    obtain ⟨i, hi⟩ : ∃ i, s i = true := by
      by_contra hne
      push Not at hne
      apply hs
      funext i
      simpa using hne i
    have : ((bernoulli (1 - 1) h0 h1).pi κ).prob s = 0 := by
      show ∏ i, (bernoulli (1 - 1) h0 h1).prob (s i) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bernoulli, hi])
    rw [this]
    simp
  · simp

end Helpers

section Replace
variable {k : ℕ} {A : Fin (k + 1) → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- the probability `Pr_{I ∼_{1-ρ}[ι], z ∼ μ^I}[∃ 1-bounded product functions Pᵢ (i ∈ T) on Ī with
|𝔼_{x ∼ μ^{⊗Ī}} ∏_{i ∈ T} Pᵢ(xᵢ) ∏_{i ∉ T} (fᵢ)_{I→zᵢ}(xᵢ)| ≥ η]`: the event of CSP_7 `lemma:replace` (`T = {j}`) and of
CSP_7 `cor:replace` (`T` = all coordinates but the surviving one; only the surviving `z_i` is used). `ρ` = free rate.
A real number, not a bundled `Prop`. -/
def k7ReplEventProb (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (ρ η : ℝ) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (f : ∀ i, (ι → A i) → ℂ) : ℝ :=
  (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
    (μ.pi ↥I).cexpect fun z =>
      if ∃ P : ∀ i, ↥Iᶜ → A i → ℂ, (∀ i ∈ T, ∀ t a, ‖P i t a‖ ≤ 1) ∧
          η ≤ ‖(μ.pi ↥Iᶜ).cexpect fun X => ∏ i,
            (if i ∈ T then ∏ t, P i t (X t i)
              else restrictFix I (fun t => z t i) (f i) (fun t => X t i))‖
        then (1 : ℂ) else 0).re

/-! ### Private helpers on the event -/

/-- the event inside `k7ReplEventProb`. -/
private def k7rGood (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (η : ℝ)
    (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι) (z : ↥I → ∀ i, A i) : Prop :=
  ∃ P : ∀ i, ↥Iᶜ → A i → ℂ, (∀ i ∈ T, ∀ t a, ‖P i t a‖ ≤ 1) ∧
    η ≤ ‖(μ.pi ↥Iᶜ).cexpect fun X => ∏ i,
      (if i ∈ T then ∏ t, P i t (X t i)
        else restrictFix I (fun t => z t i) (f i) (fun t => X t i))‖

open scoped Classical in
/-- its indicator. -/
private def k7rInd (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (η : ℝ)
    (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι) (z : ↥I → ∀ i, A i) : ℂ :=
  if k7rGood μ T η f I z then 1 else 0

omit [∀ i, DecidableEq (A i)] in
private theorem k7r_replEventProb_eq (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1)))
    (ρ η : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f : ∀ i, (ι → A i) → ℂ) :
    k7ReplEventProb μ T ρ η h0 h1 f =
      (subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (μ.pi ↥I).cexpect fun z => k7rInd μ T η f I z).re :=
  rfl

omit [∀ i, DecidableEq (A i)] in
private theorem k7r_replEventProb_congr (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1)))
    {ρ ρ' η η' : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1)
    (f : ∀ i, (ι → A i) → ℂ) (hρ : ρ = ρ') (hη : η = η') :
    k7ReplEventProb μ T ρ η h0 h1 f = k7ReplEventProb μ T ρ' η' h0' h1' f := by
  subst hρ hη
  rfl

omit [∀ i, DecidableEq (A i)] in
private theorem k7r_ind_re_nonneg (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (η : ℝ)
    (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι) (z : ↥I → ∀ i, A i) :
    0 ≤ (k7rInd μ T η f I z).re := by
  unfold k7rInd
  split_ifs <;> simp

omit [∀ i, DecidableEq (A i)] in
private theorem k7r_ind_re_of (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (η : ℝ)
    (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι) (z : ↥I → ∀ i, A i) (h : k7rGood μ T η f I z) :
    (k7rInd μ T η f I z).re = 1 := by
  unfold k7rInd
  simp [h]

omit [∀ i, DecidableEq (A i)] in
private theorem k7r_ind_re_of_not (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (η : ℝ)
    (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι) (z : ↥I → ∀ i, A i) (h : ¬ k7rGood μ T η f I z) :
    (k7rInd μ T η f I z).re = 0 := by
  unfold k7rInd
  simp [h]

omit [∀ i, DecidableEq (A i)] in
private theorem k7r_ind_re_le_one (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1))) (η : ℝ)
    (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι) (z : ↥I → ∀ i, A i) :
    (k7rInd μ T η f I z).re ≤ 1 := by
  unfold k7rInd
  split_ifs <;> simp

/-- the mass of a fibre `{X | X·j = x}` is the mass of `x` under `μ_j^{⊗κ}`. -/
private theorem k7r_fibre_mass (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (x : κ → A j) :
    ∑ X : κ → ∀ i, A i, (if (fun t => X t j) = x then (μ.pi κ).prob X else 0) =
      ((μ.marginalPi j).pi κ).prob x := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ.filter fun X : κ → ∀ i, A i => (fun t => X t j) = x) =
      Fintype.piFinset fun t => Finset.univ.filter fun y : ∀ i, A i => y j = x t := by
    ext X
    simp [Fintype.mem_piFinset, funext_iff]
  rw [h]
  simp only [FinProb.pi, FinProb.marginalPi]
  rw [Finset.prod_univ_sum]

/-- the expectation of a function of one coordinate is an expectation under the marginal. -/
private theorem k7r_cexpect_marginal (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {κ : Type}
    [Fintype κ] [DecidableEq κ] (G : (κ → A j) → ℂ) :
    (μ.pi κ).cexpect (fun X => G (fun t => X t j)) = ((μ.marginalPi j).pi κ).cexpect G := by
  unfold FinProb.cexpect
  have h : ∀ X : κ → ∀ i, A i, ((μ.pi κ).prob X : ℂ) * G (fun t => X t j) =
      ∑ x, (if (fun t => X t j) = x then ((μ.pi κ).prob X : ℂ) else 0) * G x := by
    intro X
    rw [Finset.sum_eq_single (fun t => X t j)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  rw [Finset.sum_congr rfl fun X _ => h X, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [← k7r_fibre_mass μ j x]
  push_cast
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs <;> simp

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
/-- the `i`-th letters of a glued point are the glued `i`-th letters. -/
private theorem k7r_glue_comp (I : Finset ι) (z : ↥I → ∀ i, A i) (Y : ↥Iᶜ → ∀ i, A i)
    (i : Fin (k + 1)) :
    (fun t => glueFix I z Y t i) = glueFix I (fun t => z t i) (fun t => Y t i) := by
  funext t
  unfold glueFix
  split_ifs <;> rfl

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
/-- the `i`-th letters of the combined fixing are the combined `i`-th letters. -/
private theorem k7r_composeVals_comp (I : Finset ι) (I' : Finset ↥Iᶜ) (z : ↥I → ∀ i, A i)
    (z' : ↥I' → ∀ i, A i) (i : Fin (k + 1)) :
    composeVals I I' (fun t => z t i) (fun t => z' t i) = fun t => composeVals I I' z z' t i := by
  funext t
  unfold composeVals
  split_ifs <;> rfl

/-- `𝔼_{μ^{⊗ι}} [∏_{i ≠ i₁} fᵢ(Xᵢ) · H(X_{i₁})] = 𝔼_{x ∼ μ_{i₁}^{⊗ι}} f̃_{i₁}(x) H(x)` (the defining property of
the conditional expectation `f̃`, from `replace_cexpect_prod_eq`). -/
private theorem k7r_tilde_mul (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ)
    (i₁ : Fin (k + 1)) (H : (ι → A i₁) → ℂ) :
    (μ.pi ι).cexpect (fun X => (∏ i ∈ univ.erase i₁, f i (fun t => X t i)) * H (fun t => X t i₁)) =
      ((μ.marginalPi i₁).pi ι).cexpect (fun x => replaceCondProdExp μ f i₁ x * H x) := by
  have h := replace_cexpect_prod_eq μ (Function.update f i₁ H) i₁
  have hp : ∀ X : ι → ∀ i, A i, ∏ i ∈ univ.erase i₁, Function.update f i₁ H i (fun t => X t i) =
      ∏ i ∈ univ.erase i₁, f i (fun t => X t i) := fun X =>
    Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hc : replaceCondProdExp μ (Function.update f i₁ H) i₁ = replaceCondProdExp μ f i₁ := by
    funext x
    unfold replaceCondProdExp
    simp only [hp]
  rw [hc, Function.update_self] at h
  rw [← h]
  congr 1
  funext X
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i₁), Function.update_self, hp, mul_comm]

/-! ### Targets: the base, the symmetry, and `lemma:replace` -/

/-- zero rounds: `I = ∅` (free rate `1`), no coordinate replaced. -/
theorem k7_replEventProb_base (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) {η : ℝ}
    (h : η ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖) :
    1 ≤ k7ReplEventProb μ ∅ 1 η zero_le_one le_rfl f := by
  rw [k7r_replEventProb_eq, k7r_subsetExpect_one_sub_one]
  refine k7r_re_cexpect_ge _ _ _ fun z => le_of_eq (k7r_ind_re_of μ ∅ η f ∅ z ?_).symm
  refine ⟨fun _ _ _ => 0, fun i hi => absurd hi (Finset.notMem_empty i), ?_⟩
  have he : ∀ t : ι, t ∈ (∅ : Finset ι)ᶜ := fun t => by simp
  have hcx := cexpect_pi_equiv (Equiv.subtypeUnivEquiv he) μ
    (fun X : ι → ∀ i, A i => ∏ i, f i fun t => X t i)
  refine h.trans (le_of_eq ?_)
  rw [← hcx]
  congr 2

/-- CSP_7 `thm:kcsp`, step `all-coordinates-by-symmetry`, and the premise discharge of CSP_7 `lemma:replace`, step `apply-lemma-kcsp`
(`obs:pc`, `obs:sub`, and the unstated coordinate permutation): a conclusion of `lemma:kcsp`
for every pair (removed `j`, surviving `s`) gives it for every coordinate `i₁` of a `μ` without abelian
embeddings. -/
theorem k7_kcsp_any_coordinate (μ : FinProb (∀ i, A i)) (hk : 1 ≤ k)
    (hno : NoNontrivialAbelianEmbeddingPi μ.support) {ε τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hF3 : ∀ (j : Fin (k + 1)) (s : Fin k), PairwiseConnectedDist μ →
      NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support →
      ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
        (∀ i x, ‖F i x‖ ≤ 1) → ε ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
        τ ≤ k7EventProb (μ.marginalPi (j.succAbove s)) (μ.marginalPi (j.succAbove s)) τ τ hτ0 hτ1
          (F (j.succAbove s))) :
    ∀ (i₁ : Fin (k + 1)) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
      (∀ i x, ‖F i x‖ ≤ 1) → ε ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      τ ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) τ τ hτ0 hτ1 (F i₁) := by
  intro i₁ ι' _ _ F hF hcorr
  have hcard : 1 < Fintype.card (Fin (k + 1)) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i₁
  obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hj)
  have hpc := pairwiseConnected_of_noNontrivialAbelianEmbeddingPi μ hno
  have hno' : NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support := by
    rw [k7_dropMarg_support]
    exact noNontrivialAbelianEmbeddingPi_image_succAbove j μ.support hno
  exact hF3 j s hpc hno' ι' F hF hcorr

/-- CSP_7 `lemma:replace`, step `apply-lemma-kcsp` (the tuple `((fᵢ)_{i ≠ i₁}, conj f̃_{i₁})` has correlation
`‖f̃_{i₁}‖₂² ≥ ε²`, `replace_eps_sq_le_l2sq`, `replace_cexpect_prod_erase_mul_star`, so `lemma:kcsp` applies to `conj f̃`). -/
theorem k7_replace_apply_lemma_kcsp (μ : FinProb (∀ i, A i)) (i₁ : Fin (k + 1)) {ε τ : ℝ}
    (hε0 : 0 < ε) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hlk : ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
      (∀ i x, ‖F i x‖ ≤ 1) → ε ^ 2 ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      τ ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) τ τ hτ0 hτ1 (F i₁))
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hε : ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖) :
    τ ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) τ τ hτ0 hτ1
      (fun x => star (replaceCondProdExp μ f i₁ x)) := by
  let g : (ι → A i₁) → ℂ := fun x => star (replaceCondProdExp μ f i₁ x)
  let F : ∀ i, (ι → A i) → ℂ := Function.update f i₁ g
  have hFi : F i₁ = g := Function.update_self _ _ _
  have hF1 : ∀ i x, ‖F i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = i₁
    · subst hi
      rw [hFi]
      show ‖star (replaceCondProdExp μ f i x)‖ ≤ 1
      rw [norm_star]
      exact replace_condProdExp_norm_le μ f hf i x
    · show ‖Function.update f i₁ g i x‖ ≤ 1
      rw [Function.update_of_ne hi]
      exact hf i x
  have hcorr : ε ^ 2 ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, F i fun t => X t i‖ := by
    have h1 : (μ.pi ι).cexpect (fun X => ∏ i, F i fun t => X t i) =
        (μ.pi ι).cexpect (fun X => (∏ i ∈ univ.erase i₁, f i (fun t => X t i)) *
          star (replaceCondProdExp μ f i₁ (fun t => X t i₁))) := by
      congr 1
      funext X
      rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i₁), mul_comm, hFi]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      show Function.update f i₁ g i _ = _
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [h1, replace_cexpect_prod_erase_mul_star, Complex.norm_real, Real.norm_eq_abs]
    exact (replace_eps_sq_le_l2sq μ f hf i₁ hε0.le hε).trans (le_abs_self _)
  have := hlk ι F hF1 hcorr
  rwa [hFi] at this

/-- one fibre of the averaging step: a good `(I, w)` for `conj f̃_{i₁}` (witness `P`) gives, by Markov over
the conditional law of the other letters of `z` given `z_{i₁} = w`, mass `≥ (τ/2) μ_{i₁}^I(w)` of good `z`. -/
private theorem k7r_avg_fiber (μ : FinProb (∀ i, A i)) (i₁ : Fin (k + 1)) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) (I : Finset ι) (w : ↥I → A i₁)
    (P : ↥Iᶜ → A i₁ → ℂ) (hP : ∀ i a, ‖P i a‖ ≤ 1)
    (hb : τ ≤ ‖((μ.marginalPi i₁).pi ↥Iᶜ).cexpect fun x =>
      restrictFix I w (fun x => star (replaceCondProdExp μ f i₁ x)) x * ∏ i, P i (x i)‖) :
    τ / 2 * ((μ.marginalPi i₁).pi ↥I).prob w ≤
      ∑ z : ↥I → ∀ i, A i, (if (fun t => z t i₁) = w then (μ.pi ↥I).prob z else 0) *
        (k7rInd μ {i₁} (τ / 2) f I z).re := by
  classical
  set μ₁ := μ.marginalPi i₁ with hμ₁
  set ft := replaceCondProdExp μ f i₁ with hft
  let Pc : (↥Iᶜ → A i₁) → ℂ := fun y => ∏ t, star (P t (y t))
  let H : (ι → A i₁) → ℂ := fun x =>
    (if (fun t : ↥I => x t) = w then (1 : ℂ) else 0) * Pc (fun t : ↥Iᶜ => x t)
  let E : (↥I → ∀ i, A i) → ℂ := fun z => (μ.pi ↥Iᶜ).cexpect fun Y =>
    (∏ i ∈ univ.erase i₁, restrictFix I (fun t => z t i) (f i) (fun t => Y t i)) *
      Pc (fun t => Y t i₁)
  set Ehyp : ℂ := (μ₁.pi ↥Iᶜ).cexpect fun x =>
    restrictFix I w (fun x => star (ft x)) x * ∏ i, P i (x i) with hEhyp
  -- the `μ_{i₁}` side
  have hL : (μ₁.pi ι).cexpect (fun x => ft x * H x) = ((μ₁.pi ↥I).prob w : ℂ) * star Ehyp := by
    rw [k7r_cexpect_glue μ₁ I]
    have h1 : ∀ w' : ↥I → A i₁, ((μ₁.pi ↥Iᶜ).cexpect fun y => ft (glueFix I w' y) *
        H (glueFix I w' y)) = (if w' = w then (1 : ℂ) else 0) * star Ehyp := by
      intro w'
      simp only [H, k7r_glue_fst, k7r_glue_snd]
      by_cases hw : w' = w
      · subst hw
        rw [ite_eq_left rfl, one_mul, hEhyp, k7r_star_cexpect]
        congr 1
        funext y
        simp only [one_mul, restrictFix, Pc, star_mul', star_star, star_prod]
      · simp only [ite_eq_right hw, zero_mul, mul_zero]
        unfold FinProb.cexpect
        simp
    simp only [h1]
    exact k7r_cexpect_indicator _ w _
  -- the `μ` side
  have hR : (μ.pi ι).cexpect (fun X => (∏ i ∈ univ.erase i₁, f i (fun t => X t i)) *
      H (fun t => X t i₁)) =
      ∑ z, (((if (fun t => z t i₁) = w then (μ.pi ↥I).prob z else 0 : ℝ)) : ℂ) * E z := by
    rw [k7r_cexpect_glue μ I]
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun z _ => ?_
    have h2 : ∀ Y : ↥Iᶜ → ∀ i, A i,
        (∏ i ∈ univ.erase i₁, f i (fun t => glueFix I z Y t i)) * H (fun t => glueFix I z Y t i₁) =
          (if (fun t => z t i₁) = w then (1 : ℂ) else 0) *
            ((∏ i ∈ univ.erase i₁, restrictFix I (fun t => z t i) (f i) (fun t => Y t i)) *
              Pc (fun t => Y t i₁)) := by
      intro Y
      simp only [k7r_glue_comp, H, k7r_glue_fst, k7r_glue_snd]
      unfold restrictFix
      ring
    simp only [h2]
    have h3 : ∑ Y : ↥Iᶜ → ∀ i, A i, ((μ.pi ↥Iᶜ).prob Y : ℂ) *
        ((if (fun t => z t i₁) = w then (1 : ℂ) else 0) *
          ((∏ i ∈ univ.erase i₁, restrictFix I (fun t => z t i) (f i) (fun t => Y t i)) *
            Pc (fun t => Y t i₁))) = (if (fun t => z t i₁) = w then (1 : ℂ) else 0) * E z := by
      rw [← k7r_cexpect_const_mul]
      rfl
    rw [h3]
    split_ifs <;> simp
  have hglob := k7r_tilde_mul μ f i₁ H
  rw [hR, ← hμ₁, ← hft, hL] at hglob
  -- the fibre weights
  let m : (↥I → ∀ i, A i) → ℝ := fun z => if (fun t => z t i₁) = w then (μ.pi ↥I).prob z else 0
  have hm : ∀ z, 0 ≤ m z := fun z => by
    show 0 ≤ (if (fun t => z t i₁) = w then (μ.pi ↥I).prob z else 0)
    split_ifs
    · exact (μ.pi ↥I).nonneg z
    · exact le_rfl
  have hM : ∑ z, m z = (μ₁.pi ↥I).prob w := k7r_fibre_mass μ i₁ w
  have hE1 : ∀ z, ‖E z‖ ≤ 1 := by
    intro z
    refine k7r_norm_cexpect_le_one _ _ fun Y => ?_
    rw [norm_mul, norm_prod]
    have h1 : ∏ i ∈ univ.erase i₁, ‖restrictFix I (fun t => z t i) (f i) (fun t => Y t i)‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hf i _
    have h2 : ‖Pc (fun t => Y t i₁)‖ ≤ 1 := by
      show ‖∏ t, star (P t (Y t i₁))‖ ≤ 1
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun t _ => by rw [norm_star]; exact hP _ _
    calc (∏ i ∈ univ.erase i₁, ‖restrictFix I (fun t => z t i) (f i) (fun t => Y t i)‖) *
          ‖Pc (fun t => Y t i₁)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hτM : τ * ∑ z, m z ≤ ∑ z, m z * ‖E z‖ := by
    rw [hM]
    have hw0 := (μ₁.pi ↥I).nonneg w
    calc τ * (μ₁.pi ↥I).prob w ≤ (μ₁.pi ↥I).prob w * ‖Ehyp‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hb hw0
      _ = ‖((μ₁.pi ↥I).prob w : ℂ) * star Ehyp‖ := by
          rw [norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hw0]
      _ = ‖∑ z, ((m z : ℝ) : ℂ) * E z‖ := by rw [← hglob]
      _ ≤ ∑ z, m z * ‖E z‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hm z)]
  have hgood : ∀ z, τ / 2 ≤ ‖E z‖ → 1 ≤ (k7rInd μ {i₁} (τ / 2) f I z).re := by
    intro z hz
    refine le_of_eq (k7r_ind_re_of μ {i₁} (τ / 2) f I z ?_).symm
    let P' : ∀ i, ↥Iᶜ → A i → ℂ :=
      Function.update (β := fun i => ↥Iᶜ → A i → ℂ) (fun _ _ _ => 0) i₁ (fun t a => star (P t a))
    have hP'1 : P' i₁ = fun t a => star (P t a) := Function.update_self _ _ _
    refine ⟨P', fun i hi t a => ?_, ?_⟩
    · obtain rfl := Finset.mem_singleton.1 hi
      rw [hP'1, norm_star]
      exact hP t a
    · have hEz : ((μ.pi ↥Iᶜ).cexpect fun X => ∏ i,
          (if i ∈ ({i₁} : Finset (Fin (k + 1))) then ∏ t, P' i t (X t i)
            else restrictFix I (fun t => z t i) (f i) (fun t => X t i))) = E z := by
        show _ = (μ.pi ↥Iᶜ).cexpect fun Y =>
          (∏ i ∈ univ.erase i₁, restrictFix I (fun t => z t i) (f i) (fun t => Y t i)) *
            Pc (fun t => Y t i₁)
        refine congrArg (μ.pi ↥Iᶜ).cexpect (funext fun Y => ?_)
        rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i₁),
          ite_eq_left (Finset.mem_singleton_self i₁), hP'1, mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [ite_eq_right (by simpa using Finset.ne_of_mem_erase hi)]
      rw [hEz]
      exact hz
  have hmk := k7r_markov m (fun z => ‖E z‖) (fun z => (k7rInd μ {i₁} (τ / 2) f I z).re) hm hE1
    (fun z => k7r_ind_re_nonneg _ _ _ _ _ _) hτ0 hgood hτM
  rw [hM] at hmk
  exact hmk

open scoped Classical in
/-- one fixed set `I` of the averaging step. -/
private theorem k7r_avg_I (μ : FinProb (∀ i, A i)) (i₁ : Fin (k + 1)) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) (I : Finset ι) :
    τ / 2 * ((((μ.marginalPi i₁).pi ↥I).cexpect fun w =>
      if ∃ P : ↥Iᶜ → A i₁ → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
          τ ≤ ‖((μ.marginalPi i₁).pi ↥Iᶜ).cexpect fun x =>
            restrictFix I w (fun x => star (replaceCondProdExp μ f i₁ x)) x * ∏ i, P i (x i)‖
        then (1 : ℂ) else 0).re) ≤
      ((μ.pi ↥I).cexpect fun z => k7rInd μ {i₁} (τ / 2) f I z).re := by
  rw [k7r_re_cexpect_eq, k7r_re_cexpect_eq, Finset.mul_sum]
  have hRHS : ∑ z, (μ.pi ↥I).prob z * (k7rInd μ {i₁} (τ / 2) f I z).re =
      ∑ w : ↥I → A i₁, ∑ z, (if (fun t => z t i₁) = w then (μ.pi ↥I).prob z else 0) *
        (k7rInd μ {i₁} (τ / 2) f I z).re := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  rw [hRHS]
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases hb : ∃ P : ↥Iᶜ → A i₁ → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      τ ≤ ‖((μ.marginalPi i₁).pi ↥Iᶜ).cexpect fun x =>
        restrictFix I w (fun x => star (replaceCondProdExp μ f i₁ x)) x * ∏ i, P i (x i)‖
  · obtain ⟨P, hP, hn⟩ := hb
    rw [ite_eq_left ⟨P, hP, hn⟩, Complex.one_re, mul_one]
    exact k7r_avg_fiber μ i₁ hτ0 f hf I w P hP hn
  · rw [ite_eq_right hb, Complex.zero_re, mul_zero, mul_zero]
    refine Finset.sum_nonneg fun z _ => mul_nonneg ?_ (k7r_ind_re_nonneg _ _ _ _ _ _)
    split_ifs
    · exact (μ.pi ↥I).nonneg z
    · exact le_rfl

/-- CSP_7 `lemma:replace`, step `averaging` (the probability is `τ²/2`, not `τ/2`; the display drops
`|·|` and conjugates `P`): from the `lemma:kcsp` event of `conj f̃_{i₁}` (probability `τ` over `I`, `z ∼ μ_{i₁}^I`),
average over the other coordinates of `z` (conditionally on `z_{i₁}`, Markov): with probability `≥ τ²/2` over
`I ∼_{1-τ}`, `z ∼ μ^I` there is a `1`-bounded product `P_{i₁}` with correlation `≥ τ/2`. -/
theorem k7_replace_averaging (μ : FinProb (∀ i, A i)) (i₁ : Fin (k + 1)) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (h : τ ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) τ τ hτ0.le hτ1
      (fun x => star (replaceCondProdExp μ f i₁ x))) :
    τ * τ / 2 ≤ k7ReplEventProb μ {i₁} τ (τ / 2) hτ0.le hτ1 f := by
  rw [k7r_replEventProb_eq]
  unfold k7EventProb at h
  unfold subsetExpect at h ⊢
  have key := k7r_re_cexpect_scaled ((bernoulli (1 - τ) (by linarith) (by linarith)).pi ι) (τ / 2)
    _ _ fun s => k7r_avg_I μ i₁ hτ0.le f hf (trueSet s)
  calc τ * τ / 2 = τ / 2 * τ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ _ := key

/-- CSP_7 `lemma:replace`. -/
theorem k7_lemma_replace (μ : FinProb (∀ i, A i)) (i₁ : Fin (k + 1)) {ε τ : ℝ} (hε0 : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hlk : ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
      (∀ i x, ‖F i x‖ ≤ 1) → ε ^ 2 ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      τ ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) τ τ hτ0.le hτ1 (F i₁))
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hε : ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖) :
    τ * τ / 2 ≤ k7ReplEventProb μ {i₁} τ (τ / 2) hτ0.le hτ1 f :=
  k7_replace_averaging μ i₁ hτ0 hτ1 f hf
    (k7_replace_apply_lemma_kcsp μ i₁ hε0 hτ0.le hτ1 hlk f hf hε)

/-! ### `cor:replace`: one closure step (private, with `0 ≤ p'`) and the `k` rounds -/

/-- the core of the closure step: a good second restriction `(I', z')` of the tuple
`F = (Pᵢ for i ∈ T, (fᵢ)_{I→z} otherwise)` (on `Iᶜ`) gives a good composite restriction for `insert i₁ T`
(the constant factors `∏_{t ∈ I'} Pᵢ(z'_t)` of the fixed product coordinates have modulus `≤ 1`). -/
private theorem k7r_iterate_core (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1)))
    (i₁ : Fin (k + 1)) (hi : i₁ ∉ T) {τ : ℝ} (f : ∀ i, (ι → A i) → ℂ) (I : Finset ι)
    (z : ↥I → ∀ i, A i) (P : ∀ i, ↥Iᶜ → A i → ℂ) (hP : ∀ i ∈ T, ∀ t a, ‖P i t a‖ ≤ 1)
    (I' : Finset ↥Iᶜ) (z' : ↥I' → ∀ i, A i)
    (hg : k7rGood μ {i₁} (τ / 2) (fun i X => if i ∈ T then ∏ t, P i t (X t)
      else restrictFix I (fun t => z t i) (f i) X) I' z') :
    k7rGood μ (insert i₁ T) (τ / 2) f (composeSet I I') (composeVals I I' z z') := by
  obtain ⟨P', hP', hn⟩ := hg
  set e := composeEquiv I I' with he
  let Pn : ∀ i, ↥(composeSet I I')ᶜ → A i → ℂ := fun i j a =>
    if i = i₁ then P' i (e j) a else P i (e j).1 a
  refine ⟨Pn, ?_, ?_⟩
  · intro i hi' j a
    rcases Finset.mem_insert.1 hi' with rfl | hiT
    · simp only [Pn, ite_true]
      exact hP' i (Finset.mem_singleton_self i) _ _
    · have hne : i ≠ i₁ := fun h => hi (h ▸ hiT)
      simp only [Pn, ite_eq_right hne]
      exact hP i hiT _ _
  · let C : Fin (k + 1) → ℂ := fun i => if i ∈ T then ∏ t : ↥I', P i t.1 (z' t i) else 1
    have hC : ‖∏ i, C i‖ ≤ 1 := by
      rw [norm_prod]
      refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
      show ‖if i ∈ T then ∏ t : ↥I', P i t.1 (z' t i) else 1‖ ≤ 1
      split_ifs with hiT
      · rw [norm_prod]
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun t _ => hP i hiT _ _
      · simp
    have hEq : ((μ.pi ↥I'ᶜ).cexpect fun X => ∏ i,
        (if i ∈ ({i₁} : Finset (Fin (k + 1))) then ∏ t, P' i t (X t i)
          else restrictFix I' (fun t => z' t i)
            (fun X => if i ∈ T then ∏ t, P i t (X t)
              else restrictFix I (fun t => z t i) (f i) X) (fun t => X t i))) =
        (∏ i, C i) * ((μ.pi ↥(composeSet I I')ᶜ).cexpect fun X => ∏ i,
          (if i ∈ insert i₁ T then ∏ t, Pn i t (X t i)
            else restrictFix (composeSet I I') (fun t => composeVals I I' z z' t i) (f i)
              (fun t => X t i))) := by
      rw [cexpect_pi_composeEquiv μ I I', ← k7r_cexpect_const_mul]
      congr 1
      funext y
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h1 : i = i₁
      · subst h1
        rw [ite_eq_left (Finset.mem_singleton_self i), ite_eq_left (Finset.mem_insert_self i T)]
        have hC1 : C i = 1 := ite_eq_right hi
        rw [hC1, one_mul]
        refine (Fintype.prod_equiv e (fun j => Pn i j (y j i))
          (fun t => P' i t (y (e.symm t) i)) fun j => ?_).symm
        simp only [Pn, ite_true, Equiv.symm_apply_apply]
      · have hns : i ∉ ({i₁} : Finset (Fin (k + 1))) := by simpa using h1
        rw [ite_eq_right hns]
        by_cases hiT : i ∈ T
        · rw [ite_eq_left (Finset.mem_insert_of_mem hiT)]
          have hCi : C i = ∏ t : ↥I', P i t.1 (z' t i) := ite_eq_left hiT
          rw [hCi]
          unfold restrictFix
          simp only [ite_eq_left hiT]
          rw [k7r_prod_glue_split I' (fun t a => P i t a)]
          congr 1
          refine (Fintype.prod_equiv e (fun j => Pn i j (y j i))
            (fun t => P i t.1 (y (e.symm t) i)) fun j => ?_).symm
          simp only [Pn, ite_eq_right h1, Equiv.symm_apply_apply]
        · have hni : i ∉ insert i₁ T := by
            rw [Finset.mem_insert]
            exact fun h => h.elim h1 hiT
          rw [ite_eq_right hni]
          have hCi : C i = 1 := ite_eq_right hiT
          rw [hCi, one_mul]
          simp only [ite_eq_right hiT]
          rw [restrictFix_compose I I' (fun t => z t i) (fun t => z' t i) (f i),
            k7r_composeVals_comp]
          congr 1
    rw [hEq, norm_mul] at hn
    have hn0 : 0 ≤ ‖(μ.pi ↥(composeSet I I')ᶜ).cexpect fun X => ∏ i,
          (if i ∈ insert i₁ T then ∏ t, Pn i t (X t i)
            else restrictFix (composeSet I I') (fun t => composeVals I I' z z' t i) (f i)
              (fun t => X t i))‖ := norm_nonneg _
    calc τ / 2 ≤ ‖∏ i, C i‖ * _ := hn
      _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hC hn0
      _ = _ := one_mul _

/-- the pointwise step of the closure: a good `(I, z)` for the state `T` gives, through the round
hypothesis on `Iᶜ` and `k7r_iterate_core`, probability `≥ p'` of a good composite restriction. -/
private theorem k7r_iterate_pointwise (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1)))
    (i₁ : Fin (k + 1)) (hi : i₁ ∉ T) {η τ p' : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hround : ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
      (∀ i x, ‖F i x‖ ≤ 1) → η ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      p' ≤ k7ReplEventProb μ {i₁} τ (τ / 2) hτ0.le hτ1 F)
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) (I : Finset ι) (z : ↥I → ∀ i, A i)
    (hg : k7rGood μ T η f I z) :
    p' ≤ (subsetExpect (ι := ↥Iᶜ) (1 - τ) (by linarith) (by linarith) fun I' =>
      (μ.pi ↥I').cexpect fun w' =>
        k7rInd μ (insert i₁ T) (τ / 2) f (composeSet I I') (composeVals I I' z w')).re := by
  obtain ⟨P, hP, hn⟩ := hg
  let F : ∀ i, (↥Iᶜ → A i) → ℂ := fun i X =>
    if i ∈ T then ∏ t, P i t (X t) else restrictFix I (fun t => z t i) (f i) X
  have hF1 : ∀ i x, ‖F i x‖ ≤ 1 := by
    intro i x
    show ‖if i ∈ T then ∏ t, P i t (x t) else restrictFix I (fun t => z t i) (f i) x‖ ≤ 1
    split_ifs with hiT
    · rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun t _ => hP i hiT _ _
    · exact hf i _
  have hr := hround ↥Iᶜ F hF1 hn
  rw [k7r_replEventProb_eq] at hr
  refine hr.trans ?_
  unfold subsetExpect
  have hm := k7r_re_cexpect_scaled ((bernoulli (1 - τ) (by linarith) (by linarith)).pi ↥Iᶜ) 1
    (fun s' => (μ.pi ↥(trueSet s')).cexpect fun z' => k7rInd μ {i₁} (τ / 2) F (trueSet s') z')
    (fun s' => (μ.pi ↥(trueSet s')).cexpect fun w' =>
      k7rInd μ (insert i₁ T) (τ / 2) f (composeSet I (trueSet s'))
        (composeVals I (trueSet s') z w'))
    (fun s' => k7r_re_cexpect_scaled _ 1 _ _ fun z' => by
      rw [one_mul]
      by_cases hg' : k7rGood μ {i₁} (τ / 2) F (trueSet s') z'
      · rw [k7r_ind_re_of _ _ _ _ _ _ hg', k7r_ind_re_of _ _ _ _ _ _
          (k7r_iterate_core μ T i₁ hi f I z P hP (trueSet s') z' hg')]
      · rw [k7r_ind_re_of_not _ _ _ _ _ _ hg']
        exact k7r_ind_re_nonneg _ _ _ _ _ _)
  rw [one_mul] at hm
  exact hm

/-- CSP_7 `cor:replace`, step `iterate-replace`, one closure step. The premise `0 ≤ p'` is TYPING (`p'` is a
probability bound; without it the statement is false). -/
theorem k7_cor_replace_iterate (μ : FinProb (∀ i, A i)) (T : Finset (Fin (k + 1)))
    (i₁ : Fin (k + 1)) (hi : i₁ ∉ T) {ρ η q τ p' : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) (hp' : 0 ≤ p')
    (hround : ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
      (∀ i x, ‖F i x‖ ≤ 1) → η ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      p' ≤ k7ReplEventProb μ {i₁} τ (τ / 2) hτ0.le hτ1 F)
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hE : q ≤ k7ReplEventProb μ T ρ η hρ0.le hρ1 f) :
    q * p' ≤ k7ReplEventProb μ (insert i₁ T) (ρ * τ) (τ / 2) (mul_pos hρ0 hτ0).le
      (by nlinarith [mul_pos hρ0 hτ0]) f := by
  have hbar : ∀ a, (1 - ρ * τ) * μ.prob a = (1 - ρ) * μ.prob a + ρ * (1 - τ) * μ.prob a :=
    fun a => by ring
  have hnest := nested_restriction_law (ι := ι) hρ0.le hρ1 hτ0.le hτ1 μ μ μ hbar
    (fun J v => k7rInd μ (insert i₁ T) (τ / 2) f J v)
  rw [k7r_replEventProb_eq] at hE ⊢
  have key := k7r_re_nested_scaled (κ := ι) (by linarith : 0 ≤ 1 - ρ) (by linarith) μ p'
    (fun I z => k7rInd μ T η f I z)
    (fun I w => subsetExpect (ι := ↥Iᶜ) (1 - τ) (by linarith) (by linarith) fun I' =>
      (μ.pi ↥I').cexpect fun w' =>
        k7rInd μ (insert i₁ T) (τ / 2) f (composeSet I I') (composeVals I I' w w'))
    (fun I z => by
      by_cases hg : k7rGood μ T η f I z
      · rw [k7r_ind_re_of μ T η f I z hg, mul_one]
        exact k7r_iterate_pointwise μ T i₁ hi hτ0 hτ1 hround f hf I z hg
      · rw [k7r_ind_re_of_not μ T η f I z hg, mul_zero]
        unfold subsetExpect
        exact k7r_re_cexpect_ge _ _ _ fun s' => k7r_re_cexpect_ge _ _ _ fun w' =>
          k7r_ind_re_nonneg _ _ _ _ _ _)
  rw [hnest] at key
  calc q * p' = p' * q := by ring
    _ ≤ p' * _ := mul_le_mul_of_nonneg_left hE hp'
    _ ≤ _ := key

/-- CSP_7 `cor:replace` (`k` rounds, one per coordinate `≠ i₀`; the three roles of `δ` are kept apart as
`(R, p, η')`: the free rate, the probability and the correlation of the
printed single `δ`; the expectation is over `μ^{⊗Ī}`). `τfun η` is the `τ` of
`lemma:kcsp` for the correlation parameter `η²` (`hlk`, for every coordinate). The rounds use
`η₀ = ε`, `η_{r+1} = τfun(η_r)/2`. -/
theorem k7_cor_replace_of_kcsp (μ : FinProb (∀ i, A i)) (i₀ : Fin (k + 1)) (τfun : ℝ → ℝ)
    (hτ : ∀ η : ℝ, 0 < η → η ≤ 1 → 0 < τfun η ∧ τfun η ≤ 1)
    (hlk : ∀ (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1) (i₁ : Fin (k + 1)) (ι' : Type) [Fintype ι']
      [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ), (∀ i x, ‖F i x‖ ≤ 1) →
      η ^ 2 ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      τfun η ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) (τfun η) (τfun η)
        (hτ η h0 h1).1.le (hτ η h0 h1).2 (F i₁))
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hε : ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖) :
    ∃ (R p η' : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1),
      R = ∏ r ∈ Finset.range k, τfun ((fun x => τfun x / 2)^[r] ε) ∧
      p = ∏ r ∈ Finset.range k, (τfun ((fun x => τfun x / 2)^[r] ε) ^ 2 / 2) ∧
      η' = (fun x => τfun x / 2)^[k] ε ∧
      p ≤ k7ReplEventProb μ (Finset.univ.erase i₀) R η' hR0 hR1 f := by
  set g : ℝ → ℝ := fun x => τfun x / 2 with hgdef
  have hηpos : ∀ r : ℕ, 0 < g^[r] ε ∧ g^[r] ε ≤ 1 := by
    intro r
    induction r with
    | zero => exact ⟨hε0, hε1⟩
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      have := hτ _ ih.1 ih.2
      exact ⟨by simp only [hgdef]; linarith [this.1], by simp only [hgdef]; linarith [this.2]⟩
  have hτpos : ∀ r : ℕ, 0 < τfun (g^[r] ε) ∧ τfun (g^[r] ε) ≤ 1 :=
    fun r => hτ _ (hηpos r).1 (hηpos r).2
  have hR0 : ∀ m : ℕ, 0 ≤ ∏ r ∈ Finset.range m, τfun (g^[r] ε) :=
    fun m => Finset.prod_nonneg fun r _ => (hτpos r).1.le
  have hRpos : ∀ m : ℕ, 0 < ∏ r ∈ Finset.range m, τfun (g^[r] ε) :=
    fun m => Finset.prod_pos fun r _ => (hτpos r).1
  have hR1 : ∀ m : ℕ, ∏ r ∈ Finset.range m, τfun (g^[r] ε) ≤ 1 :=
    fun m => Finset.prod_le_one₀ (fun r _ => (hτpos r).1.le) fun r _ => (hτpos r).2
  have hstate : ∀ m : ℕ, m ≤ k → ∃ T : Finset (Fin (k + 1)), T ⊆ univ.erase i₀ ∧ T.card = m ∧
      ∏ r ∈ Finset.range m, (τfun (g^[r] ε) ^ 2 / 2) ≤
        k7ReplEventProb μ T (∏ r ∈ Finset.range m, τfun (g^[r] ε)) (g^[m] ε) (hR0 m) (hR1 m) f := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨∅, Finset.empty_subset _, Finset.card_empty, ?_⟩
      calc ∏ r ∈ Finset.range 0, (τfun (g^[r] ε) ^ 2 / 2) = 1 := Finset.prod_range_zero _
        _ ≤ k7ReplEventProb μ ∅ 1 ε zero_le_one le_rfl f := k7_replEventProb_base μ f hε
        _ = _ := k7r_replEventProb_congr μ ∅ _ _ _ _ f (by simp) (by simp)
    | succ m ih =>
      intro hm
      obtain ⟨T, hTsub, hTcard, hT⟩ := ih (by omega)
      obtain ⟨i₁, hi₁, hi₁T⟩ : ∃ i₁ ∈ univ.erase i₀, i₁ ∉ T := by
        by_contra hne
        push Not at hne
        have hsub : univ.erase i₀ ⊆ T := hne
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
          hTcard] at this
        omega
      have hround : ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
          (∀ i x, ‖F i x‖ ≤ 1) → g^[m] ε ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
          τfun (g^[m] ε) ^ 2 / 2 ≤ k7ReplEventProb μ {i₁} (τfun (g^[m] ε)) (τfun (g^[m] ε) / 2)
            (hτpos m).1.le (hτpos m).2 F := by
        intro ι' _ _ F hF hc
        have := k7_lemma_replace μ i₁ (hηpos m).1 (hτpos m).1 (hτpos m).2
          (fun ι'' _ _ F' hF' hc' => hlk (g^[m] ε) (hηpos m).1 (hηpos m).2 i₁ ι'' F' hF' hc')
          F hF hc
        calc τfun (g^[m] ε) ^ 2 / 2 = τfun (g^[m] ε) * τfun (g^[m] ε) / 2 := by ring
          _ ≤ _ := this
      have hit := k7_cor_replace_iterate μ T i₁ hi₁T (hRpos m) (hR1 m) (hτpos m).1 (hτpos m).2
        (by positivity) hround f hf hT
      refine ⟨insert i₁ T, Finset.insert_subset hi₁ hTsub, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi₁T, hTcard]
      · rw [Finset.prod_range_succ]
        refine hit.trans (le_of_eq (k7r_replEventProb_congr μ _ _ _ _ _ f ?_ ?_))
        · rw [Finset.prod_range_succ]
        · rw [Function.iterate_succ_apply']
  obtain ⟨T, hTsub, hTcard, hT⟩ := hstate k le_rfl
  have hTeq : T = univ.erase i₀ := by
    refine Finset.eq_of_subset_of_card_le hTsub ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, hTcard]
    omega
  subst hTeq
  exact ⟨_, _, _, hR0 k, hR1 k, rfl, rfl, rfl, hT⟩

/-! ### From the `cor:replace` event to stability -/

/-- one good restriction gives stability `≥ η²/4` (`lemma:fstab` on `Ī`); off the event `cstab ≥ 0`. -/
private theorem k7r_fstab_pointwise (μ : FinProb (∀ i, A i)) (i₀ : Fin (k + 1))
    (f : ∀ i, (ι → A i) → ℂ) {η γ : ℝ} (hγ : 0 ≤ 1 - γ) (I : Finset ι) (z : ↥I → ∀ i, A i)
    (hfs : ∀ Q : ∀ i, ↥Iᶜ → A i → ℂ, (∀ i j a, ‖Q i j a‖ ≤ 1) →
      η ≤ ‖(μ.pi ↥Iᶜ).cexpect fun X => restrictFix I (fun t => z t i₀) (f i₀) (fun t => X t i₀) *
        ∏ i ∈ univ.erase i₀, ∏ j, Q i j (X j i)‖ →
      η ^ 2 / 4 ≤ (cstab (μ.marginalPi i₀) (1 - γ) (restrictFix I (fun t => z t i₀) (f i₀))).re) :
    η ^ 2 / 4 * (k7rInd μ (univ.erase i₀) η f I z).re ≤
      (cstab (μ.marginalPi i₀) (1 - γ) (restrictFix I (fun t => z t i₀) (f i₀))).re := by
  have hnn : 0 ≤ (cstab (μ.marginalPi i₀) (1 - γ) (restrictFix I (fun t => z t i₀) (f i₀))).re := by
    have := cstab_nonneg (μ.marginalPi i₀) hγ (restrictFix I (fun t => z t i₀) (f i₀))
    have h2 := (Complex.le_def.1 this).1
    simpa using h2
  by_cases hg : k7rGood μ (univ.erase i₀) η f I z
  · rw [k7r_ind_re_of _ _ _ _ _ _ hg, mul_one]
    obtain ⟨P, hP, hn⟩ := hg
    let Q : ∀ i, ↥Iᶜ → A i → ℂ := fun i t a => if i = i₀ then 0 else P i t a
    refine hfs Q (fun i t a => ?_) (hn.trans (le_of_eq ?_))
    · show ‖if i = i₀ then (0 : ℂ) else P i t a‖ ≤ 1
      split_ifs with h
      · simp
      · exact hP i (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) t a
    · congr 2
      funext X
      rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i₀),
        ite_eq_right (by simp : i₀ ∉ univ.erase i₀)]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [ite_eq_left hi]
      refine Finset.prod_congr rfl fun t _ => ?_
      show _ = if i = i₀ then (0 : ℂ) else P i t (X t i)
      rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
  · rw [k7r_ind_re_of_not _ _ _ _ _ _ hg, mul_zero]
    exact hnn

/-- one fixed set `I`: average of `k7r_fstab_pointwise` (the law of `z_{i₀}` is the marginal). -/
private theorem k7r_fstab_I (μ : FinProb (∀ i, A i)) (i₀ : Fin (k + 1)) (f : ∀ i, (ι → A i) → ℂ)
    {η γ : ℝ} (hγ : 0 ≤ 1 - γ) (I : Finset ι)
    (hfs : ∀ z : ↥I → ∀ i, A i, ∀ Q : ∀ i, ↥Iᶜ → A i → ℂ, (∀ i j a, ‖Q i j a‖ ≤ 1) →
      η ≤ ‖(μ.pi ↥Iᶜ).cexpect fun X => restrictFix I (fun t => z t i₀) (f i₀) (fun t => X t i₀) *
        ∏ i ∈ univ.erase i₀, ∏ j, Q i j (X j i)‖ →
      η ^ 2 / 4 ≤ (cstab (μ.marginalPi i₀) (1 - γ) (restrictFix I (fun t => z t i₀) (f i₀))).re) :
    η ^ 2 / 4 * ((μ.pi ↥I).cexpect fun z => k7rInd μ (univ.erase i₀) η f I z).re ≤
      (((μ.marginalPi i₀).pi ↥I).cexpect fun w =>
        cstab (μ.marginalPi i₀) (1 - γ) (restrictFix I w (f i₀))).re := by
  rw [← k7r_cexpect_marginal μ i₀
    (fun w => cstab (μ.marginalPi i₀) (1 - γ) (restrictFix I w (f i₀)))]
  exact k7r_re_cexpect_scaled _ _ _ _ fun z => k7r_fstab_pointwise μ i₀ f hγ I z (hfs z)

/-- CSP_7 `thm:kcsp`, step `apply-cor-replace-and-fstab` (the passage from the `cor:replace` event to stability:
`lemma:fstab` on `Ī` for every good `(I, z)`, and the identity `stab_eq_expect_restriction`,
`Stab_{1-γR}(f) = 𝔼_{I ∼_{1-R}, z ∼ μ_{i₀}^I} Stab_{1-γ}(f_{I→z})`, with `cstab ≥ 0` off the event; `c` is the
constant of `lemma:fstab`, `c = c(k, α)`). -/
theorem k7_kcsp_apply_cor_replace_and_fstab (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Fin (k + 1) → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ (i₀ : Fin (k + 1)) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ),
        (∀ i x, ‖f i x‖ ≤ 1) → ∀ (R p η : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1), 0 < η → η < 1 →
        p ≤ k7ReplEventProb μ (Finset.univ.erase i₀) R η hR0.le hR1 f →
        ∀ (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1), γ ≤ c * η ^ 2 / Real.log (1 / η) →
          p * (η ^ 2 / 4) ≤ (cstab (μ.marginalPi i₀) (1 - γ * R) (f i₀)).re := by
  obtain ⟨c, hc, hfs⟩ := k7_lemma_fstab (k + 1) hα
  refine ⟨c, hc, ?_⟩
  intro A _ _ μ hno hatom i₀ ι _ _ f hf R p η hR0 hR1 hη0 hη1 hp γ hγ0 hγ1 hγc
  rw [stab_eq_expect_restriction (μ.marginalPi i₀) hγ0.le hγ1.le hR0.le hR1 (f i₀)]
  rw [k7r_replEventProb_eq] at hp
  unfold subsetExpect at hp ⊢
  have key := k7r_re_cexpect_scaled ((bernoulli (1 - R) (by linarith) (by linarith)).pi ι)
    (η ^ 2 / 4)
    (fun s => (μ.pi ↥(trueSet s)).cexpect fun z => k7rInd μ (univ.erase i₀) η f (trueSet s) z)
    (fun s => ((μ.marginalPi i₀).pi ↥(trueSet s)).cexpect fun w =>
      cstab (μ.marginalPi i₀) (1 - γ) (restrictFix (trueSet s) w (f i₀)))
    fun s => k7r_fstab_I μ i₀ f (by linarith) (trueSet s) fun z Q hQ hcorr =>
      hfs A μ hno hatom i₀ ↥(trueSet s)ᶜ (restrictFix (trueSet s) (fun t => z t i₀) (f i₀))
        (fun x => hf i₀ _) Q hQ η hη0 hη1 hcorr γ hγ0 hγ1 hγc
  calc p * (η ^ 2 / 4) = η ^ 2 / 4 * p := by ring
    _ ≤ η ^ 2 / 4 * _ := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := key

end Replace

end TrackB
end RestrictedPolynomials
end
