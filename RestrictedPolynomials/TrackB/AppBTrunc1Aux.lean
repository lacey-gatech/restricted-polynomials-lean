module

public import RestrictedPolynomials.TrackB.AppBSetting
public import RestrictedPolynomials.TrackB.NoiseClaims
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.MaxTClass
public import RestrictedPolynomials.TrackB.HomBridge

/-!
# Track B, Appendix B: noise, restriction, the bad event

Supplement I: the repair of paper IV App. B `soft_trunc1`,
term (I), at `H = {0}`. This part holds Lemmas `lem:noisy-law`, `lem:noise-split`, `lem:letters`,
`lem:restriction`, `lem:pushforward`, `lem:fprime`-adjacent sup-norm facts, `lem:bad-event` and
`cor:bad-xyz`. Part 2 (`AppBTrunc1`) holds the chain, the gap, the Loewner step, term (III) and
`appB_soft_trunc1`.

The random-restriction component is `μ'' := ν_{xz} ⊗ ν_y` (called `μbar`); all of `μ'`, `μbar`,
`μ3 = μ'''` have `x`-marginal `ν_x`, which charges every letter with mass `≥ α`. Nothing here
uses `Σ'`, `Φ'`, `K`, `P`-maximality or the relaxed base case.

Constants: the threshold of the bad event carries the BUILT constant `c` of
`rr_stab_trivial_master` (never `c = 1`) and the obtained `δ_F` of `appB_stab_fprime_le`.
All proof helpers are `private`.
-/

@[expose] public section

open Finset
open scoped ComplexOrder
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Noise
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]



private theorem t1_finProb_ext {A : Type} [Fintype A] {P Q : FinProb A}
    (h : ∀ a, P.prob a = Q.prob a) : P = Q := by
  cases P; cases Q
  congr
  exact funext h

omit [DecidableEq Y] [DecidableEq Z] in
private theorem t1_lawX_prob (ν : FinProb (X × Y × Z)) (x : X) :
    (lawX ν).prob x = ∑ y, ∑ z, ν.prob (x, y, z) := by
  show ∑ a ∈ univ.filter (fun a : X × Y × Z => a.1 = x), ν.prob a = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [Fintype.sum_prod_type]
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq X] [DecidableEq Z] in
private theorem t1_lawY_prob (ν : FinProb (X × Y × Z)) (y : Y) :
    (lawY ν).prob y = ∑ x, ∑ z, ν.prob (x, y, z) := by
  show ∑ a ∈ univ.filter (fun a : X × Y × Z => a.2.1 = y), ν.prob a = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq X] [DecidableEq Y] in
private theorem t1_lawZ_prob (ν : FinProb (X × Y × Z)) (z : Z) :
    (lawZ ν).prob z = ∑ x, ∑ y, ν.prob (x, y, z) := by
  show ∑ a ∈ univ.filter (fun a : X × Y × Z => a.2.2 = z), ν.prob a = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem t1_sum_triple (ν : FinProb (X × Y × Z)) :
    ∑ x, ∑ y, ∑ z, ν.prob (x, y, z) = 1 := by
  have := ν.sum_eq_one
  simpa only [Fintype.sum_prod_type] using this

private theorem t1_neK_formula {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (ξ : ℝ)
    (a b : A) : nonEmbedKernel D (fun _ : A => ()) ξ a b =
      (1 - ξ) * (if a = b then 1 else 0) + ξ * D.prob b := by
  unfold nonEmbedKernel graphNoiseKernel
  have h2 : ∑ c : A, D.prob c = 1 := D.sum_eq_one
  beta_reduce
  simp [h2]

private theorem t1_mubar_marginals_aux (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) :
    lawX μbar = lawX ν ∧ lawY μbar = lawY ν ∧ lawZ μbar = lawZ ν := by
  have hY1 : ∑ y, (lawY ν).prob y = 1 := (lawY ν).sum_eq_one
  refine ⟨t1_finProb_ext fun x => ?_, t1_finProb_ext fun y => ?_, t1_finProb_ext fun z => ?_⟩
  · rw [t1_lawX_prob, t1_lawX_prob]
    simp only [hμ]
    have : ∀ y : Y, ∑ z : Z, (∑ y' : Y, ν.prob (x, y', z)) * (lawY ν).prob y =
        (∑ z : Z, ∑ y' : Y, ν.prob (x, y', z)) * (lawY ν).prob y := fun y => by
      rw [Finset.sum_mul]
    simp only [this]
    rw [← Finset.mul_sum, hY1, mul_one, Finset.sum_comm]
  · rw [t1_lawY_prob, t1_lawY_prob]
    simp only [hμ]
    have : ∀ x : X, ∑ z : Z, (∑ y' : Y, ν.prob (x, y', z)) * (lawY ν).prob y =
        (∑ z : Z, ∑ y' : Y, ν.prob (x, y', z)) * (lawY ν).prob y := fun x => by
      rw [Finset.sum_mul]
    simp only [this]
    rw [← Finset.sum_mul]
    have h1 : ∑ x : X, ∑ z : Z, ∑ y' : Y, ν.prob (x, y', z) = 1 := by
      rw [← t1_sum_triple ν]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
    rw [h1, one_mul, t1_lawY_prob]
  · rw [t1_lawZ_prob, t1_lawZ_prob]
    simp only [hμ]
    have : ∀ x : X, ∑ y : Y, (∑ y' : Y, ν.prob (x, y', z)) * (lawY ν).prob y =
        (∑ y' : Y, ν.prob (x, y', z)) := fun x => by
      rw [← Finset.mul_sum, hY1, mul_one]
    simp only [this]

/-- `lem:noisy-law` + `lem:noise-split` (Supplement I, §3), at `H = {0}`, for every law `ν` and every
rate `r ∈ (0, 1]`: the noisy law `μ'` of l. 8987 equals `(1 - r) ν + r μbar` with
`μbar = ν_{xz} ⊗ ν_y`, and splits as `μ' = (r/2) μbar + (1 - r/2) μ3` with `μ3` a law. All three
have `x`-marginal `ν_x`. No `Rel67`. -/
theorem appB_t1_noise_split (ν : FinProb (X × Y × Z)) {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    ∃ μ' μbar μ3 : FinProb (X × Y × Z),
      (∀ p, μ'.prob p = ∑ y', ν.prob (p.1, y', p.2.2) *
        nonEmbedKernel (lawY ν) (fun _ : Y => ()) r y' p.2.1) ∧
      (∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) ∧
      (∀ p, μ'.prob p = (1 - r) * ν.prob p + r * μbar.prob p) ∧
      (∀ p, μ'.prob p = (r / 2) * μbar.prob p + (1 - r / 2) * μ3.prob p) ∧
      lawX μ' = lawX ν ∧ lawX μbar = lawX ν ∧ lawX μ3 = lawX ν ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ), corr3 ν f (tNE (lawY ν) r g) h = corr3 μ' f g h := by
  obtain ⟨μ', hμ', hc⟩ := appB_noisyY_law_exists ν h0.le h1
  have hnn : ∀ p : X × Y × Z, 0 ≤ (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1 :=
    fun p => mul_nonneg (Finset.sum_nonneg fun y' _ => ν.nonneg _) ((lawY ν).nonneg _)
  let μbar : FinProb (X × Y × Z) :=
    ⟨fun p => (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1, hnn, by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type]
      have : ∀ x : X, ∑ y : Y, ∑ z : Z, (∑ y' : Y, ν.prob (x, y', z)) * (lawY ν).prob y =
          (∑ z : Z, ∑ y' : Y, ν.prob (x, y', z)) * ∑ y : Y, (lawY ν).prob y := fun x => by
        rw [Finset.sum_mul_sum, Finset.sum_comm]
      simp only [this, (lawY ν).sum_eq_one, mul_one]
      rw [← t1_sum_triple ν]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]⟩
  have hmb : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1 :=
    fun p => rfl
  have hmu : ∀ p, μ'.prob p = (1 - r) * ν.prob p + r * μbar.prob p := by
    rintro ⟨x, y, z⟩
    rw [hμ']
    simp only [t1_neK_formula, hmb, mul_add, Finset.sum_add_distrib]
    congr 1
    · have : ∀ y' : Y, ν.prob (x, y', z) * ((1 - r) * (if y' = y then (1 : ℝ) else 0)) =
          (1 - r) * (if y' = y then ν.prob (x, y', z) else 0) := fun y' => by
        split_ifs <;> ring
      simp only [this, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · have : ∀ y' : Y, ν.prob (x, y', z) * (r * (lawY ν).prob y) =
          r * (ν.prob (x, y', z) * (lawY ν).prob y) := fun y' => by ring
      simp only [this, ← Finset.mul_sum, ← Finset.sum_mul]
  have hr2 : 0 < 1 - r / 2 := by linarith
  have hnn3 : ∀ p : X × Y × Z, 0 ≤ ((1 - r) * ν.prob p + (r / 2) * μbar.prob p) / (1 - r / 2) :=
    fun p => div_nonneg (add_nonneg (mul_nonneg (by linarith) (ν.nonneg _))
      (mul_nonneg (by linarith) (μbar.nonneg _))) hr2.le
  let μ3 : FinProb (X × Y × Z) :=
    ⟨fun p => ((1 - r) * ν.prob p + (r / 2) * μbar.prob p) / (1 - r / 2), hnn3, by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ν.sum_eq_one, μbar.sum_eq_one, div_eq_one_iff_eq hr2.ne']
      ring⟩
  have hm3 : ∀ p, μ3.prob p = ((1 - r) * ν.prob p + (r / 2) * μbar.prob p) / (1 - r / 2) :=
    fun p => rfl
  have hsplit : ∀ p, μ'.prob p = (r / 2) * μbar.prob p + (1 - r / 2) * μ3.prob p := by
    intro p
    rw [hm3, hmu, mul_div_cancel₀ _ hr2.ne']
    ring
  obtain ⟨hmx, -, -⟩ := t1_mubar_marginals_aux ν μbar hmb
  have haff : ∀ (a b : ℝ) (ρ : FinProb (X × Y × Z)),
      (∀ p, ρ.prob p = a * ν.prob p + b * μbar.prob p) → a + b = 1 → lawX ρ = lawX ν := by
    intro a b ρ hρ hab
    refine t1_finProb_ext fun x => ?_
    rw [t1_lawX_prob]
    simp only [hρ]
    have e1 : ∑ y : Y, ∑ z : Z, (a * ν.prob (x, y, z) + b * μbar.prob (x, y, z)) =
        a * (lawX ν).prob x + b * (lawX μbar).prob x := by
      rw [t1_lawX_prob, t1_lawX_prob]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [e1, hmx, ← add_mul, hab, one_mul]
  refine ⟨μ', μbar, μ3, hμ', hmb, hmu, hsplit, ?_, hmx, ?_, hc⟩
  · exact haff (1 - r) r μ' hmu (by ring)
  · refine haff ((1 - r) / (1 - r / 2)) ((r / 2) / (1 - r / 2)) μ3 (fun p => ?_) ?_
    · rw [hm3]; ring
    · rw [← add_div, div_eq_one_iff_eq hr2.ne']; ring

/-- `lem:noise-split` (b): the marginals of `μbar` (given by its pointwise formula). -/
theorem appB_t1_mubar_marginals (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) :
    lawX μbar = lawX ν ∧ lawY μbar = lawY ν ∧ lawZ μbar = lawZ ν :=
  t1_mubar_marginals_aux ν μbar hμ

/-- `lem:letters` (Supplement I, §4; every letter occurs), derived from
`PairwiseConnected3`: the occurrence half is the built `hom_hocc_x_of_pc3`, `hom_hocc_y_of_pc3`,
`hom_hocc_z_of_pc3` of `HomBridge` (themselves `PairwiseConnected3.exists_atom_x/y/z`); with atoms
`≥ α` on the support, every marginal letter has mass `≥ α`. -/
theorem appB_inT_letters {ν : FinProb (X × Y × Z)} {al : ℝ}
    (hat : ∀ p ∈ ν.support, al ≤ ν.prob p) (hT : PairwiseConnected3 ν.support) :
    (∀ x, al ≤ (lawX ν).prob x) ∧ (∀ y, al ≤ (lawY ν).prob y) ∧
      (∀ z, al ≤ (lawZ ν).prob z) := by
  have hx : ∀ x : X, al ≤ (lawX ν).prob x := by
    intro x
    obtain ⟨y, z, hyz⟩ := hom_hocc_x_of_pc3 hT x
    have h1 : al ≤ ν.prob (x, y, z) := hat _ hyz
    rw [t1_lawX_prob]
    refine h1.trans ((Finset.single_le_sum (f := fun z => ν.prob (x, y, z))
      (fun z _ => ν.nonneg _) (Finset.mem_univ z)).trans
      (Finset.single_le_sum (f := fun y => ∑ z, ν.prob (x, y, z))
        (fun y _ => Finset.sum_nonneg fun z _ => ν.nonneg _) (Finset.mem_univ y)))
  have hy : ∀ y : Y, al ≤ (lawY ν).prob y := by
    intro y
    obtain ⟨x, z, hxz⟩ := hom_hocc_y_of_pc3 hT y
    have h1 : al ≤ ν.prob (x, y, z) := hat _ hxz
    rw [t1_lawY_prob]
    refine h1.trans ((Finset.single_le_sum (f := fun z => ν.prob (x, y, z))
      (fun z _ => ν.nonneg _) (Finset.mem_univ z)).trans
      (Finset.single_le_sum (f := fun x => ∑ z, ν.prob (x, y, z))
        (fun x _ => Finset.sum_nonneg fun z _ => ν.nonneg _) (Finset.mem_univ x)))
  have hz : ∀ z : Z, al ≤ (lawZ ν).prob z := by
    intro z
    obtain ⟨x, y, hxy⟩ := hom_hocc_z_of_pc3 hT z
    have h1 : al ≤ ν.prob (x, y, z) := hat _ hxy
    rw [t1_lawZ_prob]
    refine h1.trans ((Finset.single_le_sum (f := fun y => ν.prob (x, y, z))
      (fun y _ => ν.nonneg _) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (f := fun x => ∑ y, ν.prob (x, y, z))
        (fun x _ => Finset.sum_nonneg fun y _ => ν.nonneg _) (Finset.mem_univ x)))
  exact ⟨hx, hy, hz⟩

/-- `lem:letters` (c): the `(x, z)`-marginal charges its support with mass `≥ α`. -/
theorem appB_xz_atoms {ν : FinProb (X × Y × Z)} {al : ℝ}
    (hat : ∀ p ∈ ν.support, al ≤ ν.prob p) (x : X) (z : Z)
    (hpos : 0 < ∑ y, ν.prob (x, y, z)) : al ≤ ∑ y, ν.prob (x, y, z) := by
  by_contra hlt
  push Not at hlt
  have hle : ∀ y, ν.prob (x, y, z) ≤ 0 := by
    intro y
    by_contra hy
    push Not at hy
    have hs : (x, y, z) ∈ ν.support := ne_of_gt hy
    have h1 : al ≤ ν.prob (x, y, z) := hat _ hs
    exact absurd (h1.trans_lt (lt_of_le_of_lt
      (Finset.single_le_sum (f := fun y => ν.prob (x, y, z)) (fun y _ => ν.nonneg _)
        (Finset.mem_univ y)) hlt)) (lt_irrefl _)
  have : ∑ y, ν.prob (x, y, z) ≤ 0 := Finset.sum_nonpos fun y _ => hle y
  linarith

end Noise

section Restriction

/-- `lem:restriction`, product step (Supplement I, §5): the restriction of a product function
`f(t¹) g(t²) h(t³)` is the product of the restrictions, so its `μ`-expectation over the live
coordinates is the `corr3` of the restrictions (index type `↥I`). -/
theorem appB_restrictFree_prod {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinProb (X × Y × Z)) (I : Finset ι) (t : ↥Iᶜ → X × Y × Z) (f : (ι → X) → ℂ)
    (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    (μ.pi ↥I).cexpect (restrictFree I t
        (fun s => f (fun i => (s i).1) * g (fun i => (s i).2.1) * h (fun i => (s i).2.2))) =
      corr3 μ (restrictFree I (fun i => (t i).1) f) (restrictFree I (fun i => (t i).2.1) g)
        (restrictFree I (fun i => (t i).2.2) h) := by
  unfold corr3
  congr 1
  funext w
  have h1 : (fun i => (glueFree I w t i).1) = glueFree I (fun i => (w i).1) (fun i => (t i).1) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  have h2 : (fun i => (glueFree I w t i).2.1) =
      glueFree I (fun i => (w i).2.1) (fun i => (t i).2.1) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  have h3 : (fun i => (glueFree I w t i).2.2) =
      glueFree I (fun i => (w i).2.2) (fun i => (t i).2.2) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  simp only [restrictFree, h1, h2, h3]

/-- `lem:pushforward`, first step (Supplement I, §5): restricting `F ∘ π₁` and evaluating at the fixed
`(y₀, z₀)` is restricting `F` to the `x`-part of the fixed coordinates. -/
theorem appB_restrictFree_proj {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] {ι : Type} [Fintype ι] [DecidableEq ι] (I : Finset ι)
    (t : ↥Iᶜ → X × Y × Z) (y0 : Y) (z0 : Z) (F : (ι → X) → ℂ) :
    (fun w : ↥I → X =>
        restrictFree I t (fun s => F (fun i => (s i).1)) (fun i => (w i, y0, z0))) =
      restrictFree I (fun i => (t i).1) F := by
  funext w
  simp only [restrictFree]
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [glueFree, hi]

/-- `lem:restriction` (Supplement I, §5), noise as a restriction: for `0 < r ≤ 1` there are
`μbar = ν_{xz} ⊗ ν_y` (pointwise formula) and `μ3` with `x`-marginal `ν_x` such that
`corr3 ν f (T_{1-r} g) h` is the mixture-restriction expectation, with weight `β = r/2`, random
component `μ3` and live functional `E_{μbar^I}`, of the product function `f(t¹) g(t²) h(t³)`.
Via the built `mixture_restriction_expect` and `appB_t1_noise_split`. -/
theorem appB_t1_restriction {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) {r : ℝ} (h0 : 0 < r)
    (h1 : r ≤ 1) :
    ∃ μbar μ3 : FinProb (X × Y × Z),
      (∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) ∧
      lawX μbar = lawX ν ∧ lawX μ3 = lawX ν ∧
      ∀ (hb0 : 0 ≤ r / 2) (hb1 : r / 2 ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι]
        (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ),
        corr3 ν f (tNE (lawY ν) r g) h =
          mixtureRestrictionExpect (r / 2) hb0 hb1 μ3
            (fun s => f (fun i => (s i).1) * g (fun i => (s i).2.1) * h (fun i => (s i).2.2))
            (fun I G => (μbar.pi ↥I).cexpect G) := by
  obtain ⟨μ', μbar, μ3, -, hmb, hmu, hsplit, -, hx1, hx3, hc⟩ := appB_t1_noise_split ν h0 h1
  have hb1 : r / 2 < 1 := by linarith
  have hb0 : 0 < r / 2 := by linarith
  refine ⟨μbar, μ3, hmb, hx1, hx3, ?_⟩
  intro hb0' hb1' ι _ _ f g h
  rw [hc f g h]
  have := mixture_restriction_expect (ι := ι) hb0 hb1 μ' μbar μ3 hsplit
    (fun s => f (fun i => (s i).1) * g (fun i => (s i).2.1) * h (fun i => (s i).2.2))
  exact this.symm

end Restriction

section MRE

private theorem t1_re_cexpect {β : Type} [Fintype β] (π : FinProb β) (g : β → ℂ) :
    (π.cexpect g).re = ∑ a, π.prob a * (g a).re := by
  simp [FinProb.cexpect, Complex.re_sum]

private theorem t1_norm_cexpect_le {β : Type} [Fintype β] (π : FinProb β) (g : β → ℂ) :
    ‖π.cexpect g‖ ≤ ∑ a, π.prob a * ‖g a‖ := by
  unfold FinProb.cexpect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (π.nonneg a)]

private theorem t1_sum_affine {β : Type} [Fintype β] (p : β → ℝ) (hp : ∑ a, p a = 1)
    (u : β → ℝ) (A c : ℝ) : ∑ a, p a * (A * u a + c) = A * ∑ a, p a * u a + c := by
  have : ∀ a, p a * (A * u a + c) = A * (p a * u a) + c * p a := fun a => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hp, mul_one]

private theorem t1_push_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {ι : Type} [Fintype ι] [DecidableEq ι] (a : α → β) (w : ι → α → ℝ) (G : (ι → β) → ℂ) :
    ∑ x : ι → α, ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)) =
    ∑ b : ι → β, ((∏ i, ∑ c ∈ univ.filter (fun c => a c = b i), w i c : ℝ) : ℂ) * G b := by
  rw [← Finset.sum_fiberwise univ (fun x : ι → α => fun i => a (x i))
    (fun x => ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ x ∈ univ.filter (fun x : ι → α => (fun i => a (x i)) = b),
      ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)) = ((∏ i, w i (x i) : ℝ) : ℂ) * G b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Fintype.mem_piFinset, funext_iff]

private theorem t1_cexpect_pi_push {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (a : α → β)
    (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (t1_push_sum a (fun _ c => π.prob c) G).symm

/-- `mRE` is a convex combination, so the norm of the mixture-restriction expectation is at most
the real part of the same expectation of the norms (Supplement I, §1, linearity and monotonicity). -/
theorem appB_mre_norm_le {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    [DecidableEq ι] (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) (D₂ : FinProb α) (F : (ι → α) → ℂ)
    (Φ : ∀ I : Finset ι, ((↥I → α) → ℂ) → ℂ) :
    ‖mixtureRestrictionExpect β h0 h1 D₂ F Φ‖ ≤
      (mixtureRestrictionExpect β h0 h1 D₂ F (fun I G => ((‖Φ I G‖ : ℝ) : ℂ))).re := by
  unfold mixtureRestrictionExpect subsetExpect
  refine (t1_norm_cexpect_le _ _).trans ?_
  rw [t1_re_cexpect]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (FinProb.nonneg _ _)
  refine (t1_norm_cexpect_le _ _).trans ?_
  rw [t1_re_cexpect]
  exact le_of_eq (Finset.sum_congr rfl fun z _ => by simp)

/-- monotonicity of `mRE` (real parts), pointwise in the restriction `(I, z)`; the two
functions `F₁`, `F₂` may differ (the correlation and the bad event use different `F`). -/
theorem appB_mre_mono {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    [DecidableEq ι] (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) (D₂ : FinProb α) (F₁ F₂ : (ι → α) → ℂ)
    (Φ₁ Φ₂ : ∀ I : Finset ι, ((↥I → α) → ℂ) → ℂ)
    (h : ∀ (I : Finset ι) (z : ↥Iᶜ → α),
      (Φ₁ I (restrictFree I z F₁)).re ≤ (Φ₂ I (restrictFree I z F₂)).re) :
    (mixtureRestrictionExpect β h0 h1 D₂ F₁ Φ₁).re ≤
      (mixtureRestrictionExpect β h0 h1 D₂ F₂ Φ₂).re := by
  unfold mixtureRestrictionExpect subsetExpect
  rw [t1_re_cexpect, t1_re_cexpect]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (FinProb.nonneg _ _)
  rw [t1_re_cexpect, t1_re_cexpect]
  exact Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h _ z) (FinProb.nonneg _ _)

/-- affine behaviour of `mRE` (real parts): `E[a Φ + c] = a E[Φ] + c`. -/
theorem appB_mre_affine {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    [DecidableEq ι] (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) (D₂ : FinProb α) (F : (ι → α) → ℂ)
    (Φ : ∀ I : Finset ι, ((↥I → α) → ℂ) → ℂ) (a c : ℝ) :
    (mixtureRestrictionExpect β h0 h1 D₂ F
        (fun I G => (a : ℂ) * Φ I G + (c : ℂ))).re =
      a * (mixtureRestrictionExpect β h0 h1 D₂ F Φ).re + c := by
  unfold mixtureRestrictionExpect subsetExpect
  rw [t1_re_cexpect, t1_re_cexpect]
  have hin : ∀ s : ι → Bool, ((D₂.pi ↥(trueSet s)ᶜ).cexpect fun z =>
      (a : ℂ) * Φ (trueSet s) (restrictFree (trueSet s) z F) + (c : ℂ)).re =
      a * ((D₂.pi ↥(trueSet s)ᶜ).cexpect fun z => Φ (trueSet s) (restrictFree (trueSet s) z F)).re
        + c := by
    intro s
    rw [t1_re_cexpect, t1_re_cexpect]
    have := t1_sum_affine (fun z => (D₂.pi ↥(trueSet s)ᶜ).prob z) (FinProb.sum_eq_one _)
      (fun z => (Φ (trueSet s) (restrictFree (trueSet s) z F)).re) a c
    simpa using this
  simp only [hin]
  exact t1_sum_affine _ (FinProb.sum_eq_one _) _ a c

/-- `lem:pushforward` (Supplement I, §5): the `x`-marginal pushforward for the mixture
restriction. For `F̃(t) = F(t¹)` and a functional that reads only the `x`-part of the restricted
function (at the fixed `(y₀, z₀)`), `mRE` with random component `D₂` equals `mRE` with `lawX D₂`.
The probability of the bad event is the instance `Ψ = 1[a < Re Stab(·)]`. -/
theorem appB_mre_pushforward {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (D₂ : FinProb (X × Y × Z)) (y0 : Y) (z0 : Z) {b : ℝ}
    (h0 : 0 ≤ b) (h1 : b ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → X) → ℂ)
    (Ψ : ∀ I : Finset ι, ((↥I → X) → ℂ) → ℂ) :
    mixtureRestrictionExpect b h0 h1 D₂ (fun t => F (fun i => (t i).1))
        (fun I G => Ψ I (fun w => G (fun i => (w i, y0, z0)))) =
      mixtureRestrictionExpect b h0 h1 (lawX D₂) F Ψ := by
  unfold mixtureRestrictionExpect subsetExpect
  congr 1
  funext s
  have hproj := fun z : ↥(trueSet s)ᶜ → X × Y × Z =>
    appB_restrictFree_proj (trueSet s) z y0 z0 F
  simp only [hproj]
  exact (t1_cexpect_pi_push D₂ (fun p => p.1)
    (fun x => Ψ (trueSet s) (restrictFree (trueSet s) x F))).symm

end MRE

section SupNorm

private theorem t1_noiseKernel_nonneg {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a b : A) : 0 ≤ noiseKernel D ρ a b := by
  unfold noiseKernel
  have := D.nonneg b
  have h3 : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
  have h4 : 0 ≤ 1 - ρ := by linarith
  positivity

private theorem t1_noiseKernel_row {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    (ρ : ℝ) (a : A) : ∑ b, noiseKernel D ρ a b = 1 := by
  simp only [noiseKernel, Finset.sum_add_distrib, ← Finset.mul_sum, D.sum_eq_one]
  simp

private theorem t1_cexpect_expect_nonempty {β : Type} [Fintype β] (π : FinProb β) :
    Nonempty β := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := π.sum_eq_one
  simp at this

/-- `(St3)`: the Markov operator `T_{1-s}` does not increase the sup norm. -/
theorem appB_tNE_sup_le {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → A) → ℂ)
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) : ∀ x, ‖tNE D s f x‖ ≤ B := by
  intro x
  rw [tNE_eq_cnoiseOp]
  unfold cnoiseOp
  have hw0 : ∀ y : ι → A, 0 ≤ ∏ i, noiseKernel D (1 - s) (x i) (y i) :=
    fun y => Finset.prod_nonneg fun i _ => t1_noiseKernel_nonneg D (by linarith) (by linarith) _ _
  have hw1 : ∑ y : ι → A, ∏ i, noiseKernel D (1 - s) (x i) (y i) = 1 := by
    rw [← Fintype.prod_sum (fun i b => noiseKernel D (1 - s) (x i) b)]
    exact Finset.prod_eq_one fun i _ => t1_noiseKernel_row D _ _
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y : ι → A, ‖(((∏ i, noiseKernel D (1 - s) (x i) (y i) : ℝ) : ℂ)) * f y‖
      ≤ ∑ y : ι → A, (∏ i, noiseKernel D (1 - s) (x i) (y i)) * B := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 y)]
        exact mul_le_mul_of_nonneg_left (hf y) (hw0 y)
    _ = B := by rw [← Finset.sum_mul, hw1, one_mul]

/-- `cor:bad-xyz` (d): `f' = f - T_{1-s} f` is `2`-bounded, not `1`-bounded. -/
theorem appB_t1_fprime_sup {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → A) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : ∀ x, ‖(f - tNE D s f) x‖ ≤ 2 := by
  intro x
  have h1 := appB_tNE_sup_le D hs0 hs1 f hf x
  calc ‖(f - tNE D s f) x‖ = ‖f x - tNE D s f x‖ := rfl
    _ ≤ ‖f x‖ + ‖tNE D s f x‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (hf x) h1
    _ = 2 := by norm_num

/-- `‖f‖_{L²(D^ι)} ≤ ‖f‖_∞`: a sup-norm bound by `B ≥ 0` bounds the `L²` norm (used to feed
`cl2norm D f ≤ 1` to the built-style hypotheses from `‖f‖_∞ ≤ 1`). -/
theorem appB_cl2norm_le_sup {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {ι : Type}
    [Fintype ι] [DecidableEq ι] (f : (ι → A) → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) : cl2norm D f ≤ B := by
  obtain ⟨x0⟩ := t1_cexpect_expect_nonempty (D.pi ι)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf x0)
  unfold cl2norm
  rw [Real.sqrt_le_iff]
  refine ⟨hB, ?_⟩
  unfold cl2sq FinProb.expect
  calc ∑ x, (D.pi ι).prob x * ‖f x‖ ^ 2 ≤ ∑ x, (D.pi ι).prob x * B ^ 2 := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (FinProb.nonneg _ _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
    _ = B ^ 2 := by rw [← Finset.sum_mul, (D.pi ι).sum_eq_one, one_mul]

/-- the trivial bound `|corr3 μ f g h| ≤ A B C` for sup-norm bounds (`μ^ι` is a probability
measure). -/
theorem appB_corr3_norm_le {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) {A B C : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ A) (hg : ∀ y, ‖g y‖ ≤ B) (hh : ∀ z, ‖h z‖ ≤ C) :
    ‖corr3 μ f g h‖ ≤ A * B * C := by
  obtain ⟨⟨x0, y0, z0⟩⟩ := t1_cexpect_expect_nonempty μ
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf (fun _ => x0))
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg (fun _ => y0))
  unfold corr3
  refine (t1_norm_cexpect_le _ _).trans ?_
  calc ∑ t, (μ.pi ι).prob t * ‖f (fun i => (t i).1) * g (fun i => (t i).2.1) *
        h (fun i => (t i).2.2)‖ ≤ ∑ t, (μ.pi ι).prob t * (A * B * C) := by
        refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (FinProb.nonneg _ _)
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hf _) (hg _) (norm_nonneg _) hA) (hh _) (norm_nonneg _)
          (mul_nonneg hA hB)
    _ = A * B * C := by rw [← Finset.sum_mul, (μ.pi ι).sum_eq_one, one_mul]

end SupNorm

section BadEvent

/-- `lem:bad-event`, full-support form (Supplement I, §6): `c` is the constant of
the BUILT `rr_stab_trivial_master` (obtained, never `c = 1`), `δ_F` the one of the built
`appB_stab_fprime_le`, and
`d2 = min 1 (min ((c/4)^(4/ξ)) (min ((2/c)^(4/ξ)) δ_F))`. All three laws have atoms `≥ α` on every
letter of `S`. (a) is the `Stab_{1-δ'}` bound `≤ ρ^{ξ/4}`, (b) the Markov bound
`Pr[W > ρ^{ξ/8}] ≤ ρ^{ξ/8}`; both are stated on real parts. -/
theorem appB_t1_bad_event_full (m : ℕ) {al : ℝ} (hal : 0 < al) {xi : ℝ} (hxi : 0 < xi) :
    ∃ d2 : ℝ, 0 < d2 ∧ ∀ rho rho' : ℝ, 0 < rho → rho ≤ d2 → rho / 2 ≤ rho' → rho' ≤ rho →
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ D D' D'' : FinProb S, (∀ x, al ≤ D.prob x) → (∀ x, al ≤ D'.prob x) →
        (∀ x, al ≤ D''.prob x) →
        (∀ x, D.prob x = rho' / 2 * D'.prob x + (1 - rho' / 2) * D''.prob x) →
      ∀ (h0 : 0 ≤ rho' / 2) (h1 : rho' / 2 ≤ 1) (ι : Type) [Fintype ι] [DecidableEq ι]
        (f : (ι → S) → ℂ), cl2norm D f ≤ 1 →
        (mixtureRestrictionExpect (rho' / 2) h0 h1 D'' (f - tNE D (rho ^ (1 + xi)) f)
          (fun _ g => cstab D' (1 - rho ^ (xi / 4)) g)).re ≤ rho ^ (xi / 4) ∧
        (mixtureRestrictionExpect (rho' / 2) h0 h1 D'' (f - tNE D (rho ^ (1 + xi)) f)
          (fun _ g => if rho ^ (xi / 8) < (cstab D' (1 - rho ^ (xi / 4)) g).re then (1 : ℂ)
            else 0)).re ≤ rho ^ (xi / 8) := by
  obtain ⟨c, hc, hrr⟩ := rr_stab_trivial_master hal m
  obtain ⟨dF, hdF, hF⟩ := appB_stab_fprime_le hxi
  have hcx : (0 : ℝ) < c / 4 := by positivity
  have hcx2 : (0 : ℝ) < 2 / c := by positivity
  refine ⟨min 1 (min ((c / 4) ^ (4 / xi)) (min ((2 / c) ^ (4 / xi)) dF)), ?_, ?_⟩
  · exact lt_min one_pos (lt_min (Real.rpow_pos_of_pos hcx _)
      (lt_min (Real.rpow_pos_of_pos hcx2 _) hdF))
  intro rho rho' hρ0 hρd hρ1 hρ2 S _ _ hcard D D' D'' hD hD' hD'' hmix h0 h1 ι _ _ f hf
  have hρ1' : rho ≤ 1 := hρd.trans (min_le_left _ _)
  have hρc : rho ≤ (c / 4) ^ (4 / xi) :=
    hρd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρc2 : rho ≤ (2 / c) ^ (4 / xi) :=
    hρd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρF : rho ≤ dF :=
    hρd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hβ0 : 0 < rho' / 2 := by linarith
  have hδ0 : 0 < rho ^ (xi / 4) := Real.rpow_pos_of_pos hρ0 _
  have hδ1 : rho ^ (xi / 4) ≤ 1 := Real.rpow_le_one hρ0.le hρ1' (by positivity)
  have hxi4 : (4 / xi) * (xi / 4) = 1 := by field_simp
  have hδc : rho ^ (xi / 4) ≤ c / 4 := by
    calc rho ^ (xi / 4) ≤ ((c / 4) ^ (4 / xi)) ^ (xi / 4) :=
          Real.rpow_le_rpow hρ0.le hρc (by positivity)
      _ = c / 4 := by rw [← Real.rpow_mul hcx.le, hxi4, Real.rpow_one]
  have hδc2 : rho ^ (xi / 4) ≤ 2 / c := by
    calc rho ^ (xi / 4) ≤ ((2 / c) ^ (4 / xi)) ^ (xi / 4) :=
          Real.rpow_le_rpow hρ0.le hρc2 (by positivity)
      _ = 2 / c := by rw [← Real.rpow_mul hcx2.le, hxi4, Real.rpow_one]
  have hcδ : rho ^ (xi / 4) * c ≤ 2 := (le_div_iff₀ hc).1 hδc2
  have he : rho ^ (1 + xi / 2) = rho * rho ^ (xi / 4) * rho ^ (xi / 4) := by
    rw [Real.rpow_add hρ0, Real.rpow_one, mul_assoc, ← Real.rpow_add hρ0]
    congr 2
    ring
  have hlow : rho ^ (1 + xi / 2) ≤ c * (rho' / 2) * rho ^ (xi / 4) := by
    rw [he]
    have h1' : rho * rho ^ (xi / 4) * rho ^ (xi / 4) ≤ rho * rho ^ (xi / 4) * (c / 4) :=
      mul_le_mul_of_nonneg_left hδc (mul_nonneg hρ0.le hδ0.le)
    have h2' : rho * rho ^ (xi / 4) * (c / 4) ≤ c * (rho' / 2) * rho ^ (xi / 4) := by
      have : rho * rho ^ (xi / 4) * (c / 4) = c * (rho / 4) * rho ^ (xi / 4) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hc.le) hδ0.le
    exact h1'.trans h2'
  have hup : c * (rho' / 2) * rho ^ (xi / 4) ≤ 1 := by
    have : c * (rho' / 2) * rho ^ (xi / 4) = (rho' / 2) * (rho ^ (xi / 4) * c) := by ring
    rw [this]
    nlinarith [mul_pos hδ0 hc]
  have key := hrr (rho' / 2) hβ0 h1 S hcard D D' D'' hD hD' hD'' hmix (rho ^ (xi / 4)) hδ0 hδ1
    ι (f - tNE D (rho ^ (1 + xi)) f)
  have hmono := cstab_mono D (ι := ι) (ρ := 1 - c * (rho' / 2) * rho ^ (xi / 4))
    (ρ' := 1 - rho ^ (1 + xi / 2)) (by linarith) (by linarith) (f - tNE D (rho ^ (1 + xi)) f)
  have hfp := hF rho hρ0 hρF S D ι f hf
  have ha : (mixtureRestrictionExpect (rho' / 2) h0 h1 D'' (f - tNE D (rho ^ (1 + xi)) f)
      (fun _ g => cstab D' (1 - rho ^ (xi / 4)) g)).re ≤ rho ^ (xi / 4) :=
    ((Complex.le_def.1 (key.trans hmono)).1).trans hfp
  refine ⟨ha, ?_⟩
  set a := rho ^ (xi / 8) with ha_def
  have ha0 : 0 < a := Real.rpow_pos_of_pos hρ0 _
  have haa : rho ^ (xi / 4) = a * a := by
    rw [ha_def, ← Real.rpow_add hρ0]
    congr 1
    ring
  have hmono2 := appB_mre_mono (rho' / 2) h0 h1 D''
    (f - tNE D (rho ^ (1 + xi)) f) (f - tNE D (rho ^ (1 + xi)) f)
    (fun _ g => if a < (cstab D' (1 - rho ^ (xi / 4)) g).re then (1 : ℂ) else 0)
    (fun _ g => ((1 / a : ℝ) : ℂ) * cstab D' (1 - rho ^ (xi / 4)) g + ((0 : ℝ) : ℂ))
    (fun I z => by
      have hnn := cstab_nonneg D' (ι := ↥I)
        (ρ := 1 - rho ^ (xi / 4)) (by linarith) (restrictFree I z (f - tNE D (rho ^ (1 + xi)) f))
      have hw0 := (Complex.le_def.1 hnn).1
      simp only [Complex.zero_re] at hw0
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, add_zero]
      split_ifs with hlt
      · simp only [Complex.one_re]
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ha0]
        linarith
      · simp only [Complex.zero_re]
        positivity)
  have haff := appB_mre_affine (rho' / 2) h0 h1 D'' (f - tNE D (rho ^ (1 + xi)) f)
    (fun _ g => cstab D' (1 - rho ^ (xi / 4)) g) (1 / a) 0
  have hfin : (1 / a) * (mixtureRestrictionExpect (rho' / 2) h0 h1 D''
      (f - tNE D (rho ^ (1 + xi)) f) (fun _ g => cstab D' (1 - rho ^ (xi / 4)) g)).re + 0 ≤ a := by
    rw [add_zero]
    calc (1 / a) * _ ≤ (1 / a) * (a * a) :=
          mul_le_mul_of_nonneg_left (haa ▸ ha) (by positivity)
      _ = a := by field_simp
  exact hmono2.trans (haff.le.trans hfin)

/-- `cor:bad-xyz` (Supplement I, §6): the bad event on the triple alphabet. Under (A), (B) of
`(⋆)` and `lawX μ3 = ν_x` (the third conclusion of `appB_t1_noise_split`), the `x`-part of the
restriction, `W = Stab_{1-ρ^{ξ/4}}(f'_{Ī→x̃}; ν_x)`, satisfies (b) `E W ≤ ρ^{ξ/4}` and
(c) `Pr[W > ρ^{ξ/8}] ≤ ρ^{ξ/8}`, for `f` `1`-bounded. `y₀, z₀` only select the slice read by the
functional (`appB_mre_pushforward`). The threshold `d2` is the one of `appB_t1_bad_event_full`. -/
theorem appB_t1_bad_event_xyz (m : ℕ) {al : ℝ} (hal : 0 < al) {xi : ℝ} (hxi : 0 < xi) :
    ∃ d2 : ℝ, 0 < d2 ∧ ∀ rho rho' : ℝ, 0 < rho → rho ≤ d2 → rho / 2 ≤ rho' → rho' ≤ rho →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
      ∀ (ν μ3 : FinProb (X × Y × Z)), (∀ p ∈ ν.support, al ≤ ν.prob p) →
        PairwiseConnected3 ν.support → lawX μ3 = lawX ν →
      ∀ (y0 : Y) (z0 : Z) (h0 : 0 ≤ rho' / 2) (h1 : rho' / 2 ≤ 1) (ι : Type) [Fintype ι]
        [DecidableEq ι] (f : (ι → X) → ℂ), (∀ x, ‖f x‖ ≤ 1) →
        (mixtureRestrictionExpect (rho' / 2) h0 h1 μ3
          (fun t => (f - tNE (lawX ν) (rho ^ (1 + xi)) f) (fun i => (t i).1))
          (fun I G => cstab (lawX ν) (1 - rho ^ (xi / 4))
            (fun w : ↥I → X => G (fun i => (w i, y0, z0))))).re ≤ rho ^ (xi / 4) ∧
        (mixtureRestrictionExpect (rho' / 2) h0 h1 μ3
          (fun t => (f - tNE (lawX ν) (rho ^ (1 + xi)) f) (fun i => (t i).1))
          (fun I G => if rho ^ (xi / 8) < (cstab (lawX ν) (1 - rho ^ (xi / 4))
              (fun w : ↥I → X => G (fun i => (w i, y0, z0)))).re then (1 : ℂ) else 0)).re ≤
          rho ^ (xi / 8) := by
  obtain ⟨d2, hd2, H⟩ := appB_t1_bad_event_full m hal hxi
  refine ⟨d2, hd2, ?_⟩
  intro ρ ρ' hρ0 hρd hρ1 hρ2 X Y Z _ _ _ _ _ _ hX ν μ3 hat hT hx3 y0 z0 h0 h1 ι _ _ f hf
  obtain ⟨hlx, _, _⟩ := appB_inT_letters hat hT
  have hcl : cl2norm (lawX ν) f ≤ 1 := appB_cl2norm_le_sup (lawX ν) f hf
  have key := H ρ ρ' hρ0 hρd hρ1 hρ2 X hX (lawX ν) (lawX ν) (lawX ν) hlx hlx hlx
    (fun x => by ring) h0 h1 ι f hcl
  have e1 := appB_mre_pushforward μ3 y0 z0 h0 h1 (f - tNE (lawX ν) (ρ ^ (1 + xi)) f)
    (fun I G' => cstab (lawX ν) (1 - ρ ^ (xi / 4)) G')
  have e2 := appB_mre_pushforward μ3 y0 z0 h0 h1 (f - tNE (lawX ν) (ρ ^ (1 + xi)) f)
    (fun I G' => if ρ ^ (xi / 8) < (cstab (lawX ν) (1 - ρ ^ (xi / 4)) G').re then (1 : ℂ)
      else 0)
  rw [hx3] at e1 e2
  exact ⟨(congrArg Complex.re e1).trans_le key.1, (congrArg Complex.re e2).trans_le key.2⟩


end BadEvent

end TrackB
end RestrictedPolynomials
end
