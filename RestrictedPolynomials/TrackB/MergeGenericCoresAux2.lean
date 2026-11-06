module

public import RestrictedPolynomials.TrackB.MergeGenericCoresAux

/-!
# Track B, support layer of the cores (2): the random-restriction calculus of
`lem:merge` / `lem:merge2`

Support for `MergeGenericCores` (paper IV `writeup_stability.tex` l. 8554-8900):

* `mgenCjE`: the real expectation over the random restriction `(J, t)`, `J ∼_s`, `t ∼ ν^{J̄}`,
  with its linearity, push-forward and mixture identities;
* the joint restriction of `corr3` and the affine pointwise bound `mgenC_restrict_affine`;
* the pointwise bounds of term (I): `mgenC_xy_pointwise` (`lem:merge`, the `L²` form of `S_y`)
  and `mgenC_xx_pointwise` (`lem:merge2` in the `x` slot), where the events of the source are
  replaced by the Markov-type bound `𝟙[Stab > δ'] ≤ Stab / δ'`;
* the parameter arithmetic `mgenC_xy_params`, `mgenC_xx_params`, `mgenC_xy_final`,
  `mgenC_xx_final`.

Public helpers carry the prefix `mgenC`; the others are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section GnBlocks
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the soft average `R = T_{1-ξ}` on the blocks of the component average. -/
theorem mgenC_gn_blocks (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (ξ : ℝ) (g : (ι → X) → ℂ) :
    graphNoiseOp (lawX μ) (mgenComp μ) ξ g = ∑ B : Finset ι,
      (((1 - ξ) ^ B.card : ℝ) : ℂ) • mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B g := by
  rw [← mgenCOp_soft]
  exact mgenCOp_congr (fun i a b => mgenC_gn_soft _ _ ξ a b) g

end GnBlocks

/-! ### tools for the cores: joint restriction, expectation calculus, merge bound -/

section Tools
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem finProb_ext' {α : Type} [Fintype α] {π π' : FinProb α}
    (h : ∀ a, π.prob a = π'.prob a) : π = π' := by
  cases π
  cases π'
  congr
  funext a
  exact h a

private theorem mergePush_comp' {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (π : FinProb α) (f : α → β) (g : β → γ) :
    mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine finProb_ext' fun c => ?_
  show ∑ b ∈ univ.filter (fun b => g b = c), ∑ a ∈ univ.filter (fun a => f a = b), π.prob a =
    ∑ a ∈ univ.filter (fun a => g (f a) = c), π.prob a
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun a => g (f a) = c))
    (t := univ.filter (fun b => g b = c)) (g := f) (f := π.prob)
    (fun a ha => by simpa using ha)]
  refine Finset.sum_congr rfl fun b hb => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  have hb' : g b = c := (Finset.mem_filter.1 hb).2
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ hb', h⟩, fun h => h.2⟩

private theorem prob_le_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (a : α) : π.prob a ≤ (mergePush π f).prob (f a) :=
  Finset.single_le_sum (f := π.prob) (fun c _ => π.nonneg c) (by simp)

theorem mgenC_atom_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) {α₀ : ℝ} (h : ∀ p ∈ π.support, α₀ ≤ π.prob p) :
    ∀ p ∈ (mergePush π f).support, α₀ ≤ (mergePush π f).prob p := by
  intro p hp
  have hp' : (∑ a ∈ Finset.univ.filter (fun a => f a = p), π.prob a) ≠ 0 := hp
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
  have hle : π.prob a ≤ (mergePush π f).prob p :=
    Finset.single_le_sum (f := π.prob) (fun q _ => π.nonneg q) ha
  exact (h a hne).trans hle

private theorem lawX_mergeDistX (μ : FinProb (X × Y × Z)) (a : X → X) :
    lawX (mergeDistX μ a) =
      mergePush (lawX μ) (fun x => (⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a))) := by
  unfold lawX mergeDistX
  rw [mergePush_comp', mergePush_comp']

private theorem lawY_mergeDistX (μ : FinProb (X × Y × Z)) (a : X → X) :
    lawY (mergeDistX μ a) = lawY μ := by
  unfold lawY mergeDistX
  rw [mergePush_comp']

private theorem expect_pi_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    {κ : Type} [Fintype κ] [DecidableEq κ] (π : FinProb α) (p : α → β) (φ : (κ → β) → ℝ) :
    ((mergePush π p).pi κ).expect φ = (π.pi κ).expect (fun x => φ (fun i => p (x i))) := by
  unfold FinProb.expect
  symm
  rw [← Finset.sum_fiberwise univ (fun x : κ → α => fun i => p (x i))
    (fun x => (π.pi κ).prob x * φ (fun i => p (x i)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ x ∈ univ.filter (fun x : κ → α => (fun i => p (x i)) = b),
      (π.pi κ).prob x * φ (fun i => p (x i)) = (π.pi κ).prob x * φ b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  show _ = ∏ i, ∑ c ∈ univ.filter (fun c => p c = b i), π.prob c
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Fintype.mem_piFinset, funext_iff]

private theorem norm_cexpect_le {β : Type} [Fintype β] (π : FinProb β) (c : β → ℂ) :
    ‖π.cexpect c‖ ≤ π.expect (fun b => ‖c b‖) := by
  unfold FinProb.cexpect FinProb.expect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (π.nonneg b)]

private theorem sq_expect_le {β : Type} [Fintype β] (π : FinProb β) (φ : β → ℝ) :
    π.expect φ ^ 2 ≤ π.expect (fun b => φ b ^ 2) := by
  have h := π.expect_nonneg (f := fun b => (φ b - π.expect φ) ^ 2) (fun b => sq_nonneg _)
  have e : ∀ b, (φ b - π.expect φ) ^ 2 =
      φ b ^ 2 + (-2 * π.expect φ) * φ b + (π.expect φ) ^ 2 := fun b => by ring
  simp only [e, FinProb.expect_add, FinProb.expect_const_mul, FinProb.expect_const] at h
  nlinarith

/-- `√x ≤ (x/c + c)/2`. -/
private theorem sqrt_le_amgm {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    Real.sqrt x ≤ (x / c + c) / 2 := by
  have h1 := sq_nonneg (Real.sqrt x - c)
  have h2 := Real.sq_sqrt hx
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : x / c = x * (1 / c) := by ring
  have h3 : (Real.sqrt x * 2) * c ≤ (x / c + c) * c := by
    rw [add_mul, div_mul_cancel₀ x hc.ne']
    nlinarith
  exact le_of_mul_le_mul_right h3 hc

private theorem cl2sq_mergeX (μ : FinProb (X × Y × Z)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → X) → ℂ) :
    cl2sq (lawX μ) w = (μ.pi κ).expect (fun t => ‖w (fun i => (t i).1)‖ ^ 2) := by
  unfold cl2sq lawX
  rw [expect_pi_push]

/-- `|𝔼 w g h|² ≤ ‖w‖²` for `1`-bounded `g, h`. -/
private theorem corr3_sq_le_cl2sq (μ : FinProb (X × Y × Z)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hh : ∀ z, ‖h z‖ ≤ 1) : ‖corr3 μ w g h‖ ^ 2 ≤ cl2sq (lawX μ) w := by
  have h1 : ‖corr3 μ w g h‖ ≤ (μ.pi κ).expect (fun t => ‖w (fun i => (t i).1)‖) := by
    unfold corr3
    refine (norm_cexpect_le _ _).trans (FinProb.expect_mono _ fun t => ?_)
    rw [norm_mul, norm_mul]
    have e1 := hg (fun i => (t i).2.1)
    have e2 := hh (fun i => (t i).2.2)
    have e3 := norm_nonneg (w (fun i => (t i).1))
    have e4 := norm_nonneg (g (fun i => (t i).2.1))
    have e5 := norm_nonneg (h (fun i => (t i).2.2))
    nlinarith [mul_le_mul e1 e2 e5 zero_le_one]
  rw [cl2sq_mergeX]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (sq_expect_le _ _)

private theorem norm_le_sqrt_of_sq_le {c : ℂ} {y : ℝ} (h : ‖c‖ ^ 2 ≤ y) : ‖c‖ ≤ Real.sqrt y := by
  calc ‖c‖ = Real.sqrt (‖c‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt y := Real.sqrt_le_sqrt h

/-- the joint random restriction of a correlation (the restriction triple `(x̃, ỹ, z̃) ∼ μ^{J̄}`). -/
private theorem corr3_restrict (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (F : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 μ F g h = subsetExpect s hs0 hs1 (fun I => (μ.pi ↥Iᶜ).cexpect (fun t =>
      corr3 μ (restrictFree I (fun i => (t i).1) F) (restrictFree I (fun i => (t i).2.1) g)
        (restrictFree I (fun i => (t i).2.2) h))) := by
  have key := restrict_key hs0 hs1 μ μ μ (fun a => by ring)
    (fun t : ι → X × Y × Z => F (fun i => (t i).1) * g (fun i => (t i).2.1) * h (fun i => (t i).2.2))
  unfold corr3
  rw [← key]
  congr 1
  funext I
  congr 1
  funext z
  congr 1
  funext y
  simp only [restrictFree]
  have e1 : (fun i => (glueFree I y z i).1) = glueFree I (fun i => (y i).1) (fun i => (z i).1) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  have e2 : (fun i => (glueFree I y z i).2.1) =
      glueFree I (fun i => (y i).2.1) (fun i => (z i).2.1) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  have e3 : (fun i => (glueFree I y z i).2.2) =
      glueFree I (fun i => (y i).2.2) (fun i => (z i).2.2) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  rw [e1, e2, e3]

/-- the real expectation over the random restriction `(J, t)`, `J ∼_s`, `t ∼ ν^{J̄}`. -/
def mgenCjE {ι : Type} [Fintype ι] [DecidableEq ι] {β : Type} [Fintype β] (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ν : FinProb β) (Φ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) : ℝ :=
  ((bernoulli s hs0 hs1).pi ι).expect fun σ => (ν.pi ↥(trueSet σ)ᶜ).expect (Φ (trueSet σ))

section JE
variable {ι : Type} [Fintype ι] [DecidableEq ι] {β : Type} [Fintype β] {s : ℝ} (hs0 : 0 ≤ s)
  (hs1 : s ≤ 1) (ν : FinProb β)

private theorem norm_subsetExpect_le (c : (I : Finset ι) → (↥Iᶜ → β) → ℂ) :
    ‖subsetExpect s hs0 hs1 (fun I => (ν.pi ↥Iᶜ).cexpect (c I))‖ ≤
      mgenCjE s hs0 hs1 ν (fun I t => ‖c I t‖) := by
  unfold subsetExpect mgenCjE
  exact (norm_cexpect_le _ _).trans (FinProb.expect_mono _ fun σ => norm_cexpect_le _ _)

private theorem jE_mono {Φ Ψ : (I : Finset ι) → (↥Iᶜ → β) → ℝ} (h : ∀ I t, Φ I t ≤ Ψ I t) :
    mgenCjE s hs0 hs1 ν Φ ≤ mgenCjE s hs0 hs1 ν Ψ :=
  FinProb.expect_mono _ fun _ => FinProb.expect_mono _ fun t => h _ t

private theorem jE_add (Φ Ψ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => Φ I t + Ψ I t) = mgenCjE s hs0 hs1 ν Φ + mgenCjE s hs0 hs1 ν Ψ := by
  unfold mgenCjE
  simp only [FinProb.expect_add]

private theorem jE_mul (c : ℝ) (Φ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => c * Φ I t) = c * mgenCjE s hs0 hs1 ν Φ := by
  unfold mgenCjE
  simp only [FinProb.expect_const_mul]

private theorem jE_const (c : ℝ) : mgenCjE (ι := ι) s hs0 hs1 ν (fun _ _ => c) = c := by
  unfold mgenCjE
  simp

private theorem jE_push {γ : Type} [Fintype γ] [DecidableEq γ] (p : β → γ)
    (Ψ : (I : Finset ι) → (↥Iᶜ → γ) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => Ψ I (fun i => p (t i))) = mgenCjE s hs0 hs1 (mergePush ν p) Ψ := by
  unfold mgenCjE
  congr 1
  funext σ
  exact (expect_pi_push ν p _).symm

theorem mgenC_jE_mix {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (F : (ι → α) → ℂ)
    (Ψ : (I : Finset ι) → ((↥I → α) → ℂ) → ℝ) :
    (mixtureRestrictionExpect s hs0 hs1 D F (fun I gt => ((Ψ I gt : ℝ) : ℂ))).re =
      mgenCjE s hs0 hs1 D (fun I z => Ψ I (restrictFree I z F)) := by
  unfold mixtureRestrictionExpect subsetExpect mgenCjE
  simp only [mgenC_cexpect_ofReal, Complex.ofReal_re]

theorem mgenC_jE_cl2sq {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α)
    (F : (ι → α) → ℂ) :
    mgenCjE s hs0 hs1 D (fun I z => cl2sq D (restrictFree I z F)) = cl2sq D F := by
  unfold mgenCjE
  simp only [mgenC_expect_cl2sq_restrict, FinProb.expect_const]

end JE

/-- the component average sees only the component of each coordinate. -/
private theorem gn1_row (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : (κ → X) → ℂ) (x : κ → X) :
    graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => a (x i)) =
      graphNoiseOp (lawX μ) (mgenComp μ) 1 u x := by
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  unfold graphNoiseOp
  refine Finset.sum_congr rfl fun y _ => ?_
  have e : ∏ i, graphNoiseKernel (lawX μ) (mgenComp μ) 1 (a (x i)) (y i) =
      ∏ i, graphNoiseKernel (lawX μ) (mgenComp μ) 1 (x i) (y i) :=
    Finset.prod_congr rfl fun i _ => (mgenC_gnE_row hG (ha.1 (x i)) (y i)).symm
  beta_reduce
  rw [e]

private theorem cl2sq_gn_le (μ : FinProb (X × Y × Z)) {κ : Type} [Fintype κ] [DecidableEq κ]
    {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (u : (κ → X) → ℂ) :
    cl2sq (lawX μ) (graphNoiseOp (lawX μ) (mgenComp μ) ξ u) ≤ cl2sq (lawX μ) u := by
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  have hEE := mgenC_gnE_idem (D := lawX μ) hG
  have hErev := mgenC_gnE_rev (D := lawX μ) hG
  rw [mgenC_gn_blocks, mgenCP_cl2sq_sum (D := lawX μ) hEE hErev,
    mgenCP_cl2sq (D := lawX μ) hEE hErev u]
  refine Finset.sum_le_sum fun B _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_of_le_one_left (cl2sq_nonneg _ _)
    (pow_le_one₀ (pow_nonneg (by linarith) _) (pow_le_one₀ (by linarith) (by linarith)))

theorem mgenC_gn_bounded {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α)
    (G : α → α → Prop) [DecidableRel G] {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) {κ : Type}
    [Fintype κ] [DecidableEq κ] (u : (κ → α) → ℂ) (hu : ∀ x, ‖u x‖ ≤ 1) (x : κ → α) :
    ‖graphNoiseOp D G ξ u x‖ ≤ 1 := by
  unfold graphNoiseOp
  refine (norm_sum_le _ _).trans ?_
  have hK : ∀ y : κ → α, 0 ≤ ∏ i, graphNoiseKernel D G ξ (x i) (y i) := fun y =>
    Finset.prod_nonneg fun i _ => mgenC_gn_nonneg h0 h1 _ _
  calc ∑ y, ‖((∏ i, graphNoiseKernel D G ξ (x i) (y i) : ℝ) : ℂ) * u y‖
      ≤ ∑ y : κ → α, ∏ i, graphNoiseKernel D G ξ (x i) (y i) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK y)]
        exact mul_le_of_le_one_right (hK y) (hu y)
    _ = ∏ i, ∑ b, graphNoiseKernel D G ξ (x i) b := (Fintype.prod_sum _).symm
    _ ≤ 1 := Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun b _ => mgenC_gn_nonneg h0 h1 _ _)
        (fun i _ => mgenC_gn_rowsum_le h0 h1 _)

/-- (V)+(VI) of `lem:merge`: `|𝔼_μ u g h| ≤ ‖u - P₀u‖ + |𝔼_{μ'} U g h|` with `P₀ u = U ∘ a`. -/
private theorem corr3_split_merge (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖corr3 μ u g h‖ ≤ Real.sqrt (cl2sq (lawX μ)
        (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x)) +
      ‖corr3 (mergeDistX μ a)
        (fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val)) g h‖ := by
  have hsplit : corr3 μ u g h = corr3 μ (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x)
      g h + corr3 μ (graphNoiseOp (lawX μ) (mgenComp μ) 1 u) g h := by
    unfold corr3 FinProb.cexpect
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hmerge : corr3 μ (graphNoiseOp (lawX μ) (mgenComp μ) 1 u) g h = corr3 (mergeDistX μ a)
      (fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val)) g h := by
    rw [← mgen_corr3_merge_x]
    congr 1
    funext x
    exact (gn1_row μ a ha u x).symm
  rw [hsplit, hmerge]
  exact (norm_add_le _ _).trans (add_le_add_left (norm_le_sqrt_of_sq_le
    (corr3_sq_le_cl2sq μ _ g h hg hh)) _)

/-- `‖U‖_{μ'_x} ≤ ‖u‖_{μ_x}` for `U ∘ a = P₀ u`. -/
private theorem cl2sq_merge_le (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : (κ → X) → ℂ) :
    cl2sq (lawX (mergeDistX μ a))
      (fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val)) ≤
      cl2sq (lawX μ) u := by
  have e : cl2sq (lawX (mergeDistX μ a))
      (fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val)) =
      cl2sq (lawX μ) (graphNoiseOp (lawX μ) (mgenComp μ) 1 u) := by
    rw [lawX_mergeDistX]
    unfold cl2sq
    rw [expect_pi_push]
    congr 1
    funext x
    show ‖graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => a (x i))‖ ^ 2 = _
    rw [gn1_row μ a ha u x]
  rw [e]
  exact cl2sq_gn_le μ zero_le_one le_rfl u

/-- `Stab(U; μ'_x) ≤ Stab(u; μ_x)` for `U ∘ a = P₀ u`. -/
private theorem cstab_merge_le (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) {κ : Type} [Fintype κ] [DecidableEq κ]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (u : (κ → X) → ℂ) :
    (cstab (lawX (mergeDistX μ a)) ρ
      (fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val))).re ≤
      (cstab (lawX μ) ρ u).re := by
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  rw [lawX_mergeDistX, ← cstab_pushforward]
  have e : (fun x : κ → X => graphNoiseOp (lawX μ) (mgenComp μ) 1 u
      (fun i => ((⟨a (x i), Set.mem_range_self _⟩ : ↥(Set.range a)) : X))) =
      graphNoiseOp (lawX μ) (mgenComp μ) 1 u := by
    funext x
    exact gn1_row μ a ha u x
  rw [e]
  exact mgen_stab_graphNoise_le (lawX μ) (mgenComp μ) hG zero_le_one le_rfl hρ0 hρ1 u

end Tools

section SGen
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem corr3_reindex (ν : FinProb (X × Y × Z)) {κ : Type} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (e : κ ≃ Fin n) (f : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) :
    corr3 ν (fun x : Fin n → X => f (x ∘ e)) (fun y => g (y ∘ e)) (fun z => h (z ∘ e)) =
      corr3 ν f g h := by
  unfold corr3
  rw [← cexpect_pi_equiv e ν]
  congr 1
  funext y
  simp [Function.comp_def]

private theorem cstab_reindex {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (ρ : ℝ)
    {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n) (g : (κ → α) → ℂ) :
    cstab D ρ (fun y : Fin n → α => g (y ∘ e)) = cstab D ρ g := by
  have := cstab_equiv e.symm D ρ g
  rwa [Equiv.symm_symm] at this

private theorem sStmtY_gen {ν : FinProb (X × Y × Z)} {M δ₀ η : ℝ} (H : SStmtY ν M δ₀ η)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ δ₀) {κ : Type} [Fintype κ] [DecidableEq κ]
    (f : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) (hs : (cstab (lawY ν) (1 - δ) g).re ≤ δ) :
    ‖corr3 ν f g h‖ ≤ M * δ ^ η := by
  have := H δ hδ hδ' (Fintype.card κ) (fun x => f (x ∘ Fintype.equivFin κ))
    (fun y => g (y ∘ Fintype.equivFin κ)) (fun z => h (z ∘ Fintype.equivFin κ))
    (fun x => hf _) (fun y => hg _) (fun z => hh _)
    (by rw [cstab_reindex]; exact hs)
  rwa [corr3_reindex] at this

private theorem sStmtX_gen {ν : FinProb (X × Y × Z)} {M δ₀ η : ℝ} (H : SStmtX ν M δ₀ η)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ δ₀) {κ : Type} [Fintype κ] [DecidableEq κ]
    (f : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) (hs : (cstab (lawX ν) (1 - δ) f).re ≤ δ) :
    ‖corr3 ν f g h‖ ≤ M * δ ^ η := by
  have := H δ hδ hδ' (Fintype.card κ) (fun x => f (x ∘ Fintype.equivFin κ))
    (fun y => g (y ∘ Fintype.equivFin κ)) (fun z => h (z ∘ Fintype.equivFin κ))
    (fun x => hf _) (fun y => hg _) (fun z => hh _)
    (by rw [cstab_reindex]; exact hs)
  rwa [corr3_reindex] at this

/-- the `L²` form of `S_y` (the step `‖f̃₀‖ ‖f''‖` of term (VI) of `lem:merge`):
`|𝔼 F g h|² ≤ ‖F‖² M δ^η` for an unbounded `F`. -/
private theorem sStmtY_L2 {ν : FinProb (X × Y × Z)} {M δ₀ η : ℝ} (H : SStmtY ν M δ₀ η)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ δ₀) {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hh : ∀ z, ‖h z‖ ≤ 1) (hs : (cstab (lawY ν) (1 - δ) g).re ≤ δ) :
    ‖corr3 ν F g h‖ ^ 2 ≤ cl2sq (lawX ν) F * (M * δ ^ η) := by
  set w : (κ → X) → ℝ := fun x => ((lawX ν).pi κ).prob x with hw
  set A : (κ → X) → ℂ := fun x => ∑ u : κ → Y × Z,
    ((∏ i, ν.prob (x i, u i) : ℝ) : ℂ) * (g (fun i => (u i).1) * h (fun i => (u i).2)) with hA
  have hsplit : ∀ F' : (κ → X) → ℂ, corr3 ν F' g h = ∑ x, F' x * A x := by
    intro F'
    unfold corr3 FinProb.cexpect
    rw [← (Equiv.arrowProdEquivProdArrow κ (fun _ => X) (fun _ => Y × Z)).symm.sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, FinProb.pi_prob]
    ring
  have hwx : ∀ x, ∑ u : κ → Y × Z, ∏ i, ν.prob (x i, u i) = w x := by
    intro x
    rw [← Fintype.prod_sum (fun i v => ν.prob (x i, v))]
    show _ = ((lawX ν).pi κ).prob x
    rw [FinProb.pi_prob]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mgenC_lawX_prob, Fintype.sum_prod_type]
  have hw0 : ∀ x, 0 ≤ w x := fun x => ((lawX ν).pi κ).nonneg x
  have hA_le : ∀ x, ‖A x‖ ≤ w x := by
    intro x
    rw [hA, ← hwx x]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    have hp : 0 ≤ ∏ i, ν.prob (x i, u i) := Finset.prod_nonneg fun i _ => ν.nonneg _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, norm_mul]
    have e1 := hg (fun i => (u i).1)
    have e2 := hh (fun i => (u i).2)
    have := mul_le_mul e1 e2 (norm_nonneg _) zero_le_one
    nlinarith
  set f'' : (κ → X) → ℂ := fun x => if w x = 0 then 0 else A x / (w x : ℂ) with hf''
  have hA_eq : ∀ x, A x = (w x : ℂ) * f'' x := by
    intro x
    by_cases h0 : w x = 0
    · have := hA_le x
      rw [h0] at this
      have hA0 : A x = 0 := norm_le_zero_iff.1 this
      simp [hf'', h0, hA0]
    · have : (w x : ℂ) ≠ 0 := by exact_mod_cast h0
      simp only [hf'', h0, ite_false]
      field_simp
  have hf''b : ∀ x, ‖f'' x‖ ≤ 1 := by
    intro x
    by_cases h0 : w x = 0
    · simp [hf'', h0]
    · simp only [hf'', h0, ite_false, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw0 x)]
      rw [div_le_one (lt_of_le_of_ne (hw0 x) (Ne.symm h0))]
      exact hA_le x
  set T : ℝ := ∑ x, w x * ‖f'' x‖ ^ 2 with hT
  have hTc : (T : ℂ) = corr3 ν (fun x => star (f'' x)) g h := by
    rw [hsplit, hT, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA_eq x]
    have : star (f'' x) * f'' x = ((‖f'' x‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    push_cast
    rw [← this]
    ring
  have hTle : T ≤ M * δ ^ η := by
    have h1 := sStmtY_gen H hδ hδ' (fun x => star (f'' x)) g h
      (fun x => by rw [norm_star]; exact hf''b x) hg hh hs
    rw [← hTc, Complex.norm_real, Real.norm_eq_abs] at h1
    exact (le_abs_self T).trans h1
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => mul_nonneg (hw0 x) (sq_nonneg _)
  have hcs : ‖corr3 ν F g h‖ ≤ ∑ x, Real.sqrt (w x) * ‖F x‖ * (Real.sqrt (w x) * ‖f'' x‖) := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    rw [hA_eq x, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
    have hs := Real.mul_self_sqrt (hw0 x)
    calc ‖F x‖ * (w x * ‖f'' x‖) =
        ‖F x‖ * ((Real.sqrt (w x) * Real.sqrt (w x)) * ‖f'' x‖) := by rw [hs]
      _ = _ := by ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => Real.sqrt (w x) * ‖F x‖)
    (fun x => Real.sqrt (w x) * ‖f'' x‖)
  have e1 : ∑ x, (Real.sqrt (w x) * ‖F x‖) ^ 2 = cl2sq (lawX ν) F := by
    unfold cl2sq FinProb.expect
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw0 x)]
  have e2 : ∑ x, (Real.sqrt (w x) * ‖f'' x‖) ^ 2 = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw0 x)]
  rw [e1, e2] at h2
  have h3 : ‖corr3 ν F g h‖ ^ 2 ≤ cl2sq (lawX ν) F * T :=
    (pow_le_pow_left₀ (norm_nonneg _) hcs 2).trans h2
  exact h3.trans (mul_le_mul_of_nonneg_left hTle (cl2sq_nonneg _ _))

end SGen

/-! ### real arithmetic for the cores -/

theorem mgenC_rpow_inv_pow {δ : ℝ} (hδ : 0 ≤ δ) (k n : ℕ) :
    (δ ^ (1 / (k : ℝ))) ^ n = δ ^ ((n : ℝ) / k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ]
  congr 1
  ring

private theorem sqrt_rpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : Real.sqrt (x ^ y) = x ^ (y / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

private theorem log_le_inv_rpow {δ : ℝ} (hδ : 0 < δ) {k : ℝ} (hk : 0 < k) :
    Real.log (1 / δ) ≤ k / δ ^ (1 / k) := by
  have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / δ) (by positivity : 0 < 1 / k)
  rw [one_div δ, Real.inv_rpow hδ.le] at h
  rw [one_div δ]
  calc Real.log δ⁻¹ ≤ (δ ^ (1 / k))⁻¹ / (1 / k) := h
    _ = k / δ ^ (1 / k) := by field_simp

private theorem pow_le_of_log {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ) {d : ℕ}
    (hd : Real.log (1 / δ) / γ ≤ d) : (1 - γ) ^ d ≤ δ := by
  have h1 : (1 - γ) ^ d ≤ Real.exp (-γ) ^ d :=
    pow_le_pow_left₀ (by linarith) (by have := Real.one_sub_le_exp_neg γ; linarith) d
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.log (1 / δ) ≤ γ * d := by rwa [div_le_iff₀ hγ0, mul_comm] at hd
  have h3 : (d : ℝ) * -γ ≤ Real.log δ := by
    rw [one_div, Real.log_inv] at h2
    linarith
  calc (1 - γ) ^ d ≤ Real.exp ((d : ℝ) * -γ) := h1
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 h3
    _ = δ := Real.exp_log hδ

theorem mgenC_cl2sq_le_one {X : Type} [Fintype X] {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : FinProb X) (f : (ι → X) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) : cl2sq D f ≤ 1 := by
  unfold cl2sq
  refine FinProb.expect_le_const _ fun x => ?_
  have := hf x
  have := norm_nonneg (f x)
  nlinarith

theorem mgenC_restrict_bounded {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    [DecidableEq ι] (I : Finset ι) (z : ↥Iᶜ → α) (f : (ι → α) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∀ y, ‖restrictFree I z f y‖ ≤ 1 := fun _ => hf _

private theorem cstab_re_nonneg {α : Type} [Fintype α] [DecidableEq α] {κ : Type} [Fintype κ]
    [DecidableEq κ] (D : FinProb α) {ρ : ℝ} (hρ : 0 ≤ ρ) (g : (κ → α) → ℂ) :
    0 ≤ (cstab D ρ g).re :=
  (Complex.le_def.1 (cstab_nonneg D hρ g)).1

section CoreLemmas
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

theorem mgenC_atoms_lawY {μ : FinProb (X × Y × Z)} (hT : InT μ.support) {α : ℝ}
    (hat : ∀ p ∈ μ.support, α ≤ μ.prob p) (y : Y) : α ≤ (lawY μ).prob y := by
  obtain ⟨x, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_y hT.1 y
  exact (hat _ hp).trans (prob_le_push μ (fun p => p.2.1) (x, y, z))

theorem mgenC_atoms_lawX {μ : FinProb (X × Y × Z)} (hT : InT μ.support) {α : ℝ}
    (hat : ∀ p ∈ μ.support, α ≤ μ.prob p) (x : X) : α ≤ (lawX μ).prob x := by
  obtain ⟨y, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_x hT.1 x
  exact (hat _ hp).trans (prob_le_push μ (fun p => p.1) (x, y, z))

/-- the random restriction, with an affine pointwise bound in the restricted quantities. -/
theorem mgenC_restrict_affine (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (F : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    {V : Type} [Fintype V] [DecidableEq V] (p : X × Y × Z → V) (c₁ c₂ c₃ c₄ : ℝ)
    (W N : (I : Finset ι) → (↥Iᶜ → X) → ℝ) (S : (I : Finset ι) → (↥Iᶜ → V) → ℝ)
    (hpt : ∀ (I : Finset ι) (t : ↥Iᶜ → X × Y × Z),
      ‖corr3 μ (restrictFree I (fun i => (t i).1) F) (restrictFree I (fun i => (t i).2.1) g)
        (restrictFree I (fun i => (t i).2.2) h)‖ ≤
      c₁ * W I (fun i => (t i).1) + c₂ * N I (fun i => (t i).1) + c₃ * S I (fun i => p (t i)) +
        c₄) :
    ‖corr3 μ F g h‖ ≤ c₁ * mgenCjE s hs0 hs1 (lawX μ) W + c₂ * mgenCjE s hs0 hs1 (lawX μ) N +
      c₃ * mgenCjE s hs0 hs1 (mergePush μ p) S + c₄ := by
  rw [corr3_restrict μ hs0 hs1 F g h]
  refine (norm_subsetExpect_le hs0 hs1 μ _).trans ((jE_mono hs0 hs1 μ hpt).trans (le_of_eq ?_))
  have e1 := jE_push hs0 hs1 μ (fun q => q.1) W
  have e2 := jE_push hs0 hs1 μ (fun q => q.1) N
  have e3 := jE_push hs0 hs1 μ p S
  rw [jE_add, jE_add, jE_add, jE_mul, jE_mul, jE_mul, jE_const, e3]
  exact congrArg₂ (fun u v => c₁ * u + c₂ * v + c₃ * mgenCjE s hs0 hs1 (mergePush μ p) S + c₄) e1 e2

/-- pointwise bound of term (I) of `lem:merge` after the restriction. -/
theorem mgenC_xy_pointwise (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) {M δ₀ η δ' ε : ℝ}
    (Hμ' : SStmtY (mergeDistX μ a) M δ₀ η) (hM : 0 ≤ M) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hδ'δ₀ : δ' ≤ δ₀) (hε0 : 0 < ε) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : (κ → X) → ℂ) (gt : (κ → Y) → ℂ) (ht : (κ → Z) → ℂ) (hgt : ∀ y, ‖gt y‖ ≤ 1)
    (hht : ∀ z, ‖ht z‖ ≤ 1) :
    ‖corr3 μ u gt ht‖ ≤ (1 / (2 * ε)) *
        cl2sq (lawX μ) (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x) +
      (Real.sqrt (M * δ' ^ η) / 2 + ε / 2) * cl2sq (lawX μ) u +
      (1 / (2 * ε * δ')) * (cstab (lawY μ) (1 - δ') gt).re +
      (ε / 2 + Real.sqrt (M * δ' ^ η) / 2) := by
  set W := cl2sq (lawX μ) (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x) with hW
  set N := cl2sq (lawX μ) u with hN
  set S := (cstab (lawY μ) (1 - δ') gt).re with hS
  set Q := Real.sqrt (M * δ' ^ η) with hQ
  set U : (κ → ↥(Set.range a)) → ℂ :=
    fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val) with hU
  have h1 : ‖corr3 μ u gt ht‖ ≤ Real.sqrt W + ‖corr3 (mergeDistX μ a) U gt ht‖ :=
    corr3_split_merge μ a ha u gt ht hgt hht
  have hW0 : 0 ≤ W := cl2sq_nonneg _ _
  have hN0 : 0 ≤ N := cl2sq_nonneg _ _
  have hS0 : 0 ≤ S := cstab_re_nonneg _ (by linarith) _
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have h2 : Real.sqrt W ≤ (W / ε + ε) / 2 := sqrt_le_amgm hW0 hε0
  have hUN : cl2sq (lawX (mergeDistX μ a)) U ≤ N := cl2sq_merge_le μ a ha u
  have hT0 : 0 ≤ (ε * N + S / (ε * δ')) / 2 := by positivity
  have hQN : 0 ≤ Q * (N + 1) / 2 := by positivity
  have h3 : ‖corr3 (mergeDistX μ a) U gt ht‖ ≤ Q * (N + 1) / 2 + (ε * N + S / (ε * δ')) / 2 := by
    by_cases hSd : S ≤ δ'
    · have h4 := sStmtY_L2 Hμ' hδ'0 hδ'δ₀ U gt ht hgt hht (by rw [lawY_mergeDistX]; exact hSd)
      have h5 : ‖corr3 (mergeDistX μ a) U gt ht‖ ≤ Real.sqrt N * Q := by
        rw [hQ, ← Real.sqrt_mul hN0]
        exact norm_le_sqrt_of_sq_le (h4.trans (mul_le_mul_of_nonneg_right hUN
          (mul_nonneg hM (Real.rpow_nonneg hδ'0.le _))))
      have h6 : Real.sqrt N ≤ (N + 1) / 2 := by
        have := sqrt_le_amgm hN0 one_pos
        simpa using this
      have h7 := mul_le_mul_of_nonneg_right h6 hQ0
      have e : (N + 1) / 2 * Q = Q * (N + 1) / 2 := by ring
      linarith
    · push Not at hSd
      have h4 := corr3_sq_le_cl2sq (mergeDistX μ a) U gt ht hgt hht
      have h5 := norm_le_sqrt_of_sq_le (h4.trans hUN)
      have h6 := sqrt_le_amgm hN0 (show 0 < 1 / ε by positivity)
      have h7 : 1 / ε ≤ S / (ε * δ') := by
        rw [div_le_div_iff₀ hε0 (by positivity)]
        nlinarith
      have h8 : N / (1 / ε) = ε * N := by field_simp
      rw [h8] at h6
      linarith
  have e1 : (W / ε + ε) / 2 = (1 / (2 * ε)) * W + ε / 2 := by field_simp
  have e2 : (1 / (2 * ε * δ')) * S = (S / (ε * δ')) / 2 := by field_simp
  have e3 : (Q / 2 + ε / 2) * N = Q * N / 2 + ε * N / 2 := by ring
  linarith

end CoreLemmas

/-! ### the parameter arithmetic of `lem:merge` -/

theorem mgenC_xy_params {γ K δ₂ δ ε s : ℝ} {d : ℕ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hK0 : 0 < K)
    (hδ₂0 : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hδq : δ ≤ (δ₂ / (K * (6 / γ + 1))) ^ 2) (hε : ε = δ ^ (1 / (6 : ℕ) : ℝ))
    (hd : d = ⌈Real.log (1 / δ) / γ⌉₊) (hs : s = ε ^ 2 / d) :
    0 < ε ∧ ε ≤ 1 ∧ ε ^ 3 = δ ^ (1 / 2 : ℝ) ∧ (1 - γ) ^ d ≤ δ ∧ 0 < s ∧ s ≤ 1 ∧
      (d : ℝ) * s = ε ^ 2 ∧ 0 < K * δ / s ∧ K * δ / s ≤ δ₂ ∧ K * δ ≤ s ∧
      K * δ / s ≤ K * (6 / γ + 1) * ε ^ 3 ∧ δ / (ε * (K * δ / s)) ≤ ε / K := by
  have hδ1' : δ < 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; exact Real.rpow_pos_of_pos hδ _
  have hε1 : ε ≤ 1 := by rw [hε]; exact Real.rpow_le_one hδ.le hδ1'.le (by norm_num)
  have hε6 : ε ^ 6 = δ := by
    rw [hε, mgenC_rpow_inv_pow hδ.le]
    norm_num
  have hε3 : ε ^ 3 = δ ^ (1 / 2 : ℝ) := by
    rw [hε, mgenC_rpow_inv_pow hδ.le]
    norm_num
  have hlog : Real.log (1 / δ) ≤ 6 / ε := by
    have := log_le_inv_rpow hδ (k := 6) (by norm_num)
    rw [hε]
    push_cast
    exact this
  have hlogpos : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hd_lo : Real.log (1 / δ) / γ ≤ d := by rw [hd]; exact Nat.le_ceil _
  have hd_pos : (0 : ℝ) < d := lt_of_lt_of_le (div_pos hlogpos hγ0) hd_lo
  have hd_up : (d : ℝ) ≤ (6 / γ + 1) / ε := by
    have h1 : (d : ℝ) < Real.log (1 / δ) / γ + 1 := by
      rw [hd]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : Real.log (1 / δ) / γ ≤ 6 / ε / γ := div_le_div_of_nonneg_right hlog hγ0.le
    have h3 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
    have h4 : (6 / γ + 1) / ε = 6 / ε / γ + 1 / ε := by field_simp
    rw [h4]
    linarith
  have hpow : (1 - γ) ^ d ≤ δ := pow_le_of_log hγ0 hγ1 hδ hd_lo
  have hd1 : (1 : ℝ) ≤ d := by
    have : 0 < d := by exact_mod_cast hd_pos
    exact_mod_cast this
  have hs0 : 0 < s := by rw [hs]; positivity
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hd_pos]
    linarith
  have hds : (d : ℝ) * s = ε ^ 2 := by rw [hs]; field_simp
  have hδ'eq : K * δ / s = K * d * ε ^ 4 := by
    rw [hs, ← hε6]
    field_simp
  have hδ'le : K * δ / s ≤ K * (6 / γ + 1) * ε ^ 3 := by
    rw [hδ'eq]
    have := mul_le_mul_of_nonneg_left hd_up (show 0 ≤ K * ε ^ 4 by positivity)
    calc K * d * ε ^ 4 = K * ε ^ 4 * d := by ring
      _ ≤ K * ε ^ 4 * ((6 / γ + 1) / ε) := this
      _ = K * (6 / γ + 1) * ε ^ 3 := by field_simp
  have hε3le : ε ^ 3 ≤ δ₂ / (K * (6 / γ + 1)) := by
    have h1 : ε ^ 3 = Real.sqrt δ := by rw [hε3, Real.sqrt_eq_rpow]
    rw [h1]
    calc Real.sqrt δ ≤ Real.sqrt ((δ₂ / (K * (6 / γ + 1))) ^ 2) := Real.sqrt_le_sqrt hδq
      _ = δ₂ / (K * (6 / γ + 1)) := Real.sqrt_sq (by positivity)
  have hδ'δ₂ : K * δ / s ≤ δ₂ := by
    calc K * δ / s ≤ K * (6 / γ + 1) * ε ^ 3 := hδ'le
      _ ≤ K * (6 / γ + 1) * (δ₂ / (K * (6 / γ + 1))) :=
          mul_le_mul_of_nonneg_left hε3le (by positivity)
      _ = δ₂ := by field_simp
  have hKδ : K * δ ≤ s := by
    have h : K * δ / s ≤ 1 := hδ'δ₂.trans hδ₂1
    rwa [div_le_one hs0] at h
  have hδK : δ / (ε * (K * δ / s)) ≤ ε / K := by
    rw [hδ'eq, div_le_div_iff₀ (by positivity) hK0, ← hε6]
    have h5 : ε ^ 6 * K * 1 ≤ ε * (K * d * ε ^ 4) * ε := by
      have : ε ^ 6 * K = ε * (K * ε ^ 4) * ε := by ring
      nlinarith [mul_le_mul_of_nonneg_left hd1 (show 0 ≤ ε * (K * ε ^ 4) * ε by positivity)]
    linarith
  exact ⟨hε0, hε1, hε3, hpow, hs0, hs1, hds, by positivity, hδ'δ₂, hKδ, hδ'le, hδK⟩

theorem mgenC_xy_final {ε Q B K δ δ' θ jW jN jS : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK0 : 0 < K)
    (hδ'0 : 0 < δ') (hQ0 : 0 ≤ Q) (hjW : jW ≤ ε ^ 2) (hjN : jN ≤ 1)
    (hjS : jS ≤ δ) (hδK : δ / (ε * δ') ≤ ε / K) (hQ : Q ≤ B * θ) (hθ : ε ≤ θ) :
    (1 / (2 * ε)) * jW + (Q / 2 + ε / 2) * jN + (1 / (2 * ε * δ')) * jS + (ε / 2 + Q / 2) +
      ε ^ 3 ≤ (3 + 1 / K + B) * θ := by
  have hc1 : (1 / (2 * ε)) * jW ≤ ε / 2 := by
    have : (1 / (2 * ε)) * jW ≤ (1 / (2 * ε)) * ε ^ 2 :=
      mul_le_mul_of_nonneg_left hjW (by positivity)
    have e : (1 / (2 * ε)) * ε ^ 2 = ε / 2 := by field_simp
    linarith
  have hc2 : (Q / 2 + ε / 2) * jN ≤ Q / 2 + ε / 2 :=
    mul_le_of_le_one_right (by positivity) hjN
  have hc3 : (1 / (2 * ε * δ')) * jS ≤ ε / K / 2 := by
    have : (1 / (2 * ε * δ')) * jS ≤ (1 / (2 * ε * δ')) * δ :=
      mul_le_mul_of_nonneg_left hjS (by positivity)
    have e : (1 / (2 * ε * δ')) * δ = δ / (ε * δ') / 2 := by field_simp
    linarith
  have hε3 : ε ^ 3 ≤ ε := by
    have : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
    nlinarith
  have h1 : ε / K ≤ (1 / K) * θ := by
    rw [div_eq_mul_one_div ε K, mul_comm]
    exact mul_le_mul_of_nonneg_left hθ (by positivity)
  have hθ0 : 0 ≤ θ := hε0.le.trans hθ
  have hεK : 0 ≤ ε / K := by positivity
  linarith

theorem mgenC_rpow_Q_le {M K C δ δ' ε η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hδ'0 : 0 ≤ δ') (hε0 : 0 ≤ ε) (hη : 0 ≤ η) (hδ'le : δ' ≤ K * C * ε ^ 3)
    (hε3 : ε ^ 3 = δ ^ (1 / 2 : ℝ)) :
    Real.sqrt (M * δ' ^ η) ≤ Real.sqrt M * (K * C) ^ (η / 2) * δ ^ (η / 4) := by
  have h1 : δ' ^ η ≤ (K * C) ^ η * δ ^ (η / 2) := by
    calc δ' ^ η ≤ (K * C * ε ^ 3) ^ η := Real.rpow_le_rpow hδ'0 hδ'le hη
      _ = (K * C) ^ η * (ε ^ 3) ^ η := Real.mul_rpow (by positivity) (by positivity)
      _ = (K * C) ^ η * δ ^ (η / 2) := by
          rw [hε3, ← Real.rpow_mul hδ]
          congr 2
          ring
  calc Real.sqrt (M * δ' ^ η) ≤ Real.sqrt (M * ((K * C) ^ η * δ ^ (η / 2))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 hM)
    _ = Real.sqrt M * (K * C) ^ (η / 2) * δ ^ (η / 4) := by
        rw [Real.sqrt_mul hM, Real.sqrt_mul (by positivity), sqrt_rpow (by positivity),
          sqrt_rpow hδ]
        ring_nf

section CoreLemmas2
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- pointwise bound of term (I) of `lem:merge2` (in the `x` slot) after the restriction; the
event `E₁` of the source is replaced by the bound `𝟙[Stab > δ'] ≤ Stab/δ'`. -/
theorem mgenC_xx_pointwise (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) {M δ₀ η δ' ε : ℝ}
    (Hμ' : SStmtX (mergeDistX μ a) M δ₀ η) (hM : 0 ≤ M) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hδ'δ₀ : δ' ≤ δ₀) (hε0 : 0 < ε) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : (κ → X) → ℂ) (gt : (κ → Y) → ℂ) (ht : (κ → Z) → ℂ) (hu : ∀ x, ‖u x‖ ≤ 1)
    (hgt : ∀ y, ‖gt y‖ ≤ 1) (hht : ∀ z, ‖ht z‖ ≤ 1) :
    ‖corr3 μ u gt ht‖ ≤ (1 / (2 * ε)) *
        cl2sq (lawX μ) (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x) +
      0 * cl2sq (lawX μ) (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x) +
      (1 / δ') * (cstab (lawX μ) (1 - δ') u).re + (ε / 2 + M * δ' ^ η) := by
  set W := cl2sq (lawX μ) (fun x => u x - graphNoiseOp (lawX μ) (mgenComp μ) 1 u x) with hW
  set S := (cstab (lawX μ) (1 - δ') u).re with hS
  set U : (κ → ↥(Set.range a)) → ℂ :=
    fun y => graphNoiseOp (lawX μ) (mgenComp μ) 1 u (fun i => (y i).val) with hU
  have h1 : ‖corr3 μ u gt ht‖ ≤ Real.sqrt W + ‖corr3 (mergeDistX μ a) U gt ht‖ :=
    corr3_split_merge μ a ha u gt ht hgt hht
  have hW0 : 0 ≤ W := cl2sq_nonneg _ _
  have hS0 : 0 ≤ S := cstab_re_nonneg _ (by linarith) _
  have hP0 : 0 ≤ M * δ' ^ η := mul_nonneg hM (Real.rpow_nonneg hδ'0.le _)
  have h2 : Real.sqrt W ≤ (W / ε + ε) / 2 := sqrt_le_amgm hW0 hε0
  have hUb : ∀ y, ‖U y‖ ≤ 1 := fun y => mgenC_gn_bounded _ _ zero_le_one le_rfl u hu _
  have h3 : ‖corr3 (mergeDistX μ a) U gt ht‖ ≤ M * δ' ^ η + (1 / δ') * S := by
    have hSd0 : 0 ≤ (1 / δ') * S := by positivity
    by_cases hSd : S ≤ δ'
    · have h4 := cstab_merge_le μ a ha (ρ := 1 - δ') (by linarith) (by linarith) u
      have h5 := sStmtX_gen Hμ' hδ'0 hδ'δ₀ U gt ht hUb hgt hht (h4.trans hSd)
      linarith
    · push Not at hSd
      have h4 := corr3_sq_le_cl2sq (mergeDistX μ a) U gt ht hgt hht
      have h5 : ‖corr3 (mergeDistX μ a) U gt ht‖ ≤ 1 := by
        have h6 := h4.trans (mgenC_cl2sq_le_one _ U hUb)
        nlinarith [norm_nonneg (corr3 (mergeDistX μ a) U gt ht)]
      have h6 : 1 ≤ (1 / δ') * S := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ'0]
        linarith
      linarith
  have e1 : (W / ε + ε) / 2 = (1 / (2 * ε)) * W + ε / 2 := by field_simp
  linarith

end CoreLemmas2

theorem mgenC_xx_params {Wc K δ₂ δ ε s : ℝ} {d : ℕ} (hW0 : 0 < Wc) (hK0 : 0 < K)
    (hδ₂0 : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hδq : δ ≤ (δ₂ / (K * (Wc + 1))) ^ 6) (hε : ε = δ ^ (1 / (12 : ℕ) : ℝ))
    (hd : d = ⌈Wc / Real.sqrt δ⌉₊) (hs : s = δ ^ (1 / 3 : ℝ) / d) :
    0 < ε ∧ ε ≤ 1 ∧ δ ^ (1 / 2 : ℝ) = ε ^ 6 ∧ 1 ≤ d ∧ 0 < s ∧ s ≤ 1 ∧ 0 < K * δ / s ∧
      K * δ / s ≤ δ₂ ∧ K * δ ≤ s ∧ K * δ / s ≤ K * (Wc + 1) * ε ^ 2 ∧
      δ / (K * δ / s) ≤ ε / K ∧ Real.log (1 / δ) * δ ^ (1 / 3 : ℝ) ≤ 12 * ε ^ 3 := by
  have hδ1' : δ < 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; exact Real.rpow_pos_of_pos hδ _
  have hε1 : ε ≤ 1 := by rw [hε]; exact Real.rpow_le_one hδ.le hδ1'.le (by norm_num)
  have hε12 : ε ^ 12 = δ := by rw [hε, mgenC_rpow_inv_pow hδ.le]; norm_num
  have hε6 : δ ^ (1 / 2 : ℝ) = ε ^ 6 := by rw [hε, mgenC_rpow_inv_pow hδ.le]; norm_num
  have hε4 : δ ^ (1 / 3 : ℝ) = ε ^ 4 := by rw [hε, mgenC_rpow_inv_pow hδ.le]; norm_num
  have hsq : Real.sqrt δ = ε ^ 6 := by rw [Real.sqrt_eq_rpow, hε6]
  have hε6pos : 0 < ε ^ 6 := by positivity
  have hd_pos : (0 : ℝ) < d := by
    rw [hd]
    have : 0 < Wc / Real.sqrt δ := by rw [hsq]; positivity
    exact_mod_cast Nat.ceil_pos.2 this
  have hd1 : 1 ≤ d := by
    have : 0 < d := by exact_mod_cast hd_pos
    omega
  have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hd_up : (d : ℝ) ≤ (Wc + 1) / ε ^ 6 := by
    have h1 : (d : ℝ) < Wc / Real.sqrt δ + 1 := by
      rw [hd]; exact Nat.ceil_lt_add_one (by rw [hsq]; positivity)
    have h3 : (1 : ℝ) ≤ 1 / ε ^ 6 := by
      rw [le_div_iff₀ hε6pos, one_mul]
      exact pow_le_one₀ hε0.le hε1
    have h4 : (Wc + 1) / ε ^ 6 = Wc / ε ^ 6 + 1 / ε ^ 6 := by field_simp
    rw [hsq] at h1
    rw [h4]
    linarith
  have hs' : s = ε ^ 4 / d := by rw [hs, hε4]
  have hs0 : 0 < s := by rw [hs']; positivity
  have hε4le : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hs1 : s ≤ 1 := by
    rw [hs', div_le_one hd_pos]
    linarith
  have hδ'eq : K * δ / s = K * d * ε ^ 8 := by
    rw [hs', ← hε12]
    field_simp
  have hδ'le : K * δ / s ≤ K * (Wc + 1) * ε ^ 2 := by
    rw [hδ'eq]
    have := mul_le_mul_of_nonneg_left hd_up (show 0 ≤ K * ε ^ 8 by positivity)
    calc K * d * ε ^ 8 = K * ε ^ 8 * d := by ring
      _ ≤ K * ε ^ 8 * ((Wc + 1) / ε ^ 6) := this
      _ = K * (Wc + 1) * ε ^ 2 := by field_simp
  have hε2le : ε ^ 2 ≤ δ₂ / (K * (Wc + 1)) := by
    have h1 : (ε ^ 2) ^ 6 ≤ (δ₂ / (K * (Wc + 1))) ^ 6 := by
      rw [← pow_mul]; norm_num; rw [hε12]; exact hδq
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
  have hδ'δ₂ : K * δ / s ≤ δ₂ := by
    calc K * δ / s ≤ K * (Wc + 1) * ε ^ 2 := hδ'le
      _ ≤ K * (Wc + 1) * (δ₂ / (K * (Wc + 1))) :=
          mul_le_mul_of_nonneg_left hε2le (by positivity)
      _ = δ₂ := by field_simp
  have hKδ : K * δ ≤ s := by
    have h : K * δ / s ≤ 1 := hδ'δ₂.trans hδ₂1
    rwa [div_le_one hs0] at h
  have hδK : δ / (K * δ / s) ≤ ε / K := by
    have e : δ / (K * δ / s) = s / K := by field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hK0.le
    rw [hs', div_le_iff₀ hd_pos]
    have : ε ^ 4 ≤ ε := by
      have : ε ^ 3 ≤ 1 := pow_le_one₀ hε0.le hε1
      nlinarith
    nlinarith
  have hlog : Real.log (1 / δ) ≤ 12 / ε := by
    have := log_le_inv_rpow hδ (k := 12) (by norm_num)
    rw [hε]
    push_cast
    exact this
  have hlogb : Real.log (1 / δ) * δ ^ (1 / 3 : ℝ) ≤ 12 * ε ^ 3 := by
    rw [hε4]
    calc Real.log (1 / δ) * ε ^ 4 ≤ 12 / ε * ε ^ 4 :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = 12 * ε ^ 3 := by field_simp
  exact ⟨hε0, hε1, hε6, hd1, hs0, hs1, by positivity, hδ'δ₂, hKδ, hδ'le, hδK, hlogb⟩

theorem mgenC_xx_final {ε P B K δ δ' θ jW jS : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK0 : 0 < K)
    (hδ'0 : 0 < δ') (hjW : jW ≤ 12 * ε ^ 3) (hjS : jS ≤ δ) (hδK : δ / δ' ≤ ε / K)
    (hP : P ≤ B * θ) (hθ : ε ≤ θ) :
    (1 / (2 * ε)) * jW + 0 * jW + (1 / δ') * jS + (ε / 2 + P) + ε ^ 3 ≤ (8 + 1 / K + B) * θ := by
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε := by nlinarith
  have hc1 : (1 / (2 * ε)) * jW ≤ 6 * ε := by
    have : (1 / (2 * ε)) * jW ≤ (1 / (2 * ε)) * (12 * ε ^ 3) :=
      mul_le_mul_of_nonneg_left hjW (by positivity)
    have e : (1 / (2 * ε)) * (12 * ε ^ 3) = 6 * ε ^ 2 := by field_simp; ring
    linarith
  have hc3 : (1 / δ') * jS ≤ ε / K := by
    have : (1 / δ') * jS ≤ (1 / δ') * δ := mul_le_mul_of_nonneg_left hjS (by positivity)
    have e : (1 / δ') * δ = δ / δ' := by ring
    linarith
  have h1 : ε / K ≤ (1 / K) * θ := by
    rw [div_eq_mul_one_div ε K, mul_comm]
    exact mul_le_mul_of_nonneg_left hθ (by positivity)
  have hθ0 : 0 ≤ θ := hε0.le.trans hθ
  linarith

theorem mgenC_rpow_P_le {M K C δ δ' ε η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hδ'0 : 0 ≤ δ') (hη : 0 ≤ η) (hδ'le : δ' ≤ K * C * ε ^ 2)
    (hε2 : ε ^ 2 = δ ^ (1 / 6 : ℝ)) :
    M * δ' ^ η ≤ M * (K * C) ^ η * δ ^ (η / 6) := by
  have h1 : δ' ^ η ≤ (K * C) ^ η * δ ^ (η / 6) := by
    calc δ' ^ η ≤ (K * C * ε ^ 2) ^ η := Real.rpow_le_rpow hδ'0 hδ'le hη
      _ = (K * C) ^ η * (ε ^ 2) ^ η := Real.mul_rpow (by positivity) (by positivity)
      _ = (K * C) ^ η * δ ^ (η / 6) := by
          rw [hε2, ← Real.rpow_mul hδ]
          congr 2
          ring
  calc M * δ' ^ η ≤ M * ((K * C) ^ η * δ ^ (η / 6)) := mul_le_mul_of_nonneg_left h1 hM
    _ = M * (K * C) ^ η * δ ^ (η / 6) := by ring

end MaxT
end TrackB
end RestrictedPolynomials
end
