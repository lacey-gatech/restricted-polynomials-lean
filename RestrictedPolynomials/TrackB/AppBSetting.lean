module

public import RestrictedPolynomials.TrackB.S7Beta
public import RestrictedPolynomials.TrackB.MaxTSec6Relaxed65
public import RestrictedPolynomials.TrackB.NoiseClaims
public import RestrictedPolynomials.TrackB.Restrict

/-!
# Track B, Appendix B: the setting on `𝒯`

Paper IV Appendix B (l. 8903-9388) at the trivial embedding group
(Supplement E §proof67). Everything is stated at `H = {0}`: the non-embedding noise
operator is `nonEmbedOp D (fun _ => ()) ξ` (the ordinary noise operator, built
`nestab_trivial_master`), `E_{non-embed}` is the built `s7EffNoiseOp`.

All proof helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Defs

/-- `T_{non-embed,1-ξ}` at the trivial master embedding: stay with probability `1 - ξ`. -/
def tNE {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (ξ : ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : (ι → A) → ℂ) : (ι → A) → ℂ :=
  nonEmbedOp D (fun _ : A => ()) ξ f

/-- `T' g = (T_{non-embed,1-ρ/2} - T_{non-embed,1-ρ}) g` (l. 8962, with `ρ = 2^{-j}δ = 1 - ρ_j`;
the source's "ρ = ρ_j" at l. 8963 is read `ρ = 1 - ρ_j`, in `soft-truncate-main`). -/
def appTp {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (ρ : ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (g : (ι → A) → ℂ) : (ι → A) → ℂ :=
  tNE D (ρ / 2) g - tNE D ρ g

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the witness of hypothesis 6b of Thm 6.7′ (`Γ' = Γ` by item 9, `ν̃ ∈ 𝒯` by item 8, `ν̃`
`P`-maximal by 6b(iii)′): exactly the existential of `h67`. -/
def Rel67Wit (K : ℕ) (ν : FinProb (X × Y × Z)) (Sg : Finset X) (Phi' : Finset Z) : Prop :=
  ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (a : U → X) (νt : FinProb (U × Y × ↥Phi')),
    Fintype.card U ≤ K ∧ (∀ u, a u ∈ Sg) ∧ (∀ x ∈ Sg, ∃ u, a u = x) ∧
    (∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support) ∧ PMaxSet νt.support ∧
    FullyMergedSet νt.support ∧ 2 ≤ Fintype.card Y ∧ InT νt.support

/-- the hypotheses 1, 3+4, 5, 6 (without the gain constants of 6a), 7 of Thm 6.7′ on `ν`
(the alphabet bound `m` is a separate binder). `two` is the first clause of the relaxed base case;
`(c, C)` of 6a are NOT part of this bundle, so constants of Claims soft_trunc1/2 do not depend on
them. -/
structure Rel67 (K : ℕ) (α : ℝ) (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z) :
    Prop where
  atoms : ∀ p ∈ ν.support, α ≤ ν.prob p
  inT : InT ν.support
  yz_full : ∀ (y : Y) (z : Z), ∃ x, (x, y, z) ∈ ν.support
  yz_unif : ∀ (y : Y) (z : Z),
    ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)
  sub : Sm ⊆ Sg
  two : 2 ≤ Sm.card
  wit : Rel67Wit K ν Sg Phi'
  xy_full : ∀ x ∈ Sg, ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support
  merge : mergeImpliesX ν.support

/-- term (I) of eq. `trunate5`. -/
def termI {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z)) (ρ ξ : ℝ)
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) : ℝ :=
  ‖corr3 ν (f - tNE (lawX ν) (ρ ^ (1 + ξ)) f) (appTp (lawY ν) ρ g) h‖

/-- term (V) of eq. `trunate6`: `f' = T_{non-embed,1-ρ^{1+ξ}} f`, `Sm = Σ_modest`. -/
def termV {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z)) (Sm : Finset X)
    (ρ ξ : ℝ) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) : ℝ :=
  ‖corr3 ν (s7EffNoiseOp (lawX ν) Sm (ρ ^ (1 - ξ)) (tNE (lawX ν) (ρ ^ (1 + ξ)) f))
    (appTp (lawY ν) ρ g) h‖

/-- term (VI) of eq. `trunate6`. -/
def termVI {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z)) (Sm : Finset X)
    (ρ ξ : ℝ) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) : ℝ :=
  ‖corr3 ν (tNE (lawX ν) (ρ ^ (1 + ξ)) f -
      s7EffNoiseOp (lawX ν) Sm (ρ ^ (1 - ξ)) (tNE (lawX ν) (ρ ^ (1 + ξ)) f))
    (appTp (lawY ν) ρ g) h‖

/-- `R_III` of Supplement E (reading (6.1)): `{(x,y,z) ∈ N_y : x ∈ Σ', z ∈ Φ'}`, `Γ' = Γ`. -/
def rIII (ν : FinProb (X × Y × Z)) (Sg : Finset X) (Phi' : Finset Z) : Set (X × Y × Z) :=
  {p | p.1 ∈ Sg ∧ p.2.2 ∈ Phi' ∧ ∃ y0, (p.1, y0, p.2.2) ∈ ν.support}

/-- `Mod(x)` of the modest chain's support. -/
def modOf (Sm : Finset X) (x : X) : Set X := if x ∈ Sm then ↑Sm else {x}

/-- `R_VII` of Lemma `lem:VII-prime` (`y` unrestricted). -/
def rVII (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z) : Set (X × Y × Z) :=
  {p | p.1 ∈ Sg ∧ p.2.2 ∈ Phi' ∧ ∃ x, (x, p.2.1, p.2.2) ∈ ν.support ∧ p.1 ∈ modOf Sm x}

/-- the pull-back of a set along `a × id × val`. -/
def liftSet {U : Type} {Phi' : Finset Z} (a : U → X) (R : Set (X × Y × Z)) :
    Set (U × Y × ↥Phi') :=
  {q | (a q.1, q.2.1, q.2.2.1) ∈ R}

end Defs

section Targets
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem finProb_ext {A : Type} [Fintype A] {P Q : FinProb A}
    (h : ∀ a, P.prob a = Q.prob a) : P = Q := by
  cases P; cases Q
  congr
  exact funext h

/-! ### linearity and the identity `T_{non-embed} = cnoiseOp` -/

theorem tNE_eq_cnoiseOp {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (ξ : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → A) → ℂ) :
    tNE D ξ f = cnoiseOp D (1 - ξ) f := by
  funext x
  unfold tNE nonEmbedOp graphNoiseOp cnoiseOp
  refine Finset.sum_congr rfl fun y _ => ?_
  have hk : ∀ a b : A, nonEmbedKernel D (fun _ : A => ()) ξ a b = noiseKernel D (1 - ξ) a b := by
    intro a b
    unfold nonEmbedKernel graphNoiseKernel noiseKernel
    have h2 : ∑ c : A, D.prob c = 1 := D.sum_eq_one
    beta_reduce
    simp [h2]
  have : (∏ i, graphNoiseKernel D (fun a b => (fun _ : A => ()) a = (fun _ : A => ()) b) ξ
      (x i) (y i)) = ∏ i, noiseKernel D (1 - ξ) (x i) (y i) :=
    Finset.prod_congr rfl fun i _ => by
      have := hk (x i) (y i)
      unfold nonEmbedKernel at this
      exact this
  rw [this]

theorem corr3_sub_left {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (f f' : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν (f - f') g h = corr3 ν f g h - corr3 ν f' g h := by
  unfold corr3 FinProb.cexpect
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem corr3_sub_mid {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (f : (ι → X) → ℂ) (g g' : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν f (g - g') h = corr3 ν f g h - corr3 ν f g' h := by
  unfold corr3 FinProb.cexpect
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.sub_apply]
  ring

private theorem noisyMid_exists (ν : FinProb (X × Y × Z)) (K : Y → Y → ℝ)
    (hK0 : ∀ a b, 0 ≤ K a b) (hK1 : ∀ a, ∑ b, K a b = 1) :
    ∃ μ' : FinProb (X × Y × Z),
      (∀ p, μ'.prob p = ∑ y', ν.prob (p.1, y', p.2.2) * K y' p.2.1) ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ), corr3 ν f (s7KernelOp K g) h = corr3 μ' f g h := by
  refine ⟨⟨fun p => ∑ y', ν.prob (p.1, y', p.2.2) * K y' p.2.1, ?_, ?_⟩, fun p => rfl, ?_⟩
  · intro p
    exact Finset.sum_nonneg fun y' _ => mul_nonneg (ν.nonneg _) (hK0 _ _)
  · have h1 : ∀ x : X, ∑ y : Y, ∑ z : Z, ∑ y' : Y, ν.prob (x, y', z) * K y' y =
        ∑ z : Z, ∑ y' : Y, ν.prob (x, y', z) := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y' _ => ?_
      rw [← Finset.mul_sum, hK1, mul_one]
    have h2 : ∑ p : X × Y × Z, ν.prob p = ∑ x : X, ∑ z : Z, ∑ y' : Y, ν.prob (x, y', z) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type] at h2
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← h2]
    have := ν.sum_eq_one
    simpa only [Fintype.sum_prod_type] using this
  · intro ι _ _ f g h
    -- swap the `y`-components of the two summation variables
    let sw : (ι → X × Y × Z) × (ι → Y) → (ι → X × Y × Z) × (ι → Y) := fun q =>
      (fun i => ((q.1 i).1, q.2 i, (q.1 i).2.2), fun i => (q.1 i).2.1)
    have hsw : Function.Involutive sw := fun q => by
      simp only [sw]
    have hexp : ∀ t' : ι → X × Y × Z,
        ∏ i, (∑ y', ν.prob ((t' i).1, y', (t' i).2.2) * K y' (t' i).2.1) =
        ∑ s : ι → Y, ∏ i, ν.prob ((t' i).1, s i, (t' i).2.2) * K (s i) (t' i).2.1 :=
      fun t' => Fintype.prod_sum (fun i y' => ν.prob ((t' i).1, y', (t' i).2.2) * K y' (t' i).2.1)
    unfold corr3 FinProb.cexpect
    simp only [FinProb.pi]
    simp only [hexp]
    push_cast
    simp only [Finset.sum_mul]
    have hL : ∀ t : ι → X × Y × Z,
        (∏ i, (ν.prob (t i) : ℂ)) * (((f fun i => (t i).1) *
          s7KernelOp K g fun i => (t i).2.1) * h fun i => (t i).2.2) =
        ∑ w : ι → Y, (∏ i, (ν.prob (t i) : ℂ)) * (((f fun i => (t i).1) *
          (((∏ i, K ((t i).2.1) (w i) : ℝ) : ℂ) * g w)) * h fun i => (t i).2.2) := by
      intro t
      unfold s7KernelOp
      simp only [Finset.mul_sum, Finset.sum_mul]
    simp only [hL]
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine (Equiv.sum_comp (Function.Involutive.toPerm sw hsw) _).symm.trans ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Function.Involutive.coe_toPerm, sw]
    push_cast
    simp only [Finset.prod_mul_distrib]
    ring

private theorem neK_formula {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (ξ : ℝ)
    (a b : A) : nonEmbedKernel D (fun _ : A => ()) ξ a b =
      (1 - ξ) * (if a = b then 1 else 0) + ξ * D.prob b := by
  unfold nonEmbedKernel graphNoiseKernel
  have h2 : ∑ c : A, D.prob c = 1 := D.sum_eq_one
  beta_reduce
  simp [h2]

private theorem neK_nonneg {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {ξ : ℝ}
    (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (a b : A) : 0 ≤ nonEmbedKernel D (fun _ : A => ()) ξ a b := by
  rw [neK_formula]
  have := D.nonneg b
  have h3 : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
  have h4 : 0 ≤ 1 - ξ := by linarith
  positivity

private theorem neK_row {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (ξ : ℝ) (a : A) :
    ∑ b, nonEmbedKernel D (fun _ : A => ()) ξ a b = 1 := by
  simp only [neK_formula, Finset.sum_add_distrib, ← Finset.mul_sum, D.sum_eq_one]
  simp

/-- `E_{ν}[f(x) (T_{non-embed,1-ξ} g)(y) h(z)] = E_{μ'}[f g h]`, `μ'` the noisy law of l. 8987
(sample `(x',y',z') ∼ ν`, then `y ∼ T_{non-embed,1-ξ} y'`; the noise acts on `y`). -/
theorem appB_noisyY_law_exists (ν : FinProb (X × Y × Z)) {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) :
    ∃ μ' : FinProb (X × Y × Z),
      (∀ p, μ'.prob p = ∑ y', ν.prob (p.1, y', p.2.2) *
        nonEmbedKernel (lawY ν) (fun _ : Y => ()) ξ y' p.2.1) ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ), corr3 ν f (tNE (lawY ν) ξ g) h = corr3 μ' f g h := by
  obtain ⟨μ', hμ, hc⟩ := noisyMid_exists ν (nonEmbedKernel (lawY ν) (fun _ : Y => ()) ξ)
    (neK_nonneg (lawY ν) h0 h1) (neK_row (lawY ν) ξ)
  exact ⟨μ', hμ, fun f g h => hc f g h⟩

private theorem effK_nonneg {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    (Sm : Finset A) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a b : A) : 0 ≤ s7EffKernel D Sm δ a b := by
  unfold s7EffKernel s7ModestKernel
  have hb := D.nonneg b
  have h3 : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
  have h4 : 0 ≤ 1 - δ := by linarith
  have h5 : 0 ≤ ∑ c ∈ Sm, D.prob c := Finset.sum_nonneg fun c _ => D.nonneg c
  have h6 : (0 : ℝ) ≤ if a ∈ Sm then (if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0)
      else (if a = b then 1 else 0) := by
    split_ifs <;> first | positivity | norm_num
  positivity

private theorem effK_row {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (Sm : Finset A)
    (hS : 0 < ∑ c ∈ Sm, D.prob c) (δ : ℝ) (a : A) : ∑ b, s7EffKernel D Sm δ a b = 1 := by
  have hm : ∑ b, s7ModestKernel D Sm a b = 1 := by
    unfold s7ModestKernel
    by_cases ha : a ∈ Sm
    · simp only [ha, ite_true]
      rw [show (∑ b, if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0) =
        ∑ b ∈ Sm, D.prob b / ∑ c ∈ Sm, D.prob c by
          rw [Finset.sum_ite_mem, Finset.univ_inter]]
      rw [← Finset.sum_div, div_self hS.ne']
    · simp [ha]
  unfold s7EffKernel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
  simp

/-- the same for the noise on `x` (l. 9115, term (V)): `E_ν[(E_{non-embed,1-δ'} f)(x) g h] = E_{μ'}`.
The kernel is the modest chain `s7EffKernel`. -/
theorem appB_noisyX_law_exists (ν : FinProb (X × Y × Z)) (Sm : Finset X) {δ' : ℝ}
    (hSm : 0 < ∑ x ∈ Sm, (lawX ν).prob x) (h0 : 0 ≤ δ') (h1 : δ' ≤ 1) :
    ∃ μ' : FinProb (X × Y × Z),
      (∀ p, μ'.prob p = ∑ x', ν.prob (x', p.2.1, p.2.2) * s7EffKernel (lawX ν) Sm δ' x' p.1) ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ),
        corr3 ν (s7EffNoiseOp (lawX ν) Sm δ' f) g h = corr3 μ' f g h := by
  obtain ⟨μs, hμs, hc⟩ := noisyMid_exists (X := Y) (Y := X) (Z := Z) (lawSwapXY ν)
    (s7EffKernel (lawX ν) Sm δ') (effK_nonneg (lawX ν) Sm h0 h1) (effK_row (lawX ν) Sm hSm δ')
  refine ⟨lawSwapXY μs, fun p => ?_, fun f g h => ?_⟩
  · obtain ⟨x, y, z⟩ := p
    show (lawSwapXY μs).prob (x, y, z) = _
    rw [lawSwapXY_prob μs y x z, hμs]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only
    rw [lawSwapXY_prob ν x' y z]
  · have := hc g f h
    rw [corr3_lawSwapXY] at this
    rw [corr3_lawSwapXY μs g f h]
    exact this

/-! ### uniform maximality constants (Remark `rmk:finite`) -/

private theorem pmax_bound_mono {c M M' δ η η' : ℝ} (hM : 0 ≤ M) (hMM : M ≤ M') (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hηη : η' ≤ η) (h : c ≤ M * δ ^ η) : c ≤ M' * δ ^ η' := by
  have h1 : δ ^ η ≤ δ ^ η' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηη
  have h2 : 0 ≤ δ ^ η' := (Real.rpow_pos_of_pos hδ η').le
  calc c ≤ M * δ ^ η := h
    _ ≤ M * δ ^ η' := mul_le_mul_of_nonneg_left h1 hM
    _ ≤ M' * δ ^ η' := mul_le_mul_of_nonneg_right hMM h2

private theorem pmax_sStmtX_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtX μ M δ₀ η) :
    SStmtX μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact pmax_bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem pmax_sStmtY_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtY μ M δ₀ η) :
    SStmtY μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact pmax_bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem pmax_sStmtZ_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtZ μ M δ₀ η) :
    SStmtZ μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact pmax_bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem pmax_pStmt_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : PStmt μ M δ₀ η) :
    PStmt μ M' δ₀' η' :=
  ⟨pmax_sStmtX_mono hM hMM hδ hδ1 hηη H.1, pmax_sStmtY_mono hM hMM hδ hδ1 hηη H.2.1,
    pmax_sStmtZ_mono hM hMM hδ hδ1 hηη H.2.2⟩

private theorem pmax_inv_bound {d B : ℝ} (hd : 0 < d) (h : 1 / d ≤ B) : 1 / max B 1 ≤ d := by
  have hpos : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [div_le_iff₀ hpos]
  have h1 : 1 / d ≤ max B 1 := h.trans (le_max_left _ _)
  have := (div_le_iff₀ hd).1 h1
  linarith

/-- the finiteness argument of `rel65_uniform_supersets`, over all patterns on `Fin a × Fin b × Fin c` -/
private theorem pmax_canonical (a b c : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      ∀ T : Set (Fin a × Fin b × Fin c), QSet T → ∀ D : FinProb (Fin a × Fin b × Fin c),
        D.support = T → (∀ p ∈ D.support, α ≤ D.prob p) → PStmt D M δ₀ η := by
  have hex : ∀ T : Set (Fin a × Fin b × Fin c), ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      (QSet T → ∀ D : FinProb (Fin a × Fin b × Fin c), D.support = T →
        (∀ p ∈ D.support, α ≤ D.prob p) → PStmt D M δ₀ η) := by
    intro T
    by_cases hT : QSet T
    · obtain ⟨M1, δ1, η1, h11, h12, h13, h14, H1⟩ := hT.1 α hα
      obtain ⟨M2, δ2, η2, h21, h22, h23, h24, H2⟩ := hT.2.1 α hα
      obtain ⟨M3, δ3, η3, h31, h32, h33, h34, H3⟩ := hT.2.2 α hα
      refine ⟨max M1 (max M2 M3), min δ1 (min δ2 δ3), min η1 (min η2 η3),
        le_max_of_le_left h11, lt_min h12 (lt_min h22 h32), (min_le_left _ _).trans h13,
        lt_min h14 (lt_min h24 h34), fun _ D hD hat => ⟨?_, ?_, ?_⟩⟩
      · exact pmax_sStmtX_mono h11 (le_max_left _ _) (min_le_left _ _) h13 (min_le_left _ _)
          (H1 D hD hat)
      · exact pmax_sStmtY_mono h21 (le_max_of_le_right (le_max_left _ _))
          ((min_le_right _ _).trans (min_le_left _ _)) h23
          ((min_le_right _ _).trans (min_le_left _ _)) (H2 D hD hat)
      · exact pmax_sStmtZ_mono h31 (le_max_of_le_right (le_max_right _ _))
          ((min_le_right _ _).trans (min_le_right _ _)) h33
          ((min_le_right _ _).trans (min_le_right _ _)) (H3 D hD hat)
    · exact ⟨1, 1, 1, le_rfl, one_pos, le_rfl, one_pos, fun h => absurd h hT⟩
  choose Mf δf ηf hM hδ hδ1 hη hQ using hex
  obtain ⟨BM, hBM⟩ := Finite.bddAbove_range Mf
  obtain ⟨Bδ, hBδ⟩ := Finite.bddAbove_range (fun i => 1 / δf i)
  obtain ⟨Bη, hBη⟩ := Finite.bddAbove_range (fun i => 1 / ηf i)
  have hposδ : 0 < max Bδ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hposη : 0 < max Bη 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max BM 1, 1 / max Bδ 1, 1 / max Bη 1, le_max_right _ _, one_div_pos.2 hposδ,
    (div_le_one hposδ).2 (le_max_right _ _), one_div_pos.2 hposη, ?_⟩
  intro T hT D hD hat
  exact pmax_pStmt_mono (hM T) (le_max_of_le_left (hBM (Set.mem_range_self T)))
    (pmax_inv_bound (hδ T) (hBδ (Set.mem_range_self T))) (hδ1 T)
    (pmax_inv_bound (hη T) (hBη (Set.mem_range_self T))) (hQ T hT D hD hat)

/-- `P`-maximality gives `P(D; M, δ₀, η)` for every strict enlargement, with constants uniform over
all `P`-maximal patterns on alphabets of size `≤ m` (finitely many up to relabelling:
`pMaxSet_relabelSet_iff`, `qSet_relabelSet_iff`, `sStmt*_iff_relabel`). Not an assumption: the
proof is the finiteness argument of `rel65_uniform_supersets`, over patterns. -/
theorem pmax_uniform_constants (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ S : Set (X × Y × Z), PMaxSet S → ∀ D : FinProb (X × Y × Z), S ⊂ D.support →
          (∀ p ∈ D.support, α ≤ D.prob p) → PStmt D M δ₀ η := by
  have hc := fun t : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) =>
    pmax_canonical (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ) hα
  choose Mf δf ηf hM hδ hδ1 hη hQ using hc
  obtain ⟨BM, hBM⟩ := Finite.bddAbove_range Mf
  obtain ⟨Bδ, hBδ⟩ := Finite.bddAbove_range (fun i => 1 / δf i)
  obtain ⟨Bη, hBη⟩ := Finite.bddAbove_range (fun i => 1 / ηf i)
  have hposδ : 0 < max Bδ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hposη : 0 < max Bη 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max BM 1, 1 / max Bδ 1, 1 / max Bη 1, le_max_right _ _, one_div_pos.2 hposδ,
    (div_le_one hposδ).2 (le_max_right _ _), one_div_pos.2 hposη, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ S hS D hSD hat
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let eY : Y ≃ Fin (Fintype.card Y) := Fintype.equivFin Y
  let eZ : Z ≃ Fin (Fintype.card Z) := Fintype.equivFin Z
  let t : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) :=
    (⟨Fintype.card X, Nat.lt_succ_of_le hX⟩, ⟨Fintype.card Y, Nat.lt_succ_of_le hY⟩,
      ⟨Fintype.card Z, Nat.lt_succ_of_le hZ⟩)
  have hQD : QSet D.support := hS D.support hSD
  have hsupp : (lawRelabel eX eY eZ D).support = relabelSet eX eY eZ D.support :=
    lawRelabel_support eX eY eZ D
  have hQD' : QSet (lawRelabel eX eY eZ D).support := by
    rw [hsupp]
    exact (qSet_relabelSet_iff eX eY eZ D.support).2 hQD
  have hat' : ∀ p ∈ (lawRelabel eX eY eZ D).support, α ≤ (lawRelabel eX eY eZ D).prob p := by
    intro p hp
    rw [hsupp] at hp
    obtain ⟨⟨x, y, z⟩, hxyz, rfl⟩ := hp
    rw [lawRelabel_prob]
    exact hat _ hxyz
  have hP' : PStmt (lawRelabel eX eY eZ D) (Mf t) (δf t) (ηf t) :=
    hQ t _ hQD' _ rfl hat'
  have hP'' : PStmt (lawRelabel eX eY eZ D) (max BM 1) (1 / max Bδ 1) (1 / max Bη 1) :=
    pmax_pStmt_mono (hM t) (le_max_of_le_left (hBM (Set.mem_range_self t)))
    (pmax_inv_bound (hδ t) (hBδ (Set.mem_range_self t))) (hδ1 t)
    (pmax_inv_bound (hη t) (hBη (Set.mem_range_self t))) hP'
  exact (pStmt_relabel_iff eX eY eZ D _ _ _).1 hP''

/-! ### the lift along `a⁻¹` (l. 9065-9071, 9189-9196) -/

/-- the law of `(x'', y, z)`, `(x', y, z) ∼ μ''`, `x''` uniform on `a⁻¹(x')`, exists when the
`x`-support of `μ''` lies in the range of `a`; its atoms are `≥ (min atom of μ'')/|U|`. -/
theorem appB_lift_exists {U : Type} [Fintype U] [DecidableEq U] (a : U → X)
    {Phi' : Finset Z} (μ'' : FinProb (X × Y × Z))
    (hs : ∀ p ∈ μ''.support, ∃ u, a u = p.1) (hz : ∀ p ∈ μ''.support, p.2.2 ∈ Phi') :
    ∃ ν' : FinProb (U × Y × ↥Phi'),
      (∀ (u : U) (y : Y) (z : ↥Phi'), ν'.prob (u, y, z) =
        μ''.prob (a u, y, z.1) /
          (Finset.univ.filter (fun u' => a u' = a u)).card) ∧
      ν'.support = liftSet a μ''.support ∧
      (∀ (D : ℝ), (∀ p ∈ μ''.support, D ≤ μ''.prob p) →
        ∀ q ∈ ν'.support, D / Fintype.card U ≤ ν'.prob q) := by
  classical
  have hfpos : ∀ u : U, 0 < (Finset.univ.filter (fun u' => a u' = a u)).card := fun u =>
    Finset.card_pos.2 ⟨u, by simp⟩
  have hout : ∀ (x : X) (y : Y) (z : Z), (¬ ∃ u, a u = x) ∨ z ∉ Phi' → μ''.prob (x, y, z) = 0 := by
    intro x y z hxz
    by_contra hne
    have hmem : (x, y, z) ∈ μ''.support := hne
    rcases hxz with hx | hz'
    · exact hx (hs _ hmem)
    · exact hz' (hz _ hmem)
  have hfix : ∀ (y : Y) (z : Z), ∑ u : U, μ''.prob (a u, y, z) /
      (Finset.univ.filter (fun u' => a u' = a u)).card = ∑ x : X, μ''.prob (x, y, z) := by
    intro y z
    rw [← Finset.sum_fiberwise Finset.univ a
      (fun u => μ''.prob (a u, y, z) / (Finset.univ.filter (fun u' => a u' = a u)).card)]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ∃ u, a u = x
    · obtain ⟨u0, hu0⟩ := hx
      have hS : (Finset.univ.filter (fun u' => a u' = x)).card ≠ 0 := by
        have := hfpos u0
        rw [hu0] at this
        exact this.ne'
      rw [Finset.sum_congr rfl (g := fun _ => μ''.prob (x, y, z) /
        (Finset.univ.filter (fun u' => a u' = x)).card)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hS)]
      · intro u hu
        have hau : a u = x := (Finset.mem_filter.1 hu).2
        rw [hau]
    · rw [hout x y z (Or.inl hx)]
      rw [Finset.sum_eq_zero]
      intro u hu
      exact absurd ⟨u, (Finset.mem_filter.1 hu).2⟩ hx
  refine ⟨⟨fun q => μ''.prob (a q.1, q.2.1, q.2.2.1) /
    (Finset.univ.filter (fun u' => a u' = a q.1)).card, ?_, ?_⟩, fun u y z => rfl, ?_, ?_⟩
  · intro q
    exact div_nonneg (μ''.nonneg _) (Nat.cast_nonneg _)
  · simp only [Fintype.sum_prod_type]
    have hA : ∀ (u : U) (y : Y), ∑ z : ↥Phi', μ''.prob (a u, y, z.1) /
        (Finset.univ.filter (fun u' => a u' = a u)).card =
        ∑ z : Z, μ''.prob (a u, y, z) / (Finset.univ.filter (fun u' => a u' = a u)).card := by
      intro u y
      rw [Finset.sum_coe_sort Phi' (fun z => μ''.prob (a u, y, z) /
        (Finset.univ.filter (fun u' => a u' = a u)).card)]
      refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz' => ?_
      rw [hout (a u) y z (Or.inr hz'), zero_div]
    simp only [hA]
    rw [Finset.sum_comm]
    have hB : ∀ y : Y, ∑ u : U, ∑ z : Z, μ''.prob (a u, y, z) /
        (Finset.univ.filter (fun u' => a u' = a u)).card =
        ∑ z : Z, ∑ x : X, μ''.prob (x, y, z) := by
      intro y
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => hfix y z
    simp only [hB]
    have h1 := μ''.sum_eq_one
    simp only [Fintype.sum_prod_type] at h1
    rw [Finset.sum_comm] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
  · ext q
    obtain ⟨u, y, z⟩ := q
    show _ ≠ 0 ↔ _
    have hp := hfpos u
    constructor
    · intro h h0
      exact h (by simp [h0])
    · intro h h0
      apply h
      rcases div_eq_zero_iff.1 h0 with h0 | h0
      · exact h0
      · exact absurd h0 (by exact_mod_cast hp.ne')
  · intro D hD q hq
    obtain ⟨u, y, z⟩ := q
    have hq' : μ''.prob (a u, y, z.1) ≠ 0 := by
      intro h0
      apply hq
      show _ / _ = _
      simp [h0]
    have hmem : (a u, y, z.1) ∈ μ''.support := hq'
    have hD' := hD _ hmem
    have hUpos : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
    have hfp : (0 : ℝ) < (Finset.univ.filter (fun u' => a u' = a u)).card := by
      exact_mod_cast hfpos u
    have hfle : ((Finset.univ.filter (fun u' => a u' = a u)).card : ℝ) ≤ Fintype.card U := by
      exact_mod_cast Finset.card_le_univ _
    show D / Fintype.card U ≤ μ''.prob (a u, y, z.1) /
      (Finset.univ.filter (fun u' => a u' = a u)).card
    by_cases hD0 : D ≤ 0
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg hD0 hUpos.le)
        (div_nonneg (μ''.nonneg _) hfp.le)
    · push Not at hD0
      calc D / Fintype.card U ≤ D / (Finset.univ.filter (fun u' => a u' = a u)).card :=
            div_le_div_of_nonneg_left hD0.le hfp hfle
        _ ≤ _ := div_le_div_of_nonneg_right hD' hfp.le

/-- (St4) for the lift: `Stab_ρ(f ∘ a^{⊗J}; (ν'_x)^J) = Stab_ρ(f; (μ''_x)^J)` (Lemma `lem:III-prime`(d),
`lem:VII-prime`(d); at `H = {0}` an equality, `nestab_trivial_master`). -/
theorem appB_lift_stab {U : Type} [Fintype U] [DecidableEq U] (a : U → X) {Phi' : Finset Z}
    (μ'' : FinProb (X × Y × Z)) (ν' : FinProb (U × Y × ↥Phi'))
    (hx : ∀ x, (lawX μ'').prob x = ∑ u ∈ Finset.univ.filter (fun u => a u = x),
      (lawX ν').prob u)
    {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (f : (ι → X) → ℂ) :
    cstab (lawX ν') ρ (fun w => f (fun i => a (w i))) = cstab (lawX μ'') ρ f := by
  rw [cstab_pushforward (lawX ν') a ρ f]
  have : mergePush (lawX ν') a = lawX μ'' :=
    finProb_ext fun x => (hx x).symm
  rw [this]

/-- same for the `y`-marginal (`ν'_y = μ''_y`, the lift keeps `y, z`). -/
theorem appB_lift_stab_y {U : Type} [Fintype U] [DecidableEq U] (a : U → X) {Phi' : Finset Z}
    (μ'' : FinProb (X × Y × Z)) (ν' : FinProb (U × Y × ↥Phi'))
    (hy : ∀ y, (lawY ν').prob y = (lawY μ'').prob y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (g : (ι → Y) → ℂ) :
    cstab (lawY ν') ρ g = cstab (lawY μ'') ρ g := by
  rw [finProb_ext hy]

/-- Lemma `lem:III-prime`(b), (c): `supp ν̃ ⊊ liftSet (R_III)` and it is in `𝒯`. Uses 6b(i), (ii),
(iv), (vi), item 8 and `Γ' = Γ`. -/
theorem appB_rIII_lift_props {ν : FinProb (X × Y × Z)} {Sg : Finset X}
    {Phi' : Finset Z} {U : Type} [Fintype U] [DecidableEq U]
    (a : U → X) (νt : FinProb (U × Y × ↥Phi')) (hsurj : ∀ u, a u ∈ Sg)
    (hsub : ∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support)
    (hfm : FullyMergedSet νt.support) (hY : 2 ≤ Fintype.card Y) (hT : InT νt.support) :
    νt.support ⊂ liftSet a (rIII ν Sg Phi') ∧ InT (liftSet (Phi' := Phi') a (rIII ν Sg Phi')) := by
  have hsubset : νt.support ⊆ liftSet a (rIII ν Sg Phi') := by
    intro q hq
    exact ⟨hsurj q.1, q.2.2.2, q.2.1, hsub q hq⟩
  refine ⟨⟨hsubset, fun hall => ?_⟩, hT.mono hsubset⟩
  obtain ⟨_, _, _, ⟨u, v, w⟩, hq⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hT.1
  obtain ⟨v', hv'⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  have hmem : (u, v', w) ∈ liftSet a (rIII ν Sg Phi') := ⟨hsurj u, w.2, v, hsub _ hq⟩
  have := hfm.2.1 u w v v' hq (hall hmem)
  exact hv' this.symm

/-- Lemma `lem:VII-prime`(b), (c): `supp ν̃ ⊊ liftSet (R_VII)` (uses `|Σ_modest| ≥ 2`, `a`
surjective onto `Σ'`, `y,z ⇒ x` in `ν̃`) and it is in `𝒯`. -/
theorem appB_rVII_lift_props (K : ℕ) {α : ℝ} {ν : FinProb (X × Y × Z)} {Sg Sm : Finset X}
    {Phi' : Finset Z} (hR : Rel67 K α ν Sg Sm Phi') {U : Type} [Fintype U] [DecidableEq U]
    (a : U → X) (νt : FinProb (U × Y × ↥Phi')) (hsurj : ∀ u, a u ∈ Sg)
    (hsurj' : ∀ x ∈ Sg, ∃ u, a u = x)
    (hsub : ∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support)
    (hfm : FullyMergedSet νt.support) (hT : InT νt.support) :
    νt.support ⊂ liftSet a (rVII ν Sg Sm Phi') ∧
      InT (liftSet (Phi' := Phi') a (rVII ν Sg Sm Phi')) := by
  have hmod : ∀ x : X, x ∈ modOf Sm x := fun x => by
    unfold modOf
    split_ifs with h
    · exact h
    · exact rfl
  have hsubset : νt.support ⊆ liftSet a (rVII ν Sg Sm Phi') := by
    intro q hq
    exact ⟨hsurj q.1, q.2.2.2, a q.1, hsub q hq, hmod _⟩
  refine ⟨⟨hsubset, fun hall => ?_⟩, hT.mono hsubset⟩
  obtain ⟨x0, hx0, x1, hx1, hne⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le (by norm_num) hR.two)
  obtain ⟨u0, hu0⟩ := hsurj' x0 (hR.sub hx0)
  obtain ⟨u1, hu1⟩ := hsurj' x1 (hR.sub hx1)
  obtain ⟨v, w, hq⟩ := MaxT.PairwiseConnected3.exists_atom_x hT.1 u0
  have hmem : (u1, v, w) ∈ liftSet a (rVII ν Sg Sm Phi') := by
    refine ⟨by rw [hu1]; exact hR.sub hx1, w.2, x0, ?_, ?_⟩
    · have := hsub _ hq
      simpa [hu0] using this
    · show a u1 ∈ modOf Sm x0
      rw [hu1]
      unfold modOf
      rw [if_pos hx0]
      exact hx1
  have := hfm.1 v w u0 u1 hq (hall hmem)
  exact hne (by rw [← hu0, ← hu1, this])

/-! ### spectral estimates at the trivial group (Claims 6/7 of App. B, l. 9013-9030, 9139-9156) -/

section Spectral

/-- the pointwise bound behind both spectral estimates -/
private theorem spec_pointwise {a b q d : ℝ} (k : ℕ) (hq0 : 0 < q) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hab : b = a * q ^ 4) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hdk : d ≤ k * b) :
    (1 - a) ^ k * d ^ 2 ≤ q ^ 2 := by
  have hq2 : q ^ 3 ≤ q ^ 2 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hpow : (1 - a) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hpow0 : 0 ≤ (1 - a) ^ k := pow_nonneg (by linarith) _
  by_cases hkb : (k : ℝ) * b ≤ q
  · have : d ≤ q := hdk.trans hkb
    calc (1 - a) ^ k * d ^ 2 ≤ 1 * d ^ 2 := by gcongr
      _ ≤ q ^ 2 := by nlinarith
  · push Not at hkb
    have hak : 1 < (k : ℝ) * a * q ^ 3 := by
      have h4 : (0 : ℝ) < q ^ 3 := by positivity
      by_contra hcon
      push Not at hcon
      apply (not_lt.2 (le_refl q))
      have : (k : ℝ) * b = ((k : ℝ) * a * q ^ 3) * q := by rw [hab]; ring
      rw [this] at hkb
      nlinarith
    have h1 : (1 - a) ^ k ≤ Real.exp (-(a * k)) := by
      have : 1 - a ≤ Real.exp (-a) := by
        have := Real.add_one_le_exp (-a)
        linarith
      calc (1 - a) ^ k ≤ (Real.exp (-a)) ^ k := by gcongr
        _ = Real.exp (-(a * k)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 : Real.exp (-(a * k)) ≤ q ^ 3 := by
      rw [Real.exp_neg]
      have h5 : a * k + 1 ≤ Real.exp (a * k) := Real.add_one_le_exp _
      have h6 : 1 ≤ (a * k) * q ^ 3 := by nlinarith [hak]
      have h7 : (0 : ℝ) < Real.exp (a * k) := Real.exp_pos _
      rw [inv_le_comm₀ h7 (by positivity)]
      have : (q ^ 3)⁻¹ ≤ a * k := by
        rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    calc (1 - a) ^ k * d ^ 2 ≤ (1 - a) ^ k * 1 := by gcongr
      _ ≤ q ^ 3 := by rw [mul_one]; exact h1.trans h2
      _ ≤ q ^ 2 := hq2

variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem noiseOp_esPart (π : FinProb α) (s : ℝ) (S : Finset ι) (u : (ι → α) → ℝ)
    (x : ι → α) : noiseOp π s (esPart π S u) x = s ^ S.card * esPart π S u x := by
  rw [noiseOp_eq_sum_condExp]
  simp only [condExp_esPart]
  have : ∀ T : Finset ι, s ^ T.card * (1 - s) ^ (Fintype.card ι - T.card) *
      (if S ⊆ T then esPart π S u x else 0) =
      (if S ⊆ T then s ^ T.card * (1 - s) ^ (Fintype.card ι - T.card) else 0) *
        esPart π S u x := by
    intro T; split_ifs <;> ring
  simp only [this]
  rw [← Finset.sum_mul, ← Finset.sum_filter, sum_superset_weight]

private theorem stab_esExp (π : FinProb α) (s : ℝ) (c : ℕ → ℝ) (u w : (ι → α) → ℝ)
    (hw : ∀ x, w x = ∑ S : Finset ι, c S.card * esPart π S u x) :
    stab π s w = ∑ S : Finset ι, s ^ S.card * c S.card ^ 2 *
      (π.pi ι).expect (fun x => esPart π S u x ^ 2) := by
  have hN : ∀ x, noiseOp π s w x = ∑ S : Finset ι, c S.card * (s ^ S.card * esPart π S u x) := by
    intro x
    have hwf : w = fun y => ∑ S : Finset ι, c S.card * esPart π S u y := funext hw
    rw [hwf]
    unfold noiseOp
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    have := noiseOp_esPart π s S u x
    unfold noiseOp at this
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  unfold stab
  have h1 : ∀ x, w x * noiseOp π s w x = ∑ S : Finset ι, ∑ T : Finset ι,
      (c S.card * (c T.card * s ^ T.card)) * (esPart π S u x * esPart π T u x) := by
    intro x
    rw [hw x, hN x, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => by ring
  rw [(π.pi ι).expect_congr h1, FinProb.expect_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [FinProb.expect_sum, Finset.sum_eq_single S]
  · rw [FinProb.expect_const_mul]
    simp only [sq]
    ring
  · intro T _ hT
    rw [FinProb.expect_const_mul, expect_esPart_mul_esPart π (Ne.symm hT)]
    ring
  · intro h
    exact absurd (Finset.mem_univ S) h

private theorem stab_esExp_le (π : FinProb α) (s : ℝ) (c : ℕ → ℝ) (u w : (ι → α) → ℝ)
    (hw : ∀ x, w x = ∑ S : Finset ι, c S.card * esPart π S u x) {M : ℝ}
    (hM : ∀ k, s ^ k * c k ^ 2 ≤ M) :
    stab π s w ≤ M * (π.pi ι).expect (fun x => u x ^ 2) := by
  rw [stab_esExp π s c u w hw, expect_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  exact mul_le_mul_of_nonneg_right (hM _) ((π.pi ι).expect_nonneg fun x => sq_nonneg _)

private theorem cnoiseOp_re (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) (x : ι → α) :
    (cnoiseOp π ρ f x).re = noiseOp π ρ (fun y => (f y).re) x := by
  rw [cnoiseOp_eq_re_add_im]
  simp

private theorem cnoiseOp_im (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) (x : ι → α) :
    (cnoiseOp π ρ f x).im = noiseOp π ρ (fun y => (f y).im) x := by
  rw [cnoiseOp_eq_re_add_im]
  simp

private theorem noiseOp_expansion (π : FinProb α) (ρ : ℝ) (u : (ι → α) → ℝ) (x : ι → α) :
    noiseOp π ρ u x = ∑ S : Finset ι, ρ ^ S.card * esPart π S u x := noiseOp_eq π ρ u x

private theorem re_cstab_le_of_expansion (π : FinProb α) (s : ℝ) (c : ℕ → ℝ) {M : ℝ}
    (hM : ∀ k, s ^ k * c k ^ 2 ≤ M) (f g : (ι → α) → ℂ)
    (hre : ∀ x, (g x).re = ∑ S : Finset ι, c S.card * esPart π S (fun y => (f y).re) x)
    (him : ∀ x, (g x).im = ∑ S : Finset ι, c S.card * esPart π S (fun y => (f y).im) x) :
    (cstab π s g).re ≤ M * cl2sq π f := by
  rw [cstab_eq_re_add_im, Complex.ofReal_re]
  have h1 := stab_esExp_le π s c (fun y => (f y).re) (fun y => (g y).re) hre hM
  have h2 := stab_esExp_le π s c (fun y => (f y).im) (fun y => (g y).im) him hM
  have h3 : cl2sq π f = (π.pi ι).expect (fun x => (f x).re ^ 2) +
      (π.pi ι).expect (fun x => (f x).im ^ 2) := by
    unfold cl2sq
    rw [← FinProb.expect_add]
    refine (π.pi ι).expect_congr fun x => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h3]
  linarith

private theorem cl2sq_le_one (π : FinProb α) (f : (ι → α) → ℂ) (h : cl2norm π f ≤ 1) :
    cl2sq π f ≤ 1 := by
  have h0 : 0 ≤ cl2sq π f := (π.pi ι).expect_nonneg fun x => sq_nonneg _
  have : cl2norm π f ^ 2 = cl2sq π f := Real.sq_sqrt h0
  have h1 : 0 ≤ cl2norm π f := Real.sqrt_nonneg _
  nlinarith

private theorem expansion_one_sub (π : FinProb α) (r : ℝ) (u : (ι → α) → ℝ) (x : ι → α) :
    u x - noiseOp π r u x = ∑ S : Finset ι, (1 - r ^ S.card) * esPart π S u x := by
  have h1 := sum_esPart π u x
  rw [noiseOp_expansion, ← h1]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

private theorem expansion_diff (π : FinProb α) (r1 r2 : ℝ) (u : (ι → α) → ℝ) (x : ι → α) :
    noiseOp π r1 u x - noiseOp π r2 u x =
      ∑ S : Finset ι, (r1 ^ S.card - r2 ^ S.card) * esPart π S u x := by
  rw [noiseOp_expansion, noiseOp_expansion, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- `x^k - y^k ≤ k (x - y)` on `[0,1]` -/
private theorem pow_sub_pow_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (hx : x ≤ 1) (k : ℕ) :
    x ^ k - y ^ k ≤ k * (x - y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hnn : 0 ≤ x ^ k - y ^ k := sub_nonneg.2 (pow_le_pow_left₀ hy hxy k)
    have hyk : y ^ k ≤ 1 := pow_le_one₀ hy (hxy.trans hx)
    have : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [this]
    have h1 : x * (x ^ k - y ^ k) ≤ x ^ k - y ^ k := by nlinarith
    have h2 : (x - y) * y ^ k ≤ (x - y) := by nlinarith
    push_cast
    nlinarith

end Spectral

/-- `Stab_{1-ρ^{1+ξ/2}}(f') ≤ ρ^{ξ/4}` for `f' = (I - T_{non-embed,1-ρ^{1+ξ}}) f`, `‖f‖₂ ≤ 1`
(l. 9013-9022; the printed `‖·‖₂` for the middle expression is `√Stab`, the bound is the same). -/
theorem appB_stab_fprime_le {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (A : Type) [Fintype A] [DecidableEq A] (D : FinProb A) (ι : Type) [Fintype ι]
        [DecidableEq ι] (f : (ι → A) → ℂ), cl2norm D f ≤ 1 →
        (cstab D (1 - ρ ^ (1 + ξ / 2)) (f - tNE D (ρ ^ (1 + ξ)) f)).re ≤ ρ ^ (ξ / 4) := by
  refine ⟨1, one_pos, fun ρ hρ0 hρ1 A _ _ D ι _ _ f hf => ?_⟩
  have hq0 : 0 < ρ ^ (ξ / 8) := Real.rpow_pos_of_pos hρ0 _
  have hq1 : ρ ^ (ξ / 8) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have ha0 : 0 ≤ ρ ^ (1 + ξ / 2) := (Real.rpow_pos_of_pos hρ0 _).le
  have ha1 : ρ ^ (1 + ξ / 2) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have hb0 : 0 ≤ ρ ^ (1 + ξ) := (Real.rpow_pos_of_pos hρ0 _).le
  have hb1 : ρ ^ (1 + ξ) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have hb : ρ ^ (1 + ξ) = ρ ^ (1 + ξ / 2) * (ρ ^ (ξ / 8)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, ← Real.rpow_add hρ0]
    congr 1
    push_cast
    ring
  have hq2 : (ρ ^ (ξ / 8)) ^ 2 = ρ ^ (ξ / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1
    push_cast
    ring
  have hM : ∀ k : ℕ, (1 - ρ ^ (1 + ξ / 2)) ^ k * (1 - (1 - ρ ^ (1 + ξ)) ^ k) ^ 2 ≤
      ρ ^ (ξ / 4) := by
    intro k
    rw [← hq2]
    refine spec_pointwise k hq0 hq1 ha0 ha1 hb ?_ ?_ ?_
    · have : (1 - ρ ^ (1 + ξ)) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    · have : 0 ≤ (1 - ρ ^ (1 + ξ)) ^ k := pow_nonneg (by linarith) _
      linarith
    · have := one_add_mul_le_pow (a := -ρ ^ (1 + ξ)) (by linarith) k
      simp only [← sub_eq_add_neg] at this
      linarith
  have hexp := re_cstab_le_of_expansion D (1 - ρ ^ (1 + ξ / 2))
    (fun k => 1 - (1 - ρ ^ (1 + ξ)) ^ k) hM f (f - tNE D (ρ ^ (1 + ξ)) f)
    (fun x => by
      simp only [Pi.sub_apply, Complex.sub_re]
      rw [tNE_eq_cnoiseOp, cnoiseOp_re]
      exact expansion_one_sub D _ (fun y => (f y).re) x)
    (fun x => by
      simp only [Pi.sub_apply, Complex.sub_im]
      rw [tNE_eq_cnoiseOp, cnoiseOp_im]
      exact expansion_one_sub D _ (fun y => (f y).im) x)
  have h1 := cl2sq_le_one D f hf
  have h2 : 0 ≤ ρ ^ (ξ / 4) := (Real.rpow_pos_of_pos hρ0 _).le
  nlinarith

/-- `Stab_{1-ρ^{1-ξ/2}}(g') ≤ ρ^{ξ/4}` for `g' = T' g`, `‖g‖₂ ≤ 1`, `0 < ξ ≤ 1/2` (l. 9139-9156). -/
theorem appB_stab_gprime_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (A : Type) [Fintype A] [DecidableEq A] (D : FinProb A) (ι : Type) [Fintype ι]
        [DecidableEq ι] (g : (ι → A) → ℂ), cl2norm D g ≤ 1 →
        (cstab D (1 - ρ ^ (1 - ξ / 2)) (appTp D ρ g)).re ≤ ρ ^ (ξ / 4) := by
  refine ⟨1, one_pos, fun ρ hρ0 hρ1 A _ _ D ι _ _ g hg => ?_⟩
  have hq0 : 0 < ρ ^ (ξ / 8) := Real.rpow_pos_of_pos hρ0 _
  have hq1 : ρ ^ (ξ / 8) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have ha0 : 0 ≤ ρ ^ (1 - ξ / 2) := (Real.rpow_pos_of_pos hρ0 _).le
  have ha1 : ρ ^ (1 - ξ / 2) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by linarith)
  have hb : ρ = ρ ^ (1 - ξ / 2) * (ρ ^ (ξ / 8)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, ← Real.rpow_add hρ0]
    conv_lhs => rw [← Real.rpow_one ρ]
    congr 1
    push_cast
    ring
  have hq2 : (ρ ^ (ξ / 8)) ^ 2 = ρ ^ (ξ / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1
    push_cast
    ring
  have hM : ∀ k : ℕ, (1 - ρ ^ (1 - ξ / 2)) ^ k *
      ((1 - ρ / 2) ^ k - (1 - ρ) ^ k) ^ 2 ≤ ρ ^ (ξ / 4) := by
    intro k
    rw [← hq2]
    refine spec_pointwise k hq0 hq1 ha0 ha1 hb ?_ ?_ ?_
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - ρ) (by linarith : 1 - ρ ≤ 1 - ρ / 2) k
      linarith
    · have : (1 - ρ / 2) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have : 0 ≤ (1 - ρ) ^ k := pow_nonneg (by linarith) _
      linarith
    · have := pow_sub_pow_le (x := 1 - ρ / 2) (y := 1 - ρ) (by linarith) (by linarith)
        (by linarith) k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
  have hexp := re_cstab_le_of_expansion D (1 - ρ ^ (1 - ξ / 2))
    (fun k => (1 - ρ / 2) ^ k - (1 - ρ) ^ k) hM g (appTp D ρ g)
    (fun x => by
      unfold appTp
      simp only [Pi.sub_apply, Complex.sub_re]
      rw [tNE_eq_cnoiseOp, tNE_eq_cnoiseOp, cnoiseOp_re, cnoiseOp_re]
      have := expansion_diff D (1 - ρ / 2) (1 - ρ) (fun y => (g y).re) x
      simpa using this)
    (fun x => by
      unfold appTp
      simp only [Pi.sub_apply, Complex.sub_im]
      rw [tNE_eq_cnoiseOp, tNE_eq_cnoiseOp, cnoiseOp_im, cnoiseOp_im]
      have := expansion_diff D (1 - ρ / 2) (1 - ρ) (fun y => (g y).im) x
      simpa using this)
  have h1 := cl2sq_le_one D g hg
  have h2 : 0 ≤ ρ ^ (ξ / 4) := (Real.rpow_pos_of_pos hρ0 _).le
  nlinarith

end Targets

end TrackB
end RestrictedPolynomials
end
