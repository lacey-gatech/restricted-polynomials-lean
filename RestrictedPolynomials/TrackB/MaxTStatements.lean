module

public import RestrictedPolynomials.TrackB.MaxTOps
public import RestrictedPolynomials.TrackB.StabComplex
public import RestrictedPolynomials.Frozen.CStab

/-!
# Track B: the statement `S_s`, `P`, symmetry, very base case
(Supplement E, `lem:stab-push` (St2)-(St4), `def:S`, `lem:P-sym`, `lem:very-base-T`)

Supplement E items: `lem:stab-push` ((St1) is built in `StabComplex`), `def:S`,
`lem:P-sym`, `lem:very-base-T`.

Reading: the statement `S_s` lives on `Fin n`, uses `(cstab _ (1 - δ) u).re` of the
marginal law and an `rpow` exponent; `M ≥ 1` and `δ₀ ≤ 1` belong to `Q`, not to `SStmt*`.
All helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Stab
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ι : Type} [Fintype ι]
  [DecidableEq ι]

private theorem push_sum (a : α → β) (w : ι → α → ℝ) (G : (ι → β) → ℂ) :
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

private theorem kernel_fiber (D : FinProb α) (a : α → β) (ρ : ℝ) (x : α) (b : β) :
    ∑ c ∈ univ.filter (fun c => a c = b), noiseKernel D ρ x c =
      noiseKernel (mergePush D a) ρ (a x) b := by
  unfold noiseKernel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  · simp [Finset.sum_ite_eq]

private theorem cnoiseOp_push (D : FinProb α) (a : α → β) (ρ : ℝ) (u : (ι → β) → ℂ)
    (x : ι → α) :
    cnoiseOp D ρ (fun x => u (fun i => a (x i))) x =
      cnoiseOp (mergePush D a) ρ u (fun i => a (x i)) := by
  unfold cnoiseOp
  refine (push_sum a (fun i c => noiseKernel D ρ (x i) c) u).trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (∏ i, ∑ c ∈ univ.filter (fun c => a c = b i), noiseKernel D ρ (x i) c) =
      ∏ i, noiseKernel (mergePush D a) ρ (a (x i)) (b i) :=
    Finset.prod_congr rfl fun i _ => kernel_fiber D a ρ (x i) (b i)
  rw [this]

private theorem cexpect_pi_push (π : FinProb α) (a : α → β) (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (push_sum a (fun _ c => π.prob c) G).symm

/-! ### Supplement E `lem:stab-push`: (St2)-(St4); (St1) is `cstab_nonneg`, `cstab_mono`,
`norm_cexpect_sq_le_re_cstab` of `StabComplex` (already built). -/

theorem cstab_smul (π : FinProb α) (ρ : ℝ) (c : ℂ) (f : (ι → α) → ℂ) :
    cstab π ρ (fun x => c * f x) = (Complex.normSq c : ℂ) * cstab π ρ f := by
  have h1 : ∀ x, cnoiseOp π ρ (fun x => c * f x) x = c * cnoiseOp π ρ f x := by
    intro x
    unfold cnoiseOp
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  unfold cstab
  simp only [h1, star_mul', Complex.star_def]
  unfold FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- (St4) push-forward: `a_* D'' = D'` and `u'' = u' ∘ a^{⊗n}` have the same stability. -/
theorem cstab_pushforward (D : FinProb α) (a : α → β) (ρ : ℝ) (u : (ι → β) → ℂ) :
    cstab D ρ (fun x => u (fun i => a (x i))) = cstab (mergePush D a) ρ u := by
  unfold cstab
  simp only [cnoiseOp_push]
  exact (cexpect_pi_push D a (fun b => u b * star (cnoiseOp (mergePush D a) ρ u b))).symm

/-- (St3) relabelling by a bijection. -/
theorem cstab_relabel (e : α ≃ β) (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) :
    cstab (mergePush π e) ρ (fun y => f (fun i => e.symm (y i))) = cstab π ρ f := by
  rw [← cstab_pushforward π e ρ]
  simp

end Stab

private theorem finProb_ext {α : Type} [Fintype α] {π π' : FinProb α}
    (h : ∀ a, π.prob a = π'.prob a) : π = π' := by
  cases π
  cases π'
  congr
  funext a
  exact h a

private theorem mergePush_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (π : FinProb α) (f : α → β) (g : β → γ) :
    mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine finProb_ext fun c => ?_
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

private theorem mergePush_prob_inj {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (hf : Function.Injective f) (a : α) :
    (mergePush π f).prob (f a) = π.prob a := by
  classical
  show ∑ a' ∈ univ.filter (fun a' => f a' = f a), π.prob a' = _
  rw [Finset.filter_congr (q := fun a' => a' = a) (fun a' _ => hf.eq_iff)]
  rw [Finset.filter_eq' univ a, if_pos (Finset.mem_univ a), Finset.sum_singleton]

private theorem mem_supp_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (b : β) :
    b ∈ (mergePush π f).support ↔ ∃ a, f a = b ∧ a ∈ π.support := by
  show (∑ a ∈ Finset.univ.filter (fun a => f a = b), π.prob a) ≠ 0 ↔ _
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun a _ => π.nonneg a]
  push Not
  constructor
  · rintro ⟨a, ha, hne⟩
    exact ⟨a, (Finset.mem_filter.1 ha).2, hne⟩
  · rintro ⟨a, hfa, hne⟩
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfa⟩, hne⟩

section Statements
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the marginals `μ_x`, `μ_y`, `μ_z` -/
def lawX (μ : FinProb (X × Y × Z)) : FinProb X := mergePush μ fun p => p.1
def lawY (μ : FinProb (X × Y × Z)) : FinProb Y := mergePush μ fun p => p.2.1
def lawZ (μ : FinProb (X × Y × Z)) : FinProb Z := mergePush μ fun p => p.2.2

/-- `μ` with `y` and `z` exchanged -/
def lawSwapYZ (μ : FinProb (X × Y × Z)) : FinProb (X × Z × Y) :=
  mergePush μ fun p => (p.1, p.2.2, p.2.1)

/-- `μ` relabelled by bijections of the three alphabets -/
def lawRelabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) : FinProb (X' × Y' × Z') :=
  mergePush μ fun p => (eX p.1, eY p.2.1, eZ p.2.2)

theorem lawSwapYZ_support (μ : FinProb (X × Y × Z)) : (lawSwapYZ μ).support = swapYZ μ.support := by
  ext ⟨x, z, y⟩
  refine (mem_supp_push _ _ _).trans ?_
  constructor
  · rintro ⟨⟨x', y', z'⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨_, h, rfl⟩
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    exact ⟨_, he, h⟩

theorem lawRelabel_support {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) : (lawRelabel eX eY eZ μ).support = relabelSet eX eY eZ μ.support := by
  ext ⟨x, y, z⟩
  refine (mem_supp_push _ _ _).trans ?_
  constructor
  · rintro ⟨⟨x', y', z'⟩, he, h⟩
    exact ⟨_, h, he⟩
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    exact ⟨_, he, h⟩

theorem lawSwapXY_prob (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    (lawSwapXY μ).prob (y, x, z) = μ.prob (x, y, z) :=
  mergePush_prob_inj μ (fun p => (p.2.1, p.1, p.2.2))
    (by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto) (x, y, z)

theorem lawSwapYZ_prob (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    (lawSwapYZ μ).prob (x, z, y) = μ.prob (x, y, z) :=
  mergePush_prob_inj μ (fun p => (p.1, p.2.2, p.2.1))
    (by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto) (x, y, z)

theorem lawRelabel_prob {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    (lawRelabel eX eY eZ μ).prob (eX x, eY y, eZ z) = μ.prob (x, y, z) :=
  mergePush_prob_inj μ (fun p => (eX p.1, eY p.2.1, eZ p.2.2))
    (by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h ⊢
      exact h) (x, y, z)

/-- `𝔼_{(x,y,z) ∼ μ^{⊗ι}} f(x) g(y) h(z)` -/
def corr3 {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z)) (f : (ι → X) → ℂ)
    (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) : ℂ :=
  (μ.pi ι).cexpect fun t => f (fun i => (t i).1) * g (fun i => (t i).2.1) * h (fun i => (t i).2.2)

/-- Supplement E `def:S`, slot `x`: `Stab_{1-δ}(f; μ_x^{⊗n}) ≤ δ ⇒ |𝔼 f g h| ≤ M δ^η` for all `δ ∈ (0, δ₀]`,
all `n` and all 1-bounded `f, g, h`. -/
def SStmtX (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
    (cstab (lawX μ) (1 - δ) f).re ≤ δ → ‖corr3 μ f g h‖ ≤ M * δ ^ η

/-- Supplement E `def:S`, slot `y` (the conclusion of Thm 4.13 / 10.2). -/
def SStmtY (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
    (cstab (lawY μ) (1 - δ) g).re ≤ δ → ‖corr3 μ f g h‖ ≤ M * δ ^ η

/-- Supplement E `def:S`, slot `z`. -/
def SStmtZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
    (cstab (lawZ μ) (1 - δ) h).re ≤ δ → ‖corr3 μ f g h‖ ≤ M * δ ^ η

/-- Supplement E `def:S`, `P(μ; M, δ₀, η) := S_x ∧ S_y ∧ S_z`. -/
def PStmt (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) : Prop :=
  SStmtX μ M δ₀ η ∧ SStmtY μ M δ₀ η ∧ SStmtZ μ M δ₀ η

/-! ### Supplement E `lem:P-sym` -/

private theorem corr3_mergePush {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinProb (X × Y × Z)) (a : X × Y × Z → X' × Y' × Z') (f : (ι → X') → ℂ)
    (g : (ι → Y') → ℂ) (h : (ι → Z') → ℂ) :
    corr3 (mergePush μ a) f g h = (μ.pi ι).cexpect fun t =>
      f (fun i => (a (t i)).1) * g (fun i => (a (t i)).2.1) * h (fun i => (a (t i)).2.2) :=
  cexpect_pi_push μ a _

theorem corr3_lawSwapXY {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 (lawSwapXY μ) g f h = corr3 μ f g h := by
  unfold lawSwapXY
  rw [corr3_mergePush]
  unfold corr3
  refine congrArg _ (funext fun t => ?_)
  ring

theorem corr3_lawSwapYZ {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 (lawSwapYZ μ) f h g = corr3 μ f g h := by
  unfold lawSwapYZ
  rw [corr3_mergePush]
  unfold corr3
  refine congrArg _ (funext fun t => ?_)
  ring

theorem corr3_lawRelabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z') (μ : FinProb (X × Y × Z))
    (f : (ι → X') → ℂ) (g : (ι → Y') → ℂ) (h : (ι → Z') → ℂ) :
    corr3 (lawRelabel eX eY eZ μ) f g h =
      corr3 μ (fun x => f fun i => eX (x i)) (fun y => g fun i => eY (y i))
        (fun z => h fun i => eZ (z i)) := by
  unfold lawRelabel
  rw [corr3_mergePush]
  rfl

private theorem lawX_lawSwapXY (μ : FinProb (X × Y × Z)) : lawX (lawSwapXY μ) = lawY μ :=
  mergePush_comp μ (fun p => (p.2.1, p.1, p.2.2)) (fun p => p.1)
private theorem lawY_lawSwapXY (μ : FinProb (X × Y × Z)) : lawY (lawSwapXY μ) = lawX μ :=
  mergePush_comp μ (fun p => (p.2.1, p.1, p.2.2)) (fun p => p.2.1)
private theorem lawZ_lawSwapXY (μ : FinProb (X × Y × Z)) : lawZ (lawSwapXY μ) = lawZ μ :=
  mergePush_comp μ (fun p => (p.2.1, p.1, p.2.2)) (fun p => p.2.2)
private theorem lawX_lawSwapYZ (μ : FinProb (X × Y × Z)) : lawX (lawSwapYZ μ) = lawX μ :=
  mergePush_comp μ (fun p => (p.1, p.2.2, p.2.1)) (fun p => p.1)
private theorem lawY_lawSwapYZ (μ : FinProb (X × Y × Z)) : lawY (lawSwapYZ μ) = lawZ μ :=
  mergePush_comp μ (fun p => (p.1, p.2.2, p.2.1)) (fun p => p.2.1)
private theorem lawZ_lawSwapYZ (μ : FinProb (X × Y × Z)) : lawZ (lawSwapYZ μ) = lawY μ :=
  mergePush_comp μ (fun p => (p.1, p.2.2, p.2.1)) (fun p => p.2.2)

private theorem lawX_lawRelabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) : lawX (lawRelabel eX eY eZ μ) = mergePush (lawX μ) eX :=
  (mergePush_comp μ (fun p => (eX p.1, eY p.2.1, eZ p.2.2)) (fun p => p.1)).trans
    (mergePush_comp μ (fun p => p.1) eX).symm
private theorem lawY_lawRelabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) : lawY (lawRelabel eX eY eZ μ) = mergePush (lawY μ) eY :=
  (mergePush_comp μ (fun p => (eX p.1, eY p.2.1, eZ p.2.2)) (fun p => p.2.1)).trans
    (mergePush_comp μ (fun p => p.2.1) eY).symm
private theorem lawZ_lawRelabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) : lawZ (lawRelabel eX eY eZ μ) = mergePush (lawZ μ) eZ :=
  (mergePush_comp μ (fun p => (eX p.1, eY p.2.1, eZ p.2.2)) (fun p => p.2.2)).trans
    (mergePush_comp μ (fun p => p.2.2) eZ).symm

theorem sStmtX_iff_swapXY (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtX μ M δ₀ η ↔ SStmtY (lawSwapXY μ) M δ₀ η := by
  unfold SStmtX SStmtY
  rw [lawY_lawSwapXY]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawSwapXY μ g f h]
    exact H δ hδ hδ' n g f h hg hf hh hs
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [← corr3_lawSwapXY μ f g h]
    exact H δ hδ hδ' n g f h hg hf hh hs

theorem sStmtY_iff_swapXY (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtY μ M δ₀ η ↔ SStmtX (lawSwapXY μ) M δ₀ η := by
  unfold SStmtX SStmtY
  rw [lawX_lawSwapXY]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawSwapXY μ g f h]
    exact H δ hδ hδ' n g f h hg hf hh hs
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [← corr3_lawSwapXY μ f g h]
    exact H δ hδ hδ' n g f h hg hf hh hs

theorem sStmtZ_iff_swapXY (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtZ μ M δ₀ η ↔ SStmtZ (lawSwapXY μ) M δ₀ η := by
  unfold SStmtZ
  rw [lawZ_lawSwapXY]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawSwapXY μ g f h]
    exact H δ hδ hδ' n g f h hg hf hh hs
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [← corr3_lawSwapXY μ f g h]
    exact H δ hδ hδ' n g f h hg hf hh hs

theorem sStmtX_iff_swapYZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtX μ M δ₀ η ↔ SStmtX (lawSwapYZ μ) M δ₀ η := by
  unfold SStmtX
  rw [lawX_lawSwapYZ]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawSwapYZ μ f h g]
    exact H δ hδ hδ' n f h g hf hh hg hs
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [← corr3_lawSwapYZ μ f g h]
    exact H δ hδ hδ' n f h g hf hh hg hs

theorem sStmtY_iff_swapYZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtY μ M δ₀ η ↔ SStmtZ (lawSwapYZ μ) M δ₀ η := by
  unfold SStmtY SStmtZ
  rw [lawZ_lawSwapYZ]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawSwapYZ μ f h g]
    exact H δ hδ hδ' n f h g hf hh hg hs
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [← corr3_lawSwapYZ μ f g h]
    exact H δ hδ hδ' n f h g hf hh hg hs

theorem sStmtZ_iff_swapYZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtZ μ M δ₀ η ↔ SStmtY (lawSwapYZ μ) M δ₀ η := by
  unfold SStmtY SStmtZ
  rw [lawY_lawSwapYZ]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawSwapYZ μ f h g]
    exact H δ hδ hδ' n f h g hf hh hg hs
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [← corr3_lawSwapYZ μ f g h]
    exact H δ hδ hδ' n f h g hf hh hg hs

theorem sStmtX_iff_relabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtX (lawRelabel eX eY eZ μ) M δ₀ η ↔ SStmtX μ M δ₀ η := by
  unfold SStmtX
  rw [lawX_lawRelabel]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    have hs' := (cstab_relabel eX (lawX μ) (1 - δ) f).symm ▸ hs
    have := H δ hδ hδ' n (fun y => f fun i => eX.symm (y i)) (fun y => g fun i => eY.symm (y i))
      (fun z => h fun i => eZ.symm (z i)) (fun _ => hf _) (fun _ => hg _) (fun _ => hh _)
      (by rw [cstab_relabel]; exact hs)
    rw [corr3_lawRelabel] at this
    simpa using this
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawRelabel]
    refine H δ hδ hδ' n _ _ _ (fun _ => hf _) (fun _ => hg _) (fun _ => hh _) ?_
    rw [cstab_pushforward]
    exact hs

theorem sStmtY_iff_relabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtY (lawRelabel eX eY eZ μ) M δ₀ η ↔ SStmtY μ M δ₀ η := by
  unfold SStmtY
  rw [lawY_lawRelabel]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    have := H δ hδ hδ' n (fun y => f fun i => eX.symm (y i)) (fun y => g fun i => eY.symm (y i))
      (fun z => h fun i => eZ.symm (z i)) (fun _ => hf _) (fun _ => hg _) (fun _ => hh _)
      (by rw [cstab_relabel]; exact hs)
    rw [corr3_lawRelabel] at this
    simpa using this
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawRelabel]
    refine H δ hδ hδ' n _ _ _ (fun _ => hf _) (fun _ => hg _) (fun _ => hh _) ?_
    rw [cstab_pushforward]
    exact hs

theorem sStmtZ_iff_relabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtZ (lawRelabel eX eY eZ μ) M δ₀ η ↔ SStmtZ μ M δ₀ η := by
  unfold SStmtZ
  rw [lawZ_lawRelabel]
  constructor
  · intro H δ hδ hδ' n f g h hf hg hh hs
    have := H δ hδ hδ' n (fun y => f fun i => eX.symm (y i)) (fun y => g fun i => eY.symm (y i))
      (fun z => h fun i => eZ.symm (z i)) (fun _ => hf _) (fun _ => hg _) (fun _ => hh _)
      (by rw [cstab_relabel]; exact hs)
    rw [corr3_lawRelabel] at this
    simpa using this
  · intro H δ hδ hδ' n f g h hf hg hh hs
    rw [corr3_lawRelabel]
    refine H δ hδ hδ' n _ _ _ (fun _ => hf _) (fun _ => hg _) (fun _ => hh _) ?_
    rw [cstab_pushforward]
    exact hs

theorem pStmt_swapXY_iff (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    PStmt (lawSwapXY μ) M δ₀ η ↔ PStmt μ M δ₀ η := by
  have h1 := sStmtX_iff_swapXY μ M δ₀ η
  have h2 := sStmtY_iff_swapXY μ M δ₀ η
  have h3 := sStmtZ_iff_swapXY μ M δ₀ η
  unfold PStmt
  tauto

theorem pStmt_swapYZ_iff (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    PStmt (lawSwapYZ μ) M δ₀ η ↔ PStmt μ M δ₀ η := by
  have h1 := sStmtX_iff_swapYZ μ M δ₀ η
  have h2 := sStmtY_iff_swapYZ μ M δ₀ η
  have h3 := sStmtZ_iff_swapYZ μ M δ₀ η
  unfold PStmt
  tauto

theorem pStmt_relabel_iff {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    PStmt (lawRelabel eX eY eZ μ) M δ₀ η ↔ PStmt μ M δ₀ η := by
  have h1 := sStmtX_iff_relabel eX eY eZ μ M δ₀ η
  have h2 := sStmtY_iff_relabel eX eY eZ μ M δ₀ η
  have h3 := sStmtZ_iff_relabel eX eY eZ μ M δ₀ η
  unfold PStmt
  tauto

/-! ### Supplement E `lem:very-base-T` -/

private theorem cexpect_const_of {A : Type} [Fintype A] (π : FinProb A) (F : A → ℂ) (c : ℂ)
    (h : ∀ a, F a = c) : π.cexpect F = c := by
  unfold FinProb.cexpect
  simp only [h]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, π.sum_eq_one]
  simp

private theorem cexpect_const_mul {A : Type} [Fintype A] (π : FinProb A) (G : A → ℂ) (c : ℂ) :
    π.cexpect (fun a => c * G a) = c * π.cexpect G := by
  unfold FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

private theorem norm_cexpect_le_one {A : Type} [Fintype A] (π : FinProb A) (G : A → ℂ)
    (hG : ∀ a, ‖G a‖ ≤ 1) : ‖π.cexpect G‖ ≤ 1 := by
  unfold FinProb.cexpect
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖(π.prob a : ℂ) * G a‖ ≤ ∑ a, π.prob a := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (π.nonneg a)]
        exact mul_le_of_le_one_right (π.nonneg a) (hG a)
    _ = 1 := π.sum_eq_one

private theorem le_sqrt_of_sq_le' {a δ : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ δ) : a ≤ Real.sqrt δ := by
  simpa [abs_of_nonneg ha] using Real.abs_le_sqrt h

/-- two singleton alphabets `x`, `z`: all three slots give `|𝔼 f g h| ≤ √δ`. -/
theorem veryBase_xz [Subsingleton X] [Subsingleton Z] (μ : FinProb (X × Y × Z)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hs : (cstab (lawX μ) (1 - δ) f).re ≤ δ ∨ (cstab (lawY μ) (1 - δ) g).re ≤ δ ∨
      (cstab (lawZ μ) (1 - δ) h).re ≤ δ) :
    ‖corr3 μ f g h‖ ≤ Real.sqrt δ := by
  have hρ : 0 ≤ 1 - δ := by linarith
  have hne : Nonempty (Fin n → X × Y × Z) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := (μ.pi (Fin n)).sum_eq_one
    simp at this
  obtain ⟨t₁⟩ := hne
  have hF : ∀ t : Fin n → X × Y × Z,
      f (fun i => (t i).1) = f (fun i => (t₁ i).1) := fun t => by
    congr 1; funext i; exact Subsingleton.elim _ _
  have hH : ∀ t : Fin n → X × Y × Z,
      h (fun i => (t i).2.2) = h (fun i => (t₁ i).2.2) := fun t => by
    congr 1; funext i; exact Subsingleton.elim _ _
  set cf := f (fun i => (t₁ i).1) with hcf
  set ch := h (fun i => (t₁ i).2.2) with hch
  have hcf1 : ‖cf‖ ≤ 1 := hf _
  have hch1 : ‖ch‖ ≤ 1 := hh _
  have hEY : ((lawY μ).pi (Fin n)).cexpect g =
      (μ.pi (Fin n)).cexpect (fun t => g (fun i => (t i).2.1)) :=
    cexpect_pi_push μ (fun p => p.2.1) g
  have hEX : ((lawX μ).pi (Fin n)).cexpect f = cf := by
    rw [show ((lawX μ).pi (Fin n)).cexpect f =
      (μ.pi (Fin n)).cexpect (fun t => f (fun i => (t i).1)) from
        cexpect_pi_push μ (fun p => p.1) f]
    exact cexpect_const_of _ _ _ hF
  have hEZ : ((lawZ μ).pi (Fin n)).cexpect h = ch := by
    rw [show ((lawZ μ).pi (Fin n)).cexpect h =
      (μ.pi (Fin n)).cexpect (fun t => h (fun i => (t i).2.2)) from
        cexpect_pi_push μ (fun p => p.2.2) h]
    exact cexpect_const_of _ _ _ hH
  have hcorr : corr3 μ f g h = cf * ch * ((μ.pi (Fin n)).cexpect
      (fun t => g (fun i => (t i).2.1))) := by
    unfold corr3
    rw [← cexpect_const_mul]
    refine congrArg _ (funext fun t => ?_)
    rw [hF t, hH t]
    ring
  have hEY1 : ‖(μ.pi (Fin n)).cexpect (fun t => g (fun i => (t i).2.1))‖ ≤ 1 :=
    norm_cexpect_le_one _ _ fun t => hg _
  have hnorm : ‖corr3 μ f g h‖ ≤ ‖cf‖ ∧ ‖corr3 μ f g h‖ ≤ ‖ch‖ ∧
      ‖corr3 μ f g h‖ ≤ ‖(μ.pi (Fin n)).cexpect (fun t => g (fun i => (t i).2.1))‖ := by
    rw [hcorr, norm_mul, norm_mul]
    refine ⟨?_, ?_, ?_⟩
    · calc _ ≤ ‖cf‖ * 1 * 1 := by gcongr
        _ = _ := by ring
    · calc _ ≤ 1 * ‖ch‖ * 1 := by gcongr
        _ = _ := by ring
    · calc _ ≤ 1 * 1 * ‖(μ.pi (Fin n)).cexpect (fun t => g (fun i => (t i).2.1))‖ := by gcongr
        _ = _ := by ring
  rcases hs with hs | hs | hs
  · have := norm_cexpect_sq_le_re_cstab (lawX μ) hρ f
    rw [hEX] at this
    exact hnorm.1.trans (le_sqrt_of_sq_le' (norm_nonneg _) (this.trans hs))
  · have := norm_cexpect_sq_le_re_cstab (lawY μ) hρ g
    rw [hEY] at this
    exact hnorm.2.2.trans (le_sqrt_of_sq_le' (norm_nonneg _) (this.trans hs))
  · have := norm_cexpect_sq_le_re_cstab (lawZ μ) hρ h
    rw [hEZ] at this
    exact hnorm.2.1.trans (le_sqrt_of_sq_le' (norm_nonneg _) (this.trans hs))

theorem veryBase_xy [Subsingleton X] [Subsingleton Y] (μ : FinProb (X × Y × Z)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hs : (cstab (lawX μ) (1 - δ) f).re ≤ δ ∨ (cstab (lawY μ) (1 - δ) g).re ≤ δ ∨
      (cstab (lawZ μ) (1 - δ) h).re ≤ δ) :
    ‖corr3 μ f g h‖ ≤ Real.sqrt δ := by
  have := veryBase_xz (lawSwapYZ μ) hδ0 hδ1 f h g hf hh hg
    (by rw [lawX_lawSwapYZ, lawY_lawSwapYZ, lawZ_lawSwapYZ]; tauto)
  rwa [corr3_lawSwapYZ] at this

theorem veryBase_yz [Subsingleton Y] [Subsingleton Z] (μ : FinProb (X × Y × Z)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hs : (cstab (lawX μ) (1 - δ) f).re ≤ δ ∨ (cstab (lawY μ) (1 - δ) g).re ≤ δ ∨
      (cstab (lawZ μ) (1 - δ) h).re ≤ δ) :
    ‖corr3 μ f g h‖ ≤ Real.sqrt δ := by
  have := veryBase_xz (lawSwapXY μ) hδ0 hδ1 g f h hg hf hh
    (by rw [lawX_lawSwapXY, lawY_lawSwapXY, lawZ_lawSwapXY]; tauto)
  rwa [corr3_lawSwapXY] at this

/-- a single atom: `P(μ; 1, 1, 1/2)`. -/
theorem pStmt_of_unique [Unique X] [Unique Y] [Unique Z] (μ : FinProb (X × Y × Z)) :
    PStmt μ 1 1 (1 / 2) := by
  unfold PStmt SStmtX SStmtY SStmtZ
  have key : ∀ δ : ℝ, Real.sqrt δ = 1 * δ ^ (1 / 2 : ℝ) := fun δ => by
    rw [one_mul, Real.sqrt_eq_rpow]
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ hδ₀ n f g h hf hg hh hs
    rw [← key]
    exact veryBase_xz μ hδ hδ₀ f g h hf hg hh (Or.inl hs)
  · intro δ hδ hδ₀ n f g h hf hg hh hs
    rw [← key]
    exact veryBase_xz μ hδ hδ₀ f g h hf hg hh (Or.inr (Or.inl hs))
  · intro δ hδ hδ₀ n f g h hf hg hh hs
    rw [← key]
    exact veryBase_xz μ hδ hδ₀ f g h hf hg hh (Or.inr (Or.inr hs))

end Statements

end MaxT
end TrackB
end RestrictedPolynomials
end
