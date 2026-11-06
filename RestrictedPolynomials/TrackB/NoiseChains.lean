module

public import RestrictedPolynomials.TrackB.MarkovChain
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Frozen.FinProbPi
public import Mathlib.Analysis.Complex.Order

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section NoiseChains
variable {α : Type} [Fintype α] [DecidableEq α]

/-- `T_{1-ξ,D}` for a relation `G` on `α`: stay put with probability `1 - ξ`, otherwise draw
`x' ∼ D` conditioned on `x'` being a `G`-neighbour of `x` (paper IV l. 1291-1298). -/
def graphNoiseKernel (D : FinProb α) (G : α → α → Prop) [DecidableRel G] (ξ : ℝ) (a b : α) : ℝ :=
  (1 - ξ) * (if a = b then 1 else 0) +
    ξ * ((if G a b then D.prob b else 0) / ∑ c ∈ univ.filter (G a), D.prob c)

/-- `T_{1-ξ,D} g` on one coordinate. -/
def graphNoiseApply (D : FinProb α) (G : α → α → Prop) [DecidableRel G] (ξ : ℝ)
    (g : α → ℂ) (a : α) : ℂ :=
  ∑ b, ((graphNoiseKernel D G ξ a b : ℝ) : ℂ) * g b

/-- `T_{1-ξ,D}^{⊗ι}`: the chain applied in each coordinate independently. -/
def graphNoiseOp (D : FinProb α) (G : α → α → Prop) [DecidableRel G] (ξ : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  ∑ y, ((∏ i, graphNoiseKernel D G ξ (x i) (y i) : ℝ) : ℂ) * f y

variable {H : Type} [DecidableEq H]

/-- paper IV `definition-non-embedding-noise-operator`: from `x`, stay with probability `1 - ξ`, otherwise
`x' ∼ D` conditioned on `σ x' = σ x`; `σ` is the `x`-component of the master embedding.
The `y`- and `z`-versions are the same definition with `γ`, `φ`. Well defined (a Markov chain)
exactly when every fibre of `σ` has positive `D`-mass. -/
def nonEmbedKernel (D : FinProb α) (σ : α → H) (ξ : ℝ) (a b : α) : ℝ :=
  graphNoiseKernel D (fun a b => σ a = σ b) ξ a b

/-- `T_{non-embed,1-ξ,D,μ}^{⊗ι} f`. -/
def nonEmbedOp (D : FinProb α) (σ : α → H) (ξ : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  graphNoiseOp D (fun a b => σ a = σ b) ξ f x

/-- paper IV `def:nestab`: `NEStab_{1-ξ,μ}(f; D^{⊗n}) = ⟨f, T_{non-embed,1-ξ,D,μ}^{⊗n} f⟩`. -/
def nestab (D : FinProb α) (σ : α → H) (ξ : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) : ℂ :=
  (D.pi ι).cinner f (nonEmbedOp D σ ξ f)

theorem graphNoiseKernel_isStochastic (D : FinProb α) (G : α → α → Prop) [DecidableRel G]
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hpos : ∀ a, 0 < ∑ c ∈ univ.filter (G a), D.prob c) :
    ∃ T : StochMat α, ∀ a b, T.prob a b = graphNoiseKernel D G ξ a b := by
  have hM := hpos
  refine ⟨⟨graphNoiseKernel D G ξ, ?_, ?_⟩, fun a b => rfl⟩
  · intro a b
    have h1 : 0 ≤ ∑ c ∈ univ.filter (G a), D.prob c := (hpos a).le
    unfold graphNoiseKernel
    have : 0 ≤ (if G a b then D.prob b else 0) := by
      split_ifs
      · exact D.nonneg b
      · exact le_rfl
    have := div_nonneg this h1
    have h2 : 0 ≤ 1 - ξ := by linarith
    have h3 : 0 ≤ (if a = b then (1:ℝ) else 0) := by split_ifs <;> norm_num
    positivity
  · intro a
    unfold graphNoiseKernel
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
    have e1 : ∑ b, (if a = b then (1:ℝ) else 0) = 1 := by simp
    have e2 : ∑ b, (if G a b then D.prob b else 0) = ∑ c ∈ univ.filter (G a), D.prob c := by
      rw [Finset.sum_filter]
    rw [e1, e2, div_self (hpos a).ne']
    ring

theorem nonEmbedKernel_isReversible (D : FinProb α) (σ : α → H) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1) (hfib : ∀ a, 0 < ∑ c ∈ univ.filter (fun c => σ c = σ a), D.prob c) :
    ∃ T : StochMat α, (∀ a b, T.prob a b = nonEmbedKernel D σ ξ a b) ∧
      T.IsStationary D ∧ T.IsReversible D := by
  have hK := graphNoiseKernel_isStochastic D (fun a b => σ a = σ b) hξ0 hξ1
    (fun a => by
      have : (univ.filter fun c => σ a = σ c) = univ.filter fun c => σ c = σ a := by
        ext c; simp [eq_comm]
      rw [this]; exact hfib a)
  obtain ⟨T, hT⟩ := hK
  have hrev : T.IsReversible D := by
    intro a b
    rw [hT, hT]
    by_cases hab : a = b
    · subst hab; rfl
    · unfold graphNoiseKernel
      by_cases h : σ a = σ b
      · have hM : (univ.filter fun c => σ a = σ c) = univ.filter fun c => σ b = σ c := by
          ext c; simp [h]
        beta_reduce
        simp only [hab, Ne.symm hab, h, ite_true, ite_false]
        ring
      · beta_reduce
        simp only [hab, Ne.symm hab, h, Ne.symm h, ite_false]
        ring
  refine ⟨T, fun a b => hT a b, ?_, hrev⟩
  intro b
  have : ∀ a, D.prob a * T.prob a b = D.prob b * T.prob b a := fun a => hrev a b
  simp_rw [this, ← Finset.mul_sum, T.row_sum, mul_one]

/-- CSP_7 `thm:3csp-bkm2`, step `nestab-is-stab`, first assertion (trivial master embedding `σ ≡ 0` into `{0}`). -/
theorem nonEmbedKernel_trivial_master (D : FinProb α) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (a b : α) :
    nonEmbedKernel D (fun _ : α => ()) ξ a b = noiseKernel D (1 - ξ) a b := by
  have _ := hξ0
  have _ := hξ1
  unfold nonEmbedKernel graphNoiseKernel noiseKernel
  have h2 : ∑ c : α, D.prob c = 1 := D.sum_eq_one
  beta_reduce
  simp [h2]

/-- CSP_7 `thm:3csp-bkm2`, step `nestab-is-stab`, second assertion. -/
theorem nestab_trivial_master (D : FinProb α) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → α) → ℂ) :
    nestab D (fun _ : α => ()) ξ g = cstab D (1 - ξ) g := by
  have hk : ∀ a b : ι → α, ((∏ i : ι, nonEmbedKernel D (fun _ : α => ()) ξ (a i) (b i) : ℝ)) =
      ∏ i : ι, noiseKernel D (1 - ξ) (a i) (b i) := by
    intro a b
    exact Finset.prod_congr rfl fun i _ => nonEmbedKernel_trivial_master D hξ0 hξ1 _ _
  have hop : nonEmbedOp D (fun _ : α => ()) ξ g = cnoiseOp D (1 - ξ) g := by
    funext x
    unfold nonEmbedOp graphNoiseOp cnoiseOp
    refine Finset.sum_congr rfl fun y _ => ?_
    have := hk x y
    unfold nonEmbedKernel at this
    rw [this]
  unfold nestab cstab FinProb.cinner
  rw [hop]

end NoiseChains
end TrackB
end RestrictedPolynomials
end