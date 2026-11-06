module

public import RestrictedPolynomials.FinProb
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbSupport
public import RestrictedPolynomials.Frozen.NoiseKernel
public import RestrictedPolynomials.Frozen.StepSet
public import RestrictedPolynomials.Frozen.PolyTerm
public import RestrictedPolynomials.Frozen.HasRestrictedProgression

/-!
# Definitions

The objects of the paper, stated with as little machinery as possible. The definitions that
carry the meaning of the frozen statements live one per file in `RestrictedPolynomials.Frozen`
(`FinProb.pi`, `FinProb.support`, `noiseKernel`, `stepSet`, `polyTerm`,
`HasRestrictedProgression`, ...) and the structure `FinProb` in `RestrictedPolynomials.FinProb`;
this file imports them and adds the rest.

* `FinProb.expect`, `FinProb.marginal`, `FinProb.uniform` : expectation, marginals and the
  uniform distribution.
* `noiseOp`, `stab` : the noise operator `N_ρ` and the stability `Stab_ρ` (Section 2).
* `condExp`, `esPart`, `lowDegWeight` : the Efron–Stein decomposition and `W_{≤d}` (Section 2).
* `IsAbelianEmbedding`, `NoNontrivialAbelianEmbedding` : Definition 1.3.

Coordinates are indexed by an arbitrary finite type `ι` rather than `Fin n`, because
restricting to a coordinate fiber produces the index type `↥S` for `S : Finset ι`.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-! ## Finite probability distributions -/

namespace FinProb

variable {α : Type*} [Fintype α]

/-- `𝔼_π f = ∑ₓ π(x) f(x)`. -/
def expect (π : FinProb α) (f : α → ℝ) : ℝ := ∑ a, π.prob a * f a

/-- The marginal of a distribution on `Fin k → α` on its `j`-th coordinate. -/
def marginal [DecidableEq α] {k : ℕ} (μ : FinProb (Fin k → α)) (j : Fin k) : FinProb α where
  prob a := ∑ t with t j = a, μ.prob t
  nonneg _ := sum_nonneg fun t _ => μ.nonneg t
  sum_eq_one := by
    rw [← μ.sum_eq_one, ← sum_fiberwise univ (fun t => t j) μ.prob]

/-- The uniform distribution. -/
def uniform [Nonempty α] : FinProb α where
  prob _ := 1 / Fintype.card α
  nonneg _ := by positivity
  sum_eq_one := by simp

end FinProb

/-! ## Noise operator and stability -/

section Noise

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The noise operator `N_ρ = N_ρ^{⊗ι}`: the noise is applied independently in each coordinate,
`N_ρ f(x) = 𝔼_{y ∼_ρ x} f(y)`. -/
def noiseOp (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  ∑ y, (∏ i, noiseKernel π ρ (x i) (y i)) * f y

/-- The stability `Stab_ρ(f) = ⟨f, N_ρ f⟩_{L²(π^{⊗ι})}`. -/
def stab (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℝ) : ℝ :=
  (π.pi ι).expect fun x => f x * noiseOp π ρ f x

/-! ## Efron–Stein decomposition -/

/-- The conditional expectation `𝔼(f(y) | y_T = x_T)`: the coordinates in `T` are fixed to
those of `x` and the others are averaged over `π`. -/
def condExp (π : FinProb α) (T : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  (π.pi ι).expect fun y => f (T.piecewise x y)

/-- The Efron–Stein component
`f^{=S} = ∑_{T ⊆ S} (-1)^{|S \ T|} 𝔼(f | x_T)`. -/
def esPart (π : FinProb α) (S : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * condExp π T f x

/-- The weight at degree at most `d`, `W_{≤d}(f) = ∑_{|S| ≤ d} ‖f^{=S}‖₂²`. -/
def lowDegWeight (π : FinProb α) (d : ℕ) (f : (ι → α) → ℝ) : ℝ :=
  ∑ S with S.card ≤ d, (π.pi ι).expect fun x => esPart π S f x ^ 2

end Noise

/-! ## Abelian embeddings (Definition 1.3) -/

section Embedding

variable {α : Type*} {k : ℕ}

/-- Maps `σ i : α → G` form an abelian embedding of `S ⊆ α^k` if `∑ᵢ σᵢ(aᵢ) = 0` on `S`. -/
def IsAbelianEmbedding (S : Set (Fin k → α)) {G : Type*} [AddCommGroup G]
    (σ : Fin k → α → G) : Prop :=
  ∀ a ∈ S, ∑ i, σ i (a i) = 0

/-- Every abelian embedding of `S`, into every abelian group, is trivial (all maps constant). -/
def NoNontrivialAbelianEmbedding (S : Set (Fin k → α)) : Prop :=
  ∀ (G : Type) [AddCommGroup G] (σ : Fin k → α → G), IsAbelianEmbedding S σ →
    ∀ i a b, σ i a = σ i b

end Embedding

end RestrictedPolynomials

end
