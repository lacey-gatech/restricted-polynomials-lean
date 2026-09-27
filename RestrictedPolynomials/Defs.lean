import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

/-!
# Definitions

The objects of the paper, stated with as little machinery as possible.

* `FinProb α` : a probability distribution on a finite set `α`, with expectation `expect`,
  product measure `pi` (the paper's `π^{⊗n}`) and marginals `marginal`.
* `noiseOp`, `stab` : the noise operator `N_ρ` and the stability `Stab_ρ` (Section 2).
* `condExp`, `esPart`, `lowDegWeight` : the Efron–Stein decomposition and `W_{≤d}` (Section 2).
* `IsAbelianEmbedding`, `NoNontrivialAbelianEmbedding` : Definition 1.3.
* `stepSet`, `polyTerm`, `HasRestrictedProgression` : the configuration of Theorem 1.1.

Coordinates are indexed by an arbitrary finite type `ι` rather than `Fin n`, because
restricting to a coordinate fiber produces the index type `↥S` for `S : Finset ι`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-! ## Finite probability distributions -/

/-- A probability distribution on a finite set. -/
structure FinProb (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

namespace FinProb

variable {α : Type*} [Fintype α]

/-- `𝔼_π f = ∑ₓ π(x) f(x)`. -/
def expect (π : FinProb α) (f : α → ℝ) : ℝ := ∑ a, π.prob a * f a

/-- The support `{a : π(a) ≠ 0}`. -/
def support (π : FinProb α) : Set α := {a | π.prob a ≠ 0}

/-- The product measure `π^{⊗ι}` on `ι → α`. -/
def pi (π : FinProb α) (ι : Type*) [Fintype ι] [DecidableEq ι] : FinProb (ι → α) where
  prob x := ∏ i, π.prob (x i)
  nonneg _ := prod_nonneg fun i _ => π.nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum (fun _ a => π.prob a)]
    simp [π.sum_eq_one]

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

/-- The one-coordinate `ρ`-correlated kernel: `y = x` with probability `ρ`, and otherwise
`y ∼ π` independently of `x`. -/
def noiseKernel (π : FinProb α) (ρ : ℝ) (a b : α) : ℝ :=
  ρ * (if a = b then 1 else 0) + (1 - ρ) * π.prob b

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

/-! ## Restricted polynomial progressions -/

/-- The step set `Y = {0, 2, 3, …, M}`. -/
def stepSet (M : ℕ) : Finset ℕ := insert 0 (Icc 2 M)

/-- `P_j(y) = (y₁^j, …, y_n^j)` for `j ≥ 1`, and `P_0(y) = 0`, so that the progression
`x + P_0(y), …, x + P_{k-1}(y)` is `x, x + P_1(y), …, x + P_{k-1}(y)`. -/
def polyTerm {ι : Type*} {p : ℕ} (j : ℕ) (y : ι → ZMod p) : ι → ZMod p :=
  fun i => if j = 0 then 0 else y i ^ j

/-- `A` contains a nontrivial restricted `k`-term polynomial progression
`x, x + P_1(y), …, x + P_{k-1}(y)` with `y ∈ Y^n \ {0}`, and its `k` points are pairwise
distinct. -/
def HasRestrictedProgression {ι : Type*} (p M k : ℕ) (A : Set (ι → ZMod p)) : Prop :=
  ∃ x y : ι → ZMod p, (∀ i, ∃ t ∈ stepSet M, y i = t) ∧ y ≠ 0 ∧
    (∀ j : Fin k, x + polyTerm j y ∈ A) ∧ Function.Injective fun j : Fin k => x + polyTerm j y

end RestrictedPolynomials

end
