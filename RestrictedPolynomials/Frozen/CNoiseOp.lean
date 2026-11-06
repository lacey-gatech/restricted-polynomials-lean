module

public import RestrictedPolynomials.Frozen.NoiseKernel

/-!
# Frozen definition: the complex noise operator

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The noise operator `N_ρ = N_ρ^{⊗ι}` on complex-valued functions:
`N_ρ f(x) = 𝔼_{y ∼_ρ x} f(y)`, the noise being applied independently in each coordinate.
The source domain is `0 ≤ ρ ≤ 1`; for other real `ρ` the same formula is evaluated and has no
source meaning. -/
def cnoiseOp (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  ∑ y, ((∏ i, noiseKernel π ρ (x i) (y i) : ℝ) : ℂ) * f y

end RestrictedPolynomials

end
