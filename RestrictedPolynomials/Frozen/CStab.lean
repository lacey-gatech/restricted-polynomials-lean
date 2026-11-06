module

public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.Frozen.CNoiseOp

/-!
# Frozen definition: complex stability

This file holds exactly one declaration. Its statement was fixed and approved by the author
before any proof work, and has not changed since.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The stability `Stab_ρ(f) = ⟨f, N_ρ f⟩_{L²(π^{⊗ι})} = 𝔼_x f(x) · conj(N_ρ f(x))` of a
complex-valued `f`. The source domain is `0 ≤ ρ ≤ 1`; for other real `ρ` the same formula is
evaluated and has no source meaning. -/
def cstab (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) : ℂ :=
  (π.pi ι).cexpect fun x => f x * star (cnoiseOp π ρ f x)

end RestrictedPolynomials

end
