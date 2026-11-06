module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Definitions for Supplement C (Dubinin's hedgehog bound)

Source: Supplement C. These are the definitions used by the Lean statements of the Supplement: the
Dirichlet energy, the stars `spikes` and `starSet`, the radius `c* = R 4^{-1/N}`, the circle potential of
Fekete points, the arcsine measure and potential of the symmetric star, the symmetric test function
`u*`, the zigzag data of Lemma 6.1 and the angular map `Φ` of Lemma 6.2.
-/

@[expose] public section

open MeasureTheory
open scoped Real

noncomputable section

namespace RestrictedPolynomials

/-- Dirichlet energy `∫ |∇u|²` over `ℂ = ℝ²` with Lebesgue measure. -/
def dirichletEnergy (u : ℂ → ℝ) : ℝ := ∫ z, ‖fderiv ℝ u z‖ ^ 2

/-- The star `⋃_k [0, R e^{iθ_k}]`. -/
def spikes {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) : Set ℂ :=
  ⋃ k, segment ℝ (0 : ℂ) ((R : ℂ) * Complex.exp ((θ k : ℂ) * Complex.I))

/-- The symmetric star `K* = {z : z^N ∈ [0, R^N]}`. -/
def starSet (N : ℕ) (R : ℝ) : Set ℂ := {z | ∃ x ∈ Set.Icc (0 : ℝ) (R ^ N), z ^ N = (x : ℂ)}

/-- `c* = R 4^{-1/N}`. -/
def starRadius (N : ℕ) (R : ℝ) : ℝ := R * (4 : ℝ) ^ (-(1 / (N : ℝ)))

/-- `ω = e^{2πi/N}`. -/
def rootN (N : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- Potential of `m` circles: `U(z) = -(1/m) ∑ log max(|z - z_a|, δ)`. -/
def circlePotential (m : ℕ) (δ : ℝ) (zs : Fin m → ℂ) (z : ℂ) : ℝ :=
  -(1 / (m : ℝ)) * ∑ a, Real.log (max ‖z - zs a‖ δ)

/-- The point `ω^k x(s)^{1/N}` of the support of the arcsine measure, `x(s) = (R^N/2)(1 + cos s)`. -/
def starPoint (N : ℕ) (R : ℝ) (k : Fin N) (s : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)) *
    (((R ^ N / 2 * (1 + Real.cos s)) ^ ((1 : ℝ) / N) : ℝ) : ℂ)

/-- The probability measure `ν`: `∫ f dν = (1/π) ∫_0^π (1/N) ∑_k f(ω^k x(s)^{1/N}) ds`. -/
def arcsineMeasure (N : ℕ) (R : ℝ) : Measure ℂ :=
  ENNReal.ofReal (1 / (Real.pi * N)) •
    ∑ k : Fin N, (volume.restrict (Set.Ioc 0 Real.pi)).map (starPoint N R k)

/-- `U^ν(z) = ∫ -log|z - w| dν(w)`. -/
def arcsinePotential (N : ℕ) (R : ℝ) (z : ℂ) : ℝ :=
  ∫ w, -Real.log ‖z - w‖ ∂(arcsineMeasure N R)

/-- The symmetric test function `u*`, with `G = -log c* - U^ν`, `β = log((r'-R)/c*)`. -/
def symTest (N : ℕ) (R r' α : ℝ) (z : ℂ) : ℝ :=
  min 1 (max 0 ((Real.log ((r' - R) / starRadius N R) -
    (-Real.log (starRadius N R) - arcsinePotential N R z)) /
      (Real.log ((r' - R) / starRadius N R) - α)))

/-- A leg of the zigzag: on `[lo, hi]` the path is `ψ θ = val + sign (θ - lo)`. -/
structure Leg where
  lo : ℝ
  hi : ℝ
  sign : ℝ
  val : ℝ

/-- The affine function of a leg. -/
def Leg.psi (l : Leg) (t : ℝ) : ℝ := l.val + l.sign * (t - l.lo)

/-- The open interval of values swept by a leg. -/
def Leg.range (l : Leg) : Set ℝ := Set.Ioo (min l.val (l.psi l.hi)) (max l.val (l.psi l.hi))

/-- The zigzag data for directions `θ`: the path `ψ` and its legs. -/
def IsZigzag (N : ℕ) (θ : Fin N → ℝ) (ψ : ℝ → ℝ) (L : List Leg) : Prop :=
  Continuous ψ ∧ Function.Periodic ψ (2 * Real.pi) ∧ LipschitzWith 1 ψ ∧
  (∀ t, ψ t ∈ Set.Icc (0 : ℝ) (Real.pi / N)) ∧ (∀ k, ψ (θ k) = 0) ∧
  (∀ l ∈ L, l.lo < l.hi ∧ (l.sign = 1 ∨ l.sign = -1) ∧ ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t) ∧
  L.IsChain (fun a b => a.hi = b.lo) ∧
  (∃ t₀, (L.head?.map Leg.lo) = some t₀ ∧ (L.getLast?.map Leg.hi) = some (t₀ + 2 * Real.pi)) ∧
  ∃ F : Finset ℝ, ∀ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / N), φ ∉ F →
    (L.map fun l => Set.indicator l.range (fun _ => (1 : ℕ)) φ).sum = 2 * N

/-- `Φ(ρ e^{iθ}) = ρ e^{iψ(θ)}`. -/
def phiMap (ψ : ℝ → ℝ) (z : ℂ) : ℂ :=
  (‖z‖ : ℂ) * Complex.exp ((ψ (Complex.arg z) : ℂ) * Complex.I)

end RestrictedPolynomials
