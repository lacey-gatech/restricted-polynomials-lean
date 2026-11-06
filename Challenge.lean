module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Restricted polynomial progressions in `𝔽_p^n`: Theorem 1.1

This is the statement of record for Theorem 1.1 of A. Burgin, A. Fragkos, D. Kruzel, M. Lacey and
A. Stokolosa, *Reasonable bounds for restricted polynomial progressions in `𝔽_p^n`*,
arXiv:2610.12831.

Fix `k ≥ 2`. There are `M_k = exp(O(k log k))` and `P_k = exp exp(O(k² log k))`, depending only on
`k`, and `K = k^{O(k)}`, with the following property. For every prime `p ≥ P_k` there are
`C, c > 0` such that if `n > exp^{(K)}(1)` and `A ⊆ 𝔽_p^n` has density `|A| / p^n` at least
`C / (log^{(K)} n)^c`, then `A` contains a restricted progression

  `x, x + P_1(y), …, x + P_{k-1}(y)`,  where `P_j(y) = (y_1^j, …, y_n^j)`,

with `y ∈ {0, 2, 3, …, M_k}^n` and `y ≠ 0`. Moreover, the `k` points of every such progression are
pairwise distinct.

The four definitions below are the statement's only project-specific vocabulary. Every other
notion is Mathlib's: `ZMod p` is `𝔽_p` for prime `p`; `Fin n → ZMod p` is `𝔽_p^n`;
`Real.exp^[m]` and `Real.log^[m]` are the `m`-fold iterates of `exp` and `log`.

The deliberate `sorry` below is the Comparator hole. The proved declaration of the same name and
type is in the library module `RestrictedPolynomials.Frozen.MainTheoremProof`, which `comparator.json`
names as the Solution module.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- The step set `Y = {0, 2, 3, …, M}`: the coordinates allowed for the common difference `y`.
The value `1` is excluded, as in the paper. -/
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

/-- **Theorem 1.1**, as a proposition. There is an absolute constant `C₁` (so `K = k^{C₁ k}` is
`k^{O(k)}`) such that for every `k ≥ 2` there are `M = M_k` and `P = P_k`, with
`M_k ≤ exp(7 k log k)` and `P_k ≤ exp exp(25 k² log k)`, with the following property. For every
prime `p ≥ P`:
* the `k` points `x, x + P_1(y), …, x + P_{k-1}(y)` of any restricted progression with
  `y ∈ {0, 2, 3, …, M}^n \ {0}` are pairwise distinct; and
* there are `C, c > 0` such that if `n > exp^{(K)}(1)` and `A ⊆ 𝔽_p^n` has density at least
  `C / (log^{(K)} n)^c`, then `A` contains such a progression. -/
def MainTheorem : Prop :=
  ∃ C₁ : ℕ, ∀ k : ℕ, 2 ≤ k → ∃ M P : ℕ,
    (M : ℝ) ≤ Real.exp (7 * k * Real.log k) ∧
    (P : ℝ) ≤ Real.exp (Real.exp (25 * k ^ 2 * Real.log k)) ∧
    ∀ p : ℕ, p.Prime → P ≤ p →
      (∀ (n : ℕ) (x y : Fin n → ZMod p), (∀ i, ∃ t ∈ stepSet M, y i = t) → y ≠ 0 →
        Function.Injective fun j : Fin k => x + polyTerm j y) ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, Real.exp^[k ^ (C₁ * k)] 1 < n →
        ∀ A : Finset (Fin n → ZMod p),
          C / (Real.log^[k ^ (C₁ * k)] n) ^ c ≤ (A.card : ℝ) / (p : ℝ) ^ n →
          HasRestrictedProgression p M k (A : Set (Fin n → ZMod p))

/-- **Theorem 1.1** (Burgin–Fragkos–Kruzel–Lacey–Stokolosa). -/
theorem main_theorem : MainTheorem := by
  sorry

end RestrictedPolynomials

end
