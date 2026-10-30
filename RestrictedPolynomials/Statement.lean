import RestrictedPolynomials.Defs

/-!
# The admitted inverse theorem and the statement of the main theorem

This file contains the first of the two `admit`s of the formalization: the inverse theorem of
Bhangale, Khot, Liu and Minzer [CSP_7, Theorem 1] (Theorem 1.4 of the paper). The second is
Dimitrov's theorem (`Dimitrov.lean`), used only for the explicit bounds on `M_k` and `P_k`.
Everything else is proved from these.

The admitted statement is a special case of the one quoted in the paper, in three harmless ways:
all alphabets `Σ₁, …, Σ_k` are the same finite type `α`; the functions are real-valued rather
than complex-valued; and the exponent `b` and threshold `n₀` are allowed to depend on the whole
distribution `μ`, not only on the minimal atom mass `γ`. The number of iterated exponentials is
`k ^ (C₀ * k)` for an absolute constant `C₀`, which is the paper's `k^{O(k)}`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- The parameter `δ = exp(-exp^{(k^{C₀ k})}(ε^{-b}))` of the inverse theorem. -/
def inverseDelta (C₀ k : ℕ) (b ε : ℝ) : ℝ :=
  Real.exp (-(Real.exp^[k ^ (C₀ * k)] (ε ^ (-b))))

/-- **Theorem 1.4** ([CSP_7, Theorem 1]). Let `μ` be a distribution on `α^k` admitting no
nontrivial abelian embedding. For every `ε > 0` there is `n₀` such that for `n ≥ n₀`, if
`1`-bounded `f₁, …, f_k : α^n → ℝ` satisfy `|𝔼_{μ^{⊗n}} ∏ᵢ fᵢ(xᵢ)| ≥ ε`, then
`Stab_{1-δ}(fᵢ) > δ` for every `i`, stability being taken with respect to the marginal `μᵢ`,
where `δ = exp(-exp^{(k^{O(k)})}(ε^{-O_μ(1)}))`.

This is the only unproved statement of the formalization. -/
theorem inverse_theorem :
    ∃ C₀ : ℕ, ∀ (k : ℕ) (α : Type) [Fintype α] [DecidableEq α] (μ : FinProb (Fin k → α)),
      NoNontrivialAbelianEmbedding μ.support →
      ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], n₀ ≤ Fintype.card ι →
        ∀ f : Fin k → (ι → α) → ℝ, (∀ i x, |f i x| ≤ 1) →
          ε ≤ |(μ.pi ι).expect fun X => ∏ i, f i fun t => X t i| →
          ∀ i, inverseDelta C₀ k b ε <
            stab (μ.marginal i) (1 - inverseDelta C₀ k b ε) (f i) := by
  admit

/-- **Theorem 1.1**, as a proposition. There is an absolute constant `C₁` (so `K = k^{C₁ k}` is
`k^{O(k)}`) such that for every `k ≥ 2` there are `M = M_k` and `P = P_k`, with
`M_k ≤ exp(7 k log k) = exp(O(k log k))` and `P_k ≤ exp exp(25 k² log k) = exp exp(O(k² log k))`
(the quantitative proof of Proposition 5.1, which uses Dimitrov's theorem), with the following
property. For every prime `p ≥ P` there are `C, c > 0` such that if `n > exp^{(K)}(1)` and
`A ⊆ 𝔽_p^n` has density at least `C / (log^{(K)} n)^c`, then `A` contains a restricted progression
`x, x + P_1(y), …, x + P_{k-1}(y)` with `y ∈ {0, 2, 3, …, M}^n \ {0}`, whose `k` points are
pairwise distinct. -/
def MainTheorem : Prop :=
  ∃ C₁ : ℕ, ∀ k : ℕ, 2 ≤ k → ∃ M P : ℕ,
    (M : ℝ) ≤ Real.exp (7 * k * Real.log k) ∧
    (P : ℝ) ≤ Real.exp (Real.exp (25 * k ^ 2 * Real.log k)) ∧
    ∀ p : ℕ, p.Prime → P ≤ p →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, Real.exp^[k ^ (C₁ * k)] 1 < n →
        ∀ A : Finset (Fin n → ZMod p),
          C / (Real.log^[k ^ (C₁ * k)] n) ^ c ≤ (A.card : ℝ) / (p : ℝ) ^ n →
          HasRestrictedProgression p M k (A : Set (Fin n → ZMod p))

end RestrictedPolynomials

end
