import RestrictedPolynomials.Counting
import RestrictedPolynomials.CyclicReduction
import RestrictedPolynomials.SameChar
import RestrictedPolynomials.DiffChar
import RestrictedPolynomials.FullRank

/-!
# Proposition 3.2: the distribution `μ` admits no nontrivial abelian embedding

With `ℓ = k - 1`, `M = M(ℓ)` from Proposition 5.1 and `p > max(P(ℓ), M^ℓ)`: an abelian embedding
of the support of `μ` reduces to one into `ℤ/qℤ` (Lemma 3.1), which is trivial by Lemma 4.1 if
`q = p` and by Lemma 5.9 if `q ≠ p`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- **Proposition 3.2**, with `M = M_k` and `P = P_k` as in (1.1): for every prime `p ≥ P`,
`M^{k-1} < p` and the counting distribution admits no nontrivial abelian embedding. -/
theorem exists_M_P (k : ℕ) (hk : 2 ≤ k) :
    ∃ M P : ℕ, ∃ hM : 2 ≤ M, ∀ (p : ℕ) [NeZero p], p.Prime → P ≤ p →
      M ^ (k - 1) < p ∧ NoNontrivialAbelianEmbedding (countingDist p k M hM).support := by
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, k = ℓ + 1 := ⟨k - 1, by omega⟩
  have hℓ : 1 ≤ ℓ := by omega
  obtain ⟨M, P₀, hℓM, hfull⟩ := full_rank ℓ
  have hM : 2 ≤ M := by omega
  refine ⟨M, max (P₀ + 1) (M ^ ℓ + 1), hM, fun p _ hp hPp => ?_⟩
  have hMℓ : M ^ ℓ < p := by
    have := le_max_right (P₀ + 1) (M ^ ℓ + 1); omega
  have hP₀ : P₀ < p := by
    have := le_max_left (P₀ + 1) (M ^ ℓ + 1); omega
  have hMp : M < p := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ ℓ := Nat.pow_le_pow_right (by omega) hℓ
      _ < p := hMℓ
  refine ⟨by simpa using hMℓ, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  intro G _ σ hσ i a b
  by_contra hne
  -- reduce to a cyclic group of prime order
  obtain ⟨q, hq, τ, hτ, i', a', b', hτne⟩ :=
    cyclic_reduction (countingDist p (ℓ + 1) M hM).support σ hσ ⟨i, a, b, hne⟩
  -- the embedding equations
  have heq : ∀ x : ZMod p, ∀ y ∈ stepSet M, ∑ j, τ j (x + pw j (y : ZMod p)) = 0 :=
    fun x y hy => hτ _ (progTuple_mem_support hM x hy)
  apply hτne
  by_cases hqp : q = p
  · subst hqp
    exact same_char hℓM hMp τ heq i' a' b'
  · have : Fact q.Prime := ⟨hq⟩
    exact diff_char (Ne.symm hqp) (fun L _ lam h1 h2 c hc => hfull L p hp hP₀ lam h1 h2 c hc)
      τ heq i' a' b'

end RestrictedPolynomials

end
