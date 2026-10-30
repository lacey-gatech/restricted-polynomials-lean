import RestrictedPolynomials.Counting
import RestrictedPolynomials.CyclicReduction
import RestrictedPolynomials.SameChar
import RestrictedPolynomials.DiffChar
import RestrictedPolynomials.FullRank
import RestrictedPolynomials.QuantFullRank

/-!
# Proposition 3.1: the distribution `μ` admits no nontrivial abelian embedding

With `ℓ = k - 1`, `M = M(ℓ) = exp(O(ℓ log ℓ))` and `P(ℓ) = exp exp(O(ℓ² log ℓ))` from the quantitative
Proposition 5.1 (`full_rank_quant`), and `p > max(P(ℓ), M^ℓ)`: an abelian embedding of the support
of `μ` reduces to one into `ℤ/qℤ` (Lemma 3.7), which is trivial by Lemma 3.4 if `q = p` and by
Lemma 3.5 (Lemma 5.9 here) if `q ≠ p`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- Bounds on `M_k = M(k-1)`. -/
lemma Mℓ_le_exp {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (Mℓ ℓ : ℝ) ≤ Real.exp (7 * ((ℓ + 1 : ℕ) : ℝ) * Real.log ((ℓ + 1 : ℕ) : ℝ)) := by
  refine (Mℓ_growth hℓ).trans (Real.exp_le_exp.2 ?_)
  push_cast
  have : 0 ≤ Real.log ((ℓ : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ ℓ)])
  nlinarith

/-- **Proposition 3.1**, with `M = M_k` and `P = P_k` as in (1.1): `M_k = exp(O(k log k))`,
`P_k = exp exp(O(k² log k))`; for every prime `p ≥ P`, `M^{k-1} < p` and the counting distribution
admits no nontrivial abelian embedding. -/
theorem exists_M_P (k : ℕ) (hk : 2 ≤ k) :
    ∃ M P : ℕ, ∃ hM : 2 ≤ M, (M : ℝ) ≤ Real.exp (7 * k * Real.log k) ∧
      (P : ℝ) ≤ Real.exp (Real.exp (25 * k ^ 2 * Real.log k)) ∧
      ∀ (p : ℕ) [NeZero p], p.Prime → P ≤ p →
        M ^ (k - 1) < p ∧ NoNontrivialAbelianEmbedding (countingDist p k M hM).support := by
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, k = ℓ + 1 := ⟨k - 1, by omega⟩
  have hℓ : 1 ≤ ℓ := by omega
  set M := Mℓ ℓ with hMdef
  have hℓM : ℓ + 1 ≤ M := Mℓ_ge ℓ
  have hM : 2 ≤ M := by omega
  have hMb := Mℓ_le_exp hℓ
  refine ⟨M, max (Pℓ ℓ + 1) (M ^ ℓ + 1), hM, hMb, ?_, fun p _ hp hPp => ?_⟩
  · -- `P_k = max (P(ℓ) + 1) (M^ℓ + 1) ≤ exp exp (25 k² log k)`
    have hpos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    set a := Real.log ((ℓ : ℝ) + 1) with ha
    have ha2 : Real.log 2 ≤ a := Real.log_le_log (by norm_num) (by
      have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      linarith)
    have ha0 : 0 < a := lt_of_lt_of_le (Real.log_pos (by norm_num)) ha2
    have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    set E := Real.exp (20 * (ℓ : ℝ) ^ 2 * a) with hE
    have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
    have hP1 : (Pℓ ℓ : ℝ) ≤ Real.exp E := Pℓ_growth hℓ
    have hM1 : (M : ℝ) ^ ℓ ≤ Real.exp E := by
      have h1 : (M : ℝ) ^ ℓ ≤ Real.exp (7 * ℓ * a) ^ ℓ :=
        pow_le_pow_left₀ (by positivity) (Mℓ_growth hℓ) ℓ
      rw [← Real.exp_nat_mul] at h1
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have : 7 * (ℓ : ℝ) ^ 2 * a ≤ 20 * (ℓ : ℝ) ^ 2 * a := by nlinarith [sq_nonneg (ℓ : ℝ)]
      have h2 : 20 * (ℓ : ℝ) ^ 2 * a ≤ E := by
        have := Real.add_one_le_exp (20 * (ℓ : ℝ) ^ 2 * a)
        linarith
      nlinarith
    have hexp1 : (1 : ℝ) ≤ Real.exp E := Real.one_le_exp (by linarith)
    have hmax : ((max (Pℓ ℓ + 1) (M ^ ℓ + 1) : ℕ) : ℝ) ≤ 2 * Real.exp E := by
      rw [Nat.cast_max]
      refine max_le ?_ ?_ <;> push_cast <;> linarith
    have h2e : 2 * Real.exp E ≤ Real.exp (E + 1) := by
      rw [Real.exp_add]
      have : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      nlinarith [Real.exp_pos E]
    refine hmax.trans (h2e.trans (Real.exp_le_exp.2 ?_))
    -- `E + 1 ≤ exp (25 k² log k)`
    have hbig : 2 ≤ Real.exp (5 * ((ℓ : ℝ) + 1) ^ 2 * a) := by
      have : Real.log 2 ≤ 5 * ((ℓ : ℝ) + 1) ^ 2 * a := by nlinarith [sq_nonneg ((ℓ : ℝ) + 1)]
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ _ := Real.exp_le_exp.2 this
    have hsplit : Real.exp (25 * ((ℓ + 1 : ℕ) : ℝ) ^ 2 * Real.log ((ℓ + 1 : ℕ) : ℝ)) =
        E * Real.exp ((25 * ((ℓ : ℝ) + 1) ^ 2 - 20 * (ℓ : ℝ) ^ 2) * a) := by
      rw [hE, ← Real.exp_add]
      push_cast
      congr 1
      ring
    have hmono : Real.exp (5 * ((ℓ : ℝ) + 1) ^ 2 * a) ≤
        Real.exp ((25 * ((ℓ : ℝ) + 1) ^ 2 - 20 * (ℓ : ℝ) ^ 2) * a) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [sq_nonneg ((ℓ : ℝ) + 1), sq_nonneg (ℓ : ℝ), mul_pos ha0 ha0]
    rw [hsplit]
    nlinarith [Real.exp_pos ((25 * ((ℓ : ℝ) + 1) ^ 2 - 20 * (ℓ : ℝ) ^ 2) * a)]
  have hMℓ : M ^ ℓ < p := by
    have := le_max_right (Pℓ ℓ + 1) (M ^ ℓ + 1); omega
  have hP₀ : Pℓ ℓ < p := by
    have := le_max_left (Pℓ ℓ + 1) (M ^ ℓ + 1); omega
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
    exact diff_char (Ne.symm hqp) (fun L _ lam h1 h2 c hc => full_rank_quant hℓ L p hp hP₀ lam h1 h2 c hc)
      τ heq i' a' b'

end RestrictedPolynomials

end
