module

public import RestrictedPolynomials.Stability
public import RestrictedPolynomials.InverseCorollary

/-!
# The inverse theorem in every dimension (Proposition 6.6)

* `inverse_theorem_all_dims` : **Proposition 6.6**. The conclusion of the inverse theorem holds
  in every dimension, by padding with dummy coordinates.

This consumer of the frozen `inverse_theorem_bklm` (through `inverse_theorem`) is split out of
`Stability.lean`, so that the general stability lemmas there do not import the frozen draft and
Track B code can use them.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- **Proposition 6.6.** The conclusion of the inverse theorem holds in every dimension, with the
same parameter `δ`. -/
theorem inverse_theorem_all_dims :
    ∃ C₀ : ℕ, ∀ (k : ℕ) (α : Type) [Fintype α] [DecidableEq α] (μ : FinProb (Fin k → α)),
      NoNontrivialAbelianEmbedding μ.support →
      ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
        ∀ f : Fin k → (ι → α) → ℝ, (∀ i x, |f i x| ≤ 1) →
          ε ≤ |(μ.pi ι).expect fun X => ∏ i, f i fun t => X t i| →
          ∀ i, inverseDelta C₀ k b ε <
            stab (μ.marginal i) (1 - inverseDelta C₀ k b ε) (f i) := by
  obtain ⟨C₀, hC₀⟩ := inverse_theorem
  refine ⟨C₀, fun k α _ _ μ hμ => ?_⟩
  obtain ⟨b, hb, hε⟩ := hC₀ k α μ hμ
  refine ⟨b, hb, fun ε hεpos ι _ _ f hf hcorr i => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hε ε hεpos
  -- pad with `n₀` dummy coordinates
  let F : Fin k → (ι ⊕ Fin n₀ → α) → ℝ := fun j y => f j (y ∘ Sum.inl)
  have hF : ∀ j y, |F j y| ≤ 1 := fun j y => hf j _
  have hcard : n₀ ≤ Fintype.card (ι ⊕ Fin n₀) := by simp
  have hcorrF : ε ≤ |(μ.pi (ι ⊕ Fin n₀)).expect fun X => ∏ j, F j fun t => X t j| := by
    have := μ.expect_sumInl (ι := ι) (κ := Fin n₀) fun Y => ∏ j, f j fun t => Y t j
    refine hcorr.trans (le_of_eq ?_)
    rw [← this]
    rfl
  have := hn₀ (ι ⊕ Fin n₀) hcard F hF hcorrF i
  simpa [F, stab_sumInl] using this

end RestrictedPolynomials

end
