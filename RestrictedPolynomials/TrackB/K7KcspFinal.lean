module

public import RestrictedPolynomials.TrackB.K7KcspStep
public import RestrictedPolynomials.TrackB.K7KcspAssembly
public import RestrictedPolynomials.TrackB.K7BaseCase
public import RestrictedPolynomials.TrackB.MaxTStatements
public import RestrictedPolynomials.Frozen.InverseDelta
public import RestrictedPolynomials.ExpIterate

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Final

/-- CSP_7 `thm:kcsp`, `thm:kcsp#induction-on-k`, `sec:solve-rec`, quantitative form, WITHOUT `hconv`:
for every `k ≥ 1` and `α > 0` there is `b > 0` such that `δ = exp(-exp^{[N_k]}(ε^{-b}))`
(`N_k = k7Height k ≤ k^k`) is a valid `δ` for all `ε ∈ (0, 1/2]`, uniformly in the alphabets, `μ`, `ι` and
the functions; no threshold on `|ι|`. Induction on `k`: `k ≤ 2` is `k7_kcsp_small_k_of_bkm2`, `k = 3` is
`k7_kcsp_three_of_bkm2`, `k ≥ 3 → k+1` is `k7_kcsp_step` (so the reduction to `Unif(supp μ)` enters through
the step). The only hypothesis is `hbase`, discharged by `MaxT.k7_hbase_explicit_of_Q`. -/
theorem k7_thm_kcsp_of_bkm2
    (hbase : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∃ (b c : ℝ), 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
          [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
          ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ c * ε ^ b →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖MaxT.corr3 μ f g h‖ →
            δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re)
    (k : ℕ) (hk : 1 ≤ k) {α : ℝ} (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[k7Height k] (ε ^ (-b)))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[k7Height k] (ε ^ (-b))))) (f i)).re) := by
  have key : ∀ k : ℕ, 1 ≤ k → ∀ {α : ℝ}, 0 < α → α ≤ 1 → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[k7Height k] (ε ^ (-b)))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[k7Height k] (ε ^ (-b))))) (f i)).re) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro α hα _
      obtain ⟨b, hb, H⟩ := k7_kcsp_small_k_of_bkm2 hbase 1 (by norm_num) hα
      exact ⟨b, hb, H⟩
    | succ k hk ih =>
      intro α hα hα1
      rcases Nat.lt_or_ge k 3 with h3 | h3
      · interval_cases k
        · obtain ⟨b, hb, H⟩ := k7_kcsp_small_k_of_bkm2 hbase 2 (by norm_num) hα
          exact ⟨b, hb, H⟩
        · obtain ⟨b, hb, H⟩ := k7_kcsp_three_of_bkm2 hbase hα
          exact ⟨b, hb, H⟩
      · obtain ⟨b, hb, H⟩ := ih hα hα1
        obtain ⟨b', hb', H'⟩ := k7_kcsp_step k h3 hα hα1 (k7Height k) ⟨b, hb, H⟩
        rw [k7_height_succ k h3]
        exact ⟨b', hb', H'⟩
  obtain ⟨b, hb, H⟩ := key k hk (lt_min hα one_pos) (min_le_right _ _)
  exact ⟨b, hb, fun ε h0 h1 A _ _ μ hno hat ι _ _ f hf hc i =>
    H ε h0 h1 A μ hno (fun a ha => (min_le_left _ _).trans (hat a ha)) ι f hf hc i⟩

open scoped ComplexOrder in
/-- The paper's `t-inverse#exact-tower-small-eps`, `#small-k-cases`, `#small-eps-exact-form`, WITHOUT
`hconv`: one absolute `C₀` (here `1`), `b = b(k, γ)`, every `ε ∈ (0, 1/2]`, the exact `inverseDelta C₀ k b ε`,
the `ComplexOrder` form (`cstab_im_eq_zero`), no threshold on `|ι|`. This is the hypothesis `T` of
`claim-near-one-regime.md`, i.e. the hypothesis `hT` of `k7_frozen_of_small_eps`. -/
theorem k7_small_eps_exact_of_bkm2
    (hbase : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∃ (b c : ℝ), 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
          [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
          ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ c * ε ^ b →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖MaxT.corr3 μ f g h‖ →
            δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re) :
    ∃ C₀ : ℕ, ∀ k : ℕ, ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, γ ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, (inverseDelta C₀ k b ε : ℂ) ≤
            cstab (μ.marginalPi i) (1 - inverseDelta C₀ k b ε) (f i) := by
  refine ⟨1, fun k γ hγ => ?_⟩
  by_cases hk : 1 ≤ k
  · obtain ⟨b, hb, H⟩ := k7_thm_kcsp_of_bkm2 hbase k hk hγ
    refine ⟨b, hb, fun ε h0 h1 A _ _ μ hno hat ι _ _ f hf hc i => ?_⟩
    have hH := H ε h0 h1 A μ hno hat ι f hf hc i
    have hN : k7Height k ≤ k ^ (1 * k) := by
      rw [one_mul]
      rcases Nat.lt_or_ge k 3 with h3 | h3
      · interval_cases k
        · simp [k7Height]
        · simp [k7Height]
      · exact k7_height_le_pow k h3
    have hle : inverseDelta 1 k b ε ≤ Real.exp (-(Real.exp^[k7Height k] (ε ^ (-b)))) := by
      unfold inverseDelta
      refine Real.exp_le_exp.2 (neg_le_neg (exp_iterate_le_of_le hN _))
    have hpos : 0 < inverseDelta 1 k b ε := Real.exp_pos _
    have hδ1 : Real.exp (-(Real.exp^[k7Height k] (ε ^ (-b)))) ≤ 1 := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.2 (neg_nonpos.2 ?_)
      exact (Real.rpow_nonneg h0.le _).trans (le_exp_iterate _ _)
    have hv := k7_valid_mono (μ.marginalPi i) (f i) hpos hle hδ1 hH
    rw [Complex.le_def, Complex.ofReal_re, Complex.ofReal_im, cstab_im_eq_zero]
    exact ⟨hv, by simp⟩
  · have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨1, one_pos, fun ε _ _ A _ _ μ _ _ ι _ _ f _ _ i => i.elim0⟩


open scoped ComplexOrder in
/-- THE FINAL COMPOSITION: the conclusion is EXACTLY the type of the frozen statement
`inverse_theorem_bklm`, and the only hypothesis is `hQ`, the `Q`-statement of every pattern of `𝒯` (the hypothesis of
`maxT_uniform_of_Q` and of `MaxT.k7_hbase_explicit_of_Q`; what remains of the route is the discharge of
`hQ` through `maxT_induction_of_merge_h64`, with its `hmerge*`, `h64` inputs). The chain is
`k7_frozen_of_small_eps (k7_small_eps_exact_of_bkm2 (MaxT.k7_hbase_explicit_of_Q hQ))`; there is no `hconv`
and no other hypothesis. -/
theorem k7_inverse_theorem_bklm_of_Q
    (hQ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), MaxT.InT S → MaxT.QSet S) :
    ∃ C₀ : ℕ, ∀ k : ℕ, ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)),
        NoNontrivialAbelianEmbeddingPi μ.support → (∀ a ∈ μ.support, γ ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], n₀ ≤ Fintype.card ι →
        ∀ f : ∀ i, (ι → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, (inverseDelta C₀ k b ε : ℂ) ≤
            cstab (μ.marginalPi i) (1 - inverseDelta C₀ k b ε) (f i) :=
  k7_frozen_of_small_eps (k7_small_eps_exact_of_bkm2 (MaxT.k7_hbase_explicit_of_Q hQ))

end Final

end TrackB
end RestrictedPolynomials
end
