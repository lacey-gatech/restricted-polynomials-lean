module

public import RestrictedPolynomials.TrackB.K7KcspFinal
public import RestrictedPolynomials.TrackB.MaxTInduct
public import RestrictedPolynomials.TrackB.MaxTSec6Relaxed65
public import RestrictedPolynomials.TrackB.MergeGenericCores
public import RestrictedPolynomials.TrackB.L6Hrb
public import RestrictedPolynomials.TrackB.HomMain
public import RestrictedPolynomials.TrackB.AppBMain

/-!
# Track B final assembly: `inverse_theorem_bklm`

The composition of the built Track B theorems into a proof of the frozen statement of
`RestrictedPolynomials.inverse_theorem_bklm` (Theorem 1.4 = [CSP_7, Thm 1]). No hypothesis remains:

* `maxT_thm_6_7_prime`: Thm 6.7′, the producer `maxT_thm_6_7_prime_of_hhomP` fed with Thm 7.14′
  (`nonembed_homogenous_prime`);
* `maxT_h64`: Thm 6.5′ in the shape of `h64`, from the merge core `mgen_sStmtY_of_mergeX`, Thm 6.7′
  and the relaxed base case `l6_hrb`;
* `maxT_hQ`: `Q` on every pattern of `𝒯`, by `maxT_induction_of_merge_h64` with the three Q-form
  merge cores `mgen_qSet_of_merge{X,Y,Z}` and `maxT_h64`;
* `trackB_inverse_theorem_bklm`: the K7 side `k7_inverse_theorem_bklm_of_Q` applied to `maxT_hQ`.

This module imports no frozen theorem file and no provider.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

/-- Thm 6.7′ (Supplement E, `thm:6.7-prime`), unconditional: the type of the hypothesis `h67` of
`maxT_thm_6_5_prime_of_hmerge_h67_hrb`. -/
theorem maxT_thm_6_7_prime :
    ∀ (m K : ℕ) (c C α : ℝ), 0 < α → 0 < c → 0 < C →
      ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) → InT ν.support →
        (∀ (y : Y) (z : Z), ∃ x, (x, y, z) ∈ ν.support) →
        (∀ (y : Y) (z : Z), ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ (Sg Sm : Finset X) (Phi' : Finset Z), Sm ⊆ Sg → RelaxedBaseCase ν Sm c C →
        (∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (a : U → X)
            (νt : FinProb (U × Y × ↥Phi')),
          Fintype.card U ≤ K ∧ (∀ u, a u ∈ Sg) ∧ (∀ x ∈ Sg, ∃ u, a u = x) ∧
          (∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support) ∧ PMaxSet νt.support ∧
          FullyMergedSet νt.support ∧ 2 ≤ Fintype.card Y ∧ InT νt.support) →
        (∀ x ∈ Sg, ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support) → mergeImpliesX ν.support →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          (cstab (lawY ν) (1 - δ) g).re ≤ δ → ‖corr3 ν f g h‖ ≤ M * δ ^ η :=
  maxT_thm_6_7_prime_of_hhomP nonembed_homogenous_prime

/-- Thm 6.5′ (Supplement E, `thm:6.5-prime`) in exactly the shape of `h64` of
`maxT_induction_of_merge_h64`. -/
theorem maxT_h64 :
    ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → FullyMergedSet S → PMaxSet S →
        1 < Fintype.card X → QY S :=
  maxT_thm_6_5_prime_of_hmerge_h67_hrb mgen_sStmtY_of_mergeX maxT_thm_6_7_prime l6_hrb

/-- `Q` on every pattern of `𝒯` (Supplement E, `prop:induction`): the hypothesis `hQ` of
`k7_inverse_theorem_bklm_of_Q`. -/
theorem maxT_hQ :
    ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → QSet S :=
  fun X Y Z _ _ _ _ _ _ S hS =>
    maxT_induction_of_merge_h64 mgen_qSet_of_mergeX mgen_qSet_of_mergeY mgen_qSet_of_mergeZ
      maxT_h64 X Y Z S hS

open scoped ComplexOrder in
/-- The frozen statement `RestrictedPolynomials.inverse_theorem_bklm` (Theorem 1.4), proved. -/
theorem trackB_inverse_theorem_bklm :
    ∃ C₀ : ℕ, ∀ k : ℕ, ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)),
        NoNontrivialAbelianEmbeddingPi μ.support → (∀ a ∈ μ.support, γ ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], n₀ ≤ Fintype.card ι →
        ∀ f : ∀ i, (ι → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, (inverseDelta C₀ k b ε : ℂ) ≤
            cstab (μ.marginalPi i) (1 - inverseDelta C₀ k b ε) (f i) :=
  k7_inverse_theorem_bklm_of_Q maxT_hQ

end TrackB
end RestrictedPolynomials
end
