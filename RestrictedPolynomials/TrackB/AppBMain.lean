module

public import RestrictedPolynomials.TrackB.AppBMainParts
public import RestrictedPolynomials.TrackB.AppBTrunc1
public import RestrictedPolynomials.TrackB.AppBTrunc2
public import RestrictedPolynomials.TrackB.AppBTrunc3
public import RestrictedPolynomials.TrackB.HomMain
public import RestrictedPolynomials.TrackB.L6Hrb
public import RestrictedPolynomials.TrackB.MergeGenericCores

/-!
# Track B, Appendix B: `soft_truncate_main`, `beta_thm_implies`, and Thm 6.7′

Paper IV App. B (l. 8903-8971, 9375-9388) and Supplement E §proof67. The elementary parts (the
`T′`-split, the harsh-bound conversion, the `√δ` first term, the telescoping, the remainder limit and
the geometric sum) are in `AppBMainParts`. Here the three truncation claims are combined. The only
hypothesis is `hhomP` (Thm 7.14′, `HomPStmt`); `appB_homP_of_hom` lets the layer L5 deliver Thm 7.14
instead. The producer `maxT_thm_6_7_prime_of_hhomP` returns EXACTLY the type of `h67` of the built
`maxT_thm_6_5_prime_of_hmerge_h67_hrb`; the unconditional Thm 6.7′ is stated in `FinalAssembly`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Main

/-- Claim `soft_truncate_main` (l. 8942-8950, 9375-9388): `|E f T'g h| ≤ M ρ^η`, constants depending
on `(m, K, α, crb, Crb)` and the homogeneous constants `(ξ_H, c')`; the choice order of l. 9377-9380
(`ξ = ξ₀ ≤ 1/100` from `soft_trunc3`, then `soft_trunc1/2` for that `ξ`) is carried out inside.
Soft_trunc1, 2, 3 are THEOREMS here (files 2-4), not hypotheses. -/
theorem appB_soft_truncate_main_of_homPAt (m K : ℕ) (crb Crb : ℝ) (hcrb : 0 < crb)
    (hCrb : 0 < Crb) {α : ℝ} (hα : 0 < α) {ξH c' : ℝ} (hξH : 0 < ξH) (hξH1 : ξH < 1)
    (hc' : 0 < c') (hhom : HomPAt m K crb Crb α ξH c') :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' → RelaxedBaseCase ν Sm crb Crb →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          ‖corr3 ν f (appTp (lawY ν) ρ g) h‖ ≤ M * ρ ^ η := by
  obtain ⟨M₃, ξ₀, hM₃, hξ₀, hξ₀1, h3⟩ :=
    appB_soft_trunc3_of_homPAt m K crb Crb hcrb hCrb hα hξH hξH1 hc' hhom
  obtain ⟨δ₃, hδ₃, hδ₃1, h3'⟩ := h3 ξ₀ hξ₀ le_rfl
  obtain ⟨M₁, δ₁, η₁, hM₁, hδ₁, hδ₁1, hη₁, h1⟩ := appB_soft_trunc1 m K hα hξ₀
  obtain ⟨M₂, δ₂, η₂, hM₂, hδ₂, hδ₂1, hη₂, h2⟩ :=
    appB_soft_trunc2 m K hα hξ₀ (by linarith)
  obtain ⟨δh, hδh, hδh1, hh⟩ := appB_harsh_bound_to_power (ξH := ξH) (c' := c' / 2) (M₃ := M₃)
    hξ₀ hξ₀1 hξH hξH1 (by positivity) (by linarith)
  refine ⟨M₁ + M₂ + 5, min (min δ₁ δ₂) (min δ₃ δh), min (min η₁ η₂) ξ₀, by linarith,
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδh),
    (min_le_right _ _).trans ((min_le_right _ _).trans hδh1),
    lt_min (lt_min hη₁ hη₂) hξ₀, ?_⟩
  intro ρ hρ hρle X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR hRB n f g h hf hg hh'
  have hρ1' : ρ ≤ δ₁ := hρle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρ2' : ρ ≤ δ₂ := hρle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρ3' : ρ ≤ δ₃ := hρle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρh' : ρ ≤ δh := hρle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ1 : ρ ≤ 1 := hρ1'.trans hδ₁1
  have e1 : ρ ^ η₁ ≤ ρ ^ (min (min η₁ η₂) ξ₀) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : ρ ^ η₂ ≤ ρ ^ (min (min η₁ η₂) ξ₀) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : ρ ^ ξ₀ ≤ ρ ^ (min (min η₁ η₂) ξ₀) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (min_le_right _ _)
  have t1 := h1 ρ hρ hρ1' X Y Z hX hY hZ ν Sg Sm Phi' hR n f g h hf hg hh'
  have t2 := h2 ρ hρ hρ2' X Y Z hX hY hZ ν Sg Sm Phi' hR n f g h hf hg hh'
  have t3 := h3' ρ hρ hρ3' X Y Z hX hY hZ ν Sg Sm Phi' hR hRB n f g h hf hg hh'
  have t4 := hh ρ hρ hρh'
  have hsplit := appB_main_split ν Sm ρ ξ₀ f g h
  have m1 : M₁ * ρ ^ η₁ ≤ M₁ * ρ ^ (min (min η₁ η₂) ξ₀) :=
    mul_le_mul_of_nonneg_left e1 (by linarith)
  have m2 : M₂ * ρ ^ η₂ ≤ M₂ * ρ ^ (min (min η₁ η₂) ξ₀) :=
    mul_le_mul_of_nonneg_left e2 (by linarith)
  have hexp : (M₁ + M₂ + 5) * ρ ^ (min (min η₁ η₂) ξ₀) =
      M₁ * ρ ^ (min (min η₁ η₂) ξ₀) + M₂ * ρ ^ (min (min η₁ η₂) ξ₀) +
        5 * ρ ^ (min (min η₁ η₂) ξ₀) := by ring
  rw [hexp]
  linarith

/-- Claim `beta_thm_implies` (l. 4347-4349; proof l. 8903-8956): Thm 7.14′ implies the relaxed
theorem, in the `∀ K` form and on `𝒯` (Thm 6.7′). `Rel67` plus `RelaxedBaseCase` are the
hypotheses of Thm 6.7′ (items 1, 3-9). -/
theorem appB_beta_thm_implies_of_homPAt (m K : ℕ) (crb Crb : ℝ) (hcrb : 0 < crb)
    (hCrb : 0 < Crb) {α : ℝ} (hα : 0 < α) {ξH c' : ℝ} (hξH : 0 < ξH) (hξH1 : ξH < 1)
    (hc' : 0 < c') (hhom : HomPAt m K crb Crb α ξH c') :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' → RelaxedBaseCase ν Sm crb Crb →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          (cstab (lawY ν) (1 - δ) g).re ≤ δ → ‖corr3 ν f g h‖ ≤ M * δ ^ η := by
  obtain ⟨M, δ₀, η, hM, hδ₀, hδ₀1, hη, hmain⟩ :=
    appB_soft_truncate_main_of_homPAt m K crb Crb hcrb hCrb hα hξH hξH1 hc' hhom
  have hq : 0 < 1 - (2 : ℝ) ^ (-η) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (z := -η) (by norm_num)
      (by linarith)
    linarith
  have hC : 0 < (1 - (2 : ℝ) ^ (-η))⁻¹ := inv_pos.2 hq
  have hMC : 0 < M * (1 - (2 : ℝ) ^ (-η))⁻¹ := mul_pos (by linarith) hC
  refine ⟨1 + M * (1 - (2 : ℝ) ^ (-η))⁻¹, δ₀, min η (1 / 2), by linarith, hδ₀, hδ₀1,
    lt_min hη (by norm_num), ?_⟩
  intro δ hδ hδle X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR hRB n f g h hf hg hh hs
  have hδ1 : δ ≤ 1 := hδle.trans hδ₀1
  have hfirst := appB_first_term ν hδ hδ1 f g h hf hh hs
  have hsum : ∀ J : ℕ, ∑ j ∈ range J, ‖corr3 ν f (appTp (lawY ν) (δ / 2 ^ j) g) h‖ ≤
      M * (1 - (2 : ℝ) ^ (-η))⁻¹ * δ ^ η := by
    intro J
    refine appB_geometric_sum (by linarith) hδ hη _ (fun j => ?_) J
    have hpos : 0 < δ / 2 ^ j := by positivity
    have hle : δ / 2 ^ j ≤ δ₀ :=
      (div_le_self hδ.le (one_le_pow₀ (by norm_num))).trans hδle
    exact hmain (δ / 2 ^ j) hpos hle X Y Z hX hY hZ ν Sg Sm Phi' hR hRB n f g h hf hg hh
  have hall : ∀ ε : ℝ, 0 < ε →
      ‖corr3 ν f g h‖ ≤ (Real.sqrt δ + M * (1 - (2 : ℝ) ^ (-η))⁻¹ * δ ^ η) + ε := by
    intro ε hε
    obtain ⟨J, hJ⟩ := appB_remainder_small ν δ f g h hf hh hε
    have := appB_split_telescope ν δ J f g h
    linarith [hsum J]
  have hfin := le_of_forall_pos_le_add hall
  have e1 : Real.sqrt δ ≤ δ ^ (min η (1 / 2)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_right _ _)
  have e2 : δ ^ η ≤ δ ^ (min η (1 / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
  have m2 : M * (1 - (2 : ℝ) ^ (-η))⁻¹ * δ ^ η ≤
      M * (1 - (2 : ℝ) ^ (-η))⁻¹ * δ ^ (min η (1 / 2)) :=
    mul_le_mul_of_nonneg_left e2 hMC.le
  have hexp : (1 + M * (1 - (2 : ℝ) ^ (-η))⁻¹) * δ ^ (min η (1 / 2)) =
      δ ^ (min η (1 / 2)) + M * (1 - (2 : ℝ) ^ (-η))⁻¹ * δ ^ (min η (1 / 2)) := by ring
  rw [hexp]
  linarith

end Main

/-- Supplement E, `thm:6.7-prime`: Thm 6.7′ in EXACTLY the type of `h67` of
`maxT_thm_6_5_prime_of_hmerge_h67_hrb`, conditional only on Thm 7.14′ (`hhomP`). -/
theorem maxT_thm_6_7_prime_of_hhomP (hhomP : HomPStmt) :
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
          (cstab (lawY ν) (1 - δ) g).re ≤ δ → ‖corr3 ν f g h‖ ≤ M * δ ^ η := by
  intro m K c C α hα hc hC
  obtain ⟨ξ, c', hξ, hξ1, hc', hhom⟩ := hhomP m K c C α hα hc hC
  obtain ⟨M, δ₀, η, hM, hδ₀, hδ₀1, hη, hb⟩ :=
    appB_beta_thm_implies_of_homPAt m K c C hc hC hα hξ hξ1 hc' hhom
  refine ⟨M, δ₀, η, hM, hδ₀, hδ₀1, hη, ?_⟩
  intro δ hδ hδle X Y Z _ _ _ _ _ _ hX hY hZ ν hat hT hyz hunif Sg Sm Phi' hsub hRB hwit hxy
    hmerge n f g h hf hg hh hs
  exact hb δ hδ hδle X Y Z hX hY hZ ν Sg Sm Phi'
    ⟨hat, hT, hyz, hunif, hsub, hRB.1, hwit, hxy, hmerge⟩ hRB n f g h hf hg hh hs

/-- compile-time check (not a target): the producer fed with the built Thm 7.14′ feeds
`maxT_thm_6_5_prime_of_hmerge_h67_hrb`, together with the built merge core and `l6_hrb`. -/
example :=
  @maxT_thm_6_5_prime_of_hmerge_h67_hrb
    (fun m _ hα _ _ _ hM hδ0 hδ1 hη => mgen_sStmtY_of_mergeX m hα hM hδ0 hδ1 hη)
    (maxT_thm_6_7_prime_of_hhomP nonembed_homogenous_prime) l6_hrb

end TrackB
end RestrictedPolynomials
end
