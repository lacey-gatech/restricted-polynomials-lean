module

public import RestrictedPolynomials.TrackB.MaxTOps

/-!
# Track B: properties of the law `ν` of paper IV Lemma 6.9

Steps `uniform-yz-marginal`, `direct-properties`, `sigma-prime-times-gamma-in-support`
(paper IV, `writeup_stability.tex` l. 3583-3598, 3974-3975).

`ν` is universal over laws with the support of the merge `S³` and a uniform
`(y,z)`-marginal. It is in fact unique, because `y, z ⇒ x` holds on the merge.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section L6Nu
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- paper IV `lem:nu-satisfies`, step `uniform-yz-marginal`. -/
theorem l6_nu_exists (μ : FinProb (X × Y × Z)) (hμ : InT μ.support) {ℓ₁ ℓ₂ : ℕ}
    (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂)
    (hc₁ : ∀ (x : X) (y : Y), ∃ w : PathX (lawSwapXZ μ) ℓ₁ h₁,
      (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support)
    (hc₂ : ∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁),
      ∃ v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂,
        (v, y, w) ∈ (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support)
    (a : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂ → PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂)
    (ha : MergeRep (mergeGraphX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support) a) :
    ∃ ν : FinProb (↥(Set.range a) × Y × PathX (lawSwapXZ μ) ℓ₁ h₁),
      ν.support = (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support ∧
      (∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁), ∑ x, ν.prob (x, y, w) =
        1 / ((Fintype.card Y : ℝ) * Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁))) ∧
      (∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁), ∃ x, (x, y, w) ∈ ν.support) := by
  obtain ⟨-, -, h3, h4, h5, -, -⟩ := inT_construction μ hμ h₁ h₂ hc₁ hc₂ a ha
  obtain ⟨nX, nY, nZ, -⟩ := PairwiseConnected3.nonempty_alphabets h3.1
  have hu := existsUnique_of_impliesX h4 (fun y z => by
    obtain ⟨x', hx'⟩ := h5 y z
    exact ⟨x', hx'⟩)
  have hs := nuOf_support hu
  refine ⟨nuOf _, hs, fun y w => nuOf_marginal_yz _ y w, fun y w => ?_⟩
  obtain ⟨x', hx'⟩ := h5 y w
  exact ⟨x', by rw [hs]; exact hx'⟩

/-- paper IV `lem:nu-satisfies`, step `direct-properties` (hypotheses 1, 2, 3, 7 of Thm 6.7 for `ν`). -/
theorem l6_nu_direct_properties (m : ℕ) (hm : 1 ≤ m) (hX : Fintype.card X ≤ m)
    (hY : Fintype.card Y ≤ m) (hZ : Fintype.card Z ≤ m)
    (μ : FinProb (X × Y × Z)) (hμ : InT μ.support) {ℓ₁ ℓ₂ : ℕ}
    (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂)
    (hc₁ : ∀ (x : X) (y : Y), ∃ w : PathX (lawSwapXZ μ) ℓ₁ h₁,
      (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support)
    (hc₂ : ∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁),
      ∃ v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂,
        (v, y, w) ∈ (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support)
    (a : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂ → PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂)
    (ha : MergeRep (mergeGraphX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support) a)
    (ν : FinProb (↥(Set.range a) × Y × PathX (lawSwapXZ μ) ℓ₁ h₁))
    (hsupp : ν.support = (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support)
    (hyz : ∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁), ∑ x, ν.prob (x, y, w) =
      1 / ((Fintype.card Y : ℝ) * Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁))) :
    (∀ p ∈ ν.support, 1 / (((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) ^ 2) ≤ ν.prob p) ∧
    Fintype.card ↥(Set.range a) ≤ m ^ (ℓ₁ + ℓ₂) ∧ Fintype.card Y ≤ m ^ (ℓ₁ + ℓ₂) ∧
    Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁) ≤ m ^ (ℓ₁ + ℓ₂) ∧
    PairwiseConnected3 ν.support ∧ mergeImpliesX ν.support := by
  obtain ⟨-, -, h3, h4, -, -, -⟩ := inT_construction μ hμ h₁ h₂ hc₁ hc₂ a ha
  have hpc : PairwiseConnected3 ν.support := by rw [hsupp]; exact h3.1
  have hmi : mergeImpliesX ν.support := by rw [hsupp]; exact h4
  have hℓ₁ : 1 ≤ ℓ₁ := by obtain ⟨k, hk⟩ := h₁; omega
  have hmono : ∀ k, k ≤ ℓ₁ + ℓ₂ → m ^ k ≤ m ^ (ℓ₁ + ℓ₂) := fun k hk => Nat.pow_le_pow_right hm hk
  have cY : Fintype.card Y ≤ m ^ (ℓ₁ + ℓ₂) :=
    hY.trans ((Nat.le_self_pow (n := ℓ₁ + ℓ₂) (by omega) m).trans (le_refl _))
  have cP : Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁) ≤ m ^ (ℓ₁ + ℓ₂) :=
    (card_pathX_le (lawSwapXZ μ) h₁).trans
      ((Nat.pow_le_pow_left hZ ℓ₁).trans (hmono _ (by omega)))
  have cS : Fintype.card ↥(Set.range a) ≤ m ^ (ℓ₁ + ℓ₂) :=
    (Fintype.card_le_of_injective (Subtype.val : ↥(Set.range a) → _) Subtype.val_injective).trans
      ((card_pathX_le (pathTrickZ μ ℓ₁ h₁) h₂).trans
        ((Nat.pow_le_pow_left hX ℓ₂).trans (hmono _ (by omega))))
  refine ⟨?_, cS, cY, cP, hpc, hmi⟩
  rintro ⟨x, y, w⟩ hp
  obtain ⟨-, nY, nP, -⟩ := PairwiseConnected3.nonempty_alphabets hpc
  have hcY : 0 < Fintype.card Y := Fintype.card_pos
  have hcP : 0 < Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁) := Fintype.card_pos
  have hsum : ν.prob (x, y, w) = 1 / ((Fintype.card Y : ℝ) *
      Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁)) := by
    rw [← hyz y w, Finset.sum_eq_single x]
    · intro x' _ hx'
      by_contra hne
      exact hx' (hmi y w x' x hne hp)
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hsum]
  have hY' : (Fintype.card Y : ℝ) ≤ ((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) := by exact_mod_cast cY
  have hP' : (Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁) : ℝ) ≤ ((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) := by
    exact_mod_cast cP
  have hYp : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcY
  have hPp : (0 : ℝ) < Fintype.card (PathX (lawSwapXZ μ) ℓ₁ h₁) := by exact_mod_cast hcP
  apply one_div_le_one_div_of_le (by positivity)
  rw [sq]
  exact mul_le_mul hY' hP' hPp.le (hYp.le.trans hY')

/-- paper IV `lem:nu-satisfies`, step `sigma-prime-times-gamma-in-support` (hypothesis 6c of Thm 6.7). -/
theorem l6_sigma_gamma_in_support (μ : FinProb (X × Y × Z)) (hμ : InT μ.support) {ℓ₁ ℓ₂ : ℕ}
    (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂)
    (hc₁ : ∀ (x : X) (y : Y), ∃ w : PathX (lawSwapXZ μ) ℓ₁ h₁,
      (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support)
    (hc₂ : ∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁),
      ∃ v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂,
        (v, y, w) ∈ (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support)
    (a : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂ → PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂)
    (ha : MergeRep (mergeGraphX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support) a)
    (ν : FinProb (↥(Set.range a) × Y × PathX (lawSwapXZ μ) ℓ₁ h₁))
    (hsupp : ν.support = (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support) :
    ∀ (x : X) (v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂), (∀ j, v.1 j = x) → ∀ y : Y,
      ∃ w : PathX (lawSwapXZ μ) ℓ₁ h₁, (⟨a v, Set.mem_range_self v⟩, y, w) ∈ ν.support := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := inT_construction μ hμ h₁ h₂ hc₁ hc₂ a ha
  intro x v hv y
  obtain ⟨w, v', hv', hmem⟩ := h7 x y
  have : v = v' := Subtype.ext (funext fun j => (hv j).trans (hv' j).symm)
  subst this
  exact ⟨w, by rw [hsupp]; exact hmem⟩

end L6Nu
end MaxT
end TrackB
end RestrictedPolynomials
end
