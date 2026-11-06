module

public import RestrictedPolynomials.TrackB.MaxTStatements

/-!
# Track B: `Q`, `P`-maximality, the order, and the conditional induction on `𝒯`
(Supplement E, `def:Q`, `def:order`, `lem:wf`, `lem:P-sym`, `prop:induction`, `cor:maxind`,
`thm:10.2-at-H0`)

Supplement E items: `def:Q`, `def:order`, `lem:wf`, `lem:P-sym`, `prop:induction`,
`thm:maxind-T`, `cor:maxind`, `thm:10.2-at-H0`.

Readings: patterns are over arbitrary finite types, and the induction is conditional. The three conditional
theorems are named `maxT_induction_of_merge_h64`, `maxT_uniform_of_Q`, `thm_10_2_at_H0_of_Q`; they take
as hypotheses `hmerge*` (the pattern form of `lem:merge-generic`) and `h64` (Thm 6.5′), which are
never strengthened, weakened or discharged here, so `prop:induction`, `thm:maxind-T`, `cor:maxind`
and `thm:10.2-at-H0` are stated conditionally on them.
All proof helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Patterns
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- Supplement E `def:Q`, `Q_x(𝔭)` for the pattern `(X, Y, Z; S)`: for every atom bound `α > 0` there are
constants `M ≥ 1`, `δ₀ ∈ (0,1]`, `η > 0` such that `S_x(μ; M, δ₀, η)` holds for EVERY law `μ` with
support `S` and atoms `≥ α` (the constants depend on the pattern and on `α`, not on `μ`). -/
def QX (S : Set (X × Y × Z)) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
    ∀ μ : FinProb (X × Y × Z), μ.support = S → (∀ p ∈ μ.support, α ≤ μ.prob p) →
      SStmtX μ M δ₀ η

def QY (S : Set (X × Y × Z)) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
    ∀ μ : FinProb (X × Y × Z), μ.support = S → (∀ p ∈ μ.support, α ≤ μ.prob p) →
      SStmtY μ M δ₀ η

def QZ (S : Set (X × Y × Z)) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
    ∀ μ : FinProb (X × Y × Z), μ.support = S → (∀ p ∈ μ.support, α ≤ μ.prob p) →
      SStmtZ μ M δ₀ η

/-- `Q(𝔭) := Q_x ∧ Q_y ∧ Q_z`. -/
def QSet (S : Set (X × Y × Z)) : Prop := QX S ∧ QY S ∧ QZ S

/-- Supplement E `def:Q`, `P`-maximal: `Q` holds for every strict enlargement over the same alphabets. -/
def PMaxSet (S : Set (X × Y × Z)) : Prop := ∀ S' : Set (X × Y × Z), S ⊂ S' → QSet S'

/-- Supplement E `def:order`: `(n, d)` with `n = |Σ|+|Γ|+|Φ|` and `d = |Σ||Γ||Φ| - |S|`, ordered
lexicographically. -/
def setMeasure (S : Set (X × Y × Z)) : ℕ ×ₗ ℕ :=
  toLex (Fintype.card X + Fintype.card Y + Fintype.card Z,
    Fintype.card X * Fintype.card Y * Fintype.card Z - Nat.card S)

/-! ### Supplement E `lem:wf` -/

theorem order_wf : WellFounded (fun p q : ℕ ×ₗ ℕ => p < q) :=
  wellFounded_lt

private theorem lex_lt_of_fst {a b c d : ℕ} (h : a < c) : toLex (a, b) < toLex (c, d) :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

private theorem lex_lt_of_snd {a b d : ℕ} (h : b < d) : toLex (a, b) < toLex (a, d) :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, h⟩)

theorem setMeasure_mergeSetX_lt (S : Set (X × Y × Z)) (a : X → X) (h : ¬ Function.Injective a) :
    setMeasure (mergeSetX S a) < setMeasure S := by
  unfold setMeasure
  apply lex_lt_of_fst
  have := card_range_lt_of_not_injective a h
  rw [Nat.card_eq_fintype_card] at this
  omega

theorem setMeasure_mergeSetY_lt (S : Set (X × Y × Z)) (b : Y → Y) (h : ¬ Function.Injective b) :
    setMeasure (mergeSetY S b) < setMeasure S := by
  unfold setMeasure
  apply lex_lt_of_fst
  have := card_range_lt_of_not_injective b h
  rw [Nat.card_eq_fintype_card] at this
  omega

theorem setMeasure_mergeSetZ_lt (S : Set (X × Y × Z)) (c : Z → Z) (h : ¬ Function.Injective c) :
    setMeasure (mergeSetZ S c) < setMeasure S := by
  unfold setMeasure
  apply lex_lt_of_fst
  have := card_range_lt_of_not_injective c h
  rw [Nat.card_eq_fintype_card] at this
  omega

private theorem natCard_le_card (S : Set (X × Y × Z)) :
    Nat.card S ≤ Fintype.card X * Fintype.card Y * Fintype.card Z := by
  have : Nat.card S ≤ Nat.card (X × Y × Z) := Nat.card_mono (Set.toFinite _) (Set.subset_univ S) |>
    fun h => by simpa using h
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, mul_assoc] using this

theorem setMeasure_enlarge_lt {S S' : Set (X × Y × Z)} (h : S ⊂ S') :
    setMeasure S' < setMeasure S := by
  unfold setMeasure
  have hlt : Nat.card S < Nat.card S' := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_lt_ncard h (Set.toFinite _)
  have hle := natCard_le_card S'
  apply lex_lt_of_snd
  omega

theorem setMeasure_swapXY (S : Set (X × Y × Z)) : setMeasure (swapXY S) = setMeasure S := by
  unfold setMeasure
  have hinj : Function.Injective (fun p : X × Y × Z => (p.2.1, p.1, p.2.2)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    tauto
  have hc : Nat.card (swapXY S) = Nat.card S := Nat.card_image_of_injective hinj S
  rw [hc]
  congr 1
  refine Prod.ext ?_ ?_
  · show Fintype.card Y + Fintype.card X + Fintype.card Z = _
    ring
  · show Fintype.card Y * Fintype.card X * Fintype.card Z - _ = _
    rw [mul_comm (Fintype.card Y)]

theorem setMeasure_swapYZ (S : Set (X × Y × Z)) : setMeasure (swapYZ S) = setMeasure S := by
  unfold setMeasure
  have hinj : Function.Injective (fun p : X × Y × Z => (p.1, p.2.2, p.2.1)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    tauto
  have hc : Nat.card (swapYZ S) = Nat.card S := Nat.card_image_of_injective hinj S
  rw [hc]
  congr 1
  refine Prod.ext ?_ ?_
  · show Fintype.card X + Fintype.card Z + Fintype.card Y = _
    ring
  · show Fintype.card X * Fintype.card Z * Fintype.card Y - _ = _
    rw [mul_assoc, mul_comm (Fintype.card Z), ← mul_assoc]

theorem setMeasure_relabelSet {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : setMeasure (relabelSet eX eY eZ S) = setMeasure S := by
  unfold setMeasure
  have hinj : Function.Injective (fun p : X × Y × Z => (eX p.1, eY p.2.1, eZ p.2.2)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h ⊢
    exact h
  have hc : Nat.card (relabelSet eX eY eZ S) = Nat.card S := Nat.card_image_of_injective hinj S
  rw [hc, Fintype.card_congr eX, Fintype.card_congr eY, Fintype.card_congr eZ]

/-! ### Supplement E `lem:P-sym` at the level of patterns (`Q` and `P`-maximality are invariant) -/

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem swapXY_swapXY (S : Set (X × Y × Z)) : swapXY (swapXY S) = S := by
  unfold swapXY
  rw [Set.image_image]
  simp

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem swapYZ_swapYZ (S : Set (X × Y × Z)) : swapYZ (swapYZ S) = S := by
  unfold swapYZ
  rw [Set.image_image]
  simp

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem relabelSet_symm {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : relabelSet eX.symm eY.symm eZ.symm (relabelSet eX eY eZ S) = S := by
  unfold relabelSet
  rw [Set.image_image]
  simp

private theorem atoms_swapXY {α : ℝ} (ν : FinProb (Y × X × Z)) (h : ∀ p ∈ ν.support, α ≤ ν.prob p) :
    ∀ p ∈ (lawSwapXY ν).support, α ≤ (lawSwapXY ν).prob p := by
  rintro ⟨x, y, z⟩ hp
  have e := lawSwapXY_prob ν y x z
  simp only [FinProb.support, Set.mem_ofPred_eq] at hp h
  rw [e] at hp ⊢
  exact h _ hp

private theorem atoms_swapYZ {α : ℝ} (ν : FinProb (X × Z × Y)) (h : ∀ p ∈ ν.support, α ≤ ν.prob p) :
    ∀ p ∈ (lawSwapYZ ν).support, α ≤ (lawSwapYZ ν).prob p := by
  rintro ⟨x, y, z⟩ hp
  have e := lawSwapYZ_prob ν x z y
  simp only [FinProb.support, Set.mem_ofPred_eq] at hp h
  rw [e] at hp ⊢
  exact h _ hp

private theorem atoms_relabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    {α : ℝ} (ν : FinProb (X × Y × Z)) (h : ∀ p ∈ ν.support, α ≤ ν.prob p) :
    ∀ p ∈ (lawRelabel eX eY eZ ν).support, α ≤ (lawRelabel eX eY eZ ν).prob p := by
  rintro ⟨x', y', z'⟩ hp
  obtain ⟨x, rfl⟩ := eX.surjective x'
  obtain ⟨y, rfl⟩ := eY.surjective y'
  obtain ⟨z, rfl⟩ := eZ.surjective z'
  have e := lawRelabel_prob eX eY eZ ν x y z
  simp only [FinProb.support, Set.mem_ofPred_eq] at hp h
  rw [e] at hp ⊢
  exact h _ hp

theorem qX_iff_swapXY (S : Set (X × Y × Z)) : QX S ↔ QY (swapXY S) := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapXY ν).support = S := by rw [lawSwapXY_support, hν, swapXY_swapXY]
    exact (sStmtY_iff_swapXY ν M δ₀ η).2 (H (lawSwapXY ν) hs (atoms_swapXY ν hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapXY ν).support = swapXY S := by rw [lawSwapXY_support, hν]
    exact (sStmtX_iff_swapXY ν M δ₀ η).2 (H (lawSwapXY ν) hs (atoms_swapXY ν hat))

theorem qY_iff_swapXY (S : Set (X × Y × Z)) : QY S ↔ QX (swapXY S) := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapXY ν).support = S := by rw [lawSwapXY_support, hν, swapXY_swapXY]
    exact (sStmtX_iff_swapXY ν M δ₀ η).2 (H (lawSwapXY ν) hs (atoms_swapXY ν hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapXY ν).support = swapXY S := by rw [lawSwapXY_support, hν]
    exact (sStmtY_iff_swapXY ν M δ₀ η).2 (H (lawSwapXY ν) hs (atoms_swapXY ν hat))

theorem qZ_iff_swapXY (S : Set (X × Y × Z)) : QZ S ↔ QZ (swapXY S) := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapXY ν).support = S := by rw [lawSwapXY_support, hν, swapXY_swapXY]
    exact (sStmtZ_iff_swapXY ν M δ₀ η).2 (H (lawSwapXY ν) hs (atoms_swapXY ν hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapXY ν).support = swapXY S := by rw [lawSwapXY_support, hν]
    exact (sStmtZ_iff_swapXY ν M δ₀ η).2 (H (lawSwapXY ν) hs (atoms_swapXY ν hat))

theorem qX_iff_swapYZ (S : Set (X × Y × Z)) : QX S ↔ QX (swapYZ S) := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapYZ ν).support = S := by rw [lawSwapYZ_support, hν, swapYZ_swapYZ]
    exact (sStmtX_iff_swapYZ ν M δ₀ η).2 (H (lawSwapYZ ν) hs (atoms_swapYZ ν hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapYZ ν).support = swapYZ S := by rw [lawSwapYZ_support, hν]
    exact (sStmtX_iff_swapYZ ν M δ₀ η).2 (H (lawSwapYZ ν) hs (atoms_swapYZ ν hat))

theorem qY_iff_swapYZ (S : Set (X × Y × Z)) : QY S ↔ QZ (swapYZ S) := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapYZ ν).support = S := by rw [lawSwapYZ_support, hν, swapYZ_swapYZ]
    exact (sStmtZ_iff_swapYZ ν M δ₀ η).2 (H (lawSwapYZ ν) hs (atoms_swapYZ ν hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapYZ ν).support = swapYZ S := by rw [lawSwapYZ_support, hν]
    exact (sStmtY_iff_swapYZ ν M δ₀ η).2 (H (lawSwapYZ ν) hs (atoms_swapYZ ν hat))

theorem qZ_iff_swapYZ (S : Set (X × Y × Z)) : QZ S ↔ QY (swapYZ S) := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapYZ ν).support = S := by rw [lawSwapYZ_support, hν, swapYZ_swapYZ]
    exact (sStmtY_iff_swapYZ ν M δ₀ η).2 (H (lawSwapYZ ν) hs (atoms_swapYZ ν hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawSwapYZ ν).support = swapYZ S := by rw [lawSwapYZ_support, hν]
    exact (sStmtZ_iff_swapYZ ν M δ₀ η).2 (H (lawSwapYZ ν) hs (atoms_swapYZ ν hat))

theorem qSet_swapXY_iff (S : Set (X × Y × Z)) : QSet (swapXY S) ↔ QSet S := by
  have h1 := qX_iff_swapXY S
  have h2 := qY_iff_swapXY S
  have h3 := qZ_iff_swapXY S
  unfold QSet
  tauto

theorem qSet_swapYZ_iff (S : Set (X × Y × Z)) : QSet (swapYZ S) ↔ QSet S := by
  have h1 := qX_iff_swapYZ S
  have h2 := qY_iff_swapYZ S
  have h3 := qZ_iff_swapYZ S
  unfold QSet
  tauto

private theorem qX_relabel_iff {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : QX (relabelSet eX eY eZ S) ↔ QX S := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun μ hμ hat => ?_⟩
    have hs : (lawRelabel eX eY eZ μ).support = relabelSet eX eY eZ S := by
      rw [lawRelabel_support, hμ]
    exact (sStmtX_iff_relabel eX eY eZ μ M δ₀ η).1 (H _ hs (atoms_relabel eX eY eZ μ hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawRelabel eX.symm eY.symm eZ.symm ν).support = S := by
      rw [lawRelabel_support, hν, relabelSet_symm]
    exact (sStmtX_iff_relabel eX.symm eY.symm eZ.symm ν M δ₀ η).1
      (H _ hs (atoms_relabel eX.symm eY.symm eZ.symm ν hat))

private theorem qY_relabel_iff {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : QY (relabelSet eX eY eZ S) ↔ QY S := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun μ hμ hat => ?_⟩
    have hs : (lawRelabel eX eY eZ μ).support = relabelSet eX eY eZ S := by
      rw [lawRelabel_support, hμ]
    exact (sStmtY_iff_relabel eX eY eZ μ M δ₀ η).1 (H _ hs (atoms_relabel eX eY eZ μ hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawRelabel eX.symm eY.symm eZ.symm ν).support = S := by
      rw [lawRelabel_support, hν, relabelSet_symm]
    exact (sStmtY_iff_relabel eX.symm eY.symm eZ.symm ν M δ₀ η).1
      (H _ hs (atoms_relabel eX.symm eY.symm eZ.symm ν hat))

private theorem qZ_relabel_iff {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : QZ (relabelSet eX eY eZ S) ↔ QZ S := by
  constructor
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun μ hμ hat => ?_⟩
    have hs : (lawRelabel eX eY eZ μ).support = relabelSet eX eY eZ S := by
      rw [lawRelabel_support, hμ]
    exact (sStmtZ_iff_relabel eX eY eZ μ M δ₀ η).1 (H _ hs (atoms_relabel eX eY eZ μ hat))
  · intro h α hα
    obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := h α hα
    refine ⟨M, δ₀, η, h1, h2, h3, h4, fun ν hν hat => ?_⟩
    have hs : (lawRelabel eX.symm eY.symm eZ.symm ν).support = S := by
      rw [lawRelabel_support, hν, relabelSet_symm]
    exact (sStmtZ_iff_relabel eX.symm eY.symm eZ.symm ν M δ₀ η).1
      (H _ hs (atoms_relabel eX.symm eY.symm eZ.symm ν hat))

theorem qSet_relabelSet_iff {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : QSet (relabelSet eX eY eZ S) ↔ QSet S := by
  have h1 := qX_relabel_iff eX eY eZ S
  have h2 := qY_relabel_iff eX eY eZ S
  have h3 := qZ_relabel_iff eX eY eZ S
  unfold QSet
  tauto

private theorem image_ssubset_image {A B : Type} {f : A → B} (hf : Function.Injective f)
    {S S' : Set A} (h : S ⊂ S') : f '' S ⊂ f '' S' :=
  ⟨Set.image_mono h.1, fun hh => h.2 ((Set.image_subset_image_iff hf).1 hh)⟩

private theorem swapXY_inj : Function.Injective (fun p : X × Y × Z => (p.2.1, p.1, p.2.2)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  tauto

private theorem swapYZ_inj : Function.Injective (fun p : X × Y × Z => (p.1, p.2.2, p.2.1)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  tauto

private theorem relabel_inj {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z') :
    Function.Injective (fun p : X × Y × Z => (eX p.1, eY p.2.1, eZ p.2.2)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h ⊢
  exact h

private theorem pMaxSet_swapXY_mp (S : Set (X × Y × Z)) : PMaxSet (swapXY S) → PMaxSet S := by
  intro h S' hS'
  exact (qSet_swapXY_iff S').1 (h _ (image_ssubset_image swapXY_inj hS'))

theorem pMaxSet_swapXY_iff (S : Set (X × Y × Z)) : PMaxSet (swapXY S) ↔ PMaxSet S := by
  refine ⟨pMaxSet_swapXY_mp S, fun h => ?_⟩
  have := pMaxSet_swapXY_mp (swapXY S)
  rw [swapXY_swapXY] at this
  exact this h

private theorem pMaxSet_swapYZ_mp (S : Set (X × Y × Z)) : PMaxSet (swapYZ S) → PMaxSet S := by
  intro h S' hS'
  exact (qSet_swapYZ_iff S').1 (h _ (image_ssubset_image swapYZ_inj hS'))

theorem pMaxSet_swapYZ_iff (S : Set (X × Y × Z)) : PMaxSet (swapYZ S) ↔ PMaxSet S := by
  refine ⟨pMaxSet_swapYZ_mp S, fun h => ?_⟩
  have := pMaxSet_swapYZ_mp (swapYZ S)
  rw [swapYZ_swapYZ] at this
  exact this h

private theorem pMaxSet_relabelSet_mp {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : PMaxSet (relabelSet eX eY eZ S) → PMaxSet S := by
  intro h S' hS'
  exact (qSet_relabelSet_iff eX eY eZ S').1 (h _ (image_ssubset_image (relabel_inj eX eY eZ) hS'))

theorem pMaxSet_relabelSet_iff {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : PMaxSet (relabelSet eX eY eZ S) ↔ PMaxSet S := by
  refine ⟨pMaxSet_relabelSet_mp eX eY eZ S, fun h => ?_⟩
  have := pMaxSet_relabelSet_mp eX.symm eY.symm eZ.symm (relabelSet eX eY eZ S)
  rw [relabelSet_symm] at this
  exact this h

end Patterns

/-! ### Supplement E `prop:induction` and `thm:maxind-T`, conditional on the two inputs
(the generic-slot merge lemma, Supplement E `lem:merge-generic`, in its pattern form
`Q(𝔭') ⇒ Q(𝔭)`, and Thm 6.4′, Supplement E `thm:6.4-prime`). -/

/-- Supplement E `prop:induction` (Thm 4.13 on `𝒯`): `Q(𝔭)` for every pattern with `S ∈ 𝒯`, by well-founded
induction on `setMeasure`. Hypotheses `hmerge*`: `Q` of a genuine merge implies `Q` (consequence of
`lem:merge-generic` stated in that lemma); `h64`: Thm 6.4′ with `|Σ| > 1`. Conditional helper. -/
theorem maxT_induction_of_merge_h64
    (hmergeX : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → ∀ a : X → X, MergeRep (mergeGraphX S) a →
        ¬ Function.Injective a → QSet (mergeSetX S a) → QSet S)
    (hmergeY : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → ∀ b : Y → Y, MergeRep (mergeGraphY S) b →
        ¬ Function.Injective b → QSet (mergeSetY S b) → QSet S)
    (hmergeZ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → ∀ c : Z → Z, MergeRep (mergeGraphZ S) c →
        ¬ Function.Injective c → QSet (mergeSetZ S c) → QSet S)
    (h64 : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → FullyMergedSet S → PMaxSet S →
        1 < Fintype.card X → QY S)
    (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (S : Set (X × Y × Z)) (hS : InT S) : QSet S := by
  have key : ∀ n : ℕ ×ₗ ℕ, ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
      [DecidableEq Y] [DecidableEq Z] (S : Set (X × Y × Z)), InT S → setMeasure S = n → QSet S := by
    intro n
    induction n using order_wf.induction with
    | _ n ih =>
      intro X Y Z _ _ _ _ _ _ S hS hn
      by_cases hm : FullyMergedSet S
      · rcases inT_fullyMerged_dichotomy hS hm with ⟨hx, hy, hz, -⟩ | ⟨hx, hy, hz⟩
        · obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hx
          obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hy
          obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hz
          refine ⟨fun α _ => ?_, fun α _ => ?_, fun α _ => ?_⟩
          · exact ⟨1, 1, 1 / 2, le_rfl, one_pos, le_rfl, by norm_num,
              fun μ _ _ => (pStmt_of_unique μ).1⟩
          · exact ⟨1, 1, 1 / 2, le_rfl, one_pos, le_rfl, by norm_num,
              fun μ _ _ => (pStmt_of_unique μ).2.1⟩
          · exact ⟨1, 1, 1 / 2, le_rfl, one_pos, le_rfl, by norm_num,
              fun μ _ _ => (pStmt_of_unique μ).2.2⟩
        · have hP : PMaxSet S := by
            intro S' hS'
            refine ih (setMeasure S') ?_ X Y Z S' (hS.mono hS'.1) rfl
            rw [← hn]
            exact setMeasure_enlarge_lt hS'
          have hQY : QY S := h64 X Y Z S hS hm hP (by omega)
          have hQX : QX S := by
            rw [qX_iff_swapXY]
            exact h64 Y X Z (swapXY S) ((inT_swapXY_iff S).2 hS)
              ((fullyMergedSet_swapXY_iff S).2 hm) ((pMaxSet_swapXY_iff S).2 hP) (by omega)
          have hQZ : QZ S := by
            rw [qZ_iff_swapYZ]
            exact h64 X Z Y (swapYZ S) ((inT_swapYZ_iff S).2 hS)
              ((fullyMergedSet_swapYZ_iff S).2 hm) ((pMaxSet_swapYZ_iff S).2 hP) (by omega)
          exact ⟨hQX, hQY, hQZ⟩
      · unfold FullyMergedSet at hm
        by_cases hx : mergeImpliesX S
        · by_cases hy : mergeImpliesY S
          · have hz : ¬ mergeImpliesZ S := fun hz => hm ⟨hx, hy, hz⟩
            obtain ⟨c, hc, hni⟩ := exists_nonInjective_mergeRepZ hz
            refine hmergeZ X Y Z S hS c hc hni (ih _ ?_ _ _ _ _ (inT_mergeSetZ hS c) rfl)
            rw [← hn]
            exact setMeasure_mergeSetZ_lt S c hni
          · obtain ⟨b, hb, hni⟩ := exists_nonInjective_mergeRepY hy
            refine hmergeY X Y Z S hS b hb hni (ih _ ?_ _ _ _ _ (inT_mergeSetY hS b) rfl)
            rw [← hn]
            exact setMeasure_mergeSetY_lt S b hni
        · obtain ⟨a, ha, hni⟩ := exists_nonInjective_mergeRepX hx
          refine hmergeX X Y Z S hS a ha hni (ih _ ?_ _ _ _ _ (inT_mergeSetX hS a) rfl)
          rw [← hn]
          exact setMeasure_mergeSetX_lt S a hni
  exact key _ X Y Z S hS rfl

/-! ### helpers for the uniform form -/

private theorem bound_mono {c M M' δ η η' : ℝ} (hM : 0 ≤ M) (hMM : M ≤ M') (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hηη : η' ≤ η) (h : c ≤ M * δ ^ η) : c ≤ M' * δ ^ η' := by
  have h1 : δ ^ η ≤ δ ^ η' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηη
  have h2 : 0 ≤ δ ^ η' := (Real.rpow_pos_of_pos hδ η').le
  calc c ≤ M * δ ^ η := h
    _ ≤ M * δ ^ η' := mul_le_mul_of_nonneg_left h1 hM
    _ ≤ M' * δ ^ η' := mul_le_mul_of_nonneg_right hMM h2

private theorem inv_bound {d B : ℝ} (hd : 0 < d) (h : 1 / d ≤ B) : 1 / max B 1 ≤ d := by
  have hpos : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [div_le_iff₀ hpos]
  have h1 : 1 / d ≤ max B 1 := h.trans (le_max_left _ _)
  have := (div_le_iff₀ hd).1 h1
  linarith

section UniformHelpers
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem sStmtX_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtX μ M δ₀ η) :
    SStmtX μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem sStmtY_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtY μ M δ₀ η) :
    SStmtY μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem sStmtZ_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtZ μ M δ₀ η) :
    SStmtZ μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem pStmt_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : PStmt μ M δ₀ η) :
    PStmt μ M' δ₀' η' :=
  ⟨sStmtX_mono hM hMM hδ hδ1 hηη H.1, sStmtY_mono hM hMM hδ hδ1 hηη H.2.1,
    sStmtZ_mono hM hMM hδ hδ1 hηη H.2.2⟩

/-- `Q(𝔭)` gives common constants for the three slots. -/
private theorem exists_pstmt_of_QSet {S : Set (X × Y × Z)} (h : QSet S) {α : ℝ} (hα : 0 < α) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      ∀ μ : FinProb (X × Y × Z), μ.support = S → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        PStmt μ M δ₀ η := by
  obtain ⟨Mx, dx, ex, hMx, hdx, hdx1, hex, Hx⟩ := h.1 α hα
  obtain ⟨My, dy, ey, hMy, hdy, hdy1, hey, Hy⟩ := h.2.1 α hα
  obtain ⟨Mz, dz, ez, hMz, hdz, hdz1, hez, Hz⟩ := h.2.2 α hα
  have hM1 : Mx ≤ max (max Mx My) Mz := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : My ≤ max (max Mx My) Mz := (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : Mz ≤ max (max Mx My) Mz := le_max_right _ _
  have hd1 : min (min dx dy) dz ≤ dx := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : min (min dx dy) dz ≤ dy := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : min (min dx dy) dz ≤ dz := min_le_right _ _
  have he1 : min (min ex ey) ez ≤ ex := (min_le_left _ _).trans (min_le_left _ _)
  have he2 : min (min ex ey) ez ≤ ey := (min_le_left _ _).trans (min_le_right _ _)
  have he3 : min (min ex ey) ez ≤ ez := min_le_right _ _
  refine ⟨max (max Mx My) Mz, min (min dx dy) dz, min (min ex ey) ez, hMx.trans hM1,
    lt_min (lt_min hdx hdy) hdz, hd1.trans hdx1, lt_min (lt_min hex hey) hez,
    fun μ hμ hat => ⟨?_, ?_, ?_⟩⟩
  · exact sStmtX_mono hMx hM1 hd1 hdx1 he1 (Hx μ hμ hat)
  · exact sStmtY_mono hMy hM2 hd2 hdy1 he2 (Hy μ hμ hat)
  · exact sStmtZ_mono hMz hM3 hd3 hdz1 he3 (Hz μ hμ hat)

end UniformHelpers

/-- Supplement E `cor:maxind` (uniform form, Remark `rmk:finite`): `∀ m α ∃ M δ₀ η ∀ μ ∈ 𝒯(m, α)`.
Conditional helper. -/
theorem maxT_uniform_of_Q
    (hQ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → QSet S)
    (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PStmt μ M δ₀ η := by
  -- the finitely many patterns over `Fin a × Fin b × Fin c`, `a, b, c ≤ m`
  have hex : ∀ i : (a : Fin (m + 1)) × (b : Fin (m + 1)) × (c : Fin (m + 1)) ×
      Set (Fin (a : ℕ) × Fin (b : ℕ) × Fin (c : ℕ)),
      ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
        (InT i.2.2.2 → ∀ μ : FinProb (Fin (i.1 : ℕ) × Fin (i.2.1 : ℕ) × Fin (i.2.2.1 : ℕ)),
          μ.support = i.2.2.2 → (∀ p ∈ μ.support, α ≤ μ.prob p) → PStmt μ M δ₀ η) := by
    rintro ⟨a, b, c, T⟩
    by_cases hT : InT T
    · obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := exists_pstmt_of_QSet (hQ _ _ _ T hT) hα
      exact ⟨M, δ₀, η, h1, h2, h3, h4, fun _ => H⟩
    · exact ⟨1, 1, 1, le_rfl, one_pos, le_rfl, one_pos, fun h => absurd h hT⟩
  choose Mf δf ηf hM hδ hδ1 hη hP using hex
  obtain ⟨BM, hBM⟩ := Finite.bddAbove_range Mf
  obtain ⟨Bδ, hBδ⟩ := Finite.bddAbove_range (fun i => 1 / δf i)
  obtain ⟨Bη, hBη⟩ := Finite.bddAbove_range (fun i => 1 / ηf i)
  have hposδ : 0 < max Bδ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hposη : 0 < max Bη 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max BM 1, 1 / max Bδ 1, 1 / max Bη 1, le_max_right _ _, one_div_pos.2 hposδ,
    (div_le_one hposδ).2 (le_max_right _ _), one_div_pos.2 hposη, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hμ hat
  let a : Fin (m + 1) := ⟨Fintype.card X, by omega⟩
  let b : Fin (m + 1) := ⟨Fintype.card Y, by omega⟩
  let c : Fin (m + 1) := ⟨Fintype.card Z, by omega⟩
  let eX : X ≃ Fin (a : ℕ) := Fintype.equivFinOfCardEq rfl
  let eY : Y ≃ Fin (b : ℕ) := Fintype.equivFinOfCardEq rfl
  let eZ : Z ≃ Fin (c : ℕ) := Fintype.equivFinOfCardEq rfl
  let i : (a : Fin (m + 1)) × (b : Fin (m + 1)) × (c : Fin (m + 1)) ×
      Set (Fin (a : ℕ) × Fin (b : ℕ) × Fin (c : ℕ)) := ⟨a, b, c, relabelSet eX eY eZ μ.support⟩
  have hInT : InT (relabelSet eX eY eZ μ.support) := (inT_relabelSet_iff eX eY eZ _).2 hμ
  have h1 := hP i hInT (lawRelabel eX eY eZ μ) (lawRelabel_support eX eY eZ μ)
    (atoms_relabel eX eY eZ μ hat)
  have h2 := (pStmt_relabel_iff eX eY eZ μ (Mf i) (δf i) (ηf i)).1 h1
  exact pStmt_mono (hM i) (le_max_of_le_left (hBM (Set.mem_range_self i)))
    (inv_bound (hδ i) (hBδ (Set.mem_range_self i))) (hδ1 i)
    (inv_bound (hη i) (hBη (Set.mem_range_self i))) h2

/-- Supplement E `thm:10.2-at-H0`: Thm 10.2 at the trivial embedding group, in the form consumed by
CSP_7 `thm:3csp-bkm2`, step `from-B4-10.2` (`NEStab = Stab` by `nestab_trivial_master`). Conditional
helper. -/
theorem thm_10_2_at_H0_of_Q
    (hQ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → QSet S)
    (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ (M : ℕ) (δ₀ η : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            (cstab (lawY μ) (1 - δ) g).re ≤ δ → ‖corr3 μ f g h‖ ≤ (M : ℝ) * δ ^ η := by
  obtain ⟨M, δ₀, η, hM, hδ₀, hδ₁, hη, H⟩ := maxT_uniform_of_Q hQ m hα
  refine ⟨⌈M⌉₊, δ₀, η, hδ₀, hδ₁, hη, fun δ hδ hδδ₀ X Y Z _ _ _ _ _ _ hX hY hZ μ hat hpc hna n f g h
    hf hg hh hs => ?_⟩
  have hP := H X Y Z hX hY hZ μ ⟨hpc, hna⟩ hat
  have := hP.2.1 δ hδ hδδ₀ n f g h hf hg hh hs
  refine this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil M) ?_)
  exact (Real.rpow_pos_of_pos hδ η).le

end MaxT
end TrackB
end RestrictedPolynomials
end
