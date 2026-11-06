module

public import RestrictedPolynomials.TrackB.K6PathTrick

/-!
# Track B: uniform constants, atoms of the path tricks (Supplement D)

Source: Supplement D (Lemma walk-atom, Lemma alphabet-bound,
Corollary three-tricks, Definition params, Lemma chain).

Formalization choices:
* `k6ptR1` is floored at `1` and uses the `+1` form `⌈log₂ (2/α + 1)⌉`; `k6ptR2` is the same rule at
  `α₁ = α ^ 2 ^ r₁`.
* The atom bound of a path trick is proved directly (a positive walk entry has a positive
  intermediate term with all step factors `≥ β`); the private `walk_claim` of
  `PathTrickEmbedding` is not needed.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### private helpers -/
section Helpers

private lemma atoms_card_mul_le {α ι : Type} [Fintype α] [Fintype ι] (ν : FinProb α) (f : ι → α)
    (hf : Function.Injective f) (hs : ∀ i, f i ∈ ν.support) {γ : ℝ}
    (hatom : ∀ p ∈ ν.support, γ ≤ ν.prob p) : (Fintype.card ι : ℝ) * γ ≤ 1 := by
  classical
  calc (Fintype.card ι : ℝ) * γ = ∑ _i : ι, γ := by simp
    _ ≤ ∑ i, ν.prob (f i) := Finset.sum_le_sum fun i _ => hatom _ (hs i)
    _ = ∑ p ∈ Finset.univ.image f, ν.prob p := (Finset.sum_image fun a _ b _ h => hf h).symm
    _ ≤ ∑ p, ν.prob p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => ν.nonneg p
    _ = 1 := ν.sum_eq_one

private lemma perm_atom_ge {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (π : FinProb α)
    {γ : ℝ} (h : ∀ p ∈ π.support, γ ≤ π.prob p) :
    ∀ q ∈ (k6ptPerm e π).support, γ ≤ (k6ptPerm e π).prob q :=
  fun q hq => h (e.symm q) hq

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private lemma exists_support_pt (μ : FinProb (X × Y × Z)) : ∃ p, p ∈ μ.support := by
  by_contra hne
  have : ∀ p, μ.prob p = 0 := fun p => by
    by_contra h0; exact hne ⟨p, h0⟩
  have h1 := μ.sum_eq_one
  simp [this] at h1

private lemma prob_le_one_pt {α : Type} [Fintype α] (ν : FinProb α) (p : α) : ν.prob p ≤ 1 := by
  rw [← ν.sum_eq_one]
  exact Finset.single_le_sum (f := ν.prob) (fun p _ => ν.nonneg p) (Finset.mem_univ p)

private lemma margY_le_one (μ : FinProb (X × Y × Z)) (y : Y) : margY μ y ≤ 1 := by
  rw [← sum_margY μ]
  exact Finset.single_le_sum (f := margY μ) (fun y _ => margY_nonneg μ y) (Finset.mem_univ y)

private lemma margZ_le_one (μ : FinProb (X × Y × Z)) (z : Z) : margZ μ z ≤ 1 := by
  have h : ∑ z, margZ μ z = 1 := by
    simp_rw [margZ_eq_sum]
    rw [← μ.sum_eq_one, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [← h]
  exact Finset.single_le_sum (f := margZ μ) (fun z _ => margZ_nonneg μ z) (Finset.mem_univ z)

private lemma stepYZ_ge (μ : FinProb (X × Y × Z)) {β : ℝ}
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) {x : X} {y : Y} {z : Z} (h : μ.prob (x, y, z) ≠ 0) :
    β ≤ stepYZ μ x y z := by
  have h0 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)
  have hm : 0 < margY μ y := lt_of_lt_of_le h0 (prob_le_margY μ x y z)
  have h1 := margY_le_one μ y
  have hb := hatom _ h
  have h2 : μ.prob (x, y, z) ≤ μ.prob (x, y, z) / margY μ y := by
    rw [le_div_iff₀ hm]; nlinarith
  exact hb.trans h2

private lemma stepZY_ge (μ : FinProb (X × Y × Z)) {β : ℝ}
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) {x : X} {y : Y} {z : Z} (h : μ.prob (x, y, z) ≠ 0) :
    β ≤ stepZY μ x z y := by
  have h0 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)
  have hm : 0 < margZ μ z := lt_of_lt_of_le h0 (prob_le_margZ μ x y z)
  have h1 := margZ_le_one μ z
  have hb := hatom _ h
  have h2 : μ.prob (x, y, z) ≤ μ.prob (x, y, z) / margZ μ z := by
    rw [le_div_iff₀ hm]; nlinarith
  exact hb.trans h2

private lemma prob_ne_of_stepYZ_pos (μ : FinProb (X × Y × Z)) {x : X} {y : Y} {z : Z}
    (h : 0 < stepYZ μ x y z) : μ.prob (x, y, z) ≠ 0 := by
  intro h0
  simp [stepYZ, h0] at h

private lemma prob_ne_of_stepZY_pos (μ : FinProb (X × Y × Z)) {x : X} {y : Y} {z : Z}
    (h : 0 < stepZY μ x z y) : μ.prob (x, y, z) ≠ 0 := by
  intro h0
  simp [stepZY, h0] at h

private lemma exists_pos_of_sum_pos {ι : Type} [Fintype ι] {f : ι → ℝ} (h : 0 < ∑ i, f i) :
    ∃ i, 0 < f i := by
  by_contra hne
  push Not at hne
  exact absurd h (not_lt.2 (Finset.sum_nonpos fun i _ => hne i))

private lemma both_pos_of_mul_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a * b) :
    0 < a ∧ 0 < b := by
  rcases mul_pos_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h1 (not_lt.2 ha)

private lemma support_X_has_pt (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    (x : X) : ∃ y z, μ.prob (x, y, z) ≠ 0 := by
  obtain ⟨p0, -⟩ := exists_support_pt μ
  obtain ⟨h1, -, -⟩ := (pairwiseConnected3_iff _).1 h
  obtain ⟨p⟩ := h1.preconnected (Sum.inl x) (Sum.inr p0.2.1)
  cases p with
  | cons hadj _ =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x', y', z', hm, h1, h2⟩ | ⟨x', y', z', hm, h1, h2⟩⟩
    · cases h1; exact ⟨y', z', hm⟩
    · cases h2

private lemma support_Y_has_pt (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    (y : Y) : ∃ x z, μ.prob (x, y, z) ≠ 0 := by
  obtain ⟨p0, -⟩ := exists_support_pt μ
  obtain ⟨-, -, h3⟩ := (pairwiseConnected3_iff _).1 h
  obtain ⟨p⟩ := h3.preconnected (Sum.inl y) (Sum.inr p0.2.2)
  cases p with
  | cons hadj _ =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x', y', z', hm, h1, h2⟩ | ⟨x', y', z', hm, h1, h2⟩⟩
    · cases h1; exact ⟨x', z', hm⟩
    · cases h2

private lemma support_Z_has_pt (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    (z : Z) : ∃ x y, μ.prob (x, y, z) ≠ 0 := by
  obtain ⟨p0, -⟩ := exists_support_pt μ
  obtain ⟨-, -, h3⟩ := (pairwiseConnected3_iff _).1 h
  obtain ⟨p⟩ := h3.preconnected (Sum.inr z) (Sum.inl p0.2.1)
  cases p with
  | cons hadj _ =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x', y', z', hm, h1, h2⟩ | ⟨x', y', z', hm, h1, h2⟩⟩
    · cases h1
    · have : z = z' := Sum.inr.inj h2
      subst this
      exact ⟨x', y', hm⟩

end Helpers

/-! ### Atoms of one trick -/
section WalkAtoms
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

theorem k6pt_margY_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ}
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) {y : Y} (hy : 0 < margY μ y) : β ≤ margY μ y := by
  have hex : ∃ p ∈ (Finset.univ.filter fun p : X × Y × Z => p.2.1 = y), 0 < μ.prob p := by
    by_contra hne
    push Not at hne
    have : margY μ y ≤ 0 := Finset.sum_nonpos hne
    linarith
  obtain ⟨p, hp, hpos⟩ := hex
  calc β ≤ μ.prob p := hatom p hpos.ne'
    _ ≤ margY μ y := Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p) hp

theorem k6pt_margZ_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ}
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) {z : Z} (hz : 0 < margZ μ z) : β ≤ margZ μ z := by
  have hex : ∃ p ∈ (Finset.univ.filter fun p : X × Y × Z => p.2.2 = z), 0 < μ.prob p := by
    by_contra hne
    push Not at hne
    have : margZ μ z ≤ 0 := Finset.sum_nonpos hne
    linarith
  obtain ⟨p, hp, hpos⟩ := hex
  calc β ≤ μ.prob p := hatom p hpos.ne'
    _ ≤ margZ μ z := Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p) hp

theorem k6pt_walkYZ_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (N : ℕ) (xs : List X) (hxs : xs.length = 2 * N + 1)
    (y : Y) (z : Z) (h : 0 < walkYZ μ xs y z) : β ^ (2 * N + 1) ≤ walkYZ μ xs y z := by
  induction N generalizing xs y z with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨x2, rest⟩⟩
    · simp at hxs
    · have hs : walkYZ μ [x] y z = stepYZ μ x y z := by simp [walkYZ]
      rw [hs] at h ⊢
      simpa using stepYZ_ge μ hatom (prob_ne_of_stepYZ_pos μ h)
    · simp at hxs
  | succ N ih =>
    rcases xs with _ | ⟨x1, _ | ⟨x2, rest⟩⟩
    · simp at hxs
    · simp at hxs
    · have hlen : rest.length = 2 * N + 1 := by simp at hxs; omega
      rw [walkYZ, Matrix.mul_apply] at h ⊢
      obtain ⟨y', hy'⟩ := exists_pos_of_sum_pos h
      have hAnn : 0 ≤ (stepYZ μ x1 * stepZY μ x2) y y' := by
        rw [Matrix.mul_apply]
        exact Finset.sum_nonneg fun z'' _ =>
          mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _)
      obtain ⟨hA, hw⟩ := both_pos_of_mul_pos hAnn (walkYZ_nonneg μ _ _ _) hy'
      have ihy := ih rest hlen y' z hw
      have hA' := hA
      rw [Matrix.mul_apply] at hA'
      obtain ⟨z', hz'⟩ := exists_pos_of_sum_pos hA'
      obtain ⟨hs1, hs2⟩ := both_pos_of_mul_pos (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _) hz'
      have g1 := stepYZ_ge μ hatom (prob_ne_of_stepYZ_pos μ hs1)
      have g2 := stepZY_ge μ hatom (prob_ne_of_stepZY_pos μ hs2)
      have hAle : stepYZ μ x1 y z' * stepZY μ x2 z' y' ≤ (stepYZ μ x1 * stepZY μ x2) y y' := by
        rw [Matrix.mul_apply]
        exact Finset.single_le_sum (f := fun z'' => stepYZ μ x1 y z'' * stepZY μ x2 z'' y')
          (fun z'' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _))
          (Finset.mem_univ z')
      have hnn : ∀ y'', 0 ≤ (stepYZ μ x1 * stepZY μ x2) y y'' * walkYZ μ rest y'' z :=
        fun y'' => mul_nonneg (by
          rw [Matrix.mul_apply]
          exact Finset.sum_nonneg fun z'' _ =>
            mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _))
          (walkYZ_nonneg μ _ _ _)
      calc β ^ (2 * (N + 1) + 1) = β * β * β ^ (2 * N + 1) := by ring
        _ ≤ (stepYZ μ x1 y z' * stepZY μ x2 z' y') * walkYZ μ rest y' z :=
          mul_le_mul (mul_le_mul g1 g2 hβ.le (stepYZ_nonneg μ _ _ _)) ihy (pow_pos hβ _).le
            (mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _))
        _ ≤ (stepYZ μ x1 * stepZY μ x2) y y' * walkYZ μ rest y' z :=
          mul_le_mul_of_nonneg_right hAle (walkYZ_nonneg μ _ _ _)
        _ ≤ ∑ y'', (stepYZ μ x1 * stepZY μ x2) y y'' * walkYZ μ rest y'' z :=
          Finset.single_le_sum (f := fun y'' =>
            (stepYZ μ x1 * stepZY μ x2) y y'' * walkYZ μ rest y'' z)
            (fun y'' _ => hnn y'') (Finset.mem_univ y')

theorem k6pt_pathTrick_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (ℓ : ℕ) (hℓ : Odd ℓ) :
    ∀ q ∈ (pathTrick μ ℓ hℓ).support, β ^ (ℓ + 1) ≤ (pathTrick μ ℓ hℓ).prob q := by
  rintro ⟨w, y, z⟩ hq
  have hq' : pathWeight μ ℓ hℓ w.1 y z ≠ 0 := hq
  obtain ⟨N, hN⟩ := id hℓ
  unfold pathWeight at hq'
  obtain ⟨hm0, hw0⟩ := mul_ne_zero_iff.1 hq'
  have hm : 0 < margY μ y := lt_of_le_of_ne (margY_nonneg μ y) (Ne.symm hm0)
  have hw : 0 < walkYZ μ (List.ofFn w.1) y z :=
    lt_of_le_of_ne (walkYZ_nonneg μ _ _ _) (Ne.symm hw0)
  have h1 := k6pt_margY_atom_ge μ hatom hm
  have h2 := k6pt_walkYZ_atom_ge μ hβ hatom N (List.ofFn w.1)
    (by rw [List.length_ofFn]; exact hN) y z hw
  show β ^ (ℓ + 1) ≤ margY μ y * walkYZ μ (List.ofFn w.1) y z
  calc β ^ (ℓ + 1) = β * β ^ (2 * N + 1) := by rw [hN]; ring
    _ ≤ margY μ y * walkYZ μ (List.ofFn w.1) y z := mul_le_mul h1 h2 (pow_pos hβ _).le hm.le

theorem k6pt_card_pathX_mul_le (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (ℓ : ℕ) (hℓ : Odd ℓ) :
    (Fintype.card (PathX μ ℓ hℓ) : ℝ) * β ^ (ℓ + 1) ≤ 1 := by
  have hs : ∀ w : PathX μ ℓ hℓ, ∃ y z, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support := fun w => by
    obtain ⟨y, z, h⟩ := w.2
    exact ⟨y, z, h⟩
  choose fy fz hf using hs
  exact atoms_card_mul_le (pathTrick μ ℓ hℓ) (fun w => (w, fy w, fz w))
    (fun a b h => (Prod.mk.inj h).1) hf (k6pt_pathTrick_atom_ge μ hβ hatom ℓ hℓ)

/-! ### Alphabet sizes -/

theorem k6pt_card_X_mul_atom_le (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    {β : ℝ} (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) : (Fintype.card X : ℝ) * β ≤ 1 := by
  have hs : ∀ x : X, ∃ y z, (x, y, z) ∈ μ.support := support_X_has_pt μ h
  choose fy fz hf using hs
  exact atoms_card_mul_le μ (fun x => (x, fy x, fz x)) (fun a b h => (Prod.mk.inj h).1) hf hatom

theorem k6pt_card_Y_mul_atom_le (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    {β : ℝ} (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) : (Fintype.card Y : ℝ) * β ≤ 1 := by
  have hs : ∀ y : Y, ∃ x z, (x, y, z) ∈ μ.support := support_Y_has_pt μ h
  choose fx fz hf using hs
  exact atoms_card_mul_le μ (fun y => (fx y, y, fz y))
    (fun a b h => (Prod.mk.inj (Prod.mk.inj h).2).1) hf hatom

theorem k6pt_card_Z_mul_atom_le (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    {β : ℝ} (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) : (Fintype.card Z : ℝ) * β ≤ 1 := by
  have hs : ∀ z : Z, ∃ x y, (x, y, z) ∈ μ.support := support_Z_has_pt μ h
  choose fx fy hf using hs
  exact atoms_card_mul_le μ (fun z => (fx z, fy z, z))
    (fun a b h => (Prod.mk.inj (Prod.mk.inj h).2).2) hf hatom

/-! ### Atom adapters for the three tricks -/

theorem k6ptViewY_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ}
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) :
    ∀ p ∈ (k6ptViewY μ).support, β ≤ (k6ptViewY μ).prob p :=
  perm_atom_ge _ _ hatom

theorem k6ptViewZ_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ}
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) :
    ∀ p ∈ (k6ptViewZ μ).support, β ≤ (k6ptViewZ μ).prob p :=
  perm_atom_ge _ _ hatom

theorem k6ptTrickX_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (r : ℕ) (hr : 1 ≤ r) :
    ∀ q ∈ (k6ptTrickX μ r hr).support, β ^ 2 ^ r ≤ (k6ptTrickX μ r hr).prob q := by
  have h := k6pt_pathTrick_atom_ge μ hβ hatom (2 ^ r - 1) (k6pt_odd hr)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact h

theorem k6ptTrickY_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (r : ℕ) (hr : 1 ≤ r) :
    ∀ q ∈ (k6ptTrickY μ r hr).support, β ^ 2 ^ r ≤ (k6ptTrickY μ r hr).prob q := by
  have h := k6pt_pathTrick_atom_ge (k6ptViewY μ) hβ (k6ptViewY_atom_ge μ hatom) (2 ^ r - 1)
    (k6pt_odd hr)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact perm_atom_ge _ _ h

theorem k6ptTrickZ_atom_ge (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (r : ℕ) (hr : 1 ≤ r) :
    ∀ q ∈ (k6ptTrickZ μ r hr).support, β ^ 2 ^ r ≤ (k6ptTrickZ μ r hr).prob q := by
  have h := k6pt_pathTrick_atom_ge (k6ptViewZ μ) hβ (k6ptViewZ_atom_ge μ hatom) (2 ^ r - 1)
    (k6pt_odd hr)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact perm_atom_ge _ _ h

theorem k6pt_card_sigPlus_mul_le (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (r : ℕ) (hr : 1 ≤ r) :
    (Fintype.card (K6ptSigPlus μ r hr) : ℝ) * β ^ 2 ^ r ≤ 1 := by
  have h := k6pt_card_pathX_mul_le μ hβ hatom (2 ^ r - 1) (k6pt_odd hr)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact h

theorem k6pt_card_gamPlus_mul_le (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (r : ℕ) (hr : 1 ≤ r) :
    (Fintype.card (K6ptGamPlus μ r hr) : ℝ) * β ^ 2 ^ r ≤ 1 := by
  have h := k6pt_card_pathX_mul_le (k6ptViewY μ) hβ (k6ptViewY_atom_ge μ hatom) (2 ^ r - 1)
    (k6pt_odd hr)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact h

theorem k6pt_card_phiPlus_mul_le (μ : FinProb (X × Y × Z)) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ μ.support, β ≤ μ.prob p) (r : ℕ) (hr : 1 ≤ r) :
    (Fintype.card (K6ptPhiPlus μ r hr) : ℝ) * β ^ 2 ^ r ≤ 1 := by
  have h := k6pt_card_pathX_mul_le (k6ptViewZ μ) hβ (k6ptViewZ_atom_ge μ hatom) (2 ^ r - 1)
    (k6pt_odd hr)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact h

end WalkAtoms

/-! ### Parameters -/
section Params

/-- `r₁ = ⌈log₂(2/α + 1)⌉`, floored at `1` so that `1 ≤ r₁` holds without hypotheses. -/
def k6ptR1 (α : ℝ) : ℕ := max 1 (Nat.clog 2 ⌈2 / α + 1⌉₊)

/-- `r₂`: the same rule at `α₁ = α ^ 2 ^ r₁`. -/
def k6ptR2 (α : ℝ) : ℕ := k6ptR1 (α ^ 2 ^ k6ptR1 α)

/-- `N = 2 ^ (r₁ + r₂ + 2)`. -/
def k6ptN (r₁ r₂ : ℕ) : ℕ := 2 ^ (r₁ + r₂ + 2)

/-- `α_* = min(1/2, α ^ N)` for `r₁ = k6ptR1 α`, `r₂ = k6ptR2 α`. -/
def k6ptAlphaStar (α : ℝ) : ℝ := min (1 / 2) (α ^ k6ptN (k6ptR1 α) (k6ptR2 α))

theorem one_le_k6ptR1 (α : ℝ) : 1 ≤ k6ptR1 α := le_max_left _ _

theorem one_le_k6ptR2 (α : ℝ) : 1 ≤ k6ptR2 α := one_le_k6ptR1 _

theorem k6ptR1_spec {α : ℝ} (hα : 0 < α) : 2 / α + 1 ≤ 2 ^ k6ptR1 α := by
  have h1 : 2 / α + 1 ≤ (⌈2 / α + 1⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ⌈2 / α + 1⌉₊ ≤ 2 ^ Nat.clog 2 ⌈2 / α + 1⌉₊ := Nat.le_pow_clog (by norm_num) _
  have h3 : 2 ^ Nat.clog 2 ⌈2 / α + 1⌉₊ ≤ 2 ^ k6ptR1 α :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have h4 : (⌈2 / α + 1⌉₊ : ℝ) ≤ ((2 ^ k6ptR1 α : ℕ) : ℝ) := by exact_mod_cast h2.trans h3
  calc 2 / α + 1 ≤ _ := h1
    _ ≤ _ := h4
    _ = 2 ^ k6ptR1 α := by push_cast; ring

theorem k6ptR2_spec {α : ℝ} (hα : 0 < α) : 2 / α ^ 2 ^ k6ptR1 α + 1 ≤ 2 ^ k6ptR2 α :=
  k6ptR1_spec (pow_pos hα _)

theorem sixteen_le_k6ptN {r₁ r₂ : ℕ} (h₁ : 1 ≤ r₁) (h₂ : 1 ≤ r₂) : 16 ≤ k6ptN r₁ r₂ := by
  unfold k6ptN
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (r₁ + r₂ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem k6ptAlphaStar_pos {α : ℝ} (hα : 0 < α) : 0 < k6ptAlphaStar α :=
  lt_min (by norm_num) (pow_pos hα _)

theorem k6ptAlphaStar_le_half (α : ℝ) : k6ptAlphaStar α ≤ 1 / 2 := min_le_left _ _

end Params

/-! ### The chain -/
section Chain
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- threshold `2 ^ r₁ ≥ |Σ| + |Φ|` of `k6pt_suppmu` from the atom bound and `2/α ≤ 2 ^ r₁`. -/
theorem k6pt_threshold_one (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support) {α : ℝ}
    (hα : 0 < α) (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {r₁ : ℕ} (h : 2 / α ≤ 2 ^ r₁) :
    Fintype.card X + Fintype.card Z ≤ 2 ^ r₁ := by
  have hX := k6pt_card_X_mul_atom_le μ hμ hatom
  have hZ := k6pt_card_Z_mul_atom_le μ hμ hatom
  have h1 : (Fintype.card X : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα]; exact hX
  have h2 : (Fintype.card Z : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα]; exact hZ
  have : ((Fintype.card X + Fintype.card Z : ℕ) : ℝ) ≤ 2 ^ r₁ := by
    push_cast
    calc (Fintype.card X : ℝ) + Fintype.card Z ≤ 1 / α + 1 / α := add_le_add h1 h2
      _ = 2 / α := by ring
      _ ≤ 2 ^ r₁ := h
  exact_mod_cast this

/-- threshold `2 ^ r₂ ≥ |Σ| + |Γ⁺|` of `k6pt_suppmu` from `2/α₁ ≤ 2 ^ r₂`, `α₁ = α ^ 2 ^ r₁`. -/
theorem k6pt_threshold_two (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support) {α : ℝ}
    (hα : 0 < α) (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {r₁ : ℕ} (hr₁ : 1 ≤ r₁) {r₂ : ℕ}
    (h : 2 / α ^ 2 ^ r₁ ≤ 2 ^ r₂) :
    Fintype.card X + Fintype.card (K6ptGam μ r₁ hr₁) ≤ 2 ^ r₂ := by
  obtain ⟨p0, hp0⟩ := exists_support_pt μ
  have hα1 : α ≤ 1 := (hatom p0 hp0).trans (prob_le_one_pt μ p0)
  have ha1 : 0 < α ^ 2 ^ r₁ := pow_pos hα _
  have ha1le : α ^ 2 ^ r₁ ≤ α := pow_le_of_le_one hα.le hα1 (by positivity)
  have hX := k6pt_card_X_mul_atom_le μ hμ hatom
  have hG := k6pt_card_gamPlus_mul_le μ hα hatom r₁ hr₁
  have h1 : (Fintype.card X : ℝ) ≤ 1 / α ^ 2 ^ r₁ := by
    have : (Fintype.card X : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα]; exact hX
    exact this.trans (one_div_le_one_div_of_le ha1 ha1le)
  have h2 : (Fintype.card (K6ptGam μ r₁ hr₁) : ℝ) ≤ 1 / α ^ 2 ^ r₁ := by
    rw [le_div_iff₀ ha1]; exact hG
  have : ((Fintype.card X + Fintype.card (K6ptGam μ r₁ hr₁) : ℕ) : ℝ) ≤ 2 ^ r₂ := by
    push_cast
    calc (Fintype.card X : ℝ) + Fintype.card (K6ptGam μ r₁ hr₁)
        ≤ 1 / α ^ 2 ^ r₁ + 1 / α ^ 2 ^ r₁ := add_le_add h1 h2
      _ = 2 / α ^ 2 ^ r₁ := by ring
      _ ≤ 2 ^ r₂ := h
  exact_mod_cast this

theorem k6ptMu1_atom_ge (μ : FinProb (X × Y × Z)) {α : ℝ} (hα : 0 < α)
    (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {r₁ : ℕ} (hr₁ : 1 ≤ r₁) :
    ∀ q ∈ (k6ptMu1 μ r₁ hr₁).support, α ^ 2 ^ r₁ ≤ (k6ptMu1 μ r₁ hr₁).prob q :=
  k6ptTrickY_atom_ge μ hα hatom r₁ hr₁

theorem k6ptMu2_atom_ge (μ : FinProb (X × Y × Z)) {α : ℝ} (hα : 0 < α)
    (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    ∀ q ∈ (k6ptMu2 μ r₁ hr₁ r₂ hr₂).support,
      (α ^ 2 ^ r₁) ^ 2 ^ r₂ ≤ (k6ptMu2 μ r₁ hr₁ r₂ hr₂).prob q :=
  k6ptTrickZ_atom_ge (k6ptMu1 μ r₁ hr₁) (pow_pos hα _) (k6ptMu1_atom_ge μ hα hatom hr₁) r₂ hr₂

/-- every atom of `μ⁺` is `≥ α ^ N`, `N = 2 ^ (r₁ + r₂ + 2)`; no connectivity is needed. -/
theorem k6ptMuPlus_atom_ge (μ : FinProb (X × Y × Z)) {α : ℝ} (hα : 0 < α)
    (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    ∀ q ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support,
      α ^ k6ptN r₁ r₂ ≤ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob q := by
  have h := k6pt_pathTrick_atom_ge (k6ptMu2 μ r₁ hr₁ r₂ hr₂) (pow_pos (pow_pos hα _) _)
    (k6ptMu2_atom_ge μ hα hatom hr₁ hr₂) 3 k6pt_odd_three
  have he : ((α ^ 2 ^ r₁) ^ 2 ^ r₂) ^ (3 + 1) = α ^ k6ptN r₁ r₂ := by
    rw [← pow_mul, ← pow_mul]
    unfold k6ptN
    congr 1
    ring
  rw [he] at h
  exact h

end Chain

end TrackB
end RestrictedPolynomials
end
