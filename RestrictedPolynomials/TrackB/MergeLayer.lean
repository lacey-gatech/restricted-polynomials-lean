module

public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.FinProbSupport

/-!
# Track B: the paper-IV merge layer

Paper IV items `definition-imply-coordinate`, `def:fully-merged`, `def:merge`, and the trivial-`H` part of
`remark-merge-preserves-hypotheses` (paper IV `writeup_stability.tex` L2668-2702).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Merge
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- paper IV `definition-imply-coordinate`: `y, z` imply `x` in `P`. -/
def mergeImpliesX (P : Set (X × Y × Z)) : Prop :=
  ∀ (y : Y) (z : Z) (x x' : X), (x, y, z) ∈ P → (x', y, z) ∈ P → x = x'

/-- `x, z` imply `y` in `P`. -/
def mergeImpliesY (P : Set (X × Y × Z)) : Prop :=
  ∀ (x : X) (z : Z) (y y' : Y), (x, y, z) ∈ P → (x, y', z) ∈ P → y = y'

/-- `x, y` imply `z` in `P`. -/
def mergeImpliesZ (P : Set (X × Y × Z)) : Prop :=
  ∀ (x : X) (y : Y) (z z' : Z), (x, y, z) ∈ P → (x, y, z') ∈ P → z = z'

/-- paper IV `def:fully-merged` (Def 5.2): any two coordinates imply the third, in `supp μ`. -/
def mergeFullyMerged (μ : FinProb (X × Y × Z)) : Prop :=
  mergeImpliesX μ.support ∧ mergeImpliesY μ.support ∧ mergeImpliesZ μ.support

/-- paper IV `def:merge`: the graph `G_{x,μ,merge}` on `Σ` (for a support `P`). -/
def mergeGraphX (P : Set (X × Y × Z)) : SimpleGraph X :=
  SimpleGraph.fromRel fun x x' => ∃ (y : Y) (z : Z), (x, y, z) ∈ P ∧ (x', y, z) ∈ P

/-- the graph `G_{y,μ,merge}` on `Γ`. -/
def mergeGraphY (P : Set (X × Y × Z)) : SimpleGraph Y :=
  SimpleGraph.fromRel fun y y' => ∃ (x : X) (z : Z), (x, y, z) ∈ P ∧ (x, y', z) ∈ P

/-- the graph `G_{z,μ,merge}` on `Φ`. -/
def mergeGraphZ (P : Set (X × Y × Z)) : SimpleGraph Z :=
  SimpleGraph.fromRel fun z z' => ∃ (x : X) (y : Y), (x, y, z) ∈ P ∧ (x, y, z') ∈ P

/-- `a v` is the distinguished element of the component of `v` (a choice of `x_i^⋆`). -/
def MergeRep {V : Type} (G : SimpleGraph V) (a : V → V) : Prop :=
  (∀ v, G.Reachable v (a v)) ∧ ∀ v w, G.Reachable v w → a v = a w

/-- the image law of `π` under `f`. -/
def mergePush {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α) (f : α → β) :
    FinProb β where
  prob b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), π.prob a
  nonneg b := Finset.sum_nonneg fun a _ => π.nonneg a
  sum_eq_one := by
    rw [← π.sum_eq_one]
    exact Finset.sum_fiberwise Finset.univ f π.prob

/-- paper IV `def:merge`: the `x`-merged distribution `μ'` over `Σ' × Γ × Φ`, `Σ' = range a`. -/
def mergeDistX (μ : FinProb (X × Y × Z)) (a : X → X) : FinProb (↥(Set.range a) × Y × Z) :=
  mergePush μ fun p => (⟨a p.1, Set.mem_range_self _⟩, p.2.1, p.2.2)

/-- the `y`-merged distribution (Remark 5.4(1)). -/
def mergeDistY (μ : FinProb (X × Y × Z)) (b : Y → Y) : FinProb (X × ↥(Set.range b) × Z) :=
  mergePush μ fun p => (p.1, ⟨b p.2.1, Set.mem_range_self _⟩, p.2.2)

/-- the `z`-merged distribution (Remark 5.4(1)). -/
def mergeDistZ (μ : FinProb (X × Y × Z)) (c : Z → Z) : FinProb (X × Y × ↥(Set.range c)) :=
  mergePush μ fun p => (p.1, p.2.1, ⟨c p.2.2, Set.mem_range_self _⟩)

/-- a surjective graph homomorphism preserves connectedness. -/
private theorem private_conn_map {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (F : V → W)
    (hF : Function.Surjective F) (hadj : ∀ u v, G.Adj u v → H.Adj (F u) (F v)) (hc : G.Connected) :
    H.Connected :=
  hc.map ⟨F, fun {u v} h => hadj u v h⟩ hF

theorem exists_mergeRep {V : Type} (G : SimpleGraph V) : ∃ a : V → V, MergeRep G a := by
  have hs : ∀ c : G.ConnectedComponent, ∃ v, G.connectedComponentMk v = c :=
    fun c => c.ind (fun v => ⟨v, rfl⟩)
  refine ⟨fun v => Classical.choose (hs (G.connectedComponentMk v)), fun v => ?_, fun v w hvw => ?_⟩
  · exact SimpleGraph.ConnectedComponent.exact (Classical.choose_spec (hs (G.connectedComponentMk v))).symm
  · dsimp only
    rw [SimpleGraph.ConnectedComponent.eq.mpr hvw]

omit [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z] in
theorem mergeGraphX_components_iff (P : Set (X × Y × Z)) :
    Nat.card (mergeGraphX P).ConnectedComponent = Fintype.card X ↔ mergeImpliesX P := by
  have hsurj : Function.Surjective (mergeGraphX P).connectedComponentMk :=
    fun c => c.ind (fun v => ⟨v, rfl⟩)
  have hfin : Finite (mergeGraphX P).ConnectedComponent := Finite.of_surjective _ hsurj
  constructor
  · intro hc
    have hb : Function.Bijective (mergeGraphX P).connectedComponentMk :=
      hsurj.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, hc])
    intro y z x x' hx hx'
    by_cases hxx : x = x'
    · exact hxx
    · have hadj : (mergeGraphX P).Adj x x' := by
        simp only [mergeGraphX, SimpleGraph.fromRel_adj]
        exact ⟨hxx, Or.inl ⟨y, z, hx, hx'⟩⟩
      exact hb.1 (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable)
  · intro h
    have key : ∀ v w, (mergeGraphX P).Reachable v w → v = w := by
      rintro v w ⟨p⟩
      induction p with
      | nil => rfl
      | cons hadj _ _ =>
        exfalso
        simp only [mergeGraphX, SimpleGraph.fromRel_adj] at hadj
        obtain ⟨hne, ⟨y, z, h1, h2⟩ | ⟨y, z, h1, h2⟩⟩ := hadj
        · exact hne (h y z _ _ h1 h2)
        · exact hne (h y z _ _ h2 h1)
    have hinj : Function.Injective (mergeGraphX P).connectedComponentMk := fun v w hvw =>
      key v w (SimpleGraph.ConnectedComponent.exact hvw)
    rw [← Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card]


theorem mergeDistX_support (μ : FinProb (X × Y × Z)) (a : X → X)
    (x' : ↥(Set.range a)) (y : Y) (z : Z) :
    (x', y, z) ∈ (mergeDistX μ a).support ↔
      ∃ x : X, a x = x'.1 ∧ (x, y, z) ∈ μ.support := by
  show (∑ p ∈ Finset.univ.filter (fun p : X × Y × Z =>
      ((⟨a p.1, Set.mem_range_self _⟩ : ↥(Set.range a)), p.2.1, p.2.2) = (x', y, z)),
      μ.prob p) ≠ 0 ↔ _
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun p _ => μ.nonneg p]
  push Not
  constructor
  · rintro ⟨⟨x, y₀, z₀⟩, hp, hne⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hp
    obtain ⟨h1, rfl, rfl⟩ := hp
    exact ⟨x, congrArg Subtype.val h1, hne⟩
  · rintro ⟨x, hx, hne⟩
    refine ⟨(x, y, z), ?_, hne⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    exact ⟨Subtype.ext hx, trivial⟩

theorem mergeDistX_impliesX (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) : mergeImpliesX (mergeDistX μ a).support := by
  intro y z x₁ x₂ h₁ h₂
  obtain ⟨u₁, hu₁, hs₁⟩ := (mergeDistX_support μ a x₁ y z).mp h₁
  obtain ⟨u₂, hu₂, hs₂⟩ := (mergeDistX_support μ a x₂ y z).mp h₂
  have hr : (mergeGraphX μ.support).Reachable u₁ u₂ := by
    by_cases h : u₁ = u₂
    · rw [h]
    · exact (SimpleGraph.Adj.reachable (by
        simp only [mergeGraphX, SimpleGraph.fromRel_adj]
        exact ⟨h, Or.inl ⟨y, z, hs₁, hs₂⟩⟩))
  exact Subtype.ext (hu₁.symm.trans ((ha.2 u₁ u₂ hr).trans hu₂))

theorem mergeDistX_atom_bound (μ : FinProb (X × Y × Z)) (a : X → X) {α₀ : ℝ}
    (h : ∀ p ∈ μ.support, α₀ ≤ μ.prob p) :
    ∀ p ∈ (mergeDistX μ a).support, α₀ ≤ (mergeDistX μ a).prob p := by
  intro p hp
  obtain ⟨x', y, z⟩ := p
  obtain ⟨x, hx, hs⟩ := (mergeDistX_support μ a x' y z).mp hp
  have hle : μ.prob (x, y, z) ≤ (mergeDistX μ a).prob (x', y, z) := by
    show _ ≤ ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z =>
      ((⟨a p.1, Set.mem_range_self _⟩ : ↥(Set.range a)), p.2.1, p.2.2) = (x', y, z)), μ.prob p
    exact Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p)
      (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
          exact ⟨Subtype.ext hx, trivial⟩)
  exact (h _ hs).trans hle

theorem mergeDistX_embedding_lift (μ : FinProb (X × Y × Z)) (a : X → X) {H : Type}
    [AddCommGroup H] (σ' : ↥(Set.range a) → H) (γ : Y → H) (φ : Z → H)
    (h : IsEmbedding3 (mergeDistX μ a).support σ' γ φ) :
    IsEmbedding3 μ.support (fun x => σ' ⟨a x, Set.mem_range_self _⟩) γ φ := by
  rw [isEmbedding3_iff] at h ⊢
  intro p hp
  exact h (⟨a p.1, Set.mem_range_self _⟩, p.2.1, p.2.2)
    ((mergeDistX_support μ a _ _ _).mpr ⟨p.1, rfl, hp⟩)

omit [DecidableEq X] in
/-- alphabet size does not grow (hypothesis 2 of Thm 4.13 passes to the merge). -/
theorem mergeDistX_card_le (a : X → X) : Nat.card ↥(Set.range a) ≤ Nat.card X :=
  Nat.card_le_card_of_surjective (fun x => (⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a)))
    (fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩)

/-- the lift, for one fixed target group `H` (e.g. `H = ℤ`). -/
theorem mergeDistX_not_admitsEmbeddingInto3 (μ : FinProb (X × Y × Z)) (a : X → X) {H : Type}
    [AddCommGroup H] (h : ¬ AdmitsEmbeddingInto3 μ.support H) :
    ¬ AdmitsEmbeddingInto3 (mergeDistX μ a).support H := by
  rw [admitsEmbeddingInto3_iff] at h ⊢
  rintro ⟨σ', γ, φ, hemb, hnt⟩
  refine h ⟨fun x => σ' ⟨a x, Set.mem_range_self _⟩, γ, φ,
    mergeDistX_embedding_lift μ a σ' γ φ hemb, ?_⟩
  rw [isNontrivialEmbedding3_iff] at hnt ⊢
  rintro ⟨h0, h1, h2⟩
  apply hnt
  refine ⟨?_, h1, h2⟩
  rintro ⟨u, x, hx⟩ ⟨v, x', hx'⟩
  subst hx; subst hx'
  exact h0 x x'

theorem mergeDistX_not_admitsAbelianEmbedding (μ : FinProb (X × Y × Z)) (a : X → X)
    (h : ¬ AdmitsAbelianEmbedding3 μ.support) :
    ¬ AdmitsAbelianEmbedding3 (mergeDistX μ a).support := by
  rintro ⟨G, inst, hG⟩
  exact h ⟨G, inst, by
    by_contra hn
    exact mergeDistX_not_admitsEmbeddingInto3 μ a hn hG⟩

theorem mergeDistX_pairwiseConnected (μ : FinProb (X × Y × Z)) (a : X → X)
    (ha : MergeRep (mergeGraphX μ.support) a) (h : PairwiseConnected3 μ.support) :
    PairwiseConnected3 (mergeDistX μ a).support := by
  rw [pairwiseConnected3_iff] at h ⊢
  obtain ⟨hXY, hXZ, hYZ⟩ := h
  have hmem : ∀ x y z, (x, y, z) ∈ μ.support →
      ((⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a)), y, z) ∈ (mergeDistX μ a).support :=
    fun x y z hx => (mergeDistX_support μ a _ _ _).mpr ⟨x, rfl, hx⟩
  have hgs : Function.Surjective
      (fun x : X => (⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a))) :=
    fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩
  refine ⟨?_, ?_, ?_⟩
  · refine private_conn_map _ _ (Sum.map (fun x : X => (⟨a x, Set.mem_range_self _⟩ :
        ↥(Set.range a))) id) ?_ ?_ hXY
    · rintro (x' | y)
      · obtain ⟨x, hx⟩ := hgs x'
        exact ⟨Sum.inl x, by simp [hx]⟩
      · exact ⟨Sum.inr y, rfl⟩
    · intro u v huv
      simp only [SimpleGraph.fromRel_adj] at huv ⊢
      obtain ⟨-, ⟨x, y, z, hs, rfl, rfl⟩ | ⟨x, y, z, hs, rfl, rfl⟩⟩ := huv
      all_goals simp only [Sum.map_inl, Sum.map_inr, id_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        true_and]
      · exact Or.inl ⟨_, y, z, hmem x y z hs, rfl, rfl⟩
      · exact Or.inr ⟨_, y, z, hmem x y z hs, rfl, rfl⟩
  · refine private_conn_map _ _ (Sum.map (fun x : X => (⟨a x, Set.mem_range_self _⟩ :
        ↥(Set.range a))) id) ?_ ?_ hXZ
    · rintro (x' | y)
      · obtain ⟨x, hx⟩ := hgs x'
        exact ⟨Sum.inl x, by simp [hx]⟩
      · exact ⟨Sum.inr y, rfl⟩
    · intro u v huv
      simp only [SimpleGraph.fromRel_adj] at huv ⊢
      obtain ⟨-, ⟨x, y, z, hs, rfl, rfl⟩ | ⟨x, y, z, hs, rfl, rfl⟩⟩ := huv
      all_goals simp only [Sum.map_inl, Sum.map_inr, id_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        true_and]
      · exact Or.inl ⟨_, y, z, hmem x y z hs, rfl, rfl⟩
      · exact Or.inr ⟨_, y, z, hmem x y z hs, rfl, rfl⟩
  · refine private_conn_map _ _ id (fun v => ⟨v, rfl⟩) ?_ hYZ
    intro u v huv
    simp only [SimpleGraph.fromRel_adj] at huv ⊢
    obtain ⟨hne, ⟨x, y, z, hs, rfl, rfl⟩ | ⟨x, y, z, hs, rfl, rfl⟩⟩ := huv
    · exact ⟨hne, Or.inl ⟨_, y, z, hmem x y z hs, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨_, y, z, hmem x y z hs, rfl, rfl⟩⟩

theorem mergeDistX_fullYZ (μ : FinProb (X × Y × Z)) (a : X → X)
    (h : ∀ (y : Y) (z : Z), ∃ x : X, (x, y, z) ∈ μ.support) :
    ∀ (y : Y) (z : Z), ∃ x' : ↥(Set.range a), (x', y, z) ∈ (mergeDistX μ a).support := by
  intro y z
  obtain ⟨x, hx⟩ := h y z
  exact ⟨⟨a x, Set.mem_range_self _⟩, (mergeDistX_support μ a _ _ _).mpr ⟨x, rfl, hx⟩⟩

end Merge
end TrackB
end RestrictedPolynomials
end
