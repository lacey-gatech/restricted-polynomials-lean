module

public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.TrackB.MasterEmbedding
public import RestrictedPolynomials.TrackB.MergeLayer

/-!
# Track B: the class `𝒯` (Supplement E)

Supplement E items: `def:T`, `lem:T-enlarge`, `lem:T-basic`, `lem:T-perm`,
`lem:sizes-F`, `cor:hole-empty`.

Reading: saturation in `T-basic` (3) is read as surjectivity; any one
of the three maps being onto suffices.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Class
variable {X Y Z : Type}

/-- Supplement E `def:T`: `S ∈ 𝒯`: pairwise connected and no non-trivial Abelian embedding. -/
def InT (S : Set (X × Y × Z)) : Prop :=
  PairwiseConnected3 S ∧ ¬ AdmitsAbelianEmbedding3 S

/-- `y, z ⇒ x`, `x, z ⇒ y`, `x, y ⇒ z` in `S` (paper IV `def:fully-merged`, for a support). -/
def FullyMergedSet (S : Set (X × Y × Z)) : Prop :=
  mergeImpliesX S ∧ mergeImpliesY S ∧ mergeImpliesZ S

theorem mergeFullyMerged_iff [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (μ : FinProb (X × Y × Z)) :
    mergeFullyMerged μ ↔ FullyMergedSet μ.support := Iff.rfl

/-- slot permutations and relabellings of a set of triples -/
def swapXY (S : Set (X × Y × Z)) : Set (Y × X × Z) := (fun p => (p.2.1, p.1, p.2.2)) '' S
def swapYZ (S : Set (X × Y × Z)) : Set (X × Z × Y) := (fun p => (p.1, p.2.2, p.2.1)) '' S
def swapXZ (S : Set (X × Y × Z)) : Set (Z × Y × X) := (fun p => (p.2.2, p.2.1, p.1)) '' S
def relabelSet {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z') (S : Set (X × Y × Z)) :
    Set (X' × Y' × Z') := (fun p => (eX p.1, eY p.2.1, eZ p.2.2)) '' S

/-! ### private helpers: bipartite graphs of a relation -/

/-- the bipartite graph of a relation. -/
private def bip {A B : Type} (R : A → B → Prop) : SimpleGraph (A ⊕ B) :=
  SimpleGraph.fromRel fun u v => ∃ a b, R a b ∧ u = Sum.inl a ∧ v = Sum.inr b

private def r12 (S : Set (X × Y × Z)) (x : X) (y : Y) : Prop := ∃ z, (x, y, z) ∈ S
private def r13 (S : Set (X × Y × Z)) (x : X) (z : Z) : Prop := ∃ y, (x, y, z) ∈ S
private def r23 (S : Set (X × Y × Z)) (y : Y) (z : Z) : Prop := ∃ x, (x, y, z) ∈ S

private theorem pc3_iff_bip (S : Set (X × Y × Z)) :
    PairwiseConnected3 S ↔
      (bip (r12 S)).Connected ∧ (bip (r13 S)).Connected ∧ (bip (r23 S)).Connected := by
  rw [pairwiseConnected3_iff]
  have e12 : (SimpleGraph.fromRel fun (a : X ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y) = bip (r12 S) := by
    unfold bip
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨x, y, z, h, h1, h2⟩
      exact ⟨x, y, ⟨z, h⟩, h1, h2⟩
    · rintro ⟨x, y, ⟨z, h⟩, h1, h2⟩
      exact ⟨x, y, z, h, h1, h2⟩
  have e13 : (SimpleGraph.fromRel fun (a : X ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z) = bip (r13 S) := by
    unfold bip
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨x, y, z, h, h1, h2⟩
      exact ⟨x, z, ⟨y, h⟩, h1, h2⟩
    · rintro ⟨x, z, ⟨y, h⟩, h1, h2⟩
      exact ⟨x, y, z, h, h1, h2⟩
  have e23 : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z) = bip (r23 S) := by
    unfold bip
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨x, y, z, h, h1, h2⟩
      exact ⟨y, z, ⟨x, h⟩, h1, h2⟩
    · rintro ⟨y, z, ⟨x, h⟩, h1, h2⟩
      exact ⟨x, y, z, h, h1, h2⟩
  rw [e12, e13, e23]

private theorem conn_bip_congr {A B : Type} {R R' : A → B → Prop} (h : ∀ a b, R a b ↔ R' a b) :
    (bip R).Connected ↔ (bip R').Connected := by
  have : R = R' := by
    funext a b
    exact propext (h a b)
  subst this
  exact Iff.rfl

private theorem conn_bip_equiv {A B A' B' : Type} (eA : A ≃ A') (eB : B ≃ B')
    {R : A → B → Prop} {R' : A' → B' → Prop} (h : ∀ a b, R' (eA a) (eB b) ↔ R a b) :
    (bip R').Connected ↔ (bip R).Connected := by
  let iso : bip R ≃g bip R' :=
    { toEquiv := Equiv.sumCongr eA eB
      map_rel_iff' := by
        intro u v
        simp only [bip, SimpleGraph.fromRel_adj]
        rcases u with u | u <;> rcases v with v | v <;> simp [h] }
  exact iso.connected_iff.symm

private theorem conn_bip_swap {A B : Type} (R : A → B → Prop) :
    (bip (fun b a => R a b)).Connected ↔ (bip R).Connected := by
  let iso : bip R ≃g bip (fun b a => R a b) :=
    { toEquiv := Equiv.sumComm A B
      map_rel_iff' := by
        intro u v
        simp only [bip, SimpleGraph.fromRel_adj]
        rcases u with u | u <;> rcases v with v | v <;> simp <;> aesop }
  exact iso.connected_iff.symm

private theorem admits_iff (S : Set (X × Y × Z)) :
    AdmitsAbelianEmbedding3 S ↔ ∃ (G : Type) (_ : AddCommGroup G) (σ : X → G) (γ : Y → G)
      (φ : Z → G), (∀ p ∈ S, σ p.1 + γ p.2.1 + φ p.2.2 = 0) ∧
        ¬ ((∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b)) := by
  constructor
  · rintro ⟨G, inst, h⟩
    have h' : AdmitsEmbeddingInto3 S G := h
    rw [admitsEmbeddingInto3_iff] at h'
    obtain ⟨σ, γ, φ, he, hn⟩ := h'
    rw [isEmbedding3_iff] at he
    rw [isNontrivialEmbedding3_iff] at hn
    exact ⟨G, inst, σ, γ, φ, he, hn⟩
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, ?_⟩
    show AdmitsEmbeddingInto3 S G
    rw [admitsEmbeddingInto3_iff]
    exact ⟨σ, γ, φ, (isEmbedding3_iff _ _ _ _).2 he, (isNontrivialEmbedding3_iff _ _ _).2 hn⟩

private theorem mem_swapXY {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (y, x, z) ∈ swapXY S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

private theorem mem_swapYZ {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (x, z, y) ∈ swapYZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

private theorem mem_swapXZ {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (z, y, x) ∈ swapXZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

private theorem mem_relabelSet {X' Y' Z' : Type} {eX : X ≃ X'} {eY : Y ≃ Y'} {eZ : Z ≃ Z'}
    {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (eX x, eY y, eZ z) ∈ relabelSet eX eY eZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

/-! ### L2: enlargement; T-basic -/

theorem InT.mono {S S' : Set (X × Y × Z)} (hS : InT S) (h : S ⊆ S') : InT S' := by
  obtain ⟨hc, hn⟩ := hS
  refine ⟨?_, ?_⟩
  · rw [pc3_iff_bip] at hc ⊢
    have mono : ∀ {A B : Type} {R R' : A → B → Prop}, (∀ a b, R a b → R' a b) →
        (bip R).Connected → (bip R').Connected := by
      intro A B R R' hR hconn
      refine SimpleGraph.Connected.mono ?_ hconn
      intro u v huv
      simp only [bip, SimpleGraph.fromRel_adj] at huv ⊢
      obtain ⟨hne, hr⟩ := huv
      refine ⟨hne, ?_⟩
      rcases hr with ⟨a, b, hab, h1, h2⟩ | ⟨a, b, hab, h1, h2⟩
      · exact Or.inl ⟨a, b, hR a b hab, h1, h2⟩
      · exact Or.inr ⟨a, b, hR a b hab, h1, h2⟩
    exact ⟨mono (fun a b ⟨z, hz⟩ => ⟨z, h hz⟩) hc.1,
      mono (fun a b ⟨y, hy⟩ => ⟨y, h hy⟩) hc.2.1,
      mono (fun a b ⟨x, hx⟩ => ⟨x, h hx⟩) hc.2.2⟩
  · intro hA
    apply hn
    rw [admits_iff] at hA ⊢
    obtain ⟨G, inst, σ, γ, φ, he, hnt⟩ := hA
    exact ⟨G, inst, σ, γ, φ, fun p hp => he p (h hp), hnt⟩

theorem PairwiseConnected3.nonempty_alphabets {S : Set (X × Y × Z)} (h : PairwiseConnected3 S) :
    Nonempty X ∧ Nonempty Y ∧ Nonempty Z ∧ S.Nonempty := by
  have hS : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [pc3_iff_bip] at h
    obtain ⟨h12, h13, h23⟩ := h
    have sub : ∀ {A B : Type} (R : A → B → Prop), (∀ a b, ¬ R a b) → (bip R).Connected →
        ∀ u v : A ⊕ B, u = v := by
      intro A B R hR hc u v
      obtain ⟨p⟩ := hc.preconnected u v
      cases p with
      | nil => rfl
      | cons hadj _ =>
        exfalso
        simp only [bip, SimpleGraph.fromRel_adj] at hadj
        obtain ⟨_, ⟨a, b, hab, _⟩ | ⟨a, b, hab, _⟩⟩ := hadj <;> exact hR a b hab
    have n12 := sub (r12 (∅ : Set (X × Y × Z))) (fun a b ⟨z, hz⟩ => hz) h12
    have n13 := sub (r13 (∅ : Set (X × Y × Z))) (fun a b ⟨z, hz⟩ => hz) h13
    have n23 := sub (r23 (∅ : Set (X × Y × Z))) (fun a b ⟨z, hz⟩ => hz) h23
    have c12 := h12.nonempty
    have c13 := h13.nonempty
    have c23 := h23.nonempty
    by_cases hx : Nonempty X
    · obtain ⟨x⟩ := hx
      obtain ⟨u⟩ := c23
      rcases u with y | z
      · have := n12 (Sum.inl x) (Sum.inr y)
        exact absurd this (by simp)
      · have := n13 (Sum.inl x) (Sum.inr z)
        exact absurd this (by simp)
    · rw [not_nonempty_iff] at hx
      obtain ⟨u⟩ := c12
      rcases u with x | y
      · exact hx.elim x
      · obtain ⟨v⟩ := c13
        rcases v with x | z
        · exact hx.elim x
        · have := n23 (Sum.inl y) (Sum.inr z)
          exact absurd this (by simp)
  obtain ⟨⟨x, y, z⟩, hp⟩ := hS
  exact ⟨⟨x⟩, ⟨y⟩, ⟨z⟩, ⟨_, hp⟩⟩

private theorem exists_adj_of_conn {V : Type} {G : SimpleGraph V} (hc : G.Connected) {u v : V}
    (huv : u ≠ v) : ∃ w, G.Adj u w := by
  obtain ⟨p⟩ := hc.preconnected u v
  cases p with
  | nil => exact absurd rfl huv
  | cons hadj _ => exact ⟨_, hadj⟩

theorem PairwiseConnected3.exists_atom_x {S : Set (X × Y × Z)} (h : PairwiseConnected3 S) (x : X) :
    ∃ y z, (x, y, z) ∈ S := by
  obtain ⟨_, ⟨y0⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets h
  have h12 := ((pc3_iff_bip S).1 h).1
  obtain ⟨w, hw⟩ := exists_adj_of_conn h12 (u := Sum.inl x) (v := Sum.inr y0) (by simp)
  simp only [bip, SimpleGraph.fromRel_adj] at hw
  obtain ⟨_, ⟨a, b, ⟨z, hz⟩, h1, h2⟩ | ⟨a, b, ⟨z, hz⟩, h1, h2⟩⟩ := hw
  · cases h1
    subst h2
    exact ⟨b, z, hz⟩
  · cases h2

theorem PairwiseConnected3.exists_atom_y {S : Set (X × Y × Z)} (h : PairwiseConnected3 S) (y : Y) :
    ∃ x z, (x, y, z) ∈ S := by
  obtain ⟨⟨x0⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets h
  have h12 := ((pc3_iff_bip S).1 h).1
  obtain ⟨w, hw⟩ := exists_adj_of_conn h12 (u := Sum.inr y) (v := Sum.inl x0) (by simp)
  simp only [bip, SimpleGraph.fromRel_adj] at hw
  obtain ⟨_, ⟨a, b, ⟨z, hz⟩, h1, h2⟩ | ⟨a, b, ⟨z, hz⟩, h1, h2⟩⟩ := hw
  · cases h1
  · cases h2
    subst h1
    exact ⟨a, z, hz⟩

theorem PairwiseConnected3.exists_atom_z {S : Set (X × Y × Z)} (h : PairwiseConnected3 S) (z : Z) :
    ∃ x y, (x, y, z) ∈ S := by
  obtain ⟨⟨x0⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets h
  have h13 := ((pc3_iff_bip S).1 h).2.1
  obtain ⟨w, hw⟩ := exists_adj_of_conn h13 (u := Sum.inr z) (v := Sum.inl x0) (by simp)
  simp only [bip, SimpleGraph.fromRel_adj] at hw
  obtain ⟨_, ⟨a, b, ⟨y, hy⟩, h1, h2⟩ | ⟨a, b, ⟨y, hy⟩, h1, h2⟩⟩ := hw
  · cases h1
  · cases h2
    subst h1
    exact ⟨a, y, hy⟩

theorem eq_univ_of_pairwiseConnected_unique [Unique X] [Unique Y] [Unique Z] {S : Set (X × Y × Z)}
    (h : PairwiseConnected3 S) : S = Set.univ := by
  obtain ⟨_, _, _, q, hq⟩ := MaxT.PairwiseConnected3.nonempty_alphabets h
  rw [Set.eq_univ_iff_forall]
  intro p
  have : p = q := Subsingleton.elim _ _
  rw [this]
  exact hq

theorem inT_univ_of_unique [Unique X] [Unique Y] [Unique Z] : InT (Set.univ : Set (X × Y × Z)) := by
  refine ⟨?_, ?_⟩
  · rw [pc3_iff_bip]
    have key : ∀ {A B : Type} [Unique A] [Unique B] (R : A → B → Prop), (∀ a b, R a b) →
        (bip R).Connected := by
      intro A B _ _ R hR
      haveI : Nonempty (A ⊕ B) := ⟨Sum.inl default⟩
      refine ⟨fun u v => ?_⟩
      rcases u with a | b <;> rcases v with a' | b'
      · rw [Subsingleton.elim a a']
      · refine SimpleGraph.Adj.reachable ?_
        simp only [bip, SimpleGraph.fromRel_adj]
        exact ⟨by simp, Or.inl ⟨a, b', hR a b', rfl, rfl⟩⟩
      · refine SimpleGraph.Adj.reachable ?_
        simp only [bip, SimpleGraph.fromRel_adj]
        exact ⟨by simp, Or.inr ⟨a', b, hR a' b, rfl, rfl⟩⟩
      · rw [Subsingleton.elim b b']
    exact ⟨key _ fun a b => ⟨default, Set.mem_univ _⟩, key _ fun a b => ⟨default, Set.mem_univ _⟩,
      key _ fun a b => ⟨default, Set.mem_univ _⟩⟩
  · intro hA
    rw [admits_iff] at hA
    obtain ⟨G, inst, σ, γ, φ, _, hn⟩ := hA
    exact hn ⟨fun a b => by rw [Subsingleton.elim a b], fun a b => by rw [Subsingleton.elim a b],
      fun a b => by rw [Subsingleton.elim a b]⟩

/-- Supplement E `lem:T-basic` (3), saturation read as: at least one of the three maps is onto. -/
theorem InT.master_subsingleton {S : Set (X × Y × Z)} (hS : InT S) {s : ℕ} {H : Fin s → Type}
    [∀ i, AddCommGroup (H i)] {σ : X → ∀ i, H i} {γ : Y → ∀ i, H i} {φ : Z → ∀ i, H i}
    (hm : IsMasterEmbedding S H σ γ φ)
    (hsat : Function.Surjective σ ∨ Function.Surjective γ ∨ Function.Surjective φ) :
    Subsingleton (∀ i, H i) := by
  have hemb := (isEmbedding3_iff _ _ _ _).1 hm.1
  have hconst : (∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b) := by
    by_contra hnc
    apply hS.2
    rw [admits_iff]
    exact ⟨∀ i, H i, inferInstance, σ, γ, φ, hemb, hnc⟩
  have key : ∀ {W : Type} (f : W → ∀ i, H i), (∀ a b, f a = f b) → Function.Surjective f →
      Subsingleton (∀ i, H i) := by
    intro W f hf hs
    refine ⟨fun g h => ?_⟩
    obtain ⟨a, rfl⟩ := hs g
    obtain ⟨b, rfl⟩ := hs h
    exact hf a b
  rcases hsat with h | h | h
  · exact key σ hconst.1 h
  · exact key γ hconst.2.1 h
  · exact key φ hconst.2.2 h

/-! ### L1: slot permutations and relabelling -/

theorem pairwiseConnected3_swapXY_iff (S : Set (X × Y × Z)) :
    PairwiseConnected3 (swapXY S) ↔ PairwiseConnected3 S := by
  rw [pc3_iff_bip, pc3_iff_bip]
  have h1 : (bip (r12 (swapXY S))).Connected ↔ (bip (r12 S)).Connected := by
    rw [conn_bip_congr (R' := fun y x => r12 S x y)
      (fun y x => by simp only [r12, mem_swapXY])]
    exact conn_bip_swap _
  have h2 : (bip (r13 (swapXY S))).Connected ↔ (bip (r23 S)).Connected :=
    conn_bip_congr fun y z => by simp only [r13, r23, mem_swapXY]
  have h3 : (bip (r23 (swapXY S))).Connected ↔ (bip (r13 S)).Connected :=
    conn_bip_congr fun x z => by simp only [r13, r23, mem_swapXY]
  rw [h1, h2, h3]
  tauto

theorem pairwiseConnected3_swapYZ_iff (S : Set (X × Y × Z)) :
    PairwiseConnected3 (swapYZ S) ↔ PairwiseConnected3 S := by
  rw [pc3_iff_bip, pc3_iff_bip]
  have h1 : (bip (r12 (swapYZ S))).Connected ↔ (bip (r13 S)).Connected :=
    conn_bip_congr fun x z => by simp only [r12, r13, mem_swapYZ]
  have h2 : (bip (r13 (swapYZ S))).Connected ↔ (bip (r12 S)).Connected :=
    conn_bip_congr fun x y => by simp only [r12, r13, mem_swapYZ]
  have h3 : (bip (r23 (swapYZ S))).Connected ↔ (bip (r23 S)).Connected := by
    rw [conn_bip_congr (R' := fun z y => r23 S y z)
      (fun z y => by simp only [r23, mem_swapYZ])]
    exact conn_bip_swap _
  rw [h1, h2, h3]
  tauto

private theorem pairwiseConnected3_swapXZ_iff (S : Set (X × Y × Z)) :
    PairwiseConnected3 (swapXZ S) ↔ PairwiseConnected3 S := by
  rw [pc3_iff_bip, pc3_iff_bip]
  have h1 : (bip (r12 (swapXZ S))).Connected ↔ (bip (r23 S)).Connected := by
    rw [conn_bip_congr (R' := fun z y => r23 S y z)
      (fun z y => by simp only [r12, r23, mem_swapXZ])]
    exact conn_bip_swap _
  have h2 : (bip (r13 (swapXZ S))).Connected ↔ (bip (r13 S)).Connected := by
    rw [conn_bip_congr (R' := fun z x => r13 S x z)
      (fun z x => by simp only [r13, mem_swapXZ])]
    exact conn_bip_swap _
  have h3 : (bip (r23 (swapXZ S))).Connected ↔ (bip (r12 S)).Connected := by
    rw [conn_bip_congr (R' := fun y x => r12 S x y)
      (fun y x => by simp only [r12, r23, mem_swapXZ])]
    exact conn_bip_swap _
  rw [h1, h2, h3]
  tauto

theorem pairwiseConnected3_relabelSet_iff {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y')
    (eZ : Z ≃ Z') (S : Set (X × Y × Z)) :
    PairwiseConnected3 (relabelSet eX eY eZ S) ↔ PairwiseConnected3 S := by
  rw [pc3_iff_bip, pc3_iff_bip]
  have h1 : (bip (r12 (relabelSet eX eY eZ S))).Connected ↔ (bip (r12 S)).Connected := by
    refine conn_bip_equiv eX eY fun x y => ?_
    simp only [r12]
    constructor
    · rintro ⟨z', hz'⟩
      obtain ⟨z, rfl⟩ := eZ.surjective z'
      exact ⟨z, mem_relabelSet.1 hz'⟩
    · rintro ⟨z, hz⟩
      exact ⟨eZ z, mem_relabelSet.2 hz⟩
  have h2 : (bip (r13 (relabelSet eX eY eZ S))).Connected ↔ (bip (r13 S)).Connected := by
    refine conn_bip_equiv eX eZ fun x z => ?_
    simp only [r13]
    constructor
    · rintro ⟨y', hy'⟩
      obtain ⟨y, rfl⟩ := eY.surjective y'
      exact ⟨y, mem_relabelSet.1 hy'⟩
    · rintro ⟨y, hy⟩
      exact ⟨eY y, mem_relabelSet.2 hy⟩
  have h3 : (bip (r23 (relabelSet eX eY eZ S))).Connected ↔ (bip (r23 S)).Connected := by
    refine conn_bip_equiv eY eZ fun y z => ?_
    simp only [r23]
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := eX.surjective x'
      exact ⟨x, mem_relabelSet.1 hx'⟩
    · rintro ⟨x, hx⟩
      exact ⟨eX x, mem_relabelSet.2 hx⟩
  rw [h1, h2, h3]

theorem admitsAbelianEmbedding3_swapXY_iff (S : Set (X × Y × Z)) :
    AdmitsAbelianEmbedding3 (swapXY S) ↔ AdmitsAbelianEmbedding3 S := by
  rw [admits_iff, admits_iff]
  constructor
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, γ, σ, φ, fun p hp => ?_, ?_⟩
    · have := he (p.2.1, p.1, p.2.2) (mem_swapXY.2 hp)
      simp only at this ⊢
      rw [add_comm (γ p.1)]
      exact this
    · rintro ⟨h1, h2, h3⟩
      exact hn ⟨h2, h1, h3⟩
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, γ, σ, φ, ?_, ?_⟩
    · rintro ⟨y, x, z⟩ hp
      have := he (x, y, z) (mem_swapXY.1 hp)
      simp only at this ⊢
      rw [add_comm (γ y)]
      exact this
    · rintro ⟨h1, h2, h3⟩
      exact hn ⟨h2, h1, h3⟩

theorem admitsAbelianEmbedding3_swapYZ_iff (S : Set (X × Y × Z)) :
    AdmitsAbelianEmbedding3 (swapYZ S) ↔ AdmitsAbelianEmbedding3 S := by
  rw [admits_iff, admits_iff]
  constructor
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, σ, φ, γ, fun p hp => ?_, ?_⟩
    · have := he (p.1, p.2.2, p.2.1) (mem_swapYZ.2 hp)
      simp only at this ⊢
      rw [add_right_comm]
      exact this
    · rintro ⟨h1, h2, h3⟩
      exact hn ⟨h1, h3, h2⟩
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, σ, φ, γ, ?_, ?_⟩
    · rintro ⟨x, z, y⟩ hp
      have := he (x, y, z) (mem_swapYZ.1 hp)
      simp only at this ⊢
      rw [add_right_comm]
      exact this
    · rintro ⟨h1, h2, h3⟩
      exact hn ⟨h1, h3, h2⟩

private theorem admitsAbelianEmbedding3_swapXZ_iff (S : Set (X × Y × Z)) :
    AdmitsAbelianEmbedding3 (swapXZ S) ↔ AdmitsAbelianEmbedding3 S := by
  rw [admits_iff, admits_iff]
  constructor
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, φ, γ, σ, fun p hp => ?_, ?_⟩
    · have := he (p.2.2, p.2.1, p.1) (mem_swapXZ.2 hp)
      simp only at this ⊢
      exact Eq.trans (by abel) this
    · rintro ⟨h1, h2, h3⟩
      exact hn ⟨h3, h2, h1⟩
  · rintro ⟨G, inst, σ, γ, φ, he, hn⟩
    refine ⟨G, inst, φ, γ, σ, ?_, ?_⟩
    · rintro ⟨z, y, x⟩ hp
      have := he (x, y, z) (mem_swapXZ.1 hp)
      simp only at this ⊢
      exact Eq.trans (by abel) this
    · rintro ⟨h1, h2, h3⟩
      exact hn ⟨h3, h2, h1⟩

theorem admitsAbelianEmbedding3_relabelSet_iff {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y')
    (eZ : Z ≃ Z') (S : Set (X × Y × Z)) :
    AdmitsAbelianEmbedding3 (relabelSet eX eY eZ S) ↔ AdmitsAbelianEmbedding3 S := by
  constructor
  · rintro ⟨G, inst, h⟩
    exact ⟨G, inst, (admitsEmbeddingInto3_map_iff eX eY eZ S G).1 h⟩
  · rintro ⟨G, inst, h⟩
    exact ⟨G, inst, (admitsEmbeddingInto3_map_iff eX eY eZ S G).2 h⟩

theorem inT_swapXY_iff (S : Set (X × Y × Z)) : InT (swapXY S) ↔ InT S := by
  unfold InT
  rw [pairwiseConnected3_swapXY_iff, admitsAbelianEmbedding3_swapXY_iff]

theorem inT_swapYZ_iff (S : Set (X × Y × Z)) : InT (swapYZ S) ↔ InT S := by
  unfold InT
  rw [pairwiseConnected3_swapYZ_iff, admitsAbelianEmbedding3_swapYZ_iff]

theorem inT_swapXZ_iff (S : Set (X × Y × Z)) : InT (swapXZ S) ↔ InT S := by
  unfold InT
  rw [pairwiseConnected3_swapXZ_iff, admitsAbelianEmbedding3_swapXZ_iff]

theorem inT_relabelSet_iff {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (S : Set (X × Y × Z)) : InT (relabelSet eX eY eZ S) ↔ InT S := by
  unfold InT
  rw [pairwiseConnected3_relabelSet_iff, admitsAbelianEmbedding3_relabelSet_iff]

theorem fullyMergedSet_swapXY_iff (S : Set (X × Y × Z)) :
    FullyMergedSet (swapXY S) ↔ FullyMergedSet S := by
  unfold FullyMergedSet mergeImpliesX mergeImpliesY mergeImpliesZ
  simp only [mem_swapXY]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun y z x x' hx hx' => h2 y z x x' hx hx', fun x z y y' hy hy' => h1 x z y y' hy hy',
      fun x y z z' hz hz' => h3 y x z z' hz hz'⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun y z x x' hx hx' => h2 y z x x' hx hx', fun x z y y' hy hy' => h1 x z y y' hy hy',
      fun x y z z' hz hz' => h3 y x z z' hz hz'⟩

theorem fullyMergedSet_swapYZ_iff (S : Set (X × Y × Z)) :
    FullyMergedSet (swapYZ S) ↔ FullyMergedSet S := by
  unfold FullyMergedSet mergeImpliesX mergeImpliesY mergeImpliesZ
  simp only [mem_swapYZ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun y z x x' hx hx' => h1 z y x x' hx hx', fun x y z z' hz hz' => h3 x y z z' hz hz',
      fun x z y y' hy hy' => h2 x z y y' hy hy'⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun y z x x' hx hx' => h1 z y x x' hx hx', fun x y z z' hz hz' => h3 x y z z' hz hz',
      fun x z y y' hy hy' => h2 x z y y' hy hy'⟩

theorem fullyMergedSet_relabelSet_iff {X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y')
    (eZ : Z ≃ Z') (S : Set (X × Y × Z)) :
    FullyMergedSet (relabelSet eX eY eZ S) ↔ FullyMergedSet S := by
  unfold FullyMergedSet mergeImpliesX mergeImpliesY mergeImpliesZ
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun y z x x' hx hx' => eX.injective (h1 (eY y) (eZ z) (eX x) (eX x')
      (mem_relabelSet.2 hx) (mem_relabelSet.2 hx')), fun x z y y' hy hy' => eY.injective
      (h2 (eX x) (eZ z) (eY y) (eY y') (mem_relabelSet.2 hy) (mem_relabelSet.2 hy')),
      fun x y z z' hz hz' => eZ.injective (h3 (eX x) (eY y) (eZ z) (eZ z')
      (mem_relabelSet.2 hz) (mem_relabelSet.2 hz'))⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun y z x x' hx hx' => ?_, fun x z y y' hy hy' => ?_, fun x y z z' hz hz' => ?_⟩
    · obtain ⟨y0, rfl⟩ := eY.surjective y
      obtain ⟨z0, rfl⟩ := eZ.surjective z
      obtain ⟨x0, rfl⟩ := eX.surjective x
      obtain ⟨x1, rfl⟩ := eX.surjective x'
      rw [h1 y0 z0 x0 x1 (mem_relabelSet.1 hx) (mem_relabelSet.1 hx')]
    · obtain ⟨x0, rfl⟩ := eX.surjective x
      obtain ⟨z0, rfl⟩ := eZ.surjective z
      obtain ⟨y0, rfl⟩ := eY.surjective y
      obtain ⟨y1, rfl⟩ := eY.surjective y'
      rw [h2 x0 z0 y0 y1 (mem_relabelSet.1 hy) (mem_relabelSet.1 hy')]
    · obtain ⟨x0, rfl⟩ := eX.surjective x
      obtain ⟨y0, rfl⟩ := eY.surjective y
      obtain ⟨z0, rfl⟩ := eZ.surjective z
      obtain ⟨z1, rfl⟩ := eZ.surjective z'
      rw [h3 x0 y0 z0 z1 (mem_relabelSet.1 hz) (mem_relabelSet.1 hz')]

/-! ### L7: Fact F and `cor:hole-empty` -/

section Sizes
variable [Fintype X] [Fintype Y] [Fintype Z]

theorem sizes_of_fullyMerged_Y {S : Set (X × Y × Z)} (hc : PairwiseConnected3 S)
    (hm : FullyMergedSet S) (h : Fintype.card Y = 1) : Fintype.card X = 1 ∧ Fintype.card Z = 1 := by
  obtain ⟨hX, hY, hZ⟩ := hm
  obtain ⟨y0, hy⟩ := Fintype.card_eq_one_iff.mp h
  have hXex : ∀ z, ∃ x, (x, y0, z) ∈ S := fun z => by
    obtain ⟨x, y, hxy⟩ := MaxT.PairwiseConnected3.exists_atom_z hc z
    rw [hy y] at hxy
    exact ⟨x, hxy⟩
  have hZex : ∀ x, ∃ z, (x, y0, z) ∈ S := fun x => by
    obtain ⟨y, z, hxy⟩ := MaxT.PairwiseConnected3.exists_atom_x hc x
    rw [hy y] at hxy
    exact ⟨z, hxy⟩
  have h13 := ((pc3_iff_bip S).1 hc).2.1
  have walk : ∀ {W : Type} (f : X ⊕ Z → W), (∀ u v, (bip (r13 S)).Adj u v → f u = f v) →
      ∀ u v, f u = f v := by
    intro W f hf u v
    obtain ⟨p⟩ := h13.preconnected u v
    induction p with
    | nil => rfl
    | cons hadj _ ih => exact (hf _ _ hadj).trans ih
  let f : X ⊕ Z → X := Sum.elim id fun z => (hXex z).choose
  let g : X ⊕ Z → Z := Sum.elim (fun x => (hZex x).choose) id
  have hf : ∀ u v, (bip (r13 S)).Adj u v → f u = f v := by
    intro u v huv
    simp only [bip, SimpleGraph.fromRel_adj] at huv
    obtain ⟨_, ⟨a, b, ⟨y, hyS⟩, h1, h2⟩ | ⟨a, b, ⟨y, hyS⟩, h1, h2⟩⟩ := huv
    · subst h1; subst h2
      rw [hy y] at hyS
      exact (hX y0 b _ _ (hXex b).choose_spec hyS).symm
    · subst h1; subst h2
      rw [hy y] at hyS
      exact hX y0 b _ _ (hXex b).choose_spec hyS
  have hg : ∀ u v, (bip (r13 S)).Adj u v → g u = g v := by
    intro u v huv
    simp only [bip, SimpleGraph.fromRel_adj] at huv
    obtain ⟨_, ⟨a, b, ⟨y, hyS⟩, h1, h2⟩ | ⟨a, b, ⟨y, hyS⟩, h1, h2⟩⟩ := huv
    · subst h1; subst h2
      rw [hy y] at hyS
      exact hZ a y0 _ _ (hZex a).choose_spec hyS
    · subst h1; subst h2
      rw [hy y] at hyS
      exact (hZ a y0 _ _ (hZex a).choose_spec hyS).symm
  obtain ⟨⟨x0⟩, _, ⟨z0⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hc
  refine ⟨Fintype.card_eq_one_iff.2 ⟨x0, fun x => ?_⟩,
    Fintype.card_eq_one_iff.2 ⟨z0, fun z => ?_⟩⟩
  · exact walk f hf (Sum.inl x) (Sum.inl x0)
  · exact walk g hg (Sum.inr z) (Sum.inr z0)

theorem sizes_of_fullyMerged_X {S : Set (X × Y × Z)} (hc : PairwiseConnected3 S)
    (hm : FullyMergedSet S) (h : Fintype.card X = 1) : Fintype.card Y = 1 ∧ Fintype.card Z = 1 :=
  sizes_of_fullyMerged_Y (S := swapXY S) ((pairwiseConnected3_swapXY_iff S).2 hc)
    ((fullyMergedSet_swapXY_iff S).2 hm) h

theorem sizes_of_fullyMerged_Z {S : Set (X × Y × Z)} (hc : PairwiseConnected3 S)
    (hm : FullyMergedSet S) (h : Fintype.card Z = 1) : Fintype.card X = 1 ∧ Fintype.card Y = 1 :=
  sizes_of_fullyMerged_Y (S := swapYZ S) ((pairwiseConnected3_swapYZ_iff S).2 hc)
    ((fullyMergedSet_swapYZ_iff S).2 hm) h

/-- Supplement E `cor:hole-empty`: a fully merged member of `𝒯` is a single atom or has all alphabets of
size `≥ 2`; in particular `|Γ| = |Φ| = 1 < |Σ|` never occurs. -/
theorem inT_fullyMerged_dichotomy {S : Set (X × Y × Z)} (hS : InT S) (hm : FullyMergedSet S) :
    (Fintype.card X = 1 ∧ Fintype.card Y = 1 ∧ Fintype.card Z = 1 ∧ S = Set.univ) ∨
      (2 ≤ Fintype.card X ∧ 2 ≤ Fintype.card Y ∧ 2 ≤ Fintype.card Z) := by
  obtain ⟨⟨x0⟩, ⟨y0⟩, ⟨z0⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hS.1
  haveI : Nonempty X := ⟨x0⟩
  haveI : Nonempty Y := ⟨y0⟩
  haveI : Nonempty Z := ⟨z0⟩
  have px : 0 < Fintype.card X := Fintype.card_pos
  have py : 0 < Fintype.card Y := Fintype.card_pos
  have pz : 0 < Fintype.card Z := Fintype.card_pos
  by_cases hx : Fintype.card X = 1
  · obtain ⟨hy, hz⟩ := sizes_of_fullyMerged_X hS.1 hm hx
    left
    obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hx
    obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hy
    obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hz
    exact ⟨hx, hy, hz, eq_univ_of_pairwiseConnected_unique hS.1⟩
  · right
    have hy : Fintype.card Y ≠ 1 := fun hy => hx (sizes_of_fullyMerged_Y hS.1 hm hy).1
    have hz : Fintype.card Z ≠ 1 := fun hz => hx (sizes_of_fullyMerged_Z hS.1 hm hz).1
    omega

theorem inT_fullyMerged_not_hole {S : Set (X × Y × Z)} (hS : InT S) (hm : FullyMergedSet S) :
    ¬ (Fintype.card Y = 1 ∧ Fintype.card Z = 1 ∧ 1 < Fintype.card X) := by
  rintro ⟨hy, _, hx⟩
  have := (sizes_of_fullyMerged_Y hS.1 hm hy).1
  omega

end Sizes
end Class
end MaxT
end TrackB
end RestrictedPolynomials
end
