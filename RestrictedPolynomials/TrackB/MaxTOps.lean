module

public import RestrictedPolynomials.TrackB.MaxTClass
public import RestrictedPolynomials.TrackB.MergeLayer
public import RestrictedPolynomials.TrackB.PathTrickEmbedding
public import RestrictedPolynomials.Defs

/-!
# Track B: operations on the class `𝒯` (Supplement E)

Supplement E items: `def:merge`, `lem:T-merge`, `lem:T-full-merge` (one genuine step),
`def:path`, `lem:T-path`, `lem:T-construction`, `lem:dup-trivial`,
`cor:Gamma-prime`, and paper IV `thm:nonembed-deg-must-be-small-rephrase-maximal2`, step `construction-of-nu`
(steps 1-3, 5).

Readings: the merged alphabet is `↥(Set.range a)`; `ν` is built without duplication (`nuOf`);
the `z`- and `y`-path tricks are swap conjugates; the forward merge direction holds for
every map, while the converse needs a representative map.
`inT_construction` carries the property-6c conjunct, and
`nuOf_marginal_yz` and `nuOf_atom_ge` carry no `hyz` (`nuOf_support` keeps it).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Ops
variable {X Y Z : Type}

/-! ### L3: merges at the level of supports -/

/-- the `x`-merged support: `t` with `t_x` replaced by `a(t_x)` (paper IV `def:merge` / Supplement E `def:merge`). -/
def mergeSetX (S : Set (X × Y × Z)) (a : X → X) : Set (↥(Set.range a) × Y × Z) :=
  (fun p => (⟨a p.1, Set.mem_range_self _⟩, p.2.1, p.2.2)) '' S

/-- the `y`-merged support. -/
def mergeSetY (S : Set (X × Y × Z)) (b : Y → Y) : Set (X × ↥(Set.range b) × Z) :=
  (fun p => (p.1, ⟨b p.2.1, Set.mem_range_self _⟩, p.2.2)) '' S

/-- the `z`-merged support. -/
def mergeSetZ (S : Set (X × Y × Z)) (c : Z → Z) : Set (X × Y × ↥(Set.range c)) :=
  (fun p => (p.1, p.2.1, ⟨c p.2.2, Set.mem_range_self _⟩)) '' S

/-! ### private helpers: membership, bipartite graphs, lifting of connectedness -/

private theorem mem_mergeSetX {S : Set (X × Y × Z)} {a : X → X} {x' : ↥(Set.range a)} {y : Y}
    {z : Z} : (x', y, z) ∈ mergeSetX S a ↔ ∃ x, a x = x'.1 ∧ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x, y₀, z₀⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, rfl, rfl⟩ := he
    exact ⟨x, congrArg Subtype.val h1, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨(x, y, z), h, Prod.ext (Subtype.ext hx) rfl⟩

private theorem mem_mergeSetY {S : Set (X × Y × Z)} {b : Y → Y} {x : X} {y' : ↥(Set.range b)}
    {z : Z} : (x, y', z) ∈ mergeSetY S b ↔ ∃ y, b y = y'.1 ∧ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x₀, y, z₀⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, h1, rfl⟩ := he
    exact ⟨y, congrArg Subtype.val h1, h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨(x, y, z), h, Prod.ext rfl (Prod.ext (Subtype.ext hy) rfl)⟩

private theorem mem_mergeSetZ {S : Set (X × Y × Z)} {c : Z → Z} {x : X} {y : Y}
    {z' : ↥(Set.range c)} : (x, y, z') ∈ mergeSetZ S c ↔ ∃ z, c z = z'.1 ∧ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x₀, y₀, z⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, h1⟩ := he
    exact ⟨z, congrArg Subtype.val h1, h⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨(x, y, z), h, Prod.ext rfl (Prod.ext rfl (Subtype.ext hz))⟩

private theorem mem_swapXY' {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (y, x, z) ∈ swapXY S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

private theorem mem_swapXZ' {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (z, y, x) ∈ swapXZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

private theorem swapXY_mergeSetY (S : Set (X × Y × Z)) (b : Y → Y) :
    swapXY (mergeSetY S b) = mergeSetX (swapXY S) b := by
  ext ⟨u, x, z⟩
  rw [mem_swapXY', mem_mergeSetY, mem_mergeSetX]
  simp only [mem_swapXY']

private theorem swapXZ_mergeSetZ (S : Set (X × Y × Z)) (c : Z → Z) :
    swapXZ (mergeSetZ S c) = mergeSetX (swapXZ S) c := by
  ext ⟨u, y, x⟩
  rw [mem_swapXZ', mem_mergeSetZ, mem_mergeSetX]
  simp only [mem_swapXZ']

private theorem mergeGraphX_swapXY (S : Set (X × Y × Z)) :
    mergeGraphX (swapXY S) = mergeGraphY S := by
  ext u v
  simp only [mergeGraphX, mergeGraphY, SimpleGraph.fromRel_adj]
  refine and_congr Iff.rfl (or_congr ?_ ?_) <;>
  · constructor
    · rintro ⟨y, z, h1, h2⟩
      exact ⟨y, z, mem_swapXY'.1 h1, mem_swapXY'.1 h2⟩
    · rintro ⟨y, z, h1, h2⟩
      exact ⟨y, z, mem_swapXY'.2 h1, mem_swapXY'.2 h2⟩

private theorem mergeGraphX_swapXZ (S : Set (X × Y × Z)) :
    mergeGraphX (swapXZ S) = mergeGraphZ S := by
  ext u v
  simp only [mergeGraphX, mergeGraphZ, SimpleGraph.fromRel_adj]
  refine and_congr Iff.rfl (or_congr ?_ ?_) <;>
  · constructor
    · rintro ⟨y, z, h1, h2⟩
      exact ⟨z, y, mem_swapXZ'.1 h1, mem_swapXZ'.1 h2⟩
    · rintro ⟨y, z, h1, h2⟩
      exact ⟨z, y, mem_swapXZ'.2 h1, mem_swapXZ'.2 h2⟩

private theorem mergeImpliesX_swapXY (S : Set (X × Y × Z)) :
    mergeImpliesX (swapXY S) ↔ mergeImpliesY S := by
  constructor
  · intro h x z y y' h1 h2
    exact h x z y y' (mem_swapXY'.2 h1) (mem_swapXY'.2 h2)
  · intro h x z y y' h1 h2
    exact h x z y y' (mem_swapXY'.1 h1) (mem_swapXY'.1 h2)

private theorem mergeImpliesX_swapXZ (S : Set (X × Y × Z)) :
    mergeImpliesX (swapXZ S) ↔ mergeImpliesZ S := by
  constructor
  · intro h x y z z' h1 h2
    exact h y x z z' (mem_swapXZ'.2 h1) (mem_swapXZ'.2 h2)
  · intro h y x z z' h1 h2
    exact h x y z z' (mem_swapXZ'.1 h1) (mem_swapXZ'.1 h2)

/-- the bipartite graph of a relation. -/
private def bipG {A B : Type} (R : A → B → Prop) : SimpleGraph (A ⊕ B) :=
  SimpleGraph.fromRel fun u v => ∃ a b, R a b ∧ u = Sum.inl a ∧ v = Sum.inr b

private theorem bipG_adj_lr {A B : Type} {R : A → B → Prop} {a : A} {b : B} :
    (bipG R).Adj (Sum.inl a) (Sum.inr b) ↔ R a b := by
  simp only [bipG, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨a', b', h, h1, h2⟩ | ⟨a', b', h, h1, h2⟩⟩
    · cases h1
      cases h2
      exact h
    · cases h1
  · intro h
    exact ⟨by simp, Or.inl ⟨a, b, h, rfl, rfl⟩⟩

private theorem bipG_adj_rl {A B : Type} {R : A → B → Prop} {a : A} {b : B} :
    (bipG R).Adj (Sum.inr b) (Sum.inl a) ↔ R a b := by
  rw [SimpleGraph.adj_comm, bipG_adj_lr]

private theorem bipG_not_adj_ll {A B : Type} {R : A → B → Prop} {a a' : A} :
    ¬ (bipG R).Adj (Sum.inl a) (Sum.inl a') := by
  simp only [bipG, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨a₁, b₁, -, h1, h2⟩ | ⟨a₁, b₁, -, h1, h2⟩⟩ <;> cases h2

private theorem bipG_not_adj_rr {A B : Type} {R : A → B → Prop} {b b' : B} :
    ¬ (bipG R).Adj (Sum.inr b) (Sum.inr b') := by
  simp only [bipG, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨a₁, b₁, -, h1, h2⟩ | ⟨a₁, b₁, -, h1, h2⟩⟩ <;> cases h1

private theorem bipG_map {A A' B : Type} {R : A → B → Prop} {R' : A' → B → Prop} (f : A → A')
    (hf : Function.Surjective f) (hR : ∀ a b, R a b → R' (f a) b) (hc : (bipG R).Connected) :
    (bipG R').Connected := by
  refine SimpleGraph.Connected.map (f := ⟨Sum.map f id, ?_⟩) ?_ hc
  · intro u v h
    rcases u with a | b <;> rcases v with a' | b'
    · exact absurd h bipG_not_adj_ll
    · exact bipG_adj_lr.2 (hR _ _ (bipG_adj_lr.1 h))
    · exact bipG_adj_rl.2 (hR _ _ (bipG_adj_rl.1 h))
    · exact absurd h bipG_not_adj_rr
  · rintro (a' | b)
    · obtain ⟨a, rfl⟩ := hf a'
      exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr b, rfl⟩

private theorem bipG_unmap {A A' B : Type} {R : A → B → Prop} {R' : A' → B → Prop} (f : A → A')
    (hf : Function.Surjective f)
    (hfib : ∀ a a', f a = f a' → (bipG R).Reachable (Sum.inl a) (Sum.inl a'))
    (hR : ∀ a b, R' (f a) b → ∃ a₀, f a₀ = f a ∧ R a₀ b)
    (hc : (bipG R').Connected) : (bipG R).Connected := by
  have key : ∀ (a : A) (b : B), R' (f a) b → (bipG R).Reachable (Sum.inl a) (Sum.inr b) := by
    intro a b h
    obtain ⟨a₀, h1, h2⟩ := hR a b h
    exact (hfib a a₀ h1.symm).trans (SimpleGraph.Adj.reachable (bipG_adj_lr.2 h2))
  have fib : ∀ u v : A ⊕ B, Sum.map f id u = Sum.map f id v → (bipG R).Reachable u v := by
    rintro (a | b) (a' | b') h
    · exact hfib a a' (Sum.inl.inj h)
    · cases h
    · cases h
    · have : b = b' := Sum.inr.inj h
      rw [this]
  have adjl : ∀ u v : A ⊕ B, (bipG R').Adj (Sum.map f id u) (Sum.map f id v) →
      (bipG R).Reachable u v := by
    rintro (a | b) (a' | b') h
    · exact absurd h bipG_not_adj_ll
    · exact key a b' (bipG_adj_lr.1 h)
    · exact (key a' b (bipG_adj_rl.1 h)).symm
    · exact absurd h bipG_not_adj_rr
  have walk : ∀ {s t : A' ⊕ B} (p : (bipG R').Walk s t) (u v : A ⊕ B), Sum.map f id u = s →
      Sum.map f id v = t → (bipG R).Reachable u v := by
    intro s t p
    induction p with
    | nil =>
      intro u v hu hv
      exact fib u v (hu.trans hv.symm)
    | @cons s m t hadj p ih =>
      intro u v hu hv
      have : ∃ m₀ : A ⊕ B, Sum.map f id m₀ = m := by
        rcases m with a' | b
        · obtain ⟨a, rfl⟩ := hf a'
          exact ⟨Sum.inl a, rfl⟩
        · exact ⟨Sum.inr b, rfl⟩
      obtain ⟨m₀, hm₀⟩ := this
      refine (adjl u m₀ ?_).trans (ih m₀ v hm₀ hv)
      rw [hu, hm₀]
      exact hadj
  have hne : Nonempty (A ⊕ B) := by
    obtain ⟨s⟩ := hc.nonempty
    rcases s with a' | b
    · obtain ⟨a, -⟩ := hf a'
      exact ⟨Sum.inl a⟩
    · exact ⟨Sum.inr b⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨p⟩ := hc.preconnected (Sum.map f id u) (Sum.map f id v)
  exact walk p u v rfl rfl

private theorem bipG_congr {A B : Type} {R R' : A → B → Prop} (h : ∀ a b, R a b ↔ R' a b) :
    (bipG R).Connected ↔ (bipG R').Connected := by
  have : R = R' := by
    funext a b
    exact propext (h a b)
  subst this
  exact Iff.rfl

private def rXY (S : Set (X × Y × Z)) (x : X) (y : Y) : Prop := ∃ z, (x, y, z) ∈ S
private def rXZ (S : Set (X × Y × Z)) (x : X) (z : Z) : Prop := ∃ y, (x, y, z) ∈ S
private def rYZ (S : Set (X × Y × Z)) (y : Y) (z : Z) : Prop := ∃ x, (x, y, z) ∈ S

private theorem pc3_iff_bipG (S : Set (X × Y × Z)) :
    PairwiseConnected3 S ↔
      (bipG (rXY S)).Connected ∧ (bipG (rXZ S)).Connected ∧ (bipG (rYZ S)).Connected := by
  rw [pairwiseConnected3_iff]
  have e12 : (SimpleGraph.fromRel fun (a : X ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y) = bipG (rXY S) := by
    unfold bipG
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨x, y, z, h, h1, h2⟩
      exact ⟨x, y, ⟨z, h⟩, h1, h2⟩
    · rintro ⟨x, y, ⟨z, h⟩, h1, h2⟩
      exact ⟨x, y, z, h, h1, h2⟩
  have e13 : (SimpleGraph.fromRel fun (a : X ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z) = bipG (rXZ S) := by
    unfold bipG
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨x, y, z, h, h1, h2⟩
      exact ⟨x, z, ⟨y, h⟩, h1, h2⟩
    · rintro ⟨x, z, ⟨y, h⟩, h1, h2⟩
      exact ⟨x, y, z, h, h1, h2⟩
  have e23 : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z) = bipG (rYZ S) := by
    unfold bipG
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨x, y, z, h, h1, h2⟩
      exact ⟨y, z, ⟨x, h⟩, h1, h2⟩
    · rintro ⟨y, z, ⟨x, h⟩, h1, h2⟩
      exact ⟨x, y, z, h, h1, h2⟩
  rw [e12, e13, e23]


private theorem admitsIff (S : Set (X × Y × Z)) :
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

section MergeLaws
variable [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

private theorem mem_support_mergePush {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (b : β) :
    b ∈ (mergePush π f).support ↔ ∃ a, f a = b ∧ a ∈ π.support := by
  show (∑ a ∈ Finset.univ.filter (fun a => f a = b), π.prob a) ≠ 0 ↔ _
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun a _ => π.nonneg a]
  push Not
  constructor
  · rintro ⟨a, ha, hne⟩
    exact ⟨a, (Finset.mem_filter.1 ha).2, hne⟩
  · rintro ⟨a, hfa, hne⟩
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfa⟩, hne⟩

theorem mergeDistX_support_eq (μ : FinProb (X × Y × Z)) (a : X → X) :
    (mergeDistX μ a).support = mergeSetX μ.support a := by
  ext ⟨x', y, z⟩
  rw [mergeDistX_support, mem_mergeSetX]

theorem mergeDistY_support_eq (μ : FinProb (X × Y × Z)) (b : Y → Y) :
    (mergeDistY μ b).support = mergeSetY μ.support b := by
  ext ⟨x, y', z⟩
  refine (mem_support_mergePush _ _ _).trans ?_
  rw [mem_mergeSetY]
  constructor
  · rintro ⟨⟨x₀, y₀, z₀⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, h1, rfl⟩ := he
    exact ⟨y₀, congrArg Subtype.val h1, h⟩
  · rintro ⟨y₀, hy, h⟩
    exact ⟨(x, y₀, z), Prod.ext rfl (Prod.ext (Subtype.ext hy) rfl), h⟩

theorem mergeDistZ_support_eq (μ : FinProb (X × Y × Z)) (c : Z → Z) :
    (mergeDistZ μ c).support = mergeSetZ μ.support c := by
  ext ⟨x, y, z'⟩
  refine (mem_support_mergePush _ _ _).trans ?_
  rw [mem_mergeSetZ]
  constructor
  · rintro ⟨⟨x₀, y₀, z₀⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, h1⟩ := he
    exact ⟨z₀, congrArg Subtype.val h1, h⟩
  · rintro ⟨z₀, hz, h⟩
    exact ⟨(x, y, z₀), Prod.ext rfl (Prod.ext rfl (Subtype.ext hz)), h⟩

theorem mergeGraphY_components_iff (P : Set (X × Y × Z)) :
    Nat.card (mergeGraphY P).ConnectedComponent = Fintype.card Y ↔ mergeImpliesY P := by
  rw [← mergeGraphX_swapXY, ← mergeImpliesX_swapXY]
  exact mergeGraphX_components_iff (swapXY P)

theorem mergeGraphZ_components_iff (P : Set (X × Y × Z)) :
    Nat.card (mergeGraphZ P).ConnectedComponent = Fintype.card Z ↔ mergeImpliesZ P := by
  rw [← mergeGraphX_swapXZ, ← mergeImpliesX_swapXZ]
  exact mergeGraphX_components_iff (swapXZ P)

end MergeLaws

private theorem sigma_eq_of_reachable {G : Type} [AddCommGroup G] {S : Set (X × Y × Z)}
    {σ : X → G} {γ : Y → G} {φ : Z → G} (he : ∀ p ∈ S, σ p.1 + γ p.2.1 + φ p.2.2 = 0)
    {x x' : X} (h : (mergeGraphX S).Reachable x x') : σ x = σ x' := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons u v w hadj _ ih =>
    refine Eq.trans ?_ ih
    simp only [mergeGraphX, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨y, z, h1, h2⟩ | ⟨y, z, h1, h2⟩⟩ := hadj
    · have e1 : σ u + γ y + φ z = 0 := he _ h1
      have e2 : σ v + γ y + φ z = 0 := he _ h2
      exact add_right_cancel (add_right_cancel (e1.trans e2.symm))
    · have e1 : σ v + γ y + φ z = 0 := he _ h1
      have e2 : σ u + γ y + φ z = 0 := he _ h2
      exact add_right_cancel (add_right_cancel (e2.trans e1.symm))

private theorem exists_nonInj_rep {V : Type} [Finite V] (G : SimpleGraph V)
    (h : Nat.card G.ConnectedComponent ≠ Nat.card V) :
    ∃ a : V → V, MergeRep G a ∧ ¬ Function.Injective a := by
  obtain ⟨a, ha⟩ := exists_mergeRep G
  refine ⟨a, ha, fun hinj => h ?_⟩
  have hsurj : Function.Surjective G.connectedComponentMk := fun c => c.ind (fun v => ⟨v, rfl⟩)
  have hi : Function.Injective G.connectedComponentMk := fun v w hvw =>
    hinj (ha.2 v w (SimpleGraph.ConnectedComponent.exact hvw))
  exact (Nat.card_eq_of_bijective _ ⟨hi, hsurj⟩).symm

private theorem reach_bipG_xy {S : Set (X × Y × Z)} {x x' : X}
    (h : (mergeGraphX S).Reachable x x') : (bipG (rXY S)).Reachable (Sum.inl x) (Sum.inl x') := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj _ ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    simp only [mergeGraphX, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨y, z, h1, h2⟩ | ⟨y, z, h1, h2⟩⟩ := hadj
    · exact (SimpleGraph.Adj.reachable (bipG_adj_lr.2 ⟨z, h1⟩)).trans
        (SimpleGraph.Adj.reachable (bipG_adj_rl.2 ⟨z, h2⟩))
    · exact (SimpleGraph.Adj.reachable (bipG_adj_lr.2 ⟨z, h2⟩)).trans
        (SimpleGraph.Adj.reachable (bipG_adj_rl.2 ⟨z, h1⟩))

private theorem reach_bipG_xz {S : Set (X × Y × Z)} {x x' : X}
    (h : (mergeGraphX S).Reachable x x') : (bipG (rXZ S)).Reachable (Sum.inl x) (Sum.inl x') := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj _ ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    simp only [mergeGraphX, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨y, z, h1, h2⟩ | ⟨y, z, h1, h2⟩⟩ := hadj
    · exact (SimpleGraph.Adj.reachable (bipG_adj_lr.2 ⟨y, h1⟩)).trans
        (SimpleGraph.Adj.reachable (bipG_adj_rl.2 ⟨y, h2⟩))
    · exact (SimpleGraph.Adj.reachable (bipG_adj_lr.2 ⟨y, h2⟩)).trans
        (SimpleGraph.Adj.reachable (bipG_adj_rl.2 ⟨y, h1⟩))

/-- Supplement E `lem:T-merge` (1): the merge of a member of `𝒯` is in `𝒯`, for every `a` (forward direction). -/
theorem inT_mergeSetX {S : Set (X × Y × Z)} (hS : InT S) (a : X → X) : InT (mergeSetX S a) := by
  obtain ⟨hc, hn⟩ := hS
  refine ⟨?_, ?_⟩
  · rw [pc3_iff_bipG] at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    have hs : Function.Surjective
        (fun x : X => (⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a))) :=
      fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩
    refine ⟨bipG_map _ hs ?_ h1, bipG_map _ hs ?_ h2, (bipG_congr ?_).1 h3⟩
    · rintro x y ⟨z, hz⟩
      exact ⟨z, mem_mergeSetX.2 ⟨x, rfl, hz⟩⟩
    · rintro x z ⟨y, hy⟩
      exact ⟨y, mem_mergeSetX.2 ⟨x, rfl, hy⟩⟩
    · intro y z
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨⟨a x, Set.mem_range_self _⟩, mem_mergeSetX.2 ⟨x, rfl, hx⟩⟩
      · rintro ⟨x', hx'⟩
        obtain ⟨x, -, hx⟩ := mem_mergeSetX.1 hx'
        exact ⟨x, hx⟩
  · intro hA
    apply hn
    rw [admitsIff] at hA ⊢
    obtain ⟨G, inst, σ, γ, φ, he, hnt⟩ := hA
    refine ⟨G, inst, fun x => σ ⟨a x, Set.mem_range_self _⟩, γ, φ, fun p hp => ?_, ?_⟩
    · exact he (⟨a p.1, Set.mem_range_self _⟩, p.2.1, p.2.2) (mem_mergeSetX.2 ⟨p.1, rfl, hp⟩)
    · rintro ⟨h0, h1, h2⟩
      apply hnt
      refine ⟨?_, h1, h2⟩
      rintro ⟨u, x, hx⟩ ⟨v, x', hx'⟩
      subst hx
      subst hx'
      exact h0 x x'

theorem inT_mergeSetY {S : Set (X × Y × Z)} (hS : InT S) (b : Y → Y) : InT (mergeSetY S b) := by
  refine (inT_swapXY_iff _).1 ?_
  rw [swapXY_mergeSetY]
  exact inT_mergeSetX ((inT_swapXY_iff S).2 hS) b

theorem inT_mergeSetZ {S : Set (X × Y × Z)} (hS : InT S) (c : Z → Z) : InT (mergeSetZ S c) := by
  refine (inT_swapXZ_iff _).1 ?_
  rw [swapXZ_mergeSetZ]
  exact inT_mergeSetX ((inT_swapXZ_iff S).2 hS) c

/-- Supplement E `lem:T-merge` (2): the converse, for a representative map of the merge graph. -/
theorem inT_mergeSetX_iff (S : Set (X × Y × Z)) (a : X → X) (ha : MergeRep (mergeGraphX S) a) :
    InT (mergeSetX S a) ↔ InT S := by
  refine ⟨fun h' => ?_, fun h => inT_mergeSetX h a⟩
  have hfib : ∀ x x', a x = a x' → (mergeGraphX S).Reachable x x' := fun x x' h =>
    (ha.1 x).trans (by rw [h]; exact (ha.1 x').symm)
  have hs : Function.Surjective
      (fun x : X => (⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a))) :=
    fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩
  obtain ⟨hc, hn⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [pc3_iff_bipG] at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨bipG_unmap _ hs (fun x x' h => reach_bipG_xy (hfib x x' (congrArg Subtype.val h)))
      ?_ h1, bipG_unmap _ hs (fun x x' h => reach_bipG_xz (hfib x x' (congrArg Subtype.val h)))
      ?_ h2, (bipG_congr ?_).2 h3⟩
    · rintro x y ⟨z, hz⟩
      obtain ⟨x₀, hx₀, h⟩ := mem_mergeSetX.1 hz
      exact ⟨x₀, Subtype.ext hx₀, z, h⟩
    · rintro x z ⟨y, hy⟩
      obtain ⟨x₀, hx₀, h⟩ := mem_mergeSetX.1 hy
      exact ⟨x₀, Subtype.ext hx₀, y, h⟩
    · intro y z
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨⟨a x, Set.mem_range_self _⟩, mem_mergeSetX.2 ⟨x, rfl, hx⟩⟩
      · rintro ⟨x', hx'⟩
        obtain ⟨x, -, hx⟩ := mem_mergeSetX.1 hx'
        exact ⟨x, hx⟩
  · intro hA
    apply hn
    rw [admitsIff] at hA ⊢
    obtain ⟨G, inst, σ, γ, φ, he, hnt⟩ := hA
    have hσ : ∀ x, σ (a x) = σ x := fun x => (sigma_eq_of_reachable he (ha.1 x)).symm
    refine ⟨G, inst, fun u => σ u.1, γ, φ, fun p hp => ?_, ?_⟩
    · obtain ⟨⟨u, hu⟩, y, z⟩ := p
      obtain ⟨x, hx, h⟩ := mem_mergeSetX.1 hp
      have e : σ x + γ y + φ z = 0 := he (x, y, z) h
      show σ u + γ y + φ z = 0
      have hx' : a x = u := hx
      rw [← hx', hσ]
      exact e
    · rintro ⟨h0, h1, h2⟩
      apply hnt
      refine ⟨fun x x' => ?_, h1, h2⟩
      rw [← hσ x, ← hσ x']
      exact h0 ⟨a x, Set.mem_range_self _⟩ ⟨a x', Set.mem_range_self _⟩

theorem inT_mergeSetY_iff (S : Set (X × Y × Z)) (b : Y → Y) (hb : MergeRep (mergeGraphY S) b) :
    InT (mergeSetY S b) ↔ InT S := by
  rw [← inT_swapXY_iff (mergeSetY S b), swapXY_mergeSetY, ← inT_swapXY_iff S]
  have hb' : MergeRep (mergeGraphX (swapXY S)) b := by
    rw [mergeGraphX_swapXY]
    exact hb
  exact inT_mergeSetX_iff (swapXY S) b hb'

theorem inT_mergeSetZ_iff (S : Set (X × Y × Z)) (c : Z → Z) (hc : MergeRep (mergeGraphZ S) c) :
    InT (mergeSetZ S c) ↔ InT S := by
  rw [← inT_swapXZ_iff (mergeSetZ S c), swapXZ_mergeSetZ, ← inT_swapXZ_iff S]
  have hc' : MergeRep (mergeGraphX (swapXZ S)) c := by
    rw [mergeGraphX_swapXZ]
    exact hc
  exact inT_mergeSetX_iff (swapXZ S) c hc'

/-- the `y`-merged support has `x, z ⇒ y`, the `z`-merged one `x, y ⇒ z` (cf. `mergeDistX_impliesX`). -/
theorem mergeSetY_impliesY (S : Set (X × Y × Z)) (b : Y → Y) (hb : MergeRep (mergeGraphY S) b) :
    mergeImpliesY (mergeSetY S b) := by
  intro x z y₁ y₂ h₁ h₂
  obtain ⟨u₁, hu₁, hs₁⟩ := mem_mergeSetY.1 h₁
  obtain ⟨u₂, hu₂, hs₂⟩ := mem_mergeSetY.1 h₂
  have hr : (mergeGraphY S).Reachable u₁ u₂ := by
    by_cases h : u₁ = u₂
    · rw [h]
    · refine SimpleGraph.Adj.reachable ?_
      simp only [mergeGraphY, SimpleGraph.fromRel_adj]
      exact ⟨h, Or.inl ⟨x, z, hs₁, hs₂⟩⟩
  exact Subtype.ext (hu₁.symm.trans ((hb.2 u₁ u₂ hr).trans hu₂))

theorem mergeSetZ_impliesZ (S : Set (X × Y × Z)) (c : Z → Z) (hc : MergeRep (mergeGraphZ S) c) :
    mergeImpliesZ (mergeSetZ S c) := by
  intro x y z₁ z₂ h₁ h₂
  obtain ⟨u₁, hu₁, hs₁⟩ := mem_mergeSetZ.1 h₁
  obtain ⟨u₂, hu₂, hs₂⟩ := mem_mergeSetZ.1 h₂
  have hr : (mergeGraphZ S).Reachable u₁ u₂ := by
    by_cases h : u₁ = u₂
    · rw [h]
    · refine SimpleGraph.Adj.reachable ?_
      simp only [mergeGraphZ, SimpleGraph.fromRel_adj]
      exact ⟨h, Or.inl ⟨x, y, hs₁, hs₂⟩⟩
  exact Subtype.ext (hu₁.symm.trans ((hc.2 u₁ u₂ hr).trans hu₂))

/-- a representative map of a graph that has a component with two elements is not injective
(the "genuine merge" of the source). -/
theorem exists_nonInjective_mergeRepX {S : Set (X × Y × Z)} [Fintype X] [Fintype Y] [Fintype Z]
    (h : ¬ mergeImpliesX S) : ∃ a : X → X, MergeRep (mergeGraphX S) a ∧ ¬ Function.Injective a := by
  classical
  refine exists_nonInj_rep _ fun hEq => h ?_
  refine (mergeGraphX_components_iff S).1 ?_
  rw [hEq, Nat.card_eq_fintype_card]

theorem exists_nonInjective_mergeRepY {S : Set (X × Y × Z)} [Fintype X] [Fintype Y] [Fintype Z]
    (h : ¬ mergeImpliesY S) : ∃ b : Y → Y, MergeRep (mergeGraphY S) b ∧ ¬ Function.Injective b := by
  classical
  refine exists_nonInj_rep _ fun hEq => h ?_
  refine (mergeGraphY_components_iff S).1 ?_
  rw [hEq, Nat.card_eq_fintype_card]

theorem exists_nonInjective_mergeRepZ {S : Set (X × Y × Z)} [Fintype X] [Fintype Y] [Fintype Z]
    (h : ¬ mergeImpliesZ S) : ∃ c : Z → Z, MergeRep (mergeGraphZ S) c ∧ ¬ Function.Injective c := by
  classical
  refine exists_nonInj_rep _ fun hEq => h ?_
  refine (mergeGraphZ_components_iff S).1 ?_
  rw [hEq, Nat.card_eq_fintype_card]

theorem card_range_lt_of_not_injective [Fintype X] (a : X → X) (h : ¬ Function.Injective a) :
    Nat.card ↥(Set.range a) < Fintype.card X := by
  have hle : Nat.card ↥(Set.range a) ≤ Nat.card X := mergeDistX_card_le a
  rw [← Nat.card_eq_fintype_card]
  refine lt_of_le_of_ne hle fun heq => h ?_
  have hs : Function.Surjective
      (fun x : X => (⟨a x, Set.mem_range_self _⟩ : ↥(Set.range a))) :=
    fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩
  have hb := hs.bijective_of_nat_card_le heq.ge
  intro x x' hxx
  exact hb.1 (Subtype.ext hxx)

end Ops

/-! ### Path tricks in the `z`- and `y`-slots (Supplement E `def:path`, `lem:T-path`) -/

section PathSlots
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `μ` with the slots `x` and `z` exchanged (a law on `Z × Y × X`). -/
def lawSwapXZ (μ : FinProb (X × Y × Z)) : FinProb (Z × Y × X) :=
  mergePush μ fun p => (p.2.2, p.2.1, p.1)

/-- `μ` with the slots `x` and `y` exchanged (a law on `Y × X × Z`). -/
def lawSwapXY (μ : FinProb (X × Y × Z)) : FinProb (Y × X × Z) :=
  mergePush μ fun p => (p.2.1, p.1, p.2.2)

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem mem_swapYZ' {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (x, z, y) ∈ swapYZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem pc_swapXZ (S : Set (X × Y × Z)) :
    PairwiseConnected3 (swapXZ S) ↔ PairwiseConnected3 S := by
  have e : swapXZ S = swapXY (swapYZ (swapXY S)) := by
    ext ⟨z, y, x⟩
    rw [mem_swapXY', mem_swapYZ', mem_swapXY', mem_swapXZ']
  rw [e, pairwiseConnected3_swapXY_iff, pairwiseConnected3_swapYZ_iff,
    pairwiseConnected3_swapXY_iff]

theorem lawSwapXZ_support (μ : FinProb (X × Y × Z)) : (lawSwapXZ μ).support = swapXZ μ.support := by
  ext ⟨z, y, x⟩
  refine (mem_support_mergePush _ _ _).trans ?_
  constructor
  · rintro ⟨⟨x', y', z'⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact mem_swapXZ'.2 h
  · intro h
    exact ⟨(x, y, z), rfl, mem_swapXZ'.1 h⟩

theorem lawSwapXY_support (μ : FinProb (X × Y × Z)) : (lawSwapXY μ).support = swapXY μ.support := by
  ext ⟨y, x, z⟩
  refine (mem_support_mergePush _ _ _).trans ?_
  constructor
  · rintro ⟨⟨x', y', z'⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact mem_swapXY'.2 h
  · intro h
    exact ⟨(x, y, z), rfl, mem_swapXY'.1 h⟩

/-- the path trick of `μ` with respect to `z` (the labels are the `z`-coordinates of the walk),
over `X × Y × Z̃`, `Z̃ = PathX (lawSwapXZ μ) ℓ`: the `x`-path trick of the swap, swapped back. -/
def pathTrickZ (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) :
    FinProb (X × Y × PathX (lawSwapXZ μ) ℓ hℓ) :=
  mergePush (pathTrick (lawSwapXZ μ) ℓ hℓ) fun p => (p.2.2, p.2.1, p.1)

/-- the path trick of `μ` with respect to `y`, over `X × Ỹ × Z`, `Ỹ = PathX (lawSwapXY μ) ℓ`. -/
def pathTrickY (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) :
    FinProb (X × PathX (lawSwapXY μ) ℓ hℓ × Z) :=
  mergePush (pathTrick (lawSwapXY μ) ℓ hℓ) fun p => (p.2.1, p.1, p.2.2)

private theorem pathTrickZ_support (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) :
    (pathTrickZ μ ℓ hℓ).support = swapXZ (pathTrick (lawSwapXZ μ) ℓ hℓ).support := by
  ext ⟨x, y, w⟩
  refine (mem_support_mergePush _ _ _).trans ?_
  constructor
  · rintro ⟨⟨w', y', x'⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact mem_swapXZ'.2 h
  · intro h
    exact ⟨(w, y, x), rfl, mem_swapXZ'.1 h⟩

private theorem pathTrickY_support (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) :
    (pathTrickY μ ℓ hℓ).support = swapXY (pathTrick (lawSwapXY μ) ℓ hℓ).support := by
  ext ⟨x, w, z⟩
  refine (mem_support_mergePush _ _ _).trans ?_
  constructor
  · rintro ⟨⟨w', x', z'⟩, he, h⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact mem_swapXY'.2 h
  · intro h
    exact ⟨(w, x, z), rfl, mem_swapXY'.1 h⟩

theorem inT_pathTrick {μ : FinProb (X × Y × Z)} (h : InT μ.support) {ℓ : ℕ} (hℓ : Odd ℓ) :
    InT (pathTrick μ ℓ hℓ).support := by
  exact ⟨pathTrick_pairwiseConnected μ hℓ h.1, not_admitsAbelianEmbedding_pathTrick μ hℓ h.2⟩

theorem inT_pathTrickZ {μ : FinProb (X × Y × Z)} (h : InT μ.support) {ℓ : ℕ} (hℓ : Odd ℓ) :
    InT (pathTrickZ μ ℓ hℓ).support := by
  rw [pathTrickZ_support]
  refine (inT_swapXZ_iff _).2 (inT_pathTrick ?_ hℓ)
  rw [lawSwapXZ_support]
  exact (inT_swapXZ_iff _).2 h

theorem inT_pathTrickY {μ : FinProb (X × Y × Z)} (h : InT μ.support) {ℓ : ℕ} (hℓ : Odd ℓ) :
    InT (pathTrickY μ ℓ hℓ).support := by
  rw [pathTrickY_support]
  refine (inT_swapXY_iff _).2 (inT_pathTrick ?_ hℓ)
  rw [lawSwapXY_support]
  exact (inT_swapXY_iff _).2 h

/-- constant walks: every atom of `μ` is the diagonal atom of the path trick (`x`-slot). -/
theorem pathTrick_diag_mem_support (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    {p : X × Y × Z} (hp : p ∈ μ.support) :
    ∃ w : PathX μ ℓ hℓ, (∀ j, w.1 j = p.1) ∧ (w, p.2.1, p.2.2) ∈ (pathTrick μ ℓ hℓ).support := by
  obtain ⟨x, y, z⟩ := p
  exact ⟨⟨fun _ => x, y, z, (const_word_mem_pathWeight_pos μ hℓ hp).ne'⟩, fun _ => rfl,
    (const_word_mem_pathWeight_pos μ hℓ hp).ne'⟩

theorem pathTrickZ_diag_mem_support (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    {p : X × Y × Z} (hp : p ∈ μ.support) :
    ∃ w : PathX (lawSwapXZ μ) ℓ hℓ, (∀ j, w.1 j = p.2.2) ∧
      (p.1, p.2.1, w) ∈ (pathTrickZ μ ℓ hℓ).support := by
  have hp' : (p.2.2, p.2.1, p.1) ∈ (lawSwapXZ μ).support := by
    rw [lawSwapXZ_support]
    exact mem_swapXZ'.2 hp
  obtain ⟨w, hw, hmem⟩ := pathTrick_diag_mem_support (lawSwapXZ μ) hℓ hp'
  refine ⟨w, hw, ?_⟩
  rw [pathTrickZ_support]
  exact mem_swapXZ'.2 hmem

theorem pathTrickY_diag_mem_support (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    {p : X × Y × Z} (hp : p ∈ μ.support) :
    ∃ w : PathX (lawSwapXY μ) ℓ hℓ, (∀ j, w.1 j = p.2.1) ∧
      (p.1, w, p.2.2) ∈ (pathTrickY μ ℓ hℓ).support := by
  have hp' : (p.2.1, p.1, p.2.2) ∈ (lawSwapXY μ).support := by
    rw [lawSwapXY_support]
    exact mem_swapXY'.2 hp
  obtain ⟨w, hw, hmem⟩ := pathTrick_diag_mem_support (lawSwapXY μ) hℓ hp'
  refine ⟨w, hw, ?_⟩
  rw [pathTrickY_support]
  exact mem_swapXY'.2 hmem

/-- the path trick keeps the `y`-marginal (Supplement E `lem:T-path`, Lemma 3.9's `μ_y`). -/
theorem pathTrick_marginalY (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) (y : Y) :
    ∑ q ∈ Finset.univ.filter (fun q : PathX μ ℓ hℓ × Y × Z => q.2.1 = y),
        (pathTrick μ ℓ hℓ).prob q = margY μ y := by
  obtain ⟨m, rfl⟩ := id hℓ
  rw [Finset.sum_filter]
  change ∑ q : PathX μ (2 * m + 1) hℓ × Y × Z,
    (if q.2.1 = y then pathWeight μ (2 * m + 1) hℓ q.1.1 q.2.1 q.2.2 else 0) = _
  rw [Fintype.sum_prod_type]
  have h1 : ∀ w : PathX μ (2 * m + 1) hℓ,
      ∑ q : Y × Z, (if q.1 = y then pathWeight μ (2 * m + 1) hℓ w.1 q.1 q.2 else 0) =
        ∑ z, pathWeight μ (2 * m + 1) hℓ w.1 y z := by
    intro w
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  simp only [h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun w : Fin (2 * m + 1) → X =>
      ∃ (y' : Y) (z : Z), pathWeight μ (2 * m + 1) hℓ w y' z ≠ 0)
      (p := fun w : Fin (2 * m + 1) → X => ∃ (y' : Y) (z : Z),
        pathWeight μ (2 * m + 1) hℓ w y' z ≠ 0) (fun w => by simp)
      (fun w => ∑ z, pathWeight μ (2 * m + 1) hℓ w y z)]
  rw [Finset.sum_filter_of_ne]
  · unfold pathWeight
    simp_rw [← Finset.mul_sum]
    rw [sum_walkYZ_row]
    by_cases hm : 0 < margY μ y
    · simp [hm]
    · have : margY μ y = 0 := le_antisymm (not_lt.mp hm) (margY_nonneg μ y)
      simp [this]
  · intro w _ hw
    obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    exact ⟨y, z, hz⟩

theorem card_pathX_le (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) :
    Fintype.card (PathX μ ℓ hℓ) ≤ Fintype.card X ^ ℓ := by
  calc Fintype.card (PathX μ ℓ hℓ) ≤ Fintype.card (Fin ℓ → X) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card X ^ ℓ := by rw [Fintype.card_fun, Fintype.card_fin]

/-- role-permuted adapter of `pathTrick_gammaPhi_complete`: for `ℓ ≥ 2m` odd, the `(Σ, Γ)`-support
of the `z`-path trick is complete (the threshold depends only on `m`). -/
theorem pathTrickZ_sigmaGamma_complete (m : ℕ) :
    ∃ ℓ₀ : ℕ, ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
      [DecidableEq X] [DecidableEq Y] [DecidableEq Z],
      Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
      ∀ μ : FinProb (X × Y × Z), PairwiseConnected3 μ.support →
      ∀ (ℓ : ℕ) (hℓ : Odd ℓ), ℓ₀ ≤ ℓ →
      ∀ (x : X) (y : Y), ∃ w : PathX (lawSwapXZ μ) ℓ hℓ, (x, y, w) ∈ (pathTrickZ μ ℓ hℓ).support := by
  obtain ⟨ℓ₀, h⟩ := pathTrick_gammaPhi_complete m
  refine ⟨ℓ₀, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hμ ℓ hℓ hle x y
  have hν : PairwiseConnected3 (lawSwapXZ μ).support := by
    rw [lawSwapXZ_support]
    exact (pc_swapXZ _).2 hμ
  obtain ⟨w, hw⟩ := h Z Y X hZ hY hX (lawSwapXZ μ) hν ℓ hℓ hle y x
  refine ⟨w, ?_⟩
  rw [pathTrickZ_support]
  exact mem_swapXZ'.2 hw

theorem pathTrickY_sigmaPhi_complete (m : ℕ) :
    ∃ ℓ₀ : ℕ, ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
      [DecidableEq X] [DecidableEq Y] [DecidableEq Z],
      Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
      ∀ μ : FinProb (X × Y × Z), PairwiseConnected3 μ.support →
      ∀ (ℓ : ℕ) (hℓ : Odd ℓ), ℓ₀ ≤ ℓ →
      ∀ (x : X) (z : Z), ∃ w : PathX (lawSwapXY μ) ℓ hℓ, (x, w, z) ∈ (pathTrickY μ ℓ hℓ).support := by
  obtain ⟨ℓ₀, h⟩ := pathTrick_gammaPhi_complete m
  refine ⟨ℓ₀, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hμ ℓ hℓ hle x z
  have hν : PairwiseConnected3 (lawSwapXY μ).support := by
    rw [lawSwapXY_support]
    exact (pairwiseConnected3_swapXY_iff _).2 hμ
  obtain ⟨w, hw⟩ := h Y X Z hY hX hZ (lawSwapXY μ) hν ℓ hℓ hle x z
  refine ⟨w, ?_⟩
  rw [pathTrickY_support]
  exact mem_swapXY'.2 hw

end PathSlots

/-! ### L5, L6: the construction of `ν` on `𝒯` and triviality of the duplication -/

section Construction
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- steps 1-3 of the construction (support level): `S¹ = pathTrickZ μ̂ ℓ₁`, `S² = pathTrick S¹ ℓ₂`,
`S³ = ` the `x`-merge of `S²` by the representative map `a` (Supplement E `lem:T-construction`). The hypotheses
`hc₁`, `hc₂` are the source's choice of `ℓ₁`, `ℓ₂` (completeness of the `(Σ,Γ)`- resp. `(Γ,Φ̃)`-support). -/
theorem inT_construction (μ : FinProb (X × Y × Z)) (hμ : InT μ.support) {ℓ₁ ℓ₂ : ℕ}
    (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂)
    (hc₁ : ∀ (x : X) (y : Y), ∃ w : PathX (lawSwapXZ μ) ℓ₁ h₁, (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support)
    (hc₂ : ∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁),
      ∃ v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂,
        (v, y, w) ∈ (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support)
    (a : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂ → PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂)
    (ha : MergeRep (mergeGraphX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support) a) :
    InT (pathTrickZ μ ℓ₁ h₁).support ∧
    InT (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support ∧
    InT (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support ∧
    mergeImpliesX (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support ∧
    (∀ (y : Y) (w : PathX (lawSwapXZ μ) ℓ₁ h₁),
      ∃ x' : ↥(Set.range a), (x', y, w) ∈ (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support) ∧
    (∀ p ∈ μ.support, ∃ (w : PathX (lawSwapXZ μ) ℓ₁ h₁) (v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂),
      (∀ j, w.1 j = p.2.2) ∧ (∀ j, v.1 j = p.1) ∧
      (p.1, p.2.1, w) ∈ (pathTrickZ μ ℓ₁ h₁).support ∧
      (v, p.2.1, w) ∈ (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support ∧
      (⟨a v, Set.mem_range_self _⟩, p.2.1, w) ∈
        (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support) ∧
    (∀ (x : X) (y : Y), ∃ (w : PathX (lawSwapXZ μ) ℓ₁ h₁)
        (v : PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂),
      (∀ j, v.1 j = x) ∧
      (⟨a v, Set.mem_range_self _⟩, y, w) ∈
        (mergeDistX (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) a).support) := by
  have hS1 : InT (pathTrickZ μ ℓ₁ h₁).support := inT_pathTrickZ hμ h₁
  have hS2 : InT (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂).support := inT_pathTrick hS1 h₂
  refine ⟨hS1, hS2, ?_, mergeDistX_impliesX _ a ha, ?_, ?_, ?_⟩
  · rw [mergeDistX_support_eq]
    exact inT_mergeSetX hS2 a
  · intro y w
    exact mergeDistX_fullYZ _ a hc₂ y w
  · intro p hp
    obtain ⟨w, hw, hmem⟩ := pathTrickZ_diag_mem_support μ h₁ hp
    obtain ⟨v, hv, hmem2⟩ := pathTrick_diag_mem_support (pathTrickZ μ ℓ₁ h₁) h₂ hmem
    exact ⟨w, v, hw, hv, hmem, hmem2, (mergeDistX_support _ a _ _ _).2 ⟨v, rfl, hmem2⟩⟩
  · intro x y
    obtain ⟨w, hw⟩ := hc₁ x y
    obtain ⟨v, hv, hmem⟩ := pathTrick_diag_mem_support (pathTrickZ μ ℓ₁ h₁) h₂ hw
    exact ⟨w, v, hv, (mergeDistX_support _ a _ _ _).2 ⟨v, rfl, hmem⟩⟩



/-- step 5 without duplication: the law of `(X(y,z), y, z)` with `(y,z)` uniform, where `X(y,z)` is
the `x` with `(x,y,z) ∈ S` (a fixed choice if there is none). -/
def nuOf [Nonempty X] [Nonempty Y] [Nonempty Z] (S : Set (X × Y × Z)) : FinProb (X × Y × Z) :=
  open scoped Classical in
  mergePush (FinProb.uniform : FinProb (Y × Z))
    fun q => (Classical.epsilon fun x => (x, q.1, q.2) ∈ S, q.1, q.2)

private def nuEps [Nonempty X] (S : Set (X × Y × Z)) (y : Y) (z : Z) : X :=
  Classical.epsilon fun x => (x, y, z) ∈ S

private theorem nuOf_prob [Nonempty X] [Nonempty Y] [Nonempty Z] (S : Set (X × Y × Z)) (x : X)
    (y : Y) (z : Z) : (nuOf S).prob (x, y, z) =
      if nuEps S y z = x then 1 / ((Fintype.card Y : ℝ) * Fintype.card Z) else 0 := by
  have hf : Finset.univ.filter (fun q : Y × Z => (nuEps S q.1 q.2, q.1, q.2) = (x, y, z)) =
      if nuEps S y z = x then {(y, z)} else ∅ := by
    ext ⟨y', z'⟩
    by_cases h : nuEps S y z = x
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, ↓reduceIte, Finset.mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨-, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨h, rfl, rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, ↓reduceIte, Finset.notMem_empty,
        iff_false, Prod.mk.injEq]
      rintro ⟨h1, rfl, rfl⟩
      exact h h1
  show ∑ q ∈ Finset.univ.filter (fun q : Y × Z => (nuEps S q.1 q.2, q.1, q.2) = (x, y, z)),
      (1 : ℝ) / Fintype.card (Y × Z) = _
  rw [hf]
  split_ifs with h
  · simp [Fintype.card_prod]
  · simp

/-- Supplement E `lem:dup-trivial`: for `S` with `y, z ⇒ x` and complete `(Γ,Φ̃)`-support, `ν` has support `S`
(so `ν ∈ 𝒯` if `S ∈ 𝒯`), uniform `(y,z)`-marginal and atoms `≥ 1/(|Γ||Φ̃|)`. -/
theorem nuOf_support [Nonempty X] [Nonempty Y] [Nonempty Z] {S : Set (X × Y × Z)}
    (hyz : ∀ (y : Y) (z : Z), ∃! x : X, (x, y, z) ∈ S) : (nuOf S).support = S := by
  ext ⟨x, y, z⟩
  obtain ⟨x₀, hx₀, huniq⟩ := hyz y z
  have hε : nuEps S y z = x₀ := by
    refine huniq _ ?_
    exact Classical.epsilon_spec (p := fun x => (x, y, z) ∈ S) ⟨x₀, hx₀⟩
  have hpos : (0 : ℝ) < 1 / ((Fintype.card Y : ℝ) * Fintype.card Z) := by
    have : 0 < Fintype.card Y := Fintype.card_pos
    have : 0 < Fintype.card Z := Fintype.card_pos
    positivity
  show (nuOf S).prob (x, y, z) ≠ 0 ↔ _
  rw [nuOf_prob, hε]
  constructor
  · intro h
    by_contra hx
    have hx' : ¬ x₀ = x := fun e => hx (e ▸ hx₀)
    simp only [hx', ↓reduceIte] at h
    exact h rfl
  · intro h
    have : x₀ = x := (huniq x h).symm
    simp only [this, ↓reduceIte]
    exact hpos.ne'

theorem nuOf_marginal_yz [Nonempty X] [Nonempty Y] [Nonempty Z] (S : Set (X × Y × Z))
    (y : Y) (z : Z) :
    ∑ x, (nuOf S).prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z) := by
  simp_rw [nuOf_prob]
  simp

theorem nuOf_atom_ge [Nonempty X] [Nonempty Y] [Nonempty Z] (S : Set (X × Y × Z)) :
    ∀ p ∈ (nuOf S).support, 1 / ((Fintype.card Y : ℝ) * Fintype.card Z) ≤ (nuOf S).prob p := by
  rintro ⟨x, y, z⟩ hp
  have hp' : (nuOf S).prob (x, y, z) ≠ 0 := hp
  rw [nuOf_prob] at hp' ⊢
  split_ifs at hp' ⊢ with h
  · exact le_rfl
  · exact absurd rfl hp'

/-- `y, z ⇒ x` with complete `(Γ,Φ̃)`-support is exactly `∃! x`. -/
theorem existsUnique_of_impliesX {S : Set (X × Y × Z)} (hi : mergeImpliesX S)
    (hc : ∀ (y : Y) (z : Z), ∃ x : X, (x, y, z) ∈ S) : ∀ (y : Y) (z : Z), ∃! x : X, (x, y, z) ∈ S := by
  intro y z
  obtain ⟨x, hx⟩ := hc y z
  exact ⟨x, hx, fun x' hx' => hi y z x' x hx' hx⟩

end Construction

end MaxT
end TrackB
end RestrictedPolynomials
end

