module

public import RestrictedPolynomials.TrackB.PathTrick
public import RestrictedPolynomials.TrackB.MasterEmbedding
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Track B: the path trick and embeddings (paper IV, Section 3.2)

Source: paper IV (`writeup_stability.tex`), L1740-1754 (definition), L1887-1932
(Lemma 3.10), L1960-1974 (Lemma 3.12, trivial-`H` form only), L1982-2001 (Lemma 3.13).

The general-`H` form of Lemma 3.12 is deliberately NOT stated.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section PathTrickEmb
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem pathWeight_nonneg (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) (w : Fin ℓ → X)
    (y : Y) (z : Z) : 0 ≤ pathWeight μ ℓ hℓ w y z :=
  mul_nonneg (margY_nonneg μ y) (walkYZ_nonneg μ _ y z)

/-- `Σ'`: the words of `Σ^ℓ` that occur as the label vector of a support point of `μ_ℓ`. -/
abbrev PathX (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) : Type :=
  {w : Fin ℓ → X // ∃ (y : Y) (z : Z), pathWeight μ ℓ hℓ w y z ≠ 0}

instance (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) : Fintype (PathX μ ℓ hℓ) :=
  Fintype.ofFinite _

theorem sum_pathWeight_subtype (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) :
    ∑ p : PathX μ ℓ hℓ × Y × Z, pathWeight μ ℓ hℓ p.1.1 p.2.1 p.2.2 = 1 := by
  classical
  rw [← sum_pathWeight μ hℓ]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_subtype (Finset.univ.filter fun w : Fin ℓ → X => ∃ (y : Y) (z : Z),
      pathWeight μ ℓ hℓ w y z ≠ 0) (p := fun w : Fin ℓ → X => ∃ (y : Y) (z : Z),
      pathWeight μ ℓ hℓ w y z ≠ 0) (fun w => by simp)
      (fun w => ∑ y, ∑ z, pathWeight μ ℓ hℓ w y z)]
  rw [Finset.sum_filter_of_ne]
  intro w _ hw
  by_contra hne
  apply hw
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => ?_
  by_contra h
  exact hne ⟨y, z, h⟩

/-- The path-trick distribution `μ_ℓ` of paper IV §3.2 on `Σ' × Γ × Φ` (walk definition, `ℓ` odd). -/
def pathTrick (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) :
    FinProb (PathX μ ℓ hℓ × Y × Z) where
  prob p := pathWeight μ ℓ hℓ p.1.1 p.2.1 p.2.2
  nonneg _ := pathWeight_nonneg μ hℓ _ _ _
  sum_eq_one := sum_pathWeight_subtype μ hℓ

theorem pathTrick_prob (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) (w : PathX μ ℓ hℓ)
    (y : Y) (z : Z) : (pathTrick μ ℓ hℓ).prob (w, y, z) = pathWeight μ ℓ hℓ w.1 y z := rfl

/-! ### Private helpers -/

private def altL {X H : Type*} [AddCommGroup H] (σ : X → H) : List X → H
  | [] => 0
  | x :: xs => σ x - altL σ xs

private lemma sharp_eq_altL {X H : Type*} [AddCommGroup H] (σ : X → H) :
    ∀ (ℓ : ℕ) (w : Fin ℓ → X), sharp σ ℓ w = altL σ (List.ofFn w)
  | 0, w => by simp [sharp, altL]
  | n + 1, w => by
    rw [List.ofFn_succ, altL, ← sharp_eq_altL σ n (fun i => w i.succ)]
    simp only [sharp, Fin.sum_univ_succ, pow_succ, pow_zero, Fin.val_zero, Fin.val_succ]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib, mul_comm, mul_smul]

private lemma altL_walk (μ : FinProb (X × Y × Z)) {H : Type*} [AddCommGroup H]
    {σ : X → H} {γ : Y → H} {φ : Z → H}
    (h : ∀ x y z, μ.prob (x, y, z) ≠ 0 → σ x + γ y + φ z = 0) :
    ∀ (n : ℕ) (xs : List X), xs.length = 2 * n + 1 → ∀ (y : Y) (z : Z),
      walkYZ μ xs y z ≠ 0 → altL σ xs = -γ y - φ z := by
  intro n
  induction n with
  | zero =>
    intro xs hlen y z hw
    match xs, hlen with
    | [x], _ =>
      have hp : μ.prob (x, y, z) ≠ 0 := by
        intro h0
        apply hw
        simp [walkYZ, stepYZ, h0]
      have := h x y z hp
      simp only [altL, sub_zero]
      rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]
      rw [← this]; abel
  | succ n ih =>
    intro xs hlen y z hw
    match xs, hlen with
    | x₁ :: x₂ :: rest, hlen =>
      have hl : rest.length = 2 * n + 1 := by simp at hlen; omega
      rw [walkYZ, Matrix.mul_apply] at hw
      obtain ⟨y', -, hy'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
      rcases mul_ne_zero_iff.1 hy' with ⟨h1, h2⟩
      rw [Matrix.mul_apply] at h1
      obtain ⟨z', -, hz'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      rcases mul_ne_zero_iff.1 hz' with ⟨h3, h4⟩
      have p1 : μ.prob (x₁, y, z') ≠ 0 := by
        intro h0; apply h3; simp [stepYZ, h0]
      have p2 : μ.prob (x₂, y', z') ≠ 0 := by
        intro h0; apply h4; simp [stepZY, h0]
      have e1 := h x₁ y z' p1
      have e2 := h x₂ y' z' p2
      have e3 := ih rest hl y' z h2
      simp only [altL]
      rw [e3]
      have a1 : σ x₁ = -γ y - φ z' := by rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← e1]; abel
      have a2 : σ x₂ = -γ y' - φ z' := by rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← e2]; abel
      rw [a1, a2]; abel

private lemma emb_prob (μ : FinProb (X × Y × Z)) {H : Type*} [AddCommGroup H]
    {σ : X → H} {γ : Y → H} {φ : Z → H} (h : IsEmbedding3 μ.support σ γ φ) :
    ∀ x y z, μ.prob (x, y, z) ≠ 0 → σ x + γ y + φ z = 0 := fun x y z hp =>
  (isEmbedding3_iff _ _ _ _).1 h (x, y, z) hp

private lemma sharp_walk (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) {H : Type*}
    [AddCommGroup H] {σ : X → H} {γ : Y → H} {φ : Z → H}
    (h : IsEmbedding3 μ.support σ γ φ) (w : Fin ℓ → X) (y : Y) (z : Z)
    (hw : pathWeight μ ℓ hℓ w y z ≠ 0) : sharp σ ℓ w = -γ y - φ z := by
  obtain ⟨n, hn⟩ := hℓ
  have hw' : walkYZ μ (List.ofFn w) y z ≠ 0 := (mul_ne_zero_iff.1 hw).2
  rw [sharp_eq_altL]
  exact altL_walk μ (emb_prob μ h) n _ (by simp [hn]) y z hw'

/-- paper IV `lem:master-stays`, step `sharp-is-embedding`. -/
theorem sharp_isEmbedding (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) {H : Type*}
    [AddCommGroup H] {σ : X → H} {γ : Y → H} {φ : Z → H}
    (h : IsEmbedding3 μ.support σ γ φ) :
    IsEmbedding3 (pathTrick μ ℓ hℓ).support (fun w : PathX μ ℓ hℓ => sharp σ ℓ w.1) γ φ := by
  rw [isEmbedding3_iff]
  rintro ⟨w, y, z⟩ hp
  have hp' : pathWeight μ ℓ hℓ w.1 y z ≠ 0 := hp
  simp only
  rw [sharp_walk μ hℓ h w.1 y z hp']
  abel

/-- paper IV `lem:reverse-embed` (Lemma 3.10). -/
theorem reverse_embed (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) {H : Type*}
    [AddCommGroup H] (σ : PathX μ ℓ hℓ → H) (γ : Y → H) (φ : Z → H)
    (h : IsEmbedding3 (pathTrick μ ℓ hℓ).support σ γ φ) :
    ∃ σ' : X → H, IsEmbedding3 μ.support σ' γ φ ∧ ∀ w : PathX μ ℓ hℓ, σ w = sharp σ' ℓ w.1 := by
  classical
  have hmem : ∀ x y z, μ.prob (x, y, z) ≠ 0 →
      ∃ y' z', pathWeight μ ℓ hℓ (fun _ => x) y' z' ≠ 0 := fun x y z hp =>
    ⟨y, z, (const_word_mem_pathWeight_pos μ hℓ hp).ne'⟩
  let σ' : X → H := fun x =>
    if hx : ∃ y z, μ.prob (x, y, z) ≠ 0 then
      σ ⟨fun _ => x, hmem x hx.choose hx.choose_spec.choose hx.choose_spec.choose_spec⟩
    else 0
  have hσ' : ∀ x y z, (hp : μ.prob (x, y, z) ≠ 0) →
      σ' x = σ ⟨fun _ => x, hmem x y z hp⟩ := by
    intro x y z hp
    have hx : ∃ y z, μ.prob (x, y, z) ≠ 0 := ⟨y, z, hp⟩
    simp only [σ', dif_pos hx]
  have hemb := (isEmbedding3_iff _ _ _ _).1 h
  have key : ∀ x y z, (hp : μ.prob (x, y, z) ≠ 0) → σ' x + γ y + φ z = 0 := by
    intro x y z hp
    rw [hσ' x y z hp]
    exact hemb (⟨fun _ => x, hmem x y z hp⟩, y, z)
      (by show pathWeight μ ℓ hℓ (fun _ => x) y z ≠ 0
          exact (const_word_mem_pathWeight_pos μ hℓ hp).ne')
  have hE : IsEmbedding3 μ.support σ' γ φ := by
    rw [isEmbedding3_iff]
    rintro ⟨x, y, z⟩ hp
    exact key x y z hp
  refine ⟨σ', hE, fun w => ?_⟩
  obtain ⟨y, z, hyz⟩ := w.2
  have h1 : σ w + γ y + φ z = 0 := hemb (w, y, z) hyz
  rw [sharp_walk μ hℓ hE w.1 y z hyz]
  rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h1]; abel

private lemma const_of_not_admits (μ : FinProb (X × Y × Z))
    (h : ¬ AdmitsAbelianEmbedding3 μ.support) {G : Type} [AddCommGroup G]
    {σ : X → G} {γ : Y → G} {φ : Z → G} (he : IsEmbedding3 μ.support σ γ φ) :
    (∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b) := by
  by_contra hc
  exact h ⟨G, inferInstance, (admitsEmbeddingInto3_iff _ _).2
    ⟨σ, γ, φ, he, (isNontrivialEmbedding3_iff _ _ _).2 hc⟩⟩

/-- trivial-H form of paper IV `lem:master-stays`: `μ_ℓ` admits no non-trivial abelian embedding when
`μ` admits none. -/
theorem not_admitsAbelianEmbedding_pathTrick (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (h : ¬ AdmitsAbelianEmbedding3 μ.support) :
    ¬ AdmitsAbelianEmbedding3 (pathTrick μ ℓ hℓ).support := by
  rintro ⟨G, _, hA⟩
  obtain ⟨σ, γ, φ, he, hn⟩ := (admitsEmbeddingInto3_iff _ _).1
    (show AdmitsEmbeddingInto3 (pathTrick μ ℓ hℓ).support G from hA)
  obtain ⟨σ', he', hσ⟩ := reverse_embed μ hℓ σ γ φ he
  obtain ⟨c1, c2, c3⟩ := const_of_not_admits μ h he'
  refine (isNontrivialEmbedding3_iff _ _ _).1 hn ⟨fun a b => ?_, c2, c3⟩
  rw [hσ a, hσ b]
  unfold sharp
  exact Finset.sum_congr rfl fun j _ => by rw [c1 (a.1 j) (b.1 j)]

private lemma exists_support (μ : FinProb (X × Y × Z)) : ∃ p, p ∈ μ.support := by
  by_contra hne
  push_neg at hne
  have : ∀ p, μ.prob p = 0 := fun p => by
    by_contra h0; exact hne p h0
  have h1 := μ.sum_eq_one
  simp [this] at h1

/-- CSP_7 `thm:3csp-bkm2`, step `trivial-master-embedding`. -/
theorem trivial_master_embedding (μ : FinProb (X × Y × Z))
    (h : ¬ AdmitsAbelianEmbedding3 μ.support) :
    IsMasterEmbedding μ.support (s := 1) (fun _ => Unit)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
      IsSaturated3 (fun (_ : X) (_ : Fin 1) => (0 : Unit)) (fun (_ : Y) (_ : Fin 1) => (0 : Unit))
        (fun (_ : Z) (_ : Fin 1) => (0 : Unit)) ∧
      ∀ a b c : Fin 1 → Unit, a + b + c = 0 → ∃ p ∈ μ.support,
        (fun (_ : X) (_ : Fin 1) => (0 : Unit)) p.1 = a ∧
          (fun (_ : Y) (_ : Fin 1) => (0 : Unit)) p.2.1 = b ∧
          (fun (_ : Z) (_ : Fin 1) => (0 : Unit)) p.2.2 = c := by
  obtain ⟨p0, hp0⟩ := exists_support μ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [isEmbedding3_iff]
    intro p _
    exact Subsingleton.elim _ _
  · intro G _ σ' γ' φ' he hz
    obtain ⟨c1, c2, c3⟩ := const_of_not_admits μ h he
    obtain ⟨⟨x0, hx0⟩, ⟨y0, hy0⟩, ⟨z0, hz0⟩⟩ := hz
    refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | exact Function.injective_of_subsingleton _
      | (intro x; simp only [AddMonoidHom.zero_apply]; first
          | exact (c1 x x0).trans hx0
          | exact (c2 x y0).trans hy0
          | exact (c3 x z0).trans hz0)
  · refine ⟨⟨⊤, ?_⟩, ⟨⊤, ?_⟩, ⟨⊤, ?_⟩⟩
    · ext t
      simp only [AddSubgroup.coe_top, Set.mem_univ, Set.mem_range, true_iff]
      exact ⟨p0.1, trivial⟩
    · ext t
      simp only [AddSubgroup.coe_top, Set.mem_univ, Set.mem_range, true_iff]
      exact ⟨p0.2.1, trivial⟩
    · ext t
      simp only [AddSubgroup.coe_top, Set.mem_univ, Set.mem_range, true_iff]
      exact ⟨p0.2.2, trivial⟩
  · intro a b c _
    exact ⟨p0, hp0, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- trivial-H form of paper IV `lem:master-stays` (Lemma 3.12): if `μ` admits no non-trivial abelian embedding,
the zero maps into `{0}` are a master embedding of the path trick `μ_ℓ`. The general-`H` lemma is NOT
stated. -/
theorem master_stays_trivial (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (h : ¬ AdmitsAbelianEmbedding3 μ.support) :
    IsMasterEmbedding (pathTrick μ ℓ hℓ).support (s := 1) (fun _ => Unit)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) :=
  (trivial_master_embedding (pathTrick μ ℓ hℓ) (not_admitsAbelianEmbedding_pathTrick μ hℓ h)).1

/-! ### Lemma 3.13: connectedness -/

private lemma lift_connected {X A W : Type} [Nonempty A] (R : X → A → Prop) (R' : W → A → Prop)
    (c : X → W) (hc : ∀ x a, R x a → R' (c x) a) (hW : ∀ w, ∃ a, R' w a)
    (G : SimpleGraph (X ⊕ A)) (G' : SimpleGraph (W ⊕ A))
    (hG : ∀ u v, G.Adj u v → (∃ x a, R x a ∧ u = Sum.inl x ∧ v = Sum.inr a) ∨
      (∃ x a, R x a ∧ v = Sum.inl x ∧ u = Sum.inr a))
    (hG' : ∀ w a, R' w a → G'.Adj (Sum.inl w) (Sum.inr a))
    (hconn : G.Connected) : G'.Connected := by
  let f : X ⊕ A → W ⊕ A := Sum.map c id
  have hom : ∀ u v, G.Adj u v → G'.Adj (f u) (f v) := by
    intro u v hadj
    rcases hG u v hadj with ⟨x, a, hr, rfl, rfl⟩ | ⟨x, a, hr, rfl, rfl⟩
    · exact hG' _ _ (hc x a hr)
    · exact (hG' _ _ (hc x a hr)).symm
  let F : G →g G' := ⟨f, fun {u v} h => hom u v h⟩
  have hA : ∀ a a' : A, G'.Reachable (Sum.inr a) (Sum.inr a') := fun a a' =>
    (hconn.preconnected (Sum.inr a) (Sum.inr a')).map F
  have hu : ∀ u : W ⊕ A, ∃ a, G'.Reachable u (Sum.inr a) := by
    rintro (w | a)
    · obtain ⟨a, ha⟩ := hW w
      exact ⟨a, (hG' w a ha).reachable⟩
    · exact ⟨a, SimpleGraph.Reachable.refl _⟩
  obtain ⟨a0⟩ := ‹Nonempty A›
  refine ⟨fun u v => ?_⟩
  obtain ⟨a, ha⟩ := hu u
  obtain ⟨a', ha'⟩ := hu v
  exact ha.trans ((hA a a').trans ha'.symm)

private lemma exists_const_map (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) :
    ∃ c : X → PathX μ ℓ hℓ, ∀ x y z, μ.prob (x, y, z) ≠ 0 → (c x).1 = fun _ => x := by
  classical
  obtain ⟨p0, hp0⟩ := exists_support μ
  have hmem : ∀ x y z, μ.prob (x, y, z) ≠ 0 →
      ∃ y' z', pathWeight μ ℓ hℓ (fun _ => x) y' z' ≠ 0 := fun x y z hp =>
    ⟨y, z, (const_word_mem_pathWeight_pos μ hℓ hp).ne'⟩
  refine ⟨fun x => if hx : ∃ y z, μ.prob (x, y, z) ≠ 0 then
      ⟨fun _ => x, hmem x hx.choose hx.choose_spec.choose hx.choose_spec.choose_spec⟩
    else ⟨fun _ => p0.1, hmem p0.1 p0.2.1 p0.2.2 hp0⟩, ?_⟩
  intro x y z hp
  have hx : ∃ y z, μ.prob (x, y, z) ≠ 0 := ⟨y, z, hp⟩
  simp only [dif_pos hx]

private lemma const_mem_support (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (c : X → PathX μ ℓ hℓ) (hc : ∀ x y z, μ.prob (x, y, z) ≠ 0 → (c x).1 = fun _ => x)
    {x : X} {y : Y} {z : Z} (hp : μ.prob (x, y, z) ≠ 0) :
    (c x, y, z) ∈ (pathTrick μ ℓ hℓ).support := by
  show pathWeight μ ℓ hℓ (c x).1 y z ≠ 0
  rw [hc x y z hp]
  exact (const_word_mem_pathWeight_pos μ hℓ hp).ne'

/-- paper IV `lem:path-keeps-connectedness`, step `x-graphs-connected`. -/
theorem pathTrick_xGraphs_connected (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (h : PairwiseConnected3 μ.support) :
    (SimpleGraph.fromRel fun (a : PathX μ ℓ hℓ ⊕ Y) b =>
        ∃ w y z, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support ∧ a = Sum.inl w ∧ b = Sum.inr y).Connected ∧
    (SimpleGraph.fromRel fun (a : PathX μ ℓ hℓ ⊕ Z) b =>
        ∃ w y z, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support ∧ a = Sum.inl w ∧ b = Sum.inr z).Connected := by
  obtain ⟨c, hc⟩ := exists_const_map μ hℓ
  obtain ⟨p0, hp0⟩ := exists_support μ
  obtain ⟨h1, h2, -⟩ := (pairwiseConnected3_iff _).1 h
  constructor
  · haveI : Nonempty Y := ⟨p0.2.1⟩
    refine lift_connected (fun x y => ∃ z, (x, y, z) ∈ μ.support)
      (fun w y => ∃ z, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support) c ?_ ?_ _ _ ?_ ?_ h1
    · rintro x y ⟨z, hz⟩
      exact ⟨z, const_mem_support μ hℓ c hc hz⟩
    · intro w
      obtain ⟨y, z, hyz⟩ := w.2
      exact ⟨y, z, hyz⟩
    · intro u v hadj
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj with ⟨_, ⟨x, y, z, hm, rfl, rfl⟩ | ⟨x, y, z, hm, rfl, rfl⟩⟩
      · exact Or.inl ⟨x, y, ⟨z, hm⟩, rfl, rfl⟩
      · exact Or.inr ⟨x, y, ⟨z, hm⟩, rfl, rfl⟩
    · rintro w a ⟨z, hz⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inl ⟨w, a, z, hz, rfl, rfl⟩⟩
  · haveI : Nonempty Z := ⟨p0.2.2⟩
    refine lift_connected (fun x z => ∃ y, (x, y, z) ∈ μ.support)
      (fun w z => ∃ y, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support) c ?_ ?_ _ _ ?_ ?_ h2
    · rintro x z ⟨y, hy⟩
      exact ⟨y, const_mem_support μ hℓ c hc hy⟩
    · intro w
      obtain ⟨y, z, hyz⟩ := w.2
      exact ⟨z, y, hyz⟩
    · intro u v hadj
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj with ⟨_, ⟨x, y, z, hm, rfl, rfl⟩ | ⟨x, y, z, hm, rfl, rfl⟩⟩
      · exact Or.inl ⟨x, z, ⟨y, hm⟩, rfl, rfl⟩
      · exact Or.inr ⟨x, z, ⟨y, hm⟩, rfl, rfl⟩
    · rintro w a ⟨y, hy⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inl ⟨w, y, a, hy, rfl, rfl⟩⟩

/-- paper IV `lem:path-keeps-connectedness`, step `gamma-phi-connected`. -/
theorem pathTrick_gammaPhi_connected (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (h : PairwiseConnected3 μ.support) :
    (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ w y z, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support ∧ a = Sum.inl y ∧ b = Sum.inr z).Connected := by
  obtain ⟨c, hc⟩ := exists_const_map μ hℓ
  obtain ⟨-, -, h3⟩ := (pairwiseConnected3_iff _).1 h
  refine SimpleGraph.Connected.mono ?_ h3
  intro u v hadj
  rw [SimpleGraph.fromRel_adj] at hadj ⊢
  rcases hadj with ⟨hne, ⟨x, y, z, hm, rfl, rfl⟩ | ⟨x, y, z, hm, rfl, rfl⟩⟩
  · exact ⟨hne, Or.inl ⟨c x, y, z, const_mem_support μ hℓ c hc hm, rfl, rfl⟩⟩
  · exact ⟨hne, Or.inr ⟨c x, y, z, const_mem_support μ hℓ c hc hm, rfl, rfl⟩⟩

/-- paper IV `lem:path-keeps-connectedness` (first assertion). -/
theorem pathTrick_pairwiseConnected (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (h : PairwiseConnected3 μ.support) : PairwiseConnected3 (pathTrick μ ℓ hℓ).support := by
  rw [pairwiseConnected3_iff]
  exact ⟨(pathTrick_xGraphs_connected μ hℓ h).1, (pathTrick_xGraphs_connected μ hℓ h).2,
    pathTrick_gammaPhi_connected μ hℓ h⟩

end PathTrickEmb

/-! ### Completeness of the `Γ–Φ` graph -/

section Complete

/-- an odd walk of `2N+1` steps with positive weight -/
private def Qpos {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) (N : ℕ) (y : Y) (z : Z) : Prop :=
  ∃ xs : List X, xs.length = 2 * N + 1 ∧ 0 < walkYZ μ xs y z

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

private lemma Qpos_zero (μ : FinProb (X × Y × Z)) {x : X} {y : Y} {z : Z}
    (h : μ.prob (x, y, z) ≠ 0) : Qpos μ 0 y z :=
  ⟨[x], rfl, by simpa [walkYZ] using stepYZ_pos μ h⟩

private lemma Qpos_prepend (μ : FinProb (X × Y × Z)) {N : ℕ} {y y' : Y} {z z' : Z} {x₁ x₂ : X}
    (hQ : Qpos μ N y' z) (h1 : μ.prob (x₁, y, z') ≠ 0) (h2 : μ.prob (x₂, y', z') ≠ 0) :
    Qpos μ (N + 1) y z := by
  obtain ⟨xs, hlen, hpos⟩ := hQ
  refine ⟨x₁ :: x₂ :: xs, by simp [hlen]; ring, ?_⟩
  rw [walkYZ, Matrix.mul_apply]
  have hnn : ∀ y'', 0 ≤ (stepYZ μ x₁ * stepZY μ x₂) y y'' * walkYZ μ xs y'' z := fun y'' => by
    refine mul_nonneg ?_ (walkYZ_nonneg μ _ _ _)
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun z'' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun y'' _ => hnn y'') (Finset.mem_univ y'))
  refine mul_pos ?_ hpos
  rw [Matrix.mul_apply]
  exact lt_of_lt_of_le (mul_pos (stepYZ_pos μ h1) (stepZY_pos μ h2))
    (Finset.single_le_sum (f := fun z'' => stepYZ μ x₁ y z'' * stepZY μ x₂ z'' y')
      (fun z'' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _))
      (Finset.mem_univ z'))

private lemma Qpos_mono (μ : FinProb (X × Y × Z)) {y : Y} {z : Z}
    (he : ∃ x z', μ.prob (x, y, z') ≠ 0) {N : ℕ} (hQ : Qpos μ N y z) :
    ∀ k, Qpos μ (N + k) y z := by
  obtain ⟨x, z', hx⟩ := he
  intro k
  induction k with
  | zero => simpa using hQ
  | succ k ih => exact Qpos_prepend μ ih hx hx

private lemma walk_claim (μ : FinProb (X × Y × Z)) :
    ∀ (u v : Y ⊕ Z) (p : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ μ.support ∧ a = Sum.inl y ∧ b = Sum.inr z).Walk u v), ∀ z, v = Sum.inr z →
      (∀ y, u = Sum.inl y → ∃ N, p.length = 2 * N + 1 ∧ Qpos μ N y z) ∧
      (∀ z0, u = Sum.inr z0 → (p.length = 0 ∧ z0 = z) ∨
        ∃ N, p.length = 2 * N + 2 ∧ ∃ y1 x, μ.prob (x, y1, z0) ≠ 0 ∧ Qpos μ N y1 z) := by
  intro u v p
  induction p with
  | nil =>
    intro z hv
    refine ⟨fun y hy => ?_, fun z0 hz0 => ?_⟩
    · rw [hv] at hy; cases hy
    · rw [hv] at hz0
      exact Or.inl ⟨rfl, (Sum.inr.inj hz0).symm⟩
  | @cons u v w hadj p ih =>
    intro z hw
    have ihv := ih z hw
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x, y, z', hm, rfl, rfl⟩ | ⟨x, y, z', hm, rfl, rfl⟩⟩
    · refine ⟨fun y1 hy1 => ?_, fun z0 hz0 => by cases hz0⟩
      have hy1' : y1 = y := (Sum.inl.inj hy1).symm
      subst hy1'
      rcases ihv.2 z' rfl with ⟨hl, hz⟩ | ⟨N, hl, y2, x', hx', hQ⟩
      · refine ⟨0, by simp [hl], ?_⟩
        subst hz
        exact Qpos_zero μ hm
      · exact ⟨N + 1, by simp [hl]; ring, Qpos_prepend μ hQ hm hx'⟩
    · refine ⟨fun y1 hy1 => (by cases hy1), fun z0 hz0 => ?_⟩
      have hz0' : z0 = z' := (Sum.inr.inj hz0).symm
      subst hz0'
      obtain ⟨N, hl, hQ⟩ := ihv.1 y rfl
      exact Or.inr ⟨N, by simp [hl], y, x, hm, hQ⟩

private lemma Y_has_edge (μ : FinProb (X × Y × Z)) (z0 : Z)
    (h3 : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ μ.support ∧ a = Sum.inl y ∧ b = Sum.inr z).Connected) (y : Y) :
    ∃ x z, μ.prob (x, y, z) ≠ 0 := by
  obtain ⟨p⟩ := h3.preconnected (Sum.inl y) (Sum.inr z0)
  cases p with
  | cons hadj _ =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x, y', z, hm, h1, h2⟩ | ⟨x, y', z, hm, h1, h2⟩⟩
    · cases h1; exact ⟨x, z, hm⟩
    · cases h2

end Complete

section Complete2
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- paper IV `lem:path-keeps-connectedness`, step `gamma-phi-complete`, with the uniformity of the source's
`ℓ₀(|Σ|,|Γ|,|Φ|)` closed over the alphabet bound `m` and the extension to all odd `ℓ ≥ ℓ₀`. -/
theorem pathTrick_gammaPhi_complete (m : ℕ) :
    ∃ ℓ₀ : ℕ, ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
      [DecidableEq X] [DecidableEq Y] [DecidableEq Z],
      Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
      ∀ μ : FinProb (X × Y × Z), PairwiseConnected3 μ.support →
      ∀ (ℓ : ℕ) (hℓ : Odd ℓ), ℓ₀ ≤ ℓ →
      ∀ (y : Y) (z : Z), ∃ w : PathX μ ℓ hℓ, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support := by
  refine ⟨2 * m, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ h ℓ hℓ hle y z
  obtain ⟨p0, hp0⟩ := exists_support μ
  obtain ⟨-, -, h3⟩ := (pairwiseConnected3_iff _).1 h
  obtain ⟨p, hpath, -⟩ := h3.exists_path_of_dist (Sum.inl y) (Sum.inr z)
  have hlt := hpath.length_lt
  rw [Fintype.card_sum] at hlt
  obtain ⟨N, hN, hQ⟩ := (walk_claim μ _ _ p z rfl).1 y rfl
  obtain ⟨n, hn⟩ := id hℓ
  have hNn : N + (n - N) = n := by omega
  have hedge := Y_has_edge μ p0.2.2 h3 y
  obtain ⟨xs, hlen, hpos⟩ := hNn ▸ Qpos_mono μ hedge hQ (n - N)
  obtain ⟨x, z', hxz⟩ := hedge
  have hm : 0 < margY μ y :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm hxz)) (prob_le_margY μ x y z')
  let w : Fin ℓ → X := fun i => xs[i.1]'(by have := i.2; omega)
  have hw : List.ofFn w = xs := by
    apply List.ext_getElem
    · simp [hlen, hn]
    · intro i h1 h2; simp [w]
  have hne : pathWeight μ ℓ hℓ w y z ≠ 0 := by
    unfold pathWeight
    rw [hw]
    exact (mul_pos hm hpos).ne'
  exact ⟨⟨w, y, z, hne⟩, hne⟩

end Complete2

end TrackB
end RestrictedPolynomials
end
