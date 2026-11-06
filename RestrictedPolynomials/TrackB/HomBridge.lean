module

public import RestrictedPolynomials.TrackB.S8Split
public import RestrictedPolynomials.TrackB.PathTrickEmbedding

/-!
# Track B: the bridge from the printed setting of Thm 7.14 to the Section 8 and 9 statements

Paper IV Thm 7.14 / 7.14′ (l. 4337-4345, 4464-4470) at the trivial embedding
group `H = {0}` (Supplement E). Section 8's lemmas are stated for a
saturated master embedding `(σ, γ, φ)` into `∀ i, Hs i`; Section 9's `delta_inductive` for any
group `H`; the hypotheses `HomAt`/`HomPAt` for `H = Unit`. This file supplies, as THEOREMS:

* every letter of `X`, `Y`, `Z` occurs, derived from `PairwiseConnected3` (no field is added
  to `Rel67`/`HomPAt`), and the positivity of the three marginals;
* the uniform law of hypothesis 4 for a subsingleton embedding group;
* the transport of a modest basis along two subsingleton groups (`S7ModestBasis.congrTrivial`,
  DATA with its characterisation) and `s7Beta_congrTrivial`: `β` does not change.

Reading of the transport: the Section 8 statements need `H = ∀ i, Hs i`, `Hs := fun _ : Fin 1 => Unit` (built
`trivial_master_embedding`), whereas `HomAt` has `H = Unit`; `β` only sees the functions `u`, and
all of them are the constant `1` on the embedding part, so the two bases are relabelled.
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

/-! ### Every letter occurs; the marginals are positive -/

section Occurs
variable {X Y Z : Type}

/-- Every letter occurs (x): pairwise connectedness gives every `x` an atom `(x, y, z)` (built
`PairwiseConnected3.exists_atom_x`); this is the `hocc` of `s9d_delta_inductive`. -/
theorem hom_hocc_x_of_pc3 {S : Set (X × Y × Z)} (hT : PairwiseConnected3 S) :
    ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ S :=
  fun x => MaxT.PairwiseConnected3.exists_atom_x hT x

/-- Every letter occurs (y). -/
theorem hom_hocc_y_of_pc3 {S : Set (X × Y × Z)} (hT : PairwiseConnected3 S) :
    ∀ y : Y, ∃ (x : X) (z : Z), (x, y, z) ∈ S :=
  fun y => MaxT.PairwiseConnected3.exists_atom_y hT y

/-- Every letter occurs (z). -/
theorem hom_hocc_z_of_pc3 {S : Set (X × Y × Z)} (hT : PairwiseConnected3 S) :
    ∀ z : Z, ∃ (x : X) (y : Y), (x, y, z) ∈ S :=
  fun z => MaxT.PairwiseConnected3.exists_atom_z hT z

variable [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- the three marginals of `ν` charge every letter (TYPING of the Section 8 statements: positivity of
`μ_x`, `μ_y`, `μ_z`): a letter occurs in an atom, and `ν.support` is `{p | ν.prob p ≠ 0}`. -/
theorem hom_marginals_pos_of_pc3 (ν : FinProb (X × Y × Z)) (hT : PairwiseConnected3 ν.support) :
    (∀ a, 0 < (lawX ν).prob a) ∧ (∀ a, 0 < (lawY ν).prob a) ∧ (∀ a, 0 < (lawZ ν).prob a) := by
  have pos : ∀ p ∈ ν.support, 0 < ν.prob p := fun p hp =>
    lt_of_le_of_ne (ν.nonneg p) (Ne.symm hp)
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_⟩
  · obtain ⟨y, z, h⟩ := MaxT.PairwiseConnected3.exists_atom_x hT a
    show 0 < ∑ p ∈ univ.filter (fun p : X × Y × Z => p.1 = a), ν.prob p
    exact lt_of_lt_of_le (pos _ h) (Finset.single_le_sum (f := ν.prob) (fun p _ => ν.nonneg p)
      (by simp : (a, y, z) ∈ univ.filter (fun p : X × Y × Z => p.1 = a)))
  · obtain ⟨x, z, h⟩ := MaxT.PairwiseConnected3.exists_atom_y hT a
    show 0 < ∑ p ∈ univ.filter (fun p : X × Y × Z => p.2.1 = a), ν.prob p
    exact lt_of_lt_of_le (pos _ h) (Finset.single_le_sum (f := ν.prob) (fun p _ => ν.nonneg p)
      (by simp : (x, a, z) ∈ univ.filter (fun p : X × Y × Z => p.2.1 = a)))
  · obtain ⟨x, y, h⟩ := MaxT.PairwiseConnected3.exists_atom_z hT a
    show 0 < ∑ p ∈ univ.filter (fun p : X × Y × Z => p.2.2 = a), ν.prob p
    exact lt_of_lt_of_le (pos _ h) (Finset.single_le_sum (f := ν.prob) (fun p _ => ν.nonneg p)
      (by simp : (x, y, a) ∈ univ.filter (fun p : X × Y × Z => p.2.2 = a)))

end Occurs

/-! ### hypothesis 4 for a subsingleton group -/

section Uniform
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- hypothesis 4 of Thm 7.14 at a subsingleton embedding group (`|H| = 1`): the triple of images is
the unique point, of mass `1 = 1 / |H|²`. Applied to `H := ∀ i : Fin 1, Unit` for the built
`trivial_master_embedding`. -/
theorem hom_uniform_law_of_subsingleton [Subsingleton H] (ν : FinProb (X × Y × Z)) (σ : X → H)
    (γ : Y → H) (φ : Z → H) (a b c : H) :
    ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), ν.prob p =
      if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0 := by
  have h1 : univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)) = univ := by
    ext p; simp [Subsingleton.elim (σ p.1) a, Subsingleton.elim (γ p.2.1) b,
      Subsingleton.elim (φ p.2.2) c]
  have h2 : a + b + c = 0 := Subsingleton.elim _ _
  have h3 : Fintype.card H = 1 := Fintype.card_eq_one_iff.2 ⟨0, fun x => Subsingleton.elim _ _⟩
  rw [h1, h3, ν.sum_eq_one]; simp [h2]

end Uniform

/-! ### transport of a modest basis along subsingleton groups -/

section Transport
variable {α : Type} [Fintype α] {H H' : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  [AddCommGroup H'] [Fintype H'] [DecidableEq H'] [Subsingleton H] [Subsingleton H']

private theorem hom_char_one {G : Type} [AddCommGroup G] [Subsingleton G] (χ : AddChar G ℂ)
    (g : G) : χ g = 1 := by
  rw [Subsingleton.elim g 0, AddChar.map_zero_eq_one]

private theorem hom_char_sub (G : Type) [AddCommGroup G] [Subsingleton G] (χ χ' : AddChar G ℂ) :
    χ = χ' := by
  ext g; rw [hom_char_one χ g, hom_char_one χ' g]

/-- over a subsingleton group `Embed_σ` is the span of the constant `1`, whatever `σ`: so it does
not depend on the group. -/
theorem s7_embedSpan_eq_of_subsingleton (σ : α → H) (σ' : α → H') : embedSpan σ = embedSpan σ' := by
  have key : ∀ {G : Type} [AddCommGroup G] [Subsingleton G] (τ : α → G),
      embedSpan τ = Submodule.span ℂ {fun _ => (1 : ℂ)} := by
    intro G _ _ τ
    unfold embedSpan
    congr 1
    ext f
    constructor
    · rintro ⟨χ, rfl⟩
      funext w
      exact hom_char_one χ _
    · intro hf
      refine ⟨1, ?_⟩
      rw [hf]
      funext w
      simp
  rw [key σ, key σ']

/-- `NENM_σ` does not depend on the (subsingleton) group either. -/
theorem s7_nenm_eq_of_subsingleton (D : FinProb α) (σ : α → H) (σ' : α → H') (Sm : Finset α) :
    s7Nenm D σ Sm = s7Nenm D σ' Sm := by
  unfold s7Nenm; rw [s7_embedSpan_eq_of_subsingleton σ σ']

/-- the one field of `S7ModestBasis` that mentions the group: the embedding characters are
orthonormal (there is one character, the constant `1`, of `L²`-norm `1`). -/
theorem s7_embed_orthonormal_of_subsingleton (D : FinProb α) (σ : α → H) :
    ∀ χ χ' : AddChar H ℂ,
      D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) = if χ = χ' then 1 else 0 := by
  intro χ χ'
  have hc : χ = χ' := hom_char_sub H χ χ'
  simp only [hc, ↓reduceIte]
  simp only [hom_char_one, FinProb.cinner, FinProb.cexpect]
  simp
  exact_mod_cast D.sum_eq_one

/-- DATA: the basis `B` of Def. 7.1 for `σ : α → H`, as a basis for any `σ' : α → H'`
(`H`, `H'` subsingleton): the non-embedding and modest functions are those of `B`. -/
def S7ModestBasis.congrTrivial {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (σ' : α → H') : S7ModestBasis D σ' Sm where
  nN := B.nN
  nM := B.nM
  uN := B.uN
  uM := B.uM
  embed_orthonormal := s7_embed_orthonormal_of_subsingleton D σ'
  orthonormal_N := B.orthonormal_N
  orthonormal_M := B.orthonormal_M
  span_N := B.span_N.trans (s7_nenm_eq_of_subsingleton D σ σ' Sm)
  span_M := by
    rw [B.span_M, s7_embedSpan_eq_of_subsingleton σ σ', s7_nenm_eq_of_subsingleton D σ σ' Sm]

@[simp] theorem S7ModestBasis.congrTrivial_nN {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (σ' : α → H') : (B.congrTrivial σ').nN = B.nN := rfl

@[simp] theorem S7ModestBasis.congrTrivial_nM {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (σ' : α → H') : (B.congrTrivial σ').nM = B.nM := rfl

@[simp] theorem S7ModestBasis.congrTrivial_u_inr_inl {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (σ' : α → H') (i : Fin B.nN) :
    (B.congrTrivial σ').u (Sum.inr (Sum.inl i)) = B.u (Sum.inr (Sum.inl i)) := rfl

@[simp] theorem S7ModestBasis.congrTrivial_u_inr_inr {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (σ' : α → H') (i : Fin B.nM) :
    (B.congrTrivial σ').u (Sum.inr (Sum.inr i)) = B.u (Sum.inr (Sum.inr i)) := rfl

/-- the embedding part of the basis: every `χ ∘ σ` is the constant `1` over a subsingleton group. -/
theorem s7_basis_u_inl_of_subsingleton {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (χ : AddChar H ℂ) : B.u (Sum.inl χ) = fun _ => 1 := by
  funext a
  simp only [S7ModestBasis.u_inl]
  exact hom_char_one χ _

end Transport

/-! ### `β` is unchanged under the relabelling of the embedding part -/

section Relabel
variable {α : Type} [Fintype α] {H H' : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  [AddCommGroup H'] [Fintype H'] [DecidableEq H'] [Subsingleton H] [Subsingleton H']
  {K₁ K₂ : Type}

private def hom_lift : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → AddChar H ℂ ⊕ (K₁ ⊕ K₂) :=
  Sum.map (fun _ => 1) id

private theorem hom_coef (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (u' : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) (hu : ∀ j, u (hom_lift j) = u' j)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → α) → ℂ) (c : ι → AddChar H' ℂ ⊕ (K₁ ⊕ K₂)) :
    s7Coef D u' f c = s7Coef D u f (hom_lift ∘ c) := by
  unfold s7Coef
  congr 1
  funext x
  simp [s7Mono, hu]

private theorem hom_nedeg {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → AddChar H' ℂ ⊕ (K₁ ⊕ K₂)) : s7NeDeg (hom_lift (H := H) ∘ c) = s7NeDeg c := by
  unfold s7NeDeg s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, Function.comp]
  generalize c i = j
  rcases j with a | k <;> simp [hom_lift]

private theorem hom_effdeg {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → AddChar H' ℂ ⊕ (K₁ ⊕ K₂)) : s7EffDeg (hom_lift (H := H) ∘ c) = s7EffDeg c := by
  unfold s7EffDeg s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, Function.comp]
  generalize c i = j
  rcases j with a | k | k <;> simp [hom_lift]

private theorem hom_embdeg {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → AddChar H' ℂ ⊕ (K₁ ⊕ K₂)) (a' : AddChar H' ℂ) :
    s7EmbedDegA (1 : AddChar H ℂ) (hom_lift ∘ c) = s7EmbedDegA a' c := by
  unfold s7EmbedDegA s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, Function.comp]
  generalize c i = j
  rcases j with a | k | k
  · simp [hom_lift, hom_char_sub H' a a']
  · simp [hom_lift]
  · simp [hom_lift]
  
private theorem hom_fp_sub (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (u' : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) (hu : ∀ j, u (hom_lift j) = u' j) (n d d' : ℕ) :
    s7ClassFp D u n d d' ⊆ s7ClassFp D u' n d d' := by
  rintro f ⟨⟨Dtot, Da, hsum, hDa⟩, hne, heff⟩
  refine ⟨⟨Dtot, fun _ => Dtot, ?_, ?_⟩, ?_, ?_⟩
  · have : Fintype.card (AddChar H' ℂ) = 1 :=
      Fintype.card_eq_one_iff.2 ⟨1, fun x => hom_char_sub H' _ _⟩
    simp [this]
  · intro c hc a'
    rw [hom_coef D u u' hu] at hc
    have h1 := hDa _ hc 1
    have h2 : Da 1 = Dtot := by
      rw [← hsum]
      have : (Finset.univ : Finset (AddChar H ℂ)) = {1} := by
        ext x; simp [hom_char_sub H x 1]
      rw [this]; simp
    rw [← hom_embdeg (H := H) c a', h1, h2]
  · intro c hc
    rw [hom_coef D u u' hu] at hc
    rw [← hom_nedeg (H := H) c]
    exact hne _ hc
  · intro c hc
    rw [hom_coef D u u' hu] at hc
    rw [← hom_effdeg (H := H) c]
    exact heff _ hc


private theorem hom_g_sub (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (u' : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) (hu : ∀ j, u (hom_lift j) = u' j) (n : ℕ) :
    s7ClassG D u n ⊆ s7ClassG D u' n := by
  rintro f ⟨⟨Dtot, Da, hsum, hDa⟩, d, hne⟩
  refine ⟨⟨Dtot, fun _ => Dtot, ?_, ?_⟩, d, ?_⟩
  · have : Fintype.card (AddChar H' ℂ) = 1 :=
      Fintype.card_eq_one_iff.2 ⟨1, fun x => hom_char_sub H' _ _⟩
    simp [this]
  · intro c hc a'
    rw [hom_coef D u u' hu] at hc
    have h1 := hDa _ hc 1
    have h2 : Da 1 = Dtot := by
      rw [← hsum]
      have : (Finset.univ : Finset (AddChar H ℂ)) = {1} := by
        ext x; simp [hom_char_sub H x 1]
      rw [this]; simp
    rw [← hom_embdeg (H := H) c a', h1, h2]
  · intro c hc
    rw [hom_coef D u u' hu] at hc
    rw [← hom_nedeg (H := H) c]
    exact hne _ hc


/-- the classes `F'_{n,d,d'}` only see the family `u`: relabel `AddChar H ℂ` to `AddChar H' ℂ`
(both are singletons). Hypotheses: the embedding part and the other parts agree. -/
theorem s7_classFp_relabel (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (u' : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (hinl : ∀ (χ : AddChar H ℂ) (χ' : AddChar H' ℂ), u' (Sum.inl χ') = u (Sum.inl χ))
    (hinr : ∀ k : K₁ ⊕ K₂, u' (Sum.inr k) = u (Sum.inr k)) (n d d' : ℕ) :
    s7ClassFp D u' n d d' = s7ClassFp D u n d d' := by
  have hu : ∀ j, u (hom_lift j) = u' j := by
    rintro (a | k)
    · exact (hinl 1 a).symm
    · exact (hinr k).symm
  have hu' : ∀ j, u' (hom_lift j) = u j := by
    rintro (a | k)
    · exact hinl a 1
    · exact hinr k
  exact Set.Subset.antisymm (hom_fp_sub D u' u hu' n d d') (hom_fp_sub D u u' hu n d d')

/-- the same for `G_n`, `H_n`. -/
theorem s7_classG_relabel (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (u' : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (hinl : ∀ (χ : AddChar H ℂ) (χ' : AddChar H' ℂ), u' (Sum.inl χ') = u (Sum.inl χ))
    (hinr : ∀ k : K₁ ⊕ K₂, u' (Sum.inr k) = u (Sum.inr k)) (n : ℕ) :
    s7ClassG D u' n = s7ClassG D u n := by
  have hu : ∀ j, u (hom_lift j) = u' j := by
    rintro (a | k)
    · exact (hinl 1 a).symm
    · exact (hinr k).symm
  have hu' : ∀ j, u' (hom_lift j) = u j := by
    rintro (a | k)
    · exact hinl a 1
    · exact hinr k
  exact Set.Subset.antisymm (hom_g_sub D u' u hu' n) (hom_g_sub D u u' hu n)

end Relabel

section BetaRelabel
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H H' : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  [AddCommGroup H'] [Fintype H'] [DecidableEq H'] [Subsingleton H] [Subsingleton H']
  {K₁ K₂ K₃ K₄ K₅ K₆ : Type}

/-- `β_{n,d,d'}` is unchanged when the three families are relabelled along two subsingleton
embedding groups. -/
theorem s7Beta_relabel (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) (ux' : AddChar H' ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uy' : AddChar H' ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ)
    (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ) (uz' : AddChar H' ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (hx1 : ∀ (χ : AddChar H ℂ) (χ' : AddChar H' ℂ), ux' (Sum.inl χ') = ux (Sum.inl χ))
    (hx2 : ∀ k, ux' (Sum.inr k) = ux (Sum.inr k))
    (hy1 : ∀ (χ : AddChar H ℂ) (χ' : AddChar H' ℂ), uy' (Sum.inl χ') = uy (Sum.inl χ))
    (hy2 : ∀ k, uy' (Sum.inr k) = uy (Sum.inr k))
    (hz1 : ∀ (χ : AddChar H ℂ) (χ' : AddChar H' ℂ), uz' (Sum.inl χ') = uz (Sum.inl χ))
    (hz2 : ∀ k, uz' (Sum.inr k) = uz (Sum.inr k)) (n d d' : ℕ) :
    s7Beta μ hμ ux' uy' uz' n d d' = s7Beta μ hμ ux uy uz n d d' := by
  have hF : s7ClassF μ hμ ux' n d d' = s7ClassF μ hμ ux n d d' := by
    ext F
    rw [s7_mem_classF_iff, s7_mem_classF_iff, s7_classFp_relabel (lawX μ) ux ux' hx1 hx2 n d d']
  unfold s7Beta
  rw [hF, s7_classG_relabel (lawY μ) uy uy' hy1 hy2 n, s7_classG_relabel (lawZ μ) uz uz' hz1 hz2 n]

/-- the consumer form: for bases `Bx, By, Bz` over subsingleton groups, the transported
bases give the same `β`. -/
theorem s7Beta_congrTrivial (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X}
    (Bx : S7ModestBasis (lawX μ) σ Sm) (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
    (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (σ' : X → H') (γ' : Y → H') (φ' : Z → H')
    (n d d' : ℕ) :
    s7Beta μ hμ (Bx.congrTrivial σ').u (By.congrTrivial γ').u (Bz.congrTrivial φ').u n d d' =
      s7Beta μ hμ Bx.u By.u Bz.u n d d' := by
  refine s7Beta_relabel μ hμ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ n d d'
  · intro χ χ'
    exact (s7_basis_u_inl_of_subsingleton _ χ').trans (s7_basis_u_inl_of_subsingleton _ χ).symm
  · rintro (i | i) <;> rfl
  · intro χ χ'
    exact (s7_basis_u_inl_of_subsingleton _ χ').trans (s7_basis_u_inl_of_subsingleton _ χ).symm
  · rintro (i | i) <;> rfl
  · intro χ χ'
    exact (s7_basis_u_inl_of_subsingleton _ χ').trans (s7_basis_u_inl_of_subsingleton _ χ).symm
  · rintro (i | i) <;> rfl

end BetaRelabel

end TrackB
end RestrictedPolynomials
end
