module

public import RestrictedPolynomials.TrackB.MasterEmbedding
public import RestrictedPolynomials.TrackB.NoiseChains
public import RestrictedPolynomials.TrackB.MarkovBlocks

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section S7Basis
variable {α : Type} [Fintype α]

/-- `V^⊥` in `L²(D)`, as a submodule (`⟨g, v⟩ = 𝔼_D g · conj v`). -/
def s7Perp (D : FinProb α) (V : Submodule ℂ (α → ℂ)) : Submodule ℂ (α → ℂ) where
  carrier := {g | ∀ v ∈ V, D.cinner g v = 0}
  add_mem' := by
    intro f g hf hg v hv
    simp only [FinProb.cinner, FinProb.cexpect] at *
    have := hf v hv
    have := hg v hv
    simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at *
    simp_all
  zero_mem' := by
    intro v _
    simp [FinProb.cinner, FinProb.cexpect]
  smul_mem' := by
    intro c f hf v hv
    have h := hf v hv
    simp only [FinProb.cinner, FinProb.cexpect] at *
    simp only [Pi.smul_apply, smul_eq_mul]
    have : ∑ a, (D.prob a : ℂ) * (c * f a * star (v a)) =
        c * ∑ a, (D.prob a : ℂ) * (f a * star (v a)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, h, mul_zero]

/-- the functions `f : Σ → ℂ` that are constant on `Sm` (`f|_{Σ_modest}` constant). -/
def s7ConstOn (Sm : Finset α) : Submodule ℂ (α → ℂ) where
  carrier := {g | ∀ a ∈ Sm, ∀ b ∈ Sm, g a = g b}
  add_mem' := fun ha hb a h1 b h2 => by simp [ha a h1 b h2, hb a h1 b h2]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c g hg a h1 b h2 => by simp [hg a h1 b h2]

open scoped Classical in
/-- `L²(D)`-orthonormal basis: orthonormal family spanning all functions
(paper IV l. 4157-4173, Def. C.1 l. 9396). -/
def S7IsONB {J : Type} (D : FinProb α) (u : J → α → ℂ) : Prop :=
  (∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) ∧ Submodule.span ℂ (Set.range u) = ⊤

variable {H : Type} [AddCommGroup H] [Fintype H]

/-- `NENM_σ(μ) = {f : f ∈ Embed_σ(μ)^⊥, f|_{Σ_modest} constant}` (Def. 7.1(2), l. 4164-4168),
orthogonality in `L²(D)`, `D = μ_x`. -/
def s7Nenm (D : FinProb α) (σ : α → H) (Sm : Finset α) : Submodule ℂ (α → ℂ) :=
  s7Perp D (embedSpan σ) ⊓ s7ConstOn Sm

/-- Paper IV `definition-modest-basis` (Def. 7.1, l. 4157-4173): the *chosen* orthonormal bases of the
source ("Pick ..."), as data with their defining properties. `B_embed = {χ∘σ : χ ∈ Ĥ}` is
indexed by `Ĥ` and required orthonormal; `B_non-embed = uN` spans `NENM_σ`; `B_modest = uM`
spans `NENM^⊥ ∩ Embed^⊥`. -/
structure S7ModestBasis (D : FinProb α) (σ : α → H) (Sm : Finset α) where
  nN : ℕ
  nM : ℕ
  uN : Fin nN → α → ℂ
  uM : Fin nM → α → ℂ
  embed_orthonormal : ∀ χ χ' : AddChar H ℂ,
    D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) = if χ = χ' then 1 else 0
  orthonormal_N : ∀ i j, D.cinner (uN i) (uN j) = if i = j then 1 else 0
  orthonormal_M : ∀ i j, D.cinner (uM i) (uM j) = if i = j then 1 else 0
  span_N : Submodule.span ℂ (Set.range uN) = s7Nenm D σ Sm
  span_M : Submodule.span ℂ (Set.range uM) = s7Perp D (embedSpan σ) ⊓ s7Perp D (s7Nenm D σ Sm)

/-- the index set of `B_embed ∪ B_non-embed ∪ B_modest`: `Ĥ ⊕ (Fin nN ⊕ Fin nM)`. -/
abbrev S7ModestBasis.J {D : FinProb α} {σ : α → H} {Sm : Finset α} (B : S7ModestBasis D σ Sm) :
    Type :=
  AddChar H ℂ ⊕ (Fin B.nN ⊕ Fin B.nM)

/-- the functions of the basis: `inl χ ↦ χ∘σ`, `inr (inl i) ↦ uN i`, `inr (inr i) ↦ uM i`. -/
def S7ModestBasis.u {D : FinProb α} {σ : α → H} {Sm : Finset α} (B : S7ModestBasis D σ Sm) :
    B.J → α → ℂ :=
  Sum.elim (fun χ a => χ (σ a)) (Sum.elim B.uN B.uM)

@[simp] theorem S7ModestBasis.u_inl {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (χ : AddChar H ℂ) : B.u (Sum.inl χ) = fun a => χ (σ a) := rfl
@[simp] theorem S7ModestBasis.u_inr_inl {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (i : Fin B.nN) : B.u (Sum.inr (Sum.inl i)) = B.uN i := rfl
@[simp] theorem S7ModestBasis.u_inr_inr {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (i : Fin B.nM) : B.u (Sum.inr (Sum.inr i)) = B.uM i := rfl

section Monomials
variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : Type}

/-- the monomial `χ(x) = ∏ᵢ χᵢ(xᵢ)` of `c : ι → J` (paper IV `definition-modest-monomial`, l. 4184-4187;
`definition-monomial-basis`, l. 2415-2419). -/
def s7Mono (u : J → α → ℂ) (c : ι → J) : (ι → α) → ℂ := fun x => ∏ i, u (c i) (x i)

/-- `f̂(χ) = ⟨f, χ⟩` in `L²(D^{⊗ι})` (l. 4177-4183). -/
def s7Coef (D : FinProb α) (u : J → α → ℂ) (f : (ι → α) → ℂ) (c : ι → J) : ℂ :=
  (D.pi ι).cinner f (s7Mono u c)

/-- `#{i : P (c i)}`: the common shape of all degrees of Def. 7.3 and Def. C.1. -/
def s7CountWhere (P : J → Prop) (c : ι → J) : ℕ := Set.ncard {i | P (c i)}

@[simp] theorem s7Mono_apply (u : J → α → ℂ) (c : ι → J) (x : ι → α) :
    s7Mono u c x = ∏ i, u (c i) (x i) := rfl

/-- `⟨f, χ⟩` unfolded. -/
theorem s7Coef_def (D : FinProb α) (u : J → α → ℂ) (f : (ι → α) → ℂ) (c : ι → J) :
    s7Coef D u f c = ∑ x, ((D.pi ι).prob x : ℂ) * (f x * star (s7Mono u c x)) := rfl

/-- Def. C.1 (l. 9396-9407): degree of `c` with respect to the block `{j : blk j = b}`. -/
def s7BlockDeg {K : Type} (blk : J → K) (b : K) (c : ι → J) : ℕ :=
  s7CountWhere (fun j => blk j = b) c

/-- Def. C.1: `f` is degree-`d` homogeneous with respect to the block `b`. -/
def S7HomWrtBlock {K : Type} (D : FinProb α) (u : J → α → ℂ) (blk : J → K) (b : K)
    (f : (ι → α) → ℂ) (d : ℕ) : Prop :=
  ∀ c : ι → J, s7Coef D u f c ≠ 0 → s7BlockDeg blk b c = d

end Monomials

section Degrees
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K₁ K₂ : Type}

/-- `embeddeg_a(χ)`: number of coordinates `i` with `χᵢ = a` (Def. 7.3(1), l. 4193). -/
def s7EmbedDegA (a : AddChar H ℂ) (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) : ℕ :=
  s7CountWhere (fun j => j = Sum.inl a) c

/-- `embeddeg(χ)`: number of coordinates in `B_embed` (Def. 7.3(2), l. 4194). -/
def s7EmbedDeg (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) : ℕ :=
  s7CountWhere (fun j => ∃ a, j = Sum.inl a) c

/-- `nedeg(χ)`: number of coordinates outside `B_embed` (Def. 4.4 and Def. 7.3(3), l. 2422, 4196). -/
def s7NeDeg (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) : ℕ :=
  s7CountWhere (fun j => ¬ ∃ a, j = Sum.inl a) c

/-- `effnon(χ)`: number of coordinates in `B_modest` (Def. 7.3(4), l. 4198). -/
def s7EffDeg (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) : ℕ :=
  s7CountWhere (fun j => ∃ m : K₂, j = Sum.inr (Sum.inr m)) c

variable (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)

/-- completely embedding homogeneous of degree `Dtot` (Def. l. 4288-4295). -/
def S7CompEmbedHom (f : (ι → α) → ℂ) (Dtot : ℕ) : Prop :=
  ∃ Da : AddChar H ℂ → ℕ, ∑ a, Da a = Dtot ∧
    ∀ c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7Coef D u f c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a

/-- non-embedding homogeneous of non-embedding degree `d` (l. 4297-4302). -/
def S7NeHom (f : (ι → α) → ℂ) (d : ℕ) : Prop :=
  ∀ c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7Coef D u f c ≠ 0 → s7NeDeg c = d

/-- effective non-embedding degree at least `d'` (l. 4304-4307). -/
def S7EffDegGE (f : (ι → α) → ℂ) (d' : ℕ) : Prop :=
  ∀ c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7Coef D u f c ≠ 0 → d' ≤ s7EffDeg c

/-- `F'_{n,d,d'}` (Def. l. 4315-4319, item 1). -/
def s7ClassFp (n d d' : ℕ) : Set ((Fin n → α) → ℂ) :=
  {f | (∃ Dtot, S7CompEmbedHom D u f Dtot) ∧ S7NeHom D u f d ∧ S7EffDegGE D u f d'}

/-- `G_n`, `H_n` (items 2, 3): completely embedding homogeneous and non-embedding homogeneous,
with respect to the basis `u` of the `y`- (resp. `z`-) alphabet. -/
def s7ClassG (n : ℕ) : Set ((Fin n → α) → ℂ) :=
  {f | (∃ Dtot, S7CompEmbedHom D u f Dtot) ∧ ∃ d, S7NeHom D u f d}

end Degrees

/-! ### Theorems of file 1 (targets) -/

section Thms
variable {α : Type} [Fintype α] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private lemma cinner_sub_left' {β : Type*} [Fintype β] (π : FinProb β) (f g h : β → ℂ) :
    π.cinner (f - g) h = π.cinner f h - π.cinner g h := by
  have : f - g = f + (-1 : ℂ) • g := by ext x; simp [sub_eq_add_neg]
  rw [this, cinner_add_left, cinner_smul_left]; ring

private lemma wt_perp_decomp (D : FinProb α) (hD : ∀ a, 0 < D.prob a)
    (V : Submodule ℂ (α → ℂ)) (g : α → ℂ) : ∃ v ∈ V, ∃ w ∈ s7Perp D V, v + w = g := by
  classical
  let _ := wtCore D hD
  let _ : NormedAddCommGroup (Wt D) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ (Wt D) := InnerProductSpace.ofCore _
  let V' : Submodule ℂ (Wt D) := V
  have hmem : ∀ g : Wt D, g ∈ V'ᗮ ↔ (g : α → ℂ) ∈ s7Perp D V := fun g => by
    rw [Submodule.mem_orthogonal]; exact Iff.rfl
  let x : Wt D := g
  have hPx : V'.starProjection x ∈ V' := Submodule.starProjection_apply_mem V' x
  have hw : x - V'.starProjection x ∈ V'ᗮ := Submodule.sub_starProjection_mem_orthogonal x
  refine ⟨(V'.starProjection x : α → ℂ), hPx, ((x - V'.starProjection x : Wt D) : α → ℂ),
    (hmem _).1 hw, ?_⟩
  exact add_sub_cancel (V'.starProjection x) x

private lemma wt_perp_sup (D : FinProb α) (hD : ∀ a, 0 < D.prob a)
    (V : Submodule ℂ (α → ℂ)) : V ⊔ s7Perp D V = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨v, hv, w, hw, rfl⟩ := wt_perp_decomp D hD V g
  exact Submodule.add_mem_sup hv hw

private lemma exists_onb (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (W : Submodule ℂ (α → ℂ)) :
    ∃ (n : ℕ) (u : Fin n → α → ℂ),
      (∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) ∧
        Submodule.span ℂ (Set.range u) = W := by
  classical
  let _ := wtCore D hD
  let _ : NormedAddCommGroup (Wt D) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ (Wt D) := InnerProductSpace.ofCore _
  have hinner : ∀ x y : Wt D, inner ℂ x y = D.cinner (y : α → ℂ) (x : α → ℂ) := fun x y => rfl
  let W' : Submodule ℂ (Wt D) := W
  let b := stdOrthonormalBasis ℂ W'
  let e : Wt D → α → ℂ := fun x => x
  refine ⟨Module.finrank ℂ W', fun i => e ((b i : W') : Wt D), ?_, ?_⟩
  · intro i j
    have h := orthonormal_iff_ite.1 b.orthonormal j i
    rw [Submodule.coe_inner, hinner] at h
    show D.cinner ((b i : W') : Wt D) ((b j : W') : Wt D) = _
    rw [h]
    simp [eq_comm]
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (b i).2
    · intro w hw
      have h := b.sum_repr' (⟨w, hw⟩ : W')
      have h2 : (⟨w, hw⟩ : W') = ∑ i, inner ℂ (b i) (⟨w, hw⟩ : W') • b i := h.symm
      let w' : Wt D := w
      have h3 : w' = ∑ i, inner ℂ ((b i : W') : Wt D) w' • ((b i : W') : Wt D) := by
        have := congrArg (fun x : W' => (x : Wt D)) h2
        simpa [Submodule.coe_inner] using this
      have h4 : w = ∑ i, D.cinner w (e ((b i : W') : Wt D)) • e ((b i : W') : Wt D) := h3
      rw [h4]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma embed_le_constOn (σ : α → H) (Sm : Finset α)
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') : embedSpan σ ≤ s7ConstOn Sm := by
  rw [embedSpan, Submodule.span_le]
  rintro _ ⟨χ, rfl⟩ a ha b hb
  simp [hconst a ha b hb]

/-- the orthogonal projection onto `Embed_σ`, from an orthonormal family of characters -/
private def embedProj (D : FinProb α) (σ : α → H) (g : α → ℂ) : α → ℂ :=
  ∑ χ : AddChar H ℂ, D.cinner g (fun a => χ (σ a)) • (fun a => χ (σ a))

private lemma embedProj_mem (D : FinProb α) (σ : α → H) (g : α → ℂ) :
    embedProj D σ g ∈ embedSpan σ :=
  Submodule.sum_mem _ fun χ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)

private lemma sub_embedProj_mem_perp (D : FinProb α) (σ : α → H)
    (hort : ∀ χ χ' : AddChar H ℂ,
      D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) = if χ = χ' then 1 else 0)
    (g : α → ℂ) : g - embedProj D σ g ∈ s7Perp D (embedSpan σ) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨χ', rfl⟩ := hv
    rw [cinner_sub_left']
    unfold embedProj
    rw [cinner_sum_left, Finset.sum_eq_single χ']
    · rw [cinner_smul_left, hort]; simp
    · intro χ _ hχ; rw [cinner_smul_left, hort]; simp [hχ]
    · simp
  | zero => exact cinner_zero_right _ _
  | add x y _ _ hx hy => rw [cinner_add_right, hx, hy]; simp
  | smul a x _ hx => rw [cinner_smul_right, hx]; simp

private lemma embedProj_constOn (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') (g : α → ℂ) :
    embedProj D σ g ∈ s7ConstOn Sm :=
  embed_le_constOn σ Sm hconst (embedProj_mem D σ g)

private lemma sub_embedProj_mem_nenm (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (hort : ∀ χ χ' : AddChar H ℂ,
      D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) = if χ = χ' then 1 else 0)
    (g : α → ℂ) (hg : g ∈ s7ConstOn Sm) : g - embedProj D σ g ∈ s7Nenm D σ Sm :=
  ⟨sub_embedProj_mem_perp D σ hort g, Submodule.sub_mem _ hg (embedProj_constOn D σ Sm hconst g)⟩

/-- Paper IV `claim-constant-on-modest-span` (l. 4253-4258): `span(B_embed ∪ B_non-embed)` is the space of
functions constant on `Σ_modest`; needs item 1 of the relaxed base case (`σ` constant on `Sm`). -/
theorem s7_embed_sup_nenm_eq_constOn (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') (B : S7ModestBasis D σ Sm) :
    embedSpan σ ⊔ s7Nenm D σ Sm = s7ConstOn Sm := by
  apply le_antisymm
  · exact sup_le (embed_le_constOn σ Sm hconst) inf_le_right
  · intro f hf
    refine Submodule.mem_sup.2 ⟨embedProj D σ f, embedProj_mem D σ f, f - embedProj D σ f,
      sub_embedProj_mem_nenm D σ Sm hconst B.embed_orthonormal f hf, by abel⟩

/-- the same, in the form used by `lem:effective-noise`: every element of `B_embed ∪ B_non-embed`
is constant on `Sm`. -/
theorem s7_basis_embed_nenm_constOn (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') (B : S7ModestBasis D σ Sm)
    (j : B.J) (hj : ¬ ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) : B.u j ∈ s7ConstOn Sm := by
  rcases j with χ | k | k
  · exact embed_le_constOn σ Sm hconst (Submodule.subset_span ⟨χ, rfl⟩)
  · have : B.uN k ∈ s7Nenm D σ Sm := by
      rw [← B.span_N]; exact Submodule.subset_span ⟨k, rfl⟩
    exact this.2
  · exact absurd ⟨k, rfl⟩ hj

private lemma embed_orthonormal_of_unif (D : FinProb α) (σ : α → H)
    (hx : ∀ h : H, ∑ a ∈ univ.filter (fun a => σ a = h), D.prob a = 1 / (Fintype.card H : ℝ))
    (χ χ' : AddChar H ℂ) :
    D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) = if χ = χ' then 1 else 0 := by
  have h1 : D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) =
      ∑ h : H, ((1 / (Fintype.card H : ℝ) : ℝ) : ℂ) * (χ h * star (χ' h)) := by
    rw [cinner_def, ← Finset.sum_fiberwise (univ : Finset α) σ]
    refine Finset.sum_congr rfl fun h _ => ?_
    have : ∀ a ∈ univ.filter (fun a => σ a = h),
        (D.prob a : ℂ) * (χ (σ a) * star (χ' (σ a))) = (D.prob a : ℂ) * (χ h * star (χ' h)) := by
      intro a ha
      rw [(Finset.mem_filter.1 ha).2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Complex.ofReal_sum, hx h]
  have h2 := AddChar.wInner_cWeight_eq_boole (G := H) (R := ℂ) χ' χ
  rw [RCLike.wInner_cWeight_eq_expect] at h2
  simp only [RCLike.inner_apply, Fintype.expect_eq_sum_div_card] at h2
  rw [h1]
  have h3 : ∑ h : H, ((1 / (Fintype.card H : ℝ) : ℝ) : ℂ) * (χ h * star (χ' h)) =
      (∑ h : H, χ h * (starRingEnd ℂ) (χ' h)) / (Fintype.card H : ℂ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [div_eq_mul_inv, mul_comm]
  rw [h3, h2]
  by_cases hc : χ = χ'
  · simp [hc]
  · simp [hc, Ne.symm hc]

private lemma modest_orthonormal (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B : S7ModestBasis D σ Sm) (i j : B.J) :
    D.cinner (B.u i) (B.u j) = if i = j then 1 else 0 := by
  have orth : ∀ (g v : α → ℂ) (V : Submodule ℂ (α → ℂ)), g ∈ s7Perp D V → v ∈ V →
      D.cinner g v = 0 := fun g v V hg hv => hg v hv
  have orth' : ∀ (g v : α → ℂ) (V : Submodule ℂ (α → ℂ)), g ∈ s7Perp D V → v ∈ V →
      D.cinner v g = 0 := by
    intro g v V hg hv
    rw [cinner_comm, orth g v V hg hv]; simp
  have hNmem : ∀ k : Fin B.nN, B.uN k ∈ s7Nenm D σ Sm := fun k => by
    rw [← B.span_N]; exact Submodule.subset_span ⟨k, rfl⟩
  have hMmem : ∀ k : Fin B.nM, B.uM k ∈ s7Perp D (embedSpan σ) ⊓ s7Perp D (s7Nenm D σ Sm) :=
    fun k => by
      rw [← B.span_M]; exact Submodule.subset_span ⟨k, rfl⟩
  have hNE : ∀ k : Fin B.nN, B.uN k ∈ s7Perp D (embedSpan σ) := fun k => (hNmem k).1
  have hME : ∀ k : Fin B.nM, B.uM k ∈ s7Perp D (embedSpan σ) := fun k => (hMmem k).1
  have hMN : ∀ k : Fin B.nM, B.uM k ∈ s7Perp D (s7Nenm D σ Sm) := fun k => (hMmem k).2
  have hEmem : ∀ χ : AddChar H ℂ, (fun a => χ (σ a)) ∈ embedSpan σ := fun χ =>
    Submodule.subset_span ⟨χ, rfl⟩
  rcases i with χ | k | k <;> rcases j with χ' | k' | k'
  · show D.cinner (fun a => χ (σ a)) (fun a => χ' (σ a)) = _
    rw [B.embed_orthonormal]; simp
  · show D.cinner (fun a => χ (σ a)) (B.uN k') = _
    rw [orth' _ _ _ (hNE k') (hEmem χ)]; simp
  · show D.cinner (fun a => χ (σ a)) (B.uM k') = _
    rw [orth' _ _ _ (hME k') (hEmem χ)]; simp
  · show D.cinner (B.uN k) (fun a => χ' (σ a)) = _
    rw [orth _ _ _ (hNE k) (hEmem χ')]; simp
  · show D.cinner (B.uN k) (B.uN k') = _
    rw [B.orthonormal_N]; simp
  · show D.cinner (B.uN k) (B.uM k') = _
    rw [orth' _ _ _ (hMN k') (hNmem k)]; simp
  · show D.cinner (B.uM k) (fun a => χ' (σ a)) = _
    rw [orth _ _ _ (hME k) (hEmem χ')]; simp
  · show D.cinner (B.uM k) (B.uN k') = _
    rw [orth _ _ _ (hMN k) (hNmem k')]; simp
  · show D.cinner (B.uM k) (B.uM k') = _
    rw [B.orthonormal_M]; simp

/-- Well-definedness of `S7ModestBasis`: the choices of Def. 7.1 exist (Gram-Schmidt on the finite
dimensional spaces `NENM` and `NENM^⊥ ∩ Embed^⊥`), once `σ_*μ_x` is uniform on `H`
(hypothesis 4 of the relaxed theorem; `embed_characters_orthonormal`). The provers prove this. -/
theorem s7_exists_modestBasis (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a)
    (hx : ∀ h : H, ∑ a ∈ univ.filter (fun a => σ a = h), D.prob a = 1 / (Fintype.card H : ℝ)) :
    Nonempty (S7ModestBasis D σ Sm) := by
  classical
  obtain ⟨nN, uN, hN1, hN2⟩ := exists_onb D hD (s7Nenm D σ Sm)
  obtain ⟨nM, uM, hM1, hM2⟩ :=
    exists_onb D hD (s7Perp D (embedSpan σ) ⊓ s7Perp D (s7Nenm D σ Sm))
  exact ⟨⟨nN, nM, uN, uM, embed_orthonormal_of_unif D σ hx, hN1, hM1, hN2, hM2⟩⟩

/-- `B_embed ∪ B_non-embed ∪ B_modest` is an orthonormal basis of `L²(Σ; μ_x)` (Def. 7.1). -/
theorem s7_modestBasis_isONB (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) : S7IsONB D B.u := by
  classical
  refine ⟨fun i j => by convert modest_orthonormal D σ Sm B i j, ?_⟩
  have hr : Set.range B.u = Set.range (fun χ : AddChar H ℂ => fun a => χ (σ a)) ∪
      (Set.range B.uN ∪ Set.range B.uM) := by
    unfold S7ModestBasis.u; rw [Set.Sum.elim_range, Set.Sum.elim_range]
  rw [hr, Submodule.span_union, Submodule.span_union, B.span_N, B.span_M]
  change embedSpan σ ⊔ (s7Nenm D σ Sm ⊔
    (s7Perp D (embedSpan σ) ⊓ s7Perp D (s7Nenm D σ Sm))) = ⊤
  rw [eq_top_iff]
  intro g _
  obtain ⟨v, hv, w, hw, rfl⟩ := wt_perp_decomp D hD (embedSpan σ) g
  obtain ⟨n, hn, p, hp, rfl⟩ := wt_perp_decomp D hD (s7Nenm D σ Sm) w
  apply Submodule.add_mem _ (Submodule.mem_sup_left hv)
  apply Submodule.mem_sup_right
  refine Submodule.add_mem_sup hn ⟨?_, hp⟩
  have : p = (n + p) - n := by abel
  rw [this]
  exact Submodule.sub_mem _ hw hn.1

/-- the three parts are mutually orthogonal (so the whole family is orthonormal). -/
theorem s7_modestBasis_orthonormal (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B : S7ModestBasis D σ Sm) (i j : B.J) :
    D.cinner (B.u i) (B.u j) = if i = j then 1 else 0 := by
  exact modest_orthonormal D σ Sm B i j

/-- `B_modest` vanishes off `Σ_modest`. This is the by-product of the printed proof of Lemma 7.5
(P4 l. 4248-4255) at points `x ∉ Σ_modest`: there the modest chain stays at `x`, `p = 1_x`, `p/μ_x`
vanishes on `Σ_modest`, hence is constant there, hence lies in `span(B_embed ∪ B_non-embed)` (this
uses item 1 of the relaxed base case, `σ` constant on `Σ_modest`), hence is orthogonal to `B_modest`,
and the pairing `⟨χ, p/μ_x⟩ = χ(x)` is `0`. The printed proof displays only the case `x ∈ Σ_modest`
(`p(a) = μ_x(a)/μ_x(Σ_modest)`) and never states the vanishing, which the eigenvalue identity at
`x ∉ Σ_modest` and Fact 7.8 use (an omitted case in the source). Hand proof: for `g` supported off `Sm`,
`g - P_embed g ∈ NENM` (as `σ` is constant on `Sm`) and `B_modest ⊥ NENM ⊔ Embed`. -/
theorem s7_basis_modest_vanish_outside (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) (m : Fin B.nM) (a : α) (ha : a ∉ Sm) : B.uM m a = 0 := by
  classical
  have hm : B.uM m ∈ s7Perp D (embedSpan σ) ⊓ s7Perp D (s7Nenm D σ Sm) := by
    rw [← B.span_M]; exact Submodule.subset_span ⟨m, rfl⟩
  let g : α → ℂ := fun b => if b = a then 1 else 0
  have hg : g ∈ s7ConstOn Sm := fun x hx y hy => by
    have hx' : x ≠ a := fun h => ha (h ▸ hx)
    have hy' : y ≠ a := fun h => ha (h ▸ hy)
    simp [g, hx', hy']
  have hN := sub_embedProj_mem_nenm D σ Sm hconst B.embed_orthonormal g hg
  have h1 : D.cinner (B.uM m) (g - embedProj D σ g) = 0 := hm.2 _ hN
  have h2 : D.cinner (B.uM m) (embedProj D σ g) = 0 := hm.1 _ (embedProj_mem D σ g)
  have e : embedProj D σ g + (g - embedProj D σ g) = g := by abel
  have h3 : D.cinner (B.uM m) g = 0 := by
    have := cinner_add_right D (B.uM m) (embedProj D σ g) (g - embedProj D σ g)
    rw [e, h1, h2] at this
    simpa using this
  have h4 : D.cinner (B.uM m) g = (D.prob a : ℂ) * B.uM m a := by
    simp [cinner_def, g]
  rw [h4] at h3
  exact (mul_eq_zero.1 h3).resolve_left (by exact_mod_cast (hD a).ne')

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : Type}

/-- monomials of an orthonormal family are orthonormal (the classical tensor-product orthonormal basis fact). -/
theorem s7_mono_orthonormal (D : FinProb α) (u : J → α → ℂ) [DecidableEq J]
    (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) (c c' : ι → J) :
    (D.pi ι).cinner (s7Mono u c) (s7Mono u c') = if c = c' then 1 else 0 := by
  classical
  show (D.pi ι).cinner (fun x => ∏ i, u (c i) (x i)) (fun x => ∏ i, u (c' i) (x i)) = _
  rw [cinner_pi_prod D (fun i => u (c i)) (fun i => u (c' i))]
  by_cases h : c = c'
  · subst h; simp [hu]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    simp [h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hu]; simp [hi])

private lemma cinner_sum_smul_sum {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    (π : FinProb β) (m : γ → β → ℂ)
    (hm : ∀ c c', π.cinner (m c) (m c') = if c = c' then 1 else 0) (a b : γ → ℂ) :
    π.cinner (∑ c, a c • m c) (∑ c, b c • m c) = ∑ c, a c * star (b c) := by
  rw [cinner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [cinner_smul_right, hm]; simp
  · intro c' _ hc'; rw [cinner_smul_right, hm]; simp [Ne.symm hc']
  · simp

/-- Paper IV `definition-monomial-basis#fourier-expansion`: `f = ∑_χ f̂(χ) χ` over the monomials of an
orthonormal basis of `L²(D)` (needs `D` of full support, which holds for `μ_x`). -/
theorem s7_fourier_expansion (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (u : J → α → ℂ)
    [Fintype J] (hu : S7IsONB D u) (f : (ι → α) → ℂ) :
    f = ∑ c : ι → J, s7Coef D u f c • s7Mono u c := by
  classical
  have _ := hD
  have hm := s7_mono_orthonormal (ι := ι) D u hu.1
  have hadd : ∀ (x y : (ι → α) → ℂ) (c : ι → J), s7Coef D u (x + y) c = s7Coef D u x c + s7Coef D u y c :=
    fun x y c => cinner_add_left _ _ _ _
  have hsmul : ∀ (a : ℂ) (x : (ι → α) → ℂ) (c : ι → J), s7Coef D u (a • x) c = a * s7Coef D u x c :=
    fun a x c => cinner_smul_left _ _ _ _
  have key : ∀ g ∈ Submodule.span ℂ (Set.range (s7Mono (ι := ι) u)),
      g = ∑ c, s7Coef D u g c • s7Mono u c := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨c0, rfl⟩ := hg
      simp only [s7Coef, hm]
      simp
    | zero => simp [s7Coef, cinner_zero_left]
    | add x y _ _ hx hy =>
      simp only [hadd, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul a x _ hx =>
      simp only [hsmul, mul_smul, ← Finset.smul_sum]
      rw [← hx]
  apply key
  -- every function is in the span of the monomials
  have hb : ∀ a : α, ∃ b : J → ℂ, ∑ j, b j • u j = fun z => if a = z then (1 : ℂ) else 0 := by
    intro a
    have : (fun z => if a = z then (1 : ℂ) else 0) ∈ Submodule.span ℂ (Set.range u) := by
      rw [hu.2]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose b hb using hb
  have hind : ∀ x : ι → α, (fun y => if x = y then (1 : ℂ) else 0) ∈
      Submodule.span ℂ (Set.range (s7Mono (ι := ι) u)) := by
    intro x
    have : (fun y : ι → α => if x = y then (1 : ℂ) else 0) =
        ∑ c : ι → J, (∏ i, b (x i) (c i)) • s7Mono u c := by
      funext y
      have e1 : (if x = y then (1 : ℂ) else 0) = ∏ i, (if x i = y i then (1 : ℂ) else 0) := by
        by_cases h : x = y
        · subst h; simp
        · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
          simp [h]
          exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
      have e2 : ∀ i, (if x i = y i then (1 : ℂ) else 0) = ∑ j, b (x i) j * u j (y i) := by
        intro i
        have := congrFun (hb (x i)) (y i)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        exact this.symm
      rw [e1]
      simp only [e2]
      rw [Fintype.prod_sum (fun i j => b (x i) j * u j (y i))]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, s7Mono_apply,
        Finset.prod_mul_distrib]
    rw [this]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  have hf : f = ∑ x : ι → α, f x • (fun y : ι → α => if x = y then (1 : ℂ) else 0) := by
    funext y
    simp [Finset.sum_apply, Pi.smul_apply]
  rw [hf]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hind x)

/-- Parseval for the monomial expansion: `‖f‖₂² = ∑_χ |f̂(χ)|²`. -/
theorem s7_parseval (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (u : J → α → ℂ)
    [Fintype J] (hu : S7IsONB D u) (f : (ι → α) → ℂ) :
    (D.pi ι).expect (fun x => ‖f x‖ ^ 2) = ∑ c : ι → J, ‖s7Coef D u f c‖ ^ 2 := by
  classical
  have hm := s7_mono_orthonormal (ι := ι) D u hu.1
  have hf := s7_fourier_expansion D hD u hu f
  have h1 := cinner_self_eq (D.pi ι) f
  have h2 : (D.pi ι).cinner f f = ∑ c, s7Coef D u f c * star (s7Coef D u f c) := by
    conv_lhs => rw [hf]
    exact cinner_sum_smul_sum (D.pi ι) _ hm _ _
  have h3 : ((D.pi ι).expect (fun x => ‖f x‖ ^ 2) : ℂ) =
      ((∑ c, ‖s7Coef D u f c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h1, h2]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  exact_mod_cast h3

open scoped Classical in
/-- the part of `f` on the monomials satisfying `P` (the "part of `f` of embedding degrees `D_a`,
effective degree `i`, non-embedding degree `i'`" of App. B, l. 9225-9262, and of the degree
decompositions of Sections 8-9). -/
def s7Part (D : FinProb α) (u : J → α → ℂ) [Fintype J] (P : (ι → J) → Prop)
    (f : (ι → α) → ℂ) : (ι → α) → ℂ :=
  ∑ c : ι → J, if P c then s7Coef D u f c • s7Mono u c else 0

private lemma expect_sq_expansion {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    (π : FinProb β) (m : γ → β → ℂ)
    (hm : ∀ c c', π.cinner (m c) (m c') = if c = c' then 1 else 0) (a : γ → ℂ) :
    π.expect (fun x => ‖(∑ c, a c • m c) x‖ ^ 2) = ∑ c, ‖a c‖ ^ 2 := by
  have h1 := cinner_self_eq π (∑ c, a c • m c)
  rw [cinner_sum_smul_sum π m hm] at h1
  have h3 : (π.expect (fun x => ‖(∑ c, a c • m c) x‖ ^ 2) : ℂ) = ((∑ c, ‖a c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  exact_mod_cast h3

private lemma coef_expansion {α J ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype J]
    [DecidableEq J] (D : FinProb α) (u : J → α → ℂ)
    (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) (a : (ι → J) → ℂ)
    (c0 : ι → J) : s7Coef D u (∑ c, a c • s7Mono u c) c0 = a c0 := by
  have hm := s7_mono_orthonormal (ι := ι) D u hu
  unfold s7Coef
  rw [cinner_sum_left, Finset.sum_eq_single c0]
  · rw [cinner_smul_left, hm]; simp
  · intro c _ hc; rw [cinner_smul_left, hm]; simp [hc]
  · simp

open scoped Classical in
private lemma s7Part_eq {α J ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype J]
    (D : FinProb α) (u : J → α → ℂ) (P : (ι → J) → Prop) (f : (ι → α) → ℂ) :
    s7Part D u P f = ∑ c : ι → J, (if P c then s7Coef D u f c else 0) • s7Mono u c := by
  unfold s7Part
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

open scoped Classical in
/-- a part has the coefficients of `f` on the monomials of the pattern and `0` elsewhere. -/
theorem s7Part_coef (D : FinProb α) (u : J → α → ℂ) [Fintype J] [DecidableEq J]
    (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) (P : (ι → J) → Prop)
    (f : (ι → α) → ℂ) (c : ι → J) :
    s7Coef D u (s7Part D u P f) c = if P c then s7Coef D u f c else 0 := by
  rw [s7Part_eq]
  exact coef_expansion D u hu _ c

open scoped Classical in
/-- `f = (part on `P`) + (part on `¬ P`)`. -/
theorem s7Part_add_compl (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (u : J → α → ℂ) [Fintype J]
    (hu : S7IsONB D u) (P : (ι → J) → Prop) (f : (ι → α) → ℂ) :
    s7Part D u P f + s7Part D u (fun c => ¬ P c) f = f := by
  have hf := s7_fourier_expansion D hD u hu f
  rw [s7Part_eq, s7Part_eq, ← Finset.sum_add_distrib]
  conv_rhs => rw [hf]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hP : P c <;> simp [hP]

open scoped Classical in
/-- Parseval for a part: `‖f_P‖₂² = ∑_{χ : P χ} |f̂(χ)|²`. -/
theorem s7Part_expect_sq (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (u : J → α → ℂ) [Fintype J]
    (hu : S7IsONB D u) (P : (ι → J) → Prop) (f : (ι → α) → ℂ) :
    (D.pi ι).expect (fun x => ‖s7Part D u P f x‖ ^ 2) =
      ∑ c ∈ univ.filter P, ‖s7Coef D u f c‖ ^ 2 := by
  classical
  have _ := hD
  have hm := s7_mono_orthonormal (ι := ι) D u hu.1
  rw [s7Part_eq, expect_sq_expansion _ _ hm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hP : P c <;> simp [hP]

open scoped Classical in
/-- parts on disjoint patterns are orthogonal. -/
theorem s7Part_orthogonal (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (u : J → α → ℂ) [Fintype J]
    (hu : S7IsONB D u) (P Q : (ι → J) → Prop) (hPQ : ∀ c, ¬ (P c ∧ Q c))
    (f g : (ι → α) → ℂ) :
    (D.pi ι).cinner (s7Part D u P f) (s7Part D u Q g) = 0 := by
  classical
  have _ := hD
  have hm := s7_mono_orthonormal (ι := ι) D u hu.1
  rw [s7Part_eq, s7Part_eq, cinner_sum_smul_sum _ _ hm]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hP : P c
  · have : ¬ Q c := fun hQ => hPQ c ⟨hP, hQ⟩
    simp [this]
  · simp [hP]

open scoped Classical in
/-- the part of `f` of non-embedding degree exactly `d` is non-embedding homogeneous of degree `d`
(and likewise for the other degrees; this is the instance used for the decomposition of `g`, `h`
into homogeneous parts). -/
theorem s7Part_neHom {H : Type} [AddCommGroup H] [Fintype H] {K₁ K₂ : Type} [Fintype K₁]
    [Fintype K₂] (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) (d : ℕ)
    (f : (ι → α) → ℂ) : S7NeHom D u (s7Part D u (fun c => s7NeDeg c = d) f) d := by
  classical
  intro c hc
  rw [s7Part_coef D u hu] at hc
  by_cases hP : s7NeDeg c = d
  · exact hP
  · exact absurd (by simp [hP]) hc

/-- `Fintype` of the index set of a modest basis is its cardinality `|Ĥ| + nN + nM = |Σ|`. -/
theorem s7_modestBasis_card (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) :
    Fintype.card H + B.nN + B.nM = Fintype.card α := by
  classical
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  have hli : LinearIndependent ℂ B.u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h := congrArg (fun f => D.cinner f (B.u k)) hg
    simp only [cinner_zero_left] at h
    rw [cinner_sum_left, Finset.sum_eq_single k] at h
    · rw [cinner_smul_left, modest_orthonormal] at h; simpa using h
    · intro j _ hj; rw [cinner_smul_left, modest_orthonormal]; simp [hj]
    · simp
  let b : Module.Basis B.J ℂ (α → ℂ) := Module.Basis.mk hli hONB.2.ge
  have h1 := Module.finrank_eq_card_basis b
  rw [Module.finrank_fintype_fun_eq_card] at h1
  rw [h1]
  simp [S7ModestBasis.J, Fintype.card_sum, add_assoc]

end Tensor

section DegreeFacts
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K₁ K₂ : Type}

/-- l. 4202-4203: `nedeg + embeddeg = n`. -/
theorem s7_embedDeg_add_neDeg (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EmbedDeg c + s7NeDeg c = Fintype.card ι := by
  unfold s7EmbedDeg s7NeDeg s7CountWhere
  have := Set.ncard_add_ncard_compl {i | ∃ a, c i = (Sum.inl a : AddChar H ℂ ⊕ (K₁ ⊕ K₂))}
  rw [Nat.card_eq_fintype_card] at this
  exact this

/-- l. 4195: `embeddeg = ∑_a embeddeg_a`. -/
theorem s7_embedDeg_eq_sum (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EmbedDeg c = ∑ a : AddChar H ℂ, s7EmbedDegA a c := by
  classical
  unfold s7EmbedDeg s7EmbedDegA s7CountWhere
  have e : ∀ P : ι → Prop, {i | P i}.ncard = ∑ i, if P i then 1 else 0 := by
    intro P
    have : {i | P i} = ↑(Finset.univ.filter P) := by ext; simp
    rw [this, Set.ncard_coe_finset, Finset.card_filter]
  rw [e]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hci : c i with b | b
  · simp
  · simp

/-- l. 4202: `effnon ≤ nedeg`. -/
theorem s7_effDeg_le_neDeg (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) : s7EffDeg c ≤ s7NeDeg c := by
  unfold s7EffDeg s7NeDeg s7CountWhere
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro i ⟨m, hm⟩
  rintro ⟨a, ha⟩
  rw [hm] at ha
  cases ha

end DegreeFacts

/-- the pattern of a basis index: the embedding character `a`, `B_non-embed` (`false`) or
`B_modest` (`true`). The canonical spaces `V_{inl a} = span(a∘σ)`, `V_N = NENM`, `V_M` are indexed by
patterns, and all degrees are functions of the pattern. -/
def s7Pat {K₁ K₂ : Type} : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → AddChar H ℂ ⊕ Bool :=
  Sum.elim Sum.inl (Sum.elim (fun _ => Sum.inr false) (fun _ => Sum.inr true))


section Indep
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the span of the monomials of pattern `τ` -/
private def patSpan {J Q : Type} (u : J → α → ℂ) (pat : J → Q) (τ : ι → Q) :
    Submodule ℂ ((ι → α) → ℂ) :=
  Submodule.span ℂ {g | ∃ c : ι → J, (fun i => pat (c i)) = τ ∧ g = s7Mono u c}

private lemma coefZero_iff_perp {J Q : Type} (D : FinProb α) (u : J → α → ℂ) (pat : J → Q)
    (τ : ι → Q) (f : (ι → α) → ℂ) :
    (∀ c : ι → J, (fun i => pat (c i)) = τ → s7Coef D u f c = 0) ↔
      ∀ g ∈ patSpan u pat τ, (D.pi ι).cinner f g = 0 := by
  constructor
  · intro h g hg
    induction hg using Submodule.span_induction with
    | mem g hg => obtain ⟨c, hc, rfl⟩ := hg; exact h c hc
    | zero => exact cinner_zero_right _ _
    | add x y _ _ hx hy => rw [cinner_add_right, hx, hy]; simp
    | smul a x _ hx => rw [cinner_smul_right, hx]; simp
  · intro h c hc
    exact h _ (Submodule.subset_span ⟨c, hc, rfl⟩)

private lemma hom_iff_pattern {J Q : Type} (D : FinProb α) (u : J → α → ℂ) (pat : J → Q)
    (φ : (ι → Q) → Prop) (f : (ι → α) → ℂ) :
    (∀ c : ι → J, s7Coef D u f c ≠ 0 → φ (fun i => pat (c i))) ↔
      ∀ τ : ι → Q, ¬ φ τ → ∀ c : ι → J, (fun i => pat (c i)) = τ → s7Coef D u f c = 0 := by
  constructor
  · intro h τ hτ c hc
    by_contra hne
    exact hτ (by have := h c hne; rwa [hc] at this)
  · intro h c hne
    by_contra hφ
    exact hne (h _ hφ c rfl)

private lemma mem_span_expansion {J : Type} [Fintype J] [DecidableEq J] (D : FinProb α)
    (u : J → α → ℂ) (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0)
    (S : Finset J) (v : α → ℂ) (hv : v ∈ Submodule.span ℂ (u '' (S : Set J))) :
    v = ∑ j ∈ S, D.cinner v (u j) • u j := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨k, hk, rfl⟩ := hv
    rw [Finset.sum_eq_single k]
    · rw [hu]; simp
    · intro j _ hj; rw [hu]; simp [Ne.symm hj]
    · intro hk'; exact absurd hk hk'
  | zero => simp [cinner_zero_left]
  | add x y _ _ hx hy =>
    simp only [cinner_add_left, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul a x _ hx =>
    simp only [cinner_smul_left, mul_smul, ← Finset.smul_sum]
    rw [← hx]

private lemma prod_mem_patSpan {J Q : Type} [Fintype J] [DecidableEq J] (D : FinProb α)
    (u : J → α → ℂ) (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0)
    (pat : J → Q) (τ : ι → Q) (v : ι → α → ℂ)
    (hv : ∀ i, v i ∈ Submodule.span ℂ (u '' {j | pat j = τ i})) :
    (fun x => ∏ i, v i (x i)) ∈ patSpan u pat τ := by
  classical
  let t : ι → Finset J := fun i => Finset.univ.filter (fun j => pat j = τ i)
  have hv' : ∀ i, v i = ∑ j ∈ t i, D.cinner (v i) (u j) • u j := fun i => by
    apply mem_span_expansion D u hu (t i) (v i)
    simpa [t] using hv i
  have key : (fun x : ι → α => ∏ i, v i (x i)) =
      ∑ p ∈ Fintype.piFinset t, (∏ i, D.cinner (v i) (u (p i))) • s7Mono u p := by
    funext x
    have e1 : ∀ i, v i (x i) = ∑ j ∈ t i, D.cinner (v i) (u j) * u j (x i) := fun i => by
      conv_lhs => rw [hv' i]
      simp [Finset.sum_apply]
    simp only [e1]
    rw [Finset.prod_univ_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, s7Mono_apply, Finset.prod_mul_distrib]
  rw [key]
  refine Submodule.sum_mem _ fun p hp =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, ?_, rfl⟩)
  funext i
  have := Fintype.mem_piFinset.1 hp i
  simpa [t] using this

private lemma u_mem_span_pat {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B B' : S7ModestBasis D σ Sm) (j : B.J) :
    B.u j ∈ Submodule.span ℂ (B'.u '' {j' | s7Pat j' = s7Pat j}) := by
  rcases j with χ | k | k
  · exact Submodule.subset_span ⟨Sum.inl χ, rfl, rfl⟩
  · have hN : B.uN k ∈ Submodule.span ℂ (Set.range B'.uN) := by
      rw [B'.span_N, ← B.span_N]; exact Submodule.subset_span ⟨k, rfl⟩
    have : Set.range B'.uN ⊆ B'.u '' {j' | s7Pat j' = s7Pat (Sum.inr (Sum.inl k) : B.J)} := by
      rintro _ ⟨k', rfl⟩; exact ⟨Sum.inr (Sum.inl k'), rfl, rfl⟩
    exact Submodule.span_mono this hN
  · have hM : B.uM k ∈ Submodule.span ℂ (Set.range B'.uM) := by
      rw [B'.span_M, ← B.span_M]; exact Submodule.subset_span ⟨k, rfl⟩
    have : Set.range B'.uM ⊆ B'.u '' {j' | s7Pat j' = s7Pat (Sum.inr (Sum.inr k) : B.J)} := by
      rintro _ ⟨k', rfl⟩; exact ⟨Sum.inr (Sum.inr k'), rfl, rfl⟩
    exact Submodule.span_mono this hM

private lemma patSpan_le {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B B' : S7ModestBasis D σ Sm) (τ : ι → AddChar H ℂ ⊕ Bool) :
    patSpan B.u s7Pat τ ≤ patSpan B'.u s7Pat τ := by
  classical
  have hu' : ∀ i j : B'.J, D.cinner (B'.u i) (B'.u j) = if i = j then 1 else 0 :=
    fun i j => by convert modest_orthonormal D σ Sm B' i j
  rw [patSpan, Submodule.span_le]
  rintro _ ⟨c, hc, rfl⟩
  refine prod_mem_patSpan D B'.u hu' s7Pat τ (fun i => B.u (c i)) fun i => ?_
  have := u_mem_span_pat B B' (c i)
  rwa [show s7Pat (c i) = τ i from congrFun hc i] at this

private lemma patSpan_eq {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B B' : S7ModestBasis D σ Sm) (τ : ι → AddChar H ℂ ⊕ Bool) :
    patSpan B.u s7Pat τ = patSpan B'.u s7Pat τ :=
  le_antisymm (patSpan_le B B' τ) (patSpan_le B' B τ)

private lemma coefZero_indep (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B B' : S7ModestBasis D σ Sm) (τ : ι → AddChar H ℂ ⊕ Bool) (f : (ι → α) → ℂ) :
    (∀ c : ι → B.J, (fun i => s7Pat (c i)) = τ → s7Coef D B.u f c = 0) ↔
      (∀ c : ι → B'.J, (fun i => s7Pat (c i)) = τ → s7Coef D B'.u f c = 0) := by
  rw [coefZero_iff_perp, coefZero_iff_perp, patSpan_eq B B' τ]

private lemma homP_indep (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B B' : S7ModestBasis D σ Sm) (φ : (ι → AddChar H ℂ ⊕ Bool) → Prop) (f : (ι → α) → ℂ) :
    (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 → φ (fun i => s7Pat (c i))) ↔
      (∀ c : ι → B'.J, s7Coef D B'.u f c ≠ 0 → φ (fun i => s7Pat (c i))) := by
  rw [hom_iff_pattern, hom_iff_pattern]
  exact forall_congr' fun τ => imp_congr_right fun _ => coefZero_indep D σ Sm B B' τ f

private lemma s7EffDeg_eq_pat {K₁ K₂ : Type} (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EffDeg c = s7CountWhere (fun p : AddChar H ℂ ⊕ Bool => p = Sum.inr true)
      (fun i => s7Pat (c i)) := by
  unfold s7EffDeg s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  generalize c i = j
  rcases j with a | k | m <;> simp [s7Pat]

private lemma s7EmbedDegA_eq_pat {K₁ K₂ : Type} (a : AddChar H ℂ)
    (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EmbedDegA a c = s7CountWhere (fun p : AddChar H ℂ ⊕ Bool => p = Sum.inl a)
      (fun i => s7Pat (c i)) := by
  unfold s7EmbedDegA s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  generalize c i = j
  rcases j with b | k | m <;> simp [s7Pat]

private lemma s7NeDeg_eq_pat {K₁ K₂ : Type} (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7NeDeg c = s7CountWhere (fun p : AddChar H ℂ ⊕ Bool => ¬ ∃ a, p = Sum.inl a)
      (fun i => s7Pat (c i)) := by
  unfold s7NeDeg s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  generalize c i = j
  rcases j with b | k | m <;> simp [s7Pat]

private lemma compEmbedHom_indep (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B B' : S7ModestBasis D σ Sm) (f : (ι → α) → ℂ) (Dtot : ℕ) :
    S7CompEmbedHom (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u f Dtot ↔
      S7CompEmbedHom (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u f Dtot := by
  unfold S7CompEmbedHom
  refine exists_congr fun Da => and_congr_right fun _ => ?_
  have e : ∀ B : S7ModestBasis D σ Sm,
      (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a) ↔
      (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 →
        (fun τ : ι → AddChar H ℂ ⊕ Bool => ∀ a, s7CountWhere (fun p => p = Sum.inl a) τ = Da a)
          (fun i => s7Pat (c i))) := fun B => by
    simp only [s7EmbedDegA_eq_pat]
  rw [e B, e B']
  exact homP_indep D σ Sm B B'
    (fun τ : ι → AddChar H ℂ ⊕ Bool => ∀ a, s7CountWhere (fun p => p = Sum.inl a) τ = Da a) f

private lemma neHom_indep (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B B' : S7ModestBasis D σ Sm) (f : (ι → α) → ℂ) (d : ℕ) :
    S7NeHom (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u f d ↔
      S7NeHom (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u f d := by
  unfold S7NeHom
  have e : ∀ B : S7ModestBasis D σ Sm,
      (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 → s7NeDeg c = d) ↔
      (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 →
        (fun τ : ι → AddChar H ℂ ⊕ Bool =>
          s7CountWhere (fun p => ¬ ∃ a, p = Sum.inl a) τ = d) (fun i => s7Pat (c i))) :=
    fun B => by simp only [s7NeDeg_eq_pat]
  rw [e B, e B']
  exact homP_indep D σ Sm B B'
    (fun τ : ι → AddChar H ℂ ⊕ Bool => s7CountWhere (fun p => ¬ ∃ a, p = Sum.inl a) τ = d) f

private lemma effDegGE_indep (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (B B' : S7ModestBasis D σ Sm) (f : (ι → α) → ℂ) (d' : ℕ) :
    S7EffDegGE (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u f d' ↔
      S7EffDegGE (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u f d' := by
  unfold S7EffDegGE
  have e : ∀ B : S7ModestBasis D σ Sm,
      (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 → d' ≤ s7EffDeg c) ↔
      (∀ c : ι → B.J, s7Coef D B.u f c ≠ 0 →
        (fun τ : ι → AddChar H ℂ ⊕ Bool =>
          d' ≤ s7CountWhere (fun p => p = Sum.inr true) τ) (fun i => s7Pat (c i))) :=
    fun B => by simp only [s7EffDeg_eq_pat]
  rw [e B, e B']
  exact homP_indep D σ Sm B B'
    (fun τ : ι → AddChar H ℂ ⊕ Bool => d' ≤ s7CountWhere (fun p => p = Sum.inr true) τ) f

private lemma cinner_self_eq_zero' {β : Type*} [Fintype β] (π : FinProb β)
    (hπ : ∀ a, 0 < π.prob a) (f : β → ℂ) (h : π.cinner f f = 0) : f = 0 := by
  rw [cinner_self_eq π f] at h
  have h0 : (π.expect fun a => ‖f a‖ ^ 2) = 0 := by exact_mod_cast h
  have hnn : ∀ a ∈ (Finset.univ : Finset β), 0 ≤ π.prob a * ‖f a‖ ^ 2 :=
    fun a _ => mul_nonneg (π.nonneg a) (sq_nonneg _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0
  funext a
  have := h1 a (Finset.mem_univ a)
  have h2 : ‖f a‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hπ a).ne'
    · exact h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

open scoped Classical in
/-- the part of `f` of exact pattern `τ` for the basis `B` -/
private def patPart (D : FinProb α) {σ : α → H} {Sm : Finset α} (B : S7ModestBasis D σ Sm)
    (τ : ι → AddChar H ℂ ⊕ Bool) (f : (ι → α) → ℂ) : (ι → α) → ℂ :=
  ∑ c ∈ Finset.univ.filter (fun c : ι → B.J => (fun i => s7Pat (c i)) = τ),
    s7Coef D B.u f c • s7Mono B.u c

open scoped Classical in
private lemma patPart_mem (D : FinProb α) {σ : α → H} {Sm : Finset α} (B : S7ModestBasis D σ Sm)
    (τ : ι → AddChar H ℂ ⊕ Bool) (f : (ι → α) → ℂ) : patPart D B τ f ∈ patSpan B.u s7Pat τ :=
  Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨c, (Finset.mem_filter.1 hc).2, rfl⟩)

open scoped Classical in
private lemma patPart_perp (D : FinProb α) {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (τ : ι → AddChar H ℂ ⊕ Bool) (f : (ι → α) → ℂ) :
    ∀ g ∈ patSpan B.u s7Pat τ, (D.pi ι).cinner (f - patPart D B τ f) g = 0 := by
  have hu' : ∀ i j : B.J, D.cinner (B.u i) (B.u j) = if i = j then 1 else 0 :=
    fun i j => by convert modest_orthonormal D σ Sm B i j
  have hm := s7_mono_orthonormal (ι := ι) D B.u hu'
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c', hc', rfl⟩ := hg
    rw [cinner_sub_left']
    unfold patPart
    rw [cinner_sum_left, Finset.sum_eq_single c']
    · rw [cinner_smul_left, hm]
      simp [s7Coef]
    · intro c hc hne
      rw [cinner_smul_left, hm]; simp [hne]
    · intro hn
      exfalso; apply hn; simpa using hc'
  | zero => exact cinner_zero_right _ _
  | add x y _ _ hx hy => rw [cinner_add_right, hx, hy]; simp
  | smul a x _ hx => rw [cinner_smul_right, hx]; simp

private lemma patPart_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) {σ : α → H}
    {Sm : Finset α} (B B' : S7ModestBasis D σ Sm) (τ : ι → AddChar H ℂ ⊕ Bool)
    (f : (ι → α) → ℂ) : patPart D B τ f = patPart D B' τ f := by
  have hpos : ∀ x : ι → α, 0 < (D.pi ι).prob x := fun x =>
    Finset.prod_pos fun i _ => hD (x i)
  have h1 := patPart_mem D B τ f
  have h2 := patPart_mem D B' τ f
  rw [patSpan_eq B B' τ] at h1
  have hd : patPart D B τ f - patPart D B' τ f ∈ patSpan B'.u s7Pat τ :=
    Submodule.sub_mem _ h1 h2
  have e1 := patPart_perp D B τ f
  rw [patSpan_eq B B' τ] at e1
  have e2 := patPart_perp D B' τ f
  have h3 := cinner_sub_left' (D.pi ι) (f - patPart D B' τ f) (f - patPart D B τ f)
    (patPart D B τ f - patPart D B' τ f)
  rw [e2 _ hd, e1 _ hd, sub_zero] at h3
  have h4 : (D.pi ι).cinner (patPart D B τ f - patPart D B' τ f)
      (patPart D B τ f - patPart D B' τ f) = 0 := by
    have : (f - patPart D B' τ f) - (f - patPart D B τ f) =
        patPart D B τ f - patPart D B' τ f := by abel
    rw [this] at h3
    exact h3
  exact sub_eq_zero.1 (cinner_self_eq_zero' (D.pi ι) hpos _ h4)

end Indep

/-- The classes `F'_{n,d,d'}` do not depend on the choice of `B_non-embed`, `B_modest`:
membership only involves, for each monomial, the pattern (`B_embed` character / `B_non-embed` /
`B_modest`) of its coordinates, and the span of the monomials of one pattern is canonical. -/
theorem s7_classFp_basis_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H)
    (Sm : Finset α) (B B' : S7ModestBasis D σ Sm) (n d d' : ℕ) :
    s7ClassFp (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u n d d' =
      s7ClassFp (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u n d d' := by
  have _ := hD
  ext f
  exact and_congr (exists_congr fun Dtot => compEmbedHom_indep D σ Sm B B' f Dtot)
    (and_congr (neHom_indep D σ Sm B B' f d) (effDegGE_indep D σ Sm B B' f d'))

/-- the same for `G_n`, `H_n`. -/
theorem s7_classG_basis_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H)
    (Sm : Finset α) (B B' : S7ModestBasis D σ Sm) (n : ℕ) :
    s7ClassG (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u n =
      s7ClassG (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u n := by
  have _ := hD
  ext f
  exact and_congr (exists_congr fun Dtot => compEmbedHom_indep D σ Sm B B' f Dtot)
    (exists_congr fun d => neHom_indep D σ Sm B B' f d)

/-- the effective-degree condition does not depend on the bases either. -/
theorem s7_effDegGE_basis_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H)
    (Sm : Finset α) (B B' : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (d' : ℕ) :
    S7EffDegGE (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u f d' ↔
      S7EffDegGE (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u f d' := by
  have _ := hD
  exact effDegGE_indep D σ Sm B B' f d'

/-- the zero function lies in every class (the source excludes it from the suprema). -/
theorem s7_zero_mem_classFp (D : FinProb α) {K₁ K₂ : Type}
    (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) (n d d' : ℕ) :
    (fun _ => 0) ∈ s7ClassFp D u n d d' := by
  have h0 : ∀ c : Fin n → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7Coef D u (fun _ => (0 : ℂ)) c = 0 :=
    fun c => cinner_zero_left _ _
  refine ⟨⟨0, fun _ => 0, by simp, fun c hc => absurd (h0 c) hc⟩, fun c hc => absurd (h0 c) hc,
    fun c hc => absurd (h0 c) hc⟩

/-- complete embedding homogeneity does not depend on the pick. -/
theorem s7_compEmbedHom_basis_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H)
    (Sm : Finset α) (B B' : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (Dtot : ℕ) :
    S7CompEmbedHom (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u f Dtot ↔
      S7CompEmbedHom (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u f Dtot := by
  have _ := hD
  exact compEmbedHom_indep D σ Sm B B' f Dtot

/-- non-embedding homogeneity does not depend on the pick. -/
theorem s7_neHom_basis_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H)
    (Sm : Finset α) (B B' : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (d : ℕ) :
    S7NeHom (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u f d ↔
      S7NeHom (K₁ := Fin B'.nN) (K₂ := Fin B'.nM) D B'.u f d := by
  have _ := hD
  exact neHom_indep D σ Sm B B' f d

open scoped Classical in
/-- the part of `f` on any set of patterns (in particular the parts of given embedding,
non-embedding and effective degrees of App. B) does not depend on the pick. -/
theorem s7Part_basis_indep (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H)
    (Sm : Finset α) (B B' : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → AddChar H ℂ ⊕ Bool) → Prop) (f : (ι → α) → ℂ) :
    s7Part D B.u (fun c => Q (fun i => s7Pat (c i))) f =
      s7Part D B'.u (fun c => Q (fun i => s7Pat (c i))) f := by
  have key : ∀ B : S7ModestBasis D σ Sm,
      s7Part D B.u (fun c => Q (fun i => s7Pat (c i))) f =
        ∑ τ ∈ Finset.univ.filter Q, patPart D B τ f := by
    intro B
    unfold s7Part patPart
    rw [← Finset.sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun c : ι → B.J => Q (fun i => s7Pat (c i)))) (t := Finset.univ.filter Q)
      (g := fun c => fun i => s7Pat (c i))]
    · refine Finset.sum_congr rfl fun τ hτ => ?_
      have hQ : Q τ := (Finset.mem_filter.1 hτ).2
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hQ, h⟩
    · intro c hc
      simpa using (Finset.mem_filter.1 hc).2
  rw [key B, key B']
  exact Finset.sum_congr rfl fun τ _ => patPart_indep D hD B B' τ f

/-- the degree predicates are functions of the pattern (so `Q` above can express them). -/
theorem s7_neDeg_eq_pattern {ι : Type} [Fintype ι] [DecidableEq ι] {K₁ K₂ : Type}
    (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7NeDeg c = s7CountWhere (fun p : AddChar H ℂ ⊕ Bool => ¬ ∃ a, p = Sum.inl a)
      (fun i => s7Pat (c i)) := by
  exact s7NeDeg_eq_pat c

/-- `F'_{n,d,d'}` for the chosen basis `B` (the only admissible use of `s7ClassFp`). -/
def S7ModestBasis.classFp {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (n d d' : ℕ) : Set ((Fin n → α) → ℂ) :=
  s7ClassFp (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u n d d'

/-- the same for `G_n`, `H_n` -/
def S7ModestBasis.classG {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (n : ℕ) : Set ((Fin n → α) → ℂ) :=
  s7ClassG (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u n


end Thms

end S7Basis
end TrackB
end RestrictedPolynomials
end
