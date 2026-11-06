module

public import RestrictedPolynomials.TrackB.S7Beta

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S8Split
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the type of the coordinates `I = [n] \ {j}` of the split `[n] = I ⊔ {j}` of Sections 8-9 (the
source's `|J| = 1`, `J = {j}`). -/
abbrev S8Rest (j : ι) : Type := {i : ι // i ≠ j}

/-- glue a value `a` at the coordinate `j` and a point `b` of `I`: `(y_I, y_J) ↦ y`. -/
def s8Glue {α : Type} (j : ι) (a : α) (b : S8Rest j → α) : ι → α :=
  fun i => if h : i = j then a else b ⟨i, h⟩

/-- the restriction `y ↦ y_I`. -/
def s8Restr {α : Type} (j : ι) (w : ι → α) : S8Rest j → α := fun i => w i.1

/-- transport of a function on `ι → α` along `e : ι ≃ κ`, `x ↦ f (x ∘ e)`. -/
def s8Reindex {α : Type} {κ : Type} (e : ι ≃ κ) (f : (ι → α) → ℂ) : (κ → α) → ℂ :=
  fun x => f (fun i => x (e i))

/-- one-variable `W`: `(W f)(y, z) = f(x)` for the unique `x` of `(y, z)` (the case `|J| = 1` of
`s7W`, for the `F'_χ ∈ span{W ∘ χ ∘ σ}` of Claim 8.5). -/
def s8W1 {X Y Z : Type} {S : Set (X × Y × Z)} (h : S7YZImpliesX S) (f : X → ℂ) : Y × Z → ℂ :=
  fun v => f (s7Pre h v.1 v.2)

/-- the one-site correlation `𝔼_{(x,y,z) ∼ μ} F(y,z) g(y) h(z)` (`F̂'_t(r, s)` of eq. `project_eq`). -/
def s8Corr1 {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (μ : FinProb (X × Y × Z))
    (F : Y × Z → ℂ) (g : Y → ℂ) (h : Z → ℂ) : ℂ :=
  μ.cexpect fun p => F (p.2.1, p.2.2) * g p.2.1 * h p.2.2

omit [Fintype ι] in
@[simp] theorem s8Glue_same {α : Type} (j : ι) (a : α) (b : S8Rest j → α) :
    s8Glue j a b j = a := by
  simp [s8Glue]

omit [Fintype ι] in
@[simp] theorem s8Restr_glue {α : Type} (j : ι) (a : α) (b : S8Rest j → α) :
    s8Restr j (s8Glue j a b) = b := by
  funext i
  simp [s8Restr, s8Glue, i.2]

omit [Fintype ι] in
@[simp] theorem s8Glue_restr {α : Type} (j : ι) (w : ι → α) :
    s8Glue j (w j) (s8Restr j w) = w := by
  funext i
  by_cases h : i = j
  · subst h; simp [s8Glue]
  · simp [s8Glue, s8Restr, h]

theorem s8_card_rest (j : ι) : Fintype.card (S8Rest j) + 1 = Fintype.card ι := by
  have h := Fintype.card_subtype_compl (fun i : ι => i = j)
  have h2 : Fintype.card {i : ι // i = j} = 1 := by simp
  have h3 : Fintype.card ι ≥ 1 := Fintype.card_pos_iff.2 ⟨j⟩
  have h4 : Fintype.card (S8Rest j) = Fintype.card {i : ι // ¬ i = j} :=
    Fintype.card_congr (Equiv.refl _)
  omega

end S8Split

/-! ### Theorems of file 1 (targets) -/

section S8SplitThms

/-- the splitting equivalence `(ι → α) ≃ α × (I → α)`. -/
private def splitEquiv {α : Type} {ι : Type} [DecidableEq ι] (j : ι) :
    (ι → α) ≃ α × (S8Rest j → α) where
  toFun w := (w j, s8Restr j w)
  invFun p := s8Glue j p.1 p.2
  left_inv w := by simp
  right_inv p := Prod.ext (by simp) (by simp)

private lemma pi_prob_glue {β : Type} [Fintype β] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb β) (j : ι) (a : β) (b : S8Rest j → β) :
    (π.pi ι).prob (s8Glue j a b) = π.prob a * (π.pi (S8Rest j)).prob b := by
  simp only [FinProb.pi]
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => π.prob (s8Glue j a b i)) j]
  have : ∀ i : S8Rest j, s8Glue j a b i = b i := fun i => by simp [s8Glue, i.2]
  simp only [this, s8Glue_same]

/-- Fubini for the split `[n] = I ⊔ {j}`: `𝔼_{π^{⊗ι}} φ = 𝔼_{a ∼ π} 𝔼_{b ∼ π^{⊗I}} φ(b, a)`.
(The source uses `μ^{⊗n} = μ^{⊗I} ⊗ μ^{⊗J}` without comment, l. 4872 and the proofs of Claims 8.4-8.6.) -/
theorem s8_cexpect_split {β : Type} [Fintype β] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb β) (j : ι) (φ : (ι → β) → ℂ) :
    (π.pi ι).cexpect φ =
      π.cexpect (fun a => (π.pi (S8Rest j)).cexpect (fun b => φ (s8Glue j a b))) := by
  unfold FinProb.cexpect
  have h1 : ∑ w : ι → β, ((π.pi ι).prob w : ℂ) * φ w =
      ∑ p : β × (S8Rest j → β), ((π.pi ι).prob (s8Glue j p.1 p.2) : ℂ) * φ (s8Glue j p.1 p.2) :=
    Fintype.sum_equiv (splitEquiv j) _ _ (fun w => by simp [splitEquiv])
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pi_prob_glue]
  push_cast
  ring

/-- inner products of tensors `f_I ⊗ f_J`: `⟨f_I ⊗ f_J, f'_I ⊗ f'_J⟩ = ⟨f_I, f'_I⟩ ⟨f_J, f'_J⟩`. -/
theorem s8_cinner_glue {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb α) (j : ι) (fI fI' : (S8Rest j → α) → ℂ) (fJ fJ' : α → ℂ) :
    (π.pi ι).cinner (fun w => fI (s8Restr j w) * fJ (w j)) (fun w => fI' (s8Restr j w) * fJ' (w j)) =
      (π.pi (S8Rest j)).cinner fI fI' * π.cinner fJ fJ' := by
  unfold FinProb.cinner
  rw [s8_cexpect_split π j]
  unfold FinProb.cexpect
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [s8Restr_glue, s8Glue_same, star_mul']
  ring

/-- the factorisation of eq. `project_eq`: for product functions,
`𝔼_{μ^{⊗n}} (F_I ⊗ F_J)(y,z) (g_I ⊗ g_J)(y) (h_I ⊗ h_J)(z) = F̂(r,s) · F̂'(r,s)`. -/
theorem s8_corrF_glue {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinProb (X × Y × Z)) (j : ι)
    (FI : (S8Rest j → Y × Z) → ℂ) (FJ : Y × Z → ℂ) (gI : (S8Rest j → Y) → ℂ) (gJ : Y → ℂ)
    (hI : (S8Rest j → Z) → ℂ) (hJ : Z → ℂ) :
    s7CorrF μ (fun w : ι → Y × Z => FI (s8Restr j w) * FJ (w j))
        (fun y : ι → Y => gI (s8Restr j y) * gJ (y j))
        (fun z : ι → Z => hI (s8Restr j z) * hJ (z j)) =
      s7CorrF μ FI gI hI * s8Corr1 μ FJ gJ hJ := by
  unfold s7CorrF s8Corr1
  rw [s8_cexpect_split μ j]
  unfold FinProb.cexpect
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : s8Restr j (fun i : ι => (((s8Glue j a b) i).2.1, ((s8Glue j a b) i).2.2)) =
      fun i => ((b i).2.1, (b i).2.2) := by
    funext i; simp [s8Restr, s8Glue, i.2]
  have e2 : s8Restr j (fun i : ι => ((s8Glue j a b) i).2.1) = fun i => (b i).2.1 := by
    funext i; simp [s8Restr, s8Glue, i.2]
  have e3 : s8Restr j (fun i : ι => ((s8Glue j a b) i).2.2) = fun i => (b i).2.2 := by
    funext i; simp [s8Restr, s8Glue, i.2]
  simp only [e1, e2, e3, s8Glue_same]
  ring

/-- `|I| = n - 1` for every `j` of a type of `n` elements: `I` is indexed by `Fin (n - 1)`. -/
theorem s8_restEquivFin {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (e : ι ≃ Fin m) (j : ι) :
    Nonempty (S8Rest j ≃ Fin (m - 1)) := by
  have h1 : Fintype.card ι = m := by simpa using Fintype.card_congr e
  have h2 := s8_card_rest j
  exact ⟨Fintype.equivFinOfCardEq (by omega)⟩

end S8SplitThms

section S8Reindex
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private def reidxEquiv {α : Type} (e : ι ≃ κ) : (κ → α) ≃ (ι → α) where
  toFun x := fun i => x (e i)
  invFun y := fun k => y (e.symm k)
  left_inv x := by funext k; simp
  right_inv y := by funext i; simp

private lemma pi_prob_reindex {α : Type} [Fintype α] (π : FinProb α) (e : ι ≃ κ) (x : κ → α) :
    (π.pi κ).prob x = (π.pi ι).prob (fun i => x (e i)) := by
  simp only [FinProb.pi]
  exact (Equiv.prod_comp e (fun k => π.prob (x k))).symm

private lemma cexpect_reindex {α : Type} [Fintype α] (π : FinProb α) (e : ι ≃ κ)
    (G : (ι → α) → ℂ) :
    (π.pi κ).cexpect (fun x => G (fun i => x (e i))) = (π.pi ι).cexpect G := by
  unfold FinProb.cexpect
  exact Fintype.sum_equiv (reidxEquiv e) _ _ (fun x => by simp [pi_prob_reindex π e x, reidxEquiv])

private lemma expect_reindex {α : Type} [Fintype α] (π : FinProb α) (e : ι ≃ κ)
    (G : (ι → α) → ℝ) :
    (π.pi κ).expect (fun x => G (fun i => x (e i))) = (π.pi ι).expect G := by
  unfold FinProb.expect
  exact Fintype.sum_equiv (reidxEquiv e) _ _ (fun x => by simp [pi_prob_reindex π e x, reidxEquiv])

private lemma cinner_reindex {α : Type} [Fintype α] (π : FinProb α) (e : ι ≃ κ)
    (f g : (ι → α) → ℂ) :
    (π.pi κ).cinner (s8Reindex e f) (s8Reindex e g) = (π.pi ι).cinner f g :=
  cexpect_reindex π e (fun y => f y * star (g y))

omit [DecidableEq ι] [DecidableEq κ] in
private lemma mono_reindex {α J : Type} (u : J → α → ℂ) (e : ι ≃ κ) (c : ι → J) :
    s7Mono u (fun k => c (e.symm k)) = s8Reindex e (s7Mono u c) := by
  funext x
  simp only [s7Mono, s8Reindex]
  exact (Equiv.prod_comp e (fun k => u (c (e.symm k)) (x k))).symm.trans
    (Finset.prod_congr rfl fun i _ => by simp)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private lemma countWhere_reindex {J : Type} (e : ι ≃ κ) (P : J → Prop) (c : ι → J) :
    s7CountWhere P (fun k => c (e.symm k)) = s7CountWhere P c := by
  unfold s7CountWhere
  exact Set.ncard_congr (fun k _ => e.symm k) (fun k hk => hk) (fun a b _ _ h => e.symm.injective h)
    (fun i hi => ⟨e i, by simpa using hi, by simp⟩)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private lemma all_reindex_iff {J : Type} (e : ι ≃ κ) (P : (κ → J) → Prop) (Q : (ι → J) → Prop)
    (h : ∀ c : ι → J, P (fun k => c (e.symm k)) ↔ Q c) : (∀ c', P c') ↔ ∀ c, Q c := by
  constructor
  · intro H c; exact (h c).1 (H _)
  · intro H c'
    have := (h (fun i => c' (e i))).2 (H _)
    simpa using this


/-- the reindexing lemma for the classes `F'_{n,d,d'}`, `G_n`, `H_n` (audit B, note "API gap"):
the monomial coefficients are invariant under a bijection of the coordinate type
(`f̂(χ) = ⟨f, χ⟩` and the monomial `∏ᵢ χᵢ(xᵢ)` are permuted by `e`). -/
theorem s8_coef_reindex {α J : Type} [Fintype α] (D : FinProb α) (u : J → α → ℂ) (e : ι ≃ κ)
    (f : (ι → α) → ℂ) (c : ι → J) :
    s7Coef D u (s8Reindex e f) (fun k => c (e.symm k)) = s7Coef D u f c := by
  unfold s7Coef
  rw [mono_reindex]
  exact cinner_reindex D e f _

/-- the same for the cc coefficients `F̂(Wχ) = ⟨F, Wχ⟩_{μ_{y,z}^{⊗ι}}`. -/
theorem s8_ccCoef_reindex {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] {J : Type} (μ : FinProb (X × Y × Z))
    (h : S7YZImpliesX μ.support) (u : J → X → ℂ) (e : ι ≃ κ) (F : (ι → Y × Z) → ℂ) (c : ι → J) :
    s7CCCoef μ h u (s8Reindex e F) (fun k => c (e.symm k)) = s7CCCoef μ h u F c := by
  unfold s7CCCoef
  have : s7W h (s7Mono u (fun k => c (e.symm k))) = s8Reindex e (s7W h (s7Mono u c)) := by
    funext w
    simp only [s7W, s8Reindex, s7Mono]
    exact (Equiv.prod_comp e (fun k => u (c (e.symm k)) (s7Pre h (w k).1 (w k).2))).symm.trans
      (Finset.prod_congr rfl fun i _ => by simp)
  rw [this]
  exact cinner_reindex _ e F _

/-- `‖f ∘ e‖₂ = ‖f‖₂`. -/
theorem s8_cl2norm_reindex {α : Type} [Fintype α] (π : FinProb α) (e : ι ≃ κ)
    (f : (ι → α) → ℂ) : cl2norm π (s8Reindex e f) = cl2norm π f := by
  unfold cl2norm cl2sq
  rw [← expect_reindex π e (fun y => ‖f y‖ ^ 2)]
  rfl

/-- `s7CorrF` is invariant under reindexing all three functions. -/
theorem s8_corrF_reindex {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) (e : ι ≃ κ)
    (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    s7CorrF μ (s8Reindex e F) (s8Reindex e g) (s8Reindex e h) = s7CorrF μ F g h := by
  unfold s7CorrF
  exact cexpect_reindex μ e (fun t => F (fun i => ((t i).2.1, (t i).2.2)) *
    g (fun i => (t i).2.1) * h (fun i => (t i).2.2))

variable {α : Type} [Fintype α] {H : Type} [AddCommGroup H] [Fintype H] {K₁ K₂ : Type}

private lemma compEmbedHom_reindex (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (e : ι ≃ κ) (f : (ι → α) → ℂ) (Dtot : ℕ) :
    S7CompEmbedHom D u (s8Reindex e f) Dtot ↔ S7CompEmbedHom D u f Dtot := by
  unfold S7CompEmbedHom
  refine exists_congr fun Da => and_congr_right fun _ => ?_
  refine all_reindex_iff e _ _ (fun c => ?_)
  rw [s8_coef_reindex]
  simp only [s7EmbedDegA, countWhere_reindex]

omit [Fintype H] in
private lemma neHom_reindex (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (e : ι ≃ κ) (f : (ι → α) → ℂ) (d : ℕ) :
    S7NeHom D u (s8Reindex e f) d ↔ S7NeHom D u f d := by
  unfold S7NeHom
  refine all_reindex_iff e _ _ (fun c => ?_)
  rw [s8_coef_reindex]
  simp only [s7NeDeg, countWhere_reindex]

omit [Fintype H] in
private lemma effDegGE_reindex (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (e : ι ≃ κ) (f : (ι → α) → ℂ) (d : ℕ) :
    S7EffDegGE D u (s8Reindex e f) d ↔ S7EffDegGE D u f d := by
  unfold S7EffDegGE
  refine all_reindex_iff e _ _ (fun c => ?_)
  rw [s8_coef_reindex]
  simp only [s7EffDeg, countWhere_reindex]


/-- `F'_{n,d,d'}` on `Fin n` versus the generic-coordinate predicates: a function on `ι → α`,
transported along `e : ι ≃ Fin n`, is in the class iff it has the three properties of Def. 7.? on `ι`.
(Used for `F_t ∈ F'_{n-1,d-1,d'-1}` on `I = [n] \ {j}`.) -/
theorem s8_mem_classFp_iff (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) {n : ℕ}
    (e : ι ≃ Fin n) (f : (ι → α) → ℂ) (d d' : ℕ) :
    s8Reindex e f ∈ s7ClassFp D u n d d' ↔
      (∃ Dtot, S7CompEmbedHom D u f Dtot) ∧ S7NeHom D u f d ∧ S7EffDegGE D u f d' := by
  simp only [s7ClassFp, Set.mem_ofPred_eq, compEmbedHom_reindex, neHom_reindex,
    effDegGE_reindex]

/-- `G_n`, `H_n` on `Fin n` versus the generic-coordinate predicates. -/
theorem s8_mem_classG_iff (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) {n : ℕ}
    (e : ι ≃ Fin n) (g : (ι → α) → ℂ) :
    s8Reindex e g ∈ s7ClassG D u n ↔ (∃ Dtot, S7CompEmbedHom D u g Dtot) ∧ ∃ d, S7NeHom D u g d := by
  simp only [s7ClassG, Set.mem_ofPred_eq, compEmbedHom_reindex, neHom_reindex]

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
  (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma reidx_comm_W (e : ι ≃ κ) (f : (ι → X) → ℂ) :
    s7W hμ (s8Reindex e f) = s8Reindex e (s7W hμ f) := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private lemma reindex_symm_reindex {β : Type} (e : ι ≃ κ) (f : (ι → β) → ℂ) :
    s8Reindex e.symm (s8Reindex e f) = f := by
  funext y
  simp [s8Reindex]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma constOnCC_reindex (e : ι ≃ κ) (F : (ι → Y × Z) → ℂ) :
    S7ConstOnCC hμ (s8Reindex e F) ↔ S7ConstOnCC hμ F := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨s8Reindex e.symm f, ?_⟩
    rw [reidx_comm_W, hf, reindex_symm_reindex]
  · rintro ⟨f, hf⟩
    exact ⟨s8Reindex e f, by rw [reidx_comm_W, hf]⟩

private lemma ccCompEmbedHom_reindex (e : ι ≃ κ) (F : (ι → Y × Z) → ℂ) (Dtot : ℕ) :
    S7CCCompEmbedHom μ hμ u (s8Reindex e F) Dtot ↔ S7CCCompEmbedHom μ hμ u F Dtot := by
  unfold S7CCCompEmbedHom
  refine exists_congr fun Da => and_congr_right fun _ => ?_
  refine all_reindex_iff e _ _ (fun c => ?_)
  rw [s8_ccCoef_reindex]
  simp only [s7EmbedDegA, countWhere_reindex]

omit [Fintype H] in
private lemma ccNeHom_reindex (e : ι ≃ κ) (F : (ι → Y × Z) → ℂ) (d : ℕ) :
    S7CCNeHom μ hμ u (s8Reindex e F) d ↔ S7CCNeHom μ hμ u F d := by
  unfold S7CCNeHom
  refine all_reindex_iff e _ _ (fun c => ?_)
  rw [s8_ccCoef_reindex]
  simp only [s7NeDeg, countWhere_reindex]

omit [Fintype H] in
private lemma ccEffDegGE_reindex (e : ι ≃ κ) (F : (ι → Y × Z) → ℂ) (d : ℕ) :
    S7CCEffDegGE μ hμ u (s8Reindex e F) d ↔ S7CCEffDegGE μ hμ u F d := by
  unfold S7CCEffDegGE
  refine all_reindex_iff e _ _ (fun c => ?_)
  rw [s8_ccCoef_reindex]
  simp only [s7EffDeg, countWhere_reindex]


/-- `F_{n,d,d'}` on `Fin n` versus the generic-coordinate cc predicates. -/
theorem s8_mem_classF_iff {n : ℕ} (e : ι ≃ Fin n) (F : (ι → Y × Z) → ℂ) (d d' : ℕ) :
    s8Reindex e F ∈ s7ClassF μ hμ u n d d' ↔
      S7ConstOnCC hμ F ∧ (∃ Dtot, S7CCCompEmbedHom μ hμ u F Dtot) ∧ S7CCNeHom μ hμ u F d ∧
        S7CCEffDegGE μ hμ u F d' := by
  simp only [s7ClassF, Set.mem_ofPred_eq, constOnCC_reindex, ccCompEmbedHom_reindex,
    ccNeHom_reindex, ccEffDegGE_reindex]

/-- `F_{n,d'}` on `Fin n` versus the generic-coordinate cc predicates. -/
theorem s8_mem_classFn_iff {n : ℕ} (e : ι ≃ Fin n) (F : (ι → Y × Z) → ℂ) (d' : ℕ) :
    s8Reindex e F ∈ s7ClassFn μ hμ u n d' ↔ S7ConstOnCC hμ F ∧ S7CCEffDegGE μ hμ u F d' := by
  simp only [s7ClassFn, Set.mem_ofPred_eq, constOnCC_reindex, ccEffDegGE_reindex]

end S8Reindex

section S8BetaTransport
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H]
  [DecidableEq H]

/-- `β_{n,d,d'} ≤ b` in the form used for functions on the coordinate set `I = [n] \ {j}`
(`β_{n-1,d-1,d'-1}` of Section 8.3): the bound `|𝔼 F g h| ≤ b ‖F‖‖g‖‖h‖` for every triple of the
classes on ANY coordinate type `ι ≃ Fin n`. The bases are the bases `Bx`, `By`, `Bz` of Def. 7.1
(R-1; the statement is for all bases). -/
theorem s8_beta_le_iff_generic (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (γ : Y → H) (φ : Z → H) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX μ) σ Sm) (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
    (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) {n : ℕ} (e : ι ≃ Fin n) (d d' : ℕ) {b : ℝ}
    (hb : 0 ≤ b) :
    s7Beta μ hμ Bx.u By.u Bz.u n d d' ≤ ENNReal.ofReal b ↔
      ∀ (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ),
        S7ConstOnCC hμ F → (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) →
        S7CCNeHom μ hμ Bx.u F d → S7CCEffDegGE μ hμ Bx.u F d' →
        ((∃ Dtot, S7CompEmbedHom (lawY μ) By.u g Dtot) ∧ ∃ d₁, S7NeHom (lawY μ) By.u g d₁) →
        ((∃ Dtot, S7CompEmbedHom (lawZ μ) Bz.u h Dtot) ∧ ∃ d₂, S7NeHom (lawZ μ) Bz.u h d₂) →
        cl2norm (s7LawYZ μ) F ≠ 0 → cl2norm (lawY μ) g ≠ 0 → cl2norm (lawZ μ) h ≠ 0 →
        ‖s7CorrF μ F g h‖ ≤
          b * (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h) := by
  rw [s7Beta_le_iff μ hμ Bx.u By.u Bz.u n d d' hb]
  constructor
  · intro Hs F g h hF hFe hFn hFd hg hh nF ng nh
    have := Hs (s8Reindex e F) (s8Reindex e g) (s8Reindex e h)
      ((s8_mem_classF_iff μ hμ Bx.u e F d d').2 ⟨hF, hFe, hFn, hFd⟩)
      ((s8_mem_classG_iff (lawY μ) By.u e g).2 hg) ((s8_mem_classG_iff (lawZ μ) Bz.u e h).2 hh)
      (by rwa [s8_cl2norm_reindex]) (by rwa [s8_cl2norm_reindex]) (by rwa [s8_cl2norm_reindex])
    rwa [s8_corrF_reindex, s8_cl2norm_reindex, s8_cl2norm_reindex, s8_cl2norm_reindex] at this
  · intro Hs F' g' h' hF' hg' hh' nF ng nh
    obtain ⟨F, rfl⟩ : ∃ F, F' = s8Reindex e F :=
      ⟨s8Reindex e.symm F', by simpa using (reindex_symm_reindex e.symm F').symm⟩
    obtain ⟨g, rfl⟩ : ∃ g, g' = s8Reindex e g :=
      ⟨s8Reindex e.symm g', by simpa using (reindex_symm_reindex e.symm g').symm⟩
    obtain ⟨h, rfl⟩ : ∃ h, h' = s8Reindex e h :=
      ⟨s8Reindex e.symm h', by simpa using (reindex_symm_reindex e.symm h').symm⟩
    obtain ⟨hF, hFe, hFn, hFd⟩ := (s8_mem_classF_iff μ hμ Bx.u e F d d').1 hF'
    have := Hs F g h hF hFe hFn hFd ((s8_mem_classG_iff (lawY μ) By.u e g).1 hg')
      ((s8_mem_classG_iff (lawZ μ) Bz.u e h).1 hh')
      (by rwa [s8_cl2norm_reindex] at nF) (by rwa [s8_cl2norm_reindex] at ng)
      (by rwa [s8_cl2norm_reindex] at nh)
    rwa [← s8_corrF_reindex μ e, ← s8_cl2norm_reindex (s7LawYZ μ) e,
      ← s8_cl2norm_reindex (lawY μ) e, ← s8_cl2norm_reindex (lawZ μ) e] at this

/-- `δ_{n,d'} ≤ b` in the same form (for layer L4, `delta_inductive`, whose `F_t`, `F'_t` live on
`I = [n] \ {j}`): `F ∈ F_{n,d'}` on any `ι ≃ Fin n`, `g`, `h` arbitrary. -/
theorem s8_deltaParam_le_iff_generic (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (Sm : Finset X) (Bx : S7ModestBasis (lawX μ) σ Sm) {n : ℕ} (e : ι ≃ Fin n)
    (d' : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    s7DeltaParam μ hμ Bx.u n d' ≤ ENNReal.ofReal b ↔
      ∀ (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ),
        S7ConstOnCC hμ F → S7CCEffDegGE μ hμ Bx.u F d' →
        cl2norm (s7LawYZ μ) F ≠ 0 → cl2norm (lawY μ) g ≠ 0 → cl2norm (lawZ μ) h ≠ 0 →
        ‖s7CorrF μ F g h‖ ≤
          b * (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h) := by
  rw [s7DeltaParam_le_iff μ hμ Bx.u n d' hb]
  constructor
  · intro Hs F g h hF hFd nF ng nh
    have := Hs (s8Reindex e F) (s8Reindex e g) (s8Reindex e h)
      ((s8_mem_classFn_iff μ hμ Bx.u e F d').2 ⟨hF, hFd⟩)
      (by rwa [s8_cl2norm_reindex]) (by rwa [s8_cl2norm_reindex]) (by rwa [s8_cl2norm_reindex])
    rwa [s8_corrF_reindex, s8_cl2norm_reindex, s8_cl2norm_reindex, s8_cl2norm_reindex] at this
  · intro Hs F' g' h' hF' nF ng nh
    obtain ⟨F, rfl⟩ : ∃ F, F' = s8Reindex e F :=
      ⟨s8Reindex e.symm F', by simpa using (reindex_symm_reindex e.symm F').symm⟩
    obtain ⟨g, rfl⟩ : ∃ g, g' = s8Reindex e g :=
      ⟨s8Reindex e.symm g', by simpa using (reindex_symm_reindex e.symm g').symm⟩
    obtain ⟨h, rfl⟩ : ∃ h, h' = s8Reindex e h :=
      ⟨s8Reindex e.symm h', by simpa using (reindex_symm_reindex e.symm h').symm⟩
    obtain ⟨hF, hFd⟩ := (s8_mem_classFn_iff μ hμ Bx.u e F d').1 hF'
    have := Hs F g h hF hFd
      (by rwa [s8_cl2norm_reindex] at nF) (by rwa [s8_cl2norm_reindex] at ng)
      (by rwa [s8_cl2norm_reindex] at nh)
    rwa [← s8_corrF_reindex μ e, ← s8_cl2norm_reindex (s7LawYZ μ) e,
      ← s8_cl2norm_reindex (lawY μ) e, ← s8_cl2norm_reindex (lawZ μ) e] at this

end S8BetaTransport

section S8Bridge
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

omit [DecidableEq X] in
private lemma sum_filter_yz (f : X × Y × Z → ℝ) (y : Y) (z : Z) :
    ∑ p ∈ univ.filter (fun p : X × Y × Z => (p.2.1, p.2.2) = (y, z)), f p =
      ∑ x, f (x, y, z) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  simp [Prod.ext_iff, ite_and]

omit [DecidableEq X] [DecidableEq Z] in
private lemma sum_filter_y (f : X × Y × Z → ℝ) (y : Y) :
    ∑ p ∈ univ.filter (fun p : X × Y × Z => p.2.1 = y), f p = ∑ z, ∑ x, f (x, y, z) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm) ?_
  simp [Finset.sum_comm (γ := Z)]

omit [DecidableEq X] [DecidableEq Y] in
private lemma sum_filter_z (f : X × Y × Z → ℝ) (z : Z) :
    ∑ p ∈ univ.filter (fun p : X × Y × Z => p.2.2 = z), f p = ∑ y, ∑ x, f (x, y, z) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

/-- TYPING bridge: hypothesis 5 in the printed form ("`μ_{y,z}` is uniform") gives the product form
used by `s7_corrF_trivial_bound` and the Section 8 lemmas (`μ_{y,z}(y,z) = μ_y(y) μ_z(z)`: both marginals
of a uniform law on `Γ × Φ` are uniform). -/
theorem s8_hind_of_uniform (μ : FinProb (X × Y × Z))
    (hu : ∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) :
    ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z := by
  intro y z
  have hYZ : (s7LawYZ μ).prob (y, z) = ∑ x, μ.prob (x, y, z) :=
    sum_filter_yz μ.prob y z
  have hY : (lawY μ).prob y = ∑ z', ∑ x, μ.prob (x, y, z') := sum_filter_y μ.prob y
  have hZ : (lawZ μ).prob z = ∑ y', ∑ x, μ.prob (x, y', z) := sum_filter_z μ.prob z
  have hy : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos_iff.2 ⟨y⟩
  have hz : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos_iff.2 ⟨z⟩
  rw [hYZ, hY, hZ]
  simp only [hu]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end S8Bridge

end TrackB
end RestrictedPolynomials
end
