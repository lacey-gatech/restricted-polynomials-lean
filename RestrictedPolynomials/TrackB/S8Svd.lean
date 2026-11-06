module

public import RestrictedPolynomials.TrackB.S8SvdAux

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S8Svd
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the recomposition `∑_p κ_p g_p(y_I) g'_p(y_J)` of an SVD with respect to `[n] = I ⊔ {j}`. -/
def s8SvdSum {P α : Type} [Fintype P] (j : ι) (κ : P → ℝ) (gI : P → (S8Rest j → α) → ℂ)
    (gJ : P → α → ℂ) : (ι → α) → ℂ :=
  fun y => ∑ p, (κ p : ℂ) * (gI p (s8Restr j y) * gJ p (y j))

/-- the same with complex coefficients (after the phase normalisation of l. 4851-4854, the
coefficients `ψ_t, κ_r, ρ_s` are complex). -/
def s8SvdSumC {P α : Type} [Fintype P] (j : ι) (κ : P → ℂ) (gI : P → (S8Rest j → α) → ℂ)
    (gJ : P → α → ℂ) : (ι → α) → ℂ :=
  fun y => ∑ p, κ p * (gI p (s8Restr j y) * gJ p (y j))

/-- `M M^*` of Claim C.2 for `M(a, b) = g(b, a)` (rows indexed by the `j`-th letter), as an operator
on `L²(D)` of the `j`-th letter: `(M M^* v)(a) = ∑_{y_I} D^{⊗I}(y_I) g(y_I, a) ∑_b D(b) conj(g(y_I, b)) v(b)`.
For the uniform `D` of hypothesis 5 this is `|Σ|^{-n}` times the unnormalised matrix `M M^*`
of the source. -/
def s8GramOp {α : Type} [Fintype α] (D : FinProb α) (j : ι) (g : (ι → α) → ℂ) (v : α → ℂ) :
    α → ℂ :=
  fun a => ∑ yI : S8Rest j → α, (((D.pi (S8Rest j)).prob yI : ℝ) : ℂ) *
    (g (s8Glue j a yI) * ∑ b, ((D.prob b : ℝ) : ℂ) * (star (g (s8Glue j b yI)) * v b))

/-- the blocks of the basis `B_embed ∪ B_non-embed ∪ B_modest` for Def. C.1: one block per
embedding character `a` (`some a`) and one block `none` for `B_non-embed ∪ B_modest`
(for the `y`, `z` sides `B_modest = ∅`). -/
def s8Blk {H : Type} [AddCommGroup H] {K₁ K₂ : Type} :
    AddChar H ℂ ⊕ (K₁ ⊕ K₂) → Option (AddChar H ℂ) :=
  Sum.elim some (fun _ => none)

end S8Svd

section Calculus
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [Fintype α]

/-- the contraction `(contr D j g v)(y_I) = 𝔼_{a ∼ D} g(y_I, a) conj v(a)`. -/
private def contr (D : FinProb α) (j : ι) (g : (ι → α) → ℂ) (v : α → ℂ) :
    (S8Rest j → α) → ℂ :=
  fun yI => D.cexpect fun a => g (s8Glue j a yI) * star (v a)

omit [Fintype α] in
private lemma mono_glue {J : Type} (u : J → α → ℂ) (j : ι) (k : J) (cI : S8Rest j → J) :
    s7Mono u (s8Glue j k cI) = fun y => s7Mono u cI (s8Restr j y) * u k (y j) := by
  funext y
  simp only [s7Mono]
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => u (s8Glue j k cI i) (y i)) j]
  have : ∀ i : S8Rest j, s8Glue j k cI i = cI i := fun i => by simp [s8Glue, i.2]
  simp only [this, s8Glue_same, s8Restr]
  ring

private lemma onb_orth {D : FinProb α} {J : Type} [DecidableEq J] {u : J → α → ℂ}
    (hu : S7IsONB D u) (i k : J) : D.cinner (u i) (u k) = if i = k then 1 else 0 := by
  convert hu.1 i k

private lemma expansion1 (D : FinProb α) {J : Type} [Fintype J] (u : J → α → ℂ)
    (hu : S7IsONB D u) (v : α → ℂ) : v = ∑ k, D.cinner v (u k) • u k := by
  classical
  have hon := onb_orth hu
  have hv : v ∈ Submodule.span ℂ (Set.range u) := by rw [hu.2]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  have : ∀ k, D.cinner v (u k) = c k := by
    intro k
    rw [← hc, cinner_sum_left, Finset.sum_eq_single k]
    · rw [cinner_smul_left, hon]; simp
    · intro i _ hik; rw [cinner_smul_left, hon]; simp [hik]
    · simp
  simp only [this]
  exact hc.symm

private lemma coef_contract (D : FinProb α) {J : Type} [Fintype J] (u : J → α → ℂ)
    (hu : S7IsONB D u) (j : ι) (g : (ι → α) → ℂ) (v : α → ℂ) (cI : S8Rest j → J) :
    s7Coef D u (contr D j g v) cI =
      ∑ k, star (D.cinner v (u k)) * s7Coef D u g (s8Glue j k cI) := by
  have step1 : s7Coef D u (contr D j g v) cI =
      (D.pi ι).cinner g (fun y => s7Mono u cI (s8Restr j y) * v (y j)) := by
    unfold s7Coef FinProb.cinner
    rw [s8_cexpect_split D j (fun y => g y * star (s7Mono u cI (s8Restr j y) * v (y j)))]
    simp only [s8Restr_glue, s8Glue_same]
    simp only [FinProb.cexpect, contr, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      simp only [star_mul']; ring
  have step2 : (fun y : ι → α => s7Mono u cI (s8Restr j y) * v (y j)) =
      ∑ k, D.cinner v (u k) • s7Mono u (s8Glue j k cI) := by
    funext y
    simp only [mono_glue, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [congrFun (expansion1 D u hu v) (y j)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [step1, step2, cinner_sum_right]
  exact Finset.sum_congr rfl fun k _ => by rw [cinner_smul_right]; rfl

open scoped Classical in
private lemma countWhere_eq {J κ : Type} [Fintype κ] (P : J → Prop) (c : κ → J) :
    s7CountWhere P c = ∑ i, if P (c i) then 1 else 0 := by
  classical
  have : {i | P (c i)} = ↑(univ.filter fun i => P (c i)) := by ext; simp
  rw [s7CountWhere, this, Set.ncard_coe_finset, Finset.card_filter]

open scoped Classical in
omit [Fintype α] in
private lemma countWhere_glue {J : Type} (P : J → Prop) (j : ι) (k : J) (cI : S8Rest j → J) :
    s7CountWhere P (s8Glue j k cI) = s7CountWhere P cI + (if P k then 1 else 0) := by
  rw [countWhere_eq, countWhere_eq,
    Fintype.sum_eq_add_sum_subtype_ne (fun i => if P (s8Glue j k cI i) then 1 else 0) j]
  have : ∀ i : S8Rest j, s8Glue j k cI i = cI i := fun i => by simp [s8Glue, i.2]
  simp only [this, s8Glue_same]
  ring

private lemma cinner_expand {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    (π : FinProb β) (m : γ → β → ℂ) (hm : ∀ c c', π.cinner (m c) (m c') = if c = c' then 1 else 0)
    (a b : γ → ℂ) : π.cinner (∑ c, a c • m c) (∑ c, b c • m c) = ∑ c, a c * star (b c) := by
  rw [cinner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [cinner_smul_right, hm]; simp
  · intro c' _ hc'; rw [cinner_smul_right, hm]; simp [Ne.symm hc']
  · simp

private lemma cinner_coef (D : FinProb α) (hD : ∀ a, 0 < D.prob a) {J : Type} [Fintype J]
    [DecidableEq J] (u : J → α → ℂ) (hu : S7IsONB D u) {κ : Type} [Fintype κ] [DecidableEq κ]
    (f g : (κ → α) → ℂ) :
    (D.pi κ).cinner f g = ∑ c : κ → J, s7Coef D u f c * star (s7Coef D u g c) := by
  have hf := s7_fourier_expansion D hD u hu f
  have hg := s7_fourier_expansion D hD u hu g
  have hm := s7_mono_orthonormal (ι := κ) D u (onb_orth hu)
  conv_lhs => rw [hf, hg]
  exact cinner_expand _ _ hm _ _

theorem s8_svd_invariant_spaces (D : FinProb α) (hD : ∀ a, 0 < D.prob a) {J K : Type} [Fintype J]
    [DecidableEq J] (u : J → α → ℂ) (hu : S7IsONB D u) (blk : J → K) (b : K) (j : ι)
    (g : (ι → α) → ℂ) (d : ℕ) (hg : S7HomWrtBlock D u blk b g d) (v : α → ℂ)
    (hv : v ∈ Submodule.span ℂ (u '' {k | blk k = b})) :
    s8GramOp D j g v ∈ Submodule.span ℂ (u '' {k | blk k = b}) := by
  classical
  have hon := onb_orth hu
  -- coefficients of `v` vanish outside the block
  have hvz : ∀ l, blk l ≠ b → D.cinner v (u l) = 0 := by
    intro l hl
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hon]; simp only [ite_eq_right_iff, one_ne_zero]; intro h; exact hl (h ▸ hk)
    | zero => exact cinner_zero_left _ _
    | add x y _ _ hx hy => rw [cinner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [cinner_smul_left, hx, mul_zero]
  have hT := s8svdaux_inner_T (D.pi (S8Rest j)) D (fun r a => g (s8Glue j a r)) v
  have hcoefm : ∀ m cI, s7Coef D u (contr D j g (u m)) cI = s7Coef D u g (s8Glue j m cI) := by
    intro m cI
    rw [coef_contract D u hu, Finset.sum_eq_single m]
    · rw [hon]; simp
    · intro k _ hk; rw [hon]; simp [Ne.symm hk]
    · simp
  have hzero : ∀ m, blk m ≠ b → D.cinner (s8GramOp D j g v) (u m) = 0 := by
    intro m hm
    have h1 : D.cinner (s8GramOp D j g v) (u m) =
        (D.pi (S8Rest j)).cinner (contr D j g (u m)) (contr D j g v) := by
      have := hT (u m)
      rw [show s8GramOp D j g v = fun a => ∑ r, (((D.pi (S8Rest j)).prob r : ℝ) : ℂ) *
        (g (s8Glue j a r) * ∑ b, ((D.prob b : ℝ) : ℂ) * (star (g (s8Glue j b r)) * v b)) from rfl,
        this, cinner_def]
      exact Finset.sum_congr rfl fun r _ => by simp only [contr]; ring
    rw [h1, cinner_coef D hD u hu]
    refine Finset.sum_eq_zero fun cI _ => ?_
    rw [hcoefm m cI, coef_contract D u hu j g v cI, star_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : blk l = b
    · by_cases h1 : s7Coef D u g (s8Glue j m cI) = 0
      · rw [h1, zero_mul]
      · by_cases h2 : s7Coef D u g (s8Glue j l cI) = 0
        · rw [h2]; simp
        · exfalso
          have e1 := hg _ h1
          have e2 := hg _ h2
          unfold s7BlockDeg at e1 e2
          rw [countWhere_glue (fun j => blk j = b) j m cI] at e1
          rw [countWhere_glue (fun j => blk j = b) j l cI] at e2
          simp only [hm, hl, ↓reduceIte] at e1 e2
          omega
    · rw [star_mul', star_star, hvz l hl]; simp
  have hexp := expansion1 D u hu (s8GramOp D j g v)
  rw [hexp]
  refine Submodule.sum_mem _ fun m _ => ?_
  by_cases hm : blk m = b
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hm, rfl⟩)
  · rw [hzero m hm, zero_smul]; exact Submodule.zero_mem _

end Calculus

section S8SvdThms
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [Fintype α] {H : Type} [AddCommGroup H]
  [Fintype H] {K₁ K₂ : Type}

omit [Fintype α] [Fintype H] in
private lemma blockDeg_some (a : AddChar H ℂ) (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7BlockDeg (s8Blk (H := H) (K₁ := K₁) (K₂ := K₂)) (some a) c = s7EmbedDegA a c := by
  unfold s7BlockDeg s7EmbedDegA s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  generalize c i = x
  rcases x with x | y <;> simp [s8Blk]

omit [Fintype α] [Fintype H] in
private lemma blockDeg_none (c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7BlockDeg (s8Blk (H := H) (K₁ := K₁) (K₂ := K₂)) none c = s7NeDeg c := by
  unfold s7BlockDeg s7NeDeg s7CountWhere
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  generalize c i = x
  rcases x with x | y <;> simp [s8Blk]

/-- `S7CompEmbedHom` is Def. C.1 homogeneity for the blocks `some a` (the embedding degrees). -/
theorem s8_compEmbedHom_iff_homWrtBlock (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (f : (ι → α) → ℂ) (Dtot : ℕ) :
    S7CompEmbedHom D u f Dtot ↔
      ∃ Da : AddChar H ℂ → ℕ, ∑ a, Da a = Dtot ∧
        ∀ a, S7HomWrtBlock D u s8Blk (some a) f (Da a) := by
  unfold S7CompEmbedHom S7HomWrtBlock
  refine exists_congr fun Da => and_congr_right fun _ => ?_
  simp only [blockDeg_some]
  exact ⟨fun h a c hc => h c hc a, fun h c hc a => h a c hc⟩

/-- `S7NeHom` is Def. C.1 homogeneity for the block `none`. -/
theorem s8_neHom_iff_homWrtBlock (D : FinProb α) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ)
    (f : (ι → α) → ℂ) (d : ℕ) :
    S7NeHom D u f d ↔ S7HomWrtBlock D u s8Blk none f d := by
  unfold S7NeHom S7HomWrtBlock
  simp only [blockDeg_none]

omit [Fintype H] in
private lemma pi_prob_pos (D : FinProb α) (hD : ∀ a, 0 < D.prob a) {κ : Type} [Fintype κ] [DecidableEq κ]
    (r : κ → α) : 0 < (D.pi κ).prob r :=
  Finset.prod_pos fun i _ => hD _

private lemma cinner_svdSum {P : Type} [Fintype P] [DecidableEq P] (D : FinProb α) (j : ι)
    (κ : P → ℝ) (gI : P → (S8Rest j → α) → ℂ) (gJ : P → α → ℂ)
    (hI : ∀ p q, κ p ≠ 0 → κ q ≠ 0 →
      (D.pi (S8Rest j)).cinner (gI p) (gI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, κ p ≠ 0 → κ q ≠ 0 → D.cinner (gJ p) (gJ q) = if p = q then 1 else 0) :
    (D.pi ι).cinner (s8SvdSum j κ gI gJ) (s8SvdSum j κ gI gJ) = ((∑ p, κ p ^ 2 : ℝ) : ℂ) := by
  have hs : s8SvdSum j κ gI gJ =
      ∑ p, (κ p : ℂ) • (fun y : ι → α => gI p (s8Restr j y) * gJ p (y j)) := by
    funext y; simp [s8SvdSum]
  rw [hs, cinner_sum_left]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single p]
  · rw [cinner_smul_right, s8_cinner_glue]
    by_cases hp : κ p = 0
    · simp [hp]
    · rw [hI p p hp hp, hJ p p hp hp]
      simp [pow_two]
  · intro q _ hq
    rw [cinner_smul_right, s8_cinner_glue]
    by_cases hp : κ p = 0
    · simp [hp]
    · by_cases hq0 : κ q = 0
      · simp [hq0]
      · rw [hI p q hp hq0]; simp [Ne.symm hq]
  · simp

section DegGlue
variable {ι : Type} [Fintype ι] [DecidableEq ι] {H : Type} [AddCommGroup H] {K₁ K₂ : Type}

private lemma ne_glue_inl (j : ι) (χ : AddChar H ℂ) (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7NeDeg (s8Glue j (Sum.inl χ) cI) = s7NeDeg cI := by
  unfold s7NeDeg
  rw [countWhere_glue]
  simp

private lemma ne_glue_inr (j : ι) (x : K₁ ⊕ K₂) (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7NeDeg (s8Glue j (Sum.inr x) cI) = s7NeDeg cI + 1 := by
  unfold s7NeDeg
  rw [countWhere_glue]
  simp

private lemma eff_glue_inl (j : ι) (χ : AddChar H ℂ) (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EffDeg (s8Glue j (Sum.inl χ) cI) = s7EffDeg cI := by
  unfold s7EffDeg
  rw [countWhere_glue]
  simp

private lemma eff_glue_le (j : ι) (k : AddChar H ℂ ⊕ (K₁ ⊕ K₂))
    (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EffDeg (s8Glue j k cI) ≤ s7EffDeg cI + 1 := by
  unfold s7EffDeg
  rw [countWhere_glue]
  split_ifs <;> omega

private lemma eff_ge_of_glue (j : ι) (k : AddChar H ℂ ⊕ (K₁ ⊕ K₂))
    (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) (d' : ℕ) (h : d' ≤ s7EffDeg (s8Glue j k cI)) :
    d' - 1 ≤ s7EffDeg cI := by
  have := eff_glue_le j k cI
  omega

private lemma emb_glue_inl (j : ι) (χ a : AddChar H ℂ)
    (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EmbedDegA a (s8Glue j (Sum.inl χ) cI) = s7EmbedDegA a cI + (if χ = a then 1 else 0) := by
  unfold s7EmbedDegA
  rw [countWhere_glue]
  simp

private lemma emb_glue_inr (j : ι) (x : K₁ ⊕ K₂) (a : AddChar H ℂ)
    (cI : S8Rest j → AddChar H ℂ ⊕ (K₁ ⊕ K₂)) :
    s7EmbedDegA a (s8Glue j (Sum.inr x) cI) = s7EmbedDegA a cI := by
  unfold s7EmbedDegA
  rw [countWhere_glue]
  simp

end DegGlue

private lemma sum_sq_eq_one {P : Type} [Fintype P] [DecidableEq P] (D : FinProb α) (j : ι)
    (κ : P → ℝ) (gI : P → (S8Rest j → α) → ℂ) (gJ : P → α → ℂ) (g : (ι → α) → ℂ)
    (hg : g = s8SvdSum j κ gI gJ)
    (hI : ∀ p q, κ p ≠ 0 → κ q ≠ 0 →
      (D.pi (S8Rest j)).cinner (gI p) (gI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, κ p ≠ 0 → κ q ≠ 0 → D.cinner (gJ p) (gJ q) = if p = q then 1 else 0)
    (hnorm : cl2norm D g = 1) : ∑ p, κ p ^ 2 = 1 := by
  have h1 := cinner_svdSum D j κ gI gJ hI hJ
  rw [← hg, ← cl2sq_cast] at h1
  have h2 : cl2sq D g = 1 := by
    have : Real.sqrt (cl2sq D g) = 1 := hnorm
    rwa [Real.sqrt_eq_one] at this
  rw [h2] at h1
  exact_mod_cast h1.symm

private lemma coef_gI_ne {P : Type} {J : Type} [Fintype J] (D : FinProb α) (u : J → α → ℂ)
    (hu : S7IsONB D u) (j : ι) (g : (ι → α) → ℂ) (κ : P → ℝ) (gI : P → (S8Rest j → α) → ℂ)
    (gJ : P → α → ℂ)
    (hCF : ∀ p, κ p ≠ 0 → ∀ r, (κ p : ℂ) * gI p r = contr D j g (gJ p) r)
    (hz : ∀ p, κ p = 0 → gI p = 0) (p : P) (cI : S8Rest j → J)
    (h : s7Coef D u (gI p) cI ≠ 0) :
    ∃ k, D.cinner (gJ p) (u k) ≠ 0 ∧ s7Coef D u g (s8Glue j k cI) ≠ 0 := by
  by_cases hp : κ p = 0
  · exfalso; apply h
    rw [hz p hp]
    exact cinner_zero_left _ _
  · have h1 : (κ p : ℂ) • gI p = contr D j g (gJ p) := funext fun r => hCF p hp r
    have h2 : s7Coef D u (contr D j g (gJ p)) cI = (κ p : ℂ) * s7Coef D u (gI p) cI := by
      rw [← h1]; exact cinner_smul_left _ _ _ _
    rw [coef_contract D u hu] at h2
    have h3 : ∑ k, star (D.cinner (gJ p) (u k)) * s7Coef D u g (s8Glue j k cI) ≠ 0 := by
      rw [h2]; exact mul_ne_zero (by exact_mod_cast hp) h
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
    refine ⟨k, fun h0 => hk (by simp [h0]), fun h0 => hk (by simp [h0])⟩

/-- the plain SVD of a function of `ι → α` with respect to `[n] = I ⊔ {j}`, for any positive `D`:
all singular values positive, and the contraction formula `κ_t gI_t = ⟨g, gJ_t⟩_j`. -/
private theorem plain_core (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (j : ι)
    (g : (ι → α) → ℂ) :
    ∃ (s : ℕ) (κ : Fin s → ℝ) (gI : Fin s → (S8Rest j → α) → ℂ) (gJ : Fin s → α → ℂ),
      (∀ t, 0 < κ t) ∧ g = s8SvdSum j κ gI gJ ∧
      (∀ t t', (D.pi (S8Rest j)).cinner (gI t) (gI t') = if t = t' then 1 else 0) ∧
      (∀ t t', D.cinner (gJ t) (gJ t') = if t = t' then 1 else 0) ∧
      (∀ t r, (κ t : ℂ) * gI t r = contr D j g (gJ t) r) := by
  classical
  obtain ⟨s, κ, gI, gJ, hκ0, hκt, hdec, -, -, hIo, hJo, hCF, -⟩ :=
    s8svdaux_svd_peel (Λ := PEmpty) (DR := D.pi (S8Rest j)) (DA := D)
      (pi_prob_pos D hD) hD (fun r a => g (s8Glue j a r)) (fun χ => χ.elim)
      (fun χ => χ.elim) (fun χ => χ.elim)
  refine ⟨s, fun t => κ (Sum.inr t), fun t => gI (Sum.inr t), fun t => gJ (Sum.inr t),
    hκt, ?_, fun t t' => ?_, fun t t' => ?_, fun t r => hCF (Sum.inr t) r (hκt t).ne'⟩
  · funext y
    have := hdec (s8Restr j y) (y j)
    simp only [s8Glue_restr, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty,
      zero_add] at this
    simpa [s8SvdSum] using this
  · simpa using hIo (Sum.inr t) (Sum.inr t') (hκt t).ne' (hκt t').ne'
  · simpa using hJo (Sum.inr t) (Sum.inr t') (hκt t).ne' (hκt t').ne'

/-- the plain structured SVD of a function `g` of `ι → α`, for any basis `B` of Def. 7.1 and any
positive `D`: Claim 8.4 together with the effective-degree inheritance of Claim 8.5. -/
private theorem plain_svd (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (γ : α → H) {Sm : Finset α}
    (B : S7ModestBasis D γ Sm) (j : ι) (g : (ι → α) → ℂ) (d d' : ℕ)
    (hge : ∃ Dtot, S7CompEmbedHom D B.u g Dtot) (hgd : S7NeHom D B.u g d)
    (hgf : S7EffDegGE D B.u g d') (hnorm : cl2norm D g = 1) :
    ∃ (s : ℕ) (κ : AddChar H ℂ ⊕ Fin s → ℝ)
      (gI : AddChar H ℂ ⊕ Fin s → (S8Rest j → α) → ℂ) (gJ : AddChar H ℂ ⊕ Fin s → α → ℂ),
      (∀ p, 0 ≤ κ p) ∧ g = s8SvdSum j κ gI gJ ∧
      (∀ χ : AddChar H ℂ, gJ (Sum.inl χ) ∈ Submodule.span ℂ {fun a => χ (γ a)} ∧
        (∃ Dtot, S7CompEmbedHom D B.u (gI (Sum.inl χ)) Dtot) ∧
        S7NeHom D B.u (gI (Sum.inl χ)) d ∧ S7EffDegGE D B.u (gI (Sum.inl χ)) d') ∧
      (∀ r : Fin s, ((∀ Da : AddChar H ℂ → ℕ,
          (∀ c, s7Coef D B.u g c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a) →
          ∀ c, s7Coef D B.u (gI (Sum.inr r)) c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a) ∧
        S7NeHom D B.u (gI (Sum.inr r)) (d - 1) ∧ S7EffDegGE D B.u (gI (Sum.inr r)) (d' - 1)) ∧
        gJ (Sum.inr r) ∈ s7Perp D (embedSpan γ)) ∧
      (∀ p q, κ p ≠ 0 → κ q ≠ 0 →
        (D.pi (S8Rest j)).cinner (gI p) (gI q) = if p = q then 1 else 0) ∧
      (∀ p q, κ p ≠ 0 → κ q ≠ 0 → D.cinner (gJ p) (gJ q) = if p = q then 1 else 0) ∧
      ∑ p, κ p ^ 2 = 1 := by
  classical
  have hONB := s7_modestBasis_isONB D γ Sm hD B
  have hon := onb_orth hONB
  obtain ⟨Dtot, Da, hDa, hDa'⟩ := hge
  -- invariance of the embedding lines
  have hT : ∀ χ : AddChar H ℂ, ∃ c : ℂ, ∀ a,
      (∑ r : S8Rest j → α, (((D.pi (S8Rest j)).prob r : ℝ) : ℂ) * (g (s8Glue j a r) *
        ∑ b, ((D.prob b : ℝ) : ℂ) * (star (g (s8Glue j b r)) * B.u (Sum.inl χ) b))) =
        c * B.u (Sum.inl χ) a := by
    intro χ
    have hg : S7HomWrtBlock D B.u s8Blk (some χ) g (Da χ) := fun c hc => by
      rw [blockDeg_some]; exact hDa' c hc χ
    have hmem : s8GramOp D j g (B.u (Sum.inl χ)) ∈
        Submodule.span ℂ (B.u '' {k | s8Blk k = some χ}) :=
      s8_svd_invariant_spaces D hD B.u hONB s8Blk (some χ) j g (Da χ) hg _
        (Submodule.subset_span ⟨Sum.inl χ, rfl, rfl⟩)
    have hset : B.u '' {k | s8Blk k = some χ} = {B.u (Sum.inl χ)} := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        rcases k with a | k
        · have : a = χ := by simpa [s8Blk] using hk
          subst this; rfl
        · simp [s8Blk] at hk
      · rintro rfl
        exact ⟨Sum.inl χ, rfl, rfl⟩
    rw [hset, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, fun a => by
      have := congrFun hc a
      simpa [s8GramOp] using this.symm⟩
  have hR : ∀ r : S8Rest j → α, 0 < (D.pi (S8Rest j)).prob r := pi_prob_pos D hD
  have heo : ∀ χ ψ : AddChar H ℂ, D.cinner (fun a => χ (γ a)) (fun a => ψ (γ a)) =
      if χ = ψ then 1 else 0 := fun χ ψ => by convert B.embed_orthonormal χ ψ
  have hT' : ∀ χ : AddChar H ℂ, ∃ c : ℂ, ∀ a,
      (∑ r : S8Rest j → α, (((D.pi (S8Rest j)).prob r : ℝ) : ℂ) * (g (s8Glue j a r) *
        ∑ b, ((D.prob b : ℝ) : ℂ) * (star (g (s8Glue j b r)) * (fun a => χ (γ a)) b))) =
        c * (fun a => χ (γ a)) a := hT
  obtain ⟨s, κ, gI, gJ, hκ0, hκt, hdec, hJe, hperp, hIo, hJo, hCF, hz⟩ :=
    s8svdaux_svd_peel (Λ := AddChar H ℂ) (DR := D.pi (S8Rest j)) (DA := D) hR hD
      (fun r a => g (s8Glue j a r)) (fun χ a => χ (γ a)) heo hT'
  have hcoef := coef_gI_ne D B.u hONB j g κ gI gJ (fun p hp r => hCF p r hp) hz
  have hdecg : g = s8SvdSum j κ gI gJ := by
    funext y
    have := hdec (s8Restr j y) (y j)
    simp only [s8Glue_restr] at this
    simpa [s8SvdSum] using this
  have hsum : ∑ p, κ p ^ 2 = 1 := sum_sq_eq_one D j κ gI gJ g hdecg hIo hJo hnorm
  have kinl : ∀ (χ : AddChar H ℂ) cI, s7Coef D B.u (gI (Sum.inl χ)) cI ≠ 0 →
      s7Coef D B.u g (s8Glue j (Sum.inl χ) cI) ≠ 0 := by
    intro χ cI h
    obtain ⟨k, hk1, hk2⟩ := hcoef (Sum.inl χ) cI h
    rw [hJe χ] at hk1
    have : Sum.inl χ = k := by
      by_contra hne
      apply hk1
      have := hon (Sum.inl χ) k
      simp only [hne, ↓reduceIte] at this
      exact this
    subst this
    exact hk2
  have kinr : ∀ (r : Fin s) cI, s7Coef D B.u (gI (Sum.inr r)) cI ≠ 0 →
      ∃ x, s7Coef D B.u g (s8Glue j (Sum.inr x) cI) ≠ 0 := by
    intro r cI h
    obtain ⟨k, hk1, hk2⟩ := hcoef (Sum.inr r) cI h
    rcases k with a | x
    · exact absurd (hperp r a) hk1
    · exact ⟨x, hk2⟩
  refine ⟨s, κ, gI, gJ, hκ0, hdecg, ?_, ?_, hIo, hJo, hsum⟩
  · intro χ
    refine ⟨?_, ⟨∑ a, (Da a - if χ = a then 1 else 0), fun a => Da a - if χ = a then 1 else 0,
      rfl, fun cI hc a => ?_⟩, fun cI hc => ?_, fun cI hc => ?_⟩
    · rw [hJe χ]; exact Submodule.mem_span_singleton_self _
    · have h1 := hDa' _ (kinl χ cI hc) a
      rw [emb_glue_inl] at h1
      show s7EmbedDegA a cI = Da a - if χ = a then 1 else 0
      split_ifs at h1 ⊢ <;> omega
    · have h1 := hgd _ (kinl χ cI hc)
      rwa [ne_glue_inl] at h1
    · have h1 := hgf _ (kinl χ cI hc)
      rwa [eff_glue_inl] at h1
  · intro r
    refine ⟨⟨fun Da' hDa'' cI hc a => ?_, fun cI hc => ?_, fun cI hc => ?_⟩, ?_⟩
    · obtain ⟨x, hx⟩ := kinr r cI hc
      have h1 := hDa'' _ hx a
      rwa [emb_glue_inr] at h1
    · obtain ⟨x, hx⟩ := kinr r cI hc
      have h1 := hgd _ hx
      rw [ne_glue_inr] at h1
      omega
    · obtain ⟨x, hx⟩ := kinr r cI hc
      exact eff_ge_of_glue j _ cI d' (hgf _ hx)
    · intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        exact hperp r χ
      | zero => exact cinner_zero_right _ _
      | add x y _ _ hx hy => rw [cinner_add_right, hx, hy, add_zero]
      | smul a x _ hx => rw [cinner_smul_right, hx, mul_zero]

/-- Paper IV `claim:svd` (Claim 8.4, l. 4727-4745; proof App. C l. 9465-9524), for the `y`-side basis
`B` of `L²(μ_y)` (`Sm = ∅`; by genericity in the alphabet this is also the `Φ`-analogue for `h`, which
the source uses at l. 4841-4842 but never states). `P = {p | κ_p ≠ 0}`; the degree `d` of items (1)-(2)
is the non-embedding degree of `g`, `d - 1` is truncated subtraction (for `d = 0` no
`r`-term has `κ_r ≠ 0`). The coefficient `κ` is the printed one (`√` of the eigenvalue of `M M^*`). -/
theorem s8_svd (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (γ : α → H)
    (B : S7ModestBasis D γ (∅ : Finset α)) (j : ι) (g : (ι → α) → ℂ) (d : ℕ)
    (hge : ∃ Dtot, S7CompEmbedHom D B.u g Dtot) (hgd : S7NeHom D B.u g d)
    (hnorm : cl2norm D g = 1) :
    ∃ (s : ℕ) (κ : AddChar H ℂ ⊕ Fin s → ℝ)
      (gI : AddChar H ℂ ⊕ Fin s → (S8Rest j → α) → ℂ) (gJ : AddChar H ℂ ⊕ Fin s → α → ℂ),
      (∀ p, 0 ≤ κ p) ∧ g = s8SvdSum j κ gI gJ ∧
      (∀ χ : AddChar H ℂ, gJ (Sum.inl χ) ∈ Submodule.span ℂ {fun a => χ (γ a)} ∧
        (∃ Dtot, S7CompEmbedHom D B.u (gI (Sum.inl χ)) Dtot) ∧
        S7NeHom D B.u (gI (Sum.inl χ)) d) ∧
      (∀ r : Fin s, ((∃ Dtot, S7CompEmbedHom D B.u (gI (Sum.inr r)) Dtot) ∧
        S7NeHom D B.u (gI (Sum.inr r)) (d - 1)) ∧ gJ (Sum.inr r) ∈ s7Perp D (embedSpan γ)) ∧
      (∀ p q, κ p ≠ 0 → κ q ≠ 0 →
        (D.pi (S8Rest j)).cinner (gI p) (gI q) = if p = q then 1 else 0) ∧
      (∀ p q, κ p ≠ 0 → κ q ≠ 0 → D.cinner (gJ p) (gJ q) = if p = q then 1 else 0) ∧
      ∑ p, κ p ^ 2 = 1 := by
  obtain ⟨s, κ, gI, gJ, h0, hg, hχ, hr, hI, hJ, hs⟩ := plain_svd D hD γ B j g d 0 hge hgd
    (fun _ _ => Nat.zero_le _) hnorm
  refine ⟨s, κ, gI, gJ, h0, hg, fun χ => ⟨(hχ χ).1, (hχ χ).2.1, (hχ χ).2.2.1⟩, fun r => ?_,
    hI, hJ, hs⟩
  obtain ⟨Dtot, Da, hDa, hDa'⟩ := hge
  refine ⟨⟨⟨∑ a, Da a, Da, rfl, (hr r).1.1 Da hDa'⟩, (hr r).1.2.1⟩, (hr r).2⟩

/-- the plain SVD without blocks, with the effective-degree inheritance of Claim 9.5. -/
private theorem plain_nonhomo (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H) {Sm : Finset α}
    (B : S7ModestBasis D σ Sm) (j : ι) (g : (ι → α) → ℂ) (d' : ℕ)
    (hgf : S7EffDegGE D B.u g d') (hnorm : cl2norm D g = 1) :
    ∃ (s : ℕ) (κ : Fin s → ℝ) (gI : Fin s → (S8Rest j → α) → ℂ) (gJ : Fin s → α → ℂ),
      (∀ t, 0 ≤ κ t) ∧ g = s8SvdSum j κ gI gJ ∧
      (∀ t t', (D.pi (S8Rest j)).cinner (gI t) (gI t') = if t = t' then 1 else 0) ∧
      (∀ t t', D.cinner (gJ t) (gJ t') = if t = t' then 1 else 0) ∧
      (∀ t, S7EffDegGE D B.u (gI t) (d' - 1)) ∧ ∑ t, κ t ^ 2 = 1 := by
  classical
  obtain ⟨s, κ, gI, gJ, hκ, hg, hI, hJ, hCF⟩ := plain_core D hD j g
  refine ⟨s, κ, gI, gJ, fun t => (hκ t).le, hg, hI, hJ, fun t cI hc => ?_,
    sum_sq_eq_one D j κ gI gJ g hg (fun p q _ _ => hI p q) (fun p q _ _ => hJ p q) hnorm⟩
  obtain ⟨k, -, hk⟩ := coef_gI_ne D B.u (s7_modestBasis_isONB D σ Sm hD B) j g κ gI gJ
    (fun p _ r => hCF p r) (fun p h => absurd h (hκ p).ne') t cI hc
  exact eff_ge_of_glue j k cI d' (hgf _ hk)

end S8SvdThms



section S8SvdEffective
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H]
  [DecidableEq H]

private lemma pi_unit_cexpect {β : Type} [Fintype β] (π : FinProb β) (G : (Unit → β) → ℂ) :
    (π.pi Unit).cexpect G = π.cexpect (fun a => G (fun _ => a)) := by
  unfold FinProb.cexpect
  exact Fintype.sum_equiv (Equiv.funUnique Unit β) _ _ (fun x => by simp [FinProb.pi])

/-- the one-letter isometry `⟨W₁ f, W₁ f'⟩_{μ_{y,z}} = ⟨f, f'⟩_{μ_x}`. -/
private lemma s8W1_cinner (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (f f' : X → ℂ) :
    (s7LawYZ μ).cinner (s8W1 hμ f) (s8W1 hμ f') = (lawX μ).cinner f f' := by
  have h := s7_W_cinner μ hμ (ι := Unit) (fun x => f (x ())) (fun x => f' (x ()))
  unfold FinProb.cinner at h ⊢
  rw [pi_unit_cexpect, pi_unit_cexpect] at h
  simpa [s7W, s8W1] using h

private lemma s8W1_cexpect (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (f : X → ℂ) :
    (s7LawYZ μ).cexpect (s8W1 hμ f) = (lawX μ).cexpect f := by
  have h := s8W1_cinner μ hμ f (fun _ => 1)
  have e : s8W1 hμ f = fun a => f (s7Pre hμ a.1 a.2) := rfl
  rw [e]
  simpa [FinProb.cinner, s8W1] using h

private lemma pre_glue (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (j : ι)
    (a : Y × Z) (yI : S8Rest j → Y × Z) :
    (fun i => s7Pre hμ ((s8Glue j a yI) i).1 ((s8Glue j a yI) i).2) =
      s8Glue j (s7Pre hμ a.1 a.2) (fun i => s7Pre hμ (yI i).1 (yI i).2) := by
  funext i
  by_cases h : i = j
  · subst h; simp [s8Glue]
  · simp [s8Glue, h]

section Transfer
variable {K₁ K₂ : Type} (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
  (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) {κ : Type} [Fintype κ] [DecidableEq κ]
  (f : (κ → X) → ℂ)

private lemma ccComp_W_iff (Dtot : ℕ) :
    S7CCCompEmbedHom μ hμ u (s7W hμ f) Dtot ↔ S7CompEmbedHom (lawX μ) u f Dtot := by
  simp only [S7CCCompEmbedHom, S7CompEmbedHom, s7CCCoef_W]

private lemma ccNe_W_iff (d : ℕ) :
    S7CCNeHom μ hμ u (s7W hμ f) d ↔ S7NeHom (lawX μ) u f d := by
  simp only [S7CCNeHom, S7NeHom, s7CCCoef_W]

private lemma ccEff_W_iff (d : ℕ) :
    S7CCEffDegGE μ hμ u (s7W hμ f) d ↔ S7EffDegGE (lawX μ) u f d := by
  simp only [S7CCEffDegGE, S7EffDegGE, s7CCCoef_W]

end Transfer

/-- recomposition of a plain SVD of `f` into one of `W f` (`W` acts factorwise). -/
private lemma W_svdSum (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (j : ι)
    {P : Type} [Fintype P] (κ : P → ℝ) (fI : P → (S8Rest j → X) → ℂ) (fJ : P → X → ℂ)
    (f : (ι → X) → ℂ) (hf : f = s8SvdSum j κ fI fJ) :
    s7W hμ f = s8SvdSum j κ (fun p => s7W hμ (fI p)) (fun p => s8W1 hμ (fJ p)) := by
  funext w
  exact congrFun hf (fun i => s7Pre hμ (w i).1 (w i).2)

/-- Paper IV `claim:svd-effective` (Claim 8.5, l. 4756-4778; proof App. C l. 9528-9554, a sketch). `F` is a
function of `(y, z)`, `L²(μ_{y,z})`-normalised; `F'_χ ∈ span{W ∘ χ ∘ σ}` is `s8W1`; `F'_t ⟂` all
embedding functions is `⟪F'_t, W ∘ χ ∘ σ⟫ = 0` for every `χ`. The degrees of `F_χ`, `F_t` are those
of the source (`d`, `d`; `d - 1`, `d' - 1`; truncated subtraction); for `F_t` the printed "completely
embedding homogeneous" is read as "has every embedding-degree vector `D_a` that `F` has" (the J-factor
is non-embedding; needed for `F̃ ∈ F_{n-1,d-1,d'-1}` in `#combine-F-t`, which the source does not state).
Item (3) is for every index
(the zero function is allowed where `ψ = 0`); orthonormality (4), (5) is on `P = {ψ ≠ 0}`. The
decomposition is for the basis `Bx` of Def. 7.1 (any `Bx`). -/
theorem s8_svd_effective (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (σ : X → H) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX μ) σ Sm) (j : ι) (F : (ι → Y × Z) → ℂ) (d d' : ℕ)
    (hF : S7ConstOnCC hμ F) (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (hFn : S7CCNeHom μ hμ Bx.u F d) (hFd : S7CCEffDegGE μ hμ Bx.u F d')
    (hnorm : cl2norm (s7LawYZ μ) F = 1) :
    ∃ (s : ℕ) (ψ : AddChar H ℂ ⊕ Fin s → ℝ)
      (FI : AddChar H ℂ ⊕ Fin s → (S8Rest j → Y × Z) → ℂ)
      (FJ : AddChar H ℂ ⊕ Fin s → Y × Z → ℂ),
      (∀ p, 0 ≤ ψ p) ∧ F = s8SvdSum j ψ FI FJ ∧
      (∀ χ : AddChar H ℂ, FJ (Sum.inl χ) ∈ Submodule.span ℂ {s8W1 hμ (fun x => χ (σ x))} ∧
        (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u (FI (Sum.inl χ)) Dtot) ∧
        S7CCNeHom μ hμ Bx.u (FI (Sum.inl χ)) d ∧ S7CCEffDegGE μ hμ Bx.u (FI (Sum.inl χ)) d') ∧
      (∀ r : Fin s, ((∀ Da : AddChar H ℂ → ℕ,
          (∀ c : ι → Bx.J, s7CCCoef μ hμ Bx.u F c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a) →
          ∀ c : S8Rest j → Bx.J, s7CCCoef μ hμ Bx.u (FI (Sum.inr r)) c ≠ 0 →
            ∀ a, s7EmbedDegA a c = Da a) ∧
        S7CCNeHom μ hμ Bx.u (FI (Sum.inr r)) (d - 1) ∧
        S7CCEffDegGE μ hμ Bx.u (FI (Sum.inr r)) (d' - 1)) ∧
        ∀ χ : AddChar H ℂ, (s7LawYZ μ).cinner (FJ (Sum.inr r)) (s8W1 hμ (fun x => χ (σ x))) = 0) ∧
      (∀ p, S7ConstOnCC hμ (FI p) ∧ ∃ f : X → ℂ, s8W1 hμ f = FJ p) ∧
      (∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
        ((s7LawYZ μ).pi (S8Rest j)).cinner (FI p) (FI q) = if p = q then 1 else 0) ∧
      (∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
        (s7LawYZ μ).cinner (FJ p) (FJ q) = if p = q then 1 else 0) ∧
      ∑ p, ψ p ^ 2 = 1 := by
  classical
  obtain ⟨f₀, rfl⟩ := hF
  have hnorm' : cl2norm (lawX μ) f₀ = 1 := by rwa [s7_cl2norm_W] at hnorm
  obtain ⟨Dtot, hDtot⟩ := hFe
  obtain ⟨s, κ, fI, fJ, h0, hg, hχ, hr, hIo, hJo, hs⟩ := plain_svd (lawX μ) hDx σ Bx j f₀ d d'
    ⟨Dtot, (ccComp_W_iff μ hμ Bx.u f₀ Dtot).1 hDtot⟩ ((ccNe_W_iff μ hμ Bx.u f₀ d).1 hFn)
    ((ccEff_W_iff μ hμ Bx.u f₀ d').1 hFd) hnorm'
  refine ⟨s, κ, fun p => s7W hμ (fI p), fun p => s8W1 hμ (fJ p), h0,
    W_svdSum μ hμ j κ fI fJ f₀ hg, fun χ => ?_, fun r => ?_, fun p => ⟨⟨fI p, rfl⟩, ⟨fJ p, rfl⟩⟩,
    fun p q hp hq => ?_, fun p q hp hq => ?_, hs⟩
  · obtain ⟨hs1, ⟨Dt, hDt⟩, hn, he⟩ := hχ χ
    refine ⟨?_, ⟨Dt, (ccComp_W_iff μ hμ Bx.u _ Dt).2 hDt⟩, (ccNe_W_iff μ hμ Bx.u _ d).2 hn,
      (ccEff_W_iff μ hμ Bx.u _ d').2 he⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hs1
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by
      show c • s8W1 hμ (fun x => χ (σ x)) = s8W1 hμ (fJ (Sum.inl χ))
      rw [← hc]; rfl⟩
  · obtain ⟨⟨hinh, hn, he⟩, hperp⟩ := hr r
    refine ⟨⟨fun Da hDa c hc a => hinh Da (fun c' hc' => hDa c' (by rwa [s7CCCoef_W])) c
      (by rwa [s7CCCoef_W] at hc) a, (ccNe_W_iff μ hμ Bx.u _ _).2 hn,
      (ccEff_W_iff μ hμ Bx.u _ _).2 he⟩, fun χ => ?_⟩
    rw [s8W1_cinner]
    exact hperp _ (Submodule.subset_span ⟨χ, rfl⟩)
  · rw [s7_W_cinner]; exact hIo p q hp hq
  · rw [s8W1_cinner]; exact hJo p q hp hq

/-- Paper IV `claim:svd-effective-nonhomo` (Claim 9.5, l. 5276-5300, proof omitted in the source): the SVD
of a function `F` constant on connected components with effective degree at least `d'` (no
homogeneity). The index set is `Fin s`; orthonormality is for all indices (only positive singular
values are kept). -/
theorem s8_svd_effective_nonhomo (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (σ : X → H) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX μ) σ Sm) (j : ι) (F : (ι → Y × Z) → ℂ) (d' : ℕ)
    (hF : S7ConstOnCC hμ F) (hFd : S7CCEffDegGE μ hμ Bx.u F d')
    (hnorm : cl2norm (s7LawYZ μ) F = 1) :
    ∃ (s : ℕ) (ψ : Fin s → ℝ) (FI : Fin s → (S8Rest j → Y × Z) → ℂ) (FJ : Fin s → Y × Z → ℂ),
      (∀ t, 0 ≤ ψ t) ∧ F = s8SvdSum j ψ FI FJ ∧
      (∀ t t', ((s7LawYZ μ).pi (S8Rest j)).cinner (FI t) (FI t') = if t = t' then 1 else 0) ∧
      (∀ t t', (s7LawYZ μ).cinner (FJ t) (FJ t') = if t = t' then 1 else 0) ∧
      (∀ t, S7CCEffDegGE μ hμ Bx.u (FI t) (d' - 1)) ∧
      (∀ t, S7ConstOnCC hμ (FI t) ∧ ∃ f : X → ℂ, s8W1 hμ f = FJ t) ∧
      ∑ t, ψ t ^ 2 = 1 := by
  classical
  obtain ⟨f₀, rfl⟩ := hF
  have hnorm' : cl2norm (lawX μ) f₀ = 1 := by rwa [s7_cl2norm_W] at hnorm
  obtain ⟨s, κ, fI, fJ, h0, hg, hIo, hJo, he, hs⟩ := plain_nonhomo (lawX μ) hDx σ Bx j f₀ d'
    ((ccEff_W_iff μ hμ Bx.u f₀ d').1 hFd) hnorm'
  refine ⟨s, κ, fun p => s7W hμ (fI p), fun p => s8W1 hμ (fJ p), h0,
    W_svdSum μ hμ j κ fI fJ f₀ hg, fun t t' => ?_, fun t t' => ?_,
    fun t => (ccEff_W_iff μ hμ Bx.u _ _).2 (he t), fun p => ⟨⟨fI p, rfl⟩, ⟨fJ p, rfl⟩⟩, hs⟩
  · rw [s7_W_cinner]; exact hIo t t'
  · rw [s8W1_cinner]; exact hJo t t'

/-- Paper IV `claim:svd-effective-nonhomo-g` (Claim 9.4, l. 5276-5290, proof omitted in the source): the
SVD of an arbitrary `g` on `ι → α` with respect to `[n] = I ⊔ {j}`, for any positive `D` (for the
uniform `μ_y` of the source, `D = lawY μ`). -/
theorem s8_svd_nonhomo_g {α : Type} [Fintype α] (D : FinProb α) (hD : ∀ a, 0 < D.prob a)
    (j : ι) (g : (ι → α) → ℂ) (hnorm : cl2norm D g = 1) :
    ∃ (s : ℕ) (κ : Fin s → ℝ) (gI : Fin s → (S8Rest j → α) → ℂ) (gJ : Fin s → α → ℂ),
      (∀ r, 0 ≤ κ r) ∧ g = s8SvdSum j κ gI gJ ∧
      (∀ r r', (D.pi (S8Rest j)).cinner (gI r) (gI r') = if r = r' then 1 else 0) ∧
      (∀ r r', D.cinner (gJ r) (gJ r') = if r = r' then 1 else 0) ∧
      ∑ r, κ r ^ 2 = 1 := by
  obtain ⟨s, κ, gI, gJ, hκ, hg, hI, hJ, -⟩ := plain_core D hD j g
  exact ⟨s, κ, gI, gJ, fun t => (hκ t).le, hg, hI, hJ,
    sum_sq_eq_one D j κ gI gJ g hg (fun p q _ _ => hI p q) (fun p q _ _ => hJ p q) hnorm⟩

section Coefs
variable {α : Type} [Fintype α] [DecidableEq α] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private lemma kernel_facts (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H) :
    (∀ a, ∑ b, nonEmbedKernel D σ 1 a b = 1) ∧
    (∀ a b, D.prob a * nonEmbedKernel D σ 1 a b = D.prob b * nonEmbedKernel D σ 1 b a) ∧
    (∀ a, ∃ m : ℝ, 0 < m ∧ ∀ b,
      nonEmbedKernel D σ 1 a b = if σ b = σ a then D.prob b / m else 0) := by
  have hfib : ∀ a, 0 < ∑ c ∈ univ.filter (fun c => σ c = σ a), D.prob c := fun a =>
    Finset.sum_pos (fun c _ => hD c) ⟨a, by simp⟩
  obtain ⟨T, hT, -, hrev⟩ := nonEmbedKernel_isReversible D σ zero_le_one le_rfl hfib
  refine ⟨fun a => ?_, fun a b => ?_, fun a => ⟨_, hfib a, fun b => ?_⟩⟩
  · have := T.row_sum a
    simp only [hT] at this
    exact this
  · have := hrev a b
    rwa [hT, hT] at this
  · have hM : (univ.filter fun c => σ a = σ c) = univ.filter fun c => σ c = σ a := by
      ext c; simp [eq_comm]
    unfold nonEmbedKernel graphNoiseKernel
    rw [hM]
    by_cases h : σ b = σ a
    · simp [h]
    · simp [h, Ne.symm h]

private lemma perp_embed (D : FinProb α) (σ : α → H) (h : α → ℂ)
    (hh : ∀ χ : AddChar H ℂ, D.cinner h (fun a => χ (σ a)) = 0) :
    ∀ v ∈ embedSpan σ, D.cinner h v = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨χ, rfl⟩ := hx
    exact hh χ
  | zero => exact cinner_zero_right _ _
  | add x y _ _ hx hy => rw [cinner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [cinner_smul_right, hx, mul_zero]

private lemma inf1_embed (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H) (h : α → ℂ)
    (hh : h ∈ embedSpan σ) :
    ∑ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b * ‖h a - h b‖ ^ 2 = 0 := by
  have hfc := (embedSpan_iff_fibre_constant σ h).1 hh
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro b _
  by_cases hab : σ b = σ a
  · rw [hfc b a hab]; simp
  · obtain ⟨m, -, hm⟩ := (kernel_facts D hD σ).2.2 a
    rw [hm b]; simp [hab]

private lemma inf1_perp (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H) (h : α → ℂ)
    (hp : ∀ v ∈ embedSpan σ, D.cinner h v = 0) :
    ∑ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b * ‖h a - h b‖ ^ 2 =
      2 * ∑ a, D.prob a * ‖h a‖ ^ 2 := by
  obtain ⟨hrow, hrev, hker⟩ := kernel_facts D hD σ
  have hstat : ∀ b, ∑ a, D.prob a * nonEmbedKernel D σ 1 a b = D.prob b := fun b => by
    simp_rw [hrev _ b, ← Finset.mul_sum, hrow, mul_one]
  have hcross : ∀ a, ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * star (h b) = 0 := by
    intro a
    obtain ⟨m, hm, hK⟩ := hker a
    have hv : (fun b => if σ b = σ a then (1 : ℂ) else 0) ∈ embedSpan σ :=
      (embedSpan_iff_fibre_constant σ _).2 (fun w w' hww' => by simp [hww'])
    have h0 := hp _ hv
    have h1 : ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * star (h b) =
        (m : ℂ)⁻¹ * star (D.cinner h (fun b => if σ b = σ a then (1 : ℂ) else 0)) := by
      rw [cinner_def, star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hK b]
      by_cases hb : σ b = σ a
      · simp [hb, div_eq_mul_inv]; ring
      · simp [hb]
    rw [h1, h0]; simp
  have hcross' : ∀ a, ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * h b = 0 := by
    intro a
    have := congrArg star (hcross a)
    simp only [star_sum, star_mul', star_star, star_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show star ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) = ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ)
      by simp]
  have hmain : ∀ a, ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * ((h a - h b) * star (h a - h b)) =
      h a * star (h a) + ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * (h b * star (h b)) := by
    intro a
    have e1 : ∀ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * ((h a - h b) * star (h a - h b)) =
        ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * (h a * star (h a)) +
        ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * (h b * star (h b)) -
        h a * (((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * star (h b)) -
        star (h a) * (((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) * h b) := fun b => by
      rw [star_sub]; ring
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    rw [hcross a, hcross' a]
    have : ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) = 1 := by
      exact_mod_cast hrow a
    rw [this]; ring
  have hC : ((∑ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b * ‖h a - h b‖ ^ 2 : ℝ) : ℂ) =
      ((2 * ∑ a, D.prob a * ‖h a‖ ^ 2 : ℝ) : ℂ) := by
    have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
    simp only [hn]
    simp_rw [hmain, mul_add, Finset.sum_add_distrib]
    have : ∑ a, (D.prob a : ℂ) * ∑ b, ((nonEmbedKernel D σ 1 a b : ℝ) : ℂ) *
        (h b * star (h b)) = ∑ b, (D.prob b : ℂ) * (h b * star (h b)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      have := congrArg (fun x : ℝ => (x : ℂ)) (hstat b)
      simp only [Complex.ofReal_sum, Complex.ofReal_mul] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [this]; ring
  exact_mod_cast hC

private lemma cinner_sum_orth {β P : Type} [Fintype β] [Fintype P] [DecidableEq P]
    (π : FinProb β) (F : P → β → ℂ) (c : P → ℂ)
    (h : ∀ p q, c p ≠ 0 → c q ≠ 0 → π.cinner (F p) (F q) = if p = q then 1 else 0) :
    π.cinner (∑ p, c p • F p) (∑ p, c p • F p) = ∑ p, c p * star (c p) := by
  rw [cinner_sum_left]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single p]
  · rw [cinner_smul_right]
    by_cases hp : c p = 0
    · simp [hp]
    · rw [h p p hp hp]; simp
  · intro q _ hq
    rw [cinner_smul_right]
    by_cases hp : c p = 0
    · simp [hp]
    · by_cases hq0 : c q = 0
      · simp [hq0]
      · rw [h p q hp hq0]; simp [Ne.symm hq]
  · simp

private lemma update_glue {ι : Type} [DecidableEq ι] {β : Type} (j : ι) (a b : β)
    (xI : S8Rest j → β) : Function.update (s8Glue j a xI) j b = s8Glue j b xI := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [s8Glue]
  · simp [s8Glue, hi]

private lemma expect_split_real {β : Type} [Fintype β] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb β) (j : ι) (G : (ι → β) → ℝ) :
    (π.pi ι).expect G = π.expect (fun a => (π.pi (S8Rest j)).expect (fun b => G (s8Glue j a b))) := by
  apply Complex.ofReal_injective
  have := s8_cexpect_split π j (fun x => (G x : ℂ))
  simpa [FinProb.expect, FinProb.cexpect] using this

end Coefs

section CoefsPlain
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [Fintype α] [DecidableEq α]
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private theorem coefs_plain (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (σ : α → H) (j : ι) {s : ℕ}
    (ψ : AddChar H ℂ ⊕ Fin s → ℂ) (fI : AddChar H ℂ ⊕ Fin s → (S8Rest j → α) → ℂ)
    (h : AddChar H ℂ ⊕ Fin s → α → ℂ)
    (hχ : ∀ χ : AddChar H ℂ, h (Sum.inl χ) ∈ Submodule.span ℂ {fun a => χ (σ a)})
    (hr : ∀ (r : Fin s) (χ : AddChar H ℂ), D.cinner (h (Sum.inr r)) (fun a => χ (σ a)) = 0)
    (hI : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      (D.pi (S8Rest j)).cinner (fI p) (fI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 → D.cinner (h p) (h q) = if p = q then 1 else 0) :
    ∑ r : Fin s, ‖ψ (Sum.inr r)‖ ^ 2 = 1 / 2 * s7NonEmbedInf D σ (s8SvdSumC j ψ fI h) j := by
  classical
  set f := s8SvdSumC j ψ fI h with hf
  -- step B: the `I`-average of the squared difference
  have hB : ∀ a b, (D.pi (S8Rest j)).expect (fun xI => ‖f (s8Glue j a xI) - f (s8Glue j b xI)‖ ^ 2) =
      ∑ p, ‖ψ p‖ ^ 2 * ‖h p a - h p b‖ ^ 2 := by
    intro a b
    have e1 : (fun xI => f (s8Glue j a xI) - f (s8Glue j b xI)) =
        ∑ p, (ψ p * (h p a - h p b)) • fI p := by
      funext xI
      simp only [hf, s8SvdSumC, s8Restr_glue, s8Glue_same, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    have e2 := cinner_sum_orth (D.pi (S8Rest j)) fI (fun p => ψ p * (h p a - h p b))
      (fun p q hp hq => hI p q (left_ne_zero_of_mul hp) (left_ne_zero_of_mul hq))
    rw [← e1, cinner_self_eq] at e2
    have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    apply Complex.ofReal_injective
    rw [e2]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, hn, star_mul']
    exact Finset.sum_congr rfl fun p _ => by ring
  -- step A: Fubini
  have hA : s7NonEmbedInf D σ f j = ∑ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b *
      ∑ p, ‖ψ p‖ ^ 2 * ‖h p a - h p b‖ ^ 2 := by
    unfold s7NonEmbedInf
    have := expect_split_real D j (fun x => ∑ b, nonEmbedKernel D σ 1 (x j) b *
      ‖f x - f (Function.update x j b)‖ ^ 2)
    simp only [FinProb.expect] at this ⊢
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    simp only [s8Glue_same, update_glue]
    have h2 : ∀ b, ∑ xI, (D.pi (S8Rest j)).prob xI * (nonEmbedKernel D σ 1 a b *
        ‖f (s8Glue j a xI) - f (s8Glue j b xI)‖ ^ 2) =
        nonEmbedKernel D σ 1 a b * ∑ p, ‖ψ p‖ ^ 2 * ‖h p a - h p b‖ ^ 2 := fun b => by
      rw [← hB a b]
      simp only [FinProb.expect, Finset.mul_sum]
      exact Finset.sum_congr rfl fun xI _ => by ring
    conv_lhs => simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => h2 b
  rw [hA]
  have hswap : ∑ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b *
      ∑ p, ‖ψ p‖ ^ 2 * ‖h p a - h p b‖ ^ 2 =
      ∑ p, ‖ψ p‖ ^ 2 * ∑ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b * ‖h p a - h p b‖ ^ 2 := by
    have e : ∀ a, D.prob a * ∑ b, nonEmbedKernel D σ 1 a b *
        ∑ p, ‖ψ p‖ ^ 2 * ‖h p a - h p b‖ ^ 2 =
        ∑ b, ∑ p, D.prob a * (nonEmbedKernel D σ 1 a b * (‖ψ p‖ ^ 2 * ‖h p a - h p b‖ ^ 2)) :=
      fun a => by simp only [Finset.mul_sum]
    simp only [e]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hswap, Fintype.sum_sum_type]
  have h1 : ∑ χ : AddChar H ℂ, ‖ψ (Sum.inl χ)‖ ^ 2 * ∑ a, D.prob a * ∑ b,
      nonEmbedKernel D σ 1 a b * ‖h (Sum.inl χ) a - h (Sum.inl χ) b‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun χ _ => ?_
    have hsub : ({fun a => χ (σ a)} : Set (α → ℂ)) ⊆
        Set.range (fun χ : AddChar H ℂ => fun w => χ (σ w)) :=
      Set.singleton_subset_iff.2 ⟨χ, rfl⟩
    have hh : h (Sum.inl χ) ∈ embedSpan σ := Submodule.span_mono hsub (hχ χ)
    rw [inf1_embed D hD σ _ hh, mul_zero]
  have h2 : ∀ r : Fin s, ‖ψ (Sum.inr r)‖ ^ 2 * ∑ a, D.prob a * ∑ b,
      nonEmbedKernel D σ 1 a b * ‖h (Sum.inr r) a - h (Sum.inr r) b‖ ^ 2 =
      2 * ‖ψ (Sum.inr r)‖ ^ 2 := by
    intro r
    rw [inf1_perp D hD σ _ (perp_embed D σ _ (hr r))]
    by_cases hψ : ψ (Sum.inr r) = 0
    · simp [hψ]
    · have h3 := hJ (Sum.inr r) (Sum.inr r) hψ hψ
      rw [cinner_self_eq] at h3
      have h4 : ∑ a, D.prob a * ‖h (Sum.inr r) a‖ ^ 2 = 1 := by
        have : ((D.expect fun a => ‖h (Sum.inr r) a‖ ^ 2 : ℝ) : ℂ) = 1 := by simpa using h3
        exact_mod_cast this
      rw [h4]; ring
  rw [h1, zero_add, Finset.sum_congr rfl fun r _ => h2 r, ← Finset.mul_sum]
  ring

end CoefsPlain


private lemma W_glue (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (f₀ : (ι → X) → ℂ)
    (j : ι) (a : Y × Z) (r : S8Rest j → Y × Z) :
    s7W hμ f₀ (s8Glue j a r) =
      f₀ (s8Glue j (s7Pre hμ a.1 a.2) (fun i => s7Pre hμ (r i).1 (r i).2)) := by
  unfold s7W
  rw [pre_glue]

private lemma cf_of_decomp (μ : FinProb (X × Y × Z)) (j : ι) {P : Type} [Fintype P]
    [DecidableEq P] (ψ : P → ℝ) (FI : P → (S8Rest j → Y × Z) → ℂ) (FJ : P → Y × Z → ℂ)
    (F : (ι → Y × Z) → ℂ) (hdec : F = s8SvdSum j ψ FI FJ)
    (hI : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      ((s7LawYZ μ).pi (S8Rest j)).cinner (FI p) (FI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      (s7LawYZ μ).cinner (FJ p) (FJ q) = if p = q then 1 else 0) :
    (∀ p r, ψ p ≠ 0 → (ψ p : ℂ) * FI p r =
      (s7LawYZ μ).cexpect (fun a => F (s8Glue j a r) * star (FJ p a))) ∧
    (∀ p a, ψ p ≠ 0 → (ψ p : ℂ) * FJ p a =
      ((s7LawYZ μ).pi (S8Rest j)).cexpect (fun r => F (s8Glue j a r) * star (FI p r))) :=
  s8svdaux_cf ((s7LawYZ μ).pi (S8Rest j)) (s7LawYZ μ) ψ FI FJ (fun r a => F (s8Glue j a r))
    (fun r a => by rw [hdec]; simp [s8SvdSum]) hI hJ

private lemma FI_eq_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (j : ι)
    (f₀ : (ι → X) → ℂ) (h : X → ℂ) (c : ℂ) (hc : c ≠ 0) (FIp : (S8Rest j → Y × Z) → ℂ)
    (FJp : Y × Z → ℂ) (hJ : s8W1 hμ h = FJp)
    (hI : ∀ r, c * FIp r =
      (s7LawYZ μ).cexpect (fun a => s7W hμ f₀ (s8Glue j a r) * star (FJp a))) :
    s7W hμ (fun xI => c⁻¹ * contr (lawX μ) j f₀ h xI) = FIp := by
  funext yI
  have h1 := hI yI
  rw [← hJ] at h1
  have e : (fun a => s7W hμ f₀ (s8Glue j a yI) * star (s8W1 hμ h a)) =
      s8W1 hμ (fun x => f₀ (s8Glue j x (fun i => s7Pre hμ (yI i).1 (yI i).2)) * star (h x)) := by
    funext a
    simp only [W_glue, s8W1]
  rw [e, s8W1_cexpect] at h1
  show c⁻¹ * contr (lawX μ) j f₀ h (fun i => s7Pre hμ (yI i).1 (yI i).2) = FIp yI
  rw [show contr (lawX μ) j f₀ h (fun i => s7Pre hμ (yI i).1 (yI i).2) =
    (lawX μ).cexpect (fun x => f₀ (s8Glue j x (fun i => s7Pre hμ (yI i).1 (yI i).2)) *
      star (h x)) from rfl, ← h1, inv_mul_cancel_left₀ hc]

/-- Paper IV `claim:svd-effective#factors-constant-on-ccs` (a gap in the source for item (3)): in ANY
decomposition `F = ∑ ψ_p F_p ⊗ F'_p` of a function constant on connected components into orthonormal
families (over `{ψ ≠ 0}`), the factors with `ψ_p ≠ 0` are constant on connected components
(`F_p ∝ M^* F'_p`, and the columns and rows of `M` are cc-constant). -/
theorem s8_svd_factors_constOnCC (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (j : ι) {P : Type} [Fintype P] [DecidableEq P] (ψ : P → ℝ)
    (FI : P → (S8Rest j → Y × Z) → ℂ) (FJ : P → Y × Z → ℂ) (F : (ι → Y × Z) → ℂ)
    (hF : S7ConstOnCC hμ F) (hdec : F = s8SvdSum j ψ FI FJ)
    (hI : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      ((s7LawYZ μ).pi (S8Rest j)).cinner (FI p) (FI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      (s7LawYZ μ).cinner (FJ p) (FJ q) = if p = q then 1 else 0)
    (p : P) (hp : ψ p ≠ 0) :
    S7ConstOnCC hμ (FI p) ∧ ∃ f : X → ℂ, s8W1 hμ f = FJ p := by
  obtain ⟨f₀, rfl⟩ := hF
  obtain ⟨cfI, cfJ⟩ := cf_of_decomp μ j ψ FI FJ _ hdec hI hJ
  have hψ : ((ψ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp
  have part2 : ∃ f : X → ℂ, s8W1 hμ f = FJ p := by
    refine ⟨fun x => ((ψ p : ℝ) : ℂ)⁻¹ * ((s7LawYZ μ).pi (S8Rest j)).cexpect
      (fun r => f₀ (s8Glue j x (fun i => s7Pre hμ (r i).1 (r i).2)) * star (FI p r)), ?_⟩
    funext a
    have := cfJ p a hp
    simp only [W_glue] at this
    show _ = FJ p a
    rw [← inv_mul_cancel_left₀ hψ (FJ p a), this]
    rfl
  obtain ⟨h, hh⟩ := part2
  refine ⟨⟨_, FI_eq_W μ hμ j f₀ h _ hψ (FI p) (FJ p) hh (fun r => cfI p r hp)⟩, h, hh⟩

/-- Paper IV `claim:svd-effective-nonhomo#cc-constancy-and-effective-degree`, effective-degree half
("contracting against `F'_t` over the `J`-coordinate lowers the effective degree by at most one",
asserted without proof at l. 9552-9553): in any decomposition into orthonormal families of a
function of effective degree at least `d'`, the factors `F_p` with `ψ_p ≠ 0` have effective degree at
least `d' - 1` (truncated subtraction, vacuous for `d' = 0`). Basis `Bx` of Def. 7.1 (any `Bx`). -/
theorem s8_svd_factor_effDeg (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (σ : X → H) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX μ) σ Sm) (j : ι) {P : Type} [Fintype P] [DecidableEq P]
    (ψ : P → ℝ) (FI : P → (S8Rest j → Y × Z) → ℂ) (FJ : P → Y × Z → ℂ)
    (F : (ι → Y × Z) → ℂ) (d' : ℕ) (hF : S7ConstOnCC hμ F) (hFd : S7CCEffDegGE μ hμ Bx.u F d')
    (hdec : F = s8SvdSum j ψ FI FJ)
    (hI : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      ((s7LawYZ μ).pi (S8Rest j)).cinner (FI p) (FI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      (s7LawYZ μ).cinner (FJ p) (FJ q) = if p = q then 1 else 0)
    (hFJc : ∀ p, ψ p ≠ 0 → ∃ f : X → ℂ, s8W1 hμ f = FJ p)
    (p : P) (hp : ψ p ≠ 0) : S7CCEffDegGE μ hμ Bx.u (FI p) (d' - 1) := by
  classical
  obtain ⟨f₀, rfl⟩ := hF
  obtain ⟨cfI, -⟩ := cf_of_decomp μ j ψ FI FJ _ hdec hI hJ
  have hψ : ((ψ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp
  obtain ⟨h, hh⟩ := hFJc p hp
  rw [← FI_eq_W μ hμ j f₀ h _ hψ (FI p) (FJ p) hh (fun r => cfI p r hp)]
  rw [ccEff_W_iff]
  intro cI hc
  have hONB := s7_modestBasis_isONB (lawX μ) σ Sm hDx Bx
  have h1 : s7Coef (lawX μ) Bx.u (fun xI => ((ψ p : ℝ) : ℂ)⁻¹ * contr (lawX μ) j f₀ h xI) cI =
      ((ψ p : ℝ) : ℂ)⁻¹ * s7Coef (lawX μ) Bx.u (contr (lawX μ) j f₀ h) cI :=
    cinner_smul_left _ _ _ _
  rw [h1, coef_contract (lawX μ) Bx.u hONB j f₀ h cI] at hc
  have h2 : ∑ k, star ((lawX μ).cinner h (Bx.u k)) * s7Coef (lawX μ) Bx.u f₀ (s8Glue j k cI) ≠ 0 :=
    right_ne_zero_of_mul hc
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have hk' : s7Coef (lawX μ) Bx.u f₀ (s8Glue j k cI) ≠ 0 := right_ne_zero_of_mul hk
  exact eff_ge_of_glue j k cI d' (((ccEff_W_iff μ hμ Bx.u f₀ d').1 hFd) _ hk')

private lemma lawX_pos (μ : FinProb (X × Y × Z))
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) : ∀ x, 0 < (lawX μ).prob x := by
  intro x
  obtain ⟨y, z, hyz⟩ := hocc x
  have h1 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm hyz)
  show 0 < ∑ p ∈ univ.filter (fun p : X × Y × Z => p.1 = x), μ.prob p
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p) (by simp))

private lemma s8W1_inj (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) {f f' : X → ℂ}
    (h : s8W1 hμ f = s8W1 hμ f') : f = f' := by
  funext x
  obtain ⟨y, z, hyz⟩ := hocc x
  have : f (s7Pre hμ y z) = f' (s7Pre hμ y z) := congrFun h (y, z)
  rwa [← s7Pre_unique hμ hyz] at this

/-- Paper IV `claim:coefs-svd-effective` (Claim 8.6, l. 4785-4798): for the decomposition of Claim 8.5,
`∑_{t ∈ T} ψ_t² = ½ I_{j,non-embed}[F]` (`T = {t : ψ_t ≠ 0}`; the terms `ψ_t = 0` contribute `0`).
The hypotheses are items (1)-(3), (4), (5) of Claim 8.5 that the printed proof uses (the degree
hypotheses on `F` and the normalisation `‖F‖ = 1` are not used by the computation, so they are not
assumed: a strengthening); `hocc` (every `x` occurs) is a typing hypothesis, it makes the cc non-embedding influence
(`W⁻¹` unique) well defined. The coefficients are complex, so the claim applies to `S9Svd3`. -/
theorem s8_coefs_svd_effective (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) (σ : X → H) (j : ι)
    (F : (ι → Y × Z) → ℂ) (hF : S7ConstOnCC hμ F) {s : ℕ} (ψ : AddChar H ℂ ⊕ Fin s → ℂ)
    (FI : AddChar H ℂ ⊕ Fin s → (S8Rest j → Y × Z) → ℂ)
    (FJ : AddChar H ℂ ⊕ Fin s → Y × Z → ℂ) (hdec : F = s8SvdSumC j ψ FI FJ)
    (hχ : ∀ χ : AddChar H ℂ, FJ (Sum.inl χ) ∈ Submodule.span ℂ {s8W1 hμ (fun x => χ (σ x))})
    (hr : ∀ (r : Fin s) (χ : AddChar H ℂ),
      (s7LawYZ μ).cinner (FJ (Sum.inr r)) (s8W1 hμ (fun x => χ (σ x))) = 0)
    (hcc : ∀ p, S7ConstOnCC hμ (FI p) ∧ ∃ f : X → ℂ, s8W1 hμ f = FJ p)
    (hI : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      ((s7LawYZ μ).pi (S8Rest j)).cinner (FI p) (FI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      (s7LawYZ μ).cinner (FJ p) (FJ q) = if p = q then 1 else 0) :
    ∑ r : Fin s, ‖ψ (Sum.inr r)‖ ^ 2 = 1 / 2 * s7CCNonEmbedInf μ hμ hocc σ hF j := by
  classical
  have hD := lawX_pos μ hocc
  choose fI hfI using fun p => (hcc p).1
  choose h hh using fun p => (hcc p).2
  have hFI : FI = fun p => s7W hμ (fI p) := funext fun p => (hfI p).symm
  have hFJ : FJ = fun p => s8W1 hμ (h p) := funext fun p => (hh p).symm
  have hW : s7W hμ (s8SvdSumC j ψ fI h) = F := by
    rw [hdec, hFI, hFJ]
    rfl
  have hf₁ : s8SvdSumC j ψ fI h = s7WInv hocc hF := s7WInv_unique hμ hocc hF _ hW
  have hnon : s7CCNonEmbedInf μ hμ hocc σ hF j =
      s7NonEmbedInf (lawX μ) σ (s8SvdSumC j ψ fI h) j := by
    unfold s7CCNonEmbedInf
    rw [← hf₁]
  rw [hnon]
  refine coefs_plain (lawX μ) hD σ j ψ fI h (fun χ => ?_) (fun r χ => ?_) (fun p q hp hq => ?_)
    (fun p q hp hq => ?_)
  · have h1 := hχ χ
    rw [← hh] at h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    have h2 : h (Sum.inl χ) = c • fun x => χ (σ x) :=
      (s8W1_inj μ hμ hocc ((rfl : s8W1 hμ (c • fun x => χ (σ x)) =
        c • s8W1 hμ fun x => χ (σ x)).trans hc)).symm
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have h1 := hr r χ
    rw [← hh, s8W1_cinner] at h1
    exact h1
  · have := hI p q hp hq
    rwa [hFI, s7_W_cinner] at this
  · have := hJ p q hp hq
    rwa [hFJ, s8W1_cinner] at this

end S8SvdEffective

end TrackB
end RestrictedPolynomials
end
