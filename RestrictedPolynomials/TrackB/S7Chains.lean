module

public import RestrictedPolynomials.TrackB.S7Basis

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section S7Chains
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Paper IV `definition-modest-markov-chain` (Def. l. 4212-4215), kernel form: from `a ∉ Σ_modest` stay at
`a`; from `a ∈ Σ_modest` draw `b ∼ μ_x` conditioned on `b ∈ Σ_modest`. As for the built
`graphNoiseKernel` the formula is the source's conditional law; it is a Markov kernel exactly when
`μ_x(Σ_modest) > 0` (`s7ModestKernel_isStochastic`, hypothesis `hD`). -/
def s7ModestKernel (D : FinProb α) (Sm : Finset α) (a b : α) : ℝ :=
  if a ∈ Sm then (if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0)
  else (if a = b then 1 else 0)

/-- Paper IV `definition-effective-noise-operator` (Def. l. 4220-4223): `E_{non-embed,1-δ}` stays with
probability `1 - δ` and otherwise moves according to the modest chain. -/
def s7EffKernel (D : FinProb α) (Sm : Finset α) (δ : ℝ) (a b : α) : ℝ :=
  (1 - δ) * (if a = b then 1 else 0) + δ * s7ModestKernel D Sm a b

/-- the averaging operator of a kernel on one coordinate, `K g (a) = 𝔼_{b ∼ K a} g(b)`
(l. 4225-4228). -/
def s7KernelApply (K : α → α → ℝ) (g : α → ℂ) (a : α) : ℂ := ∑ b, (K a b : ℂ) * g b

/-- `K^{⊗ι}` acting on functions on `ι → α` (as the built `graphNoiseOp`). -/
def s7KernelOp (K : α → α → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → α) → ℂ)
    (x : ι → α) : ℂ :=
  ∑ y, ((∏ i, K (x i) (y i) : ℝ) : ℂ) * f y

/-- `E_{non-embed,1-δ}^{⊗ι}`. -/
def s7EffNoiseOp (D : FinProb α) (Sm : Finset α) (δ : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  s7KernelOp (s7EffKernel D Sm δ) f x

/-- modest influence of `f` at coordinate `i` (paper IV `definition-modest-influence`, l. 4264-4271):
`𝔼_{x ∼ μ_x^ι, b ∼ Modest(x_i)} |f(x) - f(x_i ← b)|²` (`x = (x', a)`). -/
def s7ModestInf (D : FinProb α) (Sm : Finset α) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (i : ι) : ℝ :=
  ∑ x, (D.pi ι).prob x * ∑ b, s7ModestKernel D Sm (x i) b * ‖f x - f (Function.update x i b)‖ ^ 2

/-- total modest influence `I_modest[f] = ∑ᵢ I_{i,modest}[f]`. -/
def s7ModestTotalInf (D : FinProb α) (Sm : Finset α) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) : ℝ :=
  ∑ i, s7ModestInf D Sm f i

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Paper IV `def:non-embed-inf` (Defs. 4.10-4.11, l. 2542-2557): `I_{j,non-embed}[f]
= 𝔼_{x ∼ μ_x^ι, b ∼ μ_x | σ(b) = σ(x_j)} |f(x) - f(x_j ← b)|²`, i.e. the kernel of the built
`nonEmbedKernel` at `ξ = 1` (the reading of "a, b ∼ μ_x conditioned on σ(a) = σ(b)" is
sequential: `a ∼ μ_x` then `b ∼ μ_x` conditioned on `σ(b) = σ(a)`). `f` is a function
of `x` (the printed `f : Γ^n → ℂ` is a typo). -/
def s7NonEmbedInf (D : FinProb α) (σ : α → H) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (j : ι) : ℝ :=
  ∑ x, (D.pi ι).prob x * ∑ b, nonEmbedKernel D σ 1 (x j) b * ‖f x - f (Function.update x j b)‖ ^ 2

/-- total non-embedding influence. -/
def s7NonEmbedTotalInf (D : FinProb α) (σ : α → H) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) : ℝ :=
  ∑ j, s7NonEmbedInf D σ f j

/-- Paper IV `definition-modest-variance` (Def. 9.6, l. 5317-5319): `var_{Σ_modest}(f) = 𝔼_{a,b ∈ Σ_modest}
|f(a) - f(b)|²` with `a, b` independent uniform on `Σ_modest` (the source does not say; the
same reading is used in Def. 6.6 item 2). `Σ_modest` is nonempty (`|Σ_modest| ≥ 2`). -/
def s7ModestVar (Sm : Finset α) (_hSm : Sm.Nonempty) (f : α → ℂ) : ℝ :=
  (∑ a ∈ Sm, ∑ b ∈ Sm, ‖f a - f b‖ ^ 2) / (Sm.card : ℝ) ^ 2

omit [DecidableEq α] in
@[simp] theorem s7KernelApply_def (K : α → α → ℝ) (g : α → ℂ) (a : α) :
    s7KernelApply K g a = ∑ b, (K a b : ℂ) * g b := rfl

/-! ### Private helpers -/

omit [DecidableEq α] in
private lemma kernelOp_mono {J ι : Type} [Fintype ι] [DecidableEq ι] (K : α → α → ℝ)
    (u : J → α → ℂ) (c : ι → J) (x : ι → α) :
    s7KernelOp K (s7Mono u c) x = ∏ i, s7KernelApply K (u (c i)) (x i) := by
  unfold s7KernelOp s7KernelApply s7Mono
  rw [Fintype.prod_sum (fun i b => (K (x i) b : ℂ) * u (c i) b)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

omit [DecidableEq α] in
private lemma kernelOp_expand {J ι : Type} [Fintype J] [Fintype ι] [DecidableEq ι]
    (K : α → α → ℝ) (u : J → α → ℂ) (a : (ι → J) → ℂ) (f : (ι → α) → ℂ)
    (hf : f = ∑ c, a c • s7Mono u c) (x : ι → α) :
    s7KernelOp K f x = ∑ c, a c * s7KernelOp K (s7Mono u c) x := by
  subst hf
  simp only [s7KernelOp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq α] in
private lemma kernelOp_eigen_mono {J ι : Type} [Fintype ι] [DecidableEq ι] (K : α → α → ℝ)
    (u : J → α → ℂ) (lam : J → ℂ) (hK : ∀ j a, s7KernelApply K (u j) a = lam j * u j a)
    (c : ι → J) :
    s7KernelOp K (s7Mono u c) = fun x => (∏ i, lam (c i)) * s7Mono u c x := by
  funext x
  rw [kernelOp_mono]
  simp only [hK, s7Mono, Finset.prod_mul_distrib]

private lemma prod_ite_pow {J ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [CommMonoid M]
    (P : J → Prop) [DecidablePred P] (c : ι → J) (r : M) :
    ∏ i, (if P (c i) then r else 1) = r ^ s7CountWhere P c := by
  have : {i | P (c i)} = ↑(univ.filter fun i => P (c i)) := by ext; simp
  rw [s7CountWhere, this, Set.ncard_coe_finset, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one]

private lemma countWhere_eq_sum {J ι : Type} [Fintype ι] [DecidableEq ι]
    (P : J → Prop) [DecidablePred P] (c : ι → J) :
    (s7CountWhere P c : ℝ) = ∑ i, if P (c i) then (1 : ℝ) else 0 := by
  have : {i | P (c i)} = ↑(univ.filter fun i => P (c i)) := by ext; simp
  rw [s7CountWhere, this, Set.ncard_coe_finset, Finset.sum_boole]

private lemma sum_ite_mem' {R : Type*} [AddCommMonoid R] (Sm : Finset α) (f : α → R) :
    ∑ b, (if b ∈ Sm then f b else 0) = ∑ b ∈ Sm, f b := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

private lemma modestKernel_nonneg (D : FinProb α) (Sm : Finset α) (a b : α) :
    0 ≤ s7ModestKernel D Sm a b := by
  unfold s7ModestKernel
  split_ifs
  · exact div_nonneg (D.nonneg b) (Finset.sum_nonneg fun c _ => D.nonneg c)
  all_goals norm_num

private lemma modestKernel_row (D : FinProb α) (Sm : Finset α) (hD : ∀ a, 0 < D.prob a) (a : α) :
    ∑ b, s7ModestKernel D Sm a b = 1 := by
  unfold s7ModestKernel
  by_cases ha : a ∈ Sm
  · simp only [ha, ite_true]
    have hS : 0 < ∑ c ∈ Sm, D.prob c := Finset.sum_pos (fun c _ => hD c) ⟨a, ha⟩
    rw [sum_ite_mem' Sm (fun b => D.prob b / ∑ c ∈ Sm, D.prob c), ← Finset.sum_div,
      div_self hS.ne']
  · simp [ha]

private lemma modestKernel_rev (D : FinProb α) (Sm : Finset α) (a b : α) :
    D.prob a * s7ModestKernel D Sm a b = D.prob b * s7ModestKernel D Sm b a := by
  unfold s7ModestKernel
  by_cases ha : a ∈ Sm <;> by_cases hb : b ∈ Sm
  · simp only [ha, hb, ite_true]; ring
  · have : a ≠ b := fun h => hb (h ▸ ha)
    simp [ha, hb, Ne.symm this]
  · have : a ≠ b := fun h => ha (h ▸ hb)
    simp [ha, hb, this]
  · simp only [ha, hb, ite_false]
    by_cases hab : a = b
    · subst hab; rfl
    · simp [hab, Ne.symm hab]

omit [Fintype H] [DecidableEq H] in
private lemma sum_id_kernel (g : α → ℂ) (a : α) :
    ∑ x, (((if a = x then (1 : ℝ) else 0 : ℝ)) : ℂ) * g x = g a := by
  rw [Finset.sum_eq_single a (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp

private lemma modestApply_const (D : FinProb α) (Sm : Finset α) (hD : ∀ a, 0 < D.prob a)
    (g : α → ℂ) (hg : g ∈ s7ConstOn Sm) (a : α) :
    s7KernelApply (s7ModestKernel D Sm) g a = g a := by
  unfold s7KernelApply s7ModestKernel
  by_cases ha : a ∈ Sm
  · simp only [ha, ite_true]
    have hS : 0 < ∑ c ∈ Sm, D.prob c := Finset.sum_pos (fun c _ => hD c) ⟨a, ha⟩
    have h1 : ∀ b, ((if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0 : ℝ) : ℂ) * g b
        = ((if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0 : ℝ) : ℂ) * g a := by
      intro b
      by_cases hb : b ∈ Sm
      · rw [hg b hb a ha]
      · simp [hb]
    rw [Finset.sum_congr rfl (fun b _ => h1 b), ← Finset.sum_mul, ← Complex.ofReal_sum,
      sum_ite_mem' Sm (fun b => D.prob b / ∑ c ∈ Sm, D.prob c), ← Finset.sum_div,
      div_self hS.ne']
    simp
  · simp only [ha, ite_false]
    exact sum_id_kernel g a

private lemma modestApply_perp (D : FinProb α) (Sm : Finset α) (hD : ∀ a, 0 < D.prob a)
    (g : α → ℂ) (hperp : ∀ v ∈ s7ConstOn Sm, D.cinner g v = 0) (hvan : ∀ a ∉ Sm, g a = 0)
    (a : α) : s7KernelApply (s7ModestKernel D Sm) g a = 0 := by
  unfold s7KernelApply s7ModestKernel
  by_cases ha : a ∈ Sm
  · simp only [ha, ite_true]
    have hS : 0 < ∑ c ∈ Sm, D.prob c := Finset.sum_pos (fun c _ => hD c) ⟨a, ha⟩
    have hind : (fun b : α => if b ∈ Sm then (1 : ℂ) else 0) ∈ s7ConstOn Sm :=
      fun x hx y hy => by simp [hx, hy]
    have h0 := hperp _ hind
    have h2 : ∑ b, ((if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0 : ℝ) : ℂ) * g b
        = (((∑ c ∈ Sm, D.prob c : ℝ) : ℂ))⁻¹ *
          D.cinner g (fun b : α => if b ∈ Sm then (1 : ℂ) else 0) := by
      rw [cinner_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b ∈ Sm
      · simp only [hb, ite_true, star_one]
        push_cast
        ring
      · simp [hb]
    rw [h2, h0, mul_zero]
  · simp only [ha, ite_false]
    rw [sum_id_kernel g a, hvan a ha]

omit [DecidableEq α] [Fintype H] [DecidableEq H] in
private lemma uM_mem {D : FinProb α} {σ : α → H} {Sm : Finset α} (B : S7ModestBasis D σ Sm)
    (m : Fin B.nM) : B.uM m ∈ s7Perp D (embedSpan σ) ⊓ s7Perp D (s7Nenm D σ Sm) := by
  rw [← B.span_M]; exact Submodule.subset_span ⟨m, rfl⟩

omit [DecidableEq α] in
private lemma uM_perp_const {D : FinProb α} {σ : α → H} {Sm : Finset α}
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') (B : S7ModestBasis D σ Sm) (m : Fin B.nM) :
    ∀ v ∈ s7ConstOn Sm, D.cinner (B.uM m) v = 0 := by
  intro v hv
  rw [← s7_embed_sup_nenm_eq_constOn D σ Sm hconst B] at hv
  obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hv
  rw [cinner_add_right, (uM_mem B m).1 v1 hv1, (uM_mem B m).2 v2 hv2, add_zero]

omit [DecidableEq α] [Fintype H] [DecidableEq H] in
private lemma u_perp_embed {D : FinProb α} {σ : α → H} {Sm : Finset α} (B : S7ModestBasis D σ Sm)
    (j : B.J) (hj : ¬ ∃ a, j = Sum.inl a) : B.u j ∈ s7Perp D (embedSpan σ) := by
  rcases j with χ | k | k
  · exact absurd ⟨χ, rfl⟩ hj
  · have : B.uN k ∈ s7Nenm D σ Sm := by
      rw [← B.span_N]; exact Submodule.subset_span ⟨k, rfl⟩
    exact this.1
  · exact (uM_mem B k).1

/-- the modest kernel acts on the basis: identity off `B_modest`, zero on `B_modest`. -/
private lemma modestApply_basis (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) (j : B.J) (a : α) :
    s7KernelApply (s7ModestKernel D Sm) (B.u j) a =
      if (∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) then 0 else B.u j a := by
  by_cases hj : ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)
  · obtain ⟨m, rfl⟩ := hj
    simp only [show ∃ m' : Fin B.nM, (Sum.inr (Sum.inr m) : B.J) = Sum.inr (Sum.inr m') from ⟨m, rfl⟩, ↓reduceIte]
    exact modestApply_perp D Sm hD _ (uM_perp_const hconst B m)
      (fun a ha => s7_basis_modest_vanish_outside D σ Sm hD hconst B m a ha) a
  · simp only [hj, ↓reduceIte]
    exact modestApply_const D Sm hD _ (s7_basis_embed_nenm_constOn D σ Sm hconst B j hj) a


private lemma effApply (D : FinProb α) (Sm : Finset α) (δ : ℝ) (g : α → ℂ) (a : α) :
    s7KernelApply (s7EffKernel D Sm δ) g a =
      ((1 - δ : ℝ) : ℂ) * g a + (δ : ℂ) * s7KernelApply (s7ModestKernel D Sm) g a := by
  unfold s7KernelApply s7EffKernel
  have h : ∀ b, (((1 - δ) * (if a = b then (1 : ℝ) else 0) + δ * s7ModestKernel D Sm a b : ℝ) : ℂ)
        * g b = ((1 - δ : ℝ) : ℂ) * ((((if a = b then (1 : ℝ) else 0 : ℝ)) : ℂ) * g b)
          + (δ : ℂ) * ((s7ModestKernel D Sm a b : ℂ) * g b) := by
    intro b; push_cast; ring
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_id_kernel]


omit [AddCommGroup H] [Fintype H] in
private lemma nonEmbedApply_split (D : FinProb α) (σ : α → H) (ξ : ℝ) (g : α → ℂ) (a : α) :
    s7KernelApply (nonEmbedKernel D σ ξ) g a = ((1 - ξ : ℝ) : ℂ) * g a +
      ((ξ : ℂ) / ((∑ c ∈ univ.filter (fun c => σ a = σ c), D.prob c : ℝ) : ℂ)) *
        ∑ b, (if σ a = σ b then (D.prob b : ℂ) else 0) * g b := by
  unfold s7KernelApply nonEmbedKernel graphNoiseKernel
  have h : ∀ b, (((1 - ξ) * (if a = b then (1 : ℝ) else 0) +
      ξ * ((if (fun a b => σ a = σ b) a b then D.prob b else 0) /
        ∑ c ∈ univ.filter ((fun a b => σ a = σ b) a), D.prob c) : ℝ) : ℂ) * g b =
      ((1 - ξ : ℝ) : ℂ) * ((((if a = b then (1 : ℝ) else 0 : ℝ)) : ℂ) * g b) +
      ((ξ : ℂ) / ((∑ c ∈ univ.filter (fun c => σ a = σ c), D.prob c : ℝ) : ℂ)) *
        ((if σ a = σ b then (D.prob b : ℂ) else 0) * g b) := by
    intro b
    by_cases hb : σ a = σ b
    · simp only [hb, ite_true]
      push_cast
      ring
    · simp only [hb, ite_false]
      push_cast
      ring
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_id_kernel]

omit [AddCommGroup H] [Fintype H] in
private lemma nonEmbedApply_fibre_const (D : FinProb α) (σ : α → H) (ξ : ℝ)
    (hD : ∀ a, 0 < D.prob a) (g : α → ℂ) (hg : ∀ a b, σ a = σ b → g b = g a) (a : α) :
    s7KernelApply (nonEmbedKernel D σ ξ) g a = g a := by
  rw [nonEmbedApply_split]
  have hF : 0 < ∑ c ∈ univ.filter (fun c => σ a = σ c), D.prob c :=
    Finset.sum_pos (fun c _ => hD c) ⟨a, by simp⟩
  have h2 : ∑ b, (if σ a = σ b then (D.prob b : ℂ) else 0) * g b =
      ((∑ c ∈ univ.filter (fun c => σ a = σ c), D.prob c : ℝ) : ℂ) * g a := by
    push_cast
    rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : σ a = σ b
    · simp [hb, hg a b hb]
    · simp [hb]
  rw [h2]
  have : ((∑ c ∈ univ.filter (fun c => σ a = σ c), D.prob c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hF.ne'
  field_simp
  push_cast
  ring

private lemma nonEmbedApply_perp (D : FinProb α) (σ : α → H) (ξ : ℝ)
    (g : α → ℂ) (hperp : ∀ v ∈ embedSpan σ, D.cinner g v = 0) (a : α) :
    s7KernelApply (nonEmbedKernel D σ ξ) g a = ((1 - ξ : ℝ) : ℂ) * g a := by
  rw [nonEmbedApply_split]
  have hv : (fun b : α => if σ a = σ b then (1 : ℂ) else 0) ∈ embedSpan σ :=
    (embedSpan_eq_fibreConstant σ _).2 ⟨fun h => if σ a = h then 1 else 0, rfl⟩
  have h0 := hperp _ hv
  have h2 : ∑ b, (if σ a = σ b then (D.prob b : ℂ) else 0) * g b =
      D.cinner g (fun b : α => if σ a = σ b then (1 : ℂ) else 0) := by
    rw [cinner_def]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : σ a = σ b
    · simp [hb]
    · simp [hb]
  rw [h2, h0, mul_zero, add_zero]


omit [DecidableEq α] [AddCommGroup H] [Fintype H] [DecidableEq H] in
private lemma cinner_sum_smul_sum2 {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    (π : FinProb β) (m : γ → β → ℂ)
    (hm : ∀ c c', π.cinner (m c) (m c') = if c = c' then 1 else 0) (a b : γ → ℂ) :
    π.cinner (∑ c, a c • m c) (∑ c, b c • m c) = ∑ c, a c * star (b c) := by
  rw [cinner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [cinner_smul_right, hm]; simp
  · intro c' _ hc'; rw [cinner_smul_right, hm]; simp [Ne.symm hc']
  · simp

omit [DecidableEq α] [AddCommGroup H] [Fintype H] [DecidableEq H] in
private lemma mul_star_real (r : ℝ) (z : ℂ) :
    z * star ((r : ℂ) * z) = ((r * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_left_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

omit [DecidableEq α] in
/-- `⟨f, ∑ w_χ f̂(χ) χ⟩ = ∑ w_χ |f̂(χ)|²` for real weights, in an orthonormal basis. -/
private lemma cinner_weighted (D : FinProb α) (hD : ∀ a, 0 < D.prob a) {J : Type} [Fintype J]
    (u : J → α → ℂ) (hu : S7IsONB D u) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : (ι → α) → ℂ) (w : (ι → J) → ℝ)
    (hg : g = fun x => ∑ c, (w c : ℂ) * s7Coef D u f c * s7Mono u c x) :
    (D.pi ι).cinner f g = ∑ c, ((w c * ‖s7Coef D u f c‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hm := s7_mono_orthonormal (ι := ι) D u hu.1
  have hf := s7_fourier_expansion D hD u hu f
  have hg' : g = ∑ c, ((w c : ℂ) * s7Coef D u f c) • s7Mono u c := by
    rw [hg]; funext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key := cinner_sum_smul_sum2 (D.pi ι) (s7Mono u) hm (fun c => s7Coef D u f c)
    (fun c => (w c : ℂ) * s7Coef D u f c)
  have e : (D.pi ι).cinner f g = (D.pi ι).cinner (∑ c, s7Coef D u f c • s7Mono u c)
      (∑ c, ((w c : ℂ) * s7Coef D u f c) • s7Mono u c) := by
    rw [← hf, ← hg']
  rw [e, key]
  exact Finset.sum_congr rfl fun c _ => mul_star_real (w c) _

end S7Chains

section S7ChainsAux2
variable {α : Type} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
private lemma pi_prob_split (D : FinProb α) {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (x : ι → α) :
    (D.pi ι).prob x = D.prob (x i) * ∏ k ∈ univ.erase i, D.prob (x k) := by
  show ∏ k, D.prob (x k) = _
  exact (Finset.mul_prod_erase univ (fun k => D.prob (x k)) (mem_univ i)).symm

omit [DecidableEq α] in
private lemma pi_prob_update (D : FinProb α) {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (x : ι → α) (b : α) :
    (D.pi ι).prob (Function.update x i b) = D.prob b * ∏ k ∈ univ.erase i, D.prob (x k) := by
  rw [pi_prob_split D i]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

omit [DecidableEq α] in
private lemma stationary_coord (D : FinProb α) (K : α → α → ℝ)
    (hrow : ∀ a, ∑ b, K a b = 1) (hrev : ∀ a b, D.prob a * K a b = D.prob b * K b a)
    {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (h : (ι → α) → ℝ) :
    ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b * h (Function.update x i b) =
      ∑ x, (D.pi ι).prob x * h x := by
  have hPK : ∀ (x : ι → α) (b : α), (D.pi ι).prob x * K (x i) b =
      (D.pi ι).prob (Function.update x i b) * K b (x i) := by
    intro x b
    rw [pi_prob_split D i x, pi_prob_update D i x b]
    have := hrev (x i) b
    linear_combination (∏ k ∈ univ.erase i, D.prob (x k)) * this
  let T : (ι → α) × α → (ι → α) × α := fun p => (Function.update p.1 i p.2, p.1 i)
  have hT : Function.Involutive T := by
    intro p
    simp [T]
  have h1 : ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b * h (Function.update x i b) =
      ∑ p : (ι → α) × α,
        (D.pi ι).prob p.1 * K (p.1 i) p.2 * h (Function.update p.1 i p.2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, ← Equiv.sum_comp hT.toPerm, Fintype.sum_prod_type]
  simp only [Function.Involutive.coe_toPerm, T, Function.update_self, Function.update_idem,
    Function.update_eq_self]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : ∀ b, (D.pi ι).prob (Function.update x i b) * K b (x i) * h x =
      (D.pi ι).prob x * h x * K (x i) b := by
    intro b
    rw [← hPK x b]; ring
  simp only [h2]
  rw [← Finset.mul_sum, hrow, mul_one]

omit [DecidableEq α] in
private lemma coord_eigen {J ι : Type} [Fintype ι] [DecidableEq ι] (K : α → α → ℝ)
    (u : J → α → ℂ) (lam : J → ℝ)
    (hK : ∀ j a, s7KernelApply K (u j) a = (lam j : ℂ) * u j a) (c : ι → J) (i : ι)
    (x : ι → α) :
    ∑ b, (K (x i) b : ℂ) * s7Mono u c (Function.update x i b) =
      (lam (c i) : ℂ) * s7Mono u c x := by
  have hsplit : ∀ y : ι → α,
      s7Mono u c y = u (c i) (y i) * ∏ k ∈ univ.erase i, u (c k) (y k) := fun y =>
    (Finset.mul_prod_erase univ (fun k => u (c k) (y k)) (mem_univ i)).symm
  have hR : ∀ b, s7Mono u c (Function.update x i b) =
      u (c i) b * ∏ k ∈ univ.erase i, u (c k) (x k) := by
    intro b
    rw [hsplit, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  simp only [hR]
  have : ∑ b, (K (x i) b : ℂ) * (u (c i) b * ∏ k ∈ univ.erase i, u (c k) (x k)) =
      s7KernelApply K (u (c i)) (x i) * ∏ k ∈ univ.erase i, u (c k) (x k) := by
    unfold s7KernelApply
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, hK, hsplit x]
  ring

omit [DecidableEq α] in
private lemma influence_generic (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (K : α → α → ℝ)
    (hrow : ∀ a, ∑ b, K a b = 1) (hrev : ∀ a b, D.prob a * K a b = D.prob b * K b a)
    {J : Type} [Fintype J] (u : J → α → ℂ) (hu : S7IsONB D u) (lam : J → ℝ)
    (hK : ∀ j a, s7KernelApply K (u j) a = (lam j : ℂ) * u j a)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → α) → ℂ) (i : ι) :
    ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b * ‖f x - f (Function.update x i b)‖ ^ 2 =
      2 * ∑ c : ι → J, (1 - lam (c i)) * ‖s7Coef D u f c‖ ^ 2 := by
  classical
  have hf := s7_fourier_expansion D hD u hu f
  have hpt : ∀ x b, K (x i) b * ‖f x - f (Function.update x i b)‖ ^ 2 =
      ‖f x‖ ^ 2 * K (x i) b + K (x i) b * ‖f (Function.update x i b)‖ ^ 2 -
        2 * (K (x i) b * (f x * starRingEnd ℂ (f (Function.update x i b))).re) := by
    intro x b; rw [norm_sub_sq_eq]; ring
  have hI : ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b * ‖f x - f (Function.update x i b)‖ ^ 2 =
      ∑ x, (D.pi ι).prob x * ‖f x‖ ^ 2 +
        ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b * ‖f (Function.update x i b)‖ ^ 2 -
        2 * ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b *
          (f x * starRingEnd ℂ (f (Function.update x i b))).re := by
    have : ∀ x, (D.pi ι).prob x * ∑ b, K (x i) b * ‖f x - f (Function.update x i b)‖ ^ 2 =
        (D.pi ι).prob x * ‖f x‖ ^ 2 +
          (D.pi ι).prob x * ∑ b, K (x i) b * ‖f (Function.update x i b)‖ ^ 2 -
          2 * ((D.pi ι).prob x * ∑ b, K (x i) b *
            (f x * starRingEnd ℂ (f (Function.update x i b))).re) := by
      intro x
      rw [Finset.sum_congr rfl (fun b _ => hpt x b), Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      have e1 : ∑ b, ‖f x‖ ^ 2 * K (x i) b = ‖f x‖ ^ 2 := by
        rw [← Finset.mul_sum, hrow, mul_one]
      have e2 : ∑ b, 2 * (K (x i) b * (f x * starRingEnd ℂ (f (Function.update x i b))).re) =
          2 * ∑ b, K (x i) b * (f x * starRingEnd ℂ (f (Function.update x i b))).re := by
        rw [Finset.mul_sum]
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  have hT2 := stationary_coord D K hrow hrev i (fun y => ‖f y‖ ^ 2)
  have hpars := s7_parseval D hD u hu f
  have hC : ∑ x, (D.pi ι).prob x * ∑ b, K (x i) b *
      (f x * starRingEnd ℂ (f (Function.update x i b))).re =
      ∑ c : ι → J, lam (c i) * ‖s7Coef D u f c‖ ^ 2 := by
    have h1 : ∀ y, f y = ∑ c, s7Coef D u f c * s7Mono u c y := by
      intro y
      have := congrFun hf y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this
    have hKi : ∀ x, ∑ b, (K (x i) b : ℂ) * f (Function.update x i b) =
        ∑ c, (lam (c i) : ℂ) * s7Coef D u f c * s7Mono u c x := by
      intro x
      have : ∀ b, (K (x i) b : ℂ) * f (Function.update x i b) =
          ∑ c, s7Coef D u f c * ((K (x i) b : ℂ) * s7Mono u c (Function.update x i b)) := by
        intro b
        rw [h1 (Function.update x i b), Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.mul_sum, coord_eigen K u lam hK c i x]
      ring
    have hcin := cinner_weighted D hD u hu f
      (fun x => ∑ b, (K (x i) b : ℂ) * f (Function.update x i b)) (fun c => lam (c i))
      (funext hKi)
    have hC' : (D.pi ι).cinner f (fun x => ∑ b, (K (x i) b : ℂ) * f (Function.update x i b)) =
        ∑ x, (((D.pi ι).prob x : ℝ) : ℂ) * ∑ b, (K (x i) b : ℂ) *
          (f x * starRingEnd ℂ (f (Function.update x i b))) := by
      rw [cinner_def]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      rw [star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    have := congrArg Complex.re (hC'.symm.trans hcin)
    simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re] at this
    exact this
  rw [hI, hT2, hC]
  have hp : ∑ x, (D.pi ι).prob x * ‖f x‖ ^ 2 = ∑ c : ι → J, ‖s7Coef D u f c‖ ^ 2 := hpars
  rw [hp]
  have : ∑ c : ι → J, (1 - lam (c i)) * ‖s7Coef D u f c‖ ^ 2 =
      ∑ c : ι → J, ‖s7Coef D u f c‖ ^ 2 - ∑ c : ι → J, lam (c i) * ‖s7Coef D u f c‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [this]
  ring

end S7ChainsAux2

section S7ChainsThms
variable {α : Type} [Fintype α] [DecidableEq α]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Paper IV `definition-modest-markov-chain`: the modest kernel is a Markov chain, reversible with
stationary law `μ_x` (stated "immediate" in the source, l. 4224 for the effective chain). -/
theorem s7ModestKernel_isStochastic (D : FinProb α) (Sm : Finset α) (hD : ∀ a, 0 < D.prob a) :
    ∃ T : StochMat α, (∀ a b, T.prob a b = s7ModestKernel D Sm a b) ∧
      T.IsStationary D ∧ T.IsReversible D := by
  refine ⟨⟨s7ModestKernel D Sm, modestKernel_nonneg D Sm, modestKernel_row D Sm hD⟩,
    fun a b => rfl, ?_, fun a b => modestKernel_rev D Sm a b⟩
  intro b
  have : ∀ a, D.prob a * s7ModestKernel D Sm a b = D.prob b * s7ModestKernel D Sm b a :=
    fun a => modestKernel_rev D Sm a b
  simp_rw [this, ← Finset.mul_sum, modestKernel_row D Sm hD, mul_one]

/-- Paper IV `definition-effective-noise-operator`: `E_{non-embed,1-δ}` is a Markov chain with stationary
law `μ_x` (l. 4224), for `0 ≤ δ ≤ 1`. -/
theorem s7EffKernel_isStochastic (D : FinProb α) (Sm : Finset α) (hD : ∀ a, 0 < D.prob a)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ T : StochMat α, (∀ a b, T.prob a b = s7EffKernel D Sm δ a b) ∧
      T.IsStationary D ∧ T.IsReversible D := by
  have hnn : ∀ a b, 0 ≤ s7EffKernel D Sm δ a b := by
    intro a b
    unfold s7EffKernel
    have h1 : 0 ≤ (if a = b then (1:ℝ) else 0) := by split_ifs <;> norm_num
    have := modestKernel_nonneg D Sm a b
    have h2 : 0 ≤ 1 - δ := by linarith
    positivity
  have hrow : ∀ a, ∑ b, s7EffKernel D Sm δ a b = 1 := by
    intro a
    unfold s7EffKernel
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, modestKernel_row D Sm hD]
    simp
  have hrev : ∀ a b, D.prob a * s7EffKernel D Sm δ a b = D.prob b * s7EffKernel D Sm δ b a := by
    intro a b
    unfold s7EffKernel
    have := modestKernel_rev D Sm a b
    by_cases hab : a = b
    · subst hab; rfl
    · simp only [hab, Ne.symm hab, ite_false]
      linear_combination δ * this
  refine ⟨⟨s7EffKernel D Sm δ, hnn, hrow⟩, fun a b => rfl, ?_, hrev⟩
  intro b
  have : ∀ a, D.prob a * s7EffKernel D Sm δ a b = D.prob b * s7EffKernel D Sm δ b a :=
    fun a => hrev a b
  simp_rw [this, ← Finset.mul_sum, hrow, mul_one]


/-- Paper IV `lem:effective-noise`, items 1-2 (l. 4233-4238): `E χ = (1-δ) χ` for `χ ∈ B_modest`, and
`E χ = χ` for `χ ∈ B_embed ∪ B_non-embed`. -/
theorem s7_effective_noise_basis (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) {δ : ℝ} (hδ : 0 < δ) (j : B.J) :
    s7KernelApply (s7EffKernel D Sm δ) (B.u j) =
      if (∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) then fun a => ((1 - δ : ℝ) : ℂ) * B.u j a
      else B.u j := by
  have _ := hδ
  funext a
  rw [effApply, modestApply_basis D σ Sm hD hconst B j a]
  by_cases hj : ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)
  · simp only [hj, ↓reduceIte]
    ring
  · simp only [hj, ↓reduceIte]
    push_cast
    ring

/-- Paper IV `lem:effective-noise`, consequence (l. 4239-4240): `E^{⊗n} χ = (1-δ)^{effnon(χ)} χ`. -/
theorem s7_effective_noise_mono (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) {δ : ℝ} (hδ : 0 < δ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → B.J) :
    s7EffNoiseOp D Sm δ (s7Mono B.u c) =
      fun x => ((1 - δ : ℝ) : ℂ) ^ (s7EffDeg c) * s7Mono B.u c x := by
  classical
  unfold s7EffNoiseOp
  rw [kernelOp_eigen_mono (s7EffKernel D Sm δ) B.u
    (fun j => if (∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) then ((1 - δ : ℝ) : ℂ) else 1) ?_ c]
  · funext x
    rw [prod_ite_pow (fun j : B.J => ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) c
      ((1 - δ : ℝ) : ℂ)]
    rfl
  · intro j a
    have := congrFun (s7_effective_noise_basis D σ Sm hD hconst B hδ j) a
    rw [this]
    by_cases hj : ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)
    · simp only [hj, ↓reduceIte]
    · simp only [hj, ↓reduceIte, one_mul]


/-- Paper IV `fact:soft-nonbembed-op`, one coordinate (l. 2471-2489): `T_{non-embed,1-ξ} u = u` for
`u ∈ B_embed` and `= (1-ξ) u` for `u ∈ B_2` (here `B_non-embed ∪ B_modest`). -/
theorem s7_soft_nonembed_basis (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) (ξ : ℝ) (j : B.J) :
    s7KernelApply (nonEmbedKernel D σ ξ) (B.u j) =
      if (∃ a, j = Sum.inl a) then B.u j else fun a => ((1 - ξ : ℝ) : ℂ) * B.u j a := by
  funext a
  by_cases hj : ∃ a, j = Sum.inl a
  · obtain ⟨χ, rfl⟩ := hj
    have hc : ∃ a, (Sum.inl χ : B.J) = Sum.inl a := ⟨χ, rfl⟩
    simp only [hc, ↓reduceIte]
    exact nonEmbedApply_fibre_const D σ ξ hD _ (fun a b hab => by simp [hab]) a
  · simp only [hj, ↓reduceIte]
    exact nonEmbedApply_perp D σ ξ _ (u_perp_embed B j hj) a

/-- Paper IV `fact:soft-nonbembed-op` (l. 2464-2469, typo `T^{⊗u}` read `T^{⊗n} u`) and
`claim-nonembed-noise-on-modest-monomials` (l. 4206-4208, the instance for the modest basis):
`T_{non-embed,1-ξ}^{⊗n} χ = (1-ξ)^{nedeg(χ)} χ`. The Section-4 bases `B_1 ∪ B_2` are the instance
`Sm = ∅`. -/
theorem s7_soft_nonembed_op (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) (ξ : ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : ι → B.J) :
    nonEmbedOp D σ ξ (s7Mono B.u c) =
      fun x => ((1 - ξ : ℝ) : ℂ) ^ (s7NeDeg c) * s7Mono B.u c x := by
  classical
  have h : nonEmbedOp D σ ξ (s7Mono B.u c) = s7KernelOp (nonEmbedKernel D σ ξ) (s7Mono B.u c) :=
    rfl
  rw [h, kernelOp_eigen_mono (nonEmbedKernel D σ ξ) B.u
    (fun j => if (∃ a, j = Sum.inl a) then 1 else ((1 - ξ : ℝ) : ℂ)) ?_ c]
  · funext x
    have e : ∀ i, (if (∃ a, c i = Sum.inl a) then (1 : ℂ) else ((1 - ξ : ℝ) : ℂ)) =
        if (¬ ∃ a, c i = Sum.inl a) then ((1 - ξ : ℝ) : ℂ) else 1 := by
      intro i; by_cases hi : ∃ a, c i = Sum.inl a <;> simp [hi]
    simp only [e]
    rw [prod_ite_pow (fun j : B.J => ¬ ∃ a, j = Sum.inl a) c ((1 - ξ : ℝ) : ℂ)]
    rfl
  · intro j a
    have := congrFun (s7_soft_nonembed_basis D σ Sm hD B ξ j) a
    rw [this]
    by_cases hj : ∃ a, j = Sum.inl a
    · simp only [hj, ↓reduceIte, one_mul]
    · simp only [hj, ↓reduceIte]


open scoped Classical in
/-- Paper IV `fact:modest-inf-formula` and `#parseval-computation` (Fact 7.8, l. 4275-4283), coordinate
form: `I_{i,modest}[f] = 2 ∑_{χ : χᵢ ∈ B_modest} |f̂(χ)|²`. -/
theorem s7_modest_inf_formula (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → α) → ℂ) (i : ι) :
    s7ModestInf D Sm f i =
      2 * ∑ c ∈ univ.filter (fun c : ι → B.J => ∃ m : Fin B.nM, c i = Sum.inr (Sum.inr m)),
        ‖s7Coef D B.u f c‖ ^ 2 := by
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  unfold s7ModestInf
  rw [influence_generic D hD (s7ModestKernel D Sm) (modestKernel_row D Sm hD)
    (modestKernel_rev D Sm) B.u hONB
    (fun j => if (∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) then 0 else 1) ?_ f i]
  · congr 1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ m : Fin B.nM, c i = Sum.inr (Sum.inr m) <;> simp [hc]
  · intro j a
    rw [modestApply_basis D σ Sm hD hconst B j a]
    by_cases hj : ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m) <;> simp [hj]

open scoped Classical in
/-- Paper IV `fact:modest-inf-formula`, total form: `I_modest[f] = 2 ∑_χ effnon(χ) |f̂(χ)|²`. -/
theorem s7_modest_total_inf_formula (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → α) → ℂ) :
    s7ModestTotalInf D Sm f =
      2 * ∑ c : ι → B.J, (s7EffDeg c : ℝ) * ‖s7Coef D B.u f c‖ ^ 2 := by
  unfold s7ModestTotalInf
  rw [Finset.sum_congr rfl (fun i _ => s7_modest_inf_formula D σ Sm hD hconst B f i),
    ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hd : (s7EffDeg c : ℝ) =
      ∑ i, if (∃ m : Fin B.nM, c i = Sum.inr (Sum.inr m)) then (1 : ℝ) else 0 :=
    countWhere_eq_sum (fun j : B.J => ∃ m : Fin B.nM, j = Sum.inr (Sum.inr m)) c
  rw [hd, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

open scoped Classical in
/-- Paper IV `fact:nonembed-inf-formula` item 1 (Fact 4.12, l. 2563):
`I_{j,non-embed}[f] = 2 ∑_{χ : χⱼ ∉ B_embed} |f̂(χ)|²`. -/
theorem s7_nonembed_inf_formula (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) (j : ι) :
    s7NonEmbedInf D σ f j =
      2 * ∑ c ∈ univ.filter (fun c : ι → B.J => ¬ ∃ a, c j = Sum.inl a),
        ‖s7Coef D B.u f c‖ ^ 2 := by
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  have hfib : ∀ a, 0 < ∑ c ∈ univ.filter (fun c => σ c = σ a), D.prob c := fun a =>
    Finset.sum_pos (fun c _ => hD c) ⟨a, by simp⟩
  obtain ⟨T, hT, -, hrev⟩ := nonEmbedKernel_isReversible D σ (le_refl (0 : ℝ) |>.trans zero_le_one)
    (le_refl (1 : ℝ)) hfib
  have hrow : ∀ a, ∑ b, nonEmbedKernel D σ 1 a b = 1 := fun a => by
    have := T.row_sum a
    simp only [hT] at this
    exact this
  have hrev' : ∀ a b, D.prob a * nonEmbedKernel D σ 1 a b =
      D.prob b * nonEmbedKernel D σ 1 b a := fun a b => by
    have := hrev a b
    rwa [hT, hT] at this
  unfold s7NonEmbedInf
  rw [influence_generic D hD (nonEmbedKernel D σ 1) hrow hrev' B.u hONB
    (fun j => if (∃ a, j = Sum.inl a) then 1 else 0) ?_ f j]
  · congr 1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ a, c j = Sum.inl a <;> simp [hc]
  · intro j' a
    have := congrFun (s7_soft_nonembed_basis D σ Sm hD B 1 j') a
    rw [this]
    by_cases hj : ∃ a, j' = Sum.inl a <;> simp [hj]

open scoped Classical in
/-- Paper IV `fact:nonembed-inf-formula` item 2, with the factor 2 forced by summing item 1 over `j`
(the printed item 2 omits it). -/
theorem s7_nonembed_total_inf_formula (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) :
    s7NonEmbedTotalInf D σ f =
      2 * ∑ c : ι → B.J, (s7NeDeg c : ℝ) * ‖s7Coef D B.u f c‖ ^ 2 := by
  unfold s7NonEmbedTotalInf
  rw [Finset.sum_congr rfl (fun i _ => s7_nonembed_inf_formula D σ Sm hD B f i),
    ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hd : (s7NeDeg c : ℝ) =
      ∑ i, if (¬ ∃ a, c i = Sum.inl a) then (1 : ℝ) else 0 :=
    countWhere_eq_sum (fun j : B.J => ¬ ∃ a, j = Sum.inl a) c
  rw [hd, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- spectral form of the effective noise operator (used in App. B, l. 9097-9105):
`E_{non-embed,1-δ}^{⊗n} f = ∑_χ (1-δ)^{effnon(χ)} f̂(χ) χ`. -/
theorem s7_effNoiseOp_expansion (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) {δ : ℝ} (hδ : 0 < δ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) :
    s7EffNoiseOp D Sm δ f = fun x => ∑ c : ι → B.J,
      ((1 - δ : ℝ) : ℂ) ^ (s7EffDeg c) * s7Coef D B.u f c * s7Mono B.u c x := by
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  have hf := s7_fourier_expansion D hD B.u hONB f
  funext x
  unfold s7EffNoiseOp
  rw [kernelOp_expand (s7EffKernel D Sm δ) B.u (fun c => s7Coef D B.u f c) f hf x]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := congrFun (s7_effective_noise_mono D σ Sm hD hconst B hδ c) x
  unfold s7EffNoiseOp at this
  rw [this]
  ring

/-- spectral form of the non-embedding noise operator: `T_{non-embed,1-ξ}^{⊗n} f
= ∑_χ (1-ξ)^{nedeg(χ)} f̂(χ) χ`. -/
theorem s7_nonEmbedOp_expansion (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) (ξ : ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : (ι → α) → ℂ) :
    nonEmbedOp D σ ξ f = fun x => ∑ c : ι → B.J,
      ((1 - ξ : ℝ) : ℂ) ^ (s7NeDeg c) * s7Coef D B.u f c * s7Mono B.u c x := by
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  have hf := s7_fourier_expansion D hD B.u hONB f
  funext x
  have h : nonEmbedOp D σ ξ f x = s7KernelOp (nonEmbedKernel D σ ξ) f x := rfl
  rw [h, kernelOp_expand (nonEmbedKernel D σ ξ) B.u (fun c => s7Coef D B.u f c) f hf x]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := congrFun (s7_soft_nonembed_op D σ Sm hD B ξ c) x
  have h' : nonEmbedOp D σ ξ (s7Mono B.u c) x = s7KernelOp (nonEmbedKernel D σ ξ) (s7Mono B.u c) x :=
    rfl
  rw [← h', this]
  ring

/-- `NEStab_{1-ξ}(f; μ_x^{⊗n}) = ∑_χ (1-ξ)^{nedeg(χ)} |f̂(χ)|²` (the computation inside
paper IV `claim:increase-noise-decrease-stab`, l. 2506-2512; the Section-4 basis `B_1 ∪ B_2` is the case
`Sm = ∅`). -/
theorem s7_nestab_spectral (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (B : S7ModestBasis D σ Sm) (ξ : ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : (ι → α) → ℂ) :
    nestab D σ ξ f = ∑ c : ι → B.J, (((1 - ξ) ^ (s7NeDeg c) * ‖s7Coef D B.u f c‖ ^ 2 : ℝ) : ℂ) := by
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  unfold nestab
  refine cinner_weighted D hD B.u hONB f _ (fun c => (1 - ξ) ^ (s7NeDeg c)) ?_
  rw [s7_nonEmbedOp_expansion D σ Sm hD B ξ f]
  funext x
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  ring

/-- `⟨f, E_{non-embed,1-δ}^{⊗n} f⟩ = ∑_χ (1-δ)^{effnon(χ)} |f̂(χ)|²`. -/
theorem s7_effStab_spectral (D : FinProb α) (σ : α → H) (Sm : Finset α)
    (hD : ∀ a, 0 < D.prob a) (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x')
    (B : S7ModestBasis D σ Sm) {δ : ℝ} (hδ : 0 < δ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → α) → ℂ) :
    (D.pi ι).cinner f (s7EffNoiseOp D Sm δ f) =
      ∑ c : ι → B.J, (((1 - δ) ^ (s7EffDeg c) * ‖s7Coef D B.u f c‖ ^ 2 : ℝ) : ℂ) := by
  have hONB := s7_modestBasis_isONB D σ Sm hD B
  refine cinner_weighted D hD B.u hONB f _ (fun c => (1 - δ) ^ (s7EffDeg c)) ?_
  rw [s7_effNoiseOp_expansion D σ Sm hD hconst B hδ f]
  funext x
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  ring

omit [Fintype α] [DecidableEq α] in
/-- the modest variance of a function constant on `Σ_modest` is `0` (used by `use_relaxed_base`). -/
theorem s7ModestVar_eq_zero_of_constOn (Sm : Finset α) (hSm : Sm.Nonempty) (f : α → ℂ)
    (hf : f ∈ s7ConstOn Sm) : s7ModestVar Sm hSm f = 0 := by
  unfold s7ModestVar
  rw [Finset.sum_eq_zero, zero_div]
  intro a ha
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [hf a ha b hb, sub_self]
  simp

end S7ChainsThms

end TrackB
end RestrictedPolynomials
end
