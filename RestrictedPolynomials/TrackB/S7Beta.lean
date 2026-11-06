module

public import RestrictedPolynomials.TrackB.S7ConnComp
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S7Beta
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {K₁ K₂ K₃ K₄ K₅ K₆ : Type}

/-- `𝔼_{(x,y,z) ∼ μ^{⊗ι}} F(y,z) g(y) h(z)` for `F` a function of `(y, z)` jointly (Def. l. 4458,
5259); `corr3` is the case `F(y,z) = f(x)`. -/
def s7CorrF {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) : ℂ :=
  (μ.pi ι).cexpect fun t =>
    F (fun i => ((t i).2.1, (t i).2.2)) * g (fun i => (t i).2.1) * h (fun i => (t i).2.2)

/-- Paper IV `definition-beta-prime` (Def. 7.?, l. 4327-4335): `β'_{n,d,d'}[μ] = sup |𝔼 f g h| / (‖f‖‖g‖‖h‖)`
over `f ∈ F'_{n,d,d'}`, `g ∈ G_n`, `h ∈ H_n`, taken in `[0, ∞]` over the triples of nonzero norms
(the zero function is implicitly excluded). The bases `ux, uy, uz` are the chosen ones of Def. 7.1
(`uy`, `uz` the `Sm = ∅` instances); the value does not depend on them
(`s7BetaP_basis_indep`). Outside `n ≥ d ≥ d'` the class may contain no nonzero function and the
supremum of the empty set is `0`. -/
def s7BetaP (μ : FinProb (X × Y × Z)) (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
    f ∈ s7ClassFp (lawX μ) ux n d d' ∧ g ∈ s7ClassG (lawY μ) uy n ∧
    h ∈ s7ClassG (lawZ μ) uz n ∧
    cl2norm (lawX μ) f ≠ 0 ∧ cl2norm (lawY μ) g ≠ 0 ∧ cl2norm (lawZ μ) h ≠ 0 ∧
    r = ENNReal.ofReal (‖corr3 μ f g h‖ /
      (cl2norm (lawX μ) f * cl2norm (lawY μ) g * cl2norm (lawZ μ) h))}

/-- Paper IV `definition-beta` (Def. 7.22, l. 4452-4461): `β_{n,d,d'}[μ]`, the `cc`-version (`F ∈ F_{n,d,d'}`
a function of `(y,z)`, norm in `L²(μ_{y,z}^{⊗n})`). Negative indices in `β_{n-1,d-1,d'-1}` read
as `0`, by truncated subtraction in `ℕ`. -/
def s7Beta (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
    F ∈ s7ClassF μ hμ ux n d d' ∧ g ∈ s7ClassG (lawY μ) uy n ∧ h ∈ s7ClassG (lawZ μ) uz n ∧
    cl2norm (s7LawYZ μ) F ≠ 0 ∧ cl2norm (lawY μ) g ≠ 0 ∧ cl2norm (lawZ μ) h ≠ 0 ∧
    r = ENNReal.ofReal (‖s7CorrF μ F g h‖ /
      (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h))}

/-- Paper IV `definition-delta-parameter` (Def. 9.2, l. 5252-5261): `δ_{n,d'}[μ]`, `F ∈ F_{n,d'}`, `g`, `h`
arbitrary (the supremum is over nonzero `F, g, h`; the three-index `δ_{n',e,e'}` of l. 5944-5953
is a typo in the source). -/
def s7DeltaParam (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) (n d' : ℕ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
    F ∈ s7ClassFn μ hμ ux n d' ∧
    cl2norm (s7LawYZ μ) F ≠ 0 ∧ cl2norm (lawY μ) g ≠ 0 ∧ cl2norm (lawZ μ) h ≠ 0 ∧
    r = ENNReal.ofReal (‖s7CorrF μ F g h‖ /
      (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h))}

/-! ### Theorems of file 4 (targets) -/


private theorem s7b_push_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {ι : Type} [Fintype ι] [DecidableEq ι] (a : α → β) (w : ι → α → ℝ) (G : (ι → β) → ℂ) :
    ∑ x : ι → α, ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)) =
    ∑ b : ι → β, ((∏ i, ∑ c ∈ univ.filter (fun c => a c = b i), w i c : ℝ) : ℂ) * G b := by
  rw [← Finset.sum_fiberwise univ (fun x : ι → α => fun i => a (x i))
    (fun x => ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ x ∈ univ.filter (fun x : ι → α => (fun i => a (x i)) = b),
      ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)) = ((∏ i, w i (x i) : ℝ) : ℂ) * G b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Fintype.mem_piFinset, funext_iff]

private theorem s7b_cexpect_pi_push {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (a : α → β)
    (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (s7b_push_sum a (fun _ c => π.prob c) G).symm

private theorem s7b_sum_prod {ι : Type} [Fintype ι] [DecidableEq ι] (py : Y → ℝ) (pz : Z → ℝ)
    (a : (ι → Y) → ℝ) (b : (ι → Z) → ℝ) :
    ∑ w : ι → Y × Z, (∏ i, (py (w i).1 * pz (w i).2)) *
        (a (fun i => (w i).1) * b (fun i => (w i).2)) =
      (∑ y : ι → Y, (∏ i, py (y i)) * a y) * (∑ z : ι → Z, (∏ i, pz (z i)) * b z) := by
  let e : (ι → Y × Z) ≃ (ι → Y) × (ι → Z) :=
    Equiv.arrowProdEquivProdArrow ι (fun _ => Y) (fun _ => Z)
  let G : (ι → Y) × (ι → Z) → ℝ := fun p => (∏ i, py (p.1 i)) * a p.1 * ((∏ i, pz (p.2 i)) * b p.2)
  calc _ = ∑ w : ι → Y × Z, G (e w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [G, e, Equiv.arrowProdEquivProdArrow_apply, Finset.prod_mul_distrib]
        ring
    _ = ∑ p, G p := Equiv.sum_comp e G
    _ = _ := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

private theorem s7b_term {p a b : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p * (a * b) = Real.sqrt (p * a ^ 2) * Real.sqrt (p * b ^ 2) := by
  rw [Real.sqrt_mul hp, Real.sqrt_mul hp, Real.sqrt_sq ha, Real.sqrt_sq hb]
  calc p * (a * b) = (Real.sqrt p * Real.sqrt p) * (a * b) := by rw [Real.mul_self_sqrt hp]
    _ = _ := by ring

private theorem s7_aux_pos {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (na : a ≠ 0)
    (nb : b ≠ 0) (nc : c ≠ 0) : 0 < a * b * c :=
  mul_pos (mul_pos (lt_of_le_of_ne ha (Ne.symm na)) (lt_of_le_of_ne hb (Ne.symm nb)))
    (lt_of_le_of_ne hc (Ne.symm nc))

private theorem s7_cl2norm_nn {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] (π : FinProb α)
    (f : (ι → α) → ℂ) : 0 ≤ cl2norm π f := Real.sqrt_nonneg _

/-- characterisation of `β'`: `β' ≤ b` iff `|𝔼 f g h| ≤ b ‖f‖‖g‖‖h‖` on the classes. -/
theorem s7BetaP_le_iff (μ : FinProb (X × Y × Z)) (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    s7BetaP μ ux uy uz n d d' ≤ ENNReal.ofReal b ↔
      ∀ (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
        f ∈ s7ClassFp (lawX μ) ux n d d' → g ∈ s7ClassG (lawY μ) uy n →
        h ∈ s7ClassG (lawZ μ) uz n →
        cl2norm (lawX μ) f ≠ 0 → cl2norm (lawY μ) g ≠ 0 → cl2norm (lawZ μ) h ≠ 0 →
        ‖corr3 μ f g h‖ ≤ b * (cl2norm (lawX μ) f * cl2norm (lawY μ) g * cl2norm (lawZ μ) h) := by
  unfold s7BetaP; rw [sSup_le_iff]; constructor
  · intro Hs f g h hf hg hh nf ng nh
    have hr := Hs _ ⟨f, g, h, hf, hg, hh, nf, ng, nh, rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb] at hr
    rwa [div_le_iff₀ (s7_aux_pos (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) nf ng nh)] at hr
  · rintro Hs r ⟨f, g, h, hf, hg, hh, nf, ng, nh, rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb, div_le_iff₀ (s7_aux_pos (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) nf ng nh)]
    exact Hs f g h hf hg hh nf ng nh

/-- characterisation of `β`. -/
theorem s7Beta_le_iff (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    s7Beta μ hμ ux uy uz n d d' ≤ ENNReal.ofReal b ↔
      ∀ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
        F ∈ s7ClassF μ hμ ux n d d' → g ∈ s7ClassG (lawY μ) uy n →
        h ∈ s7ClassG (lawZ μ) uz n →
        cl2norm (s7LawYZ μ) F ≠ 0 → cl2norm (lawY μ) g ≠ 0 → cl2norm (lawZ μ) h ≠ 0 →
        ‖s7CorrF μ F g h‖ ≤
          b * (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h) := by
  unfold s7Beta; rw [sSup_le_iff]; constructor
  · intro Hs F g h hf hg hh nf ng nh
    have hr := Hs _ ⟨F, g, h, hf, hg, hh, nf, ng, nh, rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb] at hr
    rwa [div_le_iff₀ (s7_aux_pos (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) nf ng nh)] at hr
  · rintro Hs r ⟨F, g, h, hf, hg, hh, nf, ng, nh, rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb, div_le_iff₀ (s7_aux_pos (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) nf ng nh)]
    exact Hs F g h hf hg hh nf ng nh

/-- characterisation of `δ_{n,d'}`. -/
theorem s7DeltaParam_le_iff (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) (n d' : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    s7DeltaParam μ hμ ux n d' ≤ ENNReal.ofReal b ↔
      ∀ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
        F ∈ s7ClassFn μ hμ ux n d' →
        cl2norm (s7LawYZ μ) F ≠ 0 → cl2norm (lawY μ) g ≠ 0 → cl2norm (lawZ μ) h ≠ 0 →
        ‖s7CorrF μ F g h‖ ≤
          b * (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h) := by
  unfold s7DeltaParam; rw [sSup_le_iff]; constructor
  · intro Hs F g h hF nF ng nh
    have hr := Hs _ ⟨F, g, h, hF, nF, ng, nh, rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb] at hr
    rwa [div_le_iff₀ (s7_aux_pos (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) nF ng nh)] at hr
  · rintro Hs r ⟨F, g, h, hF, nF, ng, nh, rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb, div_le_iff₀ (s7_aux_pos (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) (s7_cl2norm_nn _ _) nF ng nh)]
    exact Hs F g h hF nF ng nh

/-- `𝔼 f(x) g(y) h(z) = 𝔼 (W f)(y,z) g(y) h(z)` (the identity of l. 4477). -/
theorem s7_corr3_eq_corrF_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {ι : Type}
    [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 μ f g h = s7CorrF μ (s7W hμ f) g h := by
  unfold corr3 s7CorrF FinProb.cexpect
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h0 : (μ.pi ι).prob t = 0
  · simp [h0]
  · have hpre : ∀ i, s7Pre hμ (t i).2.1 (t i).2.2 = (t i).1 := by
      intro i
      have hi : μ.prob (t i) ≠ 0 := by
        intro h
        apply h0
        show ∏ j, μ.prob (t j) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i) h
      exact (s7Pre_unique hμ (x := (t i).1) (y := (t i).2.1) (z := (t i).2.2) hi).symm
    simp only [s7W, hpre]

/-- §7.3.1 (l. 4473-4483): `β'_{n,d,d'}[μ] ≤ β_{n,d,d'}[μ]` (same bases). -/
theorem s7_betaP_le_beta (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) : s7BetaP μ ux uy uz n d d' ≤ s7Beta μ hμ ux uy uz n d d' := by
  refine sSup_le ?_
  rintro r ⟨f, g, h, hf, hg, hh, nf, ng, nh, rfl⟩
  refine le_sSup ⟨s7W hμ f, g, h, ?_, hg, hh, ?_, ng, nh, ?_⟩
  · exact (s7_mem_classF_iff μ hμ ux n d d' _).2 ⟨f, rfl, hf⟩
  · rwa [s7_cl2norm_W]
  · rw [s7_cl2norm_W, s7_corr3_eq_corrF_W μ hμ f g h]

/-- `β_{n,d,d'} ≤ δ_{n,d'}` (`F_{n,d,d'} ⊆ F_{n,d'}`; used by `#beta-at-most-delta`). -/
theorem s7_beta_le_deltaParam (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) : s7Beta μ hμ ux uy uz n d d' ≤ s7DeltaParam μ hμ ux n d' := by
  refine sSup_le ?_
  rintro r ⟨F, g, h, hF, hg, hh, nF, ng, nh, rfl⟩
  exact le_sSup ⟨F, g, h, s7_classF_subset_classFn μ hμ ux n d d' hF, nF, ng, nh, rfl⟩

/-- Paper IV `claim-beta-trivial-bound` (l. 3387-3396, 5220-5223): when `y` and `z` are independent in `μ`
(`μ_{y,z}` uniform, hypothesis 5), Cauchy-Schwarz gives `|𝔼 F g h| ≤ ‖F‖‖g‖‖h‖`. -/
theorem s7_corrF_trivial_bound (μ : FinProb (X × Y × Z))
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) :
    ‖s7CorrF μ F g h‖ ≤ cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h := by
  have hE : s7CorrF μ F g h = ∑ w : ι → Y × Z, (((∏ i, (s7LawYZ μ).prob (w i) : ℝ)) : ℂ) *
      (F w * g (fun i => (w i).1) * h (fun i => (w i).2)) :=
    (s7b_cexpect_pi_push μ (fun p : X × Y × Z => (p.2.1, p.2.2))
      (fun w : ι → Y × Z => F w * g (fun i => (w i).1) * h (fun i => (w i).2))).symm
  have hP : ∀ w : ι → Y × Z, 0 ≤ ∏ i, (s7LawYZ μ).prob (w i) :=
    fun w => Finset.prod_nonneg fun i _ => (s7LawYZ μ).nonneg _
  have h1 : ‖s7CorrF μ F g h‖ ≤ ∑ w : ι → Y × Z, ((∏ i, (s7LawYZ μ).prob (w i)) *
      (‖F w‖ * (‖g (fun i => (w i).1)‖ * ‖h (fun i => (w i).2)‖))) := by
    rw [hE]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP w), norm_mul, norm_mul]
    ring
  have h2 : ∑ w : ι → Y × Z, ((∏ i, (s7LawYZ μ).prob (w i)) *
      (‖F w‖ * (‖g (fun i => (w i).1)‖ * ‖h (fun i => (w i).2)‖))) ≤
      Real.sqrt (∑ w : ι → Y × Z, (∏ i, (s7LawYZ μ).prob (w i)) * ‖F w‖ ^ 2) *
      Real.sqrt (∑ w : ι → Y × Z, (∏ i, (s7LawYZ μ).prob (w i)) *
        (‖g (fun i => (w i).1)‖ * ‖h (fun i => (w i).2)‖) ^ 2) := by
    calc _ = ∑ w : ι → Y × Z, Real.sqrt ((∏ i, (s7LawYZ μ).prob (w i)) * ‖F w‖ ^ 2) *
          Real.sqrt ((∏ i, (s7LawYZ μ).prob (w i)) *
            (‖g (fun i => (w i).1)‖ * ‖h (fun i => (w i).2)‖) ^ 2) :=
          Finset.sum_congr rfl fun w _ => s7b_term (hP w) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _ (fun w => mul_nonneg (hP w) (sq_nonneg _))
            (fun w => mul_nonneg (hP w) (sq_nonneg _))
  have h3 : ∑ w : ι → Y × Z, (∏ i, (s7LawYZ μ).prob (w i)) *
        (‖g (fun i => (w i).1)‖ * ‖h (fun i => (w i).2)‖) ^ 2 =
      cl2sq (lawY μ) g * cl2sq (lawZ μ) h := by
    have := s7b_sum_prod (ι := ι) (lawY μ).prob (lawZ μ).prob (fun y => ‖g y‖ ^ 2)
      (fun z => ‖h z‖ ^ 2)
    unfold cl2sq FinProb.expect
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_pow]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hind (w i).1 (w i).2
  have h4 : 0 ≤ cl2sq (lawY μ) g := Finset.sum_nonneg fun y _ =>
    mul_nonneg (Finset.prod_nonneg fun i _ => (lawY μ).nonneg _) (sq_nonneg _)
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [h3, Real.sqrt_mul h4]
  unfold cl2norm
  have hF : cl2sq (s7LawYZ μ) F =
      ∑ w : ι → Y × Z, (∏ i, (s7LawYZ μ).prob (w i)) * ‖F w‖ ^ 2 := rfl
  rw [hF]
  ring

/-- Paper IV `claim-beta-trivial-bound`: `δ_{n,d'} ≤ 1`, hence `β_{n,d,d'} ≤ 1` (via `s7_beta_le_deltaParam`)
and `β'_{n,d,d'} ≤ 1`. -/
theorem s7_deltaParam_le_one (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) (n d' : ℕ) : s7DeltaParam μ hμ ux n d' ≤ 1 := by
  have h := (s7DeltaParam_le_iff μ hμ ux n d' (b := 1) zero_le_one).2
    (fun F g h _ _ _ _ => by
      rw [one_mul]; exact s7_corrF_trivial_bound μ hind F g h)
  simpa using h

theorem s7_beta_le_one (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) : s7Beta μ hμ ux uy uz n d d' ≤ 1 := by
  exact (s7_beta_le_deltaParam μ hμ ux uy uz n d d').trans (s7_deltaParam_le_one μ hμ hind ux n d')

theorem s7_betaP_le_one (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (uy : AddChar H ℂ ⊕ (K₃ ⊕ K₄) → Y → ℂ) (uz : AddChar H ℂ ⊕ (K₅ ⊕ K₆) → Z → ℂ)
    (n d d' : ℕ) : s7BetaP μ ux uy uz n d d' ≤ 1 := by
  exact (s7_betaP_le_beta μ hμ ux uy uz n d d').trans (s7_beta_le_one μ hμ hind ux uy uz n d d')


private theorem s7b_classF_indep (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (Sm : Finset X) (hDx : ∀ a, 0 < (lawX μ).prob a)
    (Bx Bx' : S7ModestBasis (lawX μ) σ Sm) (n d d' : ℕ) :
    s7ClassF μ hμ Bx.u n d d' = s7ClassF μ hμ Bx'.u n d d' := by
  ext F
  rw [s7_mem_classF_iff, s7_mem_classF_iff, s7_classFp_basis_indep (lawX μ) hDx σ Sm Bx Bx']

private theorem s7b_classFn_indep (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (Sm : Finset X) (hDx : ∀ a, 0 < (lawX μ).prob a)
    (Bx Bx' : S7ModestBasis (lawX μ) σ Sm) (n d' : ℕ) :
    s7ClassFn μ hμ Bx.u n d' = s7ClassFn μ hμ Bx'.u n d' := by
  ext F
  rw [s7_mem_classFn_iff, s7_mem_classFn_iff]
  exact exists_congr fun f => and_congr_right fun _ =>
    s7_effDegGE_basis_indep (lawX μ) hDx σ Sm Bx Bx' f d'

/-- `β'` does not depend on the chosen bases of Def. 7.1. -/
theorem s7BetaP_basis_indep (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (Sm : Finset X) (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a)
    (Bx Bx' : S7ModestBasis (lawX μ) σ Sm) (By By' : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
    (Bz Bz' : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (n d d' : ℕ) :
    s7BetaP μ Bx.u By.u Bz.u n d d' = s7BetaP μ Bx'.u By'.u Bz'.u n d d' := by
  unfold s7BetaP
  rw [s7_classFp_basis_indep (lawX μ) hDx σ Sm Bx Bx' n d d',
    s7_classG_basis_indep (lawY μ) hDy γ ∅ By By' n,
    s7_classG_basis_indep (lawZ μ) hDz φ ∅ Bz Bz' n]

/-- `β` does not depend on the chosen bases. -/
theorem s7Beta_basis_indep (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (γ : Y → H) (φ : Z → H)
    (Sm : Finset X) (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a)
    (Bx Bx' : S7ModestBasis (lawX μ) σ Sm) (By By' : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
    (Bz Bz' : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (n d d' : ℕ) :
    s7Beta μ hμ Bx.u By.u Bz.u n d d' = s7Beta μ hμ Bx'.u By'.u Bz'.u n d d' := by
  unfold s7Beta
  rw [s7b_classF_indep μ hμ σ Sm hDx Bx Bx' n d d',
    s7_classG_basis_indep (lawY μ) hDy γ ∅ By By' n,
    s7_classG_basis_indep (lawZ μ) hDz φ ∅ Bz Bz' n]

/-- `δ_{n,d'}` does not depend on the chosen bases. -/
theorem s7DeltaParam_basis_indep (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (Sm : Finset X) (hDx : ∀ a, 0 < (lawX μ).prob a)
    (Bx Bx' : S7ModestBasis (lawX μ) σ Sm) (n d' : ℕ) :
    s7DeltaParam μ hμ Bx.u n d' = s7DeltaParam μ hμ Bx'.u n d' := by
  unfold s7DeltaParam
  rw [s7b_classFn_indep μ hμ σ Sm hDx Bx Bx' n d']


private theorem s7b_card_pos : (0 : ℝ) < (Fintype.card H : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- the three marginals of `hunif` are uniform. -/
private theorem s7b_unif_marg (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0) :
    (∀ h : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = h), μ.prob p =
        1 / (Fintype.card H : ℝ)) ∧
    (∀ h : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => γ p.2.1 = h), μ.prob p =
        1 / (Fintype.card H : ℝ)) ∧
    (∀ h : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => φ p.2.2 = h), μ.prob p =
        1 / (Fintype.card H : ℝ)) := by
  have hc := s7b_card_pos (H := H)
  have hk : ∀ k : ℝ, (Fintype.card H : ℝ) * k = Fintype.card H * k := fun _ => rfl
  have hfin : (Fintype.card H : ℝ) * (1 / (Fintype.card H : ℝ) ^ 2) = 1 / (Fintype.card H : ℝ) := by
    field_simp
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have e : ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = h), μ.prob p =
        ∑ q : H × H, ∑ p ∈ univ.filter (fun p : X × Y × Z =>
          (σ p.1, γ p.2.1, φ p.2.2) = (h, q.1, q.2)), μ.prob p := by
      rw [← Finset.sum_fiberwise (s := univ.filter (fun p : X × Y × Z => σ p.1 = h))
        (g := fun p => (γ p.2.1, φ p.2.2)) (f := μ.prob)]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      simp only [Prod.ext_iff]
      try tauto
    rw [e]
    simp only [hunif, Fintype.sum_prod_type]
    have : ∀ b : H, ∑ c : H, (if h + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0) =
        1 / (Fintype.card H : ℝ) ^ 2 := by
      intro b
      have : ∀ c : H, (h + b + c = 0) ↔ (c = -(h + b)) := fun c =>
        ⟨fun e => eq_neg_of_add_eq_zero_right e, fun e => by rw [e]; simp⟩
      simp_rw [this]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hfin
  · have e : ∑ p ∈ univ.filter (fun p : X × Y × Z => γ p.2.1 = h), μ.prob p =
        ∑ q : H × H, ∑ p ∈ univ.filter (fun p : X × Y × Z =>
          (σ p.1, γ p.2.1, φ p.2.2) = (q.1, h, q.2)), μ.prob p := by
      rw [← Finset.sum_fiberwise (s := univ.filter (fun p : X × Y × Z => γ p.2.1 = h))
        (g := fun p => (σ p.1, φ p.2.2)) (f := μ.prob)]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      simp only [Prod.ext_iff]
      try tauto
    rw [e]
    simp only [hunif, Fintype.sum_prod_type]
    have : ∀ a : H, ∑ c : H, (if a + h + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0) =
        1 / (Fintype.card H : ℝ) ^ 2 := by
      intro a
      have : ∀ c : H, (a + h + c = 0) ↔ (c = -(a + h)) := fun c =>
        ⟨fun e => eq_neg_of_add_eq_zero_right e, fun e => by rw [e]; simp⟩
      simp_rw [this]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hfin
  · have e : ∑ p ∈ univ.filter (fun p : X × Y × Z => φ p.2.2 = h), μ.prob p =
        ∑ q : H × H, ∑ p ∈ univ.filter (fun p : X × Y × Z =>
          (σ p.1, γ p.2.1, φ p.2.2) = (q.1, q.2, h)), μ.prob p := by
      rw [← Finset.sum_fiberwise (s := univ.filter (fun p : X × Y × Z => φ p.2.2 = h))
        (g := fun p => (σ p.1, γ p.2.1)) (f := μ.prob)]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      simp only [Prod.ext_iff]
      try tauto
    rw [e]
    simp only [hunif, Fintype.sum_prod_type]
    have : ∀ a : H, ∑ b : H, (if a + b + h = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0) =
        1 / (Fintype.card H : ℝ) ^ 2 := by
      intro a
      have : ∀ b : H, (a + b + h = 0) ↔ (b = -(a + h)) := fun b =>
        ⟨fun e => by
          have : b = -(a + h) := by
            rw [add_right_comm] at e
            exact eq_neg_of_add_eq_zero_right e
          exact this, fun e => by rw [e, add_right_comm]; simp⟩
      simp_rw [this]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hfin

private theorem s7b_push1 {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) (G : β → ℂ) :
    ∑ a, (π.prob a : ℂ) * G (f a) = ∑ b, ((mergePush π f).prob b : ℂ) * G b := by
  rw [← Finset.sum_fiberwise univ f (fun a => (π.prob a : ℂ) * G (f a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ a ∈ univ.filter (fun a => f a = b), (π.prob a : ℂ) * G (f a) =
      (π.prob a : ℂ) * G b := by
    intro a ha
    rw [(Finset.mem_filter.1 ha).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  show _ = ((∑ a ∈ univ.filter (fun a => f a = b), π.prob a : ℝ) : ℂ) * G b
  rw [Complex.ofReal_sum]

private theorem s7b_supp (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    {p : X × Y × Z} (hp : μ.prob p ≠ 0) : σ p.1 + γ p.2.1 + φ p.2.2 = 0 := by
  by_contra hne
  have h1 := hunif (σ p.1) (γ p.2.1) (φ p.2.2)
  rw [if_neg hne] at h1
  have h2 : μ.prob p ≤ ∑ q ∈ univ.filter (fun q : X × Y × Z =>
      (σ q.1, γ q.2.1, φ q.2.2) = (σ p.1, γ p.2.1, φ p.2.2)), μ.prob q :=
    Finset.single_le_sum (f := μ.prob) (fun q _ => μ.nonneg q) (by simp)
  rw [h1] at h2
  exact hp (le_antisymm h2 (μ.nonneg p))

private theorem s7b_char_star (χ : AddChar H ℂ) (a : H) : star (χ a) = χ (-a) := by
  rw [AddChar.map_neg_eq_conj]
  rfl

private theorem s7b_split (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (χ : AddChar H ℂ) (g : Y → ℂ) (h : Z → ℂ) :
    μ.cexpect (fun p => χ (σ p.1) * g p.2.1 * h p.2.2) =
      (lawY μ).cexpect (fun y => g y * χ (-γ y)) * (lawZ μ).cexpect (fun z => h z * χ (-φ z)) := by
  have step1 : μ.cexpect (fun p => χ (σ p.1) * g p.2.1 * h p.2.2) =
      ∑ p : X × Y × Z, (μ.prob p : ℂ) *
        ((fun v : Y × Z => (g v.1 * χ (-γ v.1)) * (h v.2 * χ (-φ v.2))) (p.2.1, p.2.2)) := by
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h0 : μ.prob p = 0
    · simp [h0]
    · have hs := s7b_supp μ σ γ φ hunif h0
      have : σ p.1 = -γ p.2.1 + -φ p.2.2 := by
        have : σ p.1 = -(γ p.2.1 + φ p.2.2) := eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
        rw [this, neg_add]
      simp only [this, AddChar.map_add_eq_mul]
      ring
  rw [step1, s7b_push1 μ (fun p : X × Y × Z => (p.2.1, p.2.2))
    (fun v : Y × Z => (g v.1 * χ (-γ v.1)) * (h v.2 * χ (-φ v.2)))]
  have step2 : ∀ v : Y × Z, (((mergePush μ fun p : X × Y × Z => (p.2.1, p.2.2)).prob v : ℝ) : ℂ) =
      (((lawY μ).prob v.1 * (lawZ μ).prob v.2 : ℝ) : ℂ) := fun v => by
    rw [← hind v.1 v.2]
    rfl
  simp only [step2, FinProb.cexpect, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  push_cast
  ring

private theorem s7b_embed_lin (μ : FinProb (X × Y × Z)) (σ : X → H) (g : Y → ℂ) (h : Z → ℂ)
    (hχ : ∀ χ : AddChar H ℂ, μ.cexpect (fun p => χ (σ p.1) * g p.2.1 * h p.2.2) = 0)
    (f : X → ℂ) (hf : f ∈ embedSpan σ) :
    μ.cexpect (fun p => f p.1 * g p.2.1 * h p.2.2) = 0 := by
  unfold embedSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨χ, rfl⟩ := hx
    exact hχ χ
  | zero => simp [FinProb.cexpect]
  | add x y _ _ hx hy =>
    have : μ.cexpect (fun p => (x + y) p.1 * g p.2.1 * h p.2.2) =
        μ.cexpect (fun p => x p.1 * g p.2.1 * h p.2.2) +
        μ.cexpect (fun p => y p.1 * g p.2.1 * h p.2.2) := by
      simp only [FinProb.cexpect, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [this, hx, hy, add_zero]
  | smul a x _ hx =>
    have : μ.cexpect (fun p => (a • x) p.1 * g p.2.1 * h p.2.2) =
        a * μ.cexpect (fun p => x p.1 * g p.2.1 * h p.2.2) := by
      simp only [FinProb.cexpect, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [this, hx, mul_zero]

private theorem s7b_cexpect_perp {α : Type} [Fintype α] (D : FinProb α) (g : α → ℂ) (χ : AddChar H ℂ)
    (γ : α → H) (hg : g ∈ s7Perp D (embedSpan γ)) :
    D.cexpect (fun a => g a * χ (-γ a)) = 0 := by
  have h0 := hg (fun a => χ (γ a)) (Submodule.subset_span ⟨χ, rfl⟩)
  simp only [FinProb.cinner, FinProb.cexpect, s7b_char_star] at h0 ⊢
  exact h0


private theorem s7b_fiber_exp {T : Type} [Fintype T] [DecidableEq T] (μ : FinProb (X × Y × Z))
    (u : X × Y × Z → T) {k : ℝ} (hu : ∀ a, ∑ p ∈ univ.filter (fun p => u p = a), μ.prob p = k)
    (F : T → ℂ) : μ.cexpect (fun p => F (u p)) = (k : ℂ) * ∑ a, F a := by
  unfold FinProb.cexpect
  rw [← Finset.sum_fiberwise univ u (fun p => (μ.prob p : ℂ) * F (u p)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ p ∈ univ.filter (fun p => u p = a), (μ.prob p : ℂ) * F (u p) =
      (μ.prob p : ℂ) * F a := by
    intro p hp
    rw [(Finset.mem_filter.1 hp).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Complex.ofReal_sum, hu a]

private theorem s7b_pair_zero (μ : FinProb (X × Y × Z)) (u v w : X × Y × Z → H)
    (hu : ∀ a b c : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => (u p, v p, w p) = (a, b, c)),
        μ.prob p = if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (F G : H → ℂ) (hF : ∑ a, F a = 0) : μ.cexpect (fun p => F (u p) * G (v p)) = 0 := by
  have hpair : ∀ q : H × H, ∑ p ∈ univ.filter (fun p : X × Y × Z => (u p, v p) = q), μ.prob p =
      1 / (Fintype.card H : ℝ) ^ 2 := by
    rintro ⟨a, b⟩
    rw [← Finset.sum_fiberwise (s := univ.filter (fun p : X × Y × Z => (u p, v p) = (a, b)))
      (g := w) (f := μ.prob)]
    have : ∀ c : H, ∑ p ∈ (univ.filter (fun p : X × Y × Z => (u p, v p) = (a, b))).filter
        (fun p => w p = c), μ.prob p = if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0 := by
      intro c
      rw [← hu a b c]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      tauto
    simp only [this]
    have h2 : ∀ c : H, (a + b + c = 0) ↔ (c = -(a + b)) := fun c =>
      ⟨fun e => eq_neg_of_add_eq_zero_right e, fun e => by rw [e]; simp⟩
    simp_rw [h2]
    simp
  have := s7b_fiber_exp μ (fun p => (u p, v p)) hpair (fun q => F q.1 * G q.2)
  simp only at this
  rw [this, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hF, zero_mul, mul_zero]

private theorem s7b_mean_zero {α : Type} [Fintype α] [DecidableEq α] (μ : FinProb (X × Y × Z))
    (m : X × Y × Z → α) (u : α → H) (F : H → ℂ)
    (hm : ∀ h : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => u (m p) = h), μ.prob p =
        1 / (Fintype.card H : ℝ))
    (h0 : (mergePush μ m).cexpect (fun a => F (u a)) = 0) : ∑ a, F a = 0 := by
  have h1 : (mergePush μ m).cexpect (fun a => F (u a)) = μ.cexpect (fun p => F (u (m p))) :=
    (s7b_push1 μ m (fun a => F (u a))).symm
  rw [h1, s7b_fiber_exp μ (fun p => u (m p)) hm F] at h0
  have hc : ((1 / (Fintype.card H : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have := s7b_card_pos (H := H)
    exact_mod_cast (by positivity : (1 / (Fintype.card H : ℝ)) ≠ 0)
  exact (mul_eq_zero.1 h0).resolve_left hc

/-! ### Paper IV `claim:ortho-of-embed-nonembed` (Claim 8.?, l. 4577-4592), three items -/

/-- item 1: `f ∈ Embed_σ`, `g ∈ Embed_γ^⊥` (in `L²(μ_y)`), `h` arbitrary give `𝔼 f g h = 0`.
Hypotheses: 4 (the law of `(σ x, γ y, φ z)` is uniform on `a + b + c = 0`, as in the built
`embedchar_uniform_triple_marginal_x`) and 5 (`μ_{y,z}` uniform, in the form `y ⟂ z`). -/
theorem s7_ortho_embed_nonembed_1 (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (f : X → ℂ) (hf : f ∈ embedSpan σ) (g : Y → ℂ) (hg : g ∈ s7Perp (lawY μ) (embedSpan γ))
    (h : Z → ℂ) : μ.cexpect (fun p => f p.1 * g p.2.1 * h p.2.2) = 0 := by
  refine s7b_embed_lin μ σ g h (fun χ => ?_) f hf
  rw [s7b_split μ σ γ φ hunif hind, s7b_cexpect_perp (lawY μ) g χ γ hg, zero_mul]

/-- item 2: `f ∈ Embed_σ`, `h ∈ Embed_φ^⊥`, `g` arbitrary. -/
theorem s7_ortho_embed_nonembed_2 (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (f : X → ℂ) (hf : f ∈ embedSpan σ) (g : Y → ℂ) (h : Z → ℂ)
    (hh : h ∈ s7Perp (lawZ μ) (embedSpan φ)) :
    μ.cexpect (fun p => f p.1 * g p.2.1 * h p.2.2) = 0 := by
  refine s7b_embed_lin μ σ g h (fun χ => ?_) f hf
  rw [s7b_split μ σ γ φ hunif hind, s7b_cexpect_perp (lawZ μ) h χ φ hh, mul_zero]

/-- item 3: mean-zero embedding functions in two different variables are uncorrelated. -/
theorem s7_ortho_embed_nonembed_3 (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (f : X → ℂ) (hf : f ∈ embedSpan σ) (hf0 : (lawX μ).cexpect f = 0)
    (g : Y → ℂ) (hg : g ∈ embedSpan γ) (hg0 : (lawY μ).cexpect g = 0)
    (h : Z → ℂ) (hh : h ∈ embedSpan φ) (hh0 : (lawZ μ).cexpect h = 0) :
    μ.cexpect (fun p => f p.1 * g p.2.1) = 0 ∧ μ.cexpect (fun p => f p.1 * h p.2.2) = 0 ∧
      μ.cexpect (fun p => g p.2.1 * h p.2.2) = 0 := by
  obtain ⟨h1, h2, h3⟩ := s7b_unif_marg μ σ γ φ hunif
  obtain ⟨F, rfl⟩ := (embedSpan_eq_fibreConstant σ f).1 hf
  obtain ⟨G, rfl⟩ := (embedSpan_eq_fibreConstant γ g).1 hg
  obtain ⟨K, rfl⟩ := (embedSpan_eq_fibreConstant φ h).1 hh
  have hF : ∑ a, F a = 0 :=
    s7b_mean_zero μ (fun p => p.1) σ F (fun h => h1 h) hf0
  have hG : ∑ a, G a = 0 :=
    s7b_mean_zero μ (fun p => p.2.1) γ G (fun h => h2 h) hg0
  have hK : ∑ a, K a = 0 :=
    s7b_mean_zero μ (fun p => p.2.2) φ K (fun h => h3 h) hh0
  have hu1 : ∀ a b c : H, ∑ p ∈ univ.filter (fun p : X × Y × Z =>
      (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0 := hunif
  have hu2 : ∀ a b c : H, ∑ p ∈ univ.filter (fun p : X × Y × Z =>
      (σ p.1, φ p.2.2, γ p.2.1) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0 := by
    intro a b c
    rw [show a + b + c = a + c + b from add_right_comm a b c, ← hunif a c b]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    tauto
  have hu3 : ∀ a b c : H, ∑ p ∈ univ.filter (fun p : X × Y × Z =>
      (γ p.2.1, φ p.2.2, σ p.1) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0 := by
    intro a b c
    rw [show a + b + c = c + a + b by abel, ← hunif c a b]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    tauto
  exact ⟨s7b_pair_zero μ (fun p => σ p.1) (fun p => γ p.2.1) (fun p => φ p.2.2) hu1 F G hF,
    s7b_pair_zero μ (fun p => σ p.1) (fun p => φ p.2.2) (fun p => γ p.2.1) hu2 F K hF,
    s7b_pair_zero μ (fun p => γ p.2.1) (fun p => φ p.2.2) (fun p => σ p.1) hu3 G K hG⟩


private theorem s7b_push_fiber {α : Type} [Fintype α] [DecidableEq α] (μ : FinProb (X × Y × Z))
    (f : X × Y × Z → α) (σ : α → H) (h : H) :
    ∑ a ∈ univ.filter (fun a => σ a = h), (mergePush μ f).prob a =
      ∑ p ∈ univ.filter (fun p => σ (f p) = h), μ.prob p := by
  show ∑ a ∈ univ.filter (fun a => σ a = h), ∑ p ∈ univ.filter (fun p => f p = a), μ.prob p = _
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun p => σ (f p) = h))
    (t := univ.filter (fun a => σ a = h)) (g := f) (f := μ.prob)
    (fun p hp => by simpa using hp)]
  refine Finset.sum_congr rfl fun a ha => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  have ha' : σ a = h := (Finset.mem_filter.1 ha).2
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hp => ⟨hp ▸ ha', hp⟩, fun hp => hp.2⟩

/-- the three bases of Def. 7.1 (`x`) and Section 4 (`y`, `z`: the `Sm = ∅` instances) exist under
hypothesis 4 of the relaxed theorem (`σ_*μ_x`, `γ_*μ_y`, `φ_*μ_z` uniform: the built
`embedchar_uniform_triple_marginal_x` and its `y`, `z` analogues) and full support of the marginals
(every symbol occurs, atoms `≥ α`). -/
theorem s7_exists_modestBasis_triple (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H)
    (φ : Z → H) (Sm : Finset X)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a) :
    Nonempty (S7ModestBasis (lawX μ) σ Sm) ∧ Nonempty (S7ModestBasis (lawY μ) γ (∅ : Finset Y)) ∧
      Nonempty (S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) := by
  obtain ⟨h1, h2, h3⟩ := s7b_unif_marg μ σ γ φ hunif
  refine ⟨s7_exists_modestBasis _ σ Sm hDx fun h => ?_, s7_exists_modestBasis _ γ ∅ hDy
    fun h => ?_, s7_exists_modestBasis _ φ ∅ hDz fun h => ?_⟩
  · exact (s7b_push_fiber μ (fun p => p.1) σ h).trans (h1 h)
  · exact (s7b_push_fiber μ (fun p => p.2.1) γ h).trans (h2 h)
  · exact (s7b_push_fiber μ (fun p => p.2.2) φ h).trans (h3 h)

end S7Beta

section Dimensionality

/-- Paper IV `fact:dimensionality` (Fact 9.16, l. 5783-5786), with `i ≠ j` (the printed "there are `i, j`"
is read `i ≠ j`, as the proof gives, l. 5805): `ℓ` unit vectors in `ℂ^k`, `k ≤ ℓ - 1`, contain
two with `|⟨uᵢ, uⱼ⟩| ≥ 1/(kℓ)`. -/
theorem s7_dimensionality {k ℓ : ℕ} (hkℓ : k + 1 ≤ ℓ) (u : Fin ℓ → EuclideanSpace ℂ (Fin k))
    (hu : ∀ i, ‖u i‖ = 1) :
    ∃ i j : Fin ℓ, i ≠ j ∧ 1 / ((k : ℝ) * ℓ) ≤ ‖inner ℂ (u i) (u j)‖ := by
  by_contra hcon
  push_neg at hcon
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      have h1 := hu ⟨0, by omega⟩
      rw [Subsingleton.elim (u ⟨0, by omega⟩) 0] at h1
      simp at h1
    · exact h
  set x : Fin ℓ → Fin k → ℂ := fun i a => u i a with hx
  set T : Fin k → Fin k → ℂ := fun a b => ∑ i, (starRingEnd ℂ) (x i a) * x i b with hT
  have hc : ∀ i j, inner ℂ (u i) (u j) = ∑ a, (starRingEnd ℂ) (x i a) * x j a := by
    intro i j
    simp [hx, PiLp.inner_apply, mul_comm]
  have hz : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    intro z
    rw [← Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcomm : ∀ f : Fin ℓ → Fin ℓ → Fin k → Fin k → ℂ,
      ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
    intro f
    calc _ = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hS : ∑ i, ∑ j, ‖inner ℂ (u i) (u j)‖ ^ 2 = ∑ a, ∑ b, ‖T a b‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simp only [hz, hc, hT, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
    rw [hcomm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  set r : Fin k → ℝ := fun a => ∑ i, ‖x i a‖ ^ 2 with hr
  have hTaa : ∀ a, ‖T a a‖ = r a := by
    intro a
    have : T a a = ((r a : ℝ) : ℂ) := by
      simp only [hT, hr]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz (x i a)]
      ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hsr : ∑ a, r a = ℓ := by
    simp only [hr]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1 := by
      intro i
      have h1 := hu i
      have h2 : ‖u i‖ ^ 2 = ∑ a, ‖u i a‖ ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
      rw [h1] at h2
      simpa [hx] using h2.symm
    simp [this]
  have hcs : (ℓ : ℝ) ^ 2 ≤ k * ∑ a, ∑ b, ‖T a b‖ ^ 2 := by
    have h1 : (∑ a, r a) ^ 2 ≤ (Finset.univ : Finset (Fin k)).card * ∑ a, r a ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [hsr, Finset.card_univ, Fintype.card_fin] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← hTaa a]
    exact Finset.single_le_sum (f := fun b => ‖T a b‖ ^ 2) (fun b _ => sq_nonneg _)
      (Finset.mem_univ a)
  set q : ℝ := 1 / ((k : ℝ) * ℓ) with hq
  have hKpos : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hLK : (k : ℝ) + 1 ≤ ℓ := by exact_mod_cast hkℓ
  have hrow : ∀ i, ∑ j, ‖inner ℂ (u i) (u j)‖ ^ 2 ≤ 1 + ((ℓ : ℝ) - 1) * q ^ 2 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hii : ‖inner ℂ (u i) (u i)‖ ^ 2 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hu i]
      simp
    rw [hii]
    refine add_le_add le_rfl ?_
    have : ∀ j ∈ Finset.univ.erase i, ‖inner ℂ (u i) (u j)‖ ^ 2 ≤ q ^ 2 := by
      intro j hj
      have hne : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
      have := hcon i j hne
      exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub (by omega)]
    simp
  have hSle : ∑ a, ∑ b, ‖T a b‖ ^ 2 ≤ ℓ * (1 + ((ℓ : ℝ) - 1) * q ^ 2) := by
    rw [← hS]
    refine (Finset.sum_le_sum fun i _ => hrow i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hqk : (k : ℝ) * (((ℓ : ℝ) - 1) * q ^ 2) < 1 := by
    have hL : (1 : ℝ) ≤ ℓ := by linarith
    have hk0 : (0 : ℝ) < k := by linarith
    have hl0 : (0 : ℝ) < ℓ := by linarith
    have e : (k : ℝ) * (((ℓ : ℝ) - 1) * q ^ 2) = ((ℓ : ℝ) - 1) / (k * (ℓ : ℝ) ^ 2) := by
      rw [hq]
      field_simp
    rw [e, div_lt_one (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hKpos) (sq_nonneg (ℓ : ℝ)), sq_nonneg ((ℓ : ℝ) - 1 / 2)]
  have hfin : (ℓ : ℝ) ^ 2 ≤ k * (ℓ * (1 + ((ℓ : ℝ) - 1) * q ^ 2)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hSle (by linarith))
  have hLpos : (0 : ℝ) < ℓ := by linarith
  have h5 : (ℓ : ℝ) ≤ k * (1 + ((ℓ : ℝ) - 1) * q ^ 2) := by
    refine le_of_mul_le_mul_left ?_ hLpos
    nlinarith [hfin]
  nlinarith [h5, hqk]

end Dimensionality

end TrackB
end RestrictedPolynomials
end
