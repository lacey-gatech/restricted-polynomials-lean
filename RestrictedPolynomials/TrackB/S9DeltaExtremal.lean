module

public import RestrictedPolynomials.TrackB.S9DeltaSetup

/-!
# Track B: the extremal triple of Lemma 9.3

Source: paper IV (arXiv:2307.16248v2 `writeup_stability.tex`), Lemma 9.3, l. 5352-5356
(paper IV `lem:delta-inductive#extremal-triple`). Kept apart from `S9DeltaSetup`; not consumed by
the main proof, which bounds every unit triple.

Proof: under `S7YZImpliesX μ.support` the laws `μ_{y,z}`, `μ_y`, `μ_z` have full support, so the
weighted `L²` norms are norms. The unit sphere of the subspace `F_{n,d'}` and the unit spheres of
`L²(μ_y^{⊗n})`, `L²(μ_z^{⊗n})` are compact, the correlation is continuous, so its modulus attains its
maximum `M`; trilinearity gives `δ_{n,d'} = M`, and a phase rotation of `F` (`s7_classFn_smul`) makes
the correlation equal to `M`.
-/

@[expose] public section

open Finset
open scoped ENNReal

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S9dExtremalAux

/-! ### Private helpers -/

/-- the `L²` norm is continuous. -/
private lemma s9d_continuous_cl2norm {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (π : FinProb α) : Continuous fun f : (ι → α) → ℂ => cl2norm π f := by
  unfold cl2norm cl2sq FinProb.expect
  fun_prop

/-- `‖a f‖₂ = |a| ‖f‖₂`. -/
private lemma s9d_cl2norm_smul {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (π : FinProb α) (a : ℂ) (f : (ι → α) → ℂ) : cl2norm π (a • f) = ‖a‖ * cl2norm π f := by
  have h : cl2sq π (a • f) = ‖a‖ ^ 2 * cl2sq π f := by
    unfold cl2sq FinProb.expect
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  unfold cl2norm
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- the unit sphere of a closed set of functions is compact for a law of full support. -/
private lemma s9d_isCompact_unit {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (π : FinProb α) (hπ : ∀ a, 0 < π.prob a) (S : Set ((ι → α) → ℂ)) (hS : IsClosed S) :
    IsCompact {f | f ∈ S ∧ cl2norm π f = 1} := by
  have hP : ∀ x : ι → α, 0 < (π.pi ι).prob x := fun x =>
    Finset.prod_pos fun i _ => hπ (x i)
  set R : ℝ := 1 + ∑ x : ι → α, ((π.pi ι).prob x)⁻¹ with hR
  have hR0 : 0 ≤ R := by
    have : 0 ≤ ∑ x : ι → α, ((π.pi ι).prob x)⁻¹ :=
      Finset.sum_nonneg fun x _ => inv_nonneg.2 (hP x).le
    linarith
  refine (isCompact_closedBall (0 : (ι → α) → ℂ) R).of_isClosed_subset
    (hS.inter (isClosed_eq (s9d_continuous_cl2norm π) continuous_const)) ?_
  rintro f ⟨-, hf⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR0]
  intro x
  have h1 : cl2sq π f = 1 := Real.sqrt_eq_one.1 hf
  have h2 : (π.pi ι).prob x * ‖f x‖ ^ 2 ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun y => (π.pi ι).prob y * ‖f y‖ ^ 2)
      (fun y _ => mul_nonneg ((π.pi ι).nonneg y) (sq_nonneg _)) (Finset.mem_univ x)
  have h3 : ‖f x‖ ^ 2 ≤ ((π.pi ι).prob x)⁻¹ := by
    calc ‖f x‖ ^ 2 = ((π.pi ι).prob x * ‖f x‖ ^ 2) * ((π.pi ι).prob x)⁻¹ := by
          field_simp [(hP x).ne']
      _ ≤ 1 * ((π.pi ι).prob x)⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 (hP x).le)
      _ = ((π.pi ι).prob x)⁻¹ := one_mul _
  have h4 : ((π.pi ι).prob x)⁻¹ ≤ ∑ y : ι → α, ((π.pi ι).prob y)⁻¹ :=
    Finset.single_le_sum (f := fun y => ((π.pi ι).prob y)⁻¹)
      (fun y _ => inv_nonneg.2 (hP y).le) (Finset.mem_univ x)
  have h5 : ‖f x‖ ≤ 1 + ‖f x‖ ^ 2 := by nlinarith [norm_nonneg (f x)]
  linarith

/-- the constant function `1` is a unit vector. -/
private lemma s9d_cl2norm_one {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (π : FinProb α) : cl2norm π (fun _ : ι → α => (1 : ℂ)) = 1 := by
  unfold cl2norm cl2sq FinProb.expect
  simp [(π.pi ι).sum_eq_one]

/-- normalisation of a function of nonzero norm. -/
private lemma s9d_cl2norm_normalize {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (π : FinProb α) (f : (ι → α) → ℂ) (hf : cl2norm π f ≠ 0) :
    cl2norm π ((((cl2norm π f)⁻¹ : ℝ) : ℂ) • f) = 1 := by
  have h0 : 0 < cl2norm π f := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hf)
  rw [s9d_cl2norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 h0.le),
    inv_mul_cancel₀ hf]

/-- the image law has full support where the original law charges a point. -/
private lemma s9d_push_pos {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) (a : α) (ha : 0 < π.prob a) : 0 < (mergePush π f).prob (f a) := by
  refine lt_of_lt_of_le ha ?_
  exact Finset.single_le_sum (f := π.prob) (fun _ _ => π.nonneg _)
    (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩)

end S9dExtremalAux

section S9dExtremalCorr
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- scaling of the correlation in each slot. -/
private lemma s9d_corrF_smul {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (a b c : ℂ) (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    s7CorrF μ (a • F) (b • g) (c • h) = a * b * c * s7CorrF μ F g h := by
  unfold s7CorrF FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- the correlation is continuous in the triple. -/
private lemma s9d_continuous_corrF {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z)) :
    Continuous fun p : ((ι → Y × Z) → ℂ) × ((ι → Y) → ℂ) × ((ι → Z) → ℂ) =>
      ‖s7CorrF μ p.1 p.2.1 p.2.2‖ := by
  unfold s7CorrF FinProb.cexpect
  fun_prop

end S9dExtremalCorr

section S9dExtremal
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- Paper IV `lem:delta-inductive#extremal-triple` (l. 5352-5356), with three points the source leaves
implicit: the supremum is attained (compactness of the unit spheres of the subspace `F_{n,d'}` and of
`g, h`), the phase is normalised (`𝔼 F g h = δ_{n,d'} ≥ 0`), and `F_{n,d'} ≠ {0}` is the hypothesis
`hne`. Not consumed by the main proof, which bounds EVERY unit triple (`s9d_triple_bound`). -/
theorem s9d_extremal_triple (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    {K₁ K₂ : Type} (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (n d' : ℕ) (hne : ∃ F, F ∈ s7ClassFn μ hμ ux n d' ∧ cl2norm (s7LawYZ μ) F ≠ 0) :
    ∃ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
      F ∈ s7ClassFn μ hμ ux n d' ∧ cl2norm (s7LawYZ μ) F = 1 ∧ cl2norm (lawY μ) g = 1 ∧
      cl2norm (lawZ μ) h = 1 ∧
      s7CorrF μ F g h = (((s7DeltaParam μ hμ ux n d').toReal : ℝ) : ℂ) := by
  classical
  have _ := hind
  -- the three laws have full support
  obtain ⟨p0⟩ : Nonempty (X × Y × Z) := by
    by_contra h0
    rw [not_nonempty_iff] at h0
    have h1 := μ.sum_eq_one
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have hat : ∀ (y : Y) (z : Z), 0 < μ.prob (s7Pre hμ y z, y, z) := fun y z =>
    lt_of_le_of_ne (μ.nonneg _) (Ne.symm (s7Pre_mem hμ y z))
  have hYZ : ∀ v, 0 < (s7LawYZ μ).prob v := fun v =>
    s9d_push_pos μ (fun p : X × Y × Z => (p.2.1, p.2.2)) _ (hat v.1 v.2)
  have hY : ∀ y, 0 < (lawY μ).prob y := fun y =>
    s9d_push_pos μ (fun p : X × Y × Z => p.2.1) _ (hat y p0.2.2)
  have hZ : ∀ z, 0 < (lawZ μ).prob z := fun z =>
    s9d_push_pos μ (fun p : X × Y × Z => p.2.2) _ (hat p0.2.1 z)
  -- `F_{n,d'}` is a subspace, hence closed
  let V : Submodule ℂ ((Fin n → Y × Z) → ℂ) :=
    { carrier := s7ClassFn μ hμ ux n d'
      add_mem' := fun ha hb => s7_classFn_add μ hμ ux n d' ha hb
      zero_mem' := s7_zero_mem_classFn μ hμ ux n d'
      smul_mem' := fun c _ hx => s7_classFn_smul μ hμ ux n d' c hx }
  have hVc : IsClosed (s7ClassFn μ hμ ux n d') := V.closed_of_finiteDimensional
  -- compactness of the product of the three unit spheres
  have cF := s9d_isCompact_unit (s7LawYZ μ) hYZ _ hVc
  have cg := s9d_isCompact_unit (ι := Fin n) (lawY μ) hY Set.univ isClosed_univ
  have ch := s9d_isCompact_unit (ι := Fin n) (lawZ μ) hZ Set.univ isClosed_univ
  have hK := cF.prod (cg.prod ch)
  obtain ⟨F₁, hF₁, nF₁⟩ := hne
  have hKne : ({f | f ∈ s7ClassFn μ hμ ux n d' ∧ cl2norm (s7LawYZ μ) f = 1} ×ˢ
      ({f | f ∈ Set.univ ∧ cl2norm (lawY μ) f = 1} ×ˢ
        {f | f ∈ Set.univ ∧ cl2norm (lawZ μ) f = 1})).Nonempty :=
    ⟨((((cl2norm (s7LawYZ μ) F₁)⁻¹ : ℝ) : ℂ) • F₁, fun _ => 1, fun _ => 1),
      ⟨s7_classFn_smul μ hμ ux n d' _ hF₁, s9d_cl2norm_normalize _ F₁ nF₁⟩,
      ⟨trivial, s9d_cl2norm_one (ι := Fin n) _⟩, ⟨trivial, s9d_cl2norm_one (ι := Fin n) _⟩⟩
  obtain ⟨⟨F0, g0, h0⟩, ⟨⟨hF0, nF0⟩, ⟨-, ng0⟩, ⟨-, nh0⟩⟩, hmax⟩ :=
    hK.exists_isMaxOn hKne (s9d_continuous_corrF μ).continuousOn
  obtain ⟨M, hM⟩ : ∃ M, M = ‖s7CorrF μ F0 g0 h0‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ norm_nonneg _
  -- the supremum is the maximum
  have hδ : s7DeltaParam μ hμ ux n d' = ENNReal.ofReal M := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro r ⟨F, g, h, hF, nF, ng, nh, rfl⟩
      refine ENNReal.ofReal_le_ofReal ?_
      have pF : 0 < cl2norm (s7LawYZ μ) F := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm nF)
      have pg : 0 < cl2norm (lawY μ) g := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ng)
      have ph : 0 < cl2norm (lawZ μ) h := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm nh)
      have hle := isMaxOn_iff.1 hmax
        ((((cl2norm (s7LawYZ μ) F)⁻¹ : ℝ) : ℂ) • F, (((cl2norm (lawY μ) g)⁻¹ : ℝ) : ℂ) • g,
          (((cl2norm (lawZ μ) h)⁻¹ : ℝ) : ℂ) • h)
        ⟨⟨s7_classFn_smul μ hμ ux n d' _ hF, s9d_cl2norm_normalize _ F nF⟩,
          ⟨trivial, s9d_cl2norm_normalize _ g ng⟩, ⟨trivial, s9d_cl2norm_normalize _ h nh⟩⟩
      simp only at hle
      rw [s9d_corrF_smul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 pF.le),
        Real.norm_of_nonneg (inv_nonneg.2 pg.le), Real.norm_of_nonneg (inv_nonneg.2 ph.le),
        ← hM] at hle
      calc ‖s7CorrF μ F g h‖ / (cl2norm (s7LawYZ μ) F * cl2norm (lawY μ) g * cl2norm (lawZ μ) h)
          = (cl2norm (s7LawYZ μ) F)⁻¹ * (cl2norm (lawY μ) g)⁻¹ * (cl2norm (lawZ μ) h)⁻¹ *
              ‖s7CorrF μ F g h‖ := by
            rw [div_eq_inv_mul, mul_inv, mul_inv]
        _ ≤ M := hle
    · refine le_sSup ⟨F0, g0, h0, hF0, by rw [nF0]; exact one_ne_zero,
        by rw [ng0]; exact one_ne_zero, by rw [nh0]; exact one_ne_zero, ?_⟩
      rw [nF0, ng0, nh0, hM, mul_one, mul_one, div_one]
  -- the phase rotation
  obtain ⟨z, hz⟩ : ∃ z, z = s7CorrF μ F0 g0 h0 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = if z = 0 then 1 else star z / (‖z‖ : ℂ) := ⟨_, rfl⟩
  have hu1 : ‖u‖ = 1 := by
    by_cases h0 : z = 0
    · simp [hu, h0]
    · rw [hu]
      simp only [h0, ↓reduceIte]
      rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      exact div_self (norm_ne_zero_iff.2 h0)
  have huz : u * z = (‖z‖ : ℂ) := by
    by_cases h0 : z = 0
    · simp [hu, h0]
    · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0)
      rw [hu]
      simp only [h0, ↓reduceIte]
      rw [div_mul_eq_mul_div, Complex.star_def, Complex.conj_mul', pow_two,
        mul_div_assoc, div_self hn, mul_one]
  refine ⟨u • F0, g0, h0, s7_classFn_smul μ hμ ux n d' u hF0, ?_, ng0, nh0, ?_⟩
  · rw [s9d_cl2norm_smul, hu1, nF0, one_mul]
  · have h1 : s7CorrF μ (u • F0) g0 h0 = u * s7CorrF μ F0 g0 h0 := by
      have := s9d_corrF_smul μ u 1 1 F0 g0 h0
      simpa using this
    rw [h1, ← hz, huz, hδ, ENNReal.toReal_ofReal hM0, hM, hz]

end S9dExtremal

end TrackB
end RestrictedPolynomials
end
