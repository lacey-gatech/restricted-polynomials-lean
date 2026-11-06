module

public import RestrictedPolynomials.TrackB.S9DeltaSphere

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate Matrix

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### private integration infrastructure -/

private lemma s9dF_sphere_compact (ι : Type) [Fintype ι] :
    IsCompact {w : ι → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} := by
  have hc : IsClosed {w : ι → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hc ?_
  refine (Metric.isBounded_closedBall (x := (0 : ι → ℂ)) (r := 1)).subset ?_
  intro w hw
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : ‖w i‖ ^ 2 ≤ 1 := by
    have : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
    have hw' : ∑ j, ‖w j‖ ^ 2 = 1 := hw
    rw [hw'] at this
    exact this
  nlinarith [norm_nonneg (w i)]

private lemma s9dF_int_sphere (ι : Type) [Fintype ι] [Nonempty ι] {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℂ) → E} (hf : Continuous f) : Integrable f (s9dSphere ι) := by
  have := s9dSphere_isProb ι
  obtain ⟨C, hC⟩ := (s9dF_sphere_compact ι).exists_bound_of_continuousOn hf.continuousOn
  have hae : ∀ᵐ w ∂(s9dSphere ι), w ∈ {w : ι → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} :=
    MeasureTheory.ae_iff.2 (s9dSphere_ae_sphere ι)
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (hae.mono fun w hw => hC w hw)

private lemma s9dF_int_pair (ιR ιS : Type) [Fintype ιR] [Fintype ιS] [Nonempty ιR] [Nonempty ιS]
    {E : Type*} [NormedAddCommGroup E]
    {f : (ιR → ℂ) × (ιS → ℂ) → E} (hf : Continuous f) :
    Integrable f ((s9dSphere ιR).prod (s9dSphere ιS)) := by
  have := s9dSphere_isProb ιR
  have := s9dSphere_isProb ιS
  obtain ⟨C, hC⟩ := ((s9dF_sphere_compact ιR).prod (s9dF_sphere_compact ιS)).exists_bound_of_continuousOn
    hf.continuousOn
  have h1 : ∀ᵐ w ∂(s9dSphere ιR), w ∈ {w : ιR → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} :=
    MeasureTheory.ae_iff.2 (s9dSphere_ae_sphere ιR)
  have h2 : ∀ᵐ w ∂(s9dSphere ιS), w ∈ {w : ιS → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} :=
    MeasureTheory.ae_iff.2 (s9dSphere_ae_sphere ιS)
  have hae : ∀ᵐ z ∂((s9dSphere ιR).prod (s9dSphere ιS)), z ∈
      ({w : ιR → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} ×ˢ {w : ιS → ℂ | ∑ i, ‖w i‖ ^ 2 = 1}) := by
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := s9dSphere ιR) (ν := s9dSphere ιS)).ae h1
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := s9dSphere ιR) (ν := s9dSphere ιS)).ae h2
    exact (a1.and a2).mono fun z hz => Set.mk_mem_prod hz.1 hz.2
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (hae.mono fun w hw => hC w hw)

private instance s9dF_inst_prob (ι : Type) [Fintype ι] [Nonempty ι] :
    IsProbabilityMeasure (s9dSphere ι) := s9dSphere_isProb ι

private lemma s9dF_sum1 {Ω κ : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] {P : Measure Ω}
    (hP : ∀ f : Ω → ℂ, Continuous f → Integrable f P) (s : Finset κ) (F : κ → Ω → ℂ)
    (hF : ∀ k, Continuous (fun x => F k x)) :
    ∫ x, ∑ k ∈ s, F k x ∂P = ∑ k ∈ s, ∫ x, F k x ∂P :=
  integral_finsetSum s (fun k _ => hP _ (hF k))

private lemma s9dF_prod_single (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (r : ι) :
    ∏ i, x i ^ (Pi.single r (1 : ℕ) i) = x r := by
  simp [Pi.single_apply]

section
variable (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- off-diagonal monomial -/
private lemma s9dF_mono4 (r r' u u' : ι) (h1 : r ≠ r') (h2 : u ≠ u') :
    ∫ w, (w r * starRingEnd ℂ (w r') * (starRingEnd ℂ (w u) * w u')) ∂(s9dSphere ι) =
      ((if r = u ∧ r' = u' then 1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) else 0 : ℝ) : ℂ) := by
  by_cases h : r = u ∧ r' = u'
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true]
    have : ∀ w : ι → ℂ, w r * starRingEnd ℂ (w r') * (starRingEnd ℂ (w r) * w r') =
        ((‖w r‖ ^ 2 * ‖w r'‖ ^ 2 : ℝ) : ℂ) := by
      intro w
      push_cast
      rw [show w r * starRingEnd ℂ (w r') * (starRingEnd ℂ (w r) * w r') =
        (w r * starRingEnd ℂ (w r)) * (w r' * starRingEnd ℂ (w r')) by ring,
        Complex.mul_conj', Complex.mul_conj']
    simp_rw [this]
    rw [integral_complex_ofReal, s9dSphere_moment4_offdiag ι r r' h1]
  · simp only [h, ite_false, Complex.ofReal_zero]
    have key := s9dSphere_phase_vanish ι (Pi.single r 1 + Pi.single u' 1)
      (Pi.single r' 1 + Pi.single u 1) ?_
    · rw [← key]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, s9dF_prod_single]
      ring
    · intro hab
      apply h
      have e1 := congrFun hab r
      have e2 := congrFun hab u'
      simp only [Pi.add_apply, Pi.single_apply] at e1 e2
      clear hab h
      by_cases a1 : r = u
      · subst a1
        refine ⟨rfl, ?_⟩
        by_cases a2 : u' = r'
        · exact a2.symm
        · exfalso
          simp [a2, Ne.symm h2] at e2
      · exfalso
        by_cases a2 : r = u'
        · subst a2
          simp [a1, h1, Ne.symm h1, Ne.symm h2] at e1
        · simp [a1, a2, h1] at e1

private lemma s9dF_int_zero0 (u u' : ι) (h : u ≠ u') :
    ∫ w, (w u * starRingEnd ℂ (w u')) ∂(s9dSphere ι) = 0 := by
  have key := s9dSphere_phase_vanish ι (Pi.single u 1) (Pi.single u' 1) ?_
  · rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Finset.prod_mul_distrib, s9dF_prod_single]
  · intro hab
    have := congrFun hab u
    simp [Pi.single_apply, h] at this

private lemma s9dF_int_zero1 (r u u' : ι) (h : u ≠ u') :
    ∫ w, (((‖w r‖ ^ 2 : ℝ) : ℂ) * (w u * starRingEnd ℂ (w u'))) ∂(s9dSphere ι) = 0 := by
  have key := s9dSphere_phase_vanish ι (Pi.single r 1 + Pi.single u 1)
    (Pi.single r 1 + Pi.single u' 1) ?_
  · rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, s9dF_prod_single]
    push_cast
    rw [show w r * w u * (starRingEnd ℂ (w r) * starRingEnd ℂ (w u')) =
        (w r * starRingEnd ℂ (w r)) * (w u * starRingEnd ℂ (w u')) by ring, Complex.mul_conj']
  · intro hab
    have := congrFun hab u
    by_cases hr : r = u
    · subst hr
      simp [Pi.single_apply, h] at this
    · simp [Pi.single_apply, h, hr, Ne.symm hr] at this

end

section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] {P : Measure Ω}

private lemma s9dF_sum2 (hP : ∀ f : Ω → ℂ, Continuous f → Integrable f P)
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (t : κ₁ → Finset κ₂) (F : κ₁ → κ₂ → Ω → ℂ)
    (hF : ∀ a b, Continuous (F a b)) :
    ∫ x, ∑ a ∈ s, ∑ b ∈ t a, F a b x ∂P = ∑ a ∈ s, ∑ b ∈ t a, ∫ x, F a b x ∂P := by
  rw [s9dF_sum1 hP s (fun a x => ∑ b ∈ t a, F a b x)
    (fun a => continuous_finsetSum _ (fun b _ => hF a b))]
  exact Finset.sum_congr rfl fun a _ => s9dF_sum1 hP (t a) (F a) (hF a)

private lemma s9dF_sum4 (hP : ∀ f : Ω → ℂ, Continuous f → Integrable f P)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (F : κ → κ → κ → κ → Ω → ℂ)
    (hF : ∀ a b c d, Continuous (F a b c d)) :
    ∫ x, ∑ a, ∑ b ∈ univ.erase a, ∑ c, ∑ d ∈ univ.erase c, F a b c d x ∂P =
      ∑ a, ∑ b ∈ univ.erase a, ∑ c, ∑ d ∈ univ.erase c, ∫ x, F a b c d x ∂P := by
  rw [s9dF_sum1 hP _ (fun a x => ∑ b ∈ univ.erase a, ∑ c, ∑ d ∈ univ.erase c, F a b c d x)
    (fun a => continuous_finsetSum _ (fun b _ => continuous_finsetSum _ (fun c _ =>
      continuous_finsetSum _ (fun d _ => hF a b c d))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s9dF_sum1 hP _ (fun b x => ∑ c, ∑ d ∈ univ.erase c, F a b c d x)
    (fun b => continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun d _ => hF a b c d)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact s9dF_sum2 hP univ (fun c => univ.erase c) (F a b) (hF a b)

end

section
variable (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]

private def s9dF_off (H : ι → ι → ℂ) (w : ι → ℂ) : ℂ :=
  ∑ r, ∑ r' ∈ univ.erase r, H r r' * (w r * starRingEnd ℂ (w r'))

@[fun_prop]
private lemma s9dF_off_cont (H : ι → ι → ℂ) : Continuous (s9dF_off ι H) := by
  unfold s9dF_off; fun_prop

private lemma s9dF_int_off0 (H : ι → ι → ℂ) : ∫ w, s9dF_off ι H w ∂(s9dSphere ι) = 0 := by
  unfold s9dF_off
  rw [s9dF_sum2 (fun f hf => s9dF_int_sphere ι hf) _ _
    (fun r r' w => H r r' * (w r * starRingEnd ℂ (w r'))) (fun r r' => by fun_prop)]
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun r' hr' => ?_
  rw [integral_const_mul, s9dF_int_zero0 ι r r' (Finset.ne_of_mem_erase hr').symm, mul_zero]

private lemma s9dF_int_off1 (r : ι) (H : ι → ι → ℂ) :
    ∫ w, ((‖w r‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι H w ∂(s9dSphere ι) = 0 := by
  unfold s9dF_off
  simp_rw [Finset.mul_sum]
  rw [s9dF_sum2 (fun f hf => s9dF_int_sphere ι hf) _ _
    (fun a b w => ((‖w r‖ ^ 2 : ℝ) : ℂ) * (H a b * (w a * starRingEnd ℂ (w b))))
    (fun r r' => by fun_prop)]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b hb => ?_
  have : ∀ w : ι → ℂ, ((‖w r‖ ^ 2 : ℝ) : ℂ) * (H a b * (w a * starRingEnd ℂ (w b))) =
      H a b * (((‖w r‖ ^ 2 : ℝ) : ℂ) * (w a * starRingEnd ℂ (w b))) := fun w => by ring
  simp_rw [this]
  rw [integral_const_mul, s9dF_int_zero1 ι r a b (Finset.ne_of_mem_erase hb).symm, mul_zero]

private lemma s9dF_int_C (K : ι → ι → ι → ι → ℂ) :
    ∫ w, ∑ r, ∑ r' ∈ univ.erase r, ∑ u, ∑ u' ∈ univ.erase u,
        K r r' u u' * (w r * starRingEnd ℂ (w r') * (starRingEnd ℂ (w u) * w u')) ∂(s9dSphere ι) =
      ((1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) *
        ∑ r, ∑ r' ∈ univ.erase r, K r r' r r' := by
  set x : ℝ := 1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) with hx
  rw [s9dF_sum4 (fun f hf => s9dF_int_sphere ι hf) _ (fun a b c d => by fun_prop)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r' hr' => ?_
  have hne : r ≠ r' := (Finset.ne_of_mem_erase hr').symm
  have e1 : ∀ u, ∀ u' ∈ univ.erase u, ∫ w, K r r' u u' * (w r * starRingEnd ℂ (w r') *
      (starRingEnd ℂ (w u) * w u')) ∂(s9dSphere ι) =
      if u = r then (if u' = r' then K r r' u u' * (x : ℂ) else 0) else 0 := by
    intro u u' hu'
    rw [integral_const_mul, s9dF_mono4 ι r r' u u' hne (Finset.ne_of_mem_erase hu').symm]
    by_cases a : u = r
    · by_cases b : u' = r'
      · subst a; subst b
        simp only [and_self, if_true]
        ring
      · have hh : ¬(r = u ∧ r' = u') := fun h => b h.2.symm
        have hb' : ¬ r' = u' := fun h => b h.symm
        simp [hh, a, b, hb']
    · have hh : ¬(r = u ∧ r' = u') := fun h => a h.1.symm
      simp [hh, a]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl (e1 u)]
  simp [Finset.sum_ite_eq', hr', mul_comm, Ne.symm hne]

private lemma s9dF_int_offQ (H H' : ι → ι → ℂ) :
    ∫ w, s9dF_off ι H w * starRingEnd ℂ (s9dF_off ι H' w) ∂(s9dSphere ι) =
      ((1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) *
        ∑ r, ∑ r' ∈ univ.erase r, H r r' * starRingEnd ℂ (H' r r') := by
  have hpt : ∀ w : ι → ℂ, s9dF_off ι H w * starRingEnd ℂ (s9dF_off ι H' w) =
      ∑ r, ∑ r' ∈ univ.erase r, ∑ u, ∑ u' ∈ univ.erase u,
        (H r r' * starRingEnd ℂ (H' u u')) *
          (w r * starRingEnd ℂ (w r') * (starRingEnd ℂ (w u) * w u')) := by
    intro w
    unfold s9dF_off
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [hpt]
  exact s9dF_int_C ι (fun r r' u u' => H r r' * starRingEnd ℂ (H' u u'))

private lemma s9dF_int_diag1 (r : ι) :
    ∫ w, ((‖w r‖ ^ 2 : ℝ) : ℂ) ∂(s9dSphere ι) = ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal, s9dSphere_moment2 ι r]

private lemma s9dF_int_diag2 (r u : ι) :
    ∫ w, ((‖w r‖ ^ 2 : ℝ) : ℂ) * ((‖w u‖ ^ 2 : ℝ) : ℂ) ∂(s9dSphere ι) =
      (((if r = u then 2 else 1) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) := by
  have h : ∀ w : ι → ℂ, ((‖w r‖ ^ 2 : ℝ) : ℂ) * ((‖w u‖ ^ 2 : ℝ) : ℂ) =
      ((‖w r‖ ^ 2 * ‖w u‖ ^ 2 : ℝ) : ℂ) := fun w => by push_cast; ring
  simp_rw [h]
  rw [integral_complex_ofReal]
  by_cases hru : r = u
  · subst hru
    have := s9dSphere_moment4_diag ι r
    simp only [ite_true]
    rw [← this]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    ring
  · rw [s9dSphere_moment4_offdiag ι r u hru]
    simp [hru]

end

section
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private lemma s9dF_collapse4 (x : ℝ) (L : ι → ι → ι → ι → ℂ) :
    ∑ r, ∑ r' ∈ univ.erase r, ∑ u, ∑ u' ∈ univ.erase u,
        ((if r = u ∧ r' = u' then x else 0 : ℝ) : ℂ) * L r r' u u' =
      (x : ℂ) * ∑ r, ∑ r' ∈ univ.erase r, L r r' r r' := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r' hr' => ?_
  have e1 : ∀ u, ∀ u' ∈ univ.erase u, ((if r = u ∧ r' = u' then x else 0 : ℝ) : ℂ) * L r r' u u' =
      if u = r then (if u' = r' then (x : ℂ) * L r r' u u' else 0) else 0 := by
    intro u u' _
    by_cases a : u = r
    · by_cases b : u' = r'
      · subst a; subst b
        simp only [and_self, if_true]
      · have hh : ¬(r = u ∧ r' = u') := fun h => b h.2.symm
        have hb' : ¬ r' = u' := fun h => b h.symm
        simp [hh, a, b, hb']
    · have hh : ¬(r = u ∧ r' = u') := fun h => a h.1.symm
      simp [hh, a]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl (e1 u)]
  have hne : r' ≠ r := Finset.ne_of_mem_erase hr'
  simp [Finset.sum_ite_eq', hr', hne]

private lemma s9dF_sq_cast {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f : Ω → ℂ) :
    (((∫ x, ‖f x‖ ^ 2 ∂P : ℝ)) : ℂ) = ∫ x, f x * starRingEnd ℂ (f x) ∂P := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Complex.mul_conj', Complex.ofReal_pow]

private lemma s9dF_alg1 (H : ι → κ → κ → ℂ) :
    ∑ r, ∑ u, ((if r = u then 2 else 1 : ℝ) : ℂ) *
        ∑ s, ∑ s' ∈ univ.erase s, H r s s' * starRingEnd ℂ (H u s s') =
      ((∑ s, ∑ s' ∈ univ.erase s, (‖∑ r, H r s s'‖ ^ 2 + ∑ r, ‖H r s s'‖ ^ 2) : ℝ) : ℂ) := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := fun z => by
    rw [Complex.mul_conj', Complex.ofReal_pow]
  have hA : ∑ r, ∑ u, ∑ s, ∑ s' ∈ univ.erase s, H r s s' * starRingEnd ℂ (H u s s') =
      ∑ s, ∑ s' ∈ univ.erase s, (∑ r, H r s s') * starRingEnd ℂ (∑ r, H r s s') := by
    simp only [map_sum, Finset.sum_mul_sum]
    calc _ = ∑ r, ∑ s, ∑ s' ∈ univ.erase s, ∑ u, H r s s' * starRingEnd ℂ (H u s s') :=
          Finset.sum_congr rfl fun r _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ s, ∑ r, ∑ s' ∈ univ.erase s, ∑ u, H r s s' * starRingEnd ℂ (H u s s') :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun s _ => Finset.sum_comm
  have e : ∀ r u : ι, ((if r = u then 2 else 1 : ℝ) : ℂ) = 1 + (if r = u then 1 else 0) := by
    intro r u; by_cases h : r = u <;> simp [h] <;> norm_num
  simp_rw [e, add_mul, one_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, one_mul]
  rw [hA]
  simp only [Complex.ofReal_sum, Complex.ofReal_add, hn, Finset.sum_add_distrib]
  congr 1
  calc _ = ∑ s, ∑ r, ∑ s' ∈ univ.erase s, H r s s' * starRingEnd ℂ (H r s s') :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun s _ => Finset.sum_comm

end

section
variable (ι κ : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [DecidableEq κ]

private def s9dF_D1 (H : ι → κ → κ → ℂ) (x : (ι → ℂ) × (κ → ℂ)) : ℂ :=
  ∑ r, ((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * s9dF_off κ (H r) x.2

private def s9dF_D2 (H : κ → ι → ι → ℂ) (x : (ι → ℂ) × (κ → ℂ)) : ℂ :=
  ∑ s, ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι (H s) x.1

private def s9dF_D3 (H : ι → ι → κ → κ → ℂ) (x : (ι → ℂ) × (κ → ℂ)) : ℂ :=
  ∑ r, ∑ r' ∈ univ.erase r, (x.1 r * starRingEnd ℂ (x.1 r')) * s9dF_off κ (H r r') x.2

private def s9dF_D4 (N : ι → κ → ℂ) (x : (ι → ℂ) × (κ → ℂ)) : ℂ :=
  ∑ r, ∑ s, ((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * N r s

private lemma s9dF_D1_cont (H : ι → κ → κ → ℂ) : Continuous (s9dF_D1 ι κ H) := by
  unfold s9dF_D1; fun_prop
private lemma s9dF_D2_cont (H : κ → ι → ι → ℂ) : Continuous (s9dF_D2 ι κ H) := by
  unfold s9dF_D2; fun_prop
private lemma s9dF_D3_cont (H : ι → ι → κ → κ → ℂ) : Continuous (s9dF_D3 ι κ H) := by
  unfold s9dF_D3; fun_prop
private lemma s9dF_D4_cont (N : ι → κ → ℂ) : Continuous (s9dF_D4 ι κ N) := by
  unfold s9dF_D4; fun_prop

private lemma s9dF_hP : ∀ f : (ι → ℂ) × (κ → ℂ) → ℂ, Continuous f →
    Integrable f ((s9dSphere ι).prod (s9dSphere κ)) := fun _ hf => s9dF_int_pair ι κ hf

private lemma s9dF_zero_left {F : (ι → ℂ) × (κ → ℂ) → ℂ} (f : (ι → ℂ) → ℂ) (g : (κ → ℂ) → ℂ)
    (hF : ∀ x, F x = f x.1 * g x.2) (h : ∫ w, f w ∂(s9dSphere ι) = 0) :
    ∫ x, F x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have : F = fun x => f x.1 * g x.2 := funext hF
  rw [this, integral_prod_mul, h, zero_mul]

private lemma s9dF_zero_right {F : (ι → ℂ) × (κ → ℂ) → ℂ} (f : (ι → ℂ) → ℂ) (g : (κ → ℂ) → ℂ)
    (hF : ∀ x, F x = f x.1 * g x.2) (h : ∫ v, g v ∂(s9dSphere κ) = 0) :
    ∫ x, F x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have : F = fun x => f x.1 * g x.2 := funext hF
  rw [this, integral_prod_mul, h, mul_zero]

private lemma s9dF_intsum_zero {κ' : Type*} (s : Finset κ') (F : κ' → (ι → ℂ) × (κ → ℂ) → ℂ)
    (hF : ∀ k, Continuous (F k)) (h : ∀ k ∈ s, ∫ x, F k x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0) :
    ∫ x, ∑ k ∈ s, F k x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  rw [s9dF_sum1 (s9dF_hP ι κ) s F hF]
  exact Finset.sum_eq_zero h

/-- conjugate of a vanishing off-diagonal integral -/
private lemma s9dF_int_off1_conj (r : ι) (H : ι → ι → ℂ) :
    ∫ w, ((‖w r‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (s9dF_off ι H w) ∂(s9dSphere ι) = 0 := by
  have : ∀ w : ι → ℂ, ((‖w r‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (s9dF_off ι H w) =
      starRingEnd ℂ (((‖w r‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι H w) := fun w => by
    simp [map_mul, Complex.conj_ofReal]
  simp_rw [this]
  rw [integral_conj, s9dF_int_off1 ι r H, map_zero]

private lemma s9dF_int_zero1_conj (r u u' : ι) (h : u ≠ u') :
    ∫ w, ((‖w r‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (w u * starRingEnd ℂ (w u')) ∂(s9dSphere ι) = 0 := by
  have : ∀ w : ι → ℂ, ((‖w r‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (w u * starRingEnd ℂ (w u')) =
      starRingEnd ℂ (((‖w r‖ ^ 2 : ℝ) : ℂ) * (w u * starRingEnd ℂ (w u'))) := fun w => by
    simp [map_mul, Complex.conj_ofReal]
  simp_rw [this]
  rw [integral_conj, s9dF_int_zero1 ι r u u' h, map_zero]

/-! #### expectations of the four forms -/

private lemma s9dF_I1 (H : ι → κ → κ → ℂ) :
    ∫ x, s9dF_D1 ι κ H x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  unfold s9dF_D1
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  exact s9dF_zero_right ι κ (fun w => ((‖w r‖ ^ 2 : ℝ) : ℂ)) (fun v => s9dF_off κ (H r) v)
    (fun x => rfl) (s9dF_int_off0 κ (H r))

private lemma s9dF_I2 (H : κ → ι → ι → ℂ) :
    ∫ x, s9dF_D2 ι κ H x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  unfold s9dF_D2
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun s _ => ?_)
  exact s9dF_zero_left ι κ (fun w => s9dF_off ι (H s) w) (fun v => ((‖v s‖ ^ 2 : ℝ) : ℂ))
    (fun x => mul_comm _ _) (s9dF_int_off0 ι (H s))

private lemma s9dF_I3 (H : ι → ι → κ → κ → ℂ) :
    ∫ x, s9dF_D3 ι κ H x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  unfold s9dF_D3
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun r' => by fun_prop) (fun r' hr' => ?_)
  exact s9dF_zero_left ι κ (fun w => w r * starRingEnd ℂ (w r')) (fun v => s9dF_off κ (H r r') v)
    (fun x => rfl) (s9dF_int_zero0 ι r r' (Finset.ne_of_mem_erase hr').symm)

end

section
variable (ι κ : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [DecidableEq κ]

private lemma s9dF_I4 (N : ι → κ → ℂ) :
    ∫ x, s9dF_D4 ι κ N x ∂((s9dSphere ι).prod (s9dSphere κ)) =
      ∑ r, ∑ s, ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) * ((1 / (Fintype.card κ : ℝ) : ℝ) : ℂ) * N r s := by
  unfold s9dF_D4
  rw [s9dF_sum2 (s9dF_hP ι κ) univ (fun _ => univ) _ (fun r s => by fun_prop)]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [integral_mul_const]
  have := integral_prod_mul (μ := s9dSphere ι) (ν := s9dSphere κ)
    (fun w : ι → ℂ => ((‖w r‖ ^ 2 : ℝ) : ℂ)) (fun v : κ → ℂ => ((‖v s‖ ^ 2 : ℝ) : ℂ))
  rw [this, s9dF_int_diag1 ι r, s9dF_int_diag1 κ s]

private lemma s9dF_X12 (H1 : ι → κ → κ → ℂ) (H2 : κ → ι → ι → ℂ) :
    ∫ x, s9dF_D1 ι κ H1 x * starRingEnd ℂ (s9dF_D2 ι κ H2 x)
      ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D1 ι κ H1 x * starRingEnd ℂ (s9dF_D2 ι κ H2 x) =
      ∑ r, ∑ s, (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * s9dF_off κ (H1 r) x.2) *
        starRingEnd ℂ (((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι (H2 s) x.1) := by
    intro x
    unfold s9dF_D1 s9dF_D2
    rw [map_sum, Finset.sum_mul_sum]
  simp_rw [hpt]
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun s _ => ?_)
  exact s9dF_zero_left ι κ (fun w => ((‖w r‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (s9dF_off ι (H2 s) w))
    (fun v => s9dF_off κ (H1 r) v * ((‖v s‖ ^ 2 : ℝ) : ℂ))
    (fun x => by simp only [map_mul, Complex.conj_ofReal]; ring) (s9dF_int_off1_conj ι r (H2 s))

private lemma s9dF_X13 (H1 : ι → κ → κ → ℂ) (H3 : ι → ι → κ → κ → ℂ) :
    ∫ x, s9dF_D1 ι κ H1 x * starRingEnd ℂ (s9dF_D3 ι κ H3 x)
      ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D1 ι κ H1 x * starRingEnd ℂ (s9dF_D3 ι κ H3 x) =
      ∑ r, ∑ u, ∑ u' ∈ univ.erase u, (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * s9dF_off κ (H1 r) x.2) *
        starRingEnd ℂ ((x.1 u * starRingEnd ℂ (x.1 u')) * s9dF_off κ (H3 u u') x.2) := by
    intro x
    unfold s9dF_D1 s9dF_D3
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => ?_
    rw [map_sum, Finset.mul_sum]
  simp_rw [hpt]
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun u _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun u' hu' => ?_)
  exact s9dF_zero_left ι κ
    (fun w => ((‖w r‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (w u * starRingEnd ℂ (w u')))
    (fun v => s9dF_off κ (H1 r) v * starRingEnd ℂ (s9dF_off κ (H3 u u') v))
    (fun x => by simp only [map_mul]; ring)
    (s9dF_int_zero1_conj ι r u u' (Finset.ne_of_mem_erase hu').symm)

private lemma s9dF_X23 (H2 : κ → ι → ι → ℂ) (H3 : ι → ι → κ → κ → ℂ) :
    ∫ x, s9dF_D2 ι κ H2 x * starRingEnd ℂ (s9dF_D3 ι κ H3 x)
      ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D2 ι κ H2 x * starRingEnd ℂ (s9dF_D3 ι κ H3 x) =
      ∑ s, ∑ u, ∑ u' ∈ univ.erase u, (((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι (H2 s) x.1) *
        starRingEnd ℂ ((x.1 u * starRingEnd ℂ (x.1 u')) * s9dF_off κ (H3 u u') x.2) := by
    intro x
    unfold s9dF_D2 s9dF_D3
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => ?_
    rw [map_sum, Finset.mul_sum]
  simp_rw [hpt]
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun s _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun u _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun u' hu' => ?_)
  exact s9dF_zero_right ι κ
    (fun w => s9dF_off ι (H2 s) w * starRingEnd ℂ (w u * starRingEnd ℂ (w u')))
    (fun v => ((‖v s‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (s9dF_off κ (H3 u u') v))
    (fun x => by simp only [map_mul]; ring) (s9dF_int_off1_conj κ s (H3 u u'))

private lemma s9dF_X41 (N : ι → κ → ℂ) (H1 : ι → κ → κ → ℂ) :
    ∫ x, s9dF_D4 ι κ N x * s9dF_D1 ι κ H1 x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D4 ι κ N x * s9dF_D1 ι κ H1 x =
      ∑ r, ∑ s, ∑ r'', (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * N r s) *
        (((‖x.1 r''‖ ^ 2 : ℝ) : ℂ) * s9dF_off κ (H1 r'') x.2) := by
    intro x
    unfold s9dF_D4 s9dF_D1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
  simp_rw [hpt]
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun s _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun r'' _ => ?_)
  exact s9dF_zero_right ι κ
    (fun w => ((‖w r‖ ^ 2 : ℝ) : ℂ) * ((‖w r''‖ ^ 2 : ℝ) : ℂ) * N r s)
    (fun v => ((‖v s‖ ^ 2 : ℝ) : ℂ) * s9dF_off κ (H1 r'') v)
    (fun x => by ring) (s9dF_int_off1 κ s (H1 r''))

private lemma s9dF_X42 (N : ι → κ → ℂ) (H2 : κ → ι → ι → ℂ) :
    ∫ x, s9dF_D4 ι κ N x * s9dF_D2 ι κ H2 x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D4 ι κ N x * s9dF_D2 ι κ H2 x =
      ∑ r, ∑ s, ∑ s'', (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * N r s) *
        (((‖x.2 s''‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι (H2 s'') x.1) := by
    intro x
    unfold s9dF_D4 s9dF_D2
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
  simp_rw [hpt]
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun s _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun s'' _ => ?_)
  exact s9dF_zero_left ι κ
    (fun w => ((‖w r‖ ^ 2 : ℝ) : ℂ) * s9dF_off ι (H2 s'') w)
    (fun v => ((‖v s‖ ^ 2 : ℝ) : ℂ) * ((‖v s''‖ ^ 2 : ℝ) : ℂ) * N r s)
    (fun x => by ring) (s9dF_int_off1 ι r (H2 s''))

private lemma s9dF_X43 (N : ι → κ → ℂ) (H3 : ι → ι → κ → κ → ℂ) :
    ∫ x, s9dF_D4 ι κ N x * s9dF_D3 ι κ H3 x ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D4 ι κ N x * s9dF_D3 ι κ H3 x =
      ∑ r, ∑ s, ∑ u, ∑ u' ∈ univ.erase u, (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * N r s) *
        ((x.1 u * starRingEnd ℂ (x.1 u')) * s9dF_off κ (H3 u u') x.2) := by
    intro x
    unfold s9dF_D4 s9dF_D3
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
  simp_rw [hpt]
  refine s9dF_intsum_zero ι κ _ _ (fun r => by fun_prop) (fun r _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun s _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun u _ => ?_)
  refine s9dF_intsum_zero ι κ _ _ (fun s => by fun_prop) (fun u' _ => ?_)
  exact s9dF_zero_right ι κ
    (fun w => ((‖w r‖ ^ 2 : ℝ) : ℂ) * (w u * starRingEnd ℂ (w u')) * N r s)
    (fun v => ((‖v s‖ ^ 2 : ℝ) : ℂ) * s9dF_off κ (H3 u u') v)
    (fun x => by ring) (s9dF_int_off1 κ s (H3 u u'))

end

section
variable (ι κ : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [DecidableEq κ]

private lemma s9dF_S1 (H : ι → κ → κ → ℂ) :
    ∫ x, ‖s9dF_D1 ι κ H x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) =
      (1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1))) *
        (1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1))) *
        ∑ s, ∑ s' ∈ univ.erase s, (‖∑ r, H r s s'‖ ^ 2 + ∑ r, ‖H r s s'‖ ^ 2) := by
  apply Complex.ofReal_injective
  rw [s9dF_sq_cast]
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D1 ι κ H x * starRingEnd ℂ (s9dF_D1 ι κ H x) =
      ∑ r, ∑ u, (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * ((‖x.1 u‖ ^ 2 : ℝ) : ℂ)) *
        (s9dF_off κ (H r) x.2 * starRingEnd ℂ (s9dF_off κ (H u) x.2)) := by
    intro x
    unfold s9dF_D1
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hpt]
  rw [s9dF_sum2 (s9dF_hP ι κ) univ (fun _ => univ) _ (fun r u => by fun_prop)]
  have hterm : ∀ r u : ι, ∫ x, (((‖x.1 r‖ ^ 2 : ℝ) : ℂ) * ((‖x.1 u‖ ^ 2 : ℝ) : ℂ)) *
        (s9dF_off κ (H r) x.2 * starRingEnd ℂ (s9dF_off κ (H u) x.2))
          ∂((s9dSphere ι).prod (s9dSphere κ)) =
      (((if r = u then 2 else 1) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) *
        (((1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) : ℝ) : ℂ) *
          ∑ s, ∑ s' ∈ univ.erase s, H r s s' * starRingEnd ℂ (H u s s')) := by
    intro r u
    have := integral_prod_mul (μ := s9dSphere ι) (ν := s9dSphere κ)
      (fun w : ι → ℂ => ((‖w r‖ ^ 2 : ℝ) : ℂ) * ((‖w u‖ ^ 2 : ℝ) : ℂ))
      (fun v : κ → ℂ => s9dF_off κ (H r) v * starRingEnd ℂ (s9dF_off κ (H u) v))
    rw [this, s9dF_int_diag2 ι r u, s9dF_int_offQ κ (H r) (H u)]
  have h2 : ∀ r u : ι, (((if r = u then 2 else 1) /
        ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) *
        (((1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) : ℝ) : ℂ) *
          ∑ s, ∑ s' ∈ univ.erase s, H r s s' * starRingEnd ℂ (H u s s')) =
      ((((1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1))) *
        (1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) )  : ℝ)) : ℂ) *
        (((if r = u then 2 else 1 : ℝ) : ℂ) *
          ∑ s, ∑ s' ∈ univ.erase s, H r s s' * starRingEnd ℂ (H u s s')) := by
    intro r u
    push_cast
    ring
  simp_rw [hterm, h2]
  simp only [← Finset.mul_sum]
  rw [s9dF_alg1 H]
  push_cast
  ring

end

section
variable (ι κ : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [DecidableEq κ]

private lemma s9dF_S2 (H : κ → ι → ι → ℂ) :
    ∫ x, ‖s9dF_D2 ι κ H x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) =
      (1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1))) *
        (1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1))) *
        ∑ r, ∑ r' ∈ univ.erase r, (‖∑ s, H s r r'‖ ^ 2 + ∑ s, ‖H s r r'‖ ^ 2) := by
  apply Complex.ofReal_injective
  rw [s9dF_sq_cast]
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D2 ι κ H x * starRingEnd ℂ (s9dF_D2 ι κ H x) =
      ∑ s, ∑ t, (s9dF_off ι (H s) x.1 * starRingEnd ℂ (s9dF_off ι (H t) x.1)) *
        (((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * ((‖x.2 t‖ ^ 2 : ℝ) : ℂ)) := by
    intro x
    unfold s9dF_D2
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hpt]
  rw [s9dF_sum2 (s9dF_hP ι κ) univ (fun _ => univ) _ (fun r u => by fun_prop)]
  have hterm : ∀ s t : κ, ∫ x, (s9dF_off ι (H s) x.1 * starRingEnd ℂ (s9dF_off ι (H t) x.1)) *
        (((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * ((‖x.2 t‖ ^ 2 : ℝ) : ℂ))
          ∂((s9dSphere ι).prod (s9dSphere κ)) =
      (((1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) *
          ∑ r, ∑ r' ∈ univ.erase r, H s r r' * starRingEnd ℂ (H t r r')) *
        (((if s = t then 2 else 1) / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) : ℝ) : ℂ) := by
    intro s t
    have := integral_prod_mul (μ := s9dSphere ι) (ν := s9dSphere κ)
      (fun w : ι → ℂ => s9dF_off ι (H s) w * starRingEnd ℂ (s9dF_off ι (H t) w))
      (fun v : κ → ℂ => ((‖v s‖ ^ 2 : ℝ) : ℂ) * ((‖v t‖ ^ 2 : ℝ) : ℂ))
    rw [this, s9dF_int_diag2 κ s t, s9dF_int_offQ ι (H s) (H t)]
  have h2 : ∀ s t : κ, (((1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) : ℝ) : ℂ) *
          ∑ r, ∑ r' ∈ univ.erase r, H s r r' * starRingEnd ℂ (H t r r')) *
        (((if s = t then 2 else 1) / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) : ℝ) : ℂ) =
      ((((1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1))) *
        (1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) )  : ℝ)) : ℂ) *
        (((if s = t then 2 else 1 : ℝ) : ℂ) *
          ∑ r, ∑ r' ∈ univ.erase r, H s r r' * starRingEnd ℂ (H t r r')) := by
    intro s t
    push_cast
    ring
  simp_rw [hterm, h2]
  simp only [← Finset.mul_sum]
  rw [s9dF_alg1 H]
  push_cast
  ring

private lemma s9dF_S3 (H : ι → ι → κ → κ → ℂ) :
    ∫ x, ‖s9dF_D3 ι κ H x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) =
      (1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1))) *
        (1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1))) *
        ∑ r, ∑ r' ∈ univ.erase r, ∑ s, ∑ s' ∈ univ.erase s, ‖H r r' s s'‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [s9dF_sq_cast]
  have hpt : ∀ x : (ι → ℂ) × (κ → ℂ), s9dF_D3 ι κ H x * starRingEnd ℂ (s9dF_D3 ι κ H x) =
      ∑ r, ∑ r' ∈ univ.erase r, ∑ u, ∑ u' ∈ univ.erase u,
        (x.1 r * starRingEnd ℂ (x.1 r') * (starRingEnd ℂ (x.1 u) * x.1 u')) *
        (s9dF_off κ (H r r') x.2 * starRingEnd ℂ (s9dF_off κ (H u u') x.2)) := by
    intro x
    unfold s9dF_D3
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [hpt]
  rw [s9dF_sum4 (s9dF_hP ι κ) _ (fun a b c d => by fun_prop)]
  have hterm : ∀ r, ∀ r' ∈ univ.erase r, ∀ u, ∀ u' ∈ univ.erase u,
      ∫ x, (x.1 r * starRingEnd ℂ (x.1 r') * (starRingEnd ℂ (x.1 u) * x.1 u')) *
        (s9dF_off κ (H r r') x.2 * starRingEnd ℂ (s9dF_off κ (H u u') x.2))
          ∂((s9dSphere ι).prod (s9dSphere κ)) =
      ((if r = u ∧ r' = u' then 1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) else 0 : ℝ) : ℂ) *
        (((1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) : ℝ) : ℂ) *
          ∑ s, ∑ s' ∈ univ.erase s, H r r' s s' * starRingEnd ℂ (H u u' s s')) := by
    intro r r' hr' u u' hu'
    have := integral_prod_mul (μ := s9dSphere ι) (ν := s9dSphere κ)
      (fun w : ι → ℂ => w r * starRingEnd ℂ (w r') * (starRingEnd ℂ (w u) * w u'))
      (fun v : κ → ℂ => s9dF_off κ (H r r') v * starRingEnd ℂ (s9dF_off κ (H u u') v))
    rw [this, s9dF_mono4 ι r r' u u' (Finset.ne_of_mem_erase hr').symm
      (Finset.ne_of_mem_erase hu').symm, s9dF_int_offQ κ (H r r') (H u u')]
  refine (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' hr' =>
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' hu' => hterm r r' hr' u u' hu').trans ?_
  rw [s9dF_collapse4 (1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)))
    (fun r r' u u' => ((1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1)) : ℝ) : ℂ) *
          ∑ s, ∑ s' ∈ univ.erase s, H r r' s s' * starRingEnd ℂ (H u u' s s'))]
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := fun z => by
    rw [Complex.mul_conj', Complex.ofReal_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, hn]
  simp only [← Finset.mul_sum]
  ring

end

section
variable {ιR ιS : Type} [Fintype ιR] [DecidableEq ιR] [Fintype ιS] [DecidableEq ιS]

private lemma s9dF_split (F : ιR → ιR → ιS → ιS → ℂ) :
    ∑ r, ∑ r', ∑ s, ∑ s', F r r' s s' =
      ∑ r, ∑ s, F r r s s + ∑ r, ∑ s, ∑ s' ∈ univ.erase s, F r r s s' +
        ∑ r, ∑ r' ∈ univ.erase r, ∑ s, F r r' s s +
        ∑ r, ∑ r' ∈ univ.erase r, ∑ s, ∑ s' ∈ univ.erase s, F r r' s s' := by
  have hs : ∀ r r', ∑ s, ∑ s', F r r' s s' =
      ∑ s, F r r' s s + ∑ s, ∑ s' ∈ univ.erase s, F r r' s s' := by
    intro r r'
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (Finset.add_sum_erase univ _ (Finset.mem_univ s)).symm
  have hr : ∀ r, ∑ r', ∑ s, ∑ s', F r r' s s' =
      (∑ s, F r r s s + ∑ s, ∑ s' ∈ univ.erase s, F r r s s') +
        ∑ r' ∈ univ.erase r, (∑ s, F r r' s s + ∑ s, ∑ s' ∈ univ.erase s, F r r' s s') := by
    intro r
    simp_rw [hs]
    exact (Finset.add_sum_erase univ (fun r' => ∑ s, F r r' s s +
      ∑ s, ∑ s' ∈ univ.erase s, F r r' s s') (Finset.mem_univ r)).symm
  simp_rw [hr, Finset.sum_add_distrib]
  ring

end

section
variable (ι κ : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [DecidableEq κ]

private lemma s9dF_two (a b : (ι → ℂ) × (κ → ℂ) → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hab : ∫ x, a x * starRingEnd ℂ (b x) ∂((s9dSphere ι).prod (s9dSphere κ)) = 0) :
    ∫ x, ‖a x + b x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) =
      ∫ x, ‖a x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) +
        ∫ x, ‖b x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, s9dF_sq_cast, s9dF_sq_cast, s9dF_sq_cast]
  have e : ∀ x, (a x + b x) * starRingEnd ℂ (a x + b x) =
      (a x * starRingEnd ℂ (a x) + b x * starRingEnd ℂ (b x)) +
        (a x * starRingEnd ℂ (b x) + starRingEnd ℂ (a x * starRingEnd ℂ (b x))) := fun x => by
    simp only [map_add, map_mul, Complex.conj_conj]; ring
  simp_rw [e]
  have iaa : Integrable (fun x => a x * starRingEnd ℂ (a x))
      ((s9dSphere ι).prod (s9dSphere κ)) := s9dF_hP ι κ _ (by fun_prop)
  have ibb : Integrable (fun x => b x * starRingEnd ℂ (b x))
      ((s9dSphere ι).prod (s9dSphere κ)) := s9dF_hP ι κ _ (by fun_prop)
  have iab : Integrable (fun x => a x * starRingEnd ℂ (b x))
      ((s9dSphere ι).prod (s9dSphere κ)) := s9dF_hP ι κ _ (by fun_prop)
  have icab : Integrable (fun x => starRingEnd ℂ (a x * starRingEnd ℂ (b x)))
      ((s9dSphere ι).prod (s9dSphere κ)) := s9dF_hP ι κ _ (by fun_prop)
  have i1 : Integrable (fun x => a x * starRingEnd ℂ (a x) + b x * starRingEnd ℂ (b x))
      ((s9dSphere ι).prod (s9dSphere κ)) := iaa.add ibb
  have i2 : Integrable (fun x => a x * starRingEnd ℂ (b x) +
      starRingEnd ℂ (a x * starRingEnd ℂ (b x))) ((s9dSphere ι).prod (s9dSphere κ)) :=
    iab.add icab
  rw [integral_add i1 i2, integral_add iaa ibb, integral_add iab icab, integral_conj, hab]
  simp

private lemma s9dF_three (f g h : (ι → ℂ) × (κ → ℂ) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h)
    (hfg : ∫ x, f x * starRingEnd ℂ (g x) ∂((s9dSphere ι).prod (s9dSphere κ)) = 0)
    (hfh : ∫ x, f x * starRingEnd ℂ (h x) ∂((s9dSphere ι).prod (s9dSphere κ)) = 0)
    (hgh : ∫ x, g x * starRingEnd ℂ (h x) ∂((s9dSphere ι).prod (s9dSphere κ)) = 0) :
    ∫ x, ‖f x + g x + h x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) =
      ∫ x, ‖f x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) +
        ∫ x, ‖g x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) +
        ∫ x, ‖h x‖ ^ 2 ∂((s9dSphere ι).prod (s9dSphere κ)) := by
  have ifh : Integrable (fun x => f x * starRingEnd ℂ (h x)) ((s9dSphere ι).prod (s9dSphere κ)) :=
    s9dF_hP ι κ _ (by fun_prop)
  have igh : Integrable (fun x => g x * starRingEnd ℂ (h x)) ((s9dSphere ι).prod (s9dSphere κ)) :=
    s9dF_hP ι κ _ (by fun_prop)
  have hcross : ∫ x, (f x + g x) * starRingEnd ℂ (h x) ∂((s9dSphere ι).prod (s9dSphere κ)) = 0 := by
    simp_rw [add_mul]
    rw [integral_add ifh igh, hfh, hgh, add_zero]
  rw [s9dF_two ι κ (fun x => f x + g x) h (by fun_prop) hh hcross,
    s9dF_two ι κ f g hf hg hfg]

end

section S9dForms

/-- the pair measure on `S^{ιR} × S^{ιS}` of the independent perturbations `(π, θ)` (eq. `delta_3`). -/
def s9dPair (ιR ιS : Type) [Fintype ιR] [Fintype ιS] : Measure ((ιR → ℂ) × (ιS → ℂ)) :=
  (s9dSphere ιR).prod (s9dSphere ιS)

/-- the variance of a real function under a measure: `𝔼 (f - 𝔼 f)²`. -/
def s9dVar {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P

variable {ιR ιS ιT : Type} [Fintype ιR] [Fintype ιS] [Fintype ιT]

/-- the Gram matrix `⟨V_{r,s}, V_{r',s'}⟩ = ∑_t V_{r,s}(t) conj(V_{r',s'}(t))` of the vectors
`V_{r,s} ∈ ℂ^{T'}` of eq. `delta_4`. -/
def s9dGram (V : ιR → ιS → ιT → ℂ) (r : ιR) (s : ιS) (r' : ιR) (s' : ιS) : ℂ :=
  ∑ t, V r s t * starRingEnd ℂ (V r' s' t)

/-- the form `p(π, θ) = ∑_t |∑_{r,s} (κ_rπ_r)(ρ_sθ_s) V_{r,s}(t)|²` of the random perturbation argument
(l. 5509-5540), written for the unit-sphere vectors `w = (κ_rπ_r)/√M₁` and `v = (ρ_sθ_s)/√M₂`; the factor
`M₁M₂` is the squared norm of `g̃ ⊗ h̃`. -/
def s9dP (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (w : ιR → ℂ) (v : ιS → ℂ) : ℝ :=
  M1 * M2 * ∑ t, ‖∑ r, ∑ s, w r * v s * V r s t‖ ^ 2

/-- the diagonal part `p_4 = ∑_{r,s} |a_r|²|b_s|² ‖V_{r,s}‖²` (l. 5626). -/
def s9dP4 (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (w : ιR → ℂ) (v : ιS → ℂ) : ℝ :=
  M1 * M2 * ∑ r, ∑ s, ‖w r‖ ^ 2 * ‖v s‖ ^ 2 * ∑ t, ‖V r s t‖ ^ 2

variable [DecidableEq ιR] [DecidableEq ιS]

/-- `p_1`: the terms `r = r'`, `s ≠ s'` (l. 5618-5619). -/
def s9dP1 (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (w : ιR → ℂ) (v : ιS → ℂ) : ℂ :=
  ((M1 * M2 : ℝ) : ℂ) * ∑ r, ∑ s, ∑ s' ∈ univ.erase s,
    ((‖w r‖ ^ 2 : ℝ) : ℂ) * (v s * starRingEnd ℂ (v s')) * s9dGram V r s r s'

/-- `p_2`: the terms `r ≠ r'`, `s = s'`, with the coefficient `⟨V_{r,s}, V_{r',s}⟩` of eq. `delta_4`
(`⟨a, b⟩ = ∑_t a(t) conj b(t)`). The printed pairing `⟨V_{r',s}, V_{r,s}⟩` (l. 5620) is crossed under
this convention, the one of eq. `delta_4` (under the opposite convention `p_2` is right and
eq. `delta_4` is not). -/
def s9dP2 (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (w : ιR → ℂ) (v : ιS → ℂ) : ℂ :=
  ((M1 * M2 : ℝ) : ℂ) * ∑ r, ∑ r' ∈ univ.erase r, ∑ s,
    (w r * starRingEnd ℂ (w r')) * ((‖v s‖ ^ 2 : ℝ) : ℂ) * s9dGram V r s r' s

/-- `p_3`: the terms `r ≠ r'`, `s ≠ s'`; the printed pairing `⟨V_{r',s}, V_{r,s'}⟩` (crossed under either
inner-product convention) and the missing conjugate on `θ_{s'}` (l. 5622-5623) are corrected to the
coefficient of eq. `delta_4`. -/
def s9dP3 (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (w : ιR → ℂ) (v : ιS → ℂ) : ℂ :=
  ((M1 * M2 : ℝ) : ℂ) * ∑ r, ∑ r' ∈ univ.erase r, ∑ s, ∑ s' ∈ univ.erase s,
    (w r * starRingEnd ℂ (w r')) * (v s * starRingEnd ℂ (v s')) * s9dGram V r s r' s'

/-- eq. `delta_4` and `p = p_1 + p_2 + p_3 + p_4` (l. 5532-5540, 5616-5626), pointwise. -/
theorem s9dP_decomp (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (w : ιR → ℂ) (v : ιS → ℂ) :
    ((s9dP M1 M2 V w v : ℝ) : ℂ) =
      s9dP1 M1 M2 V w v + s9dP2 M1 M2 V w v + s9dP3 M1 M2 V w v + ((s9dP4 M1 M2 V w v : ℝ) : ℂ) := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := fun z => by
    rw [Complex.mul_conj', Complex.ofReal_pow]
  set F : ιR → ιR → ιS → ιS → ℂ := fun r r' s s' =>
    (w r * starRingEnd ℂ (w r')) * (v s * starRingEnd ℂ (v s')) * s9dGram V r s r' s' with hF
  have hexp : ((s9dP M1 M2 V w v : ℝ) : ℂ) =
      ((M1 * M2 : ℝ) : ℂ) * ∑ r, ∑ r', ∑ s, ∑ s', F r r' s s' := by
    unfold s9dP
    rw [Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_sum]
    simp_rw [hn]
    have hZ : ∀ t, ∑ r, ∑ s, w r * v s * V r s t = ∑ q : ιR × ιS, w q.1 * v q.2 * V q.1 q.2 t :=
      fun t => (Fintype.sum_prod_type (fun q : ιR × ιS => w q.1 * v q.2 * V q.1 q.2 t)).symm
    simp_rw [hZ]
    calc ∑ t, (∑ q : ιR × ιS, w q.1 * v q.2 * V q.1 q.2 t) *
          starRingEnd ℂ (∑ q : ιR × ιS, w q.1 * v q.2 * V q.1 q.2 t)
        = ∑ t, ∑ q : ιR × ιS, ∑ q' : ιR × ιS, (w q.1 * v q.2 * V q.1 q.2 t) *
            starRingEnd ℂ (w q'.1 * v q'.2 * V q'.1 q'.2 t) :=
          Finset.sum_congr rfl fun t _ => by rw [map_sum, Finset.sum_mul_sum]
      _ = ∑ q : ιR × ιS, ∑ t, ∑ q' : ιR × ιS, (w q.1 * v q.2 * V q.1 q.2 t) *
            starRingEnd ℂ (w q'.1 * v q'.2 * V q'.1 q'.2 t) := Finset.sum_comm
      _ = ∑ q : ιR × ιS, ∑ q' : ιR × ιS, ∑ t, (w q.1 * v q.2 * V q.1 q.2 t) *
            starRingEnd ℂ (w q'.1 * v q'.2 * V q'.1 q'.2 t) :=
          Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = ∑ q : ιR × ιS, ∑ q' : ιR × ιS, (w q.1 * starRingEnd ℂ (w q'.1)) *
            (v q.2 * starRingEnd ℂ (v q'.2)) * s9dGram V q.1 q.2 q'.1 q'.2 := by
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
          unfold s9dGram
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [map_mul]
          ring
      _ = ∑ r, ∑ r', ∑ s, ∑ s', F r r' s s' := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
          calc _ = ∑ r, ∑ s, ∑ r', ∑ s', F r r' s s' := rfl
            _ = _ := Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hA : ∑ r, ∑ s, F r r s s =
      ((∑ r, ∑ s, ‖w r‖ ^ 2 * ‖v s‖ ^ 2 * ∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [hF]
    unfold s9dGram
    simp_rw [← hn]
    push_cast
    ring
  have hB : ∑ r, ∑ s, ∑ s' ∈ univ.erase s, F r r s s' =
      ∑ r, ∑ s, ∑ s' ∈ univ.erase s,
        ((‖w r‖ ^ 2 : ℝ) : ℂ) * (v s * starRingEnd ℂ (v s')) * s9dGram V r s r s' := by
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun s' _ => ?_
    simp only [hF, hn]
  have hC : ∑ r, ∑ r' ∈ univ.erase r, ∑ s, F r r' s s =
      ∑ r, ∑ r' ∈ univ.erase r, ∑ s,
        (w r * starRingEnd ℂ (w r')) * ((‖v s‖ ^ 2 : ℝ) : ℂ) * s9dGram V r s r' s := by
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ =>
      Finset.sum_congr rfl fun s _ => ?_
    simp only [hF, hn]
  rw [hexp, s9dF_split, hA, hB, hC]
  unfold s9dP1 s9dP2 s9dP3 s9dP4
  simp only [hF]
  push_cast
  ring

variable [Nonempty ιR] [Nonempty ιS]

private lemma s9dF_p1_eq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (x : (ιR → ℂ) × (ιS → ℂ)) :
    s9dP1 M1 M2 V x.1 x.2 = ((M1 * M2 : ℝ) : ℂ) *
      s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x := by
  unfold s9dP1 s9dF_D1 s9dF_off
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

private lemma s9dF_p2_eq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (x : (ιR → ℂ) × (ιS → ℂ)) :
    s9dP2 M1 M2 V x.1 x.2 = ((M1 * M2 : ℝ) : ℂ) *
      s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x := by
  unfold s9dP2 s9dF_D2 s9dF_off
  congr 1
  calc ∑ r, ∑ r' ∈ univ.erase r, ∑ s, (x.1 r * starRingEnd ℂ (x.1 r')) *
        ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * s9dGram V r s r' s
      = ∑ r, ∑ s, ∑ r' ∈ univ.erase r, (x.1 r * starRingEnd ℂ (x.1 r')) *
        ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * s9dGram V r s r' s :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ s, ∑ r, ∑ r' ∈ univ.erase r, (x.1 r * starRingEnd ℂ (x.1 r')) *
        ((‖x.2 s‖ ^ 2 : ℝ) : ℂ) * s9dGram V r s r' s := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => ?_
      ring

private lemma s9dF_p3_eq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (x : (ιR → ℂ) × (ιS → ℂ)) :
    s9dP3 M1 M2 V x.1 x.2 = ((M1 * M2 : ℝ) : ℂ) *
      s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x := by
  unfold s9dP3 s9dF_D3 s9dF_off
  congr 1
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

private lemma s9dF_p4_eq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (x : (ιR → ℂ) × (ιS → ℂ)) :
    ((s9dP4 M1 M2 V x.1 x.2 : ℝ) : ℂ) = ((M1 * M2 : ℝ) : ℂ) *
      s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x := by
  unfold s9dP4 s9dF_D4
  rw [Complex.ofReal_mul]
  congr 1
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast
  ring

private lemma s9dF_P_eq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (x : (ιR → ℂ) × (ιS → ℂ)) :
    ((s9dP M1 M2 V x.1 x.2 : ℝ) : ℂ) = ((M1 * M2 : ℝ) : ℂ) *
      (s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
        s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x +
        s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x +
        s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x) := by
  rw [s9dP_decomp, s9dF_p1_eq, s9dF_p2_eq, s9dF_p3_eq, s9dF_p4_eq]
  ring

/-- the expectation of `p`: only the diagonal survives, `𝔼 p = (M₁M₂/(k₁k₂)) ∑_{r,s} ‖V_{r,s}‖²`
(Claim 9.12, first display). -/
theorem s9d_expect_P (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) :
    ∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS) =
      M1 * M2 / ((Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ)) *
        ∑ r, ∑ s, ∑ t, ‖V r s t‖ ^ 2 := by
  unfold s9dPair
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [s9dF_P_eq]
  have i1 := s9dF_hP ιR ιS _ (s9dF_D1_cont ιR ιS (fun r s s' => s9dGram V r s r s'))
  have i2 := s9dF_hP ιR ιS _ (s9dF_D2_cont ιR ιS (fun s r r' => s9dGram V r s r' s))
  have i3 := s9dF_hP ιR ιS _ (s9dF_D3_cont ιR ιS (fun r r' s s' => s9dGram V r s r' s'))
  have i4 := s9dF_hP ιR ιS _ (s9dF_D4_cont ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)))
  have i12 : Integrable (fun x => s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
      s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x) ((s9dSphere ιR).prod (s9dSphere ιS)) :=
    i1.add i2
  have i123 : Integrable (fun x => s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
      s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x +
      s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x)
      ((s9dSphere ιR).prod (s9dSphere ιS)) := i12.add i3
  rw [integral_const_mul, integral_add i123 i4, integral_add i12 i3,
    integral_add i1 i2, s9dF_I1, s9dF_I2, s9dF_I3, s9dF_I4]
  simp only [zero_add, ← Finset.mul_sum, ← Complex.ofReal_sum]
  push_cast
  ring

private lemma s9dF_aux_div (m a b : ℝ) : m / (a * b) = (1 / a) * (1 / b) * m := by
  rw [div_eq_mul_inv, mul_inv]; ring

private lemma s9dF_norm_sq_mul (c : ℝ) (z : ℂ) : ‖((c : ℝ) : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- `𝔼 |p_1|²`, exactly (the fourth moments are exact: `𝔼|w_r|²|w_u|² = (1 + [r=u])/(k(k+1))`). -/
theorem s9d_expect_p1_sq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) :
    ∫ x, ‖s9dP1 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) =
      (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) *
        ∑ s, ∑ s' ∈ univ.erase s,
          (‖∑ r, s9dGram V r s r s'‖ ^ 2 + ∑ r, ‖s9dGram V r s r s'‖ ^ 2) := by
  unfold s9dPair
  simp_rw [s9dF_p1_eq, s9dF_norm_sq_mul]
  rw [integral_const_mul, s9dF_S1 ιR ιS (fun r s s' => s9dGram V r s r s'), s9dF_aux_div ((M1 * M2) ^ 2)]
  ring

/-- `𝔼 |p_2|²`, exactly. -/
theorem s9d_expect_p2_sq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) :
    ∫ x, ‖s9dP2 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) =
      (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) *
        ∑ r, ∑ r' ∈ univ.erase r,
          (‖∑ s, s9dGram V r s r' s‖ ^ 2 + ∑ s, ‖s9dGram V r s r' s‖ ^ 2) := by
  unfold s9dPair
  simp_rw [s9dF_p2_eq, s9dF_norm_sq_mul]
  rw [integral_const_mul, s9dF_S2 ιR ιS (fun s r r' => s9dGram V r s r' s), s9dF_aux_div ((M1 * M2) ^ 2)]
  ring

/-- `𝔼 |p_3|²`, exactly: all terms have distinct phase characters. -/
theorem s9d_expect_p3_sq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) :
    ∫ x, ‖s9dP3 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) =
      (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) *
        ∑ r, ∑ r' ∈ univ.erase r, ∑ s, ∑ s' ∈ univ.erase s, ‖s9dGram V r s r' s'‖ ^ 2 := by
  unfold s9dPair
  simp_rw [s9dF_p3_eq, s9dF_norm_sq_mul]
  rw [integral_const_mul, s9dF_S3 ιR ιS (fun r r' s s' => s9dGram V r s r' s'), s9dF_aux_div ((M1 * M2) ^ 2)]
  ring

/-- the cross terms vanish (eq. `delta_6`, with no loss): `𝔼|p_1+p_2+p_3|² = 𝔼|p_1|² + 𝔼|p_2|² + 𝔼|p_3|²`
(the three have disjoint phase characters). -/
theorem s9d_expect_pOff_sq (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) :
    ∫ x, ‖s9dP1 M1 M2 V x.1 x.2 + s9dP2 M1 M2 V x.1 x.2 + s9dP3 M1 M2 V x.1 x.2‖ ^ 2
        ∂(s9dPair ιR ιS) =
      ∫ x, ‖s9dP1 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) +
        ∫ x, ‖s9dP2 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) +
        ∫ x, ‖s9dP3 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) := by
  unfold s9dPair
  have e : ∀ x : (ιR → ℂ) × (ιS → ℂ), s9dP1 M1 M2 V x.1 x.2 + s9dP2 M1 M2 V x.1 x.2 +
      s9dP3 M1 M2 V x.1 x.2 = ((M1 * M2 : ℝ) : ℂ) *
        (s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
          s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x +
          s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x) := by
    intro x
    rw [s9dF_p1_eq, s9dF_p2_eq, s9dF_p3_eq]
    ring
  simp_rw [e, s9dF_p1_eq, s9dF_p2_eq, s9dF_p3_eq, s9dF_norm_sq_mul]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    s9dF_three ιR ιS _ _ _ (s9dF_D1_cont ιR ιS _) (s9dF_D2_cont ιR ιS _) (s9dF_D3_cont ιR ιS _)
      (s9dF_X12 ιR ιS _ _) (s9dF_X13 ιR ιS _ _) (s9dF_X23 ιR ιS _ _)]
  ring

/-- the variance of `p` splits orthogonally into the off-diagonal part and the variance of the
diagonal part: `var p = 𝔼|p_1+p_2+p_3|² + var p_4` (strengthens eq. `delta_5`: `p_off` is orthogonal to
every phase-invariant function, in particular to `p_4 - 𝔼 p`). -/
theorem s9d_var_P_decomp (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) :
    s9dVar (s9dPair ιR ιS) (fun x => s9dP M1 M2 V x.1 x.2) =
      ∫ x, ‖s9dP1 M1 M2 V x.1 x.2 + s9dP2 M1 M2 V x.1 x.2 + s9dP3 M1 M2 V x.1 x.2‖ ^ 2
          ∂(s9dPair ιR ιS) +
        s9dVar (s9dPair ιR ιS) (fun x => s9dP4 M1 M2 V x.1 x.2) := by
  unfold s9dVar s9dPair
  set μ := (s9dSphere ιR).prod (s9dSphere ιS) with hμ
  set P : (ιR → ℂ) × (ιS → ℂ) → ℝ := fun x => s9dP M1 M2 V x.1 x.2 with hPdef
  set P4 : (ιR → ℂ) × (ιS → ℂ) → ℝ := fun x => s9dP4 M1 M2 V x.1 x.2 with hP4def
  have hPc : Continuous P := by simp only [hPdef, s9dP]; fun_prop
  have hP4c : Continuous P4 := by simp only [hP4def, s9dP4]; fun_prop
  have hcomp : ∀ x, (((P x - P4 x : ℝ)) : ℂ) = ((M1 * M2 : ℝ) : ℂ) *
      (s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
        s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x +
        s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x) := by
    intro x
    rw [Complex.ofReal_sub]
    simp only [hPdef, hP4def]
    rw [s9dF_P_eq, s9dF_p4_eq]
    ring
  have hoff : ∀ x, ((P x - P4 x : ℝ) : ℂ) =
      s9dP1 M1 M2 V x.1 x.2 + s9dP2 M1 M2 V x.1 x.2 + s9dP3 M1 M2 V x.1 x.2 := by
    intro x
    rw [hcomp, s9dF_p1_eq, s9dF_p2_eq, s9dF_p3_eq]
    ring
  have i1 := s9dF_hP ιR ιS _ (s9dF_D1_cont ιR ιS (fun r s s' => s9dGram V r s r s'))
  have i2 := s9dF_hP ιR ιS _ (s9dF_D2_cont ιR ιS (fun s r r' => s9dGram V r s r' s))
  have i3 := s9dF_hP ιR ιS _ (s9dF_D3_cont ιR ιS (fun r r' s s' => s9dGram V r s r' s'))
  have i12 : Integrable (fun x => s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
      s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x) μ := i1.add i2
  have hd : ∫ x, (P x - P4 x) ∂μ = 0 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [hcomp]
    rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2, s9dF_I1, s9dF_I2, s9dF_I3]
    simp
  have hdP4 : ∫ x, (P x - P4 x) * P4 x ∂μ = 0 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have e : ∀ x, (((P x - P4 x) * P4 x : ℝ) : ℂ) = ((M1 * M2 : ℝ) : ℂ) * ((M1 * M2 : ℝ) : ℂ) *
        (s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x +
          (s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x +
          s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x)) := by
      intro x
      rw [Complex.ofReal_mul, hcomp x]
      simp only [hP4def]
      rw [s9dF_p4_eq]
      ring
    simp_rw [e]
    have c4 := s9dF_D4_cont ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ))
    have c1 := s9dF_D1_cont ιR ιS (fun r s s' => s9dGram V r s r s')
    have c2 := s9dF_D2_cont ιR ιS (fun s r r' => s9dGram V r s r' s)
    have c3 := s9dF_D3_cont ιR ιS (fun r r' s s' => s9dGram V r s r' s')
    have k1 : Integrable (fun x => s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D1 ιR ιS (fun r s s' => s9dGram V r s r s') x) μ :=
      s9dF_hP ιR ιS _ (c4.mul c1)
    have k2 : Integrable (fun x => s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x) μ :=
      s9dF_hP ιR ιS _ (c4.mul c2)
    have k3 : Integrable (fun x => s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x) μ :=
      s9dF_hP ιR ιS _ (c4.mul c3)
    have k23 : Integrable (fun x => s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D2 ιR ιS (fun s r r' => s9dGram V r s r' s) x +
          s9dF_D4 ιR ιS (fun r s => ((∑ t, ‖V r s t‖ ^ 2 : ℝ) : ℂ)) x *
            s9dF_D3 ιR ιS (fun r r' s s' => s9dGram V r s r' s') x) μ := k2.add k3
    rw [integral_const_mul, integral_add k1 k23, integral_add k2 k3, s9dF_X41, s9dF_X42, s9dF_X43]
    simp
  have hsq : ∫ x, ‖s9dP1 M1 M2 V x.1 x.2 + s9dP2 M1 M2 V x.1 x.2 + s9dP3 M1 M2 V x.1 x.2‖ ^ 2 ∂μ =
      ∫ x, (P x - P4 x) ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← hoff x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hmean : ∫ x, P x ∂μ = ∫ x, P4 x ∂μ := by
    have iA : Integrable (fun x => P x - P4 x) μ := s9dF_int_pair ιR ιS (by fun_prop)
    have iB : Integrable (fun x => P4 x) μ := s9dF_int_pair ιR ιS (by fun_prop)
    have : ∫ x, P x ∂μ = ∫ x, ((P x - P4 x) + P4 x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
    rw [this, integral_add iA iB, hd, zero_add]
  show ∫ x, (P x - ∫ y, P y ∂μ) ^ 2 ∂μ = _ + ∫ x, (P4 x - ∫ y, P4 y ∂μ) ^ 2 ∂μ
  rw [hsq, hmean]
  set m := ∫ y, P4 y ∂μ with hm
  have key : ∫ x, (P x - m) ^ 2 ∂μ =
      ∫ x, ((P x - P4 x) ^ 2 + 2 * ((P x - P4 x) * P4 x) - 2 * m * (P x - P4 x) + (P4 x - m) ^ 2) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  rw [key]
  have iA : Integrable (fun x => (P x - P4 x) ^ 2) μ := s9dF_int_pair ιR ιS (by fun_prop)
  have iB : Integrable (fun x => 2 * ((P x - P4 x) * P4 x)) μ := s9dF_int_pair ιR ιS (by fun_prop)
  have iC : Integrable (fun x => 2 * m * (P x - P4 x)) μ := s9dF_int_pair ιR ιS (by fun_prop)
  have iD : Integrable (fun x => (P4 x - m) ^ 2) μ := s9dF_int_pair ιR ιS (by fun_prop)
  have iAB : Integrable (fun x => (P x - P4 x) ^ 2 + 2 * ((P x - P4 x) * P4 x)) μ := iA.add iB
  have iABC : Integrable (fun x => (P x - P4 x) ^ 2 + 2 * ((P x - P4 x) * P4 x) -
      2 * m * (P x - P4 x)) μ := iAB.sub iC
  rw [integral_add iABC iD, integral_sub iAB iC, integral_add iA iB, integral_const_mul,
    integral_const_mul, hd, hdP4]
  ring

end S9dForms

end TrackB
end RestrictedPolynomials
end
