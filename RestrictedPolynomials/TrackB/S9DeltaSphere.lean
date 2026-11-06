module

public import RestrictedPolynomials.TrackB.ExtClassical

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate Matrix

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section S9dSphere

/-- the uniform probability measure on the unit sphere of `ℂ^ι` (the distribution of
`(κ_r π_r)_r / √M₁` in the random perturbation argument, l. 5488-5496): the pushforward of the measure of
`ext_sphere_measure_exists` along an enumeration of `ι`. It is canonical by `s9dSphere_unique`
(a measure is not a basis: nothing depends on the choice). -/
def s9dSphere (ι : Type) [Fintype ι] : Measure (ι → ℂ) :=
  if h : 1 ≤ Fintype.card ι then
    (Classical.choose (ext_sphere_measure_exists (Fintype.card ι) h)).map
      (fun (w : Fin (Fintype.card ι) → ℂ) (i : ι) => w (Fintype.equivFin ι i))
  else 0

private lemma s9d_meas_reindex {ι κ : Type} (e : ι ≃ κ) :
    Measurable (fun (v : ι → ℂ) (a : κ) => v (e.symm a)) :=
  measurable_pi_iff.2 (fun _ => measurable_pi_apply _)

private lemma s9d_reindex_unitary {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    ∃ U' : Matrix.unitaryGroup κ ℂ, ∀ v : ι → ℂ,
      (U' : Matrix κ κ ℂ) *ᵥ (fun a => v (e.symm a)) =
        fun a => ((U : Matrix ι ι ℂ) *ᵥ v) (e.symm a) := by
  have hU : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff.1 U.2
  refine ⟨⟨(U : Matrix ι ι ℂ).submatrix e.symm e.symm, ?_⟩, fun v => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hU, Matrix.submatrix_one_equiv]
  · ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm (fun j => (U : Matrix ι ι ℂ) (e.symm a) j * v j)

private lemma s9d_transport {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (P : Measure (ι → ℂ)) (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup ι ℂ, P.map (Matrix.mulVec (U : Matrix ι ι ℂ)) = P) :
    IsProbabilityMeasure (P.map (fun (v : ι → ℂ) (a : κ) => v (e.symm a))) ∧
      (P.map (fun (v : ι → ℂ) (a : κ) => v (e.symm a))) {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 ∧
      ∀ U : Matrix.unitaryGroup κ ℂ,
        (P.map (fun (v : ι → ℂ) (a : κ) => v (e.symm a))).map
          (Matrix.mulVec (U : Matrix κ κ ℂ)) = P.map (fun (v : ι → ℂ) (a : κ) => v (e.symm a)) := by
  have hR := s9d_meas_reindex e
  refine ⟨(Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 hP, ?_, ?_⟩
  · rw [Measure.map_apply hR (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl]
    have : (fun (v : ι → ℂ) (a : κ) => v (e.symm a)) ⁻¹' {w : κ → ℂ | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ =
        {w : ι → ℂ | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ := by
      ext v
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [Equiv.sum_comp e.symm (fun j => ‖v j‖ ^ 2)]
    rw [this]; exact hsph
  · intro U
    obtain ⟨U'', hU''⟩ := s9d_reindex_unitary e.symm U
    have hm : Measurable (Matrix.mulVec (U : Matrix κ κ ℂ)) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    have hm'' : Measurable (Matrix.mulVec (U'' : Matrix ι ι ℂ)) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    rw [Measure.map_map hm hR]
    have : (Matrix.mulVec (U : Matrix κ κ ℂ)) ∘ (fun (v : ι → ℂ) (a : κ) => v (e.symm a)) =
        (fun (v : ι → ℂ) (a : κ) => v (e.symm a)) ∘ (Matrix.mulVec (U'' : Matrix ι ι ℂ)) := by
      funext v
      have h := hU'' (fun a => v (e.symm a))
      have h2 : (fun a : ι => (fun b : κ => v (e.symm b)) (e.symm.symm a)) = v := by
        funext a; simp
      rw [h2] at h
      simp only [Function.comp]
      rw [h]
      funext a
      simp
    rw [this, ← Measure.map_map hR hm'', hinv U'']

private lemma s9dSphere_spec (ι : Type) [Fintype ι] [Nonempty ι] :
    ∃ P0 : Measure (Fin (Fintype.card ι) → ℂ), IsProbabilityMeasure P0 ∧
      P0 {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 ∧
      (∀ U : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ,
        P0.map (Matrix.mulVec (U : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)) = P0) ∧
      s9dSphere ι = P0.map (fun (w : Fin (Fintype.card ι) → ℂ) (i : ι) =>
        w (Fintype.equivFin ι i)) := by
  have hk : 1 ≤ Fintype.card ι := Fintype.card_pos
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (ext_sphere_measure_exists (Fintype.card ι) hk)
  refine ⟨Classical.choose (ext_sphere_measure_exists (Fintype.card ι) hk), h1, h2, h3, ?_⟩
  unfold s9dSphere
  rw [dif_pos hk]

variable (ι : Type) [Fintype ι] [Nonempty ι]

private lemma s9dSphere_transported [DecidableEq ι] :
    IsProbabilityMeasure (s9dSphere ι) ∧ s9dSphere ι {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 ∧
      ∀ U : Matrix.unitaryGroup ι ℂ,
        (s9dSphere ι).map (Matrix.mulVec (U : Matrix ι ι ℂ)) = s9dSphere ι := by
  obtain ⟨P0, h1, h2, h3, h4⟩ := s9dSphere_spec ι
  rw [h4]
  exact s9d_transport (Fintype.equivFin ι).symm P0 h1 h2 h3

theorem s9dSphere_isProb : IsProbabilityMeasure (s9dSphere ι) := by
  classical
  exact (s9dSphere_transported ι).1

theorem s9dSphere_ae_sphere : s9dSphere ι {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 := by
  classical
  exact (s9dSphere_transported ι).2.1

theorem s9dSphere_invariant [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    (s9dSphere ι).map (Matrix.mulVec (U : Matrix ι ι ℂ)) = s9dSphere ι :=
  (s9dSphere_transported ι).2.2 U

/-- certificate that `s9dSphere` is THE uniform measure: the unique unitarily invariant probability
measure on the sphere (transport of `ext_sphere_measure_unique`). -/
theorem s9dSphere_unique [DecidableEq ι] (P : Measure (ι → ℂ)) (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup ι ℂ, P.map (Matrix.mulVec (U : Matrix ι ι ℂ)) = P) :
    P = s9dSphere ι := by
  obtain ⟨P0, h1, h2, h3, h4⟩ := s9dSphere_spec ι
  obtain ⟨q1, q2, q3⟩ := s9d_transport (Fintype.equivFin ι) P hP hsph hinv
  have hQ := ext_sphere_measure_unique (Fintype.card ι) _ P0 q1 q2 q3 h1 h2 h3
  have hΦ : Measurable (fun (w : Fin (Fintype.card ι) → ℂ) (i : ι) => w (Fintype.equivFin ι i)) :=
    measurable_pi_iff.2 (fun _ => measurable_pi_apply _)
  rw [h4, ← hQ, Measure.map_map hΦ (s9d_meas_reindex (Fintype.equivFin ι))]
  have : ((fun (w : Fin (Fintype.card ι) → ℂ) (i : ι) => w (Fintype.equivFin ι i)) ∘
      (fun (v : ι → ℂ) (a : Fin (Fintype.card ι)) => v ((Fintype.equivFin ι).symm a))) = id := by
    funext v i
    simp
  rw [this, Measure.map_id]

private lemma s9dSphere_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℂ) → E} (hf : Continuous f) :
    ∃ P0 : Measure (Fin (Fintype.card ι) → ℂ), IsProbabilityMeasure P0 ∧
      P0 {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 ∧
      (∀ U : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ,
        P0.map (Matrix.mulVec (U : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)) = P0) ∧
      ∫ w, f w ∂(s9dSphere ι) =
        ∫ w, f (fun i => w (Fintype.equivFin ι i)) ∂P0 := by
  obtain ⟨P0, h1, h2, h3, h4⟩ := s9dSphere_spec ι
  refine ⟨P0, h1, h2, h3, ?_⟩
  rw [h4]
  exact integral_map (measurable_pi_iff.2 (fun _ => measurable_pi_apply _)).aemeasurable
    hf.aestronglyMeasurable

theorem s9dSphere_moment2 (i : ι) :
    ∫ w, ‖w i‖ ^ 2 ∂(s9dSphere ι) = 1 / (Fintype.card ι : ℝ) := by
  obtain ⟨P0, h1, h2, h3, h4⟩ := s9dSphere_integral ι (f := fun w => ‖w i‖ ^ 2) (by fun_prop)
  rw [h4]
  exact ext_sphere_second_moment (Fintype.card ι) Fintype.card_pos P0 h1 h2 h3
    (Fintype.equivFin ι i)

theorem s9dSphere_moment4_offdiag (i j : ι) (hij : i ≠ j) :
    ∫ w, ‖w i‖ ^ 2 * ‖w j‖ ^ 2 ∂(s9dSphere ι) =
      1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) := by
  obtain ⟨P0, h1, h2, h3, h4⟩ :=
    s9dSphere_integral ι (f := fun w => ‖w i‖ ^ 2 * ‖w j‖ ^ 2) (by fun_prop)
  rw [h4]
  have hne : Fintype.equivFin ι i ≠ Fintype.equivFin ι j := fun h => hij ((Fintype.equivFin ι).injective h)
  rw [ext_sphere_fourth_moment_exact (Fintype.card ι) Fintype.card_pos P0 h1 h2 h3
    (Fintype.equivFin ι i) (Fintype.equivFin ι j)]
  simp [hne]

theorem s9dSphere_moment4_diag (i : ι) :
    ∫ w, ‖w i‖ ^ 4 ∂(s9dSphere ι) = 2 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1)) := by
  obtain ⟨P0, h1, h2, h3, h4⟩ :=
    s9dSphere_integral ι (f := fun w => ‖w i‖ ^ 4) (by fun_prop)
  rw [h4]
  have := ext_sphere_fourth_moment_exact (Fintype.card ι) Fintype.card_pos P0 h1 h2 h3
    (Fintype.equivFin ι i) (Fintype.equivFin ι i)
  simp only [ite_true] at this
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  ring

/-- phase invariance: an unbalanced monomial has expectation `0`. -/
theorem s9dSphere_phase_vanish (a b : ι → ℕ) (hab : a ≠ b) :
    ∫ w, ∏ i, w i ^ a i * (starRingEnd ℂ (w i)) ^ b i ∂(s9dSphere ι) = 0 := by
  obtain ⟨P0, h1, h2, h3, h4⟩ := s9dSphere_integral ι
    (f := fun w => ∏ i, w i ^ a i * (starRingEnd ℂ (w i)) ^ b i) (by fun_prop)
  rw [h4]
  have hab' : (fun x => a ((Fintype.equivFin ι).symm x)) ≠ (fun x => b ((Fintype.equivFin ι).symm x)) := by
    intro h
    apply hab
    funext i
    have := congrFun h (Fintype.equivFin ι i)
    simpa using this
  have key := ext_sphere_unbalanced_moment_zero (Fintype.card ι) P0 h1 h2 h3 _ _ hab'
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [← Equiv.prod_comp (Fintype.equivFin ι)
    (fun x => w x ^ a ((Fintype.equivFin ι).symm x) *
      (starRingEnd ℂ (w x)) ^ b ((Fintype.equivFin ι).symm x))]
  simp

end S9dSphere

end TrackB
end RestrictedPolynomials
end
