module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import RestrictedPolynomials.Dimitrov.Fekete
public import Mathlib.Data.Finset.Sort
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Reduction to a star (Supplement C, section 7, "Reduction")

Source: Supplement C, section 7 (assembly), paragraph "Reduction".

For `V ≠ 0` with all `‖v‖ ≤ R` and `0 < d(K(V))`, the hedgehog `K(V)` is contained in a star
`spikes R θ` with `N` distinct, sorted directions (the arguments of the nonzero `v`), where
`N ≤ card V`. The hypothesis `0 < d(K(V))` excludes the case where all `v` vanish, because then
`K(V) ⊆ {0}` and `d_2 = 0`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace RestrictedPolynomials

/-- The star `spikes R θ` is compact (finite union of segments). -/
theorem isCompact_spikes {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) : IsCompact (spikes R θ) := by
  unfold spikes
  refine isCompact_iUnion fun k => ?_
  rw [segment_eq_image']
  exact (isCompact_Icc).image (by fun_prop)

theorem spikes_subset_closedBall {N : ℕ} {R : ℝ} (hR : 0 ≤ R) (θ : Fin N → ℝ) :
    spikes R θ ⊆ Metric.closedBall 0 R := by
  unfold spikes
  refine Set.iUnion_subset fun k => ?_
  refine (convex_closedBall (0 : ℂ) R).segment_subset (by simpa using hR) ?_
  simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hR]

/-- If all the `v ∈ V` vanish, the transfinite diameter of the hedgehog is `0`. -/
lemma transfiniteDiameter_hedgehog_eq_zero {V : Multiset ℂ} (h : ∀ v ∈ V, v = 0) :
    transfiniteDiameter (hedgehog V) = 0 := by
  have hsub : hedgehog V ⊆ {0} := by
    intro x hx
    simp only [hedgehog, Set.mem_iUnion] at hx
    obtain ⟨v, hv, hx⟩ := hx
    rw [h v hv] at hx
    simpa using hx
  have hδ : feketeDelta 2 (hedgehog V) = 0 := by
    refine le_antisymm ?_ (feketeDelta_nonneg _ _)
    unfold feketeDelta
    refine Real.sSup_le ?_ le_rfl
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : ∀ i, z i = 0 := fun i => by simpa using hsub (hz i (Set.mem_univ i))
    have : vandermondeNorm z = 0 := by
      unfold vandermondeNorm
      refine Finset.prod_eq_zero (i := ((0 : Fin 2), (1 : Fin 2))) (by simp) ?_
      simp [hz0]
    exact this.le
  refine le_antisymm ?_ (Real.iInf_nonneg fun m => feketeDiam_nonneg _ _)
  refine (ciInf_le (bddBelow_feketeDiam _) ⟨2, le_rfl⟩).trans ?_
  show feketeDiam 2 (hedgehog V) ≤ 0
  unfold feketeDiam
  rw [hδ]
  norm_num

/-- [Supplement C, §7, Reduction] -/
theorem exists_spikes_reduction (V : Multiset ℂ) (hV : V ≠ 0) {R : ℝ} (hR : ∀ v ∈ V, ‖v‖ ≤ R)
    (hd : 0 < transfiniteDiameter (hedgehog V)) :
    0 < R ∧ ∃ (N : ℕ) (θ : Fin N → ℝ), 1 ≤ N ∧ N ≤ Multiset.card V ∧ StrictMono θ ∧
      (∀ j k, θ k < θ j + 2 * Real.pi) ∧ hedgehog V ⊆ spikes R θ := by
  classical
  -- some element is nonzero
  have hex : ∃ v ∈ V, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd.ne' (transfiniteDiameter_hedgehog_eq_zero hcon)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := hex
  have hRpos : 0 < R := lt_of_lt_of_le (norm_pos_iff.2 hv₀ne) (hR v₀ hv₀)
  refine ⟨hRpos, ?_⟩
  set D : Finset ℝ := (V.toFinset.filter (fun v => v ≠ 0)).image Complex.arg with hD
  have hDne : D.Nonempty :=
    ⟨Complex.arg v₀, Finset.mem_image.2 ⟨v₀, by simp [hv₀, hv₀ne], rfl⟩⟩
  have hcard1 : 1 ≤ D.card := Finset.card_pos.2 hDne
  have hcardle : D.card ≤ Multiset.card V :=
    (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (Multiset.toFinset_card_le V)
  set θ : Fin D.card → ℝ := fun k => D.orderEmbOfFin rfl k with hθ
  have hθmem : ∀ k, θ k ∈ D := fun k => D.orderEmbOfFin_mem rfl k
  have hargD : ∀ k, θ k ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro k
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 (hθmem k)
    rw [← hv]
    exact ⟨Complex.neg_pi_lt_arg v, Complex.arg_le_pi v⟩
  refine ⟨D.card, θ, hcard1, hcardle, (D.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro j k
    linarith [(hargD k).2, (hargD j).1]
  · intro p hp
    simp only [hedgehog, Set.mem_iUnion] at hp
    obtain ⟨v, hv, hp⟩ := hp
    simp only [spikes, Set.mem_iUnion]
    by_cases hv0 : v = 0
    · subst hv0
      have hp0 : p = 0 := by simpa using hp
      refine ⟨⟨0, hcard1⟩, ?_⟩
      rw [hp0]
      exact left_mem_segment ℝ _ _
    · have harg : Complex.arg v ∈ D :=
        Finset.mem_image.2 ⟨v, by simp [hv, hv0], rfl⟩
      have hrange : Complex.arg v ∈ Set.range (D.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact harg
      obtain ⟨k, hk⟩ := hrange
      refine ⟨k, ?_⟩
      have hθk : θ k = Complex.arg v := hk
      set w : ℂ := (R : ℂ) * Complex.exp ((θ k : ℂ) * Complex.I) with hw
      have hvw : v ∈ segment ℝ (0 : ℂ) w := by
        have ht0 : 0 ≤ ‖v‖ / R := by positivity
        have ht1 : ‖v‖ / R ≤ 1 := (div_le_one hRpos).2 (hR v hv)
        refine ⟨1 - ‖v‖ / R, ‖v‖ / R, by linarith, ht0, by ring, ?_⟩
        rw [hw, hθk]
        have := Complex.norm_mul_exp_arg_mul_I v
        simp only [smul_zero, zero_add, Complex.real_smul]
        have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
        conv_rhs => rw [← this]
        push_cast
        field_simp
      exact ((convex_segment (0 : ℂ) w).segment_subset (left_mem_segment ℝ _ _) hvw) hp

end RestrictedPolynomials
