module

public import RestrictedPolynomials.Dimitrov.DubininReduction
public import RestrictedPolynomials.Dimitrov.DubininEnergy
public import RestrictedPolynomials.Dimitrov.DubininSymTest
public import RestrictedPolynomials.Dimitrov.DubininZigzag
public import RestrictedPolynomials.Dimitrov.DubininPhi

/-!
# Dubinin's hedgehog bound (Supplement C, Theorem thm:main)

Source: Supplement C, §7. The assembly is the limit argument of the Supplement. It combines:
- the reduction to stars;
- the energy lower bound against Fekete points;
- the exact Dirichlet integral of the symmetric test function;
- the zigzag paths;
- the dissymmetrization.

For the Fekete transfinite diameter `d`, it gives `d(K(v_1..v_N)) ≤ R·4^{-1/N}`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace RestrictedPolynomials

/-- [Supplement C, Theorem thm:main] Dubinin's hedgehog bound. -/
theorem transfiniteDiameter_hedgehog_le (V : Multiset ℂ) (hV : V ≠ 0) {R : ℝ} (hR : ∀ v ∈ V, ‖v‖ ≤ R) :
    transfiniteDiameter (hedgehog V) ≤ R * (4 : ℝ) ^ (-(1 / (Multiset.card V : ℝ))) := by
  have hd0 : 0 ≤ transfiniteDiameter (hedgehog V) :=
    Real.iInf_nonneg (fun m => feketeDiam_nonneg _ _)
  obtain ⟨v0, hv0⟩ := Multiset.exists_mem_of_ne_zero hV
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR v0 hv0)
  rcases hd0.eq_or_lt with h | hdpos
  · rw [← h]; positivity
  obtain ⟨hRpos, N, θ, hN1, hNcard, hmono, hlt, hsub⟩ := exists_spikes_reduction V hV hR hdpos
  have hKc := isCompact_spikes R θ
  have hne : (spikes R θ).Nonempty := (hedgehog_nonempty hV).mono hsub
  have hdK : transfiniteDiameter (hedgehog V) ≤ transfiniteDiameter (spikes R θ) :=
    transfiniteDiameter_mono hKc (hedgehog_nonempty hV) hsub
  have hDpos : 0 < transfiniteDiameter (spikes R θ) := lt_of_lt_of_le hdpos hdK
  have hcpos : 0 < starRadius N R := by
    unfold starRadius; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcle : starRadius N R ≤ R * (4 : ℝ) ^ (-(1 / (Multiset.card V : ℝ))) := by
    unfold starRadius
    refine mul_le_mul_of_nonneg_left ?_ hRpos.le
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (N : ℝ) ≤ Multiset.card V := by exact_mod_cast hNcard
    have := one_div_le_one_div_of_le hNpos this
    linarith
  refine hdK.trans (le_trans ?_ hcle)
  have key : ∀ r' α : ℝ, R + starRadius N R < r' → 0 < α →
      α < Real.log ((r' - R) / starRadius N R) →
      transfiniteDiameter (spikes R θ) ≤
        starRadius N R * ((r' + R) / (r' - R)) * Real.exp α := by
    intro r' α hr hα hαβ
    obtain ⟨⟨hopen, hsubO, hone⟩, hzero, ⟨Lu, hLu⟩, hsym, hdir⟩ :=
      symTest_spec hN1 hRpos hr hα hαβ
    obtain ⟨ψ, L, hz⟩ := exists_zigzag hN1 θ hmono hlt
    obtain ⟨⟨Lt, hLt⟩, hOo, hKsub, hone', hzero', hdir'⟩ :=
      dissymmetrization hN1 hz hRpos.le hLu (fun z => (hsym z).1) (fun z => (hsym z).2)
        hopen hsubO hone hzero
    have hrR : R < r' := by linarith
    have hen := energy_lower_bound hKc hne (spikes_subset_closedBall hRpos.le θ) hDpos hrR hLt
      hOo hKsub hone' hzero'
    rw [hdir', hdir] at hen
    set β := Real.log ((r' - R) / starRadius N R) with hβ
    have hβα : 0 < β - α := by linarith
    have h2 : β - α ≤ Real.log (r' + R) - Real.log (transfiniteDiameter (spikes R θ)) := by
      by_contra hh
      push Not at hh
      have h3 : 2 * Real.pi / (β - α) *
          (Real.log (r' + R) - Real.log (transfiniteDiameter (spikes R θ))) <
          2 * Real.pi / (β - α) * (β - α) :=
        mul_lt_mul_of_pos_left hh (by positivity)
      rw [div_mul_cancel₀ _ hβα.ne'] at h3
      linarith
    have hr1 : 0 < r' - R := by linarith
    have hr2 : 0 < r' + R := by linarith
    rw [← Real.log_le_log_iff hDpos (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_div hr2.ne' hr1.ne', Real.log_exp]
    rw [hβ, Real.log_div hr1.ne' hcpos.ne'] at h2
    linarith
  by_contra hcon
  push Not at hcon
  set c := starRadius N R with hcdef
  set D := transfiniteDiameter (spikes R θ) with hDdef
  have ht : 1 < D / c := by rw [lt_div_iff₀ hcpos]; linarith
  set α := Real.log (D / c) / 3 with hαdef
  have hα : 0 < α := by have := Real.log_pos ht; positivity
  set q := Real.exp α with hq
  have hq1 : 1 < q := by have := Real.add_one_lt_exp hα.ne'; linarith
  have hq3 : q ^ 3 = D / c := by
    rw [hq, ← Real.exp_nat_mul, hαdef]
    push_cast
    rw [show (3 : ℝ) * (Real.log (D / c) / 3) = Real.log (D / c) by ring,
      Real.exp_log (by positivity)]
  set s := c * q + 2 * R / (q - 1) + 1 with hs
  have hq1' : 0 < q - 1 := by linarith
  have hs1 : c * q < s := by
    have : 0 ≤ 2 * R / (q - 1) := by positivity
    linarith
  have hs2 : 2 * R ≤ s * (q - 1) := by
    have h1 : 2 * R / (q - 1) * (q - 1) = 2 * R := div_mul_cancel₀ _ hq1'.ne'
    have : 0 ≤ c * q + 1 := by positivity
    nlinarith
  have hcq : c < c * q := by nlinarith
  have hβ : α < Real.log ((R + s - R) / c) := by
    rw [add_sub_cancel_left]
    calc α = Real.log q := by rw [hq, Real.log_exp]
      _ < Real.log (s / c) :=
        Real.log_lt_log (by linarith) (by rw [lt_div_iff₀ hcpos]; linarith [mul_comm c q])
  have hk := key (R + s) α (by linarith) hα hβ
  have hrat : (R + s + R) / (R + s - R) ≤ q := by
    rw [add_sub_cancel_left, div_le_iff₀ (by linarith)]
    nlinarith
  have hq2 : c * ((R + s + R) / (R + s - R)) * Real.exp α ≤ c * q * q := by
    rw [← hq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrat hcpos.le) (by positivity)
  have hfin : c * q * q < c * q ^ 3 := by
    have : 0 < c * q * q := by positivity
    nlinarith [mul_pos hcpos (mul_pos (by linarith : (0:ℝ) < q) hq1')]
  have : c * q ^ 3 = D := by rw [hq3]; field_simp
  linarith

end RestrictedPolynomials
