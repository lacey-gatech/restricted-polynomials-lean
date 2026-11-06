module

public import RestrictedPolynomials.TrackB.S9DeltaCoeff
public import RestrictedPolynomials.TrackB.S9DeltaForms

/-!
# Paper IV, Section 9: the random perturbation, bounds on `p` and the variance contradiction

The part following `S9DeltaCoeff`: Claims
9.10, 9.12, 9.13, the variance decomposition, the three cases of Lemma 9.15 by the exact moments of
`S9DeltaForms`, and the numeric core of the variance contradiction.
-/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### the random perturbation: bounds on `p` -/

section S9dP
variable {ιR ιS ιT : Type} [Fintype ιR] [Fintype ιS] [Fintype ιT]

private instance s9dN_sphere_prob (ι : Type) [Fintype ι] [Nonempty ι] :
    IsProbabilityMeasure (s9dSphere ι) := s9dSphere_isProb ι

private instance s9dN_pair_prob [Nonempty ιR] [Nonempty ιS] : IsProbabilityMeasure (s9dPair ιR ιS) := by
  unfold s9dPair
  infer_instance

private lemma s9dN_ae_pair [Nonempty ιR] [Nonempty ιS] :
    ∀ᵐ x ∂(s9dPair ιR ιS), ∑ r, ‖x.1 r‖ ^ 2 = 1 ∧ ∑ s, ‖x.2 s‖ ^ 2 = 1 := by
  have h1 : ∀ᵐ w ∂(s9dSphere ιR), w ∈ {w : ιR → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} :=
    MeasureTheory.ae_iff.2 (s9dSphere_ae_sphere ιR)
  have h2 : ∀ᵐ w ∂(s9dSphere ιS), w ∈ {w : ιS → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} :=
    MeasureTheory.ae_iff.2 (s9dSphere_ae_sphere ιS)
  unfold s9dPair
  have a1 := (Measure.quasiMeasurePreserving_fst (μ := s9dSphere ιR) (ν := s9dSphere ιS)).ae h1
  have a2 := (Measure.quasiMeasurePreserving_snd (μ := s9dSphere ιR) (ν := s9dSphere ιS)).ae h2
  exact a1.and a2

private lemma s9dN_var_nonneg {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) :
    0 ≤ s9dVar P f := by
  unfold s9dVar
  exact integral_nonneg fun x => sq_nonneg _

private lemma s9dN_var_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) {B : ℝ} (h : ∀ᵐ x ∂P, 0 ≤ f x ∧ f x ≤ B) :
    s9dVar P f ≤ B ^ 2 - (∫ x, f x ∂P) ^ 2 := by
  have hint : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable B
      (h.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2)
  have hint2 : Integrable (fun x => f x ^ 2) P :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (B ^ 2)
      (h.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ hx.1 hx.2 2)
  set E := ∫ x, f x ∂P with hE
  have h2 : ∫ x, f x ^ 2 ∂P ≤ B ^ 2 := by
    have := integral_mono_ae hint2 (integrable_const (B ^ 2))
      (h.mono fun x hx => pow_le_pow_left₀ hx.1 hx.2 2)
    simpa using this
  have hexp : ∫ x, (f x - E) ^ 2 ∂P = ∫ x, f x ^ 2 ∂P - E ^ 2 := by
    have e : ∀ x, (f x - E) ^ 2 = f x ^ 2 - 2 * E * f x + E ^ 2 := fun x => by ring
    have i3 : Integrable (fun x => 2 * E * f x) P := hint.const_mul _
    have i4 : Integrable (fun x => f x ^ 2 - 2 * E * f x) P := hint2.sub i3
    simp_rw [e]
    have := integral_add i4 (integrable_const (E ^ 2) : Integrable (fun _ : Ω => E ^ 2) P)
    rw [this, integral_sub hint2 i3, integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, smul_eq_mul]
    rw [← hE]
    ring
  unfold s9dVar
  rw [← hE, hexp]
  linarith

/-- Paper IV `claim:pointwise-bd-p` (Claim 9.10, l. 5524-5530): `p ≤ δ'² M₁M₂ ≤ δ'²` for every `(π, θ)` of
eq. `delta_3` (the unit vectors `w`, `v`). `hV` is the definition of `δ_{n-1,d'-1}` applied to
`F̃ = ∑ conj(c_t) F_t / ‖·‖ ∈ F_{n-1,d'-1}` (`s9d_level_bounds_a`). -/
theorem s9d_pointwise_bd_p (M1 M2 δ' : ℝ) (V : ιR → ιS → ιT → ℂ)
    (hV : ∀ (a : ιR → ℂ) (b : ιS → ℂ), ∑ t, ‖∑ r, ∑ s, a r * b s * V r s t‖ ^ 2 ≤
      δ' ^ 2 * (∑ r, ‖a r‖ ^ 2) * ∑ s, ‖b s‖ ^ 2)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM12 : M1 * M2 ≤ 1) (w : ιR → ℂ) (v : ιS → ℂ)
    (hw : ∑ r, ‖w r‖ ^ 2 = 1) (hv : ∑ s, ‖v s‖ ^ 2 = 1) :
    s9dP M1 M2 V w v ≤ M1 * M2 * δ' ^ 2 ∧ s9dP M1 M2 V w v ≤ δ' ^ 2 := by
  have h := hV w v
  rw [hw, hv] at h
  have h' : ∑ t, ‖∑ r, ∑ s, w r * v s * V r s t‖ ^ 2 ≤ δ' ^ 2 := by simpa using h
  have h1 : s9dP M1 M2 V w v ≤ M1 * M2 * δ' ^ 2 := by
    unfold s9dP
    exact mul_le_mul_of_nonneg_left h' (mul_nonneg hM1 hM2)
  exact ⟨h1, h1.trans (mul_le_of_le_one_left (sq_nonneg δ') hM12)⟩

variable [DecidableEq ιR] [DecidableEq ιS] [Nonempty ιR] [Nonempty ιS]

private lemma s9dN_sqrt_facts {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    0 ≤ Real.sqrt ζ ∧ Real.sqrt ζ ≤ 1 ∧ Real.sqrt ζ ^ 2 = ζ := by
  refine ⟨Real.sqrt_nonneg _, ?_, Real.sq_sqrt hζ⟩
  rw [Real.sqrt_le_one]
  exact hζ1

/-- the expectation of `p`, as a lower bound: `M₁M₂ (1-√ζ) δ'² ≤ 𝔼 p ≤ M₁M₂ δ'²`. -/
private lemma s9dN_expect_bounds (M1 M2 δ' a : ℝ) (V : ιR → ιS → ιT → ℂ) (hM : 0 ≤ M1 * M2)
    (hup : ∀ r s, ∑ t, ‖V r s t‖ ^ 2 ≤ δ' ^ 2)
    (hlow : ∀ r s, (1 - a) * δ' ^ 2 ≤ ∑ t, ‖V r s t‖ ^ 2) :
    M1 * M2 * ((1 - a) * δ' ^ 2) ≤ ∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS) ∧
      ∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS) ≤ M1 * M2 * δ' ^ 2 := by
  rw [s9d_expect_P]
  have hk1 : (0 : ℝ) < Fintype.card ιR := by exact_mod_cast Fintype.card_pos
  have hk2 : (0 : ℝ) < Fintype.card ιS := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < (Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ) := mul_pos hk1 hk2
  have hlo : (Fintype.card ιR : ℝ) * Fintype.card ιS * ((1 - a) * δ' ^ 2) ≤
      ∑ r, ∑ s, ∑ t, ‖V r s t‖ ^ 2 := by
    calc _ = ∑ r : ιR, ∑ s : ιS, (1 - a) * δ' ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hlow r s
  have hhi : ∑ r, ∑ s, ∑ t, ‖V r s t‖ ^ 2 ≤ (Fintype.card ιR : ℝ) * Fintype.card ιS * δ' ^ 2 := by
    calc _ ≤ ∑ r : ιR, ∑ s : ιS, δ' ^ 2 :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hup r s
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hdiv : 0 ≤ M1 * M2 / ((Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ)) := div_nonneg hM hk.le
  constructor
  · calc M1 * M2 * ((1 - a) * δ' ^ 2)
        = M1 * M2 / ((Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ)) *
          ((Fintype.card ιR : ℝ) * Fintype.card ιS * ((1 - a) * δ' ^ 2)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hdiv
  · calc M1 * M2 / ((Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ)) * ∑ r, ∑ s, ∑ t, ‖V r s t‖ ^ 2
        ≤ M1 * M2 / ((Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ)) *
          ((Fintype.card ιR : ℝ) * Fintype.card ιS * δ' ^ 2) := mul_le_mul_of_nonneg_left hhi hdiv
      _ = M1 * M2 * δ' ^ 2 := by field_simp

/-- Paper IV `claim:bound-expectation` (Claim 9.12, l. 5567-5597): `𝔼 p ≥ δ'²(1 - 3√ζ)`, from `𝔼 p =
(M₁M₂/(k₁k₂)) ∑ ‖V_{r,s}‖²` (`s9d_expect_P`), Claim 9.11 and `M₁, M₂ ≥ 1 - ζ`. (The printed
"`∑_{r ∈ T∖T'}`" is `R ∖ R'`, and the stray "`0·𝔼 θθ'`" is dropped.) -/
theorem s9d_bound_expectation (M1 M2 δ' ζ : ℝ) (V : ιR → ιS → ιT → ℂ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hM1 : 1 - ζ ≤ M1) (hM2 : 1 - ζ ≤ M2)
    (hlow : ∀ r s, (1 - Real.sqrt ζ) * δ' ^ 2 ≤ ∑ t, ‖V r s t‖ ^ 2) :
    δ' ^ 2 * (1 - 3 * Real.sqrt ζ) ≤ ∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS) := by
  obtain ⟨ha0, ha1, ha2⟩ := s9dN_sqrt_facts hζ hζ1
  set a := Real.sqrt ζ with ha
  have hz0 : 0 ≤ 1 - ζ := by linarith
  have hM1' : 0 ≤ M1 := hz0.trans hM1
  have hM2' : 0 ≤ M2 := hz0.trans hM2
  have hM : 0 ≤ M1 * M2 := mul_nonneg hM1' hM2'
  have hprod : (1 - ζ) * (1 - ζ) ≤ M1 * M2 := mul_le_mul hM1 hM2 hz0 hM1'
  have hlo : M1 * M2 * ((1 - a) * δ' ^ 2) ≤ ∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS) := by
    rw [s9d_expect_P]
    have hk1 : (0 : ℝ) < Fintype.card ιR := by exact_mod_cast Fintype.card_pos
    have hk2 : (0 : ℝ) < Fintype.card ιS := by exact_mod_cast Fintype.card_pos
    have hk : (0 : ℝ) < (Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ) := mul_pos hk1 hk2
    have hlo : (Fintype.card ιR : ℝ) * Fintype.card ιS * ((1 - a) * δ' ^ 2) ≤
        ∑ r, ∑ s, ∑ t, ‖V r s t‖ ^ 2 := by
      calc _ = ∑ r : ιR, ∑ s : ιS, (1 - a) * δ' ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hlow r s
    calc M1 * M2 * ((1 - a) * δ' ^ 2)
        = M1 * M2 / ((Fintype.card ιR : ℝ) * (Fintype.card ιS : ℝ)) *
          ((Fintype.card ιR : ℝ) * Fintype.card ιS * ((1 - a) * δ' ^ 2)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (div_nonneg hM hk.le)
  refine le_trans ?_ hlo
  have h1 : (1 - a) * (1 - a) ≤ (1 - ζ) * (1 - ζ) := by
    have : a ^ 2 ≤ a := by nlinarith
    have h1a : 0 ≤ 1 - a := by linarith
    nlinarith
  have h2 : 1 - 3 * a ≤ M1 * M2 * (1 - a) := by
    have h3 : (1 - a) * (1 - a) * (1 - a) ≤ M1 * M2 * (1 - a) :=
      mul_le_mul_of_nonneg_right (h1.trans hprod) (by linarith)
    nlinarith [mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ 3 - a)]
  nlinarith [sq_nonneg δ']

/-- Paper IV `claim:p-var-ub` (Claim 9.13, l. 5600-5612): `var p ≤ δ'⁴ - δ'⁴(1 - 3√ζ)² ≤ 6√ζ δ'⁴`,
from `0 ≤ p ≤ δ'²` (Claim 9.10) and `𝔼 p ≥ δ'²(1 - 3√ζ) ≥ 0` (Claim 9.12; `3√ζ ≤ 1` is the implicit
requirement of the printed squaring). -/
theorem s9d_p_var_ub (M1 M2 δ' ζ : ℝ) (V : ιR → ιS → ιT → ℂ)
    (hV : ∀ (a : ιR → ℂ) (b : ιS → ℂ), ∑ t, ‖∑ r, ∑ s, a r * b s * V r s t‖ ^ 2 ≤
      δ' ^ 2 * (∑ r, ‖a r‖ ^ 2) * ∑ s, ‖b s‖ ^ 2)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM12 : M1 * M2 ≤ 1) (hζ : 0 ≤ ζ) (h3 : 3 * Real.sqrt ζ ≤ 1)
    (hE : δ' ^ 2 * (1 - 3 * Real.sqrt ζ) ≤ ∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS)) :
    s9dVar (s9dPair ιR ιS) (fun x => s9dP M1 M2 V x.1 x.2) ≤
        δ' ^ 4 - δ' ^ 4 * (1 - 3 * Real.sqrt ζ) ^ 2 ∧
      s9dVar (s9dPair ιR ιS) (fun x => s9dP M1 M2 V x.1 x.2) ≤ 6 * Real.sqrt ζ * δ' ^ 4 := by
  have hcont : Continuous fun x : (ιR → ℂ) × (ιS → ℂ) => s9dP M1 M2 V x.1 x.2 := by
    simp only [s9dP]; fun_prop
  have hae : ∀ᵐ x ∂(s9dPair ιR ιS), 0 ≤ s9dP M1 M2 V x.1 x.2 ∧ s9dP M1 M2 V x.1 x.2 ≤ δ' ^ 2 := by
    filter_upwards [s9dN_ae_pair (ιR := ιR) (ιS := ιS)] with x hx
    refine ⟨?_, (s9d_pointwise_bd_p M1 M2 δ' V hV hM1 hM2 hM12 x.1 x.2 hx.1 hx.2).2⟩
    unfold s9dP
    exact mul_nonneg (mul_nonneg hM1 hM2) (Finset.sum_nonneg fun t _ => sq_nonneg _)
  have hv := s9dN_var_le (s9dPair ιR ιS) _ hcont.measurable hae
  set a := Real.sqrt ζ with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ζ := Real.sq_sqrt hζ
  have he0 : 0 ≤ δ' ^ 2 * (1 - 3 * a) := mul_nonneg (sq_nonneg _) (by linarith)
  have hE2 : (δ' ^ 2 * (1 - 3 * a)) ^ 2 ≤ (∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS)) ^ 2 :=
    pow_le_pow_left₀ he0 hE 2
  constructor
  · nlinarith
  · nlinarith [mul_nonneg (sq_nonneg (δ' ^ 2)) (sq_nonneg a)]

/-- Paper IV `lem:delta-inductive#variance-decomposition` (l. 5614-5673), repaired. (i) `|𝔼 p - p_4| ≤
√ζ δ'²` for every `(π, θ)`: `p_4` and `𝔼 p = 𝔼 p_4` both lie in `[(1-√ζ)δ'² M₁M₂, δ'² M₁M₂]`
(the printed derivation, l. 5629-5632, treats `𝔼 p` as `δ'² ∑ κ²ρ²|π|²|θ|²` and is not valid as
written: a gap in the source). (iii) the cross terms vanish exactly and `p_off ⟂ (p_4 - 𝔼 p)`, so
`𝔼|p_1|² + 𝔼|p_2|² + 𝔼|p_3|² ≤ var p` with NO `O(√ζ)` loss (strengthens eq. `delta_5`, `delta_6`:
`s9d_var_P_decomp`, `s9d_expect_pOff_sq`). -/
theorem s9d_variance_decomposition (M1 M2 δ' ζ : ℝ) (V : ιR → ιS → ιT → ℂ) (hζ : 0 ≤ ζ)
    (hM1 : 0 ≤ M1) (hM1' : M1 ≤ 1) (hM2 : 0 ≤ M2) (hM2' : M2 ≤ 1)
    (hup : ∀ r s, ∑ t, ‖V r s t‖ ^ 2 ≤ δ' ^ 2)
    (hlow : ∀ r s, (1 - Real.sqrt ζ) * δ' ^ 2 ≤ ∑ t, ‖V r s t‖ ^ 2) :
    (∀ (w : ιR → ℂ) (v : ιS → ℂ), ∑ r, ‖w r‖ ^ 2 = 1 → ∑ s, ‖v s‖ ^ 2 = 1 →
      |(∫ x, s9dP M1 M2 V x.1 x.2 ∂(s9dPair ιR ιS)) - s9dP4 M1 M2 V w v| ≤ Real.sqrt ζ * δ' ^ 2) ∧
    (∫ x, ‖s9dP1 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) +
        ∫ x, ‖s9dP2 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) +
        ∫ x, ‖s9dP3 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) ≤
      s9dVar (s9dPair ιR ιS) (fun x => s9dP M1 M2 V x.1 x.2)) := by
  constructor
  · intro w v hw hv
    have hM : 0 ≤ M1 * M2 := mul_nonneg hM1 hM2
    have hM12 : M1 * M2 ≤ 1 := mul_le_one₀ hM1' hM2 hM2'
    set a := Real.sqrt ζ with ha
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    obtain ⟨hEl, hEu⟩ := s9dN_expect_bounds M1 M2 δ' a V hM hup hlow
    -- the diagonal part
    have hw1 : ∀ L : ℝ, ∑ r, ∑ s, ‖w r‖ ^ 2 * ‖v s‖ ^ 2 * L = L := by
      intro L
      calc ∑ r, ∑ s, ‖w r‖ ^ 2 * ‖v s‖ ^ 2 * L
          = (∑ r, ‖w r‖ ^ 2) * (∑ s, ‖v s‖ ^ 2) * L := by
            rw [Finset.sum_mul_sum, Finset.sum_mul]; simp_rw [Finset.sum_mul]
        _ = L := by rw [hw, hv]; ring
    have hP4l : M1 * M2 * ((1 - a) * δ' ^ 2) ≤ s9dP4 M1 M2 V w v := by
      unfold s9dP4
      refine mul_le_mul_of_nonneg_left ?_ hM
      rw [← hw1 ((1 - a) * δ' ^ 2)]
      exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (hlow r s) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hP4u : s9dP4 M1 M2 V w v ≤ M1 * M2 * δ' ^ 2 := by
      unfold s9dP4
      refine mul_le_mul_of_nonneg_left ?_ hM
      rw [← hw1 (δ' ^ 2)]
      exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (hup r s) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [abs_le]
    have hd : M1 * M2 * (a * δ' ^ 2) ≤ a * δ' ^ 2 :=
      mul_le_of_le_one_left (mul_nonneg ha0 (sq_nonneg _)) hM12
    constructor <;> nlinarith
  · have h1 := s9d_var_P_decomp M1 M2 V
    have h2 := s9d_expect_pOff_sq M1 M2 V
    have h3 := s9dN_var_nonneg (s9dPair ιR ιS) (fun x => s9dP4 M1 M2 V x.1 x.2)
    linarith

/-- Paper IV `lem:lb-var-p#case-r-and-s-differ` (l. 5694-5734): for `r ≠ r'`, `s ≠ s'` with
`|⟨V_{r,s}, V_{r',s'}⟩| ≥ c δ'²`, `𝔼|p_3|² ≥ c₀ (cδ'²)²` with `c₀ = (M₁M₂)²/(k₁(k₁+1)k₂(k₂+1))`. (The
printed `τ⁸` factor comes from writing `a_r = κ_rπ_r` in the moduli: in the variables `w, v` the
weights are absent; the printed index pairing of `p_3` is corrected.) -/
theorem s9d_lb_case_r_and_s_differ (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (r r' : ιR) (s s' : ιS)
    (hr : r ≠ r') (hs : s ≠ s') {c δ' : ℝ} (hc : 0 ≤ c)
    (hG : c * δ' ^ 2 ≤ ‖s9dGram V r s r' s'‖) :
    (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) * (c * δ' ^ 2) ^ 2 ≤
      ∫ x, ‖s9dP3 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) := by
  rw [s9d_expect_p3_sq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcd : 0 ≤ c * δ' ^ 2 := mul_nonneg hc (sq_nonneg _)
  refine (pow_le_pow_left₀ hcd hG 2).trans ?_
  have h1 : ∀ r₀ r₁ : ιR, ∀ s₀ s₁ : ιS, 0 ≤ ‖s9dGram V r₀ s₀ r₁ s₁‖ ^ 2 := fun _ _ _ _ => sq_nonneg _
  refine le_trans ?_ (Finset.single_le_sum (f := fun r₀ => ∑ r₁ ∈ univ.erase r₀, ∑ s₀,
      ∑ s₁ ∈ univ.erase s₀, ‖s9dGram V r₀ s₀ r₁ s₁‖ ^ 2)
    (fun r₀ _ => Finset.sum_nonneg fun r₁ _ => Finset.sum_nonneg fun s₀ _ =>
      Finset.sum_nonneg fun s₁ _ => h1 _ _ _ _) (Finset.mem_univ r))
  refine le_trans ?_ (Finset.single_le_sum (f := fun r₁ => ∑ s₀, ∑ s₁ ∈ univ.erase s₀,
      ‖s9dGram V r s₀ r₁ s₁‖ ^ 2)
    (fun r₁ _ => Finset.sum_nonneg fun s₀ _ => Finset.sum_nonneg fun s₁ _ => h1 _ _ _ _)
    (Finset.mem_erase.2 ⟨hr.symm, Finset.mem_univ r'⟩))
  refine le_trans ?_ (Finset.single_le_sum (f := fun s₀ => ∑ s₁ ∈ univ.erase s₀,
      ‖s9dGram V r s₀ r' s₁‖ ^ 2)
    (fun s₀ _ => Finset.sum_nonneg fun s₁ _ => h1 _ _ _ _) (Finset.mem_univ s))
  exact Finset.single_le_sum (f := fun s₁ => ‖s9dGram V r s r' s₁‖ ^ 2)
    (fun s₁ _ => h1 _ _ _ _) (Finset.mem_erase.2 ⟨hs.symm, Finset.mem_univ s'⟩)

/-- Paper IV `lem:lb-var-p#case-same-r` (l. 5736-5770): for `r = r'`, `s ≠ s'`, `𝔼|p_1|² ≥ c₀ (cδ'²)²`. The
printed concentration event `E` is not used. Its three radii are not compatible unless `1 - M₂` is
`O(c^50/m^50)` (a constraint on `ζ` that (hier2) does not state, so `Pr[E] ≫_{c,m} 1` can fail); the
derived `|κ_rπ_r| ≤ c^50/m^50` should read `≤ (c^50/m^50)^{1/2}`; and a lower bound on `|p_1|` needs
the phase of `θ_s conj(θ_{s'})`, which `E` leaves free (a gap in the source). The exact fourth moments
give `𝔼|p_1|² = c₀ ∑_{s≠s'} (|∑_r G^r_{ss'}|² + ∑_r |G^r_{ss'}|²)` (`s9d_expect_p1_sq`). -/
theorem s9d_lb_case_same_r (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (r : ιR) (s s' : ιS) (hs : s ≠ s')
    {c δ' : ℝ} (hc : 0 ≤ c) (hG : c * δ' ^ 2 ≤ ‖s9dGram V r s r s'‖) :
    (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) * (c * δ' ^ 2) ^ 2 ≤
      ∫ x, ‖s9dP1 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) := by
  rw [s9d_expect_p1_sq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcd : 0 ≤ c * δ' ^ 2 := mul_nonneg hc (sq_nonneg _)
  refine (pow_le_pow_left₀ hcd hG 2).trans ?_
  have h1 : ∀ r₀ : ιR, ∀ s₀ s₁ : ιS, 0 ≤ ‖s9dGram V r₀ s₀ r₀ s₁‖ ^ 2 := fun _ _ _ => sq_nonneg _
  have h2 : ∀ s₀ s₁ : ιS, 0 ≤ ‖∑ r₀, s9dGram V r₀ s₀ r₀ s₁‖ ^ 2 +
      ∑ r₀, ‖s9dGram V r₀ s₀ r₀ s₁‖ ^ 2 := fun s₀ s₁ =>
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun r₀ _ => h1 _ _ _)
  refine le_trans ?_ (Finset.single_le_sum (f := fun s₀ => ∑ s₁ ∈ univ.erase s₀,
      (‖∑ r₀, s9dGram V r₀ s₀ r₀ s₁‖ ^ 2 + ∑ r₀, ‖s9dGram V r₀ s₀ r₀ s₁‖ ^ 2))
    (fun s₀ _ => Finset.sum_nonneg fun s₁ _ => h2 _ _) (Finset.mem_univ s))
  refine le_trans ?_ (Finset.single_le_sum (f := fun s₁ =>
      (‖∑ r₀, s9dGram V r₀ s r₀ s₁‖ ^ 2 + ∑ r₀, ‖s9dGram V r₀ s r₀ s₁‖ ^ 2))
    (fun s₁ _ => h2 _ _) (Finset.mem_erase.2 ⟨hs.symm, Finset.mem_univ s'⟩))
  refine le_trans ?_ (le_add_of_nonneg_left (sq_nonneg _))
  exact Finset.single_le_sum (f := fun r₀ => ‖s9dGram V r₀ s r₀ s'‖ ^ 2)
    (fun r₀ _ => h1 _ _ _) (Finset.mem_univ r)

/-- Paper IV `lem:lb-var-p#case-same-s` (l. 5772-5773, "omitted"): `r ≠ r'`, `s = s'`, with `p_2`. -/
theorem s9d_lb_case_same_s (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (r r' : ιR) (s : ιS) (hr : r ≠ r')
    {c δ' : ℝ} (hc : 0 ≤ c) (hG : c * δ' ^ 2 ≤ ‖s9dGram V r s r' s‖) :
    (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) * (c * δ' ^ 2) ^ 2 ≤
      ∫ x, ‖s9dP2 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) := by
  rw [s9d_expect_p2_sq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcd : 0 ≤ c * δ' ^ 2 := mul_nonneg hc (sq_nonneg _)
  refine (pow_le_pow_left₀ hcd hG 2).trans ?_
  have h1 : ∀ r₀ r₁ : ιR, ∀ s₀ : ιS, 0 ≤ ‖s9dGram V r₀ s₀ r₁ s₀‖ ^ 2 := fun _ _ _ => sq_nonneg _
  have h2 : ∀ r₀ r₁ : ιR, 0 ≤ ‖∑ s₀, s9dGram V r₀ s₀ r₁ s₀‖ ^ 2 +
      ∑ s₀, ‖s9dGram V r₀ s₀ r₁ s₀‖ ^ 2 := fun r₀ r₁ =>
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun s₀ _ => h1 _ _ _)
  refine le_trans ?_ (Finset.single_le_sum (f := fun r₀ => ∑ r₁ ∈ univ.erase r₀,
      (‖∑ s₀, s9dGram V r₀ s₀ r₁ s₀‖ ^ 2 + ∑ s₀, ‖s9dGram V r₀ s₀ r₁ s₀‖ ^ 2))
    (fun r₀ _ => Finset.sum_nonneg fun r₁ _ => h2 _ _) (Finset.mem_univ r))
  refine le_trans ?_ (Finset.single_le_sum (f := fun r₁ =>
      (‖∑ s₀, s9dGram V r s₀ r₁ s₀‖ ^ 2 + ∑ s₀, ‖s9dGram V r s₀ r₁ s₀‖ ^ 2))
    (fun r₁ _ => h2 _ _) (Finset.mem_erase.2 ⟨hr.symm, Finset.mem_univ r'⟩))
  refine le_trans ?_ (le_add_of_nonneg_left (sq_nonneg _))
  exact Finset.single_le_sum (f := fun s₀ => ‖s9dGram V r s₀ r' s₀‖ ^ 2)
    (fun s₀ _ => h1 _ _ _) (Finset.mem_univ s)

/-- Paper IV `lem:lb-var-p` (Lemma 9.15, l. 5688-5774): if some pair `(r,s) ≠ (r',s')` has
`|⟨V_{r,s}, V_{r',s'}⟩| ≥ c δ'²`, then `var p ≥ c₀ (cδ'²)²`: the three cases of the printed proof, each
by the exact moments, joined by the orthogonal decomposition. (No `τ⁹`: the bound is `≥ c₀ c² δ'⁴`
with `c₀ ≥ 1/(16 m²(m+1)²)` for `M₁, M₂ ≥ 1/2`, `k ≤ m`; `τ⁹` is then recovered as `≤` this.) -/
theorem s9d_lb_var_p (M1 M2 : ℝ) (V : ιR → ιS → ιT → ℂ) (r r' : ιR) (s s' : ιS)
    (hne : (r, s) ≠ (r', s')) {c δ' : ℝ} (hc : 0 ≤ c) (hG : c * δ' ^ 2 ≤ ‖s9dGram V r s r' s'‖) :
    (M1 * M2) ^ 2 / (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) * (c * δ' ^ 2) ^ 2 ≤
      s9dVar (s9dPair ιR ιS) (fun x => s9dP M1 M2 V x.1 x.2) := by
  have h1 := s9d_var_P_decomp M1 M2 V
  have h2 := s9d_expect_pOff_sq M1 M2 V
  have h3 := s9dN_var_nonneg (s9dPair ιR ιS) (fun x => s9dP4 M1 M2 V x.1 x.2)
  have n1 : 0 ≤ ∫ x, ‖s9dP1 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) :=
    integral_nonneg fun x => sq_nonneg _
  have n2 : 0 ≤ ∫ x, ‖s9dP2 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) :=
    integral_nonneg fun x => sq_nonneg _
  have n3 : 0 ≤ ∫ x, ‖s9dP3 M1 M2 V x.1 x.2‖ ^ 2 ∂(s9dPair ιR ιS) :=
    integral_nonneg fun x => sq_nonneg _
  rcases eq_or_ne r r' with rfl | hrr
  · have hs : s ≠ s' := fun h => hne (by rw [h])
    have := s9d_lb_case_same_r M1 M2 V r s s' hs hc hG
    linarith
  · rcases eq_or_ne s s' with rfl | hss
    · have := s9d_lb_case_same_s M1 M2 V r r' s hrr hc hG
      linarith
    · have := s9d_lb_case_r_and_s_differ M1 M2 V r r' s s' hrr hss hc hG
      linarith

/-- Paper IV `lem:delta-inductive#variance-contradiction`, numeric core (l. 5776-5778): Claim 9.13 and
Lemma 9.15 are incompatible, if `6√ζ k₁(k₁+1)k₂(k₂+1) < (M₁M₂)² c²` (the printed "`√ζ ≪ τ⁹`", made
explicit; depends on `m` only), unless `δ' = 0`. The degenerate case `δ' = 0` (not treated in the source) is
excluded by `0 < δ'`: for `δ' = 0` every `F̂_t(r,s) = 0` and there is nothing to prove. -/
theorem s9d_variance_contradiction (M1 M2 δ' ζ c : ℝ) (V : ιR → ιS → ιT → ℂ)
    (hV : ∀ (a : ιR → ℂ) (b : ιS → ℂ), ∑ t, ‖∑ r, ∑ s, a r * b s * V r s t‖ ^ 2 ≤
      δ' ^ 2 * (∑ r, ‖a r‖ ^ 2) * ∑ s, ‖b s‖ ^ 2)
    (hδ' : 0 < δ') (hζ : 0 ≤ ζ) (h3 : 3 * Real.sqrt ζ ≤ 1) (hM1 : 1 - ζ ≤ M1) (hM1' : M1 ≤ 1)
    (hM2 : 1 - ζ ≤ M2) (hM2' : M2 ≤ 1)
    (hlow : ∀ r s, (1 - Real.sqrt ζ) * δ' ^ 2 ≤ ∑ t, ‖V r s t‖ ^ 2) (hc : 0 ≤ c)
    (hsmall : 6 * Real.sqrt ζ * (((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
          ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1))) < (M1 * M2) ^ 2 * c ^ 2)
    (r r' : ιR) (s s' : ιS) (hne : (r, s) ≠ (r', s'))
    (hG : c * δ' ^ 2 ≤ ‖s9dGram V r s r' s'‖) : False := by
  have ha0 : 0 ≤ Real.sqrt ζ := Real.sqrt_nonneg _
  have ha2 : Real.sqrt ζ ^ 2 = ζ := Real.sq_sqrt hζ
  have hζ1 : ζ ≤ 1 := by nlinarith
  have hz0 : 0 ≤ 1 - ζ := by linarith
  have hM1n : 0 ≤ M1 := hz0.trans hM1
  have hM2n : 0 ≤ M2 := hz0.trans hM2
  have hM12 : M1 * M2 ≤ 1 := mul_le_one₀ hM1' hM2n hM2'
  have hE := s9d_bound_expectation M1 M2 δ' ζ V hζ hζ1 hM1 hM2 hlow
  have hup := (s9d_p_var_ub M1 M2 δ' ζ V hV hM1n hM2n hM12 hζ h3 hE).2
  have hlb := s9d_lb_var_p M1 M2 V r r' s s' hne hc hG
  have hK : 0 < ((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
      ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1)) := by
    have hk1 : (0 : ℝ) < Fintype.card ιR := by exact_mod_cast Fintype.card_pos
    have hk2 : (0 : ℝ) < Fintype.card ιS := by exact_mod_cast Fintype.card_pos
    positivity
  set K := ((Fintype.card ιR : ℝ) * ((Fintype.card ιR : ℝ) + 1)) *
      ((Fintype.card ιS : ℝ) * ((Fintype.card ιS : ℝ) + 1)) with hKdef
  have h4 : 0 < δ' ^ 4 := by positivity
  have h5 : 6 * Real.sqrt ζ < (M1 * M2) ^ 2 * c ^ 2 / K := by
    rw [lt_div_iff₀ hK]
    exact hsmall
  have h6 : (M1 * M2) ^ 2 / K * (c * δ' ^ 2) ^ 2 = (M1 * M2) ^ 2 * c ^ 2 / K * δ' ^ 4 := by
    ring
  have h7 : 6 * Real.sqrt ζ * δ' ^ 4 < (M1 * M2) ^ 2 * c ^ 2 / K * δ' ^ 4 :=
    mul_lt_mul_of_pos_right h5 h4
  linarith

end S9dP

end TrackB
end RestrictedPolynomials
end
