module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Finset

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section S9dHierarchy

/-- the right side of the final contradiction (l. 5919-5934), explicit: with `ϑ = ζ^{1/4}`,
`υ = (ϑ/c)^{1/C}` (the `var_{Σ_modest}(f'_{r,s}) ≤ υ` of the relaxed base case with constants `(c, C)`),
`e₁ = ϑ + m√(2ϑ)`:
`B = (√(2/α) e₁ + m √υ)² + 2 m η²/α` bounds `∑_t ψ_t² var_{Σ_modest}(f'_t)` (Claim 9.19 for `t ∈ T'`, and
`var ≤ 2/α` with `ψ_t < η` for `t ∉ T'`). -/
def s9dVarBound (m : ℕ) (α c C ζ η : ℝ) : ℝ :=
  (Real.sqrt (2 / α) * (ζ ^ (1 / 4 : ℝ) + m * Real.sqrt (2 * ζ ^ (1 / 4 : ℝ))) +
      m * Real.sqrt ((ζ ^ (1 / 4 : ℝ) / c) ^ (1 / C))) ^ 2 + 2 * m * η ^ 2 / α

/-- Paper IV `claim:separate-out` (Claim 9.8, l. 5379-5390), the pigeonhole part: the intervals
`[lo i, hi i)` (`[η_i, τ_i)`) of the candidate tuples are pairwise disjoint (`hi (i+1) = lo i`, the
printed "`R_1' = R_4`"), so a finite family of at most `N` coefficients misses one of `N + 1` of them.
The source's "at most `3m` iterations" is `N = 3m ≥ |R| + |S| + |T|`. -/
theorem s9d_separate_out {ι : Type} [Fintype ι] (N : ℕ) (hN : Fintype.card ι ≤ N)
    (lo hi : ℕ → ℝ) (hlohi : ∀ i, lo i < hi i) (hchain : ∀ i, hi (i + 1) = lo i) (x : ι → ℝ) :
    ∃ i ≤ N, ∀ q, ¬(lo i ≤ x q ∧ x q < hi i) := by
  classical
  by_contra hcon
  push_neg at hcon
  have : Nonempty ι := by
    obtain ⟨q, _⟩ := hcon 0 (Nat.zero_le _)
    exact ⟨q⟩
  choose! f hf using hcon
  have hanti : ∀ i j, i ≤ j → hi j ≤ hi i := by
    intro i j hij
    refine Nat.le_induction le_rfl (fun n _ ih => ?_) j hij
    have h1 := hchain n
    have h2 := hlohi n
    linarith
  have hinj : Set.InjOn f (↑(Finset.range (N + 1)) : Set ℕ) := by
    have key : ∀ i j, i < j → j ≤ N → f i ≠ f j := by
      intro i j hij hjN heq
      have h1 := (hf i (by omega)).1
      have h2 := (hf j hjN).2
      rw [← heq] at h2
      have h3 := hanti (i + 1) j hij
      have h4 := hchain i
      have h5 := hlohi j
      linarith
    intro i hi' j hj' hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi' hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h (by omega) hij
    · exact key j i h (by omega) hij.symm
  have := Finset.card_le_card_of_injOn f (s := Finset.range (N + 1)) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simp only [Finset.card_range, Finset.card_univ] at this
  omega

private lemma s9dVarBound_le (m : ℕ) {α c C : ℝ} (hα : 0 < α) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ η : ℝ, 0 < ζ → ζ ≤ 1 → 0 ≤ η → η ≤ ζ →
      s9dVarBound m α c C ζ η ≤ K * ζ ^ (1 / (4 + 4 * C)) := by
  set θ : ℝ := 1 / (4 + 4 * C) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ4 : θ ≤ 1 / 4 := by
    rw [hθ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hθC : θ ≤ (1 / 4) * (1 / C) := by
    rw [hθ]; rw [show (1 / 4 : ℝ) * (1 / C) = 1 / (4 * C) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hθ1 : θ ≤ 1 := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨4 / α * (1 + 2 * m) ^ 2 + 2 * m ^ 2 * (1 / c) ^ (1 / C) + 2 * m / α, ?_, ?_⟩
  · positivity
  intro ζ η hζ0 hζ1 hη0 hηζ
  set q : ℝ := ζ ^ θ with hq
  set t : ℝ := ζ ^ (1 / 4 : ℝ) with ht
  have hq0 : 0 < q := Real.rpow_pos_of_pos hζ0 _
  have ht0 : 0 < t := Real.rpow_pos_of_pos hζ0 _
  have htq : t ≤ q := Real.rpow_le_rpow_of_exponent_ge hζ0 hζ1 hθ4
  have ht1 : t ≤ 1 := Real.rpow_le_one hζ0.le hζ1 (by norm_num)
  have hζq : ζ ≤ q := by
    have := Real.rpow_le_rpow_of_exponent_ge hζ0 hζ1 hθ1
    simpa using this
  have hq1 : q ≤ 1 := Real.rpow_le_one hζ0.le hζ1 hθpos.le
  -- υ
  set υ : ℝ := (t / c) ^ (1 / C) with hυ
  have hυ0 : 0 ≤ υ := Real.rpow_nonneg (div_nonneg ht0.le hc.le) _
  have hυq : υ ≤ (1 / c) ^ (1 / C) * q := by
    have e1 : t / c = t * (1 / c) := by ring
    rw [hυ, e1, Real.mul_rpow ht0.le (by positivity), mul_comm]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    rw [ht, ← Real.rpow_mul hζ0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hζ0 hζ1 hθC
  -- e1
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs : Real.sqrt (2 * t) ≤ 2 * Real.sqrt t := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have htle : t ≤ Real.sqrt t := by
    have : Real.sqrt t ≤ 1 := by rw [Real.sqrt_le_one]; exact ht1
    nlinarith [Real.sqrt_nonneg t]
  have he1 : t + m * Real.sqrt (2 * t) ≤ (1 + 2 * m) * Real.sqrt t := by
    have : (m : ℝ) * Real.sqrt (2 * t) ≤ m * (2 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hs hm0
    nlinarith
  have he1sq : (t + m * Real.sqrt (2 * t)) ^ 2 ≤ (1 + 2 * m) ^ 2 * t := by
    have h0 : 0 ≤ t + m * Real.sqrt (2 * t) := by positivity
    calc (t + m * Real.sqrt (2 * t)) ^ 2 ≤ ((1 + 2 * m) * Real.sqrt t) ^ 2 :=
          pow_le_pow_left₀ h0 he1 2
      _ = (1 + 2 * m) ^ 2 * t := by rw [mul_pow, hst]
  have ha : Real.sqrt (2 / α) ^ 2 = 2 / α := Real.sq_sqrt (by positivity)
  have hsυ : Real.sqrt υ ^ 2 = υ := Real.sq_sqrt hυ0
  have hη2 : η ^ 2 ≤ q := by
    have : η ^ 2 ≤ η := by nlinarith
    linarith
  unfold s9dVarBound
  rw [← ht, ← hυ]
  have h1 : (Real.sqrt (2 / α) * (t + m * Real.sqrt (2 * t)) + m * Real.sqrt υ) ^ 2 ≤
      2 * (2 / α) * (1 + 2 * m) ^ 2 * t + 2 * m ^ 2 * υ := by
    have h2 : (Real.sqrt (2 / α) * (t + m * Real.sqrt (2 * t)) + m * Real.sqrt υ) ^ 2 ≤
        2 * (Real.sqrt (2 / α) ^ 2 * (t + m * Real.sqrt (2 * t)) ^ 2) +
          2 * (m ^ 2 * Real.sqrt υ ^ 2) := by
      nlinarith [sq_nonneg (Real.sqrt (2 / α) * (t + m * Real.sqrt (2 * t)) - m * Real.sqrt υ)]
    rw [ha, hsυ] at h2
    have h3 : 2 / α * (t + m * Real.sqrt (2 * t)) ^ 2 ≤ 2 / α * ((1 + 2 * m) ^ 2 * t) :=
      mul_le_mul_of_nonneg_left he1sq (by positivity)
    nlinarith
  have h4 : 2 * m * η ^ 2 / α ≤ 2 * m / α * q := by
    have e : 2 * (m : ℝ) * η ^ 2 / α = 2 * m / α * η ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hη2 (by positivity)
  have h5 : 2 * (2 / α) * (1 + 2 * m) ^ 2 * t ≤ 4 / α * (1 + 2 * m) ^ 2 * q := by
    have : 2 * (2 / α) * (1 + 2 * m) ^ 2 = 4 / α * (1 + 2 * m) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left htq (by positivity)
  have h6 : 2 * (m : ℝ) ^ 2 * υ ≤ 2 * m ^ 2 * ((1 / c) ^ (1 / C) * q) :=
    mul_le_mul_of_nonneg_left hυq (by positivity)
  calc _ ≤ 4 / α * (1 + 2 * m) ^ 2 * q + 2 * m ^ 2 * ((1 / c) ^ (1 / C) * q) + 2 * m / α * q := by
        linarith
    _ = _ := by ring

private lemma s9d_small_zeta (m : ℕ) (hm : 1 ≤ m) (ζ : ℝ) (hζ0 : 0 < ζ)
    (hζ : ζ < 1 / (384 * (m : ℝ) ^ 8 * ((m : ℝ) + 1) ^ 2) ^ 2) :
    9 * ζ ≤ 1 ∧ ζ * (m : ℝ) ^ 8 < 1 ∧
      6 * Real.sqrt ζ * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 <
        (1 - ζ) ^ 4 * (1 / (2 * (m : ℝ) ^ 3)) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set E : ℝ := 384 * (m : ℝ) ^ 8 * ((m : ℝ) + 1) ^ 2 with hE
  have hm8 : (1 : ℝ) ≤ (m : ℝ) ^ 8 := one_le_pow₀ hm1
  have hm18 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hE384 : 384 ≤ E := by rw [hE]; nlinarith
  have hE0 : 0 < E := by linarith
  have hEsq : 384 ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (by norm_num) hE384 2
  have hζs : ζ < 1 / 384 ^ 2 := lt_of_lt_of_le hζ (one_div_le_one_div_of_le (by positivity) hEsq)
  have hζ2 : ζ ≤ 1 / 2 := by linarith [show (1 : ℝ) / 384 ^ 2 ≤ 1 / 2 by norm_num]
  refine ⟨by linarith [show (1 : ℝ) / 384 ^ 2 * 9 ≤ 1 by norm_num], ?_, ?_⟩
  · have hm8E : (m : ℝ) ^ 8 ≤ E := by rw [hE]; nlinarith
    have : ζ * (m : ℝ) ^ 8 ≤ ζ * E := mul_le_mul_of_nonneg_left hm8E hζ0.le
    have h2 : ζ * E < 1 := by
      have : ζ * E ^ 2 < 1 := by
        rw [lt_div_iff₀ (by positivity)] at hζ
        exact hζ
      nlinarith
    linarith
  · have hsq : Real.sqrt ζ < 1 / E := by
      rw [Real.sqrt_lt' (by positivity)]
      rw [one_div, inv_pow, ← one_div]
      exact hζ
    have hpos : 0 < 6 * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 := by positivity
    have hlhs : 6 * Real.sqrt ζ * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 <
        6 * (1 / E) * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 := by
      have := mul_lt_mul_of_pos_left hsq hpos
      nlinarith
    have hval : 6 * (1 / E) * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 = 1 / (64 * (m : ℝ) ^ 6) := by
      rw [hE]
      have : (m : ℝ) ≠ 0 := by positivity
      have : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    have hrhs : 1 / (64 * (m : ℝ) ^ 6) ≤ (1 - ζ) ^ 4 * (1 / (2 * (m : ℝ) ^ 3)) ^ 2 := by
      have h16 : (1 : ℝ) / 16 ≤ (1 - ζ) ^ 4 := by
        have : (1 : ℝ) / 2 ≤ 1 - ζ := by linarith
        calc (1 : ℝ) / 16 = (1 / 2) ^ 4 := by norm_num
          _ ≤ (1 - ζ) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
      have e : (1 / (2 * (m : ℝ) ^ 3)) ^ 2 = 1 / (4 * (m : ℝ) ^ 6) := by
        have : (m : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [e]
      calc 1 / (64 * (m : ℝ) ^ 6) = 1 / 16 * (1 / (4 * (m : ℝ) ^ 6)) := by
            have : (m : ℝ) ≠ 0 := by positivity
            field_simp
            ring
        _ ≤ (1 - ζ) ^ 4 * (1 / (4 * (m : ℝ) ^ 6)) :=
            mul_le_mul_of_nonneg_right h16 (by positivity)
    linarith

private lemma s9d_ineq_one (m : ℕ) (A x : ℝ) (hA : 2 ≤ A) :
    (m : ℝ) ^ 3 * A ^ (-(x + 2 + ((m ^ 3 : ℕ) : ℝ))) + A ^ (-(x + 2)) ≤ A ^ (-x) / 2 := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have h2 : A ^ (-(2 : ℝ)) ≤ 1 / 4 := by
    rw [Real.rpow_neg hA0.le]
    have : (4 : ℝ) ≤ A ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) this
  have hk : (m : ℝ) ^ 3 * A ^ (-((m ^ 3 : ℕ) : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hA0.le, Real.rpow_natCast]
    have h1 : ((m ^ 3 : ℕ) : ℝ) < 2 ^ (m ^ 3) := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ (m ^ 3) ≤ A ^ (m ^ 3) := pow_le_pow_left₀ (by norm_num) hA _
    have h3 : (m : ℝ) ^ 3 < A ^ (m ^ 3) := by
      have : (m : ℝ) ^ 3 = ((m ^ 3 : ℕ) : ℝ) := by push_cast; ring
      rw [this]; linarith
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact h3.le
  have e1 : A ^ (-(x + 2 + ((m ^ 3 : ℕ) : ℝ))) =
      A ^ (-x) * A ^ (-(2 : ℝ)) * A ^ (-((m ^ 3 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add hA0, ← Real.rpow_add hA0]; congr 1; ring
  have e2 : A ^ (-(x + 2)) = A ^ (-x) * A ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hA0]; congr 1; ring
  rw [e1, e2]
  have hx : 0 < A ^ (-x) := Real.rpow_pos_of_pos hA0 _
  have h2p : 0 < A ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hA0 _
  have : (m : ℝ) ^ 3 * (A ^ (-x) * A ^ (-(2 : ℝ)) * A ^ (-((m ^ 3 : ℕ) : ℝ))) =
      A ^ (-x) * A ^ (-(2 : ℝ)) * ((m : ℝ) ^ 3 * A ^ (-((m ^ 3 : ℕ) : ℝ))) := by ring
  rw [this]
  have h3 : A ^ (-x) * A ^ (-(2 : ℝ)) * ((m : ℝ) ^ 3 * A ^ (-((m ^ 3 : ℕ) : ℝ))) ≤
      A ^ (-x) * A ^ (-(2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
  have h4 : A ^ (-x) * A ^ (-(2 : ℝ)) ≤ A ^ (-x) * (1 / 4) :=
    mul_le_mul_of_nonneg_left h2 hx.le
  nlinarith

private lemma s9d_varbound_step (m : ℕ) {α c C : ℝ} (hm0 : (0 : ℝ) < m) (hC : 0 < C)
    {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ ζ η : ℝ, 0 < ζ → ζ ≤ 1 → 0 ≤ η → η ≤ ζ →
      s9dVarBound m α c C ζ η ≤ K * ζ ^ (1 / (4 + 4 * C)))
    {s : ℕ} (hs : (m : ℝ) ^ 2 * K < 2 ^ s) {A : ℝ} (hA : 2 ≤ A) {x : ℝ}
    (hx : (1 + (s : ℝ)) * (4 + 4 * C) ≤ x) {η : ℝ} (hη0 : 0 ≤ η) (hηζ : η ≤ A ^ (-x)) :
    s9dVarBound m α c C (A ^ (-x)) η < 1 / ((m : ℝ) ^ 2 * A) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hζ0 : 0 < A ^ (-x) := Real.rpow_pos_of_pos hA0 _
  have hζ1 : A ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)
  have hvb := hK (A ^ (-x)) η hζ0 hζ1 hη0 hηζ
  have hθ : (1 + (s : ℝ)) ≤ x * (1 / (4 + 4 * C)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    exact hx
  have hp : (A ^ (-x)) ^ (1 / (4 + 4 * C)) ≤ A ^ (-1 : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    rw [← Real.rpow_mul hA0.le]
    calc A ^ (-x * (1 / (4 + 4 * C))) ≤ A ^ (-(1 + (s : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
      _ = A ^ (-1 : ℝ) * (A ^ s)⁻¹ := by
          rw [show -(1 + (s : ℝ)) = -1 + -(s : ℝ) by ring, Real.rpow_add hA0,
            Real.rpow_neg hA0.le (s : ℝ), Real.rpow_natCast]
      _ ≤ A ^ (-1 : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hA0 _).le
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hA _)
  have hkey : K * (A ^ (-1 : ℝ) * ((2 : ℝ) ^ s)⁻¹) < 1 / ((m : ℝ) ^ 2 * A) := by
    rw [Real.rpow_neg_one]
    have e1 : K * (A⁻¹ * ((2 : ℝ) ^ s)⁻¹) = (K / 2 ^ s) / A := by field_simp
    have e2 : 1 / ((m : ℝ) ^ 2 * A) = (1 / (m : ℝ) ^ 2) / A := by field_simp
    rw [e1, e2]
    apply div_lt_div_of_pos_right _ hA0
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc _ ≤ K * (A ^ (-x)) ^ (1 / (4 + 4 * C)) := hvb
    _ ≤ K * (A ^ (-1 : ℝ) * ((2 : ℝ) ^ s)⁻¹) := mul_le_mul_of_nonneg_left hp hK0.le
    _ < _ := hkey

/-- Paper IV `lem:delta-inductive#parameter-hierarchy` (`eq:hier2`, l. 5347-5351), made explicit (in the
source the `≪` are never quantified). There are exponents `R₁ i < R₂ i < R₃ i < R₄ i`, chained by
`R₁ (i+1) = R₄ i` (the candidate tuples of Claim 9.8), and one absolute `C₀ ≥ R₃ i` (`i ≤ 3m`): this is the
constant `C` of Lemma 9.3, chosen before `A` (it depends on `(m, α, c, C)` only, where `(c, C)` are the
relaxed-base-case constants). For EVERY `A ≥ 2` and every `i`, the parameters `τ = A^{-R₁}`,
`ζ = A^{-R₂}`, `ε = A^{-R₃}`, `η = A^{-R₄}` satisfy every inequality the proof uses:
* `m³η + ε ≤ ζ/2` (near-equality, `√(1-ζ) ≤ 1-ζ/2`);
* `ζ ≤ τ⁸` (Claims 9.11, 9.17);  `mη² ≤ ζ` (`M₁, M₂ ≥ 1 - ζ`);
* `ζ m⁸ < 1` (Claim 9.18);  `9ζ ≤ 1`;
* `6√ζ (m(m+1))² < (1-ζ)⁴ (2m³)⁻²` (variance contradiction with `c = 1/(2m³)`);
* `s9dVarBound ... < 1/(m²A)` (modest-influence contradiction, `I_{j,modest} ≥ 1/A`). -/
theorem s9d_parameter_hierarchy (m : ℕ) (hm : 1 ≤ m) {α c C : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hC : 0 < C) :
    ∃ R₁ R₂ R₃ R₄ : ℕ → ℝ, (∀ i, 0 < R₁ i ∧ R₁ i < R₂ i ∧ R₂ i < R₃ i ∧ R₃ i < R₄ i) ∧
      (∀ i, R₁ (i + 1) = R₄ i) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧ (∀ i ≤ 3 * m, R₃ i ≤ C₀) ∧
        ∀ A : ℝ, 2 ≤ A → ∀ i,
          (m : ℝ) ^ 3 * A ^ (-R₄ i) + A ^ (-R₃ i) ≤ A ^ (-R₂ i) / 2 ∧
          A ^ (-R₂ i) ≤ (A ^ (-R₁ i)) ^ 8 ∧ (m : ℝ) * (A ^ (-R₄ i)) ^ 2 ≤ A ^ (-R₂ i) ∧
          A ^ (-R₂ i) * (m : ℝ) ^ 8 < 1 ∧ 9 * A ^ (-R₂ i) ≤ 1 ∧
          6 * Real.sqrt (A ^ (-R₂ i)) * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 <
            (1 - A ^ (-R₂ i)) ^ 4 * (1 / (2 * (m : ℝ) ^ 3)) ^ 2 ∧
          s9dVarBound m α c C (A ^ (-R₂ i)) (A ^ (-R₄ i)) < 1 / ((m : ℝ) ^ 2 * A) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨K, hK0, hK⟩ := s9dVarBound_le m hα hc hC
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ((m : ℝ) ^ 2 * K) (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt
    ((384 * (m : ℝ) ^ 8 * ((m : ℝ) + 1) ^ 2) ^ 2) (show (1 : ℝ) < 2 by norm_num)
  set Λ : ℝ := (N0 : ℝ) + (1 + (s : ℝ)) * (4 + 4 * C) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  set k : ℝ := ((m ^ 3 : ℕ) : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast pow_pos hm 3
  obtain ⟨R₁, hR10, hR1s⟩ : ∃ R₁ : ℕ → ℝ, R₁ 0 = 1 ∧ ∀ i, R₁ (i + 1) = 8 * R₁ i + Λ + 2 + k :=
    ⟨fun i => Nat.rec 1 (fun _ x => 8 * x + Λ + 2 + k) i, rfl, fun _ => rfl⟩
  have hpos : ∀ i, 0 < R₁ i := by
    intro i
    induction i with
    | zero => rw [hR10]; norm_num
    | succ n ih => rw [hR1s]; linarith
  refine ⟨R₁, fun i => 8 * R₁ i + Λ, fun i => 8 * R₁ i + Λ + 2,
    fun i => 8 * R₁ i + Λ + 2 + k, ?_, ?_, ?_⟩
  · intro i
    have := hpos i
    refine ⟨this, ?_, ?_, ?_⟩ <;> simp only <;> linarith
  · intro i
    exact hR1s i
  refine ⟨∑ i ∈ Finset.range (3 * m + 1), (8 * R₁ i + Λ + 2), ?_, ?_, ?_⟩
  · exact Finset.sum_pos (fun i _ => by have := hpos i; linarith) ⟨0, by simp⟩
  · intro i hi
    exact Finset.single_le_sum (f := fun i => 8 * R₁ i + Λ + 2)
      (fun j _ => by have := hpos j; linarith) (Finset.mem_range.2 (by omega))
  intro A hA i
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hR := hpos i
  simp only
  set x : ℝ := 8 * R₁ i + Λ with hx
  have hxΛ : Λ ≤ x := by linarith
  have hζ0 : 0 < A ^ (-x) := Real.rpow_pos_of_pos hA0 _
  have hζ1 : A ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)
  have hη0 : 0 ≤ A ^ (-(x + 2 + k)) := (Real.rpow_pos_of_pos hA0 _).le
  have hηζ : A ^ (-(x + 2 + k)) ≤ A ^ (-x) :=
    Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
  have h1 : (m : ℝ) ^ 3 * A ^ (-(x + 2 + k)) + A ^ (-(x + 2)) ≤ A ^ (-x) / 2 :=
    s9d_ineq_one m A x hA
  have hr3 : 0 < A ^ (-(x + 2)) := Real.rpow_pos_of_pos hA0 _
  have hE0 : (0 : ℝ) < (384 * (m : ℝ) ^ 8 * ((m : ℝ) + 1) ^ 2) ^ 2 := by positivity
  have hζE : A ^ (-x) < 1 / (384 * (m : ℝ) ^ 8 * ((m : ℝ) + 1) ^ 2) ^ 2 := by
    have hNΛ : (N0 : ℝ) ≤ Λ := by
      rw [hΛ]; nlinarith [hC, (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    have h1 : A ^ (-x) ≤ A ^ (-(N0 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
    have h2 : A ^ (-(N0 : ℝ)) ≤ ((2 : ℝ) ^ N0)⁻¹ := by
      rw [Real.rpow_neg hA0.le, Real.rpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hA _)
    have h3 : ((2 : ℝ) ^ N0)⁻¹ < 1 / (384 * (m : ℝ) ^ 8 * ((m : ℝ) + 1) ^ 2) ^ 2 := by
      rw [← one_div]
      exact one_div_lt_one_div_of_lt hE0 hN0
    linarith
  obtain ⟨hs9, hs8, hs6⟩ := s9d_small_zeta m hm _ hζ0 hζE
  refine ⟨h1, ?_, ?_, hs8, hs9, hs6, ?_⟩
  · have e : (A ^ (-R₁ i)) ^ 8 = A ^ (-R₁ i * 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
  · have h3 : (m : ℝ) ^ 3 * A ^ (-(x + 2 + k)) ≤ A ^ (-x) / 2 := by linarith
    have hη1 : A ^ (-(x + 2 + k)) ≤ 1 := by linarith
    have hη2 : (A ^ (-(x + 2 + k))) ^ 2 ≤ A ^ (-(x + 2 + k)) := by nlinarith
    have hmm : (m : ℝ) ≤ (m : ℝ) ^ 3 := by nlinarith
    have : (m : ℝ) * (A ^ (-(x + 2 + k))) ^ 2 ≤ (m : ℝ) * A ^ (-(x + 2 + k)) :=
      mul_le_mul_of_nonneg_left hη2 hm0.le
    have : (m : ℝ) * A ^ (-(x + 2 + k)) ≤ (m : ℝ) ^ 3 * A ^ (-(x + 2 + k)) :=
      mul_le_mul_of_nonneg_right hmm hη0
    linarith
  · exact s9d_varbound_step m hm0 hC hK0 hK hs hA
      (by rw [hx, hΛ]; nlinarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0), hR]) hη0 hηζ

end S9dHierarchy

end TrackB
end RestrictedPolynomials
end
