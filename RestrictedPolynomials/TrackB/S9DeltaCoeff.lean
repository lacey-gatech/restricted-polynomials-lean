module

public import RestrictedPolynomials.TrackB.S7Beta
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Paper IV, Section 9: coefficient data of the `delta_inductive` expansion

The finite, setting-free part of the numeric claims 9.9, 9.11, 9.17, 9.18 of paper IV (eq. `delta_1`,
`delta_2`): the sets `T', R', S'`, the main and tail sums, and the Cauchy-Schwarz, case-split and
counting estimates on arrays `F̂, F̂' : Fin sT → Fin sR → Fin sS → ℂ`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### coefficient data of the expansion (eq. `delta_1`, `delta_2`) -/

section S9dCoeff

/-- `T' = {t | ψ_t ≥ τ}`, `R' = {r | κ_r ≥ τ}`, `S' = {s | ρ_s ≥ τ}` (l. 5391-5395). -/
def s9dBig {s : ℕ} (c : Fin s → ℝ) (τ : ℝ) : Finset (Fin s) := univ.filter fun i => τ ≤ c i

/-- `∑_{i ∈ T'} ψ_i²` (and `M₁ = ∑_{R'} κ_r²`, `M₂ = ∑_{S'} ρ_s²`, l. 5484). -/
def s9dMass {s : ℕ} (c : Fin s → ℝ) (τ : ℝ) : ℝ := ∑ i ∈ s9dBig c τ, c i ^ 2

theorem s9dBig_mem {s : ℕ} (c : Fin s → ℝ) (τ : ℝ) (i : Fin s) : i ∈ s9dBig c τ ↔ τ ≤ c i := by
  simp [s9dBig]

variable {sT sR sS : ℕ}

/-- the summand `ψ_t κ_r ρ_s F̂_t(r,s) F̂'_t(r,s)` of eq. `delta_1`. -/
def s9dTerm (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) (x : Fin sT × Fin sR × Fin sS) : ℂ :=
  (ψ x.1 : ℂ) * κ x.2.1 * ρ x.2.2 * Fh x.1 x.2.1 x.2.2 * Gh x.1 x.2.1 x.2.2

/-- (I) of eq. `delta_2`: the sum over `T' × R' × S'`. -/
def s9dMain (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) : ℂ :=
  ∑ x ∈ univ.filter (fun x : Fin sT × Fin sR × Fin sS => τ ≤ ψ x.1 ∧ τ ≤ κ x.2.1 ∧ τ ≤ ρ x.2.2),
    s9dTerm ψ κ ρ Fh Gh x

/-- (II) of eq. `delta_2`: the sum over the remaining triples. -/
def s9dTail (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) : ℂ :=
  ∑ x ∈ univ.filter (fun x : Fin sT × Fin sR × Fin sS => ¬(τ ≤ ψ x.1 ∧ τ ≤ κ x.2.1 ∧ τ ≤ ρ x.2.2)),
    s9dTerm ψ κ ρ Fh Gh x

/-- eq. `delta_2`: `δ = (I) + (II)`. -/
theorem s9d_main_add_tail (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) :
    ∑ x, s9dTerm ψ κ ρ Fh Gh x = s9dMain ψ κ ρ Fh Gh τ + s9dTail ψ κ ρ Fh Gh τ := by
  unfold s9dMain s9dTail
  rw [Finset.sum_filter_add_sum_filter_not]

/-- `∑_{r∈R', s∈S'} κ_r²ρ_s² ∑_{t∈T'} |F̂_t(r,s)|²`, the left side of eq. `assume_delta_3`'s sum. -/
def s9dA1 (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) : ℝ :=
  ∑ r ∈ s9dBig κ τ, ∑ s ∈ s9dBig ρ τ, κ r ^ 2 * ρ s ^ 2 * ∑ t ∈ s9dBig ψ τ, ‖Fh t r s‖ ^ 2

/-- `∑_{t∈T'} ψ_t² ∑_{r∈R', s∈S'} |F̂'_t(r,s)|²`, the sum of eq. `assume_delta_2`. -/
def s9dA2 (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Gh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) : ℝ :=
  ∑ t ∈ s9dBig ψ τ, ψ t ^ 2 * ∑ r ∈ s9dBig κ τ, ∑ s ∈ s9dBig ρ τ, ‖Gh t r s‖ ^ 2

private lemma s9d_filter_eq (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ) (τ : ℝ) :
    (univ.filter (fun x : Fin sT × Fin sR × Fin sS => τ ≤ ψ x.1 ∧ τ ≤ κ x.2.1 ∧ τ ≤ ρ x.2.2)) =
      s9dBig ψ τ ×ˢ (s9dBig κ τ ×ˢ s9dBig ρ τ) := by
  ext x; simp [s9dBig]

private lemma s9d_A1_eq (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) :
    ∑ x ∈ s9dBig ψ τ ×ˢ (s9dBig κ τ ×ˢ s9dBig ρ τ),
      (κ x.2.1 * ρ x.2.2 * ‖Fh x.1 x.2.1 x.2.2‖) ^ 2 = s9dA1 ψ κ ρ Fh τ := by
  unfold s9dA1
  simp only [Finset.sum_product, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

private lemma s9d_A2_eq (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Gh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) :
    ∑ x ∈ s9dBig ψ τ ×ˢ (s9dBig κ τ ×ˢ s9dBig ρ τ),
      (ψ x.1 * ‖Gh x.1 x.2.1 x.2.2‖) ^ 2 = s9dA2 ψ κ ρ Gh τ := by
  unfold s9dA2
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

private lemma s9d_norm_main_le (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (hψ : ∀ t, 0 ≤ ψ t) (hκ : ∀ r, 0 ≤ κ r) (hρ : ∀ s, 0 ≤ ρ s)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) (τ : ℝ) :
    ‖s9dMain ψ κ ρ Fh Gh τ‖ ≤ Real.sqrt (s9dA1 ψ κ ρ Fh τ) * Real.sqrt (s9dA2 ψ κ ρ Gh τ) := by
  unfold s9dMain
  rw [s9d_filter_eq, ← s9d_A1_eq, ← s9d_A2_eq]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (le_of_eq ?_) (Real.sum_mul_le_sqrt_mul_sqrt _
    (fun x : Fin sT × Fin sR × Fin sS => κ x.2.1 * ρ x.2.2 * ‖Fh x.1 x.2.1 x.2.2‖)
    (fun x : Fin sT × Fin sR × Fin sS => ψ x.1 * ‖Gh x.1 x.2.1 x.2.2‖))
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [s9dTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ _),
    abs_of_nonneg (hκ _), abs_of_nonneg (hρ _)]
  ring

private lemma s9d_mul_le_one {a b : ℝ} (ha : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : a * b ≤ 1 := by
  nlinarith

private lemma s9d_mass_le_one {s : ℕ} (c : Fin s → ℝ) (τ : ℝ) (h : ∑ i, c i ^ 2 ≤ 1) :
    s9dMass c τ ≤ 1 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _).trans h

private lemma s9d_mass_nonneg {s : ℕ} (c : Fin s → ℝ) (τ : ℝ) : 0 ≤ s9dMass c τ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma s9d_le_one_of_sum_sq {s : ℕ} (c : Fin s → ℝ) (h0 : ∀ i, 0 ≤ c i)
    (h : ∑ i, c i ^ 2 = 1) (i : Fin s) : c i ≤ 1 := by
  have h1 : c i ^ 2 ≤ ∑ j, c j ^ 2 :=
    Finset.single_le_sum (f := fun j => c j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have := h0 i
  nlinarith

private lemma s9d_A1_le (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Fh : Fin sT → Fin sR → Fin sS → ℂ) {δ' : ℝ}
    (hFh : ∀ r s, ∑ t, ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2) (τ : ℝ) :
    s9dA1 ψ κ ρ Fh τ ≤ δ' ^ 2 * (s9dMass κ τ * s9dMass ρ τ) := by
  unfold s9dA1 s9dMass
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h : ∑ t ∈ s9dBig ψ τ, ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => sq_nonneg _).trans (hFh r s)
  nlinarith [mul_nonneg (sq_nonneg (κ r)) (sq_nonneg (ρ s))]

private lemma s9d_A2_le (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Gh : Fin sT → Fin sR → Fin sS → ℂ)
    (hGh : ∀ t, ∑ r, ∑ s, ‖Gh t r s‖ ^ 2 ≤ 1) (τ : ℝ) :
    s9dA2 ψ κ ρ Gh τ ≤ s9dMass ψ τ := by
  unfold s9dA2 s9dMass
  refine Finset.sum_le_sum fun t _ => ?_
  have h : ∑ r ∈ s9dBig κ τ, ∑ s ∈ s9dBig ρ τ, ‖Gh t r s‖ ^ 2 ≤ 1 := by
    refine le_trans ?_ (hGh t)
    refine (Finset.sum_le_sum fun r _ => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun r _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  nlinarith [sq_nonneg (ψ t)]

private lemma s9d_prod_le {a b c η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (hc1 : c ≤ 1) (h : a < η ∨ b < η ∨ c < η) : a * b * c ≤ η := by
  rcases h with h | h | h
  · have : a * b * c ≤ a := by
      have := s9d_mul_le_one hb1 hc hc1
      nlinarith
    linarith
  · have : a * b * c ≤ b := by
      have := s9d_mul_le_one ha1 hc hc1
      nlinarith
    linarith
  · have : a * b * c ≤ c := by
      have := s9d_mul_le_one ha1 hb hb1
      nlinarith
    linarith

/-- Paper IV `claim:bound-err-term-gamma` (Claim 9.9, l. 5411-5420): `|(II)| ≤ m³ η δ_{n-1,d'-1}`. In
each summand some coefficient is `< η` (no coefficient lies in `[η, τ)`, Claim 9.8) and the other two are
at most `1`; `|F̂_t(r,s)| ≤ δ_{n-1,d'-1}`, `|F̂'_t(r,s)| ≤ 1`; there are at most `|T||R||S| ≤ m³`
terms (`|T| ≤ |Σ| ≤ m`, `s9d_card_le`; the printed `m³` is right; the weaker
`|T| ≤ m²` would give `m⁴`). -/
theorem s9d_bound_err_term (m : ℕ) (hR : sR ≤ m) (hS : sS ≤ m) (hT : sT ≤ m)
    (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (hψ : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1) (hκ : ∀ r, 0 ≤ κ r ∧ κ r ≤ 1) (hρ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) {δ' : ℝ} (hδ' : 0 ≤ δ')
    (hFh : ∀ t r s, ‖Fh t r s‖ ≤ δ') (hGh : ∀ t r s, ‖Gh t r s‖ ≤ 1) {τ η : ℝ} (hη : 0 ≤ η)
    (hsψ : ∀ t, ψ t < η ∨ τ ≤ ψ t) (hsκ : ∀ r, κ r < η ∨ τ ≤ κ r) (hsρ : ∀ s, ρ s < η ∨ τ ≤ ρ s) :
    ‖s9dTail ψ κ ρ Fh Gh τ‖ ≤ (m : ℝ) ^ 3 * η * δ' := by
  unfold s9dTail
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x ∈ univ.filter (fun x : Fin sT × Fin sR × Fin sS =>
      ¬(τ ≤ ψ x.1 ∧ τ ≤ κ x.2.1 ∧ τ ≤ ρ x.2.2)), ‖s9dTerm ψ κ ρ Fh Gh x‖ ≤ η * δ' := by
    intro x hx
    obtain ⟨t, r, s⟩ := x
    simp only [mem_filter, mem_univ, true_and] at hx
    have hP : ψ t * κ r * ρ s ≤ η := by
      refine s9d_prod_le (hψ t).1 (hκ r).1 (hρ s).1 (hψ t).2 (hκ r).2 (hρ s).2 ?_
      rcases hsψ t with h | h
      · exact Or.inl h
      rcases hsκ r with h' | h'
      · exact Or.inr (Or.inl h')
      rcases hsρ s with h'' | h''
      · exact Or.inr (Or.inr h'')
      exact absurd ⟨h, h', h''⟩ hx
    simp only [s9dTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ t).1,
      abs_of_nonneg (hκ r).1, abs_of_nonneg (hρ s).1]
    have := mul_le_mul (mul_le_mul hP (hFh t r s) (norm_nonneg _) hη) (hGh t r s)
      (norm_nonneg _) (mul_nonneg hη hδ')
    simpa using this
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  have hcard : (univ.filter (fun x : Fin sT × Fin sR × Fin sS =>
      ¬(τ ≤ ψ x.1 ∧ τ ≤ κ x.2.1 ∧ τ ≤ ρ x.2.2))).card ≤ m ^ 3 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    calc sT * (sR * sS) ≤ m * (m * m) := Nat.mul_le_mul hT (Nat.mul_le_mul hR hS)
      _ = m ^ 3 := by ring
  rw [nsmul_eq_mul]
  have hc : ((univ.filter (fun x : Fin sT × Fin sR × Fin sS =>
      ¬(τ ≤ ψ x.1 ∧ τ ≤ κ x.2.1 ∧ τ ≤ ρ x.2.2))).card : ℝ) ≤ (m : ℝ) ^ 3 := by
    exact_mod_cast hcard
  nlinarith [mul_nonneg hη hδ']

/-- Paper IV `lem:delta-inductive#naive-cauchy-schwarz` (l. 5422-5452): `|(I)| ≤ √A₁ √A₂`,
`A₁ ≤ δ'² M₁M₂`, `A₂ ≤ ∑_{T'} ψ_t²`, hence `|(I)| ≤ δ'` (`A₁ = ∑ κ²ρ²|F̂|²`, `A₂ = ∑ ψ²|F̂'|²`). The
level-`n-1` inputs are `hFh` (`∑_t |F̂_t(r,s)|² ≤ δ'²`, `s9d_level_bounds_a`) and `hGh` (Bessel,
`s9d_level_bounds_b`). -/
theorem s9d_naive_cauchy_schwarz (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (hψ : ∀ t, 0 ≤ ψ t) (hκ : ∀ r, 0 ≤ κ r) (hρ : ∀ s, 0 ≤ ρ s) (hψ1 : ∑ t, ψ t ^ 2 = 1)
    (hκ1 : ∑ r, κ r ^ 2 = 1) (hρ1 : ∑ s, ρ s ^ 2 = 1)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) {δ' : ℝ} (hδ' : 0 ≤ δ')
    (hFh : ∀ r s, ∑ t, ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2) (hGh : ∀ t, ∑ r, ∑ s, ‖Gh t r s‖ ^ 2 ≤ 1) (τ : ℝ) :
    ‖s9dMain ψ κ ρ Fh Gh τ‖ ≤ Real.sqrt (s9dA1 ψ κ ρ Fh τ) * Real.sqrt (s9dA2 ψ κ ρ Gh τ) ∧
      s9dA1 ψ κ ρ Fh τ ≤ δ' ^ 2 * (s9dMass κ τ * s9dMass ρ τ) ∧
      s9dA2 ψ κ ρ Gh τ ≤ s9dMass ψ τ ∧ ‖s9dMain ψ κ ρ Fh Gh τ‖ ≤ δ' := by
  have hA1 := s9d_A1_le ψ κ ρ Fh hFh τ
  have hA2 := s9d_A2_le ψ κ ρ Gh hGh τ
  refine ⟨s9d_norm_main_le ψ κ ρ hψ hκ hρ Fh Gh τ, hA1, hA2, ?_⟩
  refine (s9d_norm_main_le ψ κ ρ hψ hκ hρ Fh Gh τ).trans ?_
  have h1 : Real.sqrt (s9dA1 ψ κ ρ Fh τ) ≤ δ' := by
    refine (Real.sqrt_le_sqrt hA1).trans ?_
    rw [Real.sqrt_le_left hδ']
    have hk := s9d_mass_le_one κ τ hκ1.le
    have hr := s9d_mass_le_one ρ τ hρ1.le
    have := s9d_mul_le_one hk (s9d_mass_nonneg ρ τ) hr
    nlinarith [sq_nonneg δ']
  have h2 : Real.sqrt (s9dA2 ψ κ ρ Gh τ) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hA2.trans (s9d_mass_le_one ψ τ hψ1.le)
  calc _ ≤ δ' * 1 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) hδ'
    _ = δ' := mul_one _

/-- Paper IV `lem:delta-inductive#near-equality-case-split` (l. 5453-5481): unless (`assume_delta_2`) and
(`assume_delta_3`) both hold, `|δ_{n,d'}-expansion| ≤ (1-ε) δ_{n-1,d'-1}`. (`assume_delta_1` is never
used after it is stated and is not needed.) The constraint is `m³η + ε ≤ ζ/2` (the printed "`(1-ζ) +
O_m(η) ≤ 1-ε`", made explicit; `√(1-ζ) ≤ 1-ζ/2`). -/
theorem s9d_near_equality_case_split (m : ℕ) (hR : sR ≤ m) (hS : sS ≤ m) (hT : sT ≤ m)
    (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (hψ : ∀ t, 0 ≤ ψ t) (hκ : ∀ r, 0 ≤ κ r) (hρ : ∀ s, 0 ≤ ρ s) (hψ1 : ∑ t, ψ t ^ 2 = 1)
    (hκ1 : ∑ r, κ r ^ 2 = 1) (hρ1 : ∑ s, ρ s ^ 2 = 1)
    (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ) {δ' : ℝ} (hδ' : 0 ≤ δ')
    (hFh : ∀ r s, ∑ t, ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2) (hGh : ∀ t, ∑ r, ∑ s, ‖Gh t r s‖ ^ 2 ≤ 1)
    {τ η ε ζ : ℝ} (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hsψ : ∀ t, ψ t < η ∨ τ ≤ ψ t) (hsκ : ∀ r, κ r < η ∨ τ ≤ κ r) (hsρ : ∀ s, ρ s < η ∨ τ ≤ ρ s)
    (hpar : (m : ℝ) ^ 3 * η + ε ≤ ζ / 2) :
    ‖∑ x, s9dTerm ψ κ ρ Fh Gh x‖ ≤ (1 - ε) * δ' ∨
      ((1 - ζ) * s9dMass ψ τ < s9dA2 ψ κ ρ Gh τ ∧
        (1 - ζ) * δ' ^ 2 * (s9dMass κ τ * s9dMass ρ τ) < s9dA1 ψ κ ρ Fh τ) := by
  have _ := hζ
  have hFpt : ∀ t r s, ‖Fh t r s‖ ≤ δ' := by
    intro t r s
    have h1 : ‖Fh t r s‖ ^ 2 ≤ ∑ t', ‖Fh t' r s‖ ^ 2 :=
      Finset.single_le_sum (f := fun t' => ‖Fh t' r s‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ t)
    nlinarith [norm_nonneg (Fh t r s), hFh r s]
  have hGpt : ∀ t r s, ‖Gh t r s‖ ≤ 1 := by
    intro t r s
    have h1 : ‖Gh t r s‖ ^ 2 ≤ ∑ s', ‖Gh t r s'‖ ^ 2 :=
      Finset.single_le_sum (f := fun s' => ‖Gh t r s'‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ s)
    have h2 : ∑ s', ‖Gh t r s'‖ ^ 2 ≤ ∑ r', ∑ s', ‖Gh t r' s'‖ ^ 2 :=
      Finset.single_le_sum (f := fun r' => ∑ s', ‖Gh t r' s'‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ r)
    nlinarith [norm_nonneg (Gh t r s), hGh t]
  have hTail := s9d_bound_err_term m hR hS hT ψ κ ρ
    (fun t => ⟨hψ t, s9d_le_one_of_sum_sq ψ hψ hψ1 t⟩)
    (fun r => ⟨hκ r, s9d_le_one_of_sum_sq κ hκ hκ1 r⟩)
    (fun s => ⟨hρ s, s9d_le_one_of_sum_sq ρ hρ hρ1 s⟩) Fh Gh hδ' hFpt hGpt hη hsψ hsκ hsρ
  rw [s9d_main_add_tail ψ κ ρ Fh Gh τ]
  have hCS := s9d_norm_main_le ψ κ ρ hψ hκ hρ Fh Gh τ
  have hA1 := s9d_A1_le ψ κ ρ Fh hFh τ
  have hA2 := s9d_A2_le ψ κ ρ Gh hGh τ
  have hMκ := s9d_mass_le_one κ τ hκ1.le
  have hMρ := s9d_mass_le_one ρ τ hρ1.le
  have hMψ := s9d_mass_le_one ψ τ hψ1.le
  have hM : s9dMass κ τ * s9dMass ρ τ ≤ 1 :=
    s9d_mul_le_one hMκ (s9d_mass_nonneg ρ τ) hMρ
  have hM0 : 0 ≤ s9dMass κ τ * s9dMass ρ τ :=
    mul_nonneg (s9d_mass_nonneg κ τ) (s9d_mass_nonneg ρ τ)
  have hs1 : Real.sqrt (s9dA1 ψ κ ρ Fh τ) ≤ δ' := by
    refine (Real.sqrt_le_sqrt hA1).trans ?_
    rw [Real.sqrt_le_left hδ']
    nlinarith [sq_nonneg δ']
  have hpar' : (m : ℝ) ^ 3 * η * δ' ≤ (ζ / 2 - ε) * δ' :=
    mul_le_mul_of_nonneg_right (by linarith) hδ'
  have hsqζ : Real.sqrt (1 - ζ) ≤ 1 - ζ / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith [sq_nonneg ζ]
  have hnn := Real.sqrt_nonneg (s9dA1 ψ κ ρ Fh τ)
  have hnn2 := Real.sqrt_nonneg (s9dA2 ψ κ ρ Gh τ)
  have htri := norm_add_le (s9dMain ψ κ ρ Fh Gh τ) (s9dTail ψ κ ρ Fh Gh τ)
  by_cases h2 : (1 - ζ) * s9dMass ψ τ < s9dA2 ψ κ ρ Gh τ
  · by_cases h1 : (1 - ζ) * δ' ^ 2 * (s9dMass κ τ * s9dMass ρ τ) < s9dA1 ψ κ ρ Fh τ
    · exact Or.inr ⟨h2, h1⟩
    · left
      rw [not_lt] at h1
      have hs1' : Real.sqrt (s9dA1 ψ κ ρ Fh τ) ≤ δ' * (1 - ζ / 2) := by
        rw [Real.sqrt_le_iff]
        constructor
        · nlinarith
        · have : (1 - ζ) * δ' ^ 2 * (s9dMass κ τ * s9dMass ρ τ) ≤ (1 - ζ) * δ' ^ 2 := by
            have := mul_le_mul_of_nonneg_left hM (mul_nonneg (by linarith : 0 ≤ 1 - ζ)
              (sq_nonneg δ'))
            simpa using this
          nlinarith [sq_nonneg δ', sq_nonneg ζ, mul_nonneg (sq_nonneg δ') (sq_nonneg ζ)]
      have hs2 : Real.sqrt (s9dA2 ψ κ ρ Gh τ) ≤ 1 := by
        rw [Real.sqrt_le_one]; exact hA2.trans hMψ
      have : Real.sqrt (s9dA1 ψ κ ρ Fh τ) * Real.sqrt (s9dA2 ψ κ ρ Gh τ) ≤
          δ' * (1 - ζ / 2) * 1 := mul_le_mul hs1' hs2 hnn2 (by nlinarith)
      nlinarith
  · left
    rw [not_lt] at h2
    have hs2 : Real.sqrt (s9dA2 ψ κ ρ Gh τ) ≤ 1 - ζ / 2 := by
      refine (Real.sqrt_le_sqrt (h2.trans ?_)).trans hsqζ
      nlinarith [s9d_mass_nonneg ψ τ]
    have : Real.sqrt (s9dA1 ψ κ ρ Fh τ) * Real.sqrt (s9dA2 ψ κ ρ Gh τ) ≤
        δ' * (1 - ζ / 2) := mul_le_mul hs1 hs2 hnn2 hδ'
    nlinarith

/-- Paper IV `claim:bound-norm-V` (Claim 9.11, l. 5542-5563): under `assume_delta_3`, every
`V_{r,s} = (F̂_t(r,s))_{t ∈ T'}` has `(1-√ζ) δ'² ≤ ‖V_{r,s}‖² ≤ δ'²`. The printed "`ζ/τ⁴ ≤ √ζ`" is
`ζ ≤ τ⁸`; the passage to `ζ δ'²` uses `M₁M₂ ≤ 1`. -/
theorem s9d_bound_norm_V (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ) (Fh : Fin sT → Fin sR → Fin sS → ℂ)
    (R' : Finset (Fin sR)) (S' : Finset (Fin sS)) (T' : Finset (Fin sT)) {δ' ζ τ : ℝ}
    (hδ' : 0 ≤ δ') (hζ : 0 ≤ ζ) (hτ : 0 < τ) (hζτ : ζ ≤ τ ^ 8)
    (hκτ : ∀ r ∈ R', τ ≤ κ r) (hρτ : ∀ s ∈ S', τ ≤ ρ s)
    (hκ1 : ∑ r ∈ R', κ r ^ 2 ≤ 1) (hρ1 : ∑ s ∈ S', ρ s ^ 2 ≤ 1)
    (hup : ∀ r ∈ R', ∀ s ∈ S', ∑ t ∈ T', ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2)
    (hassume : (1 - ζ) * δ' ^ 2 * ((∑ r ∈ R', κ r ^ 2) * ∑ s ∈ S', ρ s ^ 2) <
      ∑ r ∈ R', ∑ s ∈ S', κ r ^ 2 * ρ s ^ 2 * ∑ t ∈ T', ‖Fh t r s‖ ^ 2) :
    ∀ r ∈ R', ∀ s ∈ S', (1 - Real.sqrt ζ) * δ' ^ 2 ≤ ∑ t ∈ T', ‖Fh t r s‖ ^ 2 ∧
      ∑ t ∈ T', ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2 := by
  have _ := hδ'
  intro r hr s hs
  refine ⟨?_, hup r hr s hs⟩
  set M1 := ∑ r ∈ R', κ r ^ 2 with hM1def
  set M2 := ∑ s ∈ S', ρ s ^ 2 with hM2def
  have hM1 : 0 ≤ M1 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM2 : 0 ≤ M2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMM : M1 * M2 ≤ 1 := s9d_mul_le_one hκ1 hM2 hρ1
  have hsqζ := Real.sq_sqrt hζ
  have ha0 := Real.sqrt_nonneg ζ
  have hτ4 : 0 < τ ^ 4 := by positivity
  have ha : Real.sqrt ζ ≤ τ ^ 4 := by
    rw [Real.sqrt_le_iff]
    refine ⟨hτ4.le, ?_⟩
    calc ζ ≤ τ ^ 8 := hζτ
      _ = (τ ^ 4) ^ 2 := by ring
  have e1 : ∑ r' ∈ R', ∑ s' ∈ S', κ r' ^ 2 * ρ s' ^ 2 * δ' ^ 2 = δ' ^ 2 * (M1 * M2) := by
    rw [hM1def, hM2def, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by ring
  have hsum : ∑ r' ∈ R', ∑ s' ∈ S', κ r' ^ 2 * ρ s' ^ 2 * (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r' s'‖ ^ 2) <
      ζ * δ' ^ 2 * (M1 * M2) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e1]
    nlinarith
  have hnn : ∀ r' ∈ R', 0 ≤ ∑ s' ∈ S', κ r' ^ 2 * ρ s' ^ 2 *
      (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r' s'‖ ^ 2) := fun r' hr' =>
    Finset.sum_nonneg fun s' hs' =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sub_nonneg.2 (hup r' hr' s' hs'))
  have h1 := Finset.single_le_sum (f := fun r' => ∑ s' ∈ S', κ r' ^ 2 * ρ s' ^ 2 *
      (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r' s'‖ ^ 2)) hnn hr
  have h2 := Finset.single_le_sum (f := fun s' => κ r ^ 2 * ρ s' ^ 2 *
      (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r s'‖ ^ 2))
    (fun s' hs' => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (sub_nonneg.2 (hup r hr s' hs'))) hs
  have hκr : τ ^ 2 ≤ κ r ^ 2 := by
    have := hκτ r hr
    nlinarith
  have hρs : τ ^ 2 ≤ ρ s ^ 2 := by
    have := hρτ s hs
    nlinarith
  have hd : 0 ≤ δ' ^ 2 - ∑ t ∈ T', ‖Fh t r s‖ ^ 2 := sub_nonneg.2 (hup r hr s hs)
  have h3 : τ ^ 4 * (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r s‖ ^ 2) ≤
      κ r ^ 2 * ρ s ^ 2 * (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r s‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hd
    calc τ ^ 4 = τ ^ 2 * τ ^ 2 := by ring
      _ ≤ κ r ^ 2 * ρ s ^ 2 :=
        mul_le_mul hκr hρs (sq_nonneg _) (sq_nonneg _)
  have h4 : τ ^ 4 * (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r s‖ ^ 2) < ζ * δ' ^ 2 := by
    have : ζ * δ' ^ 2 * (M1 * M2) ≤ ζ * δ' ^ 2 :=
      by
        have := mul_le_mul_of_nonneg_left hMM (mul_nonneg hζ (sq_nonneg δ'))
        simpa using this
    linarith
  have h5 : ζ * δ' ^ 2 ≤ Real.sqrt ζ * δ' ^ 2 * τ ^ 4 := by
    have : ζ ≤ Real.sqrt ζ * τ ^ 4 := by nlinarith
    nlinarith [sq_nonneg δ']
  have h6 : τ ^ 4 * (δ' ^ 2 - ∑ t ∈ T', ‖Fh t r s‖ ^ 2) <
      τ ^ 4 * (Real.sqrt ζ * δ' ^ 2) := by nlinarith
  have := lt_of_mul_lt_mul_left h6 hτ4.le
  nlinarith

/-- Paper IV `claim:almost-full-norm` (Claim 9.17, l. 5809-5827): under `assume_delta_2`, every `t ∈ T'` has
`∑_{r∈R', s∈S'} |F̂'_t(r,s)|² ≥ 1 - √ζ`. Derived directly from `∑_{T'} ψ_t²(1 - ∑ ...) < ζ ∑_{T'} ψ_t²
≤ ζ` and `ψ_t ≥ τ`, so `ζ ≤ τ⁴` suffices (the printed detour through `1 - mη² ≥ 1 - η` and `2ζ/τ²`
is not needed). -/
theorem s9d_almost_full_norm (ψ : Fin sT → ℝ) (κ : Fin sR → ℝ) (ρ : Fin sS → ℝ)
    (Gh : Fin sT → Fin sR → Fin sS → ℂ) {ζ τ : ℝ} (hζ : 0 ≤ ζ) (hτ : 0 < τ) (hζτ : ζ ≤ τ ^ 4)
    (hψ1 : ∑ t, ψ t ^ 2 ≤ 1) (hGh : ∀ t, ∑ r ∈ s9dBig κ τ, ∑ s ∈ s9dBig ρ τ, ‖Gh t r s‖ ^ 2 ≤ 1)
    (hassume : (1 - ζ) * s9dMass ψ τ < s9dA2 ψ κ ρ Gh τ) :
    ∀ t, τ ≤ ψ t → 1 - Real.sqrt ζ ≤ ∑ r ∈ s9dBig κ τ, ∑ s ∈ s9dBig ρ τ, ‖Gh t r s‖ ^ 2 := by
  intro t₀ ht₀
  set G : Fin sT → ℝ := fun t => ∑ r ∈ s9dBig κ τ, ∑ s ∈ s9dBig ρ τ, ‖Gh t r s‖ ^ 2 with hG
  have hdef : ∑ t ∈ s9dBig ψ τ, ψ t ^ 2 * (1 - G t) = s9dMass ψ τ - s9dA2 ψ κ ρ Gh τ := by
    unfold s9dMass s9dA2
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by simp only [hG]; ring
  have hMψ : s9dMass ψ τ ≤ 1 := s9d_mass_le_one ψ τ hψ1
  have hM0 := s9d_mass_nonneg ψ τ
  have hlt : s9dMass ψ τ - s9dA2 ψ κ ρ Gh τ < ζ := by
    nlinarith
  have hnn : ∀ t ∈ s9dBig ψ τ, 0 ≤ ψ t ^ 2 * (1 - G t) := fun t _ =>
    mul_nonneg (sq_nonneg _) (sub_nonneg.2 (hGh t))
  have h1 := Finset.single_le_sum hnn ((s9dBig_mem ψ τ t₀).2 ht₀)
  rw [hdef] at h1
  have hsqζ := Real.sq_sqrt hζ
  have ha0 := Real.sqrt_nonneg ζ
  have hτ2 : 0 < τ ^ 2 := by positivity
  have ha : Real.sqrt ζ ≤ τ ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨hτ2.le, ?_⟩
    calc ζ ≤ τ ^ 4 := hζτ
      _ = (τ ^ 2) ^ 2 := by ring
  have hψt : τ ^ 2 ≤ ψ t₀ ^ 2 := by nlinarith
  have hd : 0 ≤ 1 - G t₀ := sub_nonneg.2 (hGh t₀)
  have h3 : τ ^ 2 * (1 - G t₀) < τ ^ 2 * Real.sqrt ζ := by
    have h4 : τ ^ 2 * (1 - G t₀) ≤ ψ t₀ ^ 2 * (1 - G t₀) := mul_le_mul_of_nonneg_right hψt hd
    have : ζ ≤ τ ^ 2 * Real.sqrt ζ := by nlinarith
    linarith
  have := lt_of_mul_lt_mul_left h3 hτ2.le
  simp only [hG] at this
  linarith

/-- Paper IV `claim:almost-full-norm2` (Claim 9.18, l. 5831-5862): if every pair `(r,s) ≠ (r',s')` of
`R' × S'` has `|⟨V_{r,s}, V_{r',s'}⟩| < c δ'²` (the contradiction hypothesis of §9.3.6), then
`∑_{t∈T'} |F̂'_t(r,s)|² ≥ 1 - ζ^{1/4}` for all `r ∈ R'`, `s ∈ S'`. The proof: otherwise
`(1-√ζ)|T'| ≤ |R'||S'| - ζ^{1/4}`, so `|T'| ≤ |R'||S'| - 1` as `ζ m⁸ < 1`, and Fact 9.16
(`s7_dimensionality`) gives a pair with `|⟨u, u'⟩| ≥ 1/(|T'||R'||S'|) ≥ 1/m³`. The printed `1/m²` is
`1/m³`; `c ≤ (1-√ζ)/m³`. -/
theorem s9d_almost_full_norm2 (m : ℕ) (hm : 1 ≤ m) (Fh Gh : Fin sT → Fin sR → Fin sS → ℂ)
    (R' : Finset (Fin sR)) (S' : Finset (Fin sS)) (T' : Finset (Fin sT)) (hR : R'.card ≤ m)
    (hS : S'.card ≤ m) (hT : T'.card ≤ m) {δ' ζ c : ℝ} (hδ' : 0 < δ') (hζ : 0 ≤ ζ)
    (hζm : ζ * (m : ℝ) ^ 8 < 1) (hc : c ≤ (1 - Real.sqrt ζ) / (m : ℝ) ^ 3)
    (hnorm : ∀ r ∈ R', ∀ s ∈ S', (1 - Real.sqrt ζ) * δ' ^ 2 ≤ ∑ t ∈ T', ‖Fh t r s‖ ^ 2 ∧
      ∑ t ∈ T', ‖Fh t r s‖ ^ 2 ≤ δ' ^ 2)
    (hfull : ∀ t ∈ T', 1 - Real.sqrt ζ ≤ ∑ r ∈ R', ∑ s ∈ S', ‖Gh t r s‖ ^ 2)
    (hbessel : ∀ r ∈ R', ∀ s ∈ S', ∑ t ∈ T', ‖Gh t r s‖ ^ 2 ≤ 1)
    (hperp : ∀ r ∈ R', ∀ s ∈ S', ∀ r' ∈ R', ∀ s' ∈ S', (r, s) ≠ (r', s') →
      ‖∑ t ∈ T', Fh t r s * starRingEnd ℂ (Fh t r' s')‖ < c * δ' ^ 2) :
    ∀ r ∈ R', ∀ s ∈ S', 1 - ζ ^ (1 / 4 : ℝ) ≤ ∑ t ∈ T', ‖Gh t r s‖ ^ 2 := by
  intro r₀ hr₀ s₀ hs₀
  by_contra hcon
  rw [not_le] at hcon
  -- the quarter root and the square root
  set a : ℝ := ζ ^ (1 / 4 : ℝ) with ha_def
  have ha0 : 0 ≤ a := Real.rpow_nonneg hζ _
  have ha4 : a ^ 4 = ζ := by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hζ]
    norm_num
  have hb : Real.sqrt ζ = a ^ 2 := by
    rw [← ha4, show (a ^ 4) = (a ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (sq_nonneg a)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm8 : (1 : ℝ) ≤ (m : ℝ) ^ 8 := one_le_pow₀ hm1
  have hζ1 : ζ < 1 := by nlinarith
  have hb1 : Real.sqrt ζ < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hζ1
  have hq : 0 < 1 - Real.sqrt ζ := by linarith
  -- positivity of the norms of `V_{r,s}`
  have hVpos : ∀ r ∈ R', ∀ s ∈ S', 0 < ∑ t ∈ T', ‖Fh t r s‖ ^ 2 := by
    intro r hr s hs
    have h := (hnorm r hr s hs).1
    have : 0 < (1 - Real.sqrt ζ) * δ' ^ 2 := mul_pos hq (by positivity)
    linarith
  have hk0 : 0 < T'.card := by
    rw [Finset.card_pos]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have := hVpos r₀ hr₀ s₀ hs₀
    rw [hne] at this
    simp at this
  set P : Finset (Fin sR × Fin sS) := R' ×ˢ S' with hP
  have hPcard : P.card = R'.card * S'.card := Finset.card_product _ _
  have hmem : (r₀, s₀) ∈ P := Finset.mem_product.2 ⟨hr₀, hs₀⟩
  have hℓ : P.card ≤ m * m := by
    rw [hPcard]; exact Nat.mul_le_mul hR hS
  have hℓ1 : 1 ≤ P.card := Finset.card_pos.2 ⟨_, hmem⟩
  -- counting: `(1 - √ζ) k < ℓ - a`
  have hcount : (1 - Real.sqrt ζ) * (T'.card : ℝ) < (P.card : ℝ) - a := by
    have h1 : (1 - Real.sqrt ζ) * (T'.card : ℝ) ≤
        ∑ t ∈ T', ∑ r ∈ R', ∑ s ∈ S', ‖Gh t r s‖ ^ 2 := by
      have := Finset.card_nsmul_le_sum T' (fun t => ∑ r ∈ R', ∑ s ∈ S', ‖Gh t r s‖ ^ 2)
        (1 - Real.sqrt ζ) hfull
      simpa [mul_comm] using this
    have h2 : ∑ t ∈ T', ∑ r ∈ R', ∑ s ∈ S', ‖Gh t r s‖ ^ 2 =
        ∑ x ∈ P, ∑ t ∈ T', ‖Gh t x.1 x.2‖ ^ 2 := by
      rw [hP, Finset.sum_product, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
    have h3 : ∑ x ∈ P, ∑ t ∈ T', ‖Gh t x.1 x.2‖ ^ 2 <
        (P.card : ℝ) - a := by
      rw [← Finset.add_sum_erase P _ hmem]
      have h4 : ∑ x ∈ P.erase (r₀, s₀), ∑ t ∈ T', ‖Gh t x.1 x.2‖ ^ 2 ≤
          ((P.erase (r₀, s₀)).card : ℝ) := by
        have := Finset.sum_le_card_nsmul (P.erase (r₀, s₀))
          (fun x => ∑ t ∈ T', ‖Gh t x.1 x.2‖ ^ 2) 1 (fun x hx => by
            obtain ⟨_, hx⟩ := Finset.mem_erase.1 hx
            obtain ⟨hr, hs⟩ := Finset.mem_product.1 hx
            exact hbessel _ hr _ hs)
        simpa using this
      rw [Finset.card_erase_of_mem hmem, Nat.cast_sub hℓ1] at h4
      simp only [Nat.cast_one] at h4
      linarith
    linarith
  -- `k + 1 ≤ ℓ`
  have hkℓ : T'.card + 1 ≤ P.card := by
    by_contra hlt
    rw [not_le] at hlt
    have hle : P.card ≤ T'.card := by omega
    have hle' : (P.card : ℝ) ≤ T'.card := by exact_mod_cast hle
    have h1 : (1 - Real.sqrt ζ) * (P.card : ℝ) ≤ (1 - Real.sqrt ζ) * (T'.card : ℝ) :=
      mul_le_mul_of_nonneg_left hle' hq.le
    have h2 : a < a ^ 2 * (P.card : ℝ) := by
      rw [hb] at h1 hcount
      nlinarith
    have hP' : (P.card : ℝ) ≤ (m : ℝ) * m := by exact_mod_cast hℓ
    rcases ha0.eq_or_lt with h0 | hpos
    · rw [← h0] at h2; simp at h2
    · have h3 : 1 < a * (P.card : ℝ) := by nlinarith
      have h4 : 1 < a * ((m : ℝ) * m) := lt_of_lt_of_le h3 (by nlinarith)
      have h5 : (a * ((m : ℝ) * m)) ^ 4 < 1 := by
        have : (a * ((m : ℝ) * m)) ^ 4 = ζ * (m : ℝ) ^ 8 := by rw [← ha4]; ring
        rw [this]; exact hζm
      have := one_le_pow₀ (n := 4) h4.le
      linarith
  -- the unit vectors
  have hVne : ∀ p : P, 0 < ∑ t ∈ T', ‖Fh t p.1.1 p.1.2‖ ^ 2 := fun p => by
    obtain ⟨hr, hs⟩ := Finset.mem_product.1 p.2
    exact hVpos _ hr _ hs
  set eP := P.equivFin with heP
  set eT := T'.equivFin with heT
  set nV : P → ℝ := fun p => Real.sqrt (∑ t ∈ T', ‖Fh t p.1.1 p.1.2‖ ^ 2) with hnV
  have hnV0 : ∀ p, 0 < nV p := fun p => Real.sqrt_pos.2 (hVne p)
  set u : Fin P.card → EuclideanSpace ℂ (Fin T'.card) := fun i =>
    WithLp.toLp 2 (fun j => Fh (eT.symm j).1 (eP.symm i).1.1 (eP.symm i).1.2 /
      ((nV (eP.symm i) : ℝ) : ℂ)) with hu
  have hui : ∀ i j, u i j = Fh (eT.symm j).1 (eP.symm i).1.1 (eP.symm i).1.2 /
      ((nV (eP.symm i) : ℝ) : ℂ) := fun i j => rfl
  have hsumT : ∀ g : Fin sT → ℝ, ∑ j : Fin T'.card, g (eT.symm j).1 = ∑ t ∈ T', g t := by
    intro g
    rw [Equiv.sum_comp eT.symm (fun t : T' => g t.1)]
    exact Finset.sum_coe_sort T' g
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    have h1 : ‖u i‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [hui, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
      rw [← Finset.sum_div, hsumT (fun t => ‖Fh t (eP.symm i).1.1 (eP.symm i).1.2‖ ^ 2)]
      have hn : nV (eP.symm i) ^ 2 = ∑ t ∈ T', ‖Fh t (eP.symm i).1.1 (eP.symm i).1.2‖ ^ 2 :=
        Real.sq_sqrt (hVne _).le
      rw [← hn]
      exact div_self (pow_pos (hnV0 _) 2).ne'
    nlinarith [norm_nonneg (u i)]
  obtain ⟨i, j, hij, hge⟩ := s7_dimensionality hkℓ u hunit
  have hne : (eP.symm i).1 ≠ (eP.symm j).1 := fun h => hij (eP.symm.injective (Subtype.ext h))
  obtain ⟨hri, hsi⟩ := Finset.mem_product.1 (eP.symm i).2
  obtain ⟨hrj, hsj⟩ := Finset.mem_product.1 (eP.symm j).2
  set S : ℂ := ∑ t ∈ T', Fh t (eP.symm i).1.1 (eP.symm i).1.2 *
    starRingEnd ℂ (Fh t (eP.symm j).1.1 (eP.symm j).1.2) with hSdef
  have hSlt : ‖S‖ < c * δ' ^ 2 := hperp _ hri _ hsi _ hrj _ hsj hne
  have hsumC : ∀ g : Fin sT → ℂ, ∑ j : Fin T'.card, g (eT.symm j).1 = ∑ t ∈ T', g t := by
    intro g
    rw [Equiv.sum_comp eT.symm (fun t : T' => g t.1)]
    exact Finset.sum_coe_sort T' g
  have hinner : inner ℂ (u i) (u j) =
      starRingEnd ℂ S / (((nV (eP.symm i) * nV (eP.symm j) : ℝ)) : ℂ) := by
    have hc : inner ℂ (u i) (u j) = ∑ a, (starRingEnd ℂ) (u i a) * u j a := by
      simp [PiLp.inner_apply, mul_comm]
    rw [hc]
    simp only [hui]
    rw [hsumC (fun t => (starRingEnd ℂ) (Fh t (eP.symm i).1.1 (eP.symm i).1.2 /
        ((nV (eP.symm i) : ℝ) : ℂ)) * (Fh t (eP.symm j).1.1 (eP.symm j).1.2 /
        ((nV (eP.symm j) : ℝ) : ℂ)))]
    rw [hSdef, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : ((nV (eP.symm i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hnV0 _).ne'
    have h2 : ((nV (eP.symm j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hnV0 _).ne'
    simp only [map_div₀, Complex.conj_ofReal, map_mul, Complex.conj_conj, Complex.ofReal_mul]
    field_simp
  set N : ℝ := nV (eP.symm i) * nV (eP.symm j) with hN
  have hN0 : 0 < N := mul_pos (hnV0 _) (hnV0 _)
  have hnorm' : ‖inner ℂ (u i) (u j)‖ = ‖S‖ / N := by
    rw [hinner, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hN0]
  rw [hnorm', le_div_iff₀ hN0] at hge
  -- lower bound of `N`
  set w : ℝ := (1 - Real.sqrt ζ) * δ' ^ 2 with hw
  have hw0 : 0 < w := mul_pos hq (by positivity)
  have hv : ∀ p : P, w ≤ nV p ^ 2 := fun p => by
    obtain ⟨hr, hs⟩ := Finset.mem_product.1 p.2
    rw [hnV, Real.sq_sqrt (hVne p).le]
    exact (hnorm _ hr _ hs).1
  have hNw : w ≤ N := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hv (eP.symm i)
    have h2 := hv (eP.symm j)
    have h3 : N ^ 2 = nV (eP.symm i) ^ 2 * nV (eP.symm j) ^ 2 := by rw [hN]; ring
    nlinarith [mul_le_mul h1 h2 hw0.le (sq_nonneg _)]
  have hkl : (T'.card : ℝ) * P.card ≤ (m : ℝ) ^ 3 := by
    have h1 : (T'.card : ℝ) ≤ m := by exact_mod_cast hT
    have h2 : (P.card : ℝ) ≤ (m : ℝ) * m := by exact_mod_cast hℓ
    calc (T'.card : ℝ) * P.card ≤ m * (m * m) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = (m : ℝ) ^ 3 := by ring
  have hkl0 : 0 < (T'.card : ℝ) * P.card := by
    have : (0 : ℝ) < T'.card := by exact_mod_cast hk0
    have : (0 : ℝ) < P.card := by exact_mod_cast hℓ1
    positivity
  have hm3 : 0 < (m : ℝ) ^ 3 := by positivity
  have h1 : 1 / (m : ℝ) ^ 3 ≤ 1 / ((T'.card : ℝ) * P.card) :=
    one_div_le_one_div_of_le hkl0 hkl
  have h2 : 1 / (m : ℝ) ^ 3 * w ≤ 1 / ((T'.card : ℝ) * P.card) * N :=
    mul_le_mul h1 hNw hw0.le (by positivity)
  have h3 : c * δ' ^ 2 ≤ (1 - Real.sqrt ζ) / (m : ℝ) ^ 3 * δ' ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have h4 : (1 - Real.sqrt ζ) / (m : ℝ) ^ 3 * δ' ^ 2 = 1 / (m : ℝ) ^ 3 * w := by
    rw [hw]; ring
  linarith

end S9dCoeff

end TrackB
end RestrictedPolynomials
end
