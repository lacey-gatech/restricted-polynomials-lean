module

public import RestrictedPolynomials.TrackB.S9ReduceBetaAux

/-!
# Track B: Lemma `reduce_beta` and its iteration (paper IV, Section 8)

Source: paper IV (`writeup_stability.tex`), l. 4504-4510 (Lemma 8.1), 4881-4885, 4987-5005 (parameters,
dominant character), 5210-5237 (Lemma 8.12). Second half of the formalization of this part (the first
half is `S9ReduceBetaAux`, imported here), with the following choices:

* `s9_reduce_beta` discharges `hadd` by `s8_additive_base_case`.
* `ε < 1` in the existentials of `s9_reduce_beta` and `s9_beta_bound_iterated`
  (`s9_beta_bound_iterated_stopping` already had it); `c ≤ 1` is used from `s8_additive_base_case`.
* `ε ≤ c / 2` is part of `s9_parameter_hierarchy` (the source leaves it unstated); the doubled constant
  `C_m := 2 m⁴` is used.
* The statements hold for all `n ≥ d ≥ d'`, including `d = 0`, `d' = 0`.
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

/-! ### Real-analytic steps (no setting) -/

section S9Analytic

/-- Paper IV `lem:reduce-beta#parameter-hierarchy` (l. 4881-4885, left implicit in the source): the parameters are
chosen in the order `c`, `C_m`, then `τ`, `η`, `ε`, `L = 10/η`, subject to the constraints the proof
uses: `1 - τ + C_m √η ≤ 1 - τ/2 ≤ 1 - ε` (`Cm * √η ≤ τ/2`, `ε ≤ τ/2`), `ε ≤ c/2` (never stated in
the source), `1/2 + 4 C_m √η / c ≤ 1 - 6τ` (`s9_bound_calculus`), `6τ ≤ 1/2`. They depend only on
`(c, C_m)`, hence on `(m, α)`. The consumer (`s9_reduce_beta`) applies it with `c` of
`s8_additive_base_case` (replaced by `min c 1`) and `C_m := 2 m⁴ ≥ 2 |Γ×Φ||Γ||Φ|`. -/
theorem s9_parameter_hierarchy {c Cm : ℝ} (hc : 0 < c) (hCm : 0 ≤ Cm) :
    ∃ τ η ε L : ℝ, 0 < τ ∧ 6 * τ ≤ 1 / 2 ∧ 0 < η ∧ 0 < ε ∧ ε ≤ c / 2 ∧ ε ≤ τ / 2 ∧
      Cm * Real.sqrt η ≤ τ / 2 ∧ 1 / 2 + 4 * Cm / c * Real.sqrt η ≤ 1 - 6 * τ ∧ L = 10 / η := by
  set s : ℝ := min (1 / (48 * (Cm + 1))) (c / (16 * (Cm + 1))) with hs
  have hCm1 : 0 < Cm + 1 := by linarith
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  have hs1 : s ≤ 1 / (48 * (Cm + 1)) := min_le_left _ _
  have hs2 : s ≤ c / (16 * (Cm + 1)) := min_le_right _ _
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs0.le
  refine ⟨1 / 24, s ^ 2, min (c / 2) (1 / 48), 10 / s ^ 2, by norm_num, by norm_num, by positivity,
    lt_min (by positivity) (by norm_num), (min_le_left _ _), ?_, ?_, ?_, rfl⟩
  · exact (min_le_right _ _).trans (by norm_num)
  · rw [hsq]
    have : Cm * s ≤ (Cm + 1) * (1 / (48 * (Cm + 1))) :=
      mul_le_mul (by linarith) hs1 hs0.le hCm1.le
    have h2 : (Cm + 1) * (1 / (48 * (Cm + 1))) = 1 / 48 := by field_simp
    linarith
  · rw [hsq]
    have h1 : 16 * (Cm + 1) * s ≤ c := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 16 * (Cm + 1))).1 hs2
      linarith
    have h3 : 4 * Cm / c * s = 4 * Cm * s / c := by ring
    rw [h3]
    have h4 : 4 * Cm * s / c ≤ 1 / 4 := by
      rw [div_le_iff₀ hc]
      nlinarith
    linarith

private lemma sd_amgm {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    p * q * r ≤ ((p + q + r) / 3) ^ 3 := by
  nlinarith [mul_nonneg hp (sq_nonneg (q - r)), mul_nonneg hq (sq_nonneg (p - r)),
    mul_nonneg hr (sq_nonneg (p - q)), mul_nonneg (add_nonneg (add_nonneg hp hq) hr)
      (add_nonneg (add_nonneg (sq_nonneg (p - q)) (sq_nonneg (q - r))) (sq_nonneg (p - r)))]

private lemma sd_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- Paper IV `lem:reduce-beta#select-dominant-character` (l. 4987-5005): Hölder with exponents `(3,3,3)`.
If `∑|a_i b_i c_i| > 1 - τ` and each of `a, b, c` has `∑ |·|² ≤ 1`, some `i*` has
`|a b c|^{1/3} ≥ 1 - τ` and `|a|, |b|, |c| ≥ 1 - 3τ` (as each is `≤ 1`). -/
theorem s9_select_dominant_character {ι : Type} [Fintype ι] (a b c : ι → ℂ) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (ha : ∑ i, ‖a i‖ ^ 2 ≤ 1) (hb : ∑ i, ‖b i‖ ^ 2 ≤ 1)
    (hc : ∑ i, ‖c i‖ ^ 2 ≤ 1) (hsum : 1 - τ < ∑ i, ‖a i * b i * c i‖) :
    ∃ i : ι, 1 - τ ≤ ‖a i * b i * c i‖ ^ ((1 : ℝ) / 3) ∧ 1 - 3 * τ ≤ ‖a i‖ ∧
      1 - 3 * τ ≤ ‖b i‖ ∧ 1 - 3 * τ ≤ ‖c i‖ := by
  have _ := hτ
  have hnorm : ∀ i, ‖a i * b i * c i‖ = ‖a i‖ * ‖b i‖ * ‖c i‖ := fun i => by
    rw [norm_mul, norm_mul]
  have hu3 : ∀ i, (‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 3 = ‖a i‖ * ‖b i‖ * ‖c i‖ := fun i => by
    rw [sd_cube (norm_nonneg _), hnorm]
  have hu0 : ∀ i, 0 ≤ ‖a i * b i * c i‖ ^ ((1 : ℝ) / 3) := fun i =>
    Real.rpow_nonneg (norm_nonneg _) _
  have hu2 : ∀ i, (‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 2 ≤
      (‖a i‖ ^ 2 + ‖b i‖ ^ 2 + ‖c i‖ ^ 2) / 3 := fun i => by
    have h6 : ((‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 2) ^ 3 ≤
        ((‖a i‖ ^ 2 + ‖b i‖ ^ 2 + ‖c i‖ ^ 2) / 3) ^ 3 := by
      have : ((‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 2) ^ 3 =
          ‖a i‖ ^ 2 * ‖b i‖ ^ 2 * ‖c i‖ ^ 2 := by
        calc ((‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 2) ^ 3
            = ((‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 3) ^ 2 := by ring
          _ = (‖a i‖ * ‖b i‖ * ‖c i‖) ^ 2 := by rw [hu3]
          _ = _ := by ring
      rw [this]
      exact sd_amgm (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by norm_num)).1 h6
  have hle1 : ∀ (f : ι → ℂ), ∑ i, ‖f i‖ ^ 2 ≤ 1 → ∀ i, ‖f i‖ ≤ 1 := fun f hf i => by
    have h1 : ‖f i‖ ^ 2 ≤ 1 :=
      (Finset.single_le_sum (f := fun i => ‖f i‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ i)).trans hf
    by_contra hh
    push Not at hh
    nlinarith [norm_nonneg (f i)]
  have hA : ∃ i, 1 - τ ≤ ‖a i * b i * c i‖ ^ ((1 : ℝ) / 3) := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ i, ‖a i * b i * c i‖ ≤
        ∑ i, (1 - τ) * ((‖a i‖ ^ 2 + ‖b i‖ ^ 2 + ‖c i‖ ^ 2) / 3) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have e : ‖a i * b i * c i‖ = (‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) *
          (‖a i * b i * c i‖ ^ ((1 : ℝ) / 3)) ^ 2 := by
        rw [← pow_succ', hu3, hnorm]
      rw [e]
      exact mul_le_mul (hcon i).le (hu2 i) (sq_nonneg _) (by linarith)
    have h2 : ∑ i, (1 - τ) * ((‖a i‖ ^ 2 + ‖b i‖ ^ 2 + ‖c i‖ ^ 2) / 3) ≤ 1 - τ := by
      rw [← Finset.mul_sum]
      have : ∑ i, ((‖a i‖ ^ 2 + ‖b i‖ ^ 2 + ‖c i‖ ^ 2) / 3) ≤ 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib]
        linarith
      nlinarith
    linarith
  obtain ⟨i, hi⟩ := hA
  have ha1 := hle1 a ha i
  have hb1 := hle1 b hb i
  have hc1 := hle1 c hc i
  have hprod : (1 - τ) ^ 3 ≤ ‖a i‖ * ‖b i‖ * ‖c i‖ := by
    rw [← hu3 i]
    exact pow_le_pow_left₀ (by linarith) hi 3
  have hb0 := norm_nonneg (b i)
  have hc0 := norm_nonneg (c i)
  have ha0 := norm_nonneg (a i)
  have hbern : 1 - 3 * τ ≤ (1 - τ) ^ 3 := by nlinarith [sq_nonneg τ, mul_nonneg hτ.le (sq_nonneg τ)]
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ha0 (mul_nonneg hb0 hc0), mul_le_mul_of_nonneg_left hb1 ha0,
      mul_nonneg hb0 hc0, mul_le_mul hb1 hc1 hc0 zero_le_one]
  · nlinarith [mul_nonneg ha0 (mul_nonneg hb0 hc0), mul_le_mul_of_nonneg_left ha1 hb0,
      mul_nonneg ha0 hc0, mul_le_mul ha1 hc1 hc0 zero_le_one]
  · nlinarith [mul_nonneg ha0 (mul_nonneg hb0 hc0), mul_nonneg ha0 hb0,
      mul_le_mul ha1 hb1 hb0 zero_le_one]

end S9Analytic

/-! ### Lemma `reduce_beta` and its iteration -/

section RBAux
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {K₁ K₂ : Type}

private lemma rb_cl2norm_smul {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (π : FinProb α) (a : ℂ) (f : (ι → α) → ℂ) :
    cl2norm π (a • f) = ‖a‖ * cl2norm π f := by
  unfold cl2norm cl2sq FinProb.expect
  have : ∑ x, (π.pi ι).prob x * ‖(a • f) x‖ ^ 2 = ‖a‖ ^ 2 * ∑ x, (π.pi ι).prob x * ‖f x‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma rb_corrF_smul {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (a b c : ℂ) (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    s7CorrF μ (a • F) (b • g) (c • h) = a * b * c * s7CorrF μ F g h := by
  unfold s7CorrF FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq X] in
private lemma rb_ccCoef_smul (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {J : Type}
    {ι : Type} [Fintype ι] [DecidableEq ι] (u : J → X → ℂ) (a : ℂ) (F : (ι → Y × Z) → ℂ)
    (c : ι → J) : s7CCCoef μ hμ u (a • F) c = a * s7CCCoef μ hμ u F c := by
  unfold s7CCCoef
  exact cinner_smul_left _ _ _ _

private lemma rb_coef_smul {α : Type} [Fintype α] (D : FinProb α) {J : Type} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u : J → α → ℂ) (a : ℂ) (f : (ι → α) → ℂ) (c : ι → J) :
    s7Coef D u (a • f) c = a * s7Coef D u f c := by
  unfold s7Coef
  exact cinner_smul_left _ _ _ _

omit [DecidableEq X] [DecidableEq H] in
private lemma rb_ccPreds_smul (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℂ)
    (F : (ι → Y × Z) → ℂ) :
    ((∃ Dtot, S7CCCompEmbedHom μ hμ u F Dtot) → ∃ Dtot, S7CCCompEmbedHom μ hμ u (a • F) Dtot) ∧
    (∀ d, S7CCNeHom μ hμ u F d → S7CCNeHom μ hμ u (a • F) d) ∧
    (∀ d, S7CCEffDegGE μ hμ u F d → S7CCEffDegGE μ hμ u (a • F) d) ∧
    (S7ConstOnCC hμ F → S7ConstOnCC hμ (a • F)) := by
  have key : ∀ c, s7CCCoef μ hμ u (a • F) c ≠ 0 → s7CCCoef μ hμ u F c ≠ 0 := fun c hc h0 =>
    hc (by rw [rb_ccCoef_smul, h0, mul_zero])
  refine ⟨?_, fun d h c hc => h c (key c hc), fun d h c hc => h c (key c hc), ?_⟩
  · rintro ⟨Dtot, Da, hs, hDa⟩
    exact ⟨Dtot, Da, hs, fun c hc => hDa c (key c hc)⟩
  · rintro ⟨f, rfl⟩
    exact ⟨a • f, rfl⟩

omit [DecidableEq H] in
private lemma rb_plainPreds_smul {α : Type} [Fintype α] (D : FinProb α)
    (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℂ)
    (f : (ι → α) → ℂ) :
    ((∃ Dtot, S7CompEmbedHom D u f Dtot) → ∃ Dtot, S7CompEmbedHom D u (a • f) Dtot) ∧
    (∀ d, S7NeHom D u f d → S7NeHom D u (a • f) d) := by
  have key : ∀ c, s7Coef D u (a • f) c ≠ 0 → s7Coef D u f c ≠ 0 := fun c hc h0 =>
    hc (by rw [rb_coef_smul, h0, mul_zero])
  refine ⟨?_, fun d h c hc => h c (key c hc)⟩
  rintro ⟨Dtot, Da, hs, hDa⟩
  exact ⟨Dtot, Da, hs, fun c hc => hDa c (key c hc)⟩

omit [DecidableEq Y] [DecidableEq Z] in
/-- every letter occurs in `μ` (from positivity of the `x`-marginal). -/
private lemma rb_occ (μ : FinProb (X × Y × Z)) (hDx : ∀ a, 0 < (lawX μ).prob a) :
    ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support := by
  intro x
  by_contra hcon
  push Not at hcon
  have h0 : (lawX μ).prob x = 0 := by
    show ∑ p ∈ univ.filter (fun p : X × Y × Z => p.1 = x), μ.prob p = 0
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨x', y, z⟩ := p
    have hx : x' = x := (Finset.mem_filter.1 hp).2
    subst hx
    have := hcon y z
    by_contra hne
    exact this hne
  exact (hDx x).ne' h0

omit [DecidableEq Y] [DecidableEq Z] in
/-- the numeric constant `|Y × Z| |Y| |Z| ≤ m⁴`. -/
private lemma rb_card_le {m : ℕ} (hY : Fintype.card Y ≤ m) (hZ : Fintype.card Z ≤ m) :
    ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z) ≤ (m : ℝ) ^ 4 := by
  have h : Fintype.card Y * Fintype.card Z * Fintype.card Y * Fintype.card Z ≤ m * m * m * m :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hY hZ) hY) hZ
  have h' : ((Fintype.card Y * Fintype.card Z * Fintype.card Y * Fintype.card Z : ℕ) : ℝ) ≤
      ((m * m * m * m : ℕ) : ℝ) := by exact_mod_cast h
  rw [Fintype.card_prod]
  push_cast at h' ⊢
  nlinarith [h']

end RBAux
/-- Paper IV `lem:reduce-beta` (Lemma 8.1, l. 4504-4510), in the printed `max` form for all
`n ≥ d ≥ d'` including `d = 0`, `d' = 0` (`d - 1`, `d' - 1`, `n - 1` truncated in `ℕ`, which for
`d = 0` or `d' = 0` is absorbed by the first term of the `max`).
`∀ m α ∃ ε L` and then `μ` "as in Thm 7.14": atoms `≥ α`, alphabets of size `≤ m`, pairwise connected
(3), the saturated master embedding `(σ, γ, φ)` into `∀ i, Hs i` with the uniform law of hypothesis 4,
`μ_{y,z}` uniform and full (5), `y, z ⇒ x` (7: `hμ` packages 5 and 7), `σ` constant on `Sm` (item 1 of
the relaxed base case), the three bases of Def. 7.1 for ALL picks, and positivity of the
three marginals. Items 2, 3 of Def. relaxed_base (`|Σ_modest| ≥ 2` and the gain) and hypotheses 6, 8, 9
are not used by the proof and are not assumed (a strengthening). `ε`, `L` do not depend on
`(Hs, σ, γ, φ)`. -/
theorem s9_reduce_beta (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ ε L : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < L ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        PairwiseConnected3 μ.support →
        (∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ hμ : S7YZImpliesX μ.support,
        (∀ a, 0 < (lawX μ).prob a) → (∀ a, 0 < (lawY μ).prob a) → (∀ a, 0 < (lawZ μ).prob a) →
        ∀ {s : ℕ} (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
          [∀ i, DecidableEq (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i),
        IsMasterEmbedding μ.support Hs σ γ φ → IsSaturated3 σ γ φ →
        (∀ a b c : ∀ i, Hs i,
          ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)),
            μ.prob p = if a + b + c = 0 then 1 / (Fintype.card (∀ i, Hs i) : ℝ) ^ 2 else 0) →
        ∀ (Sm : Finset X), (∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') →
        ∀ (Bx : S7ModestBasis (lawX μ) σ Sm) (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
          (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (n d d' : ℕ), d' ≤ d → d ≤ n →
          L * d ≤ n →
          s7Beta μ hμ Bx.u By.u Bz.u n d d' ≤
            max (s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d')
              (ENNReal.ofReal (1 - ε) * s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1)) := by
  classical
  obtain ⟨c, hc0, hc1, hadd⟩ := s8_additive_base_case m hα
  obtain ⟨τ, η, ε, L, hτ, hτ6, hη, hε, hεc, hετ, hCη, hhier, hL⟩ :=
    s9_parameter_hierarchy (c := c) (Cm := 2 * (m : ℝ) ^ 4) hc0 (by positivity)
  have hε1 : ε < 1 := by linarith
  have hLpos : 0 < L := by rw [hL]; positivity
  refine ⟨ε, L, hε, hε1, hLpos, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hat hpc hu hμ hDx hDy hDz s Hs _ _ _ σ γ φ hM hsat hunif Sm
    hconst Bx By Bz n d d' hdd hdn hLd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : d = 0 := by omega
    obtain rfl : d' = 0 := by omega
    exact le_max_of_le_left le_rfl
  have hind := s8_hind_of_uniform μ hu
  have hKm := rb_card_le (Y := Y) (Z := Z) hY hZ
  have hsq : 0 ≤ Real.sqrt η := Real.sqrt_nonneg η
  have hb0fin : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (s7_beta_le_one μ hμ hind _ _ _ _ _ _)
  have hb1fin : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (s7_beta_le_one μ hμ hind _ _ _ _ _ _)
  set b0 : ℝ := (s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d').toReal with hb0def
  set b1 : ℝ := (s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1)).toReal with hb1def
  have hb0 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' ≤ ENNReal.ofReal b0 :=
    (ENNReal.ofReal_toReal hb0fin).ge
  have hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1 :=
    (ENNReal.ofReal_toReal hb1fin).ge
  have hb0nn : 0 ≤ b0 := ENNReal.toReal_nonneg
  have hb1nn : 0 ≤ b1 := ENNReal.toReal_nonneg
  have hRnn : 0 ≤ max b0 ((1 - ε) * b1) := le_max_of_le_left hb0nn
  have hRle : ENNReal.ofReal (max b0 ((1 - ε) * b1)) ≤
      max (s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d')
        (ENNReal.ofReal (1 - ε) * s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1)) := by
    have e0 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' = ENNReal.ofReal b0 :=
      (ENNReal.ofReal_toReal hb0fin).symm
    have e1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) = ENNReal.ofReal b1 :=
      (ENNReal.ofReal_toReal hb1fin).symm
    rw [e0, e1, ← ENNReal.ofReal_mul (by linarith)]
    rcases le_total b0 ((1 - ε) * b1) with h | h
    · rw [max_eq_right h]; exact le_max_of_le_right le_rfl
    · rw [max_eq_left h]; exact le_max_of_le_left le_rfl
  refine le_trans ?_ hRle
  -- the unit-triple bound
  have hocc := rb_occ μ hDx
  have hτ1 : τ ≤ 1 := by linarith
  have hτ3 : 3 * τ ≤ 1 := by linarith
  have core : ∀ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
      F ∈ s7ClassF μ hμ Bx.u n d d' → g ∈ s7ClassG (lawY μ) By.u n →
      h ∈ s7ClassG (lawZ μ) Bz.u n → cl2norm (s7LawYZ μ) F = 1 → cl2norm (lawY μ) g = 1 →
      cl2norm (lawZ μ) h = 1 → ‖s7CorrF μ F g h‖ ≤ max b0 ((1 - ε) * b1) := by
    intro F g h hF hg hh nF ng nh
    obtain ⟨hFcc, hFe, hFn, hFd⟩ := hF
    obtain ⟨hge, dg, hgd⟩ := hg
    obtain ⟨hhe, dh, hhd⟩ := hh
    have hnd : 10 * (d : ℝ) ≤ η * n := by
      have h1 : η * L = 10 := by rw [hL]; field_simp
      have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [mul_le_mul_of_nonneg_left hLd hη.le]
    obtain ⟨j, hj⟩ := s9_choose_partition μ hμ hDx hocc σ Sm Bx hn F hFcc d hFn nF hη hnd
    obtain ⟨S⟩ := s9_svd3_exists μ hμ hDx hDy hDz σ γ φ Sm Bx By Bz j F g h d d' dg dh hFcc hFe
      hFn hFd nF hge hgd ng hhe hhd nh
    have hsmall : ∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2 ≤ η := by
      have := s8_coefs_svd_effective μ hμ hocc σ j F hFcc S.ψ S.FI S.FJ S.decF
        (fun χ => by rw [S.FJ_chi]; exact Submodule.mem_span_singleton_self _)
        (fun r χ => S.FJ_t r χ) S.F_cc S.orthF_I S.orthF_J
      linarith
    by_cases hdiag : ∑ χ : AddChar (∀ i, Hs i) ℂ,
        ‖S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ)‖ ≤ 1 - τ
    · have hh1 : (1 - τ) + ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z) *
          Real.sqrt η ≤ 1 - ε := by
        nlinarith [mul_le_mul_of_nonneg_right hKm hsq]
      have := s9_diagonal_small_beta S hFe hDy hDz hunif hind hb0nn hb1nn hb0 hb1 hε1.le hη.le
        hsmall hdiag hh1
      refine this.trans ?_
      rcases le_total b1 b0 with h | h
      · rw [max_eq_right h]
        exact le_trans (by nlinarith) (le_max_left _ _)
      · rw [max_eq_left h]
        exact le_max_right _ _
    · have hdiag' := lt_of_not_ge hdiag
      have hsa : ∑ χ : AddChar (∀ i, Hs i) ℂ, ‖S.ψ (Sum.inl χ)‖ ^ 2 ≤ 1 := by
        have := S.normF
        rw [Fintype.sum_sum_type] at this
        have h2 : 0 ≤ ∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      have hsb : ∑ χ : AddChar (∀ i, Hs i) ℂ, ‖S.κ (Sum.inl χ)‖ ^ 2 ≤ 1 := by
        have := S.normG
        rw [Fintype.sum_sum_type] at this
        have h2 : 0 ≤ ∑ t : Fin S.sG, ‖S.κ (Sum.inr t)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      have hsc : ∑ χ : AddChar (∀ i, Hs i) ℂ, ‖S.ρ (Sum.inl χ)‖ ^ 2 ≤ 1 := by
        have := S.normH
        rw [Fintype.sum_sum_type] at this
        have h2 : 0 ≤ ∑ t : Fin S.sH, ‖S.ρ (Sum.inr t)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      obtain ⟨χs, -, -, hκs, hρs⟩ := s9_select_dominant_character (fun χ => S.ψ (Sum.inl χ))
        (fun χ => S.κ (Sum.inl χ)) (fun χ => S.ρ (Sum.inl χ)) hτ hτ1 hsa hsb hsc hdiag'
      have hh2 : 1 / 2 + 4 * (2 * ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y *
          Fintype.card Z)) / c * Real.sqrt η ≤ 1 - 6 * τ := by
        refine le_trans ?_ hhier
        have : 4 * (2 * ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z)) / c *
            Real.sqrt η ≤ 4 * (2 * (m : ℝ) ^ 4) / c * Real.sqrt η := by gcongr
        linarith
      have hadd' := hadd X Y Z hX hY hZ μ hat hpc hu Hs σ γ φ hM hsat hunif
      have := s9_assemble_bound_of_additive_base S hFe hDx hDy hDz hunif hind hc0 hc1 hadd' hb0nn
        hb1nn hτ hτ3 hη.le hb0 hb1 hsmall χs hκs hρs hh2
      refine this.trans (max_le ?_ (le_max_left _ _))
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_right (by linarith) hb1nn
  refine (s7Beta_le_iff μ hμ Bx.u By.u Bz.u n d d' hRnn).2 ?_
  intro F g h hF hg hh nF ng nh
  have haF : 0 < cl2norm (s7LawYZ μ) F := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm nF)
  have haG : 0 < cl2norm (lawY μ) g := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ng)
  have haH : 0 < cl2norm (lawZ μ) h := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm nh)
  set aF := cl2norm (s7LawYZ μ) F with haFdef
  set aG := cl2norm (lawY μ) g with haGdef
  set aH := cl2norm (lawZ μ) h with haHdef
  have cF : (aF : ℂ) ≠ 0 := by exact_mod_cast haF.ne'
  have cG : (aG : ℂ) ≠ 0 := by exact_mod_cast haG.ne'
  have cH : (aH : ℂ) ≠ 0 := by exact_mod_cast haH.ne'
  obtain ⟨hFcc, hFe, hFn, hFd⟩ := hF
  obtain ⟨hge, dg, hgd⟩ := hg
  obtain ⟨hhe, dh, hhd⟩ := hh
  have pF := rb_ccPreds_smul μ hμ Bx.u ((aF : ℂ)⁻¹) F
  have pG := rb_plainPreds_smul (lawY μ) By.u ((aG : ℂ)⁻¹) g
  have pH := rb_plainPreds_smul (lawZ μ) Bz.u ((aH : ℂ)⁻¹) h
  have key := core (((aF : ℂ)⁻¹) • F) (((aG : ℂ)⁻¹) • g) (((aH : ℂ)⁻¹) • h)
    ⟨pF.2.2.2 hFcc, pF.1 hFe, pF.2.1 d hFn, pF.2.2.1 d' hFd⟩
    ⟨pG.1 hge, dg, pG.2 dg hgd⟩ ⟨pH.1 hhe, dh, pH.2 dh hhd⟩
    (by rw [rb_cl2norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg haF.le]
        exact inv_mul_cancel₀ haF.ne')
    (by rw [rb_cl2norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg haG.le]
        exact inv_mul_cancel₀ haG.ne')
    (by rw [rb_cl2norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg haH.le]
        exact inv_mul_cancel₀ haH.ne')
  rw [rb_corrF_smul] at key
  have hn : ‖(aF : ℂ)⁻¹ * (aG : ℂ)⁻¹ * (aH : ℂ)⁻¹ * s7CorrF μ F g h‖ =
      (aF * aG * aH)⁻¹ * ‖s7CorrF μ F g h‖ := by
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg haF.le,
      Real.norm_of_nonneg haG.le, Real.norm_of_nonneg haH.le]
    field_simp
  rw [hn] at key
  have hp : 0 < aF * aG * aH := by positivity
  rw [inv_mul_le_iff₀ hp] at key
  rw [mul_comm]
  exact key

/-! ### The iteration (Lemma 8.12): abstract counter argument -/

private lemma it_core (B : ℕ → ℕ → ℕ → ℝ≥0∞) (L : ℝ) (hL : 2 ≤ L) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hB1 : ∀ n d d', B n d d' ≤ 1)
    (hstep : ∀ n d d' : ℕ, d' ≤ d → d ≤ n → L * d ≤ n →
      B n d d' ≤ max (B (n - 1) d d') (ENNReal.ofReal (1 - ε) * B (n - 1) (d - 1) (d' - 1)))
    (d0 d'0 : ℕ) (hd : d'0 ≤ d0) :
    ∀ n d d' s : ℕ, d + s = d0 → d' + s = d'0 → d ≤ n →
      (ENNReal.ofReal (1 - ε) ^ s * B n d d' ≤ ENNReal.ofReal ((1 - ε) ^ ((d'0 : ℝ) / 2)) ∨
        ∃ e e' n' : ℕ, d0 ≤ 2 * e ∧ e ≤ d0 ∧ d'0 ≤ 2 * e' ∧ e' ≤ d'0 ∧ e' ≤ e ∧ e ≤ n' ∧
          (n' : ℝ) ≤ L * d0 ∧ L * d0 ≤ 2 * L * e ∧
          ENNReal.ofReal (1 - ε) ^ s * B n d d' ≤ B n' e e') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d d' s hds hd's hdn
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hr1 : ENNReal.ofReal (1 - ε) ≤ 1 := ENNReal.ofReal_le_one.2 (by linarith)
  by_cases h1 : d'0 ≤ 2 * s
  · left
    calc ENNReal.ofReal (1 - ε) ^ s * B n d d' ≤ ENNReal.ofReal (1 - ε) ^ s * 1 :=
          by gcongr; exact hB1 _ _ _
      _ = ENNReal.ofReal ((1 - ε) ^ s) := by
          rw [mul_one, ENNReal.ofReal_pow (by linarith)]
      _ ≤ ENNReal.ofReal ((1 - ε) ^ ((d'0 : ℝ) / 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.rpow_natCast]
          refine Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) ?_
          have : (d'0 : ℝ) ≤ 2 * s := by exact_mod_cast h1
          linarith
  · have h1 := not_le.1 h1
    by_cases h2 : L * (d : ℝ) ≤ n
    · have hd1 : 1 ≤ d := by omega
      have hn2 : 2 * d ≤ n := by
        have : (2 : ℝ) * d ≤ n := le_trans (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg d)) h2
        exact_mod_cast this
      have hs := hstep n d d' (by omega) hdn h2
      have K1 := ih (n - 1) (by omega) d d' s hds hd's (by omega)
      have K2 := ih (n - 1) (by omega) (d - 1) (d' - 1) (s + 1) (by omega) (by omega) (by omega)
      rcases max_choice (B (n - 1) d d')
          (ENNReal.ofReal (1 - ε) * B (n - 1) (d - 1) (d' - 1)) with h | h
      · rw [h] at hs
        have hs' : ENNReal.ofReal (1 - ε) ^ s * B n d d' ≤
            ENNReal.ofReal (1 - ε) ^ s * B (n - 1) d d' := by gcongr
        rcases K1 with K | ⟨e, e', n', a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
        · exact Or.inl (hs'.trans K)
        · exact Or.inr ⟨e, e', n', a1, a2, a3, a4, a5, a6, a7, a8, hs'.trans a9⟩
      · rw [h] at hs
        have hs' : ENNReal.ofReal (1 - ε) ^ s * B n d d' ≤
            ENNReal.ofReal (1 - ε) ^ (s + 1) * B (n - 1) (d - 1) (d' - 1) := by
          calc _ ≤ ENNReal.ofReal (1 - ε) ^ s *
                (ENNReal.ofReal (1 - ε) * B (n - 1) (d - 1) (d' - 1)) := by gcongr
            _ = _ := by rw [pow_succ, mul_assoc]
        rcases K2 with K | ⟨e, e', n', a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
        · exact Or.inl (hs'.trans K)
        · exact Or.inr ⟨e, e', n', a1, a2, a3, a4, a5, a6, a7, a8, hs'.trans a9⟩
    · right
      refine ⟨d, d', n, by omega, by omega, by omega, by omega, by omega, hdn, ?_, ?_, ?_⟩
      · have hdd : (d : ℝ) ≤ d0 := by exact_mod_cast (by omega : d ≤ d0)
        have h2 := not_le.1 h2
        nlinarith
      · have hdd : (d0 : ℝ) ≤ 2 * d := by exact_mod_cast (by omega : d0 ≤ 2 * d)
        nlinarith
      · calc ENNReal.ofReal (1 - ε) ^ s * B n d d' ≤ 1 * B n d d' :=
              by gcongr; exact pow_le_one' hr1 s
          _ = B n d d' := one_mul _

/-- Paper IV `lem:beta-bound-iterated#stopping-point-bounds` (left implicit in the source): the statement the iteration
proof actually proves, with `L ≥ 2` (wlog: `reduce_beta` for `L` implies it for larger `L`): either
`β ≤ (1 - ε)^{d'/2}` or there are `e, e', n'` with `d/2 ≤ e ≤ d`, `d'/2 ≤ e' ≤ d'`, `e' ≤ e ≤ n'`,
`n' ≤ L d ≤ 2 L e` and `β_{n,d,d'} ≤ β_{n',e,e'}` (same bases). The hypothesis `d' ≥ d^{1-ξ}` is as
printed and is not used. -/
theorem s9_beta_bound_iterated_stopping (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ L ε : ℝ, 2 ≤ L ∧ 0 < ε ∧ ε < 1 ∧ ∀ ξ : ℝ, 0 < ξ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        PairwiseConnected3 μ.support →
        (∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ hμ : S7YZImpliesX μ.support,
        (∀ a, 0 < (lawX μ).prob a) → (∀ a, 0 < (lawY μ).prob a) → (∀ a, 0 < (lawZ μ).prob a) →
        ∀ {s : ℕ} (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
          [∀ i, DecidableEq (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i),
        IsMasterEmbedding μ.support Hs σ γ φ → IsSaturated3 σ γ φ →
        (∀ a b c : ∀ i, Hs i,
          ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)),
            μ.prob p = if a + b + c = 0 then 1 / (Fintype.card (∀ i, Hs i) : ℝ) ^ 2 else 0) →
        ∀ (Sm : Finset X), (∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') →
        ∀ (Bx : S7ModestBasis (lawX μ) σ Sm) (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
          (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (n d d' : ℕ), d' ≤ d → d ≤ n →
          (d : ℝ) ^ (1 - ξ) ≤ d' →
          s7Beta μ hμ Bx.u By.u Bz.u n d d' ≤ ENNReal.ofReal ((1 - ε) ^ ((d' : ℝ) / 2)) ∨
          ∃ e e' n' : ℕ, d ≤ 2 * e ∧ e ≤ d ∧ d' ≤ 2 * e' ∧ e' ≤ d' ∧ e' ≤ e ∧ e ≤ n' ∧
            (n' : ℝ) ≤ L * d ∧ L * d ≤ 2 * L * e ∧
            s7Beta μ hμ Bx.u By.u Bz.u n d d' ≤ s7Beta μ hμ Bx.u By.u Bz.u n' e e' := by
  classical
  obtain ⟨ε, L0, hε0, hε1, hL0, hred⟩ := s9_reduce_beta m hα
  refine ⟨max L0 2, ε, le_max_right _ _, hε0, hε1, ?_⟩
  intro ξ hξ X Y Z _ _ _ _ _ _ hX hY hZ μ hat hpc hu hμ hDx hDy hDz s Hs _ _ _ σ γ φ hM hsat
    hunif Sm hconst Bx By Bz n d d' hdd' hdn hξd
  have key := it_core (fun n d d' => s7Beta μ hμ Bx.u By.u Bz.u n d d') (max L0 2)
    (le_max_right _ _) ε hε0 hε1
    (fun n d d' => s7_beta_le_one μ hμ (s8_hind_of_uniform μ hu) Bx.u By.u Bz.u n d d')
    (fun n d d' h1 h2 h3 => hred X Y Z hX hY hZ μ hat hpc hu hμ hDx hDy hDz Hs σ γ φ hM hsat
      hunif Sm hconst Bx By Bz n d d' h1 h2
      (le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg d)) h3))
    d d' hdd' n d d' 0 (by omega) (by omega) hdn
  simpa using key

/-- Paper IV `lem:beta-bound-iterated` (Lemma 8.12, l. 5210-5237), as printed:
`∀ m α ∃ L ε ∀ ξ ...`, either `β ≤ (1 - ε)^{d'/2}` or `e ≥ d/2`, `e' ≥ d'/2`, `n' ≤ 2 L e` with
`β_{n,d,d'} ≤ β_{n',e,e'}`. (A consequence of `s9_beta_bound_iterated_stopping`; stated separately so
that the printed conclusion is a target of its own.) -/
theorem s9_beta_bound_iterated (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ L ε : ℝ, 0 < L ∧ 0 < ε ∧ ε < 1 ∧ ∀ ξ : ℝ, 0 < ξ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        PairwiseConnected3 μ.support →
        (∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ hμ : S7YZImpliesX μ.support,
        (∀ a, 0 < (lawX μ).prob a) → (∀ a, 0 < (lawY μ).prob a) → (∀ a, 0 < (lawZ μ).prob a) →
        ∀ {s : ℕ} (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
          [∀ i, DecidableEq (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i),
        IsMasterEmbedding μ.support Hs σ γ φ → IsSaturated3 σ γ φ →
        (∀ a b c : ∀ i, Hs i,
          ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)),
            μ.prob p = if a + b + c = 0 then 1 / (Fintype.card (∀ i, Hs i) : ℝ) ^ 2 else 0) →
        ∀ (Sm : Finset X), (∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') →
        ∀ (Bx : S7ModestBasis (lawX μ) σ Sm) (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
          (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (n d d' : ℕ), d' ≤ d → d ≤ n →
          (d : ℝ) ^ (1 - ξ) ≤ d' →
          s7Beta μ hμ Bx.u By.u Bz.u n d d' ≤ ENNReal.ofReal ((1 - ε) ^ ((d' : ℝ) / 2)) ∨
          ∃ e e' n' : ℕ, d ≤ 2 * e ∧ d' ≤ 2 * e' ∧ (n' : ℝ) ≤ 2 * L * e ∧
            s7Beta μ hμ Bx.u By.u Bz.u n d d' ≤ s7Beta μ hμ Bx.u By.u Bz.u n' e e' := by
  obtain ⟨L, ε, hL, hε0, hε1, h⟩ := s9_beta_bound_iterated_stopping m hα
  refine ⟨L, ε, by linarith, hε0, hε1, ?_⟩
  intro ξ hξ X Y Z _ _ _ _ _ _ hX hY hZ μ hat hpc hu hμ hDx hDy hDz s Hs _ _ _ σ γ φ hM hsat
    hunif Sm hconst Bx By Bz n d d' hdd' hdn hξd
  rcases h ξ hξ X Y Z hX hY hZ μ hat hpc hu hμ hDx hDy hDz Hs σ γ φ hM hsat hunif Sm hconst
    Bx By Bz n d d' hdd' hdn hξd with h1 | ⟨e, e', n', a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  · exact Or.inl h1
  · refine Or.inr ⟨e, e', n', a1, a3, a7.trans a8, a9⟩

end TrackB
end RestrictedPolynomials
end
