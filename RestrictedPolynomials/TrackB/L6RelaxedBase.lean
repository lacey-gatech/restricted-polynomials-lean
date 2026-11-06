module

public import RestrictedPolynomials.TrackB.MaxTStatements
public import RestrictedPolynomials.TrackB.L6RelaxedClaims
public import RestrictedPolynomials.TrackB.L6Rounding

/-!
# Track B: the relaxed base case for an abstract law

Paper IV `lem:nu-satisfies`, step `relaxed-base-case` (paper IV section 6.5.3, l. 3760-3970).

Readings.
* `2 ≤ Sm.card` (the definition's "size at least 2").
* the premises are normalised, `‖f‖₂ = ‖g‖₂ = ‖h‖₂ = 1`; the conclusion is literally clause 2 of `RelaxedBaseCase` at
  `C := ((50 * m : ℕ) : ℝ)`.
* one constant `c = c(m, α)` for all `τ > 0`.

Route.  For `τ ≤ T` (small) the proof is by contradiction through Claims 6.13-6.15, the logarithms,
common-`q` Dirichlet rounding and the exact relations (files 1 and 2).  For `T < τ` the premise forces
`τ ≤ 4/β`, and lowering `τ` to `T` gives the claim with a smaller constant.

All helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section L6Base

private theorem rb_mp_ge {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (π : FinProb A) (F : A → B) (a : A) : π.prob a ≤ (mergePush π F).prob (F a) := by
  show π.prob a ≤ ∑ a' ∈ univ.filter (fun a' => F a' = F a), π.prob a'
  exact Finset.single_le_sum (f := π.prob) (fun i _ => π.nonneg i)
    (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩)

private theorem rb_fx_bound {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    (ν : FinProb (X × Y × Z)) {β : ℝ}
    (hat : ∀ p ∈ ν.support, β ≤ ν.prob p) (hpc : PairwiseConnected3 ν.support) (f : X → ℂ)
    (hf : ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 = 1) (x : X) : β * ‖f x‖ ^ 2 ≤ 1 := by
  obtain ⟨y, z, hyz⟩ := PairwiseConnected3.exists_atom_x hpc x
  have h1 := hat _ hyz
  have h2 : ν.prob (x, y, z) ≤ (lawX ν).prob x := rb_mp_ge ν (fun p => p.1) (x, y, z)
  calc β * ‖f x‖ ^ 2 ≤ (lawX ν).prob x * ‖f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
    _ ≤ ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 :=
        Finset.single_le_sum (f := fun x => (lawX ν).prob x * ‖f x‖ ^ 2)
          (fun i _ => mul_nonneg ((lawX ν).nonneg i) (sq_nonneg _)) (Finset.mem_univ x)
    _ = 1 := hf

private theorem rb_var_ge_mass {X : Type} (Sm : Finset X) (hS : 0 < Sm.card) (f : X → ℂ) {τ : ℝ}
    (h : τ ≤ (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2) / (Sm.card : ℝ) ^ 2) :
    τ / 4 ≤ (∑ x ∈ Sm, ‖f x‖ ^ 2) / (Sm.card : ℝ) := by
  have hn : (0 : ℝ) < Sm.card := by exact_mod_cast hS
  rw [le_div_iff₀ (by positivity)] at h
  have hpt : ∀ x x' : X, ‖f x - f x'‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖f x'‖ ^ 2 := by
    intro x x'
    have h1 : ‖f x - f x'‖ ≤ ‖f x‖ + ‖f x'‖ := norm_sub_le _ _
    have h2 : ‖f x - f x'‖ ^ 2 ≤ (‖f x‖ + ‖f x'‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖f x‖ - ‖f x'‖)]
  have h3 : (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2) ≤
      ∑ x ∈ Sm, ∑ x' ∈ Sm, (2 * ‖f x‖ ^ 2 + 2 * ‖f x'‖ ^ 2) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hpt x x'
  have h4 : (∑ x ∈ Sm, ∑ x' ∈ Sm, (2 * ‖f x‖ ^ 2 + 2 * ‖f x'‖ ^ 2)) =
      4 * Sm.card * ∑ x ∈ Sm, ‖f x‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [le_div_iff₀ hn]
  have : τ * (Sm.card : ℝ) ^ 2 ≤ 4 * Sm.card * ∑ x ∈ Sm, ‖f x‖ ^ 2 := by linarith
  nlinarith

private theorem rb_var_le {X : Type} (Sm : Finset X) (hS : 0 < Sm.card) (f : X → ℂ) {D : ℝ}
    (hD : ∀ x x', ‖f x - f x'‖ ^ 2 ≤ D) :
    (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2) / (Sm.card : ℝ) ^ 2 ≤ D := by
  have hn : (0 : ℝ) < Sm.card := by exact_mod_cast hS
  rw [div_le_iff₀ (by positivity)]
  calc (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2)
      ≤ ∑ x ∈ Sm, ∑ x' ∈ Sm, D :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hD x x'
    _ = D * (Sm.card : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring


private theorem rb_param (m : ℕ) (hm : 1 ≤ m) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ≤ 1 / 32) (hτβ : τ ≤ β ^ 9 / 8) :
    ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, 1 ≤ q → q ≤ N →
      (q : ℝ) * (3 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) + 2 * τ ^ (10 * m)) < 1 ∧
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ)))) ≤ 1 / 8 ∧
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) ^ 2 ≤ (β * τ) ^ 3 := by
  have hβτ : 0 < β * τ := by positivity
  have hβτ32 : β * τ ≤ 1 / 32 := by nlinarith
  set a : ℝ := (β * τ)⁻¹ with ha
  have ha32 : 32 ≤ a := by
    rw [ha, le_inv_comm₀ (by norm_num) hβτ]
    simpa using hβτ32
  have ha1 : 1 ≤ a := by linarith
  have hapow : 1 ≤ a ^ (9 * m) := one_le_pow₀ ha1
  refine ⟨⌈a ^ (9 * m)⌉₊, Nat.ceil_pos.2 (by linarith), ?_⟩
  intro q hq1 hqN
  set N : ℕ := ⌈a ^ (9 * m)⌉₊ with hNdef
  have hNge : a ^ (9 * m) ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < a ^ (9 * m) + 1 := Nat.ceil_lt_add_one (by linarith)
  set M : ℝ := (N : ℝ) ^ (1 / (6 * (m : ℝ))) with hMdef
  have hM0 : 0 ≤ M := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hM6 : M ^ (6 * m) = N := by
    rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    have : 1 / (6 * (m : ℝ)) * ((6 * m : ℕ) : ℝ) = 1 := by
      push_cast
      have : (m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [this, Real.rpow_one]
  have hM2 : a ^ 3 ≤ M ^ 2 := by
    by_contra hlt
    push Not at hlt
    have h1 : (M ^ 2) ^ (3 * m) < (a ^ 3) ^ (3 * m) :=
      pow_lt_pow_left₀ hlt (by positivity) (by omega)
    rw [← pow_mul, ← pow_mul, show 2 * (3 * m) = 6 * m by ring, hM6,
      show 3 * (3 * m) = 9 * m by ring] at h1
    linarith
  have ha3 : 32768 ≤ a ^ 3 := by nlinarith [sq_nonneg a]
  have hM8 : 8 ≤ M := by nlinarith
  have hMpos : 0 < M := by linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqN' : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hε0 : 0 < 1 / ((q : ℝ) * M) := by positivity
  have hqε : (q : ℝ) * (1 / ((q : ℝ) * M)) = 1 / M := by field_simp
  have hεM : 1 / ((q : ℝ) * M) ≤ 1 / M := by
    rw [← hqε]; exact le_mul_of_one_le_left hε0.le hq1'
  have hM18 : 1 / M ≤ 1 / 8 := by rw [div_le_div_iff₀ hMpos (by norm_num)]; linarith
  have hid : a ^ (9 * m) * τ ^ (10 * m) = (τ / β ^ 9) ^ m := by
    rw [pow_mul, pow_mul, ← mul_pow]
    congr 1
    rw [ha]
    field_simp
  have hτb : τ / β ^ 9 ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hτb1 : (τ / β ^ 9) ^ m ≤ 1 / 8 :=
    (pow_le_of_le_one (by positivity) (hτb.trans (by norm_num)) (by omega)).trans hτb
  refine ⟨?_, hεM.trans hM18, ?_⟩
  · have h2 : (q : ℝ) * (2 * τ ^ (10 * m)) ≤ 4 * (τ / β ^ 9) ^ m := by
      rw [← hid]
      have : (0 : ℝ) ≤ τ ^ (10 * m) := by positivity
      nlinarith
    have h3 : 3 * ((q : ℝ) * (1 / ((q : ℝ) * M))) ≤ 3 / 8 := by
      rw [hqε]; linarith
    have h1 : (q : ℝ) * (3 * (1 / ((q : ℝ) * M)) + 2 * τ ^ (10 * m)) =
        3 * ((q : ℝ) * (1 / ((q : ℝ) * M))) + q * (2 * τ ^ (10 * m)) := by ring
    linarith
  · have h1 : (1 / ((q : ℝ) * M)) ^ 2 ≤ (1 / M) ^ 2 := pow_le_pow_left₀ hε0.le hεM 2
    have h2 : (1 / M) ^ 2 ≤ (β * τ) ^ 3 := by
      rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
      have : (β * τ) ^ 3 * a ^ 3 = 1 := by
        rw [← mul_pow, ha, mul_inv_cancel₀ hβτ.ne', one_pow]
      nlinarith [pow_pos hβτ 3]
    linarith

private theorem rb_pair {X : Type} (f : X → ℂ) {β τ ε : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hτ : 0 < τ) (hτ32 : τ ≤ 1 / 32) (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8)
    (hε2 : ε ^ 2 ≤ (β * τ) ^ 3) (hb : ∀ x, β * ‖f x‖ ^ 2 ≤ 1) (hf0 : ∀ x, f x ≠ 0)
    (a : X → ℂ) (happrox : ∀ x, ‖a x - Complex.log (starRingEnd ℂ (f x))‖ ≤ 7 * ε)
    (hconst : ∀ x x', Complex.exp (a x) = Complex.exp (a x')) :
    ∀ x x', ‖f x - f x'‖ ^ 2 ≤ 784 * τ ^ 3 := by
  have hclose : ∀ x, ‖starRingEnd ℂ (f x) - Complex.exp (a x)‖ ≤ 14 * ε * ‖f x‖ := by
    intro x
    have hne : starRingEnd ℂ (f x) ≠ 0 := by simpa using hf0 x
    set d : ℂ := a x - Complex.log (starRingEnd ℂ (f x)) with hd
    have hdn : ‖d‖ ≤ 7 * ε := happrox x
    have hd1 : ‖d‖ ≤ 1 := by linarith
    have hexp : Complex.exp (a x) = starRingEnd ℂ (f x) * Complex.exp d := by
      rw [hd, ← Complex.exp_log hne, ← Complex.exp_add, Complex.exp_log hne]
      congr 1
      ring
    have h1 := Complex.norm_exp_sub_one_le hd1
    calc ‖starRingEnd ℂ (f x) - Complex.exp (a x)‖
        = ‖starRingEnd ℂ (f x)‖ * ‖Complex.exp d - 1‖ := by
          rw [hexp]
          have e : starRingEnd ℂ (f x) - starRingEnd ℂ (f x) * Complex.exp d =
              -(starRingEnd ℂ (f x) * (Complex.exp d - 1)) := by ring
          rw [e, norm_neg, norm_mul]
      _ ≤ ‖f x‖ * (2 * (7 * ε)) := by
          rw [Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (norm_nonneg _)
      _ = 14 * ε * ‖f x‖ := by ring
  intro x x'
  have hcx := hclose x
  have hcx' := hclose x'
  have heq := hconst x x'
  have h1 : ‖f x - f x'‖ ≤ 14 * ε * (‖f x‖ + ‖f x'‖) := by
    have : ‖f x - f x'‖ = ‖starRingEnd ℂ (f x) - starRingEnd ℂ (f x')‖ := by
      rw [← map_sub, Complex.norm_conj]
    rw [this]
    calc ‖starRingEnd ℂ (f x) - starRingEnd ℂ (f x')‖
        = ‖(starRingEnd ℂ (f x) - Complex.exp (a x)) -
          (starRingEnd ℂ (f x') - Complex.exp (a x'))‖ := by
          rw [heq]; congr 1; ring
      _ ≤ _ := (norm_sub_le _ _).trans (by linarith)
  have hbx := hb x
  have hbx' := hb x'
  have h2 : ‖f x - f x'‖ ^ 2 ≤ (14 * ε * (‖f x‖ + ‖f x'‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : β * ‖f x - f x'‖ ^ 2 ≤ 784 * ε ^ 2 := by
    have h4 : β * (14 * ε * (‖f x‖ + ‖f x'‖)) ^ 2 ≤ 784 * ε ^ 2 := by
      have e : β * (14 * ε * (‖f x‖ + ‖f x'‖)) ^ 2 =
          196 * ε ^ 2 * (β * (‖f x‖ + ‖f x'‖) ^ 2) := by ring
      rw [e]
      have h5 : β * (‖f x‖ + ‖f x'‖) ^ 2 ≤ 4 := by
        nlinarith [sq_nonneg (‖f x‖ - ‖f x'‖)]
      nlinarith [sq_nonneg ε]
    nlinarith
  have h6 : β * ‖f x - f x'‖ ^ 2 ≤ β * (784 * τ ^ 3) := by
    have hb2 : β ^ 2 ≤ 1 := by nlinarith
    have e : (β * τ) ^ 3 = β * (β ^ 2 * τ ^ 3) := by ring
    have : β ^ 2 * τ ^ 3 ≤ τ ^ 3 := by nlinarith [pow_pos hτ 3]
    nlinarith [mul_le_mul_of_nonneg_left this hβ.le]
  exact le_of_mul_le_mul_left h6 hβ


private theorem rb_small (m : ℕ) (hm : 1 ≤ m) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 / 32 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ T →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, β ≤ ν.prob p) → InT ν.support →
        (∀ (y : Y) (z : Z), ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ Sm : Finset X, 2 ≤ Sm.card → (∀ x ∈ Sm, ∀ y : Y, ∃ z : Z, (x, y, z) ∈ ν.support) →
        ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ),
        ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 = 1 → ∑ y, (lawY ν).prob y * ‖g y‖ ^ 2 = 1 →
        ∑ z, (lawZ ν).prob z * ‖h z‖ ^ 2 = 1 →
        τ ≤ (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2) / (Sm.card : ℝ) ^ 2 →
        ‖∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ≤ 1 - τ ^ (50 * m) := by
  obtain ⟨c₂, hc₂, H2⟩ := l6_relaxed2_pointwise m hm hβ
  obtain ⟨c₃, c', hc₃, hc', H3⟩ := l6_relaxed3_g_lower m hm hβ
  obtain ⟨c₄, hc₄, H4⟩ := l6_relaxed4_lower m hm hβ hc'
  obtain ⟨c₅, hc₅, H5⟩ := l6_log_approx_embedding m hm hc'
  have hβ9 : 0 < β ^ 9 / 8 := by positivity
  refine ⟨min (1 / 32) (min c₂ (min c₃ (min c₄ (min c₅ (β ^ 9 / 8))))),
    lt_min (by norm_num) (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ (lt_min hc₅ hβ9)))),
    min_le_left _ _, ?_⟩
  intro τ hτ hτT X Y Z _ _ _ _ _ _ hX hY hZ ν hat hT hmarg Sm hSm2 h6c f g h hf hg hh hvar
  have hτ32 : τ ≤ 1 / 32 := hτT.trans (min_le_left _ _)
  have hτc₂ : τ ≤ c₂ := hτT.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτc₃ : τ ≤ c₃ :=
    hτT.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτc₄ : τ ≤ c₄ := hτT.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hτc₅ : τ ≤ c₅ := hτT.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hτβ : τ ≤ β ^ 9 / 8 := hτT.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hτ1 : τ < 1 := by linarith
  by_contra hcon
  push Not at hcon
  have hpow : τ ^ (50 * m) < 1 := pow_lt_one₀ hτ.le hτ1 (by omega)
  set E : ℂ := ∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2) with hE
  have hEpos : 0 < ‖E‖ := by linarith
  set u : ℂ := starRingEnd ℂ E / (‖E‖ : ℂ) with hu
  have hEne : (‖E‖ : ℂ) ≠ 0 := by exact_mod_cast hEpos.ne'
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos hEpos, div_self hEpos.ne']
  have huE : u * E = (‖E‖ : ℂ) := by
    rw [hu, div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hEne]
    ring
  set h' : Z → ℂ := fun z => u * h z with hh'def
  have hh'n : ∀ z, ‖h' z‖ = ‖h z‖ := fun z => by
    simp only [hh'def, norm_mul, hun, one_mul]
  have hh' : ∑ z, (lawZ ν).prob z * ‖h' z‖ ^ 2 = 1 := by
    simpa only [hh'n] using hh
  have hE' : ∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h' p.2.2) = u * E := by
    rw [hE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hh'def]
    ring
  have hre : 1 - τ ^ (50 * m) ≤
      (∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h' p.2.2)).re := by
    rw [hE', huE, Complex.ofReal_re]
    exact hcon.le
  have hpt := H2 τ hτ hτc₂ X Y Z ν hat hmarg f g h' hf hg hh' hre
  have hmass := rb_var_ge_mass Sm (by omega) f hvar
  have hglow := H3 τ hτ hτc₃ X Y Z ν hat Sm h6c f g h' hh' hmass hpt
  obtain ⟨j, hj, hfree, hhfree⟩ := l6_free_interval m hX hZ f h' hτ hτ1
  obtain ⟨hflow, hhlow⟩ :=
    H4 τ hτ hτc₄ X Y Z ν hat hT.1 f g h' hf hg hh' hpt hglow j hj hfree hhfree
  obtain ⟨hf0, hg0, hh0, -, hlog⟩ :=
    H5 τ hτ hτc₅ ν.support f g h' j hj hpt hglow hflow hhlow
  -- the rounding parameter
  obtain ⟨N, hN, hNq⟩ := rb_param m hm hβ hβ1 hτ hτ32 hτβ
  obtain ⟨q, σR, γR, φR, σI, γI, φI, hq1, hqN, hσR, hγR, hφR, hσI, hγI, hφI⟩ :=
    l6_dirichlet_common_q m hm hX hY hZ (fun x => Complex.log (starRingEnd ℂ (f x)))
      (fun y => Complex.log (g y)) (fun z => Complex.log (h' z)) hN
  obtain ⟨hsmall, hε8, hε2⟩ := hNq q hq1 hqN
  have hε0 : 0 < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ)))) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < q := by exact_mod_cast hq1
    positivity
  obtain ⟨hRI, happrox⟩ := l6_imaginary_rounding_mod_q ν.support
    (fun x => Complex.log (starRingEnd ℂ (f x))) (fun y => Complex.log (g y))
    (fun z => Complex.log (h' z)) (2 * τ ^ (10 * m)) _ q hq1 σR γR φR σI γI φI
    (fun p hp => hlog p hp) hσR hγR hφR hσI hγI hφI hsmall
  obtain ⟨-, -, hconst⟩ := l6_rounded_triple_const ν.support hT q hq1 σR γR φR σI γI φI
    (fun p hp => (hRI p hp).1) (fun p hp => (hRI p hp).2)
  have hpair := rb_pair f hβ hβ1 hτ hτ32 hε0 hε8 hε2 (rb_fx_bound ν hat hT.1 f hf) hf0
    (fun x => ((σR x : ℂ) + 2 * Real.pi * Complex.I * (σI x : ℂ)) / q) happrox hconst
  have hv := rb_var_le Sm (by omega) f hpair
  have hτ2 : τ ^ 2 ≤ 1 / 1024 := by nlinarith
  have : 784 * τ ^ 3 < τ := by nlinarith [pow_pos hτ 3]
  linarith

/-- paper IV `lem:nu-satisfies`, step `relaxed-base-case` (§6.5.3): the gain `1 - c τ^{50 m}`, in the unfolded
form of clause 2 of `RelaxedBaseCase` (normalised premises). -/
theorem l6_relaxed_base_case_core (m : ℕ) (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) → InT ν.support →
        (∀ (y : Y) (z : Z), ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ Sm : Finset X, 2 ≤ Sm.card → (∀ x ∈ Sm, ∀ y : Y, ∃ z : Z, (x, y, z) ∈ ν.support) →
        ∀ τ : ℝ, 0 < τ → ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ),
        ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 = 1 → ∑ y, (lawY ν).prob y * ‖g y‖ ^ 2 = 1 →
        ∑ z, (lawZ ν).prob z * ‖h z‖ ^ 2 = 1 →
        τ ≤ (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2) / (Sm.card : ℝ) ^ 2 →
        ‖∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ≤
          1 - c * τ ^ ((50 * m : ℕ) : ℝ) := by
  have hβ : 0 < min α 1 := lt_min hα one_pos
  have hβ1 : min α 1 ≤ 1 := min_le_right _ _
  obtain ⟨T, hT0, hT32, H⟩ := rb_small m hm hβ hβ1
  set β := min α 1 with hβdef
  refine ⟨min 1 ((T * β / 4) ^ (50 * m)), lt_min one_pos (by positivity), ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ ν hat hT hmarg Sm hSm2 h6c τ hτ f g h hf hg hh hvar
  rw [Real.rpow_natCast]
  have hat' : ∀ p ∈ ν.support, β ≤ ν.prob p := fun p hp => (min_le_left _ _).trans (hat p hp)
  have hcpos : 0 ≤ min 1 ((T * β / 4) ^ (50 * m)) := le_min zero_le_one (by positivity)
  by_cases hτT : τ ≤ T
  · have h1 := H τ hτ hτT X Y Z hX hY hZ ν hat' hT hmarg Sm hSm2 h6c f g h hf hg hh hvar
    have h2 : min 1 ((T * β / 4) ^ (50 * m)) * τ ^ (50 * m) ≤ τ ^ (50 * m) :=
      mul_le_of_le_one_left (by positivity) (min_le_left _ _)
    linarith
  · push Not at hτT
    have h1 := H T hT0 le_rfl X Y Z hX hY hZ ν hat' hT hmarg Sm hSm2 h6c f g h hf hg hh
      (hτT.le.trans hvar)
    have hb : ∀ x x', ‖f x - f x'‖ ^ 2 ≤ 4 * (1 / β) := by
      intro x x'
      have hx := rb_fx_bound ν hat' hT.1 f hf x
      have hx' := rb_fx_bound ν hat' hT.1 f hf x'
      have e1 : ‖f x‖ ^ 2 ≤ 1 / β := by rw [le_div_iff₀ hβ]; linarith
      have e2 : ‖f x'‖ ^ 2 ≤ 1 / β := by rw [le_div_iff₀ hβ]; linarith
      have h3 : ‖f x - f x'‖ ≤ ‖f x‖ + ‖f x'‖ := norm_sub_le _ _
      have h4 : ‖f x - f x'‖ ^ 2 ≤ (‖f x‖ + ‖f x'‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [sq_nonneg (‖f x‖ - ‖f x'‖)]
    have hτle : τ ≤ 4 * (1 / β) := hvar.trans (rb_var_le Sm (by omega) f hb)
    have h5 : T * β / 4 * τ ≤ T := by
      have : τ * β ≤ 4 := by
        have := mul_le_mul_of_nonneg_right hτle hβ.le
        calc τ * β ≤ 4 * (1 / β) * β := this
          _ = 4 := by field_simp
      nlinarith
    have h6 : (T * β / 4) ^ (50 * m) * τ ^ (50 * m) ≤ T ^ (50 * m) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h5 _
    have h7 : min 1 ((T * β / 4) ^ (50 * m)) * τ ^ (50 * m) ≤ T ^ (50 * m) :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans h6
    linarith

end L6Base
end MaxT
end TrackB
end RestrictedPolynomials
end
