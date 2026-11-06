module

public import RestrictedPolynomials.TrackB.MaxTStatements

/-!
# Track B: Claims 6.13, 6.14, the free interval and Claim 6.15
(paper IV `writeup_stability.tex` l. 3785-3865, in the normalised setting)

Paper IV claims: `claim:relaxed2`, `claim:relaxed3`, `claim:relaxed4` (step `free-interval-choice`),
`claim:relaxed4`.

Readings.
* The premises are normalised, `‖f‖₂ = ‖g‖₂ = ‖h‖₂ = 1` in `L²(lawX/Y/Z ν)`.
* Claim 6.15 is read in the form the proof gives, for ALL of `X` and `Z`.
  It needs only `PairwiseConnected3 ν.support` (the source uses pairwise
  connectivity, l. 3838-3840), and the uniform `(y,z)`-marginal premise is dropped: every `y`
  occurs in an atom.
* The claims are in constants-map form `∃ c > 0, ∀ τ ≤ c`.

All helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section L6Claims

private theorem mergePush_sum' {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (π : FinProb A) (F : A → B) (u : B → ℝ) :
    ∑ b, (mergePush π F).prob b * u b = ∑ a, π.prob a * u (F a) := by
  show ∑ b, (∑ a ∈ univ.filter (fun a => F a = b), π.prob a) * u b = _
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise univ F (fun a => π.prob a * u (F a))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

private theorem mergePush_ge' {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (π : FinProb A) (F : A → B) (a : A) : π.prob a ≤ (mergePush π F).prob (F a) := by
  show π.prob a ≤ ∑ a' ∈ univ.filter (fun a' => F a' = F a), π.prob a'
  exact Finset.single_le_sum (f := π.prob) (fun i _ => π.nonneg i)
    (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩)

private theorem norm_sq_bound' {B : Type} [Fintype B] (π : FinProb B) (w : B → ℂ)
    (h1 : ∑ b, π.prob b * ‖w b‖ ^ 2 = 1) (b : B) {α : ℝ} (hb : α ≤ π.prob b) :
    α * ‖w b‖ ^ 2 ≤ 1 :=
  calc α * ‖w b‖ ^ 2 ≤ π.prob b * ‖w b‖ ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ ∑ b, π.prob b * ‖w b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => π.prob b * ‖w b‖ ^ 2)
          (fun i _ => mul_nonneg (π.nonneg i) (sq_nonneg _)) (Finset.mem_univ b)
    _ = 1 := h1

private theorem sqrt_mul_norm_le_one {B : Type} [Fintype B] (π : FinProb B) (w : B → ℂ)
    (h1 : ∑ b, π.prob b * ‖w b‖ ^ 2 = 1) (b : B) {α : ℝ} (hα : 0 < α) (hb : α ≤ π.prob b) :
    Real.sqrt α * ‖w b‖ ≤ 1 := by
  have h := norm_sq_bound' π w h1 b hb
  have h2 : (Real.sqrt α * ‖w b‖) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hα.le]; exact h
  nlinarith [mul_nonneg (Real.sqrt_nonneg α) (norm_nonneg (w b))]

private theorem sum_yz' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (ν : FinProb (X × Y × Z)) (F : Y → Z → ℝ) :
    ∑ p : X × Y × Z, ν.prob p * F p.2.1 p.2.2 =
      ∑ y, ∑ z, (∑ x, ν.prob (x, y, z)) * F y z := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

private theorem lawX_sum' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) (u : X → ℝ) :
    ∑ x, (lawX ν).prob x * u x = ∑ p : X × Y × Z, ν.prob p * u p.1 :=
  mergePush_sum' ν (fun p => p.1) u

private theorem lawY_sum' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) (u : Y → ℝ) :
    ∑ y, (lawY ν).prob y * u y = ∑ p : X × Y × Z, ν.prob p * u p.2.1 :=
  mergePush_sum' ν (fun p => p.2.1) u

private theorem lawZ_sum' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) (u : Z → ℝ) :
    ∑ z, (lawZ ν).prob z * u z = ∑ p : X × Y × Z, ν.prob p * u p.2.2 :=
  mergePush_sum' ν (fun p => p.2.2) u

private theorem lawX_ge' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) (p : X × Y × Z) :
    ν.prob p ≤ (lawX ν).prob p.1 := mergePush_ge' ν (fun p => p.1) p

private theorem lawY_ge' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) (p : X × Y × Z) :
    ν.prob p ≤ (lawY ν).prob p.2.1 := mergePush_ge' ν (fun p => p.2.1) p

private theorem lawZ_ge' {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (ν : FinProb (X × Y × Z)) (p : X × Y × Z) :
    ν.prob p ≤ (lawZ ν).prob p.2.2 := mergePush_ge' ν (fun p => p.2.2) p

private theorem norm_sq_conj_sub' (a b : ℂ) :
    ‖starRingEnd ℂ a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj]
  have : starRingEnd ℂ a * (starRingEnd ℂ) b = starRingEnd ℂ (a * b) := by simp
  rw [this, Complex.conj_re]

/-- paper IV `claim:relaxed2` (Claim 6.13). -/
theorem l6_relaxed2_pointwise (m : ℕ) (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 < τ → τ ≤ c →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) →
        (∀ (y : Y) (z : Z), ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ),
        ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 = 1 → ∑ y, (lawY ν).prob y * ‖g y‖ ^ 2 = 1 →
        ∑ z, (lawZ ν).prob z * ‖h z‖ ^ 2 = 1 →
        1 - τ ^ (50 * m) ≤ (∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)).re →
        ∀ p ∈ ν.support, ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ≤ τ ^ (20 * m) := by
  refine ⟨min 1 (α / 2), lt_min one_pos (by linarith), ?_⟩
  intro τ hτ hτc X Y Z _ _ _ _ _ _ ν hat hmarg f g h hf hg hh hre p hp
  have hτ1 : τ ≤ 1 := hτc.trans (min_le_left _ _)
  have hτα : τ ≤ α / 2 := hτc.trans (min_le_right _ _)
  have hne : Nonempty (X × Y × Z) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := ν.sum_eq_one
    simp at this
  obtain ⟨⟨x0, y0, z0⟩⟩ := hne
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos_iff.2 ⟨y0⟩
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos_iff.2 ⟨z0⟩
  set c : ℝ := 1 / ((Fintype.card Y : ℝ) * Fintype.card Z) with hc
  have hcpos : 0 < c := by positivity
  -- the uniform marginal makes the counting norms equal to the cardinalities
  have hgs : ∑ y, ‖g y‖ ^ 2 = Fintype.card Y := by
    rw [lawY_sum' ν (fun y => ‖g y‖ ^ 2), sum_yz' ν (fun y _ => ‖g y‖ ^ 2)] at hg
    simp_rw [hmarg] at hg
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hg
    rw [hc] at hg
    field_simp at hg
    linarith
  have hhs : ∑ z, ‖h z‖ ^ 2 = Fintype.card Z := by
    rw [lawZ_sum' ν (fun z => ‖h z‖ ^ 2), sum_yz' ν (fun _ z => ‖h z‖ ^ 2)] at hh
    simp_rw [hmarg] at hh
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hh
    rw [hc] at hh
    field_simp at hh
    linarith
  have hgh : ∑ q : X × Y × Z, ν.prob q * (‖g q.2.1‖ ^ 2 * ‖h q.2.2‖ ^ 2) = 1 := by
    rw [sum_yz' ν (fun y z => ‖g y‖ ^ 2 * ‖h z‖ ^ 2)]
    simp_rw [hmarg]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hgs, hhs]
    rw [hc]
    field_simp
  have hf' : ∑ q : X × Y × Z, ν.prob q * ‖f q.1‖ ^ 2 = 1 := by
    rw [← lawX_sum' ν (fun x => ‖f x‖ ^ 2)]; exact hf
  -- the identity E |conj f - g h|² = 2 - 2 Re E fgh
  have hid : ∑ q : X × Y × Z, ν.prob q * ‖starRingEnd ℂ (f q.1) - g q.2.1 * h q.2.2‖ ^ 2 =
      2 - 2 * (∑ q : X × Y × Z, (ν.prob q : ℂ) * (f q.1 * g q.2.1 * h q.2.2)).re := by
    have h1 : ∀ q : X × Y × Z, ν.prob q * ‖starRingEnd ℂ (f q.1) - g q.2.1 * h q.2.2‖ ^ 2 =
        ν.prob q * ‖f q.1‖ ^ 2 + ν.prob q * (‖g q.2.1‖ ^ 2 * ‖h q.2.2‖ ^ 2) -
          2 * ((ν.prob q : ℂ) * (f q.1 * g q.2.1 * h q.2.2)).re := by
      intro q
      rw [norm_sq_conj_sub', norm_mul, mul_pow, Complex.re_ofReal_mul, ← mul_assoc (f q.1)]
      ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hf', hgh, ← Finset.mul_sum,
      ← Complex.re_sum]
    ring
  have hsum : ∑ q : X × Y × Z, ν.prob q * ‖starRingEnd ℂ (f q.1) - g q.2.1 * h q.2.2‖ ^ 2 ≤
      2 * τ ^ (50 * m) := by
    rw [hid]; linarith
  have hαp : α * ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ^ 2 ≤ 2 * τ ^ (50 * m) := by
    calc α * ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ^ 2
        ≤ ν.prob p * ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hat p hp) (sq_nonneg _)
      _ ≤ ∑ q : X × Y × Z, ν.prob q * ‖starRingEnd ℂ (f q.1) - g q.2.1 * h q.2.2‖ ^ 2 :=
          Finset.single_le_sum (f := fun q : X × Y × Z =>
            ν.prob q * ‖starRingEnd ℂ (f q.1) - g q.2.1 * h q.2.2‖ ^ 2)
            (fun i _ => mul_nonneg (ν.nonneg i) (sq_nonneg _)) (Finset.mem_univ p)
      _ ≤ _ := hsum
  have hτ10 : τ ^ (10 * m) ≤ α / 2 :=
    (pow_le_of_le_one hτ.le hτ1 (by omega)).trans hτα
  have hτpos : 0 < τ ^ (40 * m) := pow_pos hτ _
  have hbig : 2 * τ ^ (50 * m) ≤ α * (τ ^ (20 * m)) ^ 2 := by
    have e1 : τ ^ (50 * m) = τ ^ (40 * m) * τ ^ (10 * m) := by rw [← pow_add]; ring_nf
    have e2 : (τ ^ (20 * m)) ^ 2 = τ ^ (40 * m) := by rw [← pow_mul]; ring_nf
    rw [e1, e2]
    nlinarith
  have hsq : ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ^ 2 ≤ (τ ^ (20 * m)) ^ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hτ.le _) (by norm_num)).1 hsq

/-- paper IV `claim:relaxed3` (Claim 6.14). -/
theorem l6_relaxed3_g_lower (m : ℕ) (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ τ : ℝ, 0 < τ → τ ≤ c →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) →
        ∀ Sm : Finset X, (∀ x ∈ Sm, ∀ y : Y, ∃ z : Z, (x, y, z) ∈ ν.support) →
        ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ),
        ∑ z, (lawZ ν).prob z * ‖h z‖ ^ 2 = 1 →
        τ / 4 ≤ (∑ x ∈ Sm, ‖f x‖ ^ 2) / (Sm.card : ℝ) →
        (∀ p ∈ ν.support, ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ≤ τ ^ (20 * m)) →
        ∀ y : Y, c' * Real.sqrt τ ≤ ‖g y‖ := by
  refine ⟨1 / 4, Real.sqrt α / 4, by norm_num, by positivity, ?_⟩
  intro τ hτ hτc X Y Z _ _ _ _ _ _ ν hat Sm hSm f g h hh hmean hpt y
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hss : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hs1 : Real.sqrt τ ≤ 1 / 2 := by nlinarith
  have hSmne : Sm.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hmean
    linarith
  obtain ⟨x, hxS, hx⟩ : ∃ x ∈ Sm, τ / 4 ≤ ‖f x‖ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ x ∈ Sm, ‖f x‖ ^ 2 < Sm.card * (τ / 4) := by
      calc ∑ x ∈ Sm, ‖f x‖ ^ 2 < ∑ x ∈ Sm, τ / 4 := Finset.sum_lt_sum_of_nonempty hSmne hcon
        _ = _ := by simp
    have hc : (0 : ℝ) < Sm.card := by exact_mod_cast hSmne.card_pos
    rw [le_div_iff₀ hc] at hmean
    linarith
  obtain ⟨z, hz⟩ := hSm x hxS y
  have hp := hpt _ hz
  simp only at hp
  have hlz : α ≤ (lawZ ν).prob z := (hat _ hz).trans (lawZ_ge' ν (x, y, z))
  have hhz : Real.sqrt α * ‖h z‖ ≤ 1 := sqrt_mul_norm_le_one _ h hh z hα hlz
  have hfx : Real.sqrt τ / 2 ≤ ‖f x‖ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (f x)]
  have hε : τ ^ (20 * m) ≤ Real.sqrt τ / 4 := by
    have h1 : τ ^ (20 * m) ≤ τ ^ 2 := pow_le_pow_of_le_one hτ.le (by linarith) (by omega)
    have h2 : τ ^ 2 = Real.sqrt τ ^ 4 := by
      calc τ ^ 2 = (Real.sqrt τ ^ 2) ^ 2 := by rw [hss]
        _ = Real.sqrt τ ^ 4 := by ring
    have h3 : Real.sqrt τ ^ 4 = Real.sqrt τ * Real.sqrt τ ^ 3 := by ring
    have h4 : Real.sqrt τ ^ 3 ≤ 1 / 4 := by nlinarith [pow_pos hs0 2]
    nlinarith
  have hfg : ‖f x‖ ≤ ‖g y‖ * ‖h z‖ + τ ^ (20 * m) := by
    have := norm_sub_norm_le (starRingEnd ℂ (f x)) (g y * h z)
    simp only [norm_mul, RCLike.norm_conj] at this hp
    linarith [norm_sub_norm_le (starRingEnd ℂ (f x)) (g y * h z)]
  have h1 : Real.sqrt τ / 4 ≤ ‖g y‖ * ‖h z‖ := by linarith
  have h2 : Real.sqrt α * (Real.sqrt τ / 4) ≤ ‖g y‖ := by
    have h3 : Real.sqrt α * (Real.sqrt τ / 4) ≤ Real.sqrt α * (‖g y‖ * ‖h z‖) :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    have h4 : Real.sqrt α * (‖g y‖ * ‖h z‖) = ‖g y‖ * (Real.sqrt α * ‖h z‖) := by ring
    have h5 : ‖g y‖ * (Real.sqrt α * ‖h z‖) ≤ ‖g y‖ * 1 :=
      mul_le_mul_of_nonneg_left hhz (norm_nonneg _)
    linarith
  calc Real.sqrt α / 4 * Real.sqrt τ = Real.sqrt α * (Real.sqrt τ / 4) := by ring
    _ ≤ ‖g y‖ := h2

/-- paper IV `claim:relaxed4`, step `free-interval-choice`. -/
theorem l6_free_interval (m : ℕ) {X Z : Type} [Fintype X] [Fintype Z]
    (hX : Fintype.card X ≤ m) (hZ : Fintype.card Z ≤ m) (f : X → ℂ) (h : Z → ℂ)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ j : ℕ, j ≤ 2 * m ∧
      (∀ x, ¬ (τ ^ (3 * (j + 1)) ≤ ‖f x‖ ∧ ‖f x‖ < τ ^ (3 * j))) ∧
      (∀ z, ¬ (τ ^ (3 * (j + 1)) ≤ ‖h z‖ ∧ ‖h z‖ < τ ^ (3 * j))) := by
  by_contra hcon
  -- every interval index `j ≤ 2m` has a witness in `X ⊕ Z`
  have hw : ∀ j : Fin (2 * m + 1), ∃ w : X ⊕ Z,
      τ ^ (3 * ((j : ℕ) + 1)) ≤ Sum.elim (fun x => ‖f x‖) (fun z => ‖h z‖) w ∧
        Sum.elim (fun x => ‖f x‖) (fun z => ‖h z‖) w < τ ^ (3 * (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) ≤ 2 * m := by omega
    by_contra hno
    exact hcon ⟨(j : ℕ), hj, fun x hx => hno ⟨Sum.inl x, hx⟩, fun z hz => hno ⟨Sum.inr z, hz⟩⟩
  choose w hw using hw
  -- disjointness of the intervals
  have hdisj : ∀ j k : ℕ, j < k → ∀ v : ℝ, τ ^ (3 * (j + 1)) ≤ v → v < τ ^ (3 * k) → False := by
    intro j k hjk v h1 h2
    have : τ ^ (3 * k) ≤ τ ^ (3 * (j + 1)) :=
      pow_le_pow_of_le_one hτ0.le hτ1.le (by omega)
    linarith
  have hinj : Function.Injective w := by
    intro j k hjk
    by_contra hne
    have hne' : (j : ℕ) ≠ k := fun h => hne (Fin.ext h)
    obtain ⟨hj1, hj2⟩ := hw j
    obtain ⟨hk1, hk2⟩ := hw k
    rw [hjk] at hj1 hj2
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · exact hdisj _ _ hlt _ hj1 hk2 |>.elim
    · exact hdisj _ _ hlt _ hk1 hj2 |>.elim
  have hcard := Fintype.card_le_of_injective w hinj
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  omega

/-- the `{x,z}`-graph of a pairwise connected set is connected, so a function agreeing along atoms
is constant (the key step of the pairwise-connectivity-only argument). -/
private theorem pc_xz_const {X Y Z : Type} {S : Set (X × Y × Z)} (hS : PairwiseConnected3 S)
    (A : X → ℕ) (B : Z → ℕ) (h : ∀ p ∈ S, A p.1 = B p.2.2) :
    (∀ a b, A a = A b) ∧ (∀ a b, B a = B b) := by
  have hc := ((pairwiseConnected3_iff S).1 hS).2.1
  set G : SimpleGraph (X ⊕ Z) := SimpleGraph.fromRel fun (a : X ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z with hG
  have key : ∀ u v : X ⊕ Z, G.Reachable u v → Sum.elim A B u = Sum.elim A B v := by
    intro u v ⟨w⟩
    induction w with
    | nil => rfl
    | cons hadj _ ih =>
      rw [← ih]
      rw [hG, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨-, hr⟩ := hadj
      rcases hr with ⟨x, y, z, hm, rfl, rfl⟩ | ⟨x, y, z, hm, rfl, rfl⟩
      · exact h _ hm
      · exact (h _ hm).symm
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact key (Sum.inl a) (Sum.inl b) (hc.preconnected _ _)
  · exact key (Sum.inr a) (Sum.inr b) (hc.preconnected _ _)

/-- the two cases of the proof of Claim 6.15 at one atom, on abstract reals:
`T = t s³` with `t = τ^{3j}`, `s = √τ`. -/
private theorem cases_aux' {s a c' t ε nf ng nh : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2)
    (hsa : s ^ 3 ≤ a / 2) (hsc : s ^ 2 ≤ c' / 2) (ha : 0 < a) (ht : 0 < t)
    (hε : ε ≤ t * s ^ 4) (hnh : 0 ≤ nh) (hag : a * ng ≤ 1)
    (hgl : c' * s ≤ ng) (h1 : nf ≤ ng * nh + ε) (h2 : ng * nh ≤ nf + ε)
    (hfree : ¬ (t * s ^ 6 ≤ nh ∧ nh < t)) : t * s ^ 3 ≤ nf ↔ t * s ^ 3 ≤ nh := by
  have hs3 : 0 < s ^ 3 := pow_pos hs 3
  have hs3le : s ^ 3 ≤ 1 := pow_le_one₀ hs.le (by linarith)
  have hT : 0 < t * s ^ 3 := mul_pos ht hs3
  have hε2 : ε ≤ t * s ^ 3 / 2 := by
    have : t * s ^ 4 ≤ t * s ^ 3 / 2 := by
      have e : t * s ^ 4 = t * s ^ 3 * s := by ring
      rw [e]; nlinarith
    linarith
  have hTt : t * s ^ 3 ≤ t := by nlinarith
  have hT6 : t * s ^ 6 ≤ t * s ^ 3 := by
    have : s ^ 6 ≤ s ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_left this ht.le
  constructor
  · intro hT'
    have hgh : t * s ^ 3 / 2 ≤ ng * nh := by linarith
    have h3 : a * (t * s ^ 3 / 2) ≤ nh := by
      have h4 : a * (ng * nh) ≤ nh := by
        have : a * (ng * nh) = (a * ng) * nh := by ring
        rw [this]; nlinarith
      have h5 : a * (t * s ^ 3 / 2) ≤ a * (ng * nh) := mul_le_mul_of_nonneg_left hgh ha.le
      linarith
    have h6 : t * s ^ 6 ≤ nh := by
      have : t * s ^ 6 ≤ a * (t * s ^ 3 / 2) := by
        have e : t * s ^ 6 = t * s ^ 3 * s ^ 3 := by ring
        rw [e]; nlinarith
      linarith
    by_contra hlt
    push Not at hlt
    exact hfree ⟨h6, lt_of_lt_of_le hlt hTt⟩
  · intro hh
    by_contra hnf'
    push Not at hnf'
    have h3 : ng * nh < 2 * (t * s ^ 3) := by linarith
    have h4 : c' * s * nh ≤ ng * nh := mul_le_mul_of_nonneg_right hgl hnh
    have h5 : c' * nh < 2 * t * s ^ 2 := by
      have : s * (c' * nh) < s * (2 * t * s ^ 2) := by nlinarith
      exact lt_of_mul_lt_mul_left this hs.le
    have h6 : nh < t := by
      have : 2 * t * s ^ 2 ≤ c' * t := by nlinarith
      by_contra hcon
      push Not at hcon
      nlinarith
    have h7 : nh < t * s ^ 6 := by
      by_contra hcon
      push Not at hcon
      exact hfree ⟨hcon, h6⟩
    linarith

/-- paper IV `claim:relaxed4` (Claim 6.15): pairwise connectivity only (paper IV l. 3838-3840). -/
theorem l6_relaxed4_lower (m : ℕ) (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) {c' : ℝ} (hc' : 0 < c') :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 < τ → τ ≤ c →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) →
        PairwiseConnected3 ν.support →
        ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ),
        ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 = 1 → ∑ y, (lawY ν).prob y * ‖g y‖ ^ 2 = 1 →
        ∑ z, (lawZ ν).prob z * ‖h z‖ ^ 2 = 1 →
        (∀ p ∈ ν.support, ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ≤ τ ^ (20 * m)) →
        (∀ y, c' * Real.sqrt τ ≤ ‖g y‖) →
        ∀ j : ℕ, j ≤ 2 * m →
        (∀ x, ¬ (τ ^ (3 * (j + 1)) ≤ ‖f x‖ ∧ ‖f x‖ < τ ^ (3 * j))) →
        (∀ z, ¬ (τ ^ (3 * (j + 1)) ≤ ‖h z‖ ∧ ‖h z‖ < τ ^ (3 * j))) →
        (∀ x, τ ^ ((3 * j : ℝ) + 3 / 2) ≤ ‖f x‖) ∧ (∀ z, τ ^ ((3 * j : ℝ) + 3 / 2) ≤ ‖h z‖) := by
  have ha0 : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  set s₀ : ℝ := min (1 / 2) (min (Real.sqrt α / 2) (c' / 2)) with hs₀
  have hs₀pos : 0 < s₀ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨s₀ ^ 2, by positivity, ?_⟩
  intro τ hτ hτc X Y Z _ _ _ _ _ _ ν hat hpc f g h hf hg hh hpt hglow j hj hfree hhfree
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ τ = s ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.2 hτ, (Real.sq_sqrt hτ.le).symm⟩
  have hss : s ≤ s₀ := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hs1 : s ≤ 1 / 2 := hss.trans (min_le_left _ _)
  have hsa : s ^ 3 ≤ Real.sqrt α / 2 := by
    have h1 : s ≤ Real.sqrt α / 2 := hss.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : s ^ 3 ≤ s := by nlinarith [pow_pos hs0 2]
    linarith
  have hsc : s ^ 2 ≤ c' / 2 := by
    have h1 : s ≤ c' / 2 := hss.trans ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  set t : ℝ := (s ^ 2) ^ (3 * j) with ht
  have htpos : 0 < t := pow_pos (by positivity) _
  have ht1 : t ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
  have hs1' : s ^ 2 ≤ 1 := by nlinarith
  -- the thresholds
  have hT : (s ^ 2) ^ ((3 * j : ℝ) + 3 / 2) = t * s ^ 3 := by
    rw [Real.rpow_add (by positivity)]
    have e1 : (s ^ 2) ^ ((3 * j : ℝ)) = t := by
      have : ((3 : ℝ) * j) = ((3 * j : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]
    have e2 : (s ^ 2) ^ ((3 / 2 : ℝ)) = s ^ 3 := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs0.le, ← Real.rpow_natCast s 3]
      norm_num
    rw [e1, e2]
  have hT6 : (s ^ 2) ^ (3 * (j + 1)) = t * s ^ 6 := by
    rw [show 3 * (j + 1) = 3 * j + 3 by ring, pow_add, ← ht]
    ring
  have hε : (s ^ 2) ^ (20 * m) ≤ t * s ^ 4 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 * j ≤ 20 * m by omega)
    rw [hk, pow_add, ← ht]
    have : (s ^ 2) ^ k ≤ (s ^ 2) ^ 2 := pow_le_pow_of_le_one (by positivity) hs1' (by omega)
    calc t * (s ^ 2) ^ k ≤ t * (s ^ 2) ^ 2 := mul_le_mul_of_nonneg_left this htpos.le
      _ = t * s ^ 4 := by ring
  -- indicator functions
  let A : X → ℕ := fun x => if t * s ^ 3 ≤ ‖f x‖ then 1 else 0
  let B : Z → ℕ := fun z => if t * s ^ 3 ≤ ‖h z‖ then 1 else 0
  have hAB : ∀ q ∈ ν.support, A q.1 = B q.2.2 := by
    intro q hq
    have hν : α ≤ ν.prob q := hat q hq
    have hgy : Real.sqrt α * ‖g q.2.1‖ ≤ 1 :=
      sqrt_mul_norm_le_one _ g hg q.2.1 hα (hν.trans (lawY_ge' ν q))
    have hp := hpt q hq
    have hglq := hglow q.2.1
    rw [Real.sqrt_sq hs0.le] at hglq
    have h1 := abs_norm_sub_norm_le (starRingEnd ℂ (f q.1)) (g q.2.1 * h q.2.2)
    rw [RCLike.norm_conj, norm_mul] at h1
    have h2 : ‖f q.1‖ ≤ ‖g q.2.1‖ * ‖h q.2.2‖ + (s ^ 2) ^ (20 * m) := by
      have := (abs_le.1 (h1.trans hp)).2
      linarith
    have h3 : ‖g q.2.1‖ * ‖h q.2.2‖ ≤ ‖f q.1‖ + (s ^ 2) ^ (20 * m) := by
      have := (abs_le.1 (h1.trans hp)).1
      linarith
    have key := cases_aux' hs0 hs1 hsa hsc ha0 htpos hε (norm_nonneg (h q.2.2))
      hgy hglq h2 h3 (by rw [← hT6]; exact hhfree q.2.2)
    simp only [A, B]
    by_cases hA : t * s ^ 3 ≤ ‖f q.1‖
    · simp [hA, key.1 hA]
    · simp [hA, mt key.2 hA]
  obtain ⟨hAc, hBc⟩ := pc_xz_const hpc A B hAB
  -- some `x` has `1 ≤ ‖f x‖`
  obtain ⟨x0, hx0⟩ : ∃ x, 1 ≤ ‖f x‖ := by
    by_contra hcon
    push Not at hcon
    have h1 : ∀ x, (lawX ν).prob x * (‖f x‖ ^ 2 - 1) ≤ 0 := fun x => by
      have : ‖f x‖ ^ 2 < 1 := by nlinarith [norm_nonneg (f x), hcon x]
      exact mul_nonpos_of_nonneg_of_nonpos ((lawX ν).nonneg x) (by linarith)
    have h2 : ∑ x, (lawX ν).prob x * (‖f x‖ ^ 2 - 1) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, hf, mul_one, (lawX ν).sum_eq_one]; ring
    have h3 := (Finset.sum_eq_zero_iff_of_nonpos (fun x _ => h1 x)).1 h2
    have h4 : ∀ x, (lawX ν).prob x = 0 := fun x => by
      have := h3 x (Finset.mem_univ x)
      have hlt : ‖f x‖ ^ 2 - 1 < 0 := by nlinarith [norm_nonneg (f x), hcon x]
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    have := (lawX ν).sum_eq_one
    simp [h4] at this
  have hA0 : A x0 = 1 := by
    have hge : t * s ^ 3 ≤ ‖f x0‖ := by
      nlinarith [mul_le_mul ht1 (show s ^ 3 ≤ 1 by nlinarith [pow_pos hs0 3, pow_pos hs0 2])
        (pow_pos hs0 3).le zero_le_one]
    simp [A, hge]
  have hAall : ∀ x, A x = 1 := fun x => (hAc x x0).trans hA0
  refine ⟨fun x => ?_, fun z => ?_⟩
  · rw [hT]
    by_contra hcon
    have := hAall x
    simp [A, hcon] at this
  · rw [hT]
    obtain ⟨y, z', hz'⟩ := PairwiseConnected3.exists_atom_x hpc x0
    have h1 := hAB (x0, y, z') hz'
    have h2 : B z' = 1 := by rw [← h1]; exact hA0
    have h3 : B z = 1 := (hBc z z').trans h2
    by_contra hcon
    simp [B, hcon] at h3

end L6Claims
end MaxT
end TrackB
end RestrictedPolynomials
end
