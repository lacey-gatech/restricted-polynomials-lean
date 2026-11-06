module

public import RestrictedPolynomials.TrackB.K6PathTrick

/-!
# Track B: the uniform weight and the letter marginals (Supplement D)

Source: Supplement D (`prop:uniform-weight`, `lem:walk-stationary`, `lem:chain` (e)).

`k6pt_mu_minus_uniform` strengthens `k6pt_mu_minus` (same `pt`, `μm`, conjuncts
repeated verbatim) by the uniform weight `min (1/2) β` for any atom bound `β > 0` of `μ⁺`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section UniformWeight
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- Supplement D Prop. uniform-weight (a)-(b): `k6pt_mu_minus` with the weight replaced by
`min (1/2) β`, for any `β > 0` that bounds the atoms of `μ⁺`. -/
theorem k6pt_mu_minus_uniform (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support)
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (h₁ : Fintype.card X + Fintype.card Z ≤ 2 ^ r₁)
    (h₂ : Fintype.card X + Fintype.card (K6ptGam μ r₁ hr₁) ≤ 2 ^ r₂) {β : ℝ} (hβ : 0 < β)
    (hatom : ∀ p ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support, β ≤ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p) :
    ∃ (pt : X × X × Bool → K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂)
      (μm ν : FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂)),
      (∀ t : X × X × Bool,
        (pt t).1.1 = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1] ∧
        pt t ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support ∧
        (∃ w' : K6ptSig μ r₁ hr₁ r₂ hr₂, w'.1 = ![t.2.1, k6ptMid t.1 t.2.1 t.2.2, t.1] ∧
          (w', (pt t).2) ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support) ∧
        (pt (t.2.1, t.1, !t.2.2)).2 = (pt t).2) ∧
      (∀ p, μm.prob p =
        ((univ.filter fun t : X × X × Bool => pt t = p).card : ℝ) /
          (2 * (Fintype.card X : ℝ) ^ 2)) ∧
      (∀ (w w' : K6ptSig μ r₁ hr₁ r₂ hr₂) (y : K6ptGam μ r₁ hr₁)
          (z : K6ptPhi μ r₁ hr₁ r₂ hr₂),
        w'.1 = ![w.1 2, w.1 1, w.1 0] → μm.prob (w', y, z) = μm.prob (w, y, z)) ∧
      (∀ a b : X, ∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
          K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 0 = a ∧ p.1.1 2 = b),
        μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2) ∧
      (∀ p, (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p =
        min (1 / 2) β * μm.prob p + (1 - min (1 / 2) β) * ν.prob p) := by
  obtain ⟨pt, μm, -, -, -, -, h1, h2, h3, h4, -⟩ := k6pt_mu_minus μ hμ hr₁ hr₂ h₁ h₂
  have hle1 : ∀ p, μm.prob p ≤ 1 := fun p =>
    calc μm.prob p ≤ ∑ q, μm.prob q :=
          Finset.single_le_sum (fun q _ => μm.nonneg q) (Finset.mem_univ p)
      _ = 1 := μm.sum_eq_one
  have hsupp : ∀ p, 0 < μm.prob p → p ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support := by
    intro p hp
    have hD : (0 : ℝ) < 2 * (Fintype.card X : ℝ) ^ 2 := by
      have hc : 0 < Fintype.card X := by
        by_contra hc
        have h0 : Fintype.card X = 0 := by omega
        rw [h2 p, h0] at hp
        simp at hp
      positivity
    rw [h2 p, div_pos_iff_of_pos_right hD] at hp
    obtain ⟨t, ht⟩ := Finset.card_pos.1 (by exact_mod_cast hp)
    rw [Finset.mem_filter] at ht
    have := (h1 t).2.1
    rw [ht.2] at this
    exact this
  set w : ℝ := min (1 / 2) β with hw
  have hw0 : 0 < w := lt_min (by norm_num) hβ
  have hw1 : w ≤ 1 / 2 := min_le_left _ _
  have hwβ : w ≤ β := min_le_right _ _
  have hw' : 0 < 1 - w := by linarith
  have hle : ∀ p, w * μm.prob p ≤ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p := by
    intro p
    by_cases h0 : μm.prob p = 0
    · rw [h0, mul_zero]; exact (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).nonneg p
    · have hp : 0 < μm.prob p := lt_of_le_of_ne (μm.nonneg p) (Ne.symm h0)
      calc w * μm.prob p ≤ w * 1 := by gcongr; exact hle1 p
        _ = w := mul_one w
        _ ≤ β := hwβ
        _ ≤ _ := hatom p (hsupp p hp)
  let ν : FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂) :=
    { prob := fun p => ((k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p - w * μm.prob p) / (1 - w)
      nonneg := fun p => div_nonneg (sub_nonneg.2 (hle p)) hw'.le
      sum_eq_one := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
          (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).sum_eq_one, μm.sum_eq_one, mul_one]
        exact div_self hw'.ne' }
  refine ⟨pt, μm, ν, h1, h2, h3, h4, fun p => ?_⟩
  show _ = w * μm.prob p + (1 - w) * (((k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p - w * μm.prob p) / (1 - w))
  field_simp
  ring

/-- Helper: the discharge of the `hmirror` hypothesis of
`k6pt_swap_norm_step` from the first two conjuncts of `k6pt_mu_minus_uniform`. Public, used by
`K6ToswapUniform`. -/
theorem k6pt_mirror_of_mu_minus_uniform (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁)
    (hr₂ : 1 ≤ r₂)
    (pt : X × X × Bool → K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂)
    (μm : FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂))
    (h1 : ∀ t : X × X × Bool,
        (pt t).1.1 = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1] ∧
        pt t ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support ∧
        (∃ w' : K6ptSig μ r₁ hr₁ r₂ hr₂, w'.1 = ![t.2.1, k6ptMid t.1 t.2.1 t.2.2, t.1] ∧
          (w', (pt t).2) ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support) ∧
        (pt (t.2.1, t.1, !t.2.2)).2 = (pt t).2)
    (h2 : ∀ p, μm.prob p =
        ((univ.filter fun t : X × X × Bool => pt t = p).card : ℝ) /
          (2 * (Fintype.card X : ℝ) ^ 2)) :
    ∀ (w : K6ptSig μ r₁ hr₁ r₂ hr₂) (y : K6ptGam μ r₁ hr₁) (z : K6ptPhi μ r₁ hr₁ r₂ hr₂),
      0 < μm.prob (w, y, z) →
      ∃ w' : K6ptSig μ r₁ hr₁ r₂ hr₂, (fun w : K6ptSig μ r₁ hr₁ r₂ hr₂ => w.1) w' =
        ![(fun w : K6ptSig μ r₁ hr₁ r₂ hr₂ => w.1) w 2, (fun w : K6ptSig μ r₁ hr₁ r₂ hr₂ => w.1) w 1,
          (fun w : K6ptSig μ r₁ hr₁ r₂ hr₂ => w.1) w 0] := by
  intro w y z hpos
  rw [h2] at hpos
  have hcard : 0 < (univ.filter fun t : X × X × Bool => pt t = (w, y, z)).card := by
    by_contra hc
    have : (univ.filter fun t : X × X × Bool => pt t = (w, y, z)).card = 0 := by omega
    rw [this] at hpos
    simp at hpos
  obtain ⟨t, ht⟩ := Finset.card_pos.1 hcard
  have hpt : pt t = (w, y, z) := (Finset.mem_filter.1 ht).2
  obtain ⟨hw, -, ⟨w', hw', -⟩, -⟩ := h1 t
  refine ⟨w', ?_⟩
  rw [hpt] at hw
  simp only [hw']
  rw [hw]
  simp

end UniformWeight

/-! ### Stationarity -/
section Stationarity
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the first marginal `μ_x`. -/
def k6ptMargX (μ : FinProb (X × Y × Z)) (x : X) : ℝ := ∑ p with p.1 = x, μ.prob p

omit [DecidableEq Y] [DecidableEq Z] in
private lemma k6pt_margX_eq_sum (μ : FinProb (X × Y × Z)) (x : X) :
    k6ptMargX μ x = ∑ y, ∑ z, μ.prob (x, y, z) := by
  unfold k6ptMargX
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [Fintype.sum_prod_type]
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq X] in
private lemma k6pt_sum_pathX (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (G : (Fin ℓ → X) → Y → Z → ℝ)
    (hG : ∀ w, (¬ ∃ (y : Y) (z : Z), pathWeight μ ℓ hℓ w y z ≠ 0) → ∀ y z, G w y z = 0) :
    ∑ p : PathX μ ℓ hℓ × Y × Z, G p.1.1 p.2.1 p.2.2 =
      ∑ w : Fin ℓ → X, ∑ y, ∑ z, G w y z := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_subtype (Finset.univ.filter fun w : Fin ℓ → X => ∃ (y : Y) (z : Z),
      pathWeight μ ℓ hℓ w y z ≠ 0) (p := fun w : Fin ℓ → X => ∃ (y : Y) (z : Z),
      pathWeight μ ℓ hℓ w y z ≠ 0) (fun w => by simp)
      (fun w => ∑ y, ∑ z, G w y z)]
  rw [Finset.sum_filter_of_ne]
  intro w _ hw
  by_contra hne
  exact hw (Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => hG w hne y z)

private lemma k6pt_row_odd (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) (y : Y) :
    ∑ w : Fin ℓ → X, ∑ z, walkYZ μ (List.ofFn w) y z = if 0 < margY μ y then 1 else 0 := by
  obtain ⟨m, rfl⟩ := hℓ
  exact sum_walkYZ_row μ m y

private lemma k6pt_margY_mul_ite (μ : FinProb (X × Y × Z)) (y : Y) :
    margY μ y * (if 0 < margY μ y then (1 : ℝ) else 0) = margY μ y := by
  by_cases h : 0 < margY μ y
  · simp [h]
  · have : margY μ y = 0 := le_antisymm (not_lt.mp h) (margY_nonneg μ y)
    simp [this]

theorem k6pt_pathTrick_start_marg (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) (y : Y) :
    ∑ q ∈ univ.filter (fun q : PathX μ ℓ hℓ × Y × Z => q.2.1 = y), (pathTrick μ ℓ hℓ).prob q =
      margY μ y := by
  rw [Finset.sum_filter]
  have e : ∀ q : PathX μ ℓ hℓ × Y × Z,
      (if q.2.1 = y then (pathTrick μ ℓ hℓ).prob q else 0) =
        (fun (w : Fin ℓ → X) (y' : Y) (z : Z) =>
          if y' = y then pathWeight μ ℓ hℓ w y' z else 0) q.1.1 q.2.1 q.2.2 := fun q => rfl
  have hG : ∀ w : Fin ℓ → X, (¬ ∃ (y' : Y) (z : Z), pathWeight μ ℓ hℓ w y' z ≠ 0) →
      ∀ (y' : Y) (z : Z), (if y' = y then pathWeight μ ℓ hℓ w y' z else 0) = 0 := by
    intro w hw y' z
    by_cases h : y' = y
    · simp only [h, ite_true]
      by_contra hne
      exact hw ⟨y, z, hne⟩
    · simp [h]
  rw [Finset.sum_congr rfl (fun q _ => e q)]
  refine (k6pt_sum_pathX μ hℓ (fun (w : Fin ℓ → X) (y' : Y) (z : Z) =>
    if y' = y then pathWeight μ ℓ hℓ w y' z else 0) hG).trans ?_
  have e2 : ∀ w : Fin ℓ → X, ∑ y', ∑ z, (if y' = y then pathWeight μ ℓ hℓ w y' z else 0) =
      margY μ y * ∑ z, walkYZ μ (List.ofFn w) y z := by
    intro w
    rw [Finset.sum_eq_single y]
    · simp [pathWeight, Finset.mul_sum]
    · intro b _ hb; simp [hb]
    · simp
  simp_rw [e2]
  rw [← Finset.mul_sum, k6pt_row_odd μ hℓ, k6pt_margY_mul_ite]


omit [DecidableEq X] in
private lemma k6pt_walk_cons2 (μ : FinProb (X × Y × Z)) (m : ℕ) (x₁ x₂ : X)
    (w' : Fin (2 * m + 1) → X) (y : Y) (z : Z) :
    walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X)) y z =
      ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * walkYZ μ (List.ofFn w') y' z := by
  rw [List.ofFn_succ, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [walkYZ, Matrix.mul_apply]

private lemma k6pt_sum_cons2 (m : ℕ) (F : (Fin (2 * m + 1 + 1 + 1) → X) → ℝ) :
    ∑ w, F w = ∑ x₁, ∑ x₂, ∑ w' : Fin (2 * m + 1) → X, F (Fin.cons x₁ (Fin.cons x₂ w')) := by
  rw [sum_fin_cons]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  exact sum_fin_cons (n := 2 * m + 1) (fun w'' => F (Fin.cons x₁ w''))

/-- row sum of the first two steps followed by an odd walk. -/
private lemma k6pt_row_cons2 (μ : FinProb (X × Y × Z)) (m : ℕ) (x₁ x₂ : X) (y : Y) :
    ∑ w' : Fin (2 * m + 1) → X,
      ∑ z, walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X)) y z =
      ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * (if 0 < margY μ y' then (1 : ℝ) else 0) := by
  simp_rw [k6pt_walk_cons2]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Z))]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [sum_walkYZ_row μ m y']

/-- `∑_{x₂, y'} (step a ∘ step x₂)(y,y') [0 < μ_Y(y')] = ∑_z step a (y,z)`. -/
private lemma k6pt_first_letter (μ : FinProb (X × Y × Z)) (a : X) (y : Y) :
    ∑ x₂, ∑ y', (stepYZ μ a * stepZY μ x₂) y y' * (if 0 < margY μ y' then (1 : ℝ) else 0) =
      ∑ z, stepYZ μ a y z := by
  have e : ∀ x₂ : X, ∑ y', (stepYZ μ a * stepZY μ x₂) y y' *
      (if 0 < margY μ y' then (1 : ℝ) else 0) =
      ∑ z', stepYZ μ a y z' *
        ∑ y', stepZY μ x₂ z' y' * (if 0 < margY μ y' then (1 : ℝ) else 0) := by
    intro x₂
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
  simp_rw [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [← Finset.mul_sum, sum_stepZY_mul μ (fun y' => if 0 < margY μ y' then (1 : ℝ) else 0)
    (fun y' h => if_pos h) z']
  by_cases h : 0 < margZ μ z'
  · simp [h]
  · have h0 : margZ μ z' = 0 := le_antisymm (not_lt.mp h) (margZ_nonneg μ z')
    have : stepYZ μ a y z' = 0 := by
      have hp := prob_le_margZ μ a y z'
      rw [h0] at hp
      have : μ.prob (a, y, z') = 0 := le_antisymm hp (μ.nonneg _)
      simp [stepYZ, this]
    simp [h, this]

private lemma k6pt_agg_first (μ : FinProb (X × Y × Z)) (a : X) :
    ∑ y, margY μ y * ∑ z, stepYZ μ a y z = k6ptMargX μ a := by
  rw [k6pt_margX_eq_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => margY_mul_stepYZ μ a y z

/-- `∑_{x₁, y} μ_Y(y) (step x₁ ∘ step a)(y,y') = ∑_z μ(a,y',z)`. -/
private lemma k6pt_agg_two (μ : FinProb (X × Y × Z)) (a : X) (y' : Y) :
    ∑ x₁, ∑ y, margY μ y * (stepYZ μ x₁ * stepZY μ a) y y' = ∑ z, μ.prob (a, y', z) := by
  have h1 : ∀ x₁ y, margY μ y * (stepYZ μ x₁ * stepZY μ a) y y' =
      ∑ z, μ.prob (x₁, y, z) * stepZY μ a z y' := by
    intro x₁ y
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, margY_mul_stepYZ]
  simp_rw [h1]
  calc ∑ x₁, ∑ y, ∑ z, μ.prob (x₁, y, z) * stepZY μ a z y'
      = ∑ x₁, ∑ z, ∑ y, μ.prob (x₁, y, z) * stepZY μ a z y' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x₁, ∑ y, μ.prob (x₁, y, z) * stepZY μ a z y' := Finset.sum_comm
    _ = ∑ z, margZ μ z * stepZY μ a z y' := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [margZ_eq_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
    _ = ∑ z, μ.prob (a, y', z) :=
        Finset.sum_congr rfl fun z _ => margZ_mul_stepZY μ a y' z


/-- stationarity of `μ_Y` for the two-step kernel. -/
private lemma k6pt_stat_two (μ : FinProb (X × Y × Z)) (y' : Y) :
    ∑ y, margY μ y * ∑ x₁, ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y' = margY μ y' := by
  simp_rw [Finset.mul_sum]
  calc ∑ y, ∑ x₁, ∑ x₂, margY μ y * (stepYZ μ x₁ * stepZY μ x₂) y y'
      = ∑ x₁, ∑ y, ∑ x₂, margY μ y * (stepYZ μ x₁ * stepZY μ x₂) y y' := Finset.sum_comm
    _ = ∑ x₁, ∑ x₂, ∑ y, margY μ y * (stepYZ μ x₁ * stepZY μ x₂) y y' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x₂, ∑ x₁, ∑ y, margY μ y * (stepYZ μ x₁ * stepZY μ x₂) y y' := Finset.sum_comm
    _ = ∑ x₂, ∑ z, μ.prob (x₂, y', z) :=
        Finset.sum_congr rfl fun x₂ _ => k6pt_agg_two μ x₂ y'
    _ = margY μ y' := (margY_eq_sum μ y').symm

private lemma k6pt_mu_pos_of_ne (μ : FinProb (X × Y × Z)) (a : X) (y : Y) (z : Z)
    (h : μ.prob (a, y, z) ≠ 0) : (if 0 < margY μ y then (1 : ℝ) else 0) = 1 :=
  if_pos (lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)) (prob_le_margY μ a y z))

/-- the weighted letter marginal of the walk: letter at position `k` of the `(2m+1)`-step walk
started from `μ_Y` has law `μ_x`. -/
private lemma k6pt_letter_weighted (μ : FinProb (X × Y × Z)) :
    ∀ (m k : ℕ) (hk : k < 2 * m + 1) (a : X),
      ∑ y, margY μ y * ∑ w : Fin (2 * m + 1) → X,
        ∑ z, (if w ⟨k, hk⟩ = a then walkYZ μ (List.ofFn w) y z else 0) = k6ptMargX μ a := by
  intro m
  induction m with
  | zero =>
    intro k hk a
    have hk0 : k = 0 := by omega
    subst hk0
    rw [← k6pt_agg_first μ a]
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    change ∑ w : Fin (0 + 1) → X, ∑ z, (if w ⟨0, hk⟩ = a then
      walkYZ μ (List.ofFn w) y z else 0) = _
    rw [sum_fin_cons]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun z _ => ?_
      have : (Fin.cons a (default : Fin 0 → X) : Fin (0 + 1) → X) ⟨0, hk⟩ = a := rfl
      simp [List.ofFn_succ, walkYZ]
    · intro b _ hb
      refine Finset.sum_eq_zero fun z _ => ?_
      have : (Fin.cons b (default : Fin 0 → X) : Fin (0 + 1) → X) ⟨0, hk⟩ = b := rfl
      simp [hb]
    · simp
  | succ m ih =>
    intro k hk a
    change ∑ y, margY μ y * ∑ w : Fin (2 * m + 1 + 1 + 1) → X,
        ∑ z, (if w ⟨k, hk⟩ = a then walkYZ μ (List.ofFn w) y z else 0) = _
    rcases k with _ | _ | k
    · -- letter 0
      have e : ∀ y, ∑ w : Fin (2 * m + 1 + 1 + 1) → X,
          ∑ z, (if w ⟨0, hk⟩ = a then walkYZ μ (List.ofFn w) y z else 0) =
          ∑ z, stepYZ μ a y z := by
        intro y
        rw [k6pt_sum_cons2]
        have e1 : ∀ x₁ x₂ : X, ∑ w' : Fin (2 * m + 1) → X, ∑ z,
            (if (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X) ⟨0, hk⟩ = a then
              walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') :
                Fin (2 * m + 1 + 1 + 1) → X)) y z else 0) =
            if x₁ = a then ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' *
              (if 0 < margY μ y' then (1 : ℝ) else 0) else 0 := by
          intro x₁ x₂
          by_cases hx : x₁ = a
          · simp only [hx, ite_true]
            have h0' : ∀ w' : Fin (2 * m + 1) → X,
                (Fin.cons a (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X) ⟨0, hk⟩ = a :=
              fun _ => rfl
            simp only [h0', ite_true]
            exact k6pt_row_cons2 μ m a x₂ y
          · have h0' : ∀ w' : Fin (2 * m + 1) → X,
                (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X) ⟨0, hk⟩ = x₁ :=
              fun _ => rfl
            simp [hx]
        simp_rw [e1]
        rw [Finset.sum_eq_single a]
        · simp only [ite_true]
          exact k6pt_first_letter μ a y
        · intro b _ hb
          simp [hb]
        · simp
      simp_rw [e]
      exact k6pt_agg_first μ a
    · -- letter 1
      have e : ∀ y, ∑ w : Fin (2 * m + 1 + 1 + 1) → X,
          ∑ z, (if w ⟨0 + 1, hk⟩ = a then walkYZ μ (List.ofFn w) y z else 0) =
          ∑ x₁, ∑ y', (stepYZ μ x₁ * stepZY μ a) y y' *
            (if 0 < margY μ y' then (1 : ℝ) else 0) := by
        intro y
        rw [k6pt_sum_cons2]
        refine Finset.sum_congr rfl fun x₁ _ => ?_
        have e1 : ∀ x₂ : X, ∑ w' : Fin (2 * m + 1) → X, ∑ z,
            (if (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X) ⟨0 + 1, hk⟩ = a then
              walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') :
                Fin (2 * m + 1 + 1 + 1) → X)) y z else 0) =
            if x₂ = a then ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' *
              (if 0 < margY μ y' then (1 : ℝ) else 0) else 0 := by
          intro x₂
          have h0' : ∀ w' : Fin (2 * m + 1) → X,
              (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X) ⟨0 + 1, hk⟩ = x₂ :=
            fun _ => rfl
          simp only [h0']
          by_cases hx : x₂ = a
          · simp only [hx, ite_true]
            exact k6pt_row_cons2 μ m x₁ a y
          · simp [hx]
        simp_rw [e1]
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      simp_rw [e]
      calc ∑ y, margY μ y * ∑ x₁, ∑ y', (stepYZ μ x₁ * stepZY μ a) y y' *
            (if 0 < margY μ y' then (1 : ℝ) else 0)
          = ∑ y, ∑ x₁, ∑ y', margY μ y * ((stepYZ μ x₁ * stepZY μ a) y y' *
            (if 0 < margY μ y' then (1 : ℝ) else 0)) := by
            simp_rw [Finset.mul_sum]
        _ = ∑ x₁, ∑ y, ∑ y', margY μ y * ((stepYZ μ x₁ * stepZY μ a) y y' *
            (if 0 < margY μ y' then (1 : ℝ) else 0)) := Finset.sum_comm
        _ = ∑ x₁, ∑ y', ∑ y, margY μ y * ((stepYZ μ x₁ * stepZY μ a) y y' *
            (if 0 < margY μ y' then (1 : ℝ) else 0)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ y', ∑ x₁, ∑ y, margY μ y * ((stepYZ μ x₁ * stepZY μ a) y y' *
            (if 0 < margY μ y' then (1 : ℝ) else 0)) := Finset.sum_comm
        _ = ∑ y', (∑ z, μ.prob (a, y', z)) * (if 0 < margY μ y' then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [← k6pt_agg_two μ a y', Finset.sum_mul]
            refine Finset.sum_congr rfl fun x₁ _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
        _ = k6ptMargX μ a := by
            rw [k6pt_margX_eq_sum]
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun z _ => ?_
            by_cases h : μ.prob (a, y', z) = 0
            · simp [h]
            · rw [k6pt_mu_pos_of_ne μ a y' z h, mul_one]
    · -- letter k + 2
      have e : ∀ y, ∑ w : Fin (2 * m + 1 + 1 + 1) → X,
          ∑ z, (if w ⟨k + 1 + 1, hk⟩ = a then walkYZ μ (List.ofFn w) y z else 0) =
          ∑ x₁, ∑ x₂, ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' *
            (∑ w' : Fin (2 * m + 1) → X, ∑ z,
              (if w' ⟨k, by omega⟩ = a then walkYZ μ (List.ofFn w') y' z else 0)) := by
        intro y
        rw [k6pt_sum_cons2]
        refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
        have h0' : ∀ w' : Fin (2 * m + 1) → X,
            (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X) ⟨k + 1 + 1, hk⟩ =
              w' ⟨k, by omega⟩ := fun _ => rfl
        simp only [h0', k6pt_walk_cons2]
        calc ∑ w' : Fin (2 * m + 1) → X, ∑ z, (if w' ⟨k, by omega⟩ = a then
              ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * walkYZ μ (List.ofFn w') y' z else 0)
            = ∑ w' : Fin (2 * m + 1) → X, ∑ z, ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' *
              (if w' ⟨k, by omega⟩ = a then walkYZ μ (List.ofFn w') y' z else 0) := by
              refine Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun z _ => ?_
              split_ifs <;> simp
          _ = ∑ w' : Fin (2 * m + 1) → X, ∑ y', ∑ z, (stepYZ μ x₁ * stepZY μ x₂) y y' *
              (if w' ⟨k, by omega⟩ = a then walkYZ μ (List.ofFn w') y' z else 0) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ y', ∑ w' : Fin (2 * m + 1) → X, ∑ z, (stepYZ μ x₁ * stepZY μ x₂) y y' *
              (if w' ⟨k, by omega⟩ = a then walkYZ μ (List.ofFn w') y' z else 0) :=
              Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl fun y' _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun w' _ => ?_
              rw [Finset.mul_sum]
      simp_rw [e]
      set S : Y → ℝ := fun y' => ∑ w' : Fin (2 * m + 1) → X, ∑ z,
        (if w' ⟨k, by omega⟩ = a then walkYZ μ (List.ofFn w') y' z else 0) with hS
      have e3 : ∀ y, ∑ x₁, ∑ x₂, ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * S y' =
          ∑ y', (∑ x₁, ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y') * S y' := by
        intro y
        calc ∑ x₁, ∑ x₂, ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * S y'
            = ∑ x₁, ∑ y', ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y' * S y' :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ y', ∑ x₁, ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y' * S y' := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl fun y' _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x₁ _ => ?_
              rw [Finset.sum_mul]
      calc ∑ y, margY μ y * ∑ x₁, ∑ x₂, ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * S y'
          = ∑ y, ∑ y', margY μ y * ((∑ x₁, ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y') * S y') := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [e3 y, Finset.mul_sum]
        _ = ∑ y', ∑ y, margY μ y * ((∑ x₁, ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y') * S y') :=
            Finset.sum_comm
        _ = ∑ y', (∑ y, margY μ y * ∑ x₁, ∑ x₂, (stepYZ μ x₁ * stepZY μ x₂) y y') * S y' := by
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
        _ = ∑ y', margY μ y' * S y' := by
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [k6pt_stat_two]
        _ = k6ptMargX μ a := ih k (by omega) a


theorem k6pt_pathTrick_letter_marg (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (hℓ : Odd ℓ) (k : Fin ℓ)
    (a : X) :
    ∑ q ∈ univ.filter (fun q : PathX μ ℓ hℓ × Y × Z => q.1.1 k = a), (pathTrick μ ℓ hℓ).prob q =
      k6ptMargX μ a := by
  obtain ⟨m, hm⟩ := id hℓ
  subst hm
  rw [Finset.sum_filter]
  have e : ∀ q : PathX μ (2 * m + 1) hℓ × Y × Z,
      (if q.1.1 k = a then (pathTrick μ (2 * m + 1) hℓ).prob q else 0) =
        (fun (w : Fin (2 * m + 1) → X) (y' : Y) (z : Z) =>
          if w k = a then pathWeight μ (2 * m + 1) hℓ w y' z else 0) q.1.1 q.2.1 q.2.2 :=
    fun q => rfl
  have hG : ∀ w : Fin (2 * m + 1) → X,
      (¬ ∃ (y' : Y) (z : Z), pathWeight μ (2 * m + 1) hℓ w y' z ≠ 0) →
      ∀ (y' : Y) (z : Z), (if w k = a then pathWeight μ (2 * m + 1) hℓ w y' z else 0) = 0 := by
    intro w hw y' z
    by_cases h : w k = a
    · simp only [h, ite_true]
      by_contra hne
      exact hw ⟨y', z, hne⟩
    · simp [h]
  rw [Finset.sum_congr rfl (fun q _ => e q)]
  refine (k6pt_sum_pathX μ hℓ (fun (w : Fin (2 * m + 1) → X) (y' : Y) (z : Z) =>
    if w k = a then pathWeight μ (2 * m + 1) hℓ w y' z else 0) hG).trans ?_
  calc ∑ w : Fin (2 * m + 1) → X, ∑ y, ∑ z,
        (if w k = a then pathWeight μ (2 * m + 1) hℓ w y z else 0)
      = ∑ y, ∑ w : Fin (2 * m + 1) → X, ∑ z,
        (if w k = a then pathWeight μ (2 * m + 1) hℓ w y z else 0) := Finset.sum_comm
    _ = ∑ y, margY μ y * ∑ w : Fin (2 * m + 1) → X,
        ∑ z, (if w ⟨k.1, k.2⟩ = a then walkYZ μ (List.ofFn w) y z else 0) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [pathWeight]
        split_ifs <;> simp
    _ = k6ptMargX μ a := k6pt_letter_weighted μ m k.1 k.2 a

private lemma k6pt_sum_filter_perm {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (π : FinProb α) (P : β → Prop) [DecidablePred P] [DecidablePred fun p => P (e p)] :
    ∑ q ∈ univ.filter P, (k6ptPerm e π).prob q = ∑ p ∈ univ.filter (fun p => P (e p)), π.prob p := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Equiv.sum_comp e (fun q => if P q then (k6ptPerm e π).prob q else 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [k6ptPerm]

theorem k6ptTrickY_marg_x (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) (x : X) :
    ∑ q ∈ univ.filter (fun q : X × K6ptGamPlus μ r hr × Z => q.1 = x), (k6ptTrickY μ r hr).prob q =
      k6ptMargX μ x := by
  unfold k6ptTrickY
  rw [k6pt_sum_filter_perm]
  have h := k6pt_pathTrick_start_marg (k6ptViewY μ) (2 ^ r - 1) (k6pt_odd hr) x
  refine h.trans ?_
  unfold margY k6ptViewY k6ptMargX
  rw [k6pt_sum_filter_perm]
  rfl

theorem k6ptTrickZ_marg_x (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) (x : X) :
    ∑ q ∈ univ.filter (fun q : X × Y × K6ptPhiPlus μ r hr => q.1 = x), (k6ptTrickZ μ r hr).prob q =
      k6ptMargX μ x := by
  unfold k6ptTrickZ
  rw [k6pt_sum_filter_perm]
  have h := k6pt_pathTrick_start_marg (k6ptViewZ μ) (2 ^ r - 1) (k6pt_odd hr) x
  refine h.trans ?_
  unfold margY k6ptViewZ k6ptMargX
  rw [k6pt_sum_filter_perm]
  rfl

theorem k6ptMu2_marg_x (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (x : X) :
    ∑ q ∈ univ.filter (fun q : X × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂ => q.1 = x),
      (k6ptMu2 μ r₁ hr₁ r₂ hr₂).prob q = k6ptMargX μ x :=
  (k6ptTrickZ_marg_x (k6ptMu1 μ r₁ hr₁) r₂ hr₂ x).trans (k6ptTrickY_marg_x μ r₁ hr₁ x)

/-- each of the three letters of `μ⁺` has law `μ_x` (Lemma walk-stationary (b), Lemma chain (e)). -/
theorem k6ptMuPlus_letter_marg (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁)
    (hr₂ : 1 ≤ r₂) (k : Fin 3) (a : X) :
    ∑ q ∈ univ.filter (fun q : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂ =>
      q.1.1 k = a), (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob q = k6ptMargX μ a :=
  (k6pt_pathTrick_letter_marg (k6ptMu2 μ r₁ hr₁ r₂ hr₂) 3 k6pt_odd_three k a).trans
    (k6ptMu2_marg_x μ hr₁ hr₂ a)

private lemma k6pt_sum_split {α : Type} [Fintype α] (g h : α → X) (f : α → ℝ) (a : X) :
    ∑ p ∈ univ.filter (fun p => g p = a), f p =
      ∑ b : X, ∑ p ∈ univ.filter (fun p => g p = a ∧ h p = b), f p := by
  rw [← Finset.sum_fiberwise (s := univ.filter (fun p => g p = a)) (g := h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.filter_filter]

/-- Prop. uniform-weight (c): the letters `w₁`, `w₃` of `ν` have law `(μ_x - a₀ U)/(1 - a₀)`. -/
theorem k6pt_nu_letter_law (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (μm ν : FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂))
    {a₀ : ℝ}
    (hdec : ∀ p, (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p = a₀ * μm.prob p + (1 - a₀) * ν.prob p)
    (hunif : ∀ a b : X, ∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
        K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 0 = a ∧ p.1.1 2 = b),
        μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2) (a : X) :
    (1 - a₀) * (∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
        K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 0 = a), ν.prob p) =
      k6ptMargX μ a - a₀ / (Fintype.card X : ℝ) ∧
    (1 - a₀) * (∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
        K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 2 = a), ν.prob p) =
      k6ptMargX μ a - a₀ / (Fintype.card X : ℝ) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by
    have : 0 < Fintype.card X := by
      by_contra h0
      have h0' : Fintype.card X = 0 := by omega
      have hne : IsEmpty X := Fintype.card_eq_zero_iff.1 h0'
      exact hne.false a
    positivity
  have key : ∀ (P : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂ → Prop)
      [DecidablePred P],
      ∑ p ∈ univ.filter P, (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p = k6ptMargX μ a →
      ∑ p ∈ univ.filter P, μm.prob p = 1 / (Fintype.card X : ℝ) →
      (1 - a₀) * ∑ p ∈ univ.filter P, ν.prob p = k6ptMargX μ a - a₀ / (Fintype.card X : ℝ) := by
    intro P _ h1 h2
    have h3 : ∑ p ∈ univ.filter P, (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p =
        a₀ * ∑ p ∈ univ.filter P, μm.prob p + (1 - a₀) * ∑ p ∈ univ.filter P, ν.prob p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => hdec p
    rw [h1, h2] at h3
    have : a₀ * (1 / (Fintype.card X : ℝ)) = a₀ / (Fintype.card X : ℝ) := by ring
    linarith
  have hb : ∑ _b : X, 1 / (Fintype.card X : ℝ) ^ 2 = 1 / (Fintype.card X : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  refine ⟨key _ (k6ptMuPlus_letter_marg μ hr₁ hr₂ 0 a) ?_, key _ (k6ptMuPlus_letter_marg μ hr₁ hr₂ 2 a) ?_⟩
  · rw [k6pt_sum_split (fun p => p.1.1 0) (fun p => p.1.1 2) μm.prob a, ← hb]
    exact Finset.sum_congr rfl fun b _ => hunif a b
  · rw [k6pt_sum_split (fun p => p.1.1 2) (fun p => p.1.1 0) μm.prob a, ← hb]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hunif b a]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm

/-- consequently `μ_x ≥ a₀ U` pointwise (so `ν_* ≥ 0`), for `a₀ < 1`. -/
theorem k6pt_margX_ge_of_weight (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁)
    (hr₂ : 1 ≤ r₂)
    (μm ν : FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂))
    {a₀ : ℝ} (ha₁ : a₀ < 1)
    (hdec : ∀ p, (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p = a₀ * μm.prob p + (1 - a₀) * ν.prob p)
    (hunif : ∀ a b : X, ∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
        K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 0 = a ∧ p.1.1 2 = b),
        μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2) (a : X) :
    a₀ / (Fintype.card X : ℝ) ≤ k6ptMargX μ a := by
  have h := (k6pt_nu_letter_law μ hr₁ hr₂ μm ν hdec hunif a).1
  have hnn : 0 ≤ (1 - a₀) * ∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
      K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 0 = a), ν.prob p :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun p _ => ν.nonneg p)
  linarith

end Stationarity




end TrackB
end RestrictedPolynomials
end
