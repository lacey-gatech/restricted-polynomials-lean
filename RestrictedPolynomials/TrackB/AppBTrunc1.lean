module

public import RestrictedPolynomials.TrackB.AppBTrunc1Aux
public import RestrictedPolynomials.TrackB.AppBChain

/-!
# Track B, Appendix B: term (III), `soft_trunc1`

Supplement I. The noise split, the restriction identity, the
`x`-marginal pushforward and the bad event are in `AppBTrunc1Aux`; the chain, its gap and the
Loewner tensor step are in `AppBChain`. This file holds the chain formula, `prop:chain-bound`,
`cor:III`, `termIa`, the kept triangle `appB_t1_triangle`, the pointwise bound, the bound
`termIa ≤ 3 ρ^{ξ/16}` and `appB_soft_trunc1`, with its statement UNCHANGED.

Constants of `appB_soft_trunc1`: `(M, δ₀, η) = (6, d0, ξ/16)`; they depend on `(m, α, ξ)` only and
are chosen before the alphabets. All proof helpers are `private`.
-/

@[expose] public section

open Finset
open scoped ComplexOrder
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Chain
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private def t1fN (ν : FinProb (X × Y × Z)) (a : X) (z : Z) : ℝ := ∑ y, ν.prob (a, y, z)

private theorem t1f_lawX_prob (ν : FinProb (X × Y × Z)) (a : X) :
    (lawX ν).prob a = ∑ z, t1fN ν a z := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.1 = a), ν.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [if_true, t1fN]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  · intro b _ hb
    simp [hb]
  · simp

private theorem t1f_lawZ_prob (ν : FinProb (X × Y × Z)) (z : Z) :
    (lawZ ν).prob z = ∑ a, t1fN ν a z := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.2 = z), ν.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [t1fN]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private theorem t1f_nonneg (ν : FinProb (X × Y × Z)) (a : X) (z : Z) : 0 ≤ t1fN ν a z :=
  Finset.sum_nonneg fun y _ => ν.nonneg _

private theorem t1f_le_lawX (ν : FinProb (X × Y × Z)) (a : X) (z : Z) :
    t1fN ν a z ≤ (lawX ν).prob a := by
  rw [t1f_lawX_prob]
  exact Finset.single_le_sum (f := fun z => t1fN ν a z) (fun z _ => t1f_nonneg ν a z)
    (Finset.mem_univ z)

private theorem t1f_mu (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (x : X) (y : Y) (z : Z) : μbar.prob (x, y, z) = t1fN ν x z * (lawY ν).prob y := hμ (x, y, z)

private theorem t1f_lawX_mu (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a : X) :
    (lawX μbar).prob a = (lawX ν).prob a := by
  rw [t1f_lawX_prob, t1f_lawX_prob]
  refine Finset.sum_congr rfl fun z _ => ?_
  show ∑ y, μbar.prob (a, y, z) = t1fN ν a z
  simp_rw [t1f_mu ν μbar hμ]
  rw [← Finset.mul_sum, (lawY ν).sum_eq_one, mul_one]

private theorem t1f_sumx_mu (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1)
    (y : Y) (z : Z) :
    ∑ x, μbar.prob (x, y, z) = (lawZ ν).prob z * (lawY ν).prob y := by
  simp_rw [t1f_mu ν μbar hμ]
  rw [← Finset.sum_mul, ← t1f_lawZ_prob]

private theorem t1f_mul_div (ν : FinProb (X × Y × Z)) (a : X) (z : Z) :
    (lawX ν).prob a * (t1fN ν a z / (lawX ν).prob a) = t1fN ν a z := by
  by_cases h : (lawX ν).prob a = 0
  · have h1 := t1f_le_lawX ν a z
    have h2 := t1f_nonneg ν a z
    rw [h] at h1 ⊢
    have : t1fN ν a z = 0 := le_antisymm h1 h2
    simp [this]
  · field_simp

private theorem t1f_formula (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a b : X) :
    mgenS μbar a b = ∑ z, (t1fN ν a z / (lawX ν).prob a) * (t1fN ν b z / (lawZ ν).prob z) := by
  unfold mgenS
  simp_rw [t1f_lawX_mu ν μbar hμ, t1f_sumx_mu ν μbar hμ, t1f_mu ν μbar hμ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have : ∀ y, t1fN ν a z * (lawY ν).prob y / (lawX ν).prob a *
      (t1fN ν b z * (lawY ν).prob y / ((lawZ ν).prob z * (lawY ν).prob y)) =
      (lawY ν).prob y * ((t1fN ν a z / (lawX ν).prob a) * (t1fN ν b z / (lawZ ν).prob z)) := by
    intro y
    by_cases hy : (lawY ν).prob y = 0
    · simp [hy]
    · rw [mul_div_mul_right _ _ hy]
      ring
  simp_rw [this]
  rw [← Finset.sum_mul, (lawY ν).sum_eq_one, one_mul]
/-- `lem:chain` (a) (Supplement I, §7): `mgenS μbar` is the chain `x → z → x'` of `ν_{xz}`; with the Lean
convention `u / 0 = 0` the sum may run over every `z`. -/
theorem appB_t1_chain_formula (ν μbar : FinProb (X × Y × Z))
    (hμ : ∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) (a b : X) :
    mgenS μbar a b = ∑ z, ((∑ y, ν.prob (a, y, z)) / (lawX ν).prob a) *
      ((∑ y, ν.prob (b, y, z)) / (lawZ ν).prob z) :=
  t1f_formula ν μbar hμ a b


end Chain

section ChainBound

/-- `prop:chain-bound` (Supplement I, §7): `|corr3 μbar F G H|² ≤ Re Stab_{1-κ}(F; ν_x)` for `1`-bounded
`G`, `H` and arbitrary `F`. Built `mgen_corr3_sq_le` (with `lawX μbar = ν_x`), then
`appB_t1_gap` and `appB_loewner_tensor`. `κ = min 1 (c_MC α²)`. -/
theorem appB_t1_chain_bound (m : ℕ) {al : ℝ} (hal : 0 < al) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
      ∀ (ν μbar : FinProb (X × Y × Z)), (∀ p ∈ ν.support, al ≤ ν.prob p) →
        PairwiseConnected3 ν.support →
        (∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → X) → ℂ) (G : (ι → Y) → ℂ)
        (H : (ι → Z) → ℂ), (∀ y, ‖G y‖ ≤ 1) → (∀ z, ‖H z‖ ≤ 1) →
        ‖corr3 μbar F G H‖ ^ 2 ≤ (cstab (lawX ν) (1 - κ) F).re := by
  obtain ⟨κ, hκ0, hκ1, H⟩ := appB_t1_gap m hal
  refine ⟨κ, hκ0, hκ1, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX ν μbar hat hT hμ ι _ _ F G H' hG hH
  obtain ⟨hx, hy, hz⟩ := appB_t1_mubar_marginals ν μbar hμ
  have h1 := mgen_corr3_sq_le μbar F G H' hG hH
  rw [hx] at h1
  obtain ⟨lam, g, j0, heig, hon, hnn, h1', hc, hgap⟩ := H X Y Z hX ν μbar hat hT hμ
  have hπ : ∀ a, 0 < (lawX ν).prob a := fun a =>
    lt_of_lt_of_le hal ((appB_inT_letters hat hT).1 a)
  have := appB_loewner_tensor (lawX ν) hπ (mgenS μbar) hκ0 hκ1 lam g j0 heig hon hnn h1' hc hgap F
  exact h1.trans this.2


/-- `cor:III` (Supplement I, §7), term (III) on the good event: for `0 < ρ ≤ min 1 (κ^(4/ξ))` (so
`δ' = ρ^{ξ/4} ≤ κ`) and `Stab_{1-δ'}(F; ν_x) ≤ ρ^{ξ/8}`: `|corr3 μbar F G H| ≤ ρ^{ξ/16}`.
`F` arbitrary (it will be `f''`). -/
theorem appB_t1_corIII (m : ℕ) {al : ℝ} (hal : 0 < al) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ ξ : ℝ, 0 < ξ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ρ ≤ κ ^ (4 / ξ) →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
      ∀ (ν μbar : FinProb (X × Y × Z)), (∀ p ∈ ν.support, al ≤ ν.prob p) →
        PairwiseConnected3 ν.support →
        (∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → X) → ℂ) (G : (ι → Y) → ℂ)
        (H : (ι → Z) → ℂ), (∀ y, ‖G y‖ ≤ 1) → (∀ z, ‖H z‖ ≤ 1) →
        (cstab (lawX ν) (1 - ρ ^ (ξ / 4)) F).re ≤ ρ ^ (ξ / 8) →
        ‖corr3 μbar F G H‖ ≤ ρ ^ (ξ / 16) := by
  obtain ⟨κ, hκ0, hκ1, H⟩ := appB_t1_chain_bound m hal
  refine ⟨κ, hκ0, hκ1, ?_⟩
  intro ξ hξ ρ hρ0 hρ1 hρκ X Y Z _ _ _ _ _ _ hX ν μbar hat hT hμ ι _ _ F G H' hG hH hW
  have hδ : ρ ^ (ξ / 4) ≤ κ := by
    calc ρ ^ (ξ / 4) ≤ (κ ^ (4 / ξ)) ^ (ξ / 4) :=
          Real.rpow_le_rpow hρ0.le hρκ (by positivity)
      _ = κ := by
          rw [← Real.rpow_mul hκ0.le]
          have : 4 / ξ * (ξ / 4) = 1 := by field_simp
          rw [this, Real.rpow_one]
  have hδ1 : ρ ^ (ξ / 4) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have hmono : (cstab (lawX ν) (1 - κ) F).re ≤ (cstab (lawX ν) (1 - ρ ^ (ξ / 4)) F).re :=
    (Complex.le_def.1 (cstab_mono (lawX ν) (by linarith) (by linarith) F)).1
  have hsq := H X Y Z hX ν μbar hat hT hμ F G H' hG hH
  have h16 : (ρ ^ (ξ / 16)) ^ 2 = ρ ^ (ξ / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1; push_cast; ring
  have hp : 0 < ρ ^ (ξ / 16) := Real.rpow_pos_of_pos hρ0 _
  by_contra hlt
  push Not at hlt
  have := mul_self_lt_mul_self hp.le hlt
  nlinarith



end ChainBound

section Assembly
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- one of the two terms of the triangle inequality of l. 8985-8988: noise `ρ'` on `g`
(defined here: the built `AppBSetting` has `termI`, `appTp`, `tNE` only). -/
def termIa {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z)) (ρ' ρ ξ : ℝ)
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) : ℝ :=
  ‖corr3 ν (f - tNE (lawX ν) (ρ ^ (1 + ξ)) f) (tNE (lawY ν) ρ' g) h‖

/-- l. 8985-8988: `(I) ≤` the same expression with `T_{1-ρ}` plus the one with `T_{1-ρ/2}`. KEPT. -/
theorem appB_t1_triangle {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (ρ ξ : ℝ) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    termI ν ρ ξ f g h ≤ termIa ν ρ ρ ξ f g h + termIa ν (ρ / 2) ρ ξ f g h := by
  unfold termI termIa appTp
  rw [corr3_sub_mid]
  exact (norm_sub_le _ _).trans_eq (add_comm _ _)


/-- Step 3 of Supplement I, Thm. `thm:soft-trunc1`, the pointwise bound for `Q`: with `f''` `2`-bounded and
`g'`, `h'` `1`-bounded, `|corr3 μbar f'' g' h'| ≤ 2` on the bad event `W > ρ^{ξ/8}` (term (IV),
factor `2`, since `f' = f - T_{1-s} f` is `2`-bounded) and `≤ ρ^{ξ/16}` on the good event (term (III), `appB_t1_corIII`).
`d3 = min 1 (κ^(4/ξ))`. -/
theorem appB_t1_pointwise (m : ℕ) {al : ℝ} (hal : 0 < al) {xi : ℝ} (hxi : 0 < xi) :
    ∃ d3 : ℝ, 0 < d3 ∧ d3 ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ d3 →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
      ∀ (ν μbar : FinProb (X × Y × Z)), (∀ p ∈ ν.support, al ≤ ν.prob p) →
        PairwiseConnected3 ν.support →
        (∀ p, μbar.prob p = (∑ y', ν.prob (p.1, y', p.2.2)) * (lawY ν).prob p.2.1) →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f'' : (ι → X) → ℂ) (g' : (ι → Y) → ℂ)
        (h' : (ι → Z) → ℂ), (∀ x, ‖f'' x‖ ≤ 2) → (∀ y, ‖g' y‖ ≤ 1) → (∀ z, ‖h' z‖ ≤ 1) →
        ‖corr3 μbar f'' g' h'‖ ≤
          if ρ ^ (xi / 8) < (cstab (lawX ν) (1 - ρ ^ (xi / 4)) f'').re then 2
          else ρ ^ (xi / 16) := by
  obtain ⟨κ, hκ0, hκ1, H⟩ := appB_t1_corIII m hal
  refine ⟨min 1 (κ ^ (4 / xi)), lt_min one_pos (Real.rpow_pos_of_pos hκ0 _), min_le_left _ _, ?_⟩
  intro ρ hρ0 hρ X Y Z _ _ _ _ _ _ hX ν μbar hat hT hμ ι _ _ f'' g' h' hf hg hh
  split_ifs with hW
  · have := appB_corr3_norm_le μbar f'' g' h' hf hg hh
    linarith
  · push Not at hW
    exact H xi hxi ρ hρ0 (hρ.trans (min_le_left _ _)) (hρ.trans (min_le_right _ _)) X Y Z hX ν
      μbar hat hT hμ f'' g' h' hg hh hW


/-- Steps 2-4 of Supplement I, Thm. `thm:soft-trunc1`: for `ρ' ∈ [ρ/2, ρ]` and `ρ ≤ d0`,
`termIa ≤ 2 ρ^{ξ/8} + ρ^{ξ/16} ≤ 3 ρ^{ξ/16}`. Uses only (A), (B) and `|X| ≤ m`. The threshold is
`d0 = min 1 (min ((c/4)^(4/ξ)) (min ((2/c)^(4/ξ)) (min (κ^(4/ξ)) δ_F)))`. -/
theorem appB_t1_termIa_le (m : ℕ) {al : ℝ} (hal : 0 < al) {xi : ℝ} (hxi : 0 < xi) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1 ∧ ∀ ρ ρ' : ℝ, 0 < ρ → ρ ≤ d0 → ρ / 2 ≤ ρ' → ρ' ≤ ρ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
      ∀ (ν : FinProb (X × Y × Z)), (∀ p ∈ ν.support, al ≤ ν.prob p) →
        PairwiseConnected3 ν.support →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
        termIa ν ρ' ρ xi f g h ≤ 3 * ρ ^ (xi / 16) := by
  obtain ⟨d2, hd2, hbad⟩ := appB_t1_bad_event_xyz m hal hxi
  obtain ⟨d3, hd3, hd31, hpt⟩ := appB_t1_pointwise m hal hxi
  refine ⟨min d2 d3, lt_min hd2 hd3, (min_le_right _ _).trans hd31, ?_⟩
  intro ρ ρ' hρ0 hρ hρ1 hρ2 X Y Z _ _ _ _ _ _ hX ν hat hT ι _ _ f g h hf hg hh
  have hρd2 : ρ ≤ d2 := hρ.trans (min_le_left _ _)
  have hρd3 : ρ ≤ d3 := hρ.trans (min_le_right _ _)
  have hρ1' : ρ ≤ 1 := hρd3.trans hd31
  have hr0 : 0 < ρ' := lt_of_lt_of_le (half_pos hρ0) hρ1
  have hr1 : ρ' ≤ 1 := hρ2.trans hρ1'
  obtain ⟨μbar, μ3, hμbar, hxb, hx3, hres⟩ := appB_t1_restriction ν hr0 hr1
  have hb0 : 0 ≤ ρ' / 2 := by linarith
  have hb1 : ρ' / 2 ≤ 1 := by linarith
  obtain ⟨_, ⟨y0⟩, ⟨z0⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hT
  set s := ρ ^ (1 + xi) with hs
  set f' : (ι → X) → ℂ := f - tNE (lawX ν) s f with hf'
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos hρ0 _).le
  have hs1 : s ≤ 1 := Real.rpow_le_one hρ0.le hρ1' (by positivity)
  have hf'2 : ∀ x, ‖f' x‖ ≤ 2 := appB_t1_fprime_sup (lawX ν) hs0 hs1 f hf
  obtain ⟨hbadA, hbadB⟩ := hbad ρ ρ' hρ0 hρd2 hρ1 hρ2 X Y Z hX ν μ3 hat hT
    (by rw [hx3]) y0 z0 hb0 hb1 ι f hf
  have step1 : termIa ν ρ' ρ xi f g h ≤
      (mixtureRestrictionExpect (ρ' / 2) hb0 hb1 μ3
        (fun t : ι → X × Y × Z => f' (fun i => (t i).1) * g (fun i => (t i).2.1) *
          h (fun i => (t i).2.2))
        (fun I G => ((‖(μbar.pi ↥I).cexpect G‖ : ℝ) : ℂ))).re := by
    have e := hres hb0 hb1 f' g h
    unfold termIa
    rw [e]
    exact appB_mre_norm_le (ρ' / 2) hb0 hb1 μ3 _ _
  have step2 : (mixtureRestrictionExpect (ρ' / 2) hb0 hb1 μ3
        (fun t : ι → X × Y × Z => f' (fun i => (t i).1) * g (fun i => (t i).2.1) *
          h (fun i => (t i).2.2))
        (fun I G => ((‖(μbar.pi ↥I).cexpect G‖ : ℝ) : ℂ))).re ≤
      (mixtureRestrictionExpect (ρ' / 2) hb0 hb1 μ3
        (fun t : ι → X × Y × Z => f' (fun i => (t i).1))
        (fun I G => ((2 : ℝ) : ℂ) * (if ρ ^ (xi / 8) < (cstab (lawX ν) (1 - ρ ^ (xi / 4))
              (fun w : ↥I → X => G (fun i => (w i, y0, z0)))).re then (1 : ℂ) else 0) +
            ((ρ ^ (xi / 16) : ℝ) : ℂ))).re := by
    refine appB_mre_mono (ρ' / 2) hb0 hb1 μ3 _ _ _ _ ?_
    intro I z
    have hp := appB_restrictFree_prod μbar I z f' g h
    have hq := congrFun (appB_restrictFree_proj I z y0 z0 f')
    simp only [Complex.ofReal_re]
    rw [hp]
    have hfI : ∀ w, ‖restrictFree I (fun i => (z i).1) f' w‖ ≤ 2 := fun w => hf'2 _
    have hgI : ∀ w, ‖restrictFree I (fun i => (z i).2.1) g w‖ ≤ 1 := fun w => hg _
    have hhI : ∀ w, ‖restrictFree I (fun i => (z i).2.2) h w‖ ≤ 1 := fun w => hh _
    have hpw := hpt ρ hρ0 hρd3 X Y Z hX ν μbar hat hT hμbar _ _ _ hfI hgI hhI
    have hq' : (fun w : ↥I → X => restrictFree I z (fun s => f' (fun i => (s i).1))
        (fun i => (w i, y0, z0))) = restrictFree I (fun i => (z i).1) f' :=
      appB_restrictFree_proj I z y0 z0 f'
    simp only [hq']
    have hc : 0 ≤ ρ ^ (xi / 16) := (Real.rpow_pos_of_pos hρ0 _).le
    split_ifs at hpw ⊢ with h1
    · simp; linarith
    · simp; linarith
  have step3 : (mixtureRestrictionExpect (ρ' / 2) hb0 hb1 μ3
        (fun t : ι → X × Y × Z => f' (fun i => (t i).1))
        (fun I G => ((2 : ℝ) : ℂ) * (if ρ ^ (xi / 8) < (cstab (lawX ν) (1 - ρ ^ (xi / 4))
              (fun w : ↥I → X => G (fun i => (w i, y0, z0)))).re then (1 : ℂ) else 0) +
            ((ρ ^ (xi / 16) : ℝ) : ℂ))).re =
      2 * (mixtureRestrictionExpect (ρ' / 2) hb0 hb1 μ3
        (fun t : ι → X × Y × Z => f' (fun i => (t i).1))
        (fun I G => if ρ ^ (xi / 8) < (cstab (lawX ν) (1 - ρ ^ (xi / 4))
              (fun w : ↥I → X => G (fun i => (w i, y0, z0)))).re then (1 : ℂ) else 0)).re +
        ρ ^ (xi / 16) :=
    appB_mre_affine (ρ' / 2) hb0 hb1 μ3 _ _ 2 (ρ ^ (xi / 16))
  have hexp : ρ ^ (xi / 8) ≤ ρ ^ (xi / 16) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1' (by linarith)
  linarith


/-- Claim `soft_trunc1` (l. 8972-8975): `(I) ≤ M ρ^η`, `ρ = 2^{-j}δ ≤ δ₀`, constants depending on
`(m, K, α, ξ)` only. The proof is the repaired one of Supplement I: `(M, δ₀, η) = (6, d0, ξ/16)`. -/
theorem appB_soft_trunc1 (m K : ℕ) {α : ℝ} (hα : 0 < α) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          termI ν ρ ξ f g h ≤ M * ρ ^ η := by
  obtain ⟨d0, hd0, hd01, H⟩ := appB_t1_termIa_le m hα hξ
  refine ⟨6, d0, ξ / 16, by norm_num, hd0, hd01, by positivity, ?_⟩
  intro ρ hρ0 hρ X Y Z _ _ _ _ _ _ hX _ _ ν Sg Sm Phi' hR n f g h hf hg hh
  have h1 := appB_t1_triangle ν ρ ξ f g h
  have h2 := H ρ ρ hρ0 hρ (by linarith) le_rfl X Y Z hX ν hR.atoms hR.inT.1 f g h hf hg hh
  have h3 := H ρ (ρ / 2) hρ0 hρ le_rfl (by linarith) X Y Z hX ν hR.atoms hR.inT.1 f g h hf hg hh
  linarith


/-- compile-time check (not a target): the shape in which
`appB_soft_truncate_main_of_homPAt` consumes `appB_soft_trunc1`, i.e. through the triple
`(M, δ₀, η)` for a fixed `ξ`, applied to a `Rel67` hypothesis and `Fin n`-indexed functions, with
the term (I) unfolded as in `appB_main_split`. -/
example (m K : ℕ) {α : ℝ} (hα : 0 < α) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          ‖corr3 ν (f - tNE (lawX ν) (ρ ^ (1 + ξ)) f) (appTp (lawY ν) ρ g) h‖ ≤ M * ρ ^ η := by
  obtain ⟨M, δ₀, η, hM, hδ, hδ1, hη, H⟩ := appB_soft_trunc1 m K hα hξ
  exact ⟨M, δ₀, η, hM, hδ, hδ1, hη, H⟩

end Assembly

end TrackB
end RestrictedPolynomials
end
