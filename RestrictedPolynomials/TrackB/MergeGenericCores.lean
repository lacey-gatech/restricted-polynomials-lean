module

public import RestrictedPolynomials.TrackB.MergeGenericCoresAux2

/-!
# Track B (cores): Supplement E `lem:merge-generic` (paper IV `lem:merge`, `lem:merge2`, the
`z`-merge by symmetry) and its Q-form

The 16 targets of `MergeGeneric` that need the analytic core
(`mgen_soft_split_tail` concludes `δ ^ (1/2)`):

* the steps `mgen_degree_split` (`lem:mossel_MC` tensorised: `mgenC_spec`),
  `mgen_restrict_mass`, `mgen_soft_split_tail`, `mgen_soft_restrict_mass`;
* the cores, paper IV `writeup_stability.tex` l. 8554-8900: `mgen_sStmtY_of_mergeX`
  (`lem:merge`) and `mgen_sStmtX_of_mergeX` (`lem:merge2` with the slots `x ↔ y` exchanged: the
  soft split of the unstable `x`-function) are proved directly; `mgen_sStmtY_of_mergeY`
  (`lem:merge2`) is the `swapXY` transport of the latter and `mgen_sStmtY_of_mergeZ` (the `z`-merge
  by symmetry) the `swapXZ` transport of the former;
* the other five transports `mgen_sStmt{X,Z}_of_merge{X,Y,Z}`;
* the Q-form `mgen_qSet_of_merge{X,Y,Z}`, exactly the hypotheses `hmerge*` of
  `maxT_induction_of_merge_h64`, and the compile-time discharge.

The two slips of the printed `lem:merge2` are absorbed by the existential constants: the
cores take `η' = min η 1 / 12` (merge2) or `/ 8` (merge) and `δ₀' ≤ 1/2`.
All helpers are `private`; shared support lives in `MergeGenericCoresAux` and
`MergeGenericCoresAux2` (prefix `mgenC`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

/-! ### elementary inequalities -/

private theorem rgam_le {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (r : ℕ) :
    (r : ℝ) * γ * (1 - γ) ^ r ≤ 1 := by
  have hb : 1 + (r : ℝ) * γ ≤ (1 + γ) ^ r := one_add_mul_le_pow (by linarith) r
  have hp : (1 - γ) ^ r * (1 + γ) ^ r ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hq : 0 ≤ (1 - γ) ^ r := pow_nonneg (by linarith) r
  nlinarith

private theorem rxi_sq_le {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (r : ℕ) :
    2 * ((r : ℝ) * ξ) * ((1 - ξ) ^ 2) ^ r ≤ 1 := by
  have hb : 1 + (r : ℝ) * (2 * ξ) ≤ (1 + 2 * ξ) ^ r := one_add_mul_le_pow (by linarith) r
  have hp : ((1 - ξ) ^ 2) ^ r * (1 + 2 * ξ) ^ r ≤ 1 := by
    rw [← mul_pow]
    refine pow_le_one₀ (by positivity) ?_
    nlinarith [sq_nonneg ξ, mul_nonneg h0 (sq_nonneg ξ)]
  have hq : 0 ≤ ((1 - ξ) ^ 2) ^ r := by positivity
  nlinarith

/-- Bernoulli: `1 - (1-s)^r ≤ r s`. -/
private theorem one_sub_pow_le {s : ℝ} (h1 : s ≤ 1) (r : ℕ) :
    1 - (1 - s) ^ r ≤ r * s := by
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -s by linarith) r
  rw [← sub_eq_add_neg] at this
  linarith

private theorem one_sub_pow_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (r : ℕ) :
    0 ≤ 1 - (1 - s) ^ r := by
  have : (1 - s) ^ r ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  linarith

private theorem cl2sq_zero {X : Type} [Fintype X] {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : FinProb X) : cl2sq D (0 : (ι → X) → ℂ) = 0 := by
  simp [cl2sq, FinProb.expect]

section Steps
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `mgenMeanZeroOp` is the tensor operator `Q` on `A`, identity off `A`. -/
private theorem meanZero_eq (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (f : (ι → X) → ℂ) :
    mgenMeanZeroOp μ A f = mgenCOp (fun i a b => if i ∈ A then
      mgenCQ (graphNoiseKernel (lawX μ) (mgenComp μ) 1) a b else mgenCId a b) f := rfl

/-- App. A (one coordinate, `lem:mossel_MC`, tensorised): the split `f = f₁ + f₂` into non-merged
degree `< d` and `≥ d`; `γ = Ω_{α,m}(1)` is the gap of `S` off the component constants.
Constants before `μ`, atoms and alphabet bounds only. -/
theorem mgen_degree_split (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : (ι → X) → ℂ),
          ∃ f₁ f₂ : (ι → X) → ℂ, (∀ x, f x = f₁ x + f₂ x) ∧
            (∀ A : Finset ι, d ≤ A.card → mgenMeanZeroOp μ A f₁ = 0) ∧
            (((lawX μ).pi ι).cinner f₂ (mgenSOp μ f₂)).re ≤ (1 - γ) ^ d * cl2sq (lawX μ) f ∧
            cl2sq (lawX μ) f₁ ≤ cl2sq (lawX μ) f := by
  obtain ⟨γ, hγ0, hγ1, H⟩ := mgenC_spec m hα
  refine ⟨γ, hγ0, hγ1, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX _ _ μ hat ι _ _ d f
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  have hEE := mgenC_gnE_idem (D := lawX μ) hG
  have hErev := mgenC_gnE_rev (D := lawX μ) hG
  set E := graphNoiseKernel (lawX μ) (mgenComp μ) 1 with hE
  set c₁ : Finset ι → ℂ := fun B => if B.card < d then 1 else 0 with hc₁
  set c₂ : Finset ι → ℂ := fun B => if B.card < d then 0 else 1 with hc₂
  refine ⟨∑ B, c₁ B • mgenCP E B f, ∑ B, c₂ B • mgenCP E B f, ?_, ?_, ?_, ?_⟩
  · intro x
    have e1 := congrFun (mgenCP_sum (E := E) f) x
    rw [Finset.sum_apply] at e1
    rw [← e1, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hc₁, hc₂]
    split_ifs <;> ring
  · intro A hA
    rw [meanZero_eq, mgenCOp_sum]
    refine Finset.sum_eq_zero fun B _ => ?_
    rw [mgenCOp_smul, mgenCOp_Q_mgenCP hEE]
    by_cases hB : B.card < d
    · have : ¬ A ⊆ B := fun h => absurd (Finset.card_le_card h) (by omega)
      simp [this]
    · simp [hc₁, hB]
  · refine (H X Y Z hX μ hat ι c₂ f).trans ?_
    rw [mgenCP_cl2sq (D := lawX μ) hEE hErev f, Finset.mul_sum]
    refine Finset.sum_le_sum fun B _ => ?_
    by_cases hB : B.card < d
    · simp only [hc₂, hB, ite_true, norm_zero]
      norm_num
      exact mul_nonneg (pow_nonneg (by linarith) _) (cl2sq_nonneg _ _)
    · simp only [hc₂, hB, ite_false, norm_one, one_pow, one_mul]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)) (cl2sq_nonneg _ _)
  · rw [mgenCP_cl2sq_sum (D := lawX μ) hEE hErev, mgenCP_cl2sq (D := lawX μ) hEE hErev f]
    refine Finset.sum_le_sum fun B _ => ?_
    by_cases hB : B.card < d
    · simp [hc₁, hB]
    · simp [hc₁, hB, cl2sq_nonneg]

/-- event `E₃` (merge, l. 8554ff.): after a random restriction with live density `s`, the mass of
a degree-`< d` function off the non-merged degree `0` part has expectation `≤ d s ‖f₁‖²`
(`P₀ = ⊗ E`, `E` the component average, is `graphNoiseOp _ _ 1`). -/
theorem mgen_restrict_mass (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (f₁ : (ι → X) → ℂ)
    (hlow : ∀ A : Finset ι, d ≤ A.card → mgenMeanZeroOp μ A f₁ = 0) :
    (mixtureRestrictionExpect s hs0 hs1 (lawX μ) f₁ fun I gt =>
        ((cl2sq (lawX μ) (fun x => gt x - graphNoiseOp (lawX μ) (mgenComp μ) 1 gt x) : ℝ) : ℂ)).re ≤
      d * s * cl2sq (lawX μ) f₁ := by
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  have hEE := mgenC_gnE_idem (D := lawX μ) hG
  have hErev := mgenC_gnE_rev (D := lawX μ) hG
  rw [mgenC_restrict_identity (lawX μ) (mgenComp μ) hG hs0 hs1 f₁,
    mgenCP_cl2sq (D := lawX μ) hEE hErev f₁, Finset.mul_sum]
  refine Finset.sum_le_sum fun B _ => ?_
  by_cases hB : d ≤ B.card
  · have h0 : mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B f₁ = 0 := by
      rw [mgenCP_eq_comp, ← meanZero_eq, hlow B hB, mgenCOp_zero]
    rw [h0, cl2sq_zero]
    simp
  · push Not at hB
    have h1 := one_sub_pow_le hs1 B.card
    have h2 : (B.card : ℝ) * s ≤ d * s :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hB.le) hs0
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (cl2sq_nonneg _ _)

/-- term (II) of paper IV `lem:merge2`: the soft split `g = R^{⊗} g + (I - R^{⊗}) g`,
`R = graphNoiseOp _ _ (1/d)` (stay w.p. `1 - 1/d`, else resample in the component), `d = ⌈W δ^{-1/2}⌉`:
`⟨S g₂, g₂⟩ ≤ δ^{1/2} ‖g‖²` (this is what the printed `|(II)| ≤ δ^{1/4}` needs). -/
theorem mgen_soft_split_tail (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ W δ₁ : ℝ, 0 < W ∧ 0 < δ₁ ∧ δ₁ ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : (ι → X) → ℂ),
          (((lawX μ).pi ι).cinner
            (fun x => g x - graphNoiseOp (lawX μ) (mgenComp μ) (1 / (⌈W / Real.sqrt δ⌉₊ : ℝ)) g x)
            (mgenSOp μ fun x => g x -
              graphNoiseOp (lawX μ) (mgenComp μ) (1 / (⌈W / Real.sqrt δ⌉₊ : ℝ)) g x)).re ≤
            δ ^ (1 / 2 : ℝ) * cl2sq (lawX μ) g := by
  obtain ⟨γ, hγ0, hγ1, H⟩ := mgenC_spec m hα
  refine ⟨1 / γ, 1, by positivity, one_pos, le_rfl, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX _ _ μ hat δ hδ0 _ ι _ _ g
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  have hEE := mgenC_gnE_idem (D := lawX μ) hG
  have hErev := mgenC_gnE_rev (D := lawX μ) hG
  set E := graphNoiseKernel (lawX μ) (mgenComp μ) 1 with hE
  set d : ℕ := ⌈1 / γ / Real.sqrt δ⌉₊ with hd
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hdge : 1 / γ / Real.sqrt δ ≤ d := Nat.le_ceil _
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hdge
  set ξ : ℝ := 1 / (d : ℝ) with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hξ1 : ξ ≤ 1 := by
    rw [hξ, div_le_one hdpos]
    have : (1 : ℝ) ≤ d := by
      have : 0 < d := by exact_mod_cast hdpos
      exact_mod_cast this
    exact this
  have hξγ : ξ / γ ≤ Real.sqrt δ := by
    rw [hξ, div_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hdge (show 0 ≤ γ * Real.sqrt δ by positivity)
    have e : 1 / γ / Real.sqrt δ * (γ * Real.sqrt δ) = 1 := by field_simp
    nlinarith
  have hrep : (fun x => g x - graphNoiseOp (lawX μ) (mgenComp μ) ξ g x) =
      ∑ B : Finset ι, (((1 - (1 - ξ) ^ B.card : ℝ)) : ℂ) • mgenCP E B g := by
    funext x
    have e1 := congrFun (mgenCP_sum (E := E) g) x
    rw [Finset.sum_apply] at e1
    rw [mgenC_gn_blocks, Finset.sum_apply, Finset.sum_apply]
    conv_lhs => rw [← e1]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hrep]
  refine (H X Y Z hX μ hat ι _ g).trans ?_
  rw [← Real.sqrt_eq_rpow, mgenCP_cl2sq (D := lawX μ) hEE hErev g, Finset.mul_sum]
  refine Finset.sum_le_sum fun B _ => mul_le_mul_of_nonneg_right ?_ (cl2sq_nonneg _ _)
  set r := B.card
  have hc0 := one_sub_pow_nonneg hξ0 hξ1 r
  have hc1 : 1 - (1 - ξ) ^ r ≤ 1 := by
    have : 0 ≤ (1 - ξ) ^ r := pow_nonneg (by linarith) r
    linarith
  have hc := one_sub_pow_le hξ1 r
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hg1 : 0 ≤ (1 - γ) ^ r := pow_nonneg (by linarith) r
  have hR := rgam_le hγ0.le hγ1 r
  calc (1 - (1 - ξ) ^ r) ^ 2 * (1 - γ) ^ r ≤ (r * ξ) * (1 - γ) ^ r := by
        refine mul_le_mul_of_nonneg_right ?_ hg1
        nlinarith
    _ = ξ / γ * ((r : ℝ) * γ * (1 - γ) ^ r) := by field_simp
    _ ≤ ξ / γ * 1 := mul_le_mul_of_nonneg_left hR (by positivity)
    _ ≤ Real.sqrt δ := by linarith

/-- event `E₂` of `merge2`: for `g₁ = R^{⊗} g`, `R = graphNoiseOp _ _ (1/d)`, `s = δ^{1/3}/d`, the
expected mass off non-merged degree `0` after a restriction with live density `s` is
`≤ log(1/δ) δ^{1/3}` (`δ ≤ 1/2`: the printed bound needs it, slip in the source). -/
theorem mgen_soft_restrict_mass (μ : FinProb (X × Y × Z)) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    {d : ℕ} (hd : 1 ≤ d) {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → X) → ℂ)
    (hg : cl2sq (lawX μ) g ≤ 1) (hs0 : 0 ≤ δ ^ (1 / 3 : ℝ) / d) (hs1 : δ ^ (1 / 3 : ℝ) / d ≤ 1) :
    (mixtureRestrictionExpect (δ ^ (1 / 3 : ℝ) / d) hs0 hs1 (lawX μ)
        (fun x => graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) g x)
        fun I gt => ((cl2sq (lawX μ)
          (fun x => gt x - graphNoiseOp (lawX μ) (mgenComp μ) 1 gt x) : ℝ) : ℂ)).re ≤
      Real.log (1 / δ) * δ ^ (1 / 3 : ℝ) := by
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  have hEE := mgenC_gnE_idem (D := lawX μ) hG
  have hErev := mgenC_gnE_rev (D := lawX μ) hG
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set ξ : ℝ := 1 / (d : ℝ) with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hξ1 : ξ ≤ 1 := by
    rw [hξ, div_le_one hdpos]
    exact_mod_cast hd
  set t : ℝ := δ ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  have hPR : ∀ B : Finset ι, mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B (fun x => graphNoiseOp (lawX μ) (mgenComp μ) ξ g x) =
      (((1 - ξ) ^ B.card : ℝ) : ℂ) • mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B g := by
    intro B
    have e : (fun x => graphNoiseOp (lawX μ) (mgenComp μ) ξ g x) =
        graphNoiseOp (lawX μ) (mgenComp μ) ξ g := rfl
    rw [e, mgenC_gn_blocks]
    unfold mgenCP
    rw [mgenCOp_sum]
    simp only [mgenCOp_smul]
    rw [Finset.sum_eq_single B]
    · have := mgenCP_mgenCP hEE B B g
      unfold mgenCP at this
      rw [this, if_pos rfl]
    · intro C _ hCB
      have := mgenCP_mgenCP hEE B C g
      unfold mgenCP at this
      rw [this, if_neg (Ne.symm hCB), smul_zero]
    · simp
  rw [mgenC_restrict_identity (lawX μ) (mgenComp μ) hG hs0 hs1]
  simp only [hPR, mgenC_cl2sq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hlog : (1 / 2 : ℝ) ≤ Real.log (1 / δ) := by
    have h2 : Real.log 2 ≤ Real.log (1 / δ) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hδ0]
      linarith
    have := Real.log_two_gt_d9
    linarith
  have hper : ∀ B : Finset ι, (1 - (1 - t / d) ^ B.card) * ((1 - ξ) ^ B.card) ^ 2 ≤ t / 2 := by
    intro B
    set r := B.card
    have hs0' : 0 ≤ t / d := hs0
    have hs1' : t / d ≤ 1 := hs1
    have h1 := one_sub_pow_le hs1' r
    have h2 := rxi_sq_le hξ0 hξ1 r
    have h3 : 0 ≤ ((1 - ξ) ^ r) ^ 2 := sq_nonneg _
    have e : ((1 - ξ) ^ r) ^ 2 = ((1 - ξ) ^ 2) ^ r := by rw [← pow_mul, ← pow_mul, mul_comm]
    have e2 : t / d = t * ξ := by rw [hξ]; ring
    rw [e2] at h1
    rw [e]
    rw [e] at h3
    calc (1 - (1 - t / d) ^ r) * ((1 - ξ) ^ 2) ^ r ≤ (r * (t * ξ)) * ((1 - ξ) ^ 2) ^ r :=
          mul_le_mul_of_nonneg_right (by rw [e2]; exact h1) h3
      _ = t / 2 * (2 * ((r : ℝ) * ξ) * ((1 - ξ) ^ 2) ^ r) := by ring
      _ ≤ t / 2 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = t / 2 := mul_one _
  calc ∑ B : Finset ι, (1 - (1 - t / d) ^ B.card) * (((1 - ξ) ^ B.card) ^ 2 *
        cl2sq (lawX μ) (mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B g))
      ≤ ∑ B : Finset ι, t / 2 * cl2sq (lawX μ) (mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B g) := by
        refine Finset.sum_le_sum fun B _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hper B) (cl2sq_nonneg _ _)
    _ = t / 2 * cl2sq (lawX μ) g := by
        rw [← Finset.mul_sum, ← mgenCP_cl2sq (D := lawX μ) hEE hErev g]
    _ ≤ t / 2 * 1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤ Real.log (1 / δ) * t := by nlinarith

end Steps

section Cores
open scoped Classical

/-- core (x,y). -/
theorem mgen_sStmtY_of_mergeX (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ a : X → X, MergeRep (mergeGraphX μ.support) a →
          SStmtY (mergeDistX μ a) M δ₀ η → SStmtY μ M' δ₀' η' := by
  obtain ⟨γ, hγ0, hγ1, Hsplit⟩ := mgen_degree_split m hα
  obtain ⟨K, hK0, Hstab⟩ := mgen_restriction_event_stab m hα
  have hC0 : 0 < 6 / γ + 1 := by positivity
  have hδ₂0 : 0 < min δ₀ 1 := lt_min hδ0 one_pos
  have hη'0 : 0 < min η 1 / 8 := by positivity
  have hB0 : 0 ≤ Real.sqrt M * (K * (6 / γ + 1)) ^ (η / 2) := by positivity
  refine ⟨3 + 1 / K + Real.sqrt M * (K * (6 / γ + 1)) ^ (η / 2),
    min (1 / 2) ((min δ₀ 1 / (K * (6 / γ + 1))) ^ 2), min η 1 / 8, ?_, lt_min (by norm_num)
    (by positivity), (min_le_left _ _).trans (by norm_num), hη'0, ?_⟩
  · have : 0 ≤ 1 / K := by positivity
    linarith
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat a ha Hμ' δ hδ hδδ n f g h hf hg hh hs
  obtain ⟨hε0, hε1, hε3, hpow, hs0, hs1, hds, hδ'0, hδ'δ₂, hKδ, hδ'le, hδK⟩ :=
    mgenC_xy_params (ε := δ ^ (1 / (6 : ℕ) : ℝ)) (d := ⌈Real.log (1 / δ) / γ⌉₊)
      (s := (δ ^ (1 / (6 : ℕ) : ℝ)) ^ 2 / (⌈Real.log (1 / δ) / γ⌉₊ : ℕ)) hγ0 hγ1 hK0 hδ₂0
      (min_le_right _ _) hδ
      (hδδ.trans (min_le_left _ _)) (hδδ.trans (min_le_right _ _)) rfl rfl rfl
  set ε := δ ^ (1 / (6 : ℕ) : ℝ) with hε
  set d := ⌈Real.log (1 / δ) / γ⌉₊ with hd
  set s := ε ^ 2 / (d : ℝ) with hsdef
  set δ' := K * δ / s with hδ'def
  have hδ1' : δ ≤ 1 := hδδ.trans ((min_le_left _ _).trans (by norm_num))
  obtain ⟨f₁, f₂, hsum, hlow, hS2, hN1⟩ := Hsplit X Y Z hX hY hZ μ hat (Fin n) d f
  have hcl : cl2sq (lawX μ) f ≤ 1 := mgenC_cl2sq_le_one _ f hf
  have hII : ‖corr3 μ f₂ g h‖ ≤ ε ^ 3 := by
    have h1 := mgen_corr3_sq_le μ f₂ g h hg hh
    have h2 : ‖corr3 μ f₂ g h‖ ^ 2 ≤ (ε ^ 3) ^ 2 := by
      have h3 : (1 - γ) ^ d * cl2sq (lawX μ) f ≤ δ * 1 :=
        mul_le_mul hpow hcl (cl2sq_nonneg _ _) hδ.le
      have h4 : (ε ^ 3) ^ 2 = δ := by rw [← pow_mul, hε, mgenC_rpow_inv_pow hδ.le]; norm_num
      linarith [h1.trans hS2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h2
  set Q := Real.sqrt (M * δ' ^ η) with hQdef
  let W : (I : Finset (Fin n)) → (↥Iᶜ → X) → ℝ := fun I z => cl2sq (lawX μ)
    (fun x => restrictFree I z f₁ x - graphNoiseOp (lawX μ) (mgenComp μ) 1 (restrictFree I z f₁) x)
  let N : (I : Finset (Fin n)) → (↥Iᶜ → X) → ℝ := fun I z => cl2sq (lawX μ) (restrictFree I z f₁)
  let S : (I : Finset (Fin n)) → (↥Iᶜ → Y) → ℝ := fun I z =>
    (cstab (lawY μ) (1 - δ') (restrictFree I z g)).re
  have hI : ‖corr3 μ f₁ g h‖ ≤ (1 / (2 * ε)) * mgenCjE s hs0.le hs1 (lawX μ) W +
      (Q / 2 + ε / 2) * mgenCjE s hs0.le hs1 (lawX μ) N +
      (1 / (2 * ε * δ')) * mgenCjE s hs0.le hs1 (lawY μ) S + (ε / 2 + Q / 2) :=
    mgenC_restrict_affine μ hs0.le hs1 f₁ g h (fun q => q.2.1) _ _ _ _ W N S
      (fun I t => mgenC_xy_pointwise μ a ha Hμ' (by linarith) hδ'0 (hδ'δ₂.trans (min_le_right _ _))
        (hδ'δ₂.trans (min_le_left _ _)) hε0 _ _ _ (mgenC_restrict_bounded I _ g hg)
        (mgenC_restrict_bounded I _ h hh))
  have hjW : mgenCjE s hs0.le hs1 (lawX μ) W ≤ ε ^ 2 := by
    have h1 := mgen_restrict_mass μ d hs0.le hs1 f₁ hlow
    rw [mgenC_jE_mix hs0.le hs1 (lawX μ) f₁ (fun I gt => cl2sq (lawX μ)
      (fun x => gt x - graphNoiseOp (lawX μ) (mgenComp μ) 1 gt x)), hds] at h1
    have h2 : ε ^ 2 * cl2sq (lawX μ) f₁ ≤ ε ^ 2 :=
      mul_le_of_le_one_right (by positivity) (hN1.trans hcl)
    exact h1.trans h2
  have hjN : mgenCjE s hs0.le hs1 (lawX μ) N = cl2sq (lawX μ) f₁ := mgenC_jE_cl2sq hs0.le hs1 (lawX μ) f₁
  have hjS : mgenCjE s hs0.le hs1 (lawY μ) S ≤ δ := by
    have h1 := Hstab Y hY (lawY μ) (mgenC_atoms_lawY hT hat) s δ hs0 hs1 hδ hKδ (Fin n) g
    have e : (mixtureRestrictionExpect s hs0.le hs1 (lawY μ) g fun I gt =>
        cstab (lawY μ) (1 - K * δ / s) gt) = mixtureRestrictionExpect s hs0.le hs1 (lawY μ) g
        (fun I gt => (((cstab (lawY μ) (1 - δ') gt).re : ℝ) : ℂ)) := by
      congr 1
      funext I gt
      exact cstab_eq_ofReal_re _ _ _
    rw [e, mgenC_jE_mix] at h1
    exact h1.trans hs
  have hsplit : corr3 μ f g h = corr3 μ f₁ g h + corr3 μ f₂ g h := by
    unfold corr3 FinProb.cexpect
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hsum]
    ring
  have hθ : ε ≤ δ ^ (min η 1 / 8) := by
    rw [hε]
    refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1' ?_
    have : min η 1 ≤ 1 := min_le_right _ _
    push_cast
    linarith
  have hθ2 : δ ^ (η / 4) ≤ δ ^ (min η 1 / 8) := by
    refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1' ?_
    have : min η 1 ≤ η := min_le_left _ _
    linarith
  have hQ := (mgenC_rpow_Q_le (M := M) (by linarith) hK0.le hC0.le hδ.le hδ'0.le hε0.le hη.le hδ'le
    hε3).trans (mul_le_mul_of_nonneg_left hθ2 hB0)
  have hfin := mgenC_xy_final (jN := mgenCjE s hs0.le hs1 (lawX μ) N) hε0 hε1 hK0 hδ'0
    (Real.sqrt_nonneg _) hjW (by rw [hjN]; linarith) hjS hδK hQ hθ
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith [hI, hII]

/-- core (x,x) (paper IV `lem:merge2` with the slots `x ↔ y` exchanged: the soft split of the unstable
`x`-function by `R = graphNoiseOp _ _ (1/d)`); the core (y,y) is its `swapXY` transport. -/
theorem mgen_sStmtX_of_mergeX (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ a : X → X, MergeRep (mergeGraphX μ.support) a →
          SStmtX (mergeDistX μ a) M δ₀ η → SStmtX μ M' δ₀' η' := by
  obtain ⟨Wc, δ₁, hW0, hδ₁0, hδ₁1, Hsoft⟩ := mgen_soft_split_tail m hα
  obtain ⟨K, hK0, Hstab⟩ := mgen_restriction_event_stab m hα
  have hC0 : 0 < Wc + 1 := by linarith
  have hδ₂0 : 0 < min δ₀ 1 := lt_min hδ0 one_pos
  have hB0 : 0 ≤ M * (K * (Wc + 1)) ^ η := by positivity
  refine ⟨8 + 1 / K + M * (K * (Wc + 1)) ^ η,
    min (min δ₁ (1 / 2)) ((min δ₀ 1 / (K * (Wc + 1))) ^ 6), min η 1 / 12, ?_,
    lt_min (lt_min hδ₁0 (by norm_num)) (by positivity),
    (min_le_left _ _).trans ((min_le_left _ _).trans hδ₁1), by positivity, ?_⟩
  · have : 0 ≤ 1 / K := by positivity
    linarith
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat a ha Hμ' δ hδ hδδ n f g h hf hg hh hs
  have hδδ₁ : δ ≤ δ₁ := hδδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδh : δ ≤ 1 / 2 := hδδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1' : δ ≤ 1 := by linarith
  obtain ⟨hε0, hε1, hε6, hd1, hs0, hs1, hδ'0, hδ'δ₂, hKδ, hδ'le, hδK, hlogb⟩ :=
    mgenC_xx_params (ε := δ ^ (1 / (12 : ℕ) : ℝ)) (d := ⌈Wc / Real.sqrt δ⌉₊)
      (s := δ ^ (1 / 3 : ℝ) / (⌈Wc / Real.sqrt δ⌉₊ : ℕ)) hW0 hK0 hδ₂0 (min_le_right _ _) hδ hδh
      (hδδ.trans (min_le_right _ _)) rfl rfl rfl
  set ε := δ ^ (1 / (12 : ℕ) : ℝ) with hε
  set d := ⌈Wc / Real.sqrt δ⌉₊ with hd
  set s := δ ^ (1 / 3 : ℝ) / (d : ℝ) with hsdef
  set δ' := K * δ / s with hδ'def
  have hcl : cl2sq (lawX μ) f ≤ 1 := mgenC_cl2sq_le_one _ f hf
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hξ0 : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have hξ1 : 1 / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdpos]
    exact_mod_cast hd1
  -- term (II): the soft split
  have hII : ‖corr3 μ (fun x => f x - graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) f x)
      g h‖ ≤ ε ^ 3 := by
    have h1 := mgen_corr3_sq_le μ (fun x => f x - graphNoiseOp (lawX μ) (mgenComp μ)
      (1 / (d : ℝ)) f x) g h hg hh
    have h2 := Hsoft X Y Z hX hY hZ μ hat δ hδ hδδ₁ (Fin n) f
    have h3 : ‖corr3 μ (fun x => f x - graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) f x)
        g h‖ ^ 2 ≤ (ε ^ 3) ^ 2 := by
      have h4 : δ ^ (1 / 2 : ℝ) * cl2sq (lawX μ) f ≤ ε ^ 6 * 1 := by
        rw [hε6]
        exact mul_le_mul_of_nonneg_left hcl (by positivity)
      have e : (ε ^ 3) ^ 2 = ε ^ 6 := by ring
      linarith [h1.trans h2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h3
  -- term (I): restriction of `R f`
  have hf₁b : ∀ x, ‖graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) f x‖ ≤ 1 :=
    fun x => mgenC_gn_bounded _ _ hξ0 hξ1 f hf x
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  have hstab₁ : (cstab (lawX μ) (1 - δ)
      (fun x => graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) f x)).re ≤ δ :=
    (mgen_stab_graphNoise_le (lawX μ) (mgenComp μ) hG hξ0 hξ1 (by linarith) (by linarith)
      f).trans hs
  set f₁ : (Fin n → X) → ℂ := fun x => graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) f x
    with hf₁
  let W : (I : Finset (Fin n)) → (↥Iᶜ → X) → ℝ := fun I z => cl2sq (lawX μ)
    (fun x => restrictFree I z f₁ x - graphNoiseOp (lawX μ) (mgenComp μ) 1 (restrictFree I z f₁) x)
  let S : (I : Finset (Fin n)) → (↥Iᶜ → X) → ℝ := fun I z =>
    (cstab (lawX μ) (1 - δ') (restrictFree I z f₁)).re
  have hI : ‖corr3 μ f₁ g h‖ ≤ (1 / (2 * ε)) * mgenCjE s hs0.le hs1 (lawX μ) W +
      0 * mgenCjE s hs0.le hs1 (lawX μ) W + (1 / δ') * mgenCjE s hs0.le hs1 (lawX μ) S +
      (ε / 2 + M * δ' ^ η) :=
    mgenC_restrict_affine μ hs0.le hs1 f₁ g h (fun q => q.1) _ _ _ _ W W S
      (fun I t => mgenC_xx_pointwise μ a ha Hμ' (by linarith) hδ'0 (hδ'δ₂.trans (min_le_right _ _))
        (hδ'δ₂.trans (min_le_left _ _)) hε0 _ _ _ (mgenC_restrict_bounded I _ f₁ hf₁b)
        (mgenC_restrict_bounded I _ g hg) (mgenC_restrict_bounded I _ h hh))
  have hjW : mgenCjE s hs0.le hs1 (lawX μ) W ≤ 12 * ε ^ 3 := by
    have h1 := mgen_soft_restrict_mass μ hδ hδh hd1 f hcl hs0.le hs1
    rw [mgenC_jE_mix hs0.le hs1 (lawX μ) f₁ (fun I gt => cl2sq (lawX μ)
      (fun x => gt x - graphNoiseOp (lawX μ) (mgenComp μ) 1 gt x))] at h1
    exact h1.trans hlogb
  have hjS : mgenCjE s hs0.le hs1 (lawX μ) S ≤ δ := by
    have h1 := Hstab X hX (lawX μ) (mgenC_atoms_lawX hT hat) s δ hs0 hs1 hδ hKδ (Fin n) f₁
    have e : (mixtureRestrictionExpect s hs0.le hs1 (lawX μ) f₁ fun I gt =>
        cstab (lawX μ) (1 - K * δ / s) gt) = mixtureRestrictionExpect s hs0.le hs1 (lawX μ) f₁
        (fun I gt => (((cstab (lawX μ) (1 - δ') gt).re : ℝ) : ℂ)) := by
      congr 1
      funext I gt
      exact cstab_eq_ofReal_re _ _ _
    rw [e, mgenC_jE_mix] at h1
    exact h1.trans hstab₁
  have hθ : ε ≤ δ ^ (min η 1 / 12) := by
    rw [hε]
    refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1' ?_
    have : min η 1 ≤ 1 := min_le_right _ _
    push_cast
    linarith
  have hθ2 : δ ^ (η / 6) ≤ δ ^ (min η 1 / 12) := by
    refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1' ?_
    have : min η 1 ≤ η := min_le_left _ _
    linarith
  have hε2 : ε ^ 2 = δ ^ (1 / 6 : ℝ) := by rw [hε, mgenC_rpow_inv_pow hδ.le]; norm_num
  have hP := (mgenC_rpow_P_le (M := M) (by linarith) hK0.le hC0.le hδ.le hδ'0.le hη.le hδ'le
    hε2).trans (mul_le_mul_of_nonneg_left hθ2 hB0)
  have hfin := mgenC_xx_final hε0 hε1 hK0 hδ'0 hjW hjS hδK hP hθ
  have hsplit : corr3 μ f g h = corr3 μ f₁ g h +
      corr3 μ (fun x => f x - graphNoiseOp (lawX μ) (mgenComp μ) (1 / (d : ℝ)) f x) g h := by
    unfold corr3 FinProb.cexpect
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hf₁]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith [hI, hII]

/-- core (y,y) (paper IV `lem:merge2`): the `swapXY` transport of `mgen_sStmtX_of_mergeX`. -/
theorem mgen_sStmtY_of_mergeY (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ b : Y → Y, MergeRep (mergeGraphY μ.support) b →
          SStmtY (mergeDistY μ b) M δ₀ η → SStmtY μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtX_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat b hb Hμ'
  rw [sStmtY_iff_swapXY]
  refine H Y X Z hY hX hZ (lawSwapXY μ) ?_ (mgenC_atom_push μ _ hat) b ?_ ?_
  · rw [lawSwapXY_support]; exact (inT_swapXY_iff _).2 hT
  · rw [lawSwapXY_support, mgen_mergeGraphX_swapXY]; exact hb
  · rw [mgen_mergeDistX_lawSwapXY, ← sStmtY_iff_swapXY]; exact Hμ'

/-- core (z,y) (paper IV `lem:merge`, step `z-merge-by-symmetry`): the `swapXZ` transport of
`mgen_sStmtY_of_mergeX`. -/
theorem mgen_sStmtY_of_mergeZ (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ c : Z → Z, MergeRep (mergeGraphZ μ.support) c →
          SStmtY (mergeDistZ μ c) M δ₀ η → SStmtY μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtY_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat c hc Hμ'
  rw [mgen_sStmtY_iff_swapXZ]
  refine H Z Y X hZ hY hX (lawSwapXZ μ) ?_ (mgenC_atom_push μ _ hat) c ?_ ?_
  · rw [lawSwapXZ_support]; exact (inT_swapXZ_iff _).2 hT
  · rw [lawSwapXZ_support, mgen_mergeGraphX_swapXZ]; exact hc
  · rw [mgen_mergeDistX_lawSwapXZ, ← mgen_sStmtY_iff_swapXZ]; exact Hμ'

/-- transport to (x,z) from the cores. -/
theorem mgen_sStmtZ_of_mergeX (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ a : X → X, MergeRep (mergeGraphX μ.support) a →
          SStmtZ (mergeDistX μ a) M δ₀ η → SStmtZ μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtY_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat a ha Hμ'
  rw [sStmtZ_iff_swapYZ]
  refine H X Z Y hX hZ hY (lawSwapYZ μ) ?_ (mgenC_atom_push μ _ hat) a ?_ ?_
  · rw [lawSwapYZ_support]; exact (inT_swapYZ_iff _).2 hT
  · rw [lawSwapYZ_support, mgen_mergeGraphX_swapYZ]; exact ha
  · rw [mgen_mergeDistX_lawSwapYZ, ← sStmtZ_iff_swapYZ]; exact Hμ'

/-- transport to (y,x) from the cores. -/
theorem mgen_sStmtX_of_mergeY (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ b : Y → Y, MergeRep (mergeGraphY μ.support) b →
          SStmtX (mergeDistY μ b) M δ₀ η → SStmtX μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtY_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat b hb Hμ'
  rw [sStmtX_iff_swapXY]
  refine H Y X Z hY hX hZ (lawSwapXY μ) ?_ (mgenC_atom_push μ _ hat) b ?_ ?_
  · rw [lawSwapXY_support]; exact (inT_swapXY_iff _).2 hT
  · rw [lawSwapXY_support, mgen_mergeGraphX_swapXY]; exact hb
  · rw [mgen_mergeDistX_lawSwapXY, ← sStmtX_iff_swapXY]; exact Hμ'

/-- transport to (y,z) from the cores. -/
theorem mgen_sStmtZ_of_mergeY (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ b : Y → Y, MergeRep (mergeGraphY μ.support) b →
          SStmtZ (mergeDistY μ b) M δ₀ η → SStmtZ μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtZ_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat b hb Hμ'
  rw [sStmtZ_iff_swapXY]
  refine H Y X Z hY hX hZ (lawSwapXY μ) ?_ (mgenC_atom_push μ _ hat) b ?_ ?_
  · rw [lawSwapXY_support]; exact (inT_swapXY_iff _).2 hT
  · rw [lawSwapXY_support, mgen_mergeGraphX_swapXY]; exact hb
  · rw [mgen_mergeDistX_lawSwapXY, ← sStmtZ_iff_swapXY]; exact Hμ'

/-- transport to (z,x) from the cores. -/
theorem mgen_sStmtX_of_mergeZ (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ c : Z → Z, MergeRep (mergeGraphZ μ.support) c →
          SStmtX (mergeDistZ μ c) M δ₀ η → SStmtX μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtZ_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat c hc Hμ'
  rw [mgen_sStmtX_iff_swapXZ]
  refine H Z Y X hZ hY hX (lawSwapXZ μ) ?_ (mgenC_atom_push μ _ hat) c ?_ ?_
  · rw [lawSwapXZ_support]; exact (inT_swapXZ_iff _).2 hT
  · rw [lawSwapXZ_support, mgen_mergeGraphX_swapXZ]; exact hc
  · rw [mgen_mergeDistX_lawSwapXZ, ← mgen_sStmtX_iff_swapXZ]; exact Hμ'

/-- transport to (z,z) from the cores. -/
theorem mgen_sStmtZ_of_mergeZ (m : ℕ) {α : ℝ} (hα : 0 < α) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (hη : 0 < η) :
    ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ c : Z → Z, MergeRep (mergeGraphZ μ.support) c →
          SStmtZ (mergeDistZ μ c) M δ₀ η → SStmtZ μ M' δ₀' η' := by
  obtain ⟨M', δ₀', η', hM', hd0, hd1, hη', H⟩ := mgen_sStmtX_of_mergeX m hα hM hδ0 hδ1 hη
  refine ⟨M', δ₀', η', hM', hd0, hd1, hη', ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat c hc Hμ'
  rw [mgen_sStmtZ_iff_swapXZ]
  refine H Z Y X hZ hY hX (lawSwapXZ μ) ?_ (mgenC_atom_push μ _ hat) c ?_ ?_
  · rw [lawSwapXZ_support]; exact (inT_swapXZ_iff _).2 hT
  · rw [lawSwapXZ_support, mgen_mergeGraphX_swapXZ]; exact hc
  · rw [mgen_mergeDistX_lawSwapXZ, ← mgen_sStmtZ_iff_swapXZ]; exact Hμ'

end Cores

section QForm
variable (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- Supplement E `lem:merge-generic`, "Consequently" clause, `k = x`: EXACTLY the hypothesis `hmergeX` of
`maxT_induction_of_merge_h64`. -/
theorem mgen_qSet_of_mergeX (S : Set (X × Y × Z)) (hS : InT S) (a : X → X)
    (ha : MergeRep (mergeGraphX S) a) (hna : ¬ Function.Injective a)
    (hq : QSet (mergeSetX S a)) : QSet S := by
  have hX : Fintype.card X ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    le_max_left _ _
  have hY : Fintype.card Y ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hZ : Fintype.card Z ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun α hα => ?_, fun α hα => ?_, fun α hα => ?_⟩
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.1 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtX_of_mergeX _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat a (by rw [hμ]; exact ha)
      (H _ ?_ (mergeDistX_atom_bound μ a hat))
    rw [mergeDistX_support_eq, hμ]
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.2.1 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtY_of_mergeX _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat a (by rw [hμ]; exact ha)
      (H _ ?_ (mergeDistX_atom_bound μ a hat))
    rw [mergeDistX_support_eq, hμ]
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.2.2 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtZ_of_mergeX _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat a (by rw [hμ]; exact ha)
      (H _ ?_ (mergeDistX_atom_bound μ a hat))
    rw [mergeDistX_support_eq, hμ]

theorem mgen_qSet_of_mergeY (S : Set (X × Y × Z)) (hS : InT S) (b : Y → Y)
    (hb : MergeRep (mergeGraphY S) b) (hnb : ¬ Function.Injective b)
    (hq : QSet (mergeSetY S b)) : QSet S := by
  have hX : Fintype.card X ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    le_max_left _ _
  have hY : Fintype.card Y ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hZ : Fintype.card Z ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun α hα => ?_, fun α hα => ?_, fun α hα => ?_⟩
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.1 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtX_of_mergeY _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat b (by rw [hμ]; exact hb)
      (H _ ?_ (mgen_mergeDistY_atom_bound μ b hat))
    rw [mergeDistY_support_eq, hμ]
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.2.1 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtY_of_mergeY _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat b (by rw [hμ]; exact hb)
      (H _ ?_ (mgen_mergeDistY_atom_bound μ b hat))
    rw [mergeDistY_support_eq, hμ]
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.2.2 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtZ_of_mergeY _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat b (by rw [hμ]; exact hb)
      (H _ ?_ (mgen_mergeDistY_atom_bound μ b hat))
    rw [mergeDistY_support_eq, hμ]

theorem mgen_qSet_of_mergeZ (S : Set (X × Y × Z)) (hS : InT S) (c : Z → Z)
    (hc : MergeRep (mergeGraphZ S) c) (hnc : ¬ Function.Injective c)
    (hq : QSet (mergeSetZ S c)) : QSet S := by
  have hX : Fintype.card X ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    le_max_left _ _
  have hY : Fintype.card Y ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hZ : Fintype.card Z ≤ max (Fintype.card X) (max (Fintype.card Y) (Fintype.card Z)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun α hα => ?_, fun α hα => ?_, fun α hα => ?_⟩
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.1 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtX_of_mergeZ _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat c (by rw [hμ]; exact hc)
      (H _ ?_ (mgen_mergeDistZ_atom_bound μ c hat))
    rw [mergeDistZ_support_eq, hμ]
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.2.1 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtY_of_mergeZ _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat c (by rw [hμ]; exact hc)
      (H _ ?_ (mgen_mergeDistZ_atom_bound μ c hat))
    rw [mergeDistZ_support_eq, hμ]
  · obtain ⟨M, δ₀, η, hM, hd0, hd1, hη, H⟩ := hq.2.2 α hα
    obtain ⟨M', δ₀', η', hM', hd0', hd1', hη', H'⟩ := mgen_sStmtZ_of_mergeZ _ hα hM hd0 hd1 hη
    refine ⟨M', δ₀', η', hM', hd0', hd1', hη', fun μ hμ hat => ?_⟩
    refine H' X Y Z hX hY hZ μ (by rw [hμ]; exact hS) hat c (by rw [hμ]; exact hc)
      (H _ ?_ (mgen_mergeDistZ_atom_bound μ c hat))
    rw [mergeDistZ_support_eq, hμ]

end QForm

/-- the three `mgen_qSet_of_merge*` are literally the hypotheses `hmerge*`. -/
example
    (h64 : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → FullyMergedSet S → PMaxSet S →
        1 < Fintype.card X → QY S)
    (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (S : Set (X × Y × Z)) (hS : InT S) : QSet S :=
  maxT_induction_of_merge_h64 mgen_qSet_of_mergeX mgen_qSet_of_mergeY mgen_qSet_of_mergeZ h64 X Y Z
    S hS

end MaxT
end TrackB
end RestrictedPolynomials
end
