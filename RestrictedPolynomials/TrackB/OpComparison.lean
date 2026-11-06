module

public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.MarkovBlocks
public import RestrictedPolynomials.TrackB.NoiseChains
public import Mathlib.Analysis.Complex.Order

/-!
# Track B: Lemma 2.8 (the operator comparison lemma)

Source: paper IV (`writeup_stability.tex`) L1290-1369. Paper IV items
`lem:op-comparison-lemma` with steps `mixture-chain-representation`, `univariate-eigenvalue-bounds`.

Proof route (no use of `mossel_MC`: the one-coordinate gap is computed directly).
For a `G`-equivalence and a measure `D` of full support let `P_D g x` be the `D`-average of `g`
over the `G`-class of `x`; then `T_{1-ξ,D} = (1-ξ) I + ξ P_D`. The mixture chain satisfies
`μ(x) (T g)(x) = μ(x) g(x) - β ξ ν₁(x) (g - P_{ν₁} g)(x)`, which gives
`⟨g, T g⟩_μ = ‖g‖²_μ - β ξ ‖g - P_{ν₁} g‖²_{ν₁}`. On `V^⊥` (`V` the class-constant functions)
`‖g‖²_μ ≤ α₀⁻¹ ‖g - P_{ν₁} g‖²_{ν₁}`, so the gap is `α₀ β ξ` (so `s = α₀`, `C = 1`), and
`T_{1-ξ',μ}` acts as the scalar `1 - ξ'` on `V^⊥`. The tensor power comparison is
`tensor_block_bound`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section OpComparison
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the functions constant on every connected component of the graph `G` -/
def constOnGraph (G : α → α → Prop) : Submodule ℂ (α → ℂ) where
  carrier := {g | ∀ a b, (SimpleGraph.fromRel G).Reachable a b → g a = g b}
  add_mem' := fun ha hb a b h => by simp [ha a b h, hb a b h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c g hg a b h => by simp [hg a b h]

/-- the joint law of one coordinate pair `(x, x')` in the proof of Lemma 2.8: with probability
`1 - β`, `x = x' ∼ ν₂`; otherwise `x ∼ ν₁` and `x' ∼ T_{1-ξ,ν₁} x`. -/
def mixJoint (β : ℝ) (ν₁ ν₂ : FinProb α) (G : α → α → Prop) [DecidableRel G] (ξ : ℝ)
    (x x' : α) : ℝ :=
  (1 - β) * ν₂.prob x * (if x = x' then 1 else 0) + β * ν₁.prob x * graphNoiseKernel ν₁ G ξ x x'

/-- the chain `T` of `lem:op-comparison-lemma#mixture-chain-representation`: `T(x,x') = D(x,x') / μ(x)`. -/
def mixChainKernel (β : ℝ) (ν₁ ν₂ : FinProb α) (G : α → α → Prop) [DecidableRel G] (ξ : ℝ)
    (x x' : α) : ℝ :=
  mixJoint β ν₁ ν₂ G ξ x x' / (β * ν₁.prob x + (1 - β) * ν₂.prob x)

end OpComparison

section Helpers
variable {S : Type} [Fintype S] [DecidableEq S]

/-- the `D`-mass of the `G`-neighbourhood of `x` -/
private def nbr (D : FinProb S) (G : S → S → Prop) [DecidableRel G] (x : S) : ℝ :=
  ∑ c ∈ univ.filter (G x), D.prob c

/-- the `D`-average of `g` over the `G`-neighbourhood of `x` -/
private def avg (D : FinProb S) (G : S → S → Prop) [DecidableRel G] (g : S → ℂ) (x : S) : ℂ :=
  (∑ y ∈ univ.filter (G x), ((D.prob y : ℝ) : ℂ) * g y) / ((nbr D G x : ℝ) : ℂ)

/-- `‖g‖²_D` -/
private def nsq (D : FinProb S) (g : S → ℂ) : ℝ := D.expect fun a => ‖g a‖ ^ 2

variable {G : S → S → Prop} [DecidableRel G]

omit [DecidableEq S] in
private lemma cinner_nsq (D : FinProb S) (g : S → ℂ) : D.cinner g g = ((nsq D g : ℝ) : ℂ) :=
  cinner_self_eq D g

omit [DecidableEq S] in
private lemma nsq_nonneg (D : FinProb S) (g : S → ℂ) : 0 ≤ nsq D g :=
  Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (sq_nonneg _)

omit [DecidableEq S] in
private lemma nsq_pos (D : FinProb S) (hD : ∀ x, 0 < D.prob x) {g : S → ℂ} (hg : g ≠ 0) :
    0 < nsq D g := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra h; push Not at h; exact hg (funext h)
  exact Finset.sum_pos' (fun x _ => mul_nonneg (D.nonneg x) (sq_nonneg _))
    ⟨a, Finset.mem_univ a, mul_pos (hD a) (by positivity)⟩

omit [DecidableEq S] in
private lemma prob_le_one (D : FinProb S) (x : S) : D.prob x ≤ 1 := by
  rw [← D.sum_eq_one]
  exact Finset.single_le_sum (f := D.prob) (fun c _ => D.nonneg c) (Finset.mem_univ x)

omit [DecidableEq S] in
private lemma cinner_sub_left (D : FinProb S) (f f' g : S → ℂ) :
    D.cinner (f - f') g = D.cinner f g - D.cinner f' g := by
  simp only [cinner_def, ← Finset.sum_sub_distrib, Pi.sub_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq S] in
private lemma cinner_sub_right (D : FinProb S) (f g g' : S → ℂ) :
    D.cinner f (g - g') = D.cinner f g - D.cinner f g' := by
  simp only [cinner_def, ← Finset.sum_sub_distrib, Pi.sub_apply, star_sub]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq S] in
/-- Pythagoras -/
private lemma nsq_add_of_orth (D : FinProb S) {a b : S → ℂ} (h : D.cinner a b = 0) :
    nsq D (a + b) = nsq D a + nsq D b := by
  have h' : D.cinner b a = 0 := by rw [cinner_comm, h]; simp
  have : ((nsq D (a + b) : ℝ) : ℂ) = ((nsq D a + nsq D b : ℝ) : ℂ) := by
    push_cast
    rw [← cinner_nsq, ← cinner_nsq, ← cinner_nsq, cinner_add_left, cinner_add_right,
      cinner_add_right, h, h']
    ring
  exact_mod_cast this

omit [DecidableEq S] in
private lemma nsq_sub_of_orth (D : FinProb S) {a b : S → ℂ} (h : D.cinner a b = 0) :
    nsq D (a - b) = nsq D a + nsq D b := by
  have h' : D.cinner b a = 0 := by rw [cinner_comm, h]; simp
  have : ((nsq D (a - b) : ℝ) : ℂ) = ((nsq D a + nsq D b : ℝ) : ℂ) := by
    push_cast
    rw [← cinner_nsq, ← cinner_nsq, ← cinner_nsq, cinner_sub_left, cinner_sub_right,
      cinner_sub_right, h, h']
    ring
  exact_mod_cast this

omit [DecidableEq S] in
private lemma filter_eq_of_rel (hG : Equivalence G) {x y : S} (h : G x y) :
    univ.filter (G x) = univ.filter (G y) := by
  ext c
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun hc => hG.trans (hG.symm h) hc, fun hc => hG.trans h hc⟩

omit [DecidableEq S] in
private lemma nbr_pos (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (x : S) :
    0 < nbr D G x := by
  unfold nbr
  have hx : x ∈ univ.filter (G x) := by simp [hG.refl x]
  calc 0 < D.prob x := hD x
    _ ≤ _ := Finset.single_le_sum (f := D.prob) (fun c _ => D.nonneg c) hx

omit [DecidableEq S] in
private lemma nbr_congr (D : FinProb S) (hG : Equivalence G) {x y : S} (h : G x y) :
    nbr D G x = nbr D G y := by
  unfold nbr
  rw [filter_eq_of_rel hG h]

omit [DecidableEq S] in
private lemma avg_congr (D : FinProb S) (hG : Equivalence G) (g : S → ℂ) {x y : S} (h : G x y) :
    avg D G g x = avg D G g y := by
  unfold avg
  rw [filter_eq_of_rel hG h, nbr_congr D hG h]

omit [DecidableEq S] in
private lemma avg_of_const (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) {u : S → ℂ}
    (hu : ∀ a b, G a b → u a = u b) (x : S) : avg D G u x = u x := by
  have h1 : ∑ y ∈ univ.filter (G x), ((D.prob y : ℝ) : ℂ) * u y =
      ((nbr D G x : ℝ) : ℂ) * u x := by
    rw [nbr, Complex.ofReal_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y hy => by rw [← hu x y (Finset.mem_filter.1 hy).2]
  have hne : ((nbr D G x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nbr_pos D hD hG x).ne'
  unfold avg
  rw [h1]
  field_simp

private lemma noiseApply_eq (D : FinProb S) (ξ : ℝ) (g : S → ℂ) (x : S) :
    graphNoiseApply D G ξ g x = ((1 - ξ : ℝ) : ℂ) * g x + (ξ : ℂ) * avg D G g x := by
  unfold graphNoiseApply graphNoiseKernel avg nbr
  have e1 : ∑ b, (((1 - ξ) * (if x = b then 1 else 0) : ℝ) : ℂ) * g b =
      ((1 - ξ : ℝ) : ℂ) * g x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      have : x ≠ b := fun h => hb h.symm
      simp [this]
    · simp
  have e2 : ∑ b, ((ξ * ((if G x b then D.prob b else 0) /
      ∑ c ∈ univ.filter (G x), D.prob c) : ℝ) : ℂ) * g b =
      (ξ : ℂ) * ((∑ y ∈ univ.filter (G x), ((D.prob y : ℝ) : ℂ) * g y) /
        ((∑ c ∈ univ.filter (G x), D.prob c : ℝ) : ℂ)) := by
    generalize (∑ c ∈ univ.filter (G x), D.prob c : ℝ) = N
    rw [Finset.sum_filter, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : G x b
    · simp only [h, ite_true]; push_cast; ring
    · simp only [h, ite_false]; simp
  simp only [Complex.ofReal_add, add_mul, Finset.sum_add_distrib, e1, e2]

omit [DecidableEq S] in
private lemma avg_eq_sum (D : FinProb S) (g : S → ℂ) (x : S) :
    avg D G g x = (∑ y, if G x y then ((D.prob y : ℝ) : ℂ) * g y else 0) /
      ((nbr D G x : ℝ) : ℂ) := by
  unfold avg; rw [Finset.sum_filter]

omit [DecidableEq S] in
private lemma avg_selfadj (D : FinProb S) (hG : Equivalence G) (g h : S → ℂ) :
    D.cinner (avg D G g) h = D.cinner g (avg D G h) := by
  simp only [cinner_def, avg_eq_sum, star_div₀, star_sum, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases hxy : G x y
  · have hyx := hG.symm hxy
    simp [hxy, hyx, nbr_congr D hG hxy]
    ring
  · have hyx : ¬ G y x := fun h' => hxy (hG.symm h')
    simp [hxy, hyx]

omit [Fintype S] [DecidableRel G] in
private lemma mem_constOnGraph_iff (hG : Equivalence G) (g : S → ℂ) :
    g ∈ constOnGraph G ↔ ∀ a b, G a b → g a = g b := by
  constructor
  · intro h a b hab
    have h' : ∀ a b, (SimpleGraph.fromRel G).Reachable a b → g a = g b := h
    by_cases e : a = b
    · rw [e]
    · exact h' a b (SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj G a b).2 ⟨e, Or.inl hab⟩))
  · intro h
    show ∀ a b, (SimpleGraph.fromRel G).Reachable a b → g a = g b
    intro a b hr
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => rfl
    | tail _ hbc ih =>
      rw [ih]
      rcases ((SimpleGraph.fromRel_adj G _ _).1 hbc).2 with h1 | h1
      · exact h _ _ h1
      · exact (h _ _ h1).symm

private lemma kernel_rev (D : FinProb S) (hG : Equivalence G) (ξ : ℝ) (a b : S) :
    D.prob a * graphNoiseKernel D G ξ a b = D.prob b * graphNoiseKernel D G ξ b a := by
  by_cases hab : a = b
  · subst hab; rfl
  · unfold graphNoiseKernel
    by_cases h : G a b
    · have e := nbr_congr D hG h
      unfold nbr at e
      have h' := hG.symm h
      simp only [hab, Ne.symm hab, h, h', ite_true, ite_false, e]
      ring
    · have h' : ¬ G b a := fun h' => h (hG.symm h')
      simp only [hab, Ne.symm hab, h, h', ite_false]
      ring

private lemma kernel_stoch (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) {ξ : ℝ}
    (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) :
    (∀ a b, 0 ≤ graphNoiseKernel D G ξ a b) ∧ ∀ a, ∑ b, graphNoiseKernel D G ξ a b = 1 := by
  obtain ⟨T, hT⟩ := graphNoiseKernel_isStochastic D G h0 h1 (fun a => nbr_pos D hD hG a)
  exact ⟨fun a b => (hT a b) ▸ T.nonneg a b, fun a => by simp_rw [← hT]; exact T.row_sum a⟩

omit [DecidableEq S] in
private lemma const_avg (D : FinProb S) (hG : Equivalence G) (g : S → ℂ) :
    ∀ a b, G a b → avg D G g a = avg D G g b := fun _ _ h => avg_congr D hG g h

omit [DecidableEq S] in
private lemma orth_avg (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (g v : S → ℂ)
    (hv : ∀ a b, G a b → v a = v b) : D.cinner (g - avg D G g) v = 0 := by
  have hv' : avg D G v = v := funext fun x => avg_of_const D hD hG hv x
  rw [cinner_sub_left, avg_selfadj D hG, hv', sub_self]

omit [DecidableEq S] in
private lemma nsq_decomp (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (g : S → ℂ) :
    nsq D g = nsq D (g - avg D G g) + nsq D (avg D G g) := by
  rw [← nsq_add_of_orth D (orth_avg D hD hG g _ (const_avg D hG g)), sub_add_cancel]

omit [DecidableEq S] in
private lemma cinner_avg (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (g : S → ℂ) :
    D.cinner g (avg D G g) = ((nsq D (avg D G g) : ℝ) : ℂ) := by
  have h := orth_avg D hD hG g _ (const_avg D hG g)
  rw [cinner_sub_left, cinner_nsq] at h
  exact sub_eq_zero.1 h

omit [DecidableEq S] in
private lemma nsq_avg_le (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (g u : S → ℂ)
    (hu : ∀ a b, G a b → u a = u b) :
    nsq D (g - avg D G g) ≤ nsq D (g - u) := by
  have hc : ∀ a b, G a b → (avg D G g - u) a = (avg D G g - u) b := fun a b h => by
    simp only [Pi.sub_apply, avg_congr D hG g h, hu a b h]
  have h := orth_avg D hD hG g _ hc
  have e : g - u = (g - avg D G g) + (avg D G g - u) := by abel
  rw [e, nsq_add_of_orth D h]
  linarith [nsq_nonneg D (avg D G g - u)]

private lemma cinner_noise (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (ξ : ℝ)
    (g : S → ℂ) :
    D.cinner g (graphNoiseApply D G ξ g) =
      (((1 - ξ) * nsq D g + ξ * nsq D (avg D G g) : ℝ) : ℂ) := by
  have e : graphNoiseApply D G ξ g = ((1 - ξ : ℝ) : ℂ) • g + (ξ : ℂ) • avg D G g := by
    funext x; rw [noiseApply_eq]; rfl
  rw [e, cinner_add_right, cinner_smul_right, cinner_smul_right, cinner_nsq, cinner_avg D hD hG]
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

end Helpers

section Mix
variable {S : Type} [Fintype S] [DecidableEq S] {G : S → S → Prop} [DecidableRel G]
  {β ξ : ℝ} {μ ν₁ ν₂ : FinProb S}

private lemma mixJoint_nonneg (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ a b, 0 ≤ graphNoiseKernel ν₁ G ξ a b) (x x' : S) :
    0 ≤ mixJoint β ν₁ ν₂ G ξ x x' := by
  unfold mixJoint
  have h1 : 0 ≤ (if x = x' then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) (ν₂.nonneg x)) h1)
    (mul_nonneg (mul_nonneg hβ0 (ν₁.nonneg x)) (hK x x'))

private lemma mixJoint_rowsum (hK1 : ∀ a, ∑ b, graphNoiseKernel ν₁ G ξ a b = 1) (x : S) :
    ∑ x', mixJoint β ν₁ ν₂ G ξ x x' = (1 - β) * ν₂.prob x + β * ν₁.prob x := by
  unfold mixJoint
  rw [Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, hK1 x, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp

private lemma mixJoint_symm (hG : Equivalence G) (x x' : S) :
    mixJoint β ν₁ ν₂ G ξ x x' = mixJoint β ν₁ ν₂ G ξ x' x := by
  by_cases h : x = x'
  · subst h; rfl
  · have h' : ¬ x' = x := fun e => h e.symm
    unfold mixJoint
    simp only [h, h', ite_false, mul_zero, zero_add]
    linear_combination β * kernel_rev ν₁ hG ξ x x'

private lemma exists_mixChain (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hν₁ : ∀ x, 0 < ν₁.prob x)
    (hG : Equivalence G) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hden : ∀ x, 0 < β * ν₁.prob x + (1 - β) * ν₂.prob x) :
    ∃ T : StochMat S, ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x' := by
  obtain ⟨hK, hK1⟩ := kernel_stoch ν₁ hν₁ hG (G := G) hξ0 hξ1
  refine ⟨⟨mixChainKernel β ν₁ ν₂ G ξ, fun x x' => ?_, fun x => ?_⟩, fun x x' => rfl⟩
  · exact div_nonneg (mixJoint_nonneg hβ0 hβ1 hK x x') (hden x).le
  · unfold mixChainKernel
    rw [← Finset.sum_div, mixJoint_rowsum hK1, div_eq_one_iff_eq (hden x).ne']
    ring

private lemma mu_mul_T (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (T : StochMat S)
    (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') (x x' : S) :
    μ.prob x * T.prob x x' = mixJoint β ν₁ ν₂ G ξ x x' := by
  rw [hT, mixChainKernel, ← hmix x]
  exact mul_div_cancel₀ _ (hμ x).ne'

private lemma mixChain_rev (hG : Equivalence G)
    (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (T : StochMat S)
    (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') :
    T.IsReversible μ ∧ T.IsStationary μ := by
  have hrev : T.IsReversible μ := fun a b => by
    rw [mu_mul_T hmix hμ T hT, mu_mul_T hmix hμ T hT, mixJoint_symm hG]
  refine ⟨hrev, fun b => ?_⟩
  have : ∀ a, μ.prob a * T.prob a b = μ.prob b * T.prob b a := fun a => hrev a b
  simp_rw [this, ← Finset.mul_sum, T.row_sum, mul_one]

private lemma mixChain_apply (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (T : StochMat S)
    (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') (g : S → ℂ) (x : S) :
    (μ.prob x : ℂ) * T.apply g x =
      (μ.prob x : ℂ) * g x - (β : ℂ) * ξ * ν₁.prob x * (g x - avg ν₁ G g x) := by
  have h1 : (μ.prob x : ℂ) * T.apply g x =
      ∑ b, ((mixJoint β ν₁ ν₂ G ξ x b : ℝ) : ℂ) * g b := by
    unfold StochMat.apply
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mu_mul_T hmix hμ T hT x b]
    push_cast; ring
  have h2 : ∑ b, ((mixJoint β ν₁ ν₂ G ξ x b : ℝ) : ℂ) * g b =
      (((1 - β) * ν₂.prob x : ℝ) : ℂ) * g x +
        ((β * ν₁.prob x : ℝ) : ℂ) * graphNoiseApply ν₁ G ξ g x := by
    unfold mixJoint graphNoiseApply
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single x]
      · simp
      · intro b _ hb
        have : x ≠ b := fun h => hb h.symm
        simp [this]
      · simp
    · exact Finset.sum_congr rfl fun b _ => by push_cast; ring
  rw [h1, h2, noiseApply_eq, hmix x]
  push_cast
  ring

private lemma mixChain_cinner (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (hν₁ : ∀ x, 0 < ν₁.prob x) (hG : Equivalence G)
    (T : StochMat S)
    (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') (g : S → ℂ) :
    μ.cinner g (T.apply g) =
      ((nsq μ g - β * ξ * nsq ν₁ (g - avg ν₁ G g) : ℝ) : ℂ) := by
  have e1 : μ.cinner g (T.apply g) = μ.cinner g g - (β : ℂ) * ξ * ν₁.cinner g (g - avg ν₁ G g) := by
    simp only [cinner_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := mixChain_apply hmix hμ T hT g x
    have h' : (μ.prob x : ℂ) * (g x * star (T.apply g x)) =
        g x * star ((μ.prob x : ℂ) * T.apply g x) := by
      simp only [Complex.star_def, map_mul, Complex.conj_ofReal]; ring
    rw [h', h]
    simp only [Complex.star_def, map_sub, map_mul, Complex.conj_ofReal, Pi.sub_apply]
    ring
  have e2 : ν₁.cinner g (g - avg ν₁ G g) = ((nsq ν₁ (g - avg ν₁ G g) : ℝ) : ℂ) := by
    rw [cinner_sub_right, cinner_nsq, cinner_avg ν₁ hν₁ hG, ← Complex.ofReal_sub]
    congr 1
    linarith [nsq_decomp ν₁ hν₁ hG g]
  rw [e1, e2, cinner_nsq]
  push_cast; ring

omit [DecidableEq S] in
private lemma nsq_mix (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x) (g : S → ℂ) :
    nsq μ g = β * nsq ν₁ g + (1 - β) * nsq ν₂ g := by
  unfold nsq FinProb.expect
  simp only [hmix, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

omit [DecidableEq S] in
private lemma nsq_cmp {α₀ : ℝ} (hα : 0 ≤ α₀) (hν : ∀ x, α₀ ≤ ν₁.prob x) (r : S → ℂ) :
    α₀ * nsq μ r ≤ nsq ν₁ r := by
  unfold nsq FinProb.expect
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : α₀ * μ.prob x ≤ ν₁.prob x := by
    nlinarith [prob_le_one μ x, hν x]
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖r x‖)]

/-- gap of `‖g‖²_μ` against the `ν₁`-Dirichlet form on `V^⊥` -/
private lemma gap_nsq {α₀ : ℝ} (hα : 0 < α₀) (hν₁ : ∀ x, α₀ ≤ ν₁.prob x) (hG : Equivalence G)
    (hν₁' : ∀ x, 0 < ν₁.prob x) {g : S → ℂ}
    (hg : g ∈ orthSet μ (constOnGraph G : Set (S → ℂ))) :
    α₀ * nsq μ g ≤ nsq ν₁ (g - avg ν₁ G g) := by
  have hu : ∀ a b, G a b → avg ν₁ G g a = avg ν₁ G g b := const_avg ν₁ hG g
  have hum : avg ν₁ G g ∈ constOnGraph G := (mem_constOnGraph_iff hG _).2 hu
  have h0 : μ.cinner g (avg ν₁ G g) = 0 := hg _ hum
  have h1 := nsq_sub_of_orth μ h0
  have h2 : nsq μ g ≤ nsq μ (g - avg ν₁ G g) := by
    rw [h1]; linarith [nsq_nonneg μ (avg ν₁ G g)]
  have h3 := nsq_cmp (μ := μ) hα.le hν₁ (g - avg ν₁ G g)
  nlinarith

private lemma mixChain_eig (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (hν₁' : ∀ x, 0 < ν₁.prob x) (hG : Equivalence G)
    {α₀ : ℝ} (hα : 0 < α₀) (hν₁ : ∀ x, α₀ ≤ ν₁.prob x)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (T : StochMat S) (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x')
    {g : S → ℂ} (hg : g ∈ orthSet μ (constOnGraph G : Set (S → ℂ))) (hg0 : g ≠ 0) (l : ℂ)
    (hl : T.apply g = l • g) :
    ∃ r : ℝ, l = r ∧ 0 ≤ r ∧ r ≤ 1 - α₀ * β * ξ := by
  have hn : 0 < nsq μ g := nsq_pos μ hμ hg0
  have h := mixChain_cinner hmix hμ hν₁' hG T hT g
  rw [hl, cinner_smul_right, cinner_nsq] at h
  set n := nsq μ g with hn_def
  set R := nsq ν₁ (g - avg ν₁ G g) with hR
  have hR0 : 0 ≤ R := nsq_nonneg _ _
  have hgap : α₀ * n ≤ R := gap_nsq hα hν₁ hG hν₁' hg
  have hRle : R ≤ nsq ν₁ g := by
    have := nsq_decomp ν₁ hν₁' hG g
    linarith [nsq_nonneg ν₁ (avg ν₁ G g)]
  have hnmix := nsq_mix hmix g
  have hν2 := nsq_nonneg ν₂ g
  have hbR : β * R ≤ n := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - β) hν2]
  have hξR : β * ξ * R ≤ n := by nlinarith [mul_nonneg hβ0.le hR0]
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hstar : star l = (((n - β * ξ * R) / n : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff hne]
    exact h
  refine ⟨(n - β * ξ * R) / n, ?_, ?_, ?_⟩
  · have := congrArg star hstar
    rw [star_star] at this
    rw [this]; simp [Complex.star_def]
  · exact div_nonneg (by linarith) hn.le
  · rw [div_le_iff₀ hn]
    nlinarith [mul_pos hβ0 hξ0, mul_le_mul_of_nonneg_left hgap (mul_pos hβ0 hξ0).le]

private lemma mixChain_fix (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (hν₁' : ∀ x, 0 < ν₁.prob x) (hG : Equivalence G)
    (T : StochMat S) (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x')
    {g : S → ℂ} (hg : g ∈ constOnGraph G) : T.apply g = g := by
  have hc := (mem_constOnGraph_iff hG g).1 hg
  funext x
  have h := mixChain_apply hmix hμ T hT g x
  rw [avg_of_const ν₁ hν₁' hG hc x, sub_self, mul_zero, sub_zero] at h
  exact mul_left_cancel₀ (by exact_mod_cast (hμ x).ne') h

private lemma noise_fix (D : FinProb S) (hD : ∀ x, 0 < D.prob x) (hG : Equivalence G) (ξ : ℝ)
    {g : S → ℂ} (hg : g ∈ constOnGraph G) : graphNoiseApply D G ξ g = g := by
  have hc := (mem_constOnGraph_iff hG g).1 hg
  funext x
  rw [noiseApply_eq, avg_of_const D hD hG hc x]
  push_cast; ring

private lemma avg_orth_zero (D : FinProb S) (hG : Equivalence G)
    {g : S → ℂ} (hg : g ∈ orthSet D (constOnGraph G : Set (S → ℂ))) : avg D G g = 0 := by
  funext x
  have hv : (fun y => if G x y then (1 : ℂ) else 0) ∈ constOnGraph G := by
    rw [mem_constOnGraph_iff hG]
    intro a b hab
    have : G x a ↔ G x b := ⟨fun h => hG.trans h hab, fun h => hG.trans h (hG.symm hab)⟩
    simp only [this]
  have h := hg _ hv
  have h2 : ∑ y ∈ univ.filter (G x), ((D.prob y : ℝ) : ℂ) * g y = 0 := by
    rw [← h, cinner_def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : G x y <;> simp [hy]
  simp [avg, h2]

private lemma noise_orth (D : FinProb S) (hG : Equivalence G) (ξ : ℝ)
    {g : S → ℂ} (hg : g ∈ orthSet D (constOnGraph G : Set (S → ℂ))) :
    graphNoiseApply D G ξ g = ((1 - ξ : ℝ) : ℂ) • g := by
  funext x
  rw [noiseApply_eq, avg_orth_zero D hG hg]
  simp

private lemma psd_T (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (hν₁' : ∀ x, 0 < ν₁.prob x) (hG : Equivalence G)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (T : StochMat S) (hT : ∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') (g : S → ℂ) :
    0 ≤ nsq μ g - β * ξ * nsq ν₁ (g - avg ν₁ G g) := by
  have hRle : nsq ν₁ (g - avg ν₁ G g) ≤ nsq ν₁ g := by
    have := nsq_decomp ν₁ hν₁' hG g
    linarith [nsq_nonneg ν₁ (avg ν₁ G g)]
  have hnmix := nsq_mix hmix g
  have hν2 := nsq_nonneg ν₂ g
  have hR0 := nsq_nonneg ν₁ (g - avg ν₁ G g)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - β) hν2, mul_nonneg hβ0 hR0,
    mul_nonneg hβ0 (by linarith : (0:ℝ) ≤ 1 - ξ), mul_nonneg (mul_nonneg hβ0 (by linarith : (0:ℝ) ≤ 1 - ξ)) hR0,
    mul_nonneg hβ0 (by linarith : (0:ℝ) ≤ nsq ν₁ g - nsq ν₁ (g - avg ν₁ G g))]

omit [DecidableEq S] in
private lemma quad_cmp {α₀ c : ℝ} (hα : 0 < α₀) (hν₁ : ∀ x, α₀ ≤ ν₁.prob x)
    (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (hμ : ∀ x, 0 < μ.prob x) (hν₁' : ∀ x, 0 < ν₁.prob x) (hG : Equivalence G)
    (hβ0 : 0 < β) (hξ0 : 0 < ξ) (hc0 : 0 ≤ c) (hcα : c ≤ α₀) (g : S → ℂ) :
    nsq μ g - β * ξ * nsq ν₁ (g - avg ν₁ G g) ≤
      (1 - c * ξ * β) * nsq μ g + c * ξ * β * nsq μ (avg μ G g) := by
  set R := nsq ν₁ (g - avg ν₁ G g) with hR
  have hdec := nsq_decomp μ hμ hG g
  set B := nsq μ (g - avg μ G g) with hB
  have hB0 : 0 ≤ B := nsq_nonneg _ _
  have h1 : B ≤ nsq μ (g - avg ν₁ G g) :=
    nsq_avg_le μ hμ hG g _ (const_avg ν₁ hG g)
  have h2 := nsq_cmp (μ := μ) hα.le hν₁ (g - avg ν₁ G g)
  have h3 : α₀ * B ≤ R := by nlinarith
  have hξβ : 0 ≤ ξ * β := (mul_pos hξ0 hβ0).le
  have h4 : c * B ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hcα hB0]
  rw [hdec]
  nlinarith [mul_le_mul_of_nonneg_left h4 hξβ]

end Mix

section Rep
variable {S : Type} [Fintype S] [DecidableEq S] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the law of `(x, x')` with `x ∼ P` and `x' ∼ K(x, ·)` -/
private def pairLaw (P : FinProb S) (K : S → S → ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (h1 : ∀ a, ∑ b, K a b = 1) : FinProb (S × S) where
  prob w := P.prob w.1 * K w.1 w.2
  nonneg w := mul_nonneg (P.nonneg _) (hK _ _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, h1, P.sum_eq_one]

omit [Fintype S] in
private lemma diagK_nonneg : ∀ a b : S, 0 ≤ (if a = b then (1 : ℝ) else 0) := fun a b => by
  split_ifs <;> norm_num

private lemma diagK_sum : ∀ a : S, ∑ b : S, (if a = b then (1 : ℝ) else 0) = 1 := fun a => by simp

private lemma diag_pi_cexpect (ν : FinProb S) (H : (ι → S × S) → ℂ) :
    ((pairLaw ν (fun a b => if a = b then 1 else 0) diagK_nonneg diagK_sum).pi ι).cexpect H =
      (ν.pi ι).cexpect fun z => H (fun i => (z i, z i)) := by
  unfold FinProb.cexpect
  set F : (ι → S × S) → ℂ := fun w =>
    (((pairLaw ν (fun a b => if a = b then 1 else 0) diagK_nonneg diagK_sum).pi ι).prob w : ℂ) *
      H w with hF
  let d : (ι → S) → (ι → S × S) := fun z i => (z i, z i)
  have hd : Function.Injective d := by
    intro z z' h
    funext i
    have := congrFun h i
    simpa [d] using congrArg Prod.fst this
  have h0 : ∀ w ∈ (Finset.univ : Finset (ι → S × S)), w ∉ Finset.univ.image d → F w = 0 := by
    intro w _ hw
    have : ∃ i, (w i).1 ≠ (w i).2 := by
      by_contra hcon
      push Not at hcon
      apply hw
      refine Finset.mem_image.2 ⟨fun i => (w i).1, Finset.mem_univ _, ?_⟩
      funext i
      exact Prod.ext rfl (hcon i)
    obtain ⟨i, hi⟩ := this
    simp only [hF]
    have : (((pairLaw ν (fun a b => if a = b then 1 else 0) diagK_nonneg diagK_sum).pi ι).prob
        w) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [pairLaw, hi]
    rw [this]; simp
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image d)) h0,
    Finset.sum_image (fun a _ b _ h => hd h)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [hF, d]
  congr 2
  simp [FinProb.pi, pairLaw]

omit [DecidableEq S] in
private lemma pair_sum (W : S → S → ℝ) (H : (ι → S) → (ι → S) → ℂ) :
    ∑ w : ι → S × S, ((∏ i, W (w i).1 (w i).2 : ℝ) : ℂ) * H (fun i => (w i).1) (fun i => (w i).2) =
      ∑ x, ∑ x', ((∏ i, W (x i) (x' i) : ℝ) : ℂ) * H x x' := by
  rw [← Fintype.sum_prod_type' (f := fun x x' => ((∏ i, W (x i) (x' i) : ℝ) : ℂ) * H x x')]
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => S) (fun _ => S)) _ _ (fun w => rfl)

omit [DecidableEq S] in
private lemma cinner_kernel (P : FinProb S) (K : S → S → ℝ) (g : (ι → S) → ℂ) :
    (P.pi ι).cinner g (fun x => ∑ y, ((∏ i, K (x i) (y i) : ℝ) : ℂ) * g y) =
      ∑ y, ∑ y', ((∏ i, (P.prob (y i) * K (y i) (y' i)) : ℝ) : ℂ) * (g y * star (g y')) := by
  simp only [cinner_def, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [FinProb.pi, star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

omit [Fintype S] [DecidableEq S] in
private lemma glue_fst (I : Finset ι) (y' : ↥I → S × S) (z : ↥Iᶜ → S) :
    (fun i => (glueFree I y' (fun j => (z j, z j)) i).1) =
      glueFree I (fun j => (y' j).1) z := by
  funext i; by_cases h : i ∈ I <;> simp [glueFree, h]

omit [Fintype S] [DecidableEq S] in
private lemma glue_snd (I : Finset ι) (y' : ↥I → S × S) (z : ↥Iᶜ → S) :
    (fun i => (glueFree I y' (fun j => (z j, z j)) i).2) =
      glueFree I (fun j => (y' j).2) z := by
  funext i; by_cases h : i ∈ I <;> simp [glueFree, h]

private lemma claimA (P₁ P₂ : FinProb S) (K : S → S → ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (h1 : ∀ a, ∑ b, K a b = 1) (f : (ι → S) → ℂ) (I : Finset ι) :
    (P₂.pi ↥Iᶜ).cexpect (fun z => (P₁.pi ↥I).cinner (restrictFree I z f)
        (fun x => ∑ y, ((∏ i, K (x i) (y i) : ℝ) : ℂ) * restrictFree I z f y)) =
      ((pairLaw P₂ (fun a b => if a = b then 1 else 0) diagK_nonneg diagK_sum).pi ↥Iᶜ).cexpect
        fun z' => ((pairLaw P₁ K hK h1).pi ↥I).cexpect fun y' =>
          f (fun i => (glueFree I y' z' i).1) * star (f (fun i => (glueFree I y' z' i).2)) := by
  rw [diag_pi_cexpect]
  congr 1
  funext z
  rw [cinner_kernel P₁ K (restrictFree I z f)]
  unfold FinProb.cexpect
  have h := pair_sum (ι := ↥I) (fun a a' => P₁.prob a * K a a')
    (fun y y'' => restrictFree I z f y * star (restrictFree I z f y''))
  rw [← h]
  refine Finset.sum_congr rfl fun y' _ => ?_
  beta_reduce
  rw [glue_fst, glue_snd]
  rfl

omit [DecidableEq S] in
private lemma apply_eq_mulVec (T : StochMat S) (g : S → ℂ) : T.cmat.mulVec g = T.apply g := by
  funext x
  simp [Matrix.mulVec, dotProduct, StochMat.cmat, StochMat.apply]

private lemma noise_eq_mulVec (T : StochMat S) {G : S → S → Prop} [DecidableRel G] (D : FinProb S)
    (ξ : ℝ) (hT : ∀ a b, T.prob a b = graphNoiseKernel D G ξ a b) (g : S → ℂ) :
    T.apply g = graphNoiseApply D G ξ g := by
  funext x
  simp [StochMat.apply, graphNoiseApply, hT]

private lemma kernelPow_eq (T : StochMat S) {G : S → S → Prop} [DecidableRel G] (D : FinProb S)
    (ξ : ℝ) (hT : ∀ a b, T.prob a b = graphNoiseKernel D G ξ a b) (f : (ι → S) → ℂ) :
    (kernelPow T.cmat ι).mulVec f = graphNoiseOp D G ξ f := by
  funext x
  simp only [Matrix.mulVec, dotProduct, kernelPow, StochMat.cmat, Matrix.of_apply, graphNoiseOp, hT]
  push_cast
  rfl

omit [DecidableEq S] in
private lemma eigen_unique {g : S → ℂ} (hg0 : g ≠ 0) {r : ℝ} {l : ℂ}
    (h : ((r : ℝ) : ℂ) • g = l • g) : l = r := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra h'; push Not at h'; exact hg0 (funext h')
  have := congrFun h a
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact (mul_right_cancel₀ ha this).symm

end Rep

section OpComparison

open scoped ComplexOrder in
/-- paper IV `lem:op-comparison-lemma`, step `mixture-chain-representation`. Readings:
`G` is an equivalence relation (partition with loops); every atom of `μ, ν₁, ν₂` has mass
at least `α₀`; `ξ ∈ (0,1]`; `β ∈ (0,1]`; `m` bounds `|Σ|`. -/
theorem mixture_chain_representation {α₀ β : ℝ} (hα : 0 < α₀) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (m : ℕ) (S : Type) [Fintype S] [DecidableEq S] (hS : Fintype.card S ≤ m)
    (μ ν₁ ν₂ : FinProb S) (hμ : ∀ x, α₀ ≤ μ.prob x) (hν₁ : ∀ x, α₀ ≤ ν₁.prob x)
    (hν₂ : ∀ x, α₀ ≤ ν₂.prob x)
    (hmix : ∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x)
    (G : S → S → Prop) [DecidableRel G] (hG : Equivalence G)
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ T : StochMat S, (∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') ∧
      T.IsStationary μ ∧ T.IsReversible μ ∧
      (∀ g : S → ℂ, 0 ≤ μ.cinner g (T.apply g)) ∧
      (∀ g : S → ℂ, 0 ≤ μ.cinner g (graphNoiseApply μ G ξ g)) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → S) → ℂ),
        mixtureRestrictionExpect β hβ0.le hβ1 ν₂ f
            (fun I g => (ν₁.pi ↥I).cinner g (graphNoiseOp ν₁ G ξ g)) =
          (μ.pi ι).cinner f ((T.pi ι).apply f) := by
  have _ := hS
  have _ := hν₂
  have hμ' : ∀ x, 0 < μ.prob x := fun x => lt_of_lt_of_le hα (hμ x)
  have hν₁' : ∀ x, 0 < ν₁.prob x := fun x => lt_of_lt_of_le hα (hν₁ x)
  have hden : ∀ x, 0 < β * ν₁.prob x + (1 - β) * ν₂.prob x := fun x => by
    rw [← hmix x]; exact hμ' x
  obtain ⟨T, hT⟩ := exists_mixChain (ν₂ := ν₂) hβ0.le hβ1 hν₁' hG hξ0.le hξ1 hden
  obtain ⟨hrev, hstat⟩ := mixChain_rev hG hmix hμ' T hT
  refine ⟨T, hT, hstat, hrev, ?_, ?_, ?_⟩
  · intro g
    rw [mixChain_cinner hmix hμ' hν₁' hG T hT g, Complex.zero_le_real]
    exact psd_T hmix hμ' hν₁' hG hβ0.le hβ1 hξ0.le hξ1 T hT g
  · intro g
    rw [cinner_noise μ hμ' hG ξ g, Complex.zero_le_real]
    exact add_nonneg (mul_nonneg (by linarith) (nsq_nonneg _ _))
      (mul_nonneg hξ0.le (nsq_nonneg _ _))
  · intro ι _ _ f
    obtain ⟨hK, hK1⟩ := kernel_stoch ν₁ hν₁' hG (G := G) hξ0.le hξ1
    let D₁ := pairLaw ν₁ (graphNoiseKernel ν₁ G ξ) hK hK1
    let D₂ := pairLaw ν₂ (fun a b => if a = b then (1 : ℝ) else 0) diagK_nonneg diagK_sum
    let M := pairLaw μ T.prob T.nonneg T.row_sum
    have hM : ∀ w, M.prob w = β * D₁.prob w + (1 - β) * D₂.prob w := by
      intro w
      show μ.prob w.1 * T.prob w.1 w.2 = _
      rw [mu_mul_T hmix hμ' T hT]
      show _ = β * (ν₁.prob w.1 * graphNoiseKernel ν₁ G ξ w.1 w.2) +
        (1 - β) * (ν₂.prob w.1 * if w.1 = w.2 then 1 else 0)
      unfold mixJoint; ring
    have key := restrict_key hβ0.le hβ1 D₁ D₂ M hM
      (fun w => f (fun i => (w i).1) * star (f (fun i => (w i).2)))
    have e1 : mixtureRestrictionExpect β hβ0.le hβ1 ν₂ f
        (fun I g => (ν₁.pi ↥I).cinner g (graphNoiseOp ν₁ G ξ g)) =
        subsetExpect β hβ0.le hβ1 (fun I => (D₂.pi ↥Iᶜ).cexpect fun z' =>
          (D₁.pi ↥I).cexpect fun y' =>
            f (fun i => (glueFree I y' z' i).1) * star (f (fun i => (glueFree I y' z' i).2))) := by
      unfold mixtureRestrictionExpect
      congr 1
      funext I
      exact claimA ν₁ ν₂ (graphNoiseKernel ν₁ G ξ) hK hK1 f I
    rw [e1, key]
    unfold FinProb.cexpect
    have h := pair_sum (ι := ι) (fun a a' => μ.prob a * T.prob a a')
      (fun x x' => f x * star (f x'))
    exact h.trans (cinner_kernel μ T.prob f).symm

open scoped ComplexOrder in
/-- paper IV `lem:op-comparison-lemma`, step `univariate-eigenvalue-bounds` (same readings; `s` depends
on `(m, α₀)` only, `c` is any constant with `c C < s`, and `c β ≤ 1` keeps
`T_{1-cξβ,μ}` a chain). -/
theorem univariate_eigenvalue_bounds {α₀ : ℝ} (hα : 0 < α₀) (m : ℕ) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∀ c : ℝ, 0 < c → c * C < s → c * β ≤ 1 →
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ ν₁ ν₂ : FinProb S, (∀ x, α₀ ≤ μ.prob x) → (∀ x, α₀ ≤ ν₁.prob x) →
        (∀ x, α₀ ≤ ν₂.prob x) →
        (∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x) →
      ∀ (G : S → S → Prop) [DecidableRel G], Equivalence G →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 →
        ∃ T : StochMat S, (∀ x x', T.prob x x' = mixChainKernel β ν₁ ν₂ G ξ x x') ∧
          (∀ g ∈ constOnGraph G, T.apply g = g ∧ graphNoiseApply μ G ξ g = g) ∧
          (∀ g ∈ orthSet μ (constOnGraph G : Set (S → ℂ)),
            T.apply g ∈ orthSet μ (constOnGraph G : Set (S → ℂ)) ∧
            graphNoiseApply μ G (c * ξ * β) g ∈ orthSet μ (constOnGraph G : Set (S → ℂ))) ∧
          (∀ g ∈ orthSet μ (constOnGraph G : Set (S → ℂ)), g ≠ 0 → ∀ l : ℂ,
            T.apply g = l • g → ∃ r : ℝ, l = r ∧ r ≤ 1 - s * β * ξ) ∧
          (∀ g ∈ orthSet μ (constOnGraph G : Set (S → ℂ)), g ≠ 0 → ∀ l : ℂ,
            graphNoiseApply μ G (c * ξ * β) g = l • g →
              ∃ r : ℝ, l = r ∧ 1 - c * C * ξ * β ≤ r) ∧
          1 - s * β * ξ < 1 - c * C * ξ * β ∧
          ∀ g : S → ℂ, μ.cinner g (T.apply g) ≤ μ.cinner g (graphNoiseApply μ G (c * ξ * β) g) := by
  refine ⟨α₀, 1, hα, one_pos, ?_⟩
  intro β hβ0 hβ1 c hc hcC hcβ S _ _ hcard μ ν₁ ν₂ hμ hν₁ hν₂ hmix G _ hG ξ hξ0 hξ1
  have _ := hcard
  have _ := hν₂
  have hμ' : ∀ x, 0 < μ.prob x := fun x => lt_of_lt_of_le hα (hμ x)
  have hν₁' : ∀ x, 0 < ν₁.prob x := fun x => lt_of_lt_of_le hα (hν₁ x)
  have hden : ∀ x, 0 < β * ν₁.prob x + (1 - β) * ν₂.prob x := fun x => by
    rw [← hmix x]; exact hμ' x
  obtain ⟨T, hT⟩ := exists_mixChain (ν₂ := ν₂) hβ0.le hβ1 hν₁' hG hξ0.le hξ1 hden
  obtain ⟨hrev, -⟩ := mixChain_rev hG hmix hμ' T hT
  have hcα : c < α₀ := by linarith
  have hVT : ∀ v ∈ constOnGraph G, T.cmat.mulVec v = v := fun v hv => by
    rw [apply_eq_mulVec]; exact mixChain_fix hmix hμ' hν₁' hG T hT hv
  refine ⟨T, hT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨mixChain_fix hmix hμ' hν₁' hG T hT hg, noise_fix μ hμ' hG _ hg⟩
  · intro g hg
    refine ⟨?_, ?_⟩
    · rw [← apply_eq_mulVec]
      exact orthSet_mulVec T μ hrev hVT g hg
    · rw [noise_orth μ hG _ hg]
      intro v hv
      rw [cinner_smul_left, hg v hv, mul_zero]
  · intro g hg hg0 l hl
    obtain ⟨r, hr, -, hr'⟩ := mixChain_eig hmix hμ' hν₁' hG hα hν₁ hβ0 hβ1 hξ0 hξ1 T hT hg hg0 l hl
    exact ⟨r, hr, hr'⟩
  · intro g hg hg0 l hl
    rw [noise_orth μ hG _ hg] at hl
    exact ⟨1 - c * ξ * β, eigen_unique hg0 hl, by linarith⟩
  · have : 0 < β * ξ := mul_pos hβ0 hξ0
    nlinarith
  · intro g
    rw [mixChain_cinner hmix hμ' hν₁' hG T hT g, cinner_noise μ hμ' hG _ g, Complex.real_le_real]
    exact quad_cmp hα hν₁ hmix hμ' hν₁' hG hβ0 hξ0 hc.le hcα.le g

open scoped ComplexOrder in
/-- paper IV `lem:op-comparison-lemma`, `β`-uniform form. The printed order `∀ α β ∃ c` lets `c` depend on
`β`, but the consumers paper IV `lem:merge` and `lem:merge2` (step `restriction-events`)
(`β = s → 0`) and `claim:rr-nestab` use a constant independent of `β`, which the
proof (paper IV l. 1316-1325, `c C < s(m, α)`) gives. This implies `op_comparison_lemma`. -/
theorem op_comparison_lemma_uniform {α₀ : ℝ} (hα : 0 < α₀) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, ∀ (hβ0 : 0 < β) (hβ1 : β ≤ 1),
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ ν₁ ν₂ : FinProb S, (∀ x, α₀ ≤ μ.prob x) → (∀ x, α₀ ≤ ν₁.prob x) →
        (∀ x, α₀ ≤ ν₂.prob x) →
        (∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x) →
      ∀ (G : S → S → Prop) [DecidableRel G], Equivalence G →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → S) → ℂ),
        mixtureRestrictionExpect β hβ0.le hβ1 ν₂ f
            (fun I g => (ν₁.pi ↥I).cinner g (graphNoiseOp ν₁ G ξ g)) ≤
          (μ.pi ι).cinner f (graphNoiseOp μ G (c * β * ξ) f) := by
  refine ⟨min 1 (α₀ / 2), lt_min one_pos (by positivity), ?_⟩
  intro β hβ0 hβ1 S _ _ hcard μ ν₁ ν₂ hμ hν₁ hν₂ hmix G _ hG ξ hξ0 hξ1 ι _ _ f
  have hc0 : 0 < min 1 (α₀ / 2) := lt_min one_pos (by positivity)
  have hc1 : min 1 (α₀ / 2) ≤ 1 := min_le_left _ _
  have hcα : min 1 (α₀ / 2) ≤ α₀ := le_trans (min_le_right _ _) (by linarith)
  generalize min 1 (α₀ / 2) = c at hc0 hc1 hcα
  have hμ' : ∀ x, 0 < μ.prob x := fun x => lt_of_lt_of_le hα (hμ x)
  have hν₁' : ∀ x, 0 < ν₁.prob x := fun x => lt_of_lt_of_le hα (hν₁ x)
  obtain ⟨T, hT, -, hrev, -, -, hid⟩ := mixture_chain_representation hα hβ0 hβ1 m S hcard μ ν₁ ν₂
    hμ hν₁ hν₂ hmix G hG hξ0 hξ1
  rw [hid ι f]
  have hξ'0 : 0 ≤ c * β * ξ := by positivity
  have hξ'1 : c * β * ξ ≤ 1 := by
    have : c * β ≤ 1 := by nlinarith
    nlinarith
  obtain ⟨T', hT'⟩ := graphNoiseKernel_isStochastic μ G hξ'0 hξ'1 (fun a => nbr_pos μ hμ' hG a)
  have hrev' : T'.IsReversible μ := fun a b => by
    rw [hT', hT']; exact kernel_rev μ hG _ a b
  have hVT : ∀ v ∈ constOnGraph G, T.cmat.mulVec v = v := fun v hv => by
    rw [apply_eq_mulVec]
    refine mixChain_fix hmix hμ' hν₁' hG T hT hv
  have hVT' : ∀ v ∈ constOnGraph G, T'.cmat.mulVec v = v := fun v hv => by
    rw [apply_eq_mulVec, noise_eq_mulVec T' μ _ hT']
    exact noise_fix μ hμ' hG _ hv
  set b : ℝ := max (1 - α₀ * β * ξ) 0 with hb
  have hb0 : 0 ≤ b := le_max_right _ _
  have hαβξ : 0 ≤ α₀ * β * ξ := by positivity
  have hb1 : b ≤ 1 := max_le (by linarith) zero_le_one
  have hbT := tensor_block_bound μ hμ' (constOnGraph G) T.cmat (cmat_selfadj T μ hrev) hVT
    (orthSet_mulVec T μ hrev hVT) (a := 0) (b := b) le_rfl hb0 hb1
    (fun g hg hg0 l hl => by
      rw [apply_eq_mulVec] at hl
      obtain ⟨r, hr, h0, hr'⟩ := mixChain_eig hmix hμ' hν₁' hG hα hν₁ hβ0 hβ1 hξ0 hξ1 T hT hg hg0
        l hl
      exact ⟨r, hr, h0, le_trans hr' (le_max_left _ _)⟩) ι
  have hbT' := tensor_block_bound μ hμ' (constOnGraph G) T'.cmat (cmat_selfadj T' μ hrev') hVT'
    (fun g hg v hv => by
      rw [apply_eq_mulVec, noise_eq_mulVec T' μ _ hT', noise_orth μ hG _ hg, cinner_smul_left,
        hg v hv, mul_zero])
    (a := 1 - c * β * ξ) (b := 1 - c * β * ξ) (by
      have : c * β ≤ 1 := by nlinarith
      nlinarith [mul_nonneg hβ0.le hξ0.le]) le_rfl (by linarith)
    (fun g hg hg0 l hl => by
      rw [apply_eq_mulVec, noise_eq_mulVec T' μ _ hT', noise_orth μ hG _ hg] at hl
      exact ⟨1 - c * β * ξ, eigen_unique hg0 hl, le_rfl, le_rfl⟩) ι
  obtain ⟨h, hh, hfh⟩ := hbT.2.1 f
  have hu := (hbT.2.2.2 f h hh hfh).2.1
  have hl := (hbT'.2.2.2 f h hh hfh).1
  rw [← StochMat.apply_pi_eq_mulVec] at hu
  rw [kernelPow_eq T' μ _ hT'] at hl
  refine le_trans hu (le_trans ?_ hl)
  rw [Complex.real_le_real]
  refine Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left ?_ (cl2sq_nonneg μ _)
  refine pow_le_pow_left₀ hb0 ?_ _
  refine max_le ?_ (by nlinarith [mul_nonneg hβ0.le hξ0.le])
  nlinarith [mul_nonneg hβ0.le hξ0.le]

open scoped ComplexOrder in
/-- paper IV `lem:op-comparison-lemma` (Lemma 2.8). Readings: atoms of `μ, ν₁, ν₂` at least `α₀`;
`G` an equivalence relation (partition with loops); `m` bounds `|Σ|` and `c` depends on `(α₀, β, m)`;
`ξ ∈ (0,1]`, `β ∈ (0,1]` (as in the source). -/
theorem op_comparison_lemma {α₀ β : ℝ} (hα : 0 < α₀) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ ν₁ ν₂ : FinProb S, (∀ x, α₀ ≤ μ.prob x) → (∀ x, α₀ ≤ ν₁.prob x) →
        (∀ x, α₀ ≤ ν₂.prob x) →
        (∀ x, μ.prob x = β * ν₁.prob x + (1 - β) * ν₂.prob x) →
      ∀ (G : S → S → Prop) [DecidableRel G], Equivalence G →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → S) → ℂ),
        mixtureRestrictionExpect β hβ0.le hβ1 ν₂ f
            (fun I g => (ν₁.pi ↥I).cinner g (graphNoiseOp ν₁ G ξ g)) ≤
          (μ.pi ι).cinner f (graphNoiseOp μ G (c * β * ξ) f) := by
  obtain ⟨c, hc, h⟩ := op_comparison_lemma_uniform hα m
  exact ⟨c, hc, fun S _ _ hcard μ ν₁ ν₂ hμ hν₁ hν₂ hmix G _ hG ξ hξ0 hξ1 ι _ _ f =>
    h β hβ0 hβ1 S hcard μ ν₁ ν₂ hμ hν₁ hν₂ hmix G hG ξ hξ0 hξ1 ι f⟩

end OpComparison

end TrackB
end RestrictedPolynomials
end
