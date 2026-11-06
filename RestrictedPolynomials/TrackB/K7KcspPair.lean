module

public import RestrictedPolynomials.TrackB.MergeLayer
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.RestrictCompose
public import RestrictedPolynomials.TrackB.StabComplex
public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.FinProbMarginalPi

/-!
# Track B: the CSP_7 pair layer (`lemma:kcsp`, first half)

Source: CSP_7, l. 481-598: `lemma:kcsp`
`#def-mu-minus-k-minus-k`, `#cauchy-schwarz-remove-xk`, `#diagonal-mixture-decomposition`,
`eq:stuff1`, `#apply-ih`, `eq:f1`, `#def-xi-g`, `obs:pcxi`, `obs:3wisexi`,
`#xi-atom-bound`, `#xi-split`. `obs:3wisexi` has the weight
`1 - α²` (the printed `1 - α` is a slip); the atom bound of `ξ` is `α³ δ'` (the printed `α² δ` is false).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### Private helpers on finite expectations -/

section Helpers

private theorem k7p_fp_ext {β : Type} [Fintype β] {P Q : FinProb β}
    (h : ∀ a, P.prob a = Q.prob a) : P = Q := by
  cases P; cases Q
  simp only [FinProb.mk.injEq]
  exact funext h

private theorem k7p_re_cexpect {β : Type} [Fintype β] (P : FinProb β) (g : β → ℂ) :
    (P.cexpect g).re = ∑ a, P.prob a * (g a).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => Complex.re_ofReal_mul _ _

private theorem k7p_norm_cexpect_le {β : Type} [Fintype β] (P : FinProb β) (g : β → ℂ) {B : ℝ}
    (h : ∀ a, ‖g a‖ ≤ B) : ‖P.cexpect g‖ ≤ B := by
  unfold FinProb.cexpect
  calc ‖∑ a, (P.prob a : ℂ) * g a‖ ≤ ∑ a, ‖(P.prob a : ℂ) * g a‖ := norm_sum_le _ _
    _ ≤ ∑ a, P.prob a * B := Finset.sum_le_sum fun a _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P.nonneg a)]
        exact mul_le_mul_of_nonneg_left (h a) (P.nonneg a)
    _ = B := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

private theorem k7p_star_cexpect {β : Type} [Fintype β] (P : FinProb β) (g : β → ℂ) :
    star (P.cexpect g) = P.cexpect (fun a => star (g a)) := by
  unfold FinProb.cexpect
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_mul']
  congr 1
  exact Complex.conj_ofReal _

/-- expectation of a pushforward, coordinatewise on `κ`. -/
private theorem k7p_cexpect_pi_push {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq γ]
    {κ : Type} [Fintype κ] [DecidableEq κ] (P : FinProb β) (φ : β → γ) (G : (κ → γ) → ℂ) :
    ((mergePush P φ).pi κ).cexpect G = (P.pi κ).cexpect (fun x => G (fun t => φ (x t))) := by
  unfold FinProb.cexpect
  have h1 : ∀ y : κ → γ, ((mergePush P φ).pi κ).prob y =
      ∑ x ∈ univ.filter (fun x : κ → β => (fun t => φ (x t)) = y), (P.pi κ).prob x := by
    intro y
    rw [FinProb.pi_prob]
    have hp : ∀ t, (mergePush P φ).prob (y t) =
        ∑ a ∈ univ.filter (fun a => φ a = y t), P.prob a := fun t => rfl
    simp only [hp]
    rw [Finset.prod_univ_sum]
    have : Fintype.piFinset (fun t => univ.filter (fun a => φ a = y t)) =
        univ.filter (fun x : κ → β => (fun t => φ (x t)) = y) := by
      ext x; simp [Fintype.mem_piFinset, funext_iff]
    rw [this]
    rfl
  simp_rw [h1]
  rw [← Finset.sum_fiberwise univ (fun x : κ → β => fun t => φ (x t))
    (fun x => ((P.pi κ).prob x : ℂ) * G (fun t => φ (x t)))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- the product law `P ⊗ R`. -/
private def k7pProd {β γ : Type} [Fintype β] [Fintype γ] (P : FinProb β) (R : FinProb γ) :
    FinProb (β × γ) where
  prob p := P.prob p.1 * R.prob p.2
  nonneg p := mul_nonneg (P.nonneg _) (R.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, R.sum_eq_one, mul_one, P.sum_eq_one]

private theorem k7p_cexpect_pi_prod {β γ : Type} [Fintype β] [Fintype γ] {κ : Type} [Fintype κ]
    [DecidableEq κ] (P : FinProb β) (R : FinProb γ) (G : (κ → β) → (κ → γ) → ℂ) :
    (P.pi κ).cexpect (fun x => (R.pi κ).cexpect (fun y => G x y)) =
      ((k7pProd P R).pi κ).cexpect (fun z => G (fun t => (z t).1) (fun t => (z t).2)) := by
  let e : (κ → β × γ) ≃ (κ → β) × (κ → γ) :=
    Equiv.arrowProdEquivProdArrow κ (fun _ => β) (fun _ => γ)
  unfold FinProb.cexpect
  rw [← Fintype.sum_equiv e.symm (fun q : (κ → β) × (κ → γ) =>
      (((k7pProd P R).pi κ).prob (e.symm q) : ℂ) * G q.1 q.2) _ (fun q => by simp [e]),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : ((k7pProd P R).pi κ).prob (e.symm (x, y)) = (P.pi κ).prob x * (R.pi κ).prob y := by
    simp only [FinProb.pi_prob, k7pProd, e, Finset.prod_mul_distrib]
    rfl
  rw [this]
  push_cast
  ring

private theorem k7p_prob_le_one {β : Type} [Fintype β] (P : FinProb β) (a : β) :
    P.prob a ≤ 1 := by
  rw [← P.sum_eq_one]
  exact Finset.single_le_sum (fun b _ => P.nonneg b) (Finset.mem_univ a)

private theorem k7p_exists_support {β : Type} [Fintype β] (P : FinProb β) :
    ∃ a, P.prob a ≠ 0 := by
  by_contra h
  push Not at h
  have := P.sum_eq_one
  simp [h] at this

private theorem k7p_alpha_le_one {β : Type} [Fintype β] (P : FinProb β) {α : ℝ}
    (hatom : ∀ a ∈ P.support, α ≤ P.prob a) : α ≤ 1 := by
  obtain ⟨a, ha⟩ := k7p_exists_support P
  exact (hatom a ha).trans (k7p_prob_le_one P a)

/-- an expectation over `κ → β × γ` as a double sum. -/
private theorem k7p_cexpect_pi_pair {β γ : Type} [Fintype β] [Fintype γ] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : FinProb (β × γ)) (g : (κ → β) → (κ → γ) → ℂ) :
    (M.pi κ).cexpect (fun z => g (fun t => (z t).1) (fun t => (z t).2)) =
      ∑ x : κ → β, ∑ y : κ → γ, ((∏ t, M.prob (x t, y t) : ℝ) : ℂ) * g x y := by
  let e : (κ → β × γ) ≃ (κ → β) × (κ → γ) :=
    Equiv.arrowProdEquivProdArrow κ (fun _ => β) (fun _ => γ)
  unfold FinProb.cexpect
  rw [← Fintype.sum_equiv e.symm (fun q : (κ → β) × (κ → γ) =>
      ((M.pi κ).prob (e.symm q) : ℂ) * g q.1 q.2) _ (fun q => by simp [e]),
    Fintype.sum_prod_type]
  rfl

/-- weighted Cauchy-Schwarz: `|∑ u G|² ≤ ∑ |G|²/W` (`|u| ≤ 1`, `∑ W = 1`, `G = 0` on `W = 0`). -/
private theorem k7p_cs_weighted {X : Type} [Fintype X] (W : X → ℝ) (hW : ∀ x, 0 ≤ W x)
    (hW1 : ∑ x, W x = 1) (G u : X → ℂ) (hu : ∀ x, ‖u x‖ ≤ 1) (hG : ∀ x, W x = 0 → G x = 0) :
    ‖∑ x, u x * G x‖ ^ 2 ≤ ∑ x, ‖G x‖ ^ 2 / W x := by
  have h1 : ‖∑ x, u x * G x‖ ≤ ∑ x, Real.sqrt (W x) * (‖G x‖ / Real.sqrt (W x)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
    rcases eq_or_ne (W x) 0 with h | h
    · rw [hG x h]; simp
    · have hs : 0 < Real.sqrt (W x) := Real.sqrt_pos.2 (lt_of_le_of_ne (hW x) (Ne.symm h))
      rw [mul_div_cancel₀ _ hs.ne']
      exact mul_le_of_le_one_left (norm_nonneg _) (hu x)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (W x))
    (fun x => ‖G x‖ / Real.sqrt (W x))
  have h3 : ∑ x, Real.sqrt (W x) ^ 2 = 1 := by
    rw [show ∑ x, Real.sqrt (W x) ^ 2 = ∑ x, W x from
      Finset.sum_congr rfl fun x _ => Real.sq_sqrt (hW x), hW1]
  have h4 : ∀ x, (‖G x‖ / Real.sqrt (W x)) ^ 2 = ‖G x‖ ^ 2 / W x := fun x => by
    rw [div_pow, Real.sq_sqrt (hW x)]
  calc ‖∑ x, u x * G x‖ ^ 2
      ≤ (∑ x, Real.sqrt (W x) * (‖G x‖ / Real.sqrt (W x))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = ∑ x, ‖G x‖ ^ 2 / W x := by rw [h3, one_mul]; simp_rw [h4]

/-- the affine comparison `c · Re 𝔼 u ≤ d + Re 𝔼 v` from the pointwise one. -/
private theorem k7p_re_cexpect_affine {β : Type} [Fintype β] (P : FinProb β) (u v : β → ℂ)
    (c d : ℝ) (h : ∀ b, c * (u b).re ≤ d + (v b).re) :
    c * (P.cexpect u).re ≤ d + (P.cexpect v).re := by
  rw [k7p_re_cexpect, k7p_re_cexpect, Finset.mul_sum]
  calc ∑ b, c * (P.prob b * (u b).re) = ∑ b, P.prob b * (c * (u b).re) :=
        Finset.sum_congr rfl fun b _ => by ring
    _ ≤ ∑ b, P.prob b * (d + (v b).re) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h b) (P.nonneg b)
    _ = (∑ b, P.prob b) * d + ∑ b, P.prob b * (v b).re := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = d + ∑ b, P.prob b * (v b).re := by rw [P.sum_eq_one, one_mul]

private theorem k7p_subsetExpect_congr {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℝ}
    (h0 h0' : 0 ≤ q) (h1 h1' : q ≤ 1) {G G' : Finset ι → ℂ} (h : ∀ I, G I = G' I) :
    subsetExpect q h0 h1 G = subsetExpect q h0' h1' G' := by
  have : G = G' := funext h
  subst this
  rfl

private theorem k7p_cexpect_congr {β : Type} [Fintype β] (P : FinProb β) {u v : β → ℂ}
    (h : ∀ a, u a = v a) : P.cexpect u = P.cexpect v := by
  rw [funext h]

private theorem k7p_re_cstab_nonneg {α : Type} [Fintype α] [DecidableEq α] {κ : Type}
    [Fintype κ] [DecidableEq κ] (π : FinProb α) {ρ : ℝ} (hρ : 0 ≤ ρ) (g : (κ → α) → ℂ) :
    0 ≤ (cstab π ρ g).re := by
  rw [re_cstab_eq]
  exact Finset.sum_nonneg fun S _ => mul_nonneg (pow_nonneg hρ _) (cw_nonneg π S g)

/-- the affine comparison through a restriction average and an inner expectation. -/
private theorem k7p_two_level {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℝ} (h0 : 0 ≤ q)
    (h1 : q ≤ 1) {β : Finset ι → Type} [∀ I, Fintype (β I)] (P : ∀ I, FinProb (β I))
    (c Y : ∀ I, β I → ℂ) (d e : ℝ) (h : ∀ I b, d * (c I b).re ≤ e + (Y I b).re) :
    d * (subsetExpect q h0 h1 fun I => (P I).cexpect (c I)).re ≤
      e + (subsetExpect q h0 h1 fun I => (P I).cexpect (Y I)).re := by
  unfold subsetExpect
  exact k7p_re_cexpect_affine _ _ _ _ _ fun b => k7p_re_cexpect_affine _ _ _ _ _ (h _)

private theorem k7p_connected_of_reach {V : Type} (G : SimpleGraph V) (b : V)
    (h : ∀ v, G.Reachable v b) : G.Connected :=
  { preconnected := fun u v => (h u).trans (h v).symm
    nonempty := ⟨b⟩ }

private theorem k7p_fromRel_adj {V : Type} (r : V → V → Prop) {a b : V} (hab : a ≠ b)
    (h : r a b) : (SimpleGraph.fromRel r).Adj a b := by
  rw [SimpleGraph.fromRel_adj]
  exact ⟨hab, Or.inl h⟩

/-- the pointwise Markov step: `d · Re c ≤ d e + Re Y` when `|c| ≤ 1`, `Re Y ≥ 0` and
`Re Y ≥ d` on the event `|c| ≥ e`. -/
private theorem k7p_markov {c Y : ℂ} {d e : ℝ} (hd : 0 < d) (hc : ‖c‖ ≤ 1) (hY0 : 0 ≤ Y.re)
    (hY : e ≤ ‖c‖ → d ≤ Y.re) (he : 0 ≤ d * e) : d * c.re ≤ d * e + Y.re := by
  have hre := Complex.re_le_norm c
  by_cases hbig : e ≤ ‖c‖
  · have := mul_le_mul_of_nonneg_left (hre.trans hc) hd.le
    linarith [hY hbig]
  · push Not at hbig
    have := mul_le_mul_of_nonneg_left (hre.trans hbig.le) hd.le
    linarith

/-- a coordinatewise map commutes with gluing. -/
private theorem k7p_glue_map {ι α β : Type} [Fintype ι] [DecidableEq ι] (I : Finset ι)
    (g : α → β) (z : ↥I → α) (y : ↥Iᶜ → α) :
    (fun t => g (glueFix I z y t)) = glueFix I (fun t => g (z t)) (fun t => g (y t)) := by
  funext t
  by_cases h : t ∈ I <;> simp [glueFix, h]

end Helpers

section Defs
variable {k : ℕ} {A : Fin (k + 1) → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- `t ↦ (t_i)_{i ≠ j}`, indexed by `Fin k` through `j.succAbove`. -/
def k7Drop (j : Fin (k + 1)) (t : ∀ i, A i) : ∀ i : Fin k, A (j.succAbove i) :=
  fun i => t (j.succAbove i)

/-- `μ_{-j}`. -/
def k7DropMarg (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) :
    FinProb (∀ i : Fin k, A (j.succAbove i)) :=
  mergePush μ (k7Drop j)

/-- `μ_{-j,-j}` -/
def k7PairLaw (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) :
    FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))) where
  prob p := ∑ x : A j,
    (∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = p.1), μ.prob t) *
      (∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = p.2), μ.prob t) /
      (μ.marginalPi j).prob x
  nonneg p := by
    refine Finset.sum_nonneg fun x _ => ?_
    refine div_nonneg (mul_nonneg (Finset.sum_nonneg fun t _ => μ.nonneg t)
      (Finset.sum_nonneg fun t _ => μ.nonneg t)) (Finset.sum_nonneg fun t _ => μ.nonneg t)
  sum_eq_one := by
    have hfib : ∀ x : A j, ∑ a : (∀ i : Fin k, A (j.succAbove i)),
        ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t =
          (μ.marginalPi j).prob x := by
      intro x
      have h1 : ∀ a : (∀ i : Fin k, A (j.succAbove i)),
          ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t =
            ∑ t ∈ (univ.filter (fun t : ∀ i, A i => t j = x)).filter (fun t => k7Drop j t = a),
              μ.prob t := by
        intro a
        rw [Finset.filter_filter]
      simp_rw [h1]
      rw [Finset.sum_fiberwise (univ.filter (fun t : ∀ i, A i => t j = x)) (k7Drop j) μ.prob]
      rfl
    rw [Finset.sum_comm]
    rw [← (μ.marginalPi j).sum_eq_one]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ (f g : (∀ i : Fin k, A (j.succAbove i)) → ℝ) (c : ℝ),
        ∑ a, ∑ a', f a * g a' / c = (∑ a, f a) * (∑ a', g a') / c := by
      intro f g c
      rw [Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]
    simp only []
    rw [hsplit (fun a => ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t) (fun a => ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t), hfib x]
    rcases eq_or_ne ((μ.marginalPi j).prob x) 0 with h | h
    · rw [h]; simp
    · field_simp

/-- the diagonal embedding of `μ_{-j}` into pairs. -/
def k7DiagLaw (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) :
    FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))) :=
  mergePush (k7DropMarg μ j) fun a => (a, a)

/-- the law of the surviving coordinate pair `(x_s, x_s')` of a pair law. -/
def k7NuPair (j : Fin (k + 1)) (s : Fin k)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i)))) :
    FinProb (A (j.succAbove s) × A (j.succAbove s)) :=
  mergePush ν fun p => (p.1 s, p.2 s)

end Defs

section PairHelpers
variable {k : ℕ} {A : Fin (k + 1) → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- the joint mass `μ(x_j = x, x_{-j} = a)`. -/
private def k7pM (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (x : A j)
    (a : ∀ i : Fin k, A (j.succAbove i)) : ℝ :=
  ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t

private theorem k7pM_nonneg (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (x : A j)
    (a : ∀ i : Fin k, A (j.succAbove i)) : 0 ≤ k7pM μ j x a :=
  Finset.sum_nonneg fun t _ => μ.nonneg t

private theorem k7p_pairLaw_prob (μ : FinProb (∀ i, A i)) (j : Fin (k + 1))
    (p : (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))) :
    (k7PairLaw μ j).prob p =
      ∑ x, k7pM μ j x p.1 * k7pM μ j x p.2 / (μ.marginalPi j).prob x := rfl

private theorem k7pM_sum_a (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (x : A j) :
    ∑ a, k7pM μ j x a = (μ.marginalPi j).prob x := by
  unfold k7pM
  have h1 : ∀ a : (∀ i : Fin k, A (j.succAbove i)),
      ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t =
        ∑ t ∈ (univ.filter (fun t : ∀ i, A i => t j = x)).filter (fun t => k7Drop j t = a),
          μ.prob t := by
    intro a
    rw [Finset.filter_filter]
  simp_rw [h1]
  rw [Finset.sum_fiberwise (univ.filter (fun t : ∀ i, A i => t j = x)) (k7Drop j) μ.prob]
  rfl

private theorem k7pM_sum_x (μ : FinProb (∀ i, A i)) (j : Fin (k + 1))
    (a : ∀ i : Fin k, A (j.succAbove i)) :
    ∑ x, k7pM μ j x a = (k7DropMarg μ j).prob a := by
  unfold k7pM
  have h1 : ∀ x : A j,
      ∑ t ∈ univ.filter (fun t : ∀ i, A i => t j = x ∧ k7Drop j t = a), μ.prob t =
        ∑ t ∈ (univ.filter (fun t : ∀ i, A i => k7Drop j t = a)).filter (fun t => t j = x),
          μ.prob t := by
    intro x
    rw [Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  simp_rw [h1]
  rw [Finset.sum_fiberwise (univ.filter (fun t : ∀ i, A i => k7Drop j t = a)) (fun t => t j)
    μ.prob]
  rfl

private theorem k7pM_le (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (x : A j)
    (a : ∀ i : Fin k, A (j.succAbove i)) : k7pM μ j x a ≤ (μ.marginalPi j).prob x := by
  rw [← k7pM_sum_a]
  exact Finset.single_le_sum (fun b _ => k7pM_nonneg μ j x b) (Finset.mem_univ a)

/-- `m(x,a) · μ_j(x) / μ_j(x) = m(x,a)`. -/
private theorem k7pM_mul_div (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (x : A j)
    (a : ∀ i : Fin k, A (j.succAbove i)) :
    k7pM μ j x a * (μ.marginalPi j).prob x / (μ.marginalPi j).prob x = k7pM μ j x a := by
  rcases eq_or_ne ((μ.marginalPi j).prob x) 0 with h | h
  · have : k7pM μ j x a = 0 :=
      le_antisymm (h ▸ k7pM_le μ j x a) (k7pM_nonneg μ j x a)
    rw [this]; simp
  · field_simp

/-- a filtered sum over pairs with first component `a`. -/
private theorem k7p_sum_filter_fst {D : Type} [Fintype D] [DecidableEq D] (F : D × D → ℝ) (a : D) :
    ∑ p ∈ univ.filter (fun p : D × D => p.1 = a), F p = ∑ a', F (a, a') := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

private theorem k7p_sum_filter_snd {D : Type} [Fintype D] [DecidableEq D] (F : D × D → ℝ) (a : D) :
    ∑ p ∈ univ.filter (fun p : D × D => p.2 = a), F p = ∑ a', F (a', a) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

private theorem k7p_diag_prob (μ : FinProb (∀ i, A i)) (j : Fin (k + 1))
    (p : (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))) :
    (k7DiagLaw μ j).prob p = if p.1 = p.2 then (k7DropMarg μ j).prob p.1 else 0 := by
  obtain ⟨a, b⟩ := p
  show ∑ c ∈ univ.filter (fun c => (c, c) = (a, b)), (k7DropMarg μ j).prob c = _
  rw [Finset.sum_filter, Finset.sum_eq_single a]
  · by_cases h : a = b <;> simp [h]
  · intro c _ hc; simp [hc]
  · simp

private theorem k7pM_ge (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {α : ℝ}
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a) (x : A j) (a : ∀ i : Fin k, A (j.succAbove i))
    (h : k7pM μ j x a ≠ 0) : α ≤ k7pM μ j x a := by
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hatom t hne).trans (Finset.single_le_sum (f := μ.prob) (fun t' _ => μ.nonneg t') ht)

/-- `μ_{-j,-j}(a,a) ≥ α² μ_{-j}(a)`. -/
private theorem k7p_pairLaw_diag_ge (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (a : ∀ i : Fin k, A (j.succAbove i)) :
    α ^ 2 * (k7DropMarg μ j).prob a ≤ (k7PairLaw μ j).prob (a, a) := by
  rw [k7p_pairLaw_prob, ← k7pM_sum_x, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  dsimp only
  have hm0 := k7pM_nonneg μ j x a
  rcases eq_or_ne (k7pM μ j x a) 0 with hm | hm
  · rw [hm]; simp
  · have hmα := k7pM_ge μ j hatom x a hm
    have hle := k7pM_le μ j x a
    have h1 := k7p_prob_le_one (μ.marginalPi j) x
    have hpos : 0 < (μ.marginalPi j).prob x :=
      lt_of_lt_of_le (lt_of_le_of_ne hm0 (Ne.symm hm)) hle
    rw [le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg α) hm0),
      mul_le_mul_of_nonneg_right hmα hm0, mul_le_mul_of_nonneg_right hα1 (mul_nonneg hα0 hm0)]

end PairHelpers

section XiDefs
variable {A0 : Type} [Fintype A0] [DecidableEq A0] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the pairs that occur: `{(x,x') : ν₁(x,x') ≠ 0} ∪ {(x,x)}` (`A⁺` trimmed, `⋆ = none`). -/
def k7PairSet (ν1 : FinProb (A0 × A0)) : Finset (A0 × A0) :=
  univ.filter fun p => ν1.prob p ≠ 0 ∨ p.1 = p.2

def k7Dec1 {S : Finset (A0 × A0)} : Option ↥S → A0 → A0
  | some p, _ => p.1.1
  | none, u => u

def k7Dec2 {S : Finset (A0 × A0)} : Option ↥S → A0 → A0
  | some p, _ => p.1.2
  | none, u => u

/-- `g(x⁺) = 𝔼_{(x,x') ∼_⋆ x⁺} f(x) conj f(x')`. -/
def k7G (π : FinProb A0) (f : (ι → A0) → ℂ) {S : Finset (A0 × A0)} (w : ι → Option ↥S) : ℂ :=
  (π.pi ι).cexpect fun u =>
    f (fun t => k7Dec1 (w t) (u t)) * star (f (fun t => k7Dec2 (w t) (u t)))

end XiDefs

section XiHelpers
variable {A0 : Type} [Fintype A0] [DecidableEq A0]

private theorem k7p_pairSet_mem (ν1 : FinProb (A0 × A0)) {p : A0 × A0} (h : ν1.prob p ≠ 0) :
    p ∈ k7PairSet ν1 := by
  simp [k7PairSet, h]

private theorem k7p_pairSet_diag (ν1 : FinProb (A0 × A0)) (x : A0) : (x, x) ∈ k7PairSet ν1 := by
  simp [k7PairSet]

/-- the characterising formula of `ξ`. -/
private def k7pXi (π : FinProb A0) (ν1 : FinProb (A0 × A0)) (α δ' : ℝ) (x x' : A0)
    (ω : Option ↥(k7PairSet ν1)) : ℝ :=
  (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then ν1.prob (x, x') else 0) +
    α ^ 2 * (if x = x' then π.prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
      else if ω = none then δ' else 0) else 0)

/-- the `(ω, u)`-sum of `ξ(x, x', ω) π(u) T(x, x', dec(ω, u))` for fixed `(x, x')`. -/
private theorem k7p_xi_test_xx (π : FinProb A0) (ν1 : FinProb (A0 × A0)) (α δ' : ℝ)
    (T : A0 × A0 × A0 × A0 → ℝ) (x x' : A0) :
    ∑ ω : Option ↥(k7PairSet ν1), ∑ u, k7pXi π ν1 α δ' x x' ω * π.prob u *
      T (x, x', k7Dec1 ω u, k7Dec2 ω u) =
    (1 - α ^ 2) * ν1.prob (x, x') * T (x, x', x, x') + (if x = x' then α ^ 2 * π.prob x *
      ((1 - δ') * T (x, x, x, x) + δ' * ∑ u, π.prob u * T (x, x, u, u)) else 0) := by
  have hπ : ∀ c : ℝ, ∑ u, c * π.prob u = c := fun c => by
    rw [← Finset.mul_sum, π.sum_eq_one, mul_one]
  rw [Fintype.sum_option]
  obtain ⟨F, hF⟩ : ∃ F : A0 × A0 → ℝ, F = fun r => ((1 - α ^ 2) *
      (if r = (x, x') then ν1.prob (x, x') else 0) + α ^ 2 * (if x = x' then
        π.prob x * (if r = (x, x) then 1 - δ' else 0) else 0)) * T (x, x', r.1, r.2) := ⟨_, rfl⟩
  have hsome : ∀ p : ↥(k7PairSet ν1), ∑ u, k7pXi π ν1 α δ' x x' (some p) * π.prob u *
      T (x, x', k7Dec1 (some p) u, k7Dec2 (some p) u) = F p.1 := by
    intro p
    simp only [k7pXi, k7Dec1, k7Dec2, Option.map_some, Option.some.injEq, reduceCtorEq,
      ite_false, hF]
    rw [← hπ ((((1 - α ^ 2) * (if p.1 = (x, x') then ν1.prob (x, x') else 0) +
        α ^ 2 * (if x = x' then π.prob x * (if p.1 = (x, x) then 1 - δ' else 0) else 0)) *
        T (x, x', p.1.1, p.1.2)))]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [Finset.sum_congr rfl fun p _ => hsome p, Finset.sum_coe_sort (k7PairSet ν1) F, hF]
  have hnone : ∀ u, k7pXi π ν1 α δ' x x' none * π.prob u *
      T (x, x', k7Dec1 (none : Option ↥(k7PairSet ν1)) u,
        k7Dec2 (none : Option ↥(k7PairSet ν1)) u)
      = (if x = x' then α ^ 2 * π.prob x * δ' else 0) * (π.prob u * T (x, x', u, u)) := by
    intro u
    simp only [k7pXi, k7Dec1, k7Dec2, Option.map_none, reduceCtorEq, ite_false, ite_true]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun u _ => hnone u, ← Finset.mul_sum]
  by_cases hx : x = x'
  · subst hx
    have hS : ∀ r ∈ k7PairSet ν1, ((1 - α ^ 2) * (if r = (x, x) then ν1.prob (x, x) else 0) +
        α ^ 2 * (if x = x then π.prob x * (if r = (x, x) then 1 - δ' else 0) else 0)) *
        T (x, x, r.1, r.2) = if r = (x, x) then ((1 - α ^ 2) * ν1.prob (x, x) +
          α ^ 2 * π.prob x * (1 - δ')) * T (x, x, x, x) else 0 := by
      intro r _
      by_cases hr : r = (x, x)
      · subst hr; simp only [ite_true]; ring
      · simp only [hr, ite_false, ite_true]; ring
    rw [Finset.sum_congr rfl hS, Finset.sum_ite_eq']
    simp only [k7p_pairSet_diag ν1 x, ite_true]
    ring
  · have hS : ∀ r ∈ k7PairSet ν1, ((1 - α ^ 2) * (if r = (x, x') then ν1.prob (x, x') else 0) +
        α ^ 2 * (if x = x' then π.prob x * (if r = (x, x) then 1 - δ' else 0) else 0)) *
        T (x, x', r.1, r.2) = if r = (x, x') then
          (1 - α ^ 2) * ν1.prob (x, x') * T (x, x', x, x') else 0 := by
      intro r _
      by_cases hr : r = (x, x')
      · subst hr; simp only [hx, ite_true, ite_false]; ring
      · simp only [hr, hx, ite_false]; ring
    rw [Finset.sum_congr rfl hS, Finset.sum_ite_eq']
    simp only [hx, ite_false, zero_mul, zero_add, add_zero]
    split_ifs with hm
    · rfl
    · have : ν1.prob (x, x') = 0 := by
        by_contra hne; exact hm (k7p_pairSet_mem ν1 hne)
      rw [this]; ring

/-- the `ω`-sum of the formula. -/
private theorem k7p_xi_sum_ω (π : FinProb A0) (ν1 : FinProb (A0 × A0)) (α δ' : ℝ) (x x' : A0) :
    ∑ ω : Option ↥(k7PairSet ν1), k7pXi π ν1 α δ' x x' ω =
      (1 - α ^ 2) * ν1.prob (x, x') + α ^ 2 * (if x = x' then π.prob x else 0) := by
  have h := k7p_xi_test_xx π ν1 α δ' (fun _ => 1) x x'
  have hπ : ∀ c : ℝ, ∑ u, c * π.prob u * (fun _ : A0 × A0 × A0 × A0 => (1 : ℝ))
      (x, x', x, x') = c := fun c => by
    simp only [mul_one]; rw [← Finset.mul_sum, π.sum_eq_one, mul_one]
  simp only [hπ] at h
  rw [h]
  split_ifs
  · simp only [mul_one]; rw [π.sum_eq_one]; ring
  · ring

/-- the full test identity: the law of `(x, x', dec(ω, u))` under `ξ ⊗ π` is the mixture of
`(x, x', x, x')`, `(x,x') ∼ ν₁`, and `(y, y, z, z)`, `(y, z)` the `(1-δ')`-noise pair. -/
private theorem k7p_xi_test (π : FinProb A0) (ν1 : FinProb (A0 × A0)) (α δ' : ℝ)
    (ξ : FinProb (A0 × A0 × Option ↥(k7PairSet ν1)))
    (hξ : ∀ x x' ω, ξ.prob (x, x', ω) = k7pXi π ν1 α δ' x x' ω) (T : A0 × A0 × A0 × A0 → ℝ) :
    ∑ w : A0 × A0 × Option ↥(k7PairSet ν1), ∑ u, ξ.prob w * π.prob u *
      T (w.1, w.2.1, k7Dec1 w.2.2 u, k7Dec2 w.2.2 u) =
    (1 - α ^ 2) * ∑ p : A0 × A0, ν1.prob p * T (p.1, p.2, p.1, p.2) +
      α ^ 2 * ∑ p : A0 × A0, π.prob p.1 * noiseKernel π (1 - δ') p.1 p.2 *
        T (p.1, p.1, p.2, p.2) := by
  have h1 : ∑ w : A0 × A0 × Option ↥(k7PairSet ν1), ∑ u, ξ.prob w * π.prob u *
      T (w.1, w.2.1, k7Dec1 w.2.2 u, k7Dec2 w.2.2 u) =
      ∑ x, ∑ x', ((1 - α ^ 2) * ν1.prob (x, x') * T (x, x', x, x') +
        (if x = x' then α ^ 2 * π.prob x *
          ((1 - δ') * T (x, x, x, x) + δ' * ∑ u, π.prob u * T (x, x, u, u)) else 0)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [← k7p_xi_test_xx]
    simp only [hξ]
  have hD : ∑ p : A0 × A0, π.prob p.1 * noiseKernel π (1 - δ') p.1 p.2 *
      T (p.1, p.1, p.2, p.2) =
      ∑ x, π.prob x * ((1 - δ') * T (x, x, x, x) + δ' * ∑ u, π.prob u * T (x, x, u, u)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [noiseKernel]
    have : ∀ z : A0, π.prob x * ((1 - δ') * (if x = z then 1 else 0) +
        (1 - (1 - δ')) * π.prob z) * T (x, x, z, z) =
        (if x = z then π.prob x * (1 - δ') * T (x, x, x, x) else 0) +
          π.prob x * δ' * (π.prob z * T (x, x, z, z)) := by
      intro z
      by_cases hz : x = z
      · subst hz; simp only [ite_true]; ring
      · simp only [hz, ite_false]; ring
    rw [Finset.sum_congr rfl fun z _ => this z, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ← Finset.mul_sum]
    simp only [Finset.mem_univ, ite_true]
    ring
  rw [h1, hD, Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring
  · ring

/-- a mass of a pushforward as a sum against an indicator. -/
private theorem k7p_push_prob {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq γ]
    (P : FinProb β) (φ : β → γ) (q : γ) :
    (mergePush P φ).prob q = ∑ a, P.prob a * (fun r => if r = q then (1 : ℝ) else 0) (φ a) := by
  show ∑ a ∈ univ.filter (fun a => φ a = q), P.prob a = _
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by simp only [mul_ite, mul_one, mul_zero]

/-- `c · 𝔼 g = 𝔼 (c · g)`. -/
private theorem k7p_mul_cexpect {β : Type} [Fintype β] (P : FinProb β) (c : ℂ) (g : β → ℂ) :
    c * P.cexpect g = P.cexpect (fun a => c * g a) := by
  unfold FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

end XiHelpers

section Steps
variable {k : ℕ} {A : Fin (k + 1) → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- TYPING: the support of `μ_{-j}` is the image of the support. -/
theorem k7_dropMarg_support (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) :
    (k7DropMarg μ j).support = k7Drop j '' μ.support := by
  ext a
  simp only [FinProb.support, Set.mem_ofPred_eq, Set.mem_image]
  show (∑ t ∈ univ.filter (fun t => k7Drop j t = a), μ.prob t) ≠ 0 ↔ _
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg (fun t _ => μ.nonneg t)]
  push Not
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, hne⟩; exact ⟨t, hne, ht⟩
  · rintro ⟨t, hne, ht⟩; exact ⟨t, ht, hne⟩

/-- TYPING: the marginal of `μ_{-j}` at `s` is the marginal of `μ` at `j.succAbove s`. -/
theorem k7_dropMarg_marginalPi (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) :
    (k7DropMarg μ j).marginalPi s = μ.marginalPi (j.succAbove s) := by
  apply k7p_fp_ext
  intro b
  show ∑ a ∈ univ.filter (fun a : ∀ i : Fin k, A (j.succAbove i) => a s = b),
      ∑ t ∈ univ.filter (fun t : ∀ i, A i => k7Drop j t = a), μ.prob t =
    ∑ t ∈ univ.filter (fun t : ∀ i, A i => t (j.succAbove s) = b), μ.prob t
  rw [← Finset.sum_fiberwise (univ.filter (fun t : ∀ i, A i => t (j.succAbove s) = b))
    (k7Drop j) μ.prob, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨by rw [← ha, ← h]; rfl, h⟩
    · exact fun h => h.2
  · symm
    refine Finset.sum_eq_zero fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact absurd (by rw [← ht.2, ← ht.1]; rfl) ha

/-- TYPING: atoms of `μ_{-j}` are `≥ α` when atoms of `μ` are (CSP_7 `lemma:kcsp#apply-ih`, premise). -/
theorem k7_dropMarg_atom_bound (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {α : ℝ}
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a) :
    ∀ a ∈ (k7DropMarg μ j).support, α ≤ (k7DropMarg μ j).prob a := by
  intro a ha
  rw [k7_dropMarg_support] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  calc α ≤ μ.prob t := hatom t ht
    _ ≤ ∑ t' ∈ univ.filter (fun t' => k7Drop j t' = k7Drop j t), μ.prob t' :=
        Finset.single_le_sum (f := μ.prob) (fun t' _ => μ.nonneg t') (by simp)

/-- TYPING: the first and the second component of `μ_{-j,-j}` both have the law `μ_{-j}`
(the two conditional samples are exchangeable). -/
theorem k7_pairLaw_marginals (μ : FinProb (∀ i, A i)) (j : Fin (k + 1))
    (a : ∀ i : Fin k, A (j.succAbove i)) :
    (mergePush (k7PairLaw μ j) Prod.fst).prob a = (k7DropMarg μ j).prob a ∧
      (mergePush (k7PairLaw μ j) Prod.snd).prob a = (k7DropMarg μ j).prob a := by
  constructor
  · show ∑ p ∈ univ.filter (fun p => p.1 = a), (k7PairLaw μ j).prob p = _
    rw [k7p_sum_filter_fst, ← k7pM_sum_x]
    simp only [k7p_pairLaw_prob]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_div, ← Finset.mul_sum, k7pM_sum_a, k7pM_mul_div]
  · show ∑ p ∈ univ.filter (fun p => p.2 = a), (k7PairLaw μ j).prob p = _
    rw [k7p_sum_filter_snd, ← k7pM_sum_x]
    simp only [k7p_pairLaw_prob]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_div, ← Finset.sum_mul, k7pM_sum_a, mul_comm, k7pM_mul_div]

/-- CSP_7 `lemma:kcsp#cauchy-schwarz-remove-xk`: only `‖f_j‖ ≤ 1` for the removed coordinate is used;
the right side is the pair-law expectation of `∏_{i ≠ j} f_i(x_i) conj f_i(x_i')`. -/
theorem k7_cauchy_schwarz_remove (μ : FinProb (∀ i, A i)) (j : Fin (k + 1))
    (f : ∀ i, (ι → A i) → ℂ) (hj : ∀ x, ‖f j x‖ ≤ 1) :
    ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ ^ 2 ≤
      (((k7PairLaw μ j).pi ι).cexpect fun p => ∏ i : Fin k,
        (f (j.succAbove i) fun t => (p t).1 i) *
          star (f (j.succAbove i) fun t => (p t).2 i)).re := by
  let H : (ι → ∀ i : Fin k, A (j.succAbove i)) → ℂ :=
    fun Y => ∏ i : Fin k, f (j.succAbove i) (fun t => Y t i)
  let K : (ι → A j) → (ι → ∀ i : Fin k, A (j.succAbove i)) → ℝ :=
    fun x Y => ∏ t, k7pM μ j (x t) (Y t)
  let W : (ι → A j) → ℝ := fun x => ∏ t, (μ.marginalPi j).prob (x t)
  let G : (ι → A j) → ℂ := fun x => ∑ Y, (K x Y : ℂ) * H Y
  -- the left side
  let φ : (∀ i, A i) → A j × (∀ i : Fin k, A (j.succAbove i)) := fun t => (t j, k7Drop j t)
  have hM : ∀ x a, (mergePush μ φ).prob (x, a) = k7pM μ j x a := by
    intro x a
    show ∑ t ∈ univ.filter (fun t => φ t = (x, a)), μ.prob t = _
    unfold k7pM
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp [φ, Prod.ext_iff]
  have hLHS : (μ.pi ι).cexpect (fun X => ∏ i, f i fun t => X t i) = ∑ x, f j x * G x := by
    have h1 : (μ.pi ι).cexpect (fun X => ∏ i, f i fun t => X t i) =
        ((mergePush μ φ).pi ι).cexpect
          (fun z => f j (fun t => (z t).1) * H (fun t => (z t).2)) := by
      rw [k7p_cexpect_pi_push]
      congr 1
      funext X
      rw [Fin.prod_univ_succAbove _ j]
      rfl
    rw [h1, k7p_cexpect_pi_pair (mergePush μ φ) (fun x Y => f j x * H Y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hM, G, Finset.mul_sum]
    exact Finset.sum_congr rfl fun Y _ => by simp only [K]; ring
  -- the right side
  have hint : ∀ p : ι → (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i)),
      (∏ i : Fin k, (f (j.succAbove i) fun t => (p t).1 i) *
        star (f (j.succAbove i) fun t => (p t).2 i)) =
      (fun Y Y' => H Y * star (H Y')) (fun t => (p t).1) (fun t => (p t).2) := by
    intro p
    simp only [H]
    rw [Finset.prod_mul_distrib, star_prod]
  have hP : ∀ Y Y' : ι → ∀ i : Fin k, A (j.succAbove i),
      ∏ t, (k7PairLaw μ j).prob (Y t, Y' t) = ∑ x, K x Y * K x Y' / W x := by
    intro Y Y'
    simp only [k7p_pairLaw_prob]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hG2 : ∀ x, ((‖G x‖ ^ 2 / W x : ℝ) : ℂ) =
      ∑ Y, ∑ Y', ((K x Y * K x Y' / W x : ℝ) : ℂ) * (H Y * star (H Y')) := by
    intro x
    rw [Complex.ofReal_div, Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
    simp only [G, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun Y _ => by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun Y' _ => by push_cast; ring
  have hRHS : ((k7PairLaw μ j).pi ι).cexpect (fun p => ∏ i : Fin k,
      (f (j.succAbove i) fun t => (p t).1 i) * star (f (j.succAbove i) fun t => (p t).2 i)) =
      ((∑ x, ‖G x‖ ^ 2 / W x : ℝ) : ℂ) := by
    simp_rw [hint]
    rw [k7p_cexpect_pi_pair (k7PairLaw μ j) (fun Y Y' => H Y * star (H Y'))]
    simp_rw [hP, Complex.ofReal_sum, hG2, Finset.sum_mul]
    exact (Finset.sum_congr rfl fun Y _ => Finset.sum_comm).trans Finset.sum_comm
  have hW : ∀ x, 0 ≤ W x := fun x => Finset.prod_nonneg fun t _ => (μ.marginalPi j).nonneg _
  have hW1 : ∑ x, W x = 1 := ((μ.marginalPi j).pi ι).sum_eq_one
  have hG : ∀ x, W x = 0 → G x = 0 := by
    intro x hx
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 hx
    refine Finset.sum_eq_zero fun Y _ => ?_
    have : K x Y = 0 := Finset.prod_eq_zero (Finset.mem_univ t)
      (le_antisymm (ht ▸ k7pM_le μ j (x t) (Y t)) (k7pM_nonneg μ j _ _))
    rw [this]; simp
  rw [hLHS, hRHS, Complex.ofReal_re]
  exact k7p_cs_weighted W hW hW1 G (f j) hj hG

/-- CSP_7 `lemma:kcsp#diagonal-mixture-decomposition` (existence form of `ν`). -/
theorem k7_diagonal_mixture (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {α : ℝ} (hα0 : 0 < α)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a) :
    ∃ ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))),
      ∀ p, (k7PairLaw μ j).prob p =
        α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p := by
  have hα1 : α ≤ 1 := k7p_alpha_le_one μ hatom
  have hDnn : ∀ p, 0 ≤ (k7PairLaw μ j).prob p - α ^ 2 * (k7DiagLaw μ j).prob p := by
    rintro ⟨a, b⟩
    rw [k7p_diag_prob]
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      linarith [k7p_pairLaw_diag_ge μ j hα0.le hα1 hatom a]
    · simp only [hab, ite_false, mul_zero, sub_zero]
      exact (k7PairLaw μ j).nonneg _
  have hDsum : ∑ p, ((k7PairLaw μ j).prob p - α ^ 2 * (k7DiagLaw μ j).prob p) = 1 - α ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, (k7PairLaw μ j).sum_eq_one,
      (k7DiagLaw μ j).sum_eq_one, mul_one]
  rcases lt_or_eq_of_le (show α ^ 2 ≤ 1 by nlinarith) with hlt | heq
  · have hpos : 0 < 1 - α ^ 2 := by linarith
    refine ⟨⟨fun p => ((k7PairLaw μ j).prob p - α ^ 2 * (k7DiagLaw μ j).prob p) / (1 - α ^ 2),
      fun p => div_nonneg (hDnn p) hpos.le, ?_⟩, fun p => ?_⟩
    · rw [← Finset.sum_div, hDsum, div_self hpos.ne']
    · show _ = _ + (1 - α ^ 2) *
        (((k7PairLaw μ j).prob p - α ^ 2 * (k7DiagLaw μ j).prob p) / (1 - α ^ 2))
      rw [mul_div_cancel₀ _ hpos.ne']
      ring
  · refine ⟨k7DiagLaw μ j, fun p => ?_⟩
    have hD0 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hDnn p)).1
      (by rw [hDsum, heq]; ring) p (Finset.mem_univ p)
    rw [heq] at hD0 ⊢
    linarith

/-- CSP_7 `eq:stuff1` (with `ε` for the lower bound `ε ≤ |𝔼 ∏ f_i|`). -/
theorem k7_eq_stuff1 (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    (f : ∀ i, (ι → A i) → ℂ) (hj : ∀ x, ‖f j x‖ ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖) :
    ε ^ 2 ≤ (subsetExpect (1 - α ^ 2) (by nlinarith) (by nlinarith [sq_nonneg α]) fun I =>
      (ν.pi ↥I).cexpect fun w =>
        ((k7DropMarg μ j).pi ↥Iᶜ).cexpect fun x => ∏ i : Fin k,
          restrictFix I (fun t => (w t).1 i) (f (j.succAbove i)) (fun t => x t i) *
            star (restrictFix I (fun t => (w t).2 i) (f (j.succAbove i)) (fun t => x t i))).re := by
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  have hα21 : α ^ 2 ≤ 1 := by nlinarith
  have hmix : ∀ p, (k7PairLaw μ j).prob p =
      (1 - α ^ 2) * ν.prob p + α ^ 2 * (k7DiagLaw μ j).prob p := fun p => by rw [hν p]; ring
  have hE := mixture_calculus hα2 hα21 (k7PairLaw μ j) ν (k7DiagLaw μ j) hmix
    (fun p : ι → _ => ∏ i : Fin k, (f (j.succAbove i) fun t => (p t).1 i) *
      star (f (j.succAbove i) fun t => (p t).2 i))
  refine (pow_le_pow_left₀ hε0 hε 2).trans
    ((k7_cauchy_schwarz_remove μ j f hj).trans (le_of_eq ?_))
  rw [hE]
  refine congrArg Complex.re ?_
  refine k7p_subsetExpect_congr _ _ _ _ fun I => ?_
  refine k7p_cexpect_congr _ fun w => ?_
  rw [show k7DiagLaw μ j = mergePush (k7DropMarg μ j) (fun a => (a, a)) from rfl,
    k7p_cexpect_pi_push]
  refine k7p_cexpect_congr _ fun x => ?_
  simp only [restrictFix]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e1 : (fun t => (glueFix I w (fun t => (x t, x t)) t).1 i) = _ :=
    k7p_glue_map I (fun p : (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i)) =>
      p.1 i) _ _
  have e2 : (fun t => (glueFix I w (fun t => (x t, x t)) t).2 i) = _ :=
    k7p_glue_map I (fun p : (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i)) =>
      p.2 i) _ _
  rw [e1, e2]

/-- CSP_7 `lemma:kcsp#apply-ih` with `eq:f1` (and `eq:stuff2`): the induction hypothesis
(`thm:kcsp` for `k`, single parameters `(ε²/2, δ')`) is applied to `μ_{-j}`; `ν₁` is the law of
`(z_s, z'_s)` under `ν`. -/
theorem k7_eq_f1 (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (hno : NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    {ε δ' : ℝ} (hε0 : 0 < ε) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1)
    (ih : ∀ (A' : Fin k → Type) [∀ i, Fintype (A' i)] [∀ i, DecidableEq (A' i)]
      (μ' : FinProb (∀ i, A' i)), NoNontrivialAbelianEmbeddingPi μ'.support →
      (∀ a ∈ μ'.support, α ≤ μ'.prob a) →
      ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (f' : ∀ i, (ι' → A' i) → ℂ),
        (∀ i x, ‖f' i x‖ ≤ 1) → ε ^ 2 / 2 ≤ ‖(μ'.pi ι').cexpect fun X => ∏ i, f' i fun t => X t i‖ →
        ∀ i, δ' ≤ (cstab (μ'.marginalPi i) (1 - δ') (f' i)).re)
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hε : ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖) :
    ε ^ 2 * δ' / 2 ≤ (subsetExpect (1 - α ^ 2) (by nlinarith) (by nlinarith [sq_nonneg α]) fun I =>
      ((k7NuPair j s ν).pi ↥I).cexpect fun v =>
        cstab (μ.marginalPi (j.succAbove s)) (1 - δ')
          (fun x : ↥Iᶜ → A (j.succAbove s) =>
            restrictFix I (fun t => (v t).1) (f (j.succAbove s)) x *
              star (restrictFix I (fun t => (v t).2) (f (j.succAbove s)) x))).re := by
  have hst := k7_eq_stuff1 μ j hα0 hα1 ν hν f (hf j) hε0.le hε
  have hδ1' : 0 ≤ 1 - δ' := by linarith
  have key : ∀ (I : Finset ι)
      (w : ↥I → (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))),
      δ' * (((k7DropMarg μ j).pi ↥Iᶜ).cexpect fun x => ∏ i : Fin k,
          restrictFix I (fun t => (w t).1 i) (f (j.succAbove i)) (fun t => x t i) *
            star (restrictFix I (fun t => (w t).2 i) (f (j.succAbove i)) (fun t => x t i))).re ≤
        δ' * (ε ^ 2 / 2) + (cstab (μ.marginalPi (j.succAbove s)) (1 - δ')
          (fun x : ↥Iᶜ → A (j.succAbove s) =>
            restrictFix I (fun t => (w t).1 s) (f (j.succAbove s)) x *
              star (restrictFix I (fun t => (w t).2 s) (f (j.succAbove s)) x))).re := by
    intro I w
    have hgb : ∀ (i : Fin k) (x : ↥Iᶜ → A (j.succAbove i)),
        ‖restrictFix I (fun t => (w t).1 i) (f (j.succAbove i)) x *
          star (restrictFix I (fun t => (w t).2 i) (f (j.succAbove i)) x)‖ ≤ 1 := by
      intro i x
      rw [norm_mul, norm_star]
      exact (mul_le_mul (hf _ _) (hf _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    refine k7p_markov hδ0 ?_ (k7p_re_cstab_nonneg _ hδ1' _) ?_ (by positivity)
    · refine k7p_norm_cexpect_le _ _ fun x => ?_
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hgb i _
    · intro hbig
      have hih := ih (fun i => A (j.succAbove i)) (k7DropMarg μ j) hno
        (k7_dropMarg_atom_bound μ j hatom) ↥Iᶜ
        (fun i x => restrictFix I (fun t => (w t).1 i) (f (j.succAbove i)) x *
          star (restrictFix I (fun t => (w t).2 i) (f (j.succAbove i)) x)) hgb hbig s
      rwa [k7_dropMarg_marginalPi] at hih
  have h2 := k7p_two_level (q := 1 - α ^ 2) (by nlinarith) (by nlinarith [sq_nonneg α])
    (fun I => ν.pi ↥I) _ _ δ' (δ' * (ε ^ 2 / 2)) key
  have hpush : ∀ I : Finset ι, ((k7NuPair j s ν).pi ↥I).cexpect (fun v =>
      cstab (μ.marginalPi (j.succAbove s)) (1 - δ')
        (fun x : ↥Iᶜ → A (j.succAbove s) =>
          restrictFix I (fun t => (v t).1) (f (j.succAbove s)) x *
            star (restrictFix I (fun t => (v t).2) (f (j.succAbove s)) x))) =
      (ν.pi ↥I).cexpect (fun w => cstab (μ.marginalPi (j.succAbove s)) (1 - δ')
        (fun x : ↥Iᶜ → A (j.succAbove s) =>
          restrictFix I (fun t => (w t).1 s) (f (j.succAbove s)) x *
            star (restrictFix I (fun t => (w t).2 s) (f (j.succAbove s)) x))) :=
    fun I => k7p_cexpect_pi_push ν (fun p => (p.1 s, p.2 s)) _
  rw [k7p_subsetExpect_congr _ (by nlinarith) _ (by nlinarith [sq_nonneg α]) hpush]
  have h3 := mul_le_mul_of_nonneg_left hst hδ0.le
  linarith

end Steps

section Xi
variable {A0 : Type} [Fintype A0] [DecidableEq A0] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- CSP_7 `lemma:kcsp#def-xi-g` (existence form): the law `ξ` on `A × A × A⁺`, `A⁺ = Option ↥(k7PairSet ν₁)`
(`⋆ = none`): with weight `1 - α²` draw `(x,x') ∼ ν₁` and output `(x,x',(x,x'))`; with weight `α²`
draw `x ∼ π`, output `(x,x,(x,x))` with probability `1 - δ'` and `(x,x,⋆)` with probability `δ'`. -/
theorem k7_exists_xi (π : FinProb A0) (ν1 : FinProb (A0 × A0)) {α δ' : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ') (hδ1 : δ' ≤ 1) :
    ∃ ξ : FinProb (A0 × A0 × Option ↥(k7PairSet ν1)),
      ∀ (x x' : A0) (ω : Option ↥(k7PairSet ν1)),
        ξ.prob (x, x', ω) =
          (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then ν1.prob (x, x') else 0) +
          α ^ 2 * (if x = x' then
            π.prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
              else if ω = none then δ' else 0) else 0) := by
  have h1 : 0 ≤ 1 - α ^ 2 := by nlinarith
  refine ⟨⟨fun p => k7pXi π ν1 α δ' p.1 p.2.1 p.2.2, fun p => ?_, ?_⟩, fun x x' ω => rfl⟩
  · refine add_nonneg (mul_nonneg h1 ?_) (mul_nonneg (sq_nonneg α) ?_) <;> split_ifs <;>
      first | exact le_rfl | exact ν1.nonneg _ | exact mul_nonneg (π.nonneg _) (by linarith)
  · show ∑ p : A0 × A0 × Option ↥(k7PairSet ν1), k7pXi π ν1 α δ' p.1 p.2.1 p.2.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    simp only [k7p_xi_sum_ω, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hν : ∑ x, ∑ x', ν1.prob (x, x') = 1 := by
      rw [← Fintype.sum_prod_type, ν1.sum_eq_one]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hν, π.sum_eq_one]
    ring

/-- TYPING: `g` is `1`-bounded when `f` is. -/
theorem k7_g_norm_le (π : FinProb A0) (f : (ι → A0) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {S : Finset (A0 × A0)} (w : ι → Option ↥S) : ‖k7G π f w‖ ≤ 1 := by
  unfold k7G
  refine k7p_norm_cexpect_le _ _ fun u => ?_
  rw [norm_mul, norm_star]
  exact (mul_le_mul (hf _) (hf _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- CSP_7 `obs:3wisexi`, with the weight `1 - α²` (the printed `I ∼_{1-α}` is a slip):
the 3-wise correlation under `ξ^{⊗ι}` of `f(x), conj f(x'), conj g(x⁺)` is the average over
`I ∼_{1-α²}` and `(z,z') ∼ ν₁^I` of `Stab_{1-δ'}((f)_{I→z} conj (f)_{I→z'})` (w.r.t. `π`). -/
theorem k7_obs_3wisexi (π : FinProb A0) (ν1 : FinProb (A0 × A0)) {α δ' : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ') (hδ1 : δ' ≤ 1)
    (ξ : FinProb (A0 × A0 × Option ↥(k7PairSet ν1)))
    (hξ : ∀ (x x' : A0) (ω : Option ↥(k7PairSet ν1)),
        ξ.prob (x, x', ω) =
          (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then ν1.prob (x, x') else 0) +
          α ^ 2 * (if x = x' then
            π.prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
              else if ω = none then δ' else 0) else 0))
    (f : (ι → A0) → ℂ) :
    (ξ.pi ι).cexpect (fun w => f (fun t => (w t).1) * star (f (fun t => (w t).2.1)) *
        star (k7G π f (fun t => (w t).2.2))) =
      subsetExpect (1 - α ^ 2) (by nlinarith) (by nlinarith [sq_nonneg α]) fun I =>
        (ν1.pi ↥I).cexpect fun v =>
          cstab π (1 - δ') (fun x : ↥Iᶜ → A0 =>
            restrictFix I (fun t => (v t).1) f x * star (restrictFix I (fun t => (v t).2) f x)) := by
  have hξ' : ∀ x x' ω, ξ.prob (x, x', ω) = k7pXi π ν1 α δ' x x' ω := hξ
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  have hα21 : α ^ 2 ≤ 1 := by nlinarith
  have hd0 : 0 ≤ 1 - δ' := by linarith
  have hd1 : 1 - δ' ≤ 1 := by linarith
  let Ψ : (A0 × A0 × Option ↥(k7PairSet ν1)) × A0 → A0 × A0 × A0 × A0 :=
    fun z => (z.1.1, z.1.2.1, k7Dec1 z.1.2.2 z.2, k7Dec2 z.1.2.2 z.2)
  let φN : A0 × A0 → A0 × A0 × A0 × A0 := fun p => (p.1, p.2, p.1, p.2)
  let φD : A0 × A0 → A0 × A0 × A0 × A0 := fun p => (p.1, p.1, p.2, p.2)
  let J := jointNoise π (1 - δ') hd0 hd1
  have hmix : ∀ q, (mergePush (k7pProd ξ π) Ψ).prob q =
      (1 - α ^ 2) * (mergePush ν1 φN).prob q + α ^ 2 * (mergePush J φD).prob q := by
    intro q
    rw [k7p_push_prob, k7p_push_prob, k7p_push_prob, Fintype.sum_prod_type]
    exact k7p_xi_test π ν1 α δ' ξ hξ' (fun r => if r = q then 1 else 0)
  let F4 : (ι → A0 × A0 × A0 × A0) → ℂ := fun q => f (fun t => (q t).1) *
    star (f (fun t => (q t).2.1)) * (star (f (fun t => (q t).2.2.1)) * f (fun t => (q t).2.2.2))
  have hL : (ξ.pi ι).cexpect (fun w => f (fun t => (w t).1) * star (f (fun t => (w t).2.1)) *
      star (k7G π f (fun t => (w t).2.2))) = ((mergePush (k7pProd ξ π) Ψ).pi ι).cexpect F4 := by
    calc (ξ.pi ι).cexpect (fun w => f (fun t => (w t).1) * star (f (fun t => (w t).2.1)) *
          star (k7G π f (fun t => (w t).2.2)))
        = (ξ.pi ι).cexpect (fun w => (π.pi ι).cexpect
            (fun u => F4 (fun t => Ψ (w t, u t)))) := by
          refine k7p_cexpect_congr _ fun w => ?_
          unfold k7G
          rw [k7p_star_cexpect, k7p_mul_cexpect]
          refine k7p_cexpect_congr _ fun u => ?_
          rw [star_mul', star_star]
      _ = ((k7pProd ξ π).pi ι).cexpect (fun z => F4 (fun t => Ψ (z t))) :=
          k7p_cexpect_pi_prod ξ π (fun w u => F4 (fun t => Ψ (w t, u t)))
      _ = ((mergePush (k7pProd ξ π) Ψ).pi ι).cexpect F4 := (k7p_cexpect_pi_push _ Ψ F4).symm
  rw [hL, mixture_calculus hα2 hα21 _ (mergePush ν1 φN) (mergePush J φD) hmix F4]
  refine k7p_subsetExpect_congr _ _ _ _ fun I => ?_
  rw [k7p_cexpect_pi_push]
  refine k7p_cexpect_congr _ fun v => ?_
  rw [k7p_cexpect_pi_push, cstab_eq_joint π (1 - δ') hd0 hd1]
  refine k7p_cexpect_congr _ fun p => ?_
  simp only [restrictFix, F4]
  have e1 : (fun t => (glueFix I (fun t => φN (v t)) (fun t => φD (p t)) t).1) = _ :=
    k7p_glue_map I (fun q : A0 × A0 × A0 × A0 => q.1) _ _
  have e2 : (fun t => (glueFix I (fun t => φN (v t)) (fun t => φD (p t)) t).2.1) = _ :=
    k7p_glue_map I (fun q : A0 × A0 × A0 × A0 => q.2.1) _ _
  have e3 : (fun t => (glueFix I (fun t => φN (v t)) (fun t => φD (p t)) t).2.2.1) = _ :=
    k7p_glue_map I (fun q : A0 × A0 × A0 × A0 => q.2.2.1) _ _
  have e4 : (fun t => (glueFix I (fun t => φN (v t)) (fun t => φD (p t)) t).2.2.2) = _ :=
    k7p_glue_map I (fun q : A0 × A0 × A0 × A0 => q.2.2.2) _ _
  rw [e1, e2, e3, e4, star_mul', star_star]

end Xi

section XiMu
variable {k : ℕ} {A : Fin (k + 1) → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- a sum over pairs whose first component has `s`-letter `x`. -/
private theorem k7p_sum_fst_s (j : Fin (k + 1)) (s : Fin k)
    (G : (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i)) → ℝ)
    (x : A (j.succAbove s)) :
    ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), G p =
      ∑ a ∈ univ.filter (fun a : ∀ i : Fin k, A (j.succAbove i) => a s = x), ∑ a', G (a, a') := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a s = x
  · simp [h]
  · simp [h]

/-- a nonzero atom of `μ_{-j,-j}` has mass `≥ α²`. -/
private theorem k7p_pairLaw_ge (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) {α : ℝ} (hα0 : 0 ≤ α)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (p : (∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i)))
    (h : (k7PairLaw μ j).prob p ≠ 0) : α ^ 2 ≤ (k7PairLaw μ j).prob p := by
  rw [k7p_pairLaw_prob] at h ⊢
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 : k7pM μ j y p.1 ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  have h2 : k7pM μ j y p.2 ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  have hm1 := k7pM_ge μ j hatom y p.1 h1
  have hm2 := k7pM_ge μ j hatom y p.2 h2
  have hn1 := k7pM_nonneg μ j y p.1
  have hle := k7p_prob_le_one (μ.marginalPi j) y
  have hpos : 0 < (μ.marginalPi j).prob y :=
    lt_of_lt_of_le (lt_of_le_of_ne hn1 (Ne.symm h1)) (k7pM_le μ j y p.1)
  have hterm : α ^ 2 ≤ k7pM μ j y p.1 * k7pM μ j y p.2 / (μ.marginalPi j).prob y := by
    rw [le_div_iff₀ hpos]
    have hmm : α * α ≤ k7pM μ j y p.1 * k7pM μ j y p.2 := mul_le_mul hm1 hm2 hα0 hn1
    nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg α)]
  exact hterm.trans (Finset.single_le_sum (f := fun y' => k7pM μ j y' p.1 * k7pM μ j y' p.2 /
    (μ.marginalPi j).prob y') (fun y' _ => div_nonneg (mul_nonneg (k7pM_nonneg μ j _ _)
      (k7pM_nonneg μ j _ _)) ((μ.marginalPi j).nonneg _)) (Finset.mem_univ y))

/-- the off-diagonal mass of `(1 - α²) ν₁` is a sum of masses of `μ_{-j,-j}`. -/
private theorem k7p_nuPair_offdiag (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α : ℝ}
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    {x x' : A (j.succAbove s)} (hxx : x ≠ x') :
    (1 - α ^ 2) * (k7NuPair j s ν).prob (x, x') =
      ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => (p.1 s, p.2 s) = (x, x')),
        (k7PairLaw μ j).prob p := by
  show (1 - α ^ 2) * ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
      (∀ i : Fin k, A (j.succAbove i)) => (p.1 s, p.2 s) = (x, x')), ν.prob p = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hp
  have hne : p.1 ≠ p.2 := fun h => hxx (by rw [← hp.1, ← hp.2, h])
  rw [hν p, k7p_diag_prob]
  simp only [hne, ite_false]
  ring

/-- off-diagonal atoms of `(1 - α²) ν₁` have mass `≥ α²`. -/
private theorem k7p_offdiag_ge (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α : ℝ}
    (hα0 : 0 ≤ α) (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    {x x' : A (j.succAbove s)} (hxx : x ≠ x')
    (h : (1 - α ^ 2) * (k7NuPair j s ν).prob (x, x') ≠ 0) :
    α ^ 2 ≤ (1 - α ^ 2) * (k7NuPair j s ν).prob (x, x') := by
  have e := k7p_nuPair_offdiag μ j s ν hν hxx
  rw [e] at h ⊢
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (k7p_pairLaw_ge μ j hα0 hatom p hne).trans
    (Finset.single_le_sum (fun q _ => (k7PairLaw μ j).nonneg q) hp)

/-- `μ_{-j,-j}(t_{-j}, t'_{-j}) > 0` for atoms `t, t'` of `μ` with `t_j = t'_j`. -/
private theorem k7p_pairLaw_pos (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (t t' : ∀ i, A i)
    (ht : μ.prob t ≠ 0) (ht' : μ.prob t' ≠ 0) (hj : t j = t' j) :
    0 < (k7PairLaw μ j).prob (k7Drop j t, k7Drop j t') := by
  have hm1 : μ.prob t ≤ k7pM μ j (t j) (k7Drop j t) :=
    Finset.single_le_sum (f := μ.prob) (fun _ _ => μ.nonneg _) (by simp)
  have hm2 : μ.prob t' ≤ k7pM μ j (t j) (k7Drop j t') :=
    Finset.single_le_sum (f := μ.prob) (fun _ _ => μ.nonneg _) (by simp [hj])
  have h1 : 0 < k7pM μ j (t j) (k7Drop j t) :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg t) (Ne.symm ht)) hm1
  have h2 : 0 < k7pM μ j (t j) (k7Drop j t') :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg t') (Ne.symm ht')) hm2
  have hpos : 0 < (μ.marginalPi j).prob (t j) := lt_of_lt_of_le h1 (k7pM_le μ j _ _)
  rw [k7p_pairLaw_prob]
  refine lt_of_lt_of_le (div_pos (mul_pos h1 h2) hpos)
    (Finset.single_le_sum (f := fun y => k7pM μ j y (k7Drop j t) * k7pM μ j y (k7Drop j t') /
      (μ.marginalPi j).prob y) (fun y _ => div_nonneg (mul_nonneg (k7pM_nonneg μ j _ _)
        (k7pM_nonneg μ j _ _)) ((μ.marginalPi j).nonneg _)) (Finset.mem_univ (t j)))

/-- the letters of `μ_{j.succAbove s}` have mass `≥ α`. -/
private theorem k7p_marg_ge (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α : ℝ}
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (hno : NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support) (y : A (j.succAbove s)) :
    α ≤ (μ.marginalPi (j.succAbove s)).prob y := by
  have := marginal_atom_ge (k7DropMarg μ j) hno (k7_dropMarg_atom_bound μ j hatom) s y
  rwa [k7_dropMarg_marginalPi] at this

/-- `∑_{x'} ν₁(x, x') = ν(z_s = x)`. -/
private theorem k7p_nuPair_sum (j : Fin (k + 1)) (s : Fin k)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (x : A (j.succAbove s)) :
    ∑ x', (k7NuPair j s ν).prob (x, x') =
      ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), ν.prob p := by
  rw [← Finset.sum_fiberwise (univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x)) (fun p => p.2 s) ν.prob]
  refine Finset.sum_congr rfl fun x' _ => ?_
  show ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
      (∀ i : Fin k, A (j.succAbove i)) => (p.1 s, p.2 s) = (x, x')), ν.prob p = _
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp [Prod.ext_iff]

/-- the `s`-marginals of `μ_{-j,-j}` and of the diagonal law are `μ_{j.succAbove s}`. -/
private theorem k7p_pair_s_marg (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k)
    (x : A (j.succAbove s)) :
    ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), (k7PairLaw μ j).prob p =
      (μ.marginalPi (j.succAbove s)).prob x ∧
    ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), (k7DiagLaw μ j).prob p =
      (μ.marginalPi (j.succAbove s)).prob x := by
  have hm : ∑ a ∈ univ.filter (fun a : ∀ i : Fin k, A (j.succAbove i) => a s = x),
      (k7DropMarg μ j).prob a = (μ.marginalPi (j.succAbove s)).prob x := by
    rw [← k7_dropMarg_marginalPi μ j s]
    rfl
  constructor
  · rw [k7p_sum_fst_s, ← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← k7p_sum_filter_fst]
    exact (k7_pairLaw_marginals μ j a).1
  · rw [k7p_sum_fst_s, ← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [k7p_diag_prob]
    rw [Finset.sum_ite_eq]
    simp

/-- TYPING: the first marginal of `ν₁` is `π` up to the weight `1 - α²` (from `hν`), hence the first
marginal of `ξ` is `π`. -/
theorem k7_xi_marginal (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α δ' : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ') (hδ1 : δ' ≤ 1)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    (ξ : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν))))
    (hξ : ∀ (x x' : A (j.succAbove s)) (ω : Option ↥(k7PairSet (k7NuPair j s ν))),
        ξ.prob (x, x', ω) =
          (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then (k7NuPair j s ν).prob (x, x')
            else 0) +
          α ^ 2 * (if x = x' then
            (μ.marginalPi (j.succAbove s)).prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
              else if ω = none then δ' else 0) else 0)) :
    ∀ x, (mergePush ξ fun p => p.1).prob x = (μ.marginalPi (j.succAbove s)).prob x := by
  intro x
  have hξ' : ∀ x x' ω, ξ.prob (x, x', ω) = k7pXi (μ.marginalPi (j.succAbove s))
      (k7NuPair j s ν) α δ' x x' ω := hξ
  have h1 : (mergePush ξ fun p => p.1).prob x =
      ∑ x', ∑ ω, ξ.prob (x, x', ω) := by
    show ∑ p ∈ univ.filter (fun p : A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν)) => p.1 = x), ξ.prob p = _
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single x]
    · simp only [ite_true]; rw [Fintype.sum_prod_type]
    · intro b _ hb; simp [hb]
    · simp
  rw [h1]
  simp only [hξ', k7p_xi_sum_ω, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [k7p_nuPair_sum]
  obtain ⟨hP, hD⟩ := k7p_pair_s_marg μ j s x
  have hsum : ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
      (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), (k7PairLaw μ j).prob p =
      α ^ 2 * ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), (k7DiagLaw μ j).prob p +
      (1 - α ^ 2) * ∑ p ∈ univ.filter (fun p : (∀ i : Fin k, A (j.succAbove i)) ×
        (∀ i : Fin k, A (j.succAbove i)) => p.1 s = x), ν.prob p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hν p
  rw [hP, hD] at hsum
  linarith

/-- CSP_7 `obs:pcxi` (with `A⁺` trimmed to the occurring pairs): `ξ` is pairwise connected; the `12` graph
uses the connectedness of the `(s, j)` graph of `μ`. -/
theorem k7_obs_pcxi (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α δ' : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ') (hδ1 : δ' < 1)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a) (hpc : PairwiseConnectedDist μ)
    (hno : NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    (ξ : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν))))
    (hξ : ∀ (x x' : A (j.succAbove s)) (ω : Option ↥(k7PairSet (k7NuPair j s ν))),
        ξ.prob (x, x', ω) =
          (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then (k7NuPair j s ν).prob (x, x')
            else 0) +
          α ^ 2 * (if x = x' then
            (μ.marginalPi (j.succAbove s)).prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
              else if ω = none then δ' else 0) else 0)) :
    PairwiseConnected3 ξ.support := by
  have hξ' := hξ
  have hπ := k7p_marg_ge μ j s hatom hno
  have hπpos : ∀ y, 0 < (μ.marginalPi (j.succAbove s)).prob y := fun y => hα0.trans_le (hπ y)
  -- `α = 1` forces a single letter
  have hsub : α = 1 → ∀ y y' : A (j.succAbove s), y = y' := by
    intro h1 y y'
    have hn := card_le_inv_of_atom_bound (k7DropMarg μ j) hno hα0
      (k7_dropMarg_atom_bound μ j hatom) s
    rw [h1, div_one] at hn
    exact Fintype.card_le_one_iff.mp (by exact_mod_cast hn) y y'
  -- the atoms
  have S1 : ∀ y, (y, y, (none : Option ↥(k7PairSet (k7NuPair j s ν)))) ∈ ξ.support := by
    intro y
    show ξ.prob _ ≠ 0
    rw [hξ]
    simp only [Option.map_none, reduceCtorEq, ite_false, ite_true, mul_zero, zero_add]
    have := hπpos y; positivity
  have S2 : ∀ q : ↥(k7PairSet (k7NuPair j s ν)), (q.1.1, q.1.2, some q) ∈ ξ.support := by
    rintro ⟨⟨a, b⟩, hmem⟩
    show ξ.prob _ ≠ 0
    rw [hξ]
    simp only [Option.map_some, ite_true]
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      have h0 := (k7NuPair j s ν).nonneg (a, a)
      have h2 : 0 ≤ 1 - α ^ 2 := by nlinarith
      have h3 : 0 < α ^ 2 * ((μ.marginalPi (j.succAbove s)).prob a * (1 - δ')) := by
        have := hπpos a; have : 0 < 1 - δ' := by linarith
        positivity
      apply ne_of_gt
      nlinarith [mul_nonneg h2 h0]
    · simp only [hab, ite_false, mul_zero, add_zero]
      have hν1 : (k7NuPair j s ν).prob (a, b) ≠ 0 :=
        (Finset.mem_filter.1 hmem).2.resolve_right hab
      exact mul_ne_zero (fun h => hab (hsub (by nlinarith) _ _)) hν1
  -- off-diagonal edges from a common `j`-letter
  have S4 : ∀ t t' : ∀ i, A i, μ.prob t ≠ 0 → μ.prob t' ≠ 0 → t j = t' j →
      t (j.succAbove s) ≠ t' (j.succAbove s) →
      ∃ ω, (t (j.succAbove s), t' (j.succAbove s), ω) ∈ ξ.support := by
    intro t t' ht ht' hj hne
    have hpos : 0 < (1 - α ^ 2) *
        (k7NuPair j s ν).prob (t (j.succAbove s), t' (j.succAbove s)) := by
      rw [k7p_nuPair_offdiag μ j s ν hν hne]
      refine lt_of_lt_of_le (k7p_pairLaw_pos μ j t t' ht ht' hj)
        (Finset.single_le_sum (fun q _ => (k7PairLaw μ j).nonneg q) ?_)
      simp [k7Drop]
    have hν1 : (k7NuPair j s ν).prob (t (j.succAbove s), t' (j.succAbove s)) ≠ 0 :=
      fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    exact ⟨_, S2 ⟨_, k7p_pairSet_mem _ hν1⟩⟩
  rw [pairwiseConnected3_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- the `12` graph, through the `(j.succAbove s, j)` graph of `μ`
    obtain ⟨x0, -⟩ := k7p_exists_support (μ.marginalPi (j.succAbove s))
    refine k7p_connected_of_reach _ (Sum.inl x0) ?_
    set G := SimpleGraph.fromRel fun (a : A (j.succAbove s) ⊕ A (j.succAbove s)) b =>
      ∃ x y z, (x, y, z) ∈ ξ.support ∧ a = Sum.inl x ∧ b = Sum.inr y with hG
    have hdiag : ∀ y, G.Adj (Sum.inl y) (Sum.inr y) :=
      fun y => k7p_fromRel_adj _ Sum.inl_ne_inr ⟨y, y, none, S1 y, rfl, rfl⟩
    have hcommon : ∀ t t' : ∀ i, A i, μ.prob t ≠ 0 → μ.prob t' ≠ 0 → t j = t' j →
        G.Reachable (Sum.inl (t (j.succAbove s))) (Sum.inl (t' (j.succAbove s))) := by
      intro t t' ht ht' hj
      by_cases hne : t (j.succAbove s) = t' (j.succAbove s)
      · rw [hne]
      · obtain ⟨ω, hω⟩ := S4 t t' ht ht' hj hne
        exact (k7p_fromRel_adj _ Sum.inl_ne_inr ⟨_, _, ω, hω, rfl, rfl⟩).reachable.trans
          (hdiag _).symm.reachable
    let P : A (j.succAbove s) ⊕ A j → Prop := Sum.elim
      (fun a => G.Reachable (Sum.inl a) (Sum.inl x0))
      (fun b => ∀ t : ∀ i, A i, μ.prob t ≠ 0 → t j = b →
        G.Reachable (Sum.inl (t (j.succAbove s))) (Sum.inl x0))
    have step : ∀ u v, (pairGraph μ.support (j.succAbove s) j).Adj u v → P v → P u := by
      intro u v huv hv
      simp only [pairGraph, SimpleGraph.fromRel_adj] at huv
      obtain ⟨-, ⟨a, b, rfl, rfl, t, ht, rfl, rfl⟩ | ⟨a, b, rfl, rfl, t, ht, rfl, rfl⟩⟩ := huv
      · exact hv t ht rfl
      · exact fun t' ht' hj => (hcommon t' t ht' ht hj).trans hv
    have key : ∀ (u v : A (j.succAbove s) ⊕ A j)
        (w : (pairGraph μ.support (j.succAbove s) j).Walk u v), P v → P u := by
      intro u v w
      induction w with
      | nil => exact id
      | cons h _ ih => exact fun hv => step _ _ h (ih hv)
    have hconn := hpc (j.succAbove s) j (Fin.succAbove_ne j s)
    have hx : ∀ x, G.Reachable (Sum.inl x) (Sum.inl x0) := fun x =>
      key _ _ (hconn.preconnected (Sum.inl x) (Sum.inl x0)).some (SimpleGraph.Reachable.refl _)
    rintro (x | y)
    · exact hx x
    · exact (hdiag y).symm.reachable.trans (hx y)
  -- the `13` and `23` graphs: every letter meets `⋆`, and `some q` meets `q.1.1` and `q.1.2`
  all_goals
    refine k7p_connected_of_reach _ (Sum.inr none) ?_
    rintro (x | _ | q)
    · exact (k7p_fromRel_adj _ Sum.inl_ne_inr ⟨x, x, none, S1 x, rfl, rfl⟩).reachable
    · exact SimpleGraph.Reachable.refl _
    · exact (k7p_fromRel_adj _ Sum.inl_ne_inr
        ⟨q.1.1, q.1.2, some q, S2 q, rfl, rfl⟩).symm.reachable.trans
          (k7p_fromRel_adj _ Sum.inl_ne_inr ⟨_, _, none, S1 _, rfl, rfl⟩).reachable

/-- CSP_7 `lemma:kcsp#xi-atom-bound`, with the corrected bound `α³ δ'` (the printed `α² δ_{k-1}` is false at
the `⋆`-atoms): every atom of `ξ` has mass `≥ α³ δ'`. -/
theorem k7_xi_atom_bound (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α δ' : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1 / 2)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (hno : NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    (ξ : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν))))
    (hξ : ∀ (x x' : A (j.succAbove s)) (ω : Option ↥(k7PairSet (k7NuPair j s ν))),
        ξ.prob (x, x', ω) =
          (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then (k7NuPair j s ν).prob (x, x')
            else 0) +
          α ^ 2 * (if x = x' then
            (μ.marginalPi (j.succAbove s)).prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
              else if ω = none then δ' else 0) else 0)) :
    ∀ p ∈ ξ.support, α ^ 3 * δ' ≤ ξ.prob p := by
  intro p hp
  obtain ⟨x, x', ω⟩ := p
  have hp' : ξ.prob (x, x', ω) ≠ 0 := hp
  have hπ := k7p_marg_ge μ j s hatom hno
  have hα2 : 0 ≤ 1 - α ^ 2 := by nlinarith
  have hα3 : 0 ≤ α ^ 3 := by positivity
  have hα4 : α ^ 3 * δ' ≤ α ^ 2 := by
    have : α ^ 3 ≤ α ^ 2 := by nlinarith [sq_nonneg α]
    nlinarith
  rw [hξ] at hp' ⊢
  rcases ω with _ | q
  · simp only [Option.map_none, reduceCtorEq, ite_false, ite_true, mul_zero, zero_add] at hp' ⊢
    by_cases hxx : x = x'
    · subst hxx
      simp only [ite_true] at hp' ⊢
      have := hπ x
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg α) hδ0.le)]
    · simp [hxx] at hp'
  · simp only [Option.map_some, Option.some.injEq, reduceCtorEq, ite_false] at hp' ⊢
    by_cases hD : x = x' ∧ q.1 = (x, x)
    · obtain ⟨rfl, hq⟩ := hD
      simp only [hq, ite_true] at hp' ⊢
      have h0 := (k7NuPair j s ν).nonneg (x, x)
      have := hπ x
      nlinarith [mul_nonneg hα2 h0, mul_le_mul_of_nonneg_left this (sq_nonneg α)]
    · have hD0 : (if x = x' then (μ.marginalPi (j.succAbove s)).prob x *
          (if q.1 = (x, x) then 1 - δ' else 0) else 0) = 0 := by
        by_cases hxx : x = x'
        · have : q.1 ≠ (x, x) := fun h => hD ⟨hxx, h⟩
          subst hxx
          simp only [this, ite_false, ite_true, mul_zero]
        · simp [hxx]
      rw [hD0, mul_zero, add_zero] at hp' ⊢
      by_cases hq : q.1 = (x, x')
      · simp only [hq, ite_true] at hp' ⊢
        have hxx : x ≠ x' := fun h => hD ⟨h, by rw [hq, h]⟩
        exact hα4.trans (k7p_offdiag_ge μ j s hα0.le hatom ν hν hxx hp')
      · simp [hq] at hp'

/-- CSP_7 `lemma:kcsp#xi-split` (construction of `ξ'`, atoms `c'_α = α²/(1+α)`, `ζ = α² δ'`, same support;
nothing depends on `f`). -/
theorem k7_xi_split (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k) {α δ' : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1 / 2)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (hno : NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support)
    (ν : FinProb ((∀ i : Fin k, A (j.succAbove i)) × (∀ i : Fin k, A (j.succAbove i))))
    (hν : ∀ p, (k7PairLaw μ j).prob p =
      α ^ 2 * (k7DiagLaw μ j).prob p + (1 - α ^ 2) * ν.prob p)
    (ξ : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν))))
    (hξ : ∀ (x x' : A (j.succAbove s)) (ω : Option ↥(k7PairSet (k7NuPair j s ν))),
        ξ.prob (x, x', ω) =
          (1 - α ^ 2) * (if ω.map Subtype.val = some (x, x') then (k7NuPair j s ν).prob (x, x')
            else 0) +
          α ^ 2 * (if x = x' then
            (μ.marginalPi (j.succAbove s)).prob x * (if ω.map Subtype.val = some (x, x) then 1 - δ'
              else if ω = none then δ' else 0) else 0)) :
    ∃ ξ' ξ'' : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
        Option ↥(k7PairSet (k7NuPair j s ν))),
      ξ'.support = ξ.support ∧ (∀ p ∈ ξ'.support, α ^ 2 / (1 + α) ≤ ξ'.prob p) ∧
        ∀ p, ξ.prob p = α ^ 2 * δ' * ξ'.prob p + (1 - α ^ 2 * δ') * ξ''.prob p := by
  have hatomξ := k7_xi_atom_bound μ j s hα0 hα1 hδ0 hδ1 hatom hno ν hν ξ hξ
  -- the support has at most `|A| + |A|²` atoms
  set N : ℝ := ((univ.filter (fun p : A (j.succAbove s) × A (j.succAbove s) ×
    Option ↥(k7PairSet (k7NuPair j s ν)) => ¬ ξ.prob p = 0)).card : ℝ) with hN
  have hcard : N ≤ (Fintype.card (A (j.succAbove s)) : ℝ) +
      (Fintype.card (A (j.succAbove s)) : ℝ) * (Fintype.card (A (j.succAbove s)) : ℝ) := by
    let g : A (j.succAbove s) ⊕ ↥(k7PairSet (k7NuPair j s ν)) → A (j.succAbove s) ×
        A (j.succAbove s) × Option ↥(k7PairSet (k7NuPair j s ν)) :=
      Sum.elim (fun x => (x, x, none)) (fun q => (q.1.1, q.1.2, some q))
    have hsub : univ.filter (fun p : A (j.succAbove s) × A (j.succAbove s) ×
        Option ↥(k7PairSet (k7NuPair j s ν)) => ¬ ξ.prob p = 0) ⊆ univ.image g := by
      rintro ⟨x, x', ω⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [hξ] at hp
      rw [Finset.mem_image]
      rcases ω with _ | q
      · simp only [Option.map_none, reduceCtorEq, ite_false, ite_true, mul_zero, zero_add] at hp
        by_cases hxx : x = x'
        · subst hxx; exact ⟨Sum.inl x, Finset.mem_univ _, rfl⟩
        · simp [hxx] at hp
      · by_cases hq : q.1 = (x, x')
        · exact ⟨Sum.inr q, Finset.mem_univ _, by simp [g, hq]⟩
        · exfalso; apply hp
          simp only [Option.map_some, Option.some.injEq, hq, ite_false, mul_zero, zero_add]
          by_cases hxx : x = x'
          · subst hxx; simp [hq]
          · simp [hxx]
    have h5 : Fintype.card ↥(k7PairSet (k7NuPair j s ν)) ≤
        Fintype.card (A (j.succAbove s)) * Fintype.card (A (j.succAbove s)) := by
      rw [Fintype.card_coe, ← Fintype.card_prod]; exact Finset.card_le_univ _
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_sum] at this
    rw [hN]; exact_mod_cast this.trans (Nat.add_le_add_left h5 _)
  have hn := card_le_inv_of_atom_bound (k7DropMarg μ j) hno hα0
    (k7_dropMarg_atom_bound μ j hatom) s
  have hnα : (Fintype.card (A (j.succAbove s)) : ℝ) * α ≤ 1 := (le_div_iff₀ hα0).1 hn
  have hn0 : (0 : ℝ) ≤ Fintype.card (A (j.succAbove s)) := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := by rw [hN]; exact Nat.cast_nonneg _
  set c : ℝ := α ^ 2 / (1 + α) with hc
  have hc0 : 0 < c := by positivity
  have hcα : c * (1 + α) = α ^ 2 := by rw [hc]; field_simp
  have hNc : N * c ≤ 1 := by
    have h1 : N * α ^ 2 ≤ 1 + α := by
      have := mul_le_mul_of_nonneg_right hcard (sq_nonneg α)
      nlinarith [mul_le_mul_of_nonneg_left hnα hα0.le, mul_le_mul hnα hnα
        (mul_nonneg hn0 hα0.le) zero_le_one]
    have h2 : N * c * (1 + α) ≤ 1 * (1 + α) := by
      rw [mul_assoc, hcα, one_mul]; exact h1
    exact le_of_mul_le_mul_right h2 (by linarith)
  set t : ℝ := 1 - N * c with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by nlinarith
  have hζ : α ^ 2 * δ' ≤ 1 / 2 := by nlinarith
  have hζ0 : 0 < α ^ 2 * δ' := by positivity
  -- `ξ'`
  let ξ' : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν))) :=
    { prob := fun p => if ξ.prob p = 0 then 0 else c + t * ξ.prob p
      nonneg := fun p => by
        split_ifs
        · exact le_rfl
        · exact add_nonneg hc0.le (mul_nonneg ht0 (ξ.nonneg p))
      sum_eq_one := by
        have hpt : ∀ p, (if ξ.prob p = 0 then 0 else c + t * ξ.prob p) =
            (if ξ.prob p = 0 then 0 else c) + t * ξ.prob p := fun p => by
          split_ifs with h <;> simp [h]
        rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_add_distrib, ← Finset.mul_sum,
          ξ.sum_eq_one, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
          nsmul_eq_mul, ← hN, ht]
        ring }
  have hξ'p : ∀ p, ξ'.prob p = if ξ.prob p = 0 then 0 else c + t * ξ.prob p := fun p => rfl
  have hle : ∀ p, α ^ 2 * δ' * ξ'.prob p ≤ ξ.prob p := by
    intro p
    rw [hξ'p]
    split_ifs with h
    · rw [h]; simp
    · have hpa := hatomξ p h
      have hkey : c ≤ (1 - α ^ 2 * δ') * α := by
        rw [hc, div_le_iff₀ (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hδ1
          (mul_nonneg (sq_nonneg α) (by linarith : (0:ℝ) ≤ 1 + α)),
          mul_le_mul_of_nonneg_left hα1 (sq_nonneg α)]
      have h1 := mul_le_mul_of_nonneg_left hkey hζ0.le
      have h2 := mul_le_mul_of_nonneg_left hpa (by linarith : (0:ℝ) ≤ 1 - α ^ 2 * δ')
      have h3 : 0 ≤ α ^ 2 * δ' * (1 - t) * ξ.prob p :=
        mul_nonneg (mul_nonneg hζ0.le (by linarith)) (ξ.nonneg p)
      nlinarith
  let ξ'' : FinProb (A (j.succAbove s) × A (j.succAbove s) ×
      Option ↥(k7PairSet (k7NuPair j s ν))) :=
    { prob := fun p => (ξ.prob p - α ^ 2 * δ' * ξ'.prob p) / (1 - α ^ 2 * δ')
      nonneg := fun p => div_nonneg (by linarith [hle p]) (by linarith)
      sum_eq_one := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ξ.sum_eq_one,
          ξ'.sum_eq_one, mul_one, div_self (by linarith)] }
  refine ⟨ξ', ξ'', ?_, ?_, ?_⟩
  · ext p
    simp only [FinProb.support, Set.mem_ofPred_eq, hξ'p]
    split_ifs with h
    · simp [h]
    · exact ⟨fun _ => h, fun _ => by have := mul_nonneg ht0 (ξ.nonneg p); linarith⟩
  · intro p hp
    have hp' : ξ'.prob p ≠ 0 := hp
    rw [hξ'p] at hp' ⊢
    split_ifs with h
    · simp [h] at hp'
    · have := mul_nonneg ht0 (ξ.nonneg p); linarith
  · intro p
    show ξ.prob p = α ^ 2 * δ' * ξ'.prob p +
      (1 - α ^ 2 * δ') * ((ξ.prob p - α ^ 2 * δ' * ξ'.prob p) / (1 - α ^ 2 * δ'))
    rw [mul_div_cancel₀ _ (by linarith)]
    ring

end XiMu

end TrackB
end RestrictedPolynomials
end
