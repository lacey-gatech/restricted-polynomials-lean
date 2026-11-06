module

public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import RestrictedPolynomials.Frozen.FinProbSupport
public import RestrictedPolynomials.Defs

/-!
# Track B, `K7KcspUnif`: the uniform law on the support

Source: Supplement H, section
`sec:unif`, `lem:unif` (l. 281-295): for a law `μ` with atoms `≥ α` on `S = supp μ` and no nontrivial
Abelian embedding, `μ̂ = Unif(S)` has `|S| ≤ 1/α` (a), atoms `1/|S| ≥ α` and the same support (b),
every letter occurs (c), rational marginals `μ̂_i(a) = n^i_a/|S|` with `1 ≤ n^i_a ≤ |S|` (d), and
`μ = λ μ̂ + (1-λ) μ''` with `λ = α|S|` (e). This material is split off `K7KcspReduce`.

`k7SuppSize` and `k7UnifSupp` are data (with complete mass proof); every other declaration is a
theorem. Private helpers carry the prefix `k7un_`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Unif
variable {α : Type} [Fintype α]

open scoped Classical in
/-- `|S|`, `S = supp μ` (as a number). -/
def k7SuppSize (μ : FinProb α) : ℕ := (univ.filter fun a => μ.prob a ≠ 0).card

open scoped Classical in
/-- `μ̂ = Unif(supp μ)` (Supplement H, `lem:unif`); the mass proof is complete. -/
def k7UnifSupp (μ : FinProb α) : FinProb α where
  prob a := if μ.prob a ≠ 0 then 1 / (k7SuppSize μ : ℝ) else 0
  nonneg a := by
    split_ifs
    · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    · exact le_rfl
  sum_eq_one := by
    have hne : (univ.filter fun a => μ.prob a ≠ 0).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      have : ∑ a, μ.prob a = 0 := Finset.sum_eq_zero fun a ha => by simpa using h ha
      rw [μ.sum_eq_one] at this
      exact one_ne_zero this
    have hN : (k7SuppSize μ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hne)
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    unfold k7SuppSize at hN ⊢
    field_simp

/-- characterisation of `k7UnifSupp`. -/
theorem k7UnifSupp_prob (μ : FinProb α) (a : α) :
    (k7UnifSupp μ).prob a = if μ.prob a ≠ 0 then 1 / (k7SuppSize μ : ℝ) else 0 := by
  rfl

/-! ### Private helpers -/

/-- a law has a point of positive mass. -/
private theorem k7un_exists_ne (μ : FinProb α) : ∃ a, μ.prob a ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := μ.sum_eq_one
  simp [h] at h1

/-- `|S| > 0` as soon as one point has positive mass. -/
private theorem k7un_suppSize_pos (μ : FinProb α) {a : α} (ha : μ.prob a ≠ 0) :
    0 < k7SuppSize μ := by
  unfold k7SuppSize
  exact Finset.card_pos.2 ⟨a, by simp [ha]⟩

/-- the total mass is carried by the support: `Σ_{a ∈ S} μ(a) = 1`. -/
private theorem k7un_sum_filter (μ : FinProb α) :
    ∑ a ∈ univ.filter (fun a => μ.prob a ≠ 0), μ.prob a = 1 := by
  rw [Finset.sum_filter_ne_zero, μ.sum_eq_one]

/-- `|S|` as the cardinality of the filter (decidability instances aside). -/
private theorem k7un_card_filter (μ : FinProb α) :
    ((univ.filter fun a => μ.prob a ≠ 0).card : ℝ) = (k7SuppSize μ : ℝ) := by
  unfold k7SuppSize
  congr 2

/-- a law that is uniform on its support is `k7UnifSupp` of itself. -/
private theorem k7un_eq_unifSupp (ν : FinProb α)
    (hunif : ∀ a ∈ ν.support, ∀ b ∈ ν.support, ν.prob a = ν.prob b) (t : α) :
    ν.prob t = (k7UnifSupp ν).prob t := by
  obtain ⟨t0, ht0⟩ := k7un_exists_ne ν
  have hconst : ∀ t ∈ univ.filter (fun a => ν.prob a ≠ 0), ν.prob t = ν.prob t0 :=
    fun t ht => hunif t (Finset.mem_filter.1 ht).2 t0 ht0
  have hsum := k7un_sum_filter ν
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, k7un_card_filter] at hsum
  have hN : (k7SuppSize ν : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsum
    exact zero_ne_one hsum
  rw [k7UnifSupp_prob]
  by_cases h : ν.prob t = 0
  · simp [h]
  · simp only [ne_eq, h, not_false_eq_true, ite_true]
    rw [hunif t h t0 ht0]
    field_simp
    linarith

/-! ### `lem:unif` -/

/-- `lem:unif` (b): `supp μ̂ = supp μ`. -/
theorem k7_unifSupp_support (μ : FinProb α) : (k7UnifSupp μ).support = μ.support := by
  ext a
  show (k7UnifSupp μ).prob a ≠ 0 ↔ μ.prob a ≠ 0
  rw [k7UnifSupp_prob]
  by_cases h : μ.prob a = 0
  · simp [h]
  · have hN : (k7SuppSize μ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (k7un_suppSize_pos μ h).ne'
    simp [h, hN]

/-- `|supp μ̂| = |supp μ|`. -/
theorem k7_suppSize_unifSupp (μ : FinProb α) : k7SuppSize (k7UnifSupp μ) = k7SuppSize μ := by
  have h : ∀ a, (k7UnifSupp μ).prob a ≠ 0 ↔ μ.prob a ≠ 0 := fun a =>
    Set.ext_iff.1 (k7_unifSupp_support μ) a
  unfold k7SuppSize
  congr 1
  exact Finset.filter_congr fun a _ => h a

/-- `μ̂` is uniform on its support. -/
theorem k7_unifSupp_unif (μ : FinProb α) :
    ∀ a ∈ (k7UnifSupp μ).support, ∀ b ∈ (k7UnifSupp μ).support,
      (k7UnifSupp μ).prob a = (k7UnifSupp μ).prob b := by
  intro a ha b hb
  rw [k7_unifSupp_support] at ha hb
  have ha' : μ.prob a ≠ 0 := ha
  have hb' : μ.prob b ≠ 0 := hb
  simp only [k7UnifSupp_prob, ne_eq, ha', hb', not_false_eq_true, ite_true]

/-- `lem:unif` (a): atoms `≥ α` on the support give `|S| ≤ 1/α`. -/
theorem k7_suppSize_le {a₀ : ℝ} (ha₀ : 0 < a₀) (μ : FinProb α)
    (hatom : ∀ a ∈ μ.support, a₀ ≤ μ.prob a) : (k7SuppSize μ : ℝ) ≤ 1 / a₀ := by
  rw [le_div_iff₀ ha₀]
  have h1 : ∑ a ∈ univ.filter (fun a => μ.prob a ≠ 0), a₀ ≤
      ∑ a ∈ univ.filter (fun a => μ.prob a ≠ 0), μ.prob a :=
    Finset.sum_le_sum fun a ha => hatom a (Finset.mem_filter.1 ha).2
  rw [k7un_sum_filter, Finset.sum_const, nsmul_eq_mul, k7un_card_filter] at h1
  exact h1

/-- `lem:unif` (b): the atoms of `μ̂` are `1/|S| ≥ α`. -/
theorem k7_unifSupp_atom {a₀ : ℝ} (ha₀ : 0 < a₀) (μ : FinProb α)
    (hatom : ∀ a ∈ μ.support, a₀ ≤ μ.prob a) :
    ∀ a ∈ (k7UnifSupp μ).support, a₀ ≤ (k7UnifSupp μ).prob a := by
  intro a ha
  rw [k7_unifSupp_support] at ha
  have ha' : μ.prob a ≠ 0 := ha
  simp only [k7UnifSupp_prob, ne_eq, ha', not_false_eq_true, ite_true]
  have hN : (0 : ℝ) < k7SuppSize μ := by exact_mod_cast k7un_suppSize_pos μ ha'
  have hle := k7_suppSize_le ha₀ μ hatom
  rw [le_div_iff₀ ha₀] at hle
  rw [le_div_iff₀ hN]
  linarith

/-- `lem:unif` (e): with `λ = α |S| ∈ (0, 1]`, `μ = λ μ̂ + (1-λ) μ''` for a law `μ''`
(`μ'' = (μ - α 1_S)/(1-λ)`; if `λ = 1` then `μ = μ̂` and `μ'' := μ̂`). -/
theorem k7_unifSupp_decomp {a₀ : ℝ} (ha₀ : 0 < a₀) (μ : FinProb α)
    (hatom : ∀ a ∈ μ.support, a₀ ≤ μ.prob a) :
    0 < a₀ * (k7SuppSize μ : ℝ) ∧ a₀ * (k7SuppSize μ : ℝ) ≤ 1 ∧
      ∃ μ2 : FinProb α, ∀ a, μ.prob a =
        a₀ * (k7SuppSize μ : ℝ) * (k7UnifSupp μ).prob a +
          (1 - a₀ * (k7SuppSize μ : ℝ)) * μ2.prob a := by
  obtain ⟨a1, ha1⟩ := k7un_exists_ne μ
  have hNpos : (0 : ℝ) < k7SuppSize μ := by exact_mod_cast k7un_suppSize_pos μ ha1
  have hle : a₀ * (k7SuppSize μ : ℝ) ≤ 1 := by
    have h := k7_suppSize_le ha₀ μ hatom
    rw [le_div_iff₀ ha₀] at h
    linarith
  -- `λ μ̂ = α 1_S`
  have hlamU : ∀ a, a₀ * (k7SuppSize μ : ℝ) * (k7UnifSupp μ).prob a =
      if μ.prob a ≠ 0 then a₀ else 0 := by
    intro a
    rw [k7UnifSupp_prob]
    split_ifs
    · field_simp
    · simp
  -- the remainder `r = μ - α 1_S ≥ 0` has mass `1 - λ`
  have hr0 : ∀ a, 0 ≤ μ.prob a - (if μ.prob a ≠ 0 then a₀ else 0) := by
    intro a
    split_ifs with h
    · exact sub_nonneg.2 (hatom a h)
    · simpa using μ.nonneg a
  have hrsum : ∑ a, (μ.prob a - (if μ.prob a ≠ 0 then a₀ else 0)) =
      1 - a₀ * (k7SuppSize μ : ℝ) := by
    rw [Finset.sum_sub_distrib, μ.sum_eq_one, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      k7un_card_filter]
    ring
  refine ⟨mul_pos ha₀ hNpos, hle, ?_⟩
  rcases hle.lt_or_eq with hlt | heq
  · have hne : (1 - a₀ * (k7SuppSize μ : ℝ)) ≠ 0 := by linarith
    refine ⟨⟨fun a => (μ.prob a - (if μ.prob a ≠ 0 then a₀ else 0)) /
      (1 - a₀ * (k7SuppSize μ : ℝ)), fun a => div_nonneg (hr0 a) (by linarith), ?_⟩, fun a => ?_⟩
    · simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, hrsum, mul_inv_cancel₀ hne]
    · show μ.prob a = a₀ * (k7SuppSize μ : ℝ) * (k7UnifSupp μ).prob a +
        (1 - a₀ * (k7SuppSize μ : ℝ)) * ((μ.prob a - (if μ.prob a ≠ 0 then a₀ else 0)) /
          (1 - a₀ * (k7SuppSize μ : ℝ)))
      rw [hlamU a, mul_div_cancel₀ _ hne]
      ring
  · refine ⟨μ, fun a => ?_⟩
    have hz : ∑ a, (μ.prob a - (if μ.prob a ≠ 0 then a₀ else 0)) = 0 := by
      rw [hrsum, heq, sub_self]
    have hra := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hr0 a)).1 hz a (Finset.mem_univ a)
    rw [hlamU a, heq]
    linarith

end Unif

section UnifMarg
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- `lem:unif` (c), (d): for a law `ν` uniform on its support `S` without nontrivial Abelian
embedding, every marginal is `ν_i(a) = n^i_a / |S|` with `1 ≤ n^i_a ≤ |S|` (`full_marginal_support`).
With `|S| ≤ 1/α` (`k7_suppSize_le`) this is `Rat(ν_i, α)` with `M = |S|`, for EVERY coordinate. -/
theorem k7_unif_marginal_counts (ν : FinProb (∀ i, A i))
    (hno : NoNontrivialAbelianEmbeddingPi ν.support)
    (hunif : ∀ a ∈ ν.support, ∀ b ∈ ν.support, ν.prob a = ν.prob b) (i : Fin k) :
    ∃ n : A i → ℕ, (∀ a, 1 ≤ n a ∧ n a ≤ k7SuppSize ν) ∧
      ∀ a, (ν.marginalPi i).prob a = (n a : ℝ) / k7SuppSize ν := by
  have hν : ∀ t, ν.prob t = if ν.prob t ≠ 0 then 1 / (k7SuppSize ν : ℝ) else 0 := fun t =>
    (k7un_eq_unifSupp ν hunif t).trans (k7UnifSupp_prob ν t)
  refine ⟨fun a => ((univ.filter fun t : (∀ i, A i) => t i = a).filter
    fun t => ν.prob t ≠ 0).card, fun a => ⟨?_, ?_⟩, fun a => ?_⟩
  · have hpos := full_marginal_support ν hno i a
    have hpos' : 0 < ∑ t ∈ univ.filter (fun t : (∀ i, A i) => t i = a), ν.prob t := hpos
    obtain ⟨t, ht, htp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos'.ne'
    exact Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨ht, htp⟩⟩
  · unfold k7SuppSize
    refine Finset.card_le_card fun t ht => ?_
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ t, ht.2⟩
  · show ∑ t ∈ univ.filter (fun t : (∀ i, A i) => t i = a), ν.prob t = _
    rw [Finset.sum_congr rfl fun t _ => hν t, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    ring

/-- marginals of a mixture: `μ = λ π̂ + (1-λ) μ''` gives `μ_i = λ π̂_i + (1-λ) μ''_i`. -/
theorem k7_marginal_mix (μ πh μ2 : FinProb (∀ i, A i)) {lam : ℝ}
    (hmix : ∀ a, μ.prob a = lam * πh.prob a + (1 - lam) * μ2.prob a) (i : Fin k) (x : A i) :
    (μ.marginalPi i).prob x =
      lam * (πh.marginalPi i).prob x + (1 - lam) * (μ2.marginalPi i).prob x := by
  simp only [FinProb.marginalPi, hmix, Finset.sum_add_distrib, Finset.mul_sum]

end UnifMarg

end TrackB
end RestrictedPolynomials
end
