module

public import RestrictedPolynomials.TrackB.MaxTInduct

/-!
# Track B: the CSP_7 base case `k = 3`
(CSP_7 `thm:3csp-bkm2` and its step `#from-B4-10.2`, l. 452-458)

`k7_thm_3csp_bkm2_of_Q` is conditional on `hQ` (`Q` of every pattern in `𝒯`), hence the `_of_Q`
name. It has no alphabet bound `m`, no `card ≤ m` hypothesis and no
`PairwiseConnected3`: the alphabet bound is derived from the atom bound and the no-embedding
hypothesis (`card_le_inv_of_atom_bound`, applied to the pushforward of `μ` to `∀ i, Tri X Y Z i`),
and pairwise connectedness from `pairwiseConnected_of_noNontrivialAbelianEmbeddingPi` (CSP_7 `obs:pc`).
All proof helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Base
variable {X Y Z : Type}

private instance triFintypeK7 (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (i : Fin 3) :
    Fintype (Tri X Y Z i) :=
  match i with
  | 0 => (inferInstance : Fintype X)
  | 1 => (inferInstance : Fintype Y)
  | 2 => (inferInstance : Fintype Z)

private instance triDecEqK7 (X Y Z : Type) [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (i : Fin 3) : DecidableEq (Tri X Y Z i) :=
  match i with
  | 0 => (inferInstance : DecidableEq X)
  | 1 => (inferInstance : DecidableEq Y)
  | 2 => (inferInstance : DecidableEq Z)

private theorem ofProd_injK7 : Function.Injective (Tri.ofProd : X × Y × Z → ∀ i, Tri X Y Z i) := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  exact Prod.ext h0 (Prod.ext h1 h2)

private theorem push_ofProd_probK7 [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) (p : X × Y × Z) :
    (mergePush μ (Tri.ofProd : X × Y × Z → ∀ i, Tri X Y Z i)).prob (Tri.ofProd p) = μ.prob p := by
  classical
  show ∑ a ∈ univ.filter (fun a => Tri.ofProd a = Tri.ofProd p), μ.prob a = _
  rw [Finset.filter_congr (q := fun a => a = p) (fun a _ => ofProd_injK7.eq_iff)]
  rw [Finset.filter_eq' univ p, if_pos (Finset.mem_univ p), Finset.sum_singleton]

private theorem push_ofProd_supportK7 [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) :
    (mergePush μ (Tri.ofProd : X × Y × Z → ∀ i, Tri X Y Z i)).support = Tri.ofProd '' μ.support := by
  ext q
  show (∑ a ∈ Finset.univ.filter (fun a => Tri.ofProd a = q), μ.prob a) ≠ 0 ↔ _
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun a _ => μ.nonneg a]
  push Not
  constructor
  · rintro ⟨a, ha, hne⟩
    exact ⟨a, hne, (Finset.mem_filter.1 ha).2⟩
  · rintro ⟨a, hne, hfa⟩
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfa⟩, hne⟩

/-- the alphabet bounds and pairwise connectedness from the no-embedding hypothesis and the atom
bound: `InT`, and `card ≤ ⌈1/α⌉`. -/
private theorem derive_InT_card_K7 [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) {α : ℝ} (hα : 0 < α)
    (hat : ∀ p ∈ μ.support, α ≤ μ.prob p) (hna : ¬ AdmitsAbelianEmbedding3 μ.support) :
    InT μ.support ∧ Fintype.card X ≤ ⌈1 / α⌉₊ ∧ Fintype.card Y ≤ ⌈1 / α⌉₊ ∧
      Fintype.card Z ≤ ⌈1 / α⌉₊ := by
  classical
  set ν := mergePush μ (Tri.ofProd : X × Y × Z → ∀ i, Tri X Y Z i) with hν
  have hsupp : ν.support = Tri.ofProd '' μ.support := push_ofProd_supportK7 μ
  have hno : NoNontrivialAbelianEmbeddingPi ν.support := by
    rw [hsupp]; exact (noNontrivialAbelianEmbeddingPi_iff_3 _).2 hna
  have hatν : ∀ q ∈ ν.support, α ≤ ν.prob q := by
    intro q hq
    rw [hsupp] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [hν, push_ofProd_probK7]; exact hat p hp
  have hpc := pairwiseConnected_of_noNontrivialAbelianEmbeddingPi ν hno
  have hpc3 : PairwiseConnected3 μ.support := by
    unfold PairwiseConnected3
    rw [← hsupp]; exact hpc
  have hc : ∀ i : Fin 3, (Fintype.card (Tri X Y Z i) : ℝ) ≤ 1 / α :=
    fun i => card_le_inv_of_atom_bound ν hno hα hatν i
  have hcn : ∀ n : ℕ, (n : ℝ) ≤ 1 / α → n ≤ ⌈1 / α⌉₊ := fun n hn =>
    Nat.cast_le.1 (hn.trans (Nat.le_ceil _))
  exact ⟨⟨hpc3, hna⟩, hcn _ (hc 0), hcn _ (hc 1), hcn _ (hc 2)⟩

/-- CSP_7 `thm:3csp-bkm2` (the base case `k = 3`), via `thm:3csp-bkm2#from-B4-10.2`: the
conclusion of `thm_10_2_at_H0_of_Q`-type input (`hQ`: `Q` of every pattern in `𝒯`, the hypothesis of
`maxT_uniform_of_Q`) in CSP_7's form `∀ ε ∃ δ`: `|𝔼 f g h| ≥ ε ⇒ Stab_{1-δ}(·) ≥ δ` in all three slots.
As in the source, there is no alphabet bound and no pairwise-connectedness hypothesis;
both are derived inside the proof. -/
theorem k7_thm_3csp_bkm2_of_Q
    (hQ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → QSet S)
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z] (μ : FinProb (X × Y × Z)), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖corr3 μ f g h‖ →
            δ ≤ (cstab (lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (lawZ μ) (1 - δ) h).re := by
  obtain ⟨M, δ₀, η, hM, hδ₀, hδ₁, hη, H⟩ := maxT_uniform_of_Q hQ ⌈1 / α⌉₊ hα
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  set t : ℝ := (ε / (2 * M)) ^ (1 / η) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos (div_pos hε (by positivity)) _
  have htη : t ^ η = ε / (2 * M) := by
    rw [ht, ← Real.rpow_mul (div_pos hε (by positivity)).le, one_div_mul_cancel hη.ne',
      Real.rpow_one]
  refine ⟨min δ₀ t, lt_min hδ₀ htpos, (min_le_left _ _).trans hδ₁, ?_⟩
  intro X Y Z _ _ _ _ _ _ μ hat hna δ hδ hδle n f g h hf hg hh hε'
  obtain ⟨hInT, hX, hY, hZ⟩ := derive_InT_card_K7 μ hα hat hna
  have hP := H X Y Z hX hY hZ μ hInT hat
  have hδ₀' : δ ≤ δ₀ := hδle.trans (min_le_left _ _)
  have hδt : δ ≤ t := hδle.trans (min_le_right _ _)
  have hbound : M * δ ^ η < ε := by
    have h1 : δ ^ η ≤ t ^ η := Real.rpow_le_rpow hδ.le hδt hη.le
    rw [htη] at h1
    have h2 : M * δ ^ η ≤ M * (ε / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM0.le
    have h3 : M * (ε / (2 * M)) = ε / 2 := by field_simp
    linarith
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    have := hP.1 δ hδ hδ₀' n f g h hf hg hh (not_le.1 hc).le
    linarith
  · by_contra hc
    have := hP.2.1 δ hδ hδ₀' n f g h hf hg hh (not_le.1 hc).le
    linarith
  · by_contra hc
    have := hP.2.2 δ hδ hδ₀' n f g h hf hg hh (not_le.1 hc).le
    linarith

end Base

/-- Explicit companion of `k7_thm_3csp_bkm2_of_Q`: the same proof gives the
quantitative base case `δ ≤ c ε^b` with `b = 1/η` and `c = min δ₀ (1/(2M))^{1/η}`, constants depending on
`(m, α)` only. Its conclusion is the hypothesis `hbase` of the assembly. -/
theorem k7_hbase_explicit_of_Q
    (hQ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → QSet S) :
    ∀ (m : ℕ) {α : ℝ}, 0 < α → ∃ (b c : ℝ), 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
          [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
          ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ c * ε ^ b →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖MaxT.corr3 μ f g h‖ →
            δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re := by
  intro m α hα
  obtain ⟨M, δ₀, η, hM, hδ₀, hδ₁, hη, H⟩ := maxT_uniform_of_Q hQ m hα
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  set s : ℝ := (1 / (2 * M)) ^ (1 / η) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  have hs1 : s ≤ 1 := Real.rpow_le_one (by positivity) (by
    rw [div_le_one (by positivity)]; linarith) (by positivity)
  refine ⟨1 / η, min δ₀ s, by positivity, lt_min hδ₀ hspos, (min_le_left _ _).trans hδ₁, ?_⟩
  intro ε hε hε1 X Y Z _ _ _ _ _ _ hX hY hZ μ hat hpc hna δ hδ hδle n f g h hf hg hh hε'
  have hP := H X Y Z hX hY hZ μ ⟨hpc, hna⟩ hat
  have hεb : ε ^ (1 / η) ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
  have hδ₀' : δ ≤ δ₀ := by
    calc δ ≤ min δ₀ s * ε ^ (1 / η) := hδle
      _ ≤ min δ₀ s * 1 := mul_le_mul_of_nonneg_left hεb (le_min hδ₀.le hspos.le)
      _ ≤ δ₀ := by rw [mul_one]; exact min_le_left _ _
  have hδt : δ ≤ s * ε ^ (1 / η) := hδle.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hbound : M * δ ^ η < ε := by
    have h1 : δ ^ η ≤ (s * ε ^ (1 / η)) ^ η := Real.rpow_le_rpow hδ.le hδt hη.le
    have h2 : (s * ε ^ (1 / η)) ^ η = ε / (2 * M) := by
      rw [Real.mul_rpow hspos.le (by positivity), hs, ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul hε.le, one_div_mul_cancel hη.ne', Real.rpow_one, Real.rpow_one]
      field_simp
    rw [h2] at h1
    have h3 : M * δ ^ η ≤ M * (ε / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM0.le
    have h4 : M * (ε / (2 * M)) = ε / 2 := by field_simp
    linarith
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    have := hP.1 δ hδ hδ₀' n f g h hf hg hh (not_le.1 hc).le
    linarith
  · by_contra hc
    have := hP.2.1 δ hδ hδ₀' n f g h hf hg hh (not_le.1 hc).le
    linarith
  · by_contra hc
    have := hP.2.2 δ hδ hδ₀' n f g h hf hg hh (not_le.1 hc).le
    linarith

end MaxT
end TrackB
end RestrictedPolynomials
end
