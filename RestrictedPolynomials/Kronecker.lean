import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kronecker's theorem and the infinite matrix (Lemmas 5.2 and 5.4)

* `abv_le_one_of_relation` : if `∑_j c_j θ^{y^{j+1}} = C` for every `y ≥ 2`, with `c ≠ 0`, then
  `|θ|_v ≤ 1` for every absolute value `v`. This is the case `|θ|_v > 1` of the proof of
  Lemma 5.4; the triangle inequality is the only property of `v` that is used.
* `pow_eq_one_of_relation` : **Lemma 5.4**. If `θ ≠ 0` lies in a number field and
  `∑_j c_j (θ^{y^{j+1}} - 1) = 0` for every `y ≥ 2`, with `c ≠ 0`, then `θ` is a root of unity.
  By the first item at the finite places `θ` is an algebraic integer (Lemma 5.2), and at the
  infinite places every conjugate of `θ` lies in the closed unit disk; Kronecker's theorem
  concludes. (With the closed-disk form of Kronecker's theorem, the case `|θ|_v < 1` of the
  paper is not needed.)
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- The growth estimate in the proof of Lemma 5.4. -/
theorem abv_le_one_of_relation {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {ℓ : ℕ} {θ C : K}
    (c : Fin ℓ → K) (hc : c ≠ 0)
    (hrel : ∀ y : ℕ, 2 ≤ y → ∑ j, c j * θ ^ (y ^ ((j : ℕ) + 1)) = C) : v θ ≤ 1 := by
  classical
  by_contra! ht
  set t := v θ with htdef
  have ht0 : 0 < t := lt_trans one_pos ht
  -- the largest index `j₊` with `c_{j₊} ≠ 0`
  have hne : (univ.filter fun j => c j ≠ 0).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    exact hc (funext fun j => by simpa using h (mem_univ j))
  set jp := (univ.filter fun j => c j ≠ 0).max' hne with hjp
  have hcjp : c jp ≠ 0 := (mem_filter.1 (max'_mem _ hne)).2
  have hgt : ∀ j, jp < j → c j = 0 := by
    intro j hj
    by_contra h
    exact absurd (le_max' _ j (mem_filter.2 ⟨mem_univ _, h⟩)) (not_le.2 hj)
  have hvc : 0 < v (c jp) := v.pos hcjp
  set B := v C + ∑ j, v (c j) with hB
  -- the key inequality `|c_{j₊}| t^{y^{j₊+1}} ≤ B t^{y^{j₊}}`
  have key : ∀ y : ℕ, 2 ≤ y →
      v (c jp) * t ^ (y ^ ((jp : ℕ) + 1)) ≤ B * t ^ (y ^ (jp : ℕ)) := by
    intro y hy
    have hy1 : 1 ≤ y := by omega
    have hrest : c jp * θ ^ (y ^ ((jp : ℕ) + 1)) =
        C - ∑ j ∈ univ.erase jp, c j * θ ^ (y ^ ((j : ℕ) + 1)) := by
      rw [← hrel y hy, ← add_sum_erase _ _ (mem_univ jp)]
      ring
    have hT1 : 1 ≤ t ^ (y ^ (jp : ℕ)) := one_le_pow₀ ht.le
    have hterm : ∀ j ∈ univ.erase jp, v (c j * θ ^ (y ^ ((j : ℕ) + 1))) ≤
        v (c j) * t ^ (y ^ (jp : ℕ)) := by
      intro j hj
      rw [map_mul, map_pow]
      by_cases hcj : c j = 0
      · simp [hcj]
      · have hjlt : j < jp := lt_of_le_of_ne (le_max' _ j (mem_filter.2 ⟨mem_univ _, hcj⟩))
          (mem_erase.1 hj).1
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht.le ?_) (v.nonneg _)
        exact Nat.pow_le_pow_right hy1 (by omega)
    calc v (c jp) * t ^ (y ^ ((jp : ℕ) + 1)) = v (c jp * θ ^ (y ^ ((jp : ℕ) + 1))) := by
          rw [map_mul, map_pow]
      _ = v (C - ∑ j ∈ univ.erase jp, c j * θ ^ (y ^ ((j : ℕ) + 1))) := by rw [hrest]
      _ ≤ v C + v (∑ j ∈ univ.erase jp, c j * θ ^ (y ^ ((j : ℕ) + 1))) := by
          rw [sub_eq_add_neg, ← v.map_neg (∑ j ∈ univ.erase jp, c j * θ ^ (y ^ ((j : ℕ) + 1)))]
          exact v.add_le _ _
      _ ≤ v C + ∑ j ∈ univ.erase jp, v (c j * θ ^ (y ^ ((j : ℕ) + 1))) := by
          gcongr; exact v.sum_le _ _
      _ ≤ v C * t ^ (y ^ (jp : ℕ)) + ∑ j ∈ univ.erase jp, v (c j) * t ^ (y ^ (jp : ℕ)) := by
          gcongr
          · exact le_mul_of_one_le_right (v.nonneg _) hT1
          · exact hterm _ ‹_›
      _ = (v C + ∑ j ∈ univ.erase jp, v (c j)) * t ^ (y ^ (jp : ℕ)) := by
          rw [add_mul, sum_mul]
      _ ≤ B * t ^ (y ^ (jp : ℕ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (le_trans zero_le_one hT1)
          rw [hB]
          exact add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (erase_subset jp univ)
            fun j _ _ => v.nonneg (c j))
  -- hence `|c_{j₊}| t^{y-1} ≤ B` for every `y ≥ 2`
  have hbound : ∀ n : ℕ, v (c jp) * t ^ (n + 1) ≤ B := by
    intro n
    set y := n + 2 with hy
    have h := key y (by omega)
    have hsplit : y ^ ((jp : ℕ) + 1) = y ^ (jp : ℕ) + y ^ (jp : ℕ) * (n + 1) := by
      rw [pow_succ, hy]; ring
    rw [hsplit, pow_add] at h
    have hpos : 0 < t ^ (y ^ (jp : ℕ)) := pow_pos ht0 _
    have h2 : v (c jp) * t ^ (y ^ (jp : ℕ) * (n + 1)) ≤ B := by
      have : t ^ (y ^ (jp : ℕ)) * (v (c jp) * t ^ (y ^ (jp : ℕ) * (n + 1))) ≤
          t ^ (y ^ (jp : ℕ)) * B := by linarith
      exact le_of_mul_le_mul_left this hpos
    have h3 : t ^ (n + 1) ≤ t ^ (y ^ (jp : ℕ) * (n + 1)) :=
      pow_le_pow_right₀ ht.le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _))
    nlinarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / v (c jp)) ht
  have h1 := hbound n
  have h2 : t ^ n ≤ t ^ (n + 1) := pow_le_pow_right₀ ht.le (Nat.le_succ n)
  rw [div_lt_iff₀ hvc] at hn
  nlinarith

/-- The absolute value `x ↦ ‖φ x‖` of a complex embedding. -/
def embAbv {K : Type*} [Field K] (φ : K →+* ℂ) : AbsoluteValue K ℝ where
  toFun x := ‖φ x‖
  map_mul' x y := by simp
  nonneg' x := norm_nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using norm_add_le (φ x) (φ y)

/-- **Lemma 5.4.** A nonzero `θ` in a number field satisfying
`∑_j c_j (θ^{y^{j+1}} - 1) = 0` for every `y ≥ 2`, with `c ≠ 0`, is a root of unity. -/
theorem pow_eq_one_of_relation {K : Type*} [Field K] [NumberField K] {ℓ : ℕ} {θ : K}
    (hθ : θ ≠ 0) (c : Fin ℓ → K) (hc : c ≠ 0)
    (hrel : ∀ y : ℕ, 2 ≤ y → ∑ j, c j * (θ ^ (y ^ ((j : ℕ) + 1)) - 1) = 0) :
    ∃ n : ℕ, 0 < n ∧ θ ^ n = 1 := by
  set C := ∑ j, c j with hC
  have hrel' : ∀ y : ℕ, 2 ≤ y → ∑ j, c j * θ ^ (y ^ ((j : ℕ) + 1)) = C := by
    intro y hy
    have := hrel y hy
    simp only [mul_sub, mul_one, sum_sub_distrib] at this
    rw [hC]; linear_combination this
  -- Lemma 5.2, finite places: `θ` is an algebraic integer
  have hint : IsIntegral ℤ θ := by
    have hmem := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := NumberField.RingOfIntegers K) K θ fun v => by
        have h := abv_le_one_of_relation (v.adicAbv (b := 2) one_lt_two) c hc hrel'
        simp only [IsDedekindDomain.HeightOneSpectrum.adicAbv, AbsoluteValue.coe_mk,
          MulHom.coe_mk, IsDedekindDomain.HeightOneSpectrum.adicAbvDef, NNReal.coe_le_one] at h
        exact (WithZeroMulInt.toNNReal_le_one_iff one_lt_two).1 h
    obtain ⟨x, rfl⟩ := hmem
    exact x.isIntegral_coe
  -- infinite places: every conjugate lies in the closed unit disk
  have hφ : ∀ φ : K →+* ℂ, ‖φ θ‖ ≤ 1 := fun φ => abv_le_one_of_relation (embAbv φ) c hc hrel'
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hθ hint hφ
  exact ⟨n, hn, h⟩

end RestrictedPolynomials

end
