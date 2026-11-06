module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Cyclotomic exclusion (core of [Dim19, Lemma square], l. 274-319)

If the squares and the fourth powers of the complex roots of a monic irreducible integer polynomial
of degree `> 1` agree as multisets, then the polynomial is cyclotomic.  The proof avoids Galois
theory: squaring maps the finite set of squared roots into itself, so every root has a repeated
orbit under squaring and hence is a root of unity; a monic irreducible integer polynomial with a root
of unity as a root is the cyclotomic polynomial of that root's order.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- A monic irreducible integer polynomial of degree `> 1` has no root `0`. -/
lemma cyclotomicExclusion_root_ne_zero (P : ℤ[X]) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) {α : ℂ} (hα : aeval α P = 0) : α ≠ 0 := by
  rintro rfl
  have hx : (X : ℤ[X]) ∣ P := by
    rw [X_dvd_iff]
    have := hα
    rw [aeval_def, eval₂_at_zero] at this
    simpa using this
  obtain ⟨u, hu⟩ := hx
  rcases hirr.isUnit_or_isUnit hu with h | h
  · exact not_isUnit_X h
  · have h1 : u.natDegree = 0 := natDegree_eq_zero_of_isUnit h
    have : P.natDegree = 1 := by
      rw [hu, natDegree_mul X_ne_zero h.ne_zero, h1]; simp
    omega

/-- Core of [Dim19, Lemma square], direction (ii) ⇒ (i), in root form: if the squares and the fourth
powers of the complex roots of a monic irreducible integer polynomial of degree > 1 agree as
multisets, the polynomial is cyclotomic. -/
theorem cyclotomic_of_roots_sq_eq_roots_four (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree)
    (h : (P.map (Int.castRingHom ℂ)).roots.map (· ^ 2) =
      (P.map (Int.castRingHom ℂ)).roots.map (· ^ 4)) :
    ∃ N : ℕ, 0 < N ∧ P = cyclotomic N ℤ := by
  obtain ⟨R, hR⟩ : ∃ R, R = (P.map (Int.castRingHom ℂ)).roots := ⟨_, rfl⟩
  rw [← hR] at h
  have hne : P.map (Int.castRingHom ℂ) ≠ 0 :=
    (hmon.map _).ne_zero
  have hroot : ∀ α ∈ R, aeval α P = 0 := by
    intro α hα
    rw [hR, mem_roots hne, IsRoot.def, eval_map] at hα
    rw [aeval_def]; simpa using hα
  -- closure of squared roots under squaring
  have hclose : ∀ β ∈ R.map (· ^ 2), β ^ 2 ∈ R.map (· ^ 2) := by
    intro β hβ
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hβ
    rw [h]
    exact Multiset.mem_map.mpr ⟨a, ha, by ring⟩
  -- a nonempty root
  have hcard : R ≠ 0 := by
    intro h0
    have : Multiset.card R = (P.map (Int.castRingHom ℂ)).natDegree :=
      by rw [hR]; exact splits_iff_card_roots.mp (IsAlgClosed.splits _)
    rw [h0, natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int] at this
    simp at this
    omega
  obtain ⟨α, hαR⟩ := Multiset.exists_mem_of_ne_zero hcard
  have hα0 : α ≠ 0 := cyclotomicExclusion_root_ne_zero P hirr hdeg (hroot α hαR)
  -- orbit of α² under squaring
  have horb : ∀ k : ℕ, α ^ 2 ^ (k + 1) ∈ R.map (· ^ 2) := by
    intro k
    induction k with
    | zero => exact Multiset.mem_map.mpr ⟨α, hαR, by simp⟩
    | succ k ih =>
      have := hclose _ ih
      rwa [← pow_mul, ← pow_succ] at this
  let S : Finset ℂ := (R.map (· ^ 2)).toFinset
  let g : ℕ → S := fun k => ⟨α ^ 2 ^ (k + 1), Multiset.mem_toFinset.mpr (horb k)⟩
  obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hg' : α ^ 2 ^ (i + 1) = α ^ 2 ^ (j + 1) := congrArg Subtype.val hg
  -- wlog i < j
  have key : ∀ i j : ℕ, i < j → α ^ 2 ^ (i + 1) = α ^ 2 ^ (j + 1) → ∃ n : ℕ, 0 < n ∧ α ^ n = 1 := by
    intro i j hlt he
    have hlt' : 2 ^ (i + 1) < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    refine ⟨2 ^ (j + 1) - 2 ^ (i + 1), by omega, ?_⟩
    have hp : α ^ 2 ^ (i + 1) ≠ 0 := pow_ne_zero _ hα0
    have : α ^ (2 ^ (j + 1) - 2 ^ (i + 1)) * α ^ 2 ^ (i + 1) = 1 * α ^ 2 ^ (i + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hlt'.le, one_mul]
      exact he.symm
    exact mul_right_cancel₀ hp this
  obtain ⟨n, hn, hαn⟩ : ∃ n : ℕ, 0 < n ∧ α ^ n = 1 := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key i j hlt hg'
    · exact key j i hlt hg'.symm
  have hprim : IsPrimitiveRoot α (orderOf α) :=
    IsPrimitiveRoot.orderOf α
  have hpos : 0 < orderOf α := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hαn⟩)
  refine ⟨orderOf α, hpos, ?_⟩
  rw [cyclotomic_eq_minpoly hprim hpos]
  have hint : IsIntegral ℤ α := ⟨P, hmon, by rw [← aeval_def]; exact hroot α hαR⟩
  obtain ⟨c, hc⟩ := minpoly.isIntegrallyClosed_dvd hint (hroot α hαR)
  have hnu : ¬ IsUnit (minpoly ℤ α) := minpoly.not_isUnit ℤ α
  rcases hirr.isUnit_or_isUnit hc with h1 | h1
  · exact absurd h1 hnu
  · exact (eq_of_monic_of_associated (minpoly.monic hint) hmon
      ⟨h1.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩).symm

end RestrictedPolynomials
