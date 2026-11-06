module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Kronecker's criterion (Hankel version)

Source: Supplement A, §1, Lemma `thm:kron`,
Lemma `lem:shift` and Corollary `cor:kron`.

If the Hankel determinants `det (c_{i+j+s})_{0 ≤ i,j < m}` vanish for all large `m`, then the
formal series `∑ c_j wʲ` is rational: `B · f` is a polynomial for some polynomial `B` with
`B(0) = 1`.

The proof follows the supplement, but the column operation of the source is replaced by polynomial
division.  A kernel vector of a Hankel matrix is read as a polynomial `V`, and the entries of the
matrix act through the linear functionals `phi c i`, `phi c i (X ^ j) = c (i + j)`.  Dividing `V`
by the monic recurrence polynomial `Λ` produces the block structure of the source.

* `hankelDet`: the Hankel determinant.
* `kronecker`: Kronecker's criterion, any shift `s`.
* `kronecker_int`: the form consumed by Supplement B.
-/

@[expose] public section

open Polynomial
open scoped Matrix

noncomputable section

namespace RestrictedPolynomials

/-- Hankel determinant `H^{(s)}_m(c) = det (c_{i+j+s})_{0 ≤ i,j < m}`. -/
noncomputable def hankelDet {k : Type*} [CommRing k] (c : ℕ → k) (s m : ℕ) : k :=
  Matrix.det (Matrix.of fun i j : Fin m => c ((i : ℕ) + j + s))

section Aux

variable {k : Type*} [Field k]

/-- The linear functional `X ^ j ↦ c (i + j)` on `k[X]`. -/
def kronPhi (c : ℕ → k) (i : ℕ) : k[X] →ₗ[k] k :=
  Polynomial.lsum fun j => c (i + j) • LinearMap.id

theorem kronPhi_monomial (c : ℕ → k) (i j : ℕ) (a : k) :
    kronPhi c i (monomial j a) = c (i + j) * a := by
  simp [kronPhi, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

theorem kronPhi_eq_range (c : ℕ → k) (i : ℕ) (V : k[X]) {m : ℕ} (hV : V.degree < m) :
    kronPhi c i V = ∑ j ∈ Finset.range m, c (i + j) * V.coeff j := by
  simp only [kronPhi, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul]
  rw [Polynomial.sum_def]
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_range]
    by_contra hjm
    rw [Polynomial.mem_support_iff] at hj
    exact hj (Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hV (by exact_mod_cast not_lt.mp hjm)))
  · intro j _ hj
    rw [Polynomial.notMem_support_iff] at hj
    simp [hj]

theorem kronPhi_X_pow_mul (c : ℕ → k) (i l : ℕ) (V : k[X]) :
    kronPhi c i (X ^ l * V) = kronPhi c (i + l) V := by
  induction V using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq]
  | monomial j a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_add,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_X_pow_eq_monomial,
      kronPhi_monomial, kronPhi_monomial]
    congr 2
    omega

/-- Applying `kronPhi` to a product with `q`, expanded in the monomials of `q`. -/
theorem kronPhi_mul (c : ℕ → k) (i : ℕ) (L q : k[X]) :
    kronPhi c i (L * q) = ∑ l ∈ Finset.range (q.natDegree + 1), q.coeff l * kronPhi c (i + l) L := by
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : L * (C (q.coeff l) * X ^ l) = q.coeff l • (X ^ l * L) := by
    rw [Polynomial.smul_eq_C_mul]; ring
  rw [this, map_smul, kronPhi_X_pow_mul, smul_eq_mul]

/-- The Hankel matrix applied to the coefficient vector of `V` computes `kronPhi`. -/
theorem kronPhi_eq_mulVec (c : ℕ → k) {m : ℕ} (V : degreeLT k m) (i : Fin m) :
    kronPhi c i (V : k[X]) =
      Matrix.mulVec (Matrix.of (fun i j : Fin m => c ((i : ℕ) + j)))
        (Polynomial.degreeLTEquiv k m V) i := by
  have hV : (V : k[X]).degree < m := Polynomial.mem_degreeLT.mp V.2
  rw [kronPhi_eq_range c i V hV, Matrix.mulVec, dotProduct, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem hankelDet_zero_eq (c : ℕ → k) (m : ℕ) :
    hankelDet c 0 m = Matrix.det (Matrix.of (fun i j : Fin m => c ((i : ℕ) + j))) := rfl

/-- A vanishing Hankel determinant gives a nonzero polynomial in the kernel. -/
theorem exists_kernel_poly (c : ℕ → k) (m : ℕ) (h : hankelDet c 0 m = 0) :
    ∃ V : k[X], V ≠ 0 ∧ V.degree < m ∧ ∀ i < m, kronPhi c i V = 0 := by
  rw [hankelDet_zero_eq, ← Matrix.exists_mulVec_eq_zero_iff] at h
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨((Polynomial.degreeLTEquiv k m).symm v : degreeLT k m), ?_, ?_, ?_⟩
  · intro h0
    apply hv0
    have : (Polynomial.degreeLTEquiv k m).symm v = 0 := Subtype.ext h0
    simpa using congrArg (Polynomial.degreeLTEquiv k m) this
  · exact Polynomial.mem_degreeLT.mp ((Polynomial.degreeLTEquiv k m).symm v).2
  · intro i hi
    have := kronPhi_eq_mulVec c ((Polynomial.degreeLTEquiv k m).symm v) ⟨i, hi⟩
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [this, hv]; rfl

/-- A nonvanishing Hankel determinant means the kernel is trivial. -/
theorem eq_zero_of_kernel (c : ℕ → k) (m : ℕ) (h : hankelDet c 0 m ≠ 0) (V : k[X])
    (hV : V.degree < m) (hφ : ∀ i < m, kronPhi c i V = 0) : V = 0 := by
  by_contra hne
  apply h
  rw [hankelDet_zero_eq, ← Matrix.exists_mulVec_eq_zero_iff]
  have hmem : V ∈ degreeLT k m := Polynomial.mem_degreeLT.mpr hV
  refine ⟨Polynomial.degreeLTEquiv k m ⟨V, hmem⟩, ?_, ?_⟩
  · intro h0
    apply hne
    have := (Polynomial.degreeLTEquiv k m).injective (h0.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  · funext i
    rw [← kronPhi_eq_mulVec c ⟨V, hmem⟩ i]
    exact hφ i i.2

/-- Existence of the recurrence polynomial `Λ` (Lemma `lem:kernel`): monic of degree `r`, killed by
`kronPhi c i` for `i ≤ r`, where `r` is such that `H_r ≠ 0` and `H_{r+1} = 0`. -/
theorem exists_recurrence_poly (c : ℕ → k) (r : ℕ) (hr : hankelDet c 0 r ≠ 0)
    (hr1 : hankelDet c 0 (r + 1) = 0) :
    ∃ L : k[X], L.Monic ∧ L.natDegree = r ∧ ∀ i ≤ r, kronPhi c i L = 0 := by
  obtain ⟨V, hV0, hVdeg, hVφ⟩ := exists_kernel_poly c (r + 1) hr1
  have hcoef : V.coeff r ≠ 0 := by
    intro h0
    apply hV0
    refine eq_zero_of_kernel c r hr V ?_ (fun i hi => hVφ i (by omega))
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro n hn
    rcases hn.eq_or_lt with h | h
    · rw [← h]; exact h0
    · exact Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hVdeg (by exact_mod_cast h))
  have hnat : V.natDegree = r := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hcoef
    exact Polynomial.natDegree_le_iff_degree_le.mpr (Order.le_of_lt_succ (by exact_mod_cast hVdeg))
  refine ⟨C (V.coeff r)⁻¹ * V, ?_, ?_, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_C_mul (inv_ne_zero hcoef),
      hnat, Polynomial.coeff_C_mul]
    exact inv_mul_cancel₀ hcoef
  · rw [Polynomial.natDegree_C_mul (inv_ne_zero hcoef), hnat]
  · intro i hi
    rw [← Polynomial.smul_eq_C_mul, map_smul, hVφ i (by omega), smul_zero]

/-- Propagation of the recurrence (Lemma `lem:prop`). -/
theorem kronPhi_recurrence_zero (c : ℕ → k) (r : ℕ) (hr : hankelDet c 0 r ≠ 0)
    (hz : ∀ m > r, hankelDet c 0 m = 0) (L : k[X]) (hL : L.Monic) (hLr : L.natDegree = r)
    (hL0 : ∀ i ≤ r, kronPhi c i L = 0) : ∀ n, kronPhi c n L = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hnr : n ≤ r
    · exact hL0 n hnr
    · replace hnr : r < n := not_le.mp hnr
      by_contra hne
      obtain ⟨V, hV0, hVdeg, hVφ⟩ := exists_kernel_poly c (n + 1) (hz _ (by omega))
      have hdivmod := Polynomial.modByMonic_add_div V L
      have hLdeg : L.degree = r := by
        rw [Polynomial.degree_eq_natDegree hL.ne_zero, hLr]
      have hρdeg : (V %ₘ L).degree < r := by
        have := Polynomial.degree_modByMonic_lt V hL
        rwa [hLdeg] at this
      have hqnat : (V /ₘ L).natDegree ≤ n - r := by
        rw [Polynomial.natDegree_divByMonic V hL, hLr]
        have : V.natDegree ≤ n := by
          rw [Polynomial.natDegree_le_iff_degree_le]
          exact Order.le_of_lt_succ (by exact_mod_cast hVdeg)
        omega
      have hLq : ∀ i, i + (V /ₘ L).natDegree < n →
          kronPhi c i (L * (V /ₘ L)) = 0 := by
        intro i hi
        rw [kronPhi_mul]
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [Finset.mem_range] at hl
        rw [ih (i + l) (by omega), mul_zero]
      have hρ : V %ₘ L = 0 := by
        refine eq_zero_of_kernel c r hr _ hρdeg fun i hi => ?_
        have h1 := hVφ i (by omega)
        rw [← hdivmod, map_add, hLq i (by omega), add_zero] at h1
        exact h1
      rw [hρ, zero_add] at hdivmod
      have hq0 : V /ₘ L ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hdivmod
        exact hV0 hdivmod.symm
      set q := V /ₘ L with hq
      have hi := hVφ (n - q.natDegree) (by omega)
      rw [← hdivmod, kronPhi_mul, Finset.sum_range_succ] at hi
      rw [Finset.sum_eq_zero, zero_add] at hi
      · have hn : n - q.natDegree + q.natDegree = n := by omega
        rw [hn, mul_eq_zero] at hi
        rcases hi with h | h
        · exact hq0 (Polynomial.leadingCoeff_eq_zero.mp h)
        · exact hne h
      · intro l hl
        rw [Finset.mem_range] at hl
        rw [ih (n - q.natDegree + l) (by omega), mul_zero]

/-- The coefficient of `Λ.reverse · f` in degree `N ≥ r` is `kronPhi c (N - r) Λ`. -/
theorem coeff_reverse_mul_mk (c : ℕ → k) (L : k[X]) (r : ℕ) (hLr : L.natDegree = r) (N : ℕ)
    (hN : r ≤ N) :
    PowerSeries.coeff N ((L.reverse : PowerSeries k) * PowerSeries.mk c) = kronPhi c (N - r) L := by
  have hLdeg : L.degree < ((r + 1 : ℕ) : WithBot ℕ) := by
    rcases eq_or_ne L 0 with h | h
    · simp [h]
    · rw [Polynomial.degree_eq_natDegree h, hLr]; exact_mod_cast Nat.lt_succ_self r
  rw [kronPhi_eq_range c (N - r) L hLdeg, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
  have hsub : ∑ j ∈ Finset.range (r + 1), L.reverse.coeff j * c (N - j) =
      ∑ j ∈ Finset.range N.succ, L.reverse.coeff j * c (N - j) := by
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega
    · intro j _ hj
      rw [Finset.mem_range] at hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
      exact lt_of_le_of_lt (Polynomial.reverse_natDegree_le L) (by omega)
  rw [← hsub, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [Polynomial.coeff_reverse, hLr, Polynomial.revAt_le (by omega)]
  have h1 : r + 1 - 1 - t = r - t := by omega
  have h2 : N - (r + 1 - 1 - t) = N - r + t := by omega
  rw [h1] at h2 ⊢
  rw [h2, show r - (r - t) = t by omega, mul_comm]

/-- The case `s = 0` of Kronecker's criterion. -/
theorem kronecker_zero (c : ℕ → k) (h : ∃ m₀, ∀ m ≥ m₀, hankelDet c 0 m = 0) :
    ∃ B : k[X], B.coeff 0 = 1 ∧ ∃ A : k[X],
      (B : PowerSeries k) * PowerSeries.mk c = (A : PowerSeries k) := by
  classical
  obtain ⟨m₀, hm₀⟩ := h
  have h0 : hankelDet c 0 0 ≠ 0 := by simp [hankelDet]
  set r := Nat.findGreatest (fun m => hankelDet c 0 m ≠ 0) m₀ with hrdef
  have hr : hankelDet c 0 r ≠ 0 :=
    Nat.findGreatest_spec (P := fun m => hankelDet c 0 m ≠ 0) (Nat.zero_le m₀) h0
  have hz : ∀ m > r, hankelDet c 0 m = 0 := by
    intro m hm
    by_cases hmm : m ≤ m₀
    · have := Nat.findGreatest_is_greatest (P := fun m => hankelDet c 0 m ≠ 0) hm hmm
      simpa using this
    · exact hm₀ m (by omega)
  obtain ⟨L, hLm, hLr, hL0⟩ := exists_recurrence_poly c r hr (hz _ (Nat.lt_succ_self r))
  have hall := kronPhi_recurrence_zero c r hr hz L hLm hLr hL0
  have hLdeg : L.degree < ((r + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hLm.ne_zero, hLr]; exact_mod_cast Nat.lt_succ_self r
  refine ⟨L.reverse, ?_, PowerSeries.trunc r (L.reverse * PowerSeries.mk c), ?_⟩
  · rw [Polynomial.coeff_zero_reverse]; exact hLm
  · ext N
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hN
    · rfl
    · rw [coeff_reverse_mul_mk c L r hLr N (by omega), hall]

end Aux

/-- [Supplement A, Lemma thm:kron] Kronecker's criterion, Hankel version. -/
theorem kronecker {k : Type*} [Field k] (c : ℕ → k) (s : ℕ)
    (h : ∃ m₀, ∀ m ≥ m₀, hankelDet c s m = 0) :
    ∃ B : k[X], B.coeff 0 = 1 ∧ ∃ A : k[X],
      (B : PowerSeries k) * PowerSeries.mk c = (A : PowerSeries k) := by
  obtain ⟨m₀, hm₀⟩ := h
  -- Lemma `lem:shift`: pass to the shifted sequence `c' j = c (j + s)`.
  obtain ⟨B, hB0, A', hA'⟩ := kronecker_zero (fun j => c (j + s)) ⟨m₀, fun m hm => hm₀ m hm⟩
  refine ⟨B, hB0, B * PowerSeries.trunc s (PowerSeries.mk c) + X ^ s * A', ?_⟩
  have hsplit : PowerSeries.mk c = ((PowerSeries.trunc s (PowerSeries.mk c) : k[X]) : PowerSeries k) +
      PowerSeries.X ^ s * PowerSeries.mk (fun j => c (j + s)) := by
    ext n
    rw [map_add, Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    by_cases hn : n < s
    · simp [hn, not_le.mpr hn]
    · have h' := not_lt.mp hn
      simp [hn, h', Nat.sub_add_cancel h']
  conv_lhs => rw [hsplit]
  rw [mul_add, ← mul_assoc, mul_comm (B : PowerSeries k) (PowerSeries.X ^ s), mul_assoc, hA']
  push_cast
  ring

/-- [Supplement A, Corollary cor:kron], the form consumed by Supplement B. -/
theorem kronecker_int (a : ℕ → ℤ) (h : ∃ N₀, ∀ N ≥ N₀, hankelDet a 1 (N + 1) = 0) :
    ∃ B : ℚ[X], B.coeff 0 = 1 ∧ ∃ A : ℚ[X],
      (B : PowerSeries ℚ) * PowerSeries.mk (fun k => (a k : ℚ)) = (A : PowerSeries ℚ) := by
  obtain ⟨N₀, hN₀⟩ := h
  refine kronecker (fun k => (a k : ℚ)) 1 ⟨N₀ + 1, fun m hm => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  have hmap : hankelDet (fun k => (a k : ℚ)) 1 (N + 1) =
      (Int.castRingHom ℚ) (hankelDet a 1 (N + 1)) := by
    unfold hankelDet
    rw [RingHom.map_det]
    congr 1
  rw [hmap, hN₀ N (by omega), map_zero]

end RestrictedPolynomials
