import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.GroupTheory.Perm.Support
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The minors of the infinite matrix `A_{ℓ,∞}(z) = (z^{y^j} - 1)_{y ≥ 2, 1 ≤ j ≤ ℓ}`

* `minor ℓ a ∈ ℤ[z]` : the `ℓ × ℓ` minor with rows `a 0, …, a (ℓ-1)`.
* `minor_monic` : **Lemma 5.7**. For rows `2 ≤ y_1 < ⋯ < y_ℓ` the minor is monic.
* `exists_kernel_of_minors_eq_zero` : over a field, if every `ℓ × ℓ` minor of `A_{ℓ,∞}(θ)`
  vanishes, then `A_{ℓ,∞}(θ)` has a nonzero kernel vector.

Columns are indexed by `j : Fin ℓ` and carry the exponent `j + 1`.
-/

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

variable {ℓ : ℕ}

/-- The matrix `(z^{a_r^{j+1}} - 1)_{r,j}` over `ℤ[z]`. -/
def minorMat (ℓ : ℕ) (a : Fin ℓ → ℕ) : Matrix (Fin ℓ) (Fin ℓ) ℤ[X] :=
  Matrix.of fun r j => X ^ (a r ^ ((j : ℕ) + 1)) - 1

/-- The minor `Δ(M_S) = det (z^{a_r^{j+1}} - 1)_{r,j} ∈ ℤ[z]`. -/
def minor (ℓ : ℕ) (a : Fin ℓ → ℕ) : ℤ[X] := (minorMat ℓ a).det

/-- Admissible choices of rows: `ℓ` distinct integers `≥ 2`. -/
def Admissible (a : Fin ℓ → ℕ) : Prop := Function.Injective a ∧ ∀ r, 2 ≤ a r

/-- The matrix `A_a(θ)`, with rows `a` and entries `θ^{a_r^{j+1}} - 1`. -/
def evalMat {R : Type*} [CommRing R] (θ : R) (a : Fin ℓ → ℕ) : Matrix (Fin ℓ) (Fin ℓ) R :=
  Matrix.of fun r j => θ ^ (a r ^ ((j : ℕ) + 1)) - 1

/-- Evaluating the minor is taking the determinant of the evaluated matrix. -/
lemma aeval_minor {R : Type*} [CommRing R] (θ : R) (a : Fin ℓ → ℕ) :
    aeval θ (minor ℓ a) = (evalMat θ a).det := by
  rw [minor, show (aeval θ) (minorMat ℓ a).det =
    (aeval θ : ℤ[X] →ₐ[ℤ] R).toRingHom (minorMat ℓ a).det from rfl, RingHom.map_det]
  congr 1
  ext r j
  simp [minorMat, evalMat]

/-! ### Lemma 5.7: the minors with increasing rows are monic -/

/-- The exponent `e(σ) = ∑_i a_{σ i}^{i+1}` of the term of the determinant indexed by `σ`. -/
def permExp (a : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ)) : ℕ := ∑ i, a (σ i) ^ ((i : ℕ) + 1)

/-- The exchange inequality `W^{s+1} + A^{m+1} < A^{s+1} + W^{m+1}` for `2 ≤ A < W`, `s < m`. -/
lemma exchange_lt {A W s m : ℕ} (hA : 2 ≤ A) (hAW : A < W) (hsm : s < m) :
    W ^ (s + 1) + A ^ (m + 1) < A ^ (s + 1) + W ^ (m + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = s + 1 + d := ⟨m - s - 1, by omega⟩
  have hP : A ^ (s + 1) < W ^ (s + 1) := Nat.pow_lt_pow_left hAW (by omega)
  have ha' : 2 ≤ A ^ (d + 1) := le_trans hA (Nat.le_self_pow (by omega) A)
  have hab : A ^ (d + 1) ≤ W ^ (d + 1) := Nat.pow_le_pow_left hAW.le _
  have e1 : A ^ (s + 1 + d + 1) = A ^ (s + 1) * A ^ (d + 1) := by rw [← pow_add]; ring_nf
  have e2 : W ^ (s + 1 + d + 1) = W ^ (s + 1) * W ^ (d + 1) := by rw [← pow_add]; ring_nf
  rw [e1, e2]
  set P := A ^ (s + 1)
  set Q := W ^ (s + 1)
  set a' := A ^ (d + 1)
  set b' := W ^ (d + 1)
  zify at hP ha' hab ⊢
  nlinarith [mul_lt_mul_of_pos_right hP (show (0 : ℤ) < a' - 1 by linarith),
    mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℤ) ≤ (Q : ℤ))]

/-- For `σ ≠ 1`, `e(σ) < e(1)`: the identity term dominates the determinant. -/
lemma permExp_lt (a : Fin ℓ → ℕ) (ha : StrictMono a) (ha2 : ∀ r, 2 ≤ a r) :
    ∀ σ : Equiv.Perm (Fin ℓ), σ ≠ 1 → permExp a σ < permExp a 1 := by
  suffices h : ∀ n : ℕ, ∀ σ : Equiv.Perm (Fin ℓ), σ.support.card ≤ n →
      permExp a σ ≤ permExp a 1 ∧ (σ ≠ 1 → permExp a σ < permExp a 1) from
    fun σ hσ => (h _ σ le_rfl).2 hσ
  intro n
  induction n with
  | zero =>
    intro σ hσ
    have : σ = 1 := Equiv.Perm.support_eq_empty_iff.1 (card_eq_zero.1 (Nat.le_zero.1 hσ))
    subst this
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  | succ n ih =>
    intro σ hσ
    by_cases h1 : σ = 1
    · subst h1; exact ⟨le_rfl, fun h => absurd rfl h⟩
    have hne : σ.support.Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, Equiv.Perm.support_eq_empty_iff]; exact h1
    set m := σ.support.max' hne with hm
    have hmS : m ∈ σ.support := max'_mem _ _
    have hσm : σ m ≠ m := Equiv.Perm.mem_support.1 hmS
    -- `σ m < m`
    have hu : σ m < m := by
      have h1 : σ m ∈ σ.support := Equiv.Perm.apply_mem_support.2 hmS
      exact lt_of_le_of_ne (le_max' _ _ h1) hσm
    -- `s = σ⁻¹ m < m`
    set s := σ⁻¹ m with hs
    have hσs : σ s = m := by simp [hs]
    have hsm : s ≠ m := by
      intro h
      have := hσs
      rw [h] at this
      exact hσm this
    have hsS : s ∈ σ.support := by
      rw [Equiv.Perm.mem_support, hσs]; exact fun h => hsm h.symm
    have hs_lt : s < m := lt_of_le_of_ne (le_max' _ _ hsS) hsm
    -- `τ = σ ∘ (s m)` fixes `m`
    set τ := σ * Equiv.swap s m with hτ
    have hτm : τ m = m := by simp [hτ, Equiv.swap_apply_right, hσs]
    have hτs : τ s = σ m := by simp [hτ, Equiv.swap_apply_left]
    have hτi : ∀ i, i ≠ s → i ≠ m → τ i = σ i := by
      intro i his him
      simp [hτ, Equiv.swap_apply_of_ne_of_ne his him]
    have hsupp : τ.support ⊆ σ.support.erase m := by
      intro i hi
      rw [Equiv.Perm.mem_support] at hi
      refine mem_erase.2 ⟨fun h => hi (h ▸ hτm), ?_⟩
      by_cases his : i = s
      · rw [his]; exact hsS
      · have him : i ≠ m := fun h => hi (h ▸ hτm)
        rw [Equiv.Perm.mem_support, ← hτi i his him]; exact hi
    have hcard : τ.support.card ≤ n := by
      have := card_le_card hsupp
      rw [card_erase_of_mem hmS] at this
      omega
    have hτle := (ih τ hcard).1
    -- `e(σ) < e(τ)`
    have hlt : permExp a σ < permExp a τ := by
      unfold permExp
      have hpair : ({s, m} : Finset (Fin ℓ)) ⊆ univ := subset_univ _
      rw [← sum_sdiff hpair, ← sum_sdiff hpair (f := fun i => a (τ i) ^ ((i : ℕ) + 1)),
        sum_pair hsm, sum_pair hsm]
      have hrest : ∑ i ∈ univ \ {s, m}, a (σ i) ^ ((i : ℕ) + 1) =
          ∑ i ∈ univ \ {s, m}, a (τ i) ^ ((i : ℕ) + 1) := by
        refine sum_congr rfl fun i hi => ?_
        simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hi
        rw [hτi i hi.2.1 hi.2.2]
      rw [hrest, hσs, hτs, hτm]
      have hA : a (σ m) < a m := ha hu
      have := exchange_lt (ha2 (σ m)) hA (show (s : ℕ) < m from hs_lt)
      omega
    exact ⟨(hlt.trans_le hτle).le, fun _ => hlt.trans_le hτle⟩

/-- **Lemma 5.7.** If `2 ≤ a_0 < a_1 < ⋯`, the minor with rows `a` is monic. -/
theorem minor_monic (a : Fin ℓ → ℕ) (ha : StrictMono a) (ha2 : ∀ r, 2 ≤ a r) :
    (minor ℓ a).Monic := by
  classical
  -- the term of the determinant indexed by `σ`
  set P : Equiv.Perm (Fin ℓ) → ℤ[X] := fun σ => ∏ i, (X ^ (a (σ i) ^ ((i : ℕ) + 1)) - 1)
    with hP
  have hmonic : ∀ σ, (P σ).Monic := fun σ =>
    monic_prod_of_monic _ _ fun i _ => monic_X_pow_sub_C 1 (pow_ne_zero _ (by
      have := ha2 (σ i); omega))
  have hdeg : ∀ σ, (P σ).natDegree = permExp a σ := by
    intro σ
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_pow_sub_C 1 (pow_ne_zero _ (by
      have := ha2 (σ i); omega))]
    refine sum_congr rfl fun i _ => ?_
    exact natDegree_X_pow_sub_C
  have hdet : minor ℓ a = P 1 + ∑ σ ∈ univ.erase 1, Equiv.Perm.sign σ • P σ := by
    rw [minor, Matrix.det_apply, ← add_sum_erase _ _ (mem_univ 1)]
    simp [minorMat, hP]
  rw [hdet]
  refine (hmonic 1).add_of_left (lt_of_le_of_lt (degree_sum_le _ _) ?_)
  rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.2 (by
    rw [Ne, degree_eq_bot]; exact (hmonic 1).ne_zero))]
  intro σ hσ
  refine lt_of_le_of_lt (degree_smul_le _ _) (degree_lt_degree ?_)
  rw [hdeg, hdeg]
  exact permExp_lt a ha ha2 σ (mem_erase.1 hσ).1

/-! ### Vanishing minors give a kernel vector -/

/-- If every `ℓ × ℓ` minor of `A_{ℓ,∞}(θ)` vanishes, then `A_{ℓ,∞}(θ)` has a nonzero kernel
vector: `∑_j c_j (θ^{y^{j+1}} - 1) = 0` for every `y ≥ 2`. -/
theorem exists_kernel_of_minors_eq_zero {F : Type*} [Field F] (θ : F)
    (h : ∀ a : Fin ℓ → ℕ, Admissible a → (evalMat θ a).det = 0) :
    ∃ c : Fin ℓ → F, c ≠ 0 ∧ ∀ y : ℕ, 2 ≤ y → ∑ j, c j * (θ ^ (y ^ ((j : ℕ) + 1)) - 1) = 0 := by
  classical
  -- the rows of the infinite matrix
  let row : {y : ℕ // 2 ≤ y} → Fin ℓ → F := fun y j => θ ^ ((y : ℕ) ^ ((j : ℕ) + 1)) - 1
  set W := Submodule.span F (Set.range row) with hW
  have hWlt : W < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    obtain ⟨κ, sub, hsub, hspan, hli⟩ := exists_linearIndependent' F row
    have hspan' : Submodule.span F (Set.range (row ∘ sub)) = ⊤ := hspan.trans htop
    have : Finite κ := hli.finite
    let b := Module.Basis.mk hli hspan'.ge
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = ℓ := by
      have := Module.finrank_eq_card_basis b
      rw [Module.finrank_fin_fun] at this
      exact this.symm
    let e : Fin ℓ ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    let a : Fin ℓ → ℕ := fun r => (sub (e r) : ℕ)
    have ha : Admissible a := ⟨fun r r' hrr => e.injective (hsub (Subtype.ext hrr)),
      fun r => (sub (e r)).2⟩
    have hrows : LinearIndependent F fun r => evalMat θ a r := by
      have : (fun r => evalMat θ a r) = (row ∘ sub) ∘ e := by
        ext r j; simp [evalMat, a, row]
      rw [this]
      exact hli.comp e e.injective
    have := (Matrix.linearIndependent_rows_iff_isUnit.1 hrows)
    rw [Matrix.isUnit_iff_isUnit_det] at this
    have hu : IsUnit (evalMat θ a).det := this
    rw [h a ha] at hu
    exact not_isUnit_zero hu
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W hWlt
  have hsingle : ∀ j : Fin ℓ, (fun k => if j = k then (1 : F) else 0) = Pi.single j 1 := by
    intro j; ext k; simp [Pi.single_apply, eq_comm]
  refine ⟨fun j => f (Pi.single j 1), fun hc => hf0 ?_, fun y hy => ?_⟩
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
    refine sum_eq_zero fun j _ => ?_
    have := congrFun hc j
    simp only [Pi.zero_apply] at this
    rw [hsingle, this, smul_zero]
  · have hmem : row ⟨y, hy⟩ ∈ W := Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
    have := hWf hmem
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ f] at this
    simp only [hsingle, smul_eq_mul] at this
    rw [← this]
    exact sum_congr rfl fun j _ => mul_comm _ _

end RestrictedPolynomials

end
