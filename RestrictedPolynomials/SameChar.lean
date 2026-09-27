import RestrictedPolynomials.Counting
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Field.ZMod

/-!
# No abelian embeddings into `𝔽_p` (Lemma 4.1)

The proof of the paper: the translation operator `T f(x) = f(x+1)` on functions `𝔽_p → 𝔽_p`
satisfies `(T - 1)^p = T^p - 1 = 0`, the equations become `B(T) g = 0` for the matrix
`B_{r,j}(T) = 1 + T + ⋯ + T^{y_r^j - 1}` with `y_r = r + 1`, and `det B(T)` is invertible
because `det B(1)` is a nonzero Vandermonde-type determinant.

Here the progression has `ℓ + 1` terms, indexed by `Fin (ℓ + 1)`.
-/

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

variable {p : ℕ}

/-- The translation operator `T f(x) = f(x + 1)`. -/
def transl (p : ℕ) : Module.End (ZMod p) (ZMod p → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) fun x => x + 1

lemma transl_pow_apply (n : ℕ) (g : ZMod p → ZMod p) (x : ZMod p) :
    (transl p ^ n) g x = g (x + n) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp [transl, LinearMap.funLeft_apply, add_assoc]

lemma transl_pow_p : transl p ^ p = 1 :=
  LinearMap.ext fun g => funext fun x => by
    rw [transl_pow_apply, ZMod.natCast_self, add_zero]
    rfl

/-- A function invariant under `x ↦ x + 1` is constant. -/
lemma const_of_transl_invariant [NeZero p] {g : ZMod p → ZMod p} (h : ∀ x, g (x + 1) = g x) (a b : ZMod p) :
    g a = g b := by
  have hn : ∀ (n : ℕ) (x : ZMod p), g (x + n) = g x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro x; rw [Nat.cast_succ, ← add_assoc, h, ih]
  have ha := hn a.val 0
  have hb := hn b.val 0
  rw [zero_add, ZMod.natCast_zmod_val] at ha hb
  rw [ha, hb]

/-- The polynomial `1 + X + ⋯ + X^{n-1}`. -/
def geomPoly (n : ℕ) : (ZMod p)[X] := ∑ i ∈ range n, X ^ i

lemma aeval_geomPoly_mul (n : ℕ) :
    aeval (transl p) (geomPoly (p := p) n) * (transl p - 1) = transl p ^ n - 1 := by
  have := geom_sum_mul (X : (ZMod p)[X]) n
  have h := congrArg (aeval (R := ZMod p) (transl p)) this
  simpa [geomPoly] using h

/-- The rows `y_r = r + 2`, `0 ≤ r < ℓ`, and the matrix `B_{r,j} = geomPoly (y_r^{j+1})`. -/
def Bmat (p ℓ : ℕ) : Matrix (Fin ℓ) (Fin ℓ) (ZMod p)[X] :=
  Matrix.of fun r j => geomPoly ((r + 2 : ℕ) ^ ((j : ℕ) + 1))

lemma eval_one_geomPoly (n : ℕ) : (geomPoly (p := p) n).eval 1 = n := by
  simp [geomPoly, eval_finsetSum]

/-- `det B(1) ≠ 0` in `𝔽_p` when `ℓ + 1 < p`. -/
lemma det_Bmat_eval_one_ne_zero [Fact p.Prime] {ℓ : ℕ} (hℓp : ℓ + 1 < p) : (Bmat p ℓ).det.eval 1 ≠ 0 := by
  rw [← coe_evalRingHom, RingHom.map_det]
  set y : Fin ℓ → ZMod p := fun r => ((r : ℕ) + 2 : ℕ)
  have hmat : (evalRingHom (1 : ZMod p)).mapMatrix (Bmat p ℓ) =
      Matrix.diagonal y * Matrix.vandermonde y := by
    ext r j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Bmat, Matrix.of_apply,
      coe_evalRingHom, eval_one_geomPoly, Matrix.diagonal_mul, Matrix.vandermonde_apply, y]
    push_cast
    ring
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
  have hne : ∀ n : ℕ, 0 < n → n < p → (n : ZMod p) ≠ 0 := by
    intro n hn hnp
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hn hnp
  refine mul_ne_zero (prod_ne_zero_iff.2 fun r _ => hne _ (by omega) (by omega))
    (prod_ne_zero_iff.2 fun r _ => prod_ne_zero_iff.2 fun s hs => ?_)
  have hrs : (r : ℕ) < s := by simpa using hs
  have : y s - y r = ((s - r : ℕ) : ZMod p) := by
    simp only [y]; push_cast [hrs.le]; ring
  rw [this]
  exact hne _ (by omega) (by omega)

/-- The operator `det B(T)` is injective. -/
lemma aeval_det_injective [Fact p.Prime] {ℓ : ℕ} (hℓp : ℓ + 1 < p) {g : ZMod p → ZMod p}
    (hg : aeval (transl p) (Bmat p ℓ).det g = 0) : g = 0 := by
  have hirr : Irreducible (X - C (1 : ZMod p)) := irreducible_X_sub_C 1
  have hcop : IsCoprime (X - C (1 : ZMod p)) (Bmat p ℓ).det := by
    rw [hirr.coprime_iff_not_dvd, dvd_iff_isRoot]
    exact det_Bmat_eval_one_ne_zero hℓp
  obtain ⟨u, w, huw⟩ := (hcop.pow_left (m := p)).symm
  have hXp : aeval (transl p) ((X - C (1 : ZMod p)) ^ p) = 0 := by
    rw [sub_pow_char, map_sub, map_pow, aeval_X, map_pow, aeval_C, map_one, one_pow, transl_pow_p,
      sub_self]
  have key : aeval (transl p) u * aeval (transl p) (Bmat p ℓ).det +
      aeval (transl p) w * aeval (transl p) ((X - C (1 : ZMod p)) ^ p) = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, huw, map_one]
  rw [hXp, mul_zero, add_zero] at key
  calc g = (1 : Module.End (ZMod p) (ZMod p → ZMod p)) g := rfl
    _ = (aeval (transl p) u * aeval (transl p) (Bmat p ℓ).det) g := by rw [key]
    _ = aeval (transl p) u (aeval (transl p) (Bmat p ℓ).det g) := rfl
    _ = 0 := by rw [hg, map_zero]

/-- **Lemma 4.1.** Let `M ≥ ℓ + 1` and `p > M` be prime. If `f₀, …, f_ℓ : 𝔽_p → 𝔽_p` satisfy
`f₀(x) + ∑_{j=1}^ℓ f_j(x + y^j) = 0` for all `x ∈ 𝔽_p` and `y ∈ {0, 2, …, M}`, then every `f_j`
is constant. -/
theorem same_char [Fact p.Prime] {ℓ M : ℕ} (hℓM : ℓ + 1 ≤ M) (hMp : M < p) (f : Fin (ℓ + 1) → ZMod p → ZMod p)
    (hf : ∀ x : ZMod p, ∀ y ∈ stepSet M, ∑ j, f j (x + pw j (y : ZMod p)) = 0) :
    ∀ j a b, f j a = f j b := by
  -- the equation at `y = 0`
  have h0 : ∀ x, f 0 x = -∑ i : Fin ℓ, f i.succ x := by
    intro x
    have := hf x 0 (by simp [stepSet])
    rw [Fin.sum_univ_succ] at this
    simp only [Nat.cast_zero, pw_zero_right, add_zero] at this
    linear_combination this
  -- subtracting it: `∑_i (T^{y^{i+1}} - 1) f_{i+1} = 0` for `y ∈ {2, …, M}`
  have hdiff : ∀ y ∈ Icc 2 M,
      ∑ i : Fin ℓ, ((transl p ^ (y ^ ((i : ℕ) + 1)) - 1) (f i.succ)) = 0 := by
    intro y hy
    ext x
    have h1 := hf x y (by simp [stepSet, hy])
    rw [Fin.sum_univ_succ] at h1
    simp only [Fin.val_zero, Fin.val_succ, pw, Nat.add_one_ne_zero, ↓reduceIte, add_zero] at h1
    rw [h0] at h1
    rw [Finset.sum_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, transl_pow_apply,
      Pi.zero_apply, sum_sub_distrib]
    push_cast
    linear_combination h1
  -- with `g_i = (T - 1) f_{i+1}`: `B(T) g = 0`
  set g : Fin ℓ → ZMod p → ZMod p := fun i => (transl p - 1) (f i.succ) with hg
  have hB : ∀ r : Fin ℓ, ∑ i, aeval (transl p) (Bmat p ℓ r i) (g i) = 0 := by
    intro r
    have := hdiff ((r : ℕ) + 2) (by simp; omega)
    rw [← this]
    refine sum_congr rfl fun i _ => ?_
    simp only [Bmat, Matrix.of_apply, hg, ← Module.End.mul_apply, aeval_geomPoly_mul]
  -- the adjugate gives `det B(T) g_i = 0`
  have hdet : ∀ i, aeval (transl p) (Bmat p ℓ).det (g i) = 0 := by
    intro i
    have key : ∀ i', aeval (transl p) (((Bmat p ℓ).adjugate * Bmat p ℓ) i i') =
        if i = i' then aeval (transl p) (Bmat p ℓ).det else 0 := by
      intro i'
      rw [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hsum : ∑ i', aeval (transl p) (((Bmat p ℓ).adjugate * Bmat p ℓ) i i') (g i') =
        aeval (transl p) (Bmat p ℓ).det (g i) := by
      rw [Finset.sum_eq_single i]
      · rw [key, ite_eq_left rfl]
      · intro i' _ hi'
        rw [key, ite_eq_right (Ne.symm hi')]
        rfl
      · simp
    rw [← hsum]
    simp only [Matrix.mul_apply, map_sum, map_mul, LinearMap.sum_apply,
      Module.End.mul_apply]
    rw [sum_comm]
    refine sum_eq_zero fun r _ => ?_
    rw [← map_sum, hB r, map_zero]
  -- hence `g_i = 0`, so `f_{i+1}` is translation invariant
  have hconst : ∀ i : Fin ℓ, ∀ a b, f i.succ a = f i.succ b := by
    intro i
    have hgi : g i = 0 := aeval_det_injective (by omega) (hdet i)
    refine const_of_transl_invariant fun x => ?_
    have := congrFun hgi x
    simp only [hg, LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, Pi.zero_apply,
      sub_eq_zero] at this
    simpa [transl, LinearMap.funLeft_apply] using this
  intro j a b
  refine Fin.cases ?_ (fun i => hconst i a b) j
  rw [h0, h0]
  congr 1
  exact sum_congr rfl fun i _ => hconst i a b

end RestrictedPolynomials

end
