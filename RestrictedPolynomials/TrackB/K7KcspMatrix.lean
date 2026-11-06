module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.Defs

/-!
# Track B: the Loewner comparison of Supplement H

Source: Supplement H, section `sec:psd`: `lem:Q-psd`, `lem:var`, `prop:loewner` and `lem:kron`
(`k7_loewner_Q_le_T` takes `hlam0 : 0 ≤ lam` and drops the unused `hα1`).

The matrices are COMPLEX matrices with real entries. `Matrix.PosSemidef` over `ℂ` is taken
under `open scoped ComplexOrder`; the order `≤` on matrices is the Loewner order of Hermitian forms
(`Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef`, `open scoped MatrixOrder`), never a pointwise order.
The quadratic form is the plain pairing `k7QForm M g = Σ_{x,x'} M(x,x') g(x) conj g(x')`, which is
`star x ⬝ᵥ M *ᵥ x` at `x = conj g`.

The three facts `0 ≤ Q_d` (`k7_QMat_posSemidef`), `Q_d ≤ T'_{αd}`
(`k7_loewner_Q_le_T`, through `k7_var_compare`) and the Kronecker telescoping
(`k7_kron_sub_posSemidef`) are THEOREMS here, never hypotheses.

Proof routes. The forms of `T'_c` and `Q_d` are computed for every matrix of the shape
"diagonal plus real rank one", `u(a) 1[a = a'] + s v(a) v(a')`; positivity and the Loewner difference
are read off the forms. The Kronecker lemmas use, in place of a reindexing induction,
the Schur product theorem (`Matrix.PosSemidef.hadamard`): a product over `t` of PSD matrices
`Z_t(x_t, x'_t)` on `ι → A` is PSD; and `X^{⊗ι} - Y^{⊗ι}` is the sum over the nonzero `β : ι → Bool`
of such products with `Z_t ∈ {X - Y, Y}` (binomial expansion of `X = (X - Y) + Y`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Quad
variable {A : Type} [Fintype A] [DecidableEq A]

/-- the plain-pairing quadratic form `⟨g, M g⟩ = Σ_{x,x'} M(x,x') g(x) conj g(x')` of a matrix on a
finite index type (for the real symmetric matrices of Supplement H it is the form of
`Matrix.PosSemidef`, `star x ⬝ᵥ M *ᵥ x` at `x = conj g`). -/
def k7QForm {B : Type} [Fintype B] (M : Matrix B B ℂ) (g : B → ℂ) : ℂ :=
  ∑ x, ∑ x', M x x' * (g x * star (g x'))

/-- the Kronecker power `X^{⊗ι}(x, x') = ∏_{t ∈ ι} X(x_t, x'_t)` on `ι → A`. -/
def k7KronPow (X : Matrix A A ℂ) (ι : Type) [Fintype ι] : Matrix (ι → A) (ι → A) ℂ :=
  Matrix.of fun x x' => ∏ t, X (x t) (x' t)

/-- the variance `Var_π(g) = Σ π |g|² - |Σ π g|²`. -/
def k7Var (π : FinProb A) (g : A → ℂ) : ℝ :=
  ∑ a, π.prob a * ‖g a‖ ^ 2 - ‖∑ a, (π.prob a : ℂ) * g a‖ ^ 2

/-- `T'_c(a, a') = (1-c) π(a) 1[a = a'] + c π(a) π(a')` (the pair law of `π`-noise at correlation `1-c`,
`= jointNoise π (1-c)`, `k7_TMat_eq_jointNoise`), as a complex matrix. -/
def k7TMat (π : FinProb A) (c : ℝ) : Matrix A A ℂ :=
  Matrix.of fun a a' =>
    (((1 - c) * π.prob a * (if a = a' then 1 else 0) + c * π.prob a * π.prob a' : ℝ) : ℂ)

/-- `Q_d(a, a') = (1-λ) μ''(a) 1[a = a'] + λ[(1-d) π̂(a) 1[a = a'] + d π̂(a) π̂(a')]`: the pair law
"junk `μ''` fixed with probability `1-λ`, else `π̂`-noise at correlation `1-d`", as a complex matrix. -/
def k7QMat (lam : ℝ) (πh μ2 : FinProb A) (d : ℝ) : Matrix A A ℂ :=
  Matrix.of fun a a' =>
    (((1 - lam) * μ2.prob a * (if a = a' then 1 else 0) +
      lam * ((1 - d) * πh.prob a * (if a = a' then 1 else 0) + d * πh.prob a * πh.prob a') : ℝ) : ℂ)

/-- `T'_c` is the pair law of the noise: `T'_c(a, a') = jointNoise π (1-c) (a, a')`. -/
theorem k7_TMat_eq_jointNoise (π : FinProb A) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a a' : A) :
    k7TMat π c a a' = ((jointNoise π (1 - c) (by linarith) (by linarith)).prob (a, a') : ℝ) := by
  simp only [k7TMat, jointNoise, noiseKernel, Matrix.of_apply]
  push_cast
  ring_nf

end Quad

/-! ### Private helpers: forms of "diagonal plus real rank one" matrices, and the variance -/

section QuadAux
open scoped ComplexOrder
variable {B : Type} [Fintype B] [DecidableEq B]

/-- `|z|²` as a complex number is `z conj z`. -/
private theorem k7m_sq_norm_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [DecidableEq B] in
open Matrix in
/-- the `PosSemidef` form at `x` is the plain-pairing form at `conj x`. -/
private theorem k7m_dot_eq_qform (M : Matrix B B ℂ) (x : B → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = k7QForm M (fun b => star (x b)) := by
  simp only [k7QForm, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq B] in
/-- a PSD matrix has a form with nonnegative real part. -/
private theorem k7m_qform_re_nonneg {M : Matrix B B ℂ} (hM : M.PosSemidef) (g : B → ℂ) :
    0 ≤ (k7QForm M g).re := by
  have h := hM.dotProduct_mulVec_nonneg (fun b => star (g b))
  rw [k7m_dot_eq_qform] at h
  simp only [star_star] at h
  exact (Complex.le_def.1 h).1

omit [DecidableEq B] in
/-- a Hermitian matrix whose plain-pairing form is nonnegative is PSD. -/
private theorem k7m_posSemidef_of_qform {M : Matrix B B ℂ} (hH : M.IsHermitian)
    (h : ∀ g, 0 ≤ k7QForm M g) : M.PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => by
    rw [k7m_dot_eq_qform]
    exact h _

omit [DecidableEq B] in
/-- the form is additive in the matrix (difference). -/
private theorem k7m_qform_sub (M N : Matrix B B ℂ) (g : B → ℂ) :
    k7QForm (M - N) g = k7QForm M g - k7QForm N g := by
  simp only [k7QForm, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- the form of a "diagonal plus real rank one" matrix `u(a) 1[a = a'] + s v(a) v(a')`. -/
private theorem k7m_dr_qform (M : Matrix B B ℂ) (u v : B → ℝ) (s : ℝ)
    (hM : ∀ a a', M a a' = ((u a * (if a = a' then 1 else 0) + s * v a * v a' : ℝ) : ℂ))
    (g : B → ℂ) :
    k7QForm M g = ((∑ a, u a * ‖g a‖ ^ 2 + s * ‖∑ a, (v a : ℂ) * g a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [k7QForm, hM, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul,
    k7m_sq_norm_eq, apply_ite Complex.ofReal, Complex.ofReal_zero, add_mul,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  congr 1
  rw [star_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

omit [Fintype B] in
/-- a "diagonal plus real rank one" matrix is Hermitian. -/
private theorem k7m_dr_isHermitian (M : Matrix B B ℂ) (u v : B → ℝ) (s : ℝ)
    (hM : ∀ a a', M a a' = ((u a * (if a = a' then 1 else 0) + s * v a * v a' : ℝ) : ℂ)) :
    M.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [hM, hM, Complex.star_def, Complex.conj_ofReal]
  congr 1
  by_cases h : i = j
  · subst h
    rfl
  · simp only [h, Ne.symm h, ite_false]
    ring

/-- a "diagonal plus real rank one" matrix with `u ≥ 0`, `s ≥ 0` is PSD. -/
private theorem k7m_dr_posSemidef (M : Matrix B B ℂ) (u v : B → ℝ) (s : ℝ)
    (hM : ∀ a a', M a a' = ((u a * (if a = a' then 1 else 0) + s * v a * v a' : ℝ) : ℂ))
    (hu : ∀ a, 0 ≤ u a) (hs : 0 ≤ s) : M.PosSemidef := by
  refine k7m_posSemidef_of_qform (k7m_dr_isHermitian M u v s hM) fun g => ?_
  rw [k7m_dr_qform M u v s hM, Complex.zero_le_real]
  exact add_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hu a) (sq_nonneg _))
    (mul_nonneg hs (sq_nonneg _))

omit [DecidableEq B] in
/-- the bias-variance identity: `Var_ν(g) + |E_ν g - c|² = E_ν |g - c|²`. -/
private theorem k7m_var_add (ν : FinProb B) (g : B → ℂ) (c : ℂ) :
    k7Var ν g + ‖(∑ a, (ν.prob a : ℂ) * g a) - c‖ ^ 2 = ∑ a, ν.prob a * ‖g a - c‖ ^ 2 := by
  simp only [k7Var, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have hR : ∑ a, ν.prob a * (((g a).re - c.re) * ((g a).re - c.re) +
      ((g a).im - c.im) * ((g a).im - c.im)) =
      ∑ a, ν.prob a * ((g a).re * (g a).re + (g a).im * (g a).im) -
        2 * c.re * ∑ a, ν.prob a * (g a).re - 2 * c.im * ∑ a, ν.prob a * (g a).im +
        (c.re * c.re + c.im * c.im) * ∑ a, ν.prob a := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hR, ν.sum_eq_one]
  ring

omit [DecidableEq B] in
/-- an atom of a law is at most `1`. -/
private theorem k7m_prob_le_one (ν : FinProb B) (a : B) : ν.prob a ≤ 1 := by
  rw [← ν.sum_eq_one]
  exact Finset.single_le_sum (fun b _ => ν.nonneg b) (Finset.mem_univ a)

end QuadAux

section Kron
open scoped ComplexOrder
variable {A : Type} [Fintype A] [DecidableEq A] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι] in
/-- Schur: a product over `t ∈ s` of PSD matrices `Z_t(x_t, x'_t)` is PSD on `ι → A`. -/
private theorem k7m_prodMat_posSemidef [DecidableEq ι] (Z : ι → Matrix A A ℂ)
    (hZ : ∀ t, (Z t).PosSemidef) (s : Finset ι) :
    (Matrix.of fun x x' : ι → A => ∏ t ∈ s, Z t (x t) (x' t)).PosSemidef := by
  induction s using Finset.induction_on with
  | empty =>
    have h1 := (Matrix.PosSemidef.one (n := Unit) (R := ℂ)).submatrix (fun _ : ι → A => ())
    convert h1 using 1
    ext x x'
    simp
  | insert a s ha ih =>
    have h := ((hZ a).submatrix (fun x : ι → A => x a)).hadamard ih
    convert h using 1
    ext x x'
    simp [Matrix.hadamard, Finset.prod_insert ha]

/-- `lem:kron`, auxiliary: Kronecker powers of PSD matrices are PSD
(`Matrix.PosSemidef.kronecker`, `Fintype.induction_empty_option`, reindexing `(ι → A) ≃ A × (ι' → A)`). -/
theorem k7_kronPow_posSemidef (X : Matrix A A ℂ) (hX : X.PosSemidef) :
    (k7KronPow X ι).PosSemidef := by
  exact k7m_prodMat_posSemidef (fun _ => X) (fun _ => hX) Finset.univ

/-- `lem:kron` (PROVED, not assumed): `X - Y ≥ 0` and `Y ≥ 0` give `X^{⊗ι} - Y^{⊗ι} ≥ 0`
(induction on `ι`, `X ⊗ P - Y ⊗ R = (X-Y) ⊗ P + Y ⊗ (P-R)`). `Y ≥ 0` cannot be dropped
(`X = 0`, `Y = -I`). -/
theorem k7_kron_sub_posSemidef (X Y : Matrix A A ℂ) (hY : Y.PosSemidef)
    (hXY : (X - Y).PosSemidef) : (k7KronPow X ι - k7KronPow Y ι).PosSemidef := by
  let M : (ι → Bool) → Matrix (ι → A) (ι → A) ℂ := fun β =>
    Matrix.of fun x x' => ∏ t ∈ Finset.univ, (if β t then X - Y else Y) (x t) (x' t)
  have hM : ∀ β, (M β).PosSemidef := fun β =>
    k7m_prodMat_posSemidef (fun t => if β t then X - Y else Y)
      (fun t => by by_cases h : β t <;> simp [h, hXY, hY]) Finset.univ
  have hsum : k7KronPow X ι = ∑ β, M β := by
    ext x x'
    simp only [k7KronPow, M, Matrix.of_apply, Matrix.sum_apply]
    rw [← Fintype.prod_sum (fun t (b : Bool) => (if b then X - Y else Y) (x t) (x' t))]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp
  have h0 : k7KronPow Y ι = M (fun _ => false) := by
    ext x x'
    simp [k7KronPow, M]
  have heq : k7KronPow X ι - k7KronPow Y ι = ∑ β ∈ Finset.univ.erase (fun _ => false), M β := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hsum, h0]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun β _ => hM β

/-- `lem:kron`, consequence: `⟨g, X^{⊗ι} g⟩ ≥ ⟨g, Y^{⊗ι} g⟩` (real parts; both sides are real). -/
theorem k7_kron_form_mono (X Y : Matrix A A ℂ) (hY : Y.PosSemidef) (hXY : (X - Y).PosSemidef)
    (g : (ι → A) → ℂ) :
    (k7QForm (k7KronPow Y ι) g).re ≤ (k7QForm (k7KronPow X ι) g).re := by
  have h := k7m_qform_re_nonneg (k7_kron_sub_posSemidef X Y hY hXY) g
  rw [k7m_qform_sub, Complex.sub_re] at h
  linarith

end Kron

section LoewnerAux
variable {A : Type} [Fintype A] [DecidableEq A]

/-- the complex form of `T'_c`. -/
private theorem k7m_TMat_qform (π : FinProb A) (c : ℝ) (g : A → ℂ) :
    k7QForm (k7TMat π c) g = ((∑ a, π.prob a * ‖g a‖ ^ 2 - c * k7Var π g : ℝ) : ℂ) := by
  rw [k7m_dr_qform (k7TMat π c) (fun a => (1 - c) * π.prob a) π.prob c (fun a a' => rfl) g]
  congr 1
  have e : ∑ a, (1 - c) * π.prob a * ‖g a‖ ^ 2 = (1 - c) * ∑ a, π.prob a * ‖g a‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e, k7Var]
  ring

/-- the entries of `Q_d` in "diagonal plus real rank one" shape. -/
private theorem k7m_QMat_apply (lam : ℝ) (πh μ2 : FinProb A) (d : ℝ) (a a' : A) :
    k7QMat lam πh μ2 d a a' =
      ((((1 - lam) * μ2.prob a + lam * (1 - d) * πh.prob a) * (if a = a' then 1 else 0) +
        lam * d * πh.prob a * πh.prob a' : ℝ) : ℂ) := by
  simp only [k7QMat, Matrix.of_apply]
  congr 1
  ring

/-- the complex form of `Q_d`. -/
private theorem k7m_QMat_qform (μ πh μ2 : FinProb A) {lam : ℝ}
    (hmix : ∀ a, μ.prob a = lam * πh.prob a + (1 - lam) * μ2.prob a) (d : ℝ) (g : A → ℂ) :
    k7QForm (k7QMat lam πh μ2 d) g =
      ((∑ a, μ.prob a * ‖g a‖ ^ 2 - lam * d * k7Var πh g : ℝ) : ℂ) := by
  rw [k7m_dr_qform (k7QMat lam πh μ2 d) (fun a => (1 - lam) * μ2.prob a + lam * (1 - d) * πh.prob a)
    πh.prob (lam * d) (k7m_QMat_apply lam πh μ2 d) g]
  congr 1
  have e1 : ∑ a, ((1 - lam) * μ2.prob a + lam * (1 - d) * πh.prob a) * ‖g a‖ ^ 2 =
      (1 - lam) * ∑ a, μ2.prob a * ‖g a‖ ^ 2 + lam * (1 - d) * ∑ a, πh.prob a * ‖g a‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, μ.prob a * ‖g a‖ ^ 2 =
      lam * ∑ a, πh.prob a * ‖g a‖ ^ 2 + (1 - lam) * ∑ a, μ2.prob a * ‖g a‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [hmix]; ring
  rw [e1, e2, k7Var]
  ring

end LoewnerAux

section Loewner
open scoped ComplexOrder
variable {A : Type} [Fintype A] [DecidableEq A]

/-- `lem:Q-psd`, `T'` half: `T'_c ≥ 0` for `c ∈ [0, 1]`. -/
theorem k7_TMat_posSemidef (π : FinProb A) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (k7TMat π c).PosSemidef :=
  k7m_dr_posSemidef (k7TMat π c) (fun a => (1 - c) * π.prob a) π.prob c (fun a a' => rfl)
    (fun a => mul_nonneg (by linarith) (π.nonneg a)) hc0

/-- `lem:Q-psd`, `T'` half, the form: `⟨g, T'_c g⟩ = ‖g‖²_π - c Var_π(g)`. -/
theorem k7_TMat_form (π : FinProb A) (c : ℝ) (g : A → ℂ) :
    (k7QForm (k7TMat π c) g).re = ∑ a, π.prob a * ‖g a‖ ^ 2 - c * k7Var π g := by
  rw [k7m_TMat_qform, Complex.ofReal_re]

/-- `lem:Q-psd` (PROVED): `Q_d ≥ 0` for `0 ≤ λ ≤ 1`, `d ∈ [0, 1]`
(a sum of three nonnegative terms; `d ≤ 1` makes `1-d ≥ 0`). -/
theorem k7_QMat_posSemidef (πh μ2 : FinProb A) {lam d : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) : (k7QMat lam πh μ2 d).PosSemidef :=
  k7m_dr_posSemidef (k7QMat lam πh μ2 d)
    (fun a => (1 - lam) * μ2.prob a + lam * (1 - d) * πh.prob a) πh.prob (lam * d)
    (k7m_QMat_apply lam πh μ2 d)
    (fun a => add_nonneg (mul_nonneg (by linarith) (μ2.nonneg a))
      (mul_nonneg (mul_nonneg hlam0 (by linarith)) (πh.nonneg a)))
    (mul_nonneg hlam0 hd0)

/-- `lem:Q-psd`, the form: with `μ = λ π̂ + (1-λ) μ''`, `⟨g, Q_d g⟩ = ‖g‖²_μ - λ d Var_π̂(g)`. -/
theorem k7_QMat_form (μ πh μ2 : FinProb A) {lam : ℝ}
    (hmix : ∀ a, μ.prob a = lam * πh.prob a + (1 - lam) * μ2.prob a) (d : ℝ) (g : A → ℂ) :
    (k7QForm (k7QMat lam πh μ2 d) g).re = ∑ a, μ.prob a * ‖g a‖ ^ 2 - lam * d * k7Var πh g := by
  rw [k7m_QMat_qform μ πh μ2 hmix, Complex.ofReal_re]

/-- `lem:var`: if `π̂(a) = n_a / N` with all `1 ≤ n_a`, then `Var_μ(g) ≤ N Var_π̂(g)` for
every law `μ` on `A` (`N π̂(a) ≥ 1`, `μ ≤ 1`, minimality of the mean). -/
theorem k7_var_compare (πh μ : FinProb A) (N : ℕ) (n : A → ℕ) (hn : ∀ a, 1 ≤ n a)
    (hπ : ∀ a, πh.prob a = (n a : ℝ) / N) (g : A → ℂ) :
    k7Var μ g ≤ N * k7Var πh g := by
  have hN : (N : ℝ) ≠ 0 := by
    intro h
    have h1 := πh.sum_eq_one
    simp [hπ, h] at h1
  have hNπ : ∀ a, (N : ℝ) * πh.prob a = n a := fun a => by
    rw [hπ]
    field_simp
  set m : ℂ := ∑ a, (πh.prob a : ℂ) * g a with hm
  have h1 : k7Var μ g ≤ ∑ a, μ.prob a * ‖g a - m‖ ^ 2 := by
    rw [← k7m_var_add μ g m]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have h2 : ∑ a, μ.prob a * ‖g a - m‖ ^ 2 ≤ ∑ a, (n a : ℝ) * ‖g a - m‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right
      ((k7m_prob_le_one μ a).trans (by exact_mod_cast hn a)) (sq_nonneg _)
  have h3 : ∑ a, (n a : ℝ) * ‖g a - m‖ ^ 2 = N * k7Var πh g := by
    have := k7m_var_add πh g m
    rw [← hm, sub_self, norm_zero, zero_pow two_ne_zero, add_zero] at this
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [← hNπ a, mul_assoc]
  linarith

open scoped MatrixOrder in
/-- `prop:loewner` (PROVED): in the Loewner order of Hermitian forms (`Matrix.le_iff`:
`A ≤ B ↔ (B - A).PosSemidef`, NOT a pointwise order) `0 ≤ Q_d ≤ T'_{α d}`, for `d ∈ [0, 1]`,
`λ = α N ∈ [0, 1]`, `μ = λ π̂ + (1-λ) μ''`, and the variance comparison `Var_μ ≤ N Var_π̂` (so `T'_{αd}`
is defined: `α d ≤ 1`). `hlam0 : 0 ≤ lam` is a binder and the unused `hα1` is dropped. -/
theorem k7_loewner_Q_le_T (μ πh μ2 : FinProb A) {α N lam d : ℝ} (hα0 : 0 < α)
    (hlam : lam = α * N) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hmix : ∀ a, μ.prob a = lam * πh.prob a + (1 - lam) * μ2.prob a)
    (hvar : ∀ g : A → ℂ, k7Var μ g ≤ N * k7Var πh g) :
    0 ≤ k7QMat lam πh μ2 d ∧ k7QMat lam πh μ2 d ≤ k7TMat μ (α * d) := by
  have hQ := k7_QMat_posSemidef πh μ2 hlam0 hlam1 hd0 hd1
  refine ⟨Matrix.nonneg_iff_posSemidef.2 hQ, Matrix.le_iff.2 ?_⟩
  have hT : (k7TMat μ (α * d)).IsHermitian :=
    k7m_dr_isHermitian (k7TMat μ (α * d)) (fun a => (1 - α * d) * μ.prob a) μ.prob (α * d)
      (fun a a' => rfl)
  refine k7m_posSemidef_of_qform (hT.sub hQ.isHermitian) fun g => ?_
  rw [k7m_qform_sub, k7m_TMat_qform, k7m_QMat_qform μ πh μ2 hmix, ← Complex.ofReal_sub,
    Complex.zero_le_real]
  have hv := mul_le_mul_of_nonneg_left (hvar g) (mul_nonneg hα0.le hd0)
  rw [hlam]
  nlinarith [hv]

end Loewner

end TrackB
end RestrictedPolynomials
end
