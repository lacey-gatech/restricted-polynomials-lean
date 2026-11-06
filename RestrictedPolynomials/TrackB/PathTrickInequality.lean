module

public import RestrictedPolynomials.TrackB.PathTrickEmbedding
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect

/-!
# Track B: the path-trick inequality (paper IV, Lemma 3.9 `from-mu-to-path`)

Source: arXiv:2307.16248v2 `writeup_stability.tex`, statement L1803-1816, proof L1817-1855.

Reading of the source used here: `μ_{2^t}` is the `x`-path trick of length `ℓ = 2^t - 1` (`t ≥ 1`), the exponent is
the printed `2^t`, the output function is `h'` (`condZ`), `altProd` uses `f` at even `0`-indexed
positions and `conj f` at odd ones, and the tensor carrier is `μ^{⊗ι}` against `(μ_ℓ)^{⊗ι}`.

Proof idea (walk form, no `ν_ℓ`): with `P = ∑ₓ f(x) · stepYZ x`, `P̄ = ∑ₓ conj f(x) · stepZY x` and
`K = P P̄` (a matrix on `Y`, self-adjoint for the `μ_Y`-weighted inner product), the right-hand side
is `⟨conj g, K^{2^{t-1}} conj g⟩`, the identity `Q_1 = ‖h'‖²` is the base step, and the iterated
Cauchy-Schwarz is `‖⟨u, K^N u⟩‖² ≤ ‖⟨u, K^{2N} u⟩‖` for `‖u‖ ≤ 1`.
-/

@[expose] public section

open Finset
open scoped Matrix
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section PathIneq
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- `F(x⃗) = ∏ₖ f(xₖ)` for even `k`, `conj f(xₖ)` for odd `k` (`k` is `0`-indexed; for `ℓ = 2^t - 1`
this is the source's `f(x_ℓ) ∏_{j<2^{t-1}} f(x_{2j-1}) conj f(x_{2j})`). -/
def altProd {W : Type} (f : W → ℂ) {ℓ : ℕ} (w : Fin ℓ → W) : ℂ :=
  ∏ k : Fin ℓ, if k.val % 2 = 0 then f (w k) else star (f (w k))

/-- `h'(z) = 𝔼_{(x',y',z')∼μ}[conj f(x') conj g(y') | z' = z]`. -/
def condZ (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) (z : Z) : ℂ :=
  ∑ p : X × Y, ((μ.prob (p.1, p.2, z) / margZ μ z : ℝ) : ℂ) * (star (f p.1) * star (g p.2))

/-- the same for the product distribution `μ^{⊗ι}` (conditioning on the whole `z`-vector). -/
def condZPi (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (z : ι → Z) : ℂ :=
  ∑ p : ι → X × Y, ((∏ i, μ.prob ((p i).1, (p i).2, z i) / margZ μ (z i) : ℝ) : ℂ) *
    (star (f fun i => (p i).1) * star (g fun i => (p i).2))

/-! ### Weighted inner products -/

/-- weighted sesquilinear form -/
private def ip {α : Type} [Fintype α] (w : α → ℝ) (a b : α → ℂ) : ℂ :=
  ∑ i, (w i : ℂ) * (star (a i) * b i)

private lemma ip_star {α : Type} [Fintype α] (w : α → ℝ) (a b : α → ℂ) :
    star (ip w a b) = ip w b a := by
  unfold ip
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

private lemma ip_self {α : Type} [Fintype α] (w : α → ℝ) (a : α → ℂ) :
    ip w a a = ((∑ i, w i * ‖a i‖ ^ 2 : ℝ) : ℂ) := by
  unfold ip
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (a i) * a i = ((‖a i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
  rw [this]

private lemma norm_ip_le {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : α → ℂ) :
    ‖ip w a b‖ ^ 2 ≤ (∑ i, w i * ‖a i‖ ^ 2) * (∑ i, w i * ‖b i‖ ^ 2) := by
  have h1 : ‖ip w a b‖ ≤ ∑ i, Real.sqrt (w i) * ‖a i‖ * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, norm_star, Real.norm_of_nonneg (hw i)]
    rw [show Real.sqrt (w i) * ‖a i‖ * (Real.sqrt (w i) * ‖b i‖) =
      (Real.sqrt (w i) * Real.sqrt (w i)) * (‖a i‖ * ‖b i‖) by ring, Real.mul_self_sqrt (hw i)]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => Real.sqrt (w i) * ‖a i‖)
    (fun i => Real.sqrt (w i) * ‖b i‖)
  have e1 : ∀ i, (Real.sqrt (w i) * ‖a i‖) ^ 2 = w i * ‖a i‖ ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have e2 : ∀ i, (Real.sqrt (w i) * ‖b i‖) ^ 2 = w i * ‖b i‖ ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simp only [e1, e2] at h2
  calc ‖ip w a b‖ ^ 2 ≤ (∑ i, Real.sqrt (w i) * ‖a i‖ * (Real.sqrt (w i) * ‖b i‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

private lemma map_mul_ofReal {A B C : Type} [Fintype B] (M : Matrix A B ℝ) (N : Matrix B C ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-! ### Complex step matrices and the closed form of the alternating walk sum -/

private def S1 (μ : FinProb (X × Y × Z)) (x : X) : Matrix Y Z ℂ :=
  (stepYZ μ x).map Complex.ofReal

private def S2 (μ : FinProb (X × Y × Z)) (x : X) : Matrix Z Y ℂ :=
  (stepZY μ x).map Complex.ofReal

/-- `P = ∑ₓ f(x) · stepYZ x` -/
private def Pm (μ : FinProb (X × Y × Z)) (f : X → ℂ) : Matrix Y Z ℂ := ∑ x, f x • S1 μ x

/-- `P̄ = ∑ₓ conj f(x) · stepZY x` -/
private def Pbm (μ : FinProb (X × Y × Z)) (f : X → ℂ) : Matrix Z Y ℂ :=
  ∑ x, star (f x) • S2 μ x

/-- the alternating walk sum of length `2m+1` -/
private def Tm (μ : FinProb (X × Y × Z)) (f : X → ℂ) (m : ℕ) : Matrix Y Z ℂ :=
  ∑ w : Fin (2 * m + 1) → X, altProd f w • (walkYZ μ (List.ofFn w)).map Complex.ofReal

private lemma sum_fin_cons_gen {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 1) → X) → M) :
    ∑ w, F w = ∑ x, ∑ w' : Fin n → X, F (Fin.cons x w') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => X) (fun p => F (Fin.cons p.1 p.2)) F
    (fun p => rfl)).symm

private lemma sum_fin_cons_cons {M : Type*} [AddCommMonoid M] {n : ℕ}
    (F : (Fin (n + 1 + 1) → X) → M) :
    ∑ w, F w = ∑ x₁, ∑ x₂, ∑ w' : Fin n → X, F (Fin.cons x₁ (Fin.cons x₂ w')) := by
  rw [sum_fin_cons_gen]
  exact Finset.sum_congr rfl fun x₁ _ => sum_fin_cons_gen (fun w => F (Fin.cons x₁ w))

private lemma altProd_cons_cons {W : Type} (f : W → ℂ) {n : ℕ} (x₁ x₂ : W) (w : Fin n → W) :
    altProd f (Fin.cons x₁ (Fin.cons x₂ w : Fin (n + 1) → W) : Fin (n + 1 + 1) → W) =
      f x₁ * star (f x₂) * altProd f w := by
  simp only [altProd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ]
  have h : ∀ i : Fin n, (i.val + 1 + 1) % 2 = i.val % 2 := fun i => by omega
  simp only [h]
  simp [mul_assoc]

private lemma altProd_one {W : Type} (f : W → ℂ) (w : Fin 1 → W) : altProd f w = f (w 0) := by
  simp [altProd]

private lemma Tm_zero (μ : FinProb (X × Y × Z)) (f : X → ℂ) : Tm μ f 0 = Pm μ f := by
  unfold Tm Pm S1
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun w => ?_)
  simp [altProd_one, List.ofFn_succ, walkYZ]

private lemma triple_sum {W : Type} [Fintype W] (a : X → Matrix Y Z ℂ) (b : X → Matrix Z Y ℂ)
    (c : W → Matrix Y Z ℂ) :
    (∑ x, a x) * (∑ x, b x) * (∑ w, c w) = ∑ x₁, ∑ x₂, ∑ w, a x₁ * b x₂ * c w := by
  rw [Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  have e1 : a x₁ * ∑ x, b x = ∑ x₂, a x₁ * b x₂ := Matrix.mul_sum _ _ _
  rw [e1, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  exact Matrix.mul_sum _ _ _

private lemma Tm_succ (μ : FinProb (X × Y × Z)) (f : X → ℂ) (m : ℕ) :
    Tm μ f (m + 1) = Pm μ f * Pbm μ f * Tm μ f m := by
  unfold Tm
  change ∑ w : Fin (2 * m + 1 + 1 + 1) → X,
    altProd f w • (walkYZ μ (List.ofFn w)).map Complex.ofReal = _
  rw [sum_fin_cons_cons]
  unfold Pm Pbm
  rw [triple_sum]
  refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ =>
    Finset.sum_congr rfl fun w _ => ?_
  rw [altProd_cons_cons, List.ofFn_succ, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, walkYZ, map_mul_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_assoc, S1, S2]
  congr 1
  ring

private lemma Tm_eq (μ : FinProb (X × Y × Z)) (f : X → ℂ) (m : ℕ) :
    Tm μ f m = (Pm μ f * Pbm μ f) ^ m * Pm μ f := by
  induction m with
  | zero => simp [Tm_zero]
  | succ m ih =>
    rw [Tm_succ, ih, pow_succ']
    simp only [Matrix.mul_assoc]

private lemma Pm_apply (μ : FinProb (X × Y × Z)) (f : X → ℂ) (y : Y) (z : Z) :
    Pm μ f y z = ∑ x, f x * ((stepYZ μ x y z : ℝ) : ℂ) := by
  simp [Pm, S1, Matrix.sum_apply]

private lemma Pbm_apply (μ : FinProb (X × Y × Z)) (f : X → ℂ) (z : Z) (y : Y) :
    Pbm μ f z y = ∑ x, star (f x) * ((stepZY μ x z y : ℝ) : ℂ) := by
  simp [Pbm, S2, Matrix.sum_apply]

private lemma margY_Pm (μ : FinProb (X × Y × Z)) (f : X → ℂ) (y : Y) (z : Z) :
    (margY μ y : ℂ) * Pm μ f y z = (margZ μ z : ℂ) * star (Pbm μ f z y) := by
  rw [Pm_apply, Pbm_apply, star_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have c1 : (margY μ y : ℂ) * (stepYZ μ x y z : ℂ) = (μ.prob (x, y, z) : ℂ) := by
    exact_mod_cast margY_mul_stepYZ μ x y z
  have c2 : (margZ μ z : ℂ) * (stepZY μ x z y : ℂ) = (μ.prob (x, y, z) : ℂ) := by
    exact_mod_cast margZ_mul_stepZY μ x y z
  simp only [star_mul', star_star, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination f x * c1 - f x * c2

/-- `K = P P̄`, the `Y → Y` transition operator of the alternating walk (two steps) -/
private lemma margY_K (μ : FinProb (X × Y × Z)) (f : X → ℂ) (y y' : Y) :
    (margY μ y : ℂ) * (Pm μ f * Pbm μ f) y y' =
      ∑ z, (margZ μ z : ℂ) * (star (Pbm μ f z y) * Pbm μ f z y') := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← mul_assoc, margY_Pm]
  ring

private lemma mulVec_apply' {A B : Type} [Fintype B] (M : Matrix A B ℂ) (v : B → ℂ) (i : A) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

private lemma ip_K (μ : FinProb (X × Y × Z)) (f : X → ℂ) (u v : Y → ℂ) :
    ip (margY μ) u ((Pm μ f * Pbm μ f) *ᵥ v) = ip (margZ μ) (Pbm μ f *ᵥ u) (Pbm μ f *ᵥ v) := by
  unfold ip
  simp only [mulVec_apply']
  have hz : ∀ z, (margZ μ z : ℂ) * (star (∑ y, Pbm μ f z y * u y) * ∑ y', Pbm μ f z y' * v y') =
      ∑ y, ∑ y', (margZ μ z : ℂ) * (star (Pbm μ f z y * u y) * (Pbm μ f z y' * v y')) :=
    fun z => by
      rw [star_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
  have hy : ∀ y, (margY μ y : ℂ) * (star (u y) * ∑ y', (Pm μ f * Pbm μ f) y y' * v y') =
      ∑ y', ∑ z, (margZ μ z : ℂ) * (star (Pbm μ f z y * u y) * (Pbm μ f z y' * v y')) :=
    fun y => by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      have := margY_K μ f y y'
      calc (margY μ y : ℂ) * (star (u y) * ((Pm μ f * Pbm μ f) y y' * v y'))
          = star (u y) * v y' * ((margY μ y : ℂ) * (Pm μ f * Pbm μ f) y y') := by ring
        _ = star (u y) * v y' *
            ∑ z, (margZ μ z : ℂ) * (star (Pbm μ f z y) * Pbm μ f z y') := by rw [this]
        _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [star_mul']
          ring
  simp only [hz, hy]
  exact (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans Finset.sum_comm

private lemma ip_pow_selfadj {α : Type} [Fintype α] [DecidableEq α] (w : α → ℝ) (K : Matrix α α ℂ)
    (hK : ∀ u v, ip w u (K *ᵥ v) = ip w (K *ᵥ u) v) :
    ∀ (n : ℕ) (u v : α → ℂ), ip w u ((K ^ n) *ᵥ v) = ip w ((K ^ n) *ᵥ u) v := by
  intro n
  induction n with
  | zero => intro u v; simp
  | succ n ih =>
    intro u v
    calc ip w u ((K ^ (n + 1)) *ᵥ v) = ip w u ((K ^ n) *ᵥ (K *ᵥ v)) := by
          rw [pow_succ, Matrix.mulVec_mulVec]
      _ = ip w ((K ^ n) *ᵥ u) (K *ᵥ v) := ih _ _
      _ = ip w (K *ᵥ ((K ^ n) *ᵥ u)) v := hK _ _
      _ = ip w ((K ^ (n + 1)) *ᵥ u) v := by rw [Matrix.mulVec_mulVec, pow_succ']

private lemma iter_cs {α : Type} [Fintype α] [DecidableEq α] (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i ≤ 1) (K : Matrix α α ℂ)
    (hK : ∀ u v, ip w u (K *ᵥ v) = ip w (K *ᵥ u) v) (u : α → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ∀ k : ℕ, ‖ip w u (K *ᵥ u)‖ ^ (2 ^ k) ≤ ‖ip w u ((K ^ (2 ^ k)) *ᵥ u)‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    set N := 2 ^ k with hN
    set v := (K ^ N) *ᵥ u with hv
    have hcs := norm_ip_le w hw u v
    have hu2 : ∑ i, w i * ‖u i‖ ^ 2 ≤ 1 := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) hw1
      have h0 := norm_nonneg (u i)
      calc w i * ‖u i‖ ^ 2 ≤ w i * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ h0 (hu i)) (hw i)
        _ = w i := mul_one _
    have hvv : ∑ i, w i * ‖v i‖ ^ 2 = ‖ip w v v‖ := by
      rw [ip_self, Complex.norm_real, Real.norm_of_nonneg]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
    have hvv2 : ip w v v = ip w u ((K ^ (2 ^ (k + 1))) *ᵥ u) := by
      rw [hv, ← ip_pow_selfadj w K hK N u, Matrix.mulVec_mulVec, ← pow_add, pow_succ, mul_two]
    have hstep : ‖ip w u v‖ ^ 2 ≤ ‖ip w u ((K ^ (2 ^ (k + 1))) *ᵥ u)‖ := by
      calc ‖ip w u v‖ ^ 2 ≤ (∑ i, w i * ‖u i‖ ^ 2) * (∑ i, w i * ‖v i‖ ^ 2) := hcs
        _ ≤ 1 * (∑ i, w i * ‖v i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hu2
            (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))
        _ = _ := by rw [one_mul, hvv, hvv2]
    calc ‖ip w u (K *ᵥ u)‖ ^ (2 ^ (k + 1)) = (‖ip w u (K *ᵥ u)‖ ^ (2 ^ k)) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ ‖ip w u v‖ ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
      _ ≤ _ := hstep

/-! ### The base step -/

private lemma sum_triple_z {M : Type*} [AddCommMonoid M] (F : X × Y × Z → M) :
    ∑ p, F p = ∑ z, ∑ q : X × Y, F (q.1, q.2, z) := by
  simp only [Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm

private lemma sum_margZ (μ : FinProb (X × Y × Z)) : ∑ z, margZ μ z = 1 := by
  rw [← μ.sum_eq_one, sum_triple_z (M := ℝ)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [margZ_eq_sum, Fintype.sum_prod_type]

private lemma sum_xy_eq (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) (z : Z) :
    ∑ p : X × Y, (μ.prob (p.1, p.2, z) : ℂ) * (f p.1 * g p.2) =
      (margZ μ z : ℂ) * star (condZ μ f g z) := by
  unfold condZ
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have c2 : (margZ μ z : ℂ) * ((μ.prob (p.1, p.2, z) / margZ μ z : ℝ) : ℂ) =
      (μ.prob (p.1, p.2, z) : ℂ) := by
    have := margZ_mul_stepZY μ p.1 p.2 z
    simp only [stepZY, Matrix.of_apply] at this
    exact_mod_cast this
  simp only [star_mul', star_star, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination (f p.1 * g p.2) * (-c2)

private lemma A_eq_ip (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ) :
    ∑ p : X × Y × Z, (μ.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2) =
      ip (margZ μ) (condZ μ f g) h := by
  rw [sum_triple_z]
  unfold ip
  refine Finset.sum_congr rfl fun z _ => ?_
  have := sum_xy_eq μ f g z
  calc ∑ q : X × Y, (μ.prob (q.1, q.2, z) : ℂ) * (f q.1 * g q.2 * h z)
      = (∑ q : X × Y, (μ.prob (q.1, q.2, z) : ℂ) * (f q.1 * g q.2)) * h z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ = _ := by rw [this]; ring

/-- Paper IV `lem:from-mu-to-path`, the base Cauchy-Schwarz step (`#base-cauchy-schwarz`). -/
theorem from_mu_to_path_base (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    (∑ p : X × Y × Z, (μ.prob p : ℂ) * (f p.1 * g p.2.1 * condZ μ f g p.2.2) =
        ((∑ z, margZ μ z * ‖condZ μ f g z‖ ^ 2 : ℝ) : ℂ)) ∧
      ‖∑ p : X × Y × Z, (μ.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ^ 2 ≤
        ∑ z, margZ μ z * ‖condZ μ f g z‖ ^ 2 := by
  have hw : ∀ z, 0 ≤ margZ μ z := margZ_nonneg μ
  refine ⟨?_, ?_⟩
  · rw [A_eq_ip, ip_self]
  · rw [A_eq_ip]
    refine (norm_ip_le (margZ μ) hw _ _).trans ?_
    have h1 : ∑ z, margZ μ z * ‖h z‖ ^ 2 ≤ 1 := by
      rw [← sum_margZ μ]
      refine Finset.sum_le_sum fun z _ => ?_
      have h0 := norm_nonneg (h z)
      calc margZ μ z * ‖h z‖ ^ 2 ≤ margZ μ z * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ h0 (hh z)) (hw z)
        _ = margZ μ z := mul_one _
    have h2 : 0 ≤ ∑ z, margZ μ z * ‖condZ μ f g z‖ ^ 2 :=
      Finset.sum_nonneg fun z _ => mul_nonneg (hw z) (sq_nonneg _)
    nlinarith

/-! ### The single-copy inequality -/

private lemma sum_pathX (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (G : (Fin ℓ → X) → Y → Z → ℂ) :
    ∑ q : PathX μ ℓ hℓ × Y × Z,
        (pathWeight μ ℓ hℓ q.1.1 q.2.1 q.2.2 : ℂ) * G q.1.1 q.2.1 q.2.2 =
      ∑ r : (Fin ℓ → X) × Y × Z, (pathWeight μ ℓ hℓ r.1 r.2.1 r.2.2 : ℂ) * G r.1 r.2.1 r.2.2 := by
  refine Fintype.sum_of_injective (fun q : PathX μ ℓ hℓ × Y × Z => (q.1.1, q.2)) ?_ _ _ ?_ ?_
  rotate_left 2
  · intro q; rfl
  rotate_right 2
  · rintro ⟨⟨w, hw⟩, y, z⟩ ⟨⟨w', hw'⟩, y', z'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · intro r hr
    have : pathWeight μ ℓ hℓ r.1 r.2.1 r.2.2 = 0 := by
      by_contra hne
      exact hr ⟨(⟨r.1, r.2.1, r.2.2, hne⟩, r.2.1, r.2.2), rfl⟩
    simp [this]

private lemma Tm_apply (μ : FinProb (X × Y × Z)) (f : X → ℂ) (m : ℕ) (y : Y) (z : Z) :
    Tm μ f m y z = ∑ w : Fin (2 * m + 1) → X,
      altProd f w * ((walkYZ μ (List.ofFn w) y z : ℝ) : ℂ) := by
  simp [Tm, Matrix.sum_apply]

private lemma Pbm_mulVec (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) :
    Pbm μ f *ᵥ (fun y => star (g y)) = condZ μ f g := by
  funext z
  rw [mulVec_apply']
  unfold condZ
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Pbm_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [stepZY, Matrix.of_apply]
  ring

private lemma B_eq_ip (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) (m : ℕ)
    (hℓ : Odd (2 * m + 1)) :
    ∑ q : PathX μ (2 * m + 1) hℓ × Y × Z, ((pathTrick μ (2 * m + 1) hℓ).prob q : ℂ) *
        (altProd f q.1.1 * g q.2.1 * condZ μ f g q.2.2) =
      ip (margY μ) (fun y => star (g y))
        (((Pm μ f * Pbm μ f) ^ (m + 1)) *ᵥ (fun y => star (g y))) := by
  have hT : (Tm μ f m) *ᵥ condZ μ f g =
      ((Pm μ f * Pbm μ f) ^ (m + 1)) *ᵥ (fun y => star (g y)) := by
    rw [← Pbm_mulVec μ f g, Tm_eq, Matrix.mulVec_mulVec, pow_succ, Matrix.mul_assoc]
  rw [← hT]
  calc ∑ q : PathX μ (2 * m + 1) hℓ × Y × Z, ((pathTrick μ (2 * m + 1) hℓ).prob q : ℂ) *
        (altProd f q.1.1 * g q.2.1 * condZ μ f g q.2.2)
      = ∑ r : (Fin (2 * m + 1) → X) × Y × Z,
          (pathWeight μ (2 * m + 1) hℓ r.1 r.2.1 r.2.2 : ℂ) *
            (altProd f r.1 * g r.2.1 * condZ μ f g r.2.2) :=
        sum_pathX μ hℓ (fun w y z => altProd f w * g y * condZ μ f g z)
    _ = ∑ y, ∑ z, ∑ w : Fin (2 * m + 1) → X,
          (pathWeight μ (2 * m + 1) hℓ w y z : ℂ) * (altProd f w * g y * condZ μ f g z) := by
        simp only [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y, ∑ z, (margY μ y : ℂ) * g y * (Tm μ f m y z * condZ μ f g z) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
        rw [Tm_apply, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        unfold pathWeight
        push_cast
        ring
    _ = _ := by
        unfold ip
        simp only [mulVec_apply', star_star]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring

/-- Paper IV `lem:from-mu-to-path` (Lemma 3.9), one copy of `μ`, `ℓ = 2^t - 1`. The exponent `2^t` is
the printed one; it needs identity (a) of the iterated Cauchy-Schwarz step
(`#iterated-cauchy-schwarz`). -/
theorem from_mu_to_path (μ : FinProb (X × Y × Z)) {t ℓ : ℕ} (hℓ : Odd ℓ) (hℓt : ℓ = 2 ^ t - 1)
    (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖∑ p : X × Y × Z, (μ.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ^ (2 ^ t) ≤
      ‖∑ q : PathX μ ℓ hℓ × Y × Z, ((pathTrick μ ℓ hℓ).prob q : ℂ) *
        (altProd f q.1.1 * g q.2.1 * condZ μ f g q.2.2)‖ := by
  obtain ⟨m, hm⟩ := id hℓ
  subst hm
  have hw : ∀ y, 0 ≤ margY μ y := margY_nonneg μ
  have hw1 : ∑ y, margY μ y ≤ 1 := (sum_margY μ).le
  have hK : ∀ u v : Y → ℂ, ip (margY μ) u ((Pm μ f * Pbm μ f) *ᵥ v) =
      ip (margY μ) ((Pm μ f * Pbm μ f) *ᵥ u) v := by
    intro u v
    calc ip (margY μ) u ((Pm μ f * Pbm μ f) *ᵥ v)
        = ip (margZ μ) (Pbm μ f *ᵥ u) (Pbm μ f *ᵥ v) := ip_K μ f u v
      _ = star (ip (margZ μ) (Pbm μ f *ᵥ v) (Pbm μ f *ᵥ u)) := (ip_star _ _ _).symm
      _ = star (ip (margY μ) v ((Pm μ f * Pbm μ f) *ᵥ u)) := by rw [ip_K]
      _ = _ := ip_star _ _ _
  have hu : ∀ y, ‖(fun y => star (g y)) y‖ ≤ 1 := fun y => by
    simpa using hg y
  have hbase := (from_mu_to_path_base μ f g h hf hg hh).2
  have ha0 : ‖ip (margY μ) (fun y => star (g y)) ((Pm μ f * Pbm μ f) *ᵥ (fun y => star (g y)))‖ =
      ∑ z, margZ μ z * ‖condZ μ f g z‖ ^ 2 := by
    rw [ip_K, Pbm_mulVec, ip_self, Complex.norm_real, Real.norm_of_nonneg]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (margZ_nonneg μ z) (sq_nonneg _)
  rw [B_eq_ip]
  cases t with
  | zero => simp at hℓt
  | succ s =>
    have h2 : 2 ^ (s + 1) = 2 * 2 ^ s := pow_succ' 2 s
    have h3 : 0 < 2 ^ s := by positivity
    have hm1 : m + 1 = 2 ^ s := by omega
    rw [hm1]
    have hit := iter_cs (margY μ) hw hw1 (Pm μ f * Pbm μ f) hK (fun y => star (g y)) hu s
    refine le_trans ?_ hit
    rw [ha0, pow_succ', pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase _

/-! ### One-boundedness of the building blocks (public: used by the consumers of Lemma 3.9) -/

/-- `‖altProd f w‖ ≤ 1` for a `1`-bounded `f`. -/
theorem norm_altProd_le_one {W : Type} (f : W → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1) {ℓ : ℕ}
    (w : Fin ℓ → W) : ‖altProd f w‖ ≤ 1 := by
  unfold altProd
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun k _ => norm_nonneg _) fun k _ => ?_
  split_ifs
  · exact hf _
  · simpa using hf _

private lemma sum_cond_le_one (μ : FinProb (X × Y × Z)) (z : Z) :
    ∑ p : X × Y, μ.prob (p.1, p.2, z) / margZ μ z ≤ 1 := by
  rw [← Finset.sum_div]
  have : ∑ p : X × Y, μ.prob (p.1, p.2, z) = margZ μ z := by
    rw [margZ_eq_sum, Fintype.sum_prod_type]
  rw [this]
  by_cases hz : margZ μ z = 0
  · simp [hz]
  · rw [div_self hz]

private lemma cond_nonneg (μ : FinProb (X × Y × Z)) (p : X × Y) (z : Z) :
    0 ≤ μ.prob (p.1, p.2, z) / margZ μ z :=
  div_nonneg (μ.nonneg _) (margZ_nonneg μ z)

/-- `‖condZ μ f g z‖ ≤ 1` for `1`-bounded `f, g` (a conditional average of `1`-bounded products). -/
theorem norm_condZ_le_one (μ : FinProb (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (z : Z) : ‖condZ μ f g z‖ ≤ 1 := by
  unfold condZ
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => ?_).trans (sum_cond_le_one μ z))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cond_nonneg μ p z), norm_mul, norm_star,
    norm_star]
  have h1 := hf p.1
  have h2 := hg p.2
  have h3 : ‖f p.1‖ * ‖g p.2‖ ≤ 1 := by
    calc ‖f p.1‖ * ‖g p.2‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc μ.prob (p.1, p.2, z) / margZ μ z * (‖f p.1‖ * ‖g p.2‖)
      ≤ μ.prob (p.1, p.2, z) / margZ μ z * 1 :=
        mul_le_mul_of_nonneg_left h3 (cond_nonneg μ p z)
    _ = _ := mul_one _

/-- `‖condZPi μ ι f g z‖ ≤ 1` for `1`-bounded `f, g` on the product alphabets. -/
theorem norm_condZPi_le_one (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (z : ι → Z) : ‖condZPi μ ι f g z‖ ≤ 1 := by
  unfold condZPi
  have hprod : ∑ p : ι → X × Y, ∏ i, μ.prob ((p i).1, (p i).2, z i) / margZ μ (z i) ≤ 1 := by
    rw [← Fintype.prod_sum (fun i (a : X × Y) => μ.prob (a.1, a.2, z i) / margZ μ (z i))]
    exact Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun p _ => cond_nonneg μ p (z i))
      fun i _ => sum_cond_le_one μ (z i)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => ?_).trans hprod)
  have hnn : 0 ≤ ∏ i, μ.prob ((p i).1, (p i).2, z i) / margZ μ (z i) :=
    Finset.prod_nonneg fun i _ => cond_nonneg μ (p i) (z i)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, norm_mul, norm_star, norm_star]
  have h3 : ‖f fun i => (p i).1‖ * ‖g fun i => (p i).2‖ ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul (hf _) (hg _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc (∏ i, μ.prob ((p i).1, (p i).2, z i) / margZ μ (z i)) *
        (‖f fun i => (p i).1‖ * ‖g fun i => (p i).2‖)
      ≤ (∏ i, μ.prob ((p i).1, (p i).2, z i) / margZ μ (z i)) * 1 :=
        mul_le_mul_of_nonneg_left h3 hnn
    _ = _ := mul_one _

/-! ### The tensor form: `μ^{⊗ι}` as a measure on the product alphabets -/

private lemma sum_pi_two {A B ι : Type} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
    (F : ι → A → B → ℝ) :
    ∑ a : ι → A, ∑ b : ι → B, ∏ i, F i (a i) (b i) = ∏ i, ∑ a, ∑ b, F i a b := by
  rw [Fintype.prod_sum (fun i a => ∑ b, F i a b)]
  exact Finset.sum_congr rfl fun a _ => (Fintype.prod_sum (fun i b => F i (a i) b)).symm

/-- the identification `(ι → X × Y × Z) ≃ (ι → X) × (ι → Y) × (ι → Z)` -/
private def tensorEquiv (ι : Type) : (ι → X × Y × Z) ≃ (ι → X) × (ι → Y) × (ι → Z) where
  toFun q := (fun i => (q i).1, fun i => (q i).2.1, fun i => (q i).2.2)
  invFun r := fun i => (r.1 i, r.2.1 i, r.2.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `μ^{⊗ι}` as a measure on the product alphabets `(ι → X) × (ι → Y) × (ι → Z)` -/
private def tensorProb (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι] :
    FinProb ((ι → X) × (ι → Y) × (ι → Z)) where
  prob r := ∏ i, μ.prob (r.1 i, r.2.1 i, r.2.2 i)
  nonneg r := Finset.prod_nonneg fun i _ => μ.nonneg _
  sum_eq_one := by
    rw [← (μ.pi ι).sum_eq_one]
    exact Fintype.sum_equiv (tensorEquiv ι).symm _ _ (fun r => rfl)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private lemma margY_tensor (μ : FinProb (X × Y × Z)) (y : ι → Y) :
    margY (tensorProb μ ι) y = ∏ i, margY μ (y i) := by
  rw [margY_eq_sum]
  simp_rw [margY_eq_sum]
  exact sum_pi_two (fun i x z => μ.prob (x, y i, z))

private lemma margZ_tensor (μ : FinProb (X × Y × Z)) (z : ι → Z) :
    margZ (tensorProb μ ι) z = ∏ i, margZ μ (z i) := by
  rw [margZ_eq_sum]
  simp_rw [margZ_eq_sum]
  exact sum_pi_two (fun i x y => μ.prob (x, y, z i))

private lemma stepYZ_tensor (μ : FinProb (X × Y × Z)) (x : ι → X) (y : ι → Y) (z : ι → Z) :
    stepYZ (tensorProb μ ι) x y z = ∏ i, stepYZ μ (x i) (y i) (z i) := by
  simp only [stepYZ, Matrix.of_apply]
  rw [margY_tensor]
  exact (Finset.prod_div_distrib _ _).symm

private lemma stepZY_tensor (μ : FinProb (X × Y × Z)) (x : ι → X) (z : ι → Z) (y : ι → Y) :
    stepZY (tensorProb μ ι) x z y = ∏ i, stepZY μ (x i) (z i) (y i) := by
  simp only [stepZY, Matrix.of_apply]
  rw [margZ_tensor]
  exact (Finset.prod_div_distrib _ _).symm

private lemma walkYZ_tensor (μ : FinProb (X × Y × Z)) :
    ∀ (m : ℕ) (L : List (ι → X)), L.length = 2 * m + 1 → ∀ (y : ι → Y) (z : ι → Z),
      walkYZ (tensorProb μ ι) L y z = ∏ i, walkYZ μ (L.map fun x => x i) (y i) (z i) := by
  intro m
  induction m with
  | zero =>
    intro L hL y z
    rcases L with _ | ⟨x, _ | ⟨x₂, rest⟩⟩
    · simp at hL
    · simp [walkYZ, stepYZ_tensor]
    · simp at hL
  | succ m ih =>
    intro L hL y z
    rcases L with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩
    · simp at hL
    · simp at hL
    · have hl : rest.length = 2 * m + 1 := by simp at hL; omega
      have e : ∀ y' : ι → Y, walkYZ (tensorProb μ ι) rest y' z =
          ∏ i, walkYZ μ (rest.map fun x => x i) (y' i) (z i) := fun y' => ih rest hl y' z
      rw [walkYZ, Matrix.mul_apply]
      simp only [List.map_cons, walkYZ, Matrix.mul_apply]
      calc ∑ y', (∑ z', stepYZ (tensorProb μ ι) x₁ y z' * stepZY (tensorProb μ ι) x₂ z' y') *
            walkYZ (tensorProb μ ι) rest y' z
          = ∑ y' : ι → Y, ∑ z' : ι → Z, ∏ i, (stepYZ μ (x₁ i) (y i) (z' i) *
              stepZY μ (x₂ i) (z' i) (y' i) * walkYZ μ (rest.map fun x => x i) (y' i) (z i)) := by
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [e, Finset.sum_mul]
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [stepYZ_tensor, stepZY_tensor, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        _ = ∏ i, ∑ y', ∑ z', (stepYZ μ (x₁ i) (y i) z' * stepZY μ (x₂ i) z' y' *
              walkYZ μ (rest.map fun x => x i) y' (z i)) :=
            sum_pi_two (fun i y' z' => stepYZ μ (x₁ i) (y i) z' * stepZY μ (x₂ i) z' y' *
              walkYZ μ (rest.map fun x => x i) y' (z i))
        _ = _ := by
            refine Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun y' _ => ?_
            rw [Finset.sum_mul]

private lemma pathWeight_tensor (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (W : Fin ℓ → ι → X) (y : ι → Y) (z : ι → Z) :
    pathWeight (tensorProb μ ι) ℓ hℓ W y z =
      ∏ i, pathWeight μ ℓ hℓ (fun k => W k i) (y i) (z i) := by
  obtain ⟨m, hm⟩ := hℓ
  unfold pathWeight
  rw [margY_tensor, walkYZ_tensor μ m _ (by simp [hm]), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [List.map_ofFn]
  rfl

private lemma condZ_tensor (μ : FinProb (X × Y × Z)) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (z : ι → Z) : condZ (tensorProb μ ι) f g z = condZPi μ ι f g z := by
  unfold condZ condZPi
  refine (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => X) (fun _ => Y)) _ _ (fun p => ?_)).symm
  rw [margZ_tensor, Finset.prod_div_distrib]
  rfl

private lemma lhs_tensor (μ : FinProb (X × Y × Z)) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) :
    (μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2)) =
      ∑ r : (ι → X) × (ι → Y) × (ι → Z), ((tensorProb μ ι).prob r : ℂ) *
        (f r.1 * g r.2.1 * h r.2.2) :=
  Fintype.sum_equiv (tensorEquiv ι) _ _ (fun q => rfl)

private lemma rhs_tensor (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) :
    ∑ q : PathX (tensorProb μ ι) ℓ hℓ × (ι → Y) × (ι → Z),
        ((pathTrick (tensorProb μ ι) ℓ hℓ).prob q : ℂ) *
          (altProd f q.1.1 * g q.2.1 * condZ (tensorProb μ ι) f g q.2.2) =
      ((pathTrick μ ℓ hℓ).pi ι).cexpect (fun q =>
        altProd f (fun k i => (q i).1.1 k) * g (fun i => (q i).2.1) *
          condZPi μ ι f g (fun i => (q i).2.2)) := by
  rw [show (∑ q : PathX (tensorProb μ ι) ℓ hℓ × (ι → Y) × (ι → Z),
        ((pathTrick (tensorProb μ ι) ℓ hℓ).prob q : ℂ) *
          (altProd f q.1.1 * g q.2.1 * condZ (tensorProb μ ι) f g q.2.2)) =
      ∑ r : (Fin ℓ → ι → X) × (ι → Y) × (ι → Z),
        (pathWeight (tensorProb μ ι) ℓ hℓ r.1 r.2.1 r.2.2 : ℂ) *
          (altProd f r.1 * g r.2.1 * condZ (tensorProb μ ι) f g r.2.2) from
    sum_pathX (tensorProb μ ι) hℓ (fun w y z => altProd f w * g y * condZ (tensorProb μ ι) f g z)]
  unfold FinProb.cexpect
  symm
  refine Fintype.sum_of_injective
    (fun q : ι → PathX μ ℓ hℓ × Y × Z =>
      ((fun k i => (q i).1.1 k, fun i => (q i).2.1, fun i => (q i).2.2) :
        (Fin ℓ → ι → X) × (ι → Y) × (ι → Z))) ?_ _ _ ?_ ?_
  rotate_left 2
  · intro q
    simp only
    rw [pathWeight_tensor, condZ_tensor]
    rfl
  · intro q q' hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    funext i
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (congrFun h2 i) (congrFun h3 i))
    funext k
    exact congrFun (congrFun h1 k) i
  · intro r hr
    have : pathWeight (tensorProb μ ι) ℓ hℓ r.1 r.2.1 r.2.2 = 0 := by
      rw [pathWeight_tensor]
      by_contra hne
      have hne' : ∀ i, pathWeight μ ℓ hℓ (fun k => r.1 k i) (r.2.1 i) (r.2.2 i) ≠ 0 :=
        fun i => Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
      exact hr ⟨fun i => (⟨fun k => r.1 k i, r.2.1 i, r.2.2 i, hne' i⟩, r.2.1 i, r.2.2 i), rfl⟩
    simp [this]

/-- Paper IV `lem:from-mu-to-path` with the tensor-power carrier (`#tensorization`, intended reading:
`μ^{⊗ι}` on the left and `(μ_ℓ)^{⊗ι}` on the right, the `ℓ` labels of coordinate `i` being the
word `(q i).1.1`). -/
theorem from_mu_to_path_tensor (μ : FinProb (X × Y × Z)) {t ℓ : ℕ} (hℓ : Odd ℓ)
    (hℓt : ℓ = 2 ^ t - 1) (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ (2 ^ t) ≤
      ‖((pathTrick μ ℓ hℓ).pi ι).cexpect (fun q =>
        altProd f (fun k i => (q i).1.1 k) * g (fun i => (q i).2.1) *
          condZPi μ ι f g (fun i => (q i).2.2))‖ := by
  rw [lhs_tensor, ← rhs_tensor]
  exact from_mu_to_path (tensorProb μ ι) hℓ hℓt f g h hf hg hh

end PathIneq

end TrackB
end RestrictedPolynomials
end
