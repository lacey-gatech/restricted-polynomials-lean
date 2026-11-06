module

public import RestrictedPolynomials.TrackB.ProductFunctionsAux
public import RestrictedPolynomials.TrackB.StabComplex
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.CStab
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Track B: product functions of the K7 recursion (CSP7 `kcsp.tex` L648-767)

CSP_7 `lemma:prod1`, `eq:pjbound`, `lemma:prodn`, `eq:wtp`, `lemma:fstab`. `prod1` goes through an
integer relation (by duality, from `NoNontrivialAbelianEmbeddingPi`) of uniformly bounded cost.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Prod
variable {B : Type} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the product function `x ↦ ∏_j Q_j(x_j)` on `ι → B`. -/
def k7ProdFun (Q : ι → B → ℂ) : (ι → B) → ℂ := fun x => ∏ j, Q j (x j)
end Prod

section Helpers
variable {B : Type} [Fintype B] [DecidableEq B] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq B] in
/-- expectation under a product measure of a product function. -/
private theorem k7_cexpect_pi_prod (ν : FinProb B) (g : ι → B → ℂ) :
    (ν.pi ι).cexpect (fun x => ∏ j, g j (x j)) = ∏ j, ν.cexpect (g j) := by
  unfold FinProb.cexpect
  have h1 : ∀ X : ι → B, (((ν.pi ι).prob X : ℝ) : ℂ) * ∏ j, g j (X j)
      = ∏ j, ((ν.prob (X j) : ℂ) * g j (X j)) := by
    intro X
    rw [Finset.prod_mul_distrib]
    simp [FinProb.pi]
  rw [Finset.sum_congr rfl fun X _ => h1 X]
  exact (Fintype.prod_sum (fun j (a : B) => (ν.prob a : ℂ) * g j a)).symm

/-- the noise kernel is symmetric against `π`. -/
private theorem k7_noise_symm (π : FinProb B) (ρ : ℝ) (a b : B) :
    π.prob a * noiseKernel π ρ a b = π.prob b * noiseKernel π ρ b a := by
  unfold noiseKernel
  by_cases h : a = b
  · subst h; ring
  · simp [h, Ne.symm h]; ring

/-- first marginal of the noise pair. -/
private theorem k7_joint_sum_snd (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : B) :
    ∑ b, (jointNoise π ρ h0 h1).prob (a, b) = π.prob a := by
  simp only [jointNoise, noiseKernel, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    π.sum_eq_one]
  simp

private theorem k7_joint_sum_fst (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (b : B) :
    ∑ a, (jointNoise π ρ h0 h1).prob (a, b) = π.prob b := by
  have : ∀ a, (jointNoise π ρ h0 h1).prob (a, b) = π.prob b * noiseKernel π ρ b a := by
    intro a; exact k7_noise_symm π ρ a b
  simp only [this, ← Finset.mul_sum]
  have h : ∑ a, noiseKernel π ρ b a = 1 := by
    simp only [noiseKernel, Finset.sum_add_distrib, ← Finset.mul_sum, π.sum_eq_one]
    simp
  rw [h, mul_one]

/-- the pair expectation as a double sum. -/
private theorem k7_pair_cexpect (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (G : (ι → B) → (ι → B) → ℂ) :
    ((jointNoise π ρ h0 h1).pi ι).cexpect (fun p => G (fun t => (p t).1) (fun t => (p t).2)) =
      ∑ x, ∑ y, (((π.pi ι).prob x * ∏ i, noiseKernel π ρ (x i) (y i) : ℝ) : ℂ) * G x y := by
  let e : (ι → B × B) ≃ (ι → B) × (ι → B) :=
    Equiv.arrowProdEquivProdArrow ι (fun _ => B) (fun _ => B)
  unfold FinProb.cexpect
  rw [← Fintype.sum_equiv e.symm (fun q : (ι → B) × (ι → B) =>
      (((jointNoise π ρ h0 h1).pi ι).prob (e.symm q) : ℂ) * G q.1 q.2) _ (fun p => by simp [e]),
    Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  have : ((jointNoise π ρ h0 h1).pi ι).prob (e.symm (x, y)) =
      ((π.pi ι).prob x) * ∏ i, noiseKernel π ρ (x i) (y i) := by
    simp only [FinProb.pi, jointNoise, e, prod_mul_distrib]
    rfl
  rw [this]

/-- the first marginal of the pair law is `π^{⊗ι}`. -/
private theorem k7_pair_cexpect_fst (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (G : (ι → B) → ℂ) :
    ((jointNoise π ρ h0 h1).pi ι).cexpect (fun p => G (fun t => (p t).1)) =
      (π.pi ι).cexpect G := by
  refine (k7_pair_cexpect π ρ h0 h1 (ι := ι) (fun x _ => G x)).trans ?_
  unfold FinProb.cexpect
  refine sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  have hs : ∑ y : ι → B, ∏ i, noiseKernel π ρ (x i) (y i) = 1 := by
    rw [← Fintype.prod_sum (fun i b => noiseKernel π ρ (x i) b)]
    have : ∀ a, ∑ b, noiseKernel π ρ a b = 1 := by
      intro a
      simp only [noiseKernel, Finset.sum_add_distrib, ← Finset.mul_sum, π.sum_eq_one]
      simp
    simp [this]
  simp only [Complex.ofReal_mul, ← Finset.mul_sum, ← Complex.ofReal_sum, hs]
  simp
end Helpers

section Linear
variable {B : Type} [Fintype B]

private theorem k7_cexpect_add (ν : FinProb B) (f g : B → ℂ) :
    ν.cexpect (fun a => f a + g a) = ν.cexpect f + ν.cexpect g := by
  unfold FinProb.cexpect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

private theorem k7_cexpect_sub (ν : FinProb B) (f g : B → ℂ) :
    ν.cexpect (fun a => f a - g a) = ν.cexpect f - ν.cexpect g := by
  unfold FinProb.cexpect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

private theorem k7_cexpect_star (ν : FinProb B) (f : B → ℂ) :
    ν.cexpect (fun a => star (f a)) = star (ν.cexpect f) := by
  unfold FinProb.cexpect
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_mul', show star ((ν.prob a : ℝ) : ℂ) = ((ν.prob a : ℝ) : ℂ) from Complex.conj_ofReal _]

private theorem k7_cexpect_const (ν : FinProb B) (c : ℂ) : ν.cexpect (fun _ => c) = c := by
  unfold FinProb.cexpect
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ν.sum_eq_one]
  simp

/-- the norm of an expectation is at most the expectation of the norm. -/
private theorem k7_norm_cexpect_le (ν : FinProb B) (f : B → ℂ) :
    ‖ν.cexpect f‖ ≤ ∑ a, ν.prob a * ‖f a‖ := by
  unfold FinProb.cexpect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.nonneg a)]

/-- Cauchy-Schwarz for the mean of a norm. -/
private theorem k7_sq_sum_norm_le (ν : FinProb B) (g : B → ℝ) :
    (∑ a, ν.prob a * |g a|) ^ 2 ≤ ∑ a, ν.prob a * g a ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => Real.sqrt (ν.prob a))
    (fun a => Real.sqrt (ν.prob a) * |g a|)
  have e1 : ∀ a, Real.sqrt (ν.prob a) * (Real.sqrt (ν.prob a) * |g a|) = ν.prob a * |g a| := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (ν.nonneg a)]
  have e2 : ∀ a, Real.sqrt (ν.prob a) ^ 2 = ν.prob a := fun a => Real.sq_sqrt (ν.nonneg a)
  have e3 : ∀ a, (Real.sqrt (ν.prob a) * |g a|) ^ 2 = ν.prob a * g a ^ 2 := by
    intro a
    rw [mul_pow, e2, sq_abs]
  simp only [e1, e2, e3, ν.sum_eq_one, one_mul] at h
  exact h
end Linear

section Var
variable {B : Type} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
private theorem k7_cexpect_mul_const (ν : FinProb B) (f : B → ℂ) (c : ℂ) :
    ν.cexpect (fun a => f a * c) = ν.cexpect f * c := by
  unfold FinProb.cexpect
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

private theorem k7_norm_sub_sq' (u v : ℂ) :
    ((‖u - v‖ ^ 2 : ℝ) : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) + ((‖v‖ ^ 2 : ℝ) : ℂ) -
      (u * star v + star (u * star v)) := by
  apply Complex.ext <;> simp [Complex.sq_norm, Complex.normSq_apply] <;> ring

private theorem k7_mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [DecidableEq B] in
/-- the variance identity `𝔼‖P - 𝔼P‖² = 𝔼‖P‖² - ‖𝔼P‖²`. -/
private theorem k7_var_identity (π : FinProb B) (P : B → ℂ) :
    ∑ a, π.prob a * ‖P a - π.cexpect P‖ ^ 2 =
      (∑ a, π.prob a * ‖P a‖ ^ 2) - ‖π.cexpect P‖ ^ 2 := by
  apply Complex.ofReal_injective
  have e1 : ((∑ a, π.prob a * ‖P a - π.cexpect P‖ ^ 2 : ℝ) : ℂ) =
      π.cexpect (fun a => ((‖P a - π.cexpect P‖ ^ 2 : ℝ) : ℂ)) := by
    unfold FinProb.cexpect; push_cast; rfl
  have e2 : ((∑ a, π.prob a * ‖P a‖ ^ 2 : ℝ) : ℂ) =
      π.cexpect (fun a => ((‖P a‖ ^ 2 : ℝ) : ℂ)) := by
    unfold FinProb.cexpect; push_cast; rfl
  rw [e1, Complex.ofReal_sub, e2]
  simp only [k7_norm_sub_sq']
  rw [k7_cexpect_sub, k7_cexpect_add, k7_cexpect_add, k7_cexpect_star, k7_cexpect_mul_const,
    k7_cexpect_const, k7_mul_star_self]
  rw [Complex.star_def, Complex.conj_ofReal]
  ring

/-- the one-coordinate noise-pair correlation: `ρ ‖P‖₂² + (1 - ρ) |𝔼 P|²`. -/
private theorem k7_joint_single (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (P : B → ℂ) :
    (jointNoise π ρ h0 h1).cexpect (fun q => P q.1 * star (P q.2)) =
      ((ρ * ∑ a, π.prob a * ‖P a‖ ^ 2 + (1 - ρ) * ‖π.cexpect P‖ ^ 2 : ℝ) : ℂ) := by
  unfold FinProb.cexpect
  rw [Fintype.sum_prod_type]
  have hterm : ∀ a b : B, (((jointNoise π ρ h0 h1).prob (a, b) : ℝ) : ℂ) * (P a * star (P b)) =
      (ρ : ℂ) * ((π.prob a : ℂ) * (if a = b then P a * star (P a) else 0)) +
        ((1 : ℂ) - ρ) * (((π.prob a : ℂ) * P a) * ((π.prob b : ℂ) * star (P b))) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp only [jointNoise, noiseKernel, ite_true]
      push_cast
      ring
    · simp only [jointNoise, noiseKernel, h, ite_false]
      push_cast
      ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  have h2 : ∑ a, (π.prob a : ℂ) * P a * ∑ b, (π.prob b : ℂ) * star (P b) =
      ((‖π.cexpect P‖ ^ 2 : ℝ) : ℂ) := by
    rw [← k7_mul_star_self]
    unfold FinProb.cexpect
    rw [star_sum, ← Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_mul', show star ((π.prob b : ℝ) : ℂ) = ((π.prob b : ℝ) : ℂ) from Complex.conj_ofReal _]
  have h3 : ∑ i, (π.prob i : ℂ) * (P i * star (P i)) = ((∑ a, π.prob a * ‖P a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [k7_mul_star_self]; push_cast; rfl
  rw [h2, h3]
  push_cast
  rfl
end Var

section ProdnLemma
variable {B : Type} [Fintype B] [DecidableEq B] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- CSP_7 `lemma:prodn`, step `tensorize-difference`: for a product function `P = ∏ⱼ Qⱼ`, along the `ρ`-noise pair law,
`𝔼|P(x) - P(y)|² = 2 ∏ⱼ ‖Qⱼ‖₂² - 2 Re ∏ⱼ 𝔼[Qⱼ(xⱼ) conj Qⱼ(yⱼ)]`. -/
theorem k7_prodn_tensorize_difference (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (Q : ι → B → ℂ) :
    ((jointNoise π ρ h0 h1).pi ι).cexpect
        (fun p => ((‖k7ProdFun Q (fun t => (p t).1) - k7ProdFun Q (fun t => (p t).2)‖ ^ 2 : ℝ) : ℂ)) =
      ((2 * ∏ j, (∑ a, π.prob a * ‖Q j a‖ ^ 2) -
        2 * (∏ j, (jointNoise π ρ h0 h1).cexpect fun q => Q j q.1 * star (Q j q.2)).re : ℝ) : ℂ) := by
  have hnorm : ∀ x : ι → B, ((‖k7ProdFun Q x‖ ^ 2 : ℝ) : ℂ) = ∏ j, ((‖Q j (x j)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    unfold k7ProdFun
    rw [norm_prod, ← Finset.prod_pow, Complex.ofReal_prod]
  have hpt : ∀ p : ι → B × B,
      ((‖k7ProdFun Q (fun t => (p t).1) - k7ProdFun Q (fun t => (p t).2)‖ ^ 2 : ℝ) : ℂ) =
        ∏ j, ((‖Q j (p j).1‖ ^ 2 : ℝ) : ℂ) + ∏ j, ((‖Q j (p j).2‖ ^ 2 : ℝ) : ℂ) -
          (∏ j, (Q j (p j).1 * star (Q j (p j).2)) +
            star (∏ j, (Q j (p j).1 * star (Q j (p j).2)))) := by
    intro p
    rw [k7_norm_sub_sq', hnorm, hnorm]
    unfold k7ProdFun
    have hs : ∀ g : ι → ℂ, star (∏ j, g j) = ∏ j, star (g j) :=
      fun g => map_prod (starRingEnd ℂ) g univ
    simp only [hs, Finset.prod_mul_distrib]
  have hfst : ∀ j, (jointNoise π ρ h0 h1).cexpect (fun q => ((‖Q j q.1‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ a, π.prob a * ‖Q j a‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    unfold FinProb.cexpect
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, k7_joint_sum_snd]
  have hsnd : ∀ j, (jointNoise π ρ h0 h1).cexpect (fun q => ((‖Q j q.2‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ a, π.prob a * ‖Q j a‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    unfold FinProb.cexpect
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, k7_joint_sum_fst]
  rw [show (fun p : ι → B × B =>
      ((‖k7ProdFun Q (fun t => (p t).1) - k7ProdFun Q (fun t => (p t).2)‖ ^ 2 : ℝ) : ℂ)) = _ from
    funext hpt]
  rw [k7_cexpect_sub, k7_cexpect_add, k7_cexpect_add, k7_cexpect_star,
    k7_cexpect_pi_prod (jointNoise π ρ h0 h1) (fun j q => ((‖Q j q.1‖ ^ 2 : ℝ) : ℂ)),
    k7_cexpect_pi_prod (jointNoise π ρ h0 h1) (fun j q => ((‖Q j q.2‖ ^ 2 : ℝ) : ℂ)),
    k7_cexpect_pi_prod (jointNoise π ρ h0 h1) (fun j q => Q j q.1 * star (Q j q.2))]
  simp only [hfst, hsnd]
  rw [← Complex.ofReal_prod]
  have := Complex.add_conj (∏ j, (jointNoise π ρ h0 h1).cexpect fun q => Q j q.1 * star (Q j q.2))
  have h2 : (∏ j, (jointNoise π ρ h0 h1).cexpect fun q => Q j q.1 * star (Q j q.2)) +
      star (∏ j, (jointNoise π ρ h0 h1).cexpect fun q => Q j q.1 * star (Q j q.2)) =
      ((2 * (∏ j, (jointNoise π ρ h0 h1).cexpect fun q => Q j q.1 * star (Q j q.2)).re : ℝ) : ℂ) :=
    this
  rw [h2]
  push_cast
  ring
end ProdnLemma

section FstabStab
variable {B : Type} [Fintype B] [DecidableEq B] {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped ComplexOrder in
private theorem k7_re_cstab_mono (π : FinProb B) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ')
    (f : (ι → B) → ℂ) : (cstab π ρ f).re ≤ (cstab π ρ' f).re :=
  (Complex.le_def.1 (cstab_mono π h0 h f)).1

/-- the pair expectation of `f(x) P(y)` is `𝔼_y P(y) N_ρ f(y)`. -/
private theorem k7_pair_fx_Py (π : FinProb B) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (f P : (ι → B) → ℂ) :
    ((jointNoise π ρ h0 h1).pi ι).cexpect (fun p => f (fun t => (p t).1) * P (fun t => (p t).2)) =
      (π.pi ι).cexpect (fun y => P y * cnoiseOp π ρ f y) := by
  refine (k7_pair_cexpect π ρ h0 h1 (ι := ι) (fun x y => f x * P y)).trans ?_
  unfold FinProb.cexpect cnoiseOp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  beta_reduce
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hs : (π.pi ι).prob x * ∏ i, noiseKernel π ρ (x i) (y i) =
      (π.pi ι).prob y * ∏ i, noiseKernel π ρ (y i) (x i) := by
    simp only [FinProb.pi, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => k7_noise_symm π ρ (x i) (y i)
  rw [hs]
  push_cast
  ring

/-- CSP_7 `lemma:fstab`, step `to-stability` (Cauchy-Schwarz gives `Stab_{ρ²}`, and `Stab` is nondecreasing in
`ρ`, `cstab_mono`): if `δ/2 ≤ |𝔼_{(x,y) ∼ noise pair} f(x) P̃(y)|` with `P̃` `1`-bounded, then
`(δ/2)² ≤ Re Stab_ρ(f)`. -/
theorem k7_fstab_to_stability {B : Type} [Fintype B] [DecidableEq B] {ι : Type} [Fintype ι]
    [DecidableEq ι] (π : FinProb B) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f P : (ι → B) → ℂ)
    (hP : ∀ x, ‖P x‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : δ / 2 ≤ ‖((jointNoise π ρ h0 h1).pi ι).cexpect fun p =>
      f (fun t => (p t).1) * P (fun t => (p t).2)‖) :
    (δ / 2) ^ 2 ≤ (cstab π ρ f).re := by
  rw [k7_pair_fx_Py] at h
  have h2 : ‖(π.pi ι).cexpect (fun y => P y * cnoiseOp π ρ f y)‖ ≤
      ∑ y, (π.pi ι).prob y * |‖cnoiseOp π ρ f y‖| := by
    refine (k7_norm_cexpect_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hP y))
      ((π.pi ι).nonneg y)
  have h3 := k7_sq_sum_norm_le (π.pi ι) (fun y => ‖cnoiseOp π ρ f y‖)
  have h4 : ∑ y, (π.pi ι).prob y * ‖cnoiseOp π ρ f y‖ ^ 2 = cl2sq π (cnoiseOp π ρ f) := rfl
  rw [cl2sq_cnoiseOp π h0] at h4
  have h5 : (cstab π (ρ ^ 2) f).re ≤ (cstab π ρ f).re :=
    k7_re_cstab_mono π (sq_nonneg ρ) (by nlinarith) f
  have h6 : δ / 2 ≤ ∑ y, (π.pi ι).prob y * |‖cnoiseOp π ρ f y‖| := h.trans h2
  have h7 : (δ / 2) ^ 2 ≤ (∑ y, (π.pi ι).prob y * |‖cnoiseOp π ρ f y‖|) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h6 2
  linarith
end FstabStab

section Fstab
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- CSP_7 `eq:wtp` and its Cauchy-Schwarz companion (the second line needs the conjugate):
for the tuple `F` with `F i = ∏ⱼ Q i j` for `i ≠ s`, the conditional-expectation function
`P̃ = f̃_s` has `δ ≤ |𝔼_{x ∼ μ_s^{⊗ι}} F_s(x) P̃(x)|` and `δ² ≤ ‖P̃‖₂²`. -/
theorem k7_fstab_eq_wtp (μ : FinProb (∀ i, A i)) (s : Fin k) (F : ∀ i, (ι → A i) → ℂ)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorr : δ ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, F i fun t => X t i‖) :
    δ ≤ ‖((μ.marginalPi s).pi ι).cexpect fun x => replaceCondProdExp μ F s x * F s x‖ ∧
      δ ^ 2 ≤ ∑ x, ((μ.marginalPi s).pi ι).prob x * ‖replaceCondProdExp μ F s x‖ ^ 2 := by
  refine ⟨?_, replace_eps_sq_le_l2sq μ F hF s hδ hcorr⟩
  rw [← replace_cexpect_prod_eq]
  exact hcorr
end Fstab

section UnitCalculus
private theorem k7_unit_mul_sub_one {z w : ℂ} (hz : ‖z‖ = 1) (_hw : ‖w‖ = 1) :
    ‖z * w - 1‖ ≤ ‖z - 1‖ + ‖w - 1‖ := by
  have h : z * w - 1 = z * (w - 1) + (z - 1) := by ring
  rw [h]
  calc ‖z * (w - 1) + (z - 1)‖ ≤ ‖z * (w - 1)‖ + ‖z - 1‖ := norm_add_le _ _
    _ = ‖w - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
    _ = _ := add_comm _ _

private theorem k7_unit_inv_sub_one {z : ℂ} (hz : ‖z‖ = 1) : ‖z⁻¹ - 1‖ = ‖z - 1‖ := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have h : z⁻¹ - 1 = z⁻¹ * (1 - z) := by field_simp
  rw [h, norm_mul, norm_inv, hz, inv_one, one_mul, norm_sub_rev]

private theorem k7_unit_zpow_sub_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℤ) :
    ‖z ^ n - 1‖ ≤ |(n : ℝ)| * ‖z - 1‖ := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have ih' : ‖z ^ (i : ℤ) - 1‖ ≤ (i : ℝ) * ‖z - 1‖ := by simpa using ih
    have h1 : ‖z ^ (i : ℤ)‖ = 1 := by rw [norm_zpow, hz, one_zpow]
    have := k7_unit_mul_sub_one h1 hz
    rw [← zpow_add_one₀ hz0] at this
    have h2 : |(((i : ℤ) + 1 : ℤ) : ℝ)| = (i : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    rw [h2]
    nlinarith [norm_nonneg (z - 1)]
  | pred i ih =>
    have ih' : ‖z ^ (-(i : ℤ)) - 1‖ ≤ (i : ℝ) * ‖z - 1‖ := by simpa using ih
    have h1 : ‖z ^ (-(i : ℤ))‖ = 1 := by rw [norm_zpow, hz, one_zpow]
    have h3 : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
    have := k7_unit_mul_sub_one h1 h3
    rw [k7_unit_inv_sub_one hz, ← zpow_neg_one, ← zpow_add₀ hz0] at this
    have h2 : |((-(i : ℤ) - 1 : ℤ) : ℝ)| = (i : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonpos (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])]
      ring
    rw [h2]
    have h4 : -(i : ℤ) + -1 = -(i : ℤ) - 1 := by ring
    rw [h4] at this
    nlinarith [norm_nonneg (z - 1)]

private theorem k7_unit_prod_sub_one {X : Type} (s : Finset X) (z : X → ℂ)
    (hz : ∀ x ∈ s, ‖z x‖ = 1) : ‖∏ x ∈ s, z x - 1‖ ≤ ∑ x ∈ s, ‖z x - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hs : ‖∏ x ∈ s, z x‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one fun x hx => hz x (Finset.mem_insert_of_mem hx)
    have := k7_unit_mul_sub_one (hz a (Finset.mem_insert_self a s)) hs
    exact this.trans (by linarith [ih fun x hx => hz x (Finset.mem_insert_of_mem hx)])

private theorem k7_zpow_sum {X : Type} (s : Finset X) (u : ℂ) (hu : u ≠ 0) (e : X → ℤ) :
    ∏ x ∈ s, u ^ e x = u ^ (∑ x ∈ s, e x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hu, ih]
end UnitCalculus

section Relation
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- the indicator vector `ind x (j, c) = 1[x_j = c]` in `ℤ^{Σ_j A_j}`. -/
private def k7Ind (x : ∀ i, A i) : (Σ j, A j) → ℤ := fun σ => if x σ.1 = σ.2 then 1 else 0

/-- the target vector `e_{(i,a)} - e_{(i,b)}`. -/
private def k7Tgt (i : Fin k) (a b : A i) : (Σ j, A j) → ℤ :=
  fun σ => (if σ = ⟨i, a⟩ then 1 else 0) - (if σ = ⟨i, b⟩ then 1 else 0)

/-- an integer relation of cost at most `D`, supported on `S`. -/
private def K7Rel (S : Set (∀ i, A i)) (i : Fin k) (a b : A i) (D : ℕ) : Prop :=
  ∃ d : (∀ i, A i) → ℤ, (∀ x, x ∉ S → d x = 0) ∧ ∑ x, |d x| ≤ (D : ℤ) ∧
    ∀ σ, ∑ x, d x * k7Ind x σ = k7Tgt i a b σ

private theorem k7_sum_zero_of_rel (i : Fin k) (a b : A i) (d : (∀ i, A i) → ℤ)
    (hd : ∀ σ, ∑ x, d x * k7Ind x σ = k7Tgt i a b σ) : ∑ x, d x = 0 := by
  have h1 : ∑ c : A i, ∑ x, d x * k7Ind x ⟨i, c⟩ = ∑ x, d x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]
    simp [k7Ind]
  have h2 : ∑ c : A i, k7Tgt i a b ⟨i, c⟩ = 0 := by
    simp [k7Tgt, Finset.sum_sub_distrib]
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl fun c _ => hd _

/-- the multiplicative form of a relation. -/
private theorem k7_prod_zpow_of_rel (u : ∀ j, A j → ℂ) (hu : ∀ j c, u j c ≠ 0)
    (i : Fin k) (a b : A i) (d : (∀ i, A i) → ℤ)
    (hd : ∀ σ, ∑ x, d x * k7Ind x σ = k7Tgt i a b σ) :
    ∏ x, (∏ j, u j (x j)) ^ d x = u i a / u i b := by
  have h1 : ∀ x : ∀ i, A i, (∏ j, u j (x j)) ^ d x = ∏ j, u j (x j) ^ d x := fun x =>
    (prod_zpow _ _ _).symm
  simp only [h1]
  rw [Finset.prod_comm]
  have h2 : ∀ j : Fin k, ∏ x : ∀ i, A i, u j (x j) ^ d x =
      ∏ c : A j, u j c ^ (∑ x, d x * k7Ind x ⟨j, c⟩) := by
    intro j
    rw [← Finset.prod_fiberwise Finset.univ (fun x : ∀ i, A i => x j)
      (fun x => u j (x j) ^ d x)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
    rw [k7_zpow_sum _ _ (hu j c)]
    congr 1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x j = c <;> simp [k7Ind, h]
  simp only [h2, hd]
  have h3 : ∏ j, ∏ c, u j c ^ k7Tgt i a b ⟨j, c⟩ =
      ∏ σ : Σ j, A j, u σ.1 σ.2 ^ k7Tgt i a b σ :=
    (Fintype.prod_sigma (fun σ : Σ j, A j => u σ.1 σ.2 ^ k7Tgt i a b σ)).symm
  rw [h3]
  have e : ∀ (τ σ : Σ j, A j), u σ.1 σ.2 ^ (if σ = τ then (1 : ℤ) else 0) =
      if σ = τ then u τ.1 τ.2 else 1 := by
    intro τ σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have h4 : ∀ σ : Σ j, A j, u σ.1 σ.2 ^ k7Tgt i a b σ =
      (if σ = ⟨i, a⟩ then u i a else 1) / (if σ = ⟨i, b⟩ then u i b else 1) := by
    intro σ
    unfold k7Tgt
    rw [zpow_sub₀ (hu _ _), e, e]
  simp only [h4]
  rw [Finset.prod_div_distrib]
  simp [Finset.prod_ite_eq']

/-- the analytic core: a unit-modulus family whose product is `ε`-close to a unit `ζ` on `S`, and a
relation supported on `S`, give `‖u_i a - u_i b‖ ≤ (∑ |d|) ε`. -/
private theorem k7_unit_relation (u : ∀ j, A j → ℂ) (hu : ∀ j c, ‖u j c‖ = 1)
    {S : Set (∀ i, A i)} {ζ : ℂ} (hζ : ‖ζ‖ = 1) {ε : ℝ}
    (hε : ∀ x ∈ S, ‖∏ j, u j (x j) - ζ‖ ≤ ε) (i : Fin k) (a b : A i)
    (d : (∀ i, A i) → ℤ) (hd0 : ∀ x, x ∉ S → d x = 0)
    (hd : ∀ σ, ∑ x, d x * k7Ind x σ = k7Tgt i a b σ) :
    ‖u i a - u i b‖ ≤ (∑ x, |(d x : ℝ)|) * ε := by
  have hu0 : ∀ j c, u j c ≠ 0 := fun j c h => by have := hu j c; rw [h] at this; simp at this
  have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hζ; simp at hζ
  have hW : ∀ x : ∀ i, A i, ‖∏ j, u j (x j)‖ = 1 := fun x => by
    rw [norm_prod]; exact Finset.prod_eq_one fun j _ => hu j _
  have hWz : ∀ x : ∀ i, A i, ‖(∏ j, u j (x j)) / ζ‖ = 1 := fun x => by
    rw [norm_div, hW, hζ, div_one]
  have hq : ∀ x : ∀ i, A i, ‖((∏ j, u j (x j)) / ζ) ^ d x‖ = 1 := fun x => by
    rw [norm_zpow, hWz, one_zpow]
  have h1 := k7_unit_prod_sub_one Finset.univ (fun x => ((∏ j, u j (x j)) / ζ) ^ d x)
    (fun x _ => hq x)
  have h2 : ∀ x : ∀ i, A i, ‖((∏ j, u j (x j)) / ζ) ^ d x - 1‖ ≤ |(d x : ℝ)| * ε := by
    intro x
    by_cases hx : x ∈ S
    · refine (k7_unit_zpow_sub_one (hWz x) (d x)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have : (∏ j, u j (x j)) / ζ - 1 = ((∏ j, u j (x j)) - ζ) / ζ := by field_simp
      rw [this, norm_div, hζ, div_one]
      exact hε x hx
    · rw [hd0 x hx]; simp
  have h3 : ∏ x, ((∏ j, u j (x j)) / ζ) ^ d x = u i a / u i b := by
    simp only [div_zpow]
    rw [Finset.prod_div_distrib, k7_prod_zpow_of_rel u hu0 i a b d hd,
      k7_zpow_sum _ _ hζ0, k7_sum_zero_of_rel i a b d hd]
    simp
  rw [h3] at h1
  have h4 : ‖u i a / u i b - 1‖ = ‖u i a - u i b‖ := by
    have : u i a / u i b - 1 = (u i a - u i b) / u i b := by field_simp [hu0 i b]
    rw [this, norm_div, hu, div_one]
  rw [h4] at h1
  refine h1.trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun x _ => h2 x
end Relation

section Duality
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

private theorem k7Ind_eq_sum_single (x : ∀ i, A i) :
    k7Ind x = ∑ j, (Pi.single (⟨j, x j⟩ : Σ j, A j) (1 : ℤ) : (Σ j, A j) → ℤ) := by
  funext σ
  obtain ⟨j', c⟩ := σ
  rw [Finset.sum_apply, Finset.sum_eq_single j']
  · by_cases h : x j' = c
    · subst h; simp [k7Ind]
    · have : (⟨j', c⟩ : Σ j, A j) ≠ ⟨j', x j'⟩ := fun h' => h (by simpa using h'.symm)
      simp [k7Ind, h, Pi.single_apply, this]
  · intro j _ hj
    have : (⟨j', c⟩ : Σ j, A j) ≠ ⟨j, x j⟩ := fun h' => hj (Sigma.mk.inj_iff.1 h'.symm).1
    simp [Pi.single_apply, this]
  · simp

omit [∀ i, Fintype (A i)] in
private theorem k7Tgt_eq (i : Fin k) (a b : A i) :
    k7Tgt i a b = (Pi.single (⟨i, a⟩ : Σ j, A j) (1 : ℤ) : (Σ j, A j) → ℤ) -
      Pi.single (⟨i, b⟩ : Σ j, A j) (1 : ℤ) := by
  funext σ
  simp [k7Tgt, Pi.single_apply]

/-- duality: with no nontrivial abelian embedding, `e_{(i,a)} - e_{(i,b)}` is an integer combination
of the indicator vectors of points of `S`. -/
private theorem k7_rel_exists {S : Set (∀ i, A i)} (h : NoNontrivialAbelianEmbeddingPi S)
    (i : Fin k) (a b : A i) : ∃ D : ℕ, K7Rel S i a b D := by
  classical
  set M : Submodule ℤ ((Σ j, A j) → ℤ) := Submodule.span ℤ (k7Ind '' S) with hM
  have hemb : ∀ x ∈ S, ∑ j, M.mkQ (Pi.single (⟨j, x j⟩ : Σ j, A j) (1 : ℤ)) = 0 := by
    intro x hx
    rw [← map_sum, ← k7Ind_eq_sum_single, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have key := h (((Σ j, A j) → ℤ) ⧸ M) (fun j c => M.mkQ (Pi.single (⟨j, c⟩ : Σ j, A j) (1 : ℤ)))
    hemb i a b
  have hmem : k7Tgt i a b ∈ M := by
    rw [k7Tgt_eq, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    have := key
    simp only [Submodule.mkQ_apply] at this
    rw [this, sub_self]
  set s : Finset (∀ i, A i) := Finset.univ.filter (· ∈ S) with hs
  have hcoe : (↑s : Set (∀ i, A i)) = S := by
    ext x; simp [hs]
  rw [hM, ← hcoe, Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨(∑ x, |(if x ∈ s then c x else 0)|).toNat, fun x => if x ∈ s then c x else 0, ?_, ?_, ?_⟩
  · intro x hx
    have : x ∉ s := fun h' => hx (by rw [← hcoe]; exact h')
    simp [this]
  · exact Int.self_le_toNat _
  · intro σ
    have := congrFun hc σ
    rw [← this, Finset.sum_apply]
    have e1 : ∀ x, (if x ∈ s then c x else 0) * k7Ind x σ =
        if x ∈ s then (c x • k7Ind x) σ else 0 := by
      intro x
      by_cases hx : x ∈ s <;> simp [hx]
    simp only [e1]
    rw [Finset.sum_ite_mem]
    simp
end Duality

section Transport
variable {k : ℕ} {A A' : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (A' i)] [∀ i, DecidableEq (A' i)]

omit [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (A' i)]
  in
private theorem k7_sigma_map_eq_iff (φ : ∀ i, A i → A' i) (hφ : ∀ i, Function.Injective (φ i))
    (j i : Fin k) (c : A j) (a : A i) :
    ((⟨j, φ j c⟩ : Σ j, A' j) = ⟨i, φ i a⟩) ↔ ((⟨j, c⟩ : Σ j, A j) = ⟨i, a⟩) := by
  constructor
  · intro h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
    have := hφ j (eq_of_heq h2)
    rw [this]
  · intro h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
    rw [eq_of_heq h2]

private theorem k7_tgt_map (φ : ∀ i, A i → A' i) (hφ : ∀ i, Function.Injective (φ i))
    (i j : Fin k) (a b : A i) (c : A j) :
    k7Tgt i (φ i a) (φ i b) ⟨j, φ j c⟩ = k7Tgt i a b ⟨j, c⟩ := by
  unfold k7Tgt
  simp only [k7_sigma_map_eq_iff φ hφ]

private theorem k7_ind_map (φ : ∀ i, A i → A' i) (hφ : ∀ i, Function.Injective (φ i))
    (x : ∀ i, A i) (j : Fin k) (c : A j) :
    k7Ind (fun i => φ i (x i)) ⟨j, φ j c⟩ = k7Ind x ⟨j, c⟩ := by
  unfold k7Ind
  simp only [(hφ j).eq_iff]

/-- transport of relations along injective relabellings of the alphabets. -/
private theorem k7Rel_map_iff (φ : ∀ i, A i → A' i) (hφ : ∀ i, Function.Injective (φ i))
    (S : Set (∀ i, A i)) (i : Fin k) (a b : A i) (D : ℕ) :
    K7Rel S i a b D ↔ K7Rel ((fun x i => φ i (x i)) '' S) i (φ i a) (φ i b) D := by
  classical
  set Φ : (∀ i, A i) → (∀ i, A' i) := fun x i => φ i (x i) with hΦ
  have hΦi : Function.Injective Φ := fun x y h => funext fun i => hφ i (congrFun h i)
  constructor
  · rintro ⟨d, hd0, hdD, hd⟩
    set d' : (∀ i, A' i) → ℤ := Function.extend Φ d 0 with hd'
    have hd'Φ : ∀ x, d' (Φ x) = d x := fun x => hΦi.extend_apply d 0 x
    have hd'0 : ∀ y, y ∉ Set.range Φ → d' y = 0 := by
      intro y hy
      rw [hd', Function.extend_apply' _ _ _ (by simpa using hy)]
      rfl
    refine ⟨d', ?_, ?_, ?_⟩
    · intro y hy
      by_cases hr : y ∈ Set.range Φ
      · obtain ⟨x, rfl⟩ := hr
        rw [hd'Φ]
        exact hd0 x fun hx => hy ⟨x, hx, rfl⟩
      · exact hd'0 y hr
    · have : ∑ y, |d' y| = ∑ x, |d x| :=
        (Fintype.sum_of_injective Φ hΦi (fun x => |d x|) (fun y => |d' y|)
          (fun y hy => by rw [hd'0 y hy]; simp) (fun x => by rw [hd'Φ])).symm
      rw [this]; exact hdD
    · rintro ⟨j, c'⟩
      have hsum : ∑ y, d' y * k7Ind y ⟨j, c'⟩ = ∑ x, d x * k7Ind (Φ x) ⟨j, c'⟩ :=
        (Fintype.sum_of_injective Φ hΦi (fun x => d x * k7Ind (Φ x) ⟨j, c'⟩)
          (fun y => d' y * k7Ind y ⟨j, c'⟩)
          (fun y hy => by rw [hd'0 y hy]; simp) (fun x => by rw [hd'Φ])).symm
      rw [hsum]
      by_cases hc : ∃ c, φ j c = c'
      · obtain ⟨c, rfl⟩ := hc
        rw [k7_tgt_map φ hφ, ← hd ⟨j, c⟩]
        exact Finset.sum_congr rfl fun x _ => by rw [hΦ, k7_ind_map φ hφ]
      · push Not at hc
        have h1 : ∀ x, k7Ind (Φ x) ⟨j, c'⟩ = 0 := by
          intro x
          unfold k7Ind
          simp [hΦ, hc (x j)]
        have h2 : k7Tgt i (φ i a) (φ i b) ⟨j, c'⟩ = 0 := by
          unfold k7Tgt
          have e : ∀ e : A i, (⟨j, c'⟩ : Σ j, A' j) ≠ ⟨i, φ i e⟩ := by
            intro e h
            obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
            exact hc e (eq_of_heq h2).symm
          simp [e]
        rw [h2]
        simp [h1]
  · rintro ⟨d', hd0, hdD, hd⟩
    refine ⟨fun x => d' (Φ x), ?_, ?_, ?_⟩
    · intro x hx
      exact hd0 _ fun h => hx (by
        obtain ⟨x', hx', hxx⟩ := h
        rw [← hΦi hxx]; exact hx')
    · have : ∑ y, |d' y| = ∑ x, |d' (Φ x)| :=
        Fintype.sum_of_injective Φ hΦi (fun x => |d' (Φ x)|) (fun y => |d' y|)
          (fun y hy => by
            rw [hd0 y fun h => hy (by obtain ⟨x, _, rfl⟩ := h; exact ⟨x, rfl⟩)]; simp)
          (fun x => rfl) |>.symm
      rw [← this]; exact hdD
    · rintro ⟨j, c⟩
      have hsum : ∑ y, d' y * k7Ind y ⟨j, φ j c⟩ = ∑ x, d' (Φ x) * k7Ind (Φ x) ⟨j, φ j c⟩ :=
        (Fintype.sum_of_injective Φ hΦi (fun x => d' (Φ x) * k7Ind (Φ x) ⟨j, φ j c⟩)
          (fun y => d' y * k7Ind y ⟨j, φ j c⟩)
          (fun y hy => by
            rw [hd0 y fun h => hy (by obtain ⟨x, _, rfl⟩ := h; exact ⟨x, rfl⟩)]; simp)
          (fun x => rfl)).symm
      have := hd ⟨j, φ j c⟩
      rw [hsum, k7_tgt_map φ hφ] at this
      rw [← this]
      exact Finset.sum_congr rfl fun x _ => by rw [hΦ, k7_ind_map φ hφ]
end Transport

section Uniform
private theorem k7Rel_mono {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    {S : Set (∀ i, A i)} {i : Fin k} {a b : A i} {D D' : ℕ} (h : K7Rel S i a b D) (hD : D ≤ D') :
    K7Rel S i a b D' := by
  obtain ⟨d, h0, h1, h2⟩ := h
  exact ⟨d, h0, h1.trans (by exact_mod_cast hD), h2⟩

open Classical in
/-- the finite maximum, over all supports on `Fin k → Fin N` and all pairs of letters for which a
relation exists, of the least cost. -/
private def k7Dmax (k N : ℕ) : ℕ :=
  Finset.univ.sup (fun t : Finset (Fin k → Fin N) × Fin k × Fin N × Fin N =>
    if h : ∃ n, K7Rel (A := fun _ : Fin k => Fin N) (↑t.1 : Set (Fin k → Fin N)) t.2.1 t.2.2.1
        t.2.2.2 n then Nat.find h else 0)

/-- the uniform cost bound: a relation on any alphabets of size at most `N` can be taken of cost at
most `k7Dmax k N`. -/
private theorem k7_dmax_spec {k N : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] (hcard : ∀ i, Fintype.card (A i) ≤ N) {S : Set (∀ i, A i)}
    {i : Fin k} {a b : A i} {D : ℕ} (h : K7Rel S i a b D) : K7Rel S i a b (k7Dmax k N) := by
  classical
  let φ : ∀ i, A i → Fin N := fun i c => Fin.castLE (hcard i) (Fintype.equivFin (A i) c)
  have hφ : ∀ i, Function.Injective (φ i) := fun i c c' h =>
    (Fintype.equivFin (A i)).injective (Fin.castLE_injective (hcard i) h)
  have h1 := (k7Rel_map_iff φ hφ S i a b D).1 h
  set S' : Finset (Fin k → Fin N) :=
    Finset.univ.filter (· ∈ ((fun x i => φ i (x i)) '' S)) with hS'
  have hcoe : (↑S' : Set (Fin k → Fin N)) = (fun x i => φ i (x i)) '' S := by
    ext x; simp [hS']
  rw [← hcoe] at h1
  have hex : ∃ n, K7Rel (A := fun _ : Fin k => Fin N) (↑S' : Set (Fin k → Fin N)) i (φ i a) (φ i b)
      n := ⟨D, h1⟩
  have hle : (if h : ∃ n, K7Rel (A := fun _ : Fin k => Fin N) (↑S' : Set (Fin k → Fin N)) i
      (φ i a) (φ i b) n then Nat.find h else 0) ≤ k7Dmax k N :=
    Finset.le_sup (f := fun t : Finset (Fin k → Fin N) × Fin k × Fin N × Fin N =>
      if h : ∃ n, K7Rel (A := fun _ : Fin k => Fin N) (↑t.1 : Set (Fin k → Fin N)) t.2.1 t.2.2.1
        t.2.2.2 n then Nat.find h else 0) (Finset.mem_univ (S', i, φ i a, φ i b))
  rw [dif_pos hex] at hle
  have h2 := k7Rel_mono (Nat.find_spec hex) hle
  rw [hcoe] at h2
  exact (k7Rel_map_iff φ hφ S i a b _).2 h2
end Uniform

section PhaseBound
/-- `‖W - ζ‖` and `‖W‖` are controlled by `Re (conj ζ · W)`. -/
private theorem k7_phase_close {W ζ : ℂ} (hζ : ‖ζ‖ = 1) (hW : ‖W‖ ≤ 1) {ε : ℝ}
    (h : 1 - ε ≤ (star ζ * W).re) : 1 - ε ≤ ‖W‖ ∧ ‖W - ζ‖ ≤ Real.sqrt (2 * ε) := by
  have h1 : (star ζ * W).re ≤ ‖W‖ := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.star_def, Complex.norm_conj, hζ, one_mul]
  refine ⟨by linarith, ?_⟩
  apply Real.le_sqrt_of_sq_le
  have h2 : ‖W - ζ‖ ^ 2 = ‖W‖ ^ 2 + 1 - 2 * (star ζ * W).re := by
    have e : ‖ζ‖ ^ 2 = 1 := by rw [hζ]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at e ⊢
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.star_def, Complex.mul_re] at *
    nlinarith [e]
  rw [h2]
  nlinarith [norm_nonneg W]

/-- there is a unit `ζ` with `Re (conj ζ · W y) ≥ 1 - η/α` on the whole support. -/
private theorem k7_phase_bound {X : Type} [Fintype X] (μ : FinProb X) (W : X → ℂ)
    (hW : ∀ y, ‖W y‖ ≤ 1) {α η : ℝ} (hα : 0 < α) (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (hcorr : 1 - η ≤ ‖μ.cexpect W‖) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ y ∈ μ.support, 1 - η / α ≤ (star ζ * W y).re := by
  classical
  set E := μ.cexpect W with hE
  obtain ⟨ζ, hζ, hζE⟩ : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ (star ζ * E).re = ‖E‖ := by
    by_cases h0 : E = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · refine ⟨E / (‖E‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0)]
      · have hn : (‖E‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
        have : star (E / (‖E‖ : ℂ)) * E = ((‖E‖ : ℝ) : ℂ) := by
          rw [Complex.star_def, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div,
            Complex.conj_mul']
          field_simp
        rw [this, Complex.ofReal_re]
  refine ⟨ζ, hζ, ?_⟩
  have hterm : ∀ y, (star ζ * W y).re ≤ 1 := fun y => by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.star_def, Complex.norm_conj, hζ, one_mul]
    exact hW y
  have hsum : ∑ y, μ.prob y * (star ζ * W y).re = ‖E‖ := by
    rw [← hζE, hE]
    unfold FinProb.cexpect
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show star ζ * ((μ.prob y : ℂ) * W y) = (μ.prob y : ℂ) * (star ζ * W y) by ring,
      Complex.re_ofReal_mul]
  have hsum2 : ∑ y, μ.prob y * (1 - (star ζ * W y).re) ≤ η := by
    have : ∑ y, μ.prob y * (1 - (star ζ * W y).re) = 1 - ‖E‖ := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, μ.sum_eq_one, hsum]
    rw [this]; linarith
  intro y hy
  have h1 : μ.prob y * (1 - (star ζ * W y).re) ≤ η :=
    (Finset.single_le_sum (f := fun y => μ.prob y * (1 - (star ζ * W y).re))
      (fun y _ => mul_nonneg (μ.nonneg y) (by linarith [hterm y])) (Finset.mem_univ y)).trans hsum2
  have h2 : α * (1 - (star ζ * W y).re) ≤ η :=
    (mul_le_mul_of_nonneg_right (hatom y hy) (by linarith [hterm y])).trans h1
  have h3 : 1 - (star ζ * W y).re ≤ η / α := by
    rw [le_div_iff₀ hα]; linarith
  linarith
end PhaseBound

section Prod1Core
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- the core of `prod1`: given a uniform relation bound `D`. -/
private theorem k7_prod1_core (μ : FinProb (∀ i, A i))
    (hno : NoNontrivialAbelianEmbeddingPi μ.support) {α : ℝ} (hα : 0 < α)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a) (D : ℕ)
    (hrel : ∀ (i : Fin k) (a b : A i), K7Rel μ.support i a b D)
    (P : ∀ i, A i → ℂ) (hP : ∀ i a, ‖P i a‖ ≤ 1) {η : ℝ} (hη : 0 < η)
    (hcorr : 1 - η ≤ ‖μ.cexpect fun y => ∏ i, P i (y i)‖) (i : Fin k) (x y : A i) :
    1 - ((3 * D + 3) / α) * η ≤ ‖P i x‖ ∧
      ‖P i x - P i y‖ ≤ ((3 * D + 3) / α) * Real.sqrt η := by
  classical
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  -- `α ≤ 1`
  have hne : ∃ a, a ∈ μ.support := by
    by_contra hcon
    push Not at hcon
    have : ∀ a, μ.prob a = 0 := fun a => by
      by_contra h; exact hcon a h
    have h1 := μ.sum_eq_one
    simp [this] at h1
  obtain ⟨a0, ha0⟩ := hne
  have hα1 : α ≤ 1 := by
    have h1 : μ.prob a0 ≤ 1 := by
      rw [← μ.sum_eq_one]
      exact Finset.single_le_sum (f := μ.prob) (fun a _ => μ.nonneg a) (Finset.mem_univ a0)
    exact (hatom a0 ha0).trans h1
  set C : ℝ := (3 * D + 3) / α with hC
  have hCα : 3 / α ≤ C := by
    rw [hC]; exact div_le_div_of_nonneg_right (by linarith) hα.le
  by_cases hηα : α ≤ η
  · -- trivial range
    have h1 : 1 ≤ C * η := by
      have : 3 ≤ C * η := by
        calc (3 : ℝ) = 3 / α * α := by field_simp
          _ ≤ C * η := mul_le_mul hCα hηα hα.le (by linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 3) hα.le])
      linarith
    have h2 : 2 ≤ C * Real.sqrt η := by
      have hs : α ≤ Real.sqrt η := by
        calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
          _ ≤ Real.sqrt η := Real.sqrt_le_sqrt (by nlinarith)
      have : 3 ≤ C * Real.sqrt η := by
        calc (3 : ℝ) = 3 / α * α := by field_simp
          _ ≤ C * Real.sqrt η :=
            mul_le_mul hCα hs hα.le (by linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 3) hα.le])
      linarith
    refine ⟨by linarith [norm_nonneg (P i x)], ?_⟩
    calc ‖P i x - P i y‖ ≤ ‖P i x‖ + ‖P i y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hP i x) (hP i y)
      _ ≤ _ := by linarith
  · push Not at hηα
    set ε₀ : ℝ := η / α with hε₀
    have hε0pos : 0 < ε₀ := div_pos hη hα
    have hε0lt : ε₀ < 1 := by rw [hε₀, div_lt_one hα]; exact hηα
    set W : (∀ i, A i) → ℂ := fun y => ∏ i, P i (y i) with hW
    have hW1 : ∀ y, ‖W y‖ ≤ 1 := fun y => by
      rw [hW]; dsimp only; rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hP j _
    obtain ⟨ζ, hζ, hζW⟩ := k7_phase_bound μ W hW1 hα hatom hcorr
    have hcl := fun y hy => k7_phase_close hζ (hW1 y) (hζW y hy)
    -- every letter occurs in the support
    have hocc : ∀ (j : Fin k) (c : A j), ∃ t ∈ μ.support, t j = c := by
      intro j c
      have hpos := full_marginal_support μ hno j c
      have hpos' : 0 < ∑ t with t j = c, μ.prob t := hpos
      obtain ⟨t, ht, htp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos'.ne'
      exact ⟨t, htp, (Finset.mem_filter.1 ht).2⟩
    have hlow : ∀ (j : Fin k) (c : A j), 1 - ε₀ ≤ ‖P j c‖ := by
      intro j c
      obtain ⟨t, ht, htc⟩ := hocc j c
      have h1 := (hcl t ht).1
      have h2 : ‖W t‖ ≤ ‖P j (t j)‖ := by
        rw [hW]; dsimp only; rw [norm_prod,
          ← Finset.mul_prod_erase Finset.univ (fun l => ‖P l (t l)‖) (Finset.mem_univ j)]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun l _ => hP l _)
      rw [htc] at h2
      linarith
    have hpos : ∀ (j : Fin k) (c : A j), 0 < ‖P j c‖ := fun j c => by linarith [hlow j c]
    have hCε : ε₀ ≤ C * η := by
      rw [hε₀, hC, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hα]
      nlinarith
    refine ⟨by linarith [hlow i x], ?_⟩
    -- units
    set u : ∀ j, A j → ℂ := fun j c => P j c / ((‖P j c‖ : ℝ) : ℂ) with hu
    have hPu : ∀ j c, P j c = ((‖P j c‖ : ℝ) : ℂ) * u j c := fun j c => by
      rw [hu]; dsimp only
      have : ((‖P j c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos j c).ne'
      field_simp
    have hun : ∀ j c, ‖u j c‖ = 1 := fun j c => by
      rw [hu]; dsimp only
      rw [norm_div, Complex.norm_real, norm_norm, div_self (hpos j c).ne']
    have hWU : ∀ y : ∀ i, A i, W y = ((‖W y‖ : ℝ) : ℂ) * ∏ j, u j (y j) := by
      intro y
      have h1 : W y = ∏ j, (((‖P j (y j)‖ : ℝ) : ℂ) * u j (y j)) :=
        Finset.prod_congr rfl fun j _ => hPu j (y j)
      have h2 : ‖W y‖ = ∏ j, ‖P j (y j)‖ := by rw [hW]; dsimp only; rw [norm_prod]
      calc W y = ∏ j, (((‖P j (y j)‖ : ℝ) : ℂ) * u j (y j)) := h1
        _ = ((∏ j, ‖P j (y j)‖ : ℝ) : ℂ) * ∏ j, u j (y j) := by
          rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
        _ = ((‖W y‖ : ℝ) : ℂ) * ∏ j, u j (y j) := by rw [h2]
    have hUnorm : ∀ y : ∀ i, A i, ‖∏ j, u j (y j)‖ = 1 := fun y => by
      rw [norm_prod]; exact Finset.prod_eq_one fun j _ => hun j _
    have hε1 : ∀ z ∈ μ.support, ‖∏ j, u j (z j) - ζ‖ ≤ ε₀ + Real.sqrt (2 * ε₀) := by
      intro z hz
      have h1 := hcl z hz
      have h2 : ‖∏ j, u j (z j) - W z‖ ≤ ε₀ := by
        have : ∏ j, u j (z j) - W z = (1 - ((‖W z‖ : ℝ) : ℂ)) * ∏ j, u j (z j) := by
          conv_lhs => rw [hWU z]
          ring
        rw [this, norm_mul, hUnorm, mul_one]
        have : (1 - ((‖W z‖ : ℝ) : ℂ)) = (((1 - ‖W z‖ : ℝ)) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hW1 z])]
        linarith [h1.1]
      calc ‖∏ j, u j (z j) - ζ‖ = ‖(∏ j, u j (z j) - W z) + (W z - ζ)‖ := by ring_nf
        _ ≤ ‖∏ j, u j (z j) - W z‖ + ‖W z - ζ‖ := norm_add_le _ _
        _ ≤ _ := add_le_add h2 h1.2
    obtain ⟨d, hd0, hdD, hd⟩ := hrel i x y
    have hrelb := k7_unit_relation u hun hζ hε1 i x y d hd0 hd
    have hsumd : (∑ z, |(d z : ℝ)|) ≤ D := by
      have : (∑ z, |(d z : ℝ)|) = ((∑ z, |d z| : ℤ) : ℝ) := by push_cast; rfl
      rw [this]; exact_mod_cast hdD
    have hs0 : 0 ≤ Real.sqrt ε₀ := Real.sqrt_nonneg _
    have hs1 : Real.sqrt ε₀ ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hε0lt.le
    have hss : Real.sqrt ε₀ ^ 2 = ε₀ := Real.sq_sqrt hε0pos.le
    have hε1b : ε₀ + Real.sqrt (2 * ε₀) ≤ 3 * Real.sqrt ε₀ := by
      have : Real.sqrt (2 * ε₀) ≤ 2 * Real.sqrt ε₀ := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      nlinarith
    have hub : ‖u i x - u i y‖ ≤ D * (3 * Real.sqrt ε₀) := by
      refine hrelb.trans ?_
      calc (∑ z, |(d z : ℝ)|) * (ε₀ + Real.sqrt (2 * ε₀))
          ≤ D * (ε₀ + Real.sqrt (2 * ε₀)) :=
            mul_le_mul_of_nonneg_right hsumd (by positivity)
        _ ≤ D * (3 * Real.sqrt ε₀) := mul_le_mul_of_nonneg_left hε1b hD0
    have hrx := hlow i x
    have hry := hlow i y
    have hrx1 := hP i x
    have hry1 := hP i y
    have hdiff : ‖P i x - P i y‖ ≤ ‖u i x - u i y‖ + ε₀ := by
      have e : P i x - P i y = ((‖P i x‖ : ℝ) : ℂ) * (u i x - u i y) +
          (((‖P i x‖ : ℝ) : ℂ) - ((‖P i y‖ : ℝ) : ℂ)) * u i y := by
        conv_lhs => rw [hPu i x, hPu i y]
        ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, norm_norm]
        exact mul_le_of_le_one_left (norm_nonneg _) hrx1
      · rw [norm_mul, hun, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        constructor <;> linarith
    have hsq : Real.sqrt ε₀ ≤ Real.sqrt η / α := by
      rw [Real.sqrt_le_left (div_nonneg (Real.sqrt_nonneg _) hα.le)]
      rw [div_pow, Real.sq_sqrt hη.le, hε₀]
      rw [div_le_div_iff_of_pos_left hη hα (by positivity)]
      nlinarith
    calc ‖P i x - P i y‖ ≤ ‖u i x - u i y‖ + ε₀ := hdiff
      _ ≤ D * (3 * Real.sqrt ε₀) + ε₀ := by linarith
      _ ≤ (3 * D + 1) * Real.sqrt ε₀ := by nlinarith
      _ ≤ (3 * D + 3) * (Real.sqrt η / α) := by
          have : (3 * (D : ℝ) + 1) ≤ 3 * D + 3 := by linarith
          exact mul_le_mul this hsq hs0 (by linarith)
      _ = C * Real.sqrt η := by rw [hC]; ring
end Prod1Core

section Prod1
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- CSP_7 `lemma:prod1` (with step `uniform-over-supports`): `C` depends on `(k, α)` only (`|Aᵢ| ≤ 1/α` and a
finite maximum over the isomorphism types of supports). -/
theorem k7_lemma_prod1 (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ P : ∀ i, A i → ℂ, (∀ i a, ‖P i a‖ ≤ 1) → ∀ η : ℝ, 0 < η →
        1 - η ≤ ‖μ.cexpect fun y => ∏ i, P i (y i)‖ →
          ∀ (i : Fin k) (x y : A i), 1 - C * η ≤ ‖P i x‖ ∧ ‖P i x - P i y‖ ≤ C * Real.sqrt η := by
  set N : ℕ := ⌈1 / α⌉₊ with hN
  set D : ℕ := k7Dmax k N with hD
  refine ⟨max 1 ((3 * D + 3) / α), le_max_left _ _, ?_⟩
  intro A _ _ μ hno hatom P hP η hη hcorr i x y
  have hcard : ∀ j, Fintype.card (A j) ≤ N := by
    intro j
    have h1 := card_le_inv_of_atom_bound μ hno hα hatom j
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have hrel : ∀ (j : Fin k) (a b : A j), K7Rel μ.support j a b D := by
    intro j a b
    obtain ⟨D', h⟩ := k7_rel_exists hno j a b
    exact k7_dmax_spec hcard h
  have := k7_prod1_core μ hno hα hatom D hrel P hP hη hcorr i x y
  have hm : (3 * (D : ℝ) + 3) / α ≤ max 1 ((3 * D + 3) / α) := le_max_right _ _
  refine ⟨?_, ?_⟩
  · nlinarith [this.1, mul_le_mul_of_nonneg_right hm hη.le]
  · refine this.2.trans ?_
    exact mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg _)

/-- CSP_7 `lemma:prod1`, step `phase-approximation` (fixed `μ`; in the source the constant depends on the support through
an integer lattice matrix; here it is obtained from `k7_lemma_prod1` with `α` the least atom of `μ`). `1`-bounded `Pᵢ` with
`|𝔼_μ ∏ Pᵢ| ≥ 1 - η` have `|Pᵢ| ≥ 1 - Cη` and `|Pᵢ(x) - Pᵢ(y)| ≤ C √η` (all coordinates `i`). -/
theorem k7_prod1_phase_approximation (μ : FinProb (∀ i, A i))
    (hno : NoNontrivialAbelianEmbeddingPi μ.support) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ∀ i, A i → ℂ, (∀ i a, ‖P i a‖ ≤ 1) → ∀ η : ℝ, 0 < η →
      1 - η ≤ ‖μ.cexpect fun y => ∏ i, P i (y i)‖ →
        ∀ (i : Fin k) (x y : A i), 1 - C * η ≤ ‖P i x‖ ∧ ‖P i x - P i y‖ ≤ C * Real.sqrt η := by
  classical
  obtain ⟨a0, ha0⟩ : ∃ a, a ∈ μ.support := by
    by_contra hcon
    push Not at hcon
    have : ∀ a, μ.prob a = 0 := fun a => by
      by_contra h; exact hcon a h
    have h1 := μ.sum_eq_one
    simp [this] at h1
  obtain ⟨am, ham, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (· ∈ μ.support)) μ.prob
    ⟨a0, by simpa using ha0⟩
  have hams : am ∈ μ.support := (Finset.mem_filter.1 ham).2
  have hpos : 0 < μ.prob am := lt_of_le_of_ne (μ.nonneg am) (Ne.symm hams)
  obtain ⟨C, hC1, hC⟩ := k7_lemma_prod1 k hpos
  exact ⟨C, hC1, fun P hP η hη hcorr i x y =>
    hC A μ hno (fun a ha => hmin a (by simpa using ha)) P hP η hη hcorr i x y⟩
end Prod1

section VarBound
variable {B : Type} [Fintype B]

/-- the variance is at most the square of a bound on the oscillation. -/
private theorem k7_var_le_of_osc [DecidableEq B] (π : FinProb B) (P : B → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a b, ‖P a - P b‖ ≤ M) :
    (∑ a, π.prob a * ‖P a‖ ^ 2) - ‖π.cexpect P‖ ^ 2 ≤ M ^ 2 := by
  rw [← k7_var_identity]
  have h1 : ∀ a, ‖P a - π.cexpect P‖ ≤ M := by
    intro a
    have e : P a - π.cexpect P = π.cexpect (fun b => P a - P b) := by
      rw [k7_cexpect_sub, k7_cexpect_const]
    rw [e]
    refine (k7_norm_cexpect_le _ _).trans ?_
    calc ∑ b, π.prob b * ‖P a - P b‖ ≤ ∑ b, π.prob b * M :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h a b) (π.nonneg b)
      _ = M := by rw [← Finset.sum_mul, π.sum_eq_one, one_mul]
  calc ∑ a, π.prob a * ‖P a - π.cexpect P‖ ^ 2 ≤ ∑ a, π.prob a * M ^ 2 :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (h1 a) 2) (π.nonneg a)
    _ = M ^ 2 := by rw [← Finset.sum_mul, π.sum_eq_one, one_mul]
end VarBound

section Pjbound
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- CSP_7 `eq:pjbound`: with `1 - η = |𝔼_μ ∏ᵢ Pᵢ|` (the printed `eq:jcor`, which defines `η`, as in
`prodn_eta_sum_bound`) and `0 ≤ γ ≤ 1`, the one-coordinate correlation along the noise pair is real and
`≥ ‖P_s‖₂² (1 - Cγη)`, `C = C(k, α)`. -/
theorem k7_eq_pjbound (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ P : ∀ i, A i → ℂ, (∀ i a, ‖P i a‖ ≤ 1) → ∀ η : ℝ, 0 ≤ η →
        ‖μ.cexpect fun y => ∏ i, P i (y i)‖ = 1 - η →
        ∀ (s : Fin k) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1),
          (1 - C * γ * η) * (∑ a, (μ.marginalPi s).prob a * ‖P s a‖ ^ 2) ≤
            ((jointNoise (μ.marginalPi s) (1 - γ) (by linarith) (by linarith)).cexpect
              fun p => P s p.1 * star (P s p.2)).re ∧
          ((jointNoise (μ.marginalPi s) (1 - γ) (by linarith) (by linarith)).cexpect
              fun p => P s p.1 * star (P s p.2)).im = 0 := by
  obtain ⟨C₁, hC1, hC⟩ := k7_lemma_prod1 k hα
  have hC1pos : 0 < C₁ := by linarith
  refine ⟨4 * C₁ ^ 2 + 2 * C₁, by nlinarith, ?_⟩
  intro A _ _ μ hno hatom P hP η hη hcorr s γ hγ0 hγ1
  set π := μ.marginalPi s with hπ
  set S : ℝ := ∑ a, π.prob a * ‖P s a‖ ^ 2 with hS
  set E : ℂ := π.cexpect (P s) with hE
  have hZ : ((jointNoise π (1 - γ) (by linarith) (by linarith)).cexpect
      fun p => P s p.1 * star (P s p.2)) =
      (((1 - γ) * S + (1 - (1 - γ)) * ‖E‖ ^ 2 : ℝ) : ℂ) :=
    k7_joint_single π (1 - γ) (by linarith) (by linarith) (P s)
  rw [hZ, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg a) (sq_nonneg _)
  -- consequences of `prod1` for every `η' ≥ η`, `η' > 0`
  have hP1 : ∀ η' : ℝ, 0 < η' → η ≤ η' → ∀ a b : A s, 1 - C₁ * η' ≤ ‖P s a‖ ∧
      ‖P s a - P s b‖ ≤ C₁ * Real.sqrt η' := fun η' h0 hle a b =>
    hC A μ hno hatom P hP η' h0 (by rw [hcorr]; linarith) s a b
  -- variance bound
  have hVar : S - ‖E‖ ^ 2 ≤ C₁ ^ 2 * η := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hη' : 0 < η + ε / C₁ ^ 2 := by positivity
    have := k7_var_le_of_osc π (P s) (M := C₁ * Real.sqrt (η + ε / C₁ ^ 2))
      (by positivity) (fun a b => (hP1 _ hη' (by have : 0 < ε / C₁ ^ 2 := by positivity
                                                 linarith) a b).2)
    rw [mul_pow, Real.sq_sqrt hη'.le] at this
    have e : C₁ ^ 2 * (η + ε / C₁ ^ 2) = C₁ ^ 2 * η + ε := by field_simp
    linarith
  -- lower bound for the modulus
  have hmin : ∀ a, 1 - C₁ * η ≤ ‖P s a‖ := by
    intro a
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hη' : 0 < η + ε / C₁ := by positivity
    have := (hP1 _ hη' (by have : 0 < ε / C₁ := by positivity
                           linarith) a a).1
    have e : C₁ * (η + ε / C₁) = C₁ * η + ε := by field_simp
    linarith
  have hVarS : S - ‖E‖ ^ 2 ≤ (4 * C₁ ^ 2 + 2 * C₁) * η * S := by
    by_cases hc : C₁ * η ≤ 1 / 2
    · have hS4 : 1 / 4 ≤ S := by
        have : ∀ a, 1 / 4 ≤ ‖P s a‖ ^ 2 := fun a => by nlinarith [hmin a]
        calc (1 : ℝ) / 4 = ∑ a, π.prob a * (1 / 4) := by
              rw [← Finset.sum_mul, π.sum_eq_one, one_mul]
          _ ≤ S := Finset.sum_le_sum fun a _ =>
              mul_le_mul_of_nonneg_left (this a) (π.nonneg a)
      nlinarith [mul_nonneg (sq_nonneg C₁) hη, mul_nonneg (mul_nonneg hC1pos.le hη) hS0,
        mul_nonneg (mul_nonneg (sq_nonneg C₁) hη) (sub_nonneg.2 hS4)]
    · push Not at hc
      nlinarith [sq_nonneg ‖E‖, mul_nonneg (mul_nonneg hC1pos.le hη) hS0,
        mul_nonneg (mul_nonneg (sq_nonneg C₁) hη) hS0]
  have hγη : 0 ≤ γ := hγ0
  nlinarith [mul_nonneg hγη (sub_nonneg.2 hVarS)]
end Pjbound

section ProdnMain
private theorem k7_prod_sub_le {J : Type} (s : Finset J) (a b : J → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (ha1 : ∀ j, a j ≤ 1) (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1) :
    ∏ j ∈ s, a j - ∏ j ∈ s, b j ≤ ∑ j ∈ s, max (a j - b j) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hS : 0 ≤ ∑ j ∈ s, max (a j - b j) 0 :=
      Finset.sum_nonneg fun j _ => le_max_right _ _
    have hPb0 : 0 ≤ ∏ j ∈ s, b j := Finset.prod_nonneg fun j _ => hb0 j
    have hPb1 : ∏ j ∈ s, b j ≤ 1 := Finset.prod_le_one₀ (fun j _ => hb0 j) fun j _ => hb1 j
    have h1 : a j * (∏ j ∈ s, a j - ∏ j ∈ s, b j) ≤ ∑ j ∈ s, max (a j - b j) 0 :=
      (mul_le_mul_of_nonneg_left ih (ha0 j)).trans (mul_le_of_le_one_left hS (ha1 j))
    have h2 : (a j - b j) * ∏ j ∈ s, b j ≤ max (a j - b j) 0 :=
      calc (a j - b j) * ∏ j ∈ s, b j ≤ max (a j - b j) 0 * ∏ j ∈ s, b j :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hPb0
        _ ≤ max (a j - b j) 0 := mul_le_of_le_one_right (le_max_right _ _) hPb1
    nlinarith

/-- CSP_7 `lemma:prodn`: `1`-bounded product functions `Pᵢ = ∏ⱼ Q i j` with `|𝔼_{μ^{⊗ι}} ∏ᵢ Pᵢ| ≥ δ` have
`𝔼_{x ∼ μ_s^{⊗ι}, y ∼_{1-γ} x} |P_s(x) - P_s(y)|² ≤ C γ log(1/δ)`, `C = C(k, α)`. -/
theorem k7_lemma_prodn (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Q : ∀ i, ι → A i → ℂ), (∀ i j a, ‖Q i j a‖ ≤ 1) →
        ∀ δ : ℝ, 0 < δ → δ ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, ∏ j, Q i j (X j i)‖ →
        ∀ (s : Fin k) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1),
          (((jointNoise (μ.marginalPi s) (1 - γ) (by linarith) (by linarith)).pi ι).cexpect
            fun p => ((‖k7ProdFun (Q s) (fun t => (p t).1) - k7ProdFun (Q s) (fun t => (p t).2)‖ ^ 2 :
              ℝ) : ℂ)).re ≤ C * γ * Real.log (1 / δ) := by
  obtain ⟨C₂, hC21, hC2⟩ := k7_eq_pjbound k hα
  refine ⟨2 * C₂, by linarith, ?_⟩
  intro A _ _ μ hno hatom ι _ _ Q hQ δ hδ hcorr s γ hγ0 hγ1
  set π := μ.marginalPi s with hπ
  obtain ⟨hη01, -, hηsum⟩ := prodn_eta_sum_bound μ Q hQ hδ hcorr
    (fun j => 1 - ‖μ.cexpect fun y => ∏ i, Q i j (y i)‖) (fun j => rfl)
  set η : ι → ℝ := fun j => 1 - ‖μ.cexpect fun y => ∏ i, Q i j (y i)‖ with hηdef
  have hγ0' : 0 ≤ γ := hγ0.le
  have hγ1' : γ ≤ 1 := hγ1.le
  have hρ0 : 0 ≤ 1 - γ := by linarith
  have hρ1 : 1 - γ ≤ 1 := by linarith
  -- single-coordinate quantities
  set S : ι → ℝ := fun j => ∑ a, π.prob a * ‖Q s j a‖ ^ 2 with hSdef
  set Z : ι → ℂ := fun j => (jointNoise π (1 - γ) hρ0 hρ1).cexpect
    fun q => Q s j q.1 * star (Q s j q.2) with hZdef
  have hZform : ∀ j, Z j = (((1 - γ) * S j + (1 - (1 - γ)) * ‖π.cexpect (Q s j)‖ ^ 2 : ℝ) : ℂ) :=
    fun j => k7_joint_single π (1 - γ) hρ0 hρ1 (Q s j)
  set z : ι → ℝ := fun j => (1 - γ) * S j + (1 - (1 - γ)) * ‖π.cexpect (Q s j)‖ ^ 2 with hzdef
  have hS0 : ∀ j, 0 ≤ S j := fun j =>
    Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg a) (sq_nonneg _)
  have hS1 : ∀ j, S j ≤ 1 := fun j =>
    calc S j ≤ ∑ a, π.prob a := Finset.sum_le_sum fun a _ => by
          have : ‖Q s j a‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hQ s j a)
          nlinarith [π.nonneg a]
      _ = 1 := π.sum_eq_one
  have hE1 : ∀ j, ‖π.cexpect (Q s j)‖ ^ 2 ≤ 1 := fun j => by
    have : ‖π.cexpect (Q s j)‖ ≤ 1 :=
      (k7_norm_cexpect_le _ _).trans (by
        calc ∑ a, π.prob a * ‖Q s j a‖ ≤ ∑ a, π.prob a * 1 :=
              Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hQ s j a) (π.nonneg a)
          _ = 1 := by simp [π.sum_eq_one])
    nlinarith [norm_nonneg (π.cexpect (Q s j))]
  have hz0 : ∀ j, 0 ≤ z j := fun j => by
    simp only [hzdef]
    nlinarith [hS0 j, sq_nonneg ‖π.cexpect (Q s j)‖]
  have hz1 : ∀ j, z j ≤ 1 := fun j => by
    simp only [hzdef]
    nlinarith [hS1 j, hE1 j, hS0 j, sq_nonneg ‖π.cexpect (Q s j)‖]
  -- the pjbound for each factor
  have hpj : ∀ j, S j - z j ≤ C₂ * γ * η j := by
    intro j
    have hPj : (∀ i a, ‖Q i j a‖ ≤ 1) := fun i a => hQ i j a
    have := (hC2 A μ hno hatom (fun i a => Q i j a) hPj (η j) (hη01 j).1
      (by simp only [hηdef]; ring) s γ hγ0' hγ1').1
    have hre : (Z j).re = z j := by rw [hZform j, Complex.ofReal_re]
    have h1 : (1 - C₂ * γ * η j) * S j ≤ z j := by
      have h2 := this
      rw [show ((jointNoise (μ.marginalPi s) (1 - γ) (by linarith) (by linarith)).cexpect
        fun p => Q s j p.1 * star (Q s j p.2)) = Z j from rfl, hre] at h2
      exact h2
    have h3 : 0 ≤ C₂ * γ * η j := mul_nonneg (mul_nonneg (by linarith) hγ0') (hη01 j).1
    nlinarith [hS1 j, hS0 j]
  have hmax : ∀ j, max (S j - z j) 0 ≤ C₂ * γ * η j := fun j =>
    max_le (hpj j) (mul_nonneg (mul_nonneg (by linarith) hγ0') (hη01 j).1)
  -- assemble
  have hT := k7_prodn_tensorize_difference π (1 - γ) hρ0 hρ1 (Q s)
  have hprodZ : (∏ j, Z j) = (((∏ j, z j : ℝ)) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun j _ => hZform j
  rw [show ((jointNoise (μ.marginalPi s) (1 - γ) (by linarith) (by linarith)).pi ι).cexpect
      (fun p => ((‖k7ProdFun (Q s) (fun t => (p t).1) - k7ProdFun (Q s) (fun t => (p t).2)‖ ^ 2 :
        ℝ) : ℂ)) = _ from hT]
  rw [Complex.ofReal_re]
  have hZre : (∏ j, (jointNoise π (1 - γ) hρ0 hρ1).cexpect fun q => Q s j q.1 * star (Q s j q.2)) =
      ((∏ j, z j : ℝ) : ℂ) := hprodZ
  rw [hZre, Complex.ofReal_re]
  have hkey := k7_prod_sub_le Finset.univ S z hS0 hS1 hz0 hz1
  have hsum : ∑ j, max (S j - z j) 0 ≤ C₂ * γ * Real.log (1 / δ) :=
    calc ∑ j, max (S j - z j) 0 ≤ ∑ j, C₂ * γ * η j := Finset.sum_le_sum fun j _ => hmax j
      _ = C₂ * γ * ∑ j, η j := by rw [← Finset.mul_sum]
      _ ≤ C₂ * γ * Real.log (1 / δ) :=
          mul_le_mul_of_nonneg_left hηsum (mul_nonneg (by linarith) hγ0')
  nlinarith
end ProdnMain

section CondFactor
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the one-sample conditional expectation `y ↦ 𝔼[∏_{i≠s} Q i j (y i) | y_s = a]`. -/
private def k7Cond (μ : FinProb (∀ i, A i)) (Q : ∀ i, ι → A i → ℂ) (s : Fin k) (j : ι)
    (a : A s) : ℂ :=
  (∑ y : ∀ i, A i, if y s = a then (μ.prob y : ℂ) * ∏ i ∈ univ.erase s, Q i j (y i) else 0) /
    (((μ.marginalPi s).prob a : ℝ) : ℂ)

/-- `P̃ = f̃_s` of product functions is itself a product function. -/
private theorem k7_cond_factor (μ : FinProb (∀ i, A i)) (s : Fin k) (Q : ∀ i, ι → A i → ℂ)
    (F : ∀ i, (ι → A i) → ℂ) (hF : ∀ i, i ≠ s → F i = k7ProdFun (Q i)) (x : ι → A s) :
    replaceCondProdExp μ F s x = ∏ j, k7Cond μ Q s j (x j) := by
  unfold replaceCondProdExp k7Cond
  rw [Finset.prod_div_distrib]
  congr 1
  · have h1 : ∀ X : ι → ∀ i, A i,
        (if (fun t => X t s) = x then ((μ.pi ι).prob X : ℂ) *
          ∏ i ∈ univ.erase s, F i (fun t => X t i) else 0) =
        ∏ j, (if X j s = x j then (μ.prob (X j) : ℂ) * ∏ i ∈ univ.erase s, Q i j (X j i)
          else 0) := by
      intro X
      rw [Finset.prod_ite_zero]
      have hc : ((fun t => X t s) = x) ↔ ∀ j ∈ (univ : Finset ι), X j s = x j := by
        simp [funext_iff]
      by_cases h : (fun t => X t s) = x
      · rw [if_pos h, if_pos (hc.1 h)]
        have e1 : ∏ i ∈ univ.erase s, F i (fun t => X t i) =
            ∏ i ∈ univ.erase s, ∏ j, Q i j (X j i) :=
          Finset.prod_congr rfl fun i hi => by
            rw [hF i (Finset.ne_of_mem_erase hi)]; rfl
        rw [e1, Finset.prod_mul_distrib, Finset.prod_comm (s := univ.erase s) (t := univ)]
        simp [FinProb.pi]
      · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]
    simp only [h1]
    exact (Fintype.prod_sum (fun (j : ι) (y : ∀ i, A i) =>
      if y s = x j then (μ.prob y : ℂ) * ∏ i ∈ univ.erase s, Q i j (y i) else 0)).symm
  · simp [FinProb.pi, FinProb.marginalPi]
end CondFactor

section ApplyProdn
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem k7_cond_norm_le (μ : FinProb (∀ i, A i)) (Q : ∀ i, ι → A i → ℂ)
    (hQ : ∀ i j a, ‖Q i j a‖ ≤ 1) (s : Fin k) (j : ι) (a : A s) : ‖k7Cond μ Q s j a‖ ≤ 1 := by
  unfold k7Cond
  by_cases hw : (μ.marginalPi s).prob a = 0
  · simp [hw]
  · have hpos : 0 < (μ.marginalPi s).prob a :=
      lt_of_le_of_ne ((μ.marginalPi s).nonneg a) (Ne.symm hw)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_le_one hpos]
    calc ‖∑ y : ∀ i, A i, if y s = a then (μ.prob y : ℂ) * ∏ i ∈ univ.erase s, Q i j (y i)
          else 0‖ ≤ ∑ y : ∀ i, A i, if y s = a then μ.prob y else 0 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
          split_ifs
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (μ.nonneg y), norm_prod]
            exact mul_le_of_le_one_right (μ.nonneg y)
              (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hQ i j _)
          · simp
      _ = (μ.marginalPi s).prob a := by
          rw [← Finset.sum_filter]; rfl

/-- CSP_7 `lemma:fstab`, step `apply-prodn`: with `P̃ = f̃_s` the conditional-expectation function of the product
functions `Pᵢ = ∏ⱼ Q i j` (`i ≠ s`; `P̃` is itself a product function), `‖f‖_∞ ≤ 1` and the pair
`(conj P̃, Pᵢ)` of correlation `≥ δ²`, one has for `γ ≤ c δ² / log(1/δ)`
`|𝔼_{x ∼ μ_s^{⊗ι}, y ∼_{1-γ} x} f(x) (P̃(x) - P̃(y))| ≤ δ/2`; `c = c(k, α)`. -/
theorem k7_fstab_apply_prodn (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ (s : Fin k) (ι : Type) [Fintype ι] [DecidableEq ι] (F : ∀ i, (ι → A i) → ℂ)
        (Q : ∀ i, ι → A i → ℂ), (∀ i j a, ‖Q i j a‖ ≤ 1) →
        (∀ i, i ≠ s → F i = k7ProdFun (Q i)) → (∀ x, ‖F s x‖ ≤ 1) →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
        δ ^ 2 ≤ ∑ x, ((μ.marginalPi s).pi ι).prob x * ‖replaceCondProdExp μ F s x‖ ^ 2 →
        ∀ (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1), γ ≤ c * δ ^ 2 / Real.log (1 / δ) →
          ‖((jointNoise (μ.marginalPi s) (1 - γ) (by linarith) (by linarith)).pi ι).cexpect
            fun p => F s (fun t => (p t).1) *
              (replaceCondProdExp μ F s (fun t => (p t).1) -
                replaceCondProdExp μ F s (fun t => (p t).2))‖ ≤ δ / 2 := by
  obtain ⟨C, hCpos, hC⟩ := k7_lemma_prodn k hα
  refine ⟨1 / (8 * C), by positivity, ?_⟩
  intro A _ _ μ hno hatom s ι _ _ F Q hQ hF hFs δ hδ hδ1 hpt γ hγ0 hγ1 hγc
  have hρ0 : 0 ≤ 1 - γ := by linarith
  have hρ1 : 1 - γ ≤ 1 := by linarith
  set Pt : (ι → A s) → ℂ := replaceCondProdExp μ F s with hPt
  have hfac : ∀ x, Pt x = ∏ j, k7Cond μ Q s j (x j) := fun x => k7_cond_factor μ s Q F hF x
  set Q' : ∀ i, ι → A i → ℂ := Function.update Q s (fun j a => star (k7Cond μ Q s j a)) with hQ'
  have hQ's : ∀ j a, Q' s j a = star (k7Cond μ Q s j a) := fun j a => by simp [hQ']
  have hQ'ne : ∀ i, i ≠ s → Q' i = Q i := fun i hi => by simp [hQ', Function.update_of_ne hi]
  have hQ'b : ∀ i j a, ‖Q' i j a‖ ≤ 1 := by
    intro i j a
    by_cases hi : i = s
    · subst hi
      rw [hQ's, Complex.star_def, Complex.norm_conj]
      exact k7_cond_norm_le μ Q hQ i j a
    · rw [hQ'ne i hi]; exact hQ i j a
  -- the correlation of the tuple `(Q', ...)` is `‖P̃‖²`
  have hcorr : δ ^ 2 ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, ∏ j, Q' i j (X j i)‖ := by
    have e : ∀ X : ι → ∀ i, A i, ∏ i, ∏ j, Q' i j (X j i) =
        (∏ i ∈ univ.erase s, F i (fun t => X t i)) * star (Pt (fun t => X t s)) := by
      intro X
      rw [← Finset.mul_prod_erase univ (fun i => ∏ j, Q' i j (X j i)) (Finset.mem_univ s),
        mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by
          rw [hQ'ne i (Finset.ne_of_mem_erase hi), hF i (Finset.ne_of_mem_erase hi)]; rfl
      · rw [hfac]
        have hs : ∀ g : ι → ℂ, star (∏ j, g j) = ∏ j, star (g j) :=
          fun g => map_prod (starRingEnd ℂ) g univ
        rw [hs]
        exact Finset.prod_congr rfl fun j _ => hQ's j _
    simp only [e]
    rw [replace_cexpect_prod_erase_mul_star, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun x _ => mul_nonneg (((μ.marginalPi s).pi ι).nonneg x) (sq_nonneg _))]
    exact hpt
  have hmain := hC A μ hno hatom ι Q' hQ'b (δ ^ 2) (by positivity) hcorr s γ hγ0 hγ1
  set ν := (jointNoise (μ.marginalPi s) (1 - γ) hρ0 hρ1).pi ι with hν
  have hnorm : ∀ x y : ι → A s,
      ‖k7ProdFun (Q' s) x - k7ProdFun (Q' s) y‖ = ‖Pt x - Pt y‖ := by
    intro x y
    have hs : ∀ x : ι → A s, k7ProdFun (Q' s) x = star (Pt x) := by
      intro x
      rw [hfac]
      have hs : ∀ g : ι → ℂ, star (∏ j, g j) = ∏ j, star (g j) :=
        fun g => map_prod (starRingEnd ℂ) g univ
      rw [hs]
      exact Finset.prod_congr rfl fun j _ => (hQ's j _)
    rw [hs, hs, ← star_sub, Complex.star_def, Complex.norm_conj]
  have hG : ∑ p, ν.prob p * ‖Pt (fun t => (p t).1) - Pt (fun t => (p t).2)‖ ^ 2 ≤
      C * γ * Real.log (1 / δ ^ 2) := by
    refine le_trans (le_of_eq ?_) hmain
    have : ν.cexpect (fun p => ((‖k7ProdFun (Q' s) (fun t => (p t).1) -
        k7ProdFun (Q' s) (fun t => (p t).2)‖ ^ 2 : ℝ) : ℂ)) =
        ((∑ p, ν.prob p * ‖Pt (fun t => (p t).1) - Pt (fun t => (p t).2)‖ ^ 2 : ℝ) : ℂ) := by
      unfold FinProb.cexpect
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hnorm]
    rw [this, Complex.ofReal_re]
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hlog2 : Real.log (1 / δ ^ 2) = 2 * Real.log (1 / δ) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [hlog2] at hG
  have hγl : γ * Real.log (1 / δ) ≤ 1 / (8 * C) * δ ^ 2 := by
    have := (le_div_iff₀ hlog).1 hγc
    linarith
  -- Cauchy-Schwarz
  have h1 : ‖ν.cexpect fun p => F s (fun t => (p t).1) *
      (Pt (fun t => (p t).1) - Pt (fun t => (p t).2))‖ ≤
      ∑ p, ν.prob p * |‖Pt (fun t => (p t).1) - Pt (fun t => (p t).2)‖| := by
    refine (k7_norm_cexpect_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hFs _)) (ν.nonneg p)
  have h2 := k7_sq_sum_norm_le ν (fun p => ‖Pt (fun t => (p t).1) - Pt (fun t => (p t).2)‖)
  have h3 : (∑ p, ν.prob p * |‖Pt (fun t => (p t).1) - Pt (fun t => (p t).2)‖|) ^ 2 ≤
      (δ / 2) ^ 2 := by
    refine h2.trans (hG.trans ?_)
    have : C * γ * (2 * Real.log (1 / δ)) = 2 * C * (γ * Real.log (1 / δ)) := by ring
    rw [this]
    calc 2 * C * (γ * Real.log (1 / δ)) ≤ 2 * C * (1 / (8 * C) * δ ^ 2) :=
          mul_le_mul_of_nonneg_left hγl (by positivity)
      _ = (δ / 2) ^ 2 := by field_simp; ring
  have h4 := abs_le_of_sq_le_sq' h3 (by linarith)
  exact h1.trans h4.2
end ApplyProdn

section FstabMain
variable {k : ℕ}

/-- CSP_7 `lemma:fstab`: `‖f‖_∞ ≤ 1`, `1`-bounded product functions `Pᵢ = ∏ⱼ Q i j` (`i ≠ s`; the printed
statement omits `1`-boundedness), `|𝔼_{μ^{⊗ι}} f(x_s) ∏_{i ≠ s} Pᵢ(xᵢ)| ≥ δ`; then
`Stab_{1-γ}(f) ≥ δ²/4` for `γ ≤ c δ²/log(1/δ)`, `c = c(k, α)`. -/
theorem k7_lemma_fstab (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ (s : Fin k) (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → A s) → ℂ),
        (∀ x, ‖f x‖ ≤ 1) → ∀ (Q : ∀ i, ι → A i → ℂ), (∀ i j a, ‖Q i j a‖ ≤ 1) →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
        δ ≤ ‖(μ.pi ι).cexpect fun X => f (fun t => X t s) *
          ∏ i ∈ univ.erase s, ∏ j, Q i j (X j i)‖ →
        ∀ (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1), γ ≤ c * δ ^ 2 / Real.log (1 / δ) →
          δ ^ 2 / 4 ≤ (cstab (μ.marginalPi s) (1 - γ) f).re := by
  obtain ⟨c, hc, hap⟩ := k7_fstab_apply_prodn k hα
  refine ⟨c, hc, ?_⟩
  intro A _ _ μ hno hatom s ι _ _ f hf Q hQ δ hδ hδ1 hcorr γ hγ0 hγ1 hγc
  have hρ0 : 0 ≤ 1 - γ := by linarith
  have hρ1 : 1 - γ ≤ 1 := by linarith
  set F : ∀ i, (ι → A i) → ℂ := Function.update (fun i => k7ProdFun (Q i)) s f with hFdef
  have hFs : F s = f := by simp [hFdef]
  have hFne : ∀ i, i ≠ s → F i = k7ProdFun (Q i) := fun i hi => by
    simp [hFdef, Function.update_of_ne hi]
  have hF1 : ∀ i x, ‖F i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = s
    · subst hi; rw [hFs]; exact hf x
    · rw [hFne i hi]
      unfold k7ProdFun
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hQ i j _
  have hcorrF : δ ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, F i fun t => X t i‖ := by
    have e : ∀ X : ι → ∀ i, A i, (∏ i, F i fun t => X t i) =
        f (fun t => X t s) * ∏ i ∈ univ.erase s, ∏ j, Q i j (X j i) := by
      intro X
      rw [← Finset.mul_prod_erase univ (fun i => F i fun t => X t i) (Finset.mem_univ s), hFs]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by rw [hFne i (Finset.ne_of_mem_erase hi)]; rfl
    simp only [e]; exact hcorr
  obtain ⟨h1, h2⟩ := k7_fstab_eq_wtp μ s F hF1 hδ.le hcorrF
  have happ := hap A μ hno hatom s ι F Q hQ hFne (fun x => hF1 s x) δ hδ hδ1 h2 γ hγ0 hγ1 hγc
  set Pt := replaceCondProdExp μ F s with hPt
  set ν := (jointNoise (μ.marginalPi s) (1 - γ) hρ0 hρ1).pi ι with hν
  have hx : ν.cexpect (fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).1)) =
      ((μ.marginalPi s).pi ι).cexpect (fun x => Pt x * F s x) := by
    rw [hν]
    refine (k7_pair_cexpect_fst (μ.marginalPi s) (1 - γ) hρ0 hρ1
      (fun x => F s x * Pt x)).trans ?_
    unfold FinProb.cexpect
    exact Finset.sum_congr rfl fun x _ => by ring
  have hsplit : ν.cexpect (fun p => F s (fun t => (p t).1) *
      (Pt (fun t => (p t).1) - Pt (fun t => (p t).2))) =
      ν.cexpect (fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).1)) -
      ν.cexpect (fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).2)) := by
    rw [← k7_cexpect_sub]
    exact congrArg ν.cexpect (funext fun p => mul_sub _ _ _)
  have hlow : δ / 2 ≤ ‖ν.cexpect fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).2)‖ := by
    have h3 : ‖ν.cexpect (fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).1))‖ ≤
        ‖ν.cexpect fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).2)‖ + δ / 2 := by
      have hA : ν.cexpect (fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).1)) =
          ν.cexpect (fun p => F s (fun t => (p t).1) * Pt (fun t => (p t).2)) +
          ν.cexpect (fun p => F s (fun t => (p t).1) *
            (Pt (fun t => (p t).1) - Pt (fun t => (p t).2))) := by rw [hsplit]; ring
      rw [hA]
      exact (norm_add_le _ _).trans (by linarith)
    rw [hx] at h3
    linarith
  rw [hFs] at hlow
  have := k7_fstab_to_stability (μ.marginalPi s) hρ0 hρ1 f Pt
    (replace_condProdExp_norm_le μ F hF1 s) hδ.le hlow
  calc δ ^ 2 / 4 = (δ / 2) ^ 2 := by ring
    _ ≤ _ := this
end FstabMain
end TrackB
end RestrictedPolynomials
end
