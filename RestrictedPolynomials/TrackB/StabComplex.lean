module

public import RestrictedPolynomials.Stability
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Track B, file 1: complex stability and the Efron–Stein decomposition

Sources: CSP_7 (`kcsp.tex`) l. 322, 445-447, 501; paper IV (`writeup_stability.tex`) l. 356-357,
478-484, 490-509, 528-529. Covered statements:

* the paper `def:stability#efron-stein-properties`: `cesPart`, `sum_cesPart`, `cesPart_empty`,
  `cstab_eq_sum_cl2sq_cesPart`, `cstab_im_eq_zero`, `cstab_nonneg`, `cstab_mono`,
  `re_cstab_le_cl2sq`, `cl2sq_cnoiseOp`, `cstab_log_convex`;
* the paper `definition-efron-stein` and `definition-efron-stein#noise-operator-formula`:
  `ccondExp`, `cesPart`, `cnoiseOp_eq_sum_cesPart`;
* the paper `t-inverse#padding-removes-large-n`: `padding_removes_large_n`.

Auxiliary lemmas (not conclusions of paper statements; they feed the padding bridge and the
tensor-power obligations of the paper's `t-inverse#near-one-regime`): `norm_cexpect_sq_le_re_cstab`, `cstab_sumInl`,
`cstab_equiv`, `cexpect_pi_sumInl`, `cexpect_pi_joint_sumInl`, `tensorPow` and its lemmas.

The complex objects `cnoiseOp`, `cstab` are the frozen definitions; the real library
(`EfronStein`, `Stability`) is applied to `Re f` and `Im f`. Helper names live in
`RestrictedPolynomials.TrackB`.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

namespace TrackB

section W1

variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- complex L² norm squared -/
def cl2sq (π : FinProb α) (f : (ι → α) → ℂ) : ℝ := (π.pi ι).expect fun x => ‖f x‖ ^ 2

/-- complex conditional expectation (source L501) -/
def ccondExp (π : FinProb α) (T : Finset ι) (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  (π.pi ι).cexpect fun y => f (T.piecewise x y)

/-- complex Efron-Stein component, the explicit formula of the source (paper L501) -/
def cesPart (π : FinProb α) (S : Finset ι) (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  ∑ T ∈ S.powerset, ((-1 : ℂ)) ^ (S.card - T.card) * ccondExp π T f x

/-! ### Real and imaginary parts -/

omit [DecidableEq α] [DecidableEq ι] in
lemma cexpect_eq_re_add_im {β : Type*} [Fintype β] (π : FinProb β) (g : β → ℂ) :
    π.cexpect g = (π.expect (fun a => (g a).re) : ℂ) + (π.expect (fun a => (g a).im) : ℂ) *
      Complex.I := by
  simp only [FinProb.cexpect, FinProb.expect, Complex.ofReal_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  apply Complex.ext <;> simp

lemma cnoiseOp_eq_re_add_im (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) (x : ι → α) :
    cnoiseOp π ρ f x = (noiseOp π ρ (fun y => (f y).re) x : ℂ)
      + (noiseOp π ρ (fun y => (f y).im) x : ℂ) * Complex.I := by
  simp only [cnoiseOp, noiseOp, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  generalize (∏ i, noiseKernel π ρ (x i) (y i)) = K
  apply Complex.ext <;> simp

lemma ccondExp_eq (π : FinProb α) (T : Finset ι) (f : (ι → α) → ℂ) (x : ι → α) :
    ccondExp π T f x = (condExp π T (fun y => (f y).re) x : ℂ)
      + (condExp π T (fun y => (f y).im) x : ℂ) * Complex.I :=
  cexpect_eq_re_add_im _ _

lemma cesPart_eq (π : FinProb α) (S : Finset ι) (f : (ι → α) → ℂ) (x : ι → α) :
    cesPart π S f x = (esPart π S (fun y => (f y).re) x : ℂ)
      + (esPart π S (fun y => (f y).im) x : ℂ) * Complex.I := by
  unfold cesPart esPart
  simp only [Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [ccondExp_eq]
  push_cast
  ring

lemma sum_cesPart (π : FinProb α) (f : (ι → α) → ℂ) (x : ι → α) :
    ∑ S : Finset ι, cesPart π S f x = f x := by
  simp only [cesPart_eq, Finset.sum_add_distrib, ← Complex.ofReal_sum, ← Finset.sum_mul,
    sum_esPart]
  exact Complex.re_add_im _

lemma cesPart_empty (π : FinProb α) (f : (ι → α) → ℂ) (x : ι → α) :
    cesPart π ∅ f x = (π.pi ι).cexpect f := by
  rw [cesPart_eq, cexpect_eq_re_add_im, esPart_empty, esPart_empty]

lemma cnoiseOp_eq_sum_cesPart (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) (x : ι → α) :
    cnoiseOp π ρ f x = ∑ S : Finset ι, ((ρ ^ S.card : ℝ) : ℂ) * cesPart π S f x := by
  rw [cnoiseOp_eq_re_add_im, noiseOp_eq, noiseOp_eq]
  simp only [cesPart_eq, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  push_cast
  ring

/-- Self-adjointness of the real noise operator. -/
lemma expect_mul_noiseOp_comm (π : FinProb α) (ρ : ℝ) (a b : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => b x * noiseOp π ρ a x) =
      (π.pi ι).expect (fun x => a x * noiseOp π ρ b x) := by
  simp only [noiseOp_eq, mul_sum, FinProb.expect_sum]
  refine sum_congr rfl fun S _ => ?_
  have h : ∀ (u v : (ι → α) → ℝ), (π.pi ι).expect (fun x => u x * (ρ ^ S.card * esPart π S v x))
      = ρ ^ S.card * (π.pi ι).expect (fun x => esPart π S u x * esPart π S v x) := by
    intro u v
    rw [show (fun x => u x * (ρ ^ S.card * esPart π S v x))
        = fun x => ρ ^ S.card * (u x * esPart π S v x) from funext fun x => by ring,
      FinProb.expect_const_mul, expect_mul_esPart]
  rw [h, h]
  congr 1
  exact (π.pi ι).expect_congr fun x => mul_comm _ _

/-- The weight `‖f^{=S}‖₂²` of a complex function, as the sum of those of its real and
imaginary parts. -/
def cw (π : FinProb α) (S : Finset ι) (f : (ι → α) → ℂ) : ℝ :=
  (π.pi ι).expect (fun x => esPart π S (fun y => (f y).re) x ^ 2) +
    (π.pi ι).expect (fun x => esPart π S (fun y => (f y).im) x ^ 2)

lemma cw_nonneg (π : FinProb α) (S : Finset ι) (f : (ι → α) → ℂ) : 0 ≤ cw π S f :=
  add_nonneg ((π.pi ι).expect_nonneg fun _ => sq_nonneg _)
    ((π.pi ι).expect_nonneg fun _ => sq_nonneg _)

lemma cstab_eq_re_add_im (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) :
    cstab π ρ f = ((stab π ρ (fun y => (f y).re) + stab π ρ (fun y => (f y).im) : ℝ) : ℂ) := by
  unfold cstab stab
  rw [cexpect_eq_re_add_im]
  have hre : ∀ x, (f x * star (cnoiseOp π ρ f x)).re =
      (f x).re * noiseOp π ρ (fun y => (f y).re) x
        + (f x).im * noiseOp π ρ (fun y => (f y).im) x := by
    intro x
    rw [cnoiseOp_eq_re_add_im]
    simp
  have him : ∀ x, (f x * star (cnoiseOp π ρ f x)).im =
      (f x).im * noiseOp π ρ (fun y => (f y).re) x
        - (f x).re * noiseOp π ρ (fun y => (f y).im) x := by
    intro x
    rw [cnoiseOp_eq_re_add_im]
    simp
    ring
  simp only [hre, him, FinProb.expect_add, FinProb.expect_sub]
  rw [expect_mul_noiseOp_comm π ρ (fun y => (f y).re) (fun y => (f y).im), sub_self]
  push_cast
  simp

lemma cstab_im_eq_zero (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) : (cstab π ρ f).im = 0 := by
  rw [cstab_eq_re_add_im]
  exact Complex.ofReal_im _

lemma re_cstab_eq (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) :
    (cstab π ρ f).re = ∑ S : Finset ι, ρ ^ S.card * cw π S f := by
  rw [cstab_eq_re_add_im, Complex.ofReal_re, stab_eq, stab_eq, ← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  unfold cw
  ring

lemma cstab_eq_ofReal_re (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) :
    cstab π ρ f = ((cstab π ρ f).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [cstab_im_eq_zero]; simp

lemma cstab_eq_sum_cl2sq_cesPart (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) :
    cstab π ρ f = ((∑ S : Finset ι, ρ ^ S.card * cl2sq π (cesPart π S f) : ℝ) : ℂ) := by
  have h : ∑ S : Finset ι, ρ ^ S.card * cw π S f =
      ∑ S : Finset ι, ρ ^ S.card * cl2sq π (cesPart π S f) := by
    refine sum_congr rfl fun S _ => ?_
    congr 1
    unfold cw cl2sq
    rw [← FinProb.expect_add]
    refine (π.pi ι).expect_congr fun x => ?_
    rw [cesPart_eq, Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [cstab_eq_ofReal_re π ρ f, re_cstab_eq, h]

open scoped ComplexOrder in
lemma cstab_nonneg (π : FinProb α) {ρ : ℝ} (hρ : 0 ≤ ρ) (f : (ι → α) → ℂ) : 0 ≤ cstab π ρ f := by
  rw [cstab_eq_ofReal_re, Complex.zero_le_real, re_cstab_eq]
  exact sum_nonneg fun S _ => mul_nonneg (pow_nonneg hρ _) (cw_nonneg π S f)

open scoped ComplexOrder in
lemma cstab_mono (π : FinProb α) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') (f : (ι → α) → ℂ) :
    cstab π ρ f ≤ cstab π ρ' f := by
  rw [cstab_eq_ofReal_re π ρ, cstab_eq_ofReal_re π ρ', Complex.real_le_real, re_cstab_eq,
    re_cstab_eq]
  exact sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h _)
    (cw_nonneg π S f)

lemma norm_cexpect_sq_le_re_cstab (π : FinProb α) {ρ : ℝ} (hρ : 0 ≤ ρ) (f : (ι → α) → ℂ) :
    ‖(π.pi ι).cexpect f‖ ^ 2 ≤ (cstab π ρ f).re := by
  rw [re_cstab_eq]
  refine le_trans ?_ (single_le_sum (f := fun S : Finset ι => ρ ^ S.card * cw π S f)
    (fun S _ => mul_nonneg (pow_nonneg hρ _) (cw_nonneg π S f)) (mem_univ (∅ : Finset ι)))
  simp only [card_empty, pow_zero, one_mul, cw, esPart_empty]
  rw [cexpect_eq_re_add_im, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 : (π.pi ι).expect (fun x => (π.pi ι).expect (fun y => (f y).re) ^ 2)
      = (π.pi ι).expect (fun y => (f y).re) ^ 2 := by simp
  have h2 : (π.pi ι).expect (fun x => (π.pi ι).expect (fun y => (f y).im) ^ 2)
      = (π.pi ι).expect (fun y => (f y).im) ^ 2 := by simp
  rw [h1, h2]

lemma cl2sq_eq_sum_cw (π : FinProb α) (f : (ι → α) → ℂ) :
    cl2sq π f = ∑ S : Finset ι, cw π S f := by
  unfold cl2sq cw
  rw [sum_add_distrib, ← expect_sq_eq_sum, ← expect_sq_eq_sum, ← FinProb.expect_add]
  refine (π.pi ι).expect_congr fun x => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma re_cstab_le_cl2sq (π : FinProb α) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f : (ι → α) → ℂ) :
    (cstab π ρ f).re ≤ cl2sq π f := by
  rw [re_cstab_eq, cl2sq_eq_sum_cw]
  exact sum_le_sum fun S _ => mul_le_of_le_one_left (cw_nonneg π S f)
    (pow_le_one₀ h0 h1)

/-- The real noise operator multiplies the `S`-weight by `ρ^{2|S|}` in `L²`. -/
lemma expect_noiseOp_sq (π : FinProb α) (ρ : ℝ) (g : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => noiseOp π ρ g x ^ 2) =
      ∑ S : Finset ι, (ρ ^ 2) ^ S.card * (π.pi ι).expect (fun x => esPart π S g x ^ 2) := by
  simp only [noiseOp_eq, sq, sum_mul_sum, FinProb.expect_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_eq_single S]
  · rw [show (fun x => ρ ^ S.card * esPart π S g x * (ρ ^ S.card * esPart π S g x))
        = fun x => (ρ ^ 2) ^ S.card * (esPart π S g x * esPart π S g x) from
        funext fun x => by rw [← pow_mul, mul_comm 2, pow_mul]; ring,
      FinProb.expect_const_mul]
    simp [sq]
  · intro S' _ hS'
    rw [show (fun x => ρ ^ S.card * esPart π S g x * (ρ ^ S'.card * esPart π S' g x))
        = fun x => (ρ ^ S.card * ρ ^ S'.card) * (esPart π S g x * esPart π S' g x) from
        funext fun x => by ring,
      FinProb.expect_const_mul, expect_esPart_mul_esPart π (Ne.symm hS'), mul_zero]
  · intro h; exact absurd (mem_univ S) h

/-- `‖N_ρ f‖₂² = Stab_{ρ²}(f)`. -/
lemma cl2sq_cnoiseOp (π : FinProb α) {ρ : ℝ} (h0 : 0 ≤ ρ) (f : (ι → α) → ℂ) :
    cl2sq π (cnoiseOp π ρ f) = (cstab π (ρ ^ 2) f).re := by
  have h : ∀ x, ‖cnoiseOp π ρ f x‖ ^ 2 =
      noiseOp π ρ (fun y => (f y).re) x ^ 2 + noiseOp π ρ (fun y => (f y).im) x ^ 2 := by
    intro x
    rw [cnoiseOp_eq_re_add_im, Complex.sq_norm, Complex.normSq_add_mul_I]
  unfold cl2sq
  simp only [h, FinProb.expect_add, expect_noiseOp_sq, re_cstab_eq, cw, mul_add, sum_add_distrib]

/-- Jensen with total weight at most `1`. -/
lemma rpow_sum_le_sum_rpow {κ : Type*} (s : Finset κ) (w x : κ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : ∑ i ∈ s, w i ≤ 1) (hx : ∀ i ∈ s, 0 ≤ x i) {t : ℝ} (ht : 1 ≤ t) :
    (∑ i ∈ s, w i * x i) ^ t ≤ ∑ i ∈ s, w i * x i ^ t := by
  set W := ∑ i ∈ s, w i with hWdef
  have hW0 : 0 ≤ W := sum_nonneg hw
  rcases hW0.eq_or_lt with hW0 | hWpos
  · have : ∀ i ∈ s, w i = 0 := (sum_eq_zero_iff_of_nonneg hw).1 hW0.symm
    rw [sum_eq_zero fun i hi => by rw [this i hi, zero_mul],
      sum_eq_zero fun i hi => by rw [this i hi, zero_mul], Real.zero_rpow (by linarith)]
  · have hnorm : ∑ i ∈ s, w i / W = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ hWpos.ne'
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / W) x
      (fun i hi => div_nonneg (hw i hi) hW0) hnorm hx ht
    have e1 : ∑ i ∈ s, w i * x i = W * ∑ i ∈ s, w i / W * x i := by
      rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; field_simp
    have e2 : ∑ i ∈ s, w i * x i ^ t = W * ∑ i ∈ s, w i / W * x i ^ t := by
      rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; field_simp
    rw [e1, e2, Real.mul_rpow hW0 (sum_nonneg fun i hi =>
      mul_nonneg (div_nonneg (hw i hi) hW0) (hx i hi))]
    have hWt : W ^ t ≤ W := by
      calc W ^ t = W ^ (t - 1) * W := by
            rw [← Real.rpow_add_one hWpos.ne']; ring_nf
        _ ≤ 1 * W := mul_le_mul_of_nonneg_right
            (Real.rpow_le_one hW0 hW (by linarith)) hW0
        _ = W := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hW0 _))
      (mul_le_mul_of_nonneg_right hWt (sum_nonneg fun i hi =>
        mul_nonneg (div_nonneg (hw i hi) hW0) (Real.rpow_nonneg (hx i hi) _)))

lemma cstab_log_convex (π : FinProb α) {ρ t : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (ht : 1 ≤ t)
    (f : (ι → α) → ℂ) (hf : cl2sq π f ≤ 1) :
    ((cstab π ρ f).re) ^ t ≤ (cstab π (ρ ^ t) f).re := by
  rw [re_cstab_eq, re_cstab_eq]
  have hpow : ∀ S : Finset ι, (ρ ^ t) ^ S.card = (ρ ^ S.card) ^ t := by
    intro S
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_mul h0,
      mul_comm]
  simp only [hpow]
  have e1 : ∑ S : Finset ι, ρ ^ S.card * cw π S f = ∑ S : Finset ι, cw π S f * ρ ^ S.card :=
    sum_congr rfl fun _ _ => mul_comm _ _
  have e2 : ∑ S : Finset ι, (ρ ^ S.card) ^ t * cw π S f =
      ∑ S : Finset ι, cw π S f * (ρ ^ S.card) ^ t :=
    sum_congr rfl fun _ _ => mul_comm _ _
  rw [e1, e2]
  refine rpow_sum_le_sum_rpow univ (fun S => cw π S f) (fun S => ρ ^ S.card)
    (fun S _ => cw_nonneg π S f) ?_ (fun S _ => pow_nonneg h0 _) ht
  rw [← cl2sq_eq_sum_cw]; exact hf

/-! ### Padding and reindexing -/

lemma cexpect_pi_sumInl {κ : Type} [Fintype κ] [DecidableEq κ] (π : FinProb α)
    (g : (ι → α) → ℂ) :
    (π.pi (ι ⊕ κ)).cexpect (fun y => g (y ∘ Sum.inl)) = (π.pi ι).cexpect g := by
  have h1 : (π.pi (ι ⊕ κ)).expect (fun y => (g (y ∘ Sum.inl)).re) =
      (π.pi ι).expect (fun y => (g y).re) := FinProb.expect_sumInl π (fun y => (g y).re)
  have h2 : (π.pi (ι ⊕ κ)).expect (fun y => (g (y ∘ Sum.inl)).im) =
      (π.pi ι).expect (fun y => (g y).im) := FinProb.expect_sumInl π (fun y => (g y).im)
  rw [cexpect_eq_re_add_im, cexpect_eq_re_add_im (π.pi ι) g, h1, h2]

lemma cstab_sumInl {κ : Type} [Fintype κ] [DecidableEq κ] (π : FinProb α) (ρ : ℝ)
    (g : (ι → α) → ℂ) :
    cstab π ρ (fun y : ι ⊕ κ → α => g (y ∘ Sum.inl)) = cstab π ρ g := by
  have h1 : stab π ρ (fun y : ι ⊕ κ → α => (g (y ∘ Sum.inl)).re) =
      stab π ρ (fun y => (g y).re) := stab_sumInl π ρ (fun y => (g y).re)
  have h2 : stab π ρ (fun y : ι ⊕ κ → α => (g (y ∘ Sum.inl)).im) =
      stab π ρ (fun y => (g y).im) := stab_sumInl π ρ (fun y => (g y).im)
  rw [cstab_eq_re_add_im, cstab_eq_re_add_im, h1, h2]

lemma cexpect_pi_equiv {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) {β : Type}
    [Fintype β] (π : FinProb β) (g : (ι → β) → ℂ) :
    (π.pi κ).cexpect (fun y => g (y ∘ e.symm)) = (π.pi ι).cexpect g := by
  unfold FinProb.cexpect
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl β)) _ _ fun y => ?_
  have hp : ∏ j : ι, π.prob ((Equiv.arrowCongr e (Equiv.refl β)) y j) = ∏ i, π.prob (y i) := by
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
    exact Equiv.prod_comp e.symm (fun i => π.prob (y i))
  have : (π.pi κ).prob y = (π.pi ι).prob ((Equiv.arrowCongr e (Equiv.refl β)) y) := by
    rw [FinProb.pi_prob, FinProb.pi_prob, hp]
  rw [this]
  rfl

lemma cnoiseOp_equiv {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (π : FinProb α)
    (ρ : ℝ) (g : (ι → α) → ℂ) (x : κ → α) :
    cnoiseOp π ρ (fun y : κ → α => g (y ∘ e.symm)) x = cnoiseOp π ρ g (x ∘ e.symm) := by
  unfold cnoiseOp
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) _ _ fun y => ?_
  have hp : ∏ j : ι, noiseKernel π ρ ((x ∘ e.symm) j) ((Equiv.arrowCongr e (Equiv.refl α)) y j)
      = ∏ i, noiseKernel π ρ (x i) (y i) := by
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
    exact Equiv.prod_comp e.symm (fun i => noiseKernel π ρ (x i) (y i))
  rw [hp]
  rfl

lemma cstab_equiv {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (π : FinProb α) (ρ : ℝ)
    (g : (ι → α) → ℂ) :
    cstab π ρ (fun y : κ → α => g (y ∘ e.symm)) = cstab π ρ g := by
  unfold cstab
  simp only [cnoiseOp_equiv]
  exact cexpect_pi_equiv e π (fun z => g z * star (cnoiseOp π ρ g z))

/-- padded joint correlation -/
lemma cexpect_pi_joint_sumInl {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)]
    {κ : Type} [Fintype κ] [DecidableEq κ] (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) :
    (μ.pi (ι ⊕ κ)).cexpect (fun X => ∏ i, f i (fun t => X (Sum.inl t) i))
      = (μ.pi ι).cexpect (fun X => ∏ i, f i (fun t => X t i)) :=
  cexpect_pi_sumInl (α := ∀ i, A i) (κ := κ) μ (fun X => ∏ i, f i (fun t => X t i))

open scoped ComplexOrder in
theorem padding_removes_large_n {k : ℕ} (A : Fin k → Type) [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] (μ : FinProb (∀ i, A i)) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (n₀ : ℕ)
    (h : ∀ n : ℕ, n₀ ≤ n → ∀ f : ∀ i, (Fin n → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
      ε ≤ ‖(μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i‖ →
      ∀ i, (δ : ℂ) ≤ cstab (μ.marginalPi i) (1 - δ) (f i)) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ f : ∀ i, (ι → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
      ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
      ∀ i, (δ : ℂ) ≤ cstab (μ.marginalPi i) (1 - δ) (f i) := by
  intro ι _ _ f hf hcorr i
  have hcard : Fintype.card (ι ⊕ Fin n₀) = Fintype.card ι + n₀ := by simp
  let e : Fin (Fintype.card ι + n₀) ≃ ι ⊕ Fin n₀ := (Fintype.equivFinOfCardEq hcard).symm
  have hc : (μ.pi (Fin (Fintype.card ι + n₀))).cexpect
      (fun X => ∏ i, f i (fun s => (fun t => X t i) (e.symm (Sum.inl s)))) =
      (μ.pi ι).cexpect (fun X => ∏ i, f i (fun t => X t i)) :=
    (cexpect_pi_equiv e μ (fun Y => ∏ i, f i (fun t => Y (Sum.inl t) i))).trans
      (cexpect_pi_joint_sumInl μ f)
  have key := h (Fintype.card ι + n₀) (Nat.le_add_left _ _)
    (fun i z => f i (fun t => z (e.symm (Sum.inl t)))) (fun i z => hf i _)
    (hcorr.trans (le_of_eq (congrArg norm hc.symm))) i
  exact le_of_le_of_eq key
    ((cstab_equiv e (μ.marginalPi i) (1 - δ) (fun y : ι ⊕ Fin n₀ → A i => f i (y ∘ Sum.inl))).trans
      (cstab_sumInl (κ := Fin n₀) (μ.marginalPi i) (1 - δ) (f i)))

end W1

section Tensor

variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- tensor power `f^{⊗m}` on `ι × Fin m` -/
def tensorPow (m : ℕ) (f : (ι → α) → ℂ) : (ι × Fin m → α) → ℂ :=
  fun x => ∏ j : Fin m, f (fun i => x (i, j))

lemma norm_tensorPow_le (m : ℕ) (f : (ι → α) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (x : ι × Fin m → α) :
    ‖tensorPow m f x‖ ≤ 1 := by
  unfold tensorPow
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hf _

/-- `ι × Fin m → β` as `m` copies of `ι → β`. -/
def tpEquiv {β : Type} (ι : Type) (m : ℕ) : (ι × Fin m → β) ≃ (Fin m → ι → β) :=
  (Equiv.curry ι (Fin m) β).trans (Equiv.piComm fun _ _ => β)

lemma cexpect_pi_prod_fin (m : ℕ) (π : FinProb α) (H : (ι → α) → ℂ) :
    (π.pi (ι × Fin m)).cexpect (fun X => ∏ j : Fin m, H (fun s => X (s, j))) =
      ((π.pi ι).cexpect H) ^ m := by
  unfold FinProb.cexpect
  rw [← (tpEquiv (β := α) ι m).symm.sum_comp]
  have hp : ∀ Z : Fin m → ι → α, (π.pi (ι × Fin m)).prob ((tpEquiv ι m).symm Z) =
      ∏ j, (π.pi ι).prob (Z j) := by
    intro Z
    rw [FinProb.pi_prob, Fintype.prod_prod_type, Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => rfl
  have hH : ∀ Z : Fin m → ι → α, ∏ j : Fin m, H (fun s => (tpEquiv ι m).symm Z (s, j)) =
      ∏ j, H (Z j) := fun Z => rfl
  simp only [hp, hH, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (y : ι → α) => (((π.pi ι).prob y : ℝ) : ℂ) * H y)]
  simp [Finset.prod_const]

lemma cnoiseOp_tensorPow (m : ℕ) (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ)
    (x : ι × Fin m → α) :
    cnoiseOp π ρ (tensorPow m f) x = ∏ j : Fin m, cnoiseOp π ρ f (fun s => x (s, j)) := by
  unfold cnoiseOp
  rw [← (tpEquiv (β := α) ι m).symm.sum_comp]
  have hp : ∀ Z : Fin m → ι → α,
      ∏ p : ι × Fin m, noiseKernel π ρ (x p) (((tpEquiv ι m).symm Z) p) =
        ∏ j, ∏ s, noiseKernel π ρ (x (s, j)) (Z j s) := by
    intro Z
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    rfl
  have hs : ∀ (Z : Fin m → ι → α) (j : Fin m),
      (fun s => (tpEquiv ι m).symm Z (s, j)) = Z j := fun _ _ => rfl
  simp only [hp, tensorPow, hs, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (y : ι → α) =>
    (∏ s, ((noiseKernel π ρ (x (s, j)) (y s) : ℝ) : ℂ)) * f y)]

lemma cexpect_pi_tensorPow {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)]
    (m : ℕ) (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) :
    (μ.pi (ι × Fin m)).cexpect (fun X => ∏ i, tensorPow m (f i) (fun t => X t i))
      = ((μ.pi ι).cexpect (fun X => ∏ i, f i (fun t => X t i))) ^ m := by
  rw [← cexpect_pi_prod_fin (α := ∀ i, A i) m μ (fun Y => ∏ i, f i (fun t => Y t i))]
  congr 1
  funext X
  simp only [tensorPow]
  exact Finset.prod_comm

lemma cstab_tensorPow (m : ℕ) (π : FinProb α) (ρ : ℝ) (f : (ι → α) → ℂ) :
    cstab π ρ (tensorPow m f) = (cstab π ρ f) ^ m := by
  unfold cstab
  rw [← cexpect_pi_prod_fin m π (fun z => f z * star (cnoiseOp π ρ f z))]
  refine Finset.sum_congr rfl fun X _ => ?_
  simp only [cnoiseOp_tensorPow, tensorPow, star_prod, Finset.prod_mul_distrib]

end Tensor

end TrackB

end RestrictedPolynomials

end
