module

public import RestrictedPolynomials.TrackB.AppBSetting
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Track B, Appendix B: the homogeneous theorem as a hypothesis, Claim `soft_trunc3`

Paper IV Thm 7.14/7.14′ (`thm:nonembed_homogenous'`, l. 4337-4345, and its `cc` form l. 4465-4470),
at the trivial embedding group, on the BUILT Section-7 definitions (`s7BetaP`, `s7Beta`,
`S7ModestBasis`). The exponent is `1 - √ξ` (the printed `1 - 2ξ` is not what the proof gives). Claim
`soft_trunc3` (l. 9214-9372) in its PROVED form (the printed `M 2^{-ρ^{-(1-10ξ)}}` is not what the
proof shows). The decay constant is `1 + c'/2`, and `hDx` is not a hypothesis of `appB_t3_parts_mem`.
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Hom

/-- the body of `hhom'` at fixed constants: Thm 7.14′ (x-form, `β'`) for the distributions of
Thm 6.7′ (hypotheses `Rel67`, `RelaxedBaseCase` with gain constants `(crb, Crb)`), all bases of
Def. 7.1 (`β'` does not depend on them, `s7BetaP_basis_indep`), `n ≥ d ≥ d'`, `d' ≥ d^{1-ξ}`:
`β' ≤ (1+c)^{-d'^{1-√ξ}}`. -/
def HomPAt (m K : ℕ) (crb Crb α ξ c : ℝ) : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
    ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
      Rel67 K α ν Sg Sm Phi' → RelaxedBaseCase ν Sm crb Crb →
    ∀ (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm)
      (By : S7ModestBasis (lawY ν) (fun _ : Y => ()) (∅ : Finset Y))
      (Bz : S7ModestBasis (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z)) (n d d' : ℕ),
      d ≤ n → d' ≤ d → (d : ℝ) ^ (1 - ξ) ≤ d' →
      s7BetaP ν Bx.u By.u Bz.u n d d' ≤
        ENNReal.ofReal ((1 + c) ^ (-((d' : ℝ) ^ (1 - Real.sqrt ξ))))

/-- the body of `hhom` at fixed constants: Thm 7.14 (`cc` form, `β`). -/
def HomAt (m K : ℕ) (crb Crb α ξ c : ℝ) : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
    ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
      Rel67 K α ν Sg Sm Phi' → RelaxedBaseCase ν Sm crb Crb →
    ∀ (hν : S7YZImpliesX ν.support)
      (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm)
      (By : S7ModestBasis (lawY ν) (fun _ : Y => ()) (∅ : Finset Y))
      (Bz : S7ModestBasis (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z)) (n d d' : ℕ),
      d ≤ n → d' ≤ d → (d : ℝ) ^ (1 - ξ) ≤ d' →
      s7Beta ν hν Bx.u By.u Bz.u n d d' ≤
        ENNReal.ofReal ((1 + c) ^ (-((d' : ℝ) ^ (1 - Real.sqrt ξ))))

/-- `hhom'` (the hypothesis of the producer): `∀ m K crb Crb α` the gain constants `(crb, Crb)`
are quantified BEFORE `(ξ, c)`, and `ξ < 1` is added. -/
def HomPStmt : Prop :=
  ∀ (m K : ℕ) (crb Crb α : ℝ), 0 < α → 0 < crb → 0 < Crb →
    ∃ ξ c : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < c ∧ HomPAt m K crb Crb α ξ c

/-- `hhom`: Thm 7.14. -/
def HomStmt : Prop :=
  ∀ (m K : ℕ) (crb Crb α : ℝ), 0 < α → 0 < crb → 0 < Crb →
    ∃ ξ c : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < c ∧ HomAt m K crb Crb α ξ c

/-- §7.3.1 (`nonembed_hom_implies`, l. 4473-4483), constants fixed: Thm 7.14 implies Thm 7.14′, by
the built `s7_betaP_le_beta` (`hν` from hypotheses 5 and 7: `s7_yzImpliesX_iff`). -/
theorem appB_homPAt_of_homAt {m K : ℕ} {crb Crb α ξ c : ℝ} (h : HomAt m K crb Crb α ξ c) :
    HomPAt m K crb Crb α ξ c := by
  intro X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR hRB Bx By Bz n d d' hdn hd'd hdd'
  have hν : S7YZImpliesX ν.support := (s7_yzImpliesX_iff _).2 ⟨hR.yz_full, hR.merge⟩
  exact (s7_betaP_le_beta ν hν Bx.u By.u Bz.u n d d').trans
    (h X Y Z hX hY hZ ν Sg Sm Phi' hR hRB hν Bx By Bz n d d' hdn hd'd hdd')

theorem appB_homP_of_hom : HomStmt → HomPStmt := by
  intro h m K crb Crb α hα hcrb hCrb
  obtain ⟨ξ, c, h0, h1, h2, hh⟩ := h m K crb Crb α hα hcrb hCrb
  exact ⟨ξ, c, h0, h1, h2, appB_homPAt_of_homAt hh⟩

end Hom

section Helpers
private theorem t3_one_add_pow_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (k : ℕ) :
    (1 + (k : ℝ) * s) * (1 - s) ^ k ≤ 1 := by
  have hb : 1 + (k : ℝ) * s ≤ (1 + s) ^ k := one_add_mul_le_pow (by linarith) k
  have h2 : ((1 + s) * (1 - s)) ^ k ≤ 1 := by
    have : (1 + s) * (1 - s) = 1 - s ^ 2 := by ring
    rw [this]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  calc (1 + (k : ℝ) * s) * (1 - s) ^ k ≤ (1 + s) ^ k * (1 - s) ^ k :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith) _)
    _ = ((1 + s) * (1 - s)) ^ k := (mul_pow _ _ _).symm
    _ ≤ 1 := h2

/-- `(1-s)^k ≤ 2 s'` once `k s ≥ 1/s'`-type: the decay bound in the form used below. -/
private theorem t3_pow_decay {s r : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (hr : 0 < r) (k : ℕ)
    (hk : 1 / r ≤ (k : ℝ) * s) : (1 - s) ^ k ≤ r := by
  have h := t3_one_add_pow_le h0 h1 k
  have hp : 0 ≤ (1 - s) ^ k := pow_nonneg (by linarith) _
  have h3 : 1 / r ≤ 1 + (k : ℝ) * s := by linarith
  have h4 : (1 / r) * (1 - s) ^ k ≤ 1 := le_trans (mul_le_mul_of_nonneg_right h3 hp) h
  rw [one_div, inv_mul_le_iff₀ hr] at h4
  linarith

private theorem t3_pow_sub_pow_le {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) (k : ℕ) :
    a ^ k - b ^ k ≤ (k : ℝ) * (a - b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
    have h2 : a * (a ^ k - b ^ k) ≤ a ^ k - b ^ k := by
      have : 0 ≤ a ^ k - b ^ k := sub_nonneg.2 (pow_le_pow_left₀ hb hba k)
      nlinarith
    have h3 : b ^ k * (a - b) ≤ a - b := by
      have := pow_le_one₀ hb (hba.trans ha) (n := k)
      nlinarith
    push_cast
    nlinarith


private theorem t3_rpow_mul_self {ρ : ℝ} (hρ : 0 < ρ) (e : ℝ) : ρ ^ e * ρ = ρ ^ (e + 1) := by
  rw [Real.rpow_add hρ, Real.rpow_one]

private theorem t3_g_mult {ρ ξ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ)
    (hk : ¬ (ρ ^ (-(1 - ξ)) < (k : ℝ) ∧ (k : ℝ) < ρ ^ (-(1 + ξ)))) :
    ‖((1 - ρ / 2 : ℝ) : ℂ) ^ k - ((1 - ρ : ℝ) : ℂ) ^ k‖ ≤ 2 * ρ ^ ξ := by
  have hpξ : 0 < ρ ^ ξ := Real.rpow_pos_of_pos hρ ξ
  have e : ((1 - ρ / 2 : ℝ) : ℂ) ^ k - ((1 - ρ : ℝ) : ℂ) ^ k =
      (((1 - ρ / 2) ^ k - (1 - ρ) ^ k : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have hb0 : 0 ≤ 1 - ρ := by linarith
  have hba : 1 - ρ ≤ 1 - ρ / 2 := by linarith
  have hnn : 0 ≤ (1 - ρ / 2) ^ k - (1 - ρ) ^ k :=
    sub_nonneg.2 (pow_le_pow_left₀ hb0 hba k)
  rw [abs_of_nonneg hnn]
  by_cases h1 : (k : ℝ) ≤ ρ ^ (-(1 - ξ))
  · have h2 := t3_pow_sub_pow_le hb0 hba (by linarith : 1 - ρ / 2 ≤ 1) k
    have h3 : (k : ℝ) * (ρ / 2) ≤ ρ ^ ξ / 2 := by
      have : (k : ℝ) * ρ ≤ ρ ^ (-(1 - ξ)) * ρ := mul_le_mul_of_nonneg_right h1 hρ.le
      rw [t3_rpow_mul_self hρ] at this
      have e2 : -(1 - ξ) + 1 = ξ := by ring
      rw [e2] at this
      linarith
    have : (k : ℝ) * ((1 - ρ / 2) - (1 - ρ)) = (k : ℝ) * (ρ / 2) := by ring
    linarith
  · have h2 : ρ ^ (-(1 + ξ)) ≤ (k : ℝ) := by
      by_contra hc
      exact hk ⟨not_le.1 h1, not_le.1 hc⟩
    have h3 : 1 / (2 * ρ ^ ξ) ≤ (k : ℝ) * (ρ / 2) := by
      have : ρ ^ (-(1 + ξ)) * ρ ≤ (k : ℝ) * ρ := mul_le_mul_of_nonneg_right h2 hρ.le
      rw [t3_rpow_mul_self hρ] at this
      have e2 : -(1 + ξ) + 1 = -ξ := by ring
      rw [e2, Real.rpow_neg hρ.le] at this
      have : 1 / (2 * ρ ^ ξ) = (ρ ^ ξ)⁻¹ / 2 := by field_simp
      rw [this]
      linarith
    have h4 := t3_pow_decay (s := ρ / 2) (r := 2 * ρ ^ ξ) (by linarith) (by linarith)
      (by positivity) k h3
    have : 0 ≤ (1 - ρ) ^ k := pow_nonneg hb0 k
    linarith


/-- the real multiplier of `f'' = f' - E f'` on a monomial with `nedeg = k`, `effdeg = e`. -/
private def t3Mult (ρ ξ : ℝ) (k e : ℕ) : ℝ :=
  (1 - ρ ^ (1 + ξ)) ^ k * (1 - (1 - ρ ^ (1 - ξ)) ^ e)

private theorem t3_f_mult_nonneg {ρ ξ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (k e : ℕ) : 0 ≤ t3Mult ρ ξ k e ∧ t3Mult ρ ξ k e ≤ 1 := by
  have hθ0 : 0 ≤ ρ ^ (1 + ξ) := (Real.rpow_pos_of_pos hρ _).le
  have hθ1 : ρ ^ (1 + ξ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
  have hδ0 : 0 ≤ ρ ^ (1 - ξ) := (Real.rpow_pos_of_pos hρ _).le
  have hδ1 : ρ ^ (1 - ξ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
  have h1 : 0 ≤ (1 - ρ ^ (1 + ξ)) ^ k := pow_nonneg (by linarith) _
  have h1' : (1 - ρ ^ (1 + ξ)) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have h2 : 0 ≤ (1 - ρ ^ (1 - ξ)) ^ e := pow_nonneg (by linarith) _
  have h2' : (1 - ρ ^ (1 - ξ)) ^ e ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  unfold t3Mult
  constructor
  · exact mul_nonneg h1 (by linarith)
  · nlinarith

private theorem t3_f_mult_small {ρ ξ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ < 1 / 2)
    (k e : ℕ)
    (hk : ¬ (ρ ^ (-(1 - 2 * ξ)) ≤ (e : ℝ) ∧ (k : ℝ) ≤ ρ ^ (-(1 + 2 * ξ)))) :
    t3Mult ρ ξ k e ≤ ρ ^ ξ := by
  have hpξ : 0 < ρ ^ ξ := Real.rpow_pos_of_pos hρ ξ
  have hθ0 : 0 ≤ ρ ^ (1 + ξ) := (Real.rpow_pos_of_pos hρ _).le
  have hθ1 : ρ ^ (1 + ξ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
  have hδ0 : 0 ≤ ρ ^ (1 - ξ) := (Real.rpow_pos_of_pos hρ _).le
  have hδ1 : ρ ^ (1 - ξ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
  obtain ⟨n0, n1⟩ := t3_f_mult_nonneg hρ hρ1 hξ (by linarith) k e
  have h1 : 0 ≤ (1 - ρ ^ (1 + ξ)) ^ k := pow_nonneg (by linarith) _
  have h1' : (1 - ρ ^ (1 + ξ)) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have h2 : 0 ≤ (1 - ρ ^ (1 - ξ)) ^ e := pow_nonneg (by linarith) _
  have h2' : (1 - ρ ^ (1 - ξ)) ^ e ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  unfold t3Mult
  by_cases hA : (e : ℝ) < ρ ^ (-(1 - 2 * ξ))
  · have hb : 1 + (e : ℝ) * (-ρ ^ (1 - ξ)) ≤ (1 + -ρ ^ (1 - ξ)) ^ e :=
      one_add_mul_le_pow (by linarith) e
    have hc : (e : ℝ) * ρ ^ (1 - ξ) ≤ ρ ^ ξ := by
      have : (e : ℝ) * ρ ^ (1 - ξ) ≤ ρ ^ (-(1 - 2 * ξ)) * ρ ^ (1 - ξ) :=
        mul_le_mul_of_nonneg_right hA.le hδ0
      rw [← Real.rpow_add hρ] at this
      have e2 : -(1 - 2 * ξ) + (1 - ξ) = ξ := by ring
      rw [e2] at this
      exact this
    have : 1 - (1 - ρ ^ (1 - ξ)) ^ e ≤ ρ ^ ξ := by
      have : (1 + -ρ ^ (1 - ξ)) = 1 - ρ ^ (1 - ξ) := by ring
      rw [this] at hb
      linarith
    nlinarith
  · have hB : ρ ^ (-(1 + 2 * ξ)) < (k : ℝ) := by
      by_contra hc
      exact hk ⟨not_lt.1 hA, not_lt.1 hc⟩
    have h3 : 1 / ρ ^ ξ ≤ (k : ℝ) * ρ ^ (1 + ξ) := by
      have : ρ ^ (-(1 + 2 * ξ)) * ρ ^ (1 + ξ) ≤ (k : ℝ) * ρ ^ (1 + ξ) :=
        mul_le_mul_of_nonneg_right hB.le hθ0
      rw [← Real.rpow_add hρ] at this
      have e2 : -(1 + 2 * ξ) + (1 + ξ) = -ξ := by ring
      rw [e2, Real.rpow_neg hρ.le] at this
      rwa [one_div]
    have h4 := t3_pow_decay hθ0 hθ1 hpξ k h3
    nlinarith

section Spectral
variable {A : Type} [Fintype A] [DecidableEq A] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem t3_cinner_sub_left {β : Type*} [Fintype β] (π : FinProb β) (f g h : β → ℂ) :
    π.cinner (f - g) h = π.cinner f h - π.cinner g h := by
  have : f - g = f + (-1 : ℂ) • g := by ext x; simp [sub_eq_add_neg]
  rw [this, cinner_add_left, cinner_smul_left]; ring

omit [DecidableEq A] in
private theorem t3_coef_sub {J : Type} (D : FinProb A) (u : J → A → ℂ) (f g : (ι → A) → ℂ)
    (c : ι → J) : s7Coef D u (f - g) c = s7Coef D u f c - s7Coef D u g c :=
  t3_cinner_sub_left _ _ _ _

omit [DecidableEq A] in
private theorem t3_coef_expansion {J : Type} [Fintype J] [DecidableEq J] (D : FinProb A)
    (u : J → A → ℂ) (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0)
    (a : (ι → J) → ℂ) (c0 : ι → J) :
    s7Coef D u (fun x => ∑ c, a c * s7Mono u c x) c0 = a c0 := by
  have hm := s7_mono_orthonormal (ι := ι) D u hu
  unfold s7Coef
  have : (fun x => ∑ c, a c * s7Mono u c x) = ∑ c, a c • s7Mono u c := by
    funext x; simp
  rw [this, cinner_sum_left, Finset.sum_eq_single c0]
  · rw [cinner_smul_left, hm]; simp
  · intro c _ hc; rw [cinner_smul_left, hm]; simp [hc]
  · simp

omit [DecidableEq A] in
/-- a coefficientwise bound transfers to the `L²` norm (Parseval). -/
private theorem t3_norm_le {J : Type} [Fintype J] (D : FinProb A) (hD : ∀ a, 0 < D.prob a)
    (u : J → A → ℂ) (hu : S7IsONB D u) (F f : (ι → A) → ℂ) {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ c, ‖s7Coef D u F c‖ ≤ s * ‖s7Coef D u f c‖) : cl2norm D F ≤ s * cl2norm D f := by
  unfold cl2norm
  have h1 : cl2sq D F ≤ s ^ 2 * cl2sq D f := by
    have e1 : cl2sq D F = ∑ c, ‖s7Coef D u F c‖ ^ 2 := s7_parseval D hD u hu F
    have e2 : cl2sq D f = ∑ c, ‖s7Coef D u f c‖ ^ 2 := s7_parseval D hD u hu f
    rw [e1, e2, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    calc ‖s7Coef D u F c‖ ^ 2 ≤ (s * ‖s7Coef D u f c‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h c) 2
      _ = _ := by ring
  calc Real.sqrt (cl2sq D F) ≤ Real.sqrt (s ^ 2 * cl2sq D f) := Real.sqrt_le_sqrt h1
    _ = s * Real.sqrt (cl2sq D f) := by rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

private theorem t3_coef_tNE {D : FinProb A} (hD : ∀ a, 0 < D.prob a) {Sm : Finset A}
    (B : S7ModestBasis D (fun _ : A => ()) Sm) (θ : ℝ) (f : (ι → A) → ℂ) (c : ι → B.J) :
    s7Coef D B.u (tNE D θ f) c = ((1 - θ : ℝ) : ℂ) ^ s7NeDeg c * s7Coef D B.u f c := by
  have h := s7_nonEmbedOp_expansion D (fun _ : A => ()) Sm hD B θ f
  have e : tNE D θ f = fun x => ∑ c, (((1 - θ : ℝ) : ℂ) ^ s7NeDeg c * s7Coef D B.u f c) *
      s7Mono B.u c x := h
  rw [e]
  exact t3_coef_expansion D B.u (fun i j => s7_modestBasis_orthonormal D _ Sm B i j) _ c

private theorem t3_coef_eff {D : FinProb A} (hD : ∀ a, 0 < D.prob a) {Sm : Finset A}
    (B : S7ModestBasis D (fun _ : A => ()) Sm) {δ : ℝ} (hδ : 0 < δ) (f : (ι → A) → ℂ)
    (c : ι → B.J) :
    s7Coef D B.u (s7EffNoiseOp D Sm δ f) c = ((1 - δ : ℝ) : ℂ) ^ s7EffDeg c * s7Coef D B.u f c := by
  have h := s7_effNoiseOp_expansion D (fun _ : A => ()) Sm hD (fun _ _ _ _ => rfl) B hδ f
  have e : s7EffNoiseOp D Sm δ f = fun x => ∑ c, (((1 - δ : ℝ) : ℂ) ^ s7EffDeg c *
      s7Coef D B.u f c) * s7Mono B.u c x := h
  rw [e]
  exact t3_coef_expansion D B.u (fun i j => s7_modestBasis_orthonormal D _ Sm B i j) _ c

end Spectral



private theorem t3_addChar_unit_eq (a b : AddChar Unit ℂ) : a = b := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one]

section CS
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem t3_expect_pi_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    {κ : Type} [Fintype κ] [DecidableEq κ] (π : FinProb α) (p : α → β) (φ : (κ → β) → ℝ) :
    ((mergePush π p).pi κ).expect φ = (π.pi κ).expect (fun x => φ (fun i => p (x i))) := by
  unfold FinProb.expect
  symm
  rw [← Finset.sum_fiberwise univ (fun x : κ → α => fun i => p (x i))
    (fun x => (π.pi κ).prob x * φ (fun i => p (x i)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ x ∈ univ.filter (fun x : κ → α => (fun i => p (x i)) = b),
      (π.pi κ).prob x * φ (fun i => p (x i)) = (π.pi κ).prob x * φ b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  show ∑ x ∈ univ.filter (fun x : κ → α => (fun i => p (x i)) = b), ∏ i, π.prob (x i) =
    ∏ i, ∑ a ∈ univ.filter (fun a => p a = b i), π.prob a
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Fintype.mem_piFinset, funext_iff]

private theorem t3_cl2sq_x {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (A : (ι → X) → ℂ) : cl2sq (lawX ν) A =
    ∑ t : ι → X × Y × Z, (ν.pi ι).prob t * ‖A (fun i => (t i).1)‖ ^ 2 :=
  t3_expect_pi_push ν (fun p => p.1) (fun x => ‖A x‖ ^ 2)

private theorem t3_cl2sq_y {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (A : (ι → Y) → ℂ) : cl2sq (lawY ν) A =
    ∑ t : ι → X × Y × Z, (ν.pi ι).prob t * ‖A (fun i => (t i).2.1)‖ ^ 2 :=
  t3_expect_pi_push ν (fun p => p.2.1) (fun x => ‖A x‖ ^ 2)

private theorem t3_corr3_bound {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (A : (ι → X) → ℂ) (B : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖corr3 ν A B h‖ ≤ cl2norm (lawX ν) A * cl2norm (lawY ν) B := by
  have hP : ∀ t : ι → X × Y × Z, 0 ≤ (ν.pi ι).prob t := (ν.pi ι).nonneg
  have h1 : ‖corr3 ν A B h‖ ≤ ∑ t : ι → X × Y × Z, (ν.pi ι).prob t *
      (‖A (fun i => (t i).1)‖ * ‖B (fun i => (t i).2.1)‖) := by
    unfold corr3 FinProb.cexpect
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP t), norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hP t)
    have := hh (fun i => (t i).2.2)
    have hA := norm_nonneg (A (fun i => (t i).1))
    have hB := norm_nonneg (B (fun i => (t i).2.1))
    nlinarith [mul_nonneg hA hB]
  have h2 : ∑ t : ι → X × Y × Z, (ν.pi ι).prob t *
      (‖A (fun i => (t i).1)‖ * ‖B (fun i => (t i).2.1)‖) ≤
      Real.sqrt (∑ t : ι → X × Y × Z, (ν.pi ι).prob t * ‖A (fun i => (t i).1)‖ ^ 2) *
      Real.sqrt (∑ t : ι → X × Y × Z, (ν.pi ι).prob t * ‖B (fun i => (t i).2.1)‖ ^ 2) := by
    calc _ = ∑ t : ι → X × Y × Z, Real.sqrt ((ν.pi ι).prob t * ‖A (fun i => (t i).1)‖ ^ 2) *
          Real.sqrt ((ν.pi ι).prob t * ‖B (fun i => (t i).2.1)‖ ^ 2) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Real.sqrt_mul (hP t), Real.sqrt_mul (hP t), Real.sqrt_sq (norm_nonneg _),
            Real.sqrt_sq (norm_nonneg _)]
          have := Real.mul_self_sqrt (hP t)
          calc _ = (Real.sqrt ((ν.pi ι).prob t) * Real.sqrt ((ν.pi ι).prob t)) *
                (‖A (fun i => (t i).1)‖ * ‖B (fun i => (t i).2.1)‖) := by rw [this]
            _ = _ := by ring
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _ (fun t => mul_nonneg (hP t) (sq_nonneg _))
            (fun t => mul_nonneg (hP t) (sq_nonneg _))
  refine h1.trans (h2.trans (le_of_eq ?_))
  unfold cl2norm
  rw [t3_cl2sq_x, t3_cl2sq_y]

private theorem t3_corr3_split {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (F F₃ : (ι → X) → ℂ) (G G₃ : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν F G h = corr3 ν (F - F₃) G h + corr3 ν F₃ (G - G₃) h + corr3 ν F₃ G₃ h := by
  unfold corr3 FinProb.cexpect
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.sub_apply]
  ring

section Extras
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem t3_corr3_sum_left {κ : Type} (s : Finset κ) (ν : FinProb (X × Y × Z))
    (F : κ → (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν (∑ c ∈ s, F c) g h = ∑ c ∈ s, corr3 ν (F c) g h := by
  unfold corr3 FinProb.cexpect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]

private theorem t3_corr3_sum_mid {κ : Type} (s : Finset κ) (ν : FinProb (X × Y × Z))
    (f : (ι → X) → ℂ) (G : κ → (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν f (∑ c ∈ s, G c) h = ∑ c ∈ s, corr3 ν f (G c) h := by
  unfold corr3 FinProb.cexpect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]

private theorem t3_corr3_sum_right {κ : Type} (s : Finset κ) (ν : FinProb (X × Y × Z))
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (H : κ → (ι → Z) → ℂ) :
    corr3 ν f g (∑ c ∈ s, H c) = ∑ c ∈ s, corr3 ν f g (H c) := by
  unfold corr3 FinProb.cexpect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_apply, Finset.mul_sum]

private theorem t3_corr3_smul_left (ν : FinProb (X × Y × Z)) (a : ℂ)
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν (a • f) g h = a * corr3 ν f g h := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem t3_corr3_smul_mid (ν : FinProb (X × Y × Z)) (a : ℂ)
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν f (a • g) h = a * corr3 ν f g h := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem t3_corr3_smul_right (ν : FinProb (X × Y × Z)) (a : ℂ)
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν f g (a • h) = a * corr3 ν f g h := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem t3_char_unit (χ : AddChar Unit ℂ) : χ () = 1 := by
  have hx : (() : Unit) = 0 := Subsingleton.elim _ _
  rw [hx, AddChar.map_zero_eq_one]

private theorem t3_corr3_mono {Jx Jy Jz : Type} (ν : FinProb (X × Y × Z)) (ux : Jx → X → ℂ)
    (uy : Jy → Y → ℂ) (uz : Jz → Z → ℂ) (cx : ι → Jx) (cy : ι → Jy) (cz : ι → Jz) :
    corr3 ν (s7Mono ux cx) (s7Mono uy cy) (s7Mono uz cz) =
      ∏ i, ν.cexpect (fun p => ux (cx i) p.1 * uy (cy i) p.2.1 * uz (cz i) p.2.2) := by
  unfold corr3
  rw [← cexpect_pi_prod ν (fun i p => ux (cx i) p.1 * uy (cy i) p.2.1 * uz (cz i) p.2.2)]
  congr 1
  funext t
  simp only [s7Mono, Finset.prod_mul_distrib]

private theorem t3_cexpect_lawZ (ν : FinProb (X × Y × Z)) (w : Z → ℂ) :
    ν.cexpect (fun p => w p.2.2) = (lawZ ν).cexpect w := by
  unfold FinProb.cexpect
  show _ = ∑ z, ((∑ a ∈ univ.filter (fun a : X × Y × Z => a.2.2 = z), ν.prob a : ℝ) : ℂ) * w z
  rw [← Finset.sum_fiberwise univ (fun p : X × Y × Z => p.2.2)
    (fun p => (ν.prob p : ℂ) * w p.2.2)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]

private theorem t3_cexpect_u_nonembed {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    {Sm : Finset A} (B : S7ModestBasis D (fun _ : A => ()) Sm) (j : B.J)
    (hj : ¬ ∃ a, j = Sum.inl a) : D.cexpect (B.u j) = 0 := by
  have h := s7_modestBasis_orthonormal D (fun _ : A => ()) Sm B j (Sum.inl 1)
  have hne : j ≠ Sum.inl 1 := fun h' => hj ⟨1, h'⟩
  simp only [hne, ite_false] at h
  have e : B.u (Sum.inl 1) = fun _ => 1 := by
    funext a
    simp [S7ModestBasis.u]
  rw [e] at h
  unfold FinProb.cinner at h
  simpa using h


private theorem t3_mono_zero (ν : FinProb (X × Y × Z)) (Sx : Finset X) (Sy : Finset Y)
    (Sz : Finset Z)
    (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sx)
    (By : S7ModestBasis (lawY ν) (fun _ : Y => ()) Sy)
    (Bz : S7ModestBasis (lawZ ν) (fun _ : Z => ()) Sz)
    (cx : ι → Bx.J) (cy : ι → By.J) (cz : ι → Bz.J)
    (hk : s7NeDeg cx + s7NeDeg cy < s7NeDeg cz) :
    corr3 ν (s7Mono Bx.u cx) (s7Mono By.u cy) (s7Mono Bz.u cz) = 0 := by
  by_contra hne
  rw [t3_corr3_mono] at hne
  have hall := Finset.prod_ne_zero_iff.1 hne
  have hsub : {i | ¬ ∃ a, cz i = Sum.inl a} ⊆
      {i | ¬ ∃ a, cx i = Sum.inl a} ∪ {i | ¬ ∃ a, cy i = Sum.inl a} := by
    intro i hi
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon hi
    obtain ⟨⟨χ, hχ⟩, ⟨χ', hχ'⟩⟩ := hcon
    apply hall i (Finset.mem_univ i)
    have e1 : ∀ p : X × Y × Z, Bx.u (cx i) p.1 = 1 := by
      intro p
      rw [hχ]
      simp [S7ModestBasis.u, t3_char_unit]
    have e2 : ∀ p : X × Y × Z, By.u (cy i) p.2.1 = 1 := by
      intro p
      rw [hχ']
      simp [S7ModestBasis.u, t3_char_unit]
    simp only [e1, e2, one_mul]
    rw [t3_cexpect_lawZ ν (Bz.u (cz i))]
    exact t3_cexpect_u_nonembed (lawZ ν) Bz (cz i) hi
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le {i | ¬ ∃ a, cx i = Sum.inl a} {i | ¬ ∃ a, cy i = Sum.inl a}
  unfold s7NeDeg s7CountWhere at hk
  beta_reduce at hk
  omega

end Extras

end CS

section Parts
variable {A : Type} [Fintype A] {ι : Type} [Fintype ι] [DecidableEq ι]
  {J : Type} [Fintype J] [DecidableEq J]

open scoped Classical in
private theorem t3_part_eq (D : FinProb A) (u : J → A → ℂ) (P : (ι → J) → Prop)
    (f : (ι → A) → ℂ) :
    s7Part D u P f = ∑ c : ι → J, (if P c then s7Coef D u f c else 0) • s7Mono u c := by
  unfold s7Part
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

open scoped Classical in
private theorem t3_part_part (D : FinProb A) (u : J → A → ℂ)
    (hu : ∀ i j, D.cinner (u i) (u j) = if i = j then 1 else 0) (P Q : (ι → J) → Prop)
    (f : (ι → A) → ℂ) :
    s7Part D u P (s7Part D u Q f) = s7Part D u (fun c => P c ∧ Q c) f := by
  rw [t3_part_eq D u P (s7Part D u Q f), t3_part_eq D u (fun c => P c ∧ Q c) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [s7Part_coef D u hu]
  by_cases hP : P c <;> by_cases hQ : Q c <;> simp [hP, hQ]

private theorem t3_sum_ite_unique {κ : Type} {M : Type} [AddCommMonoid M] (s : Finset κ)
    (Pa : κ → Prop) [DecidablePred Pa] (a0 : κ) (h0 : a0 ∈ s) (ha0 : Pa a0)
    (hu : ∀ a, Pa a → a = a0) (x : M) : ∑ a ∈ s, (if Pa a then x else 0) = x := by
  rw [Finset.sum_eq_single a0]
  · simp [ha0]
  · intro b _ hb
    have : ¬ Pa b := fun h => hb (hu b h)
    simp [this]
  · intro h; exact absurd h0 h

open scoped Classical in
/-- `f` is the sum of its parts over a partition of the monomials into finitely many classes. -/
private theorem t3_part_sum {κ : Type} (D : FinProb A) (hD : ∀ a, 0 < D.prob a) (u : J → A → ℂ)
    (hONB : S7IsONB D u) (s : Finset κ) (Pa : κ → (ι → J) → Prop)
    (hs : ∀ c, ∃ a ∈ s, Pa a c) (hu : ∀ c a b, Pa a c → Pa b c → a = b) (f : (ι → A) → ℂ) :
    f = ∑ a ∈ s, s7Part D u (Pa a) f := by
  conv_lhs => rw [s7_fourier_expansion D hD u hONB f]
  unfold s7Part
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨a0, ha0s, ha0⟩ := hs c
  exact (t3_sum_ite_unique s (fun a => Pa a c) a0 ha0s ha0 (fun a ha => hu c a a0 ha ha0) _).symm

open scoped Classical in
/-- Parseval for the parts of a partition. -/
private theorem t3_part_parseval {κ : Type} (D : FinProb A) (hD : ∀ a, 0 < D.prob a)
    (u : J → A → ℂ) (hONB : S7IsONB D u) (s : Finset κ) (Pa : κ → (ι → J) → Prop)
    (hs : ∀ c, ∃ a ∈ s, Pa a c) (hu : ∀ c a b, Pa a c → Pa b c → a = b) (f : (ι → A) → ℂ) :
    ∑ a ∈ s, cl2sq D (s7Part D u (Pa a) f) = cl2sq D f := by
  have e1 : ∀ a, cl2sq D (s7Part D u (Pa a) f) =
      ∑ c ∈ univ.filter (Pa a), ‖s7Coef D u f c‖ ^ 2 := fun a =>
    s7Part_expect_sq D hD u hONB (Pa a) f
  have e2 : cl2sq D f = ∑ c, ‖s7Coef D u f c‖ ^ 2 := s7_parseval D hD u hONB f
  simp only [e1]
  rw [e2]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨a0, ha0s, ha0⟩ := hs c
  exact t3_sum_ite_unique s (fun a => Pa a c) a0 ha0s ha0 (fun a ha => hu c a a0 ha ha0) _

/-- parts are bounded by the whole -/
private theorem t3_part_norm_le (D : FinProb A) (hD : ∀ a, 0 < D.prob a)
    (u : J → A → ℂ) (hONB : S7IsONB D u) (P : (ι → J) → Prop) (f : (ι → A) → ℂ) :
    cl2norm D (s7Part D u P f) ≤ cl2norm D f := by
  classical
  unfold cl2norm
  refine Real.sqrt_le_sqrt ?_
  have e1 : cl2sq D (s7Part D u P f) = ∑ c ∈ univ.filter P, ‖s7Coef D u f c‖ ^ 2 :=
    s7Part_expect_sq D hD u hONB P f
  have e2 : cl2sq D f = ∑ c, ‖s7Coef D u f c‖ ^ 2 := s7_parseval D hD u hONB f
  rw [e1, e2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun c _ _ => sq_nonneg _)

private theorem t3_part_mass_le {κ : Type} (D : FinProb A) (hD : ∀ a, 0 < D.prob a) (u : J → A → ℂ)
    (hONB : S7IsONB D u) (s s' : Finset κ) (hss : s' ⊆ s) (Pa : κ → (ι → J) → Prop)
    (hs : ∀ c, ∃ a ∈ s, Pa a c) (hu : ∀ c a b, Pa a c → Pa b c → a = b) (f : (ι → A) → ℂ)
    (hf : cl2norm D f ≤ 1) : ∑ a ∈ s', cl2norm D (s7Part D u (Pa a) f) ^ 2 ≤ 1 := by
  calc ∑ a ∈ s', cl2norm D (s7Part D u (Pa a) f) ^ 2 ≤
        ∑ a ∈ s, cl2norm D (s7Part D u (Pa a) f) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hss (fun _ _ _ => sq_nonneg _)
    _ = cl2sq D f := by
        rw [← t3_part_parseval D hD u hONB s Pa hs hu f]
        exact Finset.sum_congr rfl fun p _ => by
          unfold cl2norm; exact Real.sq_sqrt (Finset.sum_nonneg fun x _ =>
            mul_nonneg ((D.pi ι).nonneg x) (sq_nonneg _))
    _ ≤ 1 := by
        unfold cl2norm at hf
        have := Real.sqrt_le_one.1 hf
        exact this

end Parts

section DegRange
variable {K₁ K₂ : Type} {n : ℕ}

private theorem t3_neDeg_le (c : Fin n → AddChar Unit ℂ ⊕ (K₁ ⊕ K₂)) : s7NeDeg c ≤ n := by
  have := s7_embedDeg_add_neDeg (H := Unit) (K₁ := K₁) (K₂ := K₂) c
  simp only [Fintype.card_fin] at this
  omega

private theorem t3_effDeg_le (c : Fin n → AddChar Unit ℂ ⊕ (K₁ ⊕ K₂)) : s7EffDeg c ≤ n :=
  (s7_effDeg_le_neDeg (H := Unit) c).trans (t3_neDeg_le c)

private theorem t3_prof_ex (cc : Fin n → AddChar Unit ℂ ⊕ (K₁ ⊕ K₂)) :
    ∃ p ∈ range (n + 1) ×ˢ range (n + 1), s7EffDeg cc = p.1 ∧ s7NeDeg cc = p.2 :=
  ⟨(s7EffDeg cc, s7NeDeg cc), by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (t3_effDeg_le cc), Nat.lt_succ_of_le (t3_neDeg_le cc)⟩, rfl, rfl⟩

private theorem t3_prof_uniq (cc : Fin n → AddChar Unit ℂ ⊕ (K₁ ⊕ K₂)) (p q : ℕ × ℕ)
    (hp : s7EffDeg cc = p.1 ∧ s7NeDeg cc = p.2) (hq : s7EffDeg cc = q.1 ∧ s7NeDeg cc = q.2) :
    p = q := Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2)

private theorem t3_deg_ex (cc : Fin n → AddChar Unit ℂ ⊕ (K₁ ⊕ K₂)) :
    ∃ j ∈ range (n + 1), s7NeDeg cc = j :=
  ⟨s7NeDeg cc, Finset.mem_range.2 (Nat.lt_succ_of_le (t3_neDeg_le cc)), rfl⟩

end DegRange

private theorem t3_cl2norm_sq {A : Type} [Fintype A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : FinProb A) (f : (ι → A) → ℂ) : cl2norm D f ^ 2 = cl2sq D f := by
  unfold cl2norm
  refine Real.sq_sqrt (Finset.sum_nonneg fun x _ => mul_nonneg ((D.pi ι).nonneg x) (sq_nonneg _))

private theorem t3_cl2norm_le_one {A : Type} [Fintype A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : FinProb A) (f : (ι → A) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) : cl2norm D f ≤ 1 := by
  unfold cl2norm
  rw [Real.sqrt_le_one]
  calc cl2sq D f ≤ ∑ x, (D.pi ι).prob x * 1 := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ((D.pi ι).nonneg x)
        have := hf x
        have h0 := norm_nonneg (f x)
        nlinarith
    _ = 1 := by simp [(D.pi ι).sum_eq_one]


private theorem t3_sum_le_sqrt_card {κ : Type} (s : Finset κ) (a : κ → ℝ)
    (h2 : ∑ i ∈ s, a i ^ 2 ≤ 1) : ∑ i ∈ s, a i ≤ Real.sqrt (s.card : ℝ) := by
  have h1 : (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) := by
    calc (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (s.card : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = _ := mul_one _
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

private theorem t3_sum_profiles_fin {α β γ : Type} (sa : Finset α) (sb : Finset β)
    (sc : Finset γ) (a : α → ℝ) (b : β → ℝ) (c : γ → ℝ) (w : α → β → γ → ℝ) (w₀ : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (hc : ∀ k, 0 ≤ c k)
    (ha2 : ∑ i ∈ sa, a i ^ 2 ≤ 1) (hb2 : ∑ j ∈ sb, b j ^ 2 ≤ 1) (hc2 : ∑ k ∈ sc, c k ^ 2 ≤ 1)
    (hw : ∀ i j k, |w i j k| ≤ w₀) :
    ∑ i ∈ sa, ∑ j ∈ sb, ∑ k ∈ sc, |w i j k| * a i * b j * c k ≤
      w₀ * Real.sqrt ((sa.card : ℝ) * sb.card * sc.card) := by
  rcases sa.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · simp
  rcases sb.eq_empty_or_nonempty with rfl | ⟨j0, hj0⟩
  · simp
  rcases sc.eq_empty_or_nonempty with rfl | ⟨k0, hk0⟩
  · simp
  have hw0 : 0 ≤ w₀ := (abs_nonneg _).trans (hw i0 j0 k0)
  have hA := t3_sum_le_sqrt_card sa a ha2
  have hB := t3_sum_le_sqrt_card sb b hb2
  have hC := t3_sum_le_sqrt_card sc c hc2
  have hA0 : 0 ≤ ∑ i ∈ sa, a i := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ ∑ j ∈ sb, b j := Finset.sum_nonneg fun j _ => hb j
  have hC0 : 0 ≤ ∑ k ∈ sc, c k := Finset.sum_nonneg fun k _ => hc k
  calc ∑ i ∈ sa, ∑ j ∈ sb, ∑ k ∈ sc, |w i j k| * a i * b j * c k
      ≤ ∑ i ∈ sa, ∑ j ∈ sb, ∑ k ∈ sc, w₀ * a i * b j * c k := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => ?_
        have := hw i j k
        have h1 := ha i
        have h2 := hb j
        have h3 := hc k
        have : |w i j k| * a i * b j ≤ w₀ * a i * b j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this h1) h2
        exact mul_le_mul_of_nonneg_right this h3
    _ = w₀ * ((∑ i ∈ sa, a i) * (∑ j ∈ sb, b j) * (∑ k ∈ sc, c k)) := by
        have e : ∀ i j, ∑ k ∈ sc, w₀ * a i * b j * c k =
            w₀ * a i * b j * ∑ k ∈ sc, c k := fun i j => (Finset.mul_sum _ _ _).symm
        simp only [e]
        have e2 : ∀ i, ∑ j ∈ sb, w₀ * a i * b j * (∑ k ∈ sc, c k) =
            w₀ * a i * (∑ j ∈ sb, b j) * (∑ k ∈ sc, c k) := by
          intro i
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp only [e2]
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
    _ ≤ w₀ * (Real.sqrt (sa.card : ℝ) * Real.sqrt (sb.card : ℝ) * Real.sqrt (sc.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hw0
        exact mul_le_mul (mul_le_mul hA hB hB0 (Real.sqrt_nonneg _)) hC hC0
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]

private theorem t3_four_sum (n : ℕ) (T : ℕ → ℕ → ℕ → ℕ → ℝ) (a : ℕ → ℕ → ℝ) (b c : ℕ → ℝ)
    (w₀ : ℝ) (sa : Finset (ℕ × ℕ)) (sb sc : Finset ℕ)
    (hsa : sa ⊆ range (n + 1) ×ˢ range (n + 1)) (hsb : sb ⊆ range (n + 1))
    (hsc : sc ⊆ range (n + 1))
    (hT0 : ∀ i ∈ range (n + 1), ∀ i' ∈ range (n + 1), ∀ j ∈ range (n + 1), ∀ k ∈ range (n + 1),
      ¬ ((i, i') ∈ sa ∧ j ∈ sb ∧ k ∈ sc) → T i i' j k = 0)
    (hT : ∀ i i' j k, (i, i') ∈ sa → j ∈ sb → k ∈ sc → T i i' j k ≤ w₀ * a i i' * b j * c k)
    (ha : ∀ i i', 0 ≤ a i i') (hb : ∀ j, 0 ≤ b j) (hc : ∀ k, 0 ≤ c k)
    (ha2 : ∑ p ∈ sa, a p.1 p.2 ^ 2 ≤ 1) (hb2 : ∑ j ∈ sb, b j ^ 2 ≤ 1)
    (hc2 : ∑ k ∈ sc, c k ^ 2 ≤ 1) (hw0 : 0 ≤ w₀) :
    ∑ i ∈ range (n + 1), ∑ i' ∈ range (n + 1), ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
      T i i' j k ≤ w₀ * Real.sqrt ((sa.card : ℝ) * sb.card * sc.card) := by
  have e1 : ∑ i ∈ range (n + 1), ∑ i' ∈ range (n + 1), ∑ j ∈ range (n + 1),
      ∑ k ∈ range (n + 1), T i i' j k =
      ∑ p ∈ range (n + 1) ×ˢ range (n + 1), ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
        T p.1 p.2 j k := by
    rw [Finset.sum_product]
  have e2 : ∑ p ∈ range (n + 1) ×ˢ range (n + 1), ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
        T p.1 p.2 j k = ∑ p ∈ sa, ∑ j ∈ sb, ∑ k ∈ sc, T p.1 p.2 j k := by
    rw [← Finset.sum_subset hsa]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.sum_subset hsb]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.sum_subset hsc]
        · intro k hk hk'
          have hp' := Finset.mem_product.1 (hsa hp)
          exact hT0 _ hp'.1 _ hp'.2 _ (hsb hj) _ hk (fun h => hk' h.2.2)
      · intro j hj hj'
        refine Finset.sum_eq_zero fun k hk => ?_
        have hp' := Finset.mem_product.1 (hsa hp)
        exact hT0 _ hp'.1 _ hp'.2 _ hj _ hk (fun h => hj' h.2.1)
    · intro p hp hp'
      refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk => ?_
      have hp'' := Finset.mem_product.1 hp
      exact hT0 _ hp''.1 _ hp''.2 _ hj _ hk (fun h => hp' h.1)
  rw [e1, e2]
  have h3 := t3_sum_profiles_fin sa sb sc (fun p => a p.1 p.2) b c (fun _ _ _ => w₀) w₀ (fun p => ha _ _)
    hb hc ha2 hb2 hc2 (fun _ _ _ => by rw [abs_of_nonneg hw0])
  refine le_trans ?_ h3
  refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
  rw [abs_of_nonneg hw0]
  exact hT p.1 p.2 j k hp hj hk

section Pos
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem t3_exists_of_graph {S : Set (X × Y × Z)} (hy : Nonempty Y)
    (hc : (SimpleGraph.fromRel fun (a : X ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y).Connected) (x : X) :
    ∃ y z, (x, y, z) ∈ S := by
  obtain ⟨y0⟩ := hy
  obtain ⟨w⟩ := hc.preconnected (Sum.inl x) (Sum.inr y0)
  cases w with
  | cons h _ =>
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨x', y', z', hm, h1, h2⟩ | ⟨x', y', z', hm, h1, h2⟩
    · obtain rfl := Sum.inl_injective h1
      exact ⟨y', z', hm⟩
    · exact absurd h2 (by simp)

private theorem t3_prob_le_push {β : Type} [Fintype β] [DecidableEq β] (ν : FinProb (X × Y × Z))
    (f : X × Y × Z → β) (p : X × Y × Z) : ν.prob p ≤ (mergePush ν f).prob (f p) := by
  show ν.prob p ≤ ∑ a ∈ univ.filter (fun a => f a = f p), ν.prob a
  exact Finset.single_le_sum (f := ν.prob) (fun a _ => ν.nonneg a)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)

private theorem t3_laws_pos {K : ℕ} {α : ℝ} {ν : FinProb (X × Y × Z)} {Sg Sm : Finset X}
    {Phi' : Finset Z} (hα : 0 < α) (hR : Rel67 K α ν Sg Sm Phi') :
    (∀ a, 0 < (lawX ν).prob a) ∧ (∀ a, 0 < (lawY ν).prob a) ∧ (∀ a, 0 < (lawZ ν).prob a) := by
  have hne : ∃ p, p ∈ ν.support := by
    by_contra hcon
    push Not at hcon
    have : ∀ p, ν.prob p = 0 := fun p => by
      by_contra h; exact hcon p h
    have h1 := ν.sum_eq_one
    simp [this] at h1
  obtain ⟨p0, hp0⟩ := hne
  have hY : Nonempty Y := ⟨p0.2.1⟩
  have hZ : Nonempty Z := ⟨p0.2.2⟩
  have hatom : ∀ p, p ∈ ν.support → 0 < ν.prob p := fun p hp =>
    lt_of_lt_of_le hα (hR.atoms p hp)
  refine ⟨fun x => ?_, fun y => ?_, fun z => ?_⟩
  · obtain ⟨y, z, hm⟩ := t3_exists_of_graph hY ((pairwiseConnected3_iff _).1 hR.inT.1).1 x
    exact lt_of_lt_of_le (hatom _ hm) (t3_prob_le_push ν (fun p => p.1) (x, y, z))
  · obtain ⟨z0⟩ := hZ
    obtain ⟨x, hm⟩ := hR.yz_full y z0
    exact lt_of_lt_of_le (hatom _ hm) (t3_prob_le_push ν (fun p => p.2.1) (x, y, z0))
  · obtain ⟨y0⟩ := hY
    obtain ⟨x, hm⟩ := hR.yz_full y0 z
    exact lt_of_lt_of_le (hatom _ hm) (t3_prob_le_push ν (fun p => p.2.2) (x, y0, z))

end Pos
section Misc
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem t3_corr3_zero_left (ν : FinProb (X × Y × Z)) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) : corr3 ν (0 : (ι → X) → ℂ) g h = 0 := by
  simp [corr3, FinProb.cexpect]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem t3_corr3_zero_mid (ν : FinProb (X × Y × Z)) (f : (ι → X) → ℂ)
    (h : (ι → Z) → ℂ) : corr3 ν f (0 : (ι → Y) → ℂ) h = 0 := by
  simp [corr3, FinProb.cexpect]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem t3_corr3_zero_right (ν : FinProb (X × Y × Z)) (f : (ι → X) → ℂ)
    (g : (ι → Y) → ℂ) : corr3 ν f g (0 : (ι → Z) → ℂ) = 0 := by
  simp [corr3, FinProb.cexpect]

open scoped Classical in
private theorem t3_part_zero {A : Type} [Fintype A] {J : Type} [Fintype J]
    (D : FinProb A) (u : J → A → ℂ) (P : (ι → J) → Prop) (hP : ∀ c, ¬ P c)
    (f : (ι → A) → ℂ) : s7Part D u P f = 0 := by
  unfold s7Part
  exact Finset.sum_eq_zero fun c _ => by simp [hP c]

private theorem t3_eq_zero_of_norm {A : Type} [Fintype A] (D : FinProb A)
    (hD : ∀ a, 0 < D.prob a) (f : (ι → A) → ℂ) (h : cl2norm D f = 0) : f = 0 := by
  unfold cl2norm at h
  have h0 : cl2sq D f = 0 := by
    have hnn : 0 ≤ cl2sq D f :=
      Finset.sum_nonneg fun x _ => mul_nonneg ((D.pi ι).nonneg x) (sq_nonneg _)
    exact le_antisymm (Real.sqrt_eq_zero'.1 h) hnn
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    mul_nonneg ((D.pi ι).nonneg x) (sq_nonneg ‖f x‖))).1 h0
  funext x
  have hx := this x (Finset.mem_univ x)
  have hp : 0 < (D.pi ι).prob x := Finset.prod_pos fun i _ => hD (x i)
  have : ‖f x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 hx with h | h
    · exact absurd h hp.ne'
    · exact h
  simpa using this

private theorem t3_norm_sum4 {a b c d : Type} (s1 : Finset a) (s2 : Finset b) (s3 : Finset c)
    (s4 : Finset d) (x : a → b → c → d → ℂ) :
    ‖∑ i ∈ s1, ∑ i' ∈ s2, ∑ j ∈ s3, ∑ k ∈ s4, x i i' j k‖ ≤
      ∑ i ∈ s1, ∑ i' ∈ s2, ∑ j ∈ s3, ∑ k ∈ s4, ‖x i i' j k‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i' _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact norm_sum_le _ _

end Misc

private theorem t3_absorb {c' : ℝ} (hc' : 0 < c') {p : ℝ} (hp : 0 ≤ p) :
    ∃ M₀ : ℝ, 1 ≤ M₀ ∧ ∀ E : ℝ, 0 ≤ E →
      E ^ p * (1 + c') ^ (-E) ≤ M₀ * (1 + c' / 2) ^ (-E) := by
  have hq : (1 + c' / 2) < (1 + c') := by linarith
  have hb : 0 < Real.log ((1 + c') / (1 + c' / 2)) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hq)
  have hT := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p _ hb
  obtain ⟨E₀, hE₀⟩ := Filter.eventually_atTop.1 (hT.eventually (Iio_mem_nhds one_pos))
  refine ⟨max 1 (max E₀ 1 ^ p), le_max_left _ _, fun E hE => ?_⟩
  have e : (1 + c') ^ (-E) = (1 + c' / 2) ^ (-E) * Real.exp (-Real.log ((1 + c') / (1 + c' / 2)) * E) := by
    rw [neg_mul, Real.exp_neg, ← Real.rpow_def_of_pos (by positivity)]
    rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_neg (by positivity)]
    field_simp
  rw [e]
  have hpos : 0 < (1 + c' / 2) ^ (-E) := by positivity
  have hexp := Real.exp_pos (-Real.log ((1 + c') / (1 + c' / 2)) * E)
  have key : E ^ p * Real.exp (-Real.log ((1 + c') / (1 + c' / 2)) * E) ≤
      max 1 (max E₀ 1 ^ p) := by
    by_cases h : E₀ ≤ E
    · have := hE₀ E h
      exact (le_of_lt this).trans (le_max_left _ _)
    · push Not at h
      have h1 : E ^ p ≤ max E₀ 1 ^ p :=
        Real.rpow_le_rpow hE (h.le.trans (le_max_left _ _)) hp
      have h2 : Real.exp (-Real.log ((1 + c') / (1 + c' / 2)) * E) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.log ((1 + c') / (1 + c' / 2)) * E := mul_nonneg hb.le hE
        linarith
      calc E ^ p * Real.exp (-Real.log ((1 + c') / (1 + c' / 2)) * E)
          ≤ max E₀ 1 ^ p * 1 := mul_le_mul h1 h2 hexp.le (by positivity)
        _ ≤ _ := by rw [mul_one]; exact le_max_right _ _
  calc E ^ p * ((1 + c' / 2) ^ (-E) * Real.exp (-Real.log ((1 + c') / (1 + c' / 2)) * E))
      = (E ^ p * Real.exp (-Real.log ((1 + c') / (1 + c' / 2)) * E)) * (1 + c' / 2) ^ (-E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right key hpos.le


private theorem t3_appTp_norm_le {A : Type} [Fintype A] [DecidableEq A] {ι : Type} [Fintype ι]
    [DecidableEq ι] (D : FinProb A) (hD : ∀ a, 0 < D.prob a)
    (By : S7ModestBasis D (fun _ : A => ()) (∅ : Finset A)) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (g : (ι → A) → ℂ) : cl2norm D (appTp D ρ g) ≤ cl2norm D g := by
  have hONB := s7_modestBasis_isONB D (fun _ : A => ()) (∅ : Finset A) hD By
  have h := t3_norm_le D hD By.u hONB (appTp D ρ g) g zero_le_one ?_
  · simpa using h
  · intro c
    have hcoefG : s7Coef D By.u (appTp D ρ g) c =
        (((1 - ρ / 2 : ℝ) : ℂ) ^ s7NeDeg c - ((1 - ρ : ℝ) : ℂ) ^ s7NeDeg c) *
          s7Coef D By.u g c := by
      unfold appTp
      rw [t3_coef_sub, t3_coef_tNE hD By, t3_coef_tNE hD By]
      ring
    have e : ((1 - ρ / 2 : ℝ) : ℂ) ^ s7NeDeg c - ((1 - ρ : ℝ) : ℂ) ^ s7NeDeg c =
        (((1 - ρ / 2) ^ s7NeDeg c - (1 - ρ) ^ s7NeDeg c : ℝ) : ℂ) := by push_cast; ring
    have hb0 : 0 ≤ 1 - ρ := by linarith
    have hba : 1 - ρ ≤ 1 - ρ / 2 := by linarith
    have h1 : 0 ≤ (1 - ρ / 2) ^ s7NeDeg c - (1 - ρ) ^ s7NeDeg c :=
      sub_nonneg.2 (pow_le_pow_left₀ hb0 hba _)
    have h2 : (1 - ρ / 2) ^ s7NeDeg c ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h3 : 0 ≤ (1 - ρ) ^ s7NeDeg c := pow_nonneg hb0 _
    rw [hcoefG, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end Helpers

section Trunc3
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `g'` truncated to non-embedding degrees strictly between `ρ^{-(1-ξ)}` and `ρ^{-(1+ξ)}`
(`#truncate-g-degree`, l. 9219-9227): the two discarded parts have `‖·‖₂ ≤ ρ^ξ` (so the rest has
norm `≤ 2ρ^ξ`; `‖g‖₂ ≤ 1`). -/
theorem appB_t3_g_parts {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (A : Type) [Fintype A] [DecidableEq A] (D : FinProb A) (hD : ∀ a, 0 < D.prob a)
        (By : S7ModestBasis D (fun _ : A => ()) (∅ : Finset A)) (n : ℕ)
        (g : (Fin n → A) → ℂ), cl2norm D g ≤ 1 →
        cl2norm D (appTp D ρ g - s7Part D By.u (fun c => ρ ^ (-(1 - ξ)) < (s7NeDeg c : ℝ) ∧
          (s7NeDeg c : ℝ) < ρ ^ (-(1 + ξ))) (appTp D ρ g)) ≤ 2 * ρ ^ ξ := by
  have _ := hξ
  have _ := hξ1
  refine ⟨1, one_pos, fun ρ hρ hρ1 A _ _ D hD By n g hg => ?_⟩
  have hONB := s7_modestBasis_isONB D (fun _ : A => ()) (∅ : Finset A) hD By
  have hcoefG : ∀ c, s7Coef D By.u (appTp D ρ g) c =
      (((1 - ρ / 2 : ℝ) : ℂ) ^ s7NeDeg c - ((1 - ρ : ℝ) : ℂ) ^ s7NeDeg c) * s7Coef D By.u g c := by
    intro c
    unfold appTp
    rw [t3_coef_sub, t3_coef_tNE hD By, t3_coef_tNE hD By]
    ring
  have hs : 0 ≤ 2 * ρ ^ ξ := by positivity
  have h1 := t3_norm_le D hD By.u hONB
    (appTp D ρ g - s7Part D By.u (fun c => ρ ^ (-(1 - ξ)) < (s7NeDeg c : ℝ) ∧
          (s7NeDeg c : ℝ) < ρ ^ (-(1 + ξ))) (appTp D ρ g)) g hs ?_
  · calc _ ≤ 2 * ρ ^ ξ * cl2norm D g := h1
      _ ≤ 2 * ρ ^ ξ * 1 := mul_le_mul_of_nonneg_left hg hs
      _ = _ := mul_one _
  · intro c
    rw [t3_coef_sub, s7Part_coef D By.u (fun i j => s7_modestBasis_orthonormal D _ _ By i j)]
    by_cases hP : ρ ^ (-(1 - ξ)) < (s7NeDeg c : ℝ) ∧ (s7NeDeg c : ℝ) < ρ ^ (-(1 + ξ))
    · simp only [hP, and_self, ite_true, sub_self, norm_zero]
      positivity
    · simp only [hP, ite_false, sub_zero]
      rw [hcoefG, norm_mul]
      exact mul_le_mul_of_nonneg_right (t3_g_mult hρ hρ1 _ hP) (norm_nonneg _)

/-- `f''` truncated to effective degree `≥ d₃ = ρ^{-(1-2ξ)}` and non-embedding degree `≤ d₄ =
ρ^{-(1+2ξ)}` (`#truncate-f-degrees`, l. 9228-9240), `f'' = (I - E_{non-embed,1-ρ^{1-ξ}}) f'`,
`f' = T_{non-embed,1-ρ^{1+ξ}} f`, `‖f‖₂ ≤ 1`; the discarded part has norm `≤ 2ρ^ξ`, and
`‖f''‖₂ ≤ 1`. -/
theorem appB_t3_f_parts {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (A : Type) [Fintype A] [DecidableEq A] (D : FinProb A) (hD : ∀ a, 0 < D.prob a)
        (σ : A → Unit) (Sm : Finset A) (Bx : S7ModestBasis D σ Sm) (n : ℕ)
        (f : (Fin n → A) → ℂ), cl2norm D f ≤ 1 →
        cl2norm D (tNE D (ρ ^ (1 + ξ)) f - s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f)) ≤ 1 ∧
        cl2norm D ((tNE D (ρ ^ (1 + ξ)) f - s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f)) -
          s7Part D Bx.u (fun c => ρ ^ (-(1 - 2 * ξ)) ≤ (s7EffDeg c : ℝ) ∧
            (s7NeDeg c : ℝ) ≤ ρ ^ (-(1 + 2 * ξ)))
            (tNE D (ρ ^ (1 + ξ)) f - s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f))) ≤
          2 * ρ ^ ξ := by
  refine ⟨1, one_pos, fun ρ hρ hρ1 A _ _ D hD σ Sm Bx n f hf => ?_⟩
  have hσ : σ = fun _ : A => () := funext fun _ => Subsingleton.elim _ _
  subst hσ
  have hONB := s7_modestBasis_isONB D (fun _ : A => ()) Sm hD Bx
  have hδ : 0 < ρ ^ (1 - ξ) := Real.rpow_pos_of_pos hρ _
  have hcoefF : ∀ c, s7Coef D Bx.u (tNE D (ρ ^ (1 + ξ)) f -
      s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f)) c =
      ((t3Mult ρ ξ (s7NeDeg c) (s7EffDeg c) : ℝ) : ℂ) * s7Coef D Bx.u f c := by
    intro c
    rw [t3_coef_sub, t3_coef_tNE hD Bx, t3_coef_eff hD Bx hδ, t3_coef_tNE hD Bx]
    unfold t3Mult
    push_cast
    ring
  have hξ2 : ξ < 1 := by linarith
  have h1 := t3_norm_le D hD Bx.u hONB (tNE D (ρ ^ (1 + ξ)) f -
      s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f)) f zero_le_one ?_
  · refine ⟨?_, ?_⟩
    · calc _ ≤ 1 * cl2norm D f := h1
        _ ≤ 1 := by linarith
    · have hs : 0 ≤ 2 * ρ ^ ξ := by positivity
      have h2 := t3_norm_le D hD Bx.u hONB ((tNE D (ρ ^ (1 + ξ)) f -
          s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f)) - s7Part D Bx.u (fun c =>
          ρ ^ (-(1 - 2 * ξ)) ≤ (s7EffDeg c : ℝ) ∧ (s7NeDeg c : ℝ) ≤ ρ ^ (-(1 + 2 * ξ)))
          (tNE D (ρ ^ (1 + ξ)) f - s7EffNoiseOp D Sm (ρ ^ (1 - ξ)) (tNE D (ρ ^ (1 + ξ)) f))) f hs ?_
      · calc _ ≤ 2 * ρ ^ ξ * cl2norm D f := h2
          _ ≤ 2 * ρ ^ ξ * 1 := mul_le_mul_of_nonneg_left hf hs
          _ = _ := mul_one _
      · intro c
        rw [t3_coef_sub, s7Part_coef D Bx.u (fun i j => s7_modestBasis_orthonormal D _ _ Bx i j)]
        by_cases hP : ρ ^ (-(1 - 2 * ξ)) ≤ (s7EffDeg c : ℝ) ∧
            (s7NeDeg c : ℝ) ≤ ρ ^ (-(1 + 2 * ξ))
        · simp only [hP, and_self, ite_true, sub_self, norm_zero]
          positivity
        · simp only [hP, ite_false, sub_zero]
          rw [hcoefF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have h3 := t3_f_mult_small hρ hρ1 hξ hξ1 (s7NeDeg c) (s7EffDeg c) hP
          have h4 := (t3_f_mult_nonneg hρ hρ1 hξ hξ2 (s7NeDeg c) (s7EffDeg c)).1
          rw [abs_of_nonneg h4]
          have : ρ ^ ξ ≤ 2 * ρ ^ ξ := by
            have := Real.rpow_pos_of_pos hρ ξ
            linarith
          exact mul_le_mul_of_nonneg_right (h3.trans this) (norm_nonneg _)
  · intro c
    rw [hcoefF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 := t3_f_mult_nonneg hρ hρ1 hξ (by linarith) (s7NeDeg c) (s7EffDeg c)
    rw [abs_of_nonneg h4.1]
    exact mul_le_mul_of_nonneg_right h4.2 (norm_nonneg _)

/-- Cauchy-Schwarz bookkeeping of l. 9248-9256: `|E F G h| ≤ ‖F - F₃‖₂‖G‖₂ + ‖F₃‖₂‖G - G₃‖₂ +
|E F₃ G₃ h|` for `1`-bounded `h`, with the `L²` norms of the three marginals. -/
theorem appB_t3_cs_split {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (F F₃ : (ι → X) → ℂ) (G G₃ : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖corr3 ν F G h‖ ≤ cl2norm (lawX ν) (F - F₃) * cl2norm (lawY ν) G +
      cl2norm (lawX ν) F₃ * cl2norm (lawY ν) (G - G₃) + ‖corr3 ν F₃ G₃ h‖ := by
  rw [t3_corr3_split ν F F₃ G G₃ h]
  refine (norm_add₃_le).trans ?_
  have h1 := t3_corr3_bound ν (F - F₃) G h hh
  have h2 := t3_corr3_bound ν F₃ (G - G₃) h hh
  linarith

/-- at `H = {0}` every non-embedding homogeneous function is completely embedding homogeneous
(`embeddeg + nedeg = n`, `s7_embedDeg_add_neDeg`, one character): this is the vacuous
`#embedding-degree-mismatch-vanishes` step (the group `H` is trivial, so the mismatch step is vacuous). -/
theorem appB_t3_compEmbedHom_trivial {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    {K₁ K₂ : Type} (u : AddChar Unit ℂ ⊕ (K₁ ⊕ K₂) → A → ℂ) {n d : ℕ}
    (f : (Fin n → A) → ℂ) (hf : S7NeHom D u f d) : S7CompEmbedHom D u f (n - d) := by
  refine ⟨fun _ => n - d, ?_, ?_⟩
  · have hc : (Finset.univ : Finset (AddChar Unit ℂ)).card = 1 :=
      Finset.card_eq_one.2 ⟨1, by ext a; simp [t3_addChar_unit_eq a 1]⟩
    simp [Finset.sum_const, hc]
  · intro c hc a
    have hne : s7NeDeg c = d := hf c hc
    have h1 := s7_embedDeg_add_neDeg (H := Unit) (K₁ := K₁) (K₂ := K₂) c
    have h2 := s7_embedDeg_eq_sum (H := Unit) (K₁ := K₁) (K₂ := K₂) c
    rw [Finset.sum_eq_single a (fun b _ hb => absurd (t3_addChar_unit_eq b a) hb)
      (fun h => absurd (Finset.mem_univ a) h)] at h2
    simp only [Fintype.card_fin] at h1
    change s7EmbedDegA a c = n - d
    rw [hne] at h1
    omega

/-- `#h-degree-bound` (l. 9293-9301): `E f g h = 0` if `h` is non-embedding homogeneous of degree
`k > i' + j` (`f`, `g` homogeneous of degrees `i'`, `j`): the conditional expectation of `f g` given
`z` has non-embedding degree `≤ i' + j`. -/
theorem appB_t3_h_degree_bound (ν : FinProb (X × Y × Z))
    (hDx : ∀ a, 0 < (lawX ν).prob a) (hDy : ∀ a, 0 < (lawY ν).prob a)
    (hDz : ∀ a, 0 < (lawZ ν).prob a) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm)
    (By : S7ModestBasis (lawY ν) (fun _ : Y => ()) (∅ : Finset Y))
    (Bz : S7ModestBasis (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z)) {n i' j k : ℕ}
    (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ)
    (hf : S7NeHom (lawX ν) Bx.u f i') (hg : S7NeHom (lawY ν) By.u g j)
    (hh : S7NeHom (lawZ ν) Bz.u h k) (hk : i' + j < k) : corr3 ν f g h = 0 := by
  have hx := s7_modestBasis_isONB (lawX ν) (fun _ : X => ()) Sm hDx Bx
  have hy := s7_modestBasis_isONB (lawY ν) (fun _ : Y => ()) (∅ : Finset Y) hDy By
  have hz := s7_modestBasis_isONB (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z) hDz Bz
  have hfx := s7_fourier_expansion (lawX ν) hDx Bx.u hx f
  have hgy := s7_fourier_expansion (lawY ν) hDy By.u hy g
  have hhz := s7_fourier_expansion (lawZ ν) hDz Bz.u hz h
  calc corr3 ν f g h = corr3 ν (∑ c, s7Coef (lawX ν) Bx.u f c • s7Mono Bx.u c)
        (∑ c, s7Coef (lawY ν) By.u g c • s7Mono By.u c)
        (∑ c, s7Coef (lawZ ν) Bz.u h c • s7Mono Bz.u c) := by
        rw [← hfx, ← hgy, ← hhz]
    _ = 0 := by
      rw [t3_corr3_sum_left]
      refine Finset.sum_eq_zero fun cx _ => ?_
      rw [t3_corr3_sum_mid]
      refine Finset.sum_eq_zero fun cy _ => ?_
      rw [t3_corr3_sum_right]
      refine Finset.sum_eq_zero fun cz _ => ?_
      rw [t3_corr3_smul_left, t3_corr3_smul_mid, t3_corr3_smul_right]
      by_cases ha : s7Coef (lawX ν) Bx.u f cx = 0
      · simp [ha]
      by_cases hb : s7Coef (lawY ν) By.u g cy = 0
      · simp [hb]
      by_cases he : s7Coef (lawZ ν) Bz.u h cz = 0
      · simp [he]
      have h0 := t3_mono_zero ν Sm ∅ ∅ Bx By Bz cx cy cz
        (by rw [hf cx ha, hg cy hb, hh cz he]; exact hk)
      rw [h0]
      simp

/-- the parts of effective degree exactly `i` and non-embedding degree exactly `i'` lie in
`F'_{n,i',i}` (`#apply-homogeneous-theorem`, membership); the parts of non-embedding degree exactly
`j` lie in `G_n`. -/
theorem appB_t3_parts_mem (ν : FinProb (X × Y × Z))
    (Sm : Finset X) (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm) {n : ℕ} (i i' : ℕ)
    (f : (Fin n → X) → ℂ) :
    s7Part (lawX ν) Bx.u (fun c => s7EffDeg c = i ∧ s7NeDeg c = i') f ∈
      s7ClassFp (K₁ := Fin Bx.nN) (K₂ := Fin Bx.nM) (lawX ν) Bx.u n i' i := by
  classical
  have hu := fun a b => s7_modestBasis_orthonormal (lawX ν) (fun _ : X => ()) Sm Bx a b
  have hne : S7NeHom (lawX ν) Bx.u
      (s7Part (lawX ν) Bx.u (fun c => s7EffDeg c = i ∧ s7NeDeg c = i') f) i' := by
    intro c hc
    rw [s7Part_coef (lawX ν) Bx.u hu] at hc
    by_cases hP : s7EffDeg c = i ∧ s7NeDeg c = i'
    · exact hP.2
    · exact absurd (by simp [hP]) hc
  refine ⟨⟨n - i', appB_t3_compEmbedHom_trivial (lawX ν) Bx.u _ hne⟩, hne, ?_⟩
  intro c hc
  rw [s7Part_coef (lawX ν) Bx.u hu] at hc
  by_cases hP : s7EffDeg c = i ∧ s7NeDeg c = i'
  · exact hP.1.ge
  · exact absurd (by simp [hP]) hc

/-- every trilinear expectation splits over the degree profiles (`s7Part_add_compl`, all degrees
`≤ n`): `E f g h = Σ_{i,i',j,k ≤ n} E f_{i,i'} g_j h_k`. -/
theorem appB_t3_degree_decomposition (ν : FinProb (X × Y × Z))
    (hDx : ∀ a, 0 < (lawX ν).prob a) (hDy : ∀ a, 0 < (lawY ν).prob a)
    (hDz : ∀ a, 0 < (lawZ ν).prob a) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm)
    (By : S7ModestBasis (lawY ν) (fun _ : Y => ()) (∅ : Finset Y))
    (Bz : S7ModestBasis (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z)) {n : ℕ}
    (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ) :
    corr3 ν f g h = ∑ i ∈ range (n + 1), ∑ i' ∈ range (n + 1), ∑ j ∈ range (n + 1),
      ∑ k ∈ range (n + 1),
        corr3 ν (s7Part (lawX ν) Bx.u (fun c => s7EffDeg c = i ∧ s7NeDeg c = i') f)
          (s7Part (lawY ν) By.u (fun c => s7NeDeg c = j) g)
          (s7Part (lawZ ν) Bz.u (fun c => s7NeDeg c = k) h) := by
  classical
  have hx := s7_modestBasis_isONB (lawX ν) (fun _ : X => ()) Sm hDx Bx
  have hy := s7_modestBasis_isONB (lawY ν) (fun _ : Y => ()) (∅ : Finset Y) hDy By
  have hz := s7_modestBasis_isONB (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z) hDz Bz
  have hfp := t3_part_sum (lawX ν) hDx Bx.u hx (range (n + 1) ×ˢ range (n + 1))
    (fun p c => s7EffDeg c = p.1 ∧ s7NeDeg c = p.2) t3_prof_ex t3_prof_uniq f
  have hgp := t3_part_sum (lawY ν) hDy By.u hy (range (n + 1)) (fun j c => s7NeDeg c = j)
    t3_deg_ex (fun c a b ha hb => ha.symm.trans hb) g
  have hhp := t3_part_sum (lawZ ν) hDz Bz.u hz (range (n + 1)) (fun j c => s7NeDeg c = j)
    t3_deg_ex (fun c a b ha hb => ha.symm.trans hb) h
  calc corr3 ν f g h = corr3 ν
        (∑ p ∈ range (n + 1) ×ˢ range (n + 1), s7Part (lawX ν) Bx.u
          (fun c => s7EffDeg c = p.1 ∧ s7NeDeg c = p.2) f)
        (∑ j ∈ range (n + 1), s7Part (lawY ν) By.u (fun c => s7NeDeg c = j) g)
        (∑ k ∈ range (n + 1), s7Part (lawZ ν) Bz.u (fun c => s7NeDeg c = k) h) := by
        rw [← hfp, ← hgp, ← hhp]
    _ = _ := by
      rw [t3_corr3_sum_left]
      simp only [t3_corr3_sum_mid]
      simp only [t3_corr3_sum_right]
      rw [Finset.sum_product]

/-- Parseval for the profile parts: `Σ_{i,i'} ‖f_{i,i'}‖₂² = ‖f‖₂²` (and likewise for `g`, `h`
by `j`, `k`; `s7Part_orthogonal`, `s7_parseval`). -/
theorem appB_t3_parseval (ν : FinProb (X × Y × Z)) (hDx : ∀ a, 0 < (lawX ν).prob a)
    (Sm : Finset X) (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm) {n : ℕ}
    (f : (Fin n → X) → ℂ) :
    ∑ i ∈ range (n + 1), ∑ i' ∈ range (n + 1),
      cl2norm (lawX ν) (s7Part (lawX ν) Bx.u (fun c => s7EffDeg c = i ∧ s7NeDeg c = i') f) ^ 2 =
      cl2norm (lawX ν) f ^ 2 := by
  classical
  have hx := s7_modestBasis_isONB (lawX ν) (fun _ : X => ()) Sm hDx Bx
  have h1 := t3_part_parseval (lawX ν) hDx Bx.u hx (range (n + 1) ×ˢ range (n + 1))
    (fun p c => s7EffDeg c = p.1 ∧ s7NeDeg c = p.2) t3_prof_ex t3_prof_uniq f
  rw [Finset.sum_product] at h1
  rw [t3_cl2norm_sq, ← h1]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  rw [t3_cl2norm_sq]

/-- `#sum-degree-profiles` (l. 9355-9372), abstract inequality: nonnegative weights with `ℓ²`
mass `≤ 1` on index sets of sizes `Na, Nb, Nc`, and a bound `w ≤ w₀` give
`Σ w a b c ≤ w₀ √(Na Nb Nc)` (Cauchy-Schwarz; at `H = {0}` the degree-vector sums of l. 9357-9366
are over a single vector). -/
theorem appB_t3_sum_profiles {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (a : α → ℝ) (b : β → ℝ) (c : γ → ℝ) (w : α → β → γ → ℝ) (w₀ : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (hc : ∀ k, 0 ≤ c k)
    (ha2 : ∑ i, a i ^ 2 ≤ 1) (hb2 : ∑ j, b j ^ 2 ≤ 1) (hc2 : ∑ k, c k ^ 2 ≤ 1)
    (hw : ∀ i j k, |w i j k| ≤ w₀) :
    ∑ i, ∑ j, ∑ k, |w i j k| * a i * b j * c k ≤
      w₀ * Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β * Fintype.card γ) := by
  have h := t3_sum_profiles_fin Finset.univ Finset.univ Finset.univ a b c w w₀ ha hb hc ha2 hb2 hc2 hw
  simpa [Finset.card_univ] using h

private theorem t3_unif {A : Type} [Fintype A] (D : FinProb A) (h : Unit) :
    ∑ a ∈ univ.filter (fun a => (fun _ : A => ()) a = h), D.prob a =
      1 / (Fintype.card Unit : ℝ) := by
  rw [Finset.filter_true_of_mem (fun a _ => Subsingleton.elim _ _)]
  simp [D.sum_eq_one]

open scoped Classical in
/-- the part of non-embedding degree exactly `j` is non-embedding homogeneous of degree `j`. -/
private theorem t3_part_neHom_deg {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (D : FinProb A)
    {Sm : Finset A} (B : S7ModestBasis D (fun _ : A => ()) Sm) (j : ℕ) (f : (Fin n → A) → ℂ) :
    S7NeHom D B.u (s7Part D B.u (fun c => s7NeDeg c = j) f) j :=
  s7Part_neHom D B.u (fun a b => by
    convert s7_modestBasis_orthonormal D (fun _ : A => ()) Sm B a b) j f

/-- the parts of non-embedding degree `j` lie in `G_n`. -/
private theorem t3_part_mem_G {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (D : FinProb A)
    {Sm : Finset A} (B : S7ModestBasis D (fun _ : A => ()) Sm) (j : ℕ) (f : (Fin n → A) → ℂ) :
    s7Part D B.u (fun c => s7NeDeg c = j) f ∈ s7ClassG (K₁ := Fin B.nN) (K₂ := Fin B.nM) D B.u n :=
  ⟨⟨n - j, appB_t3_compEmbedHom_trivial D B.u _ (t3_part_neHom_deg D B j f)⟩,
    ⟨j, t3_part_neHom_deg D B j f⟩⟩

open scoped Classical in
/-- the core estimate of `#sum-degree-profiles` at fixed `ν`: the degree-truncated trilinear form
is at most `9 d₃⁴ (1+c')^{-d₃^{1-√ξ_H}}`, using the hom hypothesis on each profile. -/
private theorem t3_core {m K : ℕ} {crb Crb α ξH c' : ℝ} (hξH : 0 < ξH) (hξH1 : ξH < 1)
    (hc' : 0 < c') (hα : 0 < α) (hhom : HomPAt m K crb Crb α ξH c') (d₁ d₂ d₃ d₄ : ℝ)
    (hd3 : 1 ≤ d₃) (hd4 : 1 ≤ d₄) (hd24 : d₂ ≤ d₄) (hd43 : d₄ ≤ d₃ ^ 2)
    (hexp : ∀ i i' : ℕ, d₃ ≤ (i : ℝ) → (i' : ℝ) ≤ d₄ → (i' : ℝ) ^ (1 - ξH) ≤ (i : ℝ))
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (hX : Fintype.card X ≤ m) (hY : Fintype.card Y ≤ m)
    (hZ : Fintype.card Z ≤ m) (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z)
    (hR : Rel67 K α ν Sg Sm Phi') (hRB : RelaxedBaseCase ν Sm crb Crb) {n : ℕ}
    (F : (Fin n → X) → ℂ) (G : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ)
    (hFn : cl2norm (lawX ν) F ≤ 1) (hGn : cl2norm (lawY ν) G ≤ 1)
    (hhn : cl2norm (lawZ ν) h ≤ 1)
    (Bx : S7ModestBasis (lawX ν) (fun _ : X => ()) Sm)
    (By : S7ModestBasis (lawY ν) (fun _ : Y => ()) (∅ : Finset Y))
    (Bz : S7ModestBasis (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z)) :
    ‖corr3 ν (s7Part (lawX ν) Bx.u (fun c => d₃ ≤ (s7EffDeg c : ℝ) ∧ (s7NeDeg c : ℝ) ≤ d₄) F)
      (s7Part (lawY ν) By.u (fun c => d₁ < (s7NeDeg c : ℝ) ∧ (s7NeDeg c : ℝ) < d₂) G) h‖ ≤
      9 * d₃ ^ 4 * (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) := by
  obtain ⟨hDx, hDy, hDz⟩ := t3_laws_pos hα hR
  have hx := s7_modestBasis_isONB (lawX ν) (fun _ : X => ()) Sm hDx Bx
  have hy := s7_modestBasis_isONB (lawY ν) (fun _ : Y => ()) (∅ : Finset Y) hDy By
  have hz := s7_modestBasis_isONB (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z) hDz Bz
  have hux := fun a b => s7_modestBasis_orthonormal (lawX ν) (fun _ : X => ()) Sm Bx a b
  have huy := fun a b => s7_modestBasis_orthonormal (lawY ν) (fun _ : Y => ()) (∅ : Finset Y) By a b
  have huz := fun a b => s7_modestBasis_orthonormal (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z) Bz a b
  set P3 : (Fin n → Bx.J) → Prop := fun c => d₃ ≤ (s7EffDeg c : ℝ) ∧ (s7NeDeg c : ℝ) ≤ d₄ with hP3
  set Q3 : (Fin n → By.J) → Prop := fun c => d₁ < (s7NeDeg c : ℝ) ∧ (s7NeDeg c : ℝ) < d₂ with hQ3
  set F₃ := s7Part (lawX ν) Bx.u P3 F with hF₃
  set G₃ := s7Part (lawY ν) By.u Q3 G with hG₃
  have hF₃n : cl2norm (lawX ν) F₃ ≤ 1 := (t3_part_norm_le _ hDx _ hx _ _).trans hFn
  have hG₃n : cl2norm (lawY ν) G₃ ≤ 1 := (t3_part_norm_le _ hDy _ hy _ _).trans hGn
  have hw0 : 0 < (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) := by positivity
  have hθ : 0 < 1 - Real.sqrt ξH := by
    have : Real.sqrt ξH < 1 := by
      rw [Real.sqrt_lt' one_pos]; linarith
    linarith
  -- the index sets
  set sa : Finset (ℕ × ℕ) := (range (n + 1) ×ˢ range (n + 1)).filter
    (fun p => p.1 ≤ p.2 ∧ d₃ ≤ (p.1 : ℝ) ∧ (p.2 : ℝ) ≤ d₄) with hsa
  set sb : Finset ℕ := (range (n + 1)).filter (fun j => d₁ < (j : ℝ) ∧ (j : ℝ) < d₂) with hsb
  set sc : Finset ℕ := (range (n + 1)).filter (fun k => (k : ℝ) ≤ d₄ + d₂) with hsc
  have hsa' : sa ⊆ range (n + 1) ×ˢ range (n + 1) := Finset.filter_subset _ _
  have hsb' : sb ⊆ range (n + 1) := Finset.filter_subset _ _
  have hsc' : sc ⊆ range (n + 1) := Finset.filter_subset _ _
  -- the profile norms
  let a : ℕ → ℕ → ℝ := fun i i' => cl2norm (lawX ν)
    (s7Part (lawX ν) Bx.u (fun c => s7EffDeg c = i ∧ s7NeDeg c = i') F₃)
  let b : ℕ → ℝ := fun j => cl2norm (lawY ν) (s7Part (lawY ν) By.u (fun c => s7NeDeg c = j) G₃)
  let c : ℕ → ℝ := fun k => cl2norm (lawZ ν) (s7Part (lawZ ν) Bz.u (fun c => s7NeDeg c = k) h)
  have ha2 : ∑ p ∈ sa, a p.1 p.2 ^ 2 ≤ 1 :=
    t3_part_mass_le (lawX ν) hDx Bx.u hx _ sa hsa' (fun p cc => s7EffDeg cc = p.1 ∧
      s7NeDeg cc = p.2) t3_prof_ex t3_prof_uniq F₃ hF₃n
  have hb2 : ∑ j ∈ sb, b j ^ 2 ≤ 1 :=
    t3_part_mass_le (lawY ν) hDy By.u hy _ sb hsb' (fun j cc => s7NeDeg cc = j) t3_deg_ex
      (fun cc p q hp hq => hp.symm.trans hq) G₃ hG₃n
  have hc2 : ∑ k ∈ sc, c k ^ 2 ≤ 1 :=
    t3_part_mass_le (lawZ ν) hDz Bz.u hz _ sc hsc' (fun j cc => s7NeDeg cc = j) t3_deg_ex
      (fun cc p q hp hq => hp.symm.trans hq) h hhn
  have hT0 : ∀ i ∈ range (n + 1), ∀ i' ∈ range (n + 1), ∀ j ∈ range (n + 1),
      ∀ k ∈ range (n + 1), ¬ ((i, i') ∈ sa ∧ j ∈ sb ∧ k ∈ sc) →
      ‖corr3 ν (s7Part (lawX ν) Bx.u (fun cc => s7EffDeg cc = i ∧ s7NeDeg cc = i') F₃)
        (s7Part (lawY ν) By.u (fun cc => s7NeDeg cc = j) G₃)
        (s7Part (lawZ ν) Bz.u (fun cc => s7NeDeg cc = k) h)‖ = 0 := by
    intro i hi i' hi' j hj k hk hnot
    by_cases hA : (i, i') ∈ sa
    · by_cases hB : j ∈ sb
      · have hC : k ∉ sc := fun hC => hnot ⟨hA, hB, hC⟩
        have hkgt : d₄ + d₂ < (k : ℝ) := by
          by_contra hcon
          exact hC (Finset.mem_filter.2 ⟨hk, not_lt.1 hcon⟩)
        have hA' := (Finset.mem_filter.1 hA).2
        have hB' := (Finset.mem_filter.1 hB).2
        have hlt : i' + j < k := by
          have : ((i' + j : ℕ) : ℝ) < k := by
            push_cast
            linarith [hA'.2.2, hB'.2]
          exact_mod_cast this
        rw [appB_t3_h_degree_bound ν hDx hDy hDz Sm Bx By Bz _ _ _
          (appB_t3_parts_mem ν Sm Bx i i' F₃).2.1 (t3_part_neHom_deg (lawY ν) By j G₃)
          (t3_part_neHom_deg (lawZ ν) Bz k h) hlt, norm_zero]
      · have h0 : s7Part (lawY ν) By.u (fun cc => s7NeDeg cc = j) G₃ = 0 := by
          rw [hG₃, t3_part_part (lawY ν) By.u huy]
          refine t3_part_zero _ _ _ (fun cc hcc => hB ?_) _
          obtain ⟨h1, h2, h3⟩ := hcc
          exact Finset.mem_filter.2 ⟨hj, by rw [← h1]; exact h2, by rw [← h1]; exact h3⟩
        rw [h0, t3_corr3_zero_mid, norm_zero]
    · have h0 : s7Part (lawX ν) Bx.u (fun cc => s7EffDeg cc = i ∧ s7NeDeg cc = i') F₃ = 0 := by
        rw [hF₃, t3_part_part (lawX ν) Bx.u hux]
        refine t3_part_zero _ _ _ (fun cc hcc => hA ?_) _
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcc
        have h5 := s7_effDeg_le_neDeg (H := Unit) cc
        refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi, hi'⟩, by omega, ?_, ?_⟩
        · rw [← h1]; exact h3
        · rw [← h2]; exact h4
      rw [h0, t3_corr3_zero_left, norm_zero]
  have hT : ∀ i i' j k, (i, i') ∈ sa → j ∈ sb → k ∈ sc →
      ‖corr3 ν (s7Part (lawX ν) Bx.u (fun cc => s7EffDeg cc = i ∧ s7NeDeg cc = i') F₃)
        (s7Part (lawY ν) By.u (fun cc => s7NeDeg cc = j) G₃)
        (s7Part (lawZ ν) Bz.u (fun cc => s7NeDeg cc = k) h)‖ ≤
        (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) * a i i' * b j * c k := by
    intro i i' j k hA hB hC
    obtain ⟨hAr, hA1, hA2, hA3⟩ := Finset.mem_filter.1 hA
    have hi' : i' ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_product.1 hAr).2)
    have hmemF := appB_t3_parts_mem ν Sm Bx i i' F₃
    have hmemG := t3_part_mem_G (lawY ν) By j G₃
    have hmemH := t3_part_mem_G (lawZ ν) Bz k h
    have hbeta := hhom X Y Z hX hY hZ ν Sg Sm Phi' hR hRB Bx By Bz n i' i hi' hA1
      (hexp i i' hA2 hA3)
    have hb0 : 0 ≤ (1 + c') ^ (-((i : ℝ) ^ (1 - Real.sqrt ξH))) := by positivity
    have key := (s7BetaP_le_iff ν Bx.u By.u Bz.u n i' i hb0).1 hbeta _ _ _ hmemF hmemG hmemH
    have hb0w : (1 + c') ^ (-((i : ℝ) ^ (1 - Real.sqrt ξH))) ≤
        (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith)
        (neg_le_neg (Real.rpow_le_rpow (by linarith) hA2 hθ.le))
    have ha0 : 0 ≤ a i i' := Real.sqrt_nonneg _
    have hb0' : 0 ≤ b j := Real.sqrt_nonneg _
    have hc0 : 0 ≤ c k := Real.sqrt_nonneg _
    have hrhs : 0 ≤ (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) * a i i' * b j * c k :=
      mul_nonneg (mul_nonneg (mul_nonneg hw0.le ha0) hb0') hc0
    by_cases n1 : cl2norm (lawX ν) (s7Part (lawX ν) Bx.u
        (fun cc => s7EffDeg cc = i ∧ s7NeDeg cc = i') F₃) = 0
    · rw [t3_eq_zero_of_norm _ hDx _ n1, t3_corr3_zero_left, norm_zero]
      exact hrhs
    by_cases n2 : cl2norm (lawY ν) (s7Part (lawY ν) By.u (fun cc => s7NeDeg cc = j) G₃) = 0
    · rw [t3_eq_zero_of_norm _ hDy _ n2, t3_corr3_zero_mid, norm_zero]
      exact hrhs
    by_cases n3 : cl2norm (lawZ ν) (s7Part (lawZ ν) Bz.u (fun cc => s7NeDeg cc = k) h) = 0
    · rw [t3_eq_zero_of_norm _ hDz _ n3, t3_corr3_zero_right, norm_zero]
      exact hrhs
    refine (key n1 n2 n3).trans ?_
    calc _ ≤ (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) * (a i i' * b j * c k) :=
          mul_le_mul_of_nonneg_right hb0w (mul_nonneg (mul_nonneg ha0 hb0') hc0)
      _ = _ := by ring
  have hd4' : 0 ≤ d₄ := by linarith
  obtain ⟨N, hNr, hsaN, hsbN, hscN⟩ : ∃ N : ℕ, (N : ℝ) ≤ 2 * d₄ ∧
      sa ⊆ range (N + 1) ×ˢ range (N + 1) ∧ sb ⊆ range (N + 1) ∧ sc ⊆ range (N + 1) := by
    refine ⟨⌊2 * d₄⌋₊, Nat.floor_le (by linarith), ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.1 hp
      have h4 := Nat.le_floor (show (p.2 : ℝ) ≤ 2 * d₄ by linarith)
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    · intro j hj
      obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hj
      have h4 := Nat.le_floor (show (j : ℝ) ≤ 2 * d₄ by linarith)
      simp only [Finset.mem_range]
      omega
    · intro k hk
      obtain ⟨_, h1⟩ := Finset.mem_filter.1 hk
      have h4 := Nat.le_floor (show (k : ℝ) ≤ 2 * d₄ by linarith)
      simp only [Finset.mem_range]
      omega
  have hcard : (sa.card : ℝ) * sb.card * sc.card ≤ (((N : ℝ) + 1) ^ 2) ^ 2 := by
    have h1 : sa.card ≤ (N + 1) * (N + 1) := by
      simpa using Finset.card_le_card hsaN
    have h2 : sb.card ≤ N + 1 := by simpa using Finset.card_le_card hsbN
    have h3 : sc.card ≤ N + 1 := by simpa using Finset.card_le_card hscN
    have h4 : sa.card * sb.card * sc.card ≤ (N + 1) * (N + 1) * (N + 1) * (N + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have h5 : ((sa.card * sb.card * sc.card : ℕ) : ℝ) ≤
        (((N + 1) * (N + 1) * (N + 1) * (N + 1) : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5
    nlinarith [h5]
  have hN1 : ((N : ℝ) + 1) ^ 2 ≤ 9 * d₃ ^ 4 := by
    have h1 : (N : ℝ) + 1 ≤ 3 * d₄ := by linarith
    have h2 : ((N : ℝ) + 1) ^ 2 ≤ (3 * d₄) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : d₄ ^ 2 ≤ (d₃ ^ 2) ^ 2 := pow_le_pow_left₀ hd4' hd43 2
    nlinarith [h2, h3]
  have hsq : Real.sqrt ((sa.card : ℝ) * sb.card * sc.card) ≤ 9 * d₃ ^ 4 := by
    calc _ ≤ Real.sqrt ((((N : ℝ) + 1) ^ 2) ^ 2) := Real.sqrt_le_sqrt hcard
      _ = ((N : ℝ) + 1) ^ 2 := Real.sqrt_sq (by positivity)
      _ ≤ _ := hN1
  rw [appB_t3_degree_decomposition ν hDx hDy hDz Sm Bx By Bz F₃ G₃ h]
  calc _ ≤ ∑ i ∈ range (n + 1), ∑ i' ∈ range (n + 1), ∑ j ∈ range (n + 1),
        ∑ k ∈ range (n + 1), ‖corr3 ν
          (s7Part (lawX ν) Bx.u (fun cc => s7EffDeg cc = i ∧ s7NeDeg cc = i') F₃)
          (s7Part (lawY ν) By.u (fun cc => s7NeDeg cc = j) G₃)
          (s7Part (lawZ ν) Bz.u (fun cc => s7NeDeg cc = k) h)‖ := t3_norm_sum4 _ _ _ _ _
    _ ≤ (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) *
        Real.sqrt ((sa.card : ℝ) * sb.card * sc.card) :=
        t3_four_sum n (fun i i' j k => ‖corr3 ν
          (s7Part (lawX ν) Bx.u (fun cc => s7EffDeg cc = i ∧ s7NeDeg cc = i') F₃)
          (s7Part (lawY ν) By.u (fun cc => s7NeDeg cc = j) G₃)
          (s7Part (lawZ ν) Bz.u (fun cc => s7NeDeg cc = k) h)‖) a b c _ sa sb sc hsa' hsb'
          hsc' hT0 hT (fun _ _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
          (fun _ => Real.sqrt_nonneg _) ha2 hb2 hc2 hw0.le
    _ ≤ (1 + c') ^ (-(d₃ ^ (1 - Real.sqrt ξH))) * (9 * d₃ ^ 4) :=
        mul_le_mul_of_nonneg_left hsq hw0.le
    _ = _ := by ring

/-- Claim `soft_trunc3` (l. 9214-9217) in the PROVED form (`|(VI)| ≤ 4ρ^ξ +
M‴(1+c′/2)^{-d₃^{1-√ξ_H}}`, `d₃ = ρ^{-(1-2ξ)}`, with decay constant `c'/2`). The homogeneous constants `(ξ_H, c')`
and the premise `HomPAt` (an instance of `hhom'`) come first; `(M, ξ₀)` depend on them, `δ₀` also on
`ξ` (harmless because `ξ` is fixed first). -/
theorem appB_soft_trunc3_of_homPAt (m K : ℕ) (crb Crb : ℝ) (hcrb : 0 < crb) (hCrb : 0 < Crb)
    {α : ℝ} (hα : 0 < α) {ξH c' : ℝ} (hξH : 0 < ξH) (hξH1 : ξH < 1) (hc' : 0 < c')
    (hhom : HomPAt m K crb Crb α ξH c') :
    ∃ M ξ₀ : ℝ, 1 ≤ M ∧ 0 < ξ₀ ∧ ξ₀ ≤ 1 / 100 ∧
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' → RelaxedBaseCase ν Sm crb Crb →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          termVI ν Sm ρ ξ f g h ≤
            4 * ρ ^ ξ + M * (1 + c' / 2) ^ (-((ρ ^ (-(1 - 2 * ξ))) ^ (1 - Real.sqrt ξH))) := by
  have hθ : 0 < 1 - Real.sqrt ξH := by
    have : Real.sqrt ξH < 1 := by
      rw [Real.sqrt_lt' one_pos]; linarith
    linarith
  obtain ⟨M₀, hM₀, hM₀b⟩ := t3_absorb hc' (p := 4 / (1 - Real.sqrt ξH)) (by positivity)
  refine ⟨9 * M₀, min (ξH / 4) (1 / 100), by linarith, lt_min (by linarith) (by norm_num),
    min_le_right _ _, ?_⟩
  intro ξ hξ hξ0
  have hξ4 : 4 * ξ ≤ ξH := by linarith [min_le_left (ξH / 4) (1 / 100)]
  have hξ100 : ξ ≤ 1 / 100 := hξ0.trans (min_le_right _ _)
  obtain ⟨δf, hδf, hfp⟩ := appB_t3_f_parts hξ (by linarith : ξ < 1 / 2)
  obtain ⟨δg, hδg, hgp⟩ := appB_t3_g_parts hξ (by linarith : ξ < 1)
  refine ⟨min 1 (min δf δg), lt_min one_pos (lt_min hδf hδg), min_le_left _ _, ?_⟩
  intro ρ hρ hρδ X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR hRB n f g h hf hg hh
  have hρ1 : ρ ≤ 1 := hρδ.trans (min_le_left _ _)
  have hρf : ρ ≤ δf := hρδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρg : ρ ≤ δg := hρδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hDx, hDy, hDz⟩ := t3_laws_pos hα hR
  obtain ⟨Bx⟩ := s7_exists_modestBasis (lawX ν) (fun _ : X => ()) Sm hDx (t3_unif _)
  obtain ⟨By⟩ := s7_exists_modestBasis (lawY ν) (fun _ : Y => ()) (∅ : Finset Y) hDy (t3_unif _)
  obtain ⟨Bz⟩ := s7_exists_modestBasis (lawZ ν) (fun _ : Z => ()) (∅ : Finset Z) hDz (t3_unif _)
  have hfn := t3_cl2norm_le_one (lawX ν) f hf
  have hgn := t3_cl2norm_le_one (lawY ν) g hg
  have hhn := t3_cl2norm_le_one (lawZ ν) h hh
  obtain ⟨hF1, hF2⟩ := hfp ρ hρ hρf X (lawX ν) hDx (fun _ => ()) Sm Bx n f hfn
  have hG2 := hgp ρ hρ hρg Y (lawY ν) hDy By n g hgn
  have hGn : cl2norm (lawY ν) (appTp (lawY ν) ρ g) ≤ 1 :=
    (t3_appTp_norm_le _ hDy By hρ hρ1 g).trans hgn
  -- real facts about the degree thresholds
  have hpξ : 0 < ρ ^ ξ := Real.rpow_pos_of_pos hρ ξ
  have hd3 : 1 ≤ ρ ^ (-(1 - 2 * ξ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by linarith)
  have hd4 : 1 ≤ ρ ^ (-(1 + 2 * ξ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by linarith)
  have hd24 : ρ ^ (-(1 + ξ)) ≤ ρ ^ (-(1 + 2 * ξ)) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have hd43 : ρ ^ (-(1 + 2 * ξ)) ≤ (ρ ^ (-(1 - 2 * ξ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by push_cast; linarith)
  have hexp : ∀ i i' : ℕ, ρ ^ (-(1 - 2 * ξ)) ≤ (i : ℝ) → (i' : ℝ) ≤ ρ ^ (-(1 + 2 * ξ)) →
      (i' : ℝ) ^ (1 - ξH) ≤ (i : ℝ) := by
    intro i i' hi hi'
    have h1 : (i' : ℝ) ^ (1 - ξH) ≤ (ρ ^ (-(1 + 2 * ξ))) ^ (1 - ξH) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hi' (by linarith)
    rw [← Real.rpow_mul hρ.le] at h1
    have h2 : ρ ^ (-(1 + 2 * ξ) * (1 - ξH)) ≤ ρ ^ (-(1 - 2 * ξ)) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by nlinarith)
    linarith
  have hcore := t3_core hξH hξH1 hc' hα hhom (ρ ^ (-(1 - ξ))) (ρ ^ (-(1 + ξ)))
    (ρ ^ (-(1 - 2 * ξ))) (ρ ^ (-(1 + 2 * ξ))) hd3 hd4 hd24 hd43 hexp hX hY hZ ν Sg Sm Phi' hR hRB
    (tNE (lawX ν) (ρ ^ (1 + ξ)) f - s7EffNoiseOp (lawX ν) Sm (ρ ^ (1 - ξ))
      (tNE (lawX ν) (ρ ^ (1 + ξ)) f)) (appTp (lawY ν) ρ g) h hF1 hGn hhn Bx By Bz
  have hcs := appB_t3_cs_split ν (tNE (lawX ν) (ρ ^ (1 + ξ)) f - s7EffNoiseOp (lawX ν) Sm
    (ρ ^ (1 - ξ)) (tNE (lawX ν) (ρ ^ (1 + ξ)) f))
    (s7Part (lawX ν) Bx.u (fun c => ρ ^ (-(1 - 2 * ξ)) ≤ (s7EffDeg c : ℝ) ∧
      (s7NeDeg c : ℝ) ≤ ρ ^ (-(1 + 2 * ξ)))
      (tNE (lawX ν) (ρ ^ (1 + ξ)) f - s7EffNoiseOp (lawX ν) Sm (ρ ^ (1 - ξ))
        (tNE (lawX ν) (ρ ^ (1 + ξ)) f)))
    (appTp (lawY ν) ρ g)
    (s7Part (lawY ν) By.u (fun c => ρ ^ (-(1 - ξ)) < (s7NeDeg c : ℝ) ∧
      (s7NeDeg c : ℝ) < ρ ^ (-(1 + ξ))) (appTp (lawY ν) ρ g)) h hh
  have hF₃n := (t3_part_norm_le (lawX ν) hDx Bx.u (s7_modestBasis_isONB (lawX ν)
    (fun _ : X => ()) Sm hDx Bx) (fun c => ρ ^ (-(1 - 2 * ξ)) ≤ (s7EffDeg c : ℝ) ∧
      (s7NeDeg c : ℝ) ≤ ρ ^ (-(1 + 2 * ξ)))
      (tNE (lawX ν) (ρ ^ (1 + ξ)) f - s7EffNoiseOp (lawX ν) Sm (ρ ^ (1 - ξ))
        (tNE (lawX ν) (ρ ^ (1 + ξ)) f))).trans hF1
  -- absorb the polynomial factor
  have hE0 : 0 ≤ (ρ ^ (-(1 - 2 * ξ))) ^ (1 - Real.sqrt ξH) := by positivity
  have habs := hM₀b _ hE0
  have hpow : ((ρ ^ (-(1 - 2 * ξ))) ^ (1 - Real.sqrt ξH)) ^ (4 / (1 - Real.sqrt ξH)) =
      (ρ ^ (-(1 - 2 * ξ))) ^ 4 := by
    rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ hθ.ne']
    exact_mod_cast Real.rpow_natCast _ 4
  rw [hpow] at habs
  have hfin : 9 * (ρ ^ (-(1 - 2 * ξ))) ^ 4 * (1 + c') ^ (-((ρ ^ (-(1 - 2 * ξ))) ^
      (1 - Real.sqrt ξH))) ≤ 9 * M₀ * (1 + c' / 2) ^ (-((ρ ^ (-(1 - 2 * ξ))) ^
      (1 - Real.sqrt ξH))) := by nlinarith [habs]
  unfold termVI
  have h1 := mul_le_mul hF2 hGn (Real.sqrt_nonneg _) (by positivity)
  have h2 := mul_le_mul hF₃n hG2 (Real.sqrt_nonneg _) zero_le_one
  linarith

end Trunc3

end TrackB
end RestrictedPolynomials
end
