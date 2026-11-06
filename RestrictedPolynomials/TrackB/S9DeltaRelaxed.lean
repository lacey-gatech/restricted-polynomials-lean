module

public import RestrictedPolynomials.TrackB.S9DeltaSetup
public import RestrictedPolynomials.TrackB.S9DeltaNumeric
public import RestrictedPolynomials.TrackB.S9DeltaHierarchy
public import RestrictedPolynomials.TrackB.MaxTSec6Relaxed65
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Track B: Lemma 9.14 (`v-not-perp`) and the use of the relaxed base case

Source: paper IV (arXiv:2307.16248v2 `writeup_stability.tex`), Section 9.3.6 (l. 5677-5934).
The rank-one parts `F'_{r,s}` of eq. `delta_7`, Claim 9.19 (`use-relaxed-base`), the modest-influence
contradiction and Lemma 9.14. This is the only place where the relaxed base case
`RelaxedBaseCase μ Sm c C` (Def. 6.6, clause 2; normalised) is used. The constants are
`(c, C)` of the relaxed base case; `ϑ = ζ^{1/4}` and `υ = (ϑ/c)^{1/C}`.
-/

@[expose] public section

open Finset
open scoped ENNReal

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S9dRelaxed
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {K₁ K₂ : Type}
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ} {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ}
  {h : (Fin n → Z) → ℂ} {d' : ℕ}

/-- `F'_{r,s} = ∑_{t∈T'} conj(F̂'_t(r,s)) F'_t / (∑_{t∈T'} |F̂'_t(r,s)|²)^{1/2}` (l. 5866; the printed
normaliser lacks the square root). -/
def S9dSvd.rankOne (D : S9dSvd j μ hμ ux F g h d') (T' : Finset (Fin D.sF)) (r : Fin D.sG)
    (s : Fin D.sH) : Y × Z → ℂ :=
  fun v => (((Real.sqrt (∑ t ∈ T', ‖D.FhatJ t r s‖ ^ 2) : ℝ) : ℂ))⁻¹ *
    ∑ t ∈ T', starRingEnd ℂ (D.FhatJ t r s) * D.FJ t v

end S9dRelaxed

section S9dRelaxedHelpers

/-! ### Private helpers: `L²` calculus for `FinProb`, the `W`-isometry, the seminorm `√var` -/

private lemma s9dR_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; ring

private lemma s9dR_mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]; exact s9dR_star_mul_self z

private lemma s9dR_fun_sum_eq {β κ : Type*} (I : Finset κ) (w : κ → ℂ) (m : κ → β → ℂ) :
    (fun x => ∑ c ∈ I, w c * m c x) = ∑ c ∈ I, w c • m c := by
  funext x; simp [Finset.sum_apply]

/-- `⟨∑ a_c m_c, ∑ b_c m_c⟩ = ∑ a_c conj(b_c)` for an orthonormal family `m` (indexed by `I`). -/
private lemma s9dR_cinner_orth_sum {β κ : Type*} [Fintype β] [DecidableEq κ] (π : FinProb β)
    (I : Finset κ) (m : κ → β → ℂ)
    (hm : ∀ c ∈ I, ∀ c' ∈ I, π.cinner (m c) (m c') = if c = c' then 1 else 0) (a b : κ → ℂ) :
    π.cinner (fun x => ∑ c ∈ I, a c * m c x) (fun x => ∑ c ∈ I, b c * m c x) =
      ∑ c ∈ I, a c * star (b c) := by
  rw [s9dR_fun_sum_eq, s9dR_fun_sum_eq, cinner_sum_left]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [cinner_smul_right, hm c hc c hc]; simp
  · intro c' hc' hne; rw [cinner_smul_right, hm c hc c' hc']; simp [Ne.symm hne]
  · intro h; exact absurd hc h

/-- the residual of the orthogonal projection: `‖f - ∑ ⟨f,e_i⟩ e_i‖² = ‖f‖² - ∑ |⟨f,e_i⟩|²`. -/
private lemma s9dR_resid {β κ : Type*} [Fintype β] [DecidableEq κ] (π : FinProb β)
    (I : Finset κ) (e : κ → β → ℂ)
    (he : ∀ i ∈ I, ∀ i' ∈ I, π.cinner (e i) (e i') = if i = i' then 1 else 0) (f : β → ℂ) :
    π.expect (fun x => ‖f x - ∑ i ∈ I, π.cinner f (e i) * e i x‖ ^ 2) =
      (π.cinner f f).re - ∑ i ∈ I, ‖π.cinner f (e i)‖ ^ 2 := by
  set c : κ → ℂ := fun i => π.cinner f (e i) with hc
  set S : β → ℂ := fun x => ∑ i ∈ I, c i * e i x with hS
  have hSS : π.cinner S S = ((∑ i ∈ I, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hS, s9dR_cinner_orth_sum π I e he c c, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => s9dR_mul_star_self (c i)
  have hfS : π.cinner f S = ((∑ i ∈ I, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hS, s9dR_fun_sum_eq, cinner_sum_right, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cinner_smul_right, ← s9dR_star_mul_self]
  have hSf : π.cinner S f = ((∑ i ∈ I, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [cinner_comm, hfS]; simp
  have hfun : (fun x => f x - S x) = f + (-1 : ℂ) • S := by
    funext x; simp [sub_eq_add_neg]
  have hg : π.cinner (f + (-1 : ℂ) • S) (f + (-1 : ℂ) • S) =
      π.cinner f f - ((∑ i ∈ I, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [cinner_add_left, cinner_add_right, cinner_add_right, cinner_smul_left, cinner_smul_left,
      cinner_smul_right, cinner_smul_right, hSS, hfS, hSf]
    simp only [star_neg, star_one]
    ring
  have h1 := cinner_self_eq π (fun x => f x - S x)
  rw [hfun, hg] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at h2
  simpa [hfun] using h2.symm

/-- the expectation under a pushforward law, real form. -/
private lemma s9dR_expect_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (φ : β → ℝ) :
    (mergePush π f).expect φ = π.expect (fun a => φ (f a)) := by
  unfold FinProb.expect mergePush
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun a => π.prob a * φ (f a))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

/-- the expectation under a pushforward law, complex form. -/
private lemma s9dR_cexpect_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (φ : β → ℂ) :
    (mergePush π f).cexpect φ = π.cexpect (fun a => φ (f a)) := by
  unfold FinProb.cexpect mergePush
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun a => (π.prob a : ℂ) * φ (f a))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the one-site `W`-isometry: `𝔼_{μ_{y,z}} φ(x(y,z)) = 𝔼_{μ_x} φ`. -/
private lemma s9dR_expect_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (φ : X → ℝ) :
    (s7LawYZ μ).expect (fun v => φ (s7Pre hμ v.1 v.2)) = (lawX μ).expect φ := by
  unfold s7LawYZ lawX
  rw [s9dR_expect_push, s9dR_expect_push]
  unfold FinProb.expect
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h0 : μ.prob p = 0
  · simp [h0]
  · have hp : (p.1, p.2.1, p.2.2) ∈ μ.support := h0
    have := s7Pre_unique hμ hp
    simp only [← this]

/-- on the support, `(W f)(y,z) = f(x)`: the one-site correlation of `W f` is that of `f`. -/
private lemma s9dR_corr_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (f : X → ℂ)
    (g : Y → ℂ) (h : Z → ℂ) :
    ∑ p : X × Y × Z, (μ.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2) =
      s8Corr1 μ (s8W1 hμ f) g h := by
  unfold s8Corr1 FinProb.cexpect
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h0 : μ.prob p = 0
  · simp [h0]
  · have hp : (p.1, p.2.1, p.2.2) ∈ μ.support := h0
    have := s7Pre_unique hμ hp
    simp only [s8W1, ← this]

/-- the weighted vector of `f` in `ℓ²(β)`: `‖·‖` is the `L²(π)` norm. -/
private def s9dR_evec {β : Type} [Fintype β] (π : FinProb β) (f : β → ℂ) : EuclideanSpace ℂ β :=
  WithLp.toLp 2 fun x => ((Real.sqrt (π.prob x) : ℝ) : ℂ) * f x

/-- the `L²(π)` norm. -/
private def s9dR_nrm {β : Type} [Fintype β] (π : FinProb β) (f : β → ℂ) : ℝ := ‖s9dR_evec π f‖

private lemma s9dR_nrm_nonneg {β : Type} [Fintype β] (π : FinProb β) (f : β → ℂ) :
    0 ≤ s9dR_nrm π f := norm_nonneg _

private lemma s9dR_nrm_sq {β : Type} [Fintype β] (π : FinProb β) (f : β → ℂ) :
    s9dR_nrm π f ^ 2 = π.expect (fun a => ‖f a‖ ^ 2) := by
  unfold s9dR_nrm s9dR_evec
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (π.nonneg a)]

/-- Minkowski for `L²(π)`: `‖g + ∑ c_i h_i‖ ≤ ‖g‖ + ∑ |c_i| ‖h_i‖`. -/
private lemma s9dR_nrm_comb {β κ : Type} [Fintype β] (π : FinProb β) (I : Finset κ) (f g : β → ℂ)
    (c : κ → ℂ) (h : κ → β → ℂ) (hf : ∀ x, f x = g x + ∑ i ∈ I, c i * h i x) :
    s9dR_nrm π f ≤ s9dR_nrm π g + ∑ i ∈ I, ‖c i‖ * s9dR_nrm π (h i) := by
  have hv : s9dR_evec π f = s9dR_evec π g + ∑ i ∈ I, c i • s9dR_evec π (h i) := by
    ext x
    simp only [s9dR_evec, hf, PiLp.add_apply, WithLp.ofLp_toLp, WithLp.ofLp_sum,
      WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold s9dR_nrm
  rw [hv]
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_smul]
  exact le_rfl

variable {X : Type} [Fintype X]

/-- the vector `(f a - f b)_{(a,b) ∈ Σ_modest²}`; its squared norm is `|Σ_modest|² var_{Σ_modest}(f)`. -/
private def s9dR_sv (Sm : Finset X) (f : X → ℂ) : EuclideanSpace ℂ (↥Sm × ↥Sm) :=
  WithLp.toLp 2 fun q => f q.1 - f q.2

omit [Fintype X] in
private lemma s9dR_sv_norm_sq (Sm : Finset X) (f : X → ℂ) :
    ‖s9dR_sv Sm f‖ ^ 2 = ∑ a ∈ Sm, ∑ b ∈ Sm, ‖f a - f b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [s9dR_sv]
  rw [← Finset.sum_coe_sort Sm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_coe_sort Sm]

omit [Fintype X] in
private lemma s9dR_sqrt_var (Sm : Finset X) (hSm : Sm.Nonempty) (f : X → ℂ) :
    Real.sqrt (s7ModestVar Sm hSm f) = ‖s9dR_sv Sm f‖ / (Sm.card : ℝ) := by
  have hk : (0 : ℝ) < Sm.card := by exact_mod_cast hSm.card_pos
  unfold s7ModestVar
  rw [← s9dR_sv_norm_sq, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq hk.le]

omit [Fintype X] in
private lemma s9dR_var_nonneg (Sm : Finset X) (hSm : Sm.Nonempty) (f : X → ℂ) :
    0 ≤ s7ModestVar Sm hSm f := by
  unfold s7ModestVar
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (sq_nonneg _)

omit [Fintype X] in
/-- the seminorm `√var_{Σ_modest}` satisfies Minkowski. -/
private lemma s9dR_sqrt_var_comb {κ : Type} (Sm : Finset X) (hSm : Sm.Nonempty) (I : Finset κ)
    (f g : X → ℂ) (c : κ → ℂ) (h : κ → X → ℂ)
    (hf : ∀ x, f x = g x + ∑ i ∈ I, c i * h i x) :
    Real.sqrt (s7ModestVar Sm hSm f) ≤
      Real.sqrt (s7ModestVar Sm hSm g) +
        ∑ i ∈ I, ‖c i‖ * Real.sqrt (s7ModestVar Sm hSm (h i)) := by
  have hk : (0 : ℝ) < Sm.card := by exact_mod_cast hSm.card_pos
  have hv : s9dR_sv Sm f = s9dR_sv Sm g + ∑ i ∈ I, c i • s9dR_sv Sm (h i) := by
    ext q
    simp only [s9dR_sv, hf, PiLp.add_apply, WithLp.ofLp_toLp, WithLp.ofLp_sum,
      WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hb : ‖s9dR_sv Sm f‖ ≤ ‖s9dR_sv Sm g‖ + ∑ i ∈ I, ‖c i‖ * ‖s9dR_sv Sm (h i)‖ := by
    rw [hv]
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_smul]
    exact le_rfl
  simp only [s9dR_sqrt_var]
  have hsum : ∑ i ∈ I, ‖c i‖ * (‖s9dR_sv Sm (h i)‖ / (Sm.card : ℝ)) =
      (∑ i ∈ I, ‖c i‖ * ‖s9dR_sv Sm (h i)‖) / (Sm.card : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, ← add_div]
  exact div_le_div_of_nonneg_right hb hk.le

/-- `var_{Σ_modest}(f) ≤ (2/α) ‖f‖²_{L²(μ_x)}` when every `x` has mass `≥ α` and `|Σ_modest| ≥ 2`. -/
private lemma s9dR_var_le (π : FinProb X) (Sm : Finset X) (hSm : Sm.Nonempty)
    (h2 : 2 ≤ Sm.card) {α : ℝ} (hα : 0 < α) (hat : ∀ x, α ≤ π.prob x) (f : X → ℂ) :
    s7ModestVar Sm hSm f ≤ 2 / α * π.expect (fun x => ‖f x‖ ^ 2) := by
  have hk2 : (2 : ℝ) ≤ Sm.card := by exact_mod_cast h2
  have hk : (0 : ℝ) < Sm.card := by linarith
  set A : X → ℝ := fun a => ‖f a‖ ^ 2 with hA
  have hA0 : ∀ a, 0 ≤ A a := fun a => sq_nonneg _
  have hpt : ∀ a b, ‖f a - f b‖ ^ 2 ≤ 2 * A a + 2 * A b := by
    intro a b
    have h1 := norm_sub_le (f a) (f b)
    have h2 := norm_nonneg (f a)
    have h3 := norm_nonneg (f b)
    simp only [hA]
    nlinarith [sq_nonneg (‖f a‖ - ‖f b‖), norm_nonneg (f a - f b)]
  have S1 : ∑ a ∈ Sm, ∑ b ∈ Sm, ‖f a - f b‖ ^ 2 ≤ 4 * Sm.card * ∑ a ∈ Sm, A a := by
    calc ∑ a ∈ Sm, ∑ b ∈ Sm, ‖f a - f b‖ ^ 2 ≤ ∑ a ∈ Sm, ∑ b ∈ Sm, (2 * A a + 2 * A b) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = 4 * Sm.card * ∑ a ∈ Sm, A a := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have S2 : α * ∑ a ∈ Sm, A a ≤ π.expect (fun x => ‖f x‖ ^ 2) := by
    rw [Finset.mul_sum]
    calc ∑ a ∈ Sm, α * A a ≤ ∑ a ∈ Sm, π.prob a * A a :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hat a) (hA0 a)
      _ ≤ ∑ a, π.prob a * A a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ =>
            mul_nonneg (π.nonneg a) (hA0 a)
      _ = π.expect (fun x => ‖f x‖ ^ 2) := rfl
  unfold s7ModestVar
  rw [div_le_iff₀ (by positivity)]
  have hE0 : 0 ≤ ∑ a ∈ Sm, A a := Finset.sum_nonneg fun a _ => hA0 a
  have key : 4 * (Sm.card : ℝ) * ∑ a ∈ Sm, A a ≤ 2 / α * π.expect (fun x => ‖f x‖ ^ 2) *
      (Sm.card : ℝ) ^ 2 := by
    have h3 : 2 / α * π.expect (fun x => ‖f x‖ ^ 2) ≥ 2 * ∑ a ∈ Sm, A a := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hα]
      nlinarith
    nlinarith [mul_nonneg hE0 (by linarith : (0 : ℝ) ≤ Sm.card - 2)]
  exact S1.trans key

end S9dRelaxedHelpers

section S9dRelaxedHelpersD
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {K₁ K₂ : Type}
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ} {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ}
  {h : (Fin n → Z) → ℂ} {d' : ℕ}

/-- the functions `conj(g'_r h'_s)` on `Y × Z`. -/
private def s9dR_E (D : S9dSvd j μ hμ ux F g h d') (q : Fin D.sG × Fin D.sH) : Y × Z → ℂ :=
  fun v => star (D.gJ q.1 v.1 * D.hJ q.2 v.2)

omit [DecidableEq X] [Fintype H] [DecidableEq H] in
/-- `{conj(g'_r h'_s)}` is orthonormal in `L²(μ_{y,z})` (uses `μ_{y,z} = μ_y ⊗ μ_z`). -/
private lemma s9dR_E_orth (D : S9dSvd j μ hμ ux F g h d')
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (q q' : Fin D.sG × Fin D.sH) :
    (s7LawYZ μ).cinner (s9dR_E D q) (s9dR_E D q') = if q = q' then 1 else 0 := by
  obtain ⟨r, s⟩ := q
  obtain ⟨r', s'⟩ := q'
  have key : (s7LawYZ μ).cinner (s9dR_E D (r, s)) (s9dR_E D (r', s')) =
      (lawY μ).cinner (D.gJ r') (D.gJ r) * (lawZ μ).cinner (D.hJ s') (D.hJ s) := by
    simp only [cinner_def, Fintype.sum_prod_type, hind, Finset.sum_mul_sum, s9dR_E]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    simp only [star_mul', star_star]; push_cast; ring
  rw [key, D.gJ_orth, D.hJ_orth]
  by_cases hr : r = r' <;> by_cases hs : s = s' <;> simp [hr, hs, eq_comm]

omit [DecidableEq X] [Fintype H] [DecidableEq H] in
/-- `F̂'(r,s) = ⟨F, conj(g'_r h'_s)⟩_{μ_{y,z}}` for every `F` on `Y × Z`. -/
private lemma s9dR_cinner_E (D : S9dSvd j μ hμ ux F g h d') (G : Y × Z → ℂ) (r : Fin D.sG)
    (s : Fin D.sH) :
    (s7LawYZ μ).cinner G (s9dR_E D (r, s)) = s8Corr1 μ G (D.gJ r) (D.hJ s) := by
  simp only [s8Corr1, FinProb.cinner, s9dR_E, star_star]
  unfold s7LawYZ
  rw [s9dR_cexpect_push]
  simp only [mul_assoc]

private lemma s9dR_real_sub_sum_le {sR sS : ℕ} (R' : Finset (Fin sR)) (S' : Finset (Fin sS))
    (a : Fin sR → Fin sS → ℝ) (ha : ∀ r s, 0 ≤ a r s) :
    ∑ r ∈ R', ∑ s ∈ S', a r s ≤ ∑ r, ∑ s, a r s := by
  refine (Finset.sum_le_sum fun r _ => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) fun s _ _ => ha r s).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ =>
    Finset.sum_nonneg fun s _ => ha r s

end S9dRelaxedHelpersD


section S9dRelaxedThms
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {K₁ K₂ : Type}

/-- every `x` occurs in an atom of mass `≥ α`, so `μ_x(x) ≥ α` (used in Claim 9.19 for
`‖u‖_∞ ≤ ‖u‖_2/√α`, a point the source leaves implicit). -/
theorem s9d_lawX_ge (μ : FinProb (X × Y × Z)) {α : ℝ} (hat : ∀ p ∈ μ.support, α ≤ μ.prob p)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) (x : X) : α ≤ (lawX μ).prob x := by
  obtain ⟨y, z, hyz⟩ := hocc x
  have h1 : α ≤ μ.prob (x, y, z) := hat _ hyz
  show α ≤ ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.1 = x), μ.prob p
  exact h1.trans (Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p) (by simp))

/-- Paper IV `lem:v-not-perp#rank-one-parts-small-modest-variance` (eq. `delta_7`, l. 5864-5891): `F'_{r,s}` is
a unit function with `|𝔼_μ F'_{r,s} g'_r h'_s| ≥ 1 - ϑ` (`ϑ = ζ^{1/4}`, Claim 9.18), is `ϑ`-close to
`conj(g'_r h'_s)` (`‖F'_{r,s} - conj(g'_rh'_s)‖² ≤ 2ϑ`), equals `W f'_{r,s}`, and by the relaxed base case
(constants `(c, C)`) `var_{Σ_modest}(f'_{r,s}) ≤ (ϑ/c)^{1/C}` (the exponent is made
explicit, the source leaving it implicit; the printed `ζ^c` is `(ϑ/c)^{1/C}`). -/
theorem s9d_rank_one_parts {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)}
    {hμ : S7YZImpliesX μ.support} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ}
    {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (D : S9dSvd j μ hμ ux F g h d') (T' : Finset (Fin D.sF)) (r : Fin D.sG) (s : Fin D.sH)
    {ζ c C : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hc : 0 < c) (hC : 0 < C) (Sm : Finset X)
    (hSm : Sm.Nonempty) (hrb : RelaxedBaseCase μ Sm c C)
    (hfull2 : 1 - ζ ^ (1 / 4 : ℝ) ≤ ∑ t ∈ T', ‖D.FhatJ t r s‖ ^ 2) :
    (s7LawYZ μ).expect (fun v => ‖D.rankOne T' r s v‖ ^ 2) = 1 ∧
      1 - ζ ^ (1 / 4 : ℝ) ≤ ‖s8Corr1 μ (D.rankOne T' r s) (D.gJ r) (D.hJ s)‖ ∧
      (s7LawYZ μ).expect (fun v => ‖D.rankOne T' r s v - starRingEnd ℂ (D.gJ r v.1 * D.hJ s v.2)‖ ^ 2) ≤
        2 * ζ ^ (1 / 4 : ℝ) ∧
      ∃ f : X → ℂ, s8W1 hμ f = D.rankOne T' r s ∧
        s7ModestVar Sm hSm f ≤ (ζ ^ (1 / 4 : ℝ) / c) ^ (1 / C) := by
  classical
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : ℝ, ϑ = ζ ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hϑ] at hfull2 ⊢
  have hϑ0 : 0 ≤ ϑ := hϑ ▸ Real.rpow_nonneg hζ0.le _
  have hϑ1 : ϑ < 1 := hϑ ▸ Real.rpow_lt_one hζ0.le hζ1 (by norm_num)
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ∑ t ∈ T', ‖D.FhatJ t r s‖ ^ 2 := ⟨_, rfl⟩
  rw [← hN] at hfull2
  have hNpos : 0 < N := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt N := ⟨_, rfl⟩
  have hqpos : 0 < q := hq ▸ Real.sqrt_pos.2 hNpos
  have hqq : q * q = N := by rw [hq]; exact Real.mul_self_sqrt hNpos.le
  have hq1 : 1 - ϑ ≤ q := by
    by_cases hN1 : N ≤ 1
    · have : q ≤ 1 := by nlinarith
      nlinarith
    · have hN1 := not_le.1 hN1
      have : 1 < q := by nlinarith
      linarith
  -- the weights
  obtain ⟨w, hw⟩ : ∃ w : Fin D.sF → ℂ, w = fun t =>
      if t ∈ T' then ((q : ℂ))⁻¹ * star (D.FhatJ t r s) else 0 := ⟨_, rfl⟩
  have hR : D.rankOne T' r s = fun v => ∑ t, w t * D.FJ t v := by
    funext v
    simp only [S9dSvd.rankOne, hw, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter,
      ← hN, ← hq, Finset.mul_sum, mul_assoc]
    rfl
  have hw2 : ∑ t, ‖w t‖ ^ 2 = 1 := by
    have h1 : ∀ t, ‖w t‖ ^ 2 = if t ∈ T' then (q⁻¹) ^ 2 * ‖D.FhatJ t r s‖ ^ 2 else 0 := by
      intro t
      by_cases ht : t ∈ T' <;> simp [hw, ht, mul_pow, abs_of_pos hqpos]
    simp only [h1, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, ← hN]
    field_simp
    nlinarith
  have hRR : (s7LawYZ μ).cinner (D.rankOne T' r s) (D.rankOne T' r s) = 1 := by
    rw [hR, s9dR_cinner_orth_sum (s7LawYZ μ) Finset.univ D.FJ (fun c _ c' _ => D.FJ_orth c c') w w]
    have h1 : ((∑ t, ‖w t‖ ^ 2 : ℝ) : ℂ) = 1 := by rw [hw2]; simp
    rw [← h1, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun t _ => s9dR_mul_star_self (w t)
  have hexp1 : (s7LawYZ μ).expect (fun v => ‖D.rankOne T' r s v‖ ^ 2) = 1 := by
    have := cinner_self_eq (s7LawYZ μ) (D.rankOne T' r s)
    rw [hRR] at this
    exact_mod_cast this.symm
  -- the correlation of the rank-one part
  have hRE : (s7LawYZ μ).cinner (D.rankOne T' r s) (s9dR_E D (r, s)) = (q : ℂ) := by
    rw [hR, s9dR_fun_sum_eq, cinner_sum_left]
    simp only [cinner_smul_left, s9dR_cinner_E]
    have h1 : ∀ t, w t * s8Corr1 μ (D.FJ t) (D.gJ r) (D.hJ s) =
        if t ∈ T' then ((q : ℂ))⁻¹ * ((‖D.FhatJ t r s‖ ^ 2 : ℝ) : ℂ) else 0 := by
      intro t
      by_cases ht : t ∈ T'
      · simp only [hw, ht, ite_true, mul_assoc]
        congr 1
        exact s9dR_star_mul_self _
      · simp [hw, ht]
    simp only [h1, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
    rw [← Complex.ofReal_sum, ← hN]
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
    rw [← hqq]
    push_cast
    field_simp
  have hcorr : s8Corr1 μ (D.rankOne T' r s) (D.gJ r) (D.hJ s) = (q : ℂ) := by
    rw [← s9dR_cinner_E D, hRE]
  have hEE : (s7LawYZ μ).cinner (s9dR_E D (r, s)) (s9dR_E D (r, s)) = 1 := by
    rw [s9dR_E_orth D hind]; simp
  -- the distance to `conj(g' h')`
  have hdist : (s7LawYZ μ).expect (fun v =>
      ‖D.rankOne T' r s v - starRingEnd ℂ (D.gJ r v.1 * D.hJ s v.2)‖ ^ 2) ≤ 2 * ϑ := by
    have hfun : (fun v => D.rankOne T' r s v - starRingEnd ℂ (D.gJ r v.1 * D.hJ s v.2)) =
        D.rankOne T' r s + (-1 : ℂ) • s9dR_E D (r, s) := by
      funext v; simp [s9dR_E, sub_eq_add_neg]
    have h1 := cinner_self_eq (s7LawYZ μ) (fun v =>
      D.rankOne T' r s v - starRingEnd ℂ (D.gJ r v.1 * D.hJ s v.2))
    have h2 : (s7LawYZ μ).cinner (D.rankOne T' r s + (-1 : ℂ) • s9dR_E D (r, s))
        (D.rankOne T' r s + (-1 : ℂ) • s9dR_E D (r, s)) = ((2 - 2 * q : ℝ) : ℂ) := by
      rw [cinner_add_left, cinner_add_right, cinner_add_right, cinner_smul_left, cinner_smul_left,
        cinner_smul_right, cinner_smul_right, hRR, hRE, hEE, cinner_comm, hRE]
      simp only [star_neg, star_one, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    have h4 : (s7LawYZ μ).cinner (fun v =>
        D.rankOne T' r s v - starRingEnd ℂ (D.gJ r v.1 * D.hJ s v.2))
        (fun v => D.rankOne T' r s v - starRingEnd ℂ (D.gJ r v.1 * D.hJ s v.2)) =
        ((2 - 2 * q : ℝ) : ℂ) := by
      rw [hfun]; exact h2
    rw [h4] at h1
    have h3 := congrArg Complex.re h1
    simp only [Complex.ofReal_re] at h3
    linarith
  refine ⟨hexp1, ?_, by simpa [hϑ] using hdist, ?_⟩
  · rw [hcorr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]; exact hq1
  · -- the relaxed base case
    obtain ⟨ft, hft⟩ : ∃ ft : Fin D.sF → X → ℂ, ∀ t, s8W1 hμ (ft t) = D.FJ t := by
      choose ft hft using D.FJ_cc
      exact ⟨ft, hft⟩
    obtain ⟨f, hf⟩ : ∃ f : X → ℂ, f = fun x => ∑ t, w t * ft t x := ⟨_, rfl⟩
    have hWf : s8W1 hμ f = D.rankOne T' r s := by
      rw [hR]
      funext v
      simp only [hf, s8W1]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← congrFun (hft t) v]
      rfl
    refine ⟨f, hWf, ?_⟩
    have hfn : ∑ x, (lawX μ).prob x * ‖f x‖ ^ 2 = 1 := by
      have := s9dR_expect_W μ hμ (fun x => ‖f x‖ ^ 2)
      have h2 : (s7LawYZ μ).expect (fun v => ‖f (s7Pre hμ v.1 v.2)‖ ^ 2) = 1 := by
        rw [← hexp1]
        refine Finset.sum_congr rfl fun v _ => ?_
        beta_reduce
        have := congrFun hWf v
        simp only [s8W1] at this
        rw [this]
      rw [h2] at this
      exact this.symm
    have hgn : ∑ y, (lawY μ).prob y * ‖D.gJ r y‖ ^ 2 = 1 := by
      have := cinner_self_eq (lawY μ) (D.gJ r)
      rw [D.gJ_orth r r] at this
      simp only [↓reduceIte] at this
      have h2 : (lawY μ).expect (fun a => ‖D.gJ r a‖ ^ 2) = 1 := by
        exact_mod_cast this.symm
      exact h2
    have hhn : ∑ z, (lawZ μ).prob z * ‖D.hJ s z‖ ^ 2 = 1 := by
      have := cinner_self_eq (lawZ μ) (D.hJ s)
      rw [D.hJ_orth s s] at this
      simp only [↓reduceIte] at this
      have h2 : (lawZ μ).expect (fun a => ‖D.hJ s a‖ ^ 2) = 1 := by
        exact_mod_cast this.symm
      exact h2
    have hv0 := s9dR_var_nonneg Sm hSm f
    have hυ0 : 0 ≤ (ϑ / c) ^ (1 / C) := Real.rpow_nonneg (div_nonneg hϑ0 hc.le) _
    rcases hv0.eq_or_lt with hv | hv
    · rw [← hv]; exact hυ0
    · have hmain := hrb.2 (s7ModestVar Sm hSm f) hv f (D.gJ r) (D.hJ s) hfn hgn hhn le_rfl
      rw [s9dR_corr_W μ hμ f, hWf, hcorr, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hqpos] at hmain
      have h1 : c * s7ModestVar Sm hSm f ^ C ≤ ϑ := by linarith
      have h2 : s7ModestVar Sm hSm f ^ C ≤ ϑ / c := by
        rw [le_div_iff₀ hc]; linarith
      have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hv.le _) h2 (by positivity : (0 : ℝ) ≤ 1 / C)
      rwa [one_div, Real.rpow_rpow_inv hv.le hC.ne', ← one_div] at h3

/-- Paper IV `claim:use-relaxed-base` (Claim 9.19, l. 5893-5926): for every `t ∈ T'`,
`var_{Σ_modest}(f'_t) ≤ (√(2/α) (ϑ + m√(2ϑ)) + m √υ)²`, `ϑ = ζ^{1/4}`, `υ = (ϑ/c)^{1/C}`. The
printed `ζ^{c/2}` with a constant "`C_m`" hides: the seminorm `√var_{Σ_modest}` is `≤ √(2/α) ‖·‖_{L²(μ_x)}`
(atoms `≥ α`: the honest constant depends on `(m, α)`; a gap in the source); `‖F'_{r,s} - g'_rh'_s‖ ≤
√2 ζ^{1/8}`, not `O(ζ^{1/4})` (another gap in the source); `√ℓ ≤ m`. The bound is
`s9dVarBound m α c C ζ 0`. Inputs: Claim 9.17 (`hfull`), Claim 9.18 (`hfull2`), Bessel. -/
theorem s9d_use_relaxed_base {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)}
    {hμ : S7YZImpliesX μ.support} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ}
    {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {m : ℕ} {α ζ c C : ℝ} (hα : 0 < α) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hc : 0 < c) (hC : 0 < C)
    (hatx : ∀ x, α ≤ (lawX μ).prob x) (Sm : Finset X) (hSm : Sm.Nonempty)
    (hrb : RelaxedBaseCase μ Sm c C) (D : S9dSvd j μ hμ ux F g h d') (T' : Finset (Fin D.sF))
    (R' : Finset (Fin D.sG)) (S' : Finset (Fin D.sH)) (hR : R'.card ≤ m) (hS : S'.card ≤ m)
    (hfull : ∀ t ∈ T', 1 - Real.sqrt ζ ≤ ∑ r ∈ R', ∑ s ∈ S', ‖D.FhatJ t r s‖ ^ 2)
    (hfull2 : ∀ r ∈ R', ∀ s ∈ S', 1 - ζ ^ (1 / 4 : ℝ) ≤ ∑ t ∈ T', ‖D.FhatJ t r s‖ ^ 2)
    (f' : Fin D.sF → X → ℂ) (hf' : ∀ t, s8W1 hμ (f' t) = D.FJ t) :
    ∀ t ∈ T', s7ModestVar Sm hSm (f' t) ≤ s9dVarBound m α c C ζ 0 := by
  classical
  intro t₀ ht₀
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : ℝ, ϑ = ζ ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hϑ0 : 0 ≤ ϑ := hϑ ▸ Real.rpow_nonneg hζ0.le _
  have hϑsq : ϑ ^ 2 = Real.sqrt ζ := by
    rw [hϑ, ← Real.rpow_natCast, ← Real.rpow_mul hζ0.le, Real.sqrt_eq_rpow]; norm_num
  rw [← hϑ] at hfull2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin D.sG × Fin D.sH), I = R' ×ˢ S' := ⟨_, rfl⟩
  have hEo : ∀ q ∈ I, ∀ q' ∈ I, (s7LawYZ μ).cinner (s9dR_E D q) (s9dR_E D q') =
      if q = q' then 1 else 0 := fun q _ q' _ => s9dR_E_orth D hind q q'
  obtain ⟨a, ha⟩ : ∃ a : Fin D.sG × Fin D.sH → ℂ, a = fun q => D.FhatJ t₀ q.1 q.2 := ⟨_, rfl⟩
  have hacin : ∀ q, (s7LawYZ μ).cinner (D.FJ t₀) (s9dR_E D q) = a q := by
    rintro ⟨r, s⟩
    rw [s9dR_cinner_E D, ha]; rfl
  have hIsum : ∑ q ∈ I, ‖a q‖ ^ 2 = ∑ r ∈ R', ∑ s ∈ S', ‖D.FhatJ t₀ r s‖ ^ 2 := by
    simp only [hI, Finset.sum_product, ha]
  -- the projection error
  have hres : (s7LawYZ μ).expect (fun v => ‖D.FJ t₀ v - ∑ q ∈ I, a q * s9dR_E D q v‖ ^ 2) ≤ ϑ ^ 2 := by
    have h1 := s9dR_resid (s7LawYZ μ) I (s9dR_E D) hEo (D.FJ t₀)
    simp only [hacin] at h1
    rw [h1, D.FJ_orth t₀ t₀, hIsum, hϑsq]
    have := hfull t₀ ht₀
    simp only [↓reduceIte, Complex.one_re]
    linarith
  -- rank-one parts
  have hrp : ∀ q : Fin D.sG × Fin D.sH, ∃ fq : X → ℂ, q ∈ I →
      (s8W1 hμ fq = D.rankOne T' q.1 q.2 ∧ s7ModestVar Sm hSm fq ≤ (ϑ / c) ^ (1 / C) ∧
        (s7LawYZ μ).expect (fun v => ‖D.rankOne T' q.1 q.2 v - s9dR_E D q v‖ ^ 2) ≤ 2 * ϑ) := by
    intro q
    by_cases hq : q ∈ I
    · rw [hI, Finset.mem_product] at hq
      obtain ⟨_, h3, h4, fq, hfq, hvar⟩ :=
        s9d_rank_one_parts hind D T' q.1 q.2 hζ0 hζ1 hc hC Sm hSm hrb
          (by have := hfull2 q.1 hq.1 q.2 hq.2; rwa [hϑ] at this)
      refine ⟨fq, fun _ => ⟨hfq, by rwa [← hϑ] at hvar, ?_⟩⟩
      rw [← hϑ] at h4
      exact h4
    · exact ⟨0, fun h => absurd h hq⟩
  choose fq hfq using hrp
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : X → ℂ, Δ = fun x => f' t₀ x - ∑ q ∈ I, a q * fq q x := ⟨_, rfl⟩
  have hΔW : ∀ v, Δ (s7Pre hμ v.1 v.2) = (D.FJ t₀ v - ∑ q ∈ I, a q * s9dR_E D q v) +
      ∑ q ∈ I, a q * (s9dR_E D q v - D.rankOne T' q.1 q.2 v) := by
    intro v
    have h1 : f' t₀ (s7Pre hμ v.1 v.2) = D.FJ t₀ v := congrFun (hf' t₀) v
    have h2 : ∀ q ∈ I, fq q (s7Pre hμ v.1 v.2) = D.rankOne T' q.1 q.2 v := fun q hq =>
      congrFun (hfq q hq).1 v
    rw [hΔ]
    simp only [h1]
    rw [Finset.sum_congr rfl fun q hq => by rw [h2 q hq]]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  -- sizes
  have hIcard : (I.card : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [hI, Finset.card_product]
    have : R'.card * S'.card ≤ m * m := Nat.mul_le_mul hR hS
    calc ((R'.card * S'.card : ℕ) : ℝ) ≤ ((m * m : ℕ) : ℝ) := by exact_mod_cast this
      _ = (m : ℝ) ^ 2 := by push_cast; ring
  have hasq : ∑ q ∈ I, ‖a q‖ ^ 2 ≤ 1 := by
    rw [hIsum]
    exact (s9dR_real_sub_sum_le R' S' (fun r s => ‖D.FhatJ t₀ r s‖ ^ 2)
      fun _ _ => sq_nonneg _).trans ((s9d_level_bounds_b D hind).1 t₀)
  have hasum : ∑ q ∈ I, ‖a q‖ ≤ m := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun q => ‖a q‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    have h2 : (∑ q ∈ I, ‖a q‖) ^ 2 ≤ (m : ℝ) ^ 2 := by
      calc (∑ q ∈ I, ‖a q‖) ^ 2 ≤ I.card * ∑ q ∈ I, ‖a q‖ ^ 2 := h1
        _ ≤ (m : ℝ) ^ 2 * 1 := mul_le_mul hIcard hasq (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (sq_nonneg _)
        _ = (m : ℝ) ^ 2 := mul_one _
    exact abs_le_of_sq_le_sq' h2 hm0 |>.2
  -- the `L²`-distance of `W Δ`
  have hnrm1 : s9dR_nrm (s7LawYZ μ) (fun v => Δ (s7Pre hμ v.1 v.2)) ≤ ϑ + m * Real.sqrt (2 * ϑ) := by
    have h1 := s9dR_nrm_comb (s7LawYZ μ) I (fun v => Δ (s7Pre hμ v.1 v.2))
      (fun v => D.FJ t₀ v - ∑ q ∈ I, a q * s9dR_E D q v) a
      (fun q v => s9dR_E D q v - D.rankOne T' q.1 q.2 v) hΔW
    refine h1.trans ?_
    have h2 : s9dR_nrm (s7LawYZ μ) (fun v => D.FJ t₀ v - ∑ q ∈ I, a q * s9dR_E D q v) ≤ ϑ := by
      have h3 := s9dR_nrm_sq (s7LawYZ μ) (fun v => D.FJ t₀ v - ∑ q ∈ I, a q * s9dR_E D q v)
      have h4 := s9dR_nrm_nonneg (s7LawYZ μ) (fun v => D.FJ t₀ v - ∑ q ∈ I, a q * s9dR_E D q v)
      nlinarith
    have h5 : ∀ q ∈ I, s9dR_nrm (s7LawYZ μ) (fun v => s9dR_E D q v - D.rankOne T' q.1 q.2 v) ≤
        Real.sqrt (2 * ϑ) := by
      intro q hq
      have h6 := s9dR_nrm_sq (s7LawYZ μ) (fun v => s9dR_E D q v - D.rankOne T' q.1 q.2 v)
      have h7 := (hfq q hq).2.2
      have h8 : (s7LawYZ μ).expect (fun v => ‖s9dR_E D q v - D.rankOne T' q.1 q.2 v‖ ^ 2) ≤ 2 * ϑ := by
        have h9 : ∀ v, ‖s9dR_E D q v - D.rankOne T' q.1 q.2 v‖ =
            ‖D.rankOne T' q.1 q.2 v - s9dR_E D q v‖ := fun v => norm_sub_rev _ _
        simp only [h9]
        exact h7
      calc s9dR_nrm (s7LawYZ μ) (fun v => s9dR_E D q v - D.rankOne T' q.1 q.2 v)
          = Real.sqrt (s9dR_nrm (s7LawYZ μ) (fun v => s9dR_E D q v - D.rankOne T' q.1 q.2 v) ^ 2) :=
            (Real.sqrt_sq (s9dR_nrm_nonneg _ _)).symm
        _ ≤ Real.sqrt (2 * ϑ) := Real.sqrt_le_sqrt (by rw [h6]; exact h8)
    calc _ ≤ ϑ + ∑ q ∈ I, ‖a q‖ * Real.sqrt (2 * ϑ) :=
          add_le_add h2 (Finset.sum_le_sum fun q hq =>
            mul_le_mul_of_nonneg_left (h5 q hq) (norm_nonneg _))
      _ = ϑ + (∑ q ∈ I, ‖a q‖) * Real.sqrt (2 * ϑ) := by rw [Finset.sum_mul]
      _ ≤ ϑ + m * Real.sqrt (2 * ϑ) := by gcongr
  -- the `L²(μ_x)`-distance of `Δ`
  have hnrmX : s9dR_nrm (lawX μ) Δ = s9dR_nrm (s7LawYZ μ) (fun v => Δ (s7Pre hμ v.1 v.2)) := by
    have h1 := s9dR_nrm_sq (lawX μ) Δ
    have h2 := s9dR_nrm_sq (s7LawYZ μ) (fun v => Δ (s7Pre hμ v.1 v.2))
    have h3 := s9dR_expect_W μ hμ (fun x => ‖Δ x‖ ^ 2)
    have h4 := s9dR_nrm_nonneg (lawX μ) Δ
    have h5 := s9dR_nrm_nonneg (s7LawYZ μ) (fun v => Δ (s7Pre hμ v.1 v.2))
    have : s9dR_nrm (lawX μ) Δ ^ 2 = s9dR_nrm (s7LawYZ μ) (fun v => Δ (s7Pre hμ v.1 v.2)) ^ 2 := by
      rw [h1, h2]; exact h3.symm
    nlinarith
  -- the seminorm
  have hcard2 : 2 ≤ Sm.card := hrb.1
  have hdec : ∀ x, f' t₀ x = Δ x + ∑ q ∈ I, a q * fq q x := by
    intro x; rw [hΔ]; ring
  have hs1 := s9dR_sqrt_var_comb Sm hSm I (f' t₀) Δ a fq hdec
  have hs2 : Real.sqrt (s7ModestVar Sm hSm Δ) ≤ Real.sqrt (2 / α) * (ϑ + m * Real.sqrt (2 * ϑ)) := by
    have h1 := s9dR_var_le (lawX μ) Sm hSm hcard2 hα hatx Δ
    rw [← s9dR_nrm_sq] at h1
    calc Real.sqrt (s7ModestVar Sm hSm Δ) ≤ Real.sqrt (2 / α * s9dR_nrm (lawX μ) Δ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 / α) * s9dR_nrm (lawX μ) Δ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (s9dR_nrm_nonneg _ _)]
      _ ≤ Real.sqrt (2 / α) * (ϑ + m * Real.sqrt (2 * ϑ)) := by
          rw [hnrmX]; gcongr
  have hs3 : ∑ q ∈ I, ‖a q‖ * Real.sqrt (s7ModestVar Sm hSm (fq q)) ≤
      m * Real.sqrt ((ϑ / c) ^ (1 / C)) := by
    calc ∑ q ∈ I, ‖a q‖ * Real.sqrt (s7ModestVar Sm hSm (fq q))
        ≤ ∑ q ∈ I, ‖a q‖ * Real.sqrt ((ϑ / c) ^ (1 / C)) := by
          gcongr with q hq
          exact (hfq q hq).2.1
      _ = (∑ q ∈ I, ‖a q‖) * Real.sqrt ((ϑ / c) ^ (1 / C)) := by rw [Finset.sum_mul]
      _ ≤ m * Real.sqrt ((ϑ / c) ^ (1 / C)) := by gcongr
  have hfin : Real.sqrt (s7ModestVar Sm hSm (f' t₀)) ≤
      Real.sqrt (2 / α) * (ϑ + m * Real.sqrt (2 * ϑ)) + m * Real.sqrt ((ϑ / c) ^ (1 / C)) := by
    linarith
  have hsq := Real.sq_sqrt (s9dR_var_nonneg Sm hSm (f' t₀))
  have hpos := Real.sqrt_nonneg (s7ModestVar Sm hSm (f' t₀))
  have hB : s9dVarBound m α c C ζ 0 =
      (Real.sqrt (2 / α) * (ϑ + m * Real.sqrt (2 * ϑ)) + m * Real.sqrt ((ϑ / c) ^ (1 / C))) ^ 2 := by
    unfold s9dVarBound
    rw [← hϑ]
    ring
  rw [hB, ← hsq]
  exact pow_le_pow_left₀ hpos hfin 2

/-- Paper IV `lem:v-not-perp#modest-influence-contradiction` (l. 5928-5934): `I_{j,modest}[F] ≥ 1/A`
(`s9d_choose_coordinate`), Claim 9.7 (`I_j ≤ m² ∑_t ψ_t² var(f'_t)`), Claim 9.19 on `T'` and
`var ≤ 2/α` with `ψ_t < η` off `T'` give `1/A ≤ m² · s9dVarBound m α c C ζ η`; this contradicts
`s9dVarBound m α c C ζ η < 1/(m² A)` (the `(hier2)` constraint, `s9d_parameter_hierarchy`). -/
theorem s9d_modest_influence_contradiction {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)}
    {hμ : S7YZImpliesX μ.support} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ}
    {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    {m : ℕ} (hX : Fintype.card X ≤ m) {α ζ c C : ℝ} (hα : 0 < α) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hc : 0 < c) (hC : 0 < C) (hatx : ∀ x, α ≤ (lawX μ).prob x) (Sm : Finset X)
    (hSm : Sm.Nonempty) (hrb : RelaxedBaseCase μ Sm c C) (D : S9dSvd j μ hμ ux F g h d')
    (hF : S7ConstOnCC hμ F) {τ η A : ℝ} (hA : 0 < A) (hη : 0 ≤ η)
    (hsep : ∀ t, D.ψ t < η ∨ τ ≤ D.ψ t) (R' : Finset (Fin D.sG)) (S' : Finset (Fin D.sH))
    (hR : R'.card ≤ m) (hS : S'.card ≤ m)
    (hfull : ∀ t, τ ≤ D.ψ t → 1 - Real.sqrt ζ ≤ ∑ r ∈ R', ∑ s ∈ S', ‖D.FhatJ t r s‖ ^ 2)
    (hfull2 : ∀ r ∈ R', ∀ s ∈ S',
      1 - ζ ^ (1 / 4 : ℝ) ≤ ∑ t ∈ s9dBig D.ψ τ, ‖D.FhatJ t r s‖ ^ 2)
    (hIj : 1 / A ≤ s7CCModestInf μ hμ hocc Sm hF j)
    (hlt : s9dVarBound m α c C ζ η < 1 / ((m : ℝ) ^ 2 * A)) : False := by
  classical
  have hXpos : 0 < Fintype.card X := Fintype.card_pos_iff.2 ⟨hSm.choose⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hXpos.trans_le hX
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨f', hf'⟩ : ∃ f' : Fin D.sF → X → ℂ, ∀ t, s8W1 hμ (f' t) = D.FJ t := by
    choose f' hf' using D.FJ_cc
    exact ⟨f', hf'⟩
  have h1 := s9d_large_modestinf_sig_var μ hμ hocc Sm hSm hX j F hF D.ψ D.FI D.FJ D.F_eq D.FI_orth
    D.FI_cc f' hf'
  have hB0 : 0 ≤ s9dVarBound m α c C ζ 0 := by
    unfold s9dVarBound
    have : 0 ≤ (Real.sqrt (2 / α) * (ζ ^ (1 / 4 : ℝ) + m * Real.sqrt (2 * ζ ^ (1 / 4 : ℝ))) +
      m * Real.sqrt ((ζ ^ (1 / 4 : ℝ) / c) ^ (1 / C))) ^ 2 := sq_nonneg _
    simpa using this
  have hterm : ∀ t, D.ψ t ^ 2 * s7ModestVar Sm hSm (f' t) ≤
      D.ψ t ^ 2 * s9dVarBound m α c C ζ 0 + η ^ 2 * (2 / α) := by
    intro t
    have hψ0 := D.ψ_nonneg t
    have hv0 := s9dR_var_nonneg Sm hSm (f' t)
    have h2α : 0 ≤ 2 / α := by positivity
    rcases hsep t with hlt' | hge
    · -- `ψ_t < η`: `var ≤ 2/α`
      have hvar : s7ModestVar Sm hSm (f' t) ≤ 2 / α := by
        have h3 := s9dR_var_le (lawX μ) Sm hSm hrb.1 hα hatx (f' t)
        have h4 : (lawX μ).expect (fun x => ‖f' t x‖ ^ 2) = 1 := by
          rw [← s9dR_expect_W μ hμ]
          have h5 := cinner_self_eq (s7LawYZ μ) (D.FJ t)
          rw [D.FJ_orth t t] at h5
          simp only [↓reduceIte] at h5
          have h6 : (s7LawYZ μ).expect (fun v => ‖D.FJ t v‖ ^ 2) = 1 := by
            exact_mod_cast h5.symm
          rw [← h6]
          refine Finset.sum_congr rfl fun v _ => ?_
          beta_reduce
          have := congrFun (hf' t) v
          simp only [s8W1] at this
          rw [this]
        rw [h4, mul_one] at h3
        exact h3
      have hψη : D.ψ t ^ 2 ≤ η ^ 2 := by nlinarith
      have : D.ψ t ^ 2 * s7ModestVar Sm hSm (f' t) ≤ η ^ 2 * (2 / α) :=
        mul_le_mul hψη hvar hv0 (sq_nonneg _)
      have := mul_nonneg (sq_nonneg (D.ψ t)) hB0
      linarith
    · -- `τ ≤ ψ_t`: Claim 9.19
      have hvar := s9d_use_relaxed_base hind hα hζ0 hζ1 hc hC hatx Sm hSm hrb D (s9dBig D.ψ τ) R' S'
        hR hS (fun t' ht' => hfull t' ((s9dBig_mem D.ψ τ t').1 ht')) hfull2 f' hf' t
        ((s9dBig_mem D.ψ τ t).2 hge)
      have : D.ψ t ^ 2 * s7ModestVar Sm hSm (f' t) ≤ D.ψ t ^ 2 * s9dVarBound m α c C ζ 0 :=
        mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
      have := mul_nonneg (sq_nonneg η) (by positivity : (0 : ℝ) ≤ 2 / α)
      linarith
  have hsum : ∑ t, D.ψ t ^ 2 * s7ModestVar Sm hSm (f' t) ≤
      s9dVarBound m α c C ζ 0 + m * (η ^ 2 * (2 / α)) := by
    calc ∑ t, D.ψ t ^ 2 * s7ModestVar Sm hSm (f' t)
        ≤ ∑ t, (D.ψ t ^ 2 * s9dVarBound m α c C ζ 0 + η ^ 2 * (2 / α)) :=
          Finset.sum_le_sum fun t _ => hterm t
      _ = (∑ t, D.ψ t ^ 2) * s9dVarBound m α c C ζ 0 + D.sF * (η ^ 2 * (2 / α)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul]
          simp
      _ ≤ s9dVarBound m α c C ζ 0 + m * (η ^ 2 * (2 / α)) := by
          rw [D.ψ_sq, one_mul]
          have hsF : (D.sF : ℝ) ≤ m := by exact_mod_cast (s9d_card_le D).1.trans hX
          have : 0 ≤ η ^ 2 * (2 / α) := by positivity
          nlinarith
  have hVB : s9dVarBound m α c C ζ η = s9dVarBound m α c C ζ 0 + m * (η ^ 2 * (2 / α)) := by
    unfold s9dVarBound
    ring
  have hfin : 1 / A ≤ (m : ℝ) ^ 2 * s9dVarBound m α c C ζ η := by
    rw [hVB]
    calc 1 / A ≤ _ := hIj
      _ ≤ (m : ℝ) ^ 2 * ∑ t, D.ψ t ^ 2 * s7ModestVar Sm hSm (f' t) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
  have h2 : (m : ℝ) ^ 2 * s9dVarBound m α c C ζ η < (m : ℝ) ^ 2 * (1 / ((m : ℝ) ^ 2 * A)) :=
    mul_lt_mul_of_pos_left hlt (by positivity)
  have h3 : (m : ℝ) ^ 2 * (1 / ((m : ℝ) ^ 2 * A)) = 1 / A := by
    field_simp
  linarith

/-- Paper IV `lem:v-not-perp` (Lemma 9.14, l. 5677-5934, §9.3.6 `sec:lem_V_not_perp`): under
`assume_delta_2` and `assume_delta_3` (for `T', R', S'` the coefficients `≥ τ`) there are
`(r,s) ≠ (r',s')` in `R' × S'` with `|⟨V_{r,s}, V_{r',s'}⟩| ≥ c_V δ'²`, `c_V = 1/(2m³)`
(`s ∈ S` of the printed statement is `S'`), `δ' = δ_{n-1,d'-1} > 0` (the degenerate case is
treated separately). Proof by contradiction: Claims 9.11, 9.17, 9.18, then rank-one parts, Claim 9.19 and
the modest-influence contradiction; this is the only place the relaxed base case is used. -/
theorem s9d_v_not_perp {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)}
    {hμ : S7YZImpliesX μ.support} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ}
    {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    {m : ℕ} (hm : 1 ≤ m) (hX : Fintype.card X ≤ m) (hY : Fintype.card Y ≤ m)
    (hZ : Fintype.card Z ≤ m) {α : ℝ} (hα : 0 < α) (hat : ∀ p ∈ μ.support, α ≤ μ.prob p)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (Sm : Finset X) (hSm : Sm.Nonempty)
    (hrb : RelaxedBaseCase μ Sm c C) (D : S9dSvd j μ hμ ux F g h d') (hF : S7ConstOnCC hμ F)
    (hδ' : 0 < (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal) {τ η ζ A : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hζ0 : 0 < ζ) (hζτ : ζ ≤ τ ^ 8) (hζ9 : 9 * ζ ≤ 1) (hζm : ζ * (m : ℝ) ^ 8 < 1) (hA : 0 < A) (hη : 0 ≤ η)
    (hsep : ∀ t, D.ψ t < η ∨ τ ≤ D.ψ t)
    (hassume2 : (1 - ζ) * s9dMass D.ψ τ < s9dA2 D.ψ D.κ D.ρ D.FhatJ τ)
    (hassume3 : (1 - ζ) * (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal ^ 2 *
        (s9dMass D.κ τ * s9dMass D.ρ τ) < s9dA1 D.ψ D.κ D.ρ D.Fhat τ)
    (hIj : 1 / A ≤ s7CCModestInf μ hμ hocc Sm hF j)
    (hlt : s9dVarBound m α c C ζ η < 1 / ((m : ℝ) ^ 2 * A)) :
    ∃ r ∈ s9dBig D.κ τ, ∃ s ∈ s9dBig D.ρ τ, ∃ r' ∈ s9dBig D.κ τ, ∃ s' ∈ s9dBig D.ρ τ,
      (r, s) ≠ (r', s') ∧
      1 / (2 * (m : ℝ) ^ 3) * (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal ^ 2 ≤
        ‖∑ t ∈ s9dBig D.ψ τ, D.Fhat t r s * starRingEnd ℂ (D.Fhat t r' s')‖ := by
  classical
  by_contra hcon
  have hcon' : ∀ r ∈ s9dBig D.κ τ, ∀ s ∈ s9dBig D.ρ τ, ∀ r' ∈ s9dBig D.κ τ,
      ∀ s' ∈ s9dBig D.ρ τ, (r, s) ≠ (r', s') →
      ‖∑ t ∈ s9dBig D.ψ τ, D.Fhat t r s * starRingEnd ℂ (D.Fhat t r' s')‖ <
        1 / (2 * (m : ℝ) ^ 3) * (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal ^ 2 := by
    intro r hr s hs r' hr' s' hs' hne
    by_contra hge
    exact hcon ⟨r, hr, s, hs, r', hr', s', hs', hne, not_lt.1 hge⟩
  obtain ⟨δ', hδ'e⟩ : ∃ δ', δ' = (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal := ⟨_, rfl⟩
  rw [← hδ'e] at hδ' hassume3 hcon'
  have hζ1 : ζ < 1 := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hatx : ∀ x, α ≤ (lawX μ).prob x := s9d_lawX_ge μ hat hocc
  have hcard := s9d_card_le D
  have hlev : ∀ r s, ∑ t, ‖D.Fhat t r s‖ ^ 2 ≤ δ' ^ 2 := by
    intro r s
    have e1 : ∀ {k : ℕ} (r : Fin k), ∑ x, ‖(Pi.single r (1 : ℂ) : Fin k → ℂ) x‖ ^ 2 = 1 := by
      intro k r
      rw [Finset.sum_eq_single r]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ r) h
    have := s9d_level_bounds_a D hind (Pi.single r 1) (Pi.single s 1)
    rw [← hδ'e, e1, e1] at this
    simpa [Pi.single_apply] using this
  have hup : ∀ r ∈ s9dBig D.κ τ, ∀ s ∈ s9dBig D.ρ τ,
      ∑ t ∈ s9dBig D.ψ τ, ‖D.Fhat t r s‖ ^ 2 ≤ δ' ^ 2 := fun r _ s _ =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => sq_nonneg _).trans (hlev r s)
  have hκ1 : ∑ r ∈ s9dBig D.κ τ, D.κ r ^ 2 ≤ 1 := by
    rw [← D.κ_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hρ1 : ∑ s ∈ s9dBig D.ρ τ, D.ρ s ^ 2 ≤ 1 := by
    rw [← D.ρ_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  -- Claim 9.11
  have hnorm := s9d_bound_norm_V D.κ D.ρ D.Fhat (s9dBig D.κ τ) (s9dBig D.ρ τ) (s9dBig D.ψ τ)
    hδ'.le hζ0.le hτ hζτ (fun r hr => (s9dBig_mem D.κ τ r).1 hr)
    (fun s hs => (s9dBig_mem D.ρ τ s).1 hs) hκ1 hρ1 hup hassume3
  -- Claim 9.17
  have hζτ4 : ζ ≤ τ ^ 4 := hζτ.trans (pow_le_pow_of_le_one hτ.le hτ1 (by norm_num))
  have hbb := s9d_level_bounds_b D hind
  have hfull := s9d_almost_full_norm D.ψ D.κ D.ρ D.FhatJ hζ0.le hτ hζτ4 D.ψ_sq.le
    (fun t => (s9dR_real_sub_sum_le (s9dBig D.κ τ) (s9dBig D.ρ τ)
      (fun r s => ‖D.FhatJ t r s‖ ^ 2) fun _ _ => sq_nonneg _).trans (hbb.1 t)) hassume2
  -- Claim 9.18
  have hR : (s9dBig D.κ τ).card ≤ m :=
    (Finset.card_le_univ _).trans (by simpa using hcard.2.1.trans hY)
  have hS : (s9dBig D.ρ τ).card ≤ m :=
    (Finset.card_le_univ _).trans (by simpa using hcard.2.2.trans hZ)
  have hT : (s9dBig D.ψ τ).card ≤ m :=
    (Finset.card_le_univ _).trans (by simpa using hcard.1.trans hX)
  have hsq : Real.sqrt ζ ≤ 1 / 3 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have hm3 : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
  have hcV : 1 / (2 * (m : ℝ) ^ 3) ≤ (1 - Real.sqrt ζ) / (m : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hm3]
    nlinarith
  have hfull2 := s9d_almost_full_norm2 m hm D.Fhat D.FhatJ (s9dBig D.κ τ) (s9dBig D.ρ τ)
    (s9dBig D.ψ τ) hR hS hT hδ' hζ0.le hζm hcV hnorm
    (fun t ht => hfull t ((s9dBig_mem D.ψ τ t).1 ht))
    (fun r _ s _ => (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => sq_nonneg _).trans (hbb.2 r s))
    (fun r hr s hs r' hr' s' hs' hne => hcon' r hr s hs r' hr' s' hs' hne)
  exact s9d_modest_influence_contradiction hind hocc hX hα hζ0 hζ1 hc hC hatx Sm hSm hrb D hF hA hη
    hsep (s9dBig D.κ τ) (s9dBig D.ρ τ) hR hS hfull hfull2 hIj hlt

end S9dRelaxedThms

end TrackB
end RestrictedPolynomials
end
