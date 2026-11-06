module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# An explicit polar loop around a hedgehog

Source: Supplement B, §2, Definition `def:loop`,
Lemma `lem:r`, Definition `def:H`, Lemma `lem:avoid`, Theorem `thm:homotopy` and
Corollary `cor:contour`.

* Part A (`homotopy_invariance`): for a closed set `K`, a `C¹` periodic radius function `r`
  such that the straight-line radial homotopy `H s θ = (R₀ + s (r θ - R₀)) e^{iθ}` avoids `K`
  for `s` in an open interval `J ∋ 0, 1`, contour integrals of functions differentiable off `K`
  over the circle `|z| = R₀` and over the polar loop `Γ θ = r θ e^{iθ}` agree.  The proof
  differentiates the parameter integral under the integral sign.
* Part B: the radius function `r = ε + ∑_e ℓ_e b_e` built from bump functions around the
  directions of the vertices of the hedgehog, and its properties.
* `exists_hedgehog_loop`: the packaged corollary.
-/

@[expose] public section

open Complex MeasureTheory Set Metric intervalIntegral Filter Topology
open scoped Real Interval

noncomputable section

namespace RestrictedPolynomials

namespace Contour

/-! ### Part A: homotopy invariance -/

section PartA

variable (r : ℝ → ℝ) (R₀ : ℝ)

/-- The radial homotopy `H s θ = (R₀ + s (r θ - R₀)) e^{iθ}`. -/
def Hmap (s θ : ℝ) : ℂ := ((R₀ : ℂ) + (s : ℂ) * ((r θ : ℂ) - R₀)) * Complex.exp (θ * I)

/-- `∂_s H`. -/
def Hs (θ : ℝ) : ℂ := ((r θ : ℂ) - R₀) * Complex.exp (θ * I)

/-- `∂_θ H`. -/
def Hth (s θ : ℝ) : ℂ :=
  ((s : ℂ) * ((deriv r θ : ℝ) : ℂ) + I * ((R₀ : ℂ) + (s : ℂ) * ((r θ : ℂ) - R₀))) *
    Complex.exp (θ * I)

/-- The common mixed partial `∂_s ∂_θ H = ∂_θ ∂_s H`. -/
def Hsth (θ : ℝ) : ℂ := (((deriv r θ : ℝ) : ℂ) + I * ((r θ : ℂ) - R₀)) * Complex.exp (θ * I)

/-- The polar loop `Γ θ = r θ e^{iθ}`. -/
def polarLoop (θ : ℝ) : ℂ := (r θ : ℂ) * Complex.exp (θ * I)

variable {r R₀}

lemma hasDerivAt_exp_mul_I (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Complex.exp (θ * I)) (I * Complex.exp (θ * I)) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp
  simpa [mul_comm] using h

lemma hasDerivAt_ofReal_r (hr : ContDiff ℝ 1 r) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (r θ : ℂ)) ((deriv r θ : ℝ) : ℂ) θ :=
  ((hr.differentiable one_ne_zero θ).hasDerivAt).ofReal_comp

lemma hasDerivAt_Hmap_s (s θ : ℝ) :
    HasDerivAt (fun s : ℝ => Hmap r R₀ s θ) (Hs r R₀ θ) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
  have h2 := (((h1.mul_const ((r θ : ℂ) - R₀)).const_add (R₀ : ℂ)).mul_const
    (Complex.exp (θ * I)))
  simpa [Hmap, Hs] using h2

lemma hasDerivAt_Hmap_th (hr : ContDiff ℝ 1 r) (s θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Hmap r R₀ s θ) (Hth r R₀ s θ) θ := by
  have h1 := (((hasDerivAt_ofReal_r hr θ).sub_const (R₀ : ℂ)).const_mul (s : ℂ)).const_add (R₀ : ℂ)
  have h2 := h1.mul (hasDerivAt_exp_mul_I θ)
  refine h2.congr_deriv ?_
  unfold Hth
  ring

lemma hasDerivAt_Hs_th (hr : ContDiff ℝ 1 r) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Hs r R₀ θ) (Hsth r R₀ θ) θ := by
  have h1 := ((hasDerivAt_ofReal_r hr θ).sub_const (R₀ : ℂ)).mul (hasDerivAt_exp_mul_I θ)
  refine h1.congr_deriv ?_
  unfold Hsth
  ring

lemma hasDerivAt_Hth_s (θ s : ℝ) :
    HasDerivAt (fun s : ℝ => Hth r R₀ s θ) (Hsth r R₀ θ) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
  have h2 := ((h1.mul_const ((deriv r θ : ℝ) : ℂ)).add
    (((h1.mul_const ((r θ : ℂ) - R₀)).const_add (R₀ : ℂ)).const_mul I)).mul_const
    (Complex.exp (θ * I))
  refine h2.congr_deriv ?_
  unfold Hsth
  ring

lemma hasDerivAt_polarLoop (hr : ContDiff ℝ 1 r) (θ : ℝ) :
    HasDerivAt (polarLoop r) (Hth r R₀ 1 θ) θ := by
  have h2 := (hasDerivAt_ofReal_r hr θ).mul (hasDerivAt_exp_mul_I θ)
  refine h2.congr_deriv ?_
  unfold Hth
  push_cast
  ring

lemma polarLoop_eq_Hmap (s : ℝ) (hs : s = 1) (θ : ℝ) :
    Hmap r R₀ s θ = polarLoop r θ := by
  subst hs
  simp [Hmap, polarLoop]

end PartA

section PartA2

variable {r : ℝ → ℝ} {R₀ : ℝ} {K : Set ℂ}

/-- The integrand `G(H) ∂_θ H`. -/
def gfun (G : ℂ → ℂ) (r : ℝ → ℝ) (R₀ s θ : ℝ) : ℂ := G (Hmap r R₀ s θ) * Hth r R₀ s θ

/-- The integrand `G(H) ∂_s H`. -/
def hfun (G : ℂ → ℂ) (r : ℝ → ℝ) (R₀ s θ : ℝ) : ℂ := G (Hmap r R₀ s θ) * Hs r R₀ θ

/-- The derivative `∂_s g = ∂_θ h`. -/
def gder (G : ℂ → ℂ) (r : ℝ → ℝ) (R₀ s θ : ℝ) : ℂ :=
  deriv G (Hmap r R₀ s θ) * Hs r R₀ θ * Hth r R₀ s θ + G (Hmap r R₀ s θ) * Hsth r R₀ θ

lemma hasDerivAt_gfun_s {G : ℂ → ℂ} (hK : IsClosed K) (hG : DifferentiableOn ℂ G Kᶜ) {s θ : ℝ}
    (hmem : Hmap r R₀ s θ ∈ Kᶜ) :
    HasDerivAt (fun s => gfun G r R₀ s θ) (gder G r R₀ s θ) s := by
  have hGd : HasDerivAt G (deriv G (Hmap r R₀ s θ)) (Hmap r R₀ s θ) :=
    (hG.differentiableAt (hK.isOpen_compl.mem_nhds hmem)).hasDerivAt
  have h1 := hGd.scomp s (hasDerivAt_Hmap_s (r := r) (R₀ := R₀) s θ)
  have h2 := h1.mul (hasDerivAt_Hth_s (r := r) (R₀ := R₀) θ s)
  refine h2.congr_deriv ?_
  simp only [gder, smul_eq_mul, Function.comp_apply]
  ring

lemma hasDerivAt_hfun_th {G : ℂ → ℂ} (hr : ContDiff ℝ 1 r) (hK : IsClosed K)
    (hG : DifferentiableOn ℂ G Kᶜ) {s θ : ℝ} (hmem : Hmap r R₀ s θ ∈ Kᶜ) :
    HasDerivAt (fun θ => hfun G r R₀ s θ) (gder G r R₀ s θ) θ := by
  have hGd : HasDerivAt G (deriv G (Hmap r R₀ s θ)) (Hmap r R₀ s θ) :=
    (hG.differentiableAt (hK.isOpen_compl.mem_nhds hmem)).hasDerivAt
  have h1 := hGd.scomp θ (hasDerivAt_Hmap_th hr (R₀ := R₀) s θ)
  have h2 := h1.mul (hasDerivAt_Hs_th hr (R₀ := R₀) θ)
  refine h2.congr_deriv ?_
  simp only [gder, smul_eq_mul, Function.comp_apply]
  ring

lemma continuous_Hmap (hr : ContDiff ℝ 1 r) :
    Continuous fun p : ℝ × ℝ => Hmap r R₀ p.1 p.2 := by
  have := hr.continuous
  unfold Hmap
  fun_prop

lemma continuousOn_gder {G : ℂ → ℂ} (hr : ContDiff ℝ 1 r) (hK : IsClosed K)
    (hG : DifferentiableOn ℂ G Kᶜ) {J : Set ℝ}
    (hJ : ∀ s ∈ J, ∀ θ, Hmap r R₀ s θ ∈ Kᶜ) :
    ContinuousOn (fun p : ℝ × ℝ => gder G r R₀ p.1 p.2) (J ×ˢ univ) := by
  have hrc := hr.continuous
  have hdr : Continuous (deriv r) := hr.continuous_deriv le_rfl
  have hHc := continuous_Hmap (R₀ := R₀) hr
  have hmaps : MapsTo (fun p : ℝ × ℝ => Hmap r R₀ p.1 p.2) (J ×ˢ univ) Kᶜ :=
    fun p hp => hJ p.1 hp.1 p.2
  have hG0 : ContinuousOn G Kᶜ := hG.continuousOn
  have hG1 : ContinuousOn (deriv G) Kᶜ := (hG.deriv hK.isOpen_compl).continuousOn
  have a := hG1.comp hHc.continuousOn hmaps
  have b := hG0.comp hHc.continuousOn hmaps
  have hs : Continuous fun p : ℝ × ℝ => Hs r R₀ p.2 := by unfold Hs; fun_prop
  have hth : Continuous fun p : ℝ × ℝ => Hth r R₀ p.1 p.2 := by unfold Hth; fun_prop
  have hsth : Continuous fun p : ℝ × ℝ => Hsth r R₀ p.2 := by unfold Hsth; fun_prop
  unfold gder
  exact ((a.mul hs.continuousOn).mul hth.continuousOn).add (b.mul hsth.continuousOn)

lemma hfun_two_pi {G : ℂ → ℂ} (hper : Function.Periodic r (2 * π)) (s : ℝ) :
    hfun G r R₀ s (2 * π) = hfun G r R₀ s 0 := by
  have hr2 : r (2 * π) = r 0 := by simpa using hper 0
  have e1 : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  have e0 : Complex.exp (((0 : ℝ) : ℂ) * I) = 1 := by simp
  unfold hfun Hmap Hs
  rw [hr2, e1, e0]

/-- The parameter integral `I(s) = ∫₀^{2π} G(H(s,θ)) ∂_θ H(s,θ) dθ` has derivative zero on `J`. -/
lemma hasDerivAt_paramIntegral {G : ℂ → ℂ} {J : Set ℝ} (hr : ContDiff ℝ 1 r)
    (hper : Function.Periodic r (2 * π)) (hK : IsClosed K) (hG : DifferentiableOn ℂ G Kᶜ)
    (hJo : IsOpen J) (hav : ∀ s ∈ J, ∀ θ, Hmap r R₀ s θ ∈ Kᶜ) {s₀ : ℝ} (hs₀ : s₀ ∈ J) :
    HasDerivAt (fun s => ∫ θ in (0 : ℝ)..2 * π, gfun G r R₀ s θ) 0 s₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJo s₀ hs₀
  have hSJ : closedBall s₀ (ε / 2) ⊆ J :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hSn : closedBall s₀ (ε / 2) ∈ 𝓝 s₀ := closedBall_mem_nhds s₀ (half_pos hε)
  have hcomp : IsCompact (closedBall s₀ (ε / 2) ×ˢ Icc (0 : ℝ) (2 * π)) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hcon := (continuousOn_gder (G := G) hr hK hG hav).mono
    (show closedBall s₀ (ε / 2) ×ˢ Icc (0 : ℝ) (2 * π) ⊆ J ×ˢ univ from
      fun p hp => ⟨hSJ hp.1, mem_univ _⟩)
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hcon
  have hHcont : ∀ s : ℝ, Continuous fun θ => Hmap r R₀ s θ := fun s =>
    (continuous_Hmap hr).comp (continuous_const.prodMk continuous_id)
  have hgcont : ∀ s ∈ J, Continuous fun θ => gfun G r R₀ s θ := by
    intro s hs
    have hrc := hr.continuous
    have hdr : Continuous (deriv r) := hr.continuous_deriv le_rfl
    have h1 := hG.continuousOn.comp_continuous (hHcont s) (fun θ => hav s hs θ)
    have h2 : Continuous fun θ => Hth r R₀ s θ := by unfold Hth; fun_prop
    exact h1.mul h2
  have hdcont : Continuous fun θ => gder G r R₀ s₀ θ := by
    have hc := continuousOn_gder (G := G) hr hK hG hav
    have hs : Continuous fun θ : ℝ => (s₀, θ) := by fun_prop
    have h3 := hc.comp_continuous hs (fun θ => (⟨hs₀, mem_univ θ⟩ : (s₀, θ) ∈ J ×ˢ univ))
    exact h3
  have hmeas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (fun θ => gfun G r R₀ s θ)
      (volume.restrict (Ι (0 : ℝ) (2 * π))) :=
    Filter.mem_of_superset (hJo.mem_nhds hs₀) fun s hs => (hgcont s hs).aestronglyMeasurable
  have hbd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) (2 * π) →
      ∀ x ∈ closedBall s₀ (ε / 2), ‖gder G r R₀ x t‖ ≤ B := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le Real.two_pi_pos.le] at ht
    exact hB (x, t) ⟨hx, ⟨ht.1.le, ht.2⟩⟩
  have hdf : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) (2 * π) →
      ∀ x ∈ closedBall s₀ (ε / 2), HasDerivAt (fun s => gfun G r R₀ s t) (gder G r R₀ x t) x :=
    Filter.Eventually.of_forall fun t _ x hx => hasDerivAt_gfun_s hK hG (hav x (hSJ hx) t)
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 2 * π) (F := fun s θ => gfun G r R₀ s θ)
    (F' := fun s θ => gder G r R₀ s θ) (bound := fun _ => B) hSn hmeas
    ((hgcont s₀ hs₀).intervalIntegrable _ _) hdcont.aestronglyMeasurable hbd
    intervalIntegrable_const hdf
  obtain ⟨hint, hder⟩ := hmain
  have hzero : ∫ θ in (0 : ℝ)..2 * π, gder G r R₀ s₀ θ = 0 := by
    rw [integral_eq_sub_of_hasDerivAt
      (f := fun θ => hfun G r R₀ s₀ θ)
      (fun θ _ => hasDerivAt_hfun_th hr hK hG (hav s₀ hs₀ θ)) hint,
      hfun_two_pi hper, sub_self]
  rwa [hzero] at hder

/-- **Homotopy invariance** ([B, Theorem thm:homotopy]). -/
theorem homotopy_invariance {G : ℂ → ℂ} {J : Set ℝ} (hr : ContDiff ℝ 1 r)
    (hper : Function.Periodic r (2 * π)) (hK : IsClosed K) (hG : DifferentiableOn ℂ G Kᶜ)
    (hJo : IsOpen J) (hJc : IsPreconnected J) (h0 : (0 : ℝ) ∈ J) (h1 : (1 : ℝ) ∈ J)
    (hav : ∀ s ∈ J, ∀ θ, Hmap r R₀ s θ ∈ Kᶜ) :
    (∮ z in C(0, R₀), G z) =
      ∫ θ in (0 : ℝ)..2 * π, G (polarLoop r θ) * deriv (polarLoop r) θ := by
  have hkey := hJo.is_const_of_deriv_eq_zero hJc
    (f := fun s => ∫ θ in (0 : ℝ)..2 * π, gfun G r R₀ s θ)
    (fun s hs => (hasDerivAt_paramIntegral hr hper hK hG hJo hav hs).differentiableAt
      |>.differentiableWithinAt)
    (fun s hs => (hasDerivAt_paramIntegral hr hper hK hG hJo hav hs).deriv) h0 h1
  have e0 : (∮ z in C(0, R₀), G z) = ∫ θ in (0 : ℝ)..2 * π, gfun G r R₀ 0 θ := by
    unfold circleIntegral
    refine integral_congr fun θ _ => ?_
    have hH0 : Hmap r R₀ 0 θ = circleMap 0 R₀ θ := by simp [Hmap, circleMap]
    have hT0 : Hth r R₀ 0 θ = circleMap 0 R₀ θ * I := by
      rw [← hH0]; unfold Hth Hmap; push_cast; ring
    show _ • _ = _
    unfold gfun
    rw [hH0, hT0, deriv_circleMap, smul_eq_mul, mul_comm]
  have e1 : (∫ θ in (0 : ℝ)..2 * π, gfun G r R₀ 1 θ) =
      ∫ θ in (0 : ℝ)..2 * π, G (polarLoop r θ) * deriv (polarLoop r) θ := by
    refine integral_congr fun θ _ => ?_
    unfold gfun
    rw [polarLoop_eq_Hmap 1 rfl θ, (hasDerivAt_polarLoop (R₀ := R₀) hr θ).deriv]
  rw [e0, hkey, e1]

end PartA2

/-! ### Part B: the radius function -/

section PartB

/-- `|e^{iθ} - e|²` as a trigonometric polynomial in `θ`. -/
def dsq (e : ℂ) (θ : ℝ) : ℝ := (Real.cos θ - e.re) ^ 2 + (Real.sin θ - e.im) ^ 2

lemma dsq_eq (e : ℂ) (θ : ℝ) : dsq e θ = ‖Complex.exp (θ * I) - e‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [dsq, Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- The bump `b_e(θ) = χ(2 - |e^{iθ} - e|²/σ²)`. -/
def bump (σ : ℝ) (e : ℂ) (θ : ℝ) : ℝ := Real.smoothTransition (2 - dsq e θ / σ ^ 2)

/-- The radius function `r = ε + ∑_e ℓ_e b_e`. -/
def radius (E : Finset ℂ) (ℓ : ℂ → ℝ) (ε σ : ℝ) (θ : ℝ) : ℝ :=
  ε + ∑ e ∈ E, ℓ e * bump σ e θ

lemma contDiff_dsq (e : ℂ) : ContDiff ℝ 1 (dsq e) := by
  unfold dsq
  have h1 : ContDiff ℝ 1 Real.cos := Real.contDiff_cos
  have h2 : ContDiff ℝ 1 Real.sin := Real.contDiff_sin
  exact ((h1.sub contDiff_const).pow 2).add ((h2.sub contDiff_const).pow 2)

lemma contDiff_bump (σ : ℝ) (e : ℂ) : ContDiff ℝ 1 (bump σ e) := by
  unfold bump
  have h : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  exact h.comp (contDiff_const.sub ((contDiff_dsq e).div_const _))

lemma contDiff_radius (E : Finset ℂ) (ℓ : ℂ → ℝ) (ε σ : ℝ) :
    ContDiff ℝ 1 (radius E ℓ ε σ) := by
  unfold radius
  refine contDiff_const.add ?_
  exact ContDiff.sum fun e _ => contDiff_const.mul (contDiff_bump σ e)

lemma dsq_periodic (e : ℂ) : Function.Periodic (dsq e) (2 * π) := by
  intro θ
  simp [dsq]

lemma radius_periodic (E : Finset ℂ) (ℓ : ℂ → ℝ) (ε σ : ℝ) :
    Function.Periodic (radius E ℓ ε σ) (2 * π) := by
  intro θ
  simp only [radius, bump, dsq_periodic _ θ]

lemma bump_nonneg (σ : ℝ) (e : ℂ) (θ : ℝ) : 0 ≤ bump σ e θ := Real.smoothTransition.nonneg _

lemma bump_le_one (σ : ℝ) (e : ℂ) (θ : ℝ) : bump σ e θ ≤ 1 := Real.smoothTransition.le_one _

lemma dsq_lt_of_bump_pos {σ : ℝ} (hσ : 0 < σ) {e : ℂ} {θ : ℝ} (h : 0 < bump σ e θ) :
    dsq e θ < 2 * σ ^ 2 := by
  have h1 : ¬ (2 - dsq e θ / σ ^ 2 ≤ 0) := fun h0 => by
    have := Real.smoothTransition.zero_of_nonpos h0
    unfold bump at h
    linarith
  have h1' := not_le.1 h1
  have h2 : dsq e θ / σ ^ 2 < 2 := by linarith
  rw [div_lt_iff₀ (by positivity)] at h2
  linarith

lemma bump_eq_one_of_dsq_le {σ : ℝ} (hσ : 0 < σ) {e : ℂ} {θ : ℝ} (h : dsq e θ ≤ σ ^ 2) :
    bump σ e θ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : dsq e θ / σ ^ 2 ≤ 1 := by rwa [div_le_one (by positivity)]
  linarith

lemma norm_lt_of_dsq_lt {σ : ℝ} (hσ : 0 < σ) {e : ℂ} {θ : ℝ} (h : dsq e θ < 2 * σ ^ 2) :
    ‖Complex.exp (θ * I) - e‖ < 2 * σ := by
  rw [dsq_eq] at h
  by_contra hc
  have hc' := not_lt.1 hc
  nlinarith [norm_nonneg (Complex.exp (θ * I) - e)]

/-- At most one bump is active at each angle. -/
lemma eq_of_bump_pos {E : Finset ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hsep : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → 3 * σ ≤ ‖e - e'‖) {e e' : ℂ} (he : e ∈ E)
    (he' : e' ∈ E) {θ : ℝ} (h : 0 < bump σ e θ) (h' : 0 < bump σ e' θ) : e = e' := by
  by_contra hne
  have h3 := hsep e he e' he' hne
  have ha := dsq_lt_of_bump_pos hσ h
  have hb := dsq_lt_of_bump_pos hσ h'
  rw [dsq_eq] at ha hb
  set z := Complex.exp (θ * I)
  have htri : ‖e - e'‖ ≤ ‖z - e‖ + ‖z - e'‖ := by
    calc ‖e - e'‖ = ‖(z - e') - (z - e)‖ := by congr 1; ring
      _ ≤ ‖z - e'‖ + ‖z - e‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have h4 : 3 * σ ≤ ‖z - e‖ + ‖z - e'‖ := h3.trans htri
  have h5 : (3 * σ) ^ 2 ≤ (‖z - e‖ + ‖z - e'‖) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
  nlinarith [sq_nonneg (‖z - e‖ - ‖z - e'‖)]

lemma sum_eq_of_active {E : Finset ℂ} {σ : ℝ} (ℓ : ℂ → ℝ) (hσ : 0 < σ)
    (hsep : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → 3 * σ ≤ ‖e - e'‖) {e₀ : ℂ} (he₀ : e₀ ∈ E) {θ : ℝ}
    (h : 0 < bump σ e₀ θ) :
    ∑ e ∈ E, ℓ e * bump σ e θ = ℓ e₀ * bump σ e₀ θ := by
  refine Finset.sum_eq_single_of_mem e₀ he₀ fun e he hne => ?_
  have : bump σ e θ = 0 := by
    by_contra hc
    exact hne (eq_of_bump_pos hσ hsep he he₀
      (lt_of_le_of_ne (bump_nonneg _ _ _) (Ne.symm hc)) h)
  rw [this, mul_zero]

lemma sum_eq_zero_of_inactive {E : Finset ℂ} {σ : ℝ} (ℓ : ℂ → ℝ) {θ : ℝ}
    (h : ¬ ∃ e ∈ E, 0 < bump σ e θ) : ∑ e ∈ E, ℓ e * bump σ e θ = 0 := by
  refine Finset.sum_eq_zero fun e he => ?_
  have : bump σ e θ = 0 :=
    le_antisymm (not_lt.1 fun hc => h ⟨e, he, hc⟩) (bump_nonneg _ _ _)
  rw [this, mul_zero]

lemma radius_bounds {E : Finset ℂ} {σ : ℝ} (ℓ : ℂ → ℝ) (ε L : ℝ) (hσ : 0 < σ)
    (hsep : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → 3 * σ ≤ ‖e - e'‖) (hℓ0 : ∀ e ∈ E, 0 ≤ ℓ e)
    (hℓL : ∀ e ∈ E, ℓ e ≤ L) (hL : 0 ≤ L) (θ : ℝ) :
    ε ≤ radius E ℓ ε σ θ ∧ radius E ℓ ε σ θ ≤ ε + L := by
  unfold radius
  by_cases h : ∃ e ∈ E, 0 < bump σ e θ
  · obtain ⟨e₀, he₀, hb⟩ := h
    rw [sum_eq_of_active ℓ hσ hsep he₀ hb]
    have h1 := bump_nonneg σ e₀ θ
    have h2 := bump_le_one σ e₀ θ
    have h3 := hℓ0 e₀ he₀
    have h4 := hℓL e₀ he₀
    constructor <;> nlinarith
  · rw [sum_eq_zero_of_inactive ℓ h]
    constructor <;> linarith

lemma radius_eq_of_close {E : Finset ℂ} {σ : ℝ} (ℓ : ℂ → ℝ) (ε : ℝ) (hσ : 0 < σ)
    (hsep : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → 3 * σ ≤ ‖e - e'‖) {e₀ : ℂ} (he₀ : e₀ ∈ E) {θ : ℝ}
    (h : dsq e₀ θ ≤ σ ^ 2) : radius E ℓ ε σ θ = ε + ℓ e₀ := by
  have hb := bump_eq_one_of_dsq_le hσ h
  unfold radius
  rw [sum_eq_of_active ℓ hσ hsep he₀ (by rw [hb]; exact one_pos), hb, mul_one]

/-- The finite set `E` of directions of the nonzero vertices, with `ℓ e` the length of the longest
segment in direction `e`. -/
lemma exists_direction_data (V : Multiset ℂ) :
    ∃ (E : Finset ℂ) (ℓ : ℂ → ℝ),
      (∀ e ∈ E, 0 < ℓ e ∧ ∃ v ∈ V, ‖v‖ = ℓ e ∧ v = (ℓ e : ℂ) * e) ∧
      (∀ e ∈ E, ∀ v ∈ V, v = (‖v‖ : ℂ) * e → ‖v‖ ≤ ℓ e) ∧
      (∀ v ∈ V, v ≠ 0 → ∃ e ∈ E, v = (‖v‖ : ℂ) * e) := by
  classical
  let S : ℂ → Finset ℂ := fun e => V.toFinset.filter (fun v => v = (‖v‖ : ℂ) * e)
  refine ⟨(V.toFinset.filter (· ≠ 0)).image (fun v => v / (‖v‖ : ℂ)),
    fun e => (((S e).sup fun v => ‖v‖₊ : NNReal) : ℝ), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨v₁, hv₁, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hv₁V, hv₁0⟩ := Finset.mem_filter.1 hv₁
    have hn : (‖v₁‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv₁0
    have hv₁S : v₁ ∈ S (v₁ / (‖v₁‖ : ℂ)) := by
      refine Finset.mem_filter.2 ⟨hv₁V, ?_⟩
      field_simp
    obtain ⟨v, hvS, hsup⟩ := Finset.exists_mem_eq_sup (S (v₁ / (‖v₁‖ : ℂ))) ⟨v₁, hv₁S⟩
      (fun v => ‖v‖₊)
    obtain ⟨hvV, hveq⟩ := Finset.mem_filter.1 hvS
    have hℓ : (((S (v₁ / (‖v₁‖ : ℂ))).sup fun v => ‖v‖₊ : NNReal) : ℝ) = ‖v‖ := by
      rw [hsup]; simp
    have hle : ‖v₁‖ ≤ (((S (v₁ / (‖v₁‖ : ℂ))).sup fun v => ‖v‖₊ : NNReal) : ℝ) := by
      have := Finset.le_sup (f := fun v => ‖v‖₊) hv₁S
      exact_mod_cast this
    refine ⟨lt_of_lt_of_le (norm_pos_iff.2 hv₁0) hle, v, Multiset.mem_toFinset.1 hvV, ?_, ?_⟩
    · exact hℓ.symm
    · beta_reduce; rw [hℓ]; exact hveq
  · intro e _ v hv hve
    have hvS : v ∈ S e := Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hv, hve⟩
    have := Finset.le_sup (f := fun v => ‖v‖₊) hvS
    exact_mod_cast this
  · intro v hv hv0
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
    refine ⟨v / (‖v‖ : ℂ), Finset.mem_image.2 ⟨v, Finset.mem_filter.2
      ⟨Multiset.mem_toFinset.2 hv, hv0⟩, rfl⟩, ?_⟩
    field_simp

/-- A small `σ` separating the finitely many directions. -/
lemma exists_sep (E : Finset ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ σ : ℝ, 0 < σ ∧ σ < c ∧ ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → 3 * σ ≤ ‖e - e'‖ := by
  classical
  set D := (E ×ˢ E).filter (fun p : ℂ × ℂ => p.1 ≠ p.2) with hD
  have h2 : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ p ∈ D, 3 * σ < ‖p.1 - p.2‖ :=
    (Filter.eventually_all_finset D).2 fun p hp =>
      (continuous_const.mul continuous_id : Continuous fun σ : ℝ => 3 * σ).continuousAt.eventually_lt
        continuousAt_const (by
          simpa using norm_pos_iff.2 (sub_ne_zero.2 (Finset.mem_filter.1 hp).2))
  have h3 : ∀ᶠ σ in 𝓝[>] (0 : ℝ), 0 < σ ∧ σ < c ∧ ∀ p ∈ D, 3 * σ < ‖p.1 - p.2‖ :=
    (eventually_mem_nhdsWithin : ∀ᶠ σ in 𝓝[>] (0 : ℝ), σ ∈ Ioi (0 : ℝ)).and
      (((eventually_lt_nhds hc).and h2).filter_mono nhdsWithin_le_nhds)
  obtain ⟨σ, hσ, hσc, hall⟩ := h3.exists
  refine ⟨σ, hσ, hσc, fun e he e' he' hne => ?_⟩
  exact (hall (e, e') (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨he, he'⟩, hne⟩)).le

end PartB

section Avoid

/-- The union of the segments `[0, v]`, `v ∈ V`. -/
def hedge (V : Multiset ℂ) : Set ℂ := ⋃ v ∈ V, segment ℝ (0 : ℂ) v

lemma mem_hedge {V : Multiset ℂ} {z : ℂ} : z ∈ hedge V ↔ ∃ v ∈ V, z ∈ segment ℝ (0 : ℂ) v := by
  simp [hedge]

/-- [B, Lemma lem:avoid] The homotopy avoids the hedgehog. -/
lemma Hmap_not_mem_hedge {V : Multiset ℂ} {r : ℝ → ℝ} {R₀ ε : ℝ} (hε : 0 < ε) (hR₀ : 0 < R₀)
    (hlb : ∀ θ, ε ≤ r θ) (hub : ∀ θ, r θ ≤ R₀)
    (hspike : ∀ v ∈ V, ∀ θ : ℝ, v = (‖v‖ : ℂ) * Complex.exp (θ * I) → ε + ‖v‖ ≤ r θ)
    {s : ℝ} (hs : s < 1 + ε / (2 * R₀)) (θ : ℝ) :
    Hmap r R₀ s θ ∉ hedge V := by
  intro hmem
  obtain ⟨v, hvV, hseg⟩ := mem_hedge.1 hmem
  rw [segment_eq_image'] at hseg
  obtain ⟨t, ⟨ht0, ht1⟩, hteq⟩ := hseg
  set ρ : ℝ := R₀ + s * (r θ - R₀) with hρ
  have hH : Hmap r R₀ s θ = (ρ : ℂ) * Complex.exp (θ * I) := by
    simp [Hmap, hρ]
  have hρgt : r θ - ε / 2 < ρ := by
    have h1 : (s - 1) * R₀ < ε / 2 := by
      have := (lt_div_iff₀ (by positivity : 0 < 2 * R₀)).1 (by linarith : s - 1 < ε / (2 * R₀))
      linarith
    have h2 : 0 ≤ R₀ - r θ := by linarith [hub θ]
    have h3 : r θ ≤ R₀ := hub θ
    have hr0 : 0 ≤ r θ := le_trans hε.le (hlb θ)
    rcases le_or_gt s 1 with h | h
    · have : 0 ≤ (1 - s) * (R₀ - r θ) := mul_nonneg (by linarith) h2
      simp only [hρ]; nlinarith
    · have h4 : (s - 1) * (R₀ - r θ) ≤ (s - 1) * R₀ :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      simp only [hρ]; nlinarith
  have hρpos : 0 < ρ := by linarith [hlb θ]
  have hteq' : (t : ℂ) * v = (ρ : ℂ) * Complex.exp (θ * I) := by
    rw [← hH, ← hteq]
    simp [Algebra.smul_def]
  have hnorm : t * ‖v‖ = ρ := by
    have := congrArg norm hteq'
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_pos hρpos] at this
    exact this
  have htpos : 0 < t := by
    rcases ht0.eq_or_lt with h | h
    · rw [← h] at hnorm; linarith
    · exact h
  have hvpos : 0 < ‖v‖ := by
    by_contra hc
    have : ‖v‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [this] at hnorm; linarith
  have hvdir : v = (‖v‖ : ℂ) * Complex.exp (θ * I) := by
    have h1 : (t : ℂ) * v = (t : ℂ) * ((‖v‖ : ℂ) * Complex.exp (θ * I)) := by
      rw [hteq', ← hnorm]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast htpos.ne') h1
  have hsp := hspike v hvV θ hvdir
  nlinarith

end Avoid

section Near

/-- [B, Lemma lem:r (v)] The loop stays within `δ` of the hedgehog. -/
lemma exists_near_hedge {V : Multiset ℂ} {E : Finset ℂ} {ℓ : ℂ → ℝ} {ε σ δ L : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ / 4) (hσ : 0 < σ) (hσL : 8 * σ * (L + 1) ≤ δ)
    (hL : 0 ≤ L) (hsep : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → 3 * σ ≤ ‖e - e'‖)
    (hℓpos : ∀ e ∈ E, 0 < ℓ e) (hℓL : ∀ e ∈ E, ℓ e ≤ L)
    (hvert : ∀ e ∈ E, ∃ v ∈ V, v = (ℓ e : ℂ) * e) (h0 : (0 : ℂ) ∈ hedge V) (θ : ℝ) :
    ∃ Q ∈ hedge V, dist (polarLoop (radius E ℓ ε σ) θ) Q < δ := by
  set z : ℂ := Complex.exp (θ * I) with hz
  have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  by_cases h : ∃ e ∈ E, 0 < bump σ e θ
  · obtain ⟨e₀, he₀, hb⟩ := h
    have hbd := radius_bounds ℓ ε L hσ hsep (fun e he => (hℓpos e he).le) hℓL hL θ
    have hr : radius E ℓ ε σ θ = ε + ℓ e₀ * bump σ e₀ θ := by
      unfold radius; rw [sum_eq_of_active ℓ hσ hsep he₀ hb]
    have hb1 := bump_le_one σ e₀ θ
    have hb0 := bump_nonneg σ e₀ θ
    have hℓ0 := hℓpos e₀ he₀
    set r := radius E ℓ ε σ θ with hrdef
    set m := min r (ℓ e₀) with hm
    have hm0 : 0 ≤ m := le_min (by linarith) hℓ0.le
    have hmℓ : m ≤ ℓ e₀ := min_le_right _ _
    have hmr : m ≤ r := min_le_left _ _
    have hrm : r - m ≤ ε := by
      rcases le_total r (ℓ e₀) with h1 | h1
      · rw [hm, min_eq_left h1]; linarith
      · rw [hm, min_eq_right h1]; nlinarith
    have hQ : ((m : ℂ) * e₀) ∈ hedge V := by
      obtain ⟨v₀, hv₀V, hv₀⟩ := hvert e₀ he₀
      refine mem_hedge.2 ⟨v₀, hv₀V, ?_⟩
      rw [segment_eq_image']
      refine ⟨m / ℓ e₀, ⟨div_nonneg hm0 hℓ0.le, (div_le_one hℓ0).2 hmℓ⟩, ?_⟩
      have hn : (ℓ e₀ : ℂ) ≠ 0 := by exact_mod_cast hℓ0.ne'
      simp only [zero_add, sub_zero, Algebra.smul_def, hv₀]
      push_cast
      have := mul_inv_cancel₀ hn
      simp only [div_eq_mul_inv]
      linear_combination (e₀ * (m : ℂ)) * this
    refine ⟨_, hQ, ?_⟩
    have hdist : ‖z - e₀‖ < 2 * σ := norm_lt_of_dsq_lt hσ (dsq_lt_of_bump_pos hσ hb)
    have hdec : polarLoop (radius E ℓ ε σ) θ - (m : ℂ) * e₀ =
        ((r - m : ℝ) : ℂ) * z + (m : ℂ) * (z - e₀) := by
      unfold polarLoop; push_cast; ring
    rw [dist_eq_norm, hdec]
    calc ‖((r - m : ℝ) : ℂ) * z + (m : ℂ) * (z - e₀)‖
        ≤ ‖((r - m : ℝ) : ℂ) * z‖ + ‖(m : ℂ) * (z - e₀)‖ := norm_add_le _ _
      _ = (r - m) + m * ‖z - e₀‖ := by
          rw [norm_mul, norm_mul, hz1, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm0,
            abs_of_nonneg (by linarith)]; ring
      _ ≤ ε + L * (2 * σ) := by
          have : m * ‖z - e₀‖ ≤ L * (2 * σ) :=
            mul_le_mul (hmℓ.trans (hℓL e₀ he₀)) hdist.le (norm_nonneg _) hL
          linarith
      _ < δ := by nlinarith
  · refine ⟨0, h0, ?_⟩
    have hr : radius E ℓ ε σ θ = ε := by
      unfold radius; rw [sum_eq_zero_of_inactive ℓ h, add_zero]
    rw [dist_eq_norm, sub_zero]
    unfold polarLoop
    rw [hr, norm_mul, hz1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    linarith

end Near

section Main

lemma contDiff_polarLoop {r : ℝ → ℝ} (hr : ContDiff ℝ 1 r) : ContDiff ℝ 1 (polarLoop r) := by
  have hrc := hr.continuous
  have hdr : Continuous (deriv r) := hr.continuous_deriv le_rfl
  have hd : ∀ θ, HasDerivAt (polarLoop r) (Hth r 0 1 θ) θ := fun θ => hasDerivAt_polarLoop hr θ
  rw [contDiff_one_iff_deriv]
  refine ⟨fun θ => (hd θ).differentiableAt, ?_⟩
  have : deriv (polarLoop r) = fun θ => Hth r 0 1 θ := funext fun θ => (hd θ).deriv
  rw [this]
  unfold Hth
  fun_prop

lemma polarLoop_periodic {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) :
    Function.Periodic (polarLoop r) (2 * π) := by
  intro θ
  unfold polarLoop
  rw [hper θ]
  congr 1
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Auxiliary form of `exists_hedgehog_loop`.  [B, Corollary cor:contour] An explicit `C¹` loop around a hedgehog, inside any open
neighbourhood `O` of it and avoiding it, along which contour integrals of functions holomorphic off
the hedgehog equal the circle integral over `|z| = R₀`. -/
theorem exists_hedgehog_loop_aux (V : Multiset ℂ) (hV : V ≠ 0) {R R₀ : ℝ}
    (hR : ∀ v ∈ V, ‖v‖ < R) (hRR₀ : R < R₀) {O : Set ℂ} (hO : IsOpen O)
    (hKO : (⋃ v ∈ V, segment ℝ (0 : ℂ) v) ⊆ O) :
    ∃ Γ : ℝ → ℂ, ContDiff ℝ 1 Γ ∧ Function.Periodic Γ (2 * Real.pi) ∧
      (∀ θ, Γ θ ∈ O ∧ Γ θ ∉ (⋃ v ∈ V, segment ℝ (0 : ℂ) v) ∧ ‖Γ θ‖ ≤ R) ∧
      ∀ G : ℂ → ℂ, DifferentiableOn ℂ G (⋃ v ∈ V, segment ℝ (0 : ℂ) v)ᶜ →
        (∮ z in C(0, R₀), G z) = ∫ θ in (0 : ℝ)..2 * Real.pi, G (Γ θ) * deriv Γ θ := by
  change hedge V ⊆ O at hKO
  obtain ⟨v₁, hv₁⟩ := Multiset.exists_mem_of_ne_zero hV
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) (hR v₁ hv₁)
  have hR₀pos : 0 < R₀ := hRpos.trans hRR₀
  -- compactness
  have hseg : ∀ v : ℂ, IsCompact (segment ℝ (0 : ℂ) v) := fun v => by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hKc : IsCompact (hedge V) := by
    have : hedge V = ⋃ v ∈ V.toFinset, segment ℝ (0 : ℂ) v := by
      ext z; simp [hedge]
    rw [this]
    exact V.toFinset.isCompact_biUnion fun v _ => hseg v
  have h0 : (0 : ℂ) ∈ hedge V :=
    mem_hedge.2 ⟨v₁, hv₁, left_mem_segment ℝ _ _⟩
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hO hKO
  -- direction data
  obtain ⟨E, ℓ, hd1, hd2, hd3⟩ := exists_direction_data V
  obtain ⟨v₀, hv₀, hv₀max⟩ := Finset.exists_max_image V.toFinset (fun v => ‖v‖)
    ⟨v₁, Multiset.mem_toFinset.2 hv₁⟩
  set L : ℝ := ‖v₀‖ with hLdef
  have hv₀V : v₀ ∈ V := Multiset.mem_toFinset.1 hv₀
  have hLR : L < R := hR v₀ hv₀V
  have hL0 : 0 ≤ L := norm_nonneg _
  have hLmax : ∀ v ∈ V, ‖v‖ ≤ L := fun v hv => hv₀max v (Multiset.mem_toFinset.2 hv)
  have hℓpos : ∀ e ∈ E, 0 < ℓ e := fun e he => (hd1 e he).1
  have hℓL : ∀ e ∈ E, ℓ e ≤ L := by
    intro e he
    obtain ⟨v, hvV, hvn, -⟩ := (hd1 e he).2
    rw [← hvn]; exact hLmax v hvV
  have hvert : ∀ e ∈ E, ∃ v ∈ V, v = (ℓ e : ℂ) * e := by
    intro e he
    obtain ⟨v, hvV, -, hv⟩ := (hd1 e he).2
    exact ⟨v, hvV, hv⟩
  -- parameters
  set ε : ℝ := min (δ / 4) (R - L) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hεR : ε ≤ R - L := min_le_right _ _
  obtain ⟨σ, hσ, hσc, hsep⟩ := exists_sep E (c := δ / (8 * (L + 1))) (by positivity)
  have hσL : 8 * σ * (L + 1) ≤ δ := by
    have := (lt_div_iff₀ (by positivity : 0 < 8 * (L + 1))).1 hσc
    nlinarith
  set r : ℝ → ℝ := radius E ℓ ε σ with hrdef
  have hrC : ContDiff ℝ 1 r := contDiff_radius E ℓ ε σ
  have hrper : Function.Periodic r (2 * π) := radius_periodic E ℓ ε σ
  have hbd := radius_bounds ℓ ε L hσ hsep (fun e he => (hℓpos e he).le) hℓL hL0
  have hlb : ∀ θ, ε ≤ r θ := fun θ => (hbd θ).1
  have hubR : ∀ θ, r θ ≤ R := fun θ => by linarith [(hbd θ).2]
  have hubR₀ : ∀ θ, r θ ≤ R₀ := fun θ => (hubR θ).trans hRR₀.le
  have hspike : ∀ v ∈ V, ∀ θ : ℝ, v = (‖v‖ : ℂ) * Complex.exp (θ * I) →
      ε + ‖v‖ ≤ r θ := by
    intro v hv θ hvθ
    by_cases hv0 : v = 0
    · subst hv0; simpa using hlb θ
    · obtain ⟨e, he, hve⟩ := hd3 v hv hv0
      have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
      have hee : Complex.exp (θ * I) = e := mul_left_cancel₀ hn (hvθ.symm.trans hve)
      have hdsq : dsq e θ ≤ σ ^ 2 := by
        rw [dsq_eq, hee, sub_self, norm_zero]; nlinarith [sq_nonneg σ]
      have := radius_eq_of_close ℓ ε hσ hsep he hdsq
      have h2 := hd2 e he v hv hve
      show ε + ‖v‖ ≤ radius E ℓ ε σ θ
      rw [this]; linarith
  have hη : 0 < ε / (2 * R₀) := div_pos hε (by linarith)
  have hJ : ∀ θ, Hmap r R₀ 1 θ ∉ hedge V := fun θ =>
    Hmap_not_mem_hedge hε hR₀pos hlb hubR₀ hspike (by linarith) θ
  refine ⟨polarLoop r, contDiff_polarLoop hrC, polarLoop_periodic hrper, fun θ => ⟨?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨Q, hQ, hdist⟩ := exists_near_hedge (V := V) hε hεδ hσ hσL hL0 hsep hℓpos hℓL
      hvert h0 θ
    exact hthick (Metric.mem_thickening_iff.2 ⟨Q, hQ, hdist⟩)
  · rw [← polarLoop_eq_Hmap (R₀ := R₀) 1 rfl θ]; exact hJ θ
  · unfold polarLoop
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hε.le.trans (hlb θ))]
    exact hubR θ
  · intro G hG
    refine homotopy_invariance (J := Set.Ioo (-1) (1 + ε / (2 * R₀))) hrC hrper hKc.isClosed hG
      isOpen_Ioo isPreconnected_Ioo ?_ ?_ ?_
    · exact ⟨by norm_num, by linarith⟩
    · exact ⟨by norm_num, by linarith⟩
    · intro s hs θ
      exact Hmap_not_mem_hedge hε hR₀pos hlb hubR₀ hspike hs.2 θ

end Main

end Contour

/-- [Supplement B §2, Corollary cor:contour] An explicit C¹ loop around a hedgehog, inside any open
neighbourhood `O` of it and avoiding it, along which contour integrals of functions holomorphic off
the hedgehog equal the circle integral over `|z| = R₀`. -/
theorem exists_hedgehog_loop (V : Multiset ℂ) (hV : V ≠ 0) {R R₀ : ℝ} (hR : ∀ v ∈ V, ‖v‖ < R)
    (hRR₀ : R < R₀) {O : Set ℂ} (hO : IsOpen O) (hKO : (⋃ v ∈ V, segment ℝ (0 : ℂ) v) ⊆ O) :
    ∃ Γ : ℝ → ℂ, ContDiff ℝ 1 Γ ∧ Function.Periodic Γ (2 * Real.pi) ∧
      (∀ θ, Γ θ ∈ O ∧ Γ θ ∉ (⋃ v ∈ V, segment ℝ (0 : ℂ) v) ∧ ‖Γ θ‖ ≤ R) ∧
      ∀ G : ℂ → ℂ, DifferentiableOn ℂ G (⋃ v ∈ V, segment ℝ (0 : ℂ) v)ᶜ →
        (∮ z in C(0, R₀), G z) = ∫ θ in (0 : ℝ)..2 * Real.pi, G (Γ θ) * deriv Γ θ :=
  Contour.exists_hedgehog_loop_aux V hV hR hRR₀ hO hKO

end RestrictedPolynomials
