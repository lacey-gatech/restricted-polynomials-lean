module

public import RestrictedPolynomials.TrackB.AppBSetting

/-!
# Track B, Appendix B (part): the elementary parts of `soft_truncate_main`

The statements that do not depend on `AppBTrunc1`: the `T′`-split, the conversion of
the harsh bound into `5ρ^ξ`, the `√δ` first term, the telescoping, the remainder limit and the
geometric sum. Paper IV App. B (l. 8925-8970, 9385). All proof helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Main
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

theorem corr3_add_left {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (f f' : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 ν (f + f') g h = corr3 ν f g h + corr3 ν f' g h := by
  unfold corr3 FinProb.cexpect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.add_apply]
  ring

/-- eqs. `trunate5`, `trunate6` (l. 8962-8970, 9097-9106): `f = (f - T f) + (T f - E T f) +
E T f`, so `|E f T'g h| ≤ (I) + (VI) + (V)`. -/
theorem appB_main_split {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (Sm : Finset X) (ρ ξ : ℝ) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    ‖corr3 ν f (appTp (lawY ν) ρ g) h‖ ≤
      termI ν ρ ξ f g h + termV ν Sm ρ ξ f g h + termVI ν Sm ρ ξ f g h := by
  set Tf := tNE (lawX ν) (ρ ^ (1 + ξ)) f with hTf
  set ETf := s7EffNoiseOp (lawX ν) Sm (ρ ^ (1 - ξ)) Tf with hETf
  have hf : f = (f - Tf) + (Tf - ETf) + ETf := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h1 : corr3 ν f (appTp (lawY ν) ρ g) h =
      corr3 ν (f - Tf) (appTp (lawY ν) ρ g) h + corr3 ν (Tf - ETf) (appTp (lawY ν) ρ g) h
        + corr3 ν ETf (appTp (lawY ν) ρ g) h := by
    conv_lhs => rw [hf]
    rw [corr3_add_left, corr3_add_left]
  rw [h1]
  unfold termI termV termVI
  have e1 := norm_add₃_le (a := corr3 ν (f - Tf) (appTp (lawY ν) ρ g) h)
    (b := corr3 ν (Tf - ETf) (appTp (lawY ν) ρ g) h) (c := corr3 ν ETf (appTp (lawY ν) ρ g) h)
  linarith


/-- `#harsh-bound-to-power` (l. 9385): `4ρ^ξ + M₃(1+c′)^{-(ρ^{-(1-2ξ)})^{1-√ξ_H}}
≤ 5ρ^ξ` for `ρ ≤ δ₀`, `0 < ξ ≤ 1/100`; `δ₀` depends on `(M₃, c′, ξ, ξ_H)`. -/
theorem appB_harsh_bound_to_power {ξ ξH c' M₃ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 100)
    (hξH : 0 < ξH) (hξH1 : ξH < 1) (hc' : 0 < c') (hM : 0 ≤ M₃) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      4 * ρ ^ ξ + M₃ * (1 + c') ^ (-((ρ ^ (-(1 - 2 * ξ))) ^ (1 - Real.sqrt ξH))) ≤ 5 * ρ ^ ξ := by
  have hsq : Real.sqrt ξH < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  have hκ : 0 < (1 - 2 * ξ) * (1 - Real.sqrt ξH) :=
    mul_pos (by linarith) (by linarith)
  set κ := (1 - 2 * ξ) * (1 - Real.sqrt ξH) with hκdef
  set b := Real.log (1 + c') with hb
  have hb0 : 0 < b := Real.log_pos (by linarith)
  set p := ξ / κ with hp
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb0).const_mul M₃
  rw [mul_zero] at ht
  have hev : ∀ᶠ s : ℝ in Filter.atTop, M₃ * (s ^ p * Real.exp (-b * s)) < 1 :=
    ht.eventually (gt_mem_nhds one_pos)
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.1 hev
  set S := max S₀ 1 with hS
  have hS1 : 1 ≤ S := le_max_right _ _
  have hSpos : 0 < S := by linarith
  refine ⟨min 1 (S ^ (-(1 / κ))), lt_min one_pos (Real.rpow_pos_of_pos hSpos _), min_le_left _ _,
    fun ρ hρ hρδ => ?_⟩
  have hρ1 : ρ ≤ S ^ (-(1 / κ)) := hρδ.trans (min_le_right _ _)
  set s := (ρ ^ (-(1 - 2 * ξ))) ^ (1 - Real.sqrt ξH) with hs
  have hsκ : s = ρ ^ (-κ) := by
    rw [hs, ← Real.rpow_mul hρ.le, hκdef]; congr 1; ring
  have hsS : S ≤ s := by
    rw [hsκ]
    have := Real.rpow_le_rpow_of_nonpos hρ hρ1 (neg_nonpos.2 hκ.le)
    rw [← Real.rpow_mul hSpos.le] at this
    have e : -(1 / κ) * -κ = 1 := by field_simp
    rw [e, Real.rpow_one] at this
    exact this
  have hspos : 0 < s := lt_of_lt_of_le hSpos hsS
  have hsS0 : S₀ ≤ s := (le_max_left _ _).trans hsS
  have hkey := hS₀ s hsS0
  have hexp : (1 + c') ^ (-s) = Real.exp (-b * s) := by
    rw [Real.rpow_def_of_pos (by linarith), hb]; congr 1; ring
  have hρξ : ρ ^ ξ = (s ^ p)⁻¹ := by
    rw [hsκ, ← Real.rpow_mul hρ.le, ← Real.rpow_neg hρ.le]
    congr 1
    rw [hp]; field_simp
  have hspp : 0 < s ^ p := Real.rpow_pos_of_pos hspos _
  have : M₃ * (1 + c') ^ (-s) ≤ ρ ^ ξ := by
    rw [hexp, hρξ]
    have h1 : M₃ * Real.exp (-b * s) * s ^ p ≤ 1 := by
      have : M₃ * Real.exp (-b * s) * s ^ p = M₃ * (s ^ p * Real.exp (-b * s)) := by ring
      rw [this]; exact hkey.le
    calc M₃ * Real.exp (-b * s) = (M₃ * Real.exp (-b * s) * s ^ p) * (s ^ p)⁻¹ := by
          field_simp
      _ ≤ 1 * (s ^ p)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hspp.le)
      _ = (s ^ p)⁻¹ := one_mul _
  linarith


private theorem mp_expect_pi_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
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

private theorem mp_cl2sq_x {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (A : (ι → X) → ℂ) : cl2sq (lawX ν) A =
    ∑ t : ι → X × Y × Z, (ν.pi ι).prob t * ‖A (fun i => (t i).1)‖ ^ 2 :=
  mp_expect_pi_push ν (fun p => p.1) (fun x => ‖A x‖ ^ 2)

private theorem mp_cl2sq_y {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (A : (ι → Y) → ℂ) : cl2sq (lawY ν) A =
    ∑ t : ι → X × Y × Z, (ν.pi ι).prob t * ‖A (fun i => (t i).2.1)‖ ^ 2 :=
  mp_expect_pi_push ν (fun p => p.2.1) (fun x => ‖A x‖ ^ 2)

private theorem mp_corr3_bound {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
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
  rw [mp_cl2sq_x, mp_cl2sq_y]

private theorem mp_cl2norm_le_one {A : Type} [Fintype A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : FinProb A) (f : (ι → A) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) : cl2norm D f ≤ 1 := by
  unfold cl2norm
  rw [Real.sqrt_le_one]
  calc cl2sq D f ≤ ∑ x, (D.pi ι).prob x * 1 := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ((D.pi ι).nonneg x)
        have := hf x
        have h0 := norm_nonneg (f x)
        nlinarith
    _ = 1 := by simp [(D.pi ι).sum_eq_one]

/-- `#soft-split-g`, first assertion (l. 8925-8940): `|E f (T_{non-embed,1-δ} g) h| ≤ √δ` for
`1`-bounded `f, h` and `Stab_{1-δ}(g; ν_y) ≤ δ`, `0 < δ ≤ 1`. -/
theorem appB_first_term {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hs : (cstab (lawY ν) (1 - δ) g).re ≤ δ) :
    ‖corr3 ν f (tNE (lawY ν) δ g) h‖ ≤ Real.sqrt δ := by
  refine (mp_corr3_bound ν f _ h hh).trans ?_
  have h1 := mp_cl2norm_le_one (lawX ν) f hf
  have h2 : cl2norm (lawY ν) (tNE (lawY ν) δ g) ≤ Real.sqrt δ := by
    unfold cl2norm
    refine Real.sqrt_le_sqrt ?_
    rw [tNE_eq_cnoiseOp, cl2sq_cnoiseOp _ (by linarith)]
    refine le_trans ?_ hs
    have hmono := cstab_mono (lawY ν) (ρ := (1 - δ) ^ 2) (ρ' := 1 - δ) (by nlinarith)
      (by nlinarith) g
    exact (Complex.le_def.1 hmono).1
  calc cl2norm (lawX ν) f * cl2norm (lawY ν) (tNE (lawY ν) δ g) ≤
      1 * Real.sqrt δ :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) zero_le_one
    _ = Real.sqrt δ := one_mul _

/-- `#soft-split-g`, telescoping (eq. `trunate1`, finite form): `ρ_j = 1 - δ/2^j`. -/
theorem appB_split_telescope {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (δ : ℝ) (J : ℕ) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    ‖corr3 ν f g h‖ ≤ ‖corr3 ν f (tNE (lawY ν) δ g) h‖ +
      ∑ j ∈ range J, ‖corr3 ν f (appTp (lawY ν) (δ / 2 ^ j) g) h‖ +
      ‖corr3 ν f (g - tNE (lawY ν) (δ / 2 ^ J) g) h‖ := by
  set a : ℕ → ℂ := fun j => corr3 ν f (tNE (lawY ν) (δ / 2 ^ j) g) h with ha
  have hstep : ∀ j, corr3 ν f (appTp (lawY ν) (δ / 2 ^ j) g) h = a (j + 1) - a j := by
    intro j
    unfold appTp
    rw [corr3_sub_mid]
    have : δ / 2 ^ j / 2 = δ / 2 ^ (j + 1) := by rw [pow_succ]; field_simp
    rw [this]
  have hsum : ∑ j ∈ range J, corr3 ν f (appTp (lawY ν) (δ / 2 ^ j) g) h = a J - a 0 := by
    rw [Finset.sum_congr rfl fun j _ => hstep j]
    exact Finset.sum_range_sub a J
  have ha0 : a 0 = corr3 ν f (tNE (lawY ν) δ g) h := by
    simp [ha]
  have hmain : corr3 ν f g h = a 0 + ∑ j ∈ range J, corr3 ν f (appTp (lawY ν) (δ / 2 ^ j) g) h
      + corr3 ν f (g - tNE (lawY ν) (δ / 2 ^ J) g) h := by
    rw [hsum, corr3_sub_mid, ha0]
    have : a J = corr3 ν f (tNE (lawY ν) (δ / 2 ^ J) g) h := rfl
    rw [this]
    ring
  calc ‖corr3 ν f g h‖ ≤ ‖a 0‖ + ‖∑ j ∈ range J, corr3 ν f (appTp (lawY ν) (δ / 2 ^ j) g) h‖
        + ‖corr3 ν f (g - tNE (lawY ν) (δ / 2 ^ J) g) h‖ := by
        rw [hmain]; exact norm_add₃_le
    _ ≤ _ := by
        rw [ha0]
        gcongr
        exact norm_sum_le _ _

private theorem mp_cnoiseOp_one {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → A) → ℂ) : cnoiseOp D 1 g = g := by
  funext x
  unfold cnoiseOp noiseKernel
  have : ∀ y : ι → A, (∏ i, (1 * (if x i = y i then (1 : ℝ) else 0) + (1 - 1) * D.prob (y i)))
      = if x = y then 1 else 0 := by
    intro y
    simp only [sub_self, zero_mul, add_zero, one_mul]
    rw [Finset.prod_boole]
    simp [funext_iff]
  rw [Finset.sum_congr rfl fun y _ => by rw [this y]]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- the omitted limit `T_{non-embed,ρ_J} g → g` (of `#soft-split-g`; finite dimension):
for `1`-bounded `f, g, h` the remainder is eventually `≤ ε`. -/
theorem appB_remainder_small {ι : Type} [Fintype ι] [DecidableEq ι] (ν : FinProb (X × Y × Z))
    (δ : ℝ) (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ‖corr3 ν f (g - tNE (lawY ν) (δ / 2 ^ J) g) h‖ ≤ ε := by
  have _ := hf
  have _ := hh
  set F : ℝ → ℂ := fun t => corr3 ν f (g - cnoiseOp (lawY ν) (1 - t) g) h with hF
  have hcont : Continuous F := by
    have hc : ∀ (t : ℝ) (u : ι → Y), cnoiseOp (lawY ν) (1 - t) g u =
        ∑ y, ((∏ i, ((1 - t) * (if u i = y i then (1 : ℝ) else 0) +
          (1 - (1 - t)) * (lawY ν).prob (y i)) : ℝ) : ℂ) * g y := fun _ _ => rfl
    simp only [hF, corr3, FinProb.cexpect, Pi.sub_apply, hc]
    fun_prop
  have hF0 : F 0 = 0 := by
    simp only [hF, sub_zero, mp_cnoiseOp_one, sub_self]
    unfold corr3 FinProb.cexpect
    simp
  have hlim : Filter.Tendsto (fun J : ℕ => δ / 2 ^ J) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul δ
    rw [mul_zero] at this
    refine this.congr fun J => ?_
    rw [one_div_pow]; ring
  have h2 := (hcont.tendsto 0).comp hlim
  rw [hF0] at h2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h2 ε hε
  refine ⟨N, ?_⟩
  have := hN N le_rfl
  rw [dist_zero_right] at this
  simp only [Function.comp, hF] at this
  rw [tNE_eq_cnoiseOp]
  exact this.le

/-- `#sum-over-scales` (l. 8951-8956), abstract: `a_j ≤ M (δ/2^j)^η` gives
`Σ_{j<J} a_j ≤ M (1 - 2^{-η})^{-1} δ^η`. -/
theorem appB_geometric_sum {M δ η : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (hη : 0 < η) (a : ℕ → ℝ)
    (ha : ∀ j, a j ≤ M * (δ / 2 ^ j) ^ η) (J : ℕ) :
    ∑ j ∈ range J, a j ≤ M * (1 - (2 : ℝ) ^ (-η))⁻¹ * δ ^ η := by
  set q : ℝ := (2 : ℝ) ^ (-η) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ j : ℕ, (δ / 2 ^ j) ^ η = δ ^ η * q ^ j := by
    intro j
    have e : ((2 : ℝ) ^ j) ^ η = ((2 : ℝ) ^ η) ^ j := by
      rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    rw [Real.div_rpow hδ.le (by positivity), e, hq, Real.rpow_neg (by norm_num), inv_pow,
      div_eq_mul_inv]
  have hgeo : ∑ j ∈ range J, q ^ j ≤ (1 - q)⁻¹ := by
    rw [geom_sum_eq hq1.ne, div_le_iff_of_neg (by linarith)]
    have : 0 < q ^ J := pow_pos hq0 J
    have hne : 1 - q ≠ 0 := by linarith
    have e : (q - 1) * (1 - q)⁻¹ = -1 := by
      rw [show q - 1 = -(1 - q) by ring, neg_mul, mul_inv_cancel₀ hne]
    rw [mul_comm, e]
    linarith [this]
  calc ∑ j ∈ range J, a j ≤ ∑ j ∈ range J, M * (δ ^ η * q ^ j) :=
        Finset.sum_le_sum fun j _ => by rw [← hterm]; exact ha j
    _ = M * δ ^ η * ∑ j ∈ range J, q ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ M * δ ^ η * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo (mul_nonneg hM (Real.rpow_nonneg hδ.le _))
    _ = M * (1 - q)⁻¹ * δ ^ η := by ring

end Main

end TrackB
end RestrictedPolynomials
end
