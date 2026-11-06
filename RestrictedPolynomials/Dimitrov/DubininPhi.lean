module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import RestrictedPolynomials.Dimitrov.DubininZigzag
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The angular map `Φ` and the dissymmetrization (Supplement C, Lemma 6.2 and Prop. 6.3)

Source: Supplement C, Section 6 (`lem:Phi`, `prop:zigzag`); `rotation` lives in the root namespace.
-/

@[expose] public section

open MeasureTheory
open scoped Real

noncomputable section

namespace RestrictedPolynomials

namespace PhiAux

/-! ## Part A: the Lipschitz bound -/

theorem norm_exp_sub_exp_le (α β : ℝ) :
    ‖Complex.exp (α * Complex.I) - Complex.exp (β * Complex.I)‖ ≤ |α - β| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := α - β)
  have e : Complex.exp (α * Complex.I) - Complex.exp (β * Complex.I) =
      Complex.exp (β * Complex.I) * (Complex.exp (Complex.I * ((α - β : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa using h

theorem sq_norm_polar_sub (ρ ρ' a b : ℝ) :
    ‖(ρ : ℂ) * Complex.exp (a * Complex.I) - (ρ' : ℂ) * Complex.exp (b * Complex.I)‖ ^ 2 =
      (ρ - ρ') ^ 2 + 4 * ρ * ρ' * Real.sin ((a - b) / 2) ^ 2 := by
  have hc : Real.cos (a - b) = 1 - 2 * Real.sin ((a - b) / 2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq ((a - b) / 2)
    have := Real.cos_two_mul ((a - b) / 2)
    rw [show 2 * ((a - b) / 2) = a - b by ring] at this
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul,
    sub_zero, add_zero]
  rw [Real.cos_sub] at hc
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  linear_combination ρ ^ 2 * ha + ρ' ^ 2 * hb + (-2 * ρ * ρ') * hc

theorem chord {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {ρ ρ' a b : ℝ} (h0 : 0 ≤ ρ') (hle : ρ' ≤ ρ)
    (hab : |a - b| ≤ π) :
    ‖(ρ : ℂ) * Complex.exp (ψ a * Complex.I) - (ρ' : ℂ) * Complex.exp (ψ b * Complex.I)‖ ≤
      (1 + π / 2) *
        ‖(ρ : ℂ) * Complex.exp (a * Complex.I) - (ρ' : ℂ) * Complex.exp (b * Complex.I)‖ := by
  set D := ‖(ρ : ℂ) * Complex.exp (a * Complex.I) - (ρ' : ℂ) * Complex.exp (b * Complex.I)‖ with hD
  have hρ : 0 ≤ ρ := h0.trans hle
  -- first piece
  have h1 : ρ - ρ' ≤ D := by
    have := norm_sub_norm_le ((ρ : ℂ) * Complex.exp (a * Complex.I))
      ((ρ' : ℂ) * Complex.exp (b * Complex.I))
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hρ, Real.norm_of_nonneg h0] at this
    simpa using this
  -- second piece
  have h2 : ρ' * |a - b| ≤ π / 2 * D := by
    have hsq := sq_norm_polar_sub ρ ρ' a b
    rw [← hD] at hsq
    have hx : 0 ≤ |a - b| / 2 := by positivity
    have hx2 : |a - b| / 2 ≤ π / 2 := by linarith
    have hs := Real.mul_le_sin hx hx2
    have hsin : Real.sin ((a - b) / 2) ^ 2 = Real.sin (|a - b| / 2) ^ 2 := by
      rcases abs_cases (a - b) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, show -(a - b) / 2 = -((a - b) / 2) by ring, Real.sin_neg]; ring
    have hpi := Real.pi_pos
    have hlow : 2 / π * (|a - b| / 2) ≤ Real.sin (|a - b| / 2) := hs
    have hlow' : 0 ≤ 2 / π * (|a - b| / 2) := by positivity
    have hsq2 : (2 / π * (|a - b| / 2)) ^ 2 ≤ Real.sin ((a - b) / 2) ^ 2 := by
      rw [hsin]; exact pow_le_pow_left₀ hlow' hlow 2
    have hD2 : (2 * ρ' * |a - b| / π) ^ 2 ≤ D ^ 2 := by
      rw [hsq]
      have e : (2 * ρ' * |a - b| / π) ^ 2 = 4 * ρ' ^ 2 * (2 / π * (|a - b| / 2)) ^ 2 := by
        field_simp
        ring
      rw [e]
      have : ρ' ^ 2 ≤ ρ * ρ' := by nlinarith
      nlinarith [sq_nonneg (ρ - ρ'), mul_le_mul_of_nonneg_right this (sq_nonneg (2 / π * (|a - b| / 2))),
        mul_nonneg h0 hρ, sq_nonneg (2 / π * (|a - b| / 2)), mul_nonneg h0 (sq_nonneg (2 / π * (|a - b| / 2))),
        mul_nonneg (mul_nonneg h0 hρ) (sq_nonneg (Real.sin ((a - b) / 2)) )]
    have hD0 : 0 ≤ D := norm_nonneg _
    have := abs_le_of_sq_le_sq' hD2 hD0
    have h3 : 2 * ρ' * |a - b| / π ≤ D := this.2
    rw [div_le_iff₀ hpi] at h3
    nlinarith
  -- assemble
  have e : (ρ : ℂ) * Complex.exp (ψ a * Complex.I) - (ρ' : ℂ) * Complex.exp (ψ b * Complex.I) =
      ((ρ - ρ' : ℝ) : ℂ) * Complex.exp (ψ a * Complex.I) +
        (ρ' : ℂ) * (Complex.exp (ψ a * Complex.I) - Complex.exp (ψ b * Complex.I)) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg h0, mul_one, Real.norm_of_nonneg (sub_nonneg.2 hle)]
  have h4 := norm_exp_sub_exp_le (ψ a) (ψ b)
  have h5 : |ψ a - ψ b| ≤ |a - b| := by
    have := hψ.dist_le_mul a b
    simpa [Real.dist_eq] using this
  have h6 : ρ' * ‖Complex.exp (ψ a * Complex.I) - Complex.exp (ψ b * Complex.I)‖ ≤
      ρ' * |a - b| := mul_le_mul_of_nonneg_left (h4.trans h5) h0
  nlinarith

theorem phiMap_norm (ψ : ℝ → ℝ) (z : ℂ) : ‖phiMap ψ z‖ = ‖z‖ := by
  simp [phiMap, Complex.norm_exp_ofReal_mul_I]

theorem phiMap_zero (ψ : ℝ → ℝ) : phiMap ψ 0 = 0 := by simp [phiMap]

/-- Two polar representations of a nonzero number differ by an integer multiple of `2π`. -/
theorem exists_int_arg {z : ℂ} (hz0 : z ≠ 0) {t : ℝ}
    (hz : z = ‖z‖ * Complex.exp (t * Complex.I)) :
    ∃ n : ℤ, Complex.arg z = t + n * (2 * π) := by
  have h1 : ((‖z‖ : ℝ) : ℂ) * Complex.exp (Complex.arg z * Complex.I) = z :=
    Complex.norm_mul_exp_arg_mul_I z
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz0
  have h2 : Complex.exp (Complex.arg z * Complex.I) = Complex.exp (t * Complex.I) := by
    apply mul_left_cancel₀ hn
    rw [h1]; exact hz
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simpa using this

theorem phiMap_polar {ψ : ℝ → ℝ} (hper : Function.Periodic ψ (2 * π)) {z : ℂ} (hz0 : z ≠ 0)
    {t : ℝ} (hz : z = ‖z‖ * Complex.exp (t * Complex.I)) :
    phiMap ψ z = ‖z‖ * Complex.exp (ψ t * Complex.I) := by
  obtain ⟨n, hn⟩ := exists_int_arg hz0 hz
  unfold phiMap
  rw [hn, hper.int_mul n t]

theorem lipschitz_phiMap {ψ : ℝ → ℝ} (hper : Function.Periodic ψ (2 * π))
    (hψ : LipschitzWith 1 ψ) : LipschitzWith (Real.toNNReal (1 + π / 2)) (phiMap ψ) := by
  have hpi := Real.pi_pos
  have key : ∀ z w : ℂ, ‖w‖ ≤ ‖z‖ →
      dist (phiMap ψ z) (phiMap ψ w) ≤ (1 + π / 2) * dist z w := by
    intro z w hzw
    set a0 := Complex.arg z
    set b0 := Complex.arg w
    set n : ℤ := round ((a0 - b0) / (2 * π)) with hn
    set b : ℝ := b0 + n * (2 * π) with hb
    have hab : |a0 - b| ≤ π := by
      have := abs_sub_round ((a0 - b0) / (2 * π))
      have e : a0 - b = (2 * π) * ((a0 - b0) / (2 * π) - n) := by
        rw [hb]; field_simp; ring
      rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
      nlinarith
    have hzr : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (a0 * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    have hwr0 : w = ((‖w‖ : ℝ) : ℂ) * Complex.exp (b0 * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I w).symm
    have hexp : Complex.exp (b * Complex.I) = Complex.exp (b0 * Complex.I) := by
      rw [hb]; push_cast
      rw [add_mul, Complex.exp_add]
      have : (n : ℂ) * (2 * π) * Complex.I = n * (2 * π * Complex.I) := by ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hwr : w = ((‖w‖ : ℝ) : ℂ) * Complex.exp (b * Complex.I) := by rw [hexp]; exact hwr0
    have hψb : ψ b = ψ b0 := hper.int_mul n b0
    have hPz : phiMap ψ z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (ψ a0 * Complex.I) := rfl
    have hPw : phiMap ψ w = ((‖w‖ : ℝ) : ℂ) * Complex.exp (ψ b * Complex.I) := by
      rw [hψb]; rfl
    rw [dist_eq_norm, dist_eq_norm, hPz, hPw]
    conv_rhs => rw [hzr, hwr]
    exact chord hψ (norm_nonneg _) hzw hab
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  have hK : ((Real.toNNReal (1 + π / 2) : NNReal) : ℝ) = 1 + π / 2 :=
    Real.coe_toNNReal _ (by positivity)
  rw [hK]
  rcases le_total ‖w‖ ‖z‖ with h | h
  · exact key z w h
  · rw [dist_comm (phiMap ψ z), dist_comm z]; exact key w z h

theorem phiMap_mem_starSet {N : ℕ} (hN : 1 ≤ N) {θ : Fin N → ℝ} {ψ : ℝ → ℝ}
    (hper : Function.Periodic ψ (2 * π)) (hθ0 : ∀ k, ψ (θ k) = 0) {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hzs : z ∈ spikes R θ) : phiMap ψ z ∈ starSet N R := by
  have hRN : 0 ≤ R ^ N := pow_nonneg hR N
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hzs
  rw [segment_eq_image'] at hk
  obtain ⟨t, ⟨ht0, ht1⟩, hzeq⟩ := hk
  have hzval : z = ((t * R : ℝ) : ℂ) * Complex.exp ((θ k : ℂ) * Complex.I) := by
    rw [← hzeq]; simp [Complex.real_smul]; ring
  by_cases hz0 : z = 0
  · rw [hz0, phiMap_zero]
    refine ⟨0, ⟨le_rfl, hRN⟩, ?_⟩
    simp [zero_pow (by omega : N ≠ 0)]
  · clear hzeq hzs
    have htR : 0 ≤ t * R := mul_nonneg ht0 hR
    have hnorm : ‖z‖ = t * R := by
      rw [hzval, norm_mul, Complex.norm_exp_ofReal_mul_I]
      · simp [abs_of_nonneg ht0, abs_of_nonneg hR]
    have hpolar : z = ‖z‖ * Complex.exp ((θ k : ℝ) * Complex.I) := by
      rw [hnorm]; exact hzval
    rw [phiMap_polar hper hz0 hpolar, hθ0 k]
    refine ⟨‖z‖ ^ N, ⟨by positivity, ?_⟩, ?_⟩
    · rw [hnorm]
      exact pow_le_pow_left₀ htR (by nlinarith) N
    · simp

/-! ## Part B: the legs tile one period -/

/-- `Tile a b L`: the legs of `L` are consecutive, each nondegenerate, from `a` to `b`. -/
def Tile : ℝ → ℝ → List Leg → Prop
  | a, b, [] => a = b
  | a, b, l :: L => l.lo = a ∧ l.lo < l.hi ∧ Tile l.hi b L

theorem tile_of_chain : ∀ (L : List Leg) (a b : ℝ), (∀ l ∈ L, l.lo < l.hi) →
    L.IsChain (fun x y => x.hi = y.lo) → (L.head?.map Leg.lo) = some a →
    (L.getLast?.map Leg.hi) = some b → Tile a b L
  | [], a, b, _, _, h, _ => by simp at h
  | [l], a, b, hlt, _, hh, hl => by
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hl
      exact ⟨hh, hlt l (by simp), hl⟩
  | l :: l' :: rest, a, b, hlt, hc, hh, hl => by
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hh
      rw [List.isChain_cons_cons] at hc
      refine ⟨hh, hlt l (by simp), ?_⟩
      refine tile_of_chain (l' :: rest) l.hi b (fun x hx => hlt x (by simp_all)) hc.2 ?_ ?_
      · simp [hc.1]
      · simpa [List.getLast?_cons_cons] using hl

theorem tile_le : ∀ (L : List Leg) (a b : ℝ), Tile a b L → a ≤ b
  | [], a, b, h => h.le
  | l :: L, a, b, h => by
      obtain ⟨h1, h2, h3⟩ := h
      have := tile_le L l.hi b h3
      linarith

theorem tile_bounds : ∀ (L : List Leg) (a b : ℝ), Tile a b L → ∀ l ∈ L, a ≤ l.lo ∧ l.hi ≤ b
  | [], a, b, h, l, hl => by simp at hl
  | l₀ :: L, a, b, h, l, hl => by
      obtain ⟨h1, h2, h3⟩ := h
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨h1.ge, tile_le L _ b h3⟩
      · have := tile_bounds L l₀.hi b h3 l hl
        exact ⟨by linarith [this.1], this.2⟩

theorem tile_count : ∀ (L : List Leg) (a b : ℝ), Tile a b L → ∀ t, t ∈ Set.Ioo a b →
    (∀ l ∈ L, t ≠ l.hi) →
    (L.map fun l => Set.indicator (Set.Ioo l.lo l.hi) (fun _ => (1 : ℕ)) t).sum = 1
  | [], a, b, h, t, ht, _ => by
      have : a = b := h
      subst this
      exact absurd ht.2 (not_lt.2 ht.1.le)
  | l₀ :: L, a, b, h, t, ht, hne => by
      obtain ⟨h1, h2, h3⟩ := h
      have hne0 : t ≠ l₀.hi := hne l₀ (by simp)
      rcases lt_or_gt_of_ne hne0 with hlt | hgt
      · have hin : t ∈ Set.Ioo l₀.lo l₀.hi := ⟨by rw [h1]; exact ht.1, hlt⟩
        have htail : ∀ l ∈ L, (Set.indicator (Set.Ioo l.lo l.hi) (fun _ => (1 : ℕ)) t) = 0 := by
          intro l hl
          have := (tile_bounds L l₀.hi b h3 l hl).1
          exact Set.indicator_of_notMem (fun hh => by linarith [hh.1]) _
        simp only [List.map_cons, List.sum_cons, Set.indicator_of_mem hin]
        have : (L.map fun l => Set.indicator (Set.Ioo l.lo l.hi) (fun _ => (1 : ℕ)) t) =
            L.map (fun _ => 0) := List.map_congr_left htail
        rw [this]; simp
      · have hnin : t ∉ Set.Ioo l₀.lo l₀.hi := fun hh => by linarith [hh.2]
        simp only [List.map_cons, List.sum_cons, Set.indicator_of_notMem hnin, zero_add]
        exact tile_count L l₀.hi b h3 t ⟨hgt, ht.2⟩ (fun l hl => hne l (by simp [hl]))

/-! ## Part C: the window angle and the leg sectors -/

theorem arg_polar {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) :
    Complex.arg ((r : ℂ) * Complex.exp (θ * Complex.I)) = θ := by
  rw [Complex.exp_mul_I]; exact Complex.arg_mul_cos_add_sin_mul_I hr hθ

/-- The rotation constant `exp(-i m)`. -/
def rotc (m : ℝ) : ℂ := Complex.exp (((-m : ℝ) : ℂ) * Complex.I)

theorem norm_rotc (m : ℝ) : ‖rotc m‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem rotc_mul_exp (m t : ℝ) :
    rotc m * Complex.exp (t * Complex.I) = Complex.exp (((t - m : ℝ) : ℂ) * Complex.I) := by
  unfold rotc; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem exp_mul_rotc (m t : ℝ) :
    Complex.exp (m * Complex.I) * Complex.exp (((t - m : ℝ) : ℂ) * Complex.I) =
      Complex.exp (t * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- The angle of `z`, read in the window `(t₀, t₀ + 2π]`. -/
def winAng (t₀ : ℝ) (z : ℂ) : ℝ := (t₀ + π) + Complex.arg (rotc (t₀ + π) * z)

theorem winAng_polar (t₀ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    z = ‖z‖ * Complex.exp (winAng t₀ z * Complex.I) := by
  set m := t₀ + π with hm
  have hw : rotc m * z ≠ 0 := mul_ne_zero (by simp [rotc]) hz
  have h1 := Complex.norm_mul_exp_arg_mul_I (rotc m * z)
  rw [norm_mul, norm_rotc, one_mul] at h1
  have h2 : z = Complex.exp (m * Complex.I) * (rotc m * z) := by
    rw [← mul_assoc]
    have : Complex.exp (m * Complex.I) * rotc m = 1 := by
      unfold rotc; rw [← Complex.exp_add]; push_cast; simp
    rw [this, one_mul]
  have h3 : winAng t₀ z = m + Complex.arg (rotc m * z) := rfl
  calc z = Complex.exp (m * Complex.I) * (rotc m * z) := h2
    _ = Complex.exp (m * Complex.I) * (‖z‖ * Complex.exp (Complex.arg (rotc m * z) * Complex.I)) := by
        rw [h1]
    _ = ‖z‖ * Complex.exp (winAng t₀ z * Complex.I) := by
        rw [h3]; push_cast
        rw [add_mul, Complex.exp_add]; ring

theorem winAng_mem (t₀ : ℝ) {z : ℂ} (hz : z ≠ 0) : winAng t₀ z ∈ Set.Ioc t₀ (t₀ + 2 * π) := by
  have hw : rotc (t₀ + π) * z ≠ 0 := mul_ne_zero (by simp [rotc]) hz
  have h1 := Complex.neg_pi_lt_arg (rotc (t₀ + π) * z)
  have h2 := Complex.arg_le_pi (rotc (t₀ + π) * z)
  unfold winAng
  constructor <;> linarith

theorem winAng_eq (t₀ : ℝ) {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : t ∈ Set.Ioc t₀ (t₀ + 2 * π))
    (hzt : z = ‖z‖ * Complex.exp (t * Complex.I)) : winAng t₀ z = t := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 : rotc (t₀ + π) * z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((t - (t₀ + π) : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hzt]
    rw [mul_left_comm, rotc_mul_exp]
  have h2 : Complex.arg (rotc (t₀ + π) * z) = t - (t₀ + π) := by
    rw [h1]
    apply arg_polar hzn
    constructor <;> linarith [ht.1, ht.2]
  unfold winAng; rw [h2]; ring

/-- The open sector of a leg, as a preimage of an open subset of the slit plane. -/
def legSector (t₀ : ℝ) (l : Leg) : Set ℂ :=
  (fun z => rotc (t₀ + π) * z) ⁻¹'
    (Complex.slitPlane ∩ Complex.arg ⁻¹' Set.Ioo (l.lo - (t₀ + π)) (l.hi - (t₀ + π)))

theorem isOpen_legSector (t₀ : ℝ) (l : Leg) : IsOpen (legSector t₀ l) := by
  have hQ : IsOpen (Complex.slitPlane ∩ Complex.arg ⁻¹' Set.Ioo (l.lo - (t₀ + π)) (l.hi - (t₀ + π))) :=
    Complex.continuousOn_arg.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
  exact hQ.preimage (by fun_prop)

theorem mem_legSector_iff (t₀ : ℝ) {l : Leg} (hhi : l.hi ≤ t₀ + 2 * π) {z : ℂ} :
    z ∈ legSector t₀ l ↔ z ≠ 0 ∧ winAng t₀ z ∈ Set.Ioo l.lo l.hi := by
  have hz0 : z ≠ 0 ↔ rotc (t₀ + π) * z ≠ 0 := by
    constructor
    · intro h; exact mul_ne_zero (by simp [rotc]) h
    · intro h hz; exact h (by rw [hz, mul_zero])
  constructor
  · rintro ⟨hs, ha⟩
    have hne : rotc (t₀ + π) * z ≠ 0 := Complex.slitPlane_ne_zero hs
    refine ⟨hz0.2 hne, ?_⟩
    unfold winAng
    constructor <;> linarith [ha.1, ha.2]
  · rintro ⟨hne, ha⟩
    have hne' := hz0.1 hne
    have h1 : Complex.arg (rotc (t₀ + π) * z) ∈ Set.Ioo (l.lo - (t₀ + π)) (l.hi - (t₀ + π)) := by
      unfold winAng at ha
      constructor <;> linarith [ha.1, ha.2]
    refine ⟨?_, h1⟩
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, hne'⟩
    intro h
    have := h1.2
    rw [h] at this
    linarith

/-! ## Part D: the leg isometries -/

/-- The rotation `z ↦ exp(i s) z` as a linear isometry. -/
def rotC (s : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp s)

theorem rotC_apply (s : ℝ) (z : ℂ) : rotC s z = Complex.exp (s * Complex.I) * z := by
  simp [rotC, rotation_apply, Circle.coe_exp]

/-- The reflection `z ↦ exp(i s) conj z` as a linear isometry. -/
def reflC (s : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (rotC s)

theorem reflC_apply (s : ℝ) (z : ℂ) :
    reflC s z = Complex.exp (s * Complex.I) * (starRingEnd ℂ) z := by
  simp [reflC, rotC_apply]

/-- The linear isometry carried by a leg. -/
def legIso (l : Leg) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  if l.sign = 1 then rotC (l.val - l.lo) else reflC (l.val + l.lo)

theorem phiMap_eq_legIso {ψ : ℝ → ℝ} (hper : Function.Periodic ψ (2 * π)) {l : Leg}
    (hl : ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t) (hs : l.sign = 1 ∨ l.sign = -1) {z : ℂ}
    (hz : z ≠ 0) {t : ℝ} (ht : t ∈ Set.Ioo l.lo l.hi)
    (hzt : z = ‖z‖ * Complex.exp (t * Complex.I)) : phiMap ψ z = legIso l z := by
  rw [phiMap_polar hper hz hzt, hl t ⟨ht.1.le, ht.2.le⟩]
  unfold Leg.psi legIso
  rcases hs with h | h
  · simp only [h, ↓reduceIte]
    rw [rotC_apply]
    conv_rhs => rw [hzt]
    rw [← mul_assoc, mul_comm (Complex.exp _) (((‖z‖ : ℝ) : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  · have h1 : l.sign ≠ 1 := by rw [h]; norm_num
    simp only [h1, ↓reduceIte]
    rw [reflC_apply, h]
    have hc : (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [hzt]
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp [Complex.conj_ofReal]
    rw [hc, ← mul_assoc, mul_comm (Complex.exp _) (((‖z‖ : ℝ) : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring

theorem psi_mem_range {l : Leg} (hlt : l.lo < l.hi) (hs : l.sign = 1 ∨ l.sign = -1) {t : ℝ}
    (ht : t ∈ Set.Ioo l.lo l.hi) : l.psi t ∈ l.range := by
  unfold Leg.range Leg.psi
  rcases hs with h | h <;> rw [h]
  · rw [min_eq_left (by nlinarith [ht.1, ht.2]), max_eq_right (by nlinarith [ht.1, ht.2])]
    constructor <;> nlinarith [ht.1, ht.2]
  · rw [min_eq_right (by nlinarith [ht.1, ht.2]), max_eq_left (by nlinarith [ht.1, ht.2])]
    constructor <;> nlinarith [ht.1, ht.2]

theorem exists_psi_eq {l : Leg} (hlt : l.lo < l.hi) (hs : l.sign = 1 ∨ l.sign = -1) {a : ℝ}
    (ha : a ∈ l.range) : ∃ t ∈ Set.Ioo l.lo l.hi, l.psi t = a := by
  unfold Leg.range Leg.psi at ha
  rcases hs with h | h <;> rw [h] at ha
  · rw [min_eq_left (by nlinarith), max_eq_right (by nlinarith)] at ha
    refine ⟨l.lo + (a - l.val), ⟨by nlinarith [ha.1], by nlinarith [ha.2]⟩, ?_⟩
    unfold Leg.psi; rw [h]; ring
  · rw [min_eq_right (by nlinarith), max_eq_left (by nlinarith)] at ha
    refine ⟨l.lo - (a - l.val), ⟨by nlinarith [ha.2], by nlinarith [ha.1]⟩, ?_⟩
    unfold Leg.psi; rw [h]; ring

/-- The open sector of angles in `A`. -/
def angSector (A : Set ℝ) : Set ℂ := {z | z ≠ 0 ∧ Complex.arg z ∈ A}

theorem legIso_image {ψ : ℝ → ℝ} (hper : Function.Periodic ψ (2 * π))
    (hψπ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) π) (t₀ : ℝ) {l : Leg} (hlt : l.lo < l.hi)
    (hs : l.sign = 1 ∨ l.sign = -1) (hl : ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t)
    (hlo : t₀ ≤ l.lo) (hhi : l.hi ≤ t₀ + 2 * π) :
    legIso l '' legSector t₀ l = angSector l.range := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz0, hz1⟩ := (mem_legSector_iff t₀ hhi).1 hz
    set t := winAng t₀ z with ht
    have hzt := winAng_polar t₀ hz0
    rw [← ht] at hzt
    have hphi := phiMap_eq_legIso hper hl hs hz0 hz1 hzt
    rw [← hphi, phiMap_polar hper hz0 hzt]
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hψt : ψ t ∈ Set.Ioc (-π) π := ⟨by linarith [(hψπ t).1, Real.pi_pos], (hψπ t).2⟩
    refine ⟨?_, ?_⟩
    · intro h0
      have := congrArg norm h0
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real] at this
      simp at this
      exact hz0 (by simpa using this)
    · rw [arg_polar hzn hψt, hl t ⟨hz1.1.le, hz1.2.le⟩]
      exact psi_mem_range hlt hs hz1
  · rintro ⟨hw0, hw1⟩
    obtain ⟨t, ht, hpt⟩ := exists_psi_eq hlt hs hw1
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set z : ℂ := ((‖w‖ : ℝ) : ℂ) * Complex.exp (t * Complex.I) with hzdef
    have hzn : ‖z‖ = ‖w‖ := by
      rw [hzdef, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real]; simp
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hzn; simp at hzn; exact hw0 (by simpa using hzn.symm)
    have hzt : z = ‖z‖ * Complex.exp (t * Complex.I) := by rw [hzn]
    have hwin : winAng t₀ z = t :=
      winAng_eq t₀ hz0 ⟨by linarith [ht.1], by linarith [ht.2]⟩ hzt
    have hzm : z ∈ legSector t₀ l :=
      (mem_legSector_iff t₀ hhi).2 ⟨hz0, by rw [hwin]; exact ht⟩
    refine ⟨z, hzm, ?_⟩
    rw [← phiMap_eq_legIso hper hl hs hz0 ht hzt, phiMap_polar hper hz0 hzt, hzn,
      hl t ⟨ht.1.le, ht.2.le⟩, hpt]
    exact (Complex.norm_mul_exp_arg_mul_I w)

/-! ## Part E: Dirichlet energy density and isometries -/

/-- The energy density `|∇u|²`. -/
def dsq (u : ℂ → ℝ) (z : ℂ) : ℝ := ‖fderiv ℝ u z‖ ^ 2

theorem dsq_comp_iso (e : ℂ ≃ₗᵢ[ℝ] ℂ) (u : ℂ → ℝ) (z : ℂ) : dsq (u ∘ e) z = dsq u (e z) := by
  unfold dsq
  have h := (e.toContinuousLinearEquiv).comp_right_fderiv (f := u) (x := z)
  have h2 : fderiv ℝ (u ∘ e) z = (fderiv ℝ u (e z)).comp (e : ℂ →L[ℝ] ℂ) := h
  rw [h2, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem measurable_dsq (u : ℂ → ℝ) : Measurable (dsq u) :=
  (measurable_fderiv ℝ u).norm.pow_const 2

theorem dsq_eq_zero_of_lt {u : ℂ → ℝ} {r : ℝ} (h0 : ∀ z, r ≤ ‖z‖ → u z = 0) {z : ℂ}
    (hz : r < ‖z‖) : dsq u z = 0 := by
  have hev : u =ᶠ[nhds z] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact h0 w hw.le
  unfold dsq
  rw [hev.fderiv_eq]
  simp

theorem integrable_dsq {u : ℂ → ℝ} {K : NNReal} (hu : LipschitzWith K u) {r : ℝ}
    (h0 : ∀ z, r ≤ ‖z‖ → u z = 0) : Integrable (dsq u) := by
  have hbound : ∀ z, ‖dsq u z‖ ≤ (K : ℝ) ^ 2 * (Metric.closedBall (0 : ℂ) r).indicator 1 z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) r
    · rw [Set.indicator_of_mem hz]
      simp only [Pi.one_apply, mul_one]
      rw [Real.norm_of_nonneg (by unfold dsq; positivity)]
      unfold dsq
      have := norm_fderiv_le_of_lipschitz ℝ hu (x₀ := z)
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    · rw [Set.indicator_of_notMem hz]
      have : r < ‖z‖ := by simpa [Metric.mem_closedBall] using hz
      rw [dsq_eq_zero_of_lt h0 this]; simp
  refine Integrable.mono' (g := fun z => (K : ℝ) ^ 2 * (Metric.closedBall (0 : ℂ) r).indicator 1 z)
    ?_ (measurable_dsq u).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine Integrable.const_mul ?_ _
  rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  exact integrableOn_const (measure_closedBall_lt_top.ne)

theorem setIntegral_dsq_image (e : ℂ ≃ₗᵢ[ℝ] ℂ) (u : ℂ → ℝ) (A : Set ℂ) :
    ∫ z in e '' A, dsq u z = ∫ z in A, dsq u (e z) :=
  (e.measurePreserving).setIntegral_image_emb e.toHomeomorph.measurableEmbedding _ A

theorem phiMap_eq_on_sector {ψ : ℝ → ℝ} (hper : Function.Periodic ψ (2 * π)) (t₀ : ℝ) {l : Leg}
    (hs : l.sign = 1 ∨ l.sign = -1) (hl : ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t)
    (hhi : l.hi ≤ t₀ + 2 * π) {w : ℂ} (hw : w ∈ legSector t₀ l) : phiMap ψ w = legIso l w := by
  obtain ⟨hw0, hw1⟩ := (mem_legSector_iff t₀ hhi).1 hw
  exact phiMap_eq_legIso hper hl hs hw0 hw1 (winAng_polar t₀ hw0)

theorem leg_energy {ψ : ℝ → ℝ} (hper : Function.Periodic ψ (2 * π))
    (hψπ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) π) (t₀ : ℝ) {l : Leg} (hlt : l.lo < l.hi)
    (hs : l.sign = 1 ∨ l.sign = -1) (hl : ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t)
    (hlo : t₀ ≤ l.lo) (hhi : l.hi ≤ t₀ + 2 * π) (u : ℂ → ℝ) :
    ∫ z in legSector t₀ l, dsq (u ∘ phiMap ψ) z = ∫ z in angSector l.range, dsq u z := by
  rw [← legIso_image hper hψπ t₀ hlt hs hl hlo hhi, setIntegral_dsq_image]
  refine setIntegral_congr_fun (isOpen_legSector t₀ l).measurableSet fun z hz => ?_
  have hev : (u ∘ phiMap ψ) =ᶠ[nhds z] (u ∘ legIso l) := by
    filter_upwards [(isOpen_legSector t₀ l).mem_nhds hz] with w hw
    simp only [Function.comp]
    rw [phiMap_eq_on_sector hper t₀ hs hl hhi hw]
  have : dsq (u ∘ phiMap ψ) z = dsq (u ∘ legIso l) z := by
    unfold dsq; rw [hev.fderiv_eq]
  rw [this, dsq_comp_iso]

/-! ## Part F: null rays and the a.e. partitions -/

theorem volume_im_eq_zero : volume {v : ℂ | v.im = 0} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Set.univ ×ˢ ({0} : Set ℝ))
  have e : Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ ({0} : Set ℝ)) =
      {v : ℂ | v.im = 0} := by
    ext v; simp [Complex.measurableEquivRealProd]
  rw [e] at h
  rw [h, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem rotc_mul_eq (m : ℝ) (w : ℂ) : rotc m * w = rotC (-m) w := by
  rw [rotC_apply]; rfl

theorem volume_arg_eq (e : ℝ) : volume {z : ℂ | Complex.arg z = e} = 0 := by
  have hsub : {z : ℂ | Complex.arg z = e} ⊆ (rotC (-e)) ⁻¹' {v : ℂ | v.im = 0} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← rotc_mul_eq]
    by_cases h0 : z = 0
    · simp [h0]
    · have h1 : z = ‖z‖ * Complex.exp (e * Complex.I) := by
        conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
        rw [hz]
      rw [h1, mul_left_comm, rotc_mul_exp]
      simp
  refine measure_mono_null hsub ?_
  rw [(rotC (-e)).measurePreserving.measure_preimage
    (measurableSet_eq_fun Complex.measurable_im measurable_const).nullMeasurableSet]
  exact volume_im_eq_zero

theorem ae_arg_notMem {E : Set ℝ} (hE : E.Countable) :
    ∀ᵐ z : ℂ, z ≠ 0 ∧ Complex.arg z ∉ E := by
  rw [ae_iff]
  have : {z : ℂ | ¬(z ≠ 0 ∧ Complex.arg z ∉ E)} ⊆
      {0} ∪ ⋃ e ∈ E, {z : ℂ | Complex.arg z = e} := by
    intro z hz
    simp only [Set.mem_ofPred_eq, not_and, not_not] at hz
    by_cases h0 : z = 0
    · exact Or.inl h0
    · exact Or.inr (Set.mem_biUnion (hz h0) rfl)
  refine measure_mono_null this ?_
  refine measure_union_null (measure_singleton _) ?_
  exact (measure_biUnion_null_iff hE).2 fun e _ => volume_arg_eq e

theorem ae_winAng_notMem (t₀ : ℝ) {E : Set ℝ} (hE : E.Countable) :
    ∀ᵐ z : ℂ, z ≠ 0 ∧ winAng t₀ z ∉ E := by
  have hE' : ((fun x => x - (t₀ + π)) '' E).Countable := hE.image _
  have h1 := ae_arg_notMem hE'
  have h2 : ∀ᵐ z : ℂ, rotc (t₀ + π) * z ≠ 0 ∧
      Complex.arg (rotc (t₀ + π) * z) ∉ (fun x => x - (t₀ + π)) '' E := by
    have := (rotC (-(t₀ + π))).measurePreserving.quasiMeasurePreserving.ae h1
    filter_upwards [this] with z hz
    rw [rotc_mul_eq]
    exact hz
  filter_upwards [h2] with z hz
  refine ⟨?_, ?_⟩
  · intro h0; exact hz.1 (by rw [h0, mul_zero])
  · intro hmem
    refine hz.2 ⟨winAng t₀ z, hmem, ?_⟩
    unfold winAng; ring

theorem ae_leg_partition (t₀ : ℝ) {L : List Leg} (hT : Tile t₀ (t₀ + 2 * π) L) :
    ∀ᵐ z : ℂ, (L.map fun l => Set.indicator (legSector t₀ l) (fun _ => (1 : ℝ)) z).sum = 1 := by
  have hE : (({t₀ + 2 * π} ∪ (L.map Leg.hi).toFinset : Set ℝ)).Countable :=
    (Set.toFinite _).countable
  filter_upwards [ae_winAng_notMem t₀ hE] with z hz
  obtain ⟨hz0, hzE⟩ := hz
  have hmem := winAng_mem t₀ hz0
  have hne : ∀ l ∈ L, winAng t₀ z ≠ l.hi := by
    intro l hl h
    exact hzE (Or.inr (by simp; exact ⟨l, hl, h.symm⟩))
  have hne2 : winAng t₀ z ≠ t₀ + 2 * π := fun h => hzE (Or.inl h)
  have hcnt := tile_count L t₀ (t₀ + 2 * π) hT (winAng t₀ z)
    ⟨hmem.1, lt_of_le_of_ne hmem.2 hne2⟩ hne
  have hmap : (L.map fun l => Set.indicator (legSector t₀ l) (fun _ => (1 : ℝ)) z) =
      (L.map fun l => (((Set.indicator (Set.Ioo l.lo l.hi) (fun _ => (1 : ℕ)) (winAng t₀ z) : ℕ)) : ℝ)) := by
    refine List.map_congr_left fun l hl => ?_
    have hb := tile_bounds L t₀ (t₀ + 2 * π) hT l hl
    by_cases hin : winAng t₀ z ∈ Set.Ioo l.lo l.hi
    · have : z ∈ legSector t₀ l := (mem_legSector_iff t₀ hb.2).2 ⟨hz0, hin⟩
      simp [Set.indicator_of_mem this, Set.indicator_of_mem hin]
    · have : z ∉ legSector t₀ l := fun h => hin ((mem_legSector_iff t₀ hb.2).1 h).2
      simp [Set.indicator_of_notMem this, Set.indicator_of_notMem hin]
  rw [hmap]
  have h1 : (((L.map fun l => Set.indicator (Set.Ioo l.lo l.hi) (fun _ => (1 : ℕ))
      (winAng t₀ z)).sum : ℕ) : ℝ) = 1 := by rw [hcnt]; simp
  rw [← h1, Nat.cast_list_sum, List.map_map]
  rfl

theorem ind_angSector (A : Set ℝ) {z : ℂ} (hz0 : z ≠ 0) :
    Set.indicator (angSector A) (fun _ => (1 : ℝ)) z =
      (((Set.indicator A (fun _ => (1 : ℕ)) (Complex.arg z) : ℕ)) : ℝ) := by
  by_cases h : Complex.arg z ∈ A
  · have : z ∈ angSector A := ⟨hz0, h⟩
    simp [Set.indicator_of_mem this, Set.indicator_of_mem h]
  · have : z ∉ angSector A := fun hh => h hh.2
    simp [Set.indicator_of_notMem this, Set.indicator_of_notMem h]

theorem measurableSet_angSector {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (angSector A) := by
  have : angSector A = {0}ᶜ ∩ Complex.arg ⁻¹' A := by
    ext z; simp [angSector]
  rw [this]
  exact (measurableSet_singleton 0).compl.inter (Complex.measurable_arg hA)

theorem ae_range_partition {N : ℕ} {L : List Leg} (F : Finset ℝ)
    (hcount : ∀ φ ∈ Set.Ioo (0 : ℝ) (π / N), φ ∉ F →
      (L.map fun l => Set.indicator l.range (fun _ => (1 : ℕ)) φ).sum = 2 * N)
    (hsub : ∀ l ∈ L, l.range ⊆ Set.Ioo 0 (π / N)) :
    ∀ᵐ z : ℂ, (L.map fun l => Set.indicator (angSector l.range) (fun _ => (1 : ℝ)) z).sum =
      2 * N * Set.indicator (angSector (Set.Ioo 0 (π / N))) (fun _ => (1 : ℝ)) z := by
  filter_upwards [ae_arg_notMem F.countable_toSet] with z hz
  obtain ⟨hz0, hzF⟩ := hz
  have hmap : (L.map fun l => Set.indicator (angSector l.range) (fun _ => (1 : ℝ)) z) =
      (L.map fun l => (((Set.indicator l.range (fun _ => (1 : ℕ)) (Complex.arg z) : ℕ)) : ℝ)) :=
    List.map_congr_left fun l _ => ind_angSector _ hz0
  rw [hmap, ind_angSector _ hz0]
  by_cases hin : Complex.arg z ∈ Set.Ioo (0 : ℝ) (π / N)
  · have hc := hcount _ hin (by simpa using hzF)
    have h1 : (((L.map fun l => Set.indicator l.range (fun _ => (1 : ℕ)) (Complex.arg z)).sum : ℕ) : ℝ)
        = 2 * N := by rw [hc]; push_cast; ring
    rw [Nat.cast_list_sum, List.map_map] at h1
    have h2 : Set.indicator (Set.Ioo (0 : ℝ) (π / N)) (fun _ => (1 : ℕ)) (Complex.arg z) = 1 :=
      Set.indicator_of_mem hin _
    rw [h2]
    simpa [Function.comp_def] using h1
  · have h2 : Set.indicator (Set.Ioo (0 : ℝ) (π / N)) (fun _ => (1 : ℕ)) (Complex.arg z) = 0 :=
      Set.indicator_of_notMem hin _
    rw [h2]
    have : (L.map fun l => (((Set.indicator l.range (fun _ => (1 : ℕ)) (Complex.arg z) : ℕ)) : ℝ)) =
        L.map fun _ => 0 :=
      List.map_congr_left fun l hl => by
        rw [Set.indicator_of_notMem (fun h => hin (hsub l hl h))]; simp
    rw [this]; simp

/-! ## Part G: the dihedral group and the `2N` sectors -/

theorem rotC_polar (s r t : ℝ) :
    rotC s ((r : ℂ) * Complex.exp (t * Complex.I)) =
      (r : ℂ) * Complex.exp (((t + s : ℝ) : ℂ) * Complex.I) := by
  rw [rotC_apply, mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring

theorem reflC_polar (s r t : ℝ) :
    reflC s ((r : ℂ) * Complex.exp (t * Complex.I)) =
      (r : ℂ) * Complex.exp (((s - t : ℝ) : ℂ) * Complex.I) := by
  have hc : (starRingEnd ℂ) ((r : ℂ) * Complex.exp (t * Complex.I)) =
      (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  rw [reflC_apply, hc, mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring

theorem angSector_polar {A : Set ℝ} {z : ℂ} (hz : z ∈ angSector A) :
    z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℝ) * Complex.I) ∧ 0 < ‖z‖ :=
  ⟨(Complex.norm_mul_exp_arg_mul_I z).symm, norm_pos_iff.2 hz.1⟩

theorem polar_mem_angSector {A : Set ℝ} {r : ℝ} (hr : 0 < r) {t : ℝ}
    (ht : t ∈ Set.Ioc (-π) π) (htA : t ∈ A) :
    ((r : ℂ) * Complex.exp (t * Complex.I)) ∈ angSector A := by
  refine ⟨?_, by rw [arg_polar hr ht]; exact htA⟩
  intro h
  have := congrArg norm h
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real] at this
  simp at this
  exact hr.ne' (by simpa using this)

theorem rotC_image {s a b a' b' : ℝ} (h1 : -π ≤ a) (h2 : b ≤ π) (h3 : -π ≤ a') (h4 : b' ≤ π)
    (ha : a' = a + s) (hb : b' = b + s) :
    rotC s '' angSector (Set.Ioo a b) = angSector (Set.Ioo a' b') := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzp, hzn⟩ := angSector_polar hz
    have hx := hz.2
    rw [hzp, rotC_polar]
    exact polar_mem_angSector hzn ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
      ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  · intro hw
    obtain ⟨hwp, hwn⟩ := angSector_polar hw
    have hy := hw.2
    set y := Complex.arg w
    have hx : y - s ∈ Set.Ioo a b := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    refine ⟨((‖w‖ : ℝ) : ℂ) * Complex.exp (((y - s : ℝ) : ℂ) * Complex.I),
      polar_mem_angSector hwn ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩ hx, ?_⟩
    rw [rotC_polar, sub_add_cancel]
    exact hwp.symm

theorem reflC_image {s a b a' b' : ℝ} (h1 : -π ≤ a) (h2 : b ≤ π) (h3 : -π ≤ a') (h4 : b' ≤ π)
    (ha : a' = s - b) (hb : b' = s - a) :
    reflC s '' angSector (Set.Ioo a b) = angSector (Set.Ioo a' b') := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzp, hzn⟩ := angSector_polar hz
    have hx := hz.2
    rw [hzp, reflC_polar]
    exact polar_mem_angSector hzn ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
      ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  · intro hw
    obtain ⟨hwp, hwn⟩ := angSector_polar hw
    have hy := hw.2
    set y := Complex.arg w
    have hx : s - y ∈ Set.Ioo a b := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    refine ⟨((‖w‖ : ℝ) : ℂ) * Complex.exp (((s - y : ℝ) : ℂ) * Complex.I),
      polar_mem_angSector hwn ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩ hx, ?_⟩
    rw [reflC_polar, sub_sub_cancel]
    exact hwp.symm

theorem u_rot_nat {N : ℕ} {u : ℂ → ℝ} (hrot : ∀ z, u (rootN N * z) = u z) (n : ℕ) (z : ℂ) :
    u (rootN N ^ n * z) = u z := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_comm (rootN N ^ n), mul_assoc, hrot, ih]

theorem u_rot_int {N : ℕ} {u : ℂ → ℝ} (hrot : ∀ z, u (rootN N * z) = u z) (m : ℤ) (z : ℂ) : u (rootN N ^ m * z) = u z := by
  have hne : rootN N ≠ 0 := by unfold rootN; exact Complex.exp_ne_zero _
  rcases m with n | n
  · simpa using u_rot_nat hrot n z
  · have h1 := u_rot_nat hrot (n + 1) (rootN N ^ (Int.negSucc n) * z)
    have h2 : rootN N ^ (n + 1) * (rootN N ^ (Int.negSucc n) * z) = z := by
      rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hne]
      have : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by rw [Int.negSucc_eq]; push_cast; ring
      rw [this]; simp
    rw [h2] at h1
    exact h1.symm

theorem rotC_eq_pow {N : ℕ} (hN : 1 ≤ N) (m : ℤ) (z : ℂ) :
    rotC (m * (2 * π / N)) z = rootN N ^ m * z := by
  rw [rotC_apply]
  congr 1
  unfold rootN
  rw [← Complex.exp_int_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  push_cast
  field_simp

theorem dihedral_invariant {N : ℕ} (hN : 1 ≤ N) {u : ℂ → ℝ}
    (hrot : ∀ z, u (rootN N * z) = u z) (hconj : ∀ z, u (starRingEnd ℂ z) = u z) (m : ℤ) :
    (∀ z, u (rotC (m * (2 * π / N)) z) = u z) ∧ (∀ z, u (reflC (m * (2 * π / N)) z) = u z) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [rotC_eq_pow hN, u_rot_int hrot]
  · have : reflC (m * (2 * π / N)) z = rotC (m * (2 * π / N)) ((starRingEnd ℂ) z) := by
      rw [reflC_apply, rotC_apply]
    rw [this, rotC_eq_pow hN, u_rot_int hrot, hconj]

theorem setIntegral_dsq_invariant (e : ℂ ≃ₗᵢ[ℝ] ℂ) {u : ℂ → ℝ} (hu : ∀ z, u (e z) = u z)
    {A B : Set ℂ} (h : e '' A = B) : ∫ z in B, dsq u z = ∫ z in A, dsq u z := by
  rw [← h, setIntegral_dsq_image]
  have : ∀ z, dsq u (e z) = dsq u z := fun z => by
    rw [← dsq_comp_iso]; congr 1; funext w; exact hu w
  simp only [this]

theorem sector_integral_eq {N : ℕ} (hN : 1 ≤ N) {u : ℂ → ℝ}
    (hrot : ∀ z, u (rootN N * z) = u z) (hconj : ∀ z, u (starRingEnd ℂ z) = u z) (j : ℤ)
    (hj1 : -(N : ℤ) ≤ j) (hj2 : j < N) :
    ∫ z in angSector (Set.Ioo ((j : ℝ) * (π / N)) (((j : ℝ) + 1) * (π / N))), dsq u z =
      ∫ z in angSector (Set.Ioo 0 (π / N)), dsq u z := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  set h : ℝ := π / N with hh
  have hh0 : 0 < h := by positivity
  have hNh : (N : ℝ) * h = π := by rw [hh]; field_simp
  have hj1' : -(N : ℝ) ≤ j := by exact_mod_cast hj1
  have hj2' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj2
  have b1 : -π ≤ (j : ℝ) * h := by nlinarith
  have b2 : ((j : ℝ) + 1) * h ≤ π := by nlinarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hπh : h ≤ π := by nlinarith
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' j
  · have hjk : (j : ℝ) = 2 * k := by exact_mod_cast hk
    have hs : (k : ℝ) * (2 * π / N) = (j : ℝ) * h := by
      rw [hjk, hh]; field_simp
    refine setIntegral_dsq_invariant (rotC (k * (2 * π / N)))
      (dihedral_invariant hN hrot hconj k).1 ?_
    exact rotC_image (by linarith) hπh b1 b2 (by rw [hs]; ring) (by rw [hs]; ring)
  · have hjk : (j : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    have hs : ((k + 1 : ℤ) : ℝ) * (2 * π / N) = ((j : ℝ) + 1) * h := by
      rw [hjk, hh]; push_cast; field_simp; ring
    refine setIntegral_dsq_invariant (reflC (((k + 1 : ℤ) : ℝ) * (2 * π / N)))
      (dihedral_invariant hN hrot hconj (k + 1)).2 ?_
    exact reflC_image (by linarith) hπh b1 b2 (by rw [hs]; ring) (by rw [hs]; ring)

theorem ae_dihedral_partition {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ z : ℂ, (∑ j ∈ Finset.Ico (-(N : ℤ)) N,
      Set.indicator (angSector (Set.Ioo ((j : ℝ) * (π / N)) (((j : ℝ) + 1) * (π / N))))
        (fun _ => (1 : ℝ)) z) = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  set h : ℝ := π / N with hh
  have hh0 : 0 < h := by positivity
  have hNh : (N : ℝ) * h = π := by rw [hh]; field_simp
  have hE : (Set.range fun j : ℤ => (j : ℝ) * h).Countable := Set.countable_range _
  filter_upwards [ae_arg_notMem hE] with z hz
  obtain ⟨hz0, hzE⟩ := hz
  set a := Complex.arg z with ha
  have ha1 : -π < a := Complex.neg_pi_lt_arg z
  have ha2 : a ≤ π := Complex.arg_le_pi z
  set j0 : ℤ := ⌊a / h⌋ with hj0
  have hf1 : (j0 : ℝ) ≤ a / h := Int.floor_le _
  have hne : (j0 : ℝ) ≠ a / h := by
    intro heq
    exact hzE ⟨j0, by show (j0 : ℝ) * h = a; rw [heq]; field_simp⟩
  have hf2 : (j0 : ℝ) < a / h := lt_of_le_of_ne hf1 hne
  have hf3 : a / h < j0 + 1 := Int.lt_floor_add_one _
  have hl1 : -(N : ℝ) < a / h := by rw [lt_div_iff₀ hh0]; nlinarith
  have hl2 : a / h ≤ N := by rw [div_le_iff₀ hh0]; nlinarith
  have hj0mem : j0 ∈ Finset.Ico (-(N : ℤ)) N := by
    rw [Finset.mem_Ico]
    constructor
    · have : (-(N : ℤ) : ℝ) ≤ j0 := by
        have := Int.le_floor.2 (show ((-(N : ℤ) : ℤ) : ℝ) ≤ a / h by push_cast; linarith)
        exact_mod_cast this
      exact_mod_cast this
    · have : (j0 : ℝ) < N := by linarith
      exact_mod_cast this
  rw [Finset.sum_eq_single_of_mem j0 hj0mem]
  · have : z ∈ angSector (Set.Ioo ((j0 : ℝ) * h) (((j0 : ℝ) + 1) * h)) := by
      refine ⟨hz0, ?_, ?_⟩
      · exact (lt_div_iff₀ hh0).1 hf2
      · exact (div_lt_iff₀ hh0).1 hf3
    simp [Set.indicator_of_mem this]
  · intro j _ hj
    have : z ∉ angSector (Set.Ioo ((j : ℝ) * h) (((j : ℝ) + 1) * h)) := by
      rintro ⟨_, h1, h2⟩
      replace h1 := (lt_div_iff₀ hh0).2 h1
      replace h2 := (div_lt_iff₀ hh0).2 h2
      have e1 : j ≤ j0 := by
        have : (j : ℝ) < j0 + 1 := lt_trans h1 hf3
        exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
      have e2 : j0 ≤ j := by
        have : (j0 : ℝ) < j + 1 := lt_trans hf2 h2
        exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
      exact hj (le_antisymm e1 e2)
    simp [Set.indicator_of_notMem this]

/-! ## Part H: the energy identity -/

theorem integrable_list_sum {ι : Type*} (L : List ι) (f : ι → ℂ → ℝ)
    (hf : ∀ i ∈ L, Integrable (f i)) : Integrable (fun z => (L.map fun i => f i z).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

theorem integral_list_sum {ι : Type*} (L : List ι) (f : ι → ℂ → ℝ)
    (hf : ∀ i ∈ L, Integrable (f i)) :
    ∫ z, (L.map fun i => f i z).sum = (L.map fun i => ∫ z, f i z).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [integral_add (hf a (by simp)) (integrable_list_sum L f fun i hi => hf i (by simp [hi])),
        ih fun i hi => hf i (by simp [hi])]

theorem ind_mul (S : Set ℂ) (g : ℂ → ℝ) (z : ℂ) :
    Set.indicator S g z = Set.indicator S (fun _ => (1 : ℝ)) z * g z := by
  by_cases h : z ∈ S <;> simp [h]

theorem sum_ind_mul {ι : Type*} (L : List ι) (S : ι → Set ℂ) (g : ℂ → ℝ) (z : ℂ) :
    (L.map fun i => Set.indicator (S i) g z).sum =
      (L.map fun i => Set.indicator (S i) (fun _ => (1 : ℝ)) z).sum * g z := by
  have : (L.map fun i => Set.indicator (S i) g z) =
      L.map fun i => Set.indicator (S i) (fun _ => (1 : ℝ)) z * g z :=
    List.map_congr_left fun i _ => ind_mul _ _ _
  rw [this, List.sum_map_mul_right]

theorem energy_eq {N : ℕ} (hN : 1 ≤ N) {ψ : ℝ → ℝ} {L : List Leg}
    (hper : Function.Periodic ψ (2 * π)) (hψπ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) π) {t₀ : ℝ}
    (hT : Tile t₀ (t₀ + 2 * π) L)
    (hlegs : ∀ l ∈ L, l.lo < l.hi ∧ (l.sign = 1 ∨ l.sign = -1) ∧
      ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t)
    (F : Finset ℝ)
    (hcount : ∀ φ ∈ Set.Ioo (0 : ℝ) (π / N), φ ∉ F →
      (L.map fun l => Set.indicator l.range (fun _ => (1 : ℕ)) φ).sum = 2 * N)
    (hsub : ∀ l ∈ L, l.range ⊆ Set.Ioo 0 (π / N))
    {u : ℂ → ℝ} {Lu : NNReal} (hu : LipschitzWith Lu u)
    (hrot : ∀ z, u (rootN N * z) = u z) (hconj : ∀ z, u (starRingEnd ℂ z) = u z) {r' : ℝ}
    (h0 : ∀ z, r' ≤ ‖z‖ → u z = 0) {K : NNReal} (hK : LipschitzWith K (u ∘ phiMap ψ))
    (h0' : ∀ z, r' ≤ ‖z‖ → (u ∘ phiMap ψ) z = 0) :
    dirichletEnergy (u ∘ phiMap ψ) = dirichletEnergy u := by
  have hIu : Integrable (dsq u) := integrable_dsq hu h0
  have hIt : Integrable (dsq (u ∘ phiMap ψ)) := integrable_dsq hK h0'
  have hP : ∀ l ∈ L, MeasurableSet (legSector t₀ l) := fun l _ =>
    (isOpen_legSector t₀ l).measurableSet
  have hW0 : MeasurableSet (angSector (Set.Ioo (0 : ℝ) (π / N))) :=
    measurableSet_angSector measurableSet_Ioo
  have hS : ∀ l ∈ L, MeasurableSet (angSector l.range) := fun l _ =>
    measurableSet_angSector measurableSet_Ioo
  set c : ℝ := ∫ z in angSector (Set.Ioo (0 : ℝ) (π / N)), dsq u z with hc
  -- the energy of the composite
  have hA : ∫ z, dsq (u ∘ phiMap ψ) z = 2 * N * c := by
    have step1 : ∫ z, dsq (u ∘ phiMap ψ) z =
        ∫ z, (L.map fun l => Set.indicator (legSector t₀ l) (dsq (u ∘ phiMap ψ)) z).sum := by
      refine integral_congr_ae ?_
      filter_upwards [ae_leg_partition t₀ hT] with z hz
      rw [sum_ind_mul, hz, one_mul]
    have step2 := integral_list_sum L
      (fun l z => Set.indicator (legSector t₀ l) (dsq (u ∘ phiMap ψ)) z)
      (fun l hl => hIt.indicator (hP l hl))
    have step3 : (L.map fun l => ∫ z, Set.indicator (legSector t₀ l) (dsq (u ∘ phiMap ψ)) z) =
        L.map fun l => ∫ z, Set.indicator (angSector l.range) (dsq u) z :=
      List.map_congr_left fun l hl => by
        obtain ⟨hlt, hs, hl'⟩ := hlegs l hl
        obtain ⟨hlo, hhi⟩ := tile_bounds L t₀ (t₀ + 2 * π) hT l hl
        rw [integral_indicator (hP l hl), integral_indicator (hS l hl)]
        exact leg_energy hper hψπ t₀ hlt hs hl' hlo hhi u
    have step4 := integral_list_sum L (fun l z => Set.indicator (angSector l.range) (dsq u) z)
      (fun l hl => hIu.indicator (hS l hl))
    have step5 : ∫ z, (L.map fun l => Set.indicator (angSector l.range) (dsq u) z).sum =
        ∫ z, 2 * N * Set.indicator (angSector (Set.Ioo (0 : ℝ) (π / N))) (dsq u) z := by
      refine integral_congr_ae ?_
      filter_upwards [ae_range_partition F hcount hsub] with z hz
      rw [sum_ind_mul, hz, ind_mul (angSector _) (dsq u) z, mul_assoc]
    rw [step1, step2, step3, ← step4, step5, integral_const_mul, integral_indicator hW0]
  -- the energy of `u`
  have hB : ∫ z, dsq u z = 2 * N * c := by
    have hWj : ∀ j ∈ Finset.Ico (-(N : ℤ)) N,
        MeasurableSet (angSector (Set.Ioo ((j : ℝ) * (π / N)) (((j : ℝ) + 1) * (π / N)))) :=
      fun _ _ => measurableSet_angSector measurableSet_Ioo
    have step1 : ∫ z, dsq u z = ∫ z, ∑ j ∈ Finset.Ico (-(N : ℤ)) N,
        Set.indicator (angSector (Set.Ioo ((j : ℝ) * (π / N)) (((j : ℝ) + 1) * (π / N))))
          (dsq u) z := by
      refine integral_congr_ae ?_
      filter_upwards [ae_dihedral_partition hN] with z hz
      rw [Finset.sum_congr rfl (fun j _ => ind_mul _ (dsq u) z), ← Finset.sum_mul, hz, one_mul]
    rw [step1, integral_finsetSum _ fun j hj => hIu.indicator (hWj j hj)]
    have : ∀ j ∈ Finset.Ico (-(N : ℤ)) N,
        ∫ z, Set.indicator (angSector (Set.Ioo ((j : ℝ) * (π / N)) (((j : ℝ) + 1) * (π / N))))
          (dsq u) z = c := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [integral_indicator (hWj j (Finset.mem_Ico.2 hj))]
      exact sector_integral_eq hN hrot hconj j hj.1 hj.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Ico]
    have : (N : ℤ) - -(N : ℤ) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast, nsmul_eq_mul]
    push_cast; ring
  unfold dirichletEnergy
  change ∫ z, dsq (u ∘ phiMap ψ) z = ∫ z, dsq u z
  rw [hA, hB]

theorem range_subset {N : ℕ} {ψ : ℝ → ℝ} (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) (π / N)) {l : Leg}
    (hlt : l.lo < l.hi) (hl : ∀ t ∈ Set.Icc l.lo l.hi, ψ t = l.psi t) :
    l.range ⊆ Set.Ioo 0 (π / N) := by
  have h1 : ψ l.lo = l.val := by
    rw [hl l.lo ⟨le_rfl, hlt.le⟩]; simp [Leg.psi]
  have h2 : ψ l.hi = l.psi l.hi := hl l.hi ⟨hlt.le, le_rfl⟩
  intro x hx
  unfold Leg.range at hx
  have a1 := hrange l.lo
  have a2 := hrange l.hi
  rw [h1] at a1
  rw [← h2] at *
  exact ⟨lt_of_le_of_lt (le_min a1.1 a2.1) hx.1, lt_of_lt_of_le hx.2 (max_le a1.2 a2.2)⟩

end PhiAux

/-- [Supplement C, Lemma 6.2 (`lem:Phi`)] `Φ` preserves the norm, maps the star `spikes` into the
symmetric star, and is `(1 + π/2)`-Lipschitz. -/
theorem phiMap_spec {N : ℕ} {θ : Fin N → ℝ} {ψ : ℝ → ℝ} {L : List Leg} (hN : 1 ≤ N)
    (hz : IsZigzag N θ ψ L) {R : ℝ} (hR : 0 ≤ R) :
    (∀ z, ‖phiMap ψ z‖ = ‖z‖) ∧ (∀ z ∈ spikes R θ, phiMap ψ z ∈ starSet N R) ∧
    LipschitzWith (Real.toNNReal (1 + Real.pi / 2)) (phiMap ψ) := by
  obtain ⟨_, hper, hlip, _, hθ0, _⟩ := hz
  exact ⟨PhiAux.phiMap_norm ψ, fun z hzs => PhiAux.phiMap_mem_starSet hN hper hθ0 hR hzs,
    PhiAux.lipschitz_phiMap hper hlip⟩

/-- [Supplement C, Prop. 6.3 (`prop:zigzag`)] Dissymmetrization: `ũ = u ∘ Φ` is Lipschitz, equals `1`
on the open set `Φ⁻¹(O)` containing the spikes, vanishes for `‖z‖ ≥ r'`, and has the same Dirichlet
energy as `u`. -/
theorem dissymmetrization {N : ℕ} {θ : Fin N → ℝ} {ψ : ℝ → ℝ} {L : List Leg} (hN : 1 ≤ N)
    (hz : IsZigzag N θ ψ L) {R r' : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ} {Lu : NNReal}
    (hu : LipschitzWith Lu u) (hrot : ∀ z, u (rootN N * z) = u z)
    (hconj : ∀ z, u (starRingEnd ℂ z) = u z) {O : Set ℂ} (hO : IsOpen O)
    (hKO : starSet N R ⊆ O) (h1 : ∀ z ∈ O, u z = 1) (h0 : ∀ z, r' ≤ ‖z‖ → u z = 0) :
    (∃ K : NNReal, LipschitzWith K (u ∘ phiMap ψ)) ∧ IsOpen (phiMap ψ ⁻¹' O) ∧
    spikes R θ ⊆ phiMap ψ ⁻¹' O ∧ (∀ z ∈ phiMap ψ ⁻¹' O, (u ∘ phiMap ψ) z = 1) ∧
    (∀ z, r' ≤ ‖z‖ → (u ∘ phiMap ψ) z = 0) ∧
    dirichletEnergy (u ∘ phiMap ψ) = dirichletEnergy u := by
  obtain ⟨hnorm, hspikes, hΦ⟩ := phiMap_spec hN hz hR
  obtain ⟨_, hper, _, hrange, _, hlegs, hchain, ⟨t₀, hhead, hlast⟩, F, hcount⟩ := hz
  have hLipc : LipschitzWith (Lu * Real.toNNReal (1 + π / 2)) (u ∘ phiMap ψ) := hu.comp hΦ
  have hT : PhiAux.Tile t₀ (t₀ + 2 * π) L :=
    PhiAux.tile_of_chain L t₀ (t₀ + 2 * π) (fun l hl => (hlegs l hl).1) hchain hhead hlast
  have hψπ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) π := by
    intro t
    have h := hrange t
    have : π / N ≤ π := div_le_self Real.pi_pos.le (by exact_mod_cast hN)
    exact ⟨h.1, h.2.trans this⟩
  have h0' : ∀ z, r' ≤ ‖z‖ → (u ∘ phiMap ψ) z = 0 := fun z hz => by
    simp only [Function.comp]
    exact h0 _ (by rw [hnorm]; exact hz)
  exact ⟨⟨_, hLipc⟩, hO.preimage hΦ.continuous, fun z hz => hKO (hspikes z hz),
    fun z hz => h1 _ hz, h0',
    PhiAux.energy_eq hN hper hψπ hT hlegs F hcount
      (fun l hl => PhiAux.range_subset hrange (hlegs l hl).1 (hlegs l hl).2.2)
      hu hrot hconj h0 hLipc h0'⟩

end RestrictedPolynomials
