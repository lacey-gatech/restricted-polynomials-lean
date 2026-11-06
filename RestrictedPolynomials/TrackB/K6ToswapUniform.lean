module

public import RestrictedPolynomials.TrackB.K6UniformAtoms
public import RestrictedPolynomials.TrackB.K6UniformWeight
public import RestrictedPolynomials.TrackB.K6PathTrickIneq
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.SwapNorm
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Track B: the uniform-weight swap step (Supplement D)

Source: Supplement D (`thm:toswap-uniform` steps 1-5, `prop:uniform-weight` (c)).

Formalization choice: `ν_*` is produced by `k6pt_nuStar_exists` and enters `k6pt_toswap_uniform` as
a hypothesis `νs` with the mixture identity `hνs`; the coordinate type `ι` is an arbitrary finite
type; the exponent is `2 * k6ptN (k6ptR1 α) (k6ptR2 α)`.

`k6pt_swap_norm_step` carries the two extra hypotheses `hlab` and
`hmirror` (the printed statement is false without them); both are supplied by
`k6pt_mu_minus_uniform` (`k6pt_mirror_of_mu_minus_uniform`).
-/

@[expose] public section

open Finset
open scoped BigOperators
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section ToswapUniform
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-! ### private helpers -/
section Helpers

/-- weighted Cauchy-Schwarz -/
private lemma wcs {κ : Type} [Fintype κ] (π : FinProb κ) (u v : κ → ℝ) :
    (∑ k, π.prob k * (u k * v k)) ^ 2 ≤
      (∑ k, π.prob k * u k ^ 2) * ∑ k, π.prob k * v k ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => Real.sqrt (π.prob k) * u k)
    (fun k => Real.sqrt (π.prob k) * v k)
  convert this using 3
  · rename_i k _
    have h := Real.mul_self_sqrt (π.nonneg k)
    linear_combination (-(u k * v k)) * h
  · rw [mul_pow, Real.sq_sqrt (π.nonneg _)]
  · rw [mul_pow, Real.sq_sqrt (π.nonneg _)]

/-- the pushforward law -/
private def pushLaw {T X' : Type} [Fintype T] [Fintype X'] [DecidableEq X'] (π : FinProb T)
    (φ : T → X') : FinProb X' where
  prob a := ∑ t ∈ univ.filter (fun t => φ t = a), π.prob t
  nonneg a := Finset.sum_nonneg fun t _ => π.nonneg t
  sum_eq_one := by
    rw [Finset.sum_fiberwise univ φ π.prob]
    exact π.sum_eq_one

/-- the pushforward of a product law is the product of the pushforwards -/
private lemma pi_pushforward {T X' κ : Type} [Fintype T] [Fintype X'] [DecidableEq X']
    [Fintype κ] [DecidableEq κ] (π : FinProb T) (φ : T → X') (g : (κ → X') → ℝ) :
    ∑ q : κ → T, (π.pi κ).prob q * g (fun i => φ (q i)) =
      ∑ p : κ → X', ((pushLaw π φ).pi κ).prob p * g p := by
  have h1 : ∀ p : κ → X', ∑ q ∈ univ.filter (fun q : κ → T => (fun i => φ (q i)) = p),
      (π.pi κ).prob q = ((pushLaw π φ).pi κ).prob p := by
    intro p
    show _ = ∏ i, ∑ t ∈ univ.filter (fun t => φ t = p i), π.prob t
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext q
    simp [Fintype.mem_piFinset, funext_iff]
  rw [← Finset.sum_fiberwise univ (fun q : κ → T => fun i => φ (q i))
    (fun q => (π.pi κ).prob q * g (fun i => φ (q i)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← h1 p, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [(Finset.mem_filter.1 hq).2]

/-- symmetrization by a coordinatewise involution preserving the law -/
private lemma cexpect_involution {T κ : Type} [Fintype T] [Fintype κ] [DecidableEq κ]
    (π : FinProb T) (m : T → T) (hm : ∀ t, m (m t) = t) (hp : ∀ t, π.prob (m t) = π.prob t)
    (b : κ → Bool) (F : (κ → T) → ℂ) :
    (π.pi κ).cexpect F =
      (π.pi κ).cexpect (fun q => F (fun i => if b i then m (q i) else q i)) := by
  let Tb : (κ → T) → (κ → T) := fun q i => if b i then m (q i) else q i
  have hT : Function.Involutive Tb := by
    intro q
    funext i
    by_cases hb : b i <;> simp [Tb, hb, hm]
  have hP : ∀ q, (π.pi κ).prob (Tb q) = (π.pi κ).prob q := by
    intro q
    show ∏ i, π.prob (Tb q i) = ∏ i, π.prob (q i)
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hb : b i <;> simp [Tb, hb, hp]
  unfold FinProb.cexpect
  refine (Equiv.sum_comp hT.toPerm (fun q => (((π.pi κ).prob q : ℝ) : ℂ) * F q)).symm.trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  show (((π.pi κ).prob (Tb q) : ℝ) : ℂ) * F (Tb q) = _
  rw [hP]

/-- a mirror word of `w` if one exists, else `w` -/
private noncomputable def mirrorOf {V W : Type} (lab : W → Fin 3 → V) (w : W) : W := by
  classical
  exact if h : ∃ w', lab w' = ![lab w 2, lab w 1, lab w 0] then h.choose else w

private lemma mirrorOf_spec {V W : Type} (lab : W → Fin 3 → V) {w : W}
    (h : ∃ w', lab w' = ![lab w 2, lab w 1, lab w 0]) :
    lab (mirrorOf lab w) = ![lab w 2, lab w 1, lab w 0] := by
  unfold mirrorOf
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

private lemma mirrorOf_of_not {V W : Type} (lab : W → Fin 3 → V) {w : W}
    (h : ¬ ∃ w', lab w' = ![lab w 2, lab w 1, lab w 0]) : mirrorOf lab w = w := by
  unfold mirrorOf
  simp [h]

private lemma mirrorOf_invol {V W : Type} (lab : W → Fin 3 → V) (hlab : Function.Injective lab)
    (w : W) : mirrorOf lab (mirrorOf lab w) = w := by
  by_cases h : ∃ w', lab w' = ![lab w 2, lab w 1, lab w 0]
  · have h1 := mirrorOf_spec lab h
    have h2 : ∃ w'', lab w'' = ![lab (mirrorOf lab w) 2, lab (mirrorOf lab w) 1,
        lab (mirrorOf lab w) 0] := ⟨w, by rw [h1]; ext i; fin_cases i <;> simp⟩
    apply hlab
    rw [mirrorOf_spec lab h2, h1]
    ext i
    fin_cases i <;> simp
  · rw [mirrorOf_of_not lab h, mirrorOf_of_not lab h]

private lemma norm_cexpect_le {κ : Type} [Fintype κ] (π : FinProb κ) (G : κ → ℂ) :
    ‖π.cexpect G‖ ≤ ∑ k, π.prob k * ‖G k‖ := by
  unfold FinProb.cexpect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (π.nonneg k)]

private lemma cexpect_ofReal {κ : Type} [Fintype κ] (π : FinProb κ) (r : κ → ℝ) :
    π.cexpect (fun k => ((r k : ℝ) : ℂ)) = ((∑ k, π.prob k * r k : ℝ) : ℂ) := by
  simp [FinProb.cexpect, Complex.ofReal_sum]

private lemma rpow_half_le_quarter_mul {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : x ^ 2 ≤ A * B) : x ^ (1 / 2 : ℝ) ≤ A ^ (1 / 4 : ℝ) * B ^ (1 / 4 : ℝ) := by
  have e : x ^ (1 / 2 : ℝ) = (x ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  rw [e, ← Real.mul_rpow hA hB]
  exact Real.rpow_le_rpow (sq_nonneg _) h (by norm_num)

private lemma rpow_quarter_mul_self {V : ℝ} (hV : 0 ≤ V) :
    V ^ (1 / 4 : ℝ) * V ^ (1 / 4 : ℝ) = V ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_add' hV (by norm_num)]
  norm_num

end Helpers

/-- coordinate transport of a restriction (CSP_6 `#restriction-composition`, bookkeeping):
`(u ∘ φ^{⊗})_{I→w} = u_{I→φ∘w} ∘ φ^{⊗}`. -/
theorem k6pt_restrictFix_comp_coord {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : α → β) (I : Finset ι)
    (w : ↥I → α) (u : (ι → β) → ℂ) (y : ↥Iᶜ → α) :
    restrictFix I w (fun q => u fun i => φ (q i)) y =
      restrictFix I (fun j => φ (w j)) u (fun j => φ (y j)) := by
  unfold restrictFix glueFix
  show u _ = u _
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [hi]

/-- Cauchy-Schwarz + Jensen of Step 5: `𝔼 a^{1/4} b^{1/4} ≤ (𝔼 a)^{1/4} (𝔼 b)^{1/4}`. -/
theorem k6pt_expect_rpow_quarter_mul_le {κ : Type} [Fintype κ] (π : FinProb κ) (a b : κ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) :
    ∑ k, π.prob k * (a k ^ (1 / 4 : ℝ) * b k ^ (1 / 4 : ℝ)) ≤
      (∑ k, π.prob k * a k) ^ (1 / 4 : ℝ) * (∑ k, π.prob k * b k) ^ (1 / 4 : ℝ) := by
  have cs := wcs π
  have hq : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hh : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  -- Jensen for the square root
  have jen : ∀ c : κ → ℝ, (∀ k, 0 ≤ c k) →
      (∑ k, π.prob k * c k ^ (1 / 2 : ℝ)) ≤ (∑ k, π.prob k * c k) ^ (1 / 2 : ℝ) := by
    intro c hc
    have h1 := cs (fun k => c k ^ (1 / 2 : ℝ)) (fun _ => 1)
    have e1 : ∑ k, π.prob k * (c k ^ (1 / 2 : ℝ) * 1) = ∑ k, π.prob k * c k ^ (1 / 2 : ℝ) := by
      simp
    have e2 : ∑ k, π.prob k * (c k ^ (1 / 2 : ℝ)) ^ 2 = ∑ k, π.prob k * c k :=
      Finset.sum_congr rfl fun k _ => by rw [hh _ (hc k)]
    have e3 : ∑ k, π.prob k * (1 : ℝ) ^ 2 = 1 := by simp [π.sum_eq_one]
    rw [e1, e2, e3, mul_one] at h1
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le h1
  have hL := cs (fun k => a k ^ (1 / 4 : ℝ)) (fun k => b k ^ (1 / 4 : ℝ))
  have e1 : ∑ k, π.prob k * (a k ^ (1 / 4 : ℝ)) ^ 2 = ∑ k, π.prob k * a k ^ (1 / 2 : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [hq _ (ha k)]
  have e2 : ∑ k, π.prob k * (b k ^ (1 / 4 : ℝ)) ^ 2 = ∑ k, π.prob k * b k ^ (1 / 2 : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [hq _ (hb k)]
  rw [e1, e2] at hL
  have hA := jen a ha
  have hB := jen b hb
  have hA0 : 0 ≤ ∑ k, π.prob k * a k ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (π.nonneg k) (Real.rpow_nonneg (ha k) _)
  have hB0 : 0 ≤ ∑ k, π.prob k * b k ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (π.nonneg k) (Real.rpow_nonneg (hb k) _)
  have hSa : 0 ≤ ∑ k, π.prob k * a k := Finset.sum_nonneg fun k _ => mul_nonneg (π.nonneg k) (ha k)
  have hSb : 0 ≤ ∑ k, π.prob k * b k := Finset.sum_nonneg fun k _ => mul_nonneg (π.nonneg k) (hb k)
  set R := (∑ k, π.prob k * a k) ^ (1 / 4 : ℝ) * (∑ k, π.prob k * b k) ^ (1 / 4 : ℝ) with hR
  have hR0 : 0 ≤ R := mul_nonneg (Real.rpow_nonneg hSa _) (Real.rpow_nonneg hSb _)
  have hR2 : R ^ 2 = (∑ k, π.prob k * a k) ^ (1 / 2 : ℝ) * (∑ k, π.prob k * b k) ^ (1 / 2 : ℝ) := by
    rw [hR, mul_pow, hq _ hSa, hq _ hSb]
  have : (∑ k, π.prob k * (a k ^ (1 / 4 : ℝ) * b k ^ (1 / 4 : ℝ))) ^ 2 ≤ R ^ 2 := by
    rw [hR2]
    exact hL.trans (mul_le_mul hA hB hB0 (Real.rpow_nonneg hSa _))
  by_contra hcon
  have hcon' := not_le.mp hcon
  nlinarith [this, hcon', hR0]

/-- Steps 3-4 of Thm toswap (symmetrization and norm): for an exchange-symmetric law `μm` with
uniform `(w₁, w₃)`-marginal, `|𝔼 u₁(w₁) conj u₂(w₂) u₃(w₃) G(y,z)| ≤ val(u₁,u₃,u₁,u₃)^{1/2}`
whenever `u₂` and `G` are `1`-bounded (Supplement D, Lemma muminus-props (3), (4), (I2b)).
The hypotheses `hlab` and `hmirror` are added (without them the statement is false). -/
theorem k6pt_swap_norm_step {W B C : Type} [Fintype W] [Fintype B] [Fintype C] [DecidableEq W]
    [DecidableEq B] [DecidableEq C] (lab : W → Fin 3 → X) (hlab : Function.Injective lab)
    (μm : FinProb (W × B × C))
    (hexch : ∀ (w w' : W) (y : B) (z : C), lab w' = ![lab w 2, lab w 1, lab w 0] →
      μm.prob (w', y, z) = μm.prob (w, y, z))
    (hmirror : ∀ (w : W) (y : B) (z : C), 0 < μm.prob (w, y, z) →
      ∃ w' : W, lab w' = ![lab w 2, lab w 1, lab w 0])
    (hunif : ∀ a b : X, ∑ p ∈ univ.filter (fun p : W × B × C => lab p.1 0 = a ∧ lab p.1 2 = b),
      μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2)
    {κ : Type} [Fintype κ] [DecidableEq κ] (u₁ u₂ u₃ : (κ → X) → ℂ) (hu₂ : ∀ x, ‖u₂ x‖ ≤ 1)
    (G : (κ → B) → (κ → C) → ℂ) (hG : ∀ y z, ‖G y z‖ ≤ 1) :
    ‖(μm.pi κ).cexpect fun q =>
        u₁ (fun i => lab (q i).1 0) * star (u₂ fun i => lab (q i).1 1) *
          u₃ (fun i => lab (q i).1 2) * G (fun i => (q i).2.1) (fun i => (q i).2.2)‖ ≤
      ((val u₁ u₃ u₁ u₃).re) ^ (1 / 2 : ℝ) := by
  classical
  -- the mirror involution and its properties
  let m : W × B × C → W × B × C := fun t => (mirrorOf lab t.1, t.2)
  have hm : ∀ t, m (m t) = t := fun t => by
    simp only [m, mirrorOf_invol lab hlab]
  have hmp : ∀ t, μm.prob (m t) = μm.prob t := by
    rintro ⟨w, y, z⟩
    by_cases h : ∃ w', lab w' = ![lab w 2, lab w 1, lab w 0]
    · exact hexch w _ y z (mirrorOf_spec lab h)
    · simp only [m, mirrorOf_of_not lab h]
  set F : (κ → W × B × C) → ℂ := fun q =>
    u₁ (fun i => lab (q i).1 0) * star (u₂ fun i => lab (q i).1 1) *
      u₃ (fun i => lab (q i).1 2) * G (fun i => (q i).2.1) (fun i => (q i).2.2) with hF
  let Tb : (κ → Bool) → (κ → W × B × C) → (κ → W × B × C) :=
    fun b q i => if b i then m (q i) else q i
  -- symmetrization
  have hΛ : (μm.pi κ).cexpect F =
      ∑ q, (((μm.pi κ).prob q : ℝ) : ℂ) * 𝔼 b : κ → Bool, F (Tb b q) := by
    calc (μm.pi κ).cexpect F = 𝔼 _b : κ → Bool, (μm.pi κ).cexpect F :=
          (Finset.expect_const univ_nonempty _).symm
      _ = 𝔼 b : κ → Bool, ∑ q, (((μm.pi κ).prob q : ℝ) : ℂ) * F (Tb b q) :=
          Finset.expect_congr rfl fun b _ => cexpect_involution μm m hm hmp b F
      _ = _ := by
          rw [Finset.expect_sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_expect]
  -- the pointwise bound on the support
  have hpt : ∀ q : κ → W × B × C, (μm.pi κ).prob q ≠ 0 →
      ‖𝔼 b : κ → Bool, F (Tb b q)‖ ≤
        ‖swapU u₁ u₃ (fun i => lab (q i).1 0) (fun i => lab (q i).1 2)‖ := by
    intro q hq
    have hq' : ∀ i, μm.prob (q i) ≠ 0 := by
      have : ∏ i, μm.prob (q i) ≠ 0 := hq
      exact fun i => (Finset.prod_ne_zero_iff.1 this) i (mem_univ i)
    have hmir : ∀ i, lab (mirrorOf lab (q i).1) =
        ![lab (q i).1 2, lab (q i).1 1, lab (q i).1 0] := fun i =>
      mirrorOf_spec lab (hmirror (q i).1 (q i).2.1 (q i).2.2
        (lt_of_le_of_ne (μm.nonneg _) (Ne.symm (hq' i))))
    have hL : ∀ b : κ → Bool, F (Tb b q) =
        (u₁ (swapL b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2)) *
          u₃ (swapR b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2))) *
        (star (u₂ fun i => lab (q i).1 1) *
          G (fun i => (q i).2.1) (fun i => (q i).2.2)) := by
      intro b
      have e0 : (fun i => lab (Tb b q i).1 0) =
          swapL b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2) := by
        funext i
        by_cases hb : b i <;> simp [Tb, m, swapL, hb, hmir i]
      have e1 : (fun i => lab (Tb b q i).1 1) = fun i => lab (q i).1 1 := by
        funext i
        by_cases hb : b i <;> simp [Tb, m, hb, hmir i]
      have e2 : (fun i => lab (Tb b q i).1 2) =
          swapR b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2) := by
        funext i
        by_cases hb : b i <;> simp [Tb, m, swapR, hb, hmir i]
      have e3 : (fun i => (Tb b q i).2.1) = fun i => (q i).2.1 := by
        funext i
        by_cases hb : b i <;> simp [Tb, m, hb]
      have e4 : (fun i => (Tb b q i).2.2) = fun i => (q i).2.2 := by
        funext i
        by_cases hb : b i <;> simp [Tb, m, hb]
      simp only [hF, e0, e1, e2, e3, e4]
      ring
    simp only [hL]
    rw [← Finset.expect_mul, norm_mul]
    have : ‖star (u₂ fun i => lab (q i).1 1) * G (fun i => (q i).2.1) (fun i => (q i).2.2)‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      exact (mul_le_mul (hu₂ _) (hG _ _) (norm_nonneg _) zero_le_one).trans (by norm_num)
    calc ‖𝔼 b : κ → Bool, u₁ (swapL b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2)) *
          u₃ (swapR b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2))‖ * _
        ≤ ‖𝔼 b : κ → Bool, u₁ (swapL b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2)) *
          u₃ (swapR b (fun i => lab (q i).1 0) (fun i => lab (q i).1 2))‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by rw [mul_one]; rfl
  -- the law of the pair of outer letters
  have hX : Nonempty X := by
    have : Nonempty (W × B × C) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := μm.sum_eq_one
      simp at this
    obtain ⟨t⟩ := this
    exact ⟨lab t.1 0⟩
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  let φ : W × B × C → X × X := fun t => (lab t.1 0, lab t.1 2)
  let ρ := pushLaw μm φ
  have hρ : ∀ a : X × X, ρ.prob a = 1 / (Fintype.card X : ℝ) ^ 2 := by
    rintro ⟨a, b⟩
    rw [← hunif a b]
    show ∑ t ∈ univ.filter (fun t => φ t = (a, b)), μm.prob t = _
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp [φ]
  set g : (κ → X × X) → ℝ := fun p => ‖swapU u₁ u₃ (fun i => (p i).1) (fun i => (p i).2)‖ with hg
  -- first bound: the norm is at most `∑ P g`
  have h1 : ‖(μm.pi κ).cexpect F‖ ≤ ∑ p : κ → X × X, (ρ.pi κ).prob p * g p := by
    rw [hΛ, ← pi_pushforward μm φ g]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ((μm.pi κ).nonneg q)]
    by_cases hq : (μm.pi κ).prob q = 0
    · simp [hq]
    · exact mul_le_mul_of_nonneg_left (hpt q hq) ((μm.pi κ).nonneg q)
  -- second: Cauchy-Schwarz
  have h2 := wcs (ρ.pi κ) g (fun _ => 1)
  have hsq : ∑ p : κ → X × X, (ρ.pi κ).prob p * g p ^ 2 = (val u₁ u₃ u₁ u₃).re := by
    rw [val_pair_eq_expect_norm_sq, Complex.ofReal_re]
    have hpr : ∀ p : κ → X × X, (ρ.pi κ).prob p =
        (1 / (Fintype.card X : ℝ) ^ 2) ^ Fintype.card κ := by
      intro p
      show ∏ i, ρ.prob (p i) = _
      simp [hρ]
    simp_rw [hpr]
    rw [← Finset.mul_sum]
    have hS : ∑ p : κ → X × X, g p ^ 2 =
        ∑ x : κ → X, ∑ y : κ → X, ‖swapU u₁ u₃ x y‖ ^ 2 := by
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow κ (fun _ => X) (fun _ => X)) _ _ (fun p => by simp [hg])
    rw [hS]
    simp only [Fintype.expect_eq_sum_div_card, ← Finset.sum_div, Fintype.card_fun]
    push_cast
    field_simp
    have hc : ((1 : ℝ) / (Fintype.card X : ℝ) ^ 2) ^ Fintype.card κ *
        ((Fintype.card X : ℝ) ^ Fintype.card κ) ^ 2 = 1 := by
      rw [one_div, inv_pow, ← pow_mul, ← pow_mul, mul_comm 2 (Fintype.card κ)]
      exact inv_mul_cancel₀ (pow_ne_zero _ hcard.ne')
    rw [mul_right_comm, hc, one_mul]
  have h3 : (∑ p : κ → X × X, (ρ.pi κ).prob p * g p) ^ 2 ≤ (val u₁ u₃ u₁ u₃).re := by
    have e1 : ∑ p : κ → X × X, (ρ.pi κ).prob p * (g p * 1) = ∑ p : κ → X × X, (ρ.pi κ).prob p * g p := by
      simp
    have e3 : ∑ p : κ → X × X, (ρ.pi κ).prob p * (1 : ℝ) ^ 2 = 1 := by simp [(ρ.pi κ).sum_eq_one]
    rw [e1, e3, mul_one, hsq] at h2
    exact h2
  have hre : 0 ≤ (val u₁ u₃ u₁ u₃).re := val_re_nonneg_pair _ _
  rw [← Real.sqrt_eq_rpow]
  exact h1.trans (Real.le_sqrt_of_sq_le h3)

/-- the core of Thm toswap (uniform): the abstract form for a mixture `π = a₀ μm + (1-a₀) ν`. -/
private lemma toswap_core {W B C : Type} [Fintype W] [Fintype B] [Fintype C] [DecidableEq W]
    [DecidableEq B] [DecidableEq C] (lab : W → Fin 3 → X) (hlab : Function.Injective lab)
    (π μm ν : FinProb (W × B × C)) (νs : FinProb X) {a₀ : ℝ} (h0 : 0 ≤ a₀) (h1 : a₀ ≤ 1)
    (hdec : ∀ p, π.prob p = a₀ * μm.prob p + (1 - a₀) * ν.prob p)
    (hexch : ∀ (w w' : W) (y : B) (z : C), lab w' = ![lab w 2, lab w 1, lab w 0] →
      μm.prob (w', y, z) = μm.prob (w, y, z))
    (hmirror : ∀ (w : W) (y : B) (z : C), 0 < μm.prob (w, y, z) →
      ∃ w' : W, lab w' = ![lab w 2, lab w 1, lab w 0])
    (hunif : ∀ a b : X, ∑ p ∈ univ.filter (fun p : W × B × C => lab p.1 0 = a ∧ lab p.1 2 = b),
      μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2)
    (hl0 : ∀ a : X, ∑ p ∈ univ.filter (fun p : W × B × C => lab p.1 0 = a), ν.prob p = νs.prob a)
    (hl2 : ∀ a : X, ∑ p ∈ univ.filter (fun p : W × B × C => lab p.1 2 = a), ν.prob p = νs.prob a)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g' : (ι → B) → ℂ)
    (h' : (ι → C) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g' y‖ ≤ 1) (hh : ∀ z, ‖h' z‖ ≤ 1) :
    ‖(π.pi ι).cexpect (fun q => f (fun i => lab (q i).1 0) * star (f fun i => lab (q i).1 1) *
        f (fun i => lab (q i).1 2) * g' (fun i => (q i).2.1) * h' (fun i => (q i).2.2))‖ ≤
      ((subsetExpect (1 - a₀) (by linarith) (by linarith) fun I =>
          (νs.pi ↥I).cexpect fun z => (((val (restrictFix I z f) (restrictFix I z f)
            (restrictFix I z f) (restrictFix I z f)).re : ℝ) : ℂ)).re) ^ (1 / 2 : ℝ) := by
  classical
  -- restriction of the integrand
  have hR : ∀ (I : Finset ι) (w : ↥I → W × B × C) (y' : ↥Iᶜ → W × B × C),
      restrictFix I w (fun q => f (fun i => lab (q i).1 0) * star (f fun i => lab (q i).1 1) *
        f (fun i => lab (q i).1 2) * g' (fun i => (q i).2.1) * h' (fun i => (q i).2.2)) y' =
      restrictFix I (fun j => lab (w j).1 0) f (fun j => lab (y' j).1 0) *
        star (restrictFix I (fun j => lab (w j).1 1) f (fun j => lab (y' j).1 1)) *
        restrictFix I (fun j => lab (w j).1 2) f (fun j => lab (y' j).1 2) *
        (restrictFix I (fun j => (w j).2.1) g' (fun j => (y' j).2.1) *
          restrictFix I (fun j => (w j).2.2) h' (fun j => (y' j).2.2)) := by
    intro I w y'
    have e0 := k6pt_restrictFix_comp_coord (fun t : W × B × C => lab t.1 0) I w f y'
    have e1 := k6pt_restrictFix_comp_coord (fun t : W × B × C => lab t.1 1) I w f y'
    have e2 := k6pt_restrictFix_comp_coord (fun t : W × B × C => lab t.1 2) I w f y'
    have e3 := k6pt_restrictFix_comp_coord (fun t : W × B × C => t.2.1) I w g' y'
    have e4 := k6pt_restrictFix_comp_coord (fun t : W × B × C => t.2.2) I w h' y'
    rw [← e0, ← e1, ← e2, ← e3, ← e4]
    unfold restrictFix
    beta_reduce
    ring
  -- the Cauchy-Schwarz step for fixed `I` and `w`
  have hstep : ∀ (I : Finset ι) (w : ↥I → W × B × C),
      ‖(μm.pi ↥Iᶜ).cexpect (restrictFix I w (fun q => f (fun i => lab (q i).1 0) *
        star (f fun i => lab (q i).1 1) * f (fun i => lab (q i).1 2) *
        g' (fun i => (q i).2.1) * h' (fun i => (q i).2.2)))‖ ≤
      ((val (restrictFix I (fun j => lab (w j).1 0) f) (restrictFix I (fun j => lab (w j).1 2) f)
        (restrictFix I (fun j => lab (w j).1 0) f)
        (restrictFix I (fun j => lab (w j).1 2) f)).re) ^ (1 / 2 : ℝ) := by
    intro I w
    have := k6pt_swap_norm_step (X := X) lab hlab μm hexch hmirror hunif (κ := ↥Iᶜ)
      (restrictFix I (fun j => lab (w j).1 0) f) (restrictFix I (fun j => lab (w j).1 1) f)
      (restrictFix I (fun j => lab (w j).1 2) f) (fun x => hf _)
      (fun y z => restrictFix I (fun j => (w j).2.1) g' y *
        restrictFix I (fun j => (w j).2.2) h' z)
      (fun y z => by
        rw [norm_mul]
        exact (mul_le_mul (hg _) (hh _) (norm_nonneg _) zero_le_one).trans (by norm_num))
    convert this using 3
    funext q
    rw [hR]
  -- bookkeeping
  let Φ : ∀ I : Finset ι, (↥I → X) → ℝ := fun I z => (val (restrictFix I z f) (restrictFix I z f)
    (restrictFix I z f) (restrictFix I z f)).re
  let Vf : Finset ι → ℝ := fun I => ∑ z, (νs.pi ↥I).prob z * Φ I z
  have hΦ0 : ∀ I z, 0 ≤ Φ I z := fun I z => val_re_nonneg_pair _ _
  have hVf0 : ∀ I, 0 ≤ Vf I := fun I =>
    Finset.sum_nonneg fun z _ => mul_nonneg ((νs.pi ↥I).nonneg z) (hΦ0 I z)
  have hpush : ∀ (I : Finset ι) (φ : W × B × C → X),
      (∀ a : X, ∑ p ∈ univ.filter (fun p : W × B × C => φ p = a), ν.prob p = νs.prob a) →
      ∑ w : ↥I → W × B × C, (ν.pi ↥I).prob w * Φ I (fun j => φ (w j)) = Vf I := by
    intro I φ hφ
    rw [pi_pushforward ν φ (Φ I)]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    show ∏ i, (pushLaw ν φ).prob (z i) = ∏ i, νs.prob (z i)
    exact Finset.prod_congr rfl fun i _ => hφ (z i)
  have hinner : ∀ I : Finset ι, ‖(ν.pi ↥I).cexpect fun w => (μm.pi ↥Iᶜ).cexpect
      (restrictFix I w (fun q => f (fun i => lab (q i).1 0) * star (f fun i => lab (q i).1 1) *
        f (fun i => lab (q i).1 2) * g' (fun i => (q i).2.1) * h' (fun i => (q i).2.2)))‖ ≤
      Vf I ^ (1 / 2 : ℝ) := by
    intro I
    refine (norm_cexpect_le _ _).trans ?_
    calc ∑ w, (ν.pi ↥I).prob w * ‖(μm.pi ↥Iᶜ).cexpect
          (restrictFix I w (fun q => f (fun i => lab (q i).1 0) * star (f fun i => lab (q i).1 1) *
            f (fun i => lab (q i).1 2) * g' (fun i => (q i).2.1) * h' (fun i => (q i).2.2)))‖
        ≤ ∑ w, (ν.pi ↥I).prob w * (Φ I (fun j => lab (w j).1 0) ^ (1 / 4 : ℝ) *
            Φ I (fun j => lab (w j).1 2) ^ (1 / 4 : ℝ)) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
            ((hstep I w).trans (rpow_half_le_quarter_mul (val_re_nonneg_pair _ _) (hΦ0 _ _)
              (hΦ0 _ _) (val_pair_sq_le _ _))) ((ν.pi ↥I).nonneg w)
      _ ≤ (∑ w, (ν.pi ↥I).prob w * Φ I (fun j => lab (w j).1 0)) ^ (1 / 4 : ℝ) *
          (∑ w, (ν.pi ↥I).prob w * Φ I (fun j => lab (w j).1 2)) ^ (1 / 4 : ℝ) :=
          k6pt_expect_rpow_quarter_mul_le (ν.pi ↥I) _ _ (fun w => hΦ0 _ _) (fun w => hΦ0 _ _)
      _ = Vf I ^ (1 / 2 : ℝ) := by
          rw [hpush I (fun p => lab p.1 0) hl0, hpush I (fun p => lab p.1 2) hl2,
            rpow_quarter_mul_self (hVf0 I)]
  have hT : (subsetExpect (1 - a₀) (by linarith) (by linarith) fun I =>
      (νs.pi ↥I).cexpect fun z => (((val (restrictFix I z f) (restrictFix I z f)
        (restrictFix I z f) (restrictFix I z f)).re : ℝ) : ℂ)).re =
      ∑ s, ((bernoulli (1 - a₀) (by linarith) (by linarith)).pi ι).prob s * Vf (trueSet s) := by
    unfold subsetExpect
    simp only [cexpect_ofReal]
    rw [Complex.ofReal_re]
  have hVT0 : 0 ≤ ∑ s, ((bernoulli (1 - a₀) (by linarith) (by linarith)).pi ι).prob s *
      Vf (trueSet s) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (((bernoulli (1 - a₀) (by linarith)
      (by linarith)).pi ι).nonneg s) (hVf0 _)
  rw [mixture_calculus h0 h1 π ν μm (fun a => by rw [hdec]; ring), hT]
  unfold subsetExpect
  refine (norm_cexpect_le _ _).trans ?_
  calc ∑ s, ((bernoulli (1 - a₀) (by linarith) (by linarith)).pi ι).prob s *
        ‖(ν.pi ↥(trueSet s)).cexpect fun w => (μm.pi ↥(trueSet s)ᶜ).cexpect
          (restrictFix (trueSet s) w (fun q => f (fun i => lab (q i).1 0) *
            star (f fun i => lab (q i).1 1) * f (fun i => lab (q i).1 2) *
            g' (fun i => (q i).2.1) * h' (fun i => (q i).2.2)))‖
      ≤ ∑ s, ((bernoulli (1 - a₀) (by linarith) (by linarith)).pi ι).prob s *
          (Vf (trueSet s) ^ (1 / 4 : ℝ) * Vf (trueSet s) ^ (1 / 4 : ℝ)) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          ((hinner _).trans (rpow_quarter_mul_self (hVf0 _)).ge) (((bernoulli (1 - a₀)
            (by linarith) (by linarith)).pi ι).nonneg s)
    _ ≤ _ := k6pt_expect_rpow_quarter_mul_le _ _ _ (fun s => hVf0 _) (fun s => hVf0 _)
    _ = _ := rpow_quarter_mul_self hVT0

/-- `ν_*` exists: `μ_x = (1 - α_*) ν_* + α_* U` with `ν_*` a probability measure (Prop.
uniform-weight (c)); the weight is `k6ptAlphaStar α`. -/
theorem k6pt_nuStar_exists (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support) {α : ℝ}
    (hα : 0 < α) (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) :
    ∃ νs : FinProb X, ∀ a, k6ptMargX μ a =
      (1 - k6ptAlphaStar α) * νs.prob a + k6ptAlphaStar α * (1 / (Fintype.card X : ℝ)) := by
  have hr₁ := one_le_k6ptR1 α
  have hr₂ := one_le_k6ptR2 α
  have hc₁ : 2 / α ≤ 2 ^ k6ptR1 α := by
    have := k6ptR1_spec hα
    linarith
  have hc₂ : 2 / α ^ 2 ^ k6ptR1 α ≤ 2 ^ k6ptR2 α := by
    have := k6ptR2_spec hα
    linarith
  have h₁ := k6pt_threshold_one μ hμ hα hatom hc₁
  have h₂ := k6pt_threshold_two μ hμ hα hatom hr₁ hc₂
  have hβ : 0 < α ^ k6ptN (k6ptR1 α) (k6ptR2 α) := pow_pos hα _
  obtain ⟨pt, μm, ν, h1, h2, h3, h4, hdec⟩ := k6pt_mu_minus_uniform μ hμ hr₁ hr₂ h₁ h₂ hβ
    (k6ptMuPlus_atom_ge μ hα hatom hr₁ hr₂)
  have hlaw := fun a => (k6pt_nu_letter_law μ hr₁ hr₂ μm ν hdec h4 a).1
  have ha1 : 0 < 1 - k6ptAlphaStar α := by linarith [k6ptAlphaStar_le_half α]
  refine ⟨⟨fun a => ∑ p ∈ univ.filter (fun p : K6ptSig μ (k6ptR1 α) hr₁ (k6ptR2 α) hr₂ ×
      K6ptGam μ (k6ptR1 α) hr₁ × K6ptPhi μ (k6ptR1 α) hr₁ (k6ptR2 α) hr₂ => p.1.1 0 = a),
      ν.prob p, fun a => Finset.sum_nonneg fun p _ => ν.nonneg p, ?_⟩, fun a => ?_⟩
  · rw [Finset.sum_fiberwise univ (fun p : K6ptSig μ (k6ptR1 α) hr₁ (k6ptR2 α) hr₂ ×
      K6ptGam μ (k6ptR1 α) hr₁ × K6ptPhi μ (k6ptR1 α) hr₁ (k6ptR2 α) hr₂ => p.1.1 0) ν.prob]
    exact ν.sum_eq_one
  · have := hlaw a
    show _ = (1 - k6ptAlphaStar α) * (∑ p ∈ _, ν.prob p) + _
    have e : k6ptAlphaStar α * (1 / (Fintype.card X : ℝ)) = k6ptAlphaStar α / (Fintype.card X : ℝ) := by
      ring
    rw [e]
    unfold k6ptAlphaStar at this ⊢
    linarith

/-- Thm toswap (uniform form): `𝔼_{I ∼_{1-α_*}, z ∼ ν_*^I} val(f_{I→z}) ≥ ε^{2N}`;
`α_* = k6ptAlphaStar α`, `N = k6ptN (k6ptR1 α) (k6ptR2 α)`, all functions on an arbitrary finite
coordinate type `ι`. -/
theorem k6pt_toswap_uniform (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support)
    {α : ℝ} (hα : 0 < α) (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) (νs : FinProb X)
    (hνs : ∀ a, k6ptMargX μ a =
      (1 - k6ptAlphaStar α) * νs.prob a + k6ptAlphaStar α * (1 / (Fintype.card X : ℝ)))
    {ε : ℝ} (hε : 0 < ε) (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ)
    (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hh : ∀ z, ‖h z‖ ≤ 1)
    (hcorr : ε ≤ ‖(μ.pi ι).cexpect fun p =>
      f (fun i => (p i).1) * g (fun i => (p i).2.1) * h (fun i => (p i).2.2)‖) :
    ε ^ (2 * k6ptN (k6ptR1 α) (k6ptR2 α)) ≤
      (subsetExpect (1 - k6ptAlphaStar α) (by linarith [k6ptAlphaStar_le_half α])
        (by linarith [k6ptAlphaStar_pos hα]) fun I =>
          (νs.pi ↥I).cexpect fun z => (((val (restrictFix I z f) (restrictFix I z f)
            (restrictFix I z f) (restrictFix I z f)).re : ℝ) : ℂ)).re := by
  classical
  have hr₁ := one_le_k6ptR1 α
  have hr₂ := one_le_k6ptR2 α
  have hc₁ : 2 / α ≤ 2 ^ k6ptR1 α := by
    have := k6ptR1_spec hα
    linarith
  have hc₂ : 2 / α ^ 2 ^ k6ptR1 α ≤ 2 ^ k6ptR2 α := by
    have := k6ptR2_spec hα
    linarith
  have h₁ := k6pt_threshold_one μ hμ hα hatom hc₁
  have h₂ := k6pt_threshold_two μ hμ hα hatom hr₁ hc₂
  have hβ : 0 < α ^ k6ptN (k6ptR1 α) (k6ptR2 α) := pow_pos hα _
  obtain ⟨pt, μm, ν, h1, h2, h3, h4, hdec⟩ := k6pt_mu_minus_uniform μ hμ hr₁ hr₂ h₁ h₂ hβ
    (k6ptMuPlus_atom_ge μ hα hatom hr₁ hr₂)
  have hlaw := fun a => k6pt_nu_letter_law μ hr₁ hr₂ μm ν hdec h4 a
  have ha1 : 0 < 1 - k6ptAlphaStar α := by linarith [k6ptAlphaStar_le_half α]
  have hlet : ∀ (a : X) (S : ℝ),
      (1 - k6ptAlphaStar α) * S = k6ptMargX μ a - k6ptAlphaStar α / (Fintype.card X : ℝ) →
      S = νs.prob a := by
    intro a S hS
    have e : k6ptAlphaStar α * (1 / (Fintype.card X : ℝ)) =
        k6ptAlphaStar α / (Fintype.card X : ℝ) := by ring
    have := hνs a
    rw [e] at this
    exact mul_left_cancel₀ ha1.ne' (by linarith)
  have hl0 := fun a => hlet a _ (hlaw a).1
  have hl2 := fun a => hlet a _ (hlaw a).2
  obtain ⟨g', h', hg', hh', hb⟩ := k6pt_eq3path_eps μ hr₁ hr₂ ι f g h hf hg hh hε.le hcorr
  have hcore := toswap_core (fun w => w.1) Subtype.val_injective
    (k6ptMuPlus μ (k6ptR1 α) hr₁ (k6ptR2 α) hr₂) μm ν νs (a₀ := k6ptAlphaStar α)
    (k6ptAlphaStar_pos hα).le (by linarith [k6ptAlphaStar_le_half α]) hdec h3
    (k6pt_mirror_of_mu_minus_uniform μ hr₁ hr₂ pt μm h1 h2) h4
    hl0 hl2 f g' h' hf hg' hh'
  have hε' : 0 < ε ^ k6ptN (k6ptR1 α) (k6ptR2 α) := pow_pos hε _
  have hle := hb.trans hcore
  rw [← Real.sqrt_eq_rpow] at hle
  have := (Real.le_sqrt' hε').1 hle
  rw [pow_mul'] 
  exact this

end ToswapUniform

end TrackB
end RestrictedPolynomials
end
