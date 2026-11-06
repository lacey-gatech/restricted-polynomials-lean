module

public import RestrictedPolynomials.TrackB.S8Split
public import RestrictedPolynomials.TrackB.SwapSvd

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Engine
variable {R A : Type} [Fintype R] [Fintype A]

private lemma uinner_eq_sum' {S : Type*} [Fintype S] (u v : S → ℂ) :
    uinner u v = (∑ s, u s * star (v s)) / (Fintype.card S : ℂ) := by
  simp [uinner, Fintype.expect_eq_sum_div_card]

private lemma hdiv (z : ℂ) (x : ℝ) : star (z / (x : ℂ)) = star z / (x : ℂ) := by
  simp

private lemma sqrt_cast_mul_self (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- the weighted singular value decomposition of a matrix `M : R → A → ℂ` for the weights `DR`, `DA`
(positive), by rescaling with `√DR`, `√DA` and the uniform `svd_exists`. -/
theorem s8svdaux_svd_weighted (DR : FinProb R) (DA : FinProb A) (hR : ∀ r, 0 < DR.prob r)
    (hA : ∀ a, 0 < DA.prob a) (M : R → A → ℂ) :
    ∃ (s : ℕ) (κ : Fin s → ℝ) (gI : Fin s → R → ℂ) (gJ : Fin s → A → ℂ),
      (∀ t, 0 < κ t) ∧ (∀ r a, M r a = ∑ t, (κ t : ℂ) * (gI t r * gJ t a)) ∧
      (∀ t t', DR.cinner (gI t) (gI t') = if t = t' then 1 else 0) ∧
      (∀ t t', DA.cinner (gJ t) (gJ t') = if t = t' then 1 else 0) := by
  classical
  let N : R → A → ℂ := fun r a =>
    ((Real.sqrt (DR.prob r) * Real.sqrt (DA.prob a) : ℝ) : ℂ) * M r a
  obtain ⟨s, lam, g, h, hs⟩ := svd_exists N
  have hcardR : ∀ t : Fin s, 0 < Fintype.card R := fun t => by
    by_contra h0
    have h1 := hs.orth_g t t
    rw [uinner_eq_sum', Nat.eq_zero_of_not_pos h0] at h1
    simp at h1
  have hcardA : ∀ t : Fin s, 0 < Fintype.card A := fun t => by
    by_contra h0
    have h1 := hs.orth_h t t
    rw [uinner_eq_sum', Nat.eq_zero_of_not_pos h0] at h1
    simp at h1
  have hcR : ∀ t : Fin s, 0 < Real.sqrt (Fintype.card R) := fun t =>
    Real.sqrt_pos.2 (by exact_mod_cast hcardR t)
  have hcA : ∀ t : Fin s, 0 < Real.sqrt (Fintype.card A) := fun t =>
    Real.sqrt_pos.2 (by exact_mod_cast hcardA t)
  refine ⟨s, fun t => lam t * Real.sqrt (Fintype.card R) * Real.sqrt (Fintype.card A),
    fun t r => g t r / ((Real.sqrt (DR.prob r) * Real.sqrt (Fintype.card R) : ℝ) : ℂ),
    fun t a => h t a / ((Real.sqrt (DA.prob a) * Real.sqrt (Fintype.card A) : ℝ) : ℂ),
    fun t => mul_pos (mul_pos (hs.pos t) (hcR t)) (hcA t), ?_, ?_, ?_⟩
  · intro r a
    have hr : 0 < Real.sqrt (DR.prob r) := Real.sqrt_pos.2 (hR r)
    have ha : 0 < Real.sqrt (DA.prob a) := Real.sqrt_pos.2 (hA a)
    have hr0 : ((Real.sqrt (DR.prob r) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have ha0 : ((Real.sqrt (DA.prob a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hd := hs.decomp r a
    have key : ((Real.sqrt (DR.prob r) : ℝ) : ℂ) * ((Real.sqrt (DA.prob a) : ℝ) : ℂ) * M r a =
        ∑ i, (lam i : ℂ) * g i r * h i a := by
      simpa [N] using hd
    have hcR' : ∀ t : Fin s, ((Real.sqrt (Fintype.card R) : ℝ) : ℂ) ≠ 0 := fun t => by
      exact_mod_cast (hcR t).ne'
    have hcA' : ∀ t : Fin s, ((Real.sqrt (Fintype.card A) : ℝ) : ℂ) ≠ 0 := fun t => by
      exact_mod_cast (hcA t).ne'
    have hterm : ∀ t : Fin s, (((lam t * Real.sqrt (Fintype.card R) * Real.sqrt (Fintype.card A) : ℝ)
        : ℂ)) * (g t r / ((Real.sqrt (DR.prob r) * Real.sqrt (Fintype.card R) : ℝ) : ℂ) *
        (h t a / ((Real.sqrt (DA.prob a) * Real.sqrt (Fintype.card A) : ℝ) : ℂ))) =
        ((lam t : ℂ) * g t r * h t a) /
          (((Real.sqrt (DR.prob r) : ℝ) : ℂ) * ((Real.sqrt (DA.prob a) : ℝ) : ℂ)) := by
      intro t
      have := hcR' t
      have := hcA' t
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, ← key]
    field_simp
  · intro t t'
    have h1 := hs.orth_g t t'
    rw [uinner_eq_sum'] at h1
    rw [cinner_def]
    have hterm : ∀ r : R, (DR.prob r : ℂ) *
        (g t r / ((Real.sqrt (DR.prob r) * Real.sqrt (Fintype.card R) : ℝ) : ℂ) *
          star (g t' r / ((Real.sqrt (DR.prob r) * Real.sqrt (Fintype.card R) : ℝ) : ℂ))) =
        (g t r * star (g t' r)) / (Fintype.card R : ℂ) := by
      intro r
      have hr0 : (DR.prob r : ℂ) ≠ 0 := by exact_mod_cast (hR r).ne'
      have hc0 : ((Real.sqrt (Fintype.card R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hcR t).ne'
      have hr1 : ((Real.sqrt (DR.prob r) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 (hR r)).ne'
      have e1 := sqrt_cast_mul_self (DR.prob r) (hR r).le
      have e2 := sqrt_cast_mul_self (Fintype.card R : ℝ) (Nat.cast_nonneg _)
      rw [hdiv]
      push_cast at e2 ⊢
      rw [div_mul_div_comm, ← e1, ← e2]
      field_simp
    rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.sum_div]
    exact h1
  · intro t t'
    have h1 := hs.orth_h t t'
    rw [uinner_eq_sum'] at h1
    rw [cinner_def]
    have hterm : ∀ a : A, (DA.prob a : ℂ) *
        (h t a / ((Real.sqrt (DA.prob a) * Real.sqrt (Fintype.card A) : ℝ) : ℂ) *
          star (h t' a / ((Real.sqrt (DA.prob a) * Real.sqrt (Fintype.card A) : ℝ) : ℂ))) =
        (h t a * star (h t' a)) / (Fintype.card A : ℂ) := by
      intro a
      have hr0 : (DA.prob a : ℂ) ≠ 0 := by exact_mod_cast (hA a).ne'
      have hc0 : ((Real.sqrt (Fintype.card A) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hcA t).ne'
      have hr1 : ((Real.sqrt (DA.prob a) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 (hA a)).ne'
      have e1 := sqrt_cast_mul_self (DA.prob a) (hA a).le
      have e2 := sqrt_cast_mul_self (Fintype.card A : ℝ) (Nat.cast_nonneg _)
      rw [hdiv]
      push_cast at e2 ⊢
      rw [div_mul_div_comm, ← e1, ← e2]
      field_simp
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div]
    exact h1


/-- contraction formulas for a decomposition with orthonormal families on `{κ ≠ 0}`:
`κ_p gI_p(r) = ⟨M(r,·), gJ_p⟩` and `κ_p gJ_p(a) = ⟨M(·,a), gI_p⟩`. -/
theorem s8svdaux_cf {P : Type} [Fintype P] [DecidableEq P] (DR : FinProb R) (DA : FinProb A)
    (κ : P → ℝ) (gI : P → R → ℂ) (gJ : P → A → ℂ) (M : R → A → ℂ)
    (hM : ∀ r a, M r a = ∑ p, (κ p : ℂ) * (gI p r * gJ p a))
    (hI : ∀ p q, κ p ≠ 0 → κ q ≠ 0 → DR.cinner (gI p) (gI q) = if p = q then 1 else 0)
    (hJ : ∀ p q, κ p ≠ 0 → κ q ≠ 0 → DA.cinner (gJ p) (gJ q) = if p = q then 1 else 0) :
    (∀ p r, κ p ≠ 0 → (κ p : ℂ) * gI p r = DA.cexpect (fun a => M r a * star (gJ p a))) ∧
    (∀ p a, κ p ≠ 0 → (κ p : ℂ) * gJ p a = DR.cexpect (fun r => M r a * star (gI p r))) := by
  constructor
  · intro p r hp
    have h1 : DA.cexpect (fun a => M r a * star (gJ p a)) =
        ∑ q, (κ q : ℂ) * (gI q r * DA.cinner (gJ q) (gJ p)) := by
      simp only [FinProb.cexpect, cinner_def, hM, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => by ring
    rw [h1, Finset.sum_eq_single p]
    · rw [hJ p p hp hp]; simp
    · intro q _ hq
      by_cases hq0 : κ q = 0
      · simp [hq0]
      · rw [hJ q p hq0 hp]; simp [hq]
    · simp
  · intro p a hp
    have h1 : DR.cexpect (fun r => M r a * star (gI p r)) =
        ∑ q, (κ q : ℂ) * (gJ q a * DR.cinner (gI q) (gI p)) := by
      simp only [FinProb.cexpect, cinner_def, hM, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => by ring
    rw [h1, Finset.sum_eq_single p]
    · rw [hI p p hp hp]; simp
    · intro q _ hq
      by_cases hq0 : κ q = 0
      · simp [hq0]
      · rw [hI q p hq0 hp]; simp [hq]
    · simp

/-- the Gram form: `⟨T v, v'⟩ = ∑_r w_r conj(C_v(r)) C_{v'}(r)`. -/
theorem s8svdaux_inner_T (DR : FinProb R) (DA : FinProb A) (M : R → A → ℂ) (v v' : A → ℂ) :
    DA.cinner (fun a => ∑ r, (DR.prob r : ℂ) * (M r a * ∑ b, (DA.prob b : ℂ) *
        (star (M r b) * v b))) v' =
      ∑ r, (DR.prob r : ℂ) * (star (DA.cexpect (fun a => M r a * star (v a))) *
        DA.cexpect (fun a => M r a * star (v' a))) := by
  have hst : ∀ r, star (DA.cexpect (fun a => M r a * star (v a))) =
      ∑ b, (DA.prob b : ℂ) * (star (M r b) * v b) := fun r => by
    simp only [FinProb.cexpect, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show star (DA.prob b : ℂ) = DA.prob b by simp]
  rw [cinner_def]
  simp only [hst]
  simp only [FinProb.cexpect, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => by ring


private lemma cexp_sub {β : Type*} [Fintype β] (π : FinProb β) (f g : β → ℂ) :
    π.cexpect (fun a => f a - g a) = π.cexpect f - π.cexpect g := by
  simp [FinProb.cexpect, mul_sub, Finset.sum_sub_distrib]

private lemma cexp_sum {β γ : Type*} [Fintype β] (π : FinProb β) (s : Finset γ) (f : γ → β → ℂ) :
    π.cexpect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, π.cexpect (f i) := by
  simp only [FinProb.cexpect, Finset.mul_sum]
  exact Finset.sum_comm

private lemma cexp_mul_const {β : Type*} [Fintype β] (π : FinProb β) (c : ℂ) (f : β → ℂ) :
    π.cexpect (fun a => c * f a) = c * π.cexpect f := by
  simp only [FinProb.cexpect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [Fintype R] in
private lemma peel_contr {Λ : Type} [Fintype Λ] (DA : FinProb A) (M : R → A → ℂ)
    (e : Λ → A → ℂ) (v : A → ℂ) (r : R) :
    DA.cexpect (fun a => (M r a - ∑ χ, DA.cexpect (fun a => M r a * star (e χ a)) * e χ a) *
        star (v a)) =
      DA.cexpect (fun a => M r a * star (v a)) -
        ∑ χ, DA.cexpect (fun a => M r a * star (e χ a)) * DA.cinner (e χ) v := by
  have : ∀ a, (M r a - ∑ χ, DA.cexpect (fun a => M r a * star (e χ a)) * e χ a) * star (v a) =
      M r a * star (v a) - ∑ χ, DA.cexpect (fun a => M r a * star (e χ a)) *
        (e χ a * star (v a)) := fun a => by
    rw [sub_mul, Finset.sum_mul]
    simp only [mul_assoc]
  simp only [this]
  rw [cexp_sub, cexp_sum]
  simp only [cexp_mul_const]
  rfl

/-- the SVD of `M` adapted to a family `e` of orthonormal eigenvectors of the Gram operator
`T v (a) = ∑_r w_r M(r,a) ∑_b d_b conj(M(r,b)) v(b)`: the `e χ` are among the right singular vectors. -/
theorem s8svdaux_svd_peel {Λ : Type} [Fintype Λ] [DecidableEq Λ] (DR : FinProb R) (DA : FinProb A)
    (hR : ∀ r, 0 < DR.prob r) (hA : ∀ a, 0 < DA.prob a) (M : R → A → ℂ) (e : Λ → A → ℂ)
    (he : ∀ χ ψ, DA.cinner (e χ) (e ψ) = if χ = ψ then 1 else 0)
    (hT : ∀ χ, ∃ c : ℂ, ∀ a, (∑ r, (DR.prob r : ℂ) * (M r a *
        ∑ b, (DA.prob b : ℂ) * (star (M r b) * e χ b))) = c * e χ a) :
    ∃ (s : ℕ) (κ : Λ ⊕ Fin s → ℝ) (gI : Λ ⊕ Fin s → R → ℂ) (gJ : Λ ⊕ Fin s → A → ℂ),
      (∀ p, 0 ≤ κ p) ∧ (∀ t, 0 < κ (Sum.inr t)) ∧
      (∀ r a, M r a = ∑ p, (κ p : ℂ) * (gI p r * gJ p a)) ∧
      (∀ χ, gJ (Sum.inl χ) = e χ) ∧ (∀ t χ, DA.cinner (gJ (Sum.inr t)) (e χ) = 0) ∧
      (∀ p q, κ p ≠ 0 → κ q ≠ 0 → DR.cinner (gI p) (gI q) = if p = q then 1 else 0) ∧
      (∀ p q, κ p ≠ 0 → κ q ≠ 0 → DA.cinner (gJ p) (gJ q) = if p = q then 1 else 0) ∧
      (∀ p r, κ p ≠ 0 → (κ p : ℂ) * gI p r = DA.cexpect (fun a => M r a * star (gJ p a))) ∧
      (∀ p, κ p = 0 → gI p = 0) := by
  classical
  let C : (A → ℂ) → R → ℂ := fun v r => DA.cexpect (fun a => M r a * star (v a))
  let Mp : R → A → ℂ := fun r a => M r a - ∑ χ, C (e χ) r * e χ a
  have hMp0 : ∀ r ψ, DA.cexpect (fun a => Mp r a * star (e ψ a)) = 0 := by
    intro r ψ
    have := peel_contr DA M e (e ψ) r
    simp only [Mp, C]
    rw [this]
    simp [he]
  obtain ⟨s, κt, gIt, gJt, hκt, hdec, hIt, hJt⟩ := s8svdaux_svd_weighted DR DA hR hA Mp
  obtain ⟨cfI, cfJ⟩ := s8svdaux_cf DR DA κt gIt gJt Mp hdec (fun p q _ _ => hIt p q)
    (fun p q _ _ => hJt p q)
  have hperp : ∀ t ψ, DA.cinner (gJt t) (e ψ) = 0 := by
    intro t ψ
    have h0 : (κt t : ℂ) * DA.cinner (gJt t) (e ψ) = 0 := by
      have e1 : (κt t : ℂ) * DA.cinner (gJt t) (e ψ) =
          ∑ a, (DA.prob a : ℂ) * (((κt t : ℂ) * gJt t a) * star (e ψ a)) := by
        rw [cinner_def, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [e1, Finset.sum_congr rfl fun a _ => by rw [cfJ t a (hκt t).ne']]
      have e2 : ∑ a, (DA.prob a : ℂ) * (DR.cexpect (fun r => Mp r a * star (gIt t r)) *
          star (e ψ a)) =
          ∑ r, (DR.prob r : ℂ) * (star (gIt t r) * DA.cexpect (fun a => Mp r a * star (e ψ a))) := by
        simp only [FinProb.cexpect, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => by ring
      rw [e2]
      simp only [hMp0, mul_zero, Finset.sum_const_zero]
    exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast (hκt t).ne')
  have hCt : ∀ t r, C (gJt t) r = (κt t : ℂ) * gIt t r := by
    intro t r
    have e1 := peel_contr DA M e (gJt t) r
    have e2 : ∀ χ, DA.cinner (e χ) (gJt t) = 0 := fun χ => by
      rw [cinner_comm, hperp t χ]; simp
    simp only [e2, mul_zero, Finset.sum_const_zero, sub_zero] at e1
    have e3 := cfI t r (hκt t).ne'
    rw [e3]
    exact e1.symm
  choose c hc using hT
  have hTq : ∀ χ (v' : A → ℂ), ∑ r, (DR.prob r : ℂ) * (star (C (e χ) r) * C v' r) =
      c χ * DA.cinner (e χ) v' := by
    intro χ v'
    have h1 := s8svdaux_inner_T DR DA M (e χ) v'
    have h2 : (fun a => ∑ r, (DR.prob r : ℂ) * (M r a *
        ∑ b, (DA.prob b : ℂ) * (star (M r b) * e χ b))) = c χ • e χ := by
      funext a; rw [hc χ a]; rfl
    rw [h2, cinner_smul_left] at h1
    exact h1.symm
  have hdual : ∀ (x : ℝ) (z : ℂ), star ((x : ℂ)⁻¹ * z) = (x : ℂ)⁻¹ * star z := fun x z => by
    simp [Complex.star_def]
  -- the χ-part
  let Nχ : Λ → ℝ := fun χ => ∑ r, DR.prob r * ‖C (e χ) r‖ ^ 2
  have hN0 : ∀ χ, 0 ≤ Nχ χ := fun χ =>
    Finset.sum_nonneg fun r _ => mul_nonneg (DR.nonneg r) (sq_nonneg _)
  let κχ : Λ → ℝ := fun χ => Real.sqrt (Nχ χ)
  let gIχ : Λ → R → ℂ := fun χ r => ((κχ χ : ℝ) : ℂ)⁻¹ * C (e χ) r
  have hCzero : ∀ χ, κχ χ = 0 → ∀ r, C (e χ) r = 0 := by
    intro χ hχ r
    have hN : Nχ χ = 0 := (Real.sqrt_eq_zero (hN0 χ)).1 hχ
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ =>
      mul_nonneg (DR.nonneg r) (sq_nonneg ‖C (e χ) r‖))).1 hN r (Finset.mem_univ r)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hR r).ne'
    · simpa using h
  have hF1 : ∀ χ r, ((κχ χ : ℝ) : ℂ) * gIχ χ r = C (e χ) r := by
    intro χ r
    by_cases h0 : κχ χ = 0
    · rw [hCzero χ h0 r, h0]; simp
    · simp only [gIχ]
      rw [mul_inv_cancel_left₀ (by exact_mod_cast h0)]
  have hgIχ_zero : ∀ χ, κχ χ = 0 → gIχ χ = 0 := fun χ h0 => by
    funext r; simp only [gIχ, hCzero χ h0 r, mul_zero]; rfl
  have hsum_self : ∀ χ, ∑ r, (DR.prob r : ℂ) * (C (e χ) r * star (C (e χ) r)) =
      ((κχ χ : ℝ) : ℂ) * ((κχ χ : ℝ) : ℂ) := by
    intro χ
    show _ = ((Real.sqrt (Nχ χ) : ℝ) : ℂ) * ((Real.sqrt (Nχ χ) : ℝ) : ℂ)
    rw [sqrt_cast_mul_self _ (hN0 χ)]
    simp only [Nχ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hII : ∀ χ ψ, ∑ r, (DR.prob r : ℂ) * (C (e χ) r * star (C (e ψ) r)) =
      if χ = ψ then ((κχ χ : ℝ) : ℂ) * ((κχ χ : ℝ) : ℂ) else 0 := by
    intro χ ψ
    by_cases h : χ = ψ
    · subst h; simpa using hsum_self χ
    · simp only [h, ↓reduceIte]
      have h1 := hTq χ (e ψ)
      simp only [he, h, ↓reduceIte, mul_zero] at h1
      have h2 := congrArg star h1
      simp only [star_sum, star_mul', star_star, star_zero] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [show star (DR.prob r : ℂ) = DR.prob r by simp]
  have e2' : ∀ χ t, DA.cinner (e χ) (gJt t) = 0 := fun χ t => by
    rw [cinner_comm, hperp t χ]; simp
  have hIX : ∀ χ t, ∑ r, (DR.prob r : ℂ) * (C (e χ) r * star (gIt t r)) = 0 := by
    intro χ t
    have hg : ∀ r, gIt t r = ((κt t : ℝ) : ℂ)⁻¹ * C (gJt t) r := fun r => by
      rw [hCt t r, inv_mul_cancel_left₀ (by exact_mod_cast (hκt t).ne')]
    have h1 := hTq χ (gJt t)
    rw [e2' χ t, mul_zero] at h1
    have h2 := congrArg star h1
    simp only [star_sum, star_mul', star_star, star_zero] at h2
    have h3 : ∑ r, (DR.prob r : ℂ) * (star (C (gJt t) r) * C (e χ) r) = 0 := by
      rw [← h2]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [show star (DR.prob r : ℂ) = DR.prob r by simp]
      ring
    calc ∑ r, (DR.prob r : ℂ) * (C (e χ) r * star (gIt t r))
        = ((κt t : ℝ) : ℂ)⁻¹ * ∑ r, (DR.prob r : ℂ) * (star (C (gJt t) r) * C (e χ) r) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hg r, hdual]; ring
      _ = 0 := by rw [h3, mul_zero]
  have hcinI : ∀ χ ψ, DR.cinner (gIχ χ) (gIχ ψ) =
      ((κχ χ : ℝ) : ℂ)⁻¹ * ((κχ ψ : ℝ) : ℂ)⁻¹ *
        ∑ r, (DR.prob r : ℂ) * (C (e χ) r * star (C (e ψ) r)) := by
    intro χ ψ
    rw [cinner_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [gIχ, hdual]; ring
  have hcinX : ∀ χ t, DR.cinner (gIχ χ) (gIt t) = 0 := by
    intro χ t
    rw [cinner_def]
    have : ∀ r, (DR.prob r : ℂ) * (gIχ χ r * star (gIt t r)) =
        ((κχ χ : ℝ) : ℂ)⁻¹ * ((DR.prob r : ℂ) * (C (e χ) r * star (gIt t r))) := by
      intro r; simp only [gIχ]; ring
    rw [Finset.sum_congr rfl fun r _ => this r, ← Finset.mul_sum, hIX, mul_zero]
  refine ⟨s, Sum.elim κχ κt, Sum.elim gIχ gIt, Sum.elim e gJt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (χ | t)
    · exact Real.sqrt_nonneg _
    · exact (hκt t).le
  · intro t; exact hκt t
  · intro r a
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ χ, ((κχ χ : ℝ) : ℂ) * (gIχ χ r * e χ a) = ∑ χ, C (e χ) r * e χ a :=
      Finset.sum_congr rfl fun χ _ => by rw [← mul_assoc, hF1]
    rw [h1, ← hdec r a]
    simp [Mp]
  · intro χ; rfl
  · intro t χ; exact hperp t χ
  · rintro (χ | t) (ψ | t') h1 h2
    · simp only [Sum.elim_inl] at h1 h2
      rw [Sum.elim_inl, Sum.elim_inl, hcinI, hII]
      by_cases h : χ = ψ
      · subst h
        have : ((κχ χ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
        simp only [↓reduceIte]
        field_simp
      · simp [h]
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hcinX]; simp
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [cinner_comm, hcinX]; simp
    · simp only [Sum.elim_inr, Sum.inr.injEq]
      exact hIt t t'
  · rintro (χ | t) (ψ | t') h1 h2
    · simp only [Sum.elim_inl, Sum.inl.injEq]
      exact he χ ψ
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [e2']; simp
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hperp]; simp
    · simp only [Sum.elim_inr, Sum.inr.injEq]
      exact hJt t t'
  · rintro (χ | t) r h1
    · simp only [Sum.elim_inl] at h1 ⊢
      exact hF1 χ r
    · simp only [Sum.elim_inr] at h1 ⊢
      exact (hCt t r).symm
  · rintro (χ | t) h1
    · exact hgIχ_zero χ h1
    · exact absurd h1 (hκt t).ne'

end Engine

end TrackB
end RestrictedPolynomials
end
