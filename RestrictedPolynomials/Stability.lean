import RestrictedPolynomials.EfronStein
import RestrictedPolynomials.Statement

/-!
# From stability to low-degree weight, and the inverse theorem in every dimension

* `stability_lemma` : **Lemma 6.1**. If `Stab_{1-δ}(f - 𝔼f) > δ` for a `{0,1}`-valued `f`, then
  `W_{≤d}(f - 𝔼f) ≥ δ/2` for every integer `d ≥ δ⁻¹ log(2/δ)`.
* `inverse_theorem_all_dims` : **Proposition 6.6**. The conclusion of the inverse theorem holds
  in every dimension, by padding with dummy coordinates.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq α] in
/-- `‖f‖₂² = ∑_S ‖f^{=S}‖₂²`. -/
lemma expect_sq_eq_sum (π : FinProb α) (f : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => f x ^ 2) =
      ∑ S : Finset ι, (π.pi ι).expect (fun x => esPart π S f x ^ 2) := by
  have := expect_condExp_sq π univ f
  simp only [condExp_univ] at this
  rw [this]
  exact sum_congr (by simp) fun _ _ => rfl

/-- **Lemma 6.1.** -/
theorem stability_lemma (π : FinProb α) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (f : (ι → α) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) (d : ℕ)
    (hd : 1 / δ * Real.log (2 / δ) ≤ d)
    (hstab : δ < stab π (1 - δ) fun x => f x - (π.pi ι).expect f) :
    δ / 2 ≤ lowDegWeight π d fun x => f x - (π.pi ι).expect f := by
  set g : (ι → α) → ℝ := fun x => f x - (π.pi ι).expect f with hg
  set w : Finset ι → ℝ := fun S => (π.pi ι).expect fun x => esPart π S g x ^ 2 with hw
  have hw0 : ∀ S, 0 ≤ w S := fun S => (π.pi ι).expect_nonneg fun x => sq_nonneg _
  -- `g` has mean zero, so its degree-zero part vanishes
  have hwe : w ∅ = 0 := by
    simp only [hw, esPart_empty, hg, FinProb.expect_sub, FinProb.expect_const, sub_self]
    simp
  -- `‖g‖₂² ≤ 1`
  have hEf0 : 0 ≤ (π.pi ι).expect f :=
    (π.pi ι).expect_nonneg fun x => by rcases hf x with h | h <;> simp [h]
  have hEf1 : (π.pi ι).expect f ≤ 1 :=
    (π.pi ι).expect_le_const fun x => by rcases hf x with h | h <;> simp [h]
  have hnorm : ∑ S : Finset ι, w S ≤ 1 := by
    rw [← expect_sq_eq_sum]
    refine (π.pi ι).expect_le_const fun x => ?_
    rcases hf x with h | h <;> simp only [hg, h] <;> nlinarith
  -- `e^{-δd} ≤ δ/2`
  have hexp : (1 - δ) ^ d ≤ δ / 2 := by
    have h1 : (1 - δ) ^ d ≤ Real.exp (-δ * d) := by
      calc (1 - δ) ^ d ≤ Real.exp (-δ) ^ d :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ)]) d
        _ = Real.exp (-δ * d) := by rw [← Real.exp_nat_mul]; ring_nf
    have h2 : Real.log (2 / δ) ≤ δ * d := by
      have := mul_le_mul_of_nonneg_left hd hδ0.le
      rwa [← mul_assoc, mul_one_div_cancel hδ0.ne', one_mul] at this
    have h3 : Real.exp (-δ * d) ≤ δ / 2 := by
      have : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      rw [← this, Real.exp_le_exp]
      linarith
    linarith
  -- split the stability into low and high degrees
  by_contra! hlow
  rw [stab_eq] at hstab
  have hsplit := sum_filter_add_sum_filter_not univ (fun S : Finset ι => S.card ≤ d)
    fun S => (1 - δ) ^ S.card * w S
  have hlowpart : ∑ S with S.card ≤ d, (1 - δ) ^ S.card * w S ≤ lowDegWeight π d g :=
    sum_le_sum fun S _ => mul_le_of_le_one_left (hw0 S)
      (pow_le_one₀ (by linarith) (by linarith))
  have hhighpart : ∑ S with ¬ S.card ≤ d, (1 - δ) ^ S.card * w S ≤ (1 - δ) ^ d := by
    calc ∑ S with ¬ S.card ≤ d, (1 - δ) ^ S.card * w S
        ≤ ∑ S with ¬ S.card ≤ d, (1 - δ) ^ d * w S := by
          refine sum_le_sum fun S hS => mul_le_mul_of_nonneg_right ?_ (hw0 S)
          simp only [mem_filter] at hS
          exact pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
      _ ≤ (1 - δ) ^ d * ∑ S : Finset ι, w S := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun S _ _ => hw0 S) (pow_nonneg (by linarith) _)
      _ ≤ (1 - δ) ^ d := mul_le_of_le_one_right (pow_nonneg (by linarith) _) hnorm
  have : stab π (1 - δ) g ≤ lowDegWeight π d g + (1 - δ) ^ d := by
    rw [stab_eq, ← hsplit]
    exact add_le_add hlowpart hhighpart
  rw [← stab_eq] at hstab
  linarith

/-! ### Padding -/

/-- Each row of the noise kernel is a probability distribution. -/
lemma sum_noiseKernel (π : FinProb α) (ρ : ℝ) (a : α) : ∑ b, noiseKernel π ρ a b = 1 := by
  simp [noiseKernel, sum_add_distrib, ← mul_sum, π.sum_eq_one]

omit [DecidableEq ι] in
/-- Padding does not change the noise operator. -/
lemma noiseOp_sumInl {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ] (π : FinProb α)
    (ρ : ℝ) (g : (ι → α) → ℝ) (x : ι ⊕ κ → α) :
    noiseOp π ρ (fun y => g (y ∘ Sum.inl)) x = noiseOp π ρ g (x ∘ Sum.inl) := by
  unfold noiseOp
  rw [← (Equiv.sumArrowEquivProdArrow ι κ α).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  have hcomp : ∀ (v : ι → α) (w : κ → α),
      (Equiv.sumArrowEquivProdArrow ι κ α).symm (v, w) ∘ Sum.inl = v := by
    intro v w; ext i; simp
  simp only [hcomp]
  refine sum_congr rfl fun v _ => ?_
  have hsum : ∑ w : κ → α, ∏ j, noiseKernel π ρ (x (Sum.inr j)) (w j) = 1 := by
    rw [← Fintype.prod_sum fun j b => noiseKernel π ρ (x (Sum.inr j)) b]
    simp [sum_noiseKernel]
  calc ∑ w : κ → α, (∏ i, noiseKernel π ρ (x (Sum.inl i)) (v i)) *
        (∏ j, noiseKernel π ρ (x (Sum.inr j)) (w j)) * g v
      = (∏ i, noiseKernel π ρ (x (Sum.inl i)) (v i)) * g v *
          ∑ w : κ → α, ∏ j, noiseKernel π ρ (x (Sum.inr j)) (w j) := by
        rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
    _ = _ := by rw [hsum, mul_one]; rfl

omit [DecidableEq ι] in
/-- Padding does not change the stability. -/
lemma stab_sumInl {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ] (π : FinProb α)
    (ρ : ℝ) (g : (ι → α) → ℝ) :
    stab π ρ (fun y : ι ⊕ κ → α => g (y ∘ Sum.inl)) = stab π ρ g := by
  unfold stab
  simp only [noiseOp_sumInl]
  exact π.expect_sumInl (κ := κ) fun y => g y * noiseOp π ρ g y

/-- **Proposition 6.6.** The conclusion of the inverse theorem holds in every dimension, with the
same parameter `δ`. -/
theorem inverse_theorem_all_dims :
    ∃ C₀ : ℕ, ∀ (k : ℕ) (α : Type) [Fintype α] [DecidableEq α] (μ : FinProb (Fin k → α)),
      NoNontrivialAbelianEmbedding μ.support →
      ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
        ∀ f : Fin k → (ι → α) → ℝ, (∀ i x, |f i x| ≤ 1) →
          ε ≤ |(μ.pi ι).expect fun X => ∏ i, f i fun t => X t i| →
          ∀ i, inverseDelta C₀ k b ε <
            stab (μ.marginal i) (1 - inverseDelta C₀ k b ε) (f i) := by
  obtain ⟨C₀, hC₀⟩ := inverse_theorem
  refine ⟨C₀, fun k α _ _ μ hμ => ?_⟩
  obtain ⟨b, hb, hε⟩ := hC₀ k α μ hμ
  refine ⟨b, hb, fun ε hεpos ι _ _ f hf hcorr i => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hε ε hεpos
  -- pad with `n₀` dummy coordinates
  let F : Fin k → (ι ⊕ Fin n₀ → α) → ℝ := fun j y => f j (y ∘ Sum.inl)
  have hF : ∀ j y, |F j y| ≤ 1 := fun j y => hf j _
  have hcard : n₀ ≤ Fintype.card (ι ⊕ Fin n₀) := by simp
  have hcorrF : ε ≤ |(μ.pi (ι ⊕ Fin n₀)).expect fun X => ∏ j, F j fun t => X t j| := by
    have := μ.expect_sumInl (ι := ι) (κ := Fin n₀) fun Y => ∏ j, f j fun t => Y t j
    refine hcorr.trans (le_of_eq ?_)
    rw [← this]
    rfl
  have := hn₀ (ι ⊕ Fin n₀) hcard F hF hcorrF i
  simpa [F, stab_sumInl] using this

end RestrictedPolynomials

end
