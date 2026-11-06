module

public import RestrictedPolynomials.EfronStein
public import RestrictedPolynomials.ExpIterate
public import RestrictedPolynomials.Frozen.InverseTheoremBKLM
public import Mathlib.Tactic.IntervalCases

/-!
# The inverse theorem in the form used by the proof of Theorem 1.1

`inverse_theorem` is the special case of the frozen statement `inverse_theorem_bklm`
([CSP_7, Theorem 1]) used downstream: one alphabet `α`, real-valued functions, `b` and `n₀`
allowed to depend on `μ`, and the strict inequality `δ < Stab_{1-δ}(f_i)`. It is proved here
from `inverse_theorem_bklm`.

* For `k ≥ 2` the number of iterated exponentials is raised from `k^{C₀ k}` to `k^{(C₀+1) k}`,
  which makes `δ` strictly smaller; `Stab_ρ` is nondecreasing in `ρ` (`stab_mono`).
* For `k = 1` the number of iterates does not depend on `C₀`, so the bound comes directly from
  `Stab_ρ(f) ≥ (𝔼 f)² ≥ ε² > δ`; for `k = 0` the conclusion is vacuous.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials

section Bridge

variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma cexpect_ofReal {β : Type} [Fintype β] (π : FinProb β) (g : β → ℝ) :
    π.cexpect (fun a => (g a : ℂ)) = ((π.expect g : ℝ) : ℂ) := by
  simp [FinProb.cexpect, FinProb.expect]

lemma cnoiseOp_ofReal (π : FinProb α) (ρ : ℝ) (g : (ι → α) → ℝ) (x : ι → α) :
    cnoiseOp π ρ (fun y => (g y : ℂ)) x = ((noiseOp π ρ g x : ℝ) : ℂ) := by
  simp [cnoiseOp, noiseOp]

/-- For real-valued functions the complex stability is the real one. -/
lemma cstab_ofReal (π : FinProb α) (ρ : ℝ) (g : (ι → α) → ℝ) :
    cstab π ρ (fun y => (g y : ℂ)) = ((stab π ρ g : ℝ) : ℂ) := by
  unfold cstab stab
  simp only [cnoiseOp_ofReal, Complex.star_def, Complex.conj_ofReal]
  rw [← cexpect_ofReal]
  simp

/-- The push-forward of `μ^{⊗ι}` under the `j`-th coordinate is `(μ_j)^{⊗ι}`. -/
lemma expect_pi_marginal {k : ℕ} (μ : FinProb (Fin k → α)) (j : Fin k) (g : (ι → α) → ℝ) :
    (μ.pi ι).expect (fun X => g (fun t => X t j)) = ((μ.marginal j).pi ι).expect g := by
  simp only [FinProb.expect, FinProb.pi, FinProb.marginal]
  rw [← Finset.sum_fiberwise Finset.univ (fun X : ι → Fin k → α => fun t => X t j)]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Finset.prod_univ_sum, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun X hX => ?_
  · ext X
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter, funext_iff]
  · rw [Fintype.mem_piFinset] at hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    have hXY : (fun t => X t j) = Y := funext hX
    rw [hXY]

/-- `Stab_ρ(f) ≥ (𝔼 f)²` for `ρ ≥ 0`: the degree-zero term of `stab_eq`. -/
lemma sq_expect_le_stab (π : FinProb α) {ρ : ℝ} (hρ : 0 ≤ ρ) (g : (ι → α) → ℝ) :
    ((π.pi ι).expect g) ^ 2 ≤ stab π ρ g := by
  rw [stab_eq]
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun S : Finset ι => ρ ^ S.card * (π.pi ι).expect (fun x => esPart π S g x ^ 2))
    (fun S _ => mul_nonneg (pow_nonneg hρ _) ((π.pi ι).expect_nonneg fun x => sq_nonneg _))
    (Finset.mem_univ ∅)
  simp only [Finset.card_empty, pow_zero, one_mul, esPart_empty, FinProb.expect_const] at h
  exact h

end Bridge

lemma inverseDelta_lt_one {C₀ k : ℕ} (hk : 1 ≤ k) (b ε : ℝ) : inverseDelta C₀ k b ε < 1 := by
  unfold inverseDelta
  rw [← Real.exp_zero, Real.exp_lt_exp, neg_lt_zero]
  obtain ⟨m, hm⟩ : ∃ m, k ^ (C₀ * k) = m + 1 :=
    ⟨k ^ (C₀ * k) - 1, by have := Nat.one_le_pow (C₀ * k) k hk; omega⟩
  rw [hm, Function.iterate_succ_apply']
  exact Real.exp_pos _

open scoped ComplexOrder in
/-- **Theorem 1.4** in the form used downstream ([CSP_7, Theorem 1], specialised). Let `μ` be a
distribution on `α^k` admitting no nontrivial abelian embedding. For every `ε > 0` there is `n₀`
such that for `n ≥ n₀`, if `1`-bounded `f₁, …, f_k : α^n → ℝ` satisfy
`|𝔼_{μ^{⊗n}} ∏ᵢ fᵢ(xᵢ)| ≥ ε`, then `Stab_{1-δ}(fᵢ) > δ` for every `i`, stability being taken with
respect to the marginal `μᵢ`, where `δ = exp(-exp^{(k^{O(k)})}(ε^{-O_μ(1)}))`. Proved from the
frozen statement `inverse_theorem_bklm`. -/
theorem inverse_theorem :
    ∃ C₀ : ℕ, ∀ (k : ℕ) (α : Type) [Fintype α] [DecidableEq α] (μ : FinProb (Fin k → α)),
      NoNontrivialAbelianEmbedding μ.support →
      ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], n₀ ≤ Fintype.card ι →
        ∀ f : Fin k → (ι → α) → ℝ, (∀ i x, |f i x| ≤ 1) →
          ε ≤ |(μ.pi ι).expect fun X => ∏ i, f i fun t => X t i| →
          ∀ i, inverseDelta C₀ k b ε <
            stab (μ.marginal i) (1 - inverseDelta C₀ k b ε) (f i) := by
  obtain ⟨C₀, hC₀⟩ := inverse_theorem_bklm
  refine ⟨C₀ + 1, fun k α _ _ μ hμ => ?_⟩
  -- a lower bound `γ > 0` for the atoms of `μ`
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ℝ, 0 < γ ∧ ∀ a ∈ μ.support, γ ≤ μ.prob a := by
    have hne : (Finset.univ.filter fun a => μ.prob a ≠ 0).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      have : ∑ a, μ.prob a = 0 :=
        Finset.sum_eq_zero fun a _ => by simpa using h (Finset.mem_univ a)
      linarith [μ.sum_eq_one]
    obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image _ μ.prob hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha₀
    refine ⟨μ.prob a₀, lt_of_le_of_ne (μ.nonneg a₀) (Ne.symm ha₀), fun a ha => hmin a ?_⟩
    simpa [FinProb.support] using ha
  obtain ⟨b', hb', hb'ε⟩ := hC₀ k γ hγ0
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · -- `k = 0`: vacuous
      exact ⟨1, one_pos, fun ε _ => ⟨0, fun ι _ _ _ f _ _ i => i.elim0⟩⟩
    · -- `k = 1`: `Stab ≥ (𝔼 f)² ≥ ε² > δ`, directly
      refine ⟨1, one_pos, fun ε hε => ⟨0, fun ι _ _ _ f hf hcorr i => ?_⟩⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      set δ := inverseDelta (C₀ + 1) 1 1 ε with hδ
      have hδ1 : δ < 1 := inverseDelta_lt_one le_rfl _ _
      have hcorr' : ε ≤ |((μ.marginal 0).pi ι).expect (f 0)| := by
        rw [← expect_pi_marginal]; simpa using hcorr
      have hsq : ε ^ 2 ≤ stab (μ.marginal 0) (1 - δ) (f 0) := by
        refine le_trans ?_ (sq_expect_le_stab _ (by linarith) _)
        rw [← sq_abs (FinProb.expect _ _)]
        exact pow_le_pow_left₀ hε.le hcorr' 2
      have hδε : δ < ε ^ 2 := by
        rcases le_or_gt 1 ε with h1 | h1
        · nlinarith
        · -- `t = 1/ε > 1` and `δ = exp(-exp t) < 1/t² = ε²`
          have hδ' : δ = Real.exp (-Real.exp (ε ^ (-(1 : ℝ)))) := by
            simp [hδ, inverseDelta]
          set t := ε ^ (-(1 : ℝ)) with ht
          have ht' : t = 1 / ε := by rw [ht, Real.rpow_neg_one, one_div]
          have htpos : 0 < t := by rw [ht']; positivity
          have hq : 1 + t + t ^ 2 / 2 ≤ Real.exp t := Real.quadratic_le_exp_of_nonneg htpos.le
          have he1 : (2 : ℝ) < Real.exp 1 := by
            have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero; linarith
          have hee : Real.exp (t + 1) ≤ Real.exp (Real.exp t) :=
            Real.exp_le_exp.2 (by linarith [Real.add_one_le_exp t])
          have hbig : t ^ 2 < Real.exp (Real.exp t) := by
            rw [Real.exp_add] at hee
            have : t ^ 2 < Real.exp t * Real.exp 1 := by nlinarith
            linarith
          have : δ * t ^ 2 < 1 := by
            rw [hδ', Real.exp_neg]
            rw [inv_mul_lt_iff₀ (Real.exp_pos _)]; linarith
          rw [ht'] at this
          have hε2 : 0 < ε ^ 2 := by positivity
          rw [div_pow, one_pow, mul_one_div, div_lt_one hε2] at this
          exact this
      linarith
  · -- `k ≥ 2`: `k^{C₀ k} < k^{(C₀+1) k}`, so the new `δ` is strictly smaller than target 3's
    refine ⟨b', hb', fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := hb'ε ε hε
    refine ⟨n₀, fun ι _ _ hι f hf hcorr i => ?_⟩
    have h := hn₀ (fun _ => α) μ hμ hγ ι hι (fun i x => (f i x : ℂ))
      (fun i x => by simpa [Complex.norm_real] using hf i x) ?_ i
    · rw [show cstab (μ.marginalPi (A := fun _ => α) i) (1 - inverseDelta C₀ k b' ε)
            (fun x => (f i x : ℂ)) = cstab (μ.marginal i) (1 - inverseDelta C₀ k b' ε)
            (fun x => (f i x : ℂ)) from rfl, cstab_ofReal, Complex.real_le_real] at h
      set δ' := inverseDelta C₀ k b' ε
      set δ := inverseDelta (C₀ + 1) k b' ε
      have hlt : δ < δ' := by
        simp only [δ, δ', inverseDelta]
        rw [Real.exp_lt_exp, neg_lt_neg_iff]
        refine exp_iterate_lt_of_lt (Nat.pow_lt_pow_right (by omega) ?_) _
        nlinarith
      have hδ'1 : δ' < 1 := inverseDelta_lt_one (by omega) _ _
      calc δ < δ' := hlt
        _ ≤ _ := h
        _ ≤ _ := stab_mono _ (by linarith) (by linarith) _
    · have : (μ.pi ι).cexpect (fun X => ∏ i, ((fun i x => (f i x : ℂ)) i fun t => X t i))
          = (((μ.pi ι).expect fun X => ∏ i, f i fun t => X t i : ℝ) : ℂ) := by
        rw [← cexpect_ofReal]; simp
      rw [this, Complex.norm_real, Real.norm_eq_abs]
      exact hcorr

end RestrictedPolynomials

end
