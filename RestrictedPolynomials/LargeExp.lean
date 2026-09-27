import RestrictedPolynomials.Counting
import Mathlib.Data.Fintype.Powerset

/-!
# Lemma 6.3 (a large correlation) and Lemma 6.4 (fibers)

* `NoProgression p M k A` : `A` contains no nontrivial restricted progression
  `x, x + P_1(y), …, x + P_{k-1}(y)` with `y ∈ Y^n \ {0}`.
* `expect_prod_indicator` : if `A` has no such progression, `𝔼_{μ^{⊗n}} ∏ⱼ 1_A(xⱼ) = α / 2^n`.
* `large_exp` : **Lemma 6.3**.
* `fiber_noProgression` : **Lemma 6.4**.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- `A` contains no nontrivial restricted `k`-term progression with step in `Y^n \ {0}`. -/
def NoProgression {ι : Type*} (p M k : ℕ) (A : Set (ι → ZMod p)) : Prop :=
  ∀ x y : ι → ZMod p, (∀ i, ∃ t ∈ stepSet M, y i = t) → y ≠ 0 → ∃ j : Fin k, x + polyTerm j y ∉ A

/-- The density `|A| / p^n`. -/
def density {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (A : Finset (ι → ZMod p)) : ℝ :=
  A.card / (p : ℝ) ^ Fintype.card ι

variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma density_nonneg (A : Finset (ι → ZMod p)) : 0 ≤ density A := by
  unfold density; positivity

lemma density_le_one [NeZero p] (A : Finset (ι → ZMod p)) : density A ≤ 1 := by
  unfold density
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [div_le_one (by positivity)]
  have : A.card ≤ Fintype.card (ι → ZMod p) := card_le_univ A
  rw [Fintype.card_fun, ZMod.card] at this
  exact_mod_cast this

/-- The density is the expectation of the indicator under the uniform measure. -/
lemma expect_uniform_indicator [NeZero p] (A : Finset (ι → ZMod p)) :
    ((FinProb.uniform : FinProb (ZMod p)).pi ι).expect (fun x => if x ∈ A then 1 else 0) =
      density A := by
  unfold FinProb.expect density
  simp only [FinProb.pi_prob, FinProb.uniform, ZMod.card, prod_const, card_univ, mul_ite,
    mul_one, mul_zero]
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, one_div, inv_pow, div_eq_mul_inv]

/-- A nonzero step in `Y` is nonzero in `𝔽_p` when `M < p`. -/
lemma cast_ne_zero_of_mem_stepSet {M : ℕ} (hMp : M < p) {t : ℕ} (ht : t ∈ stepSet M)
    (h0 : t ≠ 0) : (t : ZMod p) ≠ 0 := by
  have ht' : t ≤ M := by simp [stepSet] at ht; omega
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h0) (by omega)

/-! ### The counting identity -/

section Counting

variable [NeZero p] {k M : ℕ} (hM : 2 ≤ M)

lemma prod_indicator_eq_zero {A : Finset (ι → ZMod p)} (hA : NoProgression p M k (A : Set (ι → ZMod p)))
    (hMp : M < p) {Z : ι → ZMod p × ℕ} (hZ : Z ∈ Fintype.piFinset fun _ : ι => stepPairs p M)
    (hZ0 : ¬ ∀ i, (Z i).2 = 0) :
    (∏ j : Fin k, if (fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p) j) ∈ A then (1 : ℝ)
      else 0) = 0 := by
  rw [Fintype.mem_piFinset] at hZ
  have hstep : ∀ i, (Z i).2 ∈ stepSet M := fun i => by
    have := hZ i; simp only [stepPairs, mem_product, mem_univ, true_and] at this; exact this
  obtain ⟨i₀, hi₀⟩ := not_forall.1 hZ0
  obtain ⟨j, hj⟩ := hA (fun i => (Z i).1) (fun i => ((Z i).2 : ZMod p))
    (fun i => ⟨(Z i).2, hstep i, rfl⟩)
    (fun h => cast_ne_zero_of_mem_stepSet hMp (hstep i₀) hi₀ (congrFun h i₀))
  refine prod_eq_zero (mem_univ j) (ite_eq_right ?_)
  exact fun h => hj h

/-- If `A` has no nontrivial progression, then `𝔼_{μ^{⊗n}} ∏ⱼ 1_A(xⱼ) = |A| / (2p)^n`. -/
lemma expect_prod_indicator (hk : 1 ≤ k) (hMp : M < p) (A : Finset (ι → ZMod p))
    (hA : NoProgression p M k (A : Set (ι → ZMod p))) :
    ((countingDist p k M hM).pi ι).expect
        (fun X => ∏ j : Fin k, if (fun i => X i j) ∈ A then (1 : ℝ) else 0) =
      density A / 2 ^ Fintype.card ι := by
  rw [expect_pi_countingDist]
  -- only the steps that vanish in every coordinate contribute
  have hsplit : ∀ Z ∈ Fintype.piFinset fun _ : ι => stepPairs p M,
      (∏ i, wt p M (Z i).2) * (∏ j : Fin k,
        if (fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p) j) ∈ A then (1 : ℝ) else 0) =
      if ∀ i, (Z i).2 = 0 then (1 / (2 * (p : ℝ))) ^ Fintype.card ι *
        (if (fun i => (Z i).1) ∈ A then (1 : ℝ) else 0) else (0 : ℝ) := by
    intro Z hZ
    split_ifs with h0 hA'
    · have hfun : ∀ j : Fin k, (fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p) j) =
          fun i => (Z i).1 := fun j => by ext i; simp [progTuple, h0 i]
      rw [prod_congr rfl fun i _ => (show wt p M (Z i).2 = 1 / (2 * p) by simp [wt, h0 i]),
        prod_const, card_univ]
      congr 1
      rw [prod_eq_one]
      intro j _
      rw [hfun, ite_eq_left hA']
    · have hfun : ∀ j : Fin k, (fun i => progTuple k (Z i).1 ((Z i).2 : ZMod p) j) =
          fun i => (Z i).1 := fun j => by ext i; simp [progTuple, h0 i]
      rw [prod_congr rfl fun i _ => (show wt p M (Z i).2 = 1 / (2 * p) by simp [wt, h0 i]),
        prod_const, card_univ, mul_zero]
      obtain ⟨j⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_univ j) ?_)
      rw [hfun, ite_eq_right hA']
    · rw [prod_indicator_eq_zero hA hMp hZ h0, mul_zero]
  rw [sum_congr rfl hsplit, ← sum_filter]
  -- the contributing configurations are the points `x ∈ 𝔽_p^n`
  have hbij : ∑ Z ∈ (Fintype.piFinset fun _ : ι => stepPairs p M).filter (fun Z => ∀ i, (Z i).2 = 0),
      (1 / (2 * (p : ℝ))) ^ Fintype.card ι * (if (fun i => (Z i).1) ∈ A then 1 else 0) =
      ∑ x : ι → ZMod p, (1 / (2 * (p : ℝ))) ^ Fintype.card ι * (if x ∈ A then 1 else 0) := by
    refine sum_nbij' (fun Z i => (Z i).1) (fun x i => (x i, 0)) ?_ ?_ ?_ ?_ ?_
    · intro Z _; exact mem_univ _
    · intro x _
      simp [Fintype.mem_piFinset, stepPairs, stepSet]
    · intro Z hZ
      simp only [mem_filter] at hZ
      ext i
      · rfl
      · exact (hZ.2 i).symm
    · intro x _; rfl
    · intro Z _; rfl
  rw [hbij, ← mul_sum, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one]
  unfold density
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [div_pow, mul_pow, one_pow]
  field_simp

end Counting

/-! ### Lemma 6.3 -/

section LargeExp

variable [NeZero p] {k M : ℕ} (hM : 2 ≤ M)

/-- The product `∏ⱼ (α + f(xⱼ))` expanded over the subsets `T` where `f` is chosen. -/
lemma prod_add_const_expand {β : Type*} (x : Fin k → β) (f : β → ℝ) (c : ℝ) :
    ∏ j, (c + f (x j)) =
      ∑ T : Finset (Fin k), ∏ j, (if j ∈ T then f (x j) else c) := by
  simp_rw [add_comm c]
  rw [prod_add]
  refine sum_congr (by simp) fun T _ => ?_
  rw [prod_ite, ← compl_eq_univ_sdiff]
  congr 1
  · exact prod_congr (ext fun j => by simp) fun _ _ => rfl
  · rw [prod_const, prod_const]
    congr 2
    ext j; simp

/-- **Lemma 6.3.** If `A` contains no nontrivial restricted progression, then some correlation
`𝔼_{μ^{⊗n}}[f_A(x_j) ∏_{i ≠ j} f_i(x_i)]`, with the balanced function `f_A = 1_A - α` in
position `j` and `1`-bounded functions elsewhere, is at least
`α^k / (2^k - 1) - α / (2^n (2^k - 1))` in absolute value. -/
theorem large_exp (hk : 1 ≤ k) (hMp : M < p) (A : Finset (ι → ZMod p))
    (hA : NoProgression p M k (A : Set (ι → ZMod p))) :
    ∃ j : Fin k, ∃ f : Fin k → (ι → ZMod p) → ℝ, (∀ i x, |f i x| ≤ 1) ∧
      (∀ x, f j x = (if x ∈ A then 1 else 0) - density A) ∧
      density A ^ k / (2 ^ k - 1) - density A / (2 ^ Fintype.card ι * (2 ^ k - 1)) ≤
        |((countingDist p k M hM).pi ι).expect fun X => ∏ i, f i fun t => X t i| := by
  set α := density A with hα
  have hα0 : 0 ≤ α := density_nonneg A
  have hα1 : α ≤ 1 := density_le_one A
  set fA : (ι → ZMod p) → ℝ := fun x => (if x ∈ A then 1 else 0) - α with hfA
  have hfA1 : ∀ x, |fA x| ≤ 1 := fun x => by
    simp only [hfA]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  set F : Finset (Fin k) → Fin k → (ι → ZMod p) → ℝ :=
    fun T i => if i ∈ T then fA else fun _ => α with hF
  set Θ : Finset (Fin k) → ℝ := fun T =>
    ((countingDist p k M hM).pi ι).expect fun X => ∏ i, F T i fun t => X t i with hΘ
  -- `𝔼 ∏ 1_A = ∑_T Θ_T`
  have hsum : ((countingDist p k M hM).pi ι).expect
      (fun X => ∏ j : Fin k, if (fun i => X i j) ∈ A then (1 : ℝ) else 0) = ∑ T, Θ T := by
    rw [← FinProb.expect_sum]
    refine FinProb.expect_congr _ fun X => ?_
    have := prod_add_const_expand (fun j => fun i => X i j) fA α
    simp only [hfA, add_sub_cancel] at this
    rw [this]
    refine sum_congr rfl fun T _ => prod_congr rfl fun j _ => ?_
    simp only [hF]
    by_cases hj : j ∈ T <;> simp [hj, hfA]
  have hΘ0 : Θ ∅ = α ^ k := by
    simp [hΘ, hF]
  rw [expect_prod_indicator hM hk hMp A hA, ← add_sum_erase _ _ (mem_univ ∅), hΘ0] at hsum
  -- pigeonhole over the `2^k - 1` nonempty sets `T`
  set c := α ^ k / (2 ^ k - 1) - α / (2 ^ Fintype.card ι * (2 ^ k - 1)) with hc
  have hcard : ((univ.erase (∅ : Finset (Fin k))).card : ℝ) = 2 ^ k - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin]
    push_cast [Nat.one_le_two_pow]
    ring
  have hk2 : (1 : ℝ) ≤ 2 ^ k - 1 := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    linarith
  obtain ⟨T, hT, hTc⟩ : ∃ T ∈ univ.erase (∅ : Finset (Fin k)), c ≤ |Θ T| := by
    by_contra! hall
    have hne : (univ.erase (∅ : Finset (Fin k))).Nonempty :=
      ⟨univ, mem_erase.2 ⟨fun h => by have := congrArg card h; simp at this; omega,
        mem_univ _⟩⟩
    have hlt : ∑ T ∈ univ.erase ∅, |Θ T| < ∑ T ∈ univ.erase (∅ : Finset (Fin k)), c :=
      sum_lt_sum_of_nonempty hne hall
    rw [sum_const, nsmul_eq_mul, hcard] at hlt
    have habs : -(∑ T ∈ univ.erase ∅, Θ T) ≤ ∑ T ∈ univ.erase ∅, |Θ T| := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun T _ => neg_le_abs _
    have : (2 ^ k - 1) * c = α ^ k - α / 2 ^ Fintype.card ι := by
      rw [hc]; field_simp
    linarith
  obtain ⟨j, hj⟩ := nonempty_of_ne_empty (ne_of_mem_erase hT)
  refine ⟨j, F T, fun i x => ?_, fun x => ?_, hTc⟩
  · simp only [hF]
    split_ifs
    · exact hfA1 x
    · rw [abs_of_nonneg hα0]; exact hα1
  · simp [hF, hj, hfA]

end LargeExp

/-! ### Lemma 6.4 -/

section Fiber

variable [NeZero p]

/-- The fiber `A_{Sᶜ → u} = {v ∈ 𝔽_p^S : (v, u_{Sᶜ}) ∈ A}`. -/
def fiber (A : Finset (ι → ZMod p)) (S : Finset ι) (u : ι → ZMod p) : Finset (S → ZMod p) :=
  univ.filter fun v => FinProb.extend S v u ∈ A

/-- **Lemma 6.4.** A fiber of a set with no nontrivial restricted progression has none. -/
theorem fiber_noProgression {M k : ℕ} {A : Finset (ι → ZMod p)}
    (hA : NoProgression p M k (A : Set (ι → ZMod p))) (S : Finset ι) (u : ι → ZMod p) :
    NoProgression p M k (fiber A S u : Set (S → ZMod p)) := by
  intro x y hy hy0
  obtain ⟨j, hj⟩ := hA (FinProb.extend S x u) (FinProb.extend S y 0) (fun i => by
      unfold FinProb.extend
      split_ifs with hi
      · exact hy ⟨i, hi⟩
      · exact ⟨0, by simp [stepSet], by simp⟩)
    (fun h => hy0 (funext fun s => by
      have := congrFun h s.1
      simpa [FinProb.extend, s.2] using this))
  refine ⟨j, fun hmem => hj ?_⟩
  simp only [fiber, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hmem
  rw [Finset.mem_coe]
  convert hmem using 2
  ext i
  simp only [Pi.add_apply, FinProb.extend, polyTerm]
  split_ifs with hi h0 <;> simp_all [zero_pow]

/-- The density of a fiber is the conditional average of the indicator. -/
lemma density_fiber (A : Finset (ι → ZMod p)) (S : Finset ι) (u : ι → ZMod p) :
    ((FinProb.uniform : FinProb (ZMod p)).pi S).expect
        (fun v => if FinProb.extend S v u ∈ A then 1 else 0) = density (fiber A S u) := by
  rw [← expect_uniform_indicator]
  refine FinProb.expect_congr _ fun v => ?_
  simp [fiber]

end Fiber

/-! ### The points of a progression are distinct -/

omit [Fintype ι] [DecidableEq ι] in
/-- If `p > M^{k-1}` and `y ∈ Y^n \ {0}`, the points `x + P_j(y)`, `0 ≤ j < k`, are pairwise
distinct. -/
theorem progression_injective {M k : ℕ} (hMp : M ^ (k - 1) < p) (x y : ι → ZMod p)
    (hy : ∀ i, ∃ t ∈ stepSet M, y i = t) (hy0 : y ≠ 0) :
    Function.Injective fun j : Fin k => x + polyTerm j y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
  obtain ⟨t, ht, hti⟩ := hy i
  have ht0 : t ≠ 0 := by rintro rfl; simp [hti] at hi
  have ht2 : 2 ≤ t ∧ t ≤ M := by simp [stepSet] at ht; omega
  intro j₁ j₂ h
  have h' := congrFun h i
  simp only [Pi.add_apply, add_right_inj, polyTerm, hti] at h'
  -- the naturals `pw' j t` are distinct and smaller than `p`
  let v : ℕ → ℕ := fun j => if j = 0 then 0 else t ^ j
  have hv : ∀ j : Fin k, v j < p := by
    intro j
    simp only [v]
    split_ifs
    · exact lt_of_le_of_lt (Nat.zero_le _) (lt_of_le_of_lt (Nat.zero_le _) hMp)
    · calc t ^ (j : ℕ) ≤ M ^ (j : ℕ) := Nat.pow_le_pow_left ht2.2 _
        _ ≤ M ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ < p := hMp
  have hcast : ∀ j : Fin k, ((v j : ℕ) : ZMod p) =
      if (j : ℕ) = 0 then 0 else (t : ZMod p) ^ (j : ℕ) := by
    intro j; simp only [v]; split_ifs <;> simp
  have h2 : ((v j₁ : ℕ) : ZMod p) = ((v j₂ : ℕ) : ZMod p) := by
    rw [hcast, hcast]; exact h'
  have heq : v j₁ = v j₂ := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2
    rwa [Nat.mod_eq_of_lt (hv j₁), Nat.mod_eq_of_lt (hv j₂)] at this
  have hinj : ∀ a b : ℕ, v a = v b → a = b := by
    intro a b hab
    simp only [v] at hab
    split_ifs at hab with ha hb hb
    · omega
    · exact absurd hab.symm (pow_ne_zero _ (by omega))
    · exact absurd hab (pow_ne_zero _ (by omega))
    · exact Nat.pow_right_injective (by omega) hab
  exact Fin.ext (hinj _ _ heq)

end RestrictedPolynomials

end
