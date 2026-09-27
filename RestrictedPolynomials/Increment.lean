import RestrictedPolynomials.Restriction
import RestrictedPolynomials.LargeExp

/-!
# The density increment (Lemma 6.7) and its iteration

The parameters `δ₀`, `d`, `N` enter only through the inequalities they satisfy, which are
listed as hypotheses; their values are fixed in `Main.lean`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {p k M : ℕ} [NeZero p] (hM : 2 ≤ M)

/-- The conclusion of the inverse theorem for the counting distribution, with parameters
`ε₀` and `δ₀`, in every dimension. -/
def InverseHolds (p k M : ℕ) [NeZero p] (hM : 2 ≤ M) (ε₀ δ₀ : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Fin k → (ι → ZMod p) → ℝ),
    (∀ i x, |f i x| ≤ 1) →
    ε₀ ≤ |((countingDist p k M hM).pi ι).expect fun X => ∏ i, f i fun t => X t i| →
    ∀ i, δ₀ < stab ((countingDist p k M hM).marginal i) (1 - δ₀) (f i)

omit [NeZero p] in
lemma exp_le_of_log_le {n d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ)
    (h : 2 * d ^ 2 * Real.log (32 / δ) ≤ n) : 16 * Real.exp (-n / (2 * d ^ 2)) ≤ δ / 2 := by
  have h1 : Real.log (32 / δ) ≤ n / (2 * d ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h2 : Real.exp (-n / (2 * d ^ 2)) ≤ δ / 32 := by
    have : Real.exp (-Real.log (32 / δ)) = δ / 32 := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [← this, Real.exp_le_exp, neg_div]
    linarith
  linarith

/-- **Lemma 6.7** (density increment). -/
theorem density_increment (hk : 1 ≤ k) (hMp : M < p) {δ₀ ε₀ α₀ : ℝ} {d N : ℕ}
    (hinv : InverseHolds p k M hM ε₀ δ₀) (hδ0 : 0 < δ₀) (hδ1 : δ₀ < 1 / 2) (hd2 : 2 ≤ d)
    (hd : 1 / δ₀ * Real.log (2 / δ₀) ≤ d) (hα₀ : 0 < α₀)
    (hε₀ : ε₀ ≤ α₀ ^ k / (2 * (2 ^ k - 1)))
    (hN1 : 2 * (d : ℝ) ^ 2 * Real.log (32 / δ₀) ≤ N) (hN2 : 2 * (1 / α₀) ^ (k - 1) ≤ 2 ^ N)
    (ι : Type) [Fintype ι] [DecidableEq ι] (hn : N ≤ Fintype.card ι)
    (A : Finset (ι → ZMod p)) (hA : NoProgression p M k (A : Set (ι → ZMod p)))
    (hαA : α₀ ≤ density A) :
    ∃ S : Finset ι, ∃ u : ι → ZMod p, (Fintype.card ι : ℝ) / (2 * d) ≤ S.card ∧
      density A + δ₀ / 32 ≤ density (fiber A S u) := by
  set α := density A with hα
  set n := Fintype.card ι with hn_def
  have hα0 : 0 < α := lt_of_lt_of_le hα₀ hαA
  have hα1 : α ≤ 1 := density_le_one A
  have hk2 : (1 : ℝ) ≤ 2 ^ k - 1 := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    linarith
  obtain ⟨j, f, hf1, hfj, hcorr⟩ := large_exp hM hk hMp A hA
  -- the correlation is at least `ε₀`
  have hsmall : α / 2 ^ n ≤ α ^ k / 2 := by
    have hpow : 2 * (1 / α) ^ (k - 1) ≤ 2 ^ n := by
      calc 2 * (1 / α) ^ (k - 1) ≤ 2 * (1 / α₀) ^ (k - 1) := by
            gcongr
          _ ≤ 2 ^ N := hN2
          _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hαk : α ^ k = α * α ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    have hone : (1 / α) ^ (k - 1) * α ^ (k - 1) = 1 := by
      rw [← mul_pow, one_div_mul_cancel hα0.ne', one_pow]
    have h2 : 2 ≤ 2 ^ n * α ^ (k - 1) := by
      nlinarith [pow_pos hα0 (k - 1)]
    rw [div_le_div_iff₀ (by positivity) (by norm_num), hαk]
    nlinarith
  have hε : ε₀ ≤ |((countingDist p k M hM).pi ι).expect fun X => ∏ i, f i fun t => X t i| := by
    refine le_trans ?_ hcorr
    have e1 : α ^ k / (2 ^ k - 1) - α / (2 ^ n * (2 ^ k - 1)) =
        (α ^ k - α / 2 ^ n) / (2 ^ k - 1) := by
      field_simp
    have e2 : α ^ k / (2 * (2 ^ k - 1)) = (α ^ k / 2) / (2 ^ k - 1) := by
      field_simp
    calc ε₀ ≤ α₀ ^ k / (2 * (2 ^ k - 1)) := hε₀
      _ ≤ α ^ k / (2 * (2 ^ k - 1)) := by gcongr
      _ ≤ α ^ k / (2 ^ k - 1) - α / (2 ^ n * (2 ^ k - 1)) := by
          rw [e1, e2]
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- the inverse theorem: the balanced function is noise stable
  have hstab := hinv ι f hf1 hε j
  rw [marginal_countingDist_eq] at hstab
  have hfj' : f j = fun x => (if x ∈ A then (1 : ℝ) else 0) -
      ((FinProb.uniform : FinProb (ZMod p)).pi ι).expect fun x => if x ∈ A then 1 else 0 := by
    ext x; rw [hfj x, expect_uniform_indicator]
  rw [hfj'] at hstab
  have h01 : ∀ x : ι → ZMod p, (if x ∈ A then (1 : ℝ) else 0) = 0 ∨
      (if x ∈ A then (1 : ℝ) else 0) = 1 := fun x => by split_ifs <;> simp
  -- Lemma 6.1: large weight at low degree
  have hW := stability_lemma FinProb.uniform hδ0 hδ1 _ h01 d hd hstab
  -- Lemma 6.2: a random restriction
  have hβ := exp_le_of_log_le (n := n) (d := d) (by positivity) hδ0 (le_trans hN1
    (by exact_mod_cast hn))
  obtain ⟨S, hS, u, hu⟩ := restriction_lemma FinProb.uniform _ h01 d hd2 (δ₀ / 2) hW hβ
  refine ⟨S, u, hS, ?_⟩
  rw [density_fiber, ← expect_uniform_indicator] at *
  linarith

/-- The iteration in the proof of Theorem 1.1: after at most `m` increments the density would
exceed `1`, so the dimension is less than `(2d)^m N`. -/
theorem iteration {δ₀ α₀ : ℝ} {d N : ℕ} (hδ0 : 0 < δ₀) (hd : 1 ≤ d)
    (hinc : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Finset (ι → ZMod p)),
      NoProgression p M k (A : Set (ι → ZMod p)) → α₀ ≤ density A → N ≤ Fintype.card ι →
      ∃ S : Finset ι, ∃ u : ι → ZMod p, (Fintype.card ι : ℝ) / (2 * d) ≤ S.card ∧
        density A + δ₀ / 32 ≤ density (fiber A S u)) :
    ∀ m : ℕ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Finset (ι → ZMod p)),
      NoProgression p M k (A : Set (ι → ZMod p)) → α₀ ≤ density A →
      1 - m * (δ₀ / 32) < density A → (Fintype.card ι : ℝ) < (2 * d) ^ m * N := by
  intro m
  induction m with
  | zero =>
    intro ι _ _ A _ _ hlt
    have := density_le_one A
    simp at hlt
    linarith
  | succ m ih =>
    intro ι _ _ A hA hαA hlt
    by_cases hn : N ≤ Fintype.card ι
    · obtain ⟨S, u, hS, hinc'⟩ := hinc ι A hA hαA hn
      have hA' := fiber_noProgression hA S u
      have h1 : α₀ ≤ density (fiber A S u) := by linarith [show (0 : ℝ) < δ₀ / 32 by positivity]
      have h2 : 1 - m * (δ₀ / 32) < density (fiber A S u) := by push_cast at hlt; linarith
      have := ih S (fiber A S u) hA' h1 h2
      rw [Fintype.card_coe] at this
      have hd0 : (0 : ℝ) < 2 * d := by positivity
      rw [div_le_iff₀ hd0] at hS
      calc (Fintype.card ι : ℝ) ≤ S.card * (2 * d) := hS
        _ < (2 * d) ^ m * N * (2 * d) := mul_lt_mul_of_pos_right this hd0
        _ = (2 * d) ^ (m + 1) * N := by ring
    · have hn' := not_le.mp hn
      calc (Fintype.card ι : ℝ) < N := by exact_mod_cast hn'
        _ ≤ (2 * d) ^ (m + 1) * N := by
          refine le_mul_of_one_le_left (Nat.cast_nonneg _) (one_le_pow₀ ?_)
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith

end RestrictedPolynomials

end
