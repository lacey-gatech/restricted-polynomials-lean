import RestrictedPolynomials.Stability
import RestrictedPolynomials.Hoeffding
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Random restrictions (Lemma 6.2)

A random set `S` of free coordinates, containing each coordinate independently with
probability `1/d`, is modelled by a sample `s` of the product measure `Bernoulli(1/d)^{⊗ι}`,
with `S = {i : s i = true}`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Bernoulli distribution on `Bool` with `ℙ(true) = q`. -/
def bernoulli (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinProb Bool where
  prob b := if b then q else 1 - q
  nonneg b := by cases b <;> simp [h0, h1]
  sum_eq_one := by simp

/-- The set `{i : s i = true}`. -/
def trueSet (s : ι → Bool) : Finset ι := univ.filter fun i => s i = true

omit [DecidableEq ι] in
lemma card_trueSet (s : ι → Bool) :
    ((trueSet s).card : ℝ) = ∑ i, if s i = true then (1 : ℝ) else 0 := by
  simp only [trueSet, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-! ### The size of the random set -/

/-- Hoeffding's inequality for the lower tail of `|S|`. -/
lemma bernoulli_lower_tail {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (hn : 0 < Fintype.card ι) :
    ((bernoulli q h0 h1).pi ι).expect
        (fun s => if ((trueSet s).card : ℝ) ≤ Fintype.card ι * q - a then 1 else 0) ≤
      Real.exp (-2 * a ^ 2 / Fintype.card ι) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hnpos : 0 < n := by simp [hn_def, hn]
  set t : ℝ := 4 * a / n with ht
  have ht0 : 0 ≤ t := by positivity
  -- the indicator is dominated by an exponential
  have hdom : ∀ s : ι → Bool,
      (if ((trueSet s).card : ℝ) ≤ n * q - a then (1 : ℝ) else 0) ≤
        Real.exp (-t * a) * ∏ i, Real.exp (t * (q - if s i = true then 1 else 0)) := by
    intro s
    rw [← Real.exp_sum, ← Real.exp_add]
    have hsum : ∑ i, t * (q - if s i = true then (1 : ℝ) else 0) =
        t * (n * q - (trueSet s).card) := by
      rw [← mul_sum, sum_sub_distrib, card_trueSet]
      simp [hn_def, mul_comm]
    rw [hsum]
    split_ifs with h
    · rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by nlinarith)
    · exact (Real.exp_pos _).le
  have hH := hoeffding_bernoulli h0 h1 t
  calc ((bernoulli q h0 h1).pi ι).expect
        (fun s => if ((trueSet s).card : ℝ) ≤ n * q - a then 1 else 0)
      ≤ ((bernoulli q h0 h1).pi ι).expect
          (fun s => Real.exp (-t * a) * ∏ i, Real.exp (t * (q - if s i = true then 1 else 0))) :=
        FinProb.expect_mono _ hdom
    _ = Real.exp (-t * a) *
          ∏ _i : ι, ((1 - q) * Real.exp (t * q) + q * Real.exp (t * (q - 1))) := by
        rw [FinProb.expect_const_mul]
        congr 1
        refine (FinProb.expect_pi_prod _
          (fun _ b => Real.exp (t * (q - if b = true then 1 else 0)))).trans ?_
        refine prod_congr rfl fun i _ => ?_
        simp only [FinProb.expect, bernoulli, Fintype.sum_bool, ite_true]
        simp
        ring_nf
    _ ≤ Real.exp (-t * a) * ∏ _i : ι, Real.exp (t ^ 2 / 8) := by
        refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => ?_) fun i _ => hH)
          (Real.exp_pos _).le
        have := Real.exp_pos (t * q)
        have := Real.exp_pos (t * (q - 1))
        nlinarith
    _ = Real.exp (-t * a + n * (t ^ 2 / 8)) := by
        rw [prod_const, ← Real.exp_nat_mul, ← Real.exp_add, card_univ]
    _ = Real.exp (-2 * a ^ 2 / n) := by
        congr 1
        rw [ht]
        field_simp
        ring

omit [DecidableEq ι] in
/-- With `q = 1/d`, the set `S` has fewer than `n/(2d)` elements with probability at most
`exp(-n/(2d²))`. -/
lemma small_set_prob (d : ℕ) (hd : 1 ≤ d) [DecidableEq ι] :
    ((bernoulli (1 / d) (by positivity) (by
        rw [div_le_one (by exact_mod_cast hd)]; exact_mod_cast hd)).pi ι).expect
        (fun s => if ((trueSet s).card : ℝ) < Fintype.card ι / (2 * d) then 1 else 0) ≤
      Real.exp (-(Fintype.card ι : ℝ) / (2 * d ^ 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · refine (FinProb.expect_le_const _ fun s => ?_).trans (Real.exp_pos _).le
    rw [ite_eq_right]
    simp [hn]
  refine ((FinProb.expect_mono _ fun s => ?_).trans
    (bernoulli_lower_tail _ _ (a := Fintype.card ι / (2 * d)) (by positivity) hn)).trans
    (le_of_eq ?_)
  · split_ifs with h1 h2
    · rfl
    · exfalso; apply h2
      have : (Fintype.card ι : ℝ) * (1 / d) - Fintype.card ι / (2 * d) =
          Fintype.card ι / (2 * d) := by field_simp; ring
      linarith
    · exact zero_le_one
    · rfl
  · congr 1
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
    field_simp

/-! ### An elementary inequality -/

/-- `(1 - 1/d)^m ≥ 1/4` for `m ≤ d` and `d ≥ 2`. -/
lemma one_sub_inv_pow_ge {d m : ℕ} (hd : 2 ≤ d) (hm : m ≤ d) : 1 / 4 ≤ (1 - 1 / (d : ℝ)) ^ m := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 ≤ 1 - 1 / (d : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hq1 : 1 - 1 / (d : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith
  refine le_trans ?_ (pow_le_pow_of_le_one hq0 hq1 hm)
  rcases (show d = 2 ∨ d = 3 ∨ 4 ≤ d by omega) with rfl | rfl | h4
  · norm_num
  · norm_num
  · have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast h4
    have hpos : 0 < 1 - 1 / (d : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    -- `log(1 - 1/d) ≥ -1/(d-1)`
    have hlog : -1 / ((d : ℝ) - 1) ≤ Real.log (1 - 1 / d) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
      have hdne : (d : ℝ) ≠ 0 := by linarith
      have heq : 1 - (1 - 1 / (d : ℝ))⁻¹ = -1 / ((d : ℝ) - 1) := by
        rw [show (1 - 1 / (d : ℝ)) = ((d : ℝ) - 1) / d by field_simp, inv_div]
        field_simp
        ring
      linarith
    have hexp : Real.exp (-(4 / 3)) ≤ (1 - 1 / (d : ℝ)) ^ d := by
      rw [← Real.exp_log (pow_pos hpos d), Real.log_pow, Real.exp_le_exp]
      have h1 : (d : ℝ) * (-1 / ((d : ℝ) - 1)) ≥ -(4 / 3) := by
        rw [ge_iff_le, mul_div_assoc', le_div_iff₀ (by linarith)]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ d by linarith)]
    have h4 : (1 : ℝ) / 4 ≤ Real.exp (-(4 / 3)) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos _)]
      have : (4 : ℝ) / 3 ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9
        push_cast
        linarith
      calc Real.exp (4 / 3) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.2 this
        _ = 4 := Real.exp_log (by norm_num)
    linarith

/-! ### The second moment of a random restriction -/

omit [DecidableEq α] in
/-- `𝔼_S 𝔼_u (𝔼(f | x_{Sᶜ} = u_{Sᶜ}))² = ∑_{S'} (1 - q)^{|S'|} ‖f^{=S'}‖₂²`. -/
lemma second_moment {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (π : FinProb α) (f : (ι → α) → ℝ) :
    ((bernoulli q h0 h1).pi ι).expect
        (fun s => (π.pi ι).expect fun u => condExp π (trueSet s)ᶜ f u ^ 2) =
      ∑ S' : Finset ι, (1 - q) ^ S'.card * (π.pi ι).expect fun x => esPart π S' f x ^ 2 := by
  have hs : ∀ s : ι → Bool, ((π.pi ι).expect fun u => condExp π (trueSet s)ᶜ f u ^ 2) =
      ∑ S' : Finset ι, (∏ i ∈ S', if s i = true then (0 : ℝ) else 1) *
        (π.pi ι).expect fun x => esPart π S' f x ^ 2 := by
    intro s
    rw [expect_condExp_sq]
    rw [← sum_filter_add_sum_filter_not univ fun S' : Finset ι => S' ⊆ (trueSet s)ᶜ]
    have hzero : ∑ S' with ¬ S' ⊆ (trueSet s)ᶜ, (∏ i ∈ S', if s i = true then (0 : ℝ) else 1) *
        (π.pi ι).expect (fun x => esPart π S' f x ^ 2) = 0 := by
      refine sum_eq_zero fun S' hS' => ?_
      simp only [mem_filter, mem_univ, true_and] at hS'
      obtain ⟨i, hi, hic⟩ := not_subset.1 hS'
      have : s i = true := by simpa [trueSet] using hic
      rw [prod_eq_zero hi (by simp [this]), zero_mul]
    rw [hzero, add_zero]
    refine sum_congr (ext fun S' => by simp) fun S' hS' => ?_
    simp only [mem_filter, mem_univ, true_and] at hS'
    rw [prod_eq_one, one_mul]
    intro i hi
    have := hS' hi
    simp only [trueSet, mem_compl, mem_filter, mem_univ, true_and] at this
    simp [this]
  simp only [hs, FinProb.expect_sum, FinProb.expect_mul_const]
  refine sum_congr rfl fun S' _ => ?_
  congr 1
  have hprod : ∀ s : ι → Bool, (∏ i ∈ S', if s i = true then (0 : ℝ) else 1) =
      ∏ i, (fun i (b : Bool) => if i ∈ S' then (if b = true then (0 : ℝ) else 1) else 1) i (s i) := by
    intro s
    rw [← prod_filter_mul_prod_filter_not univ (fun i : ι => i ∈ S'), prod_eq_one (s := univ.filter (fun i : ι => i ∉ S'))
      (fun i hi => by simp [(mem_filter.1 hi).2]), mul_one]
    exact prod_congr (ext fun i => by simp) fun i hi => by simp [(mem_filter.1 hi).2]
  rw [FinProb.expect_congr _ hprod]
  refine (FinProb.expect_pi_prod (ι := ι) (bernoulli q h0 h1)
    (fun i (b : Bool) => if i ∈ S' then (if b = true then (0 : ℝ) else 1) else 1)).trans ?_
  rw [← prod_filter_mul_prod_filter_not univ (fun i : ι => i ∈ S')]
  rw [prod_eq_one (s := univ.filter (fun i : ι => i ∉ S')) (fun i hi => by
    simp [(mem_filter.1 hi).2, FinProb.expect_const]), mul_one]
  rw [show univ.filter (fun i : ι => i ∈ S') = S' from ext fun i => by simp]
  rw [prod_congr rfl fun i hi => (show (bernoulli q h0 h1).expect
      (fun b => if i ∈ S' then (if b = true then (0 : ℝ) else 1) else 1) = 1 - q by
        simp [hi, FinProb.expect, bernoulli]), prod_const]

/-! ### Lemma 6.2 -/

omit [DecidableEq α] in
/-- **Lemma 6.2** (random restriction). -/
theorem restriction_lemma (π : FinProb α) (f : (ι → α) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1)
    (d : ℕ) (hd : 2 ≤ d) (β : ℝ)
    (hβ : β ≤ lowDegWeight π d fun x => f x - (π.pi ι).expect f)
    (hβn : 16 * Real.exp (-(Fintype.card ι : ℝ) / (2 * d ^ 2)) ≤ β) :
    ∃ S : Finset ι, (Fintype.card ι : ℝ) / (2 * d) ≤ S.card ∧ ∃ u : ι → α,
      (π.pi ι).expect f + β / 16 ≤ (π.pi S).expect fun v => f (FinProb.extend S v u) := by
  set a := (π.pi ι).expect f with ha
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hq0 : 0 ≤ 1 / (d : ℝ) := by positivity
  have hq1 : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hd0]; exact_mod_cast (show 1 ≤ d by omega)
  set B := bernoulli (1 / d) hq0 hq1 with hB
  set Z : (ι → Bool) → (ι → α) → ℝ := fun s u => condExp π (trueSet s)ᶜ f u with hZ
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβn
  have ha0 : 0 ≤ a := (π.pi ι).expect_nonneg fun x => by rcases hf x with h | h <;> simp [h]
  have ha1 : a ≤ 1 := (π.pi ι).expect_le_const fun x => by rcases hf x with h | h <;> simp [h]
  have hZ0 : ∀ s u, 0 ≤ Z s u := fun s u =>
    (π.pi ι).expect_nonneg fun y => by rcases hf ((trueSet s)ᶜ.piecewise u y) with h | h <;> simp [h]
  have hZ1 : ∀ s u, Z s u ≤ 1 := fun s u =>
    (π.pi ι).expect_le_const fun y => by rcases hf ((trueSet s)ᶜ.piecewise u y) with h | h <;> simp [h]
  -- the second moment is at least `a² + β/4`
  set w : Finset ι → ℝ := fun S => (π.pi ι).expect fun x => esPart π S f x ^ 2 with hw
  have hw0 : ∀ S, 0 ≤ w S := fun S => (π.pi ι).expect_nonneg fun x => sq_nonneg _
  have hwe : w ∅ = a ^ 2 := by simp [hw, esPart_empty, ha]
  have hlow : lowDegWeight π d (fun x => f x - a) =
      ∑ S with S.card ≤ d, if S = ∅ then 0 else w S := by
    unfold lowDegWeight
    refine sum_congr rfl fun S _ => ?_
    simp only [esPart_sub_const]
    split_ifs with hS
    · subst hS; simp [esPart_empty, ha]
    · simp [hw]
  have hmoment : a ^ 2 + β / 4 ≤
      (B.pi ι).expect fun s => (π.pi ι).expect fun u => Z s u ^ 2 := by
    rw [second_moment]
    have hpt : ∀ S : Finset ι, (if S = ∅ then w S else 0) +
        (if S.card ≤ d then (if S = ∅ then 0 else w S) / 4 else 0) ≤
          (1 - 1 / (d : ℝ)) ^ S.card * w S := by
      intro S
      by_cases hS : S = ∅
      · subst hS; simp
      · simp only [hS, ite_false, zero_add]
        split_ifs with hc
        · exact le_trans (by linarith [hw0 S]) (mul_le_mul_of_nonneg_right
            (one_sub_inv_pow_ge hd hc) (hw0 S))
        · exact mul_nonneg (pow_nonneg (by linarith [hq1]) _) (hw0 S)
    refine le_trans ?_ (sum_le_sum fun S _ => hpt S)
    rw [sum_add_distrib, sum_ite_eq' univ (∅ : Finset ι), ite_eq_left (mem_univ _), hwe,
      ← sum_filter, ← sum_div, ← hlow]
    linarith
  -- the good event `G = {Z² ≥ a² + β/8}` has probability at least `β/8`
  set G : (ι → Bool) → (ι → α) → ℝ :=
    fun s u => if a ^ 2 + β / 8 ≤ Z s u ^ 2 then 1 else 0 with hG
  have hG01 : ∀ s u, 0 ≤ G s u ∧ G s u ≤ 1 := fun s u => by
    simp only [hG]; split_ifs <;> norm_num
  set PG := (B.pi ι).expect fun s => (π.pi ι).expect fun u => G s u with hPG
  have hPG0 : 0 ≤ PG := (B.pi ι).expect_nonneg fun s =>
    (π.pi ι).expect_nonneg fun u => (hG01 s u).1
  have hZG : ∀ s u, Z s u ^ 2 ≤ G s u + (a ^ 2 + β / 8) * (1 - G s u) := by
    intro s u
    simp only [hG]
    split_ifs with h
    · nlinarith [hZ0 s u, hZ1 s u]
    · linarith [not_le.mp h]
  have hPGlb : β / 8 ≤ PG := by
    have h1 : ((B.pi ι).expect fun s => (π.pi ι).expect fun u => Z s u ^ 2) ≤
        PG + (a ^ 2 + β / 8) * (1 - PG) := by
      calc ((B.pi ι).expect fun s => (π.pi ι).expect fun u => Z s u ^ 2)
          ≤ (B.pi ι).expect fun s => (π.pi ι).expect fun u =>
              G s u + (a ^ 2 + β / 8) * (1 - G s u) :=
            (B.pi ι).expect_mono fun s => (π.pi ι).expect_mono fun u => hZG s u
        _ = PG + (a ^ 2 + β / 8) * (1 - PG) := by
            simp only [FinProb.expect_add, FinProb.expect_const_mul, FinProb.expect_sub,
              FinProb.expect_const]
            rw [← hPG]
    have hc : 0 ≤ (a ^ 2 + β / 8) * PG := mul_nonneg (by positivity) hPG0
    nlinarith
  -- the small-set event has probability at most `β/16`
  set Bc : (ι → Bool) → ℝ :=
    fun s => if ((trueSet s).card : ℝ) < Fintype.card ι / (2 * d) then 1 else 0 with hBc
  have hPBc : (B.pi ι).expect Bc ≤ β / 16 := by
    have := small_set_prob (ι := ι) d (by omega)
    rw [hB]
    linarith
  -- so the joint event has positive probability
  have hjoint : 0 < (B.pi ι).expect fun s => (π.pi ι).expect fun u => G s u * (1 - Bc s) := by
    have hpt : ∀ s u, G s u - Bc s ≤ G s u * (1 - Bc s) := by
      intro s u
      have := hG01 s u
      simp only [hBc]; split_ifs <;> nlinarith
    have := (B.pi ι).expect_mono fun s => (π.pi ι).expect_mono fun u => hpt s u
    simp only [FinProb.expect_sub, FinProb.expect_const] at this
    rw [← hPG] at this
    have hBc' : ((B.pi ι).expect fun s => (π.pi ι).expect fun _ : ι → α => Bc s) =
        (B.pi ι).expect Bc := by simp
    linarith
  obtain ⟨s, hs⟩ := (B.pi ι).exists_pos_of_expect_pos hjoint
  obtain ⟨u, hu⟩ := (π.pi ι).exists_pos_of_expect_pos hs
  have hGs : a ^ 2 + β / 8 ≤ Z s u ^ 2 := by
    by_contra h; simp [hG, h] at hu
  have hBs : (Fintype.card ι : ℝ) / (2 * d) ≤ (trueSet s).card := by
    by_contra! h; simp [hBc, h] at hu
  refine ⟨trueSet s, hBs, u, ?_⟩
  -- `Z ≥ a + β/16`
  have hZbig : a + β / 16 ≤ Z s u := by
    have hZs0 := hZ0 s u
    have hZs1 := hZ1 s u
    by_contra! h
    have h1 : Z s u ^ 2 < (a + β / 16) ^ 2 := pow_lt_pow_left₀ h hZs0 two_ne_zero
    have h2 : a ^ 2 + β / 8 ≤ 1 := le_trans hGs (by nlinarith)
    have h3 : β / 8 * 1 < β / 8 * (a + β / 32) := by nlinarith
    have h4 : 1 < a + β / 32 := lt_of_mul_lt_mul_left h3 (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 ha1) (show (0 : ℝ) ≤ 3 - a by linarith)]
  have hrestr : Z s u = (π.pi (trueSet s)).expect fun v => f (FinProb.extend (trueSet s) v u) := by
    rw [← FinProb.expect_piecewise_eq_expect_extend]
    refine (π.pi ι).expect_congr fun y => ?_
    congr 1
    ext i; by_cases hi : i ∈ trueSet s <;> simp [hi]
  rw [← hrestr]
  exact hZbig

end RestrictedPolynomials

end
