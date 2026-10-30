import RestrictedPolynomials.QuantDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The explicit parameters `M(ℓ)`, `P(ℓ)` of the quantitative proof, and their growth

* `Mℓ ℓ = ℓ + 4 d_ℓ ℓ² + 1`, which satisfies the hypothesis of Lemma 5.12 (using
  `2^ℓ ℓ! ≤ (ℓ+1)^ℓ ≤ 2^{ℓ²}`), and `M(ℓ) = exp(O(ℓ log ℓ))` since `d_ℓ ≤ ℓ (ℓ+1)^ℓ`.
* `Bbd ℓ`, the bound `(2n)! (2n x²)^{2n}` of `effective_bezout` with `n = n_ℓ(M(ℓ))`, `x = 2^ℓ ℓ!`.
* `Pℓ ℓ = max (d_ℓ + 1) (Bbd^{d_ℓ})` and `P(ℓ) = exp exp(O(ℓ² log ℓ))`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

/-- `M(ℓ) = ℓ + 4 d_ℓ ℓ² + 1`. -/
def Mℓ (ℓ : ℕ) : ℕ := ℓ + 4 * dℓ ℓ * ℓ ^ 2 + 1

/-- The bound on the Bézout multiplier `B`. -/
def Bbd (ℓ : ℕ) : ℕ :=
  (2 * nℓ ℓ (Mℓ ℓ)).factorial *
    (2 * nℓ ℓ (Mℓ ℓ) * (2 ^ ℓ * ℓ.factorial) ^ 2) ^ (2 * nℓ ℓ (Mℓ ℓ))

/-- `P(ℓ) = max (d_ℓ + 1) (Bbd^{d_ℓ})`. -/
def Pℓ (ℓ : ℕ) : ℕ := max (dℓ ℓ + 1) (Bbd ℓ ^ dℓ ℓ)

lemma bern_aux_qp (a k : ℕ) : a ^ k * (a + k) ≤ a * (a + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc a ^ (k+1) * (a + (k+1)) = a^k * (a * (a + k + 1)) := by ring
      _ ≤ a^k * ((a+1) * (a+k)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (a+1) * (a^k * (a+k)) := by ring
      _ ≤ (a+1) * (a * (a+1)^k) := Nat.mul_le_mul_left _ ih
      _ = a * (a+1)^(k+1) := by ring

lemma two_mul_pow_le_qp (n : ℕ) : 2 * (n+1)^(n+1) ≤ (n+2)^(n+1) := by
  have h := bern_aux_qp (n+1) (n+1)
  have h2 : (n+1) * (2 * (n+1)^(n+1)) ≤ (n+1) * (n+2)^(n+1) := by
    calc (n+1) * (2 * (n+1)^(n+1)) = (n+1)^(n+1) * ((n+1)+(n+1)) := by ring
      _ ≤ (n+1) * (n+1+1)^(n+1) := h
      _ = (n+1)*(n+2)^(n+1) := by ring
  exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos n)

lemma two_pow_mul_fact_le_qp (ℓ : ℕ) : 2 ^ ℓ * ℓ.factorial ≤ (ℓ+1)^ℓ := by
  induction ℓ with
  | zero => simp
  | succ n ih =>
    calc 2^(n+1) * (n+1).factorial = 2 * (n+1) * (2^n * n.factorial) := by
          rw [Nat.factorial_succ]; ring
      _ ≤ 2*(n+1) * (n+1)^n := Nat.mul_le_mul_left _ ih
      _ = 2 * (n+1)^(n+1) := by ring
      _ ≤ (n+2)^(n+1) := two_mul_pow_le_qp n

lemma x_le_qp (ℓ : ℕ) : 2 ^ ℓ * ℓ.factorial ≤ 2 ^ (ℓ * ℓ) := by
  calc 2 ^ ℓ * ℓ.factorial ≤ (ℓ+1)^ℓ := two_pow_mul_fact_le_qp ℓ
    _ ≤ (2^ℓ)^ℓ := Nat.pow_le_pow_left (Nat.lt_two_pow_self) ℓ
    _ = 2 ^ (ℓ * ℓ) := by rw [← pow_mul]

lemma dℓ_le_qp (ℓ : ℕ) : dℓ ℓ ≤ ℓ * (ℓ+1)^ℓ := by
  unfold dℓ
  calc ∑ r ∈ range ℓ, (r + 2) ^ (r + 1) ≤ ∑ r ∈ range ℓ, (ℓ+1)^ℓ := by
        apply sum_le_sum
        intro r hr
        have hr' := mem_range.1 hr
        calc (r+2)^(r+1) ≤ (ℓ+1)^(r+1) := Nat.pow_le_pow_left (by omega) _
          _ ≤ (ℓ+1)^ℓ := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ℓ * (ℓ+1)^ℓ := by simp

lemma nℓ_le_qp (ℓ M : ℕ) (h : ℓ ≤ M) (h1 : 1 ≤ M) : nℓ ℓ M ≤ ℓ * M ^ ℓ := by
  unfold nℓ
  calc ∑ r ∈ range ℓ, (M - ℓ + 1 + r) ^ (r + 1) ≤ ∑ r ∈ range ℓ, M ^ ℓ := by
        apply sum_le_sum
        intro r hr
        have hr' := mem_range.1 hr
        calc (M - ℓ + 1 + r)^(r+1) ≤ M^(r+1) := Nat.pow_le_pow_left (by omega) _
          _ ≤ M^ℓ := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ℓ * M ^ ℓ := by simp

lemma Mℓ_ge (ℓ : ℕ) : ℓ + 1 ≤ Mℓ ℓ := by unfold Mℓ; omega

/-- The hypothesis of Lemma 5.12 holds for `M = Mℓ ℓ`. -/
theorem Mℓ_big (ℓ : ℕ) : (2 ^ ℓ * ℓ.factorial) ^ (4 * dℓ ℓ) < 2 ^ (Mℓ ℓ - ℓ) := by
  have h1 : Mℓ ℓ - ℓ = 4 * dℓ ℓ * ℓ ^ 2 + 1 := by unfold Mℓ; omega
  rw [h1]
  calc (2 ^ ℓ * ℓ.factorial) ^ (4 * dℓ ℓ) ≤ (2 ^ (ℓ * ℓ)) ^ (4 * dℓ ℓ) :=
        Nat.pow_le_pow_left (x_le_qp ℓ) _
    _ = 2 ^ (4 * dℓ ℓ * ℓ ^ 2) := by rw [← pow_mul]; congr 1; ring
    _ < 2 ^ (4 * dℓ ℓ * ℓ ^ 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma one_le_nℓ {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 1 ≤ nℓ ℓ (Mℓ ℓ) := by
  unfold nℓ
  have := Finset.single_le_sum (f := fun r => (Mℓ ℓ - ℓ + 1 + r) ^ (r + 1))
    (s := range ℓ) (fun _ _ => Nat.zero_le _) (mem_range.2 (show 0 < ℓ by omega))
  refine le_trans ?_ this
  show 1 ≤ (Mℓ ℓ - ℓ + 1 + 0) ^ (0 + 1)
  exact Nat.one_le_pow _ _ (by omega)

lemma one_le_dℓ {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 1 ≤ dℓ ℓ := by
  unfold dℓ
  have := Finset.single_le_sum (f := fun r => (r + 2) ^ (r + 1))
    (s := range ℓ) (fun _ _ => Nat.zero_le _) (mem_range.2 (show 0 < ℓ by omega))
  refine le_trans ?_ this
  show 1 ≤ (0 + 2) ^ (0 + 1)
  norm_num

lemma dℓ_le_nℓ {ℓ : ℕ} (_hℓ : 1 ≤ ℓ) : dℓ ℓ ≤ nℓ ℓ (Mℓ ℓ) := by
  have h1 : Mℓ ℓ - ℓ = 4 * dℓ ℓ * ℓ ^ 2 + 1 := by unfold Mℓ; omega
  unfold dℓ nℓ
  apply sum_le_sum
  intro r _
  apply Nat.pow_le_pow_left
  have := Mℓ_ge ℓ
  rw [← Nat.sub_add_cancel (Nat.le_of_succ_le this)] at *
  omega

lemma Mℓ_le_pow_qp {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : Mℓ ℓ ≤ (ℓ+1) ^ (7 * ℓ) := by
  have hd := dℓ_le_qp ℓ
  have hL : 2 ≤ ℓ + 1 := by omega
  have h3 : 5 ≤ (ℓ+1)^3 := le_trans (by norm_num) (Nat.pow_le_pow_left hL 3)
  have hA : 4 * dℓ ℓ * ℓ ^ 2 ≤ 4 * (ℓ+1)^(ℓ+3) := by
    calc 4 * dℓ ℓ * ℓ ^ 2 ≤ 4 * (ℓ * (ℓ+1)^ℓ) * ℓ ^ 2 := by gcongr
      _ = 4 * (ℓ^3 * (ℓ+1)^ℓ) := by ring
      _ ≤ 4 * ((ℓ+1)^3 * (ℓ+1)^ℓ) := by gcongr; omega
      _ = 4 * (ℓ+1)^(ℓ+3) := by ring
  have hB : ℓ + 1 ≤ (ℓ+1)^(ℓ+3) := Nat.le_self_pow (by omega) _
  calc Mℓ ℓ = (ℓ + 1) + 4 * dℓ ℓ * ℓ ^ 2 := by unfold Mℓ; ring
    _ ≤ 5 * (ℓ+1)^(ℓ+3) := by omega
    _ ≤ (ℓ+1)^3 * (ℓ+1)^(ℓ+3) := Nat.mul_le_mul_right _ h3
    _ = (ℓ+1)^(ℓ+6) := by ring
    _ ≤ (ℓ+1)^(7*ℓ) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Growth rates**: `M(ℓ) ≤ exp(7 ℓ log(ℓ+1))` and `P(ℓ) ≤ exp(exp(20 ℓ² log(ℓ+1)))`. -/
theorem Mℓ_growth {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (Mℓ ℓ : ℝ) ≤ Real.exp (7 * ℓ * Real.log (ℓ + 1)) := by
  have h := Mℓ_le_pow_qp hℓ
  have h' : (Mℓ ℓ : ℝ) ≤ ((ℓ:ℝ)+1) ^ (7 * ℓ) := by exact_mod_cast h
  have hpos : (0:ℝ) < (ℓ:ℝ) + 1 := by positivity
  have : Real.exp (7 * ℓ * Real.log (ℓ + 1)) = ((ℓ:ℝ)+1) ^ (7 * ℓ) := by
    have := Real.exp_nat_mul (Real.log ((ℓ:ℝ)+1)) (7 * ℓ)
    rw [Real.exp_log hpos] at this
    rw [← this]; push_cast; ring_nf
  rw [this]; exact h'

lemma core_qp {ℓ N K : ℕ} (hℓ : 1 ≤ ℓ) (hN : N ≤ (ℓ+1)^K)
    (hK : K * (ℓ+1) ≤ (ℓ+1)^(20 * ℓ^2)) :
    (N : ℝ) ≤ Real.exp (Real.exp (20 * ℓ ^ 2 * Real.log (ℓ + 1))) := by
  have hpos : (0:ℝ) < (ℓ:ℝ) + 1 := by positivity
  have e1 : Real.exp (20 * ℓ ^ 2 * Real.log (ℓ + 1)) = ((ℓ:ℝ)+1) ^ (20 * ℓ^2) := by
    have := Real.exp_nat_mul (Real.log ((ℓ:ℝ)+1)) (20 * ℓ^2)
    rw [Real.exp_log hpos] at this
    rw [← this]; push_cast; ring_nf
  have hN' : (N : ℝ) ≤ ((ℓ:ℝ)+1) ^ K := by exact_mod_cast hN
  have hK' : (K : ℝ) * ((ℓ:ℝ)+1) ≤ ((ℓ:ℝ)+1) ^ (20 * ℓ^2) := by exact_mod_cast hK
  have hlog : Real.log ((ℓ:ℝ)+1) ≤ (ℓ:ℝ)+1 := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have e2 : ((ℓ:ℝ)+1) ^ K = Real.exp (K * Real.log ((ℓ:ℝ)+1)) := by
    have := Real.exp_nat_mul (Real.log ((ℓ:ℝ)+1)) K
    rw [Real.exp_log hpos] at this
    rw [this]
  rw [e1]
  calc (N:ℝ) ≤ ((ℓ:ℝ)+1) ^ K := hN'
    _ = Real.exp (K * Real.log ((ℓ:ℝ)+1)) := e2
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      calc (K:ℝ) * Real.log ((ℓ:ℝ)+1) ≤ K * ((ℓ:ℝ)+1) := by gcongr
        _ ≤ _ := hK'

theorem Pℓ_growth {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (Pℓ ℓ : ℝ) ≤ Real.exp (Real.exp (20 * ℓ ^ 2 * Real.log (ℓ + 1))) := by
  have hL : 2 ≤ ℓ + 1 := by omega
  have hL1 : 1 ≤ ℓ + 1 := by omega
  have hM := Mℓ_le_pow_qp hℓ
  have hMge := Mℓ_ge ℓ
  have hn : nℓ ℓ (Mℓ ℓ) ≤ (ℓ+1)^(7*ℓ*ℓ+1) := by
    calc nℓ ℓ (Mℓ ℓ) ≤ ℓ * (Mℓ ℓ)^ℓ := nℓ_le_qp ℓ _ (by omega) (by omega)
      _ ≤ (ℓ+1) * ((ℓ+1)^(7*ℓ))^ℓ := by gcongr; omega
      _ = (ℓ+1)^(7*ℓ*ℓ+1) := by rw [← pow_mul, pow_succ']
  have hd : dℓ ℓ ≤ (ℓ+1)^(ℓ+1) := by
    calc dℓ ℓ ≤ ℓ * (ℓ+1)^ℓ := dℓ_le_qp ℓ
      _ ≤ (ℓ+1) * (ℓ+1)^ℓ := by gcongr; omega
      _ = (ℓ+1)^(ℓ+1) := by rw [pow_succ']
  have hx : 2 ^ ℓ * ℓ.factorial ≤ (ℓ+1)^ℓ := two_pow_mul_fact_le_qp ℓ
  have hx1 : 1 ≤ 2 ^ ℓ * ℓ.factorial :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  generalize hnn : nℓ ℓ (Mℓ ℓ) = n at hn
  generalize hdd : dℓ ℓ = d at hd
  generalize hxx : 2 ^ ℓ * ℓ.factorial = x at hx hx1
  have hn1 : 1 ≤ n := by rw [← hnn]; exact one_le_nℓ hℓ
  have hy : 2 * n * x ^ 2 ≤ (ℓ+1)^(11*ℓ*ℓ) := by
    have h2 : 2 * n * x^2 ≤ (ℓ+1) * (ℓ+1)^(7*ℓ*ℓ+1) * ((ℓ+1)^ℓ)^2 := by gcongr
    calc 2 * n * x^2 ≤ _ := h2
      _ = (ℓ+1)^(7*ℓ*ℓ+2+2*ℓ) := by rw [← pow_mul, ← pow_succ', ← pow_add]; ring_nf
      _ ≤ (ℓ+1)^(11*ℓ*ℓ) := Nat.pow_le_pow_right hL1 (by nlinarith)
  have hB : Bbd ℓ ≤ (ℓ+1)^(11*ℓ*ℓ*(4*n)) := by
    unfold Bbd
    rw [hnn, hxx]
    have hxx2 : 2 * n ≤ 2 * n * x ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    calc (2 * n).factorial * (2 * n * x ^ 2) ^ (2 * n)
        ≤ (2 * n) ^ (2 * n) * (2 * n * x ^ 2) ^ (2 * n) :=
          Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
      _ ≤ (2 * n * x ^ 2) ^ (2 * n) * (2 * n * x ^ 2) ^ (2 * n) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hxx2 _)
      _ = (2 * n * x ^ 2) ^ (4 * n) := by rw [← pow_add]; ring_nf
      _ ≤ ((ℓ+1)^(11*ℓ*ℓ)) ^ (4 * n) := Nat.pow_le_pow_left hy _
      _ = (ℓ+1)^(11*ℓ*ℓ*(4*n)) := by rw [← pow_mul]
  have hP1 : Bbd ℓ ^ d ≤ (ℓ+1)^(11*ℓ*ℓ*(4*n)*d) := by
    calc Bbd ℓ ^ d ≤ ((ℓ+1)^(11*ℓ*ℓ*(4*n)))^d := Nat.pow_le_pow_left hB _
      _ = _ := by rw [← pow_mul]
  have hK1 : 11*ℓ*ℓ*(4*n)*d * (ℓ+1) ≤ (ℓ+1)^(20 * ℓ^2) := by
    have h6 : 44 ≤ (ℓ+1)^6 := le_trans (by norm_num) (Nat.pow_le_pow_left hL 6)
    have hℓℓ : ℓ * ℓ ≤ (ℓ+1)^2 := by nlinarith
    calc 11*ℓ*ℓ*(4*n)*d * (ℓ+1) = 44 * (ℓ*ℓ) * n * d * (ℓ+1) := by ring
      _ ≤ 44 * (ℓ+1)^2 * (ℓ+1)^(7*ℓ*ℓ+1) * (ℓ+1)^(ℓ+1) * (ℓ+1) := by gcongr
      _ = 44 * (ℓ+1)^(7*ℓ*ℓ+ℓ+5) := by ring
      _ ≤ (ℓ+1)^6 * (ℓ+1)^(7*ℓ*ℓ+ℓ+5) := Nat.mul_le_mul_right _ h6
      _ = (ℓ+1)^(7*ℓ*ℓ+ℓ+11) := by ring
      _ ≤ (ℓ+1)^(20 * ℓ^2) := Nat.pow_le_pow_right hL1 (by nlinarith)
  have hK2 : (ℓ+2) * (ℓ+1) ≤ (ℓ+1)^(20 * ℓ^2) := by
    calc (ℓ+2) * (ℓ+1) ≤ (ℓ+1)^2 * (ℓ+1)^2 := by
          have : ℓ + 2 ≤ (ℓ+1)^2 := by nlinarith
          have : ℓ + 1 ≤ (ℓ+1)^2 := by nlinarith
          exact Nat.mul_le_mul ‹ℓ + 2 ≤ (ℓ+1)^2› this
      _ = (ℓ+1)^4 := by ring
      _ ≤ (ℓ+1)^(20 * ℓ^2) := Nat.pow_le_pow_right hL1 (by nlinarith)
  have hd2 : d + 1 ≤ (ℓ+1)^(ℓ+2) := by
    calc d + 1 ≤ (ℓ+1)^(ℓ+1) + (ℓ+1)^(ℓ+1) := by
          have : 1 ≤ (ℓ+1)^(ℓ+1) := Nat.one_le_pow _ _ (by omega)
          omega
      _ = 2 * (ℓ+1)^(ℓ+1) := by ring
      _ ≤ (ℓ+1) * (ℓ+1)^(ℓ+1) := Nat.mul_le_mul_right _ hL
      _ = (ℓ+1)^(ℓ+2) := by ring
  unfold Pℓ
  rw [hdd]
  rw [Nat.cast_max]
  apply max_le
  · have := core_qp hℓ hd2 hK2
    exact_mod_cast this
  · have := core_qp hℓ hP1 hK1
    exact_mod_cast this

end RestrictedPolynomials

end
