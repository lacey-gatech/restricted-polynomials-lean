module

public import RestrictedPolynomials.TrackB.K6ToswapUniform
public import RestrictedPolynomials.TrackB.K6Lowering
public import RestrictedPolynomials.TrackB.SwapNorm
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.RestrictCompose
public import RestrictedPolynomials.TrackB.SwapInduct
public import RestrictedPolynomials.TrackB.BoundedProdCore
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open Finset
open scoped BigOperators
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section MainUniform

/-- `K₁ = K 4^{K+1}` (Step 7, in the shape of the swap theorem `δ ≥ (ε/(2B))^{K ⌈1/ε⌉^K}`). -/
def k6K1 (K : ℕ) : ℝ := (K : ℝ) * 4 ^ (K + 1)

/-- `E₁ = N (K+1) / 2`. -/
def k6E1 (N K : ℕ) : ℝ := (N : ℝ) * ((K : ℝ) + 1) / 2

/-- `C'' = ln(4/α_*) + 2N + (1 + C_b) K₁` with `C_b = 1400`. -/
def k6Cpp (αs : ℝ) (N K : ℕ) : ℝ := Real.log (4 / αs) + 2 * (N : ℝ) + (1 + 1400) * k6K1 K

/-- `C' = max(C'', E₁)`. -/
def k6Cprime (αs : ℝ) (N K : ℕ) : ℝ := max (k6Cpp αs N K) (k6E1 N K)

/-- `C_α = 2 C' + 1`. -/
def k6CAlpha (αs : ℝ) (N K : ℕ) : ℝ := 2 * k6Cprime αs N K + 1

/-- `L_α(ε) = exp(-C ε^{-C})` with `C = C_α`. -/
def k6L (α ε : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-(k6CAlpha (k6ptAlphaStar α) (k6ptN (k6ptR1 α) (k6ptR2 α)) K) *
    ε ^ (-(k6CAlpha (k6ptAlphaStar α) (k6ptN (k6ptR1 α) (k6ptR2 α)) K)))

private theorem k6E1_nonneg (N K : ℕ) : 0 ≤ k6E1 N K := by
  unfold k6E1
  positivity

private theorem k6K1_nonneg (K : ℕ) : 0 ≤ k6K1 K := by
  unfold k6K1
  positivity

private theorem k6E1_ge_one {N : ℕ} (K : ℕ) (hN : 16 ≤ N) : 1 ≤ k6E1 N K := by
  unfold k6E1
  have : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

private theorem k6Cprime_nonneg (αs : ℝ) (N K : ℕ) : 0 ≤ k6Cprime αs N K :=
  (k6E1_nonneg N K).trans (le_max_right _ _)

theorem one_le_k6CAlpha {αs : ℝ} (hαs0 : 0 < αs) (hαs : αs ≤ 1 / 2) (N K : ℕ) (hN : 16 ≤ N) :
    1 ≤ k6CAlpha αs N K := by
  have _ := hαs0
  have _ := hαs
  have _ := hN
  have := k6Cprime_nonneg αs N K
  unfold k6CAlpha
  linarith

/-! ### Real analysis of Steps 7-8 -/

/-- `δ₁ ≥ exp(-K₁ z^{K+1})` from the swap bound, when `2/ε₁ ≤ 4 z`. -/
private theorem k6_delta1_lower {e z δ₁ : ℝ} {K : ℕ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hz : 2 / e ≤ 4 * z)
    (hswap : (e / 2) ^ (K * ⌈1 / e⌉₊ ^ K) ≤ δ₁) :
    Real.exp (-(k6K1 K * z ^ (K + 1))) ≤ δ₁ := by
  have hz0 : 0 ≤ z := by
    have : 0 < 2 / e := by positivity
    linarith
  have h1e : 1 ≤ 1 / e := by
    rw [le_div_iff₀ he0]
    linarith
  have hm : ((⌈1 / e⌉₊ : ℕ) : ℝ) ≤ 4 * z := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / e by positivity)
    have h2 : 2 / e = 2 * (1 / e) := by ring
    linarith
  have hm0 : (0 : ℝ) ≤ ((⌈1 / e⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log (2 / e) ≤ 4 * z :=
    (Real.log_le_self (by positivity)).trans hz
  have hlog0 : 0 ≤ Real.log (2 / e) := Real.log_nonneg (by
    rw [le_div_iff₀ he0]; linarith)
  set n : ℕ := K * ⌈1 / e⌉₊ ^ K with hn
  have hnle : (n : ℝ) ≤ K * (4 * z) ^ K := by
    rw [hn]
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hm K) (Nat.cast_nonneg K)
  have hprod : (n : ℝ) * Real.log (2 / e) ≤ k6K1 K * z ^ (K + 1) := by
    calc (n : ℝ) * Real.log (2 / e) ≤ (K * (4 * z) ^ K) * (4 * z) :=
          mul_le_mul hnle hlog hlog0 (by positivity)
      _ = k6K1 K * z ^ (K + 1) := by
          unfold k6K1
          rw [mul_pow, pow_succ, pow_succ]
          ring
  have hpow : (e / 2) ^ n = Real.exp (-((n : ℝ) * Real.log (2 / e))) := by
    have hpos : 0 < (e / 2) ^ n := by positivity
    rw [← Real.exp_log hpos, Real.log_pow]
    congr 1
    have : Real.log (e / 2) = -Real.log (2 / e) := by
      rw [← Real.log_inv, inv_div]
    rw [this]
    ring
  calc Real.exp (-(k6K1 K * z ^ (K + 1))) ≤ Real.exp (-((n : ℝ) * Real.log (2 / e))) :=
        Real.exp_le_exp.2 (by linarith)
    _ = (e / 2) ^ n := hpow.symm
    _ ≤ δ₁ := hswap

/-- Steps 7-8 (real analysis): with `ε₁ = (ε^{2N}/2)^{1/4}` and `δ₁` at least the swap-theorem
bound at `(ε₁, B = 1)`, `L_α(ε) ≤ δ_*² / 2` for `δ_* = min{α_* δ₁, δ₂/2, c₁ δ₁ δ₂/2}`,
`δ₂ = δ₁^{1400}`, `c₁ = ε^{2N}/2`. -/
theorem k6_L_le_deltaStar_sq_half {αs : ℝ} (hαs0 : 0 < αs) (hαs : αs ≤ 1 / 2) {N K : ℕ}
    (hN : 16 ≤ N) {ε δ₁ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ₁0 : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1)
    (hswap : ((ε ^ (2 * N) / 2) ^ (1 / 4 : ℝ) / 2) ^
        (K * ⌈1 / (ε ^ (2 * N) / 2) ^ (1 / 4 : ℝ)⌉₊ ^ K) ≤ δ₁) :
    Real.exp (-(k6CAlpha αs N K) * ε ^ (-(k6CAlpha αs N K))) ≤
      (min (αs * δ₁) (min (δ₁ ^ 1400 / 2) (ε ^ (2 * N) / 2 * δ₁ * δ₁ ^ 1400 / 2))) ^ 2 / 2 := by
  have hεN : 0 < ε ^ (2 * N) := pow_pos hε0 _
  have hεN1 : ε ^ (2 * N) ≤ 1 := pow_le_one₀ hε0.le hε1
  obtain ⟨e, he⟩ : ∃ e, e = (ε ^ (2 * N) / 2) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← he] at hswap
  have he0 : 0 < e := by rw [he]; positivity
  have he4 : e ^ 4 = ε ^ (2 * N) / 2 := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have he1 : e ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < e ^ 4 := one_lt_pow₀ h (by norm_num)
    linarith
  -- y, z
  obtain ⟨y, hy⟩ : ∃ y, y = ε ^ ((N : ℝ) / 2) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy4 : y ^ 4 = ε ^ (2 * N) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hye : y / 2 ≤ e := by
    have : (y / 2) ^ 4 ≤ e ^ 4 := by
      rw [he4, div_pow, hy4]
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) he0.le this
  obtain ⟨z, hz⟩ : ∃ z, z = ε ^ (-((N : ℝ) / 2)) := ⟨_, rfl⟩
  have hzy : z = 1 / y := by
    rw [hz, hy, Real.rpow_neg hε0.le, one_div]
  have hz0 : 0 < z := by rw [hz]; positivity
  have h2e : 2 / e ≤ 4 * z := by
    rw [hzy]
    calc 2 / e ≤ 2 / (y / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hye
      _ = 4 * (1 / y) := by field_simp; norm_num
  set X : ℝ := ε ^ (-(k6E1 N K)) with hX
  have hXz : X = z ^ (K + 1) := by
    rw [hX, hz, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    congr 1
    unfold k6E1
    push_cast
    ring
  have hE1 : 1 ≤ k6E1 N K := k6E1_ge_one K hN
  have hX1 : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1 (by linarith)
  have hδlow : Real.exp (-(k6K1 K * X)) ≤ δ₁ := by
    rw [hXz]
    exact k6_delta1_lower he0 he1 h2e hswap
  -- logs
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (4 / αs) := ⟨_, rfl⟩
  have hexpL : Real.exp (-L) = αs / 4 := by
    rw [hL, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hL0 : 0 ≤ L := by
    rw [hL]
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hαs0]
    linarith
  have hαs4 : αs / 4 ≤ 1 / 4 := by linarith
  have hεlog : Real.log (1 / ε) ≤ X := by
    refine (Real.log_le_self (by positivity)).trans ?_
    have : ε ^ (-(1 : ℝ)) ≤ ε ^ (-(k6E1 N K)) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
    rw [Real.rpow_neg_one] at this
    simpa using this
  have hεexp : Real.exp (-((2 * N : ℝ) * X)) ≤ ε ^ (2 * N) := by
    have : ε ^ (2 * N) = Real.exp ((2 * N : ℕ) * Real.log ε) := by
      rw [← Real.log_pow, Real.exp_log hεN]
    rw [this]
    refine Real.exp_le_exp.2 ?_
    have hlog : Real.log ε = -Real.log (1 / ε) := by
      rw [one_div, Real.log_inv]; ring
    rw [hlog]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    push_cast
    nlinarith
  -- constants
  have hK1 := k6K1_nonneg K
  have hC'' : k6Cpp αs N K ≤ k6Cprime αs N K := le_max_left _ _
  have hE1C : k6E1 N K ≤ k6Cprime αs N K := le_max_right _ _
  have hC'0 := k6Cprime_nonneg αs N K
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCpp : k6Cpp αs N K = L + 2 * N + (1 + 1400) * k6K1 K := by
    unfold k6Cpp; rw [hL]
  set T : ℝ := k6Cprime αs N K * ε ^ (-(k6Cprime αs N K)) with hT
  have hXT : X ≤ ε ^ (-(k6Cprime αs N K)) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hCX : (L + 2 * N + (1 + 1400) * k6K1 K) * X ≤ T := by
    rw [← hCpp]
    have hC0 : 0 ≤ k6Cpp αs N K := by rw [hCpp]; positivity
    calc k6Cpp αs N K * X ≤ k6Cprime αs N K * X := mul_le_mul_of_nonneg_right hC'' (by linarith)
      _ ≤ T := mul_le_mul_of_nonneg_left hXT hC'0
  have hδ1X : Real.exp (-(k6K1 K * X)) ^ 1400 = Real.exp (-(1400 * (k6K1 K * X))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hKX0 : 0 ≤ k6K1 K * X := by positivity
  -- each term is ≥ exp(-T)
  have hδ1pow : Real.exp (-(1400 * (k6K1 K * X))) ≤ δ₁ ^ 1400 := by
    rw [← hδ1X]; exact pow_le_pow_left₀ (Real.exp_pos _).le hδlow 1400
  have hδ1pow' : Real.exp (-(1401 * (k6K1 K * X))) ≤ δ₁ ^ 1401 := by
    have : Real.exp (-(k6K1 K * X)) ^ 1401 = Real.exp (-(1401 * (k6K1 K * X))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [← this]; exact pow_le_pow_left₀ (Real.exp_pos _).le hδlow 1401
  have hLX : L ≤ L * X := by nlinarith
  have hNX : 0 ≤ (N : ℝ) * X := by positivity
  have hCX' : L * X + 2 * ((N : ℝ) * X) + 1401 * (k6K1 K * X) ≤ T := by
    have := hCX
    ring_nf at this ⊢
    linarith
  have t1 : Real.exp (-T) ≤ αs * δ₁ := by
    have : Real.exp (-T) ≤ Real.exp (-L) * Real.exp (-(k6K1 K * X)) := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_; linarith
    refine this.trans ?_
    rw [hexpL]
    exact mul_le_mul (by linarith) hδlow (Real.exp_pos _).le hαs0.le
  have t2 : Real.exp (-T) ≤ δ₁ ^ 1400 / 2 := by
    have : Real.exp (-T) ≤ Real.exp (-L) * Real.exp (-(1400 * (k6K1 K * X))) := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_; linarith
    refine this.trans ?_
    rw [hexpL]
    have := mul_le_mul (show αs / 4 ≤ 1 / 2 by linarith) hδ1pow (Real.exp_pos _).le
      (by norm_num : (0:ℝ) ≤ 1 / 2)
    linarith
  have t3 : Real.exp (-T) ≤ ε ^ (2 * N) / 2 * δ₁ * δ₁ ^ 1400 / 2 := by
    have : Real.exp (-T) ≤ Real.exp (-L) * (Real.exp (-((2 * N : ℝ) * X)) *
        Real.exp (-(1401 * (k6K1 K * X)))) := by
      rw [← Real.exp_add, ← Real.exp_add]; refine Real.exp_le_exp.2 ?_; linarith
    refine this.trans ?_
    have e1 : ε ^ (2 * N) / 2 * δ₁ * δ₁ ^ 1400 / 2 = (ε ^ (2 * N) * δ₁ ^ 1401) / 4 := by ring
    rw [e1, hexpL]
    have h3 : Real.exp (-((2 * N : ℝ) * X)) * Real.exp (-(1401 * (k6K1 K * X))) ≤
        ε ^ (2 * N) * δ₁ ^ 1401 :=
      mul_le_mul hεexp hδ1pow' (Real.exp_pos _).le hεN.le
    have h4 : 0 ≤ Real.exp (-((2 * N : ℝ) * X)) * Real.exp (-(1401 * (k6K1 K * X))) := by
      positivity
    calc αs / 4 * (Real.exp (-((2 * N : ℝ) * X)) * Real.exp (-(1401 * (k6K1 K * X))))
        ≤ 1 / 4 * (ε ^ (2 * N) * δ₁ ^ 1401) :=
          mul_le_mul hαs4 h3 h4 (by norm_num)
      _ = _ := by ring
  have hmin : Real.exp (-T) ≤ min (αs * δ₁) (min (δ₁ ^ 1400 / 2)
      (ε ^ (2 * N) / 2 * δ₁ * δ₁ ^ 1400 / 2)) := le_min t1 (le_min t2 t3)
  -- final
  have hCα1 : k6CAlpha αs N K = 2 * k6Cprime αs N K + 1 := rfl
  have hε1' : ε ^ (-(k6Cprime αs N K)) ≤ ε ^ (-(k6CAlpha αs N K)) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by rw [hCα1]; linarith)
  have hε2 : 1 ≤ ε ^ (-(k6CAlpha αs N K)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1 (by rw [hCα1]; linarith)
  have hbig : 2 * T + 1 ≤ k6CAlpha αs N K * ε ^ (-(k6CAlpha αs N K)) := by
    have h := mul_le_mul_of_nonneg_left hε1' (show 0 ≤ 2 * k6Cprime αs N K by linarith)
    nth_rewrite 1 [hCα1]
    rw [hT]
    linarith
  have hexp1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hmin0 : 0 ≤ Real.exp (-T) := (Real.exp_pos _).le
  calc Real.exp (-(k6CAlpha αs N K) * ε ^ (-(k6CAlpha αs N K)))
      ≤ Real.exp (-(2 * T) + -1) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-T) ^ 2 * Real.exp (-1) := by
        rw [Real.exp_add, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    _ ≤ Real.exp (-T) ^ 2 * (1 / 2) :=
        mul_le_mul_of_nonneg_left hexp1 (by positivity)
    _ ≤ _ := by
        have := pow_le_pow_left₀ hmin0 hmin 2
        linarith

/-! ### Expectation calculus -/

private theorem re_cexpect_eq {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) :
    (P.cexpect f).re = ∑ k, P.prob k * (f k).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

private theorem expect_affine {κ : Type} [Fintype κ] (P : FinProb κ) (f g : κ → ℂ)
    (a c₀ c₁ : ℝ) (h : ∀ k, a * (f k).re ≤ c₀ + c₁ * (g k).re) :
    a * (P.cexpect f).re ≤ c₀ + c₁ * (P.cexpect g).re := by
  rw [re_cexpect_eq, re_cexpect_eq]
  calc a * ∑ k, P.prob k * (f k).re = ∑ k, P.prob k * (a * (f k).re) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k, P.prob k * (c₀ + c₁ * (g k).re) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (P.nonneg k)
    _ = c₀ + c₁ * ∑ k, P.prob k * (g k).re := by
        have : ∀ k, P.prob k * (c₀ + c₁ * (g k).re) =
            P.prob k * c₀ + c₁ * (P.prob k * (g k).re) := fun k => by ring
        simp_rw [this]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, P.sum_eq_one]
        ring

private theorem expect_nonneg' {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ)
    (h : ∀ k, 0 ≤ (f k).re) : 0 ≤ (P.cexpect f).re := by
  rw [re_cexpect_eq]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (P.nonneg k) (h k)

section Nested
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem nested_affine (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (ν : FinProb α)
    (f g : ∀ I : Finset ι, (↥I → α) → ℂ) (a c₀ c₁ : ℝ)
    (h : ∀ I z, a * (f I z).re ≤ c₀ + c₁ * (g I z).re) :
    a * (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (f I)).re ≤
      c₀ + c₁ * (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (g I)).re := by
  unfold subsetExpect
  exact expect_affine _ _ _ a c₀ c₁ fun s => expect_affine _ _ _ a c₀ c₁ (h _)

private theorem nested_nonneg (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (ν : FinProb α)
    (g : ∀ I : Finset ι, (↥I → α) → ℂ) (h : ∀ I z, 0 ≤ (g I z).re) :
    0 ≤ (subsetExpect q h0 h1 fun I => (ν.pi ↥I).cexpect (g I)).re := by
  unfold subsetExpect
  exact expect_nonneg' _ _ fun s => expect_nonneg' _ _ (h _)

open scoped Classical in
/-- the event inside `GoodRestr` as a `ℂ`-valued indicator. -/
private def badC (f : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) : ℂ :=
  if ∃ P : ↥Jᶜ → α → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      η ≤ ‖𝔼 x : ↥Jᶜ → α, restrictFix J v f x * ∏ i, P i (x i)‖ then (1 : ℂ) else 0

private theorem badC_re_nonneg (f : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α) :
    0 ≤ (badC f η J v).re := by
  unfold badC
  split_ifs <;> simp

private theorem badC_re_of (f : (ι → α) → ℂ) (η : ℝ) (J : Finset ι) (v : J → α)
    (h : ∃ P : ↥Jᶜ → α → ℂ, (∀ i a, ‖P i a‖ ≤ 1) ∧
      η ≤ ‖𝔼 x : ↥Jᶜ → α, restrictFix J v f x * ∏ i, P i (x i)‖) :
    (badC f η J v).re = 1 := by
  unfold badC
  rw [if_pos h]
  simp

end Nested

private theorem norm_expect_le_one {κ : Type} [Fintype κ] [Nonempty κ] (g : κ → ℂ)
    (h : ∀ k, ‖g k‖ ≤ 1) : ‖𝔼 k, g k‖ ≤ 1 := by
  refine (RCLike.norm_expect_le (K := ℂ)).trans ?_
  calc 𝔼 k, ‖g k‖ ≤ 𝔼 _k : κ, (1 : ℝ) := Finset.expect_le_expect fun k _ => h k
    _ = 1 := Finset.expect_const Finset.univ_nonempty _

private theorem val_re_le_one {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    (val F F F F).re ≤ 1 := by
  refine (Complex.re_le_norm _).trans ?_
  unfold val
  refine norm_expect_le_one _ fun x => norm_expect_le_one _ fun y => norm_expect_le_one _ fun b => ?_
  rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star]
  have := hF x
  have := hF y
  have := hF (swapL b x y)
  have := hF (swapR b x y)
  have h0 : ∀ u : (ι → α), 0 ≤ ‖F u‖ := fun u => norm_nonneg _
  calc ‖F x‖ * ‖F y‖ * ‖F (swapL b x y)‖ * ‖F (swapR b x y)‖ ≤ 1 * 1 * 1 * 1 := by
        gcongr
        all_goals first | exact hF _ | exact h0 _
    _ = 1 := by norm_num

private theorem l2sq_le_one {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : (ι → α) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    l2sq F ≤ 1 := by
  unfold l2sq
  calc 𝔼 x : ι → α, ‖F x‖ ^ 2 ≤ 𝔼 _x : ι → α, (1 : ℝ) :=
        Finset.expect_le_expect fun x _ => pow_le_one₀ (norm_nonneg _) (hF x)
    _ = 1 := Finset.expect_const Finset.univ_nonempty _

/-! ### Steps 2-5: swap, composition, bounded product -/

section Step5
variable {X : Type} [Fintype X] [DecidableEq X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Steps 3-4 for one composite restriction: a swap witness for `f_{J→w}` becomes a bounded
witness (`δ₁^{1400}`) for the composed restriction `(I ∪ I', (w, w'))`. -/
private theorem swap_to_bad {δ₁ : ℝ}
    (hbp1 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (F : (κ → X) → ℂ),
      (∀ x, ‖F x‖ ≤ 1) → ∀ (P : κ → X → ℂ), (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) →
        δ₁ ≤ ‖𝔼 x : κ → X, F x * ∏ i, P i (x i)‖ →
          ∃ P' : κ → X → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
            δ₁ ^ 1400 ≤ ‖𝔼 x : κ → X, F x * ∏ i, P' i (x i)‖)
    (f : (ι → X) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (I : Finset ι) (w : I → X)
    (I' : Finset ↥Iᶜ) (w' : I' → X)
    (P : ↥I'ᶜ → X → ℂ) (hP : ∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1)
    (hδ : δ₁ ≤ ‖𝔼 x : ↥I'ᶜ → X, restrictFix I' w' (restrictFix I w f) x *
      star (∏ i, P i (x i))‖) :
    ∃ Q : ↥(composeSet I I')ᶜ → X → ℂ, (∀ i a, ‖Q i a‖ ≤ 1) ∧
      δ₁ ^ 1400 ≤ ‖𝔼 x : ↥(composeSet I I')ᶜ → X,
        restrictFix (composeSet I I') (composeVals I I' w w') f x * ∏ i, Q i (x i)‖ := by
  classical
  set g : (↥Iᶜ → X) → ℂ := restrictFix I w f with hg
  have hF : ∀ y, ‖restrictFix I' w' g y‖ ≤ 1 := fun y => hf _
  obtain ⟨P', hP', hb⟩ := hbp1 (↥I'ᶜ) (restrictFix I' w' g) hF (fun i a => star (P i a))
    (fun i => by simpa only [norm_star] using hP i)
    (by
      refine hδ.trans (le_of_eq ?_)
      congr 2
      funext x
      rw [star_prod])
  refine ⟨fun j => P' (composeEquiv I I' j), fun j a => hP' _ a, ?_⟩
  have hEq : (𝔼 x : ↥(composeSet I I')ᶜ → X, restrictFix (composeSet I I')
      (composeVals I I' w w') f x * ∏ j, P' (composeEquiv I I' j) (x j)) =
      𝔼 y : ↥I'ᶜ → X, restrictFix I' w' g y * ∏ i : ↥I'ᶜ, P' i (y i) := by
    symm
    refine Fintype.expect_equiv
      (Equiv.arrowCongr (composeEquiv I I').symm (Equiv.refl X)) _ _ fun y => ?_
    have hy : (Equiv.arrowCongr (composeEquiv I I').symm (Equiv.refl X)) y =
        fun j => y (composeEquiv I I' j) := by
      funext j
      simp [Equiv.arrowCongr_apply]
    rw [hy, hg, restrictFix_compose I I' w w' f y]
    congr 1
    exact (Fintype.prod_equiv (composeEquiv I I') (fun j => P' (composeEquiv I I' j)
      (y (composeEquiv I I' j))) (fun i => P' i (y i)) fun j => rfl).symm
  rw [hEq]
  exact hb

open scoped Classical in
/-- Steps 1-5: `S_π(f; ρ, δ₂, c₁ δ₁)` with `ρ = a₀ δ₁`. -/
private theorem k6_step5 [Nonempty X] (νs νρ : FinProb X) {a₀ δ₁ c₁ T : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀1 : a₀ ≤ 1) (hδ₁0 : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1) (hc₁ : 0 ≤ c₁) (hT : T = 2 * c₁)
    (hbar : ∀ a, (1 - a₀ * δ₁) * νρ.prob a =
      (1 - a₀) * νs.prob a + a₀ * (1 - δ₁) * (FinProb.uniform (α := X)).prob a)
    (f : (ι → X) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hval : T ≤ (subsetExpect (1 - a₀) (by linarith) (by linarith) fun I =>
      (νs.pi ↥I).cexpect fun z => (((val (restrictFix I z f) (restrictFix I z f)
        (restrictFix I z f) (restrictFix I z f)).re : ℝ) : ℂ)).re)
    (hsw : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (F : (κ → X) → ℂ), (∀ x, ‖F x‖ ≤ 1) →
      l2sq F ≤ 1 → c₁ ≤ (val F F F F).re →
      δ₁ ≤ (subsetExpect (1 - δ₁) (by linarith) (by linarith) fun I =>
        ((FinProb.uniform (α := X)).pi ↥I).cexpect fun z =>
          if ∃ P : ↥Iᶜ → X → ℂ, (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) ∧
              δ₁ ≤ ‖𝔼 x : ↥Iᶜ → X, restrictFix I z F x * star (∏ i, P i (x i))‖
            then (1 : ℂ) else 0).re)
    (hbp1 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (F : (κ → X) → ℂ),
      (∀ x, ‖F x‖ ≤ 1) → ∀ (P : κ → X → ℂ), (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) →
        δ₁ ≤ ‖𝔼 x : κ → X, F x * ∏ i, P i (x i)‖ →
          ∃ P' : κ → X → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
            δ₁ ^ 1400 ≤ ‖𝔼 x : κ → X, F x * ∏ i, P' i (x i)‖) :
    GoodRestr νρ (a₀ * δ₁) (δ₁ ^ 1400) (c₁ * δ₁)
      (by nlinarith) (by nlinarith) f := by
  have ha1 : 0 ≤ 1 - a₀ := by linarith
  have ha1' : 1 - a₀ ≤ 1 := by linarith
  have hd1 : 0 ≤ 1 - δ₁ := by linarith
  have hd1' : 1 - δ₁ ≤ 1 := by linarith
  let v : ∀ I : Finset ι, (↥I → X) → ℝ := fun I z => (val (restrictFix I z f) (restrictFix I z f)
    (restrictFix I z f) (restrictFix I z f)).re
  let g : ∀ I : Finset ι, (↥I → X) → ℂ := fun I z => if c₁ ≤ v I z then (1 : ℂ) else 0
  let Inner : ∀ I : Finset ι, (↥I → X) → ℂ := fun I w =>
    subsetExpect (ι := ↥Iᶜ) (1 - δ₁) hd1 hd1' fun I' =>
      ((FinProb.uniform (α := X)).pi ↥I').cexpect fun w' =>
        badC f (δ₁ ^ 1400) (composeSet I I') (composeVals I I' w w')
  have hg_re : ∀ I z, (g I z).re = if c₁ ≤ v I z then 1 else 0 := by
    intro I z
    simp only [g]
    split_ifs <;> simp
  -- Step A
  have hA := nested_affine (ι := ι) (1 - a₀) ha1 ha1' νs
    (fun I z => ((v I z : ℝ) : ℂ)) g 1 c₁ 1 (fun I z => by
      rw [hg_re]
      have h1 : v I z ≤ 1 := val_re_le_one _ (fun x => hf _)
      simp only [Complex.ofReal_re, one_mul]
      split_ifs with hc
      · linarith
      · linarith [not_le.1 hc])
  -- Step B
  have hB := nested_affine (ι := ι) (1 - a₀) ha1 ha1' νs g Inner δ₁ 0 1 (fun I z => by
    rw [hg_re]
    by_cases hc : c₁ ≤ v I z
    · rw [if_pos hc]
      have hs := hsw (↥Iᶜ) (restrictFix I z f) (fun x => hf _)
        (l2sq_le_one _ (fun x => hf _)) hc
      have hm := nested_affine (ι := ↥Iᶜ) (1 - δ₁) hd1 hd1' (FinProb.uniform (α := X))
        (fun I' w' => if ∃ P : ↥I'ᶜ → X → ℂ, (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) ∧
              δ₁ ≤ ‖𝔼 x : ↥I'ᶜ → X, restrictFix I' w' (restrictFix I z f) x *
                star (∏ i, P i (x i))‖ then (1 : ℂ) else 0)
        (fun I' w' => badC f (δ₁ ^ 1400) (composeSet I I') (composeVals I I' z w'))
        1 0 1 (fun I' w' => by
          by_cases hc' : ∃ P : ↥I'ᶜ → X → ℂ, (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) ∧
              δ₁ ≤ ‖𝔼 x : ↥I'ᶜ → X, restrictFix I' w' (restrictFix I z f) x *
                star (∏ i, P i (x i))‖
          · obtain ⟨P, hP, hn⟩ := hc'
            rw [if_pos ⟨P, hP, hn⟩]
            rw [badC_re_of _ _ _ _ (swap_to_bad hbp1 f hf I z I' w' P hP hn)]
            simp
          · rw [if_neg hc']
            simp only [Complex.zero_re, mul_zero, zero_add, one_mul]
            exact badC_re_nonneg _ _ _ _)
      simp only [one_mul, zero_add] at hm
      rw [mul_one, zero_add, one_mul]
      exact hs.trans hm
    · rw [if_neg hc]
      simp only [mul_zero, zero_add, one_mul]
      exact nested_nonneg (ι := ↥Iᶜ) (1 - δ₁) hd1 hd1' _ _ fun I' w' => badC_re_nonneg _ _ _ _)
  have hnest := nested_restriction_law (ι := ι) ha₀ ha₀1 hδ₁0.le hδ₁1 νs
    (FinProb.uniform (α := X)) νρ hbar (fun J u => badC f (δ₁ ^ 1400) J u)
  have hEg : c₁ ≤ (subsetExpect (1 - a₀) ha1 ha1' fun I =>
      (νs.pi ↥I).cexpect (g I)).re := by
    simp only [one_mul] at hA
    linarith
  have key : c₁ * δ₁ ≤ (subsetExpect (1 - a₀) ha1 ha1' fun I =>
      (νs.pi ↥I).cexpect (Inner I)).re := by
    simp only [zero_add, one_mul] at hB
    nlinarith
  have hcongr := congrArg Complex.re hnest
  exact le_of_le_of_eq key hcongr

end Step5

/-! ### Mixtures -/

private theorem nonempty_of_finProb {β : Type} [Fintype β] (π : FinProb β) : Nonempty β := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := π.sum_eq_one
  simp at this

private theorem exists_mix {β : Type} [Fintype β] (π : FinProb β) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h : ∀ a, r * (1 / (Fintype.card β : ℝ)) ≤ π.prob a) :
    ∃ ν : FinProb β, ∀ a, π.prob a = (1 - r) * ν.prob a + r * (1 / (Fintype.card β : ℝ)) := by
  have hne := nonempty_of_finProb π
  have hc : (Fintype.card β : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := β)
    positivity
  have h1r : 0 < 1 - r := by linarith
  refine ⟨⟨fun a => (π.prob a - r * (1 / (Fintype.card β : ℝ))) / (1 - r), fun a => ?_, ?_⟩,
    fun a => ?_⟩
  · exact div_nonneg (by linarith [h a]) h1r.le
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, π.sum_eq_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
  · show _ = (1 - r) * ((π.prob a - r * (1 / (Fintype.card β : ℝ))) / (1 - r)) + _
    field_simp
    ring

open scoped Classical in
/-- Thm main-uniform with explicit constants. `hswapK` is the body of `swap_theorem`
(CSP_6 `thm:swap`, absolute constant `K`), `hbp` is `boundedprod_one_bounded` (CSP_6 `thm:boundedprod`,
exponent `1400`), both as hypotheses ((I3), (I4) of Supplement D). `δ' ≤ 1` is TYPING
(needed to state `GoodRestr`; automatic from `δ' ≤ L_α(ε) < 1/2`). -/
theorem k6_main_uniform_explicit_of_swap_boundedprod (K : ℕ)
    (hswapK : ∀ ε B : ℝ, 0 < ε → ε ≤ 1 → ε ≤ B →
      ∃ (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1), (ε / (2 * B)) ^ (K * ⌈1 / ε⌉₊ ^ K) ≤ δ ∧
        ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι]
          [DecidableEq ι] (f : (ι → α) → ℂ), (∀ x, ‖f x‖ ≤ B) → l2sq f ≤ 1 →
          ε ^ 4 ≤ (val f f f f).re →
          δ ≤ (subsetExpect (1 - δ) (by linarith) (by linarith) fun I =>
            ((FinProb.uniform (α := α)).pi ↥I).cexpect fun z =>
              if ∃ P : ↥Iᶜ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
                  δ ≤ ‖𝔼 x : ↥Iᶜ → α, restrictFix I z f x * star (∏ i, P i (x i))‖
                then (1 : ℂ) else 0).re)
    (hbp : ∀ (α : Type) [Fintype α] (ι : Type) [Fintype ι] [DecidableEq ι] (F : (ι → α) → ℂ),
      (∀ x, ‖F x‖ ≤ 1) → ∀ (P : ι → α → ℂ), (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ ‖𝔼 x : ι → α, F x * ∏ i, P i (x i)‖ →
          ∃ P' : ι → α → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
            δ ^ 1400 ≤ ‖𝔼 x : ι → α, F x * ∏ i, P' i (x i)‖)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support) {α : ℝ}
    (hα0 : 0 < α) (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ k6L α ε K) :
    ∃ ν : FinProb X,
      (∀ a, k6ptMargX μ a = (1 - δ) * ν.prob a + δ * (1 / (Fintype.card X : ℝ))) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
        ε ≤ ‖(μ.pi ι).cexpect fun p =>
          f (fun i => (p i).1) * g (fun i => (p i).2.1) * h (fun i => (p i).2.2)‖ →
        GoodRestr ν δ δ δ hδ0.le hδ1 f := by
  have hneX : Nonempty X := by
    have := nonempty_of_finProb μ
    exact ⟨(Classical.choice this).1⟩
  have hr₁ := one_le_k6ptR1 α
  have hr₂ := one_le_k6ptR2 α
  have hN : 16 ≤ k6ptN (k6ptR1 α) (k6ptR2 α) := sixteen_le_k6ptN hr₁ hr₂
  have hαs0 := k6ptAlphaStar_pos hα0
  have hαs := k6ptAlphaStar_le_half α
  obtain ⟨νs, hνs⟩ := k6pt_nuStar_exists μ hμ hα0 hatom
  obtain ⟨N, hNdef⟩ : ∃ N, N = k6ptN (k6ptR1 α) (k6ptR2 α) := ⟨_, rfl⟩
  obtain ⟨αs, hαsdef⟩ : ∃ αs, αs = k6ptAlphaStar α := ⟨_, rfl⟩
  rw [← hNdef] at hN
  rw [← hαsdef] at hαs0 hαs
  have hεN : 0 < ε ^ (2 * N) := pow_pos hε0 _
  have hεN1 : ε ^ (2 * N) ≤ 1 := pow_le_one₀ hε0.le hε1
  obtain ⟨e, he⟩ : ∃ e, e = (ε ^ (2 * N) / 2) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  have he4 : e ^ 4 = ε ^ (2 * N) / 2 := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have he1 : e ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : 1 < e ^ 4 := one_lt_pow₀ hcon (by norm_num)
    linarith
  obtain ⟨δ₁, hδ₁0, hδ₁1, hb, hsw⟩ := hswapK e 1 he0 he1 he1
  rw [mul_one] at hb
  have hL := k6_L_le_deltaStar_sq_half (N := N) (K := K) hαs0 hαs hN hε0 hε1 hδ₁0 hδ₁1
    (by rw [← he]; exact hb)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = ε ^ (2 * N) / 2 := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  rw [← hc₁] at hL
  obtain ⟨ds, hds⟩ : ∃ ds, ds = min (αs * δ₁) (min (δ₁ ^ 1400 / 2) (c₁ * δ₁ * δ₁ ^ 1400 / 2)) :=
    ⟨_, rfl⟩
  rw [← hds] at hL
  have hδ2 : δ ≤ ds ^ 2 / 2 := by
    refine hδL.trans (le_trans (le_of_eq ?_) hL)
    unfold k6L
    rw [hNdef, hαsdef]
  have hd0 : 0 < ds := by
    rw [hds]
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdρ : ds ≤ αs * δ₁ := by rw [hds]; exact min_le_left _ _
  have hd2 : ds ≤ δ₁ ^ 1400 / 2 := by rw [hds]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hd3 : ds ≤ c₁ * δ₁ * δ₁ ^ 1400 / 2 := by
    rw [hds]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hρle : αs * δ₁ ≤ αs := by nlinarith
  have hρ1 : αs * δ₁ < 1 := by linarith
  have hdle : ds ≤ αs := hdρ.trans hρle
  have hds1 : ds < 1 := by linarith
  have hδle : δ ≤ ds := by nlinarith
  have hδ'1 : δ < 1 := by linarith
  -- the marginal as a probability measure
  let π : FinProb X :=
    ⟨k6ptMargX μ, fun a => Finset.sum_nonneg fun p _ => μ.nonneg p, by
      unfold k6ptMargX
      rw [Finset.sum_fiberwise univ (fun p : X × Y × Z => p.1) μ.prob]
      exact μ.sum_eq_one⟩
  have hπ : ∀ a, π.prob a = k6ptMargX μ a := fun a => rfl
  have hcard : (0 : ℝ) < Fintype.card X := by
    have := Fintype.card_pos (α := X)
    exact_mod_cast this
  have hνs' : ∀ a, π.prob a = (1 - αs) * νs.prob a + αs * (1 / (Fintype.card X : ℝ)) := by
    intro a
    rw [hπ, hνs a, hαsdef]
  have hatoms : ∀ r, 0 ≤ r → r ≤ αs → ∀ a,
      r * (1 / (Fintype.card X : ℝ)) ≤ π.prob a := by
    intro r hr0 hr a
    rw [hνs' a]
    have h1 : 0 ≤ (1 - αs) * νs.prob a := mul_nonneg (by linarith) (νs.nonneg a)
    have h2 : r * (1 / (Fintype.card X : ℝ)) ≤ αs * (1 / (Fintype.card X : ℝ)) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    linarith
  obtain ⟨νρ, hνρ⟩ := exists_mix π (mul_nonneg hαs0.le hδ₁0.le) hρ1
    (hatoms _ (mul_nonneg hαs0.le hδ₁0.le) hρle)
  obtain ⟨νd, hνd⟩ := exists_mix π hd0.le hds1 (hatoms _ hd0.le hdle)
  obtain ⟨ν, hν⟩ := exists_mix π hδ0.le hδ'1 (hatoms _ hδ0.le (hδle.trans hdle))
  refine ⟨ν, fun a => by rw [← hπ]; exact hν a, ?_⟩
  intro ι _ _ f g h hf hg hh hcorr
  have hval := k6pt_toswap_uniform μ hμ hα0 hatom νs hνs hε0 ι f g h hf hg hh hcorr
  have hbar : ∀ a, (1 - αs * δ₁) * νρ.prob a =
      (1 - αs) * νs.prob a + αs * (1 - δ₁) * (FinProb.uniform (α := X)).prob a := by
    intro a
    have e1 := hνρ a
    have e2 := hνs' a
    have e3 : (FinProb.uniform (α := X)).prob a = 1 / (Fintype.card X : ℝ) := rfl
    rw [e3]
    linarith
  have hsw' : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (F : (κ → X) → ℂ), (∀ x, ‖F x‖ ≤ 1) →
      l2sq F ≤ 1 → c₁ ≤ (val F F F F).re →
      δ₁ ≤ (subsetExpect (1 - δ₁) (by linarith) (by linarith) fun I =>
        ((FinProb.uniform (α := X)).pi ↥I).cexpect fun z =>
          if ∃ P : ↥Iᶜ → X → ℂ, (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) ∧
              δ₁ ≤ ‖𝔼 x : ↥Iᶜ → X, restrictFix I z F x * star (∏ i, P i (x i))‖
            then (1 : ℂ) else 0).re := by
    intro κ _ _ F hF hl hv
    refine hsw X κ F ?_ hl ?_
    · exact hF
    · rw [he4, ← hc₁]; exact hv
  have hbp1 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (F : (κ → X) → ℂ),
      (∀ x, ‖F x‖ ≤ 1) → ∀ (P : κ → X → ℂ), (∀ i, 𝔼 a : X, ‖P i a‖ ^ 2 ≤ 1) →
        δ₁ ≤ ‖𝔼 x : κ → X, F x * ∏ i, P i (x i)‖ →
          ∃ P' : κ → X → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
            δ₁ ^ 1400 ≤ ‖𝔼 x : κ → X, F x * ∏ i, P' i (x i)‖ :=
    fun κ _ _ F hF P hP hc => hbp X κ F hF P hP hδ₁0 hδ₁1 hc
  have h5 := k6_step5 νs νρ (a₀ := αs) (c₁ := c₁) (T := ε ^ (2 * N)) hαs0.le
    (by linarith) hδ₁0 hδ₁1 hc₁0.le (by rw [hc₁]; ring) hbar f hf
    (by subst hNdef hαsdef; exact hval) hsw' hbp1
  have hlow := goodRestr_lowering π νρ νd (ρ := αs * δ₁) (ρ' := ds) (η := δ₁ ^ 1400)
    (p := c₁ * δ₁) (mul_pos hαs0 hδ₁0) hρ1 hd0 hdρ (pow_pos hδ₁0 _) hνρ hνd f hf h5
  have hmono := goodRestr_mono νd hd0.le (hds1.le) f
    (η := δ₁ ^ 1400 / 2) (η' := ds) (p := c₁ * δ₁ * δ₁ ^ 1400 / 2) (p' := ds) hd2 hd3 hlow
  exact goodRestr_lowering_delta π νd ν hd0 hds1 hδ0 hδ2 hνd hν f hf hmono

open scoped Classical in
/-- Thm main-uniform (existential form): `C_α` depends on `α` and the absolute constant of
`swap_theorem` only; it is chosen before `X, Y, Z, μ, ε, δ'`. Conditional on `hswap` and `hbp`
as hypotheses; the unconditional form is `k6_main_uniform`. -/
theorem k6_main_uniform_of_swap_boundedprod
    (hswap : ∃ K : ℕ, ∀ ε B : ℝ, 0 < ε → ε ≤ 1 → ε ≤ B →
      ∃ (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1), (ε / (2 * B)) ^ (K * ⌈1 / ε⌉₊ ^ K) ≤ δ ∧
        ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (ι : Type) [Fintype ι]
          [DecidableEq ι] (f : (ι → α) → ℂ), (∀ x, ‖f x‖ ≤ B) → l2sq f ≤ 1 →
          ε ^ 4 ≤ (val f f f f).re →
          δ ≤ (subsetExpect (1 - δ) (by linarith) (by linarith) fun I =>
            ((FinProb.uniform (α := α)).pi ↥I).cexpect fun z =>
              if ∃ P : ↥Iᶜ → α → ℂ, (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) ∧
                  δ ≤ ‖𝔼 x : ↥Iᶜ → α, restrictFix I z f x * star (∏ i, P i (x i))‖
                then (1 : ℂ) else 0).re)
    (hbp : ∀ (α : Type) [Fintype α] (ι : Type) [Fintype ι] [DecidableEq ι] (F : (ι → α) → ℂ),
      (∀ x, ‖F x‖ ≤ 1) → ∀ (P : ι → α → ℂ), (∀ i, 𝔼 a : α, ‖P i a‖ ^ 2 ≤ 1) →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ ‖𝔼 x : ι → α, F x * ∏ i, P i (x i)‖ →
          ∃ P' : ι → α → ℂ, (∀ i a, ‖P' i a‖ ≤ 1) ∧
            δ ^ 1400 ≤ ‖𝔼 x : ι → α, F x * ∏ i, P' i (x i)‖)
    {α : ℝ} (hα0 : 0 < α) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z] (μ : FinProb (X × Y × Z)), PairwiseConnected3 μ.support →
        (∀ p ∈ μ.support, α ≤ μ.prob p) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ δ : ℝ, (hδ0 : 0 < δ) → (hδ1 : δ ≤ 1) → δ ≤ Real.exp (-C * ε ^ (-C)) →
        ∃ ν : FinProb X,
          (∀ a, k6ptMargX μ a = (1 - δ) * ν.prob a + δ * (1 / (Fintype.card X : ℝ))) ∧
          ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
            (h : (ι → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖(μ.pi ι).cexpect fun p =>
              f (fun i => (p i).1) * g (fun i => (p i).2.1) * h (fun i => (p i).2.2)‖ →
            GoodRestr ν δ δ δ hδ0.le hδ1 f := by
  obtain ⟨K, hK⟩ := hswap
  refine ⟨k6CAlpha (k6ptAlphaStar α) (k6ptN (k6ptR1 α) (k6ptR2 α)) K,
    one_le_k6CAlpha (k6ptAlphaStar_pos hα0) (k6ptAlphaStar_le_half α) _ K
      (sixteen_le_k6ptN (one_le_k6ptR1 α) (one_le_k6ptR2 α)), ?_⟩
  intro X Y Z _ _ _ _ _ _ μ hμ hatom ε hε0 hε1 δ hδ0 hδ1 hδL
  exact k6_main_uniform_explicit_of_swap_boundedprod K hK hbp μ hμ hα0 hatom hε0 hε1 hδ0 hδ1 hδL

open scoped Classical in
/-- Thm main-uniform with explicit constants, unconditional. The absolute constant `K` of
`swap_theorem` is existentially quantified first (it cannot be a free binder: `swap_theorem`
provides one `K`, and the claim is false for small `K`); the rest is the statement of
`k6_main_uniform_explicit_of_swap_boundedprod` without `hswapK` and `hbp`. -/
theorem k6_main_uniform_explicit : ∃ K : ℕ,
    ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support) {α : ℝ}
    (hα0 : 0 < α) (hatom : ∀ p ∈ μ.support, α ≤ μ.prob p) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ k6L α ε K),
    ∃ ν : FinProb X,
      (∀ a, k6ptMargX μ a = (1 - δ) * ν.prob a + δ * (1 / (Fintype.card X : ℝ))) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
        (h : (ι → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
        ε ≤ ‖(μ.pi ι).cexpect fun p =>
          f (fun i => (p i).1) * g (fun i => (p i).2.1) * h (fun i => (p i).2.2)‖ →
        GoodRestr ν δ δ δ hδ0.le hδ1 f := by
  obtain ⟨K, hK⟩ := swap_theorem
  refine ⟨K, ?_⟩
  intro X Y Z _ _ _ _ _ _ μ hμ α hα0 hatom ε hε0 hε1 δ hδ0 hδ1 hδL
  exact k6_main_uniform_explicit_of_swap_boundedprod K hK
    (fun _ _ _ _ _ F hF P hP => boundedprod_one_bounded F hF P hP) μ hμ hα0 hatom hε0 hε1 hδ0
    hδ1 hδL

open scoped Classical in
/-- Thm main-uniform (CSP_6 `thm:main` with `δ ≥ L_α(ε) = exp(-C_α ε^{-C_α})`),
unconditional: `k6_main_uniform_of_swap_boundedprod` with `swap_theorem` and
`boundedprod_one_bounded`. -/
theorem k6_main_uniform {α : ℝ} (hα0 : 0 < α) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z] (μ : FinProb (X × Y × Z)), PairwiseConnected3 μ.support →
        (∀ p ∈ μ.support, α ≤ μ.prob p) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ δ : ℝ, (hδ0 : 0 < δ) → (hδ1 : δ ≤ 1) → δ ≤ Real.exp (-C * ε ^ (-C)) →
        ∃ ν : FinProb X,
          (∀ a, k6ptMargX μ a = (1 - δ) * ν.prob a + δ * (1 / (Fintype.card X : ℝ))) ∧
          ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
            (h : (ι → Z) → ℂ), (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖(μ.pi ι).cexpect fun p =>
              f (fun i => (p i).1) * g (fun i => (p i).2.1) * h (fun i => (p i).2.2)‖ →
            GoodRestr ν δ δ δ hδ0.le hδ1 f :=
  k6_main_uniform_of_swap_boundedprod swap_theorem
    (fun _ _ _ _ _ F hF P hP => boundedprod_one_bounded F hF P hP) hα0

end MainUniform

end TrackB
end RestrictedPolynomials
end
