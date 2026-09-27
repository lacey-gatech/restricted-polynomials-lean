import RestrictedPolynomials.Counting
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.ZMod

/-!
# No abelian embeddings into `𝔽_q`, `q ≠ p` (Lemma 5.9)

Extend scalars to a field `L ⊇ 𝔽_q` containing a primitive `p`-th root of unity `ζ`, and
decompose functions `𝔽_p → L` along the characters `x ↦ λ^x`, `λ^p = 1`. The coefficient of
`λ ≠ 1` of `f_1, …, f_ℓ` is a kernel vector of `A_{ℓ,M}(λ)`, hence zero by the full rank
hypothesis, and a function whose nontrivial coefficients vanish is constant.

The full rank statement (Proposition 5.1) enters as the hypothesis `hfull`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

section Fourier

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]

lemma pow_val_add {μ : L} (hμ : μ ^ p = 1) (a b : ZMod p) :
    μ ^ (a + b).val = μ ^ a.val * μ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) p, pow_add, pow_mul, hμ, one_pow, one_mul]

lemma pow_natCast_val {μ : L} (hμ : μ ^ p = 1) (n : ℕ) : μ ^ ((n : ZMod p)).val = μ ^ n := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hμ, one_pow, one_mul]

/-- The Fourier coefficient `Ĝ(μ) = ∑ₓ G(x) μ^{-x}`. -/
def fourier (G : ZMod p → L) (μ : L) : L := ∑ x, G x * μ ^ (-x).val

/-- Translation multiplies the Fourier coefficient by a character. -/
lemma fourier_shift {μ : L} (hμ : μ ^ p = 1) (G : ZMod p → L) (a : ZMod p) :
    ∑ x, G (x + a) * μ ^ (-x).val = μ ^ a.val * fourier G μ := by
  rw [fourier, mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
  simp only [Equiv.coe_addRight]
  rw [show -x = a + -(x + a) by ring, pow_val_add hμ]
  ring

/-- The geometric sum of a primitive root: `∑_{m < p} ζ^{mt} = p [p ∣ t]`. -/
lemma sum_pow_primitive {ζ : L} (hζ : IsPrimitiveRoot ζ p) (t : ℕ) :
    ∑ m ∈ range p, (ζ ^ t) ^ m = if p ∣ t then (p : L) else 0 := by
  split_ifs with ht
  · rw [(hζ.pow_eq_one_iff_dvd t).2 ht]; simp
  · have hcop : Nat.Coprime t p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ht)
    exact (hζ.pow_of_coprime t hcop).geom_sum_eq_zero (Fact.out : p.Prime).one_lt

/-- Fourier inversion: `p G(x₀) = ∑_{m < p} Ĝ(ζ^m) ζ^{m x₀}`. -/
lemma fourier_inversion {ζ : L} (hζ : IsPrimitiveRoot ζ p) (G : ZMod p → L) (x₀ : ZMod p) :
    ∑ m ∈ range p, fourier G (ζ ^ m) * (ζ ^ m) ^ x₀.val = p * G x₀ := by
  simp only [fourier, sum_mul]
  rw [sum_comm]
  have hterm : ∀ x : ZMod p, ∑ m ∈ range p, G x * (ζ ^ m) ^ (-x).val * (ζ ^ m) ^ x₀.val =
      G x * if x = x₀ then (p : L) else 0 := by
    intro x
    simp only [mul_assoc, ← mul_sum]
    congr 1
    have : ∀ m, (ζ ^ m) ^ (-x).val * (ζ ^ m) ^ x₀.val = (ζ ^ ((-x).val + x₀.val)) ^ m := by
      intro m; rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm]
    simp only [this, sum_pow_primitive hζ]
    congr 1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      neg_add_eq_zero, eq_comm]
  rw [sum_congr rfl fun x _ => hterm x]
  simp [mul_comm]

/-- A function all of whose nontrivial Fourier coefficients vanish is constant. -/
lemma const_of_fourier_eq_zero {ζ : L} (hζ : IsPrimitiveRoot ζ p) (hp : (p : L) ≠ 0)
    (G : ZMod p → L) (hG : ∀ m ∈ range p, m ≠ 0 → fourier G (ζ ^ m) = 0) (a b : ZMod p) :
    G a = G b := by
  have h : ∀ x₀, (p : L) * G x₀ = fourier G 1 := by
    intro x₀
    rw [← fourier_inversion hζ G x₀, ← add_sum_erase _ _ (mem_range.2 (Fact.out : p.Prime).pos)]
    rw [sum_eq_zero fun m hm => by rw [hG m (mem_of_mem_erase hm) (ne_of_mem_erase hm), zero_mul]]
    simp
  exact mul_left_cancel₀ hp ((h a).trans (h b).symm)

end Fourier

/-- **Lemma 5.9.** Let `p ≠ q` be primes, and suppose the full rank statement holds for `ℓ` and
`M`. If `f₀, …, f_ℓ : 𝔽_p → 𝔽_q` satisfy `f₀(x) + ∑_{j=1}^ℓ f_j(x + y^j) = 0` for all `x` and all
`y ∈ {0, 2, …, M}`, then every `f_j` is constant. -/
theorem diff_char {p q ℓ M : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hfull : ∀ (L : Type) [Field L], ∀ lam : L, lam ^ p = 1 → lam ≠ 1 → ∀ c : Fin ℓ → L,
      (∀ y ∈ Icc 2 M, ∑ j, c j * (lam ^ (y ^ ((j : ℕ) + 1)) - 1) = 0) → c = 0)
    (f : Fin (ℓ + 1) → ZMod p → ZMod q)
    (hf : ∀ x : ZMod p, ∀ y ∈ stepSet M, ∑ j, f j (x + pw j (y : ZMod p)) = 0) :
    ∀ j a b, f j a = f j b := by
  -- the field `L = 𝔽_q(ζ)`
  have hpq' : ((p : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h).symm
  have : NeZero ((p : ℕ) : ZMod q) := ⟨hpq'⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let L := CyclotomicField p (ZMod q)
  set ζ : L := IsCyclotomicExtension.zeta p (ZMod q) L with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p (ZMod q) L
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap (ZMod q) L)]
    exact (map_ne_zero _).2 hpq'
  set F : Fin (ℓ + 1) → ZMod p → L := fun j x => algebraMap (ZMod q) L (f j x) with hF
  have hFeq : ∀ x : ZMod p, ∀ y ∈ stepSet M, ∑ j, F j (x + pw j (y : ZMod p)) = 0 := by
    intro x y hy
    simp only [hF, ← map_sum, hf x y hy, map_zero]
  -- the equation at `y = 0`
  have h0 : ∀ x, F 0 x = -∑ i : Fin ℓ, F i.succ x := by
    intro x
    have := hFeq x 0 (by simp [stepSet])
    rw [Fin.sum_univ_succ] at this
    simp only [Nat.cast_zero, pw_zero_right, add_zero] at this
    linear_combination this
  -- the Fourier coefficients of `F_1, …, F_ℓ` at `μ ≠ 1` form a kernel vector
  have hker : ∀ μ : L, μ ^ p = 1 → μ ≠ 1 → ∀ i : Fin ℓ, fourier (F i.succ) μ = 0 := by
    intro μ hμ hμ1
    have hvec := hfull L μ hμ hμ1 (fun i => fourier (F i.succ) μ) fun y hy => ?_
    · exact fun i => congrFun hvec i
    have hy' : y ∈ stepSet M := by simp [stepSet, hy]
    have hsum : ∀ x, ∑ i : Fin ℓ, (F i.succ (x + ((y ^ ((i : ℕ) + 1) : ℕ) : ZMod p)) -
        F i.succ x) = 0 := by
      intro x
      have h1 := hFeq x y hy'
      rw [Fin.sum_univ_succ] at h1
      simp only [Fin.val_zero, Fin.val_succ, pw, Nat.add_one_ne_zero, ↓reduceIte, add_zero]
        at h1
      rw [h0] at h1
      rw [sum_sub_distrib]
      push_cast
      linear_combination h1
    have hterm : ∀ j : Fin ℓ, fourier (F j.succ) μ * (μ ^ (y ^ ((j : ℕ) + 1)) - 1) =
        ∑ x, (F j.succ (x + ((y ^ ((j : ℕ) + 1) : ℕ) : ZMod p)) - F j.succ x) * μ ^ (-x).val := by
      intro j
      rw [sum_congr rfl fun x _ => sub_mul _ _ _, sum_sub_distrib, fourier_shift hμ,
        pow_natCast_val hμ]
      unfold fourier
      ring
    rw [sum_congr rfl fun j _ => hterm j, sum_comm]
    refine sum_eq_zero fun x _ => ?_
    rw [← sum_mul, hsum x, zero_mul]
  -- hence `F_1, …, F_ℓ` are constant
  have hconst : ∀ i : Fin ℓ, ∀ a b, f i.succ a = f i.succ b := by
    intro i a b
    have hc := const_of_fourier_eq_zero hζ hpL (F i.succ) (fun m hm hm0 => hker _
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
      (fun h1 => hm0 (by
        have := (hζ.pow_eq_one_iff_dvd m).1 h1
        exact Nat.eq_zero_of_dvd_of_lt this (mem_range.1 hm)))
      i) a b
    exact (algebraMap (ZMod q) L).injective hc
  intro j a b
  refine Fin.cases ?_ (fun i => hconst i a b) j
  apply (algebraMap (ZMod q) L).injective
  change F 0 a = F 0 b
  rw [h0, h0]
  congr 1
  exact sum_congr rfl fun i _ => by simp only [hF, hconst i a b]

end RestrictedPolynomials

end
