import RestrictedPolynomials.MinorIdeal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Polynomial.Roots

/-!
# Proposition 5.1 (full rank)

There are `M = M(ℓ)` and `P = P(ℓ)` such that for every prime `p > P`, every field `L`, and
every `λ ∈ L` of multiplicative order `p`, the matrix `A_{ℓ,M}(λ) = (λ^{y^j} - 1)_{2 ≤ y ≤ M,
1 ≤ j ≤ ℓ}` has trivial kernel.

As in the paper, `M` bounds the rows of finitely many generating minors, and `P` exceeds the
orders that can occur in the good characteristics (`q ∤ N`, Lemma 5.6) and in the exceptional
characteristics (`q ∣ N`, Lemma 5.8). In the exceptional case we bound the order through the
Frobenius orbit `λ, λ^q, λ^{q^2}, …` inside the roots of the monic minor with rows
`2, …, ℓ + 1`; this is the degree argument of Lemma 5.8 in elementary form.
-/

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

variable {ℓ : ℕ}

/-- In characteristic `q`, `f(x^q) = f(x)^q` for `f ∈ ℤ[z]`. -/
lemma aeval_pow_char {L : Type*} [Field L] {q : ℕ} [hq : Fact q.Prime] [CharP L q] (f : ℤ[X])
    (x : L) : aeval (x ^ q) f = aeval x f ^ q := by
  have : ExpChar L q := ExpChar.prime hq.out
  have h := Polynomial.hom_eval₂ f (Int.castRingHom L) (frobenius L q) x
  rw [RingHom.ext_int ((frobenius L q).comp (Int.castRingHom L)) (Int.castRingHom L)] at h
  simp only [aeval_def, algebraMap_int_eq, frobenius_def] at h ⊢
  exact h.symm

/-- **Proposition 5.1.** -/
theorem full_rank (ℓ : ℕ) :
    ∃ M P : ℕ, ℓ + 1 ≤ M ∧ ∀ (L : Type) [Field L] (p : ℕ), p.Prime → P < p →
      ∀ lam : L, lam ^ p = 1 → lam ≠ 1 → ∀ c : Fin ℓ → L,
        (∀ y ∈ Icc 2 M, ∑ j, c j * (lam ^ (y ^ ((j : ℕ) + 1)) - 1) = 0) → c = 0 := by
  classical
  obtain ⟨F, g, N, h, T, sel, V, L₀, e, hFA, hstd, hgm, hN, hgh, hsel, hbez, hL₀, hgF⟩ :=
    exists_minor_data ℓ
  set M := ℓ + 1 + ∑ a ∈ F, ∑ r, a r with hM
  set d := (minor ℓ (stdRows ℓ)).natDegree with hd
  set P := L₀ + N.natAbs ^ d with hP
  refine ⟨M, P, by omega, fun L _ p hp hPp lam hlamp hlam1 c hc => ?_⟩
  by_contra hc0
  -- every generating minor vanishes at `λ`
  have hrow : ∀ a ∈ F, ∀ r, a r ∈ Icc 2 M := by
    intro a ha r
    refine mem_Icc.2 ⟨(hFA a ha).2 r, ?_⟩
    have h1 : a r ≤ ∑ r, a r := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ r)
    have h2 : ∑ r, a r ≤ ∑ a ∈ F, ∑ r, a r :=
      single_le_sum (f := fun a : Fin ℓ → ℕ => ∑ r, a r) (fun _ _ => Nat.zero_le _) ha
    omega
  have hminor : ∀ a ∈ F, aeval lam (minor ℓ a) = 0 := by
    intro a ha
    rw [aeval_minor, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨c, hc0, funext fun r => ?_⟩
    simp only [Matrix.mulVec, dotProduct, evalMat, Matrix.of_apply, Pi.zero_apply]
    rw [← hc (a r) (hrow a ha r)]
    exact sum_congr rfl fun j _ => mul_comm _ _
  -- `λ` has order `p`
  have hord : ∀ m : ℕ, lam ^ m = 1 → p ∣ m := by
    have : Fact p.Prime := ⟨hp⟩
    intro m hm
    rw [← orderOf_eq_prime hlamp hlam1]
    exact orderOf_dvd_of_pow_eq_one hm
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hlamp
    exact zero_ne_one hlamp
  by_cases hNL : (N : L) ≠ 0
  · -- good characteristic: `D(λ) = 0`, so `λ^L = 1`
    have hg0 : aeval lam g = 0 := by
      by_contra hg0
      have hh : ∀ t ∈ T, aeval lam (h (sel t)) = 0 := by
        intro t ht
        have := hminor _ (hsel t ht)
        rw [hgh _ (hFA _ (hsel t ht)), map_mul] at this
        exact (mul_eq_zero.1 this).resolve_left hg0
      apply hNL
      have := congrArg (aeval lam) hbez
      rw [map_sum, aeval_C, algebraMap_int_eq, eq_intCast] at this
      rw [← this]
      exact sum_eq_zero fun t ht => by rw [map_mul, hh t ht, mul_zero]
    obtain ⟨q', hq'⟩ := hgF
    have hF0 : aeval lam ((X * (X ^ L₀ - 1)) ^ e : ℤ[X]) = 0 := by
      rw [hq', map_mul, hg0, zero_mul]
    have he : e ≠ 0 := by
      rintro rfl
      simp at hF0
    rw [map_pow, pow_eq_zero_iff he] at hF0
    simp only [map_mul, aeval_X, map_sub, map_pow, map_one, mul_eq_zero, hlam0, false_or,
      sub_eq_zero] at hF0
    have := Nat.le_of_dvd hL₀ (hord L₀ hF0)
    omega
  · -- exceptional characteristic `q ∣ N`: the Frobenius orbit of `λ`
    push Not at hNL
    set q := ringChar L with hqdef
    have : CharP L q := ringChar.charP L
    have hqN : (q : ℤ) ∣ N := (CharP.intCast_eq_zero_iff L q N).1 hNL
    have hq0 : q ≠ 0 := by
      rintro h0
      rw [h0, Nat.cast_zero, zero_dvd_iff] at hqN
      exact hN hqN
    have hqp : q.Prime := CharP.char_prime_of_ne_zero L hq0
    have : Fact q.Prime := ⟨hqp⟩
    have hqle : q ≤ N.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hN)
      (Int.natCast_dvd.1 hqN)
    -- the monic minor with rows `2, …, ℓ + 1`, over `L`
    set f : L[X] := (minor ℓ (stdRows ℓ)).map (Int.castRingHom L) with hf
    have hfm : f.Monic := minor_stdRows_monic.map _
    have hfd : f.natDegree = d := minor_stdRows_monic.natDegree_map _
    have hroot : ∀ i : ℕ, lam ^ (q ^ i) ∈ f.roots.toFinset := by
      intro i
      rw [Multiset.mem_toFinset, mem_roots hfm.ne_zero, IsRoot, hf, eval_map,
        ← algebraMap_int_eq, ← aeval_def]
      induction i with
      | zero => simpa using hminor _ hstd
      | succ i ih => rw [pow_succ, pow_mul, aeval_pow_char, ih, zero_pow hqp.ne_zero]
    have hcard : f.roots.toFinset.card < (range (d + 1)).card := by
      rw [card_range]
      have := (Multiset.toFinset_card_le f.roots).trans (card_roots' f)
      omega
    obtain ⟨i, hi, j, hj, hij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun i => lam ^ (q ^ i)) fun i _ => hroot i
    simp only [mem_range] at hi hj
    -- `λ^{q^i (q^{j-i} - 1)} = 1` for some `i < j ≤ d`
    have key : ∀ i j : ℕ, i < j → j ≤ d → lam ^ (q ^ i) = lam ^ (q ^ j) → False := by
      intro i j hij hjd heq
      set μ := lam ^ (q ^ i)
      have hμ0 : μ ≠ 0 := pow_ne_zero _ hlam0
      have hqj : q ^ j = q ^ i * q ^ (j - i) := by rw [← pow_add]; congr 1; omega
      have hpos : 1 ≤ q ^ (j - i) := Nat.one_le_pow _ _ hqp.pos
      have h1 : μ ^ (q ^ (j - i) - 1) = 1 := by
        have h2 : μ * μ ^ (q ^ (j - i) - 1) = μ * 1 := by
          rw [mul_one, ← pow_succ', Nat.sub_add_cancel hpos, ← pow_mul, ← hqj, ← heq]
        exact mul_left_cancel₀ hμ0 h2
      rw [← pow_mul] at h1
      rcases (Nat.Prime.dvd_mul hp).1 (hord _ h1) with h3 | h3
      · have := Nat.le_of_dvd hqp.pos (hp.dvd_of_dvd_pow h3)
        have : N.natAbs ≤ N.natAbs ^ d := by
          rcases Nat.eq_zero_or_pos d with hd0 | hd0
          · have : 0 < j := by omega
            omega
          · exact Nat.le_self_pow (by omega) _
        omega
      · have hq2 : 2 ≤ q ^ (j - i) := by
          calc 2 ≤ q := hqp.two_le
            _ = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ (j - i) := Nat.pow_le_pow_right hqp.pos (by omega)
        have := Nat.le_of_dvd (by omega) h3
        have : q ^ (j - i) ≤ N.natAbs ^ d :=
          (Nat.pow_le_pow_left hqle _).trans (Nat.pow_le_pow_right (by omega) (by omega))
        omega
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h (by omega) heq
    · exact key j i h (by omega) heq.symm

end RestrictedPolynomials

end
