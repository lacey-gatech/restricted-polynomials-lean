module

public import RestrictedPolynomials.DetEstimate
public import RestrictedPolynomials.Frozen.Dimitrov
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Lemma 5.12

* `root_of_unity_of_gcd` : **Lemma 5.12**. For `M` large, every nonzero complex root of a monic
  common divisor `D ∈ ℤ[z]` of the minors of `A_{ℓ,M}` is a root of unity. (Lemma 5.10 bounds
  all conjugates, and Dimitrov's theorem (`dimitrov`, in `Frozen/Dimitrov.lean`) excludes
  non-cyclotomic minimal polynomials.)
* Lemma 5.13 (`prime_order_le`) is in `CyclotomicOrder.lean`.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

variable {ℓ : ℕ}

lemma one_le_dℓ_ru (hℓ : 1 ≤ ℓ) : 1 ≤ dℓ ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  unfold dℓ
  rw [Finset.sum_range_succ']
  have : 0 < 2 ^ (0 + 1) := by positivity
  omega

lemma root_norm_bound {M : ℕ} (hℓ : 1 ≤ ℓ) (hM : ℓ + 1 ≤ M)
    (hbig : (2 ^ ℓ * ℓ.factorial) ^ (4 * dℓ ℓ) < 2 ^ (M - ℓ))
    {D : ℤ[X]} (hD : ∀ a ∈ rowsFin ℓ M, D ∣ minor ℓ a) {γ : ℂ} (hγ : aeval γ D = 0) :
    ‖γ‖ ^ (4 * dℓ ℓ) < 2 := by
  have hmem : (fun r : Fin ℓ => M - ℓ + 1 + (r : ℕ)) ∈ rowsFin ℓ M := by
    rw [mem_rowsFin]
    refine ⟨fun x y hxy => ?_, fun r => ⟨?_, ?_⟩⟩
    · show M - ℓ + 1 + (x : ℕ) < M - ℓ + 1 + (y : ℕ)
      have : (x : ℕ) < y := hxy
      omega
    · omega
    · have := r.2; show M - ℓ + 1 + (r : ℕ) ≤ M; omega
  have hmin : aeval γ (minor ℓ fun r : Fin ℓ => M - ℓ + 1 + (r : ℕ)) = 0 := by
    obtain ⟨q, hq⟩ := hD _ hmem
    rw [hq, map_mul, hγ, zero_mul]
  have h1 := det_estimate hℓ hM γ hmin
  have h2 : (‖γ‖ ^ (4 * dℓ ℓ)) ^ (M - ℓ) < 2 ^ (M - ℓ) := by
    calc (‖γ‖ ^ (4 * dℓ ℓ)) ^ (M - ℓ) = (‖γ‖ ^ (M - ℓ)) ^ (4 * dℓ ℓ) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ ℓ * (ℓ.factorial : ℝ)) ^ (4 * dℓ ℓ) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ < 2 ^ (M - ℓ) := by exact_mod_cast hbig
  exact lt_of_pow_lt_pow_left₀ _ (by norm_num) h2

/-- **Lemma 5.12.** -/
theorem root_of_unity_of_gcd {M : ℕ} (hℓ : 1 ≤ ℓ) (hM : ℓ + 1 ≤ M)
    (hbig : (2 ^ ℓ * ℓ.factorial) ^ (4 * dℓ ℓ) < 2 ^ (M - ℓ))
    {D : ℤ[X]} (hDm : D.Monic) (hDdeg : D.natDegree ≤ dℓ ℓ)
    (hD : ∀ a ∈ rowsFin ℓ M, D ∣ minor ℓ a) {β : ℂ} (hβ : β ≠ 0) (hDβ : aeval β D = 0) :
    ∃ n : ℕ, 0 < n ∧ β ^ n = 1 := by
  have hbound : ∀ γ : ℂ, aeval γ D = 0 → ‖γ‖ ^ (4 * dℓ ℓ) < 2 :=
    fun γ hγ => root_norm_bound hℓ hM hbig hD hγ
  have hint : IsIntegral ℤ β := ⟨D, hDm, by simpa [aeval_def] using hDβ⟩
  set m := minpoly ℤ β with hm
  have hmD : m ∣ D := minpoly.isIntegrallyClosed_dvd hint hDβ
  have hmroot : ∀ γ : ℂ, aeval γ m = 0 → aeval γ D = 0 := by
    intro γ hγ
    obtain ⟨q, hq⟩ := hmD
    rw [hq, map_mul, hγ, zero_mul]
  have hmmon : m.Monic := minpoly.monic hint
  have hmirr : Irreducible m := minpoly.irreducible hint
  have hmβ : aeval β m = 0 := minpoly.aeval ℤ β
  have hdegle : m.natDegree ≤ dℓ ℓ :=
    (Polynomial.natDegree_le_of_dvd hmD hDm.ne_zero).trans hDdeg
  have hd1 := one_le_dℓ_ru hℓ
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  rcases Nat.lt_or_ge 1 m.natDegree with hgt | hle
  · -- degree > 1
    by_cases hcyc : ∃ n : ℕ, 0 < n ∧ m = cyclotomic n ℤ
    · obtain ⟨n, hn, hmn⟩ := hcyc
      refine ⟨n, hn, ?_⟩
      have hdvd : cyclotomic n ℤ ∣ (X ^ n - 1 : ℤ[X]) := cyclotomic.dvd_X_pow_sub_one n ℤ
      obtain ⟨q, hq⟩ := hdvd
      have := congrArg (aeval β) hq
      rw [map_mul, ← hmn, hmβ, zero_mul] at this
      simpa [sub_eq_zero] using this
    · exfalso
      push Not at hcyc
      obtain ⟨γ, hγ, hγn⟩ := dimitrov m hmmon hmirr hgt hcyc
      have hb := hbound γ (hmroot γ hγ)
      have hmpos : (0 : ℝ) < m.natDegree := by exact_mod_cast hpos
      have hle : (m.natDegree : ℝ) ≤ dℓ ℓ := by exact_mod_cast hdegle
      have h2 : (2 : ℝ) ≤ ((2 : ℝ) ^ (1 / (4 * (m.natDegree : ℝ)))) ^ (4 * dℓ ℓ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        have : (1 : ℝ) ≤ 1 / (4 * (m.natDegree : ℝ)) * ((4 * dℓ ℓ : ℕ) : ℝ) := by
          push_cast
          rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
          nlinarith
        calc (2 : ℝ) = 2 ^ (1 : ℝ) := by norm_num
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      have := pow_le_pow_left₀ (by positivity) hγn (4 * dℓ ℓ)
      linarith
  · -- degree 1
    have hdeg1 : m.natDegree = 1 := le_antisymm hle hpos
    have hform := hmmon.eq_X_add_C hdeg1
    have hβc : β = -((m.coeff 0 : ℤ) : ℂ) := by
      have := hmβ
      rw [hform] at this
      simp at this
      linear_combination this
    set k : ℤ := -(m.coeff 0) with hk
    have hβk : β = (k : ℂ) := by rw [hβc, hk]; push_cast; ring
    have hk0 : k ≠ 0 := by
      intro h; apply hβ; rw [hβk, h]; simp
    have hb := hbound β hDβ
    have hnorm : ‖β‖ = |(k : ℝ)| := by rw [hβk]; simp
    have h1 : (1 : ℝ) ≤ ‖β‖ := by
      rw [hnorm]
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      have : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast this
      exact this
    have h2 : ‖β‖ ≤ ‖β‖ ^ (4 * dℓ ℓ) := le_self_pow₀ h1 (by omega)
    have h3 : |k| < 2 := by
      have : |(k : ℝ)| < 2 := by rw [← hnorm]; linarith
      exact_mod_cast this
    have : k = 1 ∨ k = -1 := by
      rcases abs_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    refine ⟨2, by norm_num, ?_⟩
    rw [hβk]
    rcases this with h | h <;> simp [h]

end RestrictedPolynomials

end
