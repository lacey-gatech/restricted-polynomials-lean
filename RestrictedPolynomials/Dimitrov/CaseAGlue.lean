module

public import RestrictedPolynomials.Dimitrov.Fekete
public import RestrictedPolynomials.Dimitrov.CaseAAlg
public import RestrictedPolynomials.Dimitrov.Continuation
public import RestrictedPolynomials.Dimitrov.Radical
public import RestrictedPolynomials.Dimitrov.Square
public import RestrictedPolynomials.Dimitrov.EvenSplit
public import RestrictedPolynomials.Dimitrov.Assembly

/-!
# Case A: the glue

Source: Supplement A, Theorem `thm:glue`.

Case A of Dimitrov's Theorem 1, conditional on the two analytic inputs: the rationality theorem for
hedgehogs (Supplement B) and Dubinin's bound (Supplement C). By contradiction: if all roots are
small, the hedgehog of the squared and fourth-powered roots has transfinite diameter `< 1`, the
series `√(P₂* P₄*)` is rational, hence `P₄ = P₂`, hence `P` is cyclotomic.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- [Supplement A, Theorem thm:glue] Case A of Dimitrov's Theorem 1, conditional on the rationality
theorem for hedgehogs (Supplement B, thm:CRI) and on Dubinin's bound (Supplement C, thm:main). -/
theorem caseA_of_rational_and_dubinin
    (hCRI : ∀ V : Multiset ℂ, V ≠ 0 → transfiniteDiameter (hedgehog V) < 1 →
      ∀ (a : ℕ → ℤ) (F : ℂ → ℂ) (ρ₀ : ℝ), 0 ≤ ρ₀ → DifferentiableOn ℂ F (hedgehog V)ᶜ →
        (∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => (a k : ℂ) * z⁻¹ ^ k) (F z)) →
        ∃ B : ℚ[X], B.coeff 0 = 1 ∧ ∃ A : ℚ[X],
          (B : PowerSeries ℚ) * PowerSeries.mk (fun k => (a k : ℚ)) = (A : PowerSeries ℚ))
    (hD : ∀ V : Multiset ℂ, V ≠ 0 → ∀ R : ℝ, (∀ v ∈ V, ‖v‖ ≤ R) →
      transfiniteDiameter (hedgehog V) ≤ R * (4 : ℝ) ^ (-(1 / (Multiset.card V : ℝ)))) :
    ∀ P : ℤ[X], P.Monic → Irreducible P → 1 < P.natDegree →
      (∀ n : ℕ, 0 < n → P ≠ cyclotomic n ℤ) → Irreducible (P2 P) →
      ∃ β : ℂ, aeval β P = 0 ∧ (2 : ℝ) ^ (1 / (4 * (P.natDegree : ℝ))) ≤ ‖β‖ := by
  intro P hmon hirr hdeg hcyc hirr2
  by_contra hcon
  push Not at hcon
  have hn : 0 < P.natDegree := by omega
  obtain ⟨-, -, α₁, hα₁, hα₁1⟩ := caseA_S0 P hmon hirr hdeg
  set A := (P.map (Int.castRingHom ℂ)).roots with hA
  have hcardA : Multiset.card A = P.natDegree := by
    rw [hA, ← natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int P]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hrootA : ∀ α ∈ A, aeval α P = 0 := by
    intro α hα
    have := (mem_roots ((hmon.map (Int.castRingHom ℂ)).ne_zero)).mp hα
    rw [IsRoot, eval_map] at this
    simpa [aeval_def, eval₂_eq_eval_map] using this
  have hne : A.toFinset.Nonempty := ⟨α₁, Multiset.mem_toFinset.mpr hα₁⟩
  obtain ⟨α₀, hα₀, hmax⟩ := A.toFinset.exists_max_image (fun α => ‖α‖) hne
  have hα₀A : α₀ ∈ A := Multiset.mem_toFinset.mp hα₀
  have hM1 : 1 ≤ ‖α₀‖ := hα₁1.trans (hmax α₁ (Multiset.mem_toFinset.mpr hα₁))
  have hM : ‖α₀‖ < (2 : ℝ) ^ (1 / (4 * (P.natDegree : ℝ))) := hcon α₀ (hrootA α₀ hα₀A)
  obtain ⟨hM24, hS9⟩ := caseA_S9 hn hM1 hM
  have hmaxA : ∀ α ∈ A, ‖α‖ ≤ ‖α₀‖ := fun α hα =>
    hmax α (Multiset.mem_toFinset.mpr hα)
  set V : Multiset ℂ := A.map (· ^ 2) + A.map (· ^ 4) with hV
  have hcardV : (Multiset.card V : ℝ) = 2 * (P.natDegree : ℝ) := by
    rw [hV, Multiset.card_add, Multiset.card_map, Multiset.card_map, hcardA]
    push_cast; ring
  have hV0 : V ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    rw [hV, Multiset.card_add, Multiset.card_map, Multiset.card_map, hcardA] at this
    simp at this
    omega
  have hVle : ∀ v ∈ V, ‖v‖ ≤ ‖α₀‖ ^ 4 := by
    intro v hv
    rw [hV, Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at hv
    rcases hv with ⟨α, hα, rfl⟩ | ⟨α, hα, rfl⟩
    · have h1 := hmaxA α hα
      have h0 : 0 ≤ ‖α‖ := norm_nonneg _
      rw [norm_pow]
      calc ‖α‖ ^ 2 ≤ ‖α₀‖ ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ ≤ ‖α₀‖ ^ 4 := hM24
    · rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hmaxA α hα) 4
  have hd : transfiniteDiameter (hedgehog V) < 1 := by
    refine lt_of_le_of_lt (hD V hV0 (‖α₀‖ ^ 4) hVle) ?_
    rw [hcardV]
    exact hS9
  have hrev0 : P.reverse.coeff 0 = 1 := by
    rw [coeff_zero_reverse]; exact hmon
  obtain ⟨f, hf0, hf⟩ := squarerad_graeffe P.reverse hrev0
  obtain ⟨hdiff, -, hsum⟩ := caseA_S5 P hmon hirr hdeg f hf0 hf
  obtain ⟨B, hB, Apol, hBA⟩ := hCRI V hV0 hd (fun k => PowerSeries.coeff k f) _ (‖α₀‖ ^ 4)
    (by positivity) hdiff (fun z hz => hsum z (fun v hv => lt_of_le_of_lt (hVle v hv) hz))
  have hmk : PowerSeries.mk (fun k => ((PowerSeries.coeff k f : ℤ) : ℚ)) =
      PowerSeries.map (Int.castRingHom ℚ) f := by
    ext k; simp
  rw [hmk] at hBA
  have h4 := caseA_S7 P hmon hirr hdeg hirr2 f hf0 hf B Apol hB hBA
  obtain ⟨N, hN, hPN⟩ := cyclotomic_of_P2_eq_P4 P hmon hirr hdeg h4.symm
  exact hcyc N hN hPN

/-- Dimitrov's theorem (the exact frozen statement), conditional on the two analytic inputs. -/
theorem dimitrov_of_rational_and_dubinin
    (hCRI : ∀ V : Multiset ℂ, V ≠ 0 → transfiniteDiameter (hedgehog V) < 1 →
      ∀ (a : ℕ → ℤ) (F : ℂ → ℂ) (ρ₀ : ℝ), 0 ≤ ρ₀ → DifferentiableOn ℂ F (hedgehog V)ᶜ →
        (∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => (a k : ℂ) * z⁻¹ ^ k) (F z)) →
        ∃ B : ℚ[X], B.coeff 0 = 1 ∧ ∃ A : ℚ[X],
          (B : PowerSeries ℚ) * PowerSeries.mk (fun k => (a k : ℚ)) = (A : PowerSeries ℚ))
    (hD : ∀ V : Multiset ℂ, V ≠ 0 → ∀ R : ℝ, (∀ v ∈ V, ‖v‖ ≤ R) →
      transfiniteDiameter (hedgehog V) ≤ R * (4 : ℝ) ^ (-(1 / (Multiset.card V : ℝ))))
    (Q : ℤ[X]) (hmon : Q.Monic) (hirr : Irreducible Q) (hdeg : 1 < Q.natDegree)
    (hcyc : ∀ n : ℕ, 0 < n → Q ≠ cyclotomic n ℤ) :
    ∃ β : ℂ, aeval β Q = 0 ∧ (2 : ℝ) ^ (1 / (4 * (Q.natDegree : ℝ))) ≤ ‖β‖ :=
  dimitrov_of_caseA (caseA_of_rational_and_dubinin hCRI hD) Q hmon hirr hdeg hcyc

end RestrictedPolynomials
