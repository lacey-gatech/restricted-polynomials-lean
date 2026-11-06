module

public import RestrictedPolynomials.TrackB.L6RelaxedBase
public import RestrictedPolynomials.TrackB.L6NuProperties
public import RestrictedPolynomials.TrackB.MaxTSec6Relaxed65

@[expose] public section



open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section L6Hrb

/-- paper IV `lem:nu-satisfies`, step `relaxed-base-case`, in EXACTLY the shape of the hypothesis `hrb` of
`m65_two_case_of_h67_hrb_hmerge` and `maxT_thm_6_5_prime_of_hmerge_h67_hrb`. -/
theorem l6_hrb : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∀ {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂),
      ℓ₁ = 2 ^ t₁ - 1 → ℓ₂ = 2 ^ t₂ - 1 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        FullyMergedSet μ.support → 1 < Fintype.card X →
        (∀ (x : X) (y : Y), ∃ w : m65Phi μ h₁, (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support) →
        (∀ (y : Y) (w : m65Phi μ h₁), ∃ v : m65Sig μ h₁ h₂,
          (v, y, w) ∈ (m65Mu2 μ h₁ h₂).support) →
        ∀ a : m65Sig μ h₁ h₂ → m65Sig μ h₁ h₂,
          MergeRep (mergeGraphX (m65Mu2 μ h₁ h₂).support) a →
        ∀ (x₁ x₂ : X), x₁ ≠ x₂ → ∀ v₁ v₂ : m65Sig μ h₁ h₂,
          (∀ j, v₁.1 j = x₁) → (∀ j, v₂.1 j = x₂) → a v₁ ≠ a v₂ →
        ∀ ν : FinProb (↥(Set.range a) × Y × m65Phi μ h₁),
          ν.support = (mergeDistX (m65Mu2 μ h₁ h₂) a).support →
          (∀ (y : Y) (w : m65Phi μ h₁),
            ∑ x, ν.prob (x, y, w) = 1 / ((Fintype.card Y : ℝ) * Fintype.card (m65Phi μ h₁))) →
          RelaxedBaseCase ν {⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} c C := by
  intro m α hα t₁ t₂ ℓ₁ ℓ₂ h₁ h₂ ht₁ ht₂
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro X Y Z _ _ _ _ _ _ hX _ _ μ
    exfalso
    have hX0 : Fintype.card X = 0 := by omega
    have hempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hX0
    have h1 := μ.sum_eq_one
    have : (∑ p : X × Y × Z, μ.prob p) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      exact (hempty.false p.1).elim
    linarith
  · have hℓ : 1 ≤ ℓ₁ + ℓ₂ := by
      obtain ⟨k, hk⟩ := h₁
      omega
    have hmν : 1 ≤ m ^ (ℓ₁ + ℓ₂) := Nat.one_le_pow _ _ hm
    have hmνR : (1 : ℝ) ≤ ((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) := by exact_mod_cast hmν
    have hαν : 0 < 1 / (((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) ^ 2) := by positivity
    obtain ⟨c, hc, hcore⟩ := l6_relaxed_base_case_core (m ^ (ℓ₁ + ℓ₂)) hmν hαν
    refine ⟨c, ((50 * m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ), hc, by positivity, ?_⟩
    intro X Y Z _ _ _ _ _ _ hX hY hZ μ hμ hat hfm hX1 hc₁ hc₂ a ha x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav ν hsupp hyz
    obtain ⟨hdp1, hdp2, hdp3, hdp4, hdpc, hdim⟩ :=
      l6_nu_direct_properties m hm hX hY hZ μ hμ h₁ h₂ hc₁ hc₂ a ha ν hsupp hyz
    have hT : InT ν.support := by
      rw [hsupp]; exact (inT_construction μ hμ h₁ h₂ hc₁ hc₂ a ha).2.2.1
    have h6c := l6_sigma_gamma_in_support μ hμ h₁ h₂ hc₁ hc₂ a ha ν hsupp
    have hne' : (⟨a v₁, Set.mem_range_self _⟩ : ↥(Set.range a)) ≠ ⟨a v₂, Set.mem_range_self _⟩ := by
      intro h; exact hav (congrArg Subtype.val h)
    have hcard : 2 ≤ ({⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} :
        Finset ↥(Set.range a)).card := by
      rw [Finset.card_pair hne']
    have h6 : ∀ x ∈ ({⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} :
        Finset ↥(Set.range a)), ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support := by
      intro x hx y
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h6c x₁ v₁ hv₁ y
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact h6c x₂ v₂ hv₂ y
    exact ⟨hcard, fun τ hτ f g h hf hg hh hv =>
      hcore _ _ _ hdp2 hdp3 hdp4 ν hdp1 hT hyz _ hcard h6 τ hτ f g h hf hg hh hv⟩


/-- paper IV `lem:nu-satisfies` (Lemma 6.9) for the constructed `ν`, without hypothesis 6b (its witness
`ν̃` is the diagonal copy of `μ`): the relaxed base case with `C = 50 m_ν`, and
hypotheses 1, 2, 3, 4, 5, 6c, 7 of Thm 6.7' at `m_ν = m^(ℓ₁+ℓ₂)`, `α_ν = 1/m_ν²`. -/
theorem l6_nu_satisfies (m : ℕ) (hm : 1 ≤ m) {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂)
    (ht₁ : ℓ₁ = 2 ^ t₁ - 1) (ht₂ : ℓ₂ = 2 ^ t₂ - 1) {α : ℝ} (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        FullyMergedSet μ.support → 1 < Fintype.card X →
        (∀ (x : X) (y : Y), ∃ w : m65Phi μ h₁, (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support) →
        (∀ (y : Y) (w : m65Phi μ h₁), ∃ v : m65Sig μ h₁ h₂,
          (v, y, w) ∈ (m65Mu2 μ h₁ h₂).support) →
        ∀ a : m65Sig μ h₁ h₂ → m65Sig μ h₁ h₂,
          MergeRep (mergeGraphX (m65Mu2 μ h₁ h₂).support) a →
        ∀ (x₁ x₂ : X), x₁ ≠ x₂ → ∀ v₁ v₂ : m65Sig μ h₁ h₂,
          (∀ j, v₁.1 j = x₁) → (∀ j, v₂.1 j = x₂) → a v₁ ≠ a v₂ →
        ∀ ν : FinProb (↥(Set.range a) × Y × m65Phi μ h₁),
          ν.support = (mergeDistX (m65Mu2 μ h₁ h₂) a).support →
          (∀ (y : Y) (w : m65Phi μ h₁),
            ∑ x, ν.prob (x, y, w) = 1 / ((Fintype.card Y : ℝ) * Fintype.card (m65Phi μ h₁))) →
          RelaxedBaseCase ν {⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} c C ∧
          C = ((50 * m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) ∧
          (∀ p ∈ ν.support, 1 / (((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) ^ 2) ≤ ν.prob p) ∧
          Fintype.card ↥(Set.range a) ≤ m ^ (ℓ₁ + ℓ₂) ∧ Fintype.card Y ≤ m ^ (ℓ₁ + ℓ₂) ∧
          Fintype.card (m65Phi μ h₁) ≤ m ^ (ℓ₁ + ℓ₂) ∧
          InT ν.support ∧ (∀ (y : Y) (w : m65Phi μ h₁), ∃ x, (x, y, w) ∈ ν.support) ∧
          (∀ (x : X) (v : m65Sig μ h₁ h₂), (∀ j, v.1 j = x) → ∀ y : Y,
            ∃ w : m65Phi μ h₁, (⟨a v, Set.mem_range_self v⟩, y, w) ∈ ν.support) ∧
          mergeImpliesX ν.support := by
  have hℓ : 1 ≤ ℓ₁ + ℓ₂ := by
    obtain ⟨k, hk⟩ := h₁
    omega
  have hmν : 1 ≤ m ^ (ℓ₁ + ℓ₂) := Nat.one_le_pow _ _ hm
  have hmνR : (1 : ℝ) ≤ ((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) := by exact_mod_cast hmν
  have hαν : 0 < 1 / (((m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ) ^ 2) := by positivity
  obtain ⟨c, hc, hcore⟩ := l6_relaxed_base_case_core (m ^ (ℓ₁ + ℓ₂)) hmν hαν
  refine ⟨c, ((50 * m ^ (ℓ₁ + ℓ₂) : ℕ) : ℝ), hc, by positivity, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hμ hat hfm hX1 hc₁ hc₂ a ha x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav ν hsupp hyz
  obtain ⟨hdp1, hdp2, hdp3, hdp4, hdpc, hdim⟩ :=
    l6_nu_direct_properties m hm hX hY hZ μ hμ h₁ h₂ hc₁ hc₂ a ha ν hsupp hyz
  have hT : InT ν.support := by
    rw [hsupp]; exact (inT_construction μ hμ h₁ h₂ hc₁ hc₂ a ha).2.2.1
  have h6c := l6_sigma_gamma_in_support μ hμ h₁ h₂ hc₁ hc₂ a ha ν hsupp
  have hne' : (⟨a v₁, Set.mem_range_self _⟩ : ↥(Set.range a)) ≠ ⟨a v₂, Set.mem_range_self _⟩ := by
    intro h; exact hav (congrArg Subtype.val h)
  have hcard : 2 ≤ ({⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} :
      Finset ↥(Set.range a)).card := by
    rw [Finset.card_pair hne']
  have h6 : ∀ x ∈ ({⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} :
      Finset ↥(Set.range a)), ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support := by
    intro x hx y
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h6c x₁ v₁ hv₁ y
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact h6c x₂ v₂ hv₂ y
  refine ⟨⟨hcard, fun τ hτ f g h hf hg hh hv =>
    hcore _ _ _ hdp2 hdp3 hdp4 ν hdp1 hT hyz _ hcard h6 τ hτ f g h hf hg hh hv⟩, rfl, hdp1, hdp2, hdp3, hdp4, hT, ?_, h6c, hdim⟩
  intro y w
  have := (inT_construction μ hμ h₁ h₂ hc₁ hc₂ a ha).2.2.2.2.1 y w
  rw [← hsupp] at this
  exact this


/-- compile-time check (fully proved): `l6_hrb` is accepted as the argument `hrb` of the
theorems above. -/
example := fun hmerge h67 => m65_two_case_of_h67_hrb_hmerge hmerge h67 l6_hrb

example := fun hmerge h67 => maxT_thm_6_5_prime_of_hmerge_h67_hrb hmerge h67 l6_hrb


end L6Hrb

end MaxT
end TrackB
end RestrictedPolynomials
end
