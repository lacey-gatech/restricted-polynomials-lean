module

public import RestrictedPolynomials.TrackB.MaxTSec6Support
public import RestrictedPolynomials.TrackB.MaxTSec6Terms
public import RestrictedPolynomials.TrackB.MaxTClass
public import RestrictedPolynomials.TrackB.MaxTOps
public import RestrictedPolynomials.TrackB.MaxTStatements
public import RestrictedPolynomials.TrackB.MaxTInduct
public import RestrictedPolynomials.TrackB.MergeGeneric
public import RestrictedPolynomials.TrackB.MergeGenericCores

/-!
# Track B: the relaxed base case, Thm 6.5′ and Thm 6.4′ on `𝒯`

Supplement E: `thm:6.5-prime`,
`thm:6.4-prime` (§6.6), the case `|Σ_modest| = 2` (§6.6, paper IV
`thm:nonembed-deg-must-be-small-rephrase-maximal2`, step `modest-two-case`), and paper IV
`writeup_stability.tex` Def. relaxed_base (l. 3411-3428, `def:relaxed-base`).

Readings:
* `RelaxedBaseCase` is the NORMALISED definition (the three
  functions have norm `1` in the `L²` of the marginals, conclusion `≤ 1 - c τ^C`); the unnormalised
  printed form is unsatisfiable.
* In `h67` the gain constants `(c, C)` are quantified before `(M, δ₀, η)`.
* The hypotheses of Thm 6.7′ and of the relaxed base case (paper IV `lem:nu-satisfies`, step `relaxed-base-case`) are binders.
* `hmerge` (the statement of `mgen_sStmtY_of_mergeX`), `h67` (Thm 6.7′) and `hrb`
  (paper IV `lem:nu-satisfies`, step `relaxed-base-case`) are hypotheses. The
  Thm 6.5′ assembly is named `maxT_thm_6_5_prime_of_hmerge_h67_hrb` (binder order).

Route: the case `|Σ_modest| = 2` builds `ν = nuOf S³`, checks the hypotheses of `h67` (the
diagonal copy of `μ` is the witness of 6b), then `m65_sameSupport_transfer` to the merge, `hmerge`
to `μ''` and Lemma 3.9 twice (`m65T_sStmtY_of_mu2`). Thm 6.5′ splits on `a v₁ = a v₂`
(`m65_ugly_case_of_hmerge`, whose richer pattern is a strict superset of `μ.support`, with constants
uniform over the finitely many supersets) and Thm 6.4′ applies Thm 6.5′ to the `x ↔ z` swap. All
proof helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Support
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]


/-! ### the relaxed base case (Def 6.6) and the two hypothesis inputs of Thm 6.5' -/

/-- paper IV `def:relaxed-base` (Def 6.6) at `H = {0}` (clause 1 vacuous), with `(c, C)` explicit. The
functions are NORMALISED in the `L²` of the three marginals (paper IV l. 3038 "2-norm equal to 1" and
l. 3762 "by normalizing"); without the normalisation the definition is false. The
expectation over `x, x' ∈ Sm` is uniform over pairs (with replacement); the correlation is the
one-site one. -/
def RelaxedBaseCase (ν : FinProb (X × Y × Z)) (Sm : Finset X) (c C : ℝ) : Prop :=
  2 ≤ Sm.card ∧ ∀ τ : ℝ, 0 < τ → ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ),
    ∑ x, (lawX ν).prob x * ‖f x‖ ^ 2 = 1 → ∑ y, (lawY ν).prob y * ‖g y‖ ^ 2 = 1 →
    ∑ z, (lawZ ν).prob z * ‖h z‖ ^ 2 = 1 →
    τ ≤ (∑ x ∈ Sm, ∑ x' ∈ Sm, ‖f x - f x'‖ ^ 2) / (Sm.card : ℝ) ^ 2 →
    ‖∑ p : X × Y × Z, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ≤ 1 - c * τ ^ C

/-! ### private helpers: monotonicity of `S_y`, uniform constants, lengths, the `x ↔ z` swap -/

private theorem rel65_bound_mono {c M M' δ η η' : ℝ} (hM : 0 ≤ M) (hMM : M ≤ M') (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hηη : η' ≤ η) (h : c ≤ M * δ ^ η) : c ≤ M' * δ ^ η' := by
  have h1 : δ ^ η ≤ δ ^ η' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηη
  have h2 : 0 ≤ δ ^ η' := (Real.rpow_pos_of_pos hδ η').le
  calc c ≤ M * δ ^ η := h
    _ ≤ M * δ ^ η' := mul_le_mul_of_nonneg_left h1 hM
    _ ≤ M' * δ ^ η' := mul_le_mul_of_nonneg_right hMM h2

omit [DecidableEq X] [DecidableEq Z] in
private theorem rel65_sStmtY_mono {μ : FinProb (X × Y × Z)} {M M' δ₀ δ₀' η η' : ℝ} (hM : 1 ≤ M)
    (hMM : M ≤ M') (hδ : δ₀' ≤ δ₀) (hδ1 : δ₀ ≤ 1) (hηη : η' ≤ η) (H : SStmtY μ M δ₀ η) :
    SStmtY μ M' δ₀' η' := by
  intro δ hδ0 hδ' n f g h hf hg hh hs
  exact rel65_bound_mono (by linarith) hMM hδ0 (by linarith) hηη
    (H δ hδ0 (by linarith) n f g h hf hg hh hs)

private theorem rel65_inv_bound {d B : ℝ} (hd : 0 < d) (h : 1 / d ≤ B) : 1 / max B 1 ≤ d := by
  have hpos : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [div_le_iff₀ hpos]
  have h1 : 1 / d ≤ max B 1 := h.trans (le_max_left _ _)
  have := (div_le_iff₀ hd).1 h1
  linarith

/-- `P`-maximality with constants that are uniform over the finitely many strict supersets of `S`
over the same alphabets (Remark `rmk:finite`). -/
private theorem rel65_uniform_supersets (S : Set (X × Y × Z)) (hP : PMaxSet S) {α : ℝ}
    (hα : 0 < α) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ D : FinProb (X × Y × Z), S ⊂ D.support →
      (∀ p ∈ D.support, α ≤ D.prob p) → SStmtY D M δ₀ η := by
  have hex : ∀ T : Set (X × Y × Z), ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      (S ⊂ T → ∀ D : FinProb (X × Y × Z), D.support = T → (∀ p ∈ D.support, α ≤ D.prob p) →
        SStmtY D M δ₀ η) := by
    intro T
    by_cases hT : S ⊂ T
    · obtain ⟨M, δ₀, η, h1, h2, h3, h4, H⟩ := (hP T hT).2.1 α hα
      exact ⟨M, δ₀, η, h1, h2, h3, h4, fun _ => H⟩
    · exact ⟨1, 1, 1, le_rfl, one_pos, le_rfl, one_pos, fun h => absurd h hT⟩
  choose Mf δf ηf hM hδ hδ1 hη hQ using hex
  obtain ⟨BM, hBM⟩ := Finite.bddAbove_range Mf
  obtain ⟨Bδ, hBδ⟩ := Finite.bddAbove_range (fun i => 1 / δf i)
  obtain ⟨Bη, hBη⟩ := Finite.bddAbove_range (fun i => 1 / ηf i)
  have hposδ : 0 < max Bδ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hposη : 0 < max Bη 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max BM 1, 1 / max Bδ 1, 1 / max Bη 1, le_max_right _ _, one_div_pos.2 hposδ,
    (div_le_one hposδ).2 (le_max_right _ _), one_div_pos.2 hposη, ?_⟩
  intro D hSD hat
  exact rel65_sStmtY_mono (hM D.support) (le_max_of_le_left (hBM (Set.mem_range_self D.support)))
    (rel65_inv_bound (hδ D.support) (hBδ (Set.mem_range_self D.support))) (hδ1 D.support)
    (rel65_inv_bound (hη D.support) (hBη (Set.mem_range_self D.support)))
    (hQ D.support hSD D rfl hat)

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
/-- the lengths `ℓ = 2^t - 1` of Lemma 3.9 above a threshold. -/
private theorem rel65_exists_len (L : ℕ) : ∃ ℓ : ℕ, Odd ℓ ∧ L ≤ ℓ ∧ ℓ = 2 ^ (L + 1) - 1 := by
  refine ⟨2 ^ (L + 1) - 1, ?_, ?_, rfl⟩
  · have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    refine ⟨2 ^ L - 1, ?_⟩
    rw [pow_succ]
    omega
  · have : L + 1 < 2 ^ (L + 1) := Nat.lt_two_pow_self
    omega

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem rel65_swapXZ_eq (S : Set (X × Y × Z)) :
    swapXZ S = swapXY (swapYZ (swapXY S)) := by
  ext ⟨z, y, x⟩
  simp only [swapXZ, swapXY, swapYZ, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨x', y', z', h, rfl, rfl, rfl⟩
    exact ⟨y', z', x', ⟨y', x', z', ⟨x', y', z', h, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  · rintro ⟨_, _, _, ⟨_, _, _, ⟨x', y', z', h, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    exact ⟨x', y', z', h, rfl, rfl, rfl⟩

/-- Supplement E `thm:6.5-prime`, case `|Σ_modest| = 2` (step `modest-two-case`): Thm 6.7' for `ν` (`h67`), the
relaxed base case of `ν` (`hrb`, paper IV `lem:nu-satisfies`, step `relaxed-base-case`) and the merge core
paper IV `lem:merge` (`hmerge`, the statement of `mgen_sStmtY_of_mergeX`); the built
ingredients are `from_mu_to_path_tensor`, `m65_sameSupport_transfer`, `inT_construction`, `nuOf_*`,
`cstab_pushforward`. -/
theorem m65_two_case_of_h67_hrb_hmerge
    (hmerge : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∀ {M δ₀ η : ℝ}, 1 ≤ M → 0 < δ₀ → δ₀ ≤ 1 → 0 < η →
      ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ a : X → X, MergeRep (mergeGraphX μ.support) a →
          SStmtY (mergeDistX μ a) M δ₀ η → SStmtY μ M' δ₀' η')
    (h67 : ∀ (m K : ℕ) (c C α : ℝ), 0 < α → 0 < c → 0 < C →
      ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) → InT ν.support →
        (∀ (y : Y) (z : Z), ∃ x, (x, y, z) ∈ ν.support) →
        (∀ (y : Y) (z : Z), ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ (Sg Sm : Finset X) (Phi' : Finset Z), Sm ⊆ Sg → RelaxedBaseCase ν Sm c C →
        (∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (a : U → X)
            (νt : FinProb (U × Y × ↥Phi')),
          Fintype.card U ≤ K ∧ (∀ u, a u ∈ Sg) ∧ (∀ x ∈ Sg, ∃ u, a u = x) ∧
          (∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support) ∧ PMaxSet νt.support ∧
          FullyMergedSet νt.support ∧ 2 ≤ Fintype.card Y ∧ InT νt.support) →
        (∀ x ∈ Sg, ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support) → mergeImpliesX ν.support →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          (cstab (lawY ν) (1 - δ) g).re ≤ δ → ‖corr3 ν f g h‖ ≤ M * δ ^ η)
    (hrb : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∀ {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂),
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
          RelaxedBaseCase ν {⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} c C)
    (m : ℕ) {α : ℝ} (hα : 0 < α) {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂)
    (ht₁ : ℓ₁ = 2 ^ t₁ - 1) (ht₂ : ℓ₂ = 2 ^ t₂ - 1) :
    ∃ αD : ℝ, 0 < αD ∧ ∀ MD δD ηD : ℝ, 1 ≤ MD → 0 < δD → δD ≤ 1 → 0 < ηD →
      ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        FullyMergedSet μ.support → 1 < Fintype.card X → PMaxSet μ.support →
        (∀ (x : X) (y : Y), ∃ w : m65Phi μ h₁, (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support) →
        (∀ (y : Y) (w : m65Phi μ h₁), ∃ v : m65Sig μ h₁ h₂,
          (v, y, w) ∈ (m65Mu2 μ h₁ h₂).support) →
        ∀ a : m65Sig μ h₁ h₂ → m65Sig μ h₁ h₂,
          MergeRep (mergeGraphX (m65Mu2 μ h₁ h₂).support) a →
        ∀ (x₁ x₂ : X), x₁ ≠ x₂ → ∀ v₁ v₂ : m65Sig μ h₁ h₂,
          (∀ j, v₁.1 j = x₁) → (∀ j, v₂.1 j = x₂) → a v₁ ≠ a v₂ →
        SStmtY μ M' δ₀' η' := by
  -- constants: alphabet bound `m_ν`, atom bound `α_ν` of `ν`, atom bound `α₂` of `μ''`
  set mν : ℕ := m ^ ℓ₁ + m ^ ℓ₂ + m
  set αν : ℝ := 1 / ((mν : ℝ) + 1) ^ 2 with hανdef
  set α₂ : ℝ := (α ^ (ℓ₁ + 1)) ^ (ℓ₂ + 1) with hα₂def
  have hαν : 0 < αν := by rw [hανdef]; positivity
  have hα₂ : 0 < α₂ := by rw [hα₂def]; positivity
  obtain ⟨c, C, hc, hC, Hrb⟩ := hrb m hα h₁ h₂ ht₁ ht₂
  obtain ⟨M, δ₀, η, hM, hδ₀, hδ₀1, hη, H67⟩ := h67 mν m c C αν hαν hc hC
  obtain ⟨κ, hκ, hκ1, Htr⟩ := m65_sameSupport_transfer m (lt_min hαν hα₂)
  have hδt0 : 0 < κ * δ₀ ^ 2 := by positivity
  have hδt1 : κ * δ₀ ^ 2 ≤ 1 := by
    have h1 : δ₀ ^ 2 ≤ 1 := pow_le_one₀ hδ₀.le hδ₀1
    calc κ * δ₀ ^ 2 ≤ 1 * 1 := mul_le_mul hκ1 h1 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨M₁, δ₁, η₁, hM₁, hδ₁, hδ₁1, hη₁, Hm⟩ := hmerge mν hα₂ (M := M + 1)
    (δ₀ := κ * δ₀ ^ 2) (η := min η 1 / 2) (by linarith) hδt0 hδt1 (by positivity)
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ => ⟨M₁, δ₁, η₁ / ((2 ^ t₁ * 2 ^ t₂ : ℕ) : ℝ), hM₁, hδ₁,
    hδ₁1, by positivity, ?_⟩⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat hfm hX1 hP hc₁ hc₂ a ha x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav
  -- Lemma 3.9 twice: from `μ'' = m65Mu2 μ h₁ h₂` back to `μ`
  refine m65T_sStmtY_of_mu2 μ h₁ h₂ ht₁ ht₂ hM₁ ?_
  obtain ⟨-, hS2, hS3, hS3X, hS3c, h31, h6c⟩ := inT_construction μ hT h₁ h₂ hc₁ hc₂ a ha
  have hat2 : ∀ q ∈ (m65Mu2 μ h₁ h₂).support, α₂ ≤ (m65Mu2 μ h₁ h₂).prob q :=
    m65T_mu2_atom_ge μ hα hat h₁ h₂
  have hat3 : ∀ q ∈ (mergeDistX (m65Mu2 μ h₁ h₂) a).support,
      α₂ ≤ (mergeDistX (m65Mu2 μ h₁ h₂) a).prob q :=
    mergeDistX_atom_bound _ a hat2
  have hcS : Fintype.card (m65Sig μ h₁ h₂) ≤ mν :=
    (card_pathX_le (pathTrickZ μ ℓ₁ h₁) h₂).trans ((Nat.pow_le_pow_left hX ℓ₂).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)))
  have hcP : Fintype.card (m65Phi μ h₁) ≤ mν :=
    (card_pathX_le (lawSwapXZ μ) h₁).trans ((Nat.pow_le_pow_left hZ ℓ₁).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hcY : Fintype.card Y ≤ mν := hY.trans (Nat.le_add_left _ _)
  have hcR : Fintype.card ↥(Set.range a) ≤ mν := (Fintype.card_range_le a).trans hcS
  -- the merge core: from `ν' = mergeDistX μ'' a` to `μ''`
  refine Hm (m65Sig μ h₁ h₂) Y (m65Phi μ h₁) hcS hcY hcP (m65Mu2 μ h₁ h₂) hS2 hat2 a ha ?_
  -- `ν = nuOf S³`: support `S³`, uniform `(y, w)`-marginal
  obtain ⟨hneR, hneY, hneP, -⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hS3.1
  set S3 := (mergeDistX (m65Mu2 μ h₁ h₂) a).support
  set ν := nuOf S3
  have hsupp : ν.support = S3 := nuOf_support (existsUnique_of_impliesX hS3X hS3c)
  have hcardpos : (0 : ℝ) < (Fintype.card Y : ℝ) * Fintype.card (m65Phi μ h₁) := by
    have : 0 < Fintype.card Y := Fintype.card_pos
    have : 0 < Fintype.card (m65Phi μ h₁) := Fintype.card_pos
    positivity
  have hcardle : (Fintype.card Y : ℝ) * Fintype.card (m65Phi μ h₁) ≤ ((mν : ℝ) + 1) ^ 2 := by
    have h1 : (Fintype.card Y : ℝ) ≤ mν + 1 := by
      have : (Fintype.card Y : ℝ) ≤ mν := by exact_mod_cast hcY
      linarith
    have h2 : (Fintype.card (m65Phi μ h₁) : ℝ) ≤ mν + 1 := by
      have : (Fintype.card (m65Phi μ h₁) : ℝ) ≤ mν := by exact_mod_cast hcP
      linarith
    rw [sq]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hatν : ∀ p ∈ ν.support, αν ≤ ν.prob p := fun p hp =>
    (one_div_le_one_div_of_le hcardpos hcardle).trans (nuOf_atom_ge S3 p hp)
  -- the same-support transfer from `ν` to `ν'`
  refine Htr M δ₀ η hM hδ₀ hδ₀1 hη (↥(Set.range a)) Y (m65Phi μ h₁) hY ν
    (mergeDistX (m65Mu2 μ h₁ h₂) a) hsupp hS3 (fun p hp => (min_le_right _ _).trans (hat3 p hp))
    (fun p hp => (min_le_left _ _).trans (hatν p hp)) ?_
  -- the diagonal words `(x, …, x)` and `(z, …, z)`
  have hdx : ∀ x : X, ∃ v : m65Sig μ h₁ h₂, ∀ j, v.1 j = x := by
    intro x
    obtain ⟨y, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_x hT.1 x
    obtain ⟨w, v, -, hv, -⟩ := h31 _ hp
    exact ⟨v, hv⟩
  have hdz : ∀ z : Z, ∃ w : m65Phi μ h₁, ∀ j, w.1 j = z := by
    intro z
    obtain ⟨x, y, hp⟩ := MaxT.PairwiseConnected3.exists_atom_z hT.1 z
    obtain ⟨w, v, hw, -⟩ := h31 _ hp
    exact ⟨w, hw⟩
  choose dx hdx using hdx
  choose dz hdz using hdz
  have hdxu : ∀ x (v : m65Sig μ h₁ h₂), (∀ j, v.1 j = x) → v = dx x := fun x v hv =>
    Subtype.ext (funext fun j => (hv j).trans (hdx x j).symm)
  have hdzu : ∀ z (w : m65Phi μ h₁), (∀ j, w.1 j = z) → w = dz z := fun z w hw =>
    Subtype.ext (funext fun j => (hw j).trans (hdz z j).symm)
  have hdzinj : Function.Injective dz := by
    intro z z' hzz
    have hpos : 0 < ℓ₁ := h₁.pos
    calc z = (dz z).1 ⟨0, hpos⟩ := (hdz z _).symm
      _ = (dz z').1 ⟨0, hpos⟩ := by rw [hzz]
      _ = z' := hdz z' _
  -- `Σ' = a(Σ'')`, `Σ_modest`, `Φ'`, and the diagonal copy `ν̃` of `μ` (the witness of 6b)
  set a' : X → ↥(Set.range a) := fun x => ⟨a (dx x), Set.mem_range_self _⟩
  set Sg : Finset ↥(Set.range a) := Finset.univ.image a'
  set Phi' : Finset (m65Phi μ h₁) := Finset.univ.image dz
  have hSmSg : ({⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} :
      Finset ↥(Set.range a)) ⊆ Sg := by
    obtain rfl := hdxu x₁ v₁ hv₁
    obtain rfl := hdxu x₂ v₂ hv₂
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact Finset.mem_image_of_mem a' (Finset.mem_univ x₁)
    · rw [Finset.mem_singleton.1 hs]
      exact Finset.mem_image_of_mem a' (Finset.mem_univ x₂)
  let eZ : Z ≃ ↥Phi' := Equiv.ofBijective
    (fun z => ⟨dz z, Finset.mem_image_of_mem dz (Finset.mem_univ z)⟩)
    ⟨fun z z' h => hdzinj (congrArg Subtype.val h), fun ⟨w, hw⟩ => by
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨z, rfl⟩⟩
  set νt : FinProb (X × Y × ↥Phi') := lawRelabel (Equiv.refl X) (Equiv.refl Y) eZ μ with hνtdef
  have hwit : ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (a : U → ↥(Set.range a))
      (νt : FinProb (U × Y × ↥Phi')),
      Fintype.card U ≤ m ∧ (∀ u, a u ∈ Sg) ∧ (∀ x ∈ Sg, ∃ u, a u = x) ∧
      (∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support) ∧ PMaxSet νt.support ∧
      FullyMergedSet νt.support ∧ 2 ≤ Fintype.card Y ∧ InT νt.support := by
    refine ⟨X, inferInstance, inferInstance, a', νt, hX,
      fun u => Finset.mem_image_of_mem a' (Finset.mem_univ u), fun x hx => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, rfl⟩
    · intro q hq
      rw [hνtdef, lawRelabel_support] at hq
      obtain ⟨⟨x, y, z⟩, hp, rfl⟩ := hq
      obtain ⟨w, v, hw, hv, -, -, hmem⟩ := h31 (x, y, z) hp
      obtain rfl := hdxu x v hv
      obtain rfl := hdzu z w hw
      rw [hsupp]
      exact hmem
    · rw [hνtdef, lawRelabel_support, pMaxSet_relabelSet_iff]
      exact hP
    · rw [hνtdef, lawRelabel_support, fullyMergedSet_relabelSet_iff]
      exact hfm
    · rcases inT_fullyMerged_dichotomy hT hfm with ⟨h1, -⟩ | ⟨-, h2, -⟩
      · omega
      · exact h2
    · rw [hνtdef, lawRelabel_support, inT_relabelSet_iff]
      exact hT
  have h6c' : ∀ x ∈ Sg, ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support := by
    intro x hx y
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨w, v, hv, hmem⟩ := h6c u y
    obtain rfl := hdxu u v hv
    exact ⟨w, by rw [hsupp]; exact hmem⟩
  have hRB := Hrb X Y Z hX hY hZ μ hT hat hfm hX1 hc₁ hc₂ a ha x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav ν hsupp
    (nuOf_marginal_yz S3)
  -- Thm 6.7′ for `ν` (`h67` at `(m_ν, K = m, c, C, α_ν)`)
  intro δ hδ hδle n f g h hf hg hh hs
  exact H67 δ hδ hδle (↥(Set.range a)) Y (m65Phi μ h₁) hcR hcY hcP ν hatν
    (by rw [hsupp]; exact hS3) (by rw [hsupp]; exact hS3c) (nuOf_marginal_yz S3) Sg _ Phi' hSmSg
    hRB hwit h6c' (by rw [hsupp]; exact hS3X) n f g h hf hg hh hs

/-- Supplement E `thm:6.5-prime` in EXACTLY the shape of `h64` of `maxT_induction_of_merge_h64`. -/
theorem maxT_thm_6_5_prime_of_hmerge_h67_hrb
    (hmerge : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∀ {M δ₀ η : ℝ}, 1 ≤ M → 0 < δ₀ → δ₀ ≤ 1 → 0 < η →
      ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ a : X → X, MergeRep (mergeGraphX μ.support) a →
          SStmtY (mergeDistX μ a) M δ₀ η → SStmtY μ M' δ₀' η')
    (h67 : ∀ (m K : ℕ) (c C α : ℝ), 0 < α → 0 < c → 0 < C →
      ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ ν : FinProb (X × Y × Z), (∀ p ∈ ν.support, α ≤ ν.prob p) → InT ν.support →
        (∀ (y : Y) (z : Z), ∃ x, (x, y, z) ∈ ν.support) →
        (∀ (y : Y) (z : Z), ∑ x, ν.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ (Sg Sm : Finset X) (Phi' : Finset Z), Sm ⊆ Sg → RelaxedBaseCase ν Sm c C →
        (∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (a : U → X)
            (νt : FinProb (U × Y × ↥Phi')),
          Fintype.card U ≤ K ∧ (∀ u, a u ∈ Sg) ∧ (∀ x ∈ Sg, ∃ u, a u = x) ∧
          (∀ q ∈ νt.support, (a q.1, q.2.1, q.2.2.1) ∈ ν.support) ∧ PMaxSet νt.support ∧
          FullyMergedSet νt.support ∧ 2 ≤ Fintype.card Y ∧ InT νt.support) →
        (∀ x ∈ Sg, ∀ y : Y, ∃ z, (x, y, z) ∈ ν.support) → mergeImpliesX ν.support →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          (cstab (lawY ν) (1 - δ) g).re ≤ δ → ‖corr3 ν f g h‖ ≤ M * δ ^ η)
    (hrb : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∀ {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂),
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
          RelaxedBaseCase ν {⟨a v₁, Set.mem_range_self _⟩, ⟨a v₂, Set.mem_range_self _⟩} c C) :
    ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → FullyMergedSet S → PMaxSet S →
        1 < Fintype.card X → QY S := by
  intro X Y Z _ _ _ _ _ _ S hS hm hP hX1 α hα
  set m : ℕ := Fintype.card X + Fintype.card Y + Fintype.card Z
  have hXm : Fintype.card X ≤ m := by omega
  have hYm : Fintype.card Y ≤ m := by omega
  have hZm : Fintype.card Z ≤ m := by omega
  -- the lengths `ℓ₁ = 2^{t₁} - 1`, `ℓ₂ = 2^{t₂} - 1` above the completeness thresholds
  obtain ⟨L₁, hL₁⟩ := pathTrickZ_sigmaGamma_complete m
  obtain ⟨ℓ₁, h₁, hℓ₁, ht₁⟩ := rel65_exists_len L₁
  obtain ⟨L₂, hL₂⟩ := pathTrick_gammaPhi_complete (m ^ ℓ₁ + m)
  obtain ⟨ℓ₂, h₂, hℓ₂, ht₂⟩ := rel65_exists_len L₂
  -- case `|Σ_modest| = 1`: the richer patterns are strict supersets of `S`
  obtain ⟨αD, hαD, Hugly⟩ := m65_ugly_case_of_hmerge hmerge m hα h₁ h₂ ht₁ ht₂
  obtain ⟨MD, δD, ηD, hMD, hδD, hδD1, hηD, HD⟩ := rel65_uniform_supersets S hP hαD
  obtain ⟨M₁, δ₁, η₁, hM₁, hδ₁, hδ₁1, hη₁, H₁⟩ := Hugly MD δD ηD hMD hδD hδD1 hηD
  -- case `|Σ_modest| = 2`
  obtain ⟨-, -, H2⟩ := m65_two_case_of_h67_hrb_hmerge hmerge h67 hrb m hα h₁ h₂ ht₁ ht₂
  obtain ⟨M₂, δ₂, η₂, hM₂, hδ₂, hδ₂1, hη₂, H₂⟩ := H2 1 1 1 le_rfl one_pos le_rfl one_pos
  refine ⟨max M₁ M₂, min δ₁ δ₂, min η₁ η₂, le_max_of_le_left hM₁, lt_min hδ₁ hδ₂,
    (min_le_left _ _).trans hδ₁1, lt_min hη₁ hη₂, fun μ hμ hat => ?_⟩
  subst hμ
  have hc₁ : ∀ (x : X) (y : Y), ∃ w : m65Phi μ h₁, (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support :=
    hL₁ X Y Z hXm hYm hZm μ hS.1 ℓ₁ h₁ hℓ₁
  have hc₂ : ∀ (y : Y) (w : m65Phi μ h₁), ∃ v : m65Sig μ h₁ h₂,
      (v, y, w) ∈ (m65Mu2 μ h₁ h₂).support :=
    hL₂ X Y (m65Phi μ h₁) (hXm.trans (Nat.le_add_left _ _)) (hYm.trans (Nat.le_add_left _ _))
      ((card_pathX_le (lawSwapXZ μ) h₁).trans ((Nat.pow_le_pow_left hZm ℓ₁).trans
        (Nat.le_add_right _ _))) (pathTrickZ μ ℓ₁ h₁) (inT_pathTrickZ hS h₁).1 ℓ₂ h₂ hℓ₂
  obtain ⟨a, ha⟩ := exists_mergeRep (mergeGraphX (m65Mu2 μ h₁ h₂).support)
  obtain ⟨x₁, x₂, hne⟩ := Fintype.exists_pair_of_one_lt_card hX1
  obtain ⟨-, -, -, -, -, h31, -⟩ := inT_construction μ hS h₁ h₂ hc₁ hc₂ a ha
  have hdx : ∀ x : X, ∃ v : m65Sig μ h₁ h₂, ∀ j, v.1 j = x := by
    intro x
    obtain ⟨y, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_x hS.1 x
    obtain ⟨w, v, -, hv, -⟩ := h31 _ hp
    exact ⟨v, hv⟩
  obtain ⟨v₁, hv₁⟩ := hdx x₁
  obtain ⟨v₂, hv₂⟩ := hdx x₂
  by_cases hav : a v₁ = a v₂
  · have HDs : ∀ D : FinProb (X × Y × Z),
        D.support = diagSupportSet a (mergeDistX (m65Mu2 μ h₁ h₂) a).support
          (fun x (v : m65Sig μ h₁ h₂) => ∀ j, v.1 j = x)
          (fun z (w : m65Phi μ h₁) => ∀ j, w.1 j = z) →
        (∀ p ∈ D.support, αD ≤ D.prob p) → SStmtY D MD δD ηD := by
      intro D hDs hDa
      refine HD D ?_ hDa
      rw [hDs]
      refine m65_D_ssubset a (mergeDistX (m65Mu2 μ h₁ h₂) a).support
        (fun x (v : m65Sig μ h₁ h₂) => ∀ j, v.1 j = x) (fun z (w : m65Phi μ h₁) => ∀ j, w.1 j = z)
        ?_ μ.support hS hm.1 ?_ x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav
      · intro x v v' hv hv'
        exact Subtype.ext (funext fun j => (hv j).trans (hv' j).symm)
      · intro p hp
        obtain ⟨w, v, hw, hv, -, -, hmem⟩ := h31 p hp
        exact ⟨v, w, hv, hw, hmem⟩
    exact rel65_sStmtY_mono hM₁ (le_max_left _ _) (min_le_left _ _) hδ₁1 (min_le_left _ _)
      (H₁ X Y Z hXm hYm hZm μ hS hat hm hX1 hc₁ hc₂ a ha x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav HDs)
  · exact rel65_sStmtY_mono hM₂ (le_max_right _ _) (min_le_right _ _) hδ₂1 (min_le_right _ _)
      (H₂ X Y Z hXm hYm hZm μ hS hat hm hX1 hP hc₁ hc₂ a ha x₁ x₂ hne v₁ v₂ hv₁ hv₂ hav)

end Support

/-- Supplement E `thm:6.4-prime`: same hypotheses, `|Σ| > 1` or `|Φ| > 1`; `h65` is Thm 6.5' (the previous
theorem) in the shape of `h64`; conclusion `Q_y`. -/
theorem maxT_thm_6_4_prime_of_h65
    (h65 : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → FullyMergedSet S → PMaxSet S →
        1 < Fintype.card X → QY S)
    (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (S : Set (X × Y × Z)) (hS : InT S) (hm : FullyMergedSet S) (hP : PMaxSet S)
    (hXZ : 1 < Fintype.card X ∨ 1 < Fintype.card Z) : QY S := by
  rcases hXZ with hX | hZ
  · exact h65 X Y Z S hS hm hP hX
  · have e := rel65_swapXZ_eq S
    have hQ := h65 Z Y X (swapXZ S) ((inT_swapXZ_iff S).2 hS)
      (by rw [e, fullyMergedSet_swapXY_iff, fullyMergedSet_swapYZ_iff, fullyMergedSet_swapXY_iff]
          exact hm)
      (by rw [e, pMaxSet_swapXY_iff, pMaxSet_swapYZ_iff, pMaxSet_swapXY_iff]; exact hP) hZ
    rw [e] at hQ
    exact (qY_iff_swapXY S).2 ((qX_iff_swapYZ _).2 ((qX_iff_swapXY _).2 hQ))

/-- the one-line discharge of `h64` of `maxT_induction_of_merge_h64`. -/
example
    (hmergeX : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → ∀ a : X → X, MergeRep (mergeGraphX S) a →
        ¬ Function.Injective a → QSet (mergeSetX S a) → QSet S)
    (hmergeY : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → ∀ b : Y → Y, MergeRep (mergeGraphY S) b →
        ¬ Function.Injective b → QSet (mergeSetY S b) → QSet S)
    (hmergeZ : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → ∀ c : Z → Z, MergeRep (mergeGraphZ S) c →
        ¬ Function.Injective c → QSet (mergeSetZ S c) → QSet S)
    (h65 : ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      [DecidableEq Z] (S : Set (X × Y × Z)), InT S → FullyMergedSet S → PMaxSet S →
        1 < Fintype.card X → QY S)
    (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (S : Set (X × Y × Z)) (hS : InT S) : QSet S :=
  maxT_induction_of_merge_h64 hmergeX hmergeY hmergeZ h65 X Y Z S hS

/-- compile-time check (not a target): the built merge core `mgen_sStmtY_of_mergeX` is
accepted as the hypothesis `hmerge`, so Thm 6.5′ is conditional on `h67` and `hrb` only. -/
example := fun h67 hrb => @maxT_thm_6_5_prime_of_hmerge_h67_hrb
  (fun m _ hα _ _ _ hM hδ0 hδ1 hη => mgen_sStmtY_of_mergeX m hα hM hδ0 hδ1 hη) h67 hrb

end MaxT
end TrackB
end RestrictedPolynomials
end
