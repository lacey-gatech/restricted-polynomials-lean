module

public import RestrictedPolynomials.TrackB.S9DeltaRelaxed

/-!
# Track B: Lemma 9.3 (`delta_inductive`)

Source: paper IV (arXiv:2307.16248v2 `writeup_stability.tex`), Lemma 9.3 and its proof
(l. 5263-5934). The core step for one admissible parameter tuple (`s9d_core_step`), the per-triple
bound with the constant `C'` of `s9d_parameter_hierarchy` (`s9d_triple_bound`), and the lemma itself
(`s9d_delta_inductive`).
-/

@[expose] public section

open Finset
open scoped ENNReal

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

/-! ### private helpers -/

section S9dInductiveHelpers

/-- the mass of the coefficients `≥ τ` is at least `1 - mη²` when the others are `< η`. -/
private lemma s9dI_mass_ge {s : ℕ} (c : Fin s → ℝ) {τ η ζ : ℝ} {m : ℕ} (hs : s ≤ m)
    (h0 : ∀ i, 0 ≤ c i) (h1 : ∑ i, c i ^ 2 = 1) (hsep : ∀ i, c i < η ∨ τ ≤ c i)
    (hd : (m : ℝ) * η ^ 2 ≤ ζ) : 1 - ζ ≤ s9dMass c τ := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin s))
    (fun i => τ ≤ c i) (fun i => c i ^ 2)
  have hbig : s9dMass c τ = ∑ i ∈ univ.filter (fun i => τ ≤ c i), c i ^ 2 := rfl
  have hrest : ∑ i ∈ univ.filter (fun i => ¬ τ ≤ c i), c i ^ 2 ≤ (m : ℝ) * η ^ 2 := by
    calc ∑ i ∈ univ.filter (fun i => ¬ τ ≤ c i), c i ^ 2
        ≤ ∑ i ∈ univ.filter (fun i => ¬ τ ≤ c i), η ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := (Finset.mem_filter.1 hi).2
          have hlt : c i < η := (hsep i).resolve_right hi'
          exact pow_le_pow_left₀ (h0 i) hlt.le 2
      _ = ((univ.filter (fun i => ¬ τ ≤ c i)).card : ℝ) * η ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * η ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have : (univ.filter (fun i => ¬ τ ≤ c i)).card ≤ m :=
            (Finset.card_filter_le _ _).trans (by simpa using hs)
          exact_mod_cast this
  rw [hbig]
  linarith

private lemma s9dI_mass_le_one {s : ℕ} (c : Fin s → ℝ) (τ : ℝ) (h1 : ∑ i, c i ^ 2 = 1) :
    s9dMass c τ ≤ 1 := by
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => sq_nonneg _

private lemma s9dI_sum_sub {k : ℕ} {β : Type*} [AddCommMonoid β] (B : Finset (Fin k))
    (G : Fin k → β) (hG : ∀ r, r ∉ B → G r = 0) : ∑ r, G r = ∑ r : B, G r := by
  rw [Finset.sum_coe_sort B G]
  exact (Finset.sum_subset (Finset.subset_univ B) (fun r _ hr => hG r hr)).symm

private lemma s9dI_kk {a b : ℝ} (h0 : 0 ≤ a) (h : a ≤ b) : a * (a + 1) ≤ b * (b + 1) :=
  mul_le_mul h (by linarith) (by linarith) (by linarith)

private lemma s9dI_sqrt_le {ζ : ℝ} (hg : 9 * ζ ≤ 1) : Real.sqrt ζ ≤ 1 / 3 :=
  Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩

/-- extension by zero. -/
private def s9dI_ext {k : ℕ} (B : Finset (Fin k)) (a : B → ℂ) : Fin k → ℂ :=
  fun r => if h : r ∈ B then a ⟨r, h⟩ else 0

private lemma s9dI_ext_mem {k : ℕ} (B : Finset (Fin k)) (a : B → ℂ) (r : B) :
    s9dI_ext B a r = a r := by
  simp [s9dI_ext, r.2]

private lemma s9dI_ext_not {k : ℕ} (B : Finset (Fin k)) (a : B → ℂ) (r : Fin k) (hr : r ∉ B) :
    s9dI_ext B a r = 0 := by
  simp [s9dI_ext, hr]

/-- restriction of the level-`(n-1)` bound to the coefficient sets `R', S', T'`, and the
contradiction `Claim 9.13` against `Lemma 9.15`, in the form of `s9d_variance_contradiction`. -/
private lemma s9dI_contra {sT sR sS : ℕ} (Fh : Fin sT → Fin sR → Fin sS → ℂ)
    (R' : Finset (Fin sR)) (S' : Finset (Fin sS)) (T' : Finset (Fin sT)) {M1 M2 δ' ζ c : ℝ}
    (hlev : ∀ (a : Fin sR → ℂ) (b : Fin sS → ℂ), ∑ t, ‖∑ r, ∑ s, a r * b s * Fh t r s‖ ^ 2 ≤
      δ' ^ 2 * (∑ r, ‖a r‖ ^ 2) * ∑ s, ‖b s‖ ^ 2)
    (hδ' : 0 < δ') (hζ : 0 ≤ ζ) (h3 : 3 * Real.sqrt ζ ≤ 1) (hM1 : 1 - ζ ≤ M1) (hM1' : M1 ≤ 1)
    (hM2 : 1 - ζ ≤ M2) (hM2' : M2 ≤ 1)
    (hlow : ∀ r ∈ R', ∀ s ∈ S', (1 - Real.sqrt ζ) * δ' ^ 2 ≤ ∑ t ∈ T', ‖Fh t r s‖ ^ 2)
    (hc : 0 ≤ c)
    (hsmall : 6 * Real.sqrt ζ * (((R'.card : ℝ) * ((R'.card : ℝ) + 1)) *
          ((S'.card : ℝ) * ((S'.card : ℝ) + 1))) < (M1 * M2) ^ 2 * c ^ 2)
    {r r' : Fin sR} {s s' : Fin sS} (hr : r ∈ R') (hr' : r' ∈ R') (hs : s ∈ S') (hs' : s' ∈ S')
    (hne : (r, s) ≠ (r', s'))
    (hG : c * δ' ^ 2 ≤ ‖∑ t ∈ T', Fh t r s * starRingEnd ℂ (Fh t r' s')‖) : False := by
  classical
  have : Nonempty R' := ⟨⟨r, hr⟩⟩
  have : Nonempty S' := ⟨⟨s, hs⟩⟩
  have hV : ∀ (a : R' → ℂ) (b : S' → ℂ), ∑ t : T', ‖∑ q : R', ∑ p : S', a q * b p * Fh t q p‖ ^ 2 ≤
      δ' ^ 2 * (∑ q, ‖a q‖ ^ 2) * ∑ p, ‖b p‖ ^ 2 := by
    intro a b
    have h := hlev (s9dI_ext R' a) (s9dI_ext S' b)
    have e1 : ∀ t, ∑ q, ∑ p, s9dI_ext R' a q * s9dI_ext S' b p * Fh t q p =
        ∑ q : R', ∑ p : S', a q * b p * Fh t q p := by
      intro t
      rw [s9dI_sum_sub R' (fun q => ∑ p, s9dI_ext R' a q * s9dI_ext S' b p * Fh t q p)
        (by
          intro q hq
          simp [s9dI_ext_not R' a q hq])]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [s9dI_sum_sub S' (fun p => s9dI_ext R' a q * s9dI_ext S' b p * Fh t q p)
        (by
          intro p hp
          simp [s9dI_ext_not S' b p hp])]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [s9dI_ext_mem, s9dI_ext_mem]
    have e2 : ∑ q, ‖s9dI_ext R' a q‖ ^ 2 = ∑ q : R', ‖a q‖ ^ 2 := by
      rw [s9dI_sum_sub R' (fun q => ‖s9dI_ext R' a q‖ ^ 2)
        (by
          intro q hq
          simp [s9dI_ext_not R' a q hq])]
      exact Finset.sum_congr rfl fun q _ => by rw [s9dI_ext_mem]
    have e3 : ∑ p, ‖s9dI_ext S' b p‖ ^ 2 = ∑ p : S', ‖b p‖ ^ 2 := by
      rw [s9dI_sum_sub S' (fun p => ‖s9dI_ext S' b p‖ ^ 2)
        (by
          intro p hp
          simp [s9dI_ext_not S' b p hp])]
      exact Finset.sum_congr rfl fun p _ => by rw [s9dI_ext_mem]
    simp only [e1, e2, e3] at h
    calc ∑ t : T', ‖∑ q : R', ∑ p : S', a q * b p * Fh t q p‖ ^ 2
        = ∑ t ∈ T', ‖∑ q : R', ∑ p : S', a q * b p * Fh t q p‖ ^ 2 :=
          Finset.sum_coe_sort T' (fun t => ‖∑ q : R', ∑ p : S', a q * b p * Fh t q p‖ ^ 2)
      _ ≤ ∑ t, ‖∑ q : R', ∑ p : S', a q * b p * Fh t q p‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
      _ ≤ _ := h
  refine s9d_variance_contradiction M1 M2 δ' ζ c (fun (q : R') (p : S') (t : T') => Fh t q p)
    hV hδ' hζ h3 hM1 hM1' hM2 hM2' ?_ hc ?_ ⟨r, hr⟩ ⟨r', hr'⟩ ⟨s, hs⟩ ⟨s', hs'⟩ ?_ ?_
  · intro q p
    have := hlow q q.2 p p.2
    rwa [← Finset.sum_coe_sort T' (fun t => ‖Fh t q p‖ ^ 2)] at this
  · simpa [Fintype.card_coe] using hsmall
  · intro hh
    apply hne
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hh
    rw [hh.1, hh.2]
  · unfold s9dGram
    rw [Finset.sum_coe_sort T' (fun t => Fh t r s * starRingEnd ℂ (Fh t r' s'))]
    exact hG

section S9dInductiveBridge
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

omit [DecidableEq X] [DecidableEq Z] in
private lemma s9dI_lawY_eq (μ : FinProb (X × Y × Z)) (y : Y) :
    (lawY μ).prob y = ∑ z, ∑ x, μ.prob (x, y, z) := by
  show ∑ p ∈ univ.filter (fun p : X × Y × Z => p.2.1 = y), μ.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm) ?_
  simp [Finset.sum_comm (γ := Z)]

omit [DecidableEq X] [DecidableEq Y] in
private lemma s9dI_lawZ_eq (μ : FinProb (X × Y × Z)) (z : Z) :
    (lawZ μ).prob z = ∑ y, ∑ x, μ.prob (x, y, z) := by
  show ∑ p ∈ univ.filter (fun p : X × Y × Z => p.2.2 = z), μ.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

omit [DecidableEq X] in
/-- under the uniform-`(y,z)` hypothesis, `μ_y` and `μ_z` have full support. -/
private lemma s9dI_pos_yz (μ : FinProb (X × Y × Z))
    (hu : ∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) :
    (∀ y, 0 < (lawY μ).prob y) ∧ ∀ z, 0 < (lawZ μ).prob z := by
  have hne : Nonempty (X × Y × Z) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := μ.sum_eq_one
    simp at this
  obtain ⟨⟨_, y0, z0⟩⟩ := hne
  have hy : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos_iff.2 ⟨y0⟩
  have hz : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos_iff.2 ⟨z0⟩
  constructor
  · intro y
    rw [s9dI_lawY_eq]
    simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    positivity
  · intro z
    rw [s9dI_lawZ_eq]
    simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    positivity

end S9dInductiveBridge

section S9dInductiveSmul
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

private lemma s9dI_cl2norm_smul {α ι : Type} [Fintype α] [DecidableEq ι] [Fintype ι]
    (π : FinProb α) (a : ℂ) (f : (ι → α) → ℂ) : cl2norm π (a • f) = ‖a‖ * cl2norm π f := by
  unfold cl2norm cl2sq FinProb.expect
  have : ∑ x, (π.pi ι).prob x * ‖(a • f) x‖ ^ 2 = ‖a‖ ^ 2 * ∑ x, (π.pi ι).prob x * ‖f x‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private lemma s9dI_corrF_smul {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (a b c : ℂ) (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    s7CorrF μ (a • F) (b • g) (c • h) = a * b * c * s7CorrF μ F g h := by
  unfold s7CorrF FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end S9dInductiveSmul

end S9dInductiveHelpers

section S9dInductive

/-- the core of Lemma 9.3 for ONE unit triple and ONE admissible parameter tuple: with `T', R', S'` the
coefficients `≥ τ` and none in `[η, τ)` (Claim 9.8), `|𝔼 F g h| ≤ (1 - ε) δ_{n-1,d'-1}`. The explicit
inequalities are exactly those `s9d_parameter_hierarchy` provides. Route: `s9d_expansion`,
`s9d_near_equality_case_split`; otherwise `assume_delta_2, 3` hold, and either `δ_{n-1,d'-1} = 0` (all
`F̂_t(r,s) = 0`, nothing to prove) or `s9d_v_not_perp` gives a pair, against `s9d_variance_contradiction`
(for `V_{r,s} = (F̂_t(r,s))_{t∈T'}`, `M₁, M₂ ≥ 1 - mη² ≥ 1 - ζ`, Claim 9.11). -/
theorem s9d_core_step {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
    {K₁ K₂ : Type} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ} {F : (Fin n → Y × Z) → ℂ}
    {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    {m : ℕ} (hm : 1 ≤ m) (hX : Fintype.card X ≤ m) (hY : Fintype.card Y ≤ m)
    (hZ : Fintype.card Z ≤ m) {α : ℝ} (hα : 0 < α) (hat : ∀ p ∈ μ.support, α ≤ μ.prob p)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (Sm : Finset X) (hSm : Sm.Nonempty)
    (hrb : RelaxedBaseCase μ Sm c C) (D : S9dSvd j μ hμ ux F g h d') (hF : S7ConstOnCC hμ F)
    {τ η ε ζ A : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η) (hζ0 : 0 < ζ) (hA : 0 < A)
    (hsψ : ∀ t, D.ψ t < η ∨ τ ≤ D.ψ t) (hsκ : ∀ r, D.κ r < η ∨ τ ≤ D.κ r)
    (hsρ : ∀ s, D.ρ s < η ∨ τ ≤ D.ρ s)
    (hIj : 1 / A ≤ s7CCModestInf μ hμ hocc Sm hF j)
    (hb : (m : ℝ) ^ 3 * η + ε ≤ ζ / 2) (hζτ : ζ ≤ τ ^ 8) (hd : (m : ℝ) * η ^ 2 ≤ ζ)
    (he : ζ * (m : ℝ) ^ 8 < 1) (hg : 9 * ζ ≤ 1)
    (hf : 6 * Real.sqrt ζ * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 <
      (1 - ζ) ^ 4 * (1 / (2 * (m : ℝ) ^ 3)) ^ 2)
    (hlt : s9dVarBound m α c C ζ η < 1 / ((m : ℝ) ^ 2 * A)) :
    ‖s7CorrF μ F g h‖ ≤ (1 - ε) * (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal := by
  classical
  obtain ⟨δ', hδ'e⟩ : ∃ δ', δ' = (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal := ⟨_, rfl⟩
  rw [← hδ'e]
  have hδ0 : 0 ≤ δ' := by rw [hδ'e]; exact ENNReal.toReal_nonneg
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hζ1 : ζ ≤ 1 := by linarith
  have hcard := s9d_card_le D
  have hR : D.sG ≤ m := hcard.2.1.trans hY
  have hS : D.sH ≤ m := hcard.2.2.trans hZ
  have hT : D.sF ≤ m := hcard.1.trans hX
  have hlevA : ∀ (a : Fin D.sG → ℂ) (b : Fin D.sH → ℂ),
      ∑ t, ‖∑ r, ∑ s, a r * b s * D.Fhat t r s‖ ^ 2 ≤
        δ' ^ 2 * (∑ r, ‖a r‖ ^ 2) * ∑ s, ‖b s‖ ^ 2 := by
    intro a b
    have := s9d_level_bounds_a D hind a b
    rw [← hδ'e] at this
    exact this
  have hlev : ∀ r s, ∑ t, ‖D.Fhat t r s‖ ^ 2 ≤ δ' ^ 2 := by
    intro r s
    have e1 : ∀ {k : ℕ} (r : Fin k), ∑ x, ‖(Pi.single r (1 : ℂ) : Fin k → ℂ) x‖ ^ 2 = 1 := by
      intro k r
      rw [Finset.sum_eq_single r]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ r) h
    have := hlevA (Pi.single r 1) (Pi.single s 1)
    rw [e1, e1] at this
    simpa [Pi.single_apply] using this
  have hbb := s9d_level_bounds_b D hind
  have hsum : s7CorrF μ F g h = ∑ x, s9dTerm D.ψ D.κ D.ρ D.Fhat D.FhatJ x := by
    rw [s9d_expansion D]
    rfl
  have hcs := s9d_near_equality_case_split m hR hS hT D.ψ D.κ D.ρ D.ψ_nonneg D.κ_nonneg
    D.ρ_nonneg D.ψ_sq D.κ_sq D.ρ_sq D.Fhat D.FhatJ hδ0 hlev hbb.1 hη hζ0.le hζ1 hsψ hsκ hsρ hb
  rcases hcs with hcs | ⟨hassume2, hassume3⟩
  · rw [hsum]
    exact hcs
  · rcases hδ0.eq_or_lt with h0 | hpos
    · have hF0 : ∀ t r s, D.Fhat t r s = 0 := by
        intro t r s
        have h1 := hlev r s
        have h2 : ‖D.Fhat t r s‖ ^ 2 ≤ ∑ t', ‖D.Fhat t' r s‖ ^ 2 :=
          Finset.single_le_sum (f := fun t' => ‖D.Fhat t' r s‖ ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ t)
        rw [← h0] at h1
        have h3 : ‖D.Fhat t r s‖ ^ 2 ≤ 0 := by nlinarith
        have h4 : ‖D.Fhat t r s‖ = 0 := by nlinarith [norm_nonneg (D.Fhat t r s)]
        exact norm_eq_zero.1 h4
      have hz : ∑ x, s9dTerm D.ψ D.κ D.ρ D.Fhat D.FhatJ x = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [s9dTerm, hF0]
      rw [hsum, hz, ← h0]
      simp
    · exfalso
      have hpos' : 0 < (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal := by
        rw [← hδ'e]; exact hpos
      have hassume3' := hassume3
      rw [hδ'e] at hassume3'
      obtain ⟨r, hr, s, hs, r', hr', s', hs', hne, hG⟩ :=
        s9d_v_not_perp hind hocc hm hX hY hZ hα hat hc hC Sm hSm hrb D hF hpos' hτ hτ1 hζ0 hζτ hg
          he hA hη hsψ hassume2 hassume3' hIj hlt
      rw [← hδ'e] at hG
      have hup : ∀ r ∈ s9dBig D.κ τ, ∀ s ∈ s9dBig D.ρ τ,
          ∑ t ∈ s9dBig D.ψ τ, ‖D.Fhat t r s‖ ^ 2 ≤ δ' ^ 2 := fun r _ s _ =>
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => sq_nonneg _).trans (hlev r s)
      have hκ1 : ∑ r ∈ s9dBig D.κ τ, D.κ r ^ 2 ≤ 1 := by
        rw [← D.κ_sq]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
      have hρ1 : ∑ s ∈ s9dBig D.ρ τ, D.ρ s ^ 2 ≤ 1 := by
        rw [← D.ρ_sq]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
      have hnorm := s9d_bound_norm_V D.κ D.ρ D.Fhat (s9dBig D.κ τ) (s9dBig D.ρ τ)
        (s9dBig D.ψ τ) hδ0 hζ0.le hτ hζτ (fun r hr => (s9dBig_mem D.κ τ r).1 hr)
        (fun s hs => (s9dBig_mem D.ρ τ s).1 hs) hκ1 hρ1 hup hassume3
      have hM1 := s9dI_mass_ge D.κ hR D.κ_nonneg D.κ_sq hsκ hd
      have hM2 := s9dI_mass_ge D.ρ hS D.ρ_nonneg D.ρ_sq hsρ hd
      have hM1' := s9dI_mass_le_one D.κ τ D.κ_sq
      have hM2' := s9dI_mass_le_one D.ρ τ D.ρ_sq
      have hRc : (s9dBig D.κ τ).card ≤ m :=
        (Finset.card_le_univ _).trans (by simpa using hR)
      have hSc : (s9dBig D.ρ τ).card ≤ m :=
        (Finset.card_le_univ _).trans (by simpa using hS)
      have hRc' : ((s9dBig D.κ τ).card : ℝ) ≤ m := by exact_mod_cast hRc
      have hSc' : ((s9dBig D.ρ τ).card : ℝ) ≤ m := by exact_mod_cast hSc
      have hsq := s9dI_sqrt_le hg
      have hm3 : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
      have hk1 := s9dI_kk (Nat.cast_nonneg (α := ℝ) (s9dBig D.κ τ).card) hRc'
      have hk2 := s9dI_kk (Nat.cast_nonneg (α := ℝ) (s9dBig D.ρ τ).card) hSc'
      have hk : (((s9dBig D.κ τ).card : ℝ) * (((s9dBig D.κ τ).card : ℝ) + 1)) *
          (((s9dBig D.ρ τ).card : ℝ) * (((s9dBig D.ρ τ).card : ℝ) + 1)) ≤
          ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 := by
        calc _ ≤ ((m : ℝ) * ((m : ℝ) + 1)) * ((m : ℝ) * ((m : ℝ) + 1)) :=
              mul_le_mul hk1 hk2 (by positivity) (by positivity)
          _ = _ := by ring
      have hz0 : 0 ≤ 1 - ζ := by linarith
      have hMM : (1 - ζ) * (1 - ζ) ≤ s9dMass D.κ τ * s9dMass D.ρ τ :=
        mul_le_mul hM1 hM2 hz0 (hz0.trans hM1)
      have hMM2 : (1 - ζ) ^ 4 ≤ (s9dMass D.κ τ * s9dMass D.ρ τ) ^ 2 := by
        calc (1 - ζ) ^ 4 = ((1 - ζ) * (1 - ζ)) ^ 2 := by ring
          _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hz0 hz0) hMM 2
      have hsmall : 6 * Real.sqrt ζ *
          ((((s9dBig D.κ τ).card : ℝ) * (((s9dBig D.κ τ).card : ℝ) + 1)) *
            (((s9dBig D.ρ τ).card : ℝ) * (((s9dBig D.ρ τ).card : ℝ) + 1))) <
          (s9dMass D.κ τ * s9dMass D.ρ τ) ^ 2 * (1 / (2 * (m : ℝ) ^ 3)) ^ 2 := by
        calc _ ≤ 6 * Real.sqrt ζ * ((m : ℝ) * ((m : ℝ) + 1)) ^ 2 :=
              mul_le_mul_of_nonneg_left hk (by positivity)
          _ < (1 - ζ) ^ 4 * (1 / (2 * (m : ℝ) ^ 3)) ^ 2 := hf
          _ ≤ _ := mul_le_mul_of_nonneg_right hMM2 (sq_nonneg _)
      exact s9dI_contra D.Fhat (s9dBig D.κ τ) (s9dBig D.ρ τ) (s9dBig D.ψ τ) hlevA hpos hζ0.le
        (by linarith) hM1 hM1' hM2 hM2' (fun r hr s hs => (hnorm r hr s hs).1) (by positivity)
        hsmall hr hr' hs hs' hne hG

/-- Paper IV `lem:delta-inductive`, per triple (l. 5346-5934): for all `m, α` and the relaxed-base-case
constants `(c, C)` there is `C' > 0` (fixed before `A`; `C' = C₀` of `s9d_parameter_hierarchy`) such
that for every `A ≥ 2`, `1 ≤ d' ≤ n ≤ d'A`, every `μ` as in Thm 6.7 (hypotheses 1, 2, 5, 7 and clause 1
and 2 of the relaxed base case; the unused 3, 4, 6b, 6c are not assumed), every basis `Bx`
and every unit `F ∈ F_{n,d'}`, `g`, `h`: `|𝔼 F g h| ≤ (1 - A^{-C'}) δ_{n-1,d'-1}`. Proof: Claim 9.8
(`s9d_separate_out`) picks the candidate tuple of `s9d_parameter_hierarchy`; then `s9d_choose_coordinate`,
`s9d_svd_exists`, `s9d_core_step`. -/
theorem s9d_triple_bound (m : ℕ) {α : ℝ} (hα : 0 < α) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ A : ℝ, 2 ≤ A → ∀ n d' : ℕ, 1 ≤ d' → d' ≤ n → (n : ℝ) ≤ d' * A →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ hμ : S7YZImpliesX μ.support, (∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) →
        (∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (σ : X → H) (Sm : Finset X),
        (∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') → RelaxedBaseCase μ Sm c C →
        ∀ Bx : S7ModestBasis (lawX μ) σ Sm,
        ∀ (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
        F ∈ s7ClassFn μ hμ Bx.u n d' → cl2norm (s7LawYZ μ) F = 1 → cl2norm (lawY μ) g = 1 →
        cl2norm (lawZ μ) h = 1 →
        ‖s7CorrF μ F g h‖ ≤
          (1 - 1 / A ^ C') * (s7DeltaParam μ hμ Bx.u (n - 1) (d' - 1)).toReal := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · refine ⟨1, one_pos, ?_⟩
    intro A _ n d' _ _ _ X Y Z _ _ _ _ _ _ hX _ _ μ
    exfalso
    subst hm0
    have hXe : IsEmpty X := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hX)
    have hPe : IsEmpty (X × Y × Z) := ⟨fun p => hXe.false p.1⟩
    have h1 := μ.sum_eq_one
    simp at h1
  obtain ⟨R₁, R₂, R₃, R₄, hRord, hchain, C₀, hC₀, hRle, hhier⟩ :=
    s9d_parameter_hierarchy m hm hα hc hC
  refine ⟨C₀, hC₀, ?_⟩
  intro A hA n d' hd'1 hd'n hnA X Y Z _ _ _ _ _ _ hX hY hZ μ hat hμ hocc hu H _ _ _ σ Sm hconst hrb
    Bx F g h hFmem nF ng nh
  obtain ⟨hF, hFd⟩ := hFmem
  have hind := s8_hind_of_uniform μ hu
  have hDx : ∀ a, 0 < (lawX μ).prob a := fun a => lt_of_lt_of_le hα (s9d_lawX_ge μ hat hocc a)
  obtain ⟨hDy, hDz⟩ := s9dI_pos_yz μ hu
  have hn : 0 < n := by omega
  have hA0 : 0 < A := by linarith
  have hA1 : 1 < A := by linarith
  obtain ⟨j, hj⟩ := s9d_choose_coordinate μ hμ hocc hDx σ Sm hconst Bx hn hd'1 F hF hFd nF hnA
  obtain ⟨D⟩ := s9d_svd_exists μ hμ hDx hDy hDz σ Sm Bx j F g h d' hF hFd nF ng nh
  have hSm : Sm.Nonempty := Finset.card_pos.1 (by have := hrb.1; omega)
  have hcard := s9d_card_le D
  have hlohi : ∀ i, A ^ (-R₄ i) < A ^ (-R₁ i) := fun i =>
    Real.rpow_lt_rpow_of_exponent_lt hA1 (by linarith [(hRord i).1, (hRord i).2.1, (hRord i).2.2.1,
      (hRord i).2.2.2])
  have hch : ∀ i, A ^ (-R₁ (i + 1)) = A ^ (-R₄ i) := fun i => by rw [hchain i]
  obtain ⟨i, hi, hsep⟩ := s9d_separate_out (ι := Fin D.sF ⊕ Fin D.sG ⊕ Fin D.sH) (3 * m)
    (by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega)
    (fun i => A ^ (-R₄ i)) (fun i => A ^ (-R₁ i)) hlohi hch
    (Sum.elim D.ψ (Sum.elim D.κ D.ρ))
  have hsplit : ∀ x : ℝ, ¬(A ^ (-R₄ i) ≤ x ∧ x < A ^ (-R₁ i)) → x < A ^ (-R₄ i) ∨ A ^ (-R₁ i) ≤ x := by
    intro x hx
    by_cases h1 : A ^ (-R₄ i) ≤ x
    · exact Or.inr (not_lt.1 fun h2 => hx ⟨h1, h2⟩)
    · exact Or.inl (not_le.1 h1)
  have hsψ : ∀ t, D.ψ t < A ^ (-R₄ i) ∨ A ^ (-R₁ i) ≤ D.ψ t := fun t =>
    hsplit _ (hsep (Sum.inl t))
  have hsκ : ∀ r, D.κ r < A ^ (-R₄ i) ∨ A ^ (-R₁ i) ≤ D.κ r := fun r =>
    hsplit _ (hsep (Sum.inr (Sum.inl r)))
  have hsρ : ∀ s, D.ρ s < A ^ (-R₄ i) ∨ A ^ (-R₁ i) ≤ D.ρ s := fun s =>
    hsplit _ (hsep (Sum.inr (Sum.inr s)))
  obtain ⟨hb, hζτ, hd, he, hg, hf, hlt⟩ := hhier A hA i
  have hτ : 0 < A ^ (-R₁ i) := Real.rpow_pos_of_pos hA0 _
  have hτ1 : A ^ (-R₁ i) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hA1.le (by linarith [(hRord i).1])
  have hη : 0 ≤ A ^ (-R₄ i) := (Real.rpow_pos_of_pos hA0 _).le
  have hζ0 : 0 < A ^ (-R₂ i) := Real.rpow_pos_of_pos hA0 _
  have hcore := s9d_core_step hind hocc hm hX hY hZ hα hat hc hC Sm hSm hrb D hF hτ hτ1 hη hζ0
    hA0 hsψ hsκ hsρ hj hb hζτ hd he hg hf hlt
  have hR3 : A ^ (-C₀) ≤ A ^ (-R₃ i) :=
    Real.rpow_le_rpow_of_exponent_le hA1.le (by linarith [hRle i hi])
  have hneg : 1 / A ^ C₀ = A ^ (-C₀) := by
    rw [Real.rpow_neg hA0.le, one_div]
  have hδ0 : 0 ≤ (s7DeltaParam μ hμ Bx.u (n - 1) (d' - 1)).toReal := ENNReal.toReal_nonneg
  refine hcore.trans (mul_le_mul_of_nonneg_right ?_ hδ0)
  rw [hneg]
  linarith

/-- Paper IV `lem:delta-inductive` (Lemma 9.3, l. 5263-5270): for all `m ∈ ℕ`, `α > 0` (and the
relaxed-base-case constants `c(α, m)`, `C(α, m)` of Def. 6.6, which the printed "`C` depends on `m, α`"
leaves implicit) there is `C > 0` such that for `A ≥ 2`, `1 ≤ d' ≤ n ≤ d'A` and every `μ` as
in Thm 6.7: `δ_{n,d'}[μ] ≤ (1 - A^{-C}) δ_{n-1,d'-1}[μ]` in `[0, ∞]` (`d' ≥ 1` is an implicit
premise; `n - 1`, `d' - 1` are `ℕ`-truncated). `Bx` is any modest basis. -/
theorem s9d_delta_inductive (m : ℕ) {α : ℝ} (hα : 0 < α) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ A : ℝ, 2 ≤ A → ∀ n d' : ℕ, 1 ≤ d' → d' ≤ n → (n : ℝ) ≤ d' * A →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ hμ : S7YZImpliesX μ.support, (∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) →
        (∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (σ : X → H) (Sm : Finset X),
        (∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') → RelaxedBaseCase μ Sm c C →
        ∀ Bx : S7ModestBasis (lawX μ) σ Sm,
        s7DeltaParam μ hμ Bx.u n d' ≤
          ENNReal.ofReal (1 - 1 / A ^ C') * s7DeltaParam μ hμ Bx.u (n - 1) (d' - 1) := by
  classical
  obtain ⟨C', hC', hbound⟩ := s9d_triple_bound m hα hc hC
  refine ⟨C', hC', ?_⟩
  intro A hA n d' hd'1 hd'n hnA X Y Z _ _ _ _ _ _ hX hY hZ μ hat hμ hocc hu H _ _ _ σ Sm hconst hrb Bx
  have hind := s8_hind_of_uniform μ hu
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hle1 := s7_deltaParam_le_one μ hμ hind Bx.u (n - 1) (d' - 1)
  have hfin : s7DeltaParam μ hμ Bx.u (n - 1) (d' - 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle1
  have hAC : 1 ≤ A ^ C' := Real.one_le_rpow hA1 hC'.le
  have hb0 : 0 ≤ 1 - 1 / A ^ C' := by
    have : 1 / A ^ C' ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hAC
    linarith
  have hδ0 : 0 ≤ (s7DeltaParam μ hμ Bx.u (n - 1) (d' - 1)).toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hb0]
  refine (s7DeltaParam_le_iff μ hμ Bx.u n d' (mul_nonneg hb0 hδ0)).2 ?_
  intro F g h hFmem nF ng nh
  have haF : 0 < cl2norm (s7LawYZ μ) F := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm nF)
  have haG : 0 < cl2norm (lawY μ) g := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ng)
  have haH : 0 < cl2norm (lawZ μ) h := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm nh)
  set aF := cl2norm (s7LawYZ μ) F with haFdef
  set aG := cl2norm (lawY μ) g with haGdef
  set aH := cl2norm (lawZ μ) h with haHdef
  have key := hbound A hA n d' hd'1 hd'n hnA X Y Z hX hY hZ μ hat hμ hocc hu H σ Sm hconst hrb Bx
    ((((aF : ℝ)⁻¹ : ℝ) : ℂ) • F) ((((aG : ℝ)⁻¹ : ℝ) : ℂ) • g) ((((aH : ℝ)⁻¹ : ℝ) : ℂ) • h)
    (s7_classFn_smul μ hμ Bx.u n d' _ hFmem)
    (by rw [s9dI_cl2norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 haF.le)]
        exact inv_mul_cancel₀ haF.ne')
    (by rw [s9dI_cl2norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 haG.le)]
        exact inv_mul_cancel₀ haG.ne')
    (by rw [s9dI_cl2norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 haH.le)]
        exact inv_mul_cancel₀ haH.ne')
  rw [s9dI_corrF_smul] at key
  have hn : ‖(((aF : ℝ)⁻¹ : ℝ) : ℂ) * (((aG : ℝ)⁻¹ : ℝ) : ℂ) * (((aH : ℝ)⁻¹ : ℝ) : ℂ) *
      s7CorrF μ F g h‖ = (aF * aG * aH)⁻¹ * ‖s7CorrF μ F g h‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 haF.le),
      Real.norm_of_nonneg (inv_nonneg.2 haG.le), Real.norm_of_nonneg (inv_nonneg.2 haH.le)]
    field_simp
  rw [hn] at key
  have hp : 0 < aF * aG * aH := by positivity
  rw [inv_mul_le_iff₀ hp] at key
  rw [mul_comm]
  exact key

end S9dInductive

end TrackB
end RestrictedPolynomials
end
