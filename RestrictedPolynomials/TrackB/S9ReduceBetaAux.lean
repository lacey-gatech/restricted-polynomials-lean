module

public import RestrictedPolynomials.TrackB.S9Setup

/-!
# Track B: the Section 8.3 bounds for an SVD triple (paper IV)

Source: paper IV (`writeup_stability.tex`), l. 5009-5203 (Claim 8.7, Lemmas 8.9-8.11, 8.8 and the
assembly). First half of the formalization of this part, split off because the whole file would be
very long; `S9ReduceBeta` imports this file and contains the real-analytic steps
`s9_parameter_hierarchy`, `s9_select_dominant_character`, `s9_reduce_beta` and the iteration.

Formalization choices:

* `s9_bound_small_beta`, `s9_bound_additivebase_beta_of_additive_base`,
  `s9_diagonal_small_beta` and `s9_assemble_bound_of_additive_base` take
  `hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot` (right after the SVD triple `S`).
* The two lemmas that take the additive base case as the hypothesis `hadd` (the body of the
  conclusion of `s8_additive_base_case`) are conditional helpers and carry the suffix `_of_additive_base`.
* The assembly holds with the plain `C_m` (the hypothesis carries `2 C_m`, which is harmless).
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

/-! ### Real-analytic step (no setting) -/

section S9Analytic

/-- Paper IV `claim:bound-calculus` (Claim 8.7, l. 5192-5200): `P(a,b) = a + b - 2ab - K(2 - a - b) ≥ 0` for
`a, b ∈ [1 - 6τ, 1]`, `K = (8 C_m / c) √η`. The hierarchy (`hier`) is read as the one inequality the proof
uses, `1/2 + 4 C_m √η / c ≤ 1 - 6τ` (`P` is decreasing in each variable there). -/
theorem s9_bound_calculus {τ η c Cm : ℝ} (hτ : 0 < τ) (hη : 0 < η) (hc : 0 < c) (hCm : 0 ≤ Cm)
    (hhier : 1 / 2 + 4 * Cm / c * Real.sqrt η ≤ 1 - 6 * τ) {a b : ℝ} (ha : 1 - 6 * τ ≤ a)
    (ha1 : a ≤ 1) (hb : 1 - 6 * τ ≤ b) (hb1 : b ≤ 1) :
    0 ≤ a + b - 2 * a * b - 8 * Cm / c * Real.sqrt η * (2 - a - b) := by
  have _ := hτ
  have _ := hη
  have _ := hCm
  have _ := hc
  set s : ℝ := 4 * Cm / c * Real.sqrt η with hs
  have hK : 8 * Cm / c * Real.sqrt η = 2 * s := by rw [hs]; ring
  rw [hK]
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact mul_nonneg (div_nonneg (by linarith) hc.le) (Real.sqrt_nonneg _)
  -- u = 1 - a, v = 1 - b ∈ [0, 6τ], 6τ ≤ 1/2 - s
  have hu : 0 ≤ 1 - a := by linarith
  have hv : 0 ≤ 1 - b := by linarith
  have hu' : 1 - a ≤ 1 / 2 - s := by linarith
  have hv' : 1 - b ≤ 1 / 2 - s := by linarith
  nlinarith [mul_nonneg hu (sub_nonneg.2 hv'), mul_nonneg hv (sub_nonneg.2 hu'), mul_nonneg hu hv]

end S9Analytic

section S9LemAux
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H]
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X} {Bx : S7ModestBasis (lawX μ) σ Sm}
  {By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)} {Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)}
  {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d d' dg dh : ℕ}

private lemma lem_cl2norm_one {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] (π : FinProb α)
    (f : (ι → α) → ℂ) (h : (π.pi ι).cinner f f = 1) : cl2norm π f = 1 := by
  have h1 : cl2sq π f = 1 := by
    have := cl2sq_cast π f
    rw [h] at this
    exact_mod_cast this
  unfold cl2norm
  rw [h1, Real.sqrt_one]

private lemma lem_FI_unit (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    {p : AddChar H ℂ ⊕ Fin S.sF} (hp : S.ψ p ≠ 0) : cl2norm (s7LawYZ μ) (S.FI p) = 1 :=
  lem_cl2norm_one _ _ (by simpa using S.orthF_I p p hp hp)

private lemma lem_gI_unit (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    {p : AddChar H ℂ ⊕ Fin S.sG} (hp : S.κ p ≠ 0) : cl2norm (lawY μ) (S.gI p) = 1 :=
  lem_cl2norm_one _ _ (by simpa using S.orthG_I p p hp hp)

private lemma lem_hI_unit (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    {p : AddChar H ℂ ⊕ Fin S.sH} (hp : S.ρ p ≠ 0) : cl2norm (lawZ μ) (S.hI p) = 1 :=
  lem_cl2norm_one _ _ (by simpa using S.orthH_I p p hp hp)

private lemma lem_gI_class (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (q : AddChar H ℂ ⊕ Fin S.sG) :
    (∃ Dtot, S7CompEmbedHom (lawY μ) By.u (S.gI q) Dtot) ∧
      ∃ d₁, S7NeHom (lawY μ) By.u (S.gI q) d₁ := by
  rcases q with π | r
  · exact ⟨(S.gI_chi π).1, dg, (S.gI_chi π).2⟩
  · exact ⟨(S.gI_r r).1, dg - 1, (S.gI_r r).2⟩

private lemma lem_hI_class (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (q : AddChar H ℂ ⊕ Fin S.sH) :
    (∃ Dtot, S7CompEmbedHom (lawZ μ) Bz.u (S.hI q) Dtot) ∧
      ∃ d₁, S7NeHom (lawZ μ) Bz.u (S.hI q) d₁ := by
  rcases q with π | r
  · exact ⟨(S.hI_chi π).1, dh, (S.hI_chi π).2⟩
  · exact ⟨(S.hI_s r).1, dh - 1, (S.hI_s r).2⟩

private lemma lem_FIt_class (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) (t : Fin S.sF) :
    S7ConstOnCC hμ (S.FI (Sum.inr t)) ∧
      (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u (S.FI (Sum.inr t)) Dtot) ∧
      S7CCNeHom μ hμ Bx.u (S.FI (Sum.inr t)) (d - 1) ∧
      S7CCEffDegGE μ hμ Bx.u (S.FI (Sum.inr t)) (d' - 1) := by
  obtain ⟨Dtot0, Da, hDsum, hDa⟩ := hFe
  exact ⟨(S.F_cc _).1, ⟨Dtot0, Da, hDsum, fun c hc a' => ((S.FI_t t).1 Da hDa) c hc a'⟩,
    (S.FI_t t).2.1, (S.FI_t t).2.2⟩

private lemma lem_FIchi_class (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (χ : AddChar H ℂ) :
    S7ConstOnCC hμ (S.FI (Sum.inl χ)) ∧
      (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u (S.FI (Sum.inl χ)) Dtot) ∧
      S7CCNeHom μ hμ Bx.u (S.FI (Sum.inl χ)) d ∧
      S7CCEffDegGE μ hμ Bx.u (S.FI (Sum.inl χ)) d' :=
  ⟨(S.F_cc _).1, (S.FI_chi χ).1, (S.FI_chi χ).2.1, (S.FI_chi χ).2.2⟩

private lemma lem_unit_cexpect {β : Type} [Fintype β] (π : FinProb β) (G : (Unit → β) → ℂ) :
    (π.pi Unit).cexpect G = π.cexpect (fun a => G (fun _ => a)) := by
  unfold FinProb.cexpect
  exact Fintype.sum_equiv (Equiv.funUnique Unit β) _ _ (fun x => by simp [FinProb.pi])

private lemma lem_unit_cinner {β : Type} [Fintype β] (π : FinProb β) (f f' : β → ℂ) :
    (π.pi Unit).cinner (fun w => f (w ())) (fun w => f' (w ())) = π.cinner f f' := by
  unfold FinProb.cinner
  rw [lem_unit_cexpect]

private lemma lem_fhatJ_bound (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {p : AddChar H ℂ ⊕ Fin S.sF} {q : AddChar H ℂ ⊕ Fin S.sG} {r : AddChar H ℂ ⊕ Fin S.sH}
    (hp : S.ψ p ≠ 0) (hq : S.κ q ≠ 0) (hr : S.ρ r ≠ 0) : ‖S.FhatJ p q r‖ ≤ 1 := by
  have key := s7_corrF_trivial_bound μ hind (ι := Unit) (fun w => S.FJ p (w ()))
    (fun y => S.gJ q (y ())) (fun z => S.hJ r (z ()))
  have e : s7CorrF μ (fun w : Unit → Y × Z => S.FJ p (w ())) (fun y : Unit → Y => S.gJ q (y ()))
      (fun z : Unit → Z => S.hJ r (z ())) = S.FhatJ p q r := by
    unfold s7CorrF S9Svd3.FhatJ s8Corr1
    rw [lem_unit_cexpect]
  rw [e] at key
  have n1 : cl2norm (s7LawYZ μ) (fun w : Unit → Y × Z => S.FJ p (w ())) = 1 :=
    lem_cl2norm_one _ _ (by rw [lem_unit_cinner]; simpa using S.orthF_J p p hp hp)
  have n2 : cl2norm (lawY μ) (fun y : Unit → Y => S.gJ q (y ())) = 1 :=
    lem_cl2norm_one _ _ (by rw [lem_unit_cinner]; simpa using S.orthG_J q q hq hq)
  have n3 : cl2norm (lawZ μ) (fun z : Unit → Z => S.hJ r (z ())) = 1 :=
    lem_cl2norm_one _ _ (by rw [lem_unit_cinner]; simpa using S.orthH_J r r hr hr)
  rwa [n1, n2, n3, mul_one, mul_one] at key

private lemma lem_triple_bound {T R Q : Type} [Fintype T] [Fintype R] [Fintype Q] (f : T → R → Q → ℂ)
    (pT : T → Prop) (pR : R → Prop) (pQ : Q → Prop) [DecidablePred pT] [DecidablePred pR]
    [DecidablePred pQ] (M : ℝ)
    (hf : ∀ t r s, ‖f t r s‖ ≤ if pT t ∧ pR r ∧ pQ s then M else 0) :
    ‖∑ t, ∑ r, ∑ s, f t r s‖ ≤
      ((Finset.univ.filter pT).card * (Finset.univ.filter pR).card *
        (Finset.univ.filter pQ).card : ℝ) * M := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ t, ‖∑ r, ∑ s, f t r s‖ ≤ ∑ r, ∑ s, ‖f t r s‖ := fun t =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _)
  refine (Finset.sum_le_sum fun t _ => h1 t).trans ?_
  have h2 : ∀ t r s, ‖f t r s‖ ≤ M * ((if pT t then 1 else 0) * (if pR r then 1 else 0) *
      (if pQ s then 1 else 0) : ℝ) := fun t r s => by
    refine (hf t r s).trans (le_of_eq ?_)
    by_cases a : pT t <;> by_cases b : pR r <;> by_cases c : pQ s <;> simp [a, b, c]
  refine (Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun r _ =>
    Finset.sum_le_sum fun s _ => h2 t r s).trans (le_of_eq ?_)
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole]
  rw [mul_comm]

private lemma lem_abs_le_sqrt_sum {P : Type} [Fintype P] (κ : P → ℂ) (p : P) :
    ‖κ p‖ ≤ Real.sqrt (∑ q, ‖κ q‖ ^ 2) :=
  (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun q => ‖κ q‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ p)))

private lemma lem_le_sqrt_one_sub {P : Type} [Fintype P] [DecidableEq P] (κ : P → ℂ)
    (h1 : ∑ p, ‖κ p‖ ^ 2 = 1) {p0 r : P} (hr : r ≠ p0) :
    ‖κ r‖ ≤ Real.sqrt (1 - ‖κ p0‖ ^ 2) := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have : ‖κ r‖ ^ 2 + ‖κ p0‖ ^ 2 ≤ ∑ p, ‖κ p‖ ^ 2 := by
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p => ‖κ p‖ ^ 2)
      (Finset.subset_univ {r, p0}) (fun p _ _ => sq_nonneg _)
    rwa [Finset.sum_pair hr] at h2
  linarith

private lemma lem_card_inr_le {A B : Type} [Fintype A] [Fintype B] (f : A ⊕ B → ℂ) :
    (Finset.univ.filter fun b : B => f (Sum.inr b) ≠ 0).card ≤
      (Finset.univ.filter fun p : A ⊕ B => f p ≠ 0).card := by
  refine Finset.card_le_card_of_injOn Sum.inr (fun b hb => ?_) (fun a _ b _ h => Sum.inr_injective h)
  simpa using hb

private lemma lem_push_c {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) (G : β → ℂ) :
    ∑ a, (π.prob a : ℂ) * G (f a) = ∑ b, ((mergePush π f).prob b : ℂ) * G b := by
  rw [← Finset.sum_fiberwise univ f (fun a => (π.prob a : ℂ) * G (f a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ a ∈ univ.filter (fun a => f a = b), (π.prob a : ℂ) * G (f a) =
      (π.prob a : ℂ) * G b := by
    intro a ha
    rw [(Finset.mem_filter.1 ha).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  show _ = ((∑ a ∈ univ.filter (fun a => f a = b), π.prob a : ℝ) : ℂ) * G b
  rw [Complex.ofReal_sum]

private lemma lem_push_r {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) (G : β → ℝ) :
    ∑ a, π.prob a * G (f a) = ∑ b, (mergePush π f).prob b * G b := by
  rw [← Finset.sum_fiberwise univ f (fun a => π.prob a * G (f a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ a ∈ univ.filter (fun a => f a = b), π.prob a * G (f a) = π.prob a * G b := by
    intro a ha
    rw [(Finset.mem_filter.1 ha).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  rfl

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma lem_supp (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H) [DecidableEq H]
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    {p : X × Y × Z} (hp : μ.prob p ≠ 0) : σ p.1 + γ p.2.1 + φ p.2.2 = 0 := by
  by_contra hne
  have h1 := hunif (σ p.1) (γ p.2.1) (φ p.2.2)
  simp only [hne, ↓reduceIte] at h1
  have h2 : μ.prob p ≤ ∑ q ∈ univ.filter (fun q : X × Y × Z =>
      (σ q.1, γ q.2.1, φ q.2.2) = (σ p.1, γ p.2.1, φ p.2.2)), μ.prob q :=
    Finset.single_le_sum (f := μ.prob) (fun q _ => μ.nonneg q) (by simp)
  rw [h1] at h2
  exact hp (le_antisymm h2 (μ.nonneg p))

private lemma lem_char_star (χ : AddChar H ℂ) (a : H) : star (χ a) = χ (-a) := by
  rw [AddChar.map_neg_eq_conj]
  rfl

private lemma lem_rot_W1_cinner (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (f f' : X → ℂ) :
    (s7LawYZ μ).cinner (s8W1 hμ f) (s8W1 hμ f') = (lawX μ).cinner f f' := by
  have h := s7_W_cinner μ hμ (ι := Unit) (fun x => f (x ())) (fun x => f' (x ()))
  unfold FinProb.cinner at h ⊢
  rw [lem_unit_cexpect, lem_unit_cexpect] at h
  simpa [s7W, s8W1] using h

private lemma lem_sq_indep {Y Z : Type} [Fintype Y] [Fintype Z] (pY : FinProb Y) (pZ : FinProb Z)
    (G : Y → ℂ) (K : Z → ℂ) (hG : pY.cexpect G = 0) :
    ∑ y, ∑ z, pY.prob y * pZ.prob z * ‖G y + K z‖ ^ 2 =
      pY.expect (fun y => ‖G y‖ ^ 2) + pZ.expect (fun z => ‖K z‖ ^ 2) := by
  have e1 : ∀ y z, ‖G y + K z‖ ^ 2 = ‖G y‖ ^ 2 + ‖K z‖ ^ 2 + 2 * (G y * star (K z)).re := by
    intro y z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp
  have hY1 : ∑ y, pY.prob y = 1 := pY.sum_eq_one
  have hZ1 : ∑ z, pZ.prob z = 1 := pZ.sum_eq_one
  simp only [e1, mul_add, Finset.sum_add_distrib]
  have t1 : ∑ y, ∑ z, pY.prob y * pZ.prob z * ‖G y‖ ^ 2 = pY.expect (fun y => ‖G y‖ ^ 2) := by
    unfold FinProb.expect
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hZ1, mul_one]
  have t2 : ∑ y, ∑ z, pY.prob y * pZ.prob z * ‖K z‖ ^ 2 = pZ.expect (fun z => ‖K z‖ ^ 2) := by
    unfold FinProb.expect
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have : ∀ y, pY.prob y * pZ.prob z * ‖K z‖ ^ 2 = pY.prob y * (pZ.prob z * ‖K z‖ ^ 2) :=
      fun y => by ring
    simp only [this]
    rw [← Finset.sum_mul, hY1, one_mul]
  have t3 : ∑ y, ∑ z, pY.prob y * pZ.prob z * (2 * (G y * star (K z)).re) = 0 := by
    have : ∑ y, ∑ z, pY.prob y * pZ.prob z * (2 * (G y * star (K z)).re) =
        2 * (∑ y, ∑ z, ((pY.prob y : ℂ) * G y) * ((pZ.prob z : ℂ) * star (K z))).re := by
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      have : ((pY.prob y : ℂ) * G y * ((pZ.prob z : ℂ) * star (K z))) =
          ((pY.prob y * pZ.prob z : ℝ) : ℂ) * (G y * star (K z)) := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      ring
    rw [this]
    have h0 : ∑ y, ∑ z, ((pY.prob y : ℂ) * G y) * ((pZ.prob z : ℂ) * star (K z)) = 0 := by
      rw [← Finset.sum_mul_sum]
      have : ∑ y, (pY.prob y : ℂ) * G y = 0 := hG
      rw [this, zero_mul]
    rw [h0]; simp
  rw [t1, t2, t3, add_zero]

private lemma lem_orth_sum_norm {P α : Type} [Fintype α] [DecidableEq P] (D : FinProb α)
    (e : P → α → ℂ) (s : Finset P) (a : P → ℂ) (w : α → ℂ) (hw : ∀ x, ‖w x‖ = 1)
    (horth : ∀ p ∈ s, ∀ q ∈ s, a p ≠ 0 → a q ≠ 0 →
      D.cinner (e p) (e q) = if p = q then 1 else 0) :
    D.expect (fun x => ‖∑ p ∈ s, a p * (e p x * w x)‖ ^ 2) = ∑ p ∈ s, ‖a p‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h1 : ((D.expect (fun x => ‖∑ p ∈ s, a p * (e p x * w x)‖ ^ 2) : ℝ) : ℂ) =
      D.cinner (fun x => ∑ p ∈ s, a p * (e p x * w x)) (fun x => ∑ p ∈ s, a p * (e p x * w x)) :=
    (cinner_self_eq D _).symm
  rw [h1]
  have hcin : ∀ p q : P, D.cinner (fun x => e p x * w x) (fun x => e q x * w x) =
      D.cinner (e p) (e q) := by
    intro p q
    unfold FinProb.cinner FinProb.cexpect
    refine Finset.sum_congr rfl fun x _ => ?_
    have : w x * star (w x) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw x]; simp
    calc (D.prob x : ℂ) * (e p x * w x * star (e q x * w x))
        = (D.prob x : ℂ) * (e p x * star (e q x)) * (w x * star (w x)) := by
          simp only [star_mul']; ring
      _ = _ := by rw [this, mul_one]
  have hfun : (fun x => ∑ p ∈ s, a p * (e p x * w x)) = ∑ p ∈ s, a p • (fun x => e p x * w x) := by
    funext x; simp [Finset.sum_apply]
  rw [hfun, cinner_sum_left]
  simp only [cinner_smul_left, cinner_sum_right, cinner_smul_right]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · rw [hcin]
    by_cases hap : a p = 0
    · simp [hap]
    · rw [horth p hp p hp hap hap]
      simp only [↓reduceIte, mul_one]
      rw [Complex.star_def]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro q hq hqp
    rw [hcin]
    by_cases hap : a p = 0
    · simp [hap]
    · by_cases haq : a q = 0
      · simp [haq]
      · rw [horth p hp q hq hap haq]
        simp [Ne.symm hqp]
  · intro hn; exact absurd hp hn

omit [Fintype H] in
private lemma lem_perp_twist {α : Type} [Fintype α] (D : FinProb α) (τ : α → H) (e : α → ℂ)
    (he : ∀ ψ : AddChar H ℂ, D.cinner e (fun x => ψ (τ x)) = 0) (χ : AddChar H ℂ) :
    (fun x => e x * star (χ (τ x))) ∈ s7Perp D (embedSpan τ) := by
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨ψ, rfl⟩
    have h := he (χ * ψ)
    unfold FinProb.cinner FinProb.cexpect at h ⊢
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [AddChar.mul_apply, star_mul']
    ring
  · exact cinner_zero_right _ _
  · intro x y _ _ hx hy
    rw [cinner_add_right, hx, hy, add_zero]
  · intro a x _ hx
    rw [cinner_smul_right, hx, mul_zero]

private lemma lem_pw (χ : AddChar H ℂ) (a b c : H) (hs : a + b + c = 0) :
    χ b = star (χ a) * star (χ c) := by
  have hb : b = -a + -c := by
    calc b = (a + b + c) - a - c := by abel
      _ = -a + -c := by rw [hs]; abel
  rw [hb, AddChar.map_add_eq_mul, lem_char_star, lem_char_star]

private lemma lem_sum_split {P : Type} [Fintype P] [DecidableEq P] (p0 : P) (f : P → ℂ) :
    ∑ p, f p = f p0 + ∑ p ∈ univ.filter (fun p => p ≠ p0), f p := by
  rw [← Finset.add_sum_erase univ f (Finset.mem_univ p0)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Finset.mem_erase]

omit [DecidableEq X] in
private lemma lem_sq_expect_yz (μ : FinProb (X × Y × Z))
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (G : Y → ℂ) (K : Z → ℂ) :
    μ.expect (fun p => ‖G p.2.1 + K p.2.2‖ ^ 2) =
      ∑ y, ∑ z, (lawY μ).prob y * (lawZ μ).prob z * ‖G y + K z‖ ^ 2 := by
  have h1 := lem_push_r μ (fun p : X × Y × Z => (p.2.1, p.2.2)) (fun v : Y × Z => ‖G v.1 + K v.2‖ ^ 2)
  unfold FinProb.expect
  refine h1.trans ?_
  show ∑ v, (s7LawYZ μ).prob v * ‖G v.1 + K v.2‖ ^ 2 = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  rw [hind y z]

private lemma lem_cexpect_sum {β I : Type} [Fintype β] (π : FinProb β) (s : Finset I) (u : I → ℂ)
    (f : I → β → ℂ) :
    π.cexpect (fun x => ∑ i ∈ s, u i * f i x) = ∑ i ∈ s, u i * π.cexpect (f i) := by
  unfold FinProb.cexpect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

private lemma lem_cexpect_add {β : Type} [Fintype β] (π : FinProb β) (A B : β → ℂ) :
    π.cexpect (fun x => A x + B x) = π.cexpect A + π.cexpect B := by
  simp [FinProb.cexpect, mul_add, Finset.sum_add_distrib]

end S9LemAux

section S9LemAux2
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X} {Bx : S7ModestBasis (lawX μ) σ Sm}
  {By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)} {Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)}
  {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d d' dg dh : ℕ}

private lemma lem_beta_apply (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (γ : Y → H) (φ : Z → H) (Sm : Finset X) (Bx : S7ModestBasis (lawX μ) σ Sm)
    (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)) (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z))
    (j : Fin n) {b : ℝ} (hb : 0 ≤ b) {d₁ d₁' : ℕ}
    (hβ : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d₁ d₁' ≤ ENNReal.ofReal b)
    {F' : (S8Rest j → Y × Z) → ℂ} {g' : (S8Rest j → Y) → ℂ} {h' : (S8Rest j → Z) → ℂ}
    (hF : S7ConstOnCC hμ F') (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F' Dtot)
    (hFn : S7CCNeHom μ hμ Bx.u F' d₁) (hFd : S7CCEffDegGE μ hμ Bx.u F' d₁')
    (hg : (∃ Dtot, S7CompEmbedHom (lawY μ) By.u g' Dtot) ∧ ∃ d₁, S7NeHom (lawY μ) By.u g' d₁)
    (hh : (∃ Dtot, S7CompEmbedHom (lawZ μ) Bz.u h' Dtot) ∧ ∃ d₂, S7NeHom (lawZ μ) Bz.u h' d₂)
    (nF : cl2norm (s7LawYZ μ) F' = 1) (ng : cl2norm (lawY μ) g' = 1)
    (nh : cl2norm (lawZ μ) h' = 1) : ‖s7CorrF μ F' g' h'‖ ≤ b := by
  obtain ⟨e⟩ := s8_restEquivFin (Equiv.refl (Fin n)) j
  have := (s8_beta_le_iff_generic μ hμ σ γ φ Sm Bx By Bz e d₁ d₁' hb).1 hβ F' g' h' hF hFe hFn hFd
    hg hh (by rw [nF]; exact one_ne_zero) (by rw [ng]; exact one_ne_zero)
    (by rw [nh]; exact one_ne_zero)
  rwa [nF, ng, nh, mul_one, mul_one, mul_one] at this

private lemma lem_fhat_t_bound (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) {b1 : ℝ} (hb1nn : 0 ≤ b1)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1)
    {t : Fin S.sF} {q : AddChar H ℂ ⊕ Fin S.sG} {r : AddChar H ℂ ⊕ Fin S.sH}
    (ht : S.ψ (Sum.inr t) ≠ 0) (hq : S.κ q ≠ 0) (hr : S.ρ r ≠ 0) :
    ‖S.Fhat (Sum.inr t) q r‖ ≤ b1 := by
  obtain ⟨c1, c2, c3, c4⟩ := lem_FIt_class S hFe t
  exact lem_beta_apply μ hμ σ γ φ Sm Bx By Bz j hb1nn hb1 c1 c2 c3 c4 (lem_gI_class S q)
    (lem_hI_class S r) (lem_FI_unit S ht) (lem_gI_unit S hq) (lem_hI_unit S hr)

private lemma lem_fhat_chi_bound (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    {b0 : ℝ} (hb0nn : 0 ≤ b0)
    (hb0 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' ≤ ENNReal.ofReal b0)
    {χ : AddChar H ℂ} (hψ : S.ψ (Sum.inl χ) ≠ 0) (hκ : S.κ (Sum.inl χ) ≠ 0)
    (hρ : S.ρ (Sum.inl χ) ≠ 0) :
    ‖S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)‖ ≤ b0 := by
  obtain ⟨c1, c2, c3, c4⟩ := lem_FIchi_class S χ
  exact lem_beta_apply μ hμ σ γ φ Sm Bx By Bz j hb0nn hb0 c1 c2 c3 c4 (lem_gI_class S _)
    (lem_hI_class S _) (lem_FI_unit S hψ) (lem_gI_unit S hκ) (lem_hI_unit S hρ)


end S9LemAux2


/-! ### The Section 8.3 lemmas for an SVD triple -/

section S9Lemmas
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X} {Bx : S7ModestBasis (lawX μ) σ Sm}
  {By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)} {Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)}
  {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d d' dg dh : ℕ}

private lemma lem_card_prod_le (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hDy : ∀ a, 0 < (lawY μ).prob a) (hDz : ∀ a, 0 < (lawZ μ).prob a) :
    ((Finset.univ.filter fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0).card *
      (Finset.univ.filter fun p => S.κ p ≠ 0).card *
      (Finset.univ.filter fun p => S.ρ p ≠ 0).card : ℝ) ≤
      (Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z := by
  obtain ⟨c1, c2, c3⟩ := s9_svd3_card_le S hDy hDz
  have d1 : (Finset.univ.filter fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0).card ≤
      Fintype.card (Y × Z) := (lem_card_inr_le S.ψ).trans c1
  have d2 : ((Finset.univ.filter fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0).card : ℝ) ≤
      Fintype.card (Y × Z) := by exact_mod_cast d1
  have d3 : ((Finset.univ.filter fun p => S.κ p ≠ 0).card : ℝ) ≤ Fintype.card Y := by
    exact_mod_cast c2
  have d4 : ((Finset.univ.filter fun p => S.ρ p ≠ 0).card : ℝ) ≤ Fintype.card Z := by
    exact_mod_cast c3
  exact mul_le_mul (mul_le_mul d2 d3 (by positivity) (by positivity)) d4 (by positivity)
    (by positivity)

private lemma lem_comb1 (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) (χs : AddChar H ℂ)
    (hκ : S.κ (Sum.inl χs) ≠ 0) {b1 : ℝ} (hb1nn : 0 ≤ b1)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1) :
    ∀ s : AddChar H ℂ ⊕ Fin S.sH, S.ρ s ≠ 0 →
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖S.Fhat (Sum.inr t) (Sum.inl χs) s‖ ^ 2 ≤ b1 ^ 2 := by
  have hc := s9_combine_F_t S hFe χs
  intro s hs
  by_cases h0 : ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
      ‖S.Fhat (Sum.inr t) (Sum.inl χs) s‖ ^ 2 = 0
  · rw [h0]; positivity
  · obtain ⟨Ft, c1, c2, c3, c4, c5, hsum⟩ := hc.1 s h0
    rw [hsum]
    have := lem_beta_apply μ hμ σ γ φ Sm Bx By Bz j hb1nn hb1 c1 c2 c3 c4
      (lem_gI_class S _) (lem_hI_class S _) c5 (lem_gI_unit S hκ) (lem_hI_unit S hs)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

private lemma lem_comb2 (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) (χs : AddChar H ℂ)
    (hρ : S.ρ (Sum.inl χs) ≠ 0) {b1 : ℝ} (hb1nn : 0 ≤ b1)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1) :
    ∀ r : AddChar H ℂ ⊕ Fin S.sG, S.κ r ≠ 0 →
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖S.Fhat (Sum.inr t) r (Sum.inl χs)‖ ^ 2 ≤ b1 ^ 2 := by
  have hc := s9_combine_F_t S hFe χs
  intro r hr
  by_cases h0 : ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
      ‖S.Fhat (Sum.inr t) r (Sum.inl χs)‖ ^ 2 = 0
  · rw [h0]; positivity
  · obtain ⟨Ft, c1, c2, c3, c4, c5, hsum⟩ := hc.2 r h0
    rw [hsum]
    have := lem_beta_apply μ hμ σ γ φ Sm Bx By Bz j hb1nn hb1 c1 c2 c3 c4
      (lem_gI_class S _) (lem_hI_class S _) c5 (lem_gI_unit S hr) (lem_hI_unit S hρ)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- Paper IV `lem:bound-additivebase-beta#combine-F-t`, second half (l. 5115-5120): with
`β_{n-1,d-1,d'-1} ≤ b₁` (stated through `ENNReal.ofReal`), `∑_t |F̂_t(χ*, s)|² ≤ b₁²` for every
`s` with `ρ_s ≠ 0`, and `∑_t |F̂_t(r, χ*)|² ≤ b₁²` for every `r` with `κ_r ≠ 0`
(`κ_{χ*}, ρ_{χ*} ≠ 0`, so that `g_{χ*}`, `h_{χ*}` are unit vectors). -/
theorem s9_combine_F_t_bound (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) (χs : AddChar H ℂ)
    (hκ : S.κ (Sum.inl χs) ≠ 0) (hρ : S.ρ (Sum.inl χs) ≠ 0) {b1 : ℝ} (hb1nn : 0 ≤ b1)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1) :
    (∀ s : AddChar H ℂ ⊕ Fin S.sH, S.ρ s ≠ 0 →
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖S.Fhat (Sum.inr t) (Sum.inl χs) s‖ ^ 2 ≤ b1 ^ 2) ∧
    (∀ r : AddChar H ℂ ⊕ Fin S.sG, S.κ r ≠ 0 →
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖S.Fhat (Sum.inr t) r (Sum.inl χs)‖ ^ 2 ≤ b1 ^ 2) :=
  ⟨lem_comb1 S hFe χs hκ hb1nn hb1, lem_comb2 S hFe χs hρ hb1nn hb1⟩

/-- Paper IV `lem:bound-main-term-beta` (Lemma 8.9, l. 5009-5019): the diagonal term, by `β_{n-1,d,d'} ≤ b₀`
(`F_χ ∈ F_{n-1,d,d'}`, `g_χ`, `h_χ` unit vectors of `G`, `H`), the triangle and Cauchy-Schwarz
inequalities. -/
theorem s9_bound_main_term (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    {b0 : ℝ} (hb0nn : 0 ≤ b0)
    (hb0 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' ≤ ENNReal.ofReal b0) :
    ‖∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
        S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)‖ ≤
      b0 * Real.sqrt (∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ)‖ ^ 2) *
        Real.sqrt (∑ χ : AddChar H ℂ, ‖S.κ (Sum.inl χ)‖ ^ 2 * ‖S.ρ (Sum.inl χ)‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
      S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)‖ ≤
      b0 * (‖S.ψ (Sum.inl χ)‖ * (‖S.κ (Sum.inl χ)‖ * ‖S.ρ (Sum.inl χ)‖)) := fun χ => by
    by_cases hz : S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) = 0
    · rw [hz, zero_mul, norm_zero]
      positivity
    · have hψ : S.ψ (Sum.inl χ) ≠ 0 := fun e => hz (by rw [e]; simp)
      have hκ : S.κ (Sum.inl χ) ≠ 0 := fun e => hz (by rw [e]; simp)
      have hρ : S.ρ (Sum.inl χ) ≠ 0 := fun e => hz (by rw [e]; simp)
      have := lem_fhat_chi_bound S hb0nn hb0 hψ hκ hρ
      rw [norm_mul, norm_mul, norm_mul]
      calc _ = (‖S.ψ (Sum.inl χ)‖ * (‖S.κ (Sum.inl χ)‖ * ‖S.ρ (Sum.inl χ)‖)) *
            ‖S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)‖ := by ring
        _ ≤ (‖S.ψ (Sum.inl χ)‖ * (‖S.κ (Sum.inl χ)‖ * ‖S.ρ (Sum.inl χ)‖)) * b0 :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
  refine (Finset.sum_le_sum fun χ _ => h1 χ).trans ?_
  rw [← Finset.mul_sum]
  have h2 : ∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ)‖ * (‖S.κ (Sum.inl χ)‖ * ‖S.ρ (Sum.inl χ)‖) ≤
      Real.sqrt (∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ)‖ ^ 2) *
        Real.sqrt (∑ χ : AddChar H ℂ, ‖S.κ (Sum.inl χ)‖ ^ 2 * ‖S.ρ (Sum.inl χ)‖ ^ 2) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (AddChar H ℂ))
      (fun χ => ‖S.ψ (Sum.inl χ)‖) (fun χ => ‖S.κ (Sum.inl χ)‖ * ‖S.ρ (Sum.inl χ)‖)
    simpa [mul_pow] using this
  calc b0 * ∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ)‖ * (‖S.κ (Sum.inl χ)‖ * ‖S.ρ (Sum.inl χ)‖)
      ≤ b0 * (Real.sqrt (∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ)‖ ^ 2) *
        Real.sqrt (∑ χ : AddChar H ℂ, ‖S.κ (Sum.inl χ)‖ ^ 2 * ‖S.ρ (Sum.inl χ)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 hb0nn
    _ = _ := by ring

/-- Paper IV `lem:bound-small-beta` (Lemma 8.10, l. 5022-5036): the terms with `t ∈ T` and
`r, s ≠ χ*`. The constant `C_m` is `|Γ × Φ| |Γ| |Φ|` (`≤ m⁴`: the number of nonzero summands,
`s9_svd3_card_le`; the source writes `≪_m` and counts `m³`). `hind` is hypothesis 5 (it gives
`|F̂'_t(r,s)| ≤ 1`, `s7_corrF_trivial_bound`). -/
theorem s9_bound_small_beta (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (hDy : ∀ a, 0 < (lawY μ).prob a) (hDz : ∀ a, 0 < (lawZ μ).prob a)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (χs : AddChar H ℂ) {b1 : ℝ} (hb1nn : 0 ≤ b1)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1) :
    ‖∑ t : Fin S.sF, ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        if r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0‖ ≤
      ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z) * b1 *
        Real.sqrt (∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2) *
        Real.sqrt (1 - ‖S.κ (Sum.inl χs)‖ ^ 2) * Real.sqrt (1 - ‖S.ρ (Sum.inl χs)‖ ^ 2) := by
  classical
  set A := Real.sqrt (∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2) with hA
  set B := Real.sqrt (1 - ‖S.κ (Sum.inl χs)‖ ^ 2) with hB
  set C := Real.sqrt (1 - ‖S.ρ (Sum.inl χs)‖ ^ 2) with hC
  have hM : 0 ≤ b1 * A * B * C := by positivity
  have key := lem_triple_bound
    (fun (t : Fin S.sF) (r : AddChar H ℂ ⊕ Fin S.sG) (s : AddChar H ℂ ⊕ Fin S.sH) =>
      if r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0)
    (fun t => S.ψ (Sum.inr t) ≠ 0) (fun r => S.κ r ≠ 0) (fun s => S.ρ s ≠ 0) (b1 * A * B * C)
    (fun t r s => by
      by_cases hc : r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs
      · by_cases hz : S.ψ (Sum.inr t) ≠ 0 ∧ S.κ r ≠ 0 ∧ S.ρ s ≠ 0
        · obtain ⟨ht, hr, hs⟩ := hz
          simp only [hc, and_self, ↓reduceIte, ht, hr, hs, ne_eq, not_false_eq_true]
          have e1 := lem_fhat_t_bound S hFe hb1nn hb1 ht hr hs
          have e2 := lem_fhatJ_bound S hind ht hr hs
          have e3 : ‖S.ψ (Sum.inr t)‖ ≤ A := lem_abs_le_sqrt_sum (fun t => S.ψ (Sum.inr t)) t
          have e4 : ‖S.κ r‖ ≤ B := lem_le_sqrt_one_sub S.κ S.normG hc.1
          have e5 : ‖S.ρ s‖ ≤ C := lem_le_sqrt_one_sub S.ρ S.normH hc.2
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
          calc _ = ‖S.ψ (Sum.inr t)‖ * ‖S.κ r‖ * ‖S.ρ s‖ *
                (‖S.Fhat (Sum.inr t) r s‖ * ‖S.FhatJ (Sum.inr t) r s‖) := rfl
            _ ≤ A * B * C * (b1 * 1) := by
                refine mul_le_mul (mul_le_mul (mul_le_mul e3 e4 (norm_nonneg _) (by positivity))
                  e5 (norm_nonneg _) (by positivity)) (mul_le_mul e1 e2 (norm_nonneg _) hb1nn)
                  (by positivity) (by positivity)
            _ = _ := by ring
        · have : ¬ (S.ψ (Sum.inr t) ≠ 0 ∧ S.κ r ≠ 0 ∧ S.ρ s ≠ 0) := hz
          simp only [this, ↓reduceIte]
          by_cases h1 : S.ψ (Sum.inr t) = 0
          · simp [hc, h1]
          · by_cases h2 : S.κ r = 0
            · simp [hc, h2]
            · have h3 : S.ρ s = 0 := by
                by_contra h3; exact hz ⟨h1, h2, h3⟩
              simp [hc, h3]
      · simp only [hc, ↓reduceIte, norm_zero]
        split_ifs <;> simp [hM])
  refine key.trans ?_
  have this := lem_card_prod_le S hDy hDz
  calc _ ≤ ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z) * (b1 * A * B * C) :=
        mul_le_mul_of_nonneg_right this hM
    _ = _ := by ring

private lemma lem_tail_eq
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh) :
    (∑ t : Fin S.sF, ∑ π : AddChar H ℂ, ∑ l : AddChar H ℂ, if π ≠ l then
        S.ψ (Sum.inr t) * S.κ (Sum.inl π) * S.ρ (Sum.inl l) *
          (S.Fhat (Sum.inr t) (Sum.inl π) (Sum.inl l) *
            S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inl l)) else 0) +
      (∑ t : Fin S.sF, ∑ r : Fin S.sG, ∑ l : AddChar H ℂ,
        S.ψ (Sum.inr t) * S.κ (Sum.inr r) * S.ρ (Sum.inl l) *
          (S.Fhat (Sum.inr t) (Sum.inr r) (Sum.inl l) *
            S.FhatJ (Sum.inr t) (Sum.inr r) (Sum.inl l))) +
      (∑ t : Fin S.sF, ∑ π : AddChar H ℂ, ∑ s : Fin S.sH,
        S.ψ (Sum.inr t) * S.κ (Sum.inl π) * S.ρ (Sum.inr s) *
          (S.Fhat (Sum.inr t) (Sum.inl π) (Sum.inr s) *
            S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inr s))) +
      (∑ t : Fin S.sF, ∑ r : Fin S.sG, ∑ s : Fin S.sH,
        S.ψ (Sum.inr t) * S.κ (Sum.inr r) * S.ρ (Sum.inr s) *
          (S.Fhat (Sum.inr t) (Sum.inr r) (Sum.inr s) *
            S.FhatJ (Sum.inr t) (Sum.inr r) (Sum.inr s))) =
    ∑ t : Fin S.sF, ∑ q : AddChar H ℂ ⊕ Fin S.sG, ∑ r : AddChar H ℂ ⊕ Fin S.sH,
      S.ψ (Sum.inr t) * S.κ q * S.ρ r * (S.Fhat (Sum.inr t) q r * S.FhatJ (Sum.inr t) q r) := by
  have v3 := (s9_vanishing_observations hunif hind S).2.2
  have e2 : (∑ t : Fin S.sF, ∑ π : AddChar H ℂ, ∑ l : AddChar H ℂ, if π ≠ l then
        S.ψ (Sum.inr t) * S.κ (Sum.inl π) * S.ρ (Sum.inl l) *
          (S.Fhat (Sum.inr t) (Sum.inl π) (Sum.inl l) *
            S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inl l)) else 0) =
      ∑ t : Fin S.sF, ∑ π : AddChar H ℂ, ∑ l : AddChar H ℂ,
        S.ψ (Sum.inr t) * S.κ (Sum.inl π) * S.ρ (Sum.inl l) *
          (S.Fhat (Sum.inr t) (Sum.inl π) (Sum.inl l) *
            S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inl l)) := by
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun π _ =>
      Finset.sum_congr rfl fun l _ => ?_
    by_cases hπ : π = l
    · subst hπ; simp [v3 t π]
    · simp [hπ]
  rw [e2]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

/-- Paper IV `lem:diagonal-small-beta` (Lemma 8.8, l. 4958-4985): if `∑_χ |ψ_χ κ_χ ρ_χ| ≤ 1 - τ` and
`∑_T |ψ_t|² ≤ η`, then `|𝔼 F g h| ≤ (1 - ε) max(β_{n-1,d-1,d'-1}, β_{n-1,d,d'})`. The relation
"`1 - τ + O_m(√η) ≤ 1 - τ/2 ≤ 1 - ε`" is the hypothesis `hhier` with the explicit `O_m` constant `C_m` of
`s9_bound_small_beta`. -/
theorem s9_diagonal_small_beta (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (hDy : ∀ a, 0 < (lawY μ).prob a) (hDz : ∀ a, 0 < (lawZ μ).prob a)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {b0 b1 τ ε η : ℝ} (hb0nn : 0 ≤ b0) (hb1nn : 0 ≤ b1)
    (hb0 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' ≤ ENNReal.ofReal b0)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1)
    (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (hsmall : ∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2 ≤ η)
    (hdiag : ∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ)‖ ≤ 1 - τ)
    (hhier : (1 - τ) + ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z) *
      Real.sqrt η ≤ 1 - ε) :
    ‖s7CorrF μ F g h‖ ≤ (1 - ε) * max b1 b0 := by
  classical
  have _ := hε1
  have _ := hη
  have hτ0 : 0 ≤ 1 - τ := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) hdiag
  set Cm : ℝ := (Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  have hsq0 : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  -- main term
  have hmain : ‖∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
      S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)‖ ≤ (1 - τ) * b0 := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
        S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)‖ ≤
        ‖S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ)‖ * b0 := fun χ => by
      by_cases hz : S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) = 0
      · rw [hz, zero_mul, norm_zero, zero_mul]
      · have hψ : S.ψ (Sum.inl χ) ≠ 0 := fun e => hz (by rw [e]; simp)
        have hκ : S.κ (Sum.inl χ) ≠ 0 := fun e => hz (by rw [e]; simp)
        have hρ : S.ρ (Sum.inl χ) ≠ 0 := fun e => hz (by rw [e]; simp)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (lem_fhat_chi_bound S hb0nn hb0 hψ hκ hρ) (norm_nonneg _)
    refine (Finset.sum_le_sum fun χ _ => h1 χ).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hdiag hb0nn
  -- tail
  have hψt : ∀ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ≤ Real.sqrt η := fun t =>
    (lem_abs_le_sqrt_sum (fun t => S.ψ (Sum.inr t)) t).trans (Real.sqrt_le_sqrt hsmall)
  have hκ1 : ∀ q, ‖S.κ q‖ ≤ 1 := fun q => by
    have := lem_abs_le_sqrt_sum S.κ q
    rwa [S.normG, Real.sqrt_one] at this
  have hρ1 : ∀ q, ‖S.ρ q‖ ≤ 1 := fun q => by
    have := lem_abs_le_sqrt_sum S.ρ q
    rwa [S.normH, Real.sqrt_one] at this
  have hM : 0 ≤ b1 * Real.sqrt η := by positivity
  have htail : ‖∑ t : Fin S.sF, ∑ q : AddChar H ℂ ⊕ Fin S.sG, ∑ r : AddChar H ℂ ⊕ Fin S.sH,
      S.ψ (Sum.inr t) * S.κ q * S.ρ r * (S.Fhat (Sum.inr t) q r * S.FhatJ (Sum.inr t) q r)‖ ≤
      Cm * (b1 * Real.sqrt η) := by
    have key := lem_triple_bound
      (fun (t : Fin S.sF) (q : AddChar H ℂ ⊕ Fin S.sG) (r : AddChar H ℂ ⊕ Fin S.sH) =>
        S.ψ (Sum.inr t) * S.κ q * S.ρ r * (S.Fhat (Sum.inr t) q r * S.FhatJ (Sum.inr t) q r))
      (fun t => S.ψ (Sum.inr t) ≠ 0) (fun q => S.κ q ≠ 0) (fun r => S.ρ r ≠ 0)
      (b1 * Real.sqrt η)
      (fun t q r => by
        by_cases hz : S.ψ (Sum.inr t) ≠ 0 ∧ S.κ q ≠ 0 ∧ S.ρ r ≠ 0
        · obtain ⟨ht, hq, hr⟩ := hz
          simp only [ht, hq, hr, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
          have e1 := lem_fhat_t_bound S hFe hb1nn hb1 ht hq hr
          have e2 := lem_fhatJ_bound S hind ht hq hr
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
          calc _ ≤ Real.sqrt η * 1 * 1 * (b1 * 1) :=
                mul_le_mul (mul_le_mul (mul_le_mul (hψt t) (hκ1 q) (norm_nonneg _) hsq0)
                  (hρ1 r) (norm_nonneg _) (by positivity))
                  (mul_le_mul e1 e2 (norm_nonneg _) hb1nn) (by positivity) (by positivity)
            _ = _ := by ring
        · have : ¬ (S.ψ (Sum.inr t) ≠ 0 ∧ S.κ q ≠ 0 ∧ S.ρ r ≠ 0) := hz
          simp only [this, ↓reduceIte]
          by_cases h1 : S.ψ (Sum.inr t) = 0
          · simp [h1]
          · by_cases h2 : S.κ q = 0
            · simp [h2]
            · have h3 : S.ρ r = 0 := by
                by_contra h3; exact hz ⟨h1, h2, h3⟩
              simp [h3])
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_right (lem_card_prod_le S hDy hDz) hM
  have hsplit : s7CorrF μ F g h =
      (∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
        S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)) +
      ∑ t : Fin S.sF, ∑ q : AddChar H ℂ ⊕ Fin S.sG, ∑ r : AddChar H ℂ ⊕ Fin S.sH,
        S.ψ (Sum.inr t) * S.κ q * S.ρ r * (S.Fhat (Sum.inr t) q r * S.FhatJ (Sum.inr t) q r) := by
    rw [← lem_tail_eq hunif hind S, s9_large_large_expansion hunif hind S]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hmx : max b1 b0 ≥ b0 := le_max_right _ _
  have hmx1 : max b1 b0 ≥ b1 := le_max_left _ _
  have h2 : (1 - τ) * b0 + Cm * (b1 * Real.sqrt η) ≤ ((1 - τ) + Cm * Real.sqrt η) * max b1 b0 := by
    nlinarith [mul_le_mul_of_nonneg_left hmx hτ0, mul_nonneg hCm0 hsq0,
      mul_le_mul_of_nonneg_left hmx1 (mul_nonneg hCm0 hsq0)]
  have h3 : ((1 - τ) + Cm * Real.sqrt η) * max b1 b0 ≤ (1 - ε) * max b1 b0 :=
    mul_le_mul_of_nonneg_right hhier (le_trans hb0nn hmx)
  linarith [hmain, htail]

private lemma lem_ftilde (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    {t : Fin S.sF} (ht : S.ψ (Sum.inr t) ≠ 0) (χ : AddChar H ℂ) :
    ∃ ft : X → ℂ, ft ∈ s7Perp (lawX μ) (embedSpan σ) ∧
      (lawX μ).expect (fun x => ‖ft x‖ ^ 2) = 1 ∧
      (∀ s, S.FhatJ (Sum.inr t) (Sum.inl χ) s =
        μ.cexpect (fun p => ft p.1 * (S.hJ s p.2.2 * star (χ (φ p.2.2))))) ∧
      (∀ r, S.FhatJ (Sum.inr t) r (Sum.inl χ) =
        μ.cexpect (fun p => ft p.1 * (S.gJ r p.2.1 * star (χ (γ p.2.1))))) := by
  obtain ⟨-, f', hf'⟩ := S.F_cc (Sum.inr t)
  have hperp : ∀ ψ : AddChar H ℂ, (lawX μ).cinner f' (fun x => ψ (σ x)) = 0 := fun ψ => by
    have := S.FJ_t t ψ
    rw [← hf', lem_rot_W1_cinner] at this
    exact this
  have hnorm : (lawX μ).cinner f' f' = 1 := by
    have := S.orthF_J (Sum.inr t) (Sum.inr t) ht ht
    rw [← hf', lem_rot_W1_cinner] at this
    simpa using this
  refine ⟨fun x => f' x * star (χ (σ x)), lem_perp_twist (lawX μ) σ f' hperp χ, ?_, ?_, ?_⟩
  · have h1 := cinner_self_eq (lawX μ) f'
    rw [hnorm] at h1
    have h2 : (lawX μ).expect (fun x => ‖f' x‖ ^ 2) = 1 := by exact_mod_cast h1.symm
    rw [← h2]
    unfold FinProb.expect
    refine Finset.sum_congr rfl fun x _ => ?_
    show (lawX μ).prob x * ‖f' x * star (χ (σ x))‖ ^ 2 = (lawX μ).prob x * ‖f' x‖ ^ 2
    rw [norm_mul, norm_star, AddChar.norm_apply, mul_one]
  · intro s
    unfold S9Svd3.FhatJ s8Corr1 FinProb.cexpect
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h0 : μ.prob p = 0
    · simp [h0]
    · have hs := lem_supp μ σ γ φ hunif h0
      have hpre : p.1 = s7Pre hμ p.2.1 p.2.2 := s7Pre_unique hμ (show p ∈ μ.support from h0)
      have e := lem_pw χ (σ p.1) (γ p.2.1) (φ p.2.2) hs
      rw [S.gJ_chi, ← hf']
      simp only [s8W1, ← hpre]
      rw [e]
      ring
  · intro r
    unfold S9Svd3.FhatJ s8Corr1 FinProb.cexpect
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h0 : μ.prob p = 0
    · simp [h0]
    · have hs := lem_supp μ σ γ φ hunif h0
      have hpre : p.1 = s7Pre hμ p.2.1 p.2.2 := s7Pre_unique hμ (show p ∈ μ.support from h0)
      have hs' : σ p.1 + φ p.2.2 + γ p.2.1 = 0 := by rw [add_right_comm]; exact hs
      have e := lem_pw χ (σ p.1) (φ p.2.2) (γ p.2.1) hs'
      rw [S.hJ_chi, ← hf']
      simp only [s8W1, ← hpre]
      rw [e]
      ring

omit [DecidableEq H] in
private lemma lem_mean_g (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh) (χ : AddChar H ℂ)
    {r : AddChar H ℂ ⊕ Fin S.sG} (hr : r ≠ Sum.inl χ) :
    (lawY μ).cexpect (fun y => S.gJ r y * star (χ (γ y))) = 0 := by
  rcases r with π | r
  · have hπ : π ≠ χ := fun e => hr (by rw [e])
    have := By.embed_orthonormal π χ
    simp only [hπ, ↓reduceIte] at this
    rw [S.gJ_chi]
    exact this
  · exact S.gJ_r r _ (Submodule.subset_span ⟨χ, rfl⟩)

private lemma lem_PT (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {c : ℝ}
    (hadd : ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ), f ∈ s7Perp (lawX μ) (embedSpan σ) →
      ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ ≤
        (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
          Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2))
    (χ : AddChar H ℂ) {t : Fin S.sF} (ht : S.ψ (Sum.inr t) ≠ 0) :
    c ≤ 1 ∧
    ‖∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        (if r = Sum.inl χ ∨ s = Sum.inl χ then
          S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s) else 0)‖ ≤
      (1 - c) * Real.sqrt
        (∑ r ∈ univ.filter (fun r : AddChar H ℂ ⊕ Fin S.sG => r ≠ Sum.inl χ),
            ‖S.ρ (Sum.inl χ) * (S.κ r * S.Fhat (Sum.inr t) r (Sum.inl χ))‖ ^ 2 +
          ∑ s ∈ univ.filter (fun s : AddChar H ℂ ⊕ Fin S.sH => s ≠ Sum.inl χ),
            ‖S.κ (Sum.inl χ) * (S.ρ s * S.Fhat (Sum.inr t) (Sum.inl χ) s)‖ ^ 2) := by
  classical
  obtain ⟨ft, hperp, hnorm, hL, hR⟩ := lem_ftilde S hunif ht χ
  set b : AddChar H ℂ ⊕ Fin S.sG → ℂ :=
    fun r => S.ρ (Sum.inl χ) * (S.κ r * S.Fhat (Sum.inr t) r (Sum.inl χ)) with hb
  set a : AddChar H ℂ ⊕ Fin S.sH → ℂ :=
    fun s => S.κ (Sum.inl χ) * (S.ρ s * S.Fhat (Sum.inr t) (Sum.inl χ) s) with ha
  set s1 := univ.filter (fun r : AddChar H ℂ ⊕ Fin S.sG => r ≠ Sum.inl χ) with hs1
  set s2 := univ.filter (fun s : AddChar H ℂ ⊕ Fin S.sH => s ≠ Sum.inl χ) with hs2
  set G : Y → ℂ := fun y => ∑ r ∈ s1, b r * (S.gJ r y * star (χ (γ y))) with hG
  set K : Z → ℂ := fun z => ∑ s ∈ s2, a s * (S.hJ s z * star (χ (φ z))) with hK
  have hG0 : (lawY μ).cexpect G = 0 := by
    rw [hG, lem_cexpect_sum]
    exact Finset.sum_eq_zero fun r hr => by
      rw [lem_mean_g S χ (Finset.mem_filter.1 hr).2, mul_zero]
  -- expectation form
  have hexp : μ.cexpect (fun p => ft p.1 * (G p.2.1 + K p.2.2)) =
      ∑ r ∈ s1, b r * S.FhatJ (Sum.inr t) r (Sum.inl χ) +
        ∑ s ∈ s2, a s * S.FhatJ (Sum.inr t) (Sum.inl χ) s := by
    have e1 : ∀ p : X × Y × Z, ft p.1 * (G p.2.1 + K p.2.2) =
        ∑ r ∈ s1, b r * (ft p.1 * (S.gJ r p.2.1 * star (χ (γ p.2.1)))) +
          ∑ s ∈ s2, a s * (ft p.1 * (S.hJ s p.2.2 * star (χ (φ p.2.2)))) := by
      intro p
      simp only [hG, hK, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun r _ => by ring
      · exact Finset.sum_congr rfl fun s _ => by ring
    simp only [e1]
    rw [lem_cexpect_add, lem_cexpect_sum, lem_cexpect_sum]
    congr 1
    · exact Finset.sum_congr rfl fun r _ => by rw [hR r]
    · exact Finset.sum_congr rfl fun s _ => by rw [hL s]
  -- the sum Σ'
  have hsum : ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        (if r = Sum.inl χ ∨ s = Sum.inl χ then
          S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s) else 0) =
      μ.cexpect (fun p => ft p.1 * (G p.2.1 + K p.2.2)) := by
    rw [hexp]
    have v3 : S.FhatJ (Sum.inr t) (Sum.inl χ) (Sum.inl χ) = 0 :=
      (s9_vanishing_observations hunif hind S).2.2 t χ
    rw [lem_sum_split (Sum.inl χ)]
    have e1 : ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        (if (Sum.inl χ : AddChar H ℂ ⊕ Fin S.sG) = Sum.inl χ ∨ s = Sum.inl χ then
          S.κ (Sum.inl χ) * S.ρ s *
            (S.Fhat (Sum.inr t) (Sum.inl χ) s * S.FhatJ (Sum.inr t) (Sum.inl χ) s) else 0) =
        ∑ s ∈ s2, a s * S.FhatJ (Sum.inr t) (Sum.inl χ) s := by
      simp only [true_or, ↓reduceIte]
      rw [lem_sum_split (Sum.inl χ : AddChar H ℂ ⊕ Fin S.sH)]
      rw [v3, mul_zero, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [ha]
      ring
    have e2 : ∑ r ∈ s1, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        (if r = Sum.inl χ ∨ s = Sum.inl χ then
          S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s) else 0) =
        ∑ r ∈ s1, b r * S.FhatJ (Sum.inr t) r (Sum.inl χ) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' : r ≠ Sum.inl χ := (Finset.mem_filter.1 hr).2
      simp only [hr', false_or]
      rw [Finset.sum_ite_eq' univ (Sum.inl χ : AddChar H ℂ ⊕ Fin S.sH)]
      simp only [Finset.mem_univ, ↓reduceIte, hb]
      ring
    rw [e1, e2]
    ring
  have hB : μ.expect (fun p => ‖G p.2.1 + K p.2.2‖ ^ 2) =
      ∑ r ∈ s1, ‖b r‖ ^ 2 + ∑ s ∈ s2, ‖a s‖ ^ 2 := by
    rw [lem_sq_expect_yz μ hind G K, lem_sq_indep (lawY μ) (lawZ μ) G K hG0]
    congr 1
    · exact lem_orth_sum_norm (lawY μ) S.gJ s1 b (fun y => star (χ (γ y)))
        (fun y => by rw [norm_star, AddChar.norm_apply])
        (fun p _ q _ hp hq => S.orthG_J p q (fun h0 => hp (by simp [hb, h0]))
          (fun h0 => hq (by simp [hb, h0])))
    · exact lem_orth_sum_norm (lawZ μ) S.hJ s2 a (fun z => star (χ (φ z)))
        (fun y => by rw [norm_star, AddChar.norm_apply])
        (fun p _ q _ hp hq => S.orthH_J p q (fun h0 => hp (by simp [ha, h0]))
          (fun h0 => hq (by simp [ha, h0])))
  have h := hadd ft G K hperp
  rw [hnorm, hB, ← hsum, Real.sqrt_one, mul_one] at h
  refine ⟨?_, h⟩
  have h1 := hadd ft (fun _ => 1) (fun _ => 0) hperp
  have h2 : μ.expect (fun p : X × Y × Z => ‖(1 : ℂ) + 0‖ ^ 2) = 1 := by
    simp [FinProb.expect, μ.sum_eq_one]
  rw [hnorm, Real.sqrt_one, mul_one] at h1
  rw [h2, Real.sqrt_one, mul_one] at h1
  linarith [norm_nonneg (μ.cexpect fun p => ft p.1 * ((1 : ℂ) + 0))]

theorem s9_bound_additivebase_beta_of_additive_base
    (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {c : ℝ} (hc : 0 < c)
    (hadd : ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ), f ∈ s7Perp (lawX μ) (embedSpan σ) →
      ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ ≤
        (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
          Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2))
    (χs : AddChar H ℂ) {b1 : ℝ} (hb1nn : 0 ≤ b1)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1) :
    ‖∑ t : Fin S.sF, ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        if r = Sum.inl χs ∨ s = Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0‖ ≤
      (1 - c) * b1 * Real.sqrt (∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2) *
        Real.sqrt (‖S.κ (Sum.inl χs)‖ ^ 2 *
            (∑ s ∈ Finset.univ.filter (fun s : AddChar H ℂ ⊕ Fin S.sH => s ≠ Sum.inl χs),
              ‖S.ρ s‖ ^ 2) +
          ‖S.ρ (Sum.inl χs)‖ ^ 2 *
            (∑ r ∈ Finset.univ.filter (fun r : AddChar H ℂ ⊕ Fin S.sG => r ≠ Sum.inl χs),
              ‖S.κ r‖ ^ 2)) := by
  classical
  have _ := hc
  have _ := hDx
  have _ := hDy
  have _ := hDz
  set Sg : Fin S.sF → ℂ := fun t => ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
    (if r = Sum.inl χs ∨ s = Sum.inl χs then
      S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s) else 0) with hSg
  have hterm : ∀ t : Fin S.sF, (∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
      if r = Sum.inl χs ∨ s = Sum.inl χs then
        S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
      else 0) = S.ψ (Sum.inr t) * Sg t := by
    intro t
    rw [hSg]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · ring
    · simp
  simp only [hterm]
  set A := Real.sqrt (∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2) with hA
  set Qtot := ‖S.κ (Sum.inl χs)‖ ^ 2 *
            (∑ s ∈ Finset.univ.filter (fun s : AddChar H ℂ ⊕ Fin S.sH => s ≠ Sum.inl χs),
              ‖S.ρ s‖ ^ 2) +
          ‖S.ρ (Sum.inl χs)‖ ^ 2 *
            (∑ r ∈ Finset.univ.filter (fun r : AddChar H ℂ ⊕ Fin S.sG => r ≠ Sum.inl χs),
              ‖S.κ r‖ ^ 2) with hQtot
  by_cases hT : ∃ t, S.ψ (Sum.inr t) ≠ 0
  swap
  · push Not at hT
    have : ∑ t : Fin S.sF, S.ψ (Sum.inr t) * Sg t = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [hT t, zero_mul]
    rw [this, norm_zero]
    have hA0 : A = 0 := by
      rw [hA]
      simp [hT]
    rw [hA0]
    simp
  obtain ⟨t0, ht0⟩ := hT
  have hc1 : c ≤ 1 := (lem_PT S hunif hind hadd χs ht0).1
  have hc1' : 0 ≤ 1 - c := by linarith
  set s1 := Finset.univ.filter (fun r : AddChar H ℂ ⊕ Fin S.sG => r ≠ Sum.inl χs) with hs1
  set s2 := Finset.univ.filter (fun s : AddChar H ℂ ⊕ Fin S.sH => s ≠ Sum.inl χs) with hs2
  set T' := Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0) with hT'
  set Q : Fin S.sF → ℝ := fun t =>
    ∑ r ∈ s1, ‖S.ρ (Sum.inl χs) * (S.κ r * S.Fhat (Sum.inr t) r (Sum.inl χs))‖ ^ 2 +
      ∑ s ∈ s2, ‖S.κ (Sum.inl χs) * (S.ρ s * S.Fhat (Sum.inr t) (Sum.inl χs) s)‖ ^ 2 with hQ
  have hQ0 : ∀ t, 0 ≤ Q t := fun t => by
    rw [hQ]; positivity
  have hpt : ∀ t, ‖S.ψ (Sum.inr t)‖ * ‖Sg t‖ ≤ ‖S.ψ (Sum.inr t)‖ * ((1 - c) * Real.sqrt (Q t)) := by
    intro t
    by_cases ht : S.ψ (Sum.inr t) = 0
    · simp [ht]
    · exact mul_le_mul_of_nonneg_left (lem_PT S hunif hind hadd χs ht).2 (norm_nonneg _)
  have hsum1 : ‖∑ t, S.ψ (Sum.inr t) * Sg t‖ ≤
      ∑ t, ‖S.ψ (Sum.inr t)‖ * ((1 - c) * Real.sqrt (Q t)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => by rw [norm_mul]; exact hpt t)
  have hsum2 : ∑ t, ‖S.ψ (Sum.inr t)‖ * ((1 - c) * Real.sqrt (Q t)) =
      (1 - c) * ∑ t ∈ T', ‖S.ψ (Sum.inr t)‖ * Real.sqrt (Q t) := by
    rw [Finset.mul_sum, hT', Finset.sum_filter_of_ne]
    · exact Finset.sum_congr rfl fun t _ => by ring
    · intro t _ h0 h1
      exact h0 (by rw [h1]; simp)
  have hcs : ∑ t ∈ T', ‖S.ψ (Sum.inr t)‖ * Real.sqrt (Q t) ≤
      Real.sqrt (∑ t ∈ T', ‖S.ψ (Sum.inr t)‖ ^ 2) * Real.sqrt (∑ t ∈ T', Q t) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt T' (fun t => ‖S.ψ (Sum.inr t)‖) (fun t => Real.sqrt (Q t))
    simpa [Real.sq_sqrt (hQ0 _)] using this
  have hA' : Real.sqrt (∑ t ∈ T', ‖S.ψ (Sum.inr t)‖ ^ 2) ≤ A :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _))
  have hQT : ∑ t ∈ T', Q t ≤ b1 ^ 2 * Qtot := by
    have hX : ∀ r : AddChar H ℂ ⊕ Fin S.sG, ∑ t ∈ T',
        ‖S.ρ (Sum.inl χs) * (S.κ r * S.Fhat (Sum.inr t) r (Sum.inl χs))‖ ^ 2 ≤
        b1 ^ 2 * (‖S.ρ (Sum.inl χs)‖ ^ 2 * ‖S.κ r‖ ^ 2) := fun r => by
      have e : ∀ t, ‖S.ρ (Sum.inl χs) * (S.κ r * S.Fhat (Sum.inr t) r (Sum.inl χs))‖ ^ 2 =
          (‖S.ρ (Sum.inl χs)‖ ^ 2 * ‖S.κ r‖ ^ 2) * ‖S.Fhat (Sum.inr t) r (Sum.inl χs)‖ ^ 2 :=
        fun t => by rw [norm_mul, norm_mul]; ring
      simp only [e, ← Finset.mul_sum]
      by_cases hρ : S.ρ (Sum.inl χs) = 0
      · simp [hρ]
      · by_cases hκ : S.κ r = 0
        · simp [hκ]
        · have := lem_comb2 S hFe χs hρ hb1nn hb1 r hκ
          nlinarith [mul_nonneg (sq_nonneg ‖S.ρ (Sum.inl χs)‖) (sq_nonneg ‖S.κ r‖)]
    have hY : ∀ s : AddChar H ℂ ⊕ Fin S.sH, ∑ t ∈ T',
        ‖S.κ (Sum.inl χs) * (S.ρ s * S.Fhat (Sum.inr t) (Sum.inl χs) s)‖ ^ 2 ≤
        b1 ^ 2 * (‖S.κ (Sum.inl χs)‖ ^ 2 * ‖S.ρ s‖ ^ 2) := fun s => by
      have e : ∀ t, ‖S.κ (Sum.inl χs) * (S.ρ s * S.Fhat (Sum.inr t) (Sum.inl χs) s)‖ ^ 2 =
          (‖S.κ (Sum.inl χs)‖ ^ 2 * ‖S.ρ s‖ ^ 2) * ‖S.Fhat (Sum.inr t) (Sum.inl χs) s‖ ^ 2 :=
        fun t => by rw [norm_mul, norm_mul]; ring
      simp only [e, ← Finset.mul_sum]
      by_cases hκ : S.κ (Sum.inl χs) = 0
      · simp [hκ]
      · by_cases hρ : S.ρ s = 0
        · simp [hρ]
        · have := lem_comb1 S hFe χs hκ hb1nn hb1 s hρ
          nlinarith [mul_nonneg (sq_nonneg ‖S.κ (Sum.inl χs)‖) (sq_nonneg ‖S.ρ s‖)]
    have e1 : ∑ t ∈ T', Q t =
        ∑ r ∈ s1, ∑ t ∈ T', ‖S.ρ (Sum.inl χs) * (S.κ r * S.Fhat (Sum.inr t) r (Sum.inl χs))‖ ^ 2 +
        ∑ s ∈ s2, ∑ t ∈ T',
          ‖S.κ (Sum.inl χs) * (S.ρ s * S.Fhat (Sum.inr t) (Sum.inl χs) s)‖ ^ 2 := by
      simp only [hQ, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_comm
    rw [e1]
    have h1 := Finset.sum_le_sum (fun r (_ : r ∈ s1) => hX r)
    have h2 := Finset.sum_le_sum (fun s (_ : s ∈ s2) => hY s)
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h2
    rw [hQtot]
    nlinarith [h1, h2]
  have hsq : Real.sqrt (∑ t ∈ T', Q t) ≤ b1 * Real.sqrt Qtot := by
    calc Real.sqrt (∑ t ∈ T', Q t) ≤ Real.sqrt (b1 ^ 2 * Qtot) := Real.sqrt_le_sqrt hQT
      _ = b1 * Real.sqrt Qtot := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb1nn]
  have hQtot0 : 0 ≤ Real.sqrt Qtot := Real.sqrt_nonneg _
  have hfin : ∑ t ∈ T', ‖S.ψ (Sum.inr t)‖ * Real.sqrt (Q t) ≤ A * (b1 * Real.sqrt Qtot) :=
    hcs.trans (mul_le_mul hA' hsq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc ‖∑ t, S.ψ (Sum.inr t) * Sg t‖ ≤ (1 - c) * ∑ t ∈ T', ‖S.ψ (Sum.inr t)‖ * Real.sqrt (Q t) :=
        hsum1.trans (le_of_eq hsum2)
    _ ≤ (1 - c) * (A * (b1 * Real.sqrt Qtot)) := mul_le_mul_of_nonneg_left hfin hc1'
    _ = _ := by ring

private lemma asm_sqrt_ab {a b : ℝ} (ha : 0 ≤ 1 - a) (hb : 0 ≤ 1 - b) :
    Real.sqrt (1 - a) * Real.sqrt (1 - b) ≤ (2 - a - b) / 2 := by
  rw [← Real.sqrt_mul ha]
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  nlinarith [sq_nonneg (a - b)]

private lemma asm_cs {x1 x2 y1 y2 : ℝ} : (x1 * y1 + x2 * y2) ^ 2 ≤ (x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2) := by
  nlinarith [sq_nonneg (x1 * y2 - x2 * y1)]

private lemma asm_poly {c E : ℝ} : 1 - c / 2 * E ≤ (1 - c / 4 * E) ^ 2 := by
  nlinarith [sq_nonneg (c * E)]

private lemma asm_alg {a b Pa Tn K1 η τ Cm c b0 b1 : ℝ} (hPa : 0 ≤ Pa) (hTn : 0 ≤ Tn)
    (hK1 : 0 ≤ K1) (hsum : Pa + Tn = 1) (hTη : Tn ≤ η) (hη : 0 ≤ η) (hτ : 0 < τ)
    (hCm : 0 ≤ Cm) (hc : 0 < c) (hc1 : c ≤ 1) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (ha1 : a ≤ 1) (hb1' : b ≤ 1) (ha : 1 - 6 * τ ≤ a) (hb : 1 - 6 * τ ≤ b)
    (hK : K1 + (a * (1 - b) + b * (1 - a)) ≤ 1)
    (hhier : 1 / 2 + 4 * (2 * Cm) / c * Real.sqrt η ≤ 1 - 6 * τ) :
    b0 * Real.sqrt Pa * Real.sqrt K1 +
      Cm * b1 * Real.sqrt Tn * Real.sqrt (1 - a) * Real.sqrt (1 - b) +
      (1 - c) * b1 * Real.sqrt Tn * Real.sqrt (a * (1 - b) + b * (1 - a)) ≤
      max ((1 - c / 2) * b1) b0 := by
  set M := max ((1 - c / 2) * b1) b0 with hM
  have hMb0 : b0 ≤ M := le_max_right _ _
  have hMb1 : (1 - c / 2) * b1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := hb0.trans hMb0
  set E := a * (1 - b) + b * (1 - a) with hE
  have hsη : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  have hη' : 0 ≤ Cm * Real.sqrt η := mul_nonneg hCm hsη
  have hτ6 : 6 * τ ≤ 1 / 2 := by
    have : 0 ≤ 4 * (2 * Cm) / c * Real.sqrt η :=
      mul_nonneg (div_nonneg (by positivity) hc.le) hsη
    linarith
  have ha0 : 0 ≤ a := by nlinarith
  have hb0' : 0 ≤ b := by nlinarith
  -- calculus
  have hcalc : 0 ≤ a + b - 2 * a * b - 8 * (2 * Cm) / c * Real.sqrt η * (2 - a - b) := by
    rcases hη.eq_or_lt with h0 | hpos
    · rw [← h0, Real.sqrt_zero]
      nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1')]
    · exact s9_bound_calculus hτ hpos hc (by positivity) hhier ha ha1 hb hb1'
  have h2ab : 0 ≤ 2 - a - b := by linarith
  have hE0 : 0 ≤ E := by
    have h1 := mul_nonneg ha0 (sub_nonneg.2 hb1')
    have h2 := mul_nonneg hb0' (sub_nonneg.2 ha1)
    rw [hE]
    linarith
  have hE1 : E ≤ 1 := by linarith
  -- key: c E / 4 ≥ Cm √η (2-a-b)
  have hkey : Cm * Real.sqrt η * (2 - a - b) ≤ c / 4 * E := by
    have h1 : 8 * (2 * Cm) / c * Real.sqrt η * (2 - a - b) = 16 * (Cm * Real.sqrt η * (2 - a - b)) / c := by
      field_simp; ring
    rw [h1] at hcalc
    have h3 : 16 * (Cm * Real.sqrt η * (2 - a - b)) / c ≤ E := by
      have : E = a + b - 2 * a * b := by rw [hE]; ring
      linarith
    rw [div_le_iff₀ hc] at h3
    nlinarith [mul_nonneg hη' h2ab]
  -- u, s
  set s := Real.sqrt (1 - c / 2) with hs
  have hu0 : 0 ≤ 1 - c / 2 := by linarith
  have hs2 : s ^ 2 = 1 - c / 2 := Real.sq_sqrt hu0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by nlinarith
  have hshalf : 1 / 2 ≤ s ^ 2 := by linarith
  have hcs : 1 - c ≤ s * s ^ 2 := by
    have : 1 - c = 2 * s ^ 2 - 1 := by linarith
    rw [this]
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs1), sq_nonneg (s - 1), mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hs1)]
  have hT3 : (1 - c) * b1 ≤ s * M := by
    calc (1 - c) * b1 ≤ (s * s ^ 2) * b1 := mul_le_mul_of_nonneg_right hcs hb1
      _ = s * ((1 - c / 2) * b1) := by rw [hs2]; ring
      _ ≤ s * M := mul_le_mul_of_nonneg_left hMb1 hs0
  have hb1M : b1 ≤ 2 * M := by
    have := mul_nonneg hb1 (sub_nonneg.2 hc1)
    linarith
  -- sqrt facts
  have hsTn : Real.sqrt Tn ≤ Real.sqrt η := Real.sqrt_le_sqrt hTη
  have hab : Real.sqrt (1 - a) * Real.sqrt (1 - b) ≤ (2 - a - b) / 2 := by
    exact asm_sqrt_ab (by linarith) (by linarith)
  have hsa : 0 ≤ Real.sqrt (1 - a) := Real.sqrt_nonneg _
  have hsb : 0 ≤ Real.sqrt (1 - b) := Real.sqrt_nonneg _
  have hT2 : Cm * b1 * Real.sqrt Tn * Real.sqrt (1 - a) * Real.sqrt (1 - b) ≤
      M * (Cm * Real.sqrt η * (2 - a - b)) := by
    have hp : 0 ≤ Real.sqrt Tn := Real.sqrt_nonneg _
    calc Cm * b1 * Real.sqrt Tn * Real.sqrt (1 - a) * Real.sqrt (1 - b)
        = (Cm * b1) * Real.sqrt Tn * (Real.sqrt (1 - a) * Real.sqrt (1 - b)) := by ring
      _ ≤ (Cm * (2 * M)) * Real.sqrt η * ((2 - a - b) / 2) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hb1M hCm) hsTn hp
            (by positivity)) hab (by positivity) (by positivity)
      _ = _ := by ring
  have hT1 : b0 * Real.sqrt Pa * Real.sqrt K1 ≤ M * (Real.sqrt Pa * Real.sqrt K1) := by
    calc _ = b0 * (Real.sqrt Pa * Real.sqrt K1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hMb0 (by positivity)
  have hT3' : (1 - c) * b1 * Real.sqrt Tn * Real.sqrt E ≤
      M * (s * Real.sqrt Tn * Real.sqrt E) := by
    calc _ = ((1 - c) * b1) * (Real.sqrt Tn * Real.sqrt E) := by ring
      _ ≤ (s * M) * (Real.sqrt Tn * Real.sqrt E) :=
          mul_le_mul_of_nonneg_right hT3 (by positivity)
      _ = _ := by ring
  -- Cauchy-Schwarz
  have hCS : Real.sqrt Pa * Real.sqrt K1 + s * Real.sqrt Tn * Real.sqrt E ≤ 1 - c / 4 * E := by
    set x1 := Real.sqrt Pa
    set x2 := Real.sqrt Tn
    set y1 := Real.sqrt K1
    set y2 := s * Real.sqrt E
    have e1 : x1 ^ 2 = Pa := Real.sq_sqrt hPa
    have e2 : x2 ^ 2 = Tn := Real.sq_sqrt hTn
    have e3 : y1 ^ 2 = K1 := Real.sq_sqrt hK1
    have e4 : y2 ^ 2 = (1 - c / 2) * E := by
      rw [mul_pow, hs2, Real.sq_sqrt hE0]
    have hx : 0 ≤ x1 * y1 + x2 * y2 := by positivity
    have hsq : (x1 * y1 + x2 * y2) ^ 2 ≤ 1 - c / 2 * E := by
      have : (x1 * y1 + x2 * y2) ^ 2 ≤ (x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2) := asm_cs
      rw [e1, e2, e3, e4, hsum, one_mul] at this
      have e5 : K1 + (1 - c / 2) * E = (K1 + E) - c / 2 * E := by ring
      linarith
    have hrhs : (1 - c / 2 * E) ≤ (1 - c / 4 * E) ^ 2 := asm_poly
    have h0 : 0 ≤ 1 - c / 4 * E := by
      have := mul_le_mul hc1 hE1 hE0 zero_le_one
      linarith
    have h5 : x1 * y1 + x2 * y2 ≤ 1 - c / 4 * E :=
      (pow_le_pow_iff_left₀ hx h0 two_ne_zero).1 (hsq.trans hrhs)
    calc x1 * y1 + s * x2 * Real.sqrt E = x1 * y1 + x2 * y2 := by ring
      _ ≤ _ := h5
  have hfin : M * (Real.sqrt Pa * Real.sqrt K1 + s * Real.sqrt Tn * Real.sqrt E) ≤
      M * (1 - c / 4 * E) := mul_le_mul_of_nonneg_left hCS hM0
  have hk := mul_le_mul_of_nonneg_left hkey hM0
  have hfin' : M * (Real.sqrt Pa * Real.sqrt K1) + M * (s * Real.sqrt Tn * Real.sqrt E) ≤
      M * (1 - c / 4 * E) := by rw [← mul_add]; exact hfin
  have hex : M * (1 - c / 4 * E) + M * (c / 4 * E) = M := by ring
  linarith [hT1, hT2, hT3', hfin', hk, hex]
private lemma asm_sq_lb {x τ : ℝ} (h : 1 - 3 * τ ≤ x) (h0 : 0 ≤ 1 - 3 * τ) : 1 - 6 * τ ≤ x ^ 2 := by
  nlinarith [mul_le_mul h h h0 (h0.trans h), sq_nonneg τ]

private lemma asm_sq_le_one {x : ℝ} (h : x ≤ 1) (h0 : 0 ≤ x) : x ^ 2 ≤ 1 := by nlinarith

private lemma asm_k1 {ι : Type} [Fintype ι] [DecidableEq ι] (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hv : ∀ i, 0 ≤ v i) (hU : ∑ i, u i ≤ 1) (hV : ∑ i, v i ≤ 1) (x : ι) :
    ∑ i, u i * v i ≤ u x * v x + (1 - u x) * (1 - v x) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hUe : ∑ i ∈ Finset.univ.erase x, u i = ∑ i, u i - u x := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]; ring
  have hVe : ∑ i ∈ Finset.univ.erase x, v i = ∑ i, v i - v x := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]; ring
  have h1 : ∑ i ∈ Finset.univ.erase x, u i * v i ≤
      (∑ i ∈ Finset.univ.erase x, u i) * ∑ i ∈ Finset.univ.erase x, v i := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := v) (fun i _ => hv i) hi) (hu i)
  have hUn : 0 ≤ ∑ i ∈ Finset.univ.erase x, u i := Finset.sum_nonneg fun i _ => hu i
  have hVn : 0 ≤ ∑ i ∈ Finset.univ.erase x, v i := Finset.sum_nonneg fun i _ => hv i
  rw [hUe] at h1 hUn
  rw [hVe] at h1 hVn
  have h2 : (∑ i, u i - u x) * (∑ i, v i - v x) ≤ (1 - u x) * (1 - v x) :=
    mul_le_mul (by linarith) (by linarith) hVn (by linarith)
  linarith

private lemma asm_filter_sum {P : Type} [Fintype P] [DecidableEq P] (κ : P → ℂ)
    (h1 : ∑ p, ‖κ p‖ ^ 2 = 1) (p0 : P) :
    ∑ p ∈ Finset.univ.filter (fun p => p ≠ p0), ‖κ p‖ ^ 2 = 1 - ‖κ p0‖ ^ 2 := by
  have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ≠ p0) (fun p => ‖κ p‖ ^ 2)
  simp only [not_not, Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton] at this
  linarith

/-- Paper IV `lem:reduce-beta#assemble-bound` (l. 5130-5203): in the case `∑_χ |ψ_χκ_χρ_χ| > 1 - τ` with the
dominant `χ*` (`|κ_{χ*}|, |ρ_{χ*}| ≥ 1 - 3τ`), `|𝔼 F g h| ≤ β'' := max((1 - c/2) b₁, b₀)`. The
parameter relation is `hhier` (`s9_bound_calculus`) with the constant `2 C_m`: the third term of the
assembly is bounded with `b₁` (Lemma 8.10; the printed l. 5141 has `β_{n-1,d,d'}`, a typo), and
`b₁ ≤ β''/(1 - c/2) ≤ 2 β''`. `hc1 : c ≤ 1`, `3τ ≤ 1` are typing hypotheses (`1 - c ≥ 0`, `1 - 3τ ≥ 0`). -/
theorem s9_assemble_bound_of_additive_base (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hadd : ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ), f ∈ s7Perp (lawX μ) (embedSpan σ) →
      ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ ≤
        (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
          Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2))
    {b0 b1 τ η : ℝ} (hb0nn : 0 ≤ b0) (hb1nn : 0 ≤ b1) (hτ : 0 < τ) (hτ3 : 3 * τ ≤ 1) (hη : 0 ≤ η)
    (hb0 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) d d' ≤ ENNReal.ofReal b0)
    (hb1 : s7Beta μ hμ Bx.u By.u Bz.u (n - 1) (d - 1) (d' - 1) ≤ ENNReal.ofReal b1)
    (hsmall : ∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2 ≤ η)
    (χs : AddChar H ℂ) (hκs : 1 - 3 * τ ≤ ‖S.κ (Sum.inl χs)‖)
    (hρs : 1 - 3 * τ ≤ ‖S.ρ (Sum.inl χs)‖)
    (hhier : 1 / 2 + 4 * (2 * ((Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z)) / c *
      Real.sqrt η ≤ 1 - 6 * τ) :
    ‖s7CorrF μ F g h‖ ≤ max ((1 - c / 2) * b1) b0 := by
  classical
  have _ := hDx
  have hm := s9_bound_main_term S hb0nn hb0
  have hs := s9_bound_small_beta S hFe hDy hDz hind χs hb1nn hb1
  have ha := s9_bound_additivebase_beta_of_additive_base S hFe hDx hDy hDz hunif hind hc hadd χs
    hb1nn hb1
  rw [asm_filter_sum S.ρ S.normH, asm_filter_sum S.κ S.normG] at ha
  set a := ‖S.κ (Sum.inl χs)‖ ^ 2 with hadef
  set b := ‖S.ρ (Sum.inl χs)‖ ^ 2 with hbdef
  have hsplit : s7CorrF μ F g h =
      (∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
        S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)) +
      ((∑ t : Fin S.sF, ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        if r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0) +
      (∑ t : Fin S.sF, ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        if r = Sum.inl χs ∨ s = Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0)) := by
    rw [← Finset.sum_add_distrib]
    have e : ∀ (t : Fin S.sF) (r : AddChar H ℂ ⊕ Fin S.sG) (s : AddChar H ℂ ⊕ Fin S.sH),
        S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s) =
        (if r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0) +
        (if r = Sum.inl χs ∨ s = Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0) := fun t r s => by
      by_cases h1 : r = Sum.inl χs ∨ s = Sum.inl χs
      · have : ¬ (r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs) := by tauto
        simp [this]
      · have : r ≠ Sum.inl χs ∧ s ≠ Sum.inl χs := by tauto
        simp [this]
    have : s7CorrF μ F g h = (∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) *
        S.ρ (Sum.inl χ) * S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)) +
        ∑ t : Fin S.sF, ∑ q : AddChar H ℂ ⊕ Fin S.sG, ∑ r : AddChar H ℂ ⊕ Fin S.sH,
          S.ψ (Sum.inr t) * S.κ q * S.ρ r *
            (S.Fhat (Sum.inr t) q r * S.FhatJ (Sum.inr t) q r) := by
      rw [← lem_tail_eq hunif hind S, s9_large_large_expansion hunif hind S]
      ring
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => e t r s
  rw [hsplit]
  have key3 : ∀ x y z : ℂ, ‖x + (y + z)‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := fun x y z => by
    have := norm_add_le x (y + z)
    have := norm_add_le y z
    linarith
  refine (key3 _ _ _).trans ?_
  -- quantities
  set Cm : ℝ := (Fintype.card (Y × Z) : ℝ) * Fintype.card Y * Fintype.card Z with hCm
  set Pa : ℝ := ∑ χ : AddChar H ℂ, ‖S.ψ (Sum.inl χ)‖ ^ 2 with hPa
  set Tn : ℝ := ∑ t : Fin S.sF, ‖S.ψ (Sum.inr t)‖ ^ 2 with hTn
  set K1 : ℝ := ∑ χ : AddChar H ℂ, ‖S.κ (Sum.inl χ)‖ ^ 2 * ‖S.ρ (Sum.inl χ)‖ ^ 2 with hK1
  have hsum : Pa + Tn = 1 := by
    have := S.normF
    rw [Fintype.sum_sum_type] at this
    exact this
  have hUle : ∑ χ : AddChar H ℂ, ‖S.κ (Sum.inl χ)‖ ^ 2 ≤ 1 := by
    have := S.normG
    rw [Fintype.sum_sum_type] at this
    have : 0 ≤ ∑ t : Fin S.sG, ‖S.κ (Sum.inr t)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith [S.normG, Fintype.sum_sum_type (fun p => ‖S.κ p‖ ^ 2)]
  have hVle : ∑ χ : AddChar H ℂ, ‖S.ρ (Sum.inl χ)‖ ^ 2 ≤ 1 := by
    have : 0 ≤ ∑ t : Fin S.sH, ‖S.ρ (Sum.inr t)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith [S.normH, Fintype.sum_sum_type (fun p => ‖S.ρ p‖ ^ 2)]
  have hK1le : K1 + (a * (1 - b) + b * (1 - a)) ≤ 1 := by
    have := asm_k1 (fun χ : AddChar H ℂ => ‖S.κ (Sum.inl χ)‖ ^ 2)
      (fun χ : AddChar H ℂ => ‖S.ρ (Sum.inl χ)‖ ^ 2) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
      hUle hVle χs
    have h2 : K1 ≤ a * b + (1 - a) * (1 - b) := this
    have h3 : a * b + (1 - a) * (1 - b) + (a * (1 - b) + b * (1 - a)) = 1 := by ring
    linarith
  have hk1nn : 0 ≤ K1 := Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have ha1 : a ≤ 1 := by
    have := lem_abs_le_sqrt_sum S.κ (Sum.inl χs)
    rw [S.normG, Real.sqrt_one] at this
    exact asm_sq_le_one this (norm_nonneg _)
  have hb1' : b ≤ 1 := by
    have := lem_abs_le_sqrt_sum S.ρ (Sum.inl χs)
    rw [S.normH, Real.sqrt_one] at this
    exact asm_sq_le_one this (norm_nonneg _)
  have haτ : 1 - 6 * τ ≤ a := by
    exact asm_sq_lb hκs (by linarith)
  have hbτ : 1 - 6 * τ ≤ b := by
    exact asm_sq_lb hρs (by linarith)
  have halg := asm_alg (a := a) (b := b) (Pa := Pa) (Tn := Tn) (K1 := K1) (η := η) (τ := τ)
    (Cm := Cm) (c := c) (b0 := b0) (b1 := b1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) hk1nn hsum hsmall hη hτ (by positivity) hc hc1
    hb0nn hb1nn ha1 hb1' haτ hbτ hK1le hhier
  have ha' : ‖∑ t : Fin S.sF, ∑ r : AddChar H ℂ ⊕ Fin S.sG, ∑ s : AddChar H ℂ ⊕ Fin S.sH,
        if r = Sum.inl χs ∨ s = Sum.inl χs then
          S.ψ (Sum.inr t) * S.κ r * S.ρ s * (S.Fhat (Sum.inr t) r s * S.FhatJ (Sum.inr t) r s)
        else 0‖ ≤ (1 - c) * b1 * Real.sqrt Tn * Real.sqrt (a * (1 - b) + b * (1 - a)) := ha
  linarith [hm, hs, ha', halg]

end S9Lemmas

end TrackB
end RestrictedPolynomials
end
