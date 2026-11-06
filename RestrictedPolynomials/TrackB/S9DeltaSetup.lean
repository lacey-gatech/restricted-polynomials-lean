module

public import RestrictedPolynomials.TrackB.S8Svd
public import RestrictedPolynomials.TrackB.S7Beta

/-!
# Track B: the setting of Lemma 9.3 (`delta_inductive`)

Source: paper IV (arXiv:2307.16248v2 `writeup_stability.tex`), Section 9.2-9.3
(l. 5276-5445). The SVD data of eq. `delta_1` (Claims 9.4, 9.5), the level-`n-1` coefficient bounds,
the choice of the coordinate `j` (eq. `choose_j_in_delta`) and Claim 9.7. The extremal triple of
`#extremal-triple` is in `S9DeltaExtremal`.
-/

@[expose] public section

open Finset
open scoped ENNReal

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S9dSetup
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {K₁ K₂ : Type}

/-- The data of eq. `delta_1` (l. 5361-5374): the three singular value decompositions of unit
`F ∈ F_{n,d'}`, `g`, `h` along `[n] = ([n] ∖ {j}) ⊔ {j}` (Claims 9.4, 9.5). Like `S9Svd3` and
`S7ModestBasis` this is DATA with its defining properties (the conclusions of Claims 9.4 and 9.5), not
a hypothesis of any statement about `δ` itself; its existence is `s9d_svd_exists`. `ux` is the basis
family of the effective degree (any pick). Coefficients are real `≥ 0` as in the claims;
orthonormality is for ALL indices (only positive singular values are kept, as in the claims). -/
structure S9dSvd {n : ℕ} (j : Fin n) (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ) (d' : ℕ) where
  sF : ℕ
  sG : ℕ
  sH : ℕ
  ψ : Fin sF → ℝ
  κ : Fin sG → ℝ
  ρ : Fin sH → ℝ
  FI : Fin sF → (S8Rest j → Y × Z) → ℂ
  FJ : Fin sF → Y × Z → ℂ
  gI : Fin sG → (S8Rest j → Y) → ℂ
  gJ : Fin sG → Y → ℂ
  hI : Fin sH → (S8Rest j → Z) → ℂ
  hJ : Fin sH → Z → ℂ
  ψ_nonneg : ∀ t, 0 ≤ ψ t
  κ_nonneg : ∀ r, 0 ≤ κ r
  ρ_nonneg : ∀ s, 0 ≤ ρ s
  F_eq : F = s8SvdSum j ψ FI FJ
  g_eq : g = s8SvdSum j κ gI gJ
  h_eq : h = s8SvdSum j ρ hI hJ
  FI_orth : ∀ t t', ((s7LawYZ μ).pi (S8Rest j)).cinner (FI t) (FI t') = if t = t' then 1 else 0
  FJ_orth : ∀ t t', (s7LawYZ μ).cinner (FJ t) (FJ t') = if t = t' then 1 else 0
  gI_orth : ∀ r r', ((lawY μ).pi (S8Rest j)).cinner (gI r) (gI r') = if r = r' then 1 else 0
  gJ_orth : ∀ r r', (lawY μ).cinner (gJ r) (gJ r') = if r = r' then 1 else 0
  hI_orth : ∀ s s', ((lawZ μ).pi (S8Rest j)).cinner (hI s) (hI s') = if s = s' then 1 else 0
  hJ_orth : ∀ s s', (lawZ μ).cinner (hJ s) (hJ s') = if s = s' then 1 else 0
  ψ_sq : ∑ t, ψ t ^ 2 = 1
  κ_sq : ∑ r, κ r ^ 2 = 1
  ρ_sq : ∑ s, ρ s ^ 2 = 1
  FI_effDeg : ∀ t, S7CCEffDegGE μ hμ ux (FI t) (d' - 1)
  FI_cc : ∀ t, S7ConstOnCC hμ (FI t)
  FJ_cc : ∀ t, ∃ f : X → ℂ, s8W1 hμ f = FJ t

variable {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ} {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ}
  {h : (Fin n → Z) → ℂ} {d' : ℕ}

/-- `F̂_t(r,s) = 𝔼_{μ^{⊗(n-1)}} F_t g_r h_s` (l. 4863). -/
def S9dSvd.Fhat (D : S9dSvd j μ hμ ux F g h d') (t : Fin D.sF) (r : Fin D.sG) (s : Fin D.sH) : ℂ :=
  s7CorrF μ (D.FI t) (D.gI r) (D.hI s)

/-- `F̂'_t(r,s) = 𝔼_{μ} F'_t g'_r h'_s` (l. 4867). -/
def S9dSvd.FhatJ (D : S9dSvd j μ hμ ux F g h d') (t : Fin D.sF) (r : Fin D.sG) (s : Fin D.sH) : ℂ :=
  s8Corr1 μ (D.FJ t) (D.gJ r) (D.hJ s)

end S9dSetup

section S9dHelpers

/-! ### Private helpers: inner-product calculus for `FinProb.cinner` -/

private lemma s9d_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; ring

private lemma s9d_mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]; exact s9d_star_mul_self z

private lemma s9d_fun_sum_eq {β κ : Type*} [Fintype κ] (w : κ → ℂ) (m : κ → β → ℂ) :
    (fun x => ∑ c, w c * m c x) = ∑ c, w c • m c := by
  funext x; simp [Finset.sum_apply]

/-- `⟨∑ a_c m_c, ∑ b_c m_c⟩ = ∑ a_c conj(b_c)` for an orthonormal family `m`. -/
private lemma s9d_cinner_orth_sum {β κ : Type*} [Fintype β] [Fintype κ] [DecidableEq κ]
    (π : FinProb β) (m : κ → β → ℂ)
    (hm : ∀ c c', π.cinner (m c) (m c') = if c = c' then 1 else 0) (a b : κ → ℂ) :
    π.cinner (fun x => ∑ c, a c * m c x) (fun x => ∑ c, b c * m c x) = ∑ c, a c * star (b c) := by
  rw [s9d_fun_sum_eq, s9d_fun_sum_eq, cinner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [cinner_smul_right, hm]; simp
  · intro c' _ hc'; rw [cinner_smul_right, hm]; simp [Ne.symm hc']
  · simp

/-- the squared norm of a combination of an orthonormal family. -/
private lemma s9d_expect_orth_sum {β κ : Type*} [Fintype β] [Fintype κ] [DecidableEq κ]
    (π : FinProb β) (m : κ → β → ℂ)
    (hm : ∀ c c', π.cinner (m c) (m c') = if c = c' then 1 else 0) (w : κ → ℂ) :
    ∑ x, π.prob x * ‖∑ c, w c * m c x‖ ^ 2 = ∑ c, ‖w c‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h1 := cinner_self_eq π (fun x => ∑ c, w c * m c x)
  rw [s9d_cinner_orth_sum π m hm w w] at h1
  simp only [FinProb.expect] at h1
  rw [← h1, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun c _ => s9d_mul_star_self (w c)

/-- orthonormal families are linearly independent. -/
private lemma s9d_linIndep_of_orth {β : Type*} [Fintype β] (π : FinProb β) {k : ℕ}
    (v : Fin k → β → ℂ) (hv : ∀ t t', π.cinner (v t) (v t') = if t = t' then 1 else 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  have := congrArg (fun f => π.cinner f (v t)) hc
  simp only [cinner_sum_left, cinner_smul_left, hv, cinner_zero_left, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  exact this

/-- Bessel's inequality for `FinProb.cinner`. -/
private lemma s9d_bessel {β κ : Type*} [Fintype β] [Fintype κ] [DecidableEq κ] (π : FinProb β)
    (e : κ → β → ℂ) (he : ∀ i i', π.cinner (e i) (e i') = if i = i' then 1 else 0) (f : β → ℂ) :
    ∑ i, ‖π.cinner f (e i)‖ ^ 2 ≤ (π.cinner f f).re := by
  set c : κ → ℂ := fun i => π.cinner f (e i) with hc
  set S : β → ℂ := fun x => ∑ i, c i * e i x with hS
  have hSS : π.cinner S S = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hS, s9d_cinner_orth_sum π e he c c, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => s9d_mul_star_self (c i)
  have hfS : π.cinner f S = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hS, s9d_fun_sum_eq, cinner_sum_right, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cinner_smul_right, ← s9d_star_mul_self]
  have hSf : π.cinner S f = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [cinner_comm, hfS]; simp
  have hg : π.cinner (f + (-1 : ℂ) • S) (f + (-1 : ℂ) • S) =
      π.cinner f f - ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [cinner_add_left, cinner_add_right, cinner_add_right, cinner_smul_left, cinner_smul_left,
      cinner_smul_right, cinner_smul_right, hSS, hfS, hSf]
    simp only [star_neg, star_one]
    ring
  have hpos : 0 ≤ (π.cinner (f + (-1 : ℂ) • S) (f + (-1 : ℂ) • S)).re := by
    rw [cinner_self_eq]
    simp only [Complex.ofReal_re, FinProb.expect]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg a) (sq_nonneg _)
  rw [hg, Complex.sub_re, Complex.ofReal_re] at hpos
  linarith

/-- the expectation under a pushforward law. -/
private lemma s9d_cexpect_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (π : FinProb α) (f : α → β) (φ : β → ℂ) :
    (mergePush π f).cexpect φ = π.cexpect (fun a => φ (f a)) := by
  unfold FinProb.cexpect mergePush
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun a => (π.prob a : ℂ) * φ (f a))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

/-- the splitting equivalence `(ι → α) ≃ α × (I → α)` of `[n] = I ⊔ {j}`. -/
private def s9dSplitEquiv {α : Type} {ι : Type} [DecidableEq ι] (j : ι) :
    (ι → α) ≃ α × (S8Rest j → α) where
  toFun w := (w j, s8Restr j w)
  invFun p := s8Glue j p.1 p.2
  left_inv w := by simp
  right_inv p := Prod.ext (by simp) (by simp)

private lemma s9d_pi_prob_glue {β : Type} [Fintype β] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb β) (j : ι) (a : β) (b : S8Rest j → β) :
    (π.pi ι).prob (s8Glue j a b) = π.prob a * (π.pi (S8Rest j)).prob b := by
  simp only [FinProb.pi]
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => π.prob (s8Glue j a b i)) j]
  have : ∀ i : S8Rest j, s8Glue j a b i = b i := fun i => by simp [s8Glue, i.2]
  simp only [this, s8Glue_same]

/-- Fubini for the split `[n] = I ⊔ {j}`, real form. -/
private lemma s9d_sum_split {β : Type} [Fintype β] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb β) (j : ι) (φ : (ι → β) → ℝ) :
    ∑ x, (π.pi ι).prob x * φ x =
      ∑ a, π.prob a * ∑ b, (π.pi (S8Rest j)).prob b * φ (s8Glue j a b) := by
  refine ((s9dSplitEquiv (α := β) j).symm.sum_comp (fun x => (π.pi ι).prob x * φ x)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [s9dSplitEquiv, Equiv.coe_fn_symm_mk, s9d_pi_prob_glue]
  ring

private lemma s9d_update_glue {α : Type} {ι : Type} [DecidableEq ι] (j : ι) (a b : α)
    (xI : S8Rest j → α) : Function.update (s8Glue j a xI) j b = s8Glue j b xI := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update, h, s8Glue]

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- `s7CorrF` is linear in the first slot. -/
private lemma s9d_corrF_sum_left {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    {P : Type} [Fintype P] (α : P → ℂ) (A : P → (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) :
    s7CorrF μ (fun w => ∑ p, α p * A p w) g h = ∑ p, α p * s7CorrF μ (A p) g h := by
  unfold s7CorrF FinProb.cexpect
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `s7CorrF` is linear in the second slot. -/
private lemma s9d_corrF_sum_mid {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    {P : Type} [Fintype P] (F : (ι → Y × Z) → ℂ) (α : P → ℂ) (B : P → (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) :
    s7CorrF μ F (fun y => ∑ p, α p * B p y) h = ∑ p, α p * s7CorrF μ F (B p) h := by
  unfold s7CorrF FinProb.cexpect
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `s7CorrF` is linear in the third slot. -/
private lemma s9d_corrF_sum_right {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    {P : Type} [Fintype P] (F : (ι → Y × Z) → ℂ) (g : (ι → Y) → ℂ) (α : P → ℂ)
    (C : P → (ι → Z) → ℂ) :
    s7CorrF μ F g (fun z => ∑ p, α p * C p z) = ∑ p, α p * s7CorrF μ F g (C p) := by
  unfold s7CorrF FinProb.cexpect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun t _ => ?_
  ring

end S9dHelpers

section S9dSetupThms
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Paper IV `lem:delta-inductive#svd-expansion`, existence (l. 5361-5374): Claims 9.4 (for `g` and, by
genericity in the alphabet, `h`) and 9.5 give the data `S9dSvd` for every unit `F ∈ F_{n,d'}`, `g`, `h`
and every coordinate `j` (any basis `Bx`). -/
theorem s9d_svd_exists (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a) (σ : X → H) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX μ) σ Sm) {n : ℕ} (j : Fin n) (F : (Fin n → Y × Z) → ℂ)
    (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ) (d' : ℕ) (hF : S7ConstOnCC hμ F)
    (hFd : S7CCEffDegGE μ hμ Bx.u F d') (hnF : cl2norm (s7LawYZ μ) F = 1)
    (hng : cl2norm (lawY μ) g = 1) (hnh : cl2norm (lawZ μ) h = 1) :
    Nonempty (S9dSvd j μ hμ Bx.u F g h d') := by
  obtain ⟨sF, ψ, FI, FJ, hψ, hFeq, hFI, hFJ, hFe, hFc, hψs⟩ :=
    s8_svd_effective_nonhomo μ hμ hDx σ Sm Bx j F d' hF hFd hnF
  obtain ⟨sG, κ, gI, gJ, hκ, hgeq, hgI, hgJ, hκs⟩ := s8_svd_nonhomo_g (lawY μ) hDy j g hng
  obtain ⟨sH, ρ, hI, hJ, hρ, hheq, hhI, hhJ, hρs⟩ := s8_svd_nonhomo_g (lawZ μ) hDz j h hnh
  exact ⟨⟨sF, sG, sH, ψ, κ, ρ, FI, FJ, gI, gJ, hI, hJ, hψ, hκ, hρ, hFeq, hgeq, hheq, hFI, hFJ, hgI,
    hgJ, hhI, hhJ, hψs, hκs, hρs, hFe, fun t => (hFc t).1, fun t => (hFc t).2⟩⟩

omit [DecidableEq X] [Fintype H] [DecidableEq H] in
/-- the size bounds of paper IV `lem:delta-inductive#svd-expansion` (left implicit in the source): `|R| ≤ |Γ|`,
`|S| ≤ |Φ|`, `|T| ≤ |Σ|` (the `F'_t = W f'_t` are orthonormal in `L²(μ_x)` by the `W`-isometry: a
dimension count). With `|Σ|, |Γ|, |Φ| ≤ m` these are `s ≤ m` of the numeric claims. -/
theorem s9d_card_le {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
    {K₁ K₂ : Type} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ} {F : (Fin n → Y × Z) → ℂ}
    {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ} (D : S9dSvd j μ hμ ux F g h d') :
    D.sF ≤ Fintype.card X ∧ D.sG ≤ Fintype.card Y ∧ D.sH ≤ Fintype.card Z := by
  refine ⟨?_, ?_, ?_⟩
  · let L : (X → ℂ) →ₗ[ℂ] (Y × Z → ℂ) :=
      { toFun := s8W1 hμ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hmem : ∀ t, D.FJ t ∈ LinearMap.range L := fun t => by
      obtain ⟨f, hf⟩ := D.FJ_cc t
      exact ⟨f, hf⟩
    let v : Fin D.sF → LinearMap.range L := fun t => ⟨D.FJ t, hmem t⟩
    have hli : LinearIndependent ℂ v :=
      LinearIndependent.of_comp (LinearMap.range L).subtype
        (s9d_linIndep_of_orth (s7LawYZ μ) D.FJ D.FJ_orth)
    have h1 := hli.fintype_card_le_finrank
    have h2 := LinearMap.finrank_range_le L
    simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h1 h2
    omega
  · have h1 := (s9d_linIndep_of_orth (lawY μ) D.gJ D.gJ_orth).fintype_card_le_finrank
    simpa using h1
  · have h1 := (s9d_linIndep_of_orth (lawZ μ) D.hJ D.hJ_orth).fintype_card_le_finrank
    simpa using h1

omit [Fintype H] [DecidableEq H] in
/-- eq. `delta_1` (l. 5372-5374): `𝔼_{μ^{⊗n}} F g h = ∑_{t,r,s} ψ_t κ_r ρ_s F̂_t(r,s) F̂'_t(r,s)`
(multilinearity and the factorisation `s8_corrF_glue`). -/
theorem s9d_expansion {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
    {K₁ K₂ : Type} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ} {F : (Fin n → Y × Z) → ℂ}
    {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ} (D : S9dSvd j μ hμ ux F g h d') :
    s7CorrF μ F g h = ∑ x : Fin D.sF × Fin D.sG × Fin D.sH,
      (D.ψ x.1 : ℂ) * D.κ x.2.1 * D.ρ x.2.2 * D.Fhat x.1 x.2.1 x.2.2 * D.FhatJ x.1 x.2.1 x.2.2 := by
  calc s7CorrF μ F g h = s7CorrF μ (s8SvdSum j D.ψ D.FI D.FJ) (s8SvdSum j D.κ D.gI D.gJ)
        (s8SvdSum j D.ρ D.hI D.hJ) := by rw [← D.F_eq, ← D.g_eq, ← D.h_eq]
    _ = _ := by
      unfold s8SvdSum
      rw [s9d_corrF_sum_left]
      simp only [s9d_corrF_sum_mid, s9d_corrF_sum_right, s8_corrF_glue, Fintype.sum_prod_type,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      simp only [S9dSvd.Fhat, S9dSvd.FhatJ]
      ring

/-- Paper IV `lem:delta-inductive#level-n-1-coefficient-bounds` (a) (l. 5437-5445): every unit combination
`F̃ ∈ span{F_t}` lies in `F_{n-1,d'-1}` (a subspace; `s8_mem_classFn_iff`, `s7_classFn_add`), so for all
`a, b`: `∑_t |∑_{r,s} a_r b_s F̂_t(r,s)|² ≤ δ_{n-1,d'-1}² ‖a‖² ‖b‖²` (take `F̃ ∝ ∑ conj(c_t) F_t`,
`g̃ = ∑ a_r g_r`, `h̃ = ∑ b_s h_s`; `s8_deltaParam_le_iff_generic`). The cases `a = e_r`, `b = e_s` are
the printed `|F̂_t(r,s)| ≤ δ'` and `∑_{t∈T'}|F̂_t(r,s)|² ≤ δ'²`. `hind` is hypothesis 5
(`s8_hind_of_uniform`); it makes `δ_{n-1,d'-1} ≤ 1` finite. -/
theorem s9d_level_bounds_a {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)}
    {hμ : S7YZImpliesX μ.support} {K₁ K₂ : Type} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ}
    {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (D : S9dSvd j μ hμ ux F g h d')
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (a : Fin D.sG → ℂ) (b : Fin D.sH → ℂ) :
    ∑ t, ‖∑ r, ∑ s, a r * b s * D.Fhat t r s‖ ^ 2 ≤
      (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal ^ 2 * (∑ r, ‖a r‖ ^ 2) * ∑ s, ‖b s‖ ^ 2 := by
  classical
  obtain ⟨e⟩ := s8_restEquivFin (Equiv.refl (Fin n)) j
  obtain ⟨δ', hδ'⟩ : ∃ δ', δ' = (s7DeltaParam μ hμ ux (n - 1) (d' - 1)).toReal := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin D.sF → ℂ, c = fun t => ∑ r, ∑ s, a r * b s * D.Fhat t r s := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : (S8Rest j → Y) → ℂ, G = fun y => ∑ r, a r * D.gI r y := ⟨_, rfl⟩
  obtain ⟨Hh, hH⟩ : ∃ Hh : (S8Rest j → Z) → ℂ, Hh = fun z => ∑ s, b s * D.hI s z := ⟨_, rfl⟩
  obtain ⟨Ft, hFt⟩ : ∃ Ft : (S8Rest j → Y × Z) → ℂ, Ft = fun w => ∑ t, star (c t) * D.FI t w :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ t, ‖c t‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ r, ‖a r‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s, ‖b s‖ ^ 2 := ⟨_, rfl⟩
  have hgoal : ∑ t, ‖∑ r, ∑ s, a r * b s * D.Fhat t r s‖ ^ 2 = S := by rw [hS, hc]
  rw [hgoal, ← hδ', ← hA, ← hB]
  have hct : ∀ t, c t = s7CorrF μ (D.FI t) G Hh := by
    intro t
    rw [hG, hH, s9d_corrF_sum_mid]
    simp only [s9d_corrF_sum_right, Finset.mul_sum, hc, S9dSvd.Fhat]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have hcorr : s7CorrF μ Ft G Hh = (S : ℂ) := by
    rw [hFt, s9d_corrF_sum_left, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hct, s9d_star_mul_self]
  have hnF : cl2norm (s7LawYZ μ) Ft = Real.sqrt S := by
    unfold cl2norm; congr 1
    apply Complex.ofReal_injective
    rw [cl2sq_cast, hFt, s9d_cinner_orth_sum _ D.FI D.FI_orth, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [star_star, s9d_star_mul_self]
  have hnG : cl2norm (lawY μ) G = Real.sqrt A := by
    unfold cl2norm; congr 1
    apply Complex.ofReal_injective
    rw [cl2sq_cast, hG, s9d_cinner_orth_sum _ D.gI D.gI_orth, hA, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun r _ => s9d_mul_star_self (a r)
  have hnH : cl2norm (lawZ μ) Hh = Real.sqrt B := by
    unfold cl2norm; congr 1
    apply Complex.ofReal_injective
    rw [cl2sq_cast, hH, s9d_cinner_orth_sum _ D.hI D.hI_orth, hB, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun s _ => s9d_mul_star_self (b s)
  -- `F̃` lies in `F_{n-1,d'-1}` (transported to `S8Rest j ≃ Fin (n - 1)`)
  have hmem : s8Reindex e Ft ∈ s7ClassFn μ hμ ux (n - 1) (d' - 1) := by
    rw [s8_mem_classFn_iff μ hμ ux e Ft (d' - 1)]
    refine ⟨?_, ?_⟩
    · choose f hf using fun t => (D.FI_cc t : ∃ f, s7W hμ f = D.FI t)
      refine ⟨fun x => ∑ t, star (c t) * f t x, ?_⟩
      rw [hFt]; funext w
      simp only [s7W]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← hf t]; rfl
    · intro cc hcc
      have hlin : s7CCCoef μ hμ ux Ft cc = ∑ t, star (c t) * s7CCCoef μ hμ ux (D.FI t) cc := by
        unfold s7CCCoef; rw [hFt, s9d_fun_sum_eq, cinner_sum_left]
        simp only [cinner_smul_left]
      rw [hlin] at hcc
      obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcc
      exact D.FI_effDeg t cc (right_ne_zero_of_mul ht)
  have hδle : s7DeltaParam μ hμ ux (n - 1) (d' - 1) ≤ ENNReal.ofReal δ' := by
    rw [hδ', ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (s7_deltaParam_le_one μ hμ hind ux _ _))]
  have hbound := (s7DeltaParam_le_iff μ hμ ux (n - 1) (d' - 1)
    (hδ' ▸ ENNReal.toReal_nonneg)).1 hδle
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun t _ => sq_nonneg _
  have hA0 : 0 ≤ A := hA ▸ Finset.sum_nonneg fun r _ => sq_nonneg _
  have hB0 : 0 ≤ B := hB ▸ Finset.sum_nonneg fun s _ => sq_nonneg _
  rcases eq_or_lt_of_le hS0 with hSz | hSpos
  · rw [← hSz]; positivity
  have hApos : 0 < A := by
    refine lt_of_le_of_ne hA0 fun hAz => ?_
    have ha : ∀ r, a r = 0 := fun r => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg ‖a r‖)).1
        (hA ▸ hAz.symm) r (Finset.mem_univ r)
      simpa using this
    have : S = 0 := by rw [hS, hc]; simp [ha]
    linarith
  have hBpos : 0 < B := by
    refine lt_of_le_of_ne hB0 fun hBz => ?_
    have hb : ∀ s, b s = 0 := fun s => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => sq_nonneg ‖b s‖)).1
        (hB ▸ hBz.symm) s (Finset.mem_univ s)
      simpa using this
    have : S = 0 := by rw [hS, hc]; simp [hb]
    linarith
  have h := hbound (s8Reindex e Ft) (s8Reindex e G) (s8Reindex e Hh) hmem
    (by rw [s8_cl2norm_reindex, hnF]; exact (Real.sqrt_pos.2 hSpos).ne')
    (by rw [s8_cl2norm_reindex, hnG]; exact (Real.sqrt_pos.2 hApos).ne')
    (by rw [s8_cl2norm_reindex, hnH]; exact (Real.sqrt_pos.2 hBpos).ne')
  rw [s8_corrF_reindex, s8_cl2norm_reindex, s8_cl2norm_reindex, s8_cl2norm_reindex, hcorr, hnF,
    hnG, hnH, Complex.norm_real, Real.norm_of_nonneg hS0] at h
  have hpos : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
  have h2 : Real.sqrt S ≤ δ' * Real.sqrt A * Real.sqrt B := by
    have h1 : Real.sqrt S * Real.sqrt S ≤ Real.sqrt S * (δ' * Real.sqrt A * Real.sqrt B) := by
      rw [Real.mul_self_sqrt hS0]
      calc S ≤ δ' * (Real.sqrt S * Real.sqrt A * Real.sqrt B) := h
        _ = Real.sqrt S * (δ' * Real.sqrt A * Real.sqrt B) := by ring
    exact le_of_mul_le_mul_left h1 hpos
  have h3 := pow_le_pow_left₀ hpos.le h2 2
  rw [Real.sq_sqrt hS0, mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0] at h3
  exact h3

omit [DecidableEq X] [Fintype H] [DecidableEq H] in
/-- Paper IV `lem:delta-inductive#level-n-1-coefficient-bounds` (b), the Bessel bounds (l. 5442-5445):
`∑_{r,s} |F̂'_t(r,s)|² ≤ 1` for each `t` and `∑_t |F̂'_t(r,s)|² ≤ 1` for each `(r,s)` (the families
`{conj(g'_r h'_s)}` and `{F'_t}` are orthonormal in `L²(μ_{y,z})`; this needs `μ_{y,z} = μ_y ⊗ μ_z`,
`hind`, implicit in the source). -/
theorem s9d_level_bounds_b {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)}
    {hμ : S7YZImpliesX μ.support} {K₁ K₂ : Type} {ux : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ}
    {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d' : ℕ}
    (D : S9dSvd j μ hμ ux F g h d')
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z) :
    (∀ t, ∑ r, ∑ s, ‖D.FhatJ t r s‖ ^ 2 ≤ 1) ∧ ∀ r s, ∑ t, ‖D.FhatJ t r s‖ ^ 2 ≤ 1 := by
  classical
  -- the functions `conj(g'_r h'_s)` on `Y × Z`
  obtain ⟨E, hE⟩ : ∃ E : Fin D.sG × Fin D.sH → Y × Z → ℂ,
      E = fun q v => star (D.gJ q.1 v.1 * D.hJ q.2 v.2) := ⟨_, rfl⟩
  have hFJ : ∀ t r s, D.FhatJ t r s = (s7LawYZ μ).cinner (D.FJ t) (E (r, s)) := by
    intro t r s
    simp only [S9dSvd.FhatJ, s8Corr1, FinProb.cinner, hE, star_star]
    unfold s7LawYZ
    rw [s9d_cexpect_push]
    simp only [mul_assoc]
  have hEo : ∀ q q', (s7LawYZ μ).cinner (E q) (E q') = if q = q' then 1 else 0 := by
    rintro ⟨r, s⟩ ⟨r', s'⟩
    have key : (s7LawYZ μ).cinner (E (r, s)) (E (r', s')) =
        (lawY μ).cinner (D.gJ r') (D.gJ r) * (lawZ μ).cinner (D.hJ s') (D.hJ s) := by
      simp only [cinner_def, Fintype.sum_prod_type, hind, Finset.sum_mul_sum, hE]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
      simp only [star_mul', star_star]; push_cast; ring
    rw [key, D.gJ_orth, D.hJ_orth]
    by_cases hr : r = r' <;> by_cases hs : s = s' <;> simp [hr, hs, eq_comm]
  refine ⟨fun t => ?_, fun r s => ?_⟩
  · have hb := s9d_bessel (s7LawYZ μ) E hEo (D.FJ t)
    rw [D.FJ_orth t t] at hb
    simp only [↓reduceIte, Complex.one_re] at hb
    calc ∑ r, ∑ s, ‖D.FhatJ t r s‖ ^ 2 =
          ∑ q : Fin D.sG × Fin D.sH, ‖(s7LawYZ μ).cinner (D.FJ t) (E q)‖ ^ 2 := by
          rw [Fintype.sum_prod_type]; simp only [hFJ]
      _ ≤ 1 := hb
  · have hb := s9d_bessel (s7LawYZ μ) D.FJ D.FJ_orth (E (r, s))
    rw [hEo] at hb
    simp only [↓reduceIte, Complex.one_re] at hb
    calc ∑ t, ‖D.FhatJ t r s‖ ^ 2 = ∑ t, ‖(s7LawYZ μ).cinner (E (r, s)) (D.FJ t)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hFJ, cinner_comm (s7LawYZ μ) (D.FJ t) (E (r, s)), norm_star]
      _ ≤ 1 := hb

/-- Paper IV `lem:delta-inductive#choose-coordinate` (eq. `choose_j_in_delta`, l. 5357-5361): for unit
`F ∈ F_{n,d'}` (`1 ≤ d'`, `n ≤ d' A`) some `j` has `I_{j,modest}[F] ≥ 1/A`: `I_modest[F] ≥ 2d'`
(Fact 7.8, `s7_modest_total_inf_formula`, through `W`: `s7CCModestInf_W`, `s7_cl2norm_W`) and the average
over `j` is `≥ 2d'/n ≥ 2/A`. -/
theorem s9d_choose_coordinate (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (σ : X → H) (Sm : Finset X)
    (hconst : ∀ x ∈ Sm, ∀ x' ∈ Sm, σ x = σ x') (Bx : S7ModestBasis (lawX μ) σ Sm) {n d' : ℕ}
    (hn : 0 < n) (hd' : 1 ≤ d') (F : (Fin n → Y × Z) → ℂ) (hF : S7ConstOnCC hμ F)
    (hFd : S7CCEffDegGE μ hμ Bx.u F d') (hnorm : cl2norm (s7LawYZ μ) F = 1) {A : ℝ}
    (hnA : (n : ℝ) ≤ d' * A) :
    ∃ j : Fin n, 1 / A ≤ s7CCModestInf μ hμ hocc Sm hF j := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → X) → ℂ, f = s7WInv hocc hF := ⟨_, rfl⟩
  have hW : s7W hμ f = F := hf ▸ s7W_s7WInv hocc hF
  have hI : ∀ i, s7CCModestInf μ hμ hocc Sm hF i = s7ModestInf (lawX μ) Sm f i := by
    intro i; rw [hf]; rfl
  have hONB := s7_modestBasis_isONB (lawX μ) σ Sm hDx Bx
  have hf1 : cl2sq (lawX μ) f = 1 := by
    have h1 : cl2norm (lawX μ) f = 1 := by rw [← s7_cl2norm_W μ hμ f, hW]; exact hnorm
    exact Real.sqrt_eq_one.1 h1
  have hpars := s7_parseval (lawX μ) hDx Bx.u hONB f
  have htot := s7_modest_total_inf_formula (lawX μ) σ Sm hDx hconst Bx f
  have hlow : 2 * (d' : ℝ) ≤ ∑ i, s7ModestInf (lawX μ) Sm f i := by
    have e1 : ∑ i, s7ModestInf (lawX μ) Sm f i = s7ModestTotalInf (lawX μ) Sm f := rfl
    rw [e1, htot]
    have h2 : (d' : ℝ) * ∑ c, ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 ≤
        ∑ c, (s7EffDeg c : ℝ) * ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      by_cases h0 : s7Coef (lawX μ) Bx.u f c = 0
      · simp [h0]
      · have hc : d' ≤ s7EffDeg c := hFd c (by rw [← hW, s7CCCoef_W]; exact h0)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)
    have h3 : ∑ c, ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 = 1 := by
      rw [← hpars]; exact hf1
    rw [h3, mul_one] at h2
    linarith
  by_contra hne
  simp only [not_exists, not_le] at hne
  have hd'pos : (0 : ℝ) < d' := by exact_mod_cast hd'
  have hApos : 0 < A := by
    have : (0 : ℝ) < d' * A := lt_of_lt_of_le (by exact_mod_cast hn) hnA
    exact (pos_iff_pos_of_mul_pos this).1 hd'pos
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsum : ∑ i, s7ModestInf (lawX μ) Sm f i < ∑ _i : Fin n, 1 / A :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hI i ▸ hne i
  have hnA' : ∑ _i : Fin n, 1 / A ≤ d' := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_le_iff₀ hApos]
    exact hnA
  linarith

/-- Paper IV `claim:large-modestinf-sig-var` (Claim 9.7, l. 5323-5345): for `F = ∑ ψ_t F_t ⊗ F'_t` (Claim
9.5) with `F'_t = W f'_t`: `I_{j,modest}[F] ≤ m² ∑_t ψ_t² var_{Σ_modest}(f'_t)`, i.e. the printed `≫_{m,α}`
with the explicit constant `m⁻²` (independent of `α`): `I_{j,modest}[f] = ∑_t ψ_t² 𝔼_{a∼μ_x, b∼Modest(a)}
|f'_t(a) - f'_t(b)|²` (orthonormality of the `f_t`, `W`-isometry), the weight `μ_x(a)μ_x(b)/μ_x(Σ_modest)`
is `≤ 1 ≤ m²/|Σ_modest|²`, and `x ∉ Σ_modest` contributes `0`. -/
theorem s9d_large_modestinf_sig_var (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) (Sm : Finset X)
    (hSm : Sm.Nonempty) {m : ℕ} (hX : Fintype.card X ≤ m) {n : ℕ} (j : Fin n)
    (F : (Fin n → Y × Z) → ℂ) (hF : S7ConstOnCC hμ F) {sT : ℕ} (ψ : Fin sT → ℝ)
    (FI : Fin sT → (S8Rest j → Y × Z) → ℂ) (FJ : Fin sT → Y × Z → ℂ)
    (hdec : F = s8SvdSum j ψ FI FJ)
    (hI : ∀ t t', ((s7LawYZ μ).pi (S8Rest j)).cinner (FI t) (FI t') = if t = t' then 1 else 0)
    (hcc : ∀ t, S7ConstOnCC hμ (FI t)) (f' : Fin sT → X → ℂ)
    (hf' : ∀ t, s8W1 hμ (f' t) = FJ t) :
    s7CCModestInf μ hμ hocc Sm hF j ≤ (m : ℝ) ^ 2 * ∑ t, ψ t ^ 2 * s7ModestVar Sm hSm (f' t) := by
  classical
  choose fI hfI using fun t => (hcc t : ∃ f, s7W hμ f = FI t)
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : (Fin n → X) → ℂ, f₀ = s8SvdSum j ψ fI f' := ⟨_, rfl⟩
  have hW : s7W hμ f₀ = F := by
    rw [hf₀, hdec]; funext w
    simp only [s7W, s8SvdSum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hfI t, ← hf' t]; rfl
  have hIeq : s7CCModestInf μ hμ hocc Sm hF j = s7ModestInf (lawX μ) Sm f₀ j := by
    unfold s7CCModestInf; rw [← s7WInv_unique hμ hocc hF f₀ hW]
  rw [hIeq]
  have hIo : ∀ t t', ((lawX μ).pi (S8Rest j)).cinner (fI t) (fI t') = if t = t' then 1 else 0 := by
    intro t t'; rw [← s7_W_cinner μ hμ, hfI, hfI]; exact hI t t'
  obtain ⟨G, hG⟩ : ∃ G : X → X → ℝ, G = fun a b => ∑ t, ψ t ^ 2 * ‖f' t a - f' t b‖ ^ 2 :=
    ⟨_, rfl⟩
  have hdiff : ∀ (a b : X) (xI : S8Rest j → X),
      f₀ (s8Glue j a xI) - f₀ (Function.update (s8Glue j a xI) j b) =
        ∑ t, ((ψ t : ℂ) * (f' t a - f' t b)) * fI t xI := by
    intro a b xI
    rw [hf₀, s9d_update_glue]
    simp only [s8SvdSum, s8Restr_glue, s8Glue_same, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hcomp : s7ModestInf (lawX μ) Sm f₀ j =
      ∑ a, (lawX μ).prob a * ∑ b, s7ModestKernel (lawX μ) Sm a b * G a b := by
    unfold s7ModestInf
    rw [s9d_sum_split (lawX μ) j]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    simp only [s8Glue_same, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hdiff]
    calc ∑ xI, ((lawX μ).pi (S8Rest j)).prob xI * (s7ModestKernel (lawX μ) Sm a b *
          ‖∑ t, ((ψ t : ℂ) * (f' t a - f' t b)) * fI t xI‖ ^ 2) =
        s7ModestKernel (lawX μ) Sm a b * ∑ xI, ((lawX μ).pi (S8Rest j)).prob xI *
          ‖∑ t, ((ψ t : ℂ) * (f' t a - f' t b)) * fI t xI‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun xI _ => by ring
      _ = s7ModestKernel (lawX μ) Sm a b * G a b := by
          rw [s9d_expect_orth_sum _ fI hIo, hG]
          congr 1
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hcomp]
  have hG0 : ∀ a b, 0 ≤ G a b := fun a b => by
    rw [hG]; exact Finset.sum_nonneg fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hGaa : ∀ a, G a a = 0 := fun a => by rw [hG]; simp
  have hD1 : ∀ a, (lawX μ).prob a ≤ 1 := fun a => by
    rw [← (lawX μ).sum_eq_one]
    exact Finset.single_le_sum (fun c _ => (lawX μ).nonneg c) (Finset.mem_univ a)
  have hstep : ∀ a, (lawX μ).prob a * ∑ b, s7ModestKernel (lawX μ) Sm a b * G a b ≤
      if a ∈ Sm then ∑ b ∈ Sm, G a b else 0 := by
    intro a
    by_cases ha : a ∈ Sm
    · simp only [ha, ↓reduceIte]
      have e1 : ∑ b, s7ModestKernel (lawX μ) Sm a b * G a b =
          ∑ b ∈ Sm, (lawX μ).prob b / (∑ c ∈ Sm, (lawX μ).prob c) * G a b := by
        simp only [s7ModestKernel, ha, ↓reduceIte, ite_mul, zero_mul]
        exact Fintype.sum_ite_mem Sm _
      rw [e1]
      have e2 : ∑ b ∈ Sm, (lawX μ).prob b / (∑ c ∈ Sm, (lawX μ).prob c) * G a b ≤
          ∑ b ∈ Sm, G a b := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hle : (lawX μ).prob b / (∑ c ∈ Sm, (lawX μ).prob c) ≤ 1 :=
          div_le_one_of_le₀ (Finset.single_le_sum (fun c _ => (lawX μ).nonneg c) hb)
            (Finset.sum_nonneg fun c _ => (lawX μ).nonneg c)
        exact mul_le_of_le_one_left (hG0 a b) hle
      have e3 : 0 ≤ ∑ b ∈ Sm, (lawX μ).prob b / (∑ c ∈ Sm, (lawX μ).prob c) * G a b :=
        Finset.sum_nonneg fun b _ => mul_nonneg (div_nonneg ((lawX μ).nonneg b)
          (Finset.sum_nonneg fun c _ => (lawX μ).nonneg c)) (hG0 a b)
      exact (mul_le_of_le_one_left e3 (hD1 a)).trans e2
    · simp [s7ModestKernel, ha, hGaa]
  have hcard : 0 < (Sm.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hSm
  have hv : ∀ t, ∑ a ∈ Sm, ∑ b ∈ Sm, ‖f' t a - f' t b‖ ^ 2 =
      (Sm.card : ℝ) ^ 2 * s7ModestVar Sm hSm (f' t) := by
    intro t; unfold s7ModestVar; field_simp
  have hv0 : ∀ t, 0 ≤ s7ModestVar Sm hSm (f' t) := fun t => by
    unfold s7ModestVar
    exact div_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
      (sq_nonneg _)
  have hcm : (Sm.card : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have : Sm.card ≤ m := (Finset.card_le_univ Sm).trans hX
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast this) 2
  calc ∑ a, (lawX μ).prob a * ∑ b, s7ModestKernel (lawX μ) Sm a b * G a b ≤
        ∑ a, (if a ∈ Sm then ∑ b ∈ Sm, G a b else 0) := Finset.sum_le_sum fun a _ => hstep a
    _ = ∑ a ∈ Sm, ∑ b ∈ Sm, G a b := Fintype.sum_ite_mem Sm (fun a => ∑ b ∈ Sm, G a b)
    _ = ∑ t, ψ t ^ 2 * ((Sm.card : ℝ) ^ 2 * s7ModestVar Sm hSm (f' t)) := by
        simp only [hG, ← hv, Finset.mul_sum]
        exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
    _ ≤ ∑ t, ψ t ^ 2 * ((m : ℝ) ^ 2 * s7ModestVar Sm hSm (f' t)) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcm (hv0 t)) (sq_nonneg _)
    _ = (m : ℝ) ^ 2 * ∑ t, ψ t ^ 2 * s7ModestVar Sm hSm (f' t) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring

end S9dSetupThms

end TrackB
end RestrictedPolynomials
end
