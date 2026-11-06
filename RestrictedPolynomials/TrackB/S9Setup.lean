module

public import RestrictedPolynomials.TrackB.S8Svd
public import RestrictedPolynomials.TrackB.S8AdditiveBase

/-!
# Track B: the setup of Section 8.3 (`reduce_beta`)

Source: paper IV (`writeup_stability.tex`), l. 4829-4949, 5035, 5110-5119 (eq. `svd_main`,
`project_eq`, `large_large_0`, the vanishing observations, `#choose-partition`, `#combine-F-t`).
The cc non-embedding influence
is `s7CCNonEmbedInf μ hμ hocc σ hF j`.  `S9Svd3` stays a structure (data with its defining
properties, precedent `S7ModestBasis`); `s9_svd3_exists` inhabits it for every unit triple.
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S9Setup
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The data of eq. `svd_main` (l. 4835-4854): the three singular value decompositions of unit
`F ∈ F_{n,d,d'}`, `g ∈ G_n`, `h ∈ H_n` along the split `[n] = ([n] \ {j}) ⊔ {j}`, after the phase
normalisation `F'_χ = W ∘ χ ∘ σ`, `g'_π = π ∘ γ`, `h'_λ = λ ∘ φ`, with the properties of Claims 8.4
and 8.5 (and of its `Φ`-analogue). Indices `Ĥ ⊕ Fin s`: `inl χ` is the embedding part, `inr t` the
non-embedding part (`T`, `R`, `S` of the source). Like `S7ModestBasis` this is DATA with its defining
properties, not a hypothesis of any statement; its existence is `s9_svd3_exists` (from
`s8_svd_effective`, `s8_svd`). The bases are the chosen ones of Def. 7.1, for all picks. -/
structure S9Svd3 {n : ℕ} (j : Fin n) (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (σ : X → H) (γ : Y → H) (φ : Z → H) {Sm : Finset X} (Bx : S7ModestBasis (lawX μ) σ Sm)
    (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)) (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z))
    (F : (Fin n → Y × Z) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ)
    (d d' dg dh : ℕ) where
  sF : ℕ
  sG : ℕ
  sH : ℕ
  ψ : AddChar H ℂ ⊕ Fin sF → ℂ
  κ : AddChar H ℂ ⊕ Fin sG → ℂ
  ρ : AddChar H ℂ ⊕ Fin sH → ℂ
  FI : AddChar H ℂ ⊕ Fin sF → (S8Rest j → Y × Z) → ℂ
  FJ : AddChar H ℂ ⊕ Fin sF → Y × Z → ℂ
  gI : AddChar H ℂ ⊕ Fin sG → (S8Rest j → Y) → ℂ
  gJ : AddChar H ℂ ⊕ Fin sG → Y → ℂ
  hI : AddChar H ℂ ⊕ Fin sH → (S8Rest j → Z) → ℂ
  hJ : AddChar H ℂ ⊕ Fin sH → Z → ℂ
  decF : F = s8SvdSumC j ψ FI FJ
  decG : g = s8SvdSumC j κ gI gJ
  decH : h = s8SvdSumC j ρ hI hJ
  FJ_chi : ∀ χ : AddChar H ℂ, FJ (Sum.inl χ) = s8W1 hμ (fun x => χ (σ x))
  gJ_chi : ∀ π : AddChar H ℂ, gJ (Sum.inl π) = fun y => π (γ y)
  hJ_chi : ∀ l : AddChar H ℂ, hJ (Sum.inl l) = fun z => l (φ z)
  FI_chi : ∀ χ : AddChar H ℂ, (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u (FI (Sum.inl χ)) Dtot) ∧
    S7CCNeHom μ hμ Bx.u (FI (Sum.inl χ)) d ∧ S7CCEffDegGE μ hμ Bx.u (FI (Sum.inl χ)) d'
  FI_t : ∀ r : Fin sF, (∀ Da : AddChar H ℂ → ℕ,
      (∀ c : Fin n → Bx.J, s7CCCoef μ hμ Bx.u F c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a) →
      ∀ c : S8Rest j → Bx.J, s7CCCoef μ hμ Bx.u (FI (Sum.inr r)) c ≠ 0 →
        ∀ a, s7EmbedDegA a c = Da a) ∧
    S7CCNeHom μ hμ Bx.u (FI (Sum.inr r)) (d - 1) ∧
    S7CCEffDegGE μ hμ Bx.u (FI (Sum.inr r)) (d' - 1)
  FJ_t : ∀ (r : Fin sF) (χ : AddChar H ℂ),
    (s7LawYZ μ).cinner (FJ (Sum.inr r)) (s8W1 hμ (fun x => χ (σ x))) = 0
  F_cc : ∀ p, S7ConstOnCC hμ (FI p) ∧ ∃ f : X → ℂ, s8W1 hμ f = FJ p
  gI_chi : ∀ π : AddChar H ℂ, (∃ Dtot, S7CompEmbedHom (lawY μ) By.u (gI (Sum.inl π)) Dtot) ∧
    S7NeHom (lawY μ) By.u (gI (Sum.inl π)) dg
  gI_r : ∀ r : Fin sG, (∃ Dtot, S7CompEmbedHom (lawY μ) By.u (gI (Sum.inr r)) Dtot) ∧
    S7NeHom (lawY μ) By.u (gI (Sum.inr r)) (dg - 1)
  gJ_r : ∀ r : Fin sG, gJ (Sum.inr r) ∈ s7Perp (lawY μ) (embedSpan γ)
  hI_chi : ∀ l : AddChar H ℂ, (∃ Dtot, S7CompEmbedHom (lawZ μ) Bz.u (hI (Sum.inl l)) Dtot) ∧
    S7NeHom (lawZ μ) Bz.u (hI (Sum.inl l)) dh
  hI_s : ∀ s : Fin sH, (∃ Dtot, S7CompEmbedHom (lawZ μ) Bz.u (hI (Sum.inr s)) Dtot) ∧
    S7NeHom (lawZ μ) Bz.u (hI (Sum.inr s)) (dh - 1)
  hJ_s : ∀ s : Fin sH, hJ (Sum.inr s) ∈ s7Perp (lawZ μ) (embedSpan φ)
  orthF_I : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
    ((s7LawYZ μ).pi (S8Rest j)).cinner (FI p) (FI q) = if p = q then 1 else 0
  orthF_J : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
    (s7LawYZ μ).cinner (FJ p) (FJ q) = if p = q then 1 else 0
  orthG_I : ∀ p q, κ p ≠ 0 → κ q ≠ 0 →
    ((lawY μ).pi (S8Rest j)).cinner (gI p) (gI q) = if p = q then 1 else 0
  orthG_J : ∀ p q, κ p ≠ 0 → κ q ≠ 0 → (lawY μ).cinner (gJ p) (gJ q) = if p = q then 1 else 0
  orthH_I : ∀ p q, ρ p ≠ 0 → ρ q ≠ 0 →
    ((lawZ μ).pi (S8Rest j)).cinner (hI p) (hI q) = if p = q then 1 else 0
  orthH_J : ∀ p q, ρ p ≠ 0 → ρ q ≠ 0 → (lawZ μ).cinner (hJ p) (hJ q) = if p = q then 1 else 0
  normF : ∑ p, ‖ψ p‖ ^ 2 = 1
  normG : ∑ p, ‖κ p‖ ^ 2 = 1
  normH : ∑ p, ‖ρ p‖ ^ 2 = 1

variable {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X} {Bx : S7ModestBasis (lawX μ) σ Sm}
  {By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)} {Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)}
  {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d d' dg dh : ℕ}

/-- `F̂_t(r, s) = 𝔼_{μ^{⊗(n-1)}} F_t(y,z) g_r(y) h_s(z)` (l. 4863-4866). -/
def S9Svd3.Fhat (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (p : AddChar H ℂ ⊕ Fin S.sF) (q : AddChar H ℂ ⊕ Fin S.sG) (r : AddChar H ℂ ⊕ Fin S.sH) : ℂ :=
  s7CorrF μ (S.FI p) (S.gI q) (S.hI r)

/-- `F̂'_t(r, s) = 𝔼_{μ} F'_t(y,z) g'_r(y) h'_s(z)` (l. 4867). -/
def S9Svd3.FhatJ (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (p : AddChar H ℂ ⊕ Fin S.sF) (q : AddChar H ℂ ⊕ Fin S.sG) (r : AddChar H ℂ ⊕ Fin S.sH) : ℂ :=
  s8Corr1 μ (S.FJ p) (S.gJ q) (S.hJ r)

end S9Setup

/-! ### Private helpers -/

section S9Aux
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X} {Bx : S7ModestBasis (lawX μ) σ Sm}
  {By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)} {Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)}
  {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d d' dg dh : ℕ}

private lemma card_orth_le {A P : Type} [Fintype A] [DecidableEq P] (D : FinProb A)
    (u : P → A → ℂ) (s : Finset P)
    (h : ∀ p ∈ s, ∀ q ∈ s, D.cinner (u p) (u q) = if p = q then 1 else 0) :
    s.card ≤ Fintype.card A := by
  have hli : LinearIndependent ℂ (fun p : s => u p) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := congrArg (fun f => D.cinner f (u q)) hc
    simp only [cinner_zero_left] at h1
    rw [cinner_sum_left] at h1
    simp only [cinner_smul_left] at h1
    rw [Finset.sum_eq_single q] at h1
    · rw [h q.1 q.2 q.1 q.2] at h1
      simpa using h1
    · intro p _ hp
      have hne : p.1 ≠ q.1 := fun e => hp (Subtype.ext e)
      rw [h p.1 p.2 q.1 q.2]
      simp [hne]
    · intro hq; exact absurd (Finset.mem_univ q) hq
  have := hli.fintype_card_le_finrank
  simpa using this

private lemma sum4 {T R Q P : Type} [Fintype T] [Fintype R] [Fintype Q] [Fintype P]
    (f : T → R → Q → P → ℂ) :
    ∑ t, ∑ r, ∑ q, ∑ p, f t r q p = ∑ p, ∑ q, ∑ r, ∑ t, f t r q p := by
  calc ∑ t, ∑ r, ∑ q, ∑ p, f t r q p = ∑ r, ∑ t, ∑ q, ∑ p, f t r q p := Finset.sum_comm
    _ = ∑ r, ∑ q, ∑ t, ∑ p, f t r q p := Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ r, ∑ q, ∑ p, ∑ t, f t r q p :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ r, ∑ p, ∑ t, f t r q p := Finset.sum_comm
    _ = ∑ q, ∑ p, ∑ r, ∑ t, f t r q p := Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ r, ∑ t, f t r q p := Finset.sum_comm

private lemma corrF_expand {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinProb (X × Y × Z)) {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
    (a : P → ℂ) (b : Q → ℂ) (c : R → ℂ)
    (Fp : P → (ι → Y × Z) → ℂ) (gq : Q → (ι → Y) → ℂ) (hr : R → (ι → Z) → ℂ) :
    s7CorrF μ (fun w => ∑ p, a p * Fp p w) (fun y => ∑ q, b q * gq q y)
        (fun z => ∑ r, c r * hr r z) =
      ∑ p, ∑ q, ∑ r, a p * b q * c r * s7CorrF μ (Fp p) (gq q) (hr r) := by
  unfold s7CorrF FinProb.cexpect
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine (sum4 _).trans ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  ring

private lemma corrF_sum_smul {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    {T : Type} (s : Finset T) (a : T → ℂ) (Fp : T → (ι → Y × Z) → ℂ) (gg : (ι → Y) → ℂ)
    (hh : (ι → Z) → ℂ) :
    s7CorrF μ (∑ t ∈ s, a t • Fp t) gg hh = ∑ t ∈ s, a t * s7CorrF μ (Fp t) gg hh := by
  unfold s7CorrF FinProb.cexpect
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun w _ => ?_
  ring

private lemma ccCoef_sum_smul {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb (X × Y × Z))
    (hμ : S7YZImpliesX μ.support) {J : Type} (u : J → X → ℂ) {T : Type} (s : Finset T)
    (a : T → ℂ) (Fp : T → (ι → Y × Z) → ℂ) (c : ι → J) :
    s7CCCoef μ hμ u (∑ t ∈ s, a t • Fp t) c = ∑ t ∈ s, a t * s7CCCoef μ hμ u (Fp t) c := by
  unfold s7CCCoef
  rw [cinner_sum_left]
  simp only [cinner_smul_left]

private lemma constOnCC_sum_smul (hμ : S7YZImpliesX μ.support) {ι : Type} {T : Type}
    (s : Finset T) (a : T → ℂ) (Fp : T → (ι → Y × Z) → ℂ)
    (hs : ∀ t ∈ s, S7ConstOnCC hμ (Fp t)) : S7ConstOnCC hμ (∑ t ∈ s, a t • Fp t) := by
  choose! f hf using hs
  refine ⟨∑ t ∈ s, a t • f t, ?_⟩
  funext w
  simp only [s7W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun t ht => by rw [← hf t ht]; rfl

private lemma combine_aux (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (gg : (S8Rest j → Y) → ℂ) (hh : (S8Rest j → Z) → ℂ)
    (hne : ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖s7CorrF μ (S.FI (Sum.inr t)) gg hh‖ ^ 2 ≠ 0) :
    ∃ Ft : (S8Rest j → Y × Z) → ℂ, S7ConstOnCC hμ Ft ∧
      (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u Ft Dtot) ∧ S7CCNeHom μ hμ Bx.u Ft (d - 1) ∧
      S7CCEffDegGE μ hμ Bx.u Ft (d' - 1) ∧ cl2norm (s7LawYZ μ) Ft = 1 ∧
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖s7CorrF μ (S.FI (Sum.inr t)) gg hh‖ ^ 2 = ‖s7CorrF μ Ft gg hh‖ ^ 2 := by
  classical
  set T := Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0) with hT
  set cs : Fin S.sF → ℂ := fun t => s7CorrF μ (S.FI (Sum.inr t)) gg hh with hcs
  set N2 : ℝ := ∑ t ∈ T, ‖cs t‖ ^ 2 with hN2
  have hN2pos : 0 < N2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun t _ => sq_nonneg _) (Ne.symm hne)
  set N : ℝ := Real.sqrt N2 with hN
  have hNpos : 0 < N := Real.sqrt_pos.2 hN2pos
  have hNsq : N ^ 2 = N2 := Real.sq_sqrt hN2pos.le
  set a : Fin S.sF → ℂ := fun t => star (cs t) / (N : ℂ) with ha
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  refine ⟨∑ t ∈ T, a t • S.FI (Sum.inr t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact constOnCC_sum_smul hμ T a (fun t => S.FI (Sum.inr t)) (fun t _ => (S.F_cc (Sum.inr t)).1)
  · obtain ⟨Dtot0, Da, hDsum, hDa⟩ := hFe
    refine ⟨Dtot0, Da, hDsum, fun c hc a' => ?_⟩
    rw [ccCoef_sum_smul] at hc
    obtain ⟨t, -, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    exact ((S.FI_t t).1 Da hDa) c (right_ne_zero_of_mul hne') a'
  · intro c hc
    rw [ccCoef_sum_smul] at hc
    obtain ⟨t, -, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    exact (S.FI_t t).2.1 c (right_ne_zero_of_mul hne')
  · intro c hc
    rw [ccCoef_sum_smul] at hc
    obtain ⟨t, -, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    exact (S.FI_t t).2.2 c (right_ne_zero_of_mul hne')
  · have hnorm2 : ∀ t, ‖a t‖ ^ 2 = ‖cs t‖ ^ 2 / N2 := fun t => by
      rw [ha]
      simp only [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
      rw [div_pow, hNsq]
    have hci : ((s7LawYZ μ).pi (S8Rest j)).cinner (∑ t ∈ T, a t • S.FI (Sum.inr t))
        (∑ t ∈ T, a t • S.FI (Sum.inr t)) = 1 := by
      rw [cinner_sum_left]
      have : ∀ t ∈ T, ((s7LawYZ μ).pi (S8Rest j)).cinner (a t • S.FI (Sum.inr t))
          (∑ t' ∈ T, a t' • S.FI (Sum.inr t')) = ((‖a t‖ ^ 2 : ℝ) : ℂ) := by
        intro t ht
        rw [cinner_smul_left, cinner_sum_right, Finset.sum_eq_single t]
        · rw [cinner_smul_right, S.orthF_I _ _ (Finset.mem_filter.1 ht).2 (Finset.mem_filter.1 ht).2]
          simp only [↓reduceIte, mul_one]
          rw [Complex.star_def, Complex.mul_conj']
          push_cast; ring
        · intro t' ht' hne'
          rw [cinner_smul_right, S.orthF_I _ _ (Finset.mem_filter.1 ht).2
            (Finset.mem_filter.1 ht').2]
          have : (Sum.inr t : AddChar H ℂ ⊕ Fin S.sF) ≠ Sum.inr t' := fun e =>
            hne' (Sum.inr_injective e).symm
          simp [this]
        · intro hn; exact absurd ht hn
      rw [Finset.sum_congr rfl this]
      rw [← Complex.ofReal_sum, Finset.sum_congr rfl (fun t _ => hnorm2 t), ← Finset.sum_div,
        ← hN2, div_self hN2pos.ne']
      simp
    have hsq : cl2sq (s7LawYZ μ) (∑ t ∈ T, a t • S.FI (Sum.inr t)) = 1 := by
      have := cl2sq_cast (s7LawYZ μ) (∑ t ∈ T, a t • S.FI (Sum.inr t))
      rw [hci] at this
      exact_mod_cast this
    unfold cl2norm
    rw [hsq, Real.sqrt_one]
  · rw [corrF_sum_smul]
    have hc : ∑ t ∈ T, a t * s7CorrF μ (S.FI (Sum.inr t)) gg hh = (N : ℂ) := by
      have : ∀ t ∈ T, a t * s7CorrF μ (S.FI (Sum.inr t)) gg hh = ((‖cs t‖ ^ 2 / N : ℝ) : ℂ) := by
        intro t _
        rw [ha]
        simp only [hcs]
        rw [div_mul_eq_mul_div, Complex.star_def, Complex.conj_mul']
        push_cast; ring
      rw [Finset.sum_congr rfl this, ← Complex.ofReal_sum, ← Finset.sum_div, ← hN2]
      rw [← hNsq]
      push_cast
      field_simp
    rw [hc]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
    exact hNsq.symm

end S9Aux

section S9AuxVan
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private lemma van_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
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

private lemma van_supp (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
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

private lemma van_char_star (χ : AddChar H ℂ) (a : H) : star (χ a) = χ (-a) := by
  rw [AddChar.map_neg_eq_conj]
  rfl

private lemma van_split (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H) (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (χ : AddChar H ℂ) (g : Y → ℂ) (h : Z → ℂ) :
    μ.cexpect (fun p => χ (σ p.1) * g p.2.1 * h p.2.2) =
      (lawY μ).cexpect (fun y => g y * χ (-γ y)) * (lawZ μ).cexpect (fun z => h z * χ (-φ z)) := by
  have step1 : μ.cexpect (fun p => χ (σ p.1) * g p.2.1 * h p.2.2) =
      ∑ p : X × Y × Z, (μ.prob p : ℂ) *
        ((fun v : Y × Z => (g v.1 * χ (-γ v.1)) * (h v.2 * χ (-φ v.2))) (p.2.1, p.2.2)) := by
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h0 : μ.prob p = 0
    · simp [h0]
    · have hs := van_supp μ σ γ φ hunif h0
      have : σ p.1 = -γ p.2.1 + -φ p.2.2 := by
        have : σ p.1 = -(γ p.2.1 + φ p.2.2) := eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
        rw [this, neg_add]
      simp only [this, AddChar.map_add_eq_mul]
      ring
  rw [step1, van_push μ (fun p : X × Y × Z => (p.2.1, p.2.2))
    (fun v : Y × Z => (g v.1 * χ (-γ v.1)) * (h v.2 * χ (-φ v.2)))]
  have step2 : ∀ v : Y × Z, (((mergePush μ fun p : X × Y × Z => (p.2.1, p.2.2)).prob v : ℝ) : ℂ) =
      (((lawY μ).prob v.1 * (lawZ μ).prob v.2 : ℝ) : ℂ) := fun v => by
    rw [← hind v.1 v.2]
    rfl
  simp only [step2, FinProb.cexpect, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  push_cast
  ring

private lemma van_W1 (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) (f : X → ℂ)
    (gg : Y → ℂ) (hh : Z → ℂ) :
    μ.cexpect (fun p => s8W1 hμ f (p.2.1, p.2.2) * gg p.2.1 * hh p.2.2) =
      μ.cexpect (fun p => f p.1 * gg p.2.1 * hh p.2.2) := by
  unfold FinProb.cexpect
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h0 : μ.prob p = 0
  · simp [h0]
  · have : p.1 = s7Pre hμ p.2.1 p.2.2 := s7Pre_unique hμ (show p ∈ μ.support from h0)
    simp only [s8W1, ← this]

private lemma sum_sum3 {A B C D E G : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype G] (T : A ⊕ B → C ⊕ D → E ⊕ G → ℂ) :
    ∑ p, ∑ q, ∑ r, T p q r =
      (∑ a, ∑ c, ∑ e, T (Sum.inl a) (Sum.inl c) (Sum.inl e)) +
      (∑ a, ∑ c, ∑ g, T (Sum.inl a) (Sum.inl c) (Sum.inr g)) +
      (∑ a, ∑ d, ∑ e, T (Sum.inl a) (Sum.inr d) (Sum.inl e)) +
      (∑ a, ∑ d, ∑ g, T (Sum.inl a) (Sum.inr d) (Sum.inr g)) +
      (∑ b, ∑ c, ∑ e, T (Sum.inr b) (Sum.inl c) (Sum.inl e)) +
      (∑ b, ∑ c, ∑ g, T (Sum.inr b) (Sum.inl c) (Sum.inr g)) +
      (∑ b, ∑ d, ∑ e, T (Sum.inr b) (Sum.inr d) (Sum.inl e)) +
      (∑ b, ∑ d, ∑ g, T (Sum.inr b) (Sum.inr d) (Sum.inr g)) := by
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

end S9AuxVan

section S9AuxRot
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {K₁ K₂ : Type}

private lemma rot_unit_cexpect {β : Type} [Fintype β] (π : FinProb β) (G : (Unit → β) → ℂ) :
    (π.pi Unit).cexpect G = π.cexpect (fun a => G (fun _ => a)) := by
  unfold FinProb.cexpect
  exact Fintype.sum_equiv (Equiv.funUnique Unit β) _ _ (fun x => by simp [FinProb.pi])

private lemma rot_W1_cinner (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (f f' : X → ℂ) :
    (s7LawYZ μ).cinner (s8W1 hμ f) (s8W1 hμ f') = (lawX μ).cinner f f' := by
  have h := s7_W_cinner μ hμ (ι := Unit) (fun x => f (x ())) (fun x => f' (x ()))
  unfold FinProb.cinner at h ⊢
  rw [rot_unit_cexpect, rot_unit_cexpect] at h
  simpa [s7W, s8W1] using h

private lemma rot_orth {A P : Type} [Fintype A] [DecidableEq P] (D : FinProb A) (ψ : P → ℝ)
    (ph : P → ℂ) (hph : ∀ p, ψ p ≠ 0 → ‖ph p‖ = 1) (u : P → A → ℂ)
    (h0 : ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 → D.cinner (u p) (u q) = if p = q then 1 else 0) :
    ∀ p q, ψ p ≠ 0 → ψ q ≠ 0 →
      D.cinner (ph p • u p) (ph q • u q) = if p = q then 1 else 0 := by
  intro p q hp hq
  rw [cinner_smul_left, cinner_smul_right, h0 p q hp hq]
  by_cases hpq : p = q
  · subst hpq
    have := hph p hp
    simp only [↓reduceIte, mul_one]
    rw [Complex.star_def, Complex.mul_conj', this]
    simp
  · simp [hpq]

private lemma rot_exists {α : Type} [Fintype α] (D : FinProb α) {s : ℕ}
    (ψ0 : AddChar H ℂ ⊕ Fin s → ℝ) (FJ0 : AddChar H ℂ ⊕ Fin s → α → ℂ)
    (v : AddChar H ℂ → α → ℂ) (hv : ∀ χ, D.cinner (v χ) (v χ) = 1)
    (hspan : ∀ χ, FJ0 (Sum.inl χ) ∈ Submodule.span ℂ {v χ})
    (hort : ∀ p q, ψ0 p ≠ 0 → ψ0 q ≠ 0 → D.cinner (FJ0 p) (FJ0 q) = if p = q then 1 else 0) :
    ∃ (ph : AddChar H ℂ ⊕ Fin s → ℂ) (FJ : AddChar H ℂ ⊕ Fin s → α → ℂ),
      (∀ p, ψ0 p ≠ 0 → ‖ph p‖ = 1) ∧ (∀ p, FJ0 p = ph p • FJ p) ∧
      (∀ χ, FJ (Sum.inl χ) = v χ) ∧ (∀ r, FJ (Sum.inr r) = FJ0 (Sum.inr r)) ∧
      (∀ r, ph (Sum.inr r) = 1) := by
  choose c hc using fun χ => Submodule.mem_span_singleton.1 (hspan χ)
  refine ⟨Sum.elim c (fun _ => 1), Sum.elim v (fun r => FJ0 (Sum.inr r)), ?_, ?_, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩
  · intro p hp
    rcases p with χ | r
    · have h1 := hort (Sum.inl χ) (Sum.inl χ) hp hp
      rw [← hc χ, cinner_smul_left, cinner_smul_right, hv χ] at h1
      simp only [↓reduceIte, mul_one] at h1
      rw [Complex.star_def, Complex.mul_conj'] at h1
      have h2 : ‖c χ‖ ^ 2 = 1 := by exact_mod_cast h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
    · simp
  · intro p
    rcases p with χ | r
    · exact (hc χ).symm
    · simp

private lemma rot_sum {P α : Type} [Fintype P] {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι)
    (κ : P → ℂ) (ph : P → ℂ) (FI0 : P → (S8Rest j → α) → ℂ) (FJ0 FJ : P → α → ℂ)
    (h : ∀ p, FJ0 p = ph p • FJ p) :
    s8SvdSumC j κ (fun p => ph p • FI0 p) FJ = s8SvdSumC j κ FI0 FJ0 := by
  funext y
  unfold s8SvdSumC
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h p]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma ccCoef_smul' (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {J : Type}
    {ι : Type} [Fintype ι] [DecidableEq ι] (u : J → X → ℂ) (a : ℂ) (F : (ι → Y × Z) → ℂ)
    (c : ι → J) : s7CCCoef μ hμ u (a • F) c = a * s7CCCoef μ hμ u F c := by
  unfold s7CCCoef
  exact cinner_smul_left _ _ _ _

private lemma coef_smul' {α : Type} [Fintype α] (D : FinProb α) {J : Type} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u : J → α → ℂ) (a : ℂ) (f : (ι → α) → ℂ) (c : ι → J) :
    s7Coef D u (a • f) c = a * s7Coef D u f c := by
  unfold s7Coef
  exact cinner_smul_left _ _ _ _

private lemma ccPreds_smul (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℂ)
    (F : (ι → Y × Z) → ℂ) :
    ((∃ Dtot, S7CCCompEmbedHom μ hμ u F Dtot) → ∃ Dtot, S7CCCompEmbedHom μ hμ u (a • F) Dtot) ∧
    (∀ d, S7CCNeHom μ hμ u F d → S7CCNeHom μ hμ u (a • F) d) ∧
    (∀ d, S7CCEffDegGE μ hμ u F d → S7CCEffDegGE μ hμ u (a • F) d) ∧
    (S7ConstOnCC hμ F → S7ConstOnCC hμ (a • F)) := by
  have key : ∀ c, s7CCCoef μ hμ u (a • F) c ≠ 0 → s7CCCoef μ hμ u F c ≠ 0 := fun c hc h0 =>
    hc (by rw [ccCoef_smul', h0, mul_zero])
  refine ⟨?_, fun d h c hc => h c (key c hc), fun d h c hc => h c (key c hc), ?_⟩
  · rintro ⟨Dtot, Da, hs, hDa⟩
    exact ⟨Dtot, Da, hs, fun c hc => hDa c (key c hc)⟩
  · rintro ⟨f, rfl⟩
    exact ⟨a • f, rfl⟩

private lemma plainPreds_smul {α : Type} [Fintype α] (D : FinProb α)
    (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → α → ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℂ)
    (f : (ι → α) → ℂ) :
    ((∃ Dtot, S7CompEmbedHom D u f Dtot) → ∃ Dtot, S7CompEmbedHom D u (a • f) Dtot) ∧
    (∀ d, S7NeHom D u f d → S7NeHom D u (a • f) d) := by
  have key : ∀ c, s7Coef D u (a • f) c ≠ 0 → s7Coef D u f c ≠ 0 := fun c hc h0 =>
    hc (by rw [coef_smul', h0, mul_zero])
  refine ⟨?_, fun d h c hc => h c (key c hc)⟩
  rintro ⟨Dtot, Da, hs, hDa⟩
  exact ⟨Dtot, Da, hs, fun c hc => hDa c (key c hc)⟩

end S9AuxRot

/-! ### Theorems of file 4 (targets) -/

section S9SetupThms
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {n : ℕ} {j : Fin n} {μ : FinProb (X × Y × Z)} {hμ : S7YZImpliesX μ.support}
  {σ : X → H} {γ : Y → H} {φ : Z → H} {Sm : Finset X} {Bx : S7ModestBasis (lawX μ) σ Sm}
  {By : S7ModestBasis (lawY μ) γ (∅ : Finset Y)} {Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)}
  {F : (Fin n → Y × Z) → ℂ} {g : (Fin n → Y) → ℂ} {h : (Fin n → Z) → ℂ} {d d' dg dh : ℕ}

/-- Paper IV `lem:reduce-beta#extremizers-and-svd-expansion`, first half: for unit `F ∈ F_{n,d,d'}`,
`g ∈ G_n`, `h ∈ H_n` (arbitrary, not necessarily extremal: the attainment of the supremum, a minor
gap in the source, is not needed since the bounds are proved for every triple, `s8_beta_le_iff_generic`) and any
`j`, the three SVDs of eq. `svd_main` exist, with the phases normalised. -/
theorem s9_svd3_exists (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (hDy : ∀ a, 0 < (lawY μ).prob a)
    (hDz : ∀ a, 0 < (lawZ μ).prob a) (σ : X → H) (γ : Y → H) (φ : Z → H) (Sm : Finset X)
    (Bx : S7ModestBasis (lawX μ) σ Sm) (By : S7ModestBasis (lawY μ) γ (∅ : Finset Y))
    (Bz : S7ModestBasis (lawZ μ) φ (∅ : Finset Z)) (j : Fin n) (F : (Fin n → Y × Z) → ℂ)
    (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ) (d d' dg dh : ℕ)
    (hF : S7ConstOnCC hμ F) (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot)
    (hFn : S7CCNeHom μ hμ Bx.u F d) (hFd : S7CCEffDegGE μ hμ Bx.u F d')
    (hFnorm : cl2norm (s7LawYZ μ) F = 1)
    (hge : ∃ Dtot, S7CompEmbedHom (lawY μ) By.u g Dtot) (hgd : S7NeHom (lawY μ) By.u g dg)
    (hgnorm : cl2norm (lawY μ) g = 1)
    (hhe : ∃ Dtot, S7CompEmbedHom (lawZ μ) Bz.u h Dtot) (hhd : S7NeHom (lawZ μ) Bz.u h dh)
    (hhnorm : cl2norm (lawZ μ) h = 1) :
    Nonempty (S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh) := by
  classical
  obtain ⟨sF, ψ0, FI0, FJ0, hψ0, hdecF, hFχ, hFr, hFcc, hFI0, hFJ0, hFs⟩ :=
    s8_svd_effective μ hμ hDx σ Sm Bx j F d d' hF hFe hFn hFd hFnorm
  obtain ⟨sG, κ0, gI0, gJ0, hκ0, hdecG, hGχ, hGr, hGI0, hGJ0, hGs⟩ :=
    s8_svd (lawY μ) hDy γ By j g dg hge hgd hgnorm
  obtain ⟨sH, ρ0, hI0, hJ0, hρ0, hdecH, hHχ, hHr, hHI0, hHJ0, hHs⟩ :=
    s8_svd (lawZ μ) hDz φ Bz j h dh hhe hhd hhnorm
  have hcz : ∀ r : ℝ, (r : ℂ) ≠ 0 → r ≠ 0 := fun r hr e => hr (by simp [e])
  have hnr : ∀ r : ℝ, ‖(r : ℂ)‖ ^ 2 = r ^ 2 := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  obtain ⟨phF, FJ, hphF1, hFJ0', hFJl, hFJr, hphF3⟩ := rot_exists (s7LawYZ μ) ψ0 FJ0
    (fun χ => s8W1 hμ (fun x => χ (σ x)))
    (fun χ => by rw [rot_W1_cinner]; simpa using Bx.embed_orthonormal χ χ)
    (fun χ => (hFχ χ).1) hFJ0
  obtain ⟨phG, gJ, hphG1, hGJ0', hGJl, hGJr, hphG3⟩ := rot_exists (lawY μ) κ0 gJ0
    (fun χ => fun y => χ (γ y)) (fun χ => by simpa using By.embed_orthonormal χ χ)
    (fun χ => (hGχ χ).1) hGJ0
  obtain ⟨phH, hJ, hphH1, hHJ0', hHJl, hHJr, hphH3⟩ := rot_exists (lawZ μ) ρ0 hJ0
    (fun χ => fun z => χ (φ z)) (fun χ => by simpa using Bz.embed_orthonormal χ χ)
    (fun χ => (hHχ χ).1) hHJ0
  refine ⟨⟨sF, sG, sH, fun p => (ψ0 p : ℂ), fun p => (κ0 p : ℂ), fun p => (ρ0 p : ℂ),
    fun p => phF p • FI0 p, FJ, fun p => phG p • gI0 p, gJ, fun p => phH p • hI0 p, hJ,
    ?_, ?_, ?_, hFJl, hGJl, hHJl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · rw [rot_sum j _ phF FI0 FJ0 FJ hFJ0']; exact hdecF
  · rw [rot_sum j _ phG gI0 gJ0 gJ hGJ0']; exact hdecG
  · rw [rot_sum j _ phH hI0 hJ0 hJ hHJ0']; exact hdecH
  · intro χ
    obtain ⟨-, hc, hn, he⟩ := hFχ χ
    have hp := ccPreds_smul μ hμ Bx.u (phF (Sum.inl χ)) (FI0 (Sum.inl χ))
    exact ⟨hp.1 hc, hp.2.1 d hn, hp.2.2.1 d' he⟩
  · intro r
    simp only [hphF3, one_smul]
    exact (hFr r).1
  · intro r χ
    rw [hFJr]
    exact (hFr r).2 χ
  · intro p
    refine ⟨(ccPreds_smul μ hμ Bx.u (phF p) (FI0 p)).2.2.2 (hFcc p).1, ?_⟩
    rcases p with χ | r
    · exact ⟨fun x => χ (σ x), (hFJl χ).symm⟩
    · obtain ⟨f, hf⟩ := (hFcc (Sum.inr r)).2
      exact ⟨f, hf.trans (hFJr r).symm⟩
  · intro π
    obtain ⟨-, hc, hn⟩ := hGχ π
    have hp := plainPreds_smul (lawY μ) By.u (phG (Sum.inl π)) (gI0 (Sum.inl π))
    exact ⟨hp.1 hc, hp.2 dg hn⟩
  · intro r
    simp only [hphG3, one_smul]
    exact (hGr r).1
  · intro r
    rw [hGJr]
    exact (hGr r).2
  · intro l
    obtain ⟨-, hc, hn⟩ := hHχ l
    have hp := plainPreds_smul (lawZ μ) Bz.u (phH (Sum.inl l)) (hI0 (Sum.inl l))
    exact ⟨hp.1 hc, hp.2 dh hn⟩
  · intro r
    simp only [hphH3, one_smul]
    exact (hHr r).1
  · intro r
    rw [hHJr]
    exact (hHr r).2
  · intro p q hp hq
    exact rot_orth ((s7LawYZ μ).pi (S8Rest j)) ψ0 phF hphF1 FI0 hFI0 p q (hcz _ hp) (hcz _ hq)
  · have hJrel : ∀ p, ψ0 p ≠ 0 → FJ p = (phF p)⁻¹ • FJ0 p := by
      intro p hp
      have hn : phF p ≠ 0 := by
        intro e
        have := hphF1 p hp
        rw [e, norm_zero] at this
        exact zero_ne_one this
      rw [hFJ0' p, smul_smul, inv_mul_cancel₀ hn, one_smul]
    intro p q hp hq
    have hp' := hcz _ hp
    have hq' := hcz _ hq
    show (s7LawYZ μ).cinner (FJ p) (FJ q) = _
    rw [hJrel p hp', hJrel q hq']
    exact rot_orth (s7LawYZ μ) ψ0 (fun p => (phF p)⁻¹)
      (fun p hp => by rw [norm_inv, hphF1 p hp, inv_one]) FJ0 hFJ0 p q hp' hq'
  · intro p q hp hq
    exact rot_orth ((lawY μ).pi (S8Rest j)) κ0 phG hphG1 gI0 hGI0 p q (hcz _ hp) (hcz _ hq)
  · have hJrel : ∀ p, κ0 p ≠ 0 → gJ p = (phG p)⁻¹ • gJ0 p := by
      intro p hp
      have hn : phG p ≠ 0 := by
        intro e
        have := hphG1 p hp
        rw [e, norm_zero] at this
        exact zero_ne_one this
      rw [hGJ0' p, smul_smul, inv_mul_cancel₀ hn, one_smul]
    intro p q hp hq
    have hp' := hcz _ hp
    have hq' := hcz _ hq
    show (lawY μ).cinner (gJ p) (gJ q) = _
    rw [hJrel p hp', hJrel q hq']
    exact rot_orth (lawY μ) κ0 (fun p => (phG p)⁻¹)
      (fun p hp => by rw [norm_inv, hphG1 p hp, inv_one]) gJ0 hGJ0 p q hp' hq'
  · intro p q hp hq
    exact rot_orth ((lawZ μ).pi (S8Rest j)) ρ0 phH hphH1 hI0 hHI0 p q (hcz _ hp) (hcz _ hq)
  · have hJrel : ∀ p, ρ0 p ≠ 0 → hJ p = (phH p)⁻¹ • hJ0 p := by
      intro p hp
      have hn : phH p ≠ 0 := by
        intro e
        have := hphH1 p hp
        rw [e, norm_zero] at this
        exact zero_ne_one this
      rw [hHJ0' p, smul_smul, inv_mul_cancel₀ hn, one_smul]
    intro p q hp hq
    have hp' := hcz _ hp
    have hq' := hcz _ hq
    show (lawZ μ).cinner (hJ p) (hJ q) = _
    rw [hJrel p hp', hJrel q hq']
    exact rot_orth (lawZ μ) ρ0 (fun p => (phH p)⁻¹)
      (fun p hp => by rw [norm_inv, hphH1 p hp, inv_one]) hJ0 hHJ0 p q hp' hq'
  · simp only [hnr]; exact hFs
  · simp only [hnr]; exact hGs
  · simp only [hnr]; exact hHs

/-- the SVD families have at most `|Γ × Φ|`, `|Γ|`, `|Φ|` nonzero coefficients (orthonormal families in
`L²(μ_{y,z})`, `L²(μ_y)`, `L²(μ_z)`): the bound "the number of summands is `≪_m`" of Lemma 8.10 (the
source counts `m³`; with `T ⊆ Γ × Φ` it is `m⁴`). -/
theorem s9_svd3_card_le (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hDy : ∀ a, 0 < (lawY μ).prob a) (hDz : ∀ a, 0 < (lawZ μ).prob a) :
    (Finset.univ.filter fun p => S.ψ p ≠ 0).card ≤ Fintype.card (Y × Z) ∧
      (Finset.univ.filter fun p => S.κ p ≠ 0).card ≤ Fintype.card Y ∧
      (Finset.univ.filter fun p => S.ρ p ≠ 0).card ≤ Fintype.card Z := by
  have _ := hDy
  have _ := hDz
  refine ⟨?_, ?_, ?_⟩
  · exact card_orth_le (s7LawYZ μ) S.FJ _ fun p hp q hq =>
      S.orthF_J p q (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2
  · exact card_orth_le (lawY μ) S.gJ _ fun p hp q hq =>
      S.orthG_J p q (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2
  · exact card_orth_le (lawZ μ) S.hJ _ fun p hp q hq =>
      S.orthH_J p q (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2

/-- eq. `project_eq` (l. 4874-4878), by `s8_corrF_glue`:
`𝔼_{μ^{⊗n}} F g h = ∑_{t, r, s} ψ_t κ_r ρ_s F̂_t(r,s) F̂'_t(r,s)`. -/
theorem s9_project_eq (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh) :
    s7CorrF μ F g h = ∑ p, ∑ q, ∑ r, S.ψ p * S.κ q * S.ρ r * (S.Fhat p q r * S.FhatJ p q r) := by
  have e : s7CorrF μ F g h = s7CorrF μ (s8SvdSumC j S.ψ S.FI S.FJ) (s8SvdSumC j S.κ S.gI S.gJ)
      (s8SvdSumC j S.ρ S.hI S.hJ) := by
    rw [← S.decF, ← S.decG, ← S.decH]
  rw [e]
  unfold s8SvdSumC
  refine (corrF_expand μ S.ψ S.κ S.ρ (fun p w => S.FI p (s8Restr j w) * S.FJ p (w j))
    (fun q y => S.gI q (s8Restr j y) * S.gJ q (y j))
    (fun r z => S.hI r (s8Restr j z) * S.hJ r (z j))).trans ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [s8_corrF_glue]
  rfl

/-- Paper IV `lem:reduce-beta#vanishing-observations`, items (1)-(3) (l. 4908-4931). Item (1) uses
hypothesis 4 (`hunif`, the form of `embedchar_uniform_triple_marginal_x`), item (2) is Claim 8.2 items
(1)-(2) (`s7_ortho_embed_nonembed_1`, `_2`, which also use `hind`, hypothesis 5), item (3) is
`⟨f'_t, π ∘ σ⟩ = 0`. -/
theorem s9_vanishing_observations
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh) :
    (∀ χ π l : AddChar H ℂ,
      S.FhatJ (Sum.inl χ) (Sum.inl π) (Sum.inl l) = if χ = π ∧ π = l then 1 else 0) ∧
    (∀ (χ : AddChar H ℂ) (q : AddChar H ℂ ⊕ Fin S.sG) (r : AddChar H ℂ ⊕ Fin S.sH),
      ((∃ a, q = Sum.inr a) ∨ (∃ b, r = Sum.inr b)) → S.FhatJ (Sum.inl χ) q r = 0) ∧
    (∀ (t : Fin S.sF) (π : AddChar H ℂ), S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inl π) = 0) := by
  have hFJ : ∀ p q r, S.FhatJ p q r = s8Corr1 μ (S.FJ p) (S.gJ q) (S.hJ r) := fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro χ π l
    rw [hFJ, S.FJ_chi, S.gJ_chi, S.hJ_chi]
    unfold s8Corr1
    rw [van_W1 μ hμ (fun x => χ (σ x)) (fun y => π (γ y)) (fun z => l (φ z)),
      van_split μ σ γ φ hunif hind χ (fun y => π (γ y)) (fun z => l (φ z))]
    have h1 : (lawY μ).cexpect (fun y => π (γ y) * χ (-γ y)) = if π = χ then 1 else 0 := by
      have := By.embed_orthonormal π χ
      simpa [FinProb.cinner, van_char_star] using this
    have h2 : (lawZ μ).cexpect (fun z => l (φ z) * χ (-φ z)) = if l = χ then 1 else 0 := by
      have := Bz.embed_orthonormal l χ
      simpa [FinProb.cinner, van_char_star] using this
    rw [h1, h2]
    have a' : π ≠ χ → χ ≠ π := fun e e' => e e'.symm
    have b' : l ≠ χ → χ ≠ l := fun e e' => e e'.symm
    by_cases a : π = χ <;> by_cases b : l = χ
    · subst a; subst b; simp
    · simp [a, b, b' b]
    · simp [a, b, a' a]
    · simp [a, b, a' a]
  · intro χ q r hqr
    rw [hFJ, S.FJ_chi]
    unfold s8Corr1
    rw [van_W1 μ hμ (fun x => χ (σ x)) (S.gJ q) (S.hJ r)]
    rcases hqr with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact s7_ortho_embed_nonembed_1 μ σ γ φ hunif hind (fun x => χ (σ x))
        (Submodule.subset_span ⟨χ, rfl⟩) (S.gJ (Sum.inr a)) (S.gJ_r a) (S.hJ r)
    · exact s7_ortho_embed_nonembed_2 μ σ γ φ hunif hind (fun x => χ (σ x))
        (Submodule.subset_span ⟨χ, rfl⟩) (S.gJ q) (S.hJ (Sum.inr b)) (S.hJ_s b)
  · intro t π
    rw [hFJ, S.gJ_chi, S.hJ_chi]
    unfold s8Corr1
    have key := S.FJ_t t π
    have key' : μ.cexpect (fun p => S.FJ (Sum.inr t) (p.2.1, p.2.2) *
        star (s8W1 hμ (fun x => π (σ x)) (p.2.1, p.2.2))) = 0 := by
      refine Eq.trans ?_ key
      exact van_push μ (fun p : X × Y × Z => (p.2.1, p.2.2))
        (fun v => S.FJ (Sum.inr t) v * star (s8W1 hμ (fun x => π (σ x)) v))
    rw [← key']
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h0 : μ.prob p = 0
    · simp [h0]
    · have hs := van_supp μ σ γ φ hunif h0
      have hpre : p.1 = s7Pre hμ p.2.1 p.2.2 := s7Pre_unique hμ (show p ∈ μ.support from h0)
      have e : star (s8W1 hμ (fun x => π (σ x)) (p.2.1, p.2.2)) = π (γ p.2.1) * π (φ p.2.2) := by
        simp only [s8W1, ← hpre]
        rw [van_char_star]
        have : -σ p.1 = γ p.2.1 + φ p.2.2 := by
          rw [neg_eq_iff_eq_neg]
          exact eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
        rw [this, AddChar.map_add_eq_mul]
      show (μ.prob p : ℂ) * (S.FJ (Sum.inr t) (p.2.1, p.2.2) * π (γ p.2.1) * π (φ p.2.2)) =
        (μ.prob p : ℂ) * (S.FJ (Sum.inr t) (p.2.1, p.2.2) *
          star (s8W1 hμ (fun x => π (σ x)) (p.2.1, p.2.2)))
      rw [e]
      ring

/-- eq. `large_large_0` (l. 4934-4949): the five surviving sums of `𝔼 F g h` (`T`, `R`, `S` are the
`inr` indices; the second sum has `π ≠ λ`, the third `r ∈ R, λ ∈ Ĥ`, the fourth `π ∈ Ĥ, s ∈ S`). -/
theorem s9_large_large_expansion
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0)
    (hind : ∀ (y : Y) (z : Z), (s7LawYZ μ).prob (y, z) = (lawY μ).prob y * (lawZ μ).prob z)
    (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh) :
    s7CorrF μ F g h =
      (∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
        S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ)) +
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
            S.FhatJ (Sum.inr t) (Sum.inr r) (Sum.inr s))) := by
  have v := s9_vanishing_observations hunif hind S
  have z1 : ∀ χ π s, S.FhatJ (Sum.inl χ) (Sum.inl π) (Sum.inr s) = 0 := fun χ π s =>
    v.2.1 χ (Sum.inl π) (Sum.inr s) (Or.inr ⟨s, rfl⟩)
  have z2 : ∀ χ r l, S.FhatJ (Sum.inl χ) (Sum.inr r) (Sum.inl l) = 0 := fun χ r l =>
    v.2.1 χ (Sum.inr r) (Sum.inl l) (Or.inl ⟨r, rfl⟩)
  have z3 : ∀ χ r s, S.FhatJ (Sum.inl χ) (Sum.inr r) (Sum.inr s) = 0 := fun χ r s =>
    v.2.1 χ (Sum.inr r) (Sum.inr s) (Or.inl ⟨r, rfl⟩)
  rw [s9_project_eq S, sum_sum3]
  simp only [z1, z2, z3, mul_zero, Finset.sum_const_zero, add_zero]
  have e1 : (∑ χ : AddChar H ℂ, ∑ π : AddChar H ℂ, ∑ l : AddChar H ℂ,
      S.ψ (Sum.inl χ) * S.κ (Sum.inl π) * S.ρ (Sum.inl l) *
        (S.Fhat (Sum.inl χ) (Sum.inl π) (Sum.inl l) * S.FhatJ (Sum.inl χ) (Sum.inl π) (Sum.inl l))) =
      ∑ χ : AddChar H ℂ, S.ψ (Sum.inl χ) * S.κ (Sum.inl χ) * S.ρ (Sum.inl χ) *
        S.Fhat (Sum.inl χ) (Sum.inl χ) (Sum.inl χ) := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp only [v.1, mul_ite, mul_one, mul_zero]
    simp [ite_and, Finset.sum_ite_eq]
  have e2 : (∑ t : Fin S.sF, ∑ π : AddChar H ℂ, ∑ l : AddChar H ℂ,
      S.ψ (Sum.inr t) * S.κ (Sum.inl π) * S.ρ (Sum.inl l) *
        (S.Fhat (Sum.inr t) (Sum.inl π) (Sum.inl l) * S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inl l))) =
      ∑ t : Fin S.sF, ∑ π : AddChar H ℂ, ∑ l : AddChar H ℂ, if π ≠ l then
        S.ψ (Sum.inr t) * S.κ (Sum.inl π) * S.ρ (Sum.inl l) *
          (S.Fhat (Sum.inr t) (Sum.inl π) (Sum.inl l) *
            S.FhatJ (Sum.inr t) (Sum.inl π) (Sum.inl l)) else 0 := by
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun π _ =>
      Finset.sum_congr rfl fun l _ => ?_
    by_cases hπ : π = l
    · subst hπ; simp [v.2.2 t π]
    · simp [hπ]
  rw [e1, e2]
  ring

/-- Paper IV `lem:reduce-beta#choose-partition` (l. 4887-4903), influence form: if `n ≥ (10/η) d` there is a
coordinate `j` with `½ I_{j,non-embed}[F] ≤ η` (the average over `j` of `½ I_j[F]` is `d/n ≤ η/10`,
Fact 4.12 and `‖F‖₂ = 1`; Markov is used only to get one `j`). By `s8_coefs_svd_effective` this is
`∑_{t ∈ T} |ψ_t|² ≤ η` for the SVD along `j` (eq. `small_nonembed_inf`). `0 < n` is a typing hypothesis (a coordinate
`j` must exist); the source's "`n ≥ 10d/η`" is `10 d ≤ η n`. -/
theorem s9_choose_partition (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hDx : ∀ a, 0 < (lawX μ).prob a) (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    (σ : X → H) (Sm : Finset X) (Bx : S7ModestBasis (lawX μ) σ Sm) (hn : 0 < n)
    (F : (Fin n → Y × Z) → ℂ) (hF : S7ConstOnCC hμ F) (d : ℕ) (hFn : S7CCNeHom μ hμ Bx.u F d)
    (hFnorm : cl2norm (s7LawYZ μ) F = 1) {η : ℝ} (hη : 0 < η) (hnd : 10 * (d : ℝ) ≤ η * n) :
    ∃ j : Fin n, 1 / 2 * s7CCNonEmbedInf μ hμ hocc σ hF j ≤ η := by
  classical
  have _ := hη
  set f := s7WInv hocc hF with hfdef
  have hW : s7W hμ f = F := s7W_s7WInv hocc hF
  have hONB := s7_modestBasis_isONB (lawX μ) σ Sm hDx Bx
  have hsq : cl2sq (lawX μ) f = 1 := by
    have h1 : cl2norm (lawX μ) f = 1 := by rw [← s7_cl2norm_W μ hμ f, hW]; exact hFnorm
    have h2 : Real.sqrt (cl2sq (lawX μ) f) = 1 := h1
    exact Real.sqrt_eq_one.1 h2
  have hpars : cl2sq (lawX μ) f = ∑ c : Fin n → Bx.J, ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 :=
    s7_parseval (lawX μ) hDx Bx.u hONB f
  have htot := s7_nonembed_total_inf_formula (lawX μ) σ Sm hDx Bx f
  have hcoef : ∀ c, s7Coef (lawX μ) Bx.u f c = s7CCCoef μ hμ Bx.u F c := fun c => by
    rw [← hW, s7CCCoef_W]
  have hsum : ∑ c : Fin n → Bx.J, (s7NeDeg c : ℝ) * ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 = d := by
    have : ∀ c : Fin n → Bx.J, (s7NeDeg c : ℝ) * ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 =
        d * ‖s7Coef (lawX μ) Bx.u f c‖ ^ 2 := fun c => by
      by_cases hc : s7Coef (lawX μ) Bx.u f c = 0
      · simp [hc]
      · rw [hcoef] at hc
        rw [hFn c hc]
    rw [Finset.sum_congr rfl fun c _ => this c, ← Finset.mul_sum, ← hpars, hsq, mul_one]
  have hI : ∑ i : Fin n, 1 / 2 * s7CCNonEmbedInf μ hμ hocc σ hF i = d := by
    rw [← Finset.mul_sum]
    have : ∑ i : Fin n, s7CCNonEmbedInf μ hμ hocc σ hF i = 2 * d := by
      unfold s7CCNonEmbedInf
      have := htot
      unfold s7NonEmbedTotalInf at this
      rw [this, hsum]
    rw [this]; ring
  have hle : ∑ i : Fin n, 1 / 2 * s7CCNonEmbedInf μ hμ hocc σ hF i ≤ ∑ _i : Fin n, η := by
    rw [hI]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩) hle
  exact ⟨i, hi⟩

/-- Paper IV `lem:bound-additivebase-beta#combine-F-t` (l. 5110-5120), first half: for fixed `s` (resp. `r`)
the combination `F̃ = ∑_t conj(F̂_t(χ*, s)) F_t / ‖·‖` over `t ∈ T = {ψ_t ≠ 0}` is a unit vector of
`F_{n-1,d-1,d'-1}` (on `I = [n] \ {j}`: it inherits the embedding degrees of `F`, which is why
`s8_svd_effective` states the inheritance) and `∑_t |F̂_t(χ*,s)|² = |𝔼 F̃ g_{χ*} h_s|²`. -/
theorem s9_combine_F_t (S : S9Svd3 j μ hμ σ γ φ Bx By Bz F g h d d' dg dh)
    (hFe : ∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u F Dtot) (χs : AddChar H ℂ) :
    (∀ s : AddChar H ℂ ⊕ Fin S.sH,
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖S.Fhat (Sum.inr t) (Sum.inl χs) s‖ ^ 2 ≠ 0 →
      ∃ Ft : (S8Rest j → Y × Z) → ℂ, S7ConstOnCC hμ Ft ∧
        (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u Ft Dtot) ∧ S7CCNeHom μ hμ Bx.u Ft (d - 1) ∧
        S7CCEffDegGE μ hμ Bx.u Ft (d' - 1) ∧ cl2norm (s7LawYZ μ) Ft = 1 ∧
        ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
          ‖S.Fhat (Sum.inr t) (Sum.inl χs) s‖ ^ 2 =
          ‖s7CorrF μ Ft (S.gI (Sum.inl χs)) (S.hI s)‖ ^ 2) ∧
    (∀ r : AddChar H ℂ ⊕ Fin S.sG,
      ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
        ‖S.Fhat (Sum.inr t) r (Sum.inl χs)‖ ^ 2 ≠ 0 →
      ∃ Ft : (S8Rest j → Y × Z) → ℂ, S7ConstOnCC hμ Ft ∧
        (∃ Dtot, S7CCCompEmbedHom μ hμ Bx.u Ft Dtot) ∧ S7CCNeHom μ hμ Bx.u Ft (d - 1) ∧
        S7CCEffDegGE μ hμ Bx.u Ft (d' - 1) ∧ cl2norm (s7LawYZ μ) Ft = 1 ∧
        ∑ t ∈ Finset.univ.filter (fun t : Fin S.sF => S.ψ (Sum.inr t) ≠ 0),
          ‖S.Fhat (Sum.inr t) r (Sum.inl χs)‖ ^ 2 =
          ‖s7CorrF μ Ft (S.gI r) (S.hI (Sum.inl χs))‖ ^ 2) := by
  refine ⟨fun s hne => ?_, fun r hne => ?_⟩
  · exact combine_aux S hFe (S.gI (Sum.inl χs)) (S.hI s) hne
  · exact combine_aux S hFe (S.gI r) (S.hI (Sum.inl χs)) hne

end S9SetupThms

end TrackB
end RestrictedPolynomials
end
