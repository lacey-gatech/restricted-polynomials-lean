module

public import RestrictedPolynomials.TrackB.MaxTInduct

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section Support
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

def diagSupportSet {W V : Type} (a : W → W) (S3 : Set (↥(Set.range a) × Y × V))
    (isDiagX : X → W → Prop) (isDiagZ : Z → V → Prop) : Set (X × Y × Z) :=
  {p | ∃ (v : W) (w : V), isDiagX p.1 v ∧ isDiagZ p.2.2 w ∧
    (⟨a v, Set.mem_range_self _⟩, p.2.1, w) ∈ S3}

abbrev m65Phi (μ : FinProb (X × Y × Z)) {ℓ₁ : ℕ} (h₁ : Odd ℓ₁) : Type :=
  PathX (lawSwapXZ μ) ℓ₁ h₁
abbrev m65Sig (μ : FinProb (X × Y × Z)) {ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂) : Type :=
  PathX (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂
abbrev m65Mu2 (μ : FinProb (X × Y × Z)) {ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂) :
    FinProb (m65Sig μ h₁ h₂ × Y × m65Phi μ h₁) :=
  pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂

theorem m65_D_ssubset {W V : Type} (a : W → W) (S3 : Set (↥(Set.range a) × Y × V))
    (isDiagX : X → W → Prop) (isDiagZ : Z → V → Prop)
    (hfunX : ∀ x v v', isDiagX x v → isDiagX x v' → v = v') (S : Set (X × Y × Z))
    (hS : InT S) (hfm : mergeImpliesX S)
    (h31 : ∀ p ∈ S, ∃ (v : W) (w : V), isDiagX p.1 v ∧ isDiagZ p.2.2 w ∧
      (⟨a v, Set.mem_range_self _⟩, p.2.1, w) ∈ S3)
    (x₁ x₂ : X) (hne : x₁ ≠ x₂) (v₁ v₂ : W) (hv₁ : isDiagX x₁ v₁) (hv₂ : isDiagX x₂ v₂)
    (hav : a v₁ = a v₂) :
    S ⊂ diagSupportSet a S3 isDiagX isDiagZ := by
  have hsub : S ⊆ diagSupportSet a S3 isDiagX isDiagZ := fun p hp => by
    obtain ⟨v, w, h1, h2, h3⟩ := h31 p hp
    exact ⟨v, w, h1, h2, h3⟩
  refine ⟨hsub, fun hD => ?_⟩
  obtain ⟨y', z', hatom⟩ := MaxT.PairwiseConnected3.exists_atom_x hS.1 x₂
  obtain ⟨v, w, h1, h2, h3⟩ := h31 _ hatom
  have hv : v = v₂ := hfunX x₂ v v₂ h1 hv₂
  subst hv
  have hmem : (x₁, y', z') ∈ diagSupportSet a S3 isDiagX isDiagZ := by
    refine ⟨v₁, w, hv₁, h2, ?_⟩
    have : (⟨a v₁, Set.mem_range_self _⟩ : ↥(Set.range a)) = ⟨a v, Set.mem_range_self _⟩ :=
      Subtype.ext hav
    simpa [this] using h3
  have hS1 : (x₁, y', z') ∈ S := hD hmem
  exact hne (hfm y' z' x₁ x₂ hS1 hatom)

theorem m65_D_inT {W V : Type} (a : W → W) (S3 : Set (↥(Set.range a) × Y × V))
    (isDiagX : X → W → Prop) (isDiagZ : Z → V → Prop) (S : Set (X × Y × Z))
    (hS : InT S)
    (h31 : ∀ p ∈ S, ∃ (v : W) (w : V), isDiagX p.1 v ∧ isDiagZ p.2.2 w ∧
      (⟨a v, Set.mem_range_self _⟩, p.2.1, w) ∈ S3) :
    InT (diagSupportSet a S3 isDiagX isDiagZ) := by
  refine hS.mono fun p hp => ?_
  obtain ⟨v, w, h1, h2, h3⟩ := h31 p hp
  exact ⟨v, w, h1, h2, h3⟩

private theorem m65_sum_filter_snd {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] (F : A × B × C → ℝ) (y : B) :
    ∑ p ∈ Finset.univ.filter (fun p : A × B × C => p.2.1 = y), F p =
      ∑ a, ∑ c, F (a, y, c) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private theorem m65_finprob_ext {α : Type} [Fintype α] {A B : FinProb α}
    (h : ∀ a, A.prob a = B.prob a) : A = B := by
  obtain ⟨p1, n1, s1⟩ := A
  obtain ⟨p2, n2, s2⟩ := B
  have : p1 = p2 := funext h
  subst this
  rfl

theorem m65_exists_lawD {W V : Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (a : W → W) (isDiagX : X → W → Prop) (isDiagZ : Z → V → Prop)
    (hfunX : ∀ x v v', isDiagX x v → isDiagX x v' → v = v')
    (hinjX : ∀ x x' v, isDiagX x v → isDiagX x' v → x = x')
    (hfunZ : ∀ z w w', isDiagZ z w → isDiagZ z w' → w = w')
    (hinjZ : ∀ z z' w, isDiagZ z w → isDiagZ z' w → z = z')
    (hexX : ∀ x, ∃ v, isDiagX x v) (hexZ : ∀ z, ∃ w, isDiagZ z w)
    (μ2 : FinProb (W × Y × V)) (νc : FinProb (↥(Set.range a) × Y × V)) {α₂ α' : ℝ}
    (hα₂ : 0 < α₂) (hα' : 0 < α')
    (hdiag : ∀ x v, isDiagX x v → α₂ ≤ (lawX μ2).prob v)
    (hνc : ∀ q ∈ νc.support, α' ≤ νc.prob q)
    (hsupp : ∀ q ∈ νc.support,
      (∃ x v, isDiagX x v ∧ (⟨a v, Set.mem_range_self _⟩ : ↥(Set.range a)) = q.1) ∧
      ∃ z, isDiagZ z q.2.2) :
    ∃ D : FinProb (X × Y × Z), D.support = diagSupportSet a νc.support isDiagX isDiagZ ∧
      (∀ p ∈ D.support, α₂ * α' ≤ D.prob p) ∧ lawY D = lawY νc := by
  classical
  choose dx hdx using hexX
  choose dz hdz using hexZ
  have hx_eq : ∀ x v, isDiagX x v → v = dx x := fun x v h => hfunX x v _ h (hdx x)
  have hz_eq : ∀ z w, isDiagZ z w → w = dz z := fun z w h => hfunZ z w _ h (hdz z)
  have dxinj : Function.Injective dx := fun x x' h =>
    hinjX x x' (dx x) (hdx x) (h ▸ hdx x')
  have dzinj : Function.Injective dz := fun z z' h =>
    hinjZ z z' (dz z) (hdz z) (h ▸ hdz z')
  let rr : X → ↥(Set.range a) := fun x => ⟨a (dx x), Set.mem_range_self _⟩
  let lam : X → ℝ := fun x => (lawX μ2).prob (dx x)
  let fib : ↥(Set.range a) → ℝ := fun r => ∑ x ∈ Finset.univ.filter (fun x => rr x = r), lam x
  have lam_nonneg : ∀ x, 0 ≤ lam x := fun x => (lawX μ2).nonneg _
  have lam_ge : ∀ x, α₂ ≤ lam x := fun x => hdiag x (dx x) (hdx x)
  have fib_ge : ∀ x, lam x ≤ fib (rr x) := fun x =>
    Finset.single_le_sum (f := lam) (fun i _ => lam_nonneg i)
      (Finset.mem_filter.2 ⟨Finset.mem_univ x, rfl⟩)
  have fib_pos : ∀ x, 0 < fib (rr x) := fun x => lt_of_lt_of_le (lt_of_lt_of_le hα₂ (lam_ge x)) (fib_ge x)
  have sum_lam_le : ∑ x, lam x ≤ 1 := by
    have h1 : ∑ x, lam x = ∑ w ∈ Finset.univ.image dx, (lawX μ2).prob w := by
      rw [Finset.sum_image (fun x _ x' _ h => dxinj h)]
    rw [h1, ← (lawX μ2).sum_eq_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => (lawX μ2).nonneg i)
  have fib_le : ∀ r, fib r ≤ 1 := fun r =>
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => lam_nonneg i)) sum_lam_le
  let D0 : X × Y × Z → ℝ := fun p =>
    νc.prob (rr p.1, p.2.1, dz p.2.2) * (lam p.1 / fib (rr p.1))
  have D0_nonneg : ∀ p, 0 ≤ D0 p := fun p =>
    mul_nonneg (νc.nonneg _) (div_nonneg (lam_nonneg _) (le_of_lt (fib_pos _)))
  have hz0 : ∀ r y w, (∀ z, w ≠ dz z) → νc.prob (r, y, w) = 0 := by
    intro r y w hw
    by_contra hne
    obtain ⟨_, z, hz⟩ := hsupp (r, y, w) hne
    exact hw z (hz_eq z w hz)
  have stepA : ∀ r y, ∑ z, νc.prob (r, y, dz z) = ∑ w, νc.prob (r, y, w) := by
    intro r y
    rw [← Finset.sum_image (f := fun w => νc.prob (r, y, w)) (fun z _ z' _ h => dzinj h)]
    refine Finset.sum_subset (Finset.subset_univ _) fun w _ hw => hz0 r y w fun z hz => hw ?_
    exact Finset.mem_image.2 ⟨z, Finset.mem_univ _, hz.symm⟩
  have stepT : ∀ r y, (∑ x ∈ Finset.univ.filter (fun x => rr x = r), lam x / fib r) *
      (∑ w, νc.prob (r, y, w)) = ∑ w, νc.prob (r, y, w) := by
    intro r y
    by_cases hne : (Finset.univ.filter (fun x => rr x = r)).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxr : rr x = r := (Finset.mem_filter.1 hx).2
      have hp : 0 < fib r := hxr ▸ fib_pos x
      rw [← Finset.sum_div]
      change fib r / fib r * _ = _
      rw [div_self hp.ne', one_mul]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : ∀ w, νc.prob (r, y, w) = 0 := by
        intro w
        by_contra hw
        obtain ⟨⟨x, v, hv, hr⟩, _⟩ := hsupp (r, y, w) hw
        have hvx := hx_eq x v hv
        subst hvx
        have : x ∈ Finset.univ.filter (fun x => rr x = r) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ x, hr⟩
        rw [hne] at this
        simp at this
      simp [this]
  have K : ∀ y, ∑ x, ∑ z, D0 (x, y, z) = ∑ r, ∑ w, νc.prob (r, y, w) := by
    intro y
    have hB : ∀ x, ∑ z, D0 (x, y, z) =
        (lam x / fib (rr x)) * ∑ w, νc.prob (rr x, y, w) := by
      intro x
      simp only [D0]
      rw [← stepA, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => mul_comm _ _
    simp_rw [hB]
    rw [← Finset.sum_fiberwise Finset.univ rr]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : ∀ x ∈ Finset.univ.filter (fun x => rr x = r),
        (lam x / fib (rr x)) * ∑ w, νc.prob (rr x, y, w) =
          (lam x / fib r) * ∑ w, νc.prob (r, y, w) := fun x hx => by
      rw [(Finset.mem_filter.1 hx).2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    exact stepT r y
  have htot : ∑ p, D0 p = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp_rw [K]
    rw [Finset.sum_comm, ← νc.sum_eq_one]
    simp_rw [Fintype.sum_prod_type]
  let D : FinProb (X × Y × Z) := ⟨D0, D0_nonneg, htot⟩
  have hDprob : ∀ p, D.prob p = D0 p := fun _ => rfl
  have hsuppD : D.support = diagSupportSet a νc.support isDiagX isDiagZ := by
    ext ⟨x, y, z⟩
    constructor
    · intro h
      have h' : D0 (x, y, z) ≠ 0 := h
      have h1 : νc.prob (rr x, y, dz z) ≠ 0 := left_ne_zero_of_mul h'
      exact ⟨dx x, dz z, hdx x, hdz z, h1⟩
    · rintro ⟨v, w, hv, hw, hm⟩
      have hv' := hx_eq x v hv
      have hw' := hz_eq z w hw
      subst hv'
      subst hw'
      have h1 : νc.prob (rr x, y, dz z) ≠ 0 := hm
      exact mul_ne_zero h1
        (div_ne_zero (lt_of_lt_of_le hα₂ (lam_ge x)).ne' (fib_pos x).ne')
  refine ⟨D, hsuppD, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, y, z⟩ := p
    have h' : D0 (x, y, z) ≠ 0 := hp
    have h1 : νc.prob (rr x, y, dz z) ≠ 0 := left_ne_zero_of_mul h'
    have h2 : α' ≤ νc.prob (rr x, y, dz z) := hνc _ h1
    have h3 : α₂ ≤ lam x / fib (rr x) :=
      le_trans (lam_ge x) (le_div_self (lam_nonneg x) (fib_pos x) (fib_le _))
    exact mul_le_mul h2 h3 hα₂.le (le_trans hα'.le h2) |>.trans_eq' (mul_comm _ _)
  · refine m65_finprob_ext fun y => ?_
    change ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.1 = y), D0 p =
      ∑ p ∈ Finset.univ.filter (fun p : ↥(Set.range a) × Y × V => p.2.1 = y), νc.prob p
    rw [m65_sum_filter_snd, m65_sum_filter_snd]
    exact K y


/-! ### Supplement E `lem:III-prime`, `lem:VII-prime` (support level) -/

/-- `R_III` of l. 9054-9093 with `Γ' = Γ`: `N_y ∩ (Sg × Γ × Φ')`, `N_y = {(x,y,z) : ∃ y₀, (x,y₀,z) ∈ S}`
(reading (6.1) of Supplement E). -/
def m65RIII (νs : Set (X × Y × Z)) (Sg : Finset X) (Φ' : Finset Z) : Set (X × Y × Z) :=
  {p | p.1 ∈ Sg ∧ p.2.2 ∈ Φ' ∧ ∃ y₀ : Y, (p.1, y₀, p.2.2) ∈ νs}

/-- `R_VII` of Lemma VII-prime, `Mod(x) = Sm` for `x ∈ Sm`, `{x}` otherwise. -/
def m65RVII (νs : Set (X × Y × Z)) (Sg Sm : Finset X) (Φ' : Finset Z) : Set (X × Y × Z) :=
  {p | p.1 ∈ Sg ∧ p.2.2 ∈ Φ' ∧ ∃ x : X, (x, p.2.1, p.2.2) ∈ νs ∧
    (p.1 = x ∨ (x ∈ Sm ∧ p.1 ∈ Sm))}

/-- the lift of a set along `a : Sg' → Sg_ν` to the alphabets `Sg' × Γ × Φ'` of `ν̃`. -/
def m65LiftSet {U : Type} (a : U → X) (Φ' : Finset Z) (R : Set (X × Y × Z)) :
    Set (U × Y × ↥Φ') :=
  {q | (a q.1, q.2.1, q.2.2.1) ∈ R}

theorem m65_III_ssubset {U : Type} (a : U → X) (Sg : Finset X) (Φ' : Finset Z)
    (νs : Set (X × Y × Z)) (νt : Set (U × Y × ↥Φ')) (haSg : ∀ u, a u ∈ Sg)
    (hsub : ∀ q ∈ νt, (a q.1, q.2.1, q.2.2.1) ∈ νs) (hfm : mergeImpliesY νt)
    (h2 : 2 ≤ Fintype.card Y) (hne : νt.Nonempty) :
    νt ⊂ m65LiftSet a Φ' (m65RIII νs Sg Φ') := by
  have hsub' : νt ⊆ m65LiftSet a Φ' (m65RIII νs Sg Φ') := fun q hq =>
    ⟨haSg q.1, q.2.2.2, q.2.1, hsub q hq⟩
  refine ⟨hsub', fun hD => ?_⟩
  obtain ⟨⟨u, y, w⟩, hq⟩ := hne
  obtain ⟨y', hy'⟩ := Fintype.exists_ne_of_one_lt_card h2 y
  have hin : (u, y', w) ∈ m65LiftSet a Φ' (m65RIII νs Sg Φ') :=
    ⟨haSg u, w.2, y, hsub _ hq⟩
  exact hy' (hfm u w y' y (hD hin) hq)

theorem m65_III_inT {U : Type} (a : U → X) (Sg : Finset X) (Φ' : Finset Z)
    (νs : Set (X × Y × Z)) (νt : Set (U × Y × ↥Φ')) (haSg : ∀ u, a u ∈ Sg)
    (hsub : ∀ q ∈ νt, (a q.1, q.2.1, q.2.2.1) ∈ νs) (hT : InT νt) :
    InT (m65LiftSet a Φ' (m65RIII νs Sg Φ')) :=
  hT.mono fun q hq => ⟨haSg q.1, q.2.2.2, q.2.1, hsub q hq⟩

theorem m65_VII_ssubset {U : Type} (a : U → X) (Sg Sm : Finset X) (Φ' : Finset Z)
    (νs : Set (X × Y × Z)) (νt : Set (U × Y × ↥Φ')) (haSg : ∀ u, a u ∈ Sg)
    (hsurj : ∀ x' ∈ Sg, ∃ u, a u = x') (hSSg : Sm ⊆ Sg) (h2 : 2 ≤ Sm.card)
    (hsub : ∀ q ∈ νt, (a q.1, q.2.1, q.2.2.1) ∈ νs) (hT : InT νt) (hfm : mergeImpliesX νt) :
    νt ⊂ m65LiftSet a Φ' (m65RVII νs Sg Sm Φ') := by
  have hsub' : νt ⊆ m65LiftSet a Φ' (m65RVII νs Sg Sm Φ') := fun q hq =>
    ⟨haSg q.1, q.2.2.2, a q.1, hsub q hq, Or.inl rfl⟩
  refine ⟨hsub', fun hD => ?_⟩
  obtain ⟨u₀, hu₀, u₀', hu₀', hne⟩ := Finset.one_lt_card.1 h2
  obtain ⟨up, hup⟩ := hsurj u₀ (hSSg hu₀)
  obtain ⟨up', hup'⟩ := hsurj u₀' (hSSg hu₀')
  obtain ⟨y, w, hatom⟩ := MaxT.PairwiseConnected3.exists_atom_x hT.1 up
  have hin : (up', y, w) ∈ m65LiftSet a Φ' (m65RVII νs Sg Sm Φ') :=
    ⟨haSg up', w.2, u₀, by simpa [hup] using hsub _ hatom, Or.inr ⟨hu₀, by rw [hup']; exact hu₀'⟩⟩
  have heq : up' = up := hfm y w up' up (hD hin) hatom
  exact hne (by rw [← hup, ← hup', heq])

theorem m65_VII_inT {U : Type} (a : U → X) (Sg Sm : Finset X) (Φ' : Finset Z)
    (νs : Set (X × Y × Z)) (νt : Set (U × Y × ↥Φ')) (haSg : ∀ u, a u ∈ Sg)
    (hsub : ∀ q ∈ νt, (a q.1, q.2.1, q.2.2.1) ∈ νs) (hT : InT νt) :
    InT (m65LiftSet a Φ' (m65RVII νs Sg Sm Φ')) :=
  hT.mono fun q hq => ⟨haSg q.1, q.2.2.2, a q.1, hsub q hq, Or.inl rfl⟩


end Support
end MaxT
end TrackB
end RestrictedPolynomials
end
