module

public import RestrictedPolynomials.TrackB.Embedding
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Track B: master embeddings, saturation, embedding functions, Lemma 3.3

Paper IV items: `definition-master-embedding` (Definition 3.5, L1691-1696),
`def:master` (`sharp`, L1941-1946), `definition-equivalent-embeddings` (L2257-2271),
`definition-saturated` (L2004-2009), `definition-embedding-functions` (with step
`span-equals-fibre-constant`, L2368-2389), `lem:bound-k-in-embed` (Lemma 3.3, L1550-1568).

Readings: `bound_k_in_embed` carries the normalisation `ZeroInImage3` and `p.Prime`;
`IsMasterEmbedding` quantifies over normalised embeddings; `[Finite H]` is assumed for the
`embedSpan` lemmas.
-/

@[expose] public section

open Finset

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

universe u

section Master
variable {X Y Z : Type u}

/-- normalisation convention of paper IV l. 1729-1733: `0` lies in the image of each component. -/
def ZeroInImage3 {H : Type*} [Zero H] (σ : X → H) (γ : Y → H) (φ : Z → H) : Prop :=
  (∃ x, σ x = 0) ∧ (∃ y, γ y = 0) ∧ (∃ z, φ z = 0)

/-- paper IV `definition-master-embedding` (Definition 3.5). -/
def IsMasterEmbedding (S : Set (X × Y × Z)) {s : ℕ} (H : Fin s → Type)
    [∀ i, AddCommGroup (H i)] (σ : X → ∀ i, H i) (γ : Y → ∀ i, H i) (φ : Z → ∀ i, H i) : Prop :=
  IsEmbedding3 S σ γ φ ∧
    ∀ (G : Type) [AddCommGroup G] (σ' : X → G) (γ' : Y → G) (φ' : Z → G),
      IsEmbedding3 S σ' γ' φ' → ZeroInImage3 σ' γ' φ' →
      ∃ i : Fin s, IsLinearReduction (fun x => σ x i) (fun y => γ y i) (fun z => φ z i) σ' γ' φ'

/-- paper IV `def:master`: `σ^{♯ℓ}(x₁,…,x_ℓ) = ∑_{j=1}^{ℓ} (-1)^{j+1} σ(x_j)`, with `j` shifted to `0`-indexing. -/
def sharp {X : Type*} {H : Type*} [AddCommGroup H] (σ : X → H) (ℓ : ℕ) (x : Fin ℓ → X) : H :=
  ∑ j : Fin ℓ, ((-1 : ℤ) ^ j.val) • σ (x j)

/-- paper IV `definition-equivalent-embeddings`. -/
def EquivalentEmbeddings {H H' : Type*} (σ : X → H) (γ : Y → H) (φ : Z → H)
    (σ' : X → H') (γ' : Y → H') (φ' : Z → H') : Prop :=
  (∃ m : Set.range σ ≃ Set.range σ', ∀ x, (m ⟨σ x, x, rfl⟩ : H') = σ' x) ∧
  (∃ m : Set.range γ ≃ Set.range γ', ∀ y, (m ⟨γ y, y, rfl⟩ : H') = γ' y) ∧
  (∃ m : Set.range φ ≃ Set.range φ', ∀ z, (m ⟨φ z, z, rfl⟩ : H') = φ' z)

/-- paper IV `definition-saturated`: the image is a subgroup. -/
def IsSaturated {H : Type*} [AddCommGroup H] {W : Type*} (σ : W → H) : Prop :=
  ∃ K : AddSubgroup H, (K : Set H) = Set.range σ

/-- a triple is saturated when each component is. -/
def IsSaturated3 {H : Type*} [AddCommGroup H] (σ : X → H) (γ : Y → H) (φ : Z → H) : Prop :=
  IsSaturated σ ∧ IsSaturated γ ∧ IsSaturated φ

/-- paper IV `definition-embedding-functions`: `Embed_σ = Span{χ ∘ σ : χ ∈ Ĥ}`. -/
def embedSpan {W : Type*} {H : Type*} [AddCommGroup H] (σ : W → H) : Submodule ℂ (W → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : AddChar H ℂ => fun w => χ (σ w))

/-- paper IV `definition-embedding-functions`, step `span-equals-fibre-constant`. -/
theorem embedSpan_eq_fibreConstant {W : Type*} {H : Type*} [AddCommGroup H] [Finite H]
    (σ : W → H) (f : W → ℂ) :
    f ∈ embedSpan σ ↔ ∃ F : H → ℂ, f = F ∘ σ := by
  have hmap : embedSpan σ = Submodule.map (LinearMap.funLeft ℂ ℂ σ)
      (Submodule.span ℂ (Set.range fun χ : AddChar H ℂ => (χ : H → ℂ))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have htop : Submodule.span ℂ (Set.range fun χ : AddChar H ℂ => (χ : H → ℂ)) = ⊤ := by
    have := (AddChar.complexBasis H).span_eq
    rw [AddChar.coe_complexBasis] at this
    exact this
  rw [hmap, htop, Submodule.map_top, LinearMap.mem_range]
  constructor
  · rintro ⟨F, hF⟩; exact ⟨F, hF.symm⟩
  · rintro ⟨F, hF⟩; exact ⟨F, hF.symm⟩

theorem embedSpan_iff_fibre_constant {W : Type*} {H : Type*} [AddCommGroup H] [Finite H]
    (σ : W → H) (f : W → ℂ) :
    f ∈ embedSpan σ ↔ ∀ w w', σ w = σ w' → f w = f w' := by
  rw [embedSpan_eq_fibreConstant]
  constructor
  · rintro ⟨F, rfl⟩ w w' h
    simp [h]
  · intro h
    classical
    refine ⟨fun a => if ha : ∃ w, σ w = a then f ha.choose else 0, ?_⟩
    funext w
    have ha : ∃ w', σ w' = σ w := ⟨w, rfl⟩
    simp only [Function.comp_apply, ha, dite_true]
    exact (h _ _ ha.choose_spec).symm

/-! ### Linear-algebra input for Lemma 3.3 -/

open scoped Classical in
/-- Clearing denominators for the three-factor system: every pair of coordinates of the same factor
is, up to a non-zero integer, a combination of the equations; the multipliers are bounded. -/
theorem bk_exists_coeff_bound (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (S : Set (X × Y × Z)) (hS : ¬ AdmitsEmbeddingInto3 S ℤ) :
    ∃ C : ℕ, ∀ n n' : X ⊕ Y ⊕ Z, SameKind n n' → ∃ D : ℤ, D ≠ 0 ∧ D.natAbs ≤ C ∧
      ∃ nn : S → ℤ, ∀ j, D * (indVec n j - indVec n' j) = ∑ i, nn i * rowVec i.1 j := by
  let N := X ⊕ Y ⊕ Z
  let rows : S → N → ℤ := fun s => rowVec s.1
  have key : ∀ q : N × N, ∃ D : ℤ, D ≠ 0 ∧ (SameKind q.1 q.2 → ∃ nn : S → ℤ,
      ∀ j, D * (indVec q.1 j - indVec q.2 j) = ∑ i, nn i * rows i j) := by
    intro q
    by_cases hk : SameKind q.1 q.2
    · have hint : ∀ v : N → ℤ, (∀ i, ∑ j, rows i j * v j = 0) →
          ∑ j, (indVec q.1 j - indVec q.2 j) * v j = 0 := by
        intro v hv
        have hv' : IsEmbedding3 S (fun x => v (Sum.inl x)) (fun y => v (Sum.inr (Sum.inl y)))
            (fun z => v (Sum.inr (Sum.inr z))) := by
          rw [isEmbedding3_iff]
          intro s hs
          have := hv ⟨s, hs⟩
          have h2 := sum_rowVec_mul (R := ℤ) s v
          simp only [Int.cast_id] at h2
          simp only [rows] at this
          rw [h2] at this
          exact this
        have hc : (∀ a b, v (Sum.inl a) = v (Sum.inl b)) ∧
            (∀ a b, v (Sum.inr (Sum.inl a)) = v (Sum.inr (Sum.inl b))) ∧
            (∀ a b, v (Sum.inr (Sum.inr a)) = v (Sum.inr (Sum.inr b))) := by
          by_contra hnc
          exact hS ((admitsEmbeddingInto3_iff S ℤ).mpr
            ⟨_, _, _, hv', (isNontrivialEmbedding3_iff _ _ _).mpr hnc⟩)
        have hv_eq : v = Sum.elim (fun a => v (Sum.inl a))
            (Sum.elim (fun a => v (Sum.inr (Sum.inl a))) fun a => v (Sum.inr (Sum.inr a))) := by
          funext n; rcases n with _ | _ | _ <;> rfl
        have := (congrFun hv_eq q.1).trans
          ((sameKind_eq_of_const _ _ _ hc q.1 q.2 hk).trans (congrFun hv_eq q.2).symm)
        simp only [sub_mul, Finset.sum_sub_distrib]
        have e1 := sum_indVec_mul (R := ℤ) q.1 v
        have e2 := sum_indVec_mul (R := ℤ) q.2 v
        simp only [Int.cast_id] at e1 e2
        rw [e1, e2, sub_eq_zero]
        exact this
      obtain ⟨D, hD, nn, hnn⟩ := exists_int_combination rows _ hint
      exact ⟨D, hD, fun _ => ⟨nn, hnn⟩⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hk⟩
  choose D hD nn hnn using key
  refine ⟨Finset.univ.sup fun q => (D q).natAbs, fun n n' hk => ⟨D (n, n'), hD _, ?_,
    nn (n, n') hk, hnn (n, n') hk⟩⟩
  exact Finset.le_sup (f := fun q => (D q).natAbs) (Finset.mem_univ (n, n'))

/-- divisibility: `p^k ∣ D b` with `D ≠ 0` forces `p^(k-e) ∣ b` for the `p`-part `p^e` of `D`. -/
theorem bk_dvd_of_dvd_mul {p : ℕ} (hp : p.Prime) (k : ℕ) (D b : ℤ) (hD : D ≠ 0)
    (h : ((p ^ k : ℕ) : ℤ) ∣ D * b) :
    ∃ e : ℕ, p ^ e ∣ D.natAbs ∧ ((p ^ (k - e) : ℕ) : ℤ) ∣ b := by
  have h1 : p ^ k ∣ D.natAbs * b.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa [Int.natAbs_mul] using this
  obtain ⟨e, D', hD', hDe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hD) p
    hp.one_lt.ne'
  refine ⟨e, ⟨D', hDe⟩, ?_⟩
  rw [Int.natCast_dvd]
  rcases le_or_gt k e with hke | hke
  · simp [Nat.sub_eq_zero_of_le hke]
  · have hk' : p ^ k = p ^ e * p ^ (k - e) := by rw [← pow_add]; congr 1; omega
    rw [hDe, mul_assoc, hk'] at h1
    have h2 : p ^ (k - e) ∣ D' * b.natAbs := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos e) h1
    have hcop : Nat.Coprime (p ^ (k - e)) D' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hD')
    exact hcop.dvd_of_dvd_mul_left h2

/-- the conclusion of Lemma 3.3 for one fixed support, with one constant `C` for `p₀` and `k₀`. -/
def BkGood {X Y Z : Type} (S : Set (X × Y × Z)) (C : ℕ) : Prop :=
  ∀ p k : ℕ, p.Prime →
    ∀ (σ : X → ZMod (p ^ k)) (γ : Y → ZMod (p ^ k)) (φ : Z → ZMod (p ^ k)),
      IsEmbedding3 S σ γ φ → IsNontrivialEmbedding3 σ γ φ → ZeroInImage3 σ γ φ →
      p ≤ C ∧ ∃ k' : ℕ, k' ≤ C ∧
        ∃ (σ' : X → ZMod (p ^ k')) (γ' : Y → ZMod (p ^ k')) (φ' : Z → ZMod (p ^ k')),
          IsEmbedding3 S σ' γ' φ' ∧ IsLinearReduction σ' γ' φ' σ γ φ

theorem BkGood.mono {X Y Z : Type} {S : Set (X × Y × Z)} {C C' : ℕ} (h : BkGood S C)
    (hC : C ≤ C') : BkGood S C' := by
  intro p k hp σ γ φ h1 h2 h3
  obtain ⟨h4, k', hk', r⟩ := h p k hp σ γ φ h1 h2 h3
  exact ⟨h4.trans hC, k', hk'.trans hC, r⟩

/-- Per-instance form of Lemma 3.3. -/
theorem bk_good (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (S : Set (X × Y × Z)) (hS : ¬ AdmitsEmbeddingInto3 S ℤ) : ∃ C : ℕ, BkGood S C := by
  classical
  obtain ⟨C, hC⟩ := bk_exists_coeff_bound X Y Z S hS
  refine ⟨C, fun p k hp σ γ φ hemb hnt hz => ?_⟩
  let v : X ⊕ Y ⊕ Z → ZMod (p ^ k) := Sum.elim σ (Sum.elim γ φ)
  have hemb' := (isEmbedding3_iff S σ γ φ).mp hemb
  have hv : ∀ i : S, ∑ j, ((rowVec i.1 j : ℤ) : ZMod (p ^ k)) * v j = 0 := by
    intro i
    rw [sum_rowVec_mul]
    exact hemb' i.1 i.2
  obtain ⟨⟨x0, hx0⟩, ⟨y0, hy0⟩, ⟨z0, hz0⟩⟩ := hz
  let zp : X ⊕ Y ⊕ Z → X ⊕ Y ⊕ Z :=
    Sum.elim (fun _ => Sum.inl x0) (Sum.elim (fun _ => Sum.inr (Sum.inl y0))
      fun _ => Sum.inr (Sum.inr z0))
  have hzp : ∀ n, SameKind n (zp n) := by
    intro n; rcases n with _ | _ | _ <;> exact trivial
  have hvzp : ∀ n, v (zp n) = 0 := by
    intro n; rcases n with _ | _ | _
    · exact hx0
    · exact hy0
    · exact hz0
  have hkey : ∀ n, ∃ e : ℕ, ∃ D : ℤ, D ≠ 0 ∧ D.natAbs ≤ C ∧ p ^ e ∣ D.natAbs ∧
      ∃ b : ℤ, v n = (b : ZMod (p ^ k)) ∧ ((p ^ (k - e) : ℕ) : ℤ) ∣ b := by
    intro n
    obtain ⟨D, hD0, hDC, nn, hnn⟩ := hC n (zp n) (hzp n)
    have h1 := int_combination_apply (R := ZMod (p ^ k)) (fun i : S => rowVec i.1)
      (fun j => indVec n j - indVec (zp n) j) D nn hnn v hv
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sum_indVec_mul, hvzp,
      sub_zero] at h1
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (v n)
    have h2 : (((D * b : ℤ)) : ZMod (p ^ k)) = 0 := by
      rw [Int.cast_mul, hb]; exact h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    obtain ⟨e, he1, he2⟩ := bk_dvd_of_dvd_mul hp k D b hD0 h2
    exact ⟨e, D, hD0, hDC, he1, b, hb.symm, he2⟩
  -- Step 1: `p ≤ C`
  have hpC : p ≤ C := by
    by_contra hlt
    push Not at hlt
    have hall : ∀ n, v n = 0 := by
      intro n
      obtain ⟨e, D, hD0, hDC, he1, b, hb, he2⟩ := hkey n
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        rw [hb]
        simp only [Nat.sub_zero] at he2
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd b _).mpr he2
      · exfalso
        have h3 : p ∣ D.natAbs := (dvd_pow_self p he.ne').trans he1
        have := Nat.le_of_dvd (Int.natAbs_pos.mpr hD0) h3
        omega
    exact absurd ((isNontrivialEmbedding3_iff σ γ φ).mp hnt)
      (not_not.mpr ⟨fun a b => (hall (Sum.inl a)).trans (hall (Sum.inl b)).symm,
        fun a b => (hall (Sum.inr (Sum.inl a))).trans (hall (Sum.inr (Sum.inl b))).symm,
        fun a b => (hall (Sum.inr (Sum.inr a))).trans (hall (Sum.inr (Sum.inr b))).symm⟩)
  refine ⟨hpC, ?_⟩
  -- Step 2: `k'`
  by_cases hkC : k ≤ C
  · refine ⟨k, hkC, σ, γ, φ, hemb, ?_⟩
    exact ⟨AddMonoidHom.id _, AddMonoidHom.id _, AddMonoidHom.id _, fun _ _ h => h,
      fun _ _ h => h, fun _ _ h => h, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  push Not at hkC
  have hdiv : ∀ n, ∃ a : ℤ, v n = (a : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - C)) := by
    intro n
    obtain ⟨e, D, hD0, hDC, he1, b, hb, he2⟩ := hkey n
    have he3 : p ^ e ≤ C := (Nat.le_of_dvd (Int.natAbs_pos.mpr hD0) he1).trans hDC
    have he4 : e < C := (Nat.lt_pow_self hp.one_lt).trans_le he3
    have h5 : ((p ^ (k - C) : ℕ) : ℤ) ∣ b :=
      (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))).trans he2
    obtain ⟨a, ha⟩ := h5
    refine ⟨a, ?_⟩
    rw [hb, ha]; push_cast; ring
  choose aσ haσ using fun x => hdiv (Sum.inl x)
  choose aγ haγ using fun y => hdiv (Sum.inr (Sum.inl y))
  choose aφ haφ using fun z => hdiv (Sum.inr (Sum.inr z))
  let f : ℤ →+ ZMod (p ^ k) :=
    (AddMonoidHom.mulRight ((p : ZMod (p ^ k)) ^ (k - C))).comp (Int.castAddHom _)
  have hf : f ((p ^ C : ℕ) : ℤ) = 0 := by
    show (((p ^ C : ℕ) : ℤ) : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - C)) = 0
    have : (p : ZMod (p ^ k)) ^ C * (p : ZMod (p ^ k)) ^ (k - C) = ((p ^ k : ℕ) : ZMod (p ^ k)) := by
      rw [← pow_add]; push_cast; congr 1; omega
    push_cast
    rw [this, ZMod.natCast_self]
  let m : ZMod (p ^ C) →+ ZMod (p ^ k) := ZMod.lift (p ^ C) ⟨f, hf⟩
  have hm : ∀ a : ℤ, m (a : ZMod (p ^ C)) = (a : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - C)) :=
    fun a => ZMod.lift_coe _ _ _
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective t
    rw [hm] at ht
    have h1 : (((b * (p ^ (k - C) : ℕ) : ℤ)) : ZMod (p ^ k)) = 0 := by
      push_cast; exact ht
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hk' : ((p ^ k : ℕ) : ℤ) = ((p ^ C : ℕ) : ℤ) * ((p ^ (k - C) : ℕ) : ℤ) := by
      push_cast; rw [← pow_add]; congr 1; omega
    rw [hk'] at h1
    have hne : ((p ^ (k - C) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero (k - C) hp.ne_zero
    exact (mul_dvd_mul_iff_right hne).mp h1
  refine ⟨C, le_rfl, fun x => (aσ x : ZMod (p ^ C)), fun y => (aγ y : ZMod (p ^ C)),
    fun z => (aφ z : ZMod (p ^ C)), ?_, m, m, m, hinj, hinj, hinj, ?_, ?_, ?_⟩
  · rw [isEmbedding3_iff]
    intro s hs
    apply hinj
    rw [map_add, map_add, hm, hm, hm, map_zero]
    have := hemb' s hs
    have e1 : σ s.1 = (aσ s.1 : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - C)) := haσ s.1
    have e2 : γ s.2.1 = (aγ s.2.1 : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - C)) := haγ s.2.1
    have e3 : φ s.2.2 = (aφ s.2.2 : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - C)) := haφ s.2.2
    rw [e1, e2, e3] at this
    exact this
  · intro x; rw [hm]; exact haσ x
  · intro y; rw [hm]; exact haγ y
  · intro z; rw [hm]; exact haφ z

theorem BkGood.of_image {X Y Z X' Y' Z' : Type} (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    {S : Set (X × Y × Z)} {C : ℕ}
    (h : BkGood ((fun p : X × Y × Z => (eX p.1, eY p.2.1, eZ p.2.2)) '' S) C) :
    BkGood S C := by
  intro p k hp σ γ φ h1 h2 h3
  have h1' : IsEmbedding3 ((fun p : X × Y × Z => (eX p.1, eY p.2.1, eZ p.2.2)) '' S)
      (fun x => σ (eX.symm x)) (fun y => γ (eY.symm y)) (fun z => φ (eZ.symm z)) := by
    rw [isEmbedding3_iff]
    rintro _ ⟨q, hq, rfl⟩
    simpa using (isEmbedding3_iff S σ γ φ).mp h1 q hq
  have h2' : IsNontrivialEmbedding3 (fun x => σ (eX.symm x)) (fun y => γ (eY.symm y))
      (fun z => φ (eZ.symm z)) := by
    rw [isNontrivialEmbedding3_iff] at h2 ⊢
    rintro ⟨a1, a2, a3⟩
    apply h2
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
    · simpa using a1 (eX a) (eX b)
    · simpa using a2 (eY a) (eY b)
    · simpa using a3 (eZ a) (eZ b)
  have h3' : ZeroInImage3 (fun x => σ (eX.symm x)) (fun y => γ (eY.symm y))
      (fun z => φ (eZ.symm z)) := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := h3
    exact ⟨⟨eX x, by simpa using hx⟩, ⟨eY y, by simpa using hy⟩, ⟨eZ z, by simpa using hz⟩⟩
  obtain ⟨hpC, k', hk', σ', γ', φ', he, m1, m2, m3, i1, i2, i3, r1, r2, r3⟩ :=
    h p k hp _ _ _ h1' h2' h3'
  refine ⟨hpC, k', hk', fun x => σ' (eX x), fun y => γ' (eY y), fun z => φ' (eZ z), ?_,
    m1, m2, m3, i1, i2, i3, ?_, ?_, ?_⟩
  · rw [isEmbedding3_iff]
    intro q hq
    simpa using (isEmbedding3_iff _ _ _ _).mp he _ ⟨q, hq, rfl⟩
  · intro x; simpa using r1 (eX x)
  · intro y; simpa using r2 (eY y)
  · intro z; simpa using r3 (eZ z)

/-- paper IV `lem:bound-k-in-embed` (Lemma 3.3), with the normalisation of l. 1731-1733
(`ZeroInImage3`), `p₀, k₀` before the alphabets as in `bound_p_in_embed`. -/
theorem bound_k_in_embed (m : ℕ) :
    ∃ p₀ k₀ : ℕ, ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z],
      Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
      ∀ μ : FinProb (X × Y × Z), ¬ AdmitsEmbeddingInto3 μ.support ℤ →
      ∀ p k : ℕ, p.Prime →
      ∀ (σ : X → ZMod (p ^ k)) (γ : Y → ZMod (p ^ k)) (φ : Z → ZMod (p ^ k)),
        IsEmbedding3 μ.support σ γ φ → IsNontrivialEmbedding3 σ γ φ → ZeroInImage3 σ γ φ →
        p ≤ p₀ ∧ ∃ k' : ℕ, k' ≤ k₀ ∧
          ∃ (σ' : X → ZMod (p ^ k')) (γ' : Y → ZMod (p ^ k')) (φ' : Z → ZMod (p ^ k')),
            IsEmbedding3 μ.support σ' γ' φ' ∧ IsLinearReduction σ' γ' φ' σ γ φ := by
  classical
  let ι := Σ abc : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
    Set (Fin abc.1.val × Fin abc.2.1.val × Fin abc.2.2.val)
  have hr : ∀ q : ι, ∃ C : ℕ, ¬ AdmitsEmbeddingInto3 q.2 ℤ → BkGood q.2 C := by
    intro q
    by_cases hq : AdmitsEmbeddingInto3 q.2 ℤ
    · exact ⟨0, fun h => absurd hq h⟩
    · obtain ⟨C, hC⟩ := bk_good _ _ _ q.2 hq
      exact ⟨C, fun _ => hC⟩
  choose C hC using hr
  have : Finite ι := inferInstance
  have := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup C, Finset.univ.sup C, ?_⟩
  intro X Y Z _ _ _ hX hY hZ μ hμ p k hp σ γ φ h1 h2 h3
  let eX := Fintype.equivFin X
  let eY := Fintype.equivFin Y
  let eZ := Fintype.equivFin Z
  let q : ι := ⟨(⟨Fintype.card X, Nat.lt_succ_of_le hX⟩, ⟨Fintype.card Y, Nat.lt_succ_of_le hY⟩,
      ⟨Fintype.card Z, Nat.lt_succ_of_le hZ⟩),
    (fun t : X × Y × Z => (eX t.1, eY t.2.1, eZ t.2.2)) '' μ.support⟩
  have hqr : C q ≤ Finset.univ.sup C := Finset.le_sup (Finset.mem_univ q)
  have h0 : ¬ AdmitsEmbeddingInto3 q.2 ℤ := fun h =>
    hμ ((admitsEmbeddingInto3_map_iff eX eY eZ μ.support ℤ).mp h)
  have hg : BkGood μ.support (Finset.univ.sup C) :=
    BkGood.of_image eX eY eZ ((hC q h0).mono hqr)
  exact hg p k hp σ γ φ h1 h2 h3

theorem bound_k_in_embed_literal (m : ℕ) (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (hX : Fintype.card X ≤ m) (hY : Fintype.card Y ≤ m) (hZ : Fintype.card Z ≤ m) :
    ∃ p₀ k₀ : ℕ, ∀ μ : FinProb (X × Y × Z), ¬ AdmitsEmbeddingInto3 μ.support ℤ →
      ∀ p k : ℕ, p.Prime →
      ∀ (σ : X → ZMod (p ^ k)) (γ : Y → ZMod (p ^ k)) (φ : Z → ZMod (p ^ k)),
        IsEmbedding3 μ.support σ γ φ → IsNontrivialEmbedding3 σ γ φ → ZeroInImage3 σ γ φ →
        p ≤ p₀ ∧ ∃ k' : ℕ, k' ≤ k₀ ∧
          ∃ (σ' : X → ZMod (p ^ k')) (γ' : Y → ZMod (p ^ k')) (φ' : Z → ZMod (p ^ k')),
            IsEmbedding3 μ.support σ' γ' φ' ∧ IsLinearReduction σ' γ' φ' σ γ φ := by
  obtain ⟨p₀, k₀, h⟩ := bound_k_in_embed m
  exact ⟨p₀, k₀, fun μ => h X Y Z hX hY hZ μ⟩

end Master
end TrackB
end RestrictedPolynomials
end
