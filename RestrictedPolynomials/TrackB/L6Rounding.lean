module

public import RestrictedPolynomials.TrackB.MaxTClass
public import RestrictedPolynomials.TrackB.TurnInfiniteFinite
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Track B: logarithms, common-`q` Dirichlet rounding, exact relations

Steps (paper IV, section 6.5.3, l. 3867-3943): `lem:nu-satisfies` steps `log-approximate-embedding`,
`dirichlet-rounding`, `imaginary-rounding-mod-q`, `rounded-triple-in-embed` (at `H = {0}`), and `claim:relaxed-base-case-embed-2` (Claim 6.16), and the typing helper
`l6_inT_embedding_const`.

Readings: hypotheses on all of `X`, `Z`; `∃ c ∀ τ ≤ c`; one common `q`
on `X ⊕ Y ⊕ Z ⊕ X ⊕ Y ⊕ Z`, bound `1/(q N^{1/(6m)})`, imaginary parts divided by `2π`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section L6Rounding

/-- helper (TYPING): at `H = {0}` an embedding of a set in `𝒯` into any Abelian group is trivial. -/
theorem l6_inT_embedding_const {X Y Z : Type} {S : Set (X × Y × Z)} (hS : InT S)
    (G : Type) [AddCommGroup G] (σ : X → G) (γ : Y → G) (φ : Z → G)
    (h : ∀ p ∈ S, σ p.1 + γ p.2.1 + φ p.2.2 = 0) :
    (∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b) := by
  by_contra hne
  apply hS.2
  exact ⟨G, inferInstance, (admitsEmbeddingInto3_iff S G).mpr
    ⟨σ, γ, φ, (isEmbedding3_iff S σ γ φ).mpr h,
      (isNontrivialEmbedding3_iff _ _ _).mpr hne⟩⟩

/-- paper IV `lem:nu-satisfies`, step `log-approximate-embedding`. -/
theorem l6_log_approx_embedding (m : ℕ) (hm : 1 ≤ m) {c' : ℝ} (hc' : 0 < c') :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 < τ → τ ≤ c →
      ∀ {X Y Z : Type} (S : Set (X × Y × Z)) (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ) (j : ℕ),
      j ≤ 2 * m →
      (∀ p ∈ S, ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ≤ τ ^ (20 * m)) →
      (∀ y, c' * Real.sqrt τ ≤ ‖g y‖) →
      (∀ x, τ ^ ((3 * j : ℝ) + 3 / 2) ≤ ‖f x‖) → (∀ z, τ ^ ((3 * j : ℝ) + 3 / 2) ≤ ‖h z‖) →
      (∀ x, f x ≠ 0) ∧ (∀ y, g y ≠ 0) ∧ (∀ z, h z ≠ 0) ∧
      (∀ p ∈ S, ‖starRingEnd ℂ (f p.1) / (g p.2.1 * h p.2.2) - 1‖ ≤ τ ^ (10 * m)) ∧
      (∀ p ∈ S, ∃ k : ℤ,
        ‖Complex.log (starRingEnd ℂ (f p.1)) - (Complex.log (g p.2.1) + Complex.log (h p.2.2))
          - 2 * Real.pi * Complex.I * k‖ ≤ 2 * τ ^ (10 * m)) := by
  refine ⟨min (1 / 2) c', lt_min (by norm_num) hc', ?_⟩
  intro τ hτ hτc X Y Z S f g h j hj hrel hg hf hh
  have hτ12 : τ ≤ 1 / 2 := le_trans hτc (min_le_left _ _)
  have hτc' : τ ≤ c' := le_trans hτc (min_le_right _ _)
  have hτ1 : τ ≤ 1 := by linarith
  have hApos : 0 < τ ^ ((3 * j : ℝ) + 3 / 2) := Real.rpow_pos_of_pos hτ _
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hf0 : ∀ x, f x ≠ 0 := fun x hx => by
    have := hf x; rw [hx, norm_zero] at this; linarith
  have hh0 : ∀ z, h z ≠ 0 := fun z hz => by
    have := hh z; rw [hz, norm_zero] at this; linarith
  have hg0 : ∀ y, g y ≠ 0 := fun y hy => by
    have := hg y; rw [hy, norm_zero] at this
    have : 0 < c' * Real.sqrt τ := by positivity
    linarith
  -- the key bound
  have key : ∀ p ∈ S, ‖starRingEnd ℂ (f p.1) / (g p.2.1 * h p.2.2) - 1‖ ≤ τ ^ (10 * m) := by
    intro p hp
    have hgh : g p.2.1 * h p.2.2 ≠ 0 := mul_ne_zero (hg0 _) (hh0 _)
    have e1 : starRingEnd ℂ (f p.1) / (g p.2.1 * h p.2.2) - 1 =
        (starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2) / (g p.2.1 * h p.2.2) := by
      rw [sub_div, div_self hgh]
    rw [e1, norm_div, div_le_iff₀ (norm_pos_iff.mpr hgh), norm_mul]
    have hlow : c' * Real.sqrt τ * τ ^ ((3 * j : ℝ) + 3 / 2) ≤ ‖g p.2.1‖ * ‖h p.2.2‖ :=
      mul_le_mul (hg _) (hh _) hApos.le (norm_nonneg _)
    have hprod : Real.sqrt τ * τ ^ ((3 * j : ℝ) + 3 / 2) = τ ^ (3 * j + 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hτ]
      have : (1 / 2 : ℝ) + ((3 * j : ℝ) + 3 / 2) = ((3 * j + 2 : ℕ) : ℝ) := by
        push_cast; ring
      rw [this, Real.rpow_natCast]
    obtain ⟨e, he⟩ : ∃ e : ℕ, 10 * m = (3 * j + 2) + (e + 1) := ⟨10 * m - 3 * j - 3, by omega⟩
    have h1 : τ ^ (10 * m) ≤ c' * τ ^ (3 * j + 2) := by
      rw [he, pow_add]
      have : τ ^ (e + 1) ≤ c' := le_trans (pow_le_of_le_one hτ.le hτ1 (by omega)) hτc'
      calc τ ^ (3 * j + 2) * τ ^ (e + 1) ≤ τ ^ (3 * j + 2) * c' :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : τ ^ (20 * m) = τ ^ (10 * m) * τ ^ (10 * m) := by rw [← pow_add]; ring_nf
    calc ‖starRingEnd ℂ (f p.1) - g p.2.1 * h p.2.2‖ ≤ τ ^ (20 * m) := hrel p hp
      _ = τ ^ (10 * m) * τ ^ (10 * m) := h2
      _ ≤ τ ^ (10 * m) * (c' * Real.sqrt τ * τ ^ ((3 * j : ℝ) + 3 / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc τ ^ (10 * m) ≤ c' * τ ^ (3 * j + 2) := h1
            _ = _ := by rw [← hprod]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  refine ⟨hf0, hg0, hh0, key, ?_⟩
  · intro p hp
    set w : ℂ := starRingEnd ℂ (f p.1) / (g p.2.1 * h p.2.2) - 1 with hw
    have hwle : ‖w‖ ≤ τ ^ (10 * m) := key p hp
    have hpow : τ ^ (10 * m) ≤ τ := pow_le_of_le_one hτ.le hτ1 (by omega)
    have hw12 : ‖w‖ ≤ 1 / 2 := by linarith
    have hf1 : starRingEnd ℂ (f p.1) ≠ 0 := by simpa using hf0 p.1
    have hgh : g p.2.1 * h p.2.2 ≠ 0 := mul_ne_zero (hg0 _) (hh0 _)
    have h1w : (1 : ℂ) + w = starRingEnd ℂ (f p.1) / (g p.2.1 * h p.2.2) := by rw [hw]; ring
    have hne : (1 : ℂ) + w ≠ 0 := by rw [h1w]; exact div_ne_zero hf1 hgh
    have hexp : Complex.exp (Complex.log (starRingEnd ℂ (f p.1)) -
        (Complex.log (g p.2.1) + Complex.log (h p.2.2))) = Complex.exp (Complex.log (1 + w)) := by
      rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hf1, Complex.exp_log (hg0 _),
        Complex.exp_log (hh0 _), Complex.exp_log hne, h1w, div_eq_div_iff hgh hgh]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨n, ?_⟩
    have : Complex.log (starRingEnd ℂ (f p.1)) - (Complex.log (g p.2.1) + Complex.log (h p.2.2))
        - 2 * Real.pi * Complex.I * n = Complex.log (1 + w) := by
      rw [sub_eq_iff_eq_add, hn]; ring
    rw [this]
    calc ‖Complex.log (1 + w)‖ ≤ 3 / 2 * ‖w‖ := Complex.norm_log_one_add_half_le_self hw12
      _ ≤ 2 * τ ^ (10 * m) := by linarith [pow_nonneg hτ.le (10 * m)]

/-- paper IV `lem:nu-satisfies`, step `dirichlet-rounding` (one common `q`). -/
theorem l6_dirichlet_common_q (m : ℕ) (hm : 1 ≤ m) {X Y Z : Type} [Fintype X] [Fintype Y]
    [Fintype Z] (hX : Fintype.card X ≤ m) (hY : Fintype.card Y ≤ m) (hZ : Fintype.card Z ≤ m)
    (u : X → ℂ) (v : Y → ℂ) (w : Z → ℂ) {N : ℕ} (hN : 0 < N) :
    ∃ (q : ℕ) (σR : X → ℤ) (γR : Y → ℤ) (φR : Z → ℤ) (σI : X → ℤ) (γI : Y → ℤ) (φI : Z → ℤ),
      1 ≤ q ∧ q ≤ N ∧
      (∀ x, |(u x).re - (σR x : ℝ) / q| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) ∧
      (∀ y, |(v y).re - (γR y : ℝ) / q| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) ∧
      (∀ z, |(w z).re - (φR z : ℝ) / q| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) ∧
      (∀ x, |(u x).im / (2 * Real.pi) - (σI x : ℝ) / q| ≤
        1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) ∧
      (∀ y, |(v y).im / (2 * Real.pi) - (γI y : ℝ) / q| ≤
        1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) ∧
      (∀ z, |(w z).im / (2 * Real.pi) - (φI z : ℝ) / q| ≤
        1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ))))) := by
  classical
  let s : ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) → ℝ :=
    Sum.elim (Sum.elim (fun x => (u x).re) (Sum.elim (fun y => (v y).re) (fun z => (w z).re)))
      (Sum.elim (fun x => (u x).im / (2 * Real.pi))
        (Sum.elim (fun y => (v y).im / (2 * Real.pi)) (fun z => (w z).im / (2 * Real.pi))))
  obtain ⟨q, p, hq1, hqN, hp⟩ := simDirichlet_exists s hN
  have hcard : Fintype.card ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) ≤ 6 * m := by
    simp only [Fintype.card_sum]; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmono : ∀ i : (X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z),
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / (Fintype.card ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) : ℝ))) ≤
        1 / ((q : ℝ) * (N : ℝ) ^ (1 / (6 * (m : ℝ)))) := by
    intro i
    have hc : (1 : ℝ) ≤ Fintype.card ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) :=
      by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    have hc6 : (Fintype.card ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) : ℝ) ≤ 6 * (m : ℝ) := by
      exact_mod_cast hcard
    have hexp : 1 / (6 * (m : ℝ)) ≤ 1 / (Fintype.card ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) : ℝ) :=
      one_div_le_one_div_of_le (by linarith) hc6
    have hpow : (N : ℝ) ^ (1 / (6 * (m : ℝ))) ≤
        (N : ℝ) ^ (1 / (Fintype.card ((X ⊕ Y ⊕ Z) ⊕ (X ⊕ Y ⊕ Z)) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hexp
    have hpos : 0 < (N : ℝ) ^ (1 / (6 * (m : ℝ))) := Real.rpow_pos_of_pos (by linarith) _
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hpow hq0.le)
  refine ⟨q, fun x => p (Sum.inl (Sum.inl x)), fun y => p (Sum.inl (Sum.inr (Sum.inl y))),
    fun z => p (Sum.inl (Sum.inr (Sum.inr z))), fun x => p (Sum.inr (Sum.inl x)),
    fun y => p (Sum.inr (Sum.inr (Sum.inl y))), fun z => p (Sum.inr (Sum.inr (Sum.inr z))),
    hq1, hqN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact (hp (Sum.inl (Sum.inl x))).trans (hmono (Sum.inl (Sum.inl x)))
  · intro y; exact (hp (Sum.inl (Sum.inr (Sum.inl y)))).trans (hmono (Sum.inl (Sum.inr (Sum.inl y))))
  · intro z; exact (hp (Sum.inl (Sum.inr (Sum.inr z)))).trans (hmono (Sum.inl (Sum.inr (Sum.inr z))))
  · intro x; exact (hp (Sum.inr (Sum.inl x))).trans (hmono (Sum.inr (Sum.inl x)))
  · intro y; exact (hp (Sum.inr (Sum.inr (Sum.inl y)))).trans (hmono (Sum.inr (Sum.inr (Sum.inl y))))
  · intro z; exact (hp (Sum.inr (Sum.inr (Sum.inr z)))).trans (hmono (Sum.inr (Sum.inr (Sum.inr z))))

/-- The exact real-part relation (shared by Claim 6.16 and the imaginary rounding). -/
private theorem l6_real_relation {X Y Z : Type} (S : Set (X × Y × Z)) (F : X → ℂ) (G : Y → ℂ)
    (H : Z → ℂ) (δ ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (σR : X → ℤ) (γR : Y → ℤ) (φR : Z → ℤ)
    (hrel : ∀ p ∈ S, ∃ k : ℤ,
      ‖F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k‖ ≤ δ)
    (hσR : ∀ x, |(F x).re - (σR x : ℝ) / q| ≤ ε) (hγR : ∀ y, |(G y).re - (γR y : ℝ) / q| ≤ ε)
    (hφR : ∀ z, |(H z).re - (φR z : ℝ) / q| ≤ ε)
    (hsmall : (q : ℝ) * (3 * ε + δ) < 1) :
    ∀ p ∈ S, σR p.1 = γR p.2.1 + φR p.2.2 := by
  intro p hp
  obtain ⟨k, hk⟩ := hrel p hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : |(F p.1).re - ((G p.2.1).re + (H p.2.2).re)| ≤ δ := by
    have := Complex.abs_re_le_norm (F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k)
    have e : (F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k).re =
        (F p.1).re - ((G p.2.1).re + (H p.2.2).re) := by simp
    rw [e] at this
    exact this.trans hk
  have h1 := hσR p.1
  have h2 := hγR p.2.1
  have h3 := hφR p.2.2
  have hb : |((σR p.1 - γR p.2.1 - φR p.2.2 : ℤ) : ℝ) / q| ≤ 3 * ε + δ := by
    have e : ((σR p.1 - γR p.2.1 - φR p.2.2 : ℤ) : ℝ) / q =
        -((F p.1).re - (σR p.1 : ℝ) / q) + ((G p.2.1).re - (γR p.2.1 : ℝ) / q) * (-1) * (-1)
        + ((H p.2.2).re - (φR p.2.2 : ℝ) / q) * (-1) * (-1)
        + ((F p.1).re - ((G p.2.1).re + (H p.2.2).re)) - 0 := by
      push_cast; ring
    -- direct linear-arithmetic route
    rw [abs_le] at h1 h2 h3 hre ⊢
    have e2 : ((σR p.1 - γR p.2.1 - φR p.2.2 : ℤ) : ℝ) / q =
        (σR p.1 : ℝ) / q - (γR p.2.1 : ℝ) / q - (φR p.2.2 : ℝ) / q := by
      push_cast; ring
    rw [e2]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hre.1, hre.2]
  have hlt : |((σR p.1 - γR p.2.1 - φR p.2.2 : ℤ) : ℝ)| < 1 := by
    have : |((σR p.1 - γR p.2.1 - φR p.2.2 : ℤ) : ℝ)| =
        q * |((σR p.1 - γR p.2.1 - φR p.2.2 : ℤ) : ℝ) / q| := by
      rw [abs_div, abs_of_pos hq0]; field_simp
    rw [this]
    calc (q : ℝ) * _ ≤ q * (3 * ε + δ) := mul_le_mul_of_nonneg_left hb hq0.le
      _ < 1 := hsmall
  have : σR p.1 - γR p.2.1 - φR p.2.2 = 0 := by
    have h' : |σR p.1 - γR p.2.1 - φR p.2.2| < 1 := by exact_mod_cast hlt
    have := abs_lt.mp h'; omega
  omega

/-- paper IV `claim:relaxed-base-case-embed-2` (Claim 6.16, as printed; real-part route). -/
theorem l6_embed2_relation {X Y Z : Type} (S : Set (X × Y × Z)) (F : X → ℂ) (G : Y → ℂ)
    (H : Z → ℂ) (δ ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (σR : X → ℤ) (γR : Y → ℤ) (φR : Z → ℤ) (σI : X → ℤ) (γI : Y → ℤ) (φI : Z → ℤ)
    (hrel : ∀ p ∈ S, ∃ k : ℤ,
      ‖F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k‖ ≤ δ)
    (hσR : ∀ x, |(F x).re - (σR x : ℝ) / q| ≤ ε) (hγR : ∀ y, |(G y).re - (γR y : ℝ) / q| ≤ ε)
    (hφR : ∀ z, |(H z).re - (φR z : ℝ) / q| ≤ ε)
    (hσI : ∀ x, |(F x).im / (2 * Real.pi) - (σI x : ℝ) / q| ≤ ε)
    (hγI : ∀ y, |(G y).im / (2 * Real.pi) - (γI y : ℝ) / q| ≤ ε)
    (hφI : ∀ z, |(H z).im / (2 * Real.pi) - (φI z : ℝ) / q| ≤ ε)
    (hsmall : (q : ℝ) * (3 * ε + δ) < 1) :
    ∀ p ∈ S, ∃ k : ℤ,
      ((σR p.1 : ℂ) + 2 * Real.pi * Complex.I * (σI p.1 : ℂ))
        - ((γR p.2.1 : ℂ) + 2 * Real.pi * Complex.I * (γI p.2.1 : ℂ))
        - ((φR p.2.2 : ℂ) + 2 * Real.pi * Complex.I * (φI p.2.2 : ℂ)) = 2 * Real.pi * Complex.I * k := by
  intro p hp
  have hR := l6_real_relation S F G H δ ε q hq σR γR φR hrel hσR hγR hφR hsmall p hp
  refine ⟨σI p.1 - γI p.2.1 - φI p.2.2, ?_⟩
  have hR' : (σR p.1 : ℂ) = (γR p.2.1 : ℂ) + (φR p.2.2 : ℂ) := by exact_mod_cast hR
  rw [hR']
  push_cast
  ring

/-- paper IV `lem:nu-satisfies`, step `imaginary-rounding-mod-q` (the repair of the §6.5.3 rounding). -/
theorem l6_imaginary_rounding_mod_q {X Y Z : Type} (S : Set (X × Y × Z)) (F : X → ℂ)
    (G : Y → ℂ) (H : Z → ℂ) (δ ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (σR : X → ℤ) (γR : Y → ℤ) (φR : Z → ℤ) (σI : X → ℤ) (γI : Y → ℤ) (φI : Z → ℤ)
    (hrel : ∀ p ∈ S, ∃ k : ℤ,
      ‖F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k‖ ≤ δ)
    (hσR : ∀ x, |(F x).re - (σR x : ℝ) / q| ≤ ε) (hγR : ∀ y, |(G y).re - (γR y : ℝ) / q| ≤ ε)
    (hφR : ∀ z, |(H z).re - (φR z : ℝ) / q| ≤ ε)
    (hσI : ∀ x, |(F x).im / (2 * Real.pi) - (σI x : ℝ) / q| ≤ ε)
    (hγI : ∀ y, |(G y).im / (2 * Real.pi) - (γI y : ℝ) / q| ≤ ε)
    (hφI : ∀ z, |(H z).im / (2 * Real.pi) - (φI z : ℝ) / q| ≤ ε)
    (hsmall : (q : ℝ) * (3 * ε + δ) < 1) :
    (∀ p ∈ S, σR p.1 = γR p.2.1 + φR p.2.2 ∧
      ((σI p.1 : ℤ) : ZMod q) = (γI p.2.1 : ZMod q) + (φI p.2.2 : ZMod q)) ∧
    (∀ x, ‖((σR x : ℂ) + 2 * Real.pi * Complex.I * (σI x : ℂ)) / q - F x‖ ≤ 7 * ε) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · intro p hp
    refine ⟨l6_real_relation S F G H δ ε q hq σR γR φR hrel hσR hγR hφR hsmall p hp, ?_⟩
    obtain ⟨k, hk⟩ := hrel p hp
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hk
    have him : |(F p.1).im - ((G p.2.1).im + (H p.2.2).im) - 2 * Real.pi * k| ≤ δ := by
      have := Complex.abs_im_le_norm
        (F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k)
      have e : (F p.1 - (G p.2.1 + H p.2.2) - 2 * Real.pi * Complex.I * k).im =
          (F p.1).im - ((G p.2.1).im + (H p.2.2).im) - 2 * Real.pi * k := by
        simp <;> ring
      rw [e] at this
      exact this.trans hk
    have him2 : |((F p.1).im - ((G p.2.1).im + (H p.2.2).im) - 2 * Real.pi * k) / (2 * Real.pi)|
        ≤ δ := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), div_le_iff₀ (by positivity)]
      have : δ ≤ δ * (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
      linarith
    have h1 := hσI p.1
    have h2 := hγI p.2.1
    have h3 := hφI p.2.2
    set b : ℤ := σI p.1 - γI p.2.1 - φI p.2.2 with hb
    have hbq : |(b : ℝ) / q - k| ≤ 3 * ε + δ := by
      have e2 : (b : ℝ) / q = (σI p.1 : ℝ) / q - (γI p.2.1 : ℝ) / q - (φI p.2.2 : ℝ) / q := by
        rw [hb]; push_cast; ring
      have e3 : ((F p.1).im - ((G p.2.1).im + (H p.2.2).im) - 2 * Real.pi * k) / (2 * Real.pi) =
          (F p.1).im / (2 * Real.pi) - (G p.2.1).im / (2 * Real.pi) - (H p.2.2).im / (2 * Real.pi)
            - k := by
        field_simp
        ring
      rw [e3] at him2
      rw [abs_le] at h1 h2 h3 him2 ⊢
      rw [e2]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, him2.1, him2.2]
    have hlt : |((b - q * k : ℤ) : ℝ)| < 1 := by
      have : |((b - q * k : ℤ) : ℝ)| = q * |(b : ℝ) / q - k| := by
        have : ((b - q * k : ℤ) : ℝ) = q * ((b : ℝ) / q - k) := by
          push_cast; field_simp
        rw [this, abs_mul, abs_of_pos hq0]
      rw [this]
      calc (q : ℝ) * _ ≤ q * (3 * ε + δ) := mul_le_mul_of_nonneg_left hbq hq0.le
        _ < 1 := hsmall
    have h0 : b - q * k = 0 := by
      have h' : |b - q * k| < 1 := by exact_mod_cast hlt
      have := abs_lt.mp h'; omega
    have hbk : b = q * k := by omega
    have : ((b : ℤ) : ZMod q) = 0 := by
      rw [hbk]; push_cast; simp
    rw [hb] at this
    push_cast at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · intro x
    have hx1 := hσR x
    have hx2 := hσI x
    have hε : 0 ≤ ε := le_trans (abs_nonneg _) hx1
    have hre : (((σR x : ℂ) + 2 * Real.pi * Complex.I * (σI x : ℂ)) / q - F x).re =
        (σR x : ℝ) / q - (F x).re := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_natCast]
      field_simp
    have him : (((σR x : ℂ) + 2 * Real.pi * Complex.I * (σI x : ℂ)) / q - F x).im =
        2 * Real.pi * ((σI x : ℝ) / q) - (F x).im := by
      simp [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_natCast]
      field_simp
    have h1 : ((σR x : ℝ) / q - (F x).re) ^ 2 ≤ ε ^ 2 := by
      exact sq_le_sq' (by linarith [(abs_le.mp hx1).1, (abs_le.mp hx1).2])
        (by linarith [(abs_le.mp hx1).1, (abs_le.mp hx1).2])
    have h2 : (2 * Real.pi * ((σI x : ℝ) / q) - (F x).im) ^ 2 ≤ (2 * Real.pi * ε) ^ 2 := by
      have : 2 * Real.pi * ((σI x : ℝ) / q) - (F x).im =
          -(2 * Real.pi) * ((F x).im / (2 * Real.pi) - (σI x : ℝ) / q) := by
        field_simp; ring
      rw [this, mul_pow]
      have : ((F x).im / (2 * Real.pi) - (σI x : ℝ) / q) ^ 2 ≤ ε ^ 2 :=
        sq_le_sq' (by linarith [(abs_le.mp hx2).1, (abs_le.mp hx2).2])
          (by linarith [(abs_le.mp hx2).1, (abs_le.mp hx2).2])
      calc (-(2 * Real.pi)) ^ 2 * ((F x).im / (2 * Real.pi) - (σI x : ℝ) / q) ^ 2
          ≤ (-(2 * Real.pi)) ^ 2 * ε ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = (2 * Real.pi * ε) ^ 2 := by ring
    have hsq : ‖((σR x : ℂ) + 2 * Real.pi * Complex.I * (σI x : ℂ)) / q - F x‖ ^ 2 ≤
        (7 * ε) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      have hpi2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) (by linarith : 0 ≤ 12 - Real.pi ^ 2)]
    exact (abs_le_of_sq_le_sq' hsq (by linarith)).2

/-- paper IV `lem:nu-satisfies`, step `rounded-triple-in-embed`, at `H = {0}`: the rounded triple is trivial,
so `e^{σ̃/q}` is constant. -/
theorem l6_rounded_triple_const {X Y Z : Type} (S : Set (X × Y × Z)) (hS : InT S) (q : ℕ)
    (hq : 1 ≤ q) (σR : X → ℤ) (γR : Y → ℤ) (φR : Z → ℤ) (σI : X → ℤ) (γI : Y → ℤ) (φI : Z → ℤ)
    (hR : ∀ p ∈ S, σR p.1 = γR p.2.1 + φR p.2.2)
    (hI : ∀ p ∈ S, ((σI p.1 : ℤ) : ZMod q) = (γI p.2.1 : ZMod q) + (φI p.2.2 : ZMod q)) :
    (∀ x x', σR x = σR x') ∧ (∀ x x', ((σI x : ℤ) : ZMod q) = (σI x' : ZMod q)) ∧
    (∀ x x', Complex.exp (((σR x : ℂ) + 2 * Real.pi * Complex.I * (σI x : ℂ)) / q) =
      Complex.exp (((σR x' : ℂ) + 2 * Real.pi * Complex.I * (σI x' : ℂ)) / q)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 := (l6_inT_embedding_const hS ℤ σR (fun y => - γR y) (fun z => - φR z)
    (fun p hp => by have := hR p hp; show σR p.1 + -γR p.2.1 + -φR p.2.2 = 0; omega)).1
  have h2 := (l6_inT_embedding_const hS (ZMod q) (fun x => (σI x : ZMod q))
    (fun y => - (γI y : ZMod q)) (fun z => - (φI z : ZMod q))
    (fun p hp => by rw [hI p hp]; ring)).1
  refine ⟨h1, h2, ?_⟩
  intro x x'
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hmod := (ZMod.intCast_eq_intCast_iff_dvd_sub (σI x') (σI x) q).mp (h2 x' x)
  obtain ⟨k, hk⟩ := hmod
  refine ⟨k, ?_⟩
  have hk' : (σI x : ℂ) - σI x' = q * k := by exact_mod_cast hk
  rw [h1 x x']
  field_simp
  have : (σI x : ℂ) = σI x' + q * k := by linear_combination hk'
  rw [this]; ring

end L6Rounding
end MaxT
end TrackB
end RestrictedPolynomials
end
