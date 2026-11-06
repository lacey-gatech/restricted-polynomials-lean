module

public import RestrictedPolynomials.TrackB.MasterEmbedding
public import Mathlib.NumberTheory.WellApproximable
public import Mathlib.Data.ZMod.Basic

/-!
# Track B: turning an infinite (circle) embedding into a finite one

Covers paper IV `lem:turn-infinite-to-finite` (Lemma 3.20, L2273-2309) together with its
two steps `#rational-approximation-is-embedding` and `#rounding-preserves-fibres` (absorbed into
`turn_infinite_to_finite_zmod`), and the classical simultaneous Dirichlet approximation theorem
(`simDirichlet_exists`, a wrapper of Mathlib's `NormedAddCommGroup.exists_norm_nsmul_le`).

Readings of the source used here: `AddCircle 1`, with the conclusion strengthened to `ℤ/q`; the gap
in the source that `α` must be the minimal separation of the distinct values of all three maps is
repaired in the proof, not in the statement; `1 ≤ q ≤ N`. The period-`p` variant is
`turn_infinite_to_finite_zmod_period`.

Consumer obligations: scale so that the coercion is injective on the images, and apply
`exists_shift_zero_in_image` before using the master property.
-/

@[expose] public section

open Finset MeasureTheory Metric
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Dirichlet

private theorem dir_ball_measure {ι : Type*} [Fintype ι] {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (volume : Measure (ι → AddCircle (1 : ℝ))) (closedBall 0 (δ / 2)) =
      ENNReal.ofReal δ ^ Fintype.card ι := by
  rw [closedBall_pi _ (by linarith)]
  rw [volume_pi_pi]
  have this : (volume : Measure (AddCircle (1 : ℝ))) (closedBall 0 (δ / 2)) = ENNReal.ofReal δ := by
    rw [AddCircle.volume_closedBall]
    congr 1
    rw [min_eq_right (by linarith)]
    ring
  simp only [Pi.zero_apply, Finset.prod_const, Finset.card_univ]
  exact congrArg (· ^ Fintype.card ι) this

/-- Simultaneous Dirichlet approximation (classical), in the standard form with the bound `q ≤ N`
(paper IV l. 2281-2283 and l. 3935): for real numbers `sᵢ` (`i` in a finite type of size `r`) and
`N ≥ 1` there are integers `1 ≤ q ≤ N` and `pᵢ` with `|sᵢ - pᵢ/q| ≤ 1/(q N^{1/r})`.
Route: Mathlib's `NormedAddCommGroup.exists_norm_nsmul_le` on the torus `ι → AddCircle 1`
(all instances are found: `Pi.normedAddCommGroup`, `Function.compactSpace`,
`instPreconnectedSpaceForall`, `Pi.borelSpace`, `volume.IsAddHaarMeasure`), with
`δ = (N+1)^{-1/r}`; it gives the slightly better bound `(N+1)^{-1/r}`. -/
theorem simDirichlet_exists {ι : Type*} [Fintype ι] (s : ι → ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ (q : ℕ) (p : ι → ℤ), 1 ≤ q ∧ q ≤ N ∧
      ∀ i, |s i - (p i : ℝ) / q| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / (Fintype.card ι : ℝ))) := by
  classical
  by_cases hr : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hr
    exact ⟨1, fun _ => 0, le_rfl, hN, fun i => isEmptyElim i⟩
  have hr' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hr
  set r : ℝ := (Fintype.card ι : ℝ) with hrdef
  set δ : ℝ := ((N : ℝ) + 1) ^ (-(1 / r)) with hδdef
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos (by linarith) _
  have hδ1 : δ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by have : 0 < 1 / r := by positivity
                                                 linarith)
  have hδr : δ ^ Fintype.card ι = ((N : ℝ) + 1)⁻¹ := by
    rw [hδdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : -(1 / r) * (Fintype.card ι : ℝ) = -1 := by
      rw [← hrdef]; field_simp
    rw [this, Real.rpow_neg_one]
  let ξ : ι → AddCircle (1 : ℝ) := fun i => ((s i : ℝ) : AddCircle (1 : ℝ))
  have key : (volume : Measure (ι → AddCircle (1 : ℝ))) Set.univ ≤
      (N + 1) • (volume : Measure (ι → AddCircle (1 : ℝ))) (closedBall 0 (δ / 2)) := by
    rw [dir_ball_measure hδ0.le hδ1, ← ENNReal.ofReal_pow hδ0.le, hδr]
    have h1 : (volume : Measure (ι → AddCircle (1 : ℝ))) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp [AddCircle.measure_univ]
    rw [h1, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have : ((N : ℝ) + 1)⁻¹ * 1 = ((N : ℝ) + 1)⁻¹ := mul_one _
    rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring] 
    rw [mul_inv_cancel₀ (by positivity)]
    simp
  obtain ⟨j, hj, hjn⟩ := NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hN δ key
  rw [Set.mem_Icc] at hj
  refine ⟨j, fun i => round ((j : ℝ) * s i), hj.1, hj.2, fun i => ?_⟩
  have hi : ‖j • ξ i‖ ≤ δ := le_trans (by
    simpa using (norm_le_pi_norm (j • ξ) i)) hjn
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj.1
  have e1 : j • ξ i = (((j : ℝ) * s i : ℝ) : AddCircle (1 : ℝ)) := by
    simp [ξ]
  rw [e1, UnitAddCircle.norm_eq] at hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : δ ≤ 1 / (N : ℝ) ^ (1 / r) := by
    rw [hδdef, one_div (_ ^ _), ← Real.rpow_neg hNpos.le]
    exact Real.rpow_le_rpow_of_nonpos hNpos (by linarith) (by
      have : 0 < 1 / r := by positivity
      linarith)
  have : |s i - (round ((j : ℝ) * s i) : ℝ) / j| = |(j : ℝ) * s i - round ((j : ℝ) * s i)| / j := by
    rw [← abs_of_pos hjpos, ← abs_div, abs_of_pos hjpos]
    congr 1
    field_simp
  rw [this, div_le_iff₀ hjpos]
  calc _ ≤ δ := hi
    _ ≤ 1 / (N : ℝ) ^ (1 / r) := hle
    _ = _ := by field_simp

end Dirichlet

section TurnInfinite
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

private theorem exists_pos_lower {T : Type*} [Finite T] (f : T → ℝ) (hf : ∀ t, 0 < f t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, ε ≤ f t := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨1, one_pos, fun t => isEmptyElim t⟩
  · obtain ⟨t0, ht0⟩ := Finite.exists_min f
    exact ⟨f t0, hf t0, ht0⟩

private theorem coe_eq_coe_iff (a b : ℝ) :
    (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) ↔ ∃ n : ℤ, a - b = n := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one]
  exact exists_congr fun n => eq_comm

private theorem int_eq_zero_of_abs_lt_one {M : ℤ} (h : |(M : ℝ)| < 1) : M = 0 := by
  have : |M| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this

/-- the real-number core of the rounding step: simultaneous Dirichlet approximation with the
separation `α` over all pairs of values. -/
private theorem round_core {ι : Type} [Fintype ι] (s : ι → ℝ) :
    ∃ (q : ℕ) (p : ι → ℤ), 0 < q ∧
      (∀ i j, (∃ n : ℤ, s i - s j = n) ↔ (p i : ZMod q) = (p j : ZMod q)) ∧
      (∀ a b c, (∃ k : ℤ, s a + s b + s c = k) →
        (p a : ZMod q) + (p b : ZMod q) + (p c : ZMod q) = 0) := by
  classical
  let f : ι × ι → ℝ := fun ij =>
    if ∃ n : ℤ, s ij.1 - s ij.2 = n then 1 else |(s ij.1 - s ij.2) - round (s ij.1 - s ij.2)|
  have hf : ∀ ij, 0 < f ij := by
    intro ij
    by_cases hc : ∃ n : ℤ, s ij.1 - s ij.2 = n
    · simp [f, hc]
    · simp only [f, hc, ite_false]
      apply abs_pos.mpr
      intro h0
      exact hc ⟨round (s ij.1 - s ij.2), by linarith⟩
  obtain ⟨ε, hε0, hε⟩ := exists_pos_lower f hf
  set α : ℝ := min ε (1 / 2) with hαdef
  have hα0 : 0 < α := lt_min hε0 (by norm_num)
  have hα1 : α ≤ 1 / 2 := min_le_right _ _
  have hαlow : ∀ i j, ¬ (∃ n : ℤ, s i - s j = n) →
      α ≤ |(s i - s j) - round (s i - s j)| := by
    intro i j hij
    have := hε (i, j)
    simp only [f, hij, ite_false] at this
    exact le_trans (min_le_left _ _) this
  set N : ℕ := ⌈(3 / α) ^ Fintype.card ι⌉₊ with hNdef
  have hNpos : 0 < N := Nat.ceil_pos.mpr (pow_pos (by positivity) _)
  obtain ⟨q, p, hq1, hqN, hdir⟩ := simDirichlet_exists s hNpos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqge : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  -- the key bound
  have hD : ∀ i, |(q : ℝ) * s i - p i| ≤ α / 3 := by
    intro i
    have hr : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    have hE : 3 / α ≤ (N : ℝ) ^ (1 / (Fintype.card ι : ℝ)) := by
      have h1 : (3 / α) ^ Fintype.card ι ≤ (N : ℝ) := Nat.le_ceil _
      calc 3 / α = ((3 / α) ^ Fintype.card ι) ^ ((Fintype.card ι : ℝ)⁻¹) :=
            (Real.pow_rpow_inv_natCast (by positivity) (by omega)).symm
        _ ≤ (N : ℝ) ^ ((Fintype.card ι : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) h1 (by positivity)
        _ = _ := by rw [one_div]
    have h2 := hdir i
    have hEpos : 0 < (N : ℝ) ^ (1 / (Fintype.card ι : ℝ)) := lt_of_lt_of_le (by positivity) hE
    have h3 : 1 / ((q : ℝ) * (N : ℝ) ^ (1 / (Fintype.card ι : ℝ))) ≤ α / (3 * q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 3 ≤ α * (N : ℝ) ^ (1 / (Fintype.card ι : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hE hα0.le
        rwa [mul_div_cancel₀ _ hα0.ne'] at this
      nlinarith
    have h4 : |s i - (p i : ℝ) / q| ≤ α / (3 * q) := le_trans h2 h3
    have h5 : |(q : ℝ) * s i - p i| = q * |s i - (p i : ℝ) / q| := by
      rw [← abs_of_pos hq0, ← abs_mul, abs_of_pos hq0]
      congr 1
      field_simp
    rw [h5]
    calc (q : ℝ) * |s i - (p i : ℝ) / q| ≤ q * (α / (3 * q)) := by gcongr
      _ = α / 3 := by field_simp
  have hDa := fun i => (abs_le.mp (hD i))
  refine ⟨q, p, hq1, ?_, ?_⟩
  · intro i j
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨n, hn⟩
      have hM : |((q * n - (p i - p j) : ℤ) : ℝ)| < 1 := by
        have : ((q * n - (p i - p j) : ℤ) : ℝ) =
            ((q : ℝ) * s i - p i) - ((q : ℝ) * s j - p j) := by
          push_cast
          have : (n : ℝ) = s i - s j := hn.symm
          rw [this]; ring
        rw [this, abs_lt]
        have := hDa i; have := hDa j
        constructor <;> linarith [hDa i, hDa j]
      have := int_eq_zero_of_abs_lt_one hM
      exact ⟨n, by linarith⟩
    · rintro ⟨m, hm⟩
      by_contra hne
      have hlow := hαlow i j hne
      have hmR : (p i : ℝ) - p j = q * m := by exact_mod_cast hm
      have h1 : |(s i - s j) - round (s i - s j)| ≤ |(s i - s j) - (m : ℝ)| := round_le _ _
      have h2 : |(s i - s j) - (m : ℝ)| ≤ |(q : ℝ) * ((s i - s j) - (m : ℝ))| := by
        rw [abs_mul, abs_of_pos hq0]
        exact le_mul_of_one_le_left (abs_nonneg _) hqge
      have h3 : (q : ℝ) * ((s i - s j) - (m : ℝ)) =
          ((q : ℝ) * s i - p i) - ((q : ℝ) * s j - p j) := by
        have : (q : ℝ) * m = p i - p j := hmR.symm
        linear_combination (-1 : ℝ) * this
      have h4 : |(q : ℝ) * ((s i - s j) - (m : ℝ))| ≤ 2 * α / 3 := by
        rw [h3, abs_le]
        constructor <;> linarith [hDa i, hDa j]
      linarith
  · rintro a b c ⟨k, hk⟩
    rw [← Int.cast_add, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hM : |((q * k - (p a + p b + p c) : ℤ) : ℝ)| < 1 := by
      have : ((q * k - (p a + p b + p c) : ℤ) : ℝ) =
          ((q : ℝ) * s a - p a) + ((q : ℝ) * s b - p b) + ((q : ℝ) * s c - p c) := by
        push_cast
        rw [show (k : ℝ) = s a + s b + s c from hk.symm]; ring
      rw [this, abs_lt]
      constructor <;> linarith [hDa a, hDa b, hDa c]
    have := int_eq_zero_of_abs_lt_one hM
    exact ⟨k, by linarith⟩

private theorem equivEmb_of_fibres {W : Type} {H H' : Type*} (σ : W → H) (σ' : W → H')
    (h : ∀ x x', σ x = σ x' ↔ σ' x = σ' x') :
    ∃ m : Set.range σ ≃ Set.range σ', ∀ x, (m ⟨σ x, x, rfl⟩ : H') = σ' x := by
  let f : Set.range σ → Set.range σ' := fun a => ⟨σ' a.2.choose, _, rfl⟩
  have hf : ∀ x, f ⟨σ x, x, rfl⟩ = ⟨σ' x, x, rfl⟩ := by
    intro x
    apply Subtype.ext
    exact (h _ _).mp (Classical.choose_spec (⟨x, rfl⟩ : ∃ y, σ y = σ x))
  have hinj : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h1 : σ' ha.choose = σ' hb.choose := congrArg Subtype.val hab
    have h2 := (h _ _).mpr h1
    rw [ha.choose_spec, hb.choose_spec] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    rintro ⟨_, x, rfl⟩
    exact ⟨⟨σ x, x, rfl⟩, hf x⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun x => congrArg Subtype.val (hf x)⟩

/-- fibre form of the turning step; the engine of both public statements. -/
private theorem turn_core (S : Set (X × Y × Z))
    (σ : X → AddCircle (1 : ℝ)) (γ : Y → AddCircle (1 : ℝ)) (φ : Z → AddCircle (1 : ℝ))
    (h : IsEmbedding3 S σ γ φ) :
    ∃ (q : ℕ) (σ' : X → ZMod q) (γ' : Y → ZMod q) (φ' : Z → ZMod q), 0 < q ∧
      IsEmbedding3 S σ' γ' φ' ∧
      (∀ x x', σ x = σ x' ↔ σ' x = σ' x') ∧ (∀ y y', γ y = γ y' ↔ γ' y = γ' y') ∧
      (∀ z z', φ z = φ z' ↔ φ' z = φ' z') := by
  have hsurj : Function.Surjective ((↑) : ℝ → AddCircle (1 : ℝ)) := QuotientAddGroup.mk_surjective
  let ρ : AddCircle (1 : ℝ) → ℝ := Function.surjInv hsurj
  have hρ : ∀ t, ((ρ t : ℝ) : AddCircle (1 : ℝ)) = t := Function.surjInv_eq hsurj
  let val : X ⊕ Y ⊕ Z → AddCircle (1 : ℝ) := Sum.elim σ (Sum.elim γ φ)
  let s : X ⊕ Y ⊕ Z → ℝ := fun i => ρ (val i)
  have hv : ∀ i j, val i = val j ↔ ∃ n : ℤ, s i - s j = n := by
    intro i j
    rw [← coe_eq_coe_iff]
    simp only [s, hρ]
  obtain ⟨q, p, hq, hfib, heq⟩ := round_core s
  refine ⟨q, fun x => (p (Sum.inl x) : ZMod q), fun y => (p (Sum.inr (Sum.inl y)) : ZMod q),
    fun z => (p (Sum.inr (Sum.inr z)) : ZMod q), hq, ?_, ?_, ?_, ?_⟩
  · rw [isEmbedding3_iff]
    intro pt hpt
    have h0 := (isEmbedding3_iff S σ γ φ).mp h pt hpt
    apply heq
    have h1 : ((s (Sum.inl pt.1) + s (Sum.inr (Sum.inl pt.2.1)) + s (Sum.inr (Sum.inr pt.2.2)) : ℝ) :
        AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_add, AddCircle.coe_add]
      simp only [s, hρ, val, Sum.elim_inl, Sum.elim_inr]
      exact h0
    rw [AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by simpa using hn.symm⟩
  · intro x x'
    rw [← hfib, ← hv]; rfl
  · intro y y'
    rw [← hfib, ← hv]; rfl
  · intro z z'
    rw [← hfib, ← hv]; rfl

/-- Paper IV `lem:turn-infinite-to-finite` (Lemma 3.20) with its two steps, in the form the proof gives:
an embedding of `S` into `([0,1), + mod 1) ≅ AddCircle 1` is equivalent (Definition 3.19) to an
embedding of `S` into the cyclic group `ℤ/q`, `q ≥ 1`. -/
theorem turn_infinite_to_finite_zmod (S : Set (X × Y × Z))
    (σ : X → AddCircle (1 : ℝ)) (γ : Y → AddCircle (1 : ℝ)) (φ : Z → AddCircle (1 : ℝ))
    (h : IsEmbedding3 S σ γ φ) :
    ∃ (q : ℕ) (σ' : X → ZMod q) (γ' : Y → ZMod q) (φ' : Z → ZMod q), 0 < q ∧
      IsEmbedding3 S σ' γ' φ' ∧ EquivalentEmbeddings σ γ φ σ' γ' φ' := by
  obtain ⟨q, σ', γ', φ', hq, he, h1, h2, h3⟩ := turn_core S σ γ φ h
  exact ⟨q, σ', γ', φ', hq, he, equivEmb_of_fibres σ σ' h1, equivEmb_of_fibres γ γ' h2,
    equivEmb_of_fibres φ φ' h3⟩

/-- Paper IV `lem:turn-infinite-to-finite`, period-`p` form: the same with
`AddCircle p`, `p ≠ 0`, obtained from the period-`1` case by the additive equivalence
`AddCircle.equivAddCircle p 1`. -/
theorem turn_infinite_to_finite_zmod_period {p : ℝ} (hp : p ≠ 0) (S : Set (X × Y × Z))
    (σ : X → AddCircle p) (γ : Y → AddCircle p) (φ : Z → AddCircle p)
    (h : IsEmbedding3 S σ γ φ) :
    ∃ (q : ℕ) (σ' : X → ZMod q) (γ' : Y → ZMod q) (φ' : Z → ZMod q), 0 < q ∧
      IsEmbedding3 S σ' γ' φ' ∧ EquivalentEmbeddings σ γ φ σ' γ' φ' := by
  let e : AddCircle p ≃+ AddCircle (1 : ℝ) := AddCircle.equivAddCircle p 1 hp one_ne_zero
  have he : IsEmbedding3 S (fun x => e (σ x)) (fun y => e (γ y)) (fun z => e (φ z)) := by
    rw [isEmbedding3_iff] at h ⊢
    intro pt hpt
    rw [← map_add, ← map_add, h pt hpt, map_zero]
  obtain ⟨q, σ', γ', φ', hq, he', h1, h2, h3⟩ :=
    turn_core S (fun x => e (σ x)) (fun y => e (γ y)) (fun z => e (φ z)) he
  simp only [e.injective.eq_iff] at h1 h2 h3
  exact ⟨q, σ', γ', φ', hq, he', equivEmb_of_fibres σ σ' h1, equivEmb_of_fibres γ γ' h2,
    equivEmb_of_fibres φ φ' h3⟩

/-- Paper IV `lem:turn-infinite-to-finite`, literally: the conclusion "equivalent to an Abelian embedding of
`μ` into a finite Abelian group". -/
theorem turn_infinite_to_finite (μ : FinProb (X × Y × Z))
    (σ : X → AddCircle (1 : ℝ)) (γ : Y → AddCircle (1 : ℝ)) (φ : Z → AddCircle (1 : ℝ))
    (h : IsEmbedding3 μ.support σ γ φ) :
    ∃ (G : Type) (_ : AddCommGroup G), Finite G ∧
      ∃ (σ' : X → G) (γ' : Y → G) (φ' : Z → G),
        IsEmbedding3 μ.support σ' γ' φ' ∧ EquivalentEmbeddings σ γ φ σ' γ' φ' := by
  obtain ⟨q, σ', γ', φ', hq, he, hequiv⟩ := turn_infinite_to_finite_zmod μ.support σ γ φ h
  have : NeZero q := ⟨hq.ne'⟩
  exact ⟨ZMod q, inferInstance, inferInstance, σ', γ', φ', he, hequiv⟩

end TurnInfinite

end TrackB
end RestrictedPolynomials
end
