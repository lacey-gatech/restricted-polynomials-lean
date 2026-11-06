module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import RestrictedPolynomials.FinProb

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate Matrix BoundedContinuousFunction

noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section ExtCharacters

/-- Classical fact `character-orthogonality-finite-abelian` (orthonormality). -/
theorem ext_character_orthonormal {H : Type} [AddCommGroup H] [Fintype H] (ψ₁ ψ₂ : AddChar H ℂ) :
    (∑ x, (starRingEnd ℂ) (ψ₁ x) * ψ₂ x) / (Fintype.card H : ℂ) = if ψ₁ = ψ₂ then 1 else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole ψ₁ ψ₂
  rw [RCLike.wInner_cWeight_eq_expect] at h
  simpa [Finset.expect_eq_sum_div_card, RCLike.inner_apply, mul_comm] using h

/-- same node (basis: the characters span `H → ℂ`). -/
theorem ext_character_basis (H : Type) [AddCommGroup H] [Fintype H] :
    ∃ b : Module.Basis (AddChar H ℂ) ℂ (H → ℂ), ∀ ψ x, b ψ x = ψ x :=
  ⟨AddChar.complexBasis H, fun ψ x => by rw [AddChar.complexBasis_apply]⟩

/-- same node (the coset average of a character vanishes unless it is trivial on the subgroup). -/
theorem ext_character_coset_sum_eq_zero {H : Type} [AddCommGroup H] [Fintype H]
    (K : AddSubgroup H) [DecidablePred (· ∈ K)] (a : H) (ψ : AddChar H ℂ)
    (hψ : ∃ k ∈ K, ψ k ≠ 1) :
    ∑ k ∈ Finset.univ.filter (· ∈ K), ψ (a + k) = 0 := by
  obtain ⟨k₀, hk₀, hne⟩ := hψ
  have hshift : ∑ k ∈ Finset.univ.filter (· ∈ K), ψ (a + k) =
      ψ k₀ * ∑ k ∈ Finset.univ.filter (· ∈ K), ψ (a + k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun k => k - k₀) (fun k => k + k₀) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact K.sub_mem hk hk₀
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact K.add_mem hk hk₀
    · intro k _; simp
    · intro k _; simp
    · intro k _
      rw [show a + k = (a + (k - k₀)) + k₀ by abel, AddChar.map_add_eq_mul, mul_comm]
  have : (1 - ψ k₀) * ∑ k ∈ Finset.univ.filter (· ∈ K), ψ (a + k) = 0 := by
    rw [sub_mul, one_mul]; exact sub_eq_zero.2 hshift
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

end ExtCharacters

section ExtLog

/-- Classical fact `complex-logarithm-estimates`: `exp (log w) = w`. -/
theorem ext_exp_log (w : ℂ) (hw : w ≠ 0) : Complex.exp (Complex.log w) = w :=
  Complex.exp_log hw

/-- same node: `log (w₁ w₂) ≡ log w₁ + log w₂ (mod 2πi)`. -/
theorem ext_log_mul_mod (w₁ w₂ : ℂ) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    ∃ k : ℤ, Complex.log (w₁ * w₂) =
      Complex.log w₁ + Complex.log w₂ + 2 * Real.pi * Complex.I * k := by
  have : Complex.exp (Complex.log (w₁ * w₂)) = Complex.exp (Complex.log w₁ + Complex.log w₂) := by
    rw [Complex.exp_add, Complex.exp_log h₁, Complex.exp_log h₂,
      Complex.exp_log (mul_ne_zero h₁ h₂)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 this
  exact ⟨k, by rw [hk]; ring⟩

/-- same node: `|log w| ≤ C |w - 1|` for `|w - 1| ≤ 1/2` (`C = 3/2`, the absolute constant). -/
theorem ext_log_norm_le (w : ℂ) (hw : ‖w - 1‖ ≤ 1 / 2) : ‖Complex.log w‖ ≤ 3 / 2 * ‖w - 1‖ := by
  have := Complex.norm_log_one_add_half_le_self (z := w - 1) hw
  simpa using this

/-- same node: `|e^u - 1| ≤ C |u|` for `|u| ≤ 1` (`C = 2`, the absolute constant). -/
theorem ext_exp_sub_one_norm_le (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖Complex.exp u - 1‖ ≤ 2 * ‖u‖ :=
  Complex.norm_exp_sub_one_le hu

end ExtLog

section ExtCompact

/-- Classical fact `sequential-compactness-finite-dim` (Bolzano-Weierstrass), real and complex. -/
theorem ext_bolzano_weierstrass {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (x : ℕ → E)
    (hx : Bornology.IsBounded (Set.range x)) :
    ∃ (a : E) (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds a) := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  obtain ⟨a, -, φ, hφ, h⟩ := tendsto_subseq_of_bounded hx (fun n => Set.mem_range_self n)
  exact ⟨a, φ, hφ, h⟩

end ExtCompact

section ExtSpectral

/-- Classical fact `spectral-theorem-self-adjoint`: an orthonormal eigenbasis with real eigenvalues. -/
theorem ext_spectral_eigenbasis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (ev : Fin (Module.finrank ℂ E) → ℝ), ∀ i, A (b i) = (ev i : ℂ) • b i :=
  ⟨hA.eigenvectorBasis rfl, hA.eigenvalues rfl, fun i => hA.apply_eigenvectorBasis rfl i⟩

/-- same node: every eigenvalue is real. -/
theorem ext_spectral_real_eigenvalues {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue A μ) : μ.im = 0 := by
  have := hA.conj_eigenvalue_eq_self hμ
  have h2 := congrArg Complex.im this
  simp at h2
  linarith

/-- same node: the orthogonal complement of an `A`-invariant subspace is `A`-invariant. -/
theorem ext_spectral_invariant_complement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (p : Submodule ℂ E) (hp : ∀ v ∈ p, A v ∈ p) : ∀ v ∈ pᗮ, A v ∈ pᗮ := by
  have := hA.orthogonalComplement_mem_invtSubmodule (p := p) (by
    intro v hv; exact hp v hv)
  exact fun v hv => this hv

end ExtSpectral

section ExtStructure

/-- Classical fact `structure-theorem-finite-abelian-groups`. -/
theorem ext_structure_finite_abelian (H : Type) [AddCommGroup H] [Finite H] :
    ∃ (k : ℕ) (p r : Fin k → ℕ), (∀ i, (p i).Prime) ∧ (∀ i, 1 ≤ r i) ∧
      Nonempty (H ≃+ ((i : Fin k) → ZMod (p i ^ r i))) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite H
  let g : {i : ι // e i ≠ 0} ≃ Fin (Fintype.card {i : ι // e i ≠ 0}) := Fintype.equivFin _
  let E1 : ((i : ι) → ZMod (p i ^ e i)) ≃+ ((j : {i : ι // e i ≠ 0}) → ZMod (p j.1 ^ e j.1)) :=
    { toFun := fun F j => F j.1
      invFun := fun G i => if h : e i ≠ 0 then G ⟨i, h⟩ else 0
      left_inv := fun F => by
        funext i
        by_cases h : e i ≠ 0
        · simp [h]
        · have hs : Subsingleton (ZMod (p i ^ e i)) :=
            ZMod.subsingleton_iff.2 (by rw [not_not.1 h, pow_zero])
          exact hs.elim _ _
      right_inv := fun G => by
        funext j
        simp [j.2]
      map_add' := fun _ _ => rfl }
  let E2 : ((j : {i : ι // e i ≠ 0}) → ZMod (p j.1 ^ e j.1)) ≃+
      ((m : Fin (Fintype.card {i : ι // e i ≠ 0})) → ZMod (p (g.symm m).1 ^ e (g.symm m).1)) :=
    ⟨Equiv.piCongrLeft' (fun j : {i : ι // e i ≠ 0} => ZMod (p j.1 ^ e j.1)) g, fun _ _ => rfl⟩
  refine ⟨Fintype.card {i : ι // e i ≠ 0}, fun m => p (g.symm m).1, fun m => e (g.symm m).1,
    fun m => hp _, fun m => Nat.one_le_iff_ne_zero.2 (g.symm m).2,
    ⟨((f.trans (DirectSum.addEquivProd _)).trans E1).trans E2⟩⟩

end ExtStructure

section ExtTensor

/-- Single-factor completeness: a square weighted orthonormal family is a basis, in dual form. -/
private theorem tensor_dual_orth {A ι : Type} [Fintype A] [Fintype ι] [DecidableEq ι]
    [DecidableEq A] (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (u : ι → A → ℂ)
    (hon : ∀ b b' : ι, ∑ a, (w a : ℂ) * (starRingEnd ℂ (u b a) * u b' a) = if b = b' then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card A) :
    (∀ a, 0 < w a) ∧ ∀ a a' : A,
      ∑ b, starRingEnd ℂ (u b a) * u b a' = if a = a' then (((w a)⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Matrix ι A ℂ, ∀ b a, S b a = ((Real.sqrt (w a) : ℝ) : ℂ) * u b a :=
    ⟨Matrix.of fun b a => ((Real.sqrt (w a) : ℝ) : ℂ) * u b a, fun _ _ => rfl⟩
  have hs : ∀ a, ((Real.sqrt (w a) : ℝ) : ℂ) * ((Real.sqrt (w a) : ℝ) : ℂ) = (w a : ℂ) := by
    intro a
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw a)]
  have h1 : S * Sᴴ = 1 := by
    ext b b'
    have := hon b' b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, hS, star_mul', Complex.star_def, Complex.conj_ofReal]
    calc ∑ a, ((Real.sqrt (w a) : ℝ) : ℂ) * u b a *
          (((Real.sqrt (w a) : ℝ) : ℂ) * (starRingEnd ℂ) (u b' a))
        = ∑ a, (w a : ℂ) * (starRingEnd ℂ (u b' a) * u b a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← hs a]; ring
      _ = _ := by rw [this]; simp [eq_comm]
  have h2 : Sᴴ * S = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).1 h1
  have h3 : ∀ a a' : A, ((Real.sqrt (w a) : ℝ) : ℂ) * ((Real.sqrt (w a') : ℝ) : ℂ) *
      ∑ b, starRingEnd ℂ (u b a) * u b a' = if a = a' then 1 else 0 := by
    intro a a'
    have := congrFun (congrFun h2 a) a'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.conjTranspose_apply, hS, star_mul', Complex.star_def,
      Complex.conj_ofReal] at this
    rw [Finset.mul_sum, ← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hpos : ∀ a, 0 < w a := by
    intro a
    have := h3 a a
    simp only [ite_true] at this
    rcases (hw a).lt_or_eq with h | h
    · exact h
    · rw [← h] at this; simp at this
  refine ⟨hpos, fun a a' => ?_⟩
  have hsa : (Real.sqrt (w a) : ℝ) ≠ 0 := (Real.sqrt_pos.2 (hpos a)).ne'
  have hsa' : (Real.sqrt (w a') : ℝ) ≠ 0 := (Real.sqrt_pos.2 (hpos a')).ne'
  have h4 := h3 a a'
  by_cases h : a = a'
  · subst h
    simp only [ite_true] at h4 ⊢
    rw [hs] at h4
    have : (w a : ℂ) ≠ 0 := by exact_mod_cast (hpos a).ne'
    rw [Complex.ofReal_inv]
    field_simp
    simpa [mul_comm] using h4
  · simp only [h, ite_false] at h4 ⊢
    have : ((Real.sqrt (w a) : ℝ) : ℂ) * ((Real.sqrt (w a') : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hsa) (by exact_mod_cast hsa')
    exact (mul_eq_zero.1 h4).resolve_left this

/-- Expansion in a square weighted orthonormal family. -/
private theorem tensor_expansion_core {A ι : Type} [Fintype A] [Fintype ι] [DecidableEq ι]
    [DecidableEq A] (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (u : ι → A → ℂ)
    (hon : ∀ b b' : ι, ∑ a, (w a : ℂ) * (starRingEnd ℂ (u b a) * u b' a) = if b = b' then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card A) (f : A → ℂ) (x : A) :
    f x = ∑ b, (∑ y, (w y : ℂ) * (starRingEnd ℂ (u b y) * f y)) * u b x := by
  obtain ⟨hpos, hdual⟩ := tensor_dual_orth w hw u hon hcard
  have : ∀ b, (∑ y, (w y : ℂ) * (starRingEnd ℂ (u b y) * f y)) * u b x =
      ∑ y, (w y : ℂ) * f y * (starRingEnd ℂ (u b y) * u b x) := by
    intro b
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hdual]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have : (w x : ℂ) ≠ 0 := by exact_mod_cast (hpos x).ne'
  rw [Complex.ofReal_inv]
  field_simp

/-- Parseval in a square weighted orthonormal family. -/
private theorem tensor_parseval_core {A ι : Type} [Fintype A] [Fintype ι] [DecidableEq ι]
    [DecidableEq A] (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (u : ι → A → ℂ)
    (hon : ∀ b b' : ι, ∑ a, (w a : ℂ) * (starRingEnd ℂ (u b a) * u b' a) = if b = b' then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card A) (f : A → ℂ) :
    ∑ y, w y * ‖f y‖ ^ 2 = ∑ b, ‖∑ y, (w y : ℂ) * (starRingEnd ℂ (u b y) * f y)‖ ^ 2 := by
  obtain ⟨hpos, hdual⟩ := tensor_dual_orth w hw u hon hcard
  apply Complex.ofReal_injective
  push_cast
  have hn : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = starRingEnd ℂ z * z := by
    intro z; rw [Complex.conj_mul']
  simp_rw [hn]
  have key : ∀ b, starRingEnd ℂ (∑ y, (w y : ℂ) * (starRingEnd ℂ (u b y) * f y)) *
      (∑ y, (w y : ℂ) * (starRingEnd ℂ (u b y) * f y)) =
      ∑ y', ∑ y, (w y' : ℂ) * (w y : ℂ) * (starRingEnd ℂ (f y') * f y) *
        (starRingEnd ℂ (u b y) * u b y') := by
    intro b
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hdual]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have : (w y' : ℂ) ≠ 0 := by exact_mod_cast (hpos y').ne'
  rw [Complex.ofReal_inv]
  field_simp

/-- Gram matrix of a product of families. -/
private theorem tensor_prod_gram {n : ℕ} (A : Fin n → Type) [∀ i, Fintype (A i)]
    (ι : Fin n → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (μ : ∀ i, FinProb (A i)) (u : ∀ i, ι i → A i → ℂ)
    (hon : ∀ i (b b' : ι i),
      ∑ a, (μ i).prob a * (starRingEnd ℂ (u i b a) * u i b' a) = if b = b' then 1 else 0)
    (b b' : ∀ i, ι i) :
    ∑ x : ∀ i, A i, (∏ i, (μ i).prob (x i)) *
        (starRingEnd ℂ (∏ i, u i (b i) (x i)) * ∏ i, u i (b' i) (x i)) = if b = b' then 1 else 0 := by
  classical
  have h1 : ∀ x : ∀ i, A i, ((∏ i, (μ i).prob (x i) : ℝ) : ℂ) *
        (starRingEnd ℂ (∏ i, u i (b i) (x i)) * ∏ i, u i (b' i) (x i)) =
      ∏ i, (((μ i).prob (x i) : ℝ) : ℂ) * (starRingEnd ℂ (u i (b i) (x i)) * u i (b' i) (x i)) := by
    intro x
    simp only [Complex.ofReal_prod, map_prod, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun i => (Finset.univ : Finset (A i)))
    (fun i a => (((μ i).prob a : ℝ) : ℂ) * (starRingEnd ℂ (u i (b i) a) * u i (b' i) a))]
  simp_rw [hon]
  by_cases h : b = b'
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The cardinalities of the product index types agree. -/
private theorem tensor_card_pi {n : ℕ} (A : Fin n → Type) [∀ i, Fintype (A i)]
    (ι : Fin n → Type) [∀ i, Fintype (ι i)]
    (hcard : ∀ i, Fintype.card (ι i) = Fintype.card (A i)) :
    Fintype.card (∀ i, ι i) = Fintype.card (∀ i, A i) := by
  rw [Fintype.card_pi, Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => hcard i

/-- Classical fact `tensor-product-orthonormal-basis` (orthonormality of the products). The
weighted `L²` of a finite product of finite probability spaces is not in Mathlib: stated as
recorded in the graph, `u i` an orthonormal basis (orthonormal, `|ι i| = |A i|`) of `L²(A i, μ i)`. -/
theorem ext_tensor_onb_orthonormal {n : ℕ} (A : Fin n → Type) [∀ i, Fintype (A i)]
    (ι : Fin n → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (μ : ∀ i, FinProb (A i)) (u : ∀ i, ι i → A i → ℂ)
    (hon : ∀ i (b b' : ι i),
      ∑ a, (μ i).prob a * (starRingEnd ℂ (u i b a) * u i b' a) = if b = b' then 1 else 0)
    (hcard : ∀ i, Fintype.card (ι i) = Fintype.card (A i)) :
    ∀ b b' : ∀ i, ι i,
      ∑ x : ∀ i, A i, (∏ i, (μ i).prob (x i)) *
        (starRingEnd ℂ (∏ i, u i (b i) (x i)) * ∏ i, u i (b' i) (x i)) = if b = b' then 1 else 0 :=
  fun b b' => by
    have _ := hcard
    exact tensor_prod_gram A ι μ u hon b b'

/-- same node (expansion `f = Σ_b ⟨f, u_b⟩ u_b`). -/
theorem ext_tensor_onb_expansion {n : ℕ} (A : Fin n → Type) [∀ i, Fintype (A i)]
    (ι : Fin n → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (μ : ∀ i, FinProb (A i)) (u : ∀ i, ι i → A i → ℂ)
    (hon : ∀ i (b b' : ι i),
      ∑ a, (μ i).prob a * (starRingEnd ℂ (u i b a) * u i b' a) = if b = b' then 1 else 0)
    (hcard : ∀ i, Fintype.card (ι i) = Fintype.card (A i)) (f : (∀ i, A i) → ℂ) (x : ∀ i, A i) :
    f x = ∑ b : ∀ i, ι i,
      (∑ y : ∀ i, A i, (∏ i, (μ i).prob (y i)) *
        (starRingEnd ℂ (∏ i, u i (b i) (y i)) * f y)) * ∏ i, u i (b i) (x i) := by
  classical
  exact tensor_expansion_core (fun y : ∀ i, A i => ∏ i, (μ i).prob (y i))
    (fun y => Finset.prod_nonneg fun i _ => (μ i).nonneg _)
    (fun (b : ∀ i, ι i) (y : ∀ i, A i) => ∏ i, u i (b i) (y i))
    (fun b b' => by simpa using tensor_prod_gram A ι μ u hon b b')
    (tensor_card_pi A ι hcard) f x

/-- same node (Parseval). -/
theorem ext_tensor_onb_parseval {n : ℕ} (A : Fin n → Type) [∀ i, Fintype (A i)]
    (ι : Fin n → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (μ : ∀ i, FinProb (A i)) (u : ∀ i, ι i → A i → ℂ)
    (hon : ∀ i (b b' : ι i),
      ∑ a, (μ i).prob a * (starRingEnd ℂ (u i b a) * u i b' a) = if b = b' then 1 else 0)
    (hcard : ∀ i, Fintype.card (ι i) = Fintype.card (A i)) (f : (∀ i, A i) → ℂ) :
    ∑ y : ∀ i, A i, (∏ i, (μ i).prob (y i)) * ‖f y‖ ^ 2 = ∑ b : ∀ i, ι i,
      ‖∑ y : ∀ i, A i, (∏ i, (μ i).prob (y i)) *
        (starRingEnd ℂ (∏ i, u i (b i) (y i)) * f y)‖ ^ 2 := by
  classical
  exact tensor_parseval_core (fun y : ∀ i, A i => ∏ i, (μ i).prob (y i))
    (fun y => Finset.prod_nonneg fun i _ => (μ i).nonneg _)
    (fun (b : ∀ i, ι i) (y : ∀ i, A i) => ∏ i, u i (b i) (y i))
    (fun b b' => by simpa using tensor_prod_gram A ι μ u hon b b')
    (tensor_card_pi A ι hcard) f

end ExtTensor

section ExtSphere

private theorem sph_sumsq_mulVec {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ) (w : Fin k → ℂ) :
    ∑ i, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
  have hU : star (U : Matrix (Fin k) (Fin k) ℂ) * (U : Matrix (Fin k) (Fin k) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 U.2
  have key : ∀ v : Fin k → ℂ, (((∑ i, ‖v i‖ ^ 2 : ℝ)) : ℂ) = star v ⬝ᵥ v := by
    intro v
    simp [dotProduct, Complex.conj_mul']
  apply Complex.ofReal_injective
  rw [key, key, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]

private theorem sph_isCompact (k : ℕ) : IsCompact {w : Fin k → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} := by
  apply (isCompact_closedBall (0 : Fin k → ℂ) 1).of_isClosed_subset
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : ‖w i‖ ^ 2 ≤ 1 := by
      have := Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
      have hw' : ∑ i, ‖w i‖ ^ 2 = 1 := hw
      rw [hw'] at this
      exact this
    nlinarith [norm_nonneg (w i)]

private theorem sph_integrable {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0) {E : Type*} [NormedAddCommGroup E]
    {f : (Fin k → ℂ) → E} (hf : Continuous f) : Integrable f P := by
  have hae : ∀ᵐ w ∂P, w ∈ {w : Fin k → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} := by
    rw [ae_iff]; exact hsph
  have : P.restrict {w : Fin k → ℂ | ∑ i, ‖w i‖ ^ 2 = 1} = P :=
    Measure.restrict_eq_self_of_ae_mem hae
  rw [← this]
  exact hf.continuousOn.integrableOn_compact (sph_isCompact k)

private theorem sph_integral_inv {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (U : Matrix.unitaryGroup (Fin k) ℂ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin k → ℂ) → E} (hg : Continuous g) :
    ∫ w, g ((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) ∂P = ∫ w, g w ∂P := by
  have hm : Measurable (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  conv_rhs => rw [← hinv U]
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]

private theorem sph_exists_diag {k : ℕ} (i : Fin k) (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin k) ℂ, ∀ w : Fin k → ℂ,
      (U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w = Function.update w i (z * w i) := by
  classical
  have hzz : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  refine ⟨⟨Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) i z), ?_⟩, fun w => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = i
      · subst ha; simp [hzz]
      · simp [Function.update_of_ne ha]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  · ext l
    simp only [Matrix.mulVec_diagonal]
    by_cases hl : l = i
    · subst hl; simp
    · simp [Function.update_of_ne hl]

private theorem sph_exists_householder {k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    ∃ U : Matrix.unitaryGroup (Fin k) ℂ, ∀ w : Fin k → ℂ,
      ((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i = (7 / 25 : ℂ) * w i - (24 / 25 : ℂ) * w j ∧
      ((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j = -(24 / 25 : ℂ) * w i - (7 / 25 : ℂ) * w j := by
  classical
  set v : Fin k → ℂ := Pi.single i (3 / 5 : ℂ) + Pi.single j (4 / 5 : ℂ) with hv
  have hvi : v i = 3 / 5 := by simp [hv, hij.symm]
  have hvj : v j = 4 / 5 := by simp [hv, hij]
  have hvl : ∀ l, l ≠ i → l ≠ j → v l = 0 := by
    intro l h1 h2; simp [hv, h1, h2]
  have hsv : star v = v := by
    ext l
    by_cases h1 : l = i
    · subst h1; simp [hvi]
    · by_cases h2 : l = j
      · subst h2; simp [hvj]
      · simp [hvl l h1 h2]
  have hnorm : star v ⬝ᵥ v = 1 := by
    rw [hsv, dotProduct, Fintype.sum_eq_add i j hij (fun l hl => by simp [hvl l hl.1 hl.2]), hvi, hvj]
    norm_num
  set P : Matrix (Fin k) (Fin k) ℂ := Matrix.vecMulVec v (star v) with hP
  have hPP : P * P = P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec, hnorm, one_smul]
  set M : Matrix (Fin k) (Fin k) ℂ := 1 - (2 : ℂ) • P with hM
  have hMstar : star M = M := by
    ext a b
    have h1 : (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 := by simp [eq_comm]
    simp only [hM, hP, Matrix.star_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, star_sub, star_mul', smul_eq_mul, Pi.star_apply, star_star]
    simp [h1, mul_comm]
  have hdot : ∀ w : Fin k → ℂ, star v ⬝ᵥ w = 3 / 5 * w i + 4 / 5 * w j := by
    intro w
    rw [dotProduct, Fintype.sum_eq_add i j hij (fun l hl => by simp [hvl l hl.1 hl.2])]
    simp [hvi, hvj]
  have hMw : ∀ w : Fin k → ℂ, ∀ l, (M *ᵥ w) l = w l - 2 * (v l * (3 / 5 * w i + 4 / 5 * w j)) := by
    intro w l
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, hP, Matrix.vecMulVec_mulVec, hdot]
    simp only [Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      smul_eq_mul, Matrix.one_mulVec]
  refine ⟨⟨M, ?_⟩, fun w => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, hMstar]
    have : M * M = 1 - (4 : ℂ) • P + (4 : ℂ) • (P * P) := by
      simp only [hM, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
        smul_smul]
      module
    rw [this, hPP]; module
  · show (M *ᵥ w) i = _ ∧ (M *ᵥ w) j = _
    rw [hMw, hMw, hvi, hvj]
    constructor <;> ring

private theorem sph_diag_integral {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (j : Fin k) (z : ℂ) (hz : ‖z‖ = 1) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin k → ℂ) → E} (hg : Continuous g) :
    ∫ w, g (Function.update w j (z * w j)) ∂P = ∫ w, g w ∂P := by
  obtain ⟨U, hU⟩ := sph_exists_diag j z hz
  have := sph_integral_inv hinv U hg
  simp_rw [hU] at this
  exact this

private theorem sph_phase_vanish {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i : Fin k) (m n : ℕ) (hmn : m ≠ n) (g : (Fin k → ℂ) → ℂ) (hg : Continuous g)
    (hphase : ∀ z : ℂ, ‖z‖ = 1 → ∀ w,
      g (Function.update w i (z * w i)) = z ^ m * (starRingEnd ℂ z) ^ n * g w) :
    ∫ w, g w ∂P = 0 := by
  set d : ℝ := (m : ℝ) - n with hd
  have hd0 : d ≠ 0 := by
    intro h; apply hmn; have : (m : ℝ) = n := by linarith
    exact_mod_cast this
  set z : ℂ := Complex.exp (((Real.pi / d : ℝ) : ℂ) * Complex.I) with hz
  have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hzm : z ^ m * (starRingEnd ℂ z) ^ n = -1 := by
    rw [hz, ← Complex.exp_nat_mul, ← Complex.exp_conj, ← Complex.exp_nat_mul,
      ← Complex.exp_add]
    have : (m : ℂ) * (((Real.pi / d : ℝ) : ℂ) * Complex.I) +
        (n : ℂ) * (starRingEnd ℂ) (((Real.pi / d : ℝ) : ℂ) * Complex.I) =
        (((Real.pi / d * ((m : ℝ) - n) : ℝ)) : ℂ) * Complex.I := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [this, show Real.pi / d * ((m : ℝ) - n) = Real.pi by rw [← hd]; field_simp,
      Complex.exp_pi_mul_I]
  have h1 := sph_diag_integral hinv i z hz1 hg
  simp_rw [hphase z hz1, hzm, neg_one_mul, integral_neg] at h1
  have h2 : (2 : ℂ) * ∫ w, g w ∂P = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Classical fact `uniform-complex-sphere-moments` (a), unbalanced moments vanish. -/
theorem ext_sphere_unbalanced_moment_zero (k : ℕ) (P : MeasureTheory.Measure (Fin k → ℂ))
    (hP : MeasureTheory.IsProbabilityMeasure P) (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (a b : Fin k → ℕ) (hab : a ≠ b) :
    ∫ w, ∏ i, (w i) ^ (a i) * (starRingEnd ℂ (w i)) ^ (b i) ∂P = 0 := by
  classical
  have _ := hP
  have _ := hsph
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
  refine sph_phase_vanish hinv i (a i) (b i) hi _ (by fun_prop) ?_
  intro z hz w
  have hprod : ∀ w' : Fin k → ℂ, ∏ l, (w' l) ^ (a l) * (starRingEnd ℂ (w' l)) ^ (b l) =
      ((w' i) ^ (a i) * (starRingEnd ℂ (w' i)) ^ (b i)) *
        ∏ l ∈ Finset.univ.erase i, (w' l) ^ (a l) * (starRingEnd ℂ (w' l)) ^ (b l) := by
    intro w'
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [hprod, hprod w]
  have : ∏ l ∈ Finset.univ.erase i, (Function.update w i (z * w i) l) ^ (a l) *
      (starRingEnd ℂ (Function.update w i (z * w i) l)) ^ (b l) =
      ∏ l ∈ Finset.univ.erase i, (w l) ^ (a l) * (starRingEnd ℂ (w l)) ^ (b l) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this]
  simp only [Function.update_self, mul_pow, map_mul]
  ring

private theorem sph_int_lin3 {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0) {f₁ f₂ f₃ : (Fin k → ℂ) → ℝ}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) (c₁ c₂ c₃ : ℝ) :
    ∫ w, (c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w) ∂P =
      c₁ * ∫ w, f₁ w ∂P + c₂ * ∫ w, f₂ w ∂P + c₃ * ∫ w, f₃ w ∂P := by
  have i₁ := (sph_integrable hP hsph h₁).const_mul c₁
  have i₂ := (sph_integrable hP hsph h₂).const_mul c₂
  have i₃ := (sph_integrable hP hsph h₃).const_mul c₃
  have hA : Integrable (fun w => c₁ * f₁ w + c₂ * f₂ w) P := i₁.add i₂
  rw [integral_add hA i₃, integral_add i₁ i₂, integral_const_mul, integral_const_mul,
    integral_const_mul]

private theorem sph_int_lin4 {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0) {f₁ f₂ f₃ f₄ : (Fin k → ℂ) → ℝ}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄)
    (c₁ c₂ c₃ c₄ : ℝ) :
    ∫ w, (c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w + c₄ * f₄ w) ∂P =
      c₁ * ∫ w, f₁ w ∂P + c₂ * ∫ w, f₂ w ∂P + c₃ * ∫ w, f₃ w ∂P + c₄ * ∫ w, f₄ w ∂P := by
  have i₁ := (sph_integrable hP hsph h₁).const_mul c₁
  have i₂ := (sph_integrable hP hsph h₂).const_mul c₂
  have i₃ := (sph_integrable hP hsph h₃).const_mul c₃
  have i₄ := (sph_integrable hP hsph h₄).const_mul c₄
  have hA : Integrable (fun w => c₁ * f₁ w + c₂ * f₂ w) P := i₁.add i₂
  have hB : Integrable (fun w => c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w) P := hA.add i₃
  rw [integral_add hB i₄, integral_add hA i₃, integral_add i₁ i₂,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- A function odd under `w_j ↦ -w_j` integrates to zero. -/
private theorem sph_odd_vanish {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (j : Fin k) {F : (Fin k → ℂ) → ℝ} (hF : Continuous F)
    (hodd : ∀ w, F (Function.update w j (-w j)) = -F w) : ∫ w, F w ∂P = 0 := by
  have h1 := sph_diag_integral hinv j (-1) (by simp) hF
  simp_rw [neg_one_mul, hodd, integral_neg] at h1
  linarith

/-- Norm of the first Householder coordinate. -/
private theorem sph_norm_sq_i (x y : ℂ) :
    ‖(7 / 25 : ℂ) * x - (24 / 25 : ℂ) * y‖ ^ 2 =
      (49 / 625) * ‖x‖ ^ 2 + (576 / 625) * ‖y‖ ^ 2 - (336 / 625) * (x * starRingEnd ℂ y).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  norm_num
  ring

private theorem sph_norm_sq_j (x y : ℂ) :
    ‖-(24 / 25 : ℂ) * x - (7 / 25 : ℂ) * y‖ ^ 2 =
      (576 / 625) * ‖x‖ ^ 2 + (49 / 625) * ‖y‖ ^ 2 + (336 / 625) * (x * starRingEnd ℂ y).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im]
  norm_num
  ring

private theorem sph_cross_zero {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) (hij : i ≠ j) : ∫ w, (w i * starRingEnd ℂ (w j)).re ∂P = 0 := by
  refine sph_odd_vanish hinv j (by fun_prop) fun w => ?_
  simp [Function.update_of_ne hij]

private theorem sph_cross_zero' {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) (hij : i ≠ j) :
    ∫ w, (‖w i‖ ^ 2 - ‖w j‖ ^ 2) * (w i * starRingEnd ℂ (w j)).re ∂P = 0 := by
  refine sph_odd_vanish hinv j (by fun_prop) fun w => ?_
  simp [Function.update_of_ne hij]
  ring

private theorem sph_cross_sq {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) (hij : i ≠ j) :
    2 * ∫ w, ((w i * starRingEnd ℂ (w j)).re) ^ 2 ∂P = ∫ w, ‖w i‖ ^ 2 * ‖w j‖ ^ 2 ∂P := by
  have h1 := sph_diag_integral hinv j Complex.I (by simp)
    (g := fun w => ((w i * starRingEnd ℂ (w j)).re) ^ 2) (by fun_prop)
  have h2 : ∀ w : Fin k → ℂ,
      ((Function.update w j (Complex.I * w j) i *
        starRingEnd ℂ (Function.update w j (Complex.I * w j) j)).re) ^ 2 =
      ‖w i‖ ^ 2 * ‖w j‖ ^ 2 - ((w i * starRingEnd ℂ (w j)).re) ^ 2 := by
    intro w
    simp only [Function.update_of_ne hij, Function.update_self, map_mul, Complex.conj_I]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im]
    ring
  simp_rw [h2] at h1
  have h3 := sph_int_lin3 hP hsph (f₁ := fun w => ‖w i‖ ^ 2 * ‖w j‖ ^ 2)
    (f₂ := fun w => ((w i * starRingEnd ℂ (w j)).re) ^ 2) (f₃ := fun _ => 0)
    (by fun_prop) (by fun_prop) (by fun_prop) 1 (-1) 0
  simp only [one_mul, neg_one_mul, add_zero, integral_zero, mul_zero] at h3
  simp only [← sub_eq_add_neg] at h3
  linarith

private theorem sph_sym2 {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) : ∫ w, ‖w i‖ ^ 2 ∂P = ∫ w, ‖w j‖ ^ 2 ∂P := by
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨U, hU⟩ := sph_exists_householder i j hij
  have h1 := sph_integral_inv hinv U (g := fun w => ‖w i‖ ^ 2) (by fun_prop)
  have h2 : ∀ w : Fin k → ℂ, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 =
      (49 / 625) * ‖w i‖ ^ 2 + (576 / 625) * ‖w j‖ ^ 2 +
        (-(336 / 625)) * (w i * starRingEnd ℂ (w j)).re := by
    intro w
    rw [(hU w).1, sph_norm_sq_i]; ring
  simp_rw [h2] at h1
  rw [sph_int_lin3 hP hsph (by fun_prop) (by fun_prop) (by fun_prop), sph_cross_zero hinv i j hij]
    at h1
  linarith

/-- The fourth-moment relation `E|w_i|⁴ + E|w_j|⁴ = 4 E|w_i|²|w_j|²`. -/
private theorem sph_fourth_rel {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) (hij : i ≠ j) :
    ∫ w, ‖w i‖ ^ 2 * ‖w i‖ ^ 2 ∂P + ∫ w, ‖w j‖ ^ 2 * ‖w j‖ ^ 2 ∂P =
      4 * ∫ w, ‖w i‖ ^ 2 * ‖w j‖ ^ 2 ∂P := by
  obtain ⟨U, hU⟩ := sph_exists_householder i j hij
  have h1 := sph_integral_inv hinv U
    (g := fun w => ‖w i‖ ^ 2 * ‖w i‖ ^ 2 + ‖w j‖ ^ 2 * ‖w j‖ ^ 2) (by fun_prop)
  have e1 : ∀ w : Fin k → ℂ, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 *
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 =
      (49 / 625) ^ 2 * (‖w i‖ ^ 2 * ‖w i‖ ^ 2) + (576 / 625) ^ 2 * (‖w j‖ ^ 2 * ‖w j‖ ^ 2) +
      (336 / 625) ^ 2 * ((w i * starRingEnd ℂ (w j)).re) ^ 2 +
      (2 * (49 / 625) * (576 / 625)) * (‖w i‖ ^ 2 * ‖w j‖ ^ 2) +
      (-2 * (49 / 625) * (336 / 625)) * (‖w i‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) +
      (-2 * (576 / 625) * (336 / 625)) * (‖w j‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) := by
    intro w
    rw [(hU w).1, sph_norm_sq_i]; ring
  have e2 : ∀ w : Fin k → ℂ, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j‖ ^ 2 *
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j‖ ^ 2 =
      (576 / 625) ^ 2 * (‖w i‖ ^ 2 * ‖w i‖ ^ 2) + (49 / 625) ^ 2 * (‖w j‖ ^ 2 * ‖w j‖ ^ 2) +
      (336 / 625) ^ 2 * ((w i * starRingEnd ℂ (w j)).re) ^ 2 +
      (2 * (49 / 625) * (576 / 625)) * (‖w i‖ ^ 2 * ‖w j‖ ^ 2) +
      (2 * (576 / 625) * (336 / 625)) * (‖w i‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) +
      (2 * (49 / 625) * (336 / 625)) * (‖w j‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) := by
    intro w
    rw [(hU w).2, sph_norm_sq_j]; ring
  have e : ∀ w : Fin k → ℂ, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 *
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 +
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j‖ ^ 2 *
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j‖ ^ 2 =
      ((49 / 625) ^ 2 + (576 / 625) ^ 2) * (‖w i‖ ^ 2 * ‖w i‖ ^ 2 + ‖w j‖ ^ 2 * ‖w j‖ ^ 2) +
      (2 * (336 / 625) ^ 2) * ((w i * starRingEnd ℂ (w j)).re) ^ 2 +
      (4 * (49 / 625) * (576 / 625)) * (‖w i‖ ^ 2 * ‖w j‖ ^ 2) +
      (2 * (336 / 625) * (576 / 625 - 49 / 625)) *
        ((‖w i‖ ^ 2 - ‖w j‖ ^ 2) * (w i * starRingEnd ℂ (w j)).re) := by
    intro w
    have h1 := e1 w
    have h2 := e2 w
    linear_combination h1 + h2
  simp_rw [e] at h1
  rw [sph_int_lin4 hP hsph (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop),
    sph_cross_zero' hinv i j hij,
    integral_add (sph_integrable hP hsph (by fun_prop)) (sph_integrable hP hsph (by fun_prop))]
    at h1
  have hc := sph_cross_sq hP hsph hinv i j hij
  linarith

private theorem sph_ae {k : ℕ} {P : Measure (Fin k → ℂ)}
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0) : ∀ᵐ w ∂P, ∑ i, ‖w i‖ ^ 2 = 1 := by
  rw [ae_iff]; exact hsph

/-- Classical fact `uniform-complex-sphere-moments` (b): `E|w_i|² = 1/k`. -/
theorem ext_sphere_second_moment (k : ℕ) (hk : 1 ≤ k) (P : MeasureTheory.Measure (Fin k → ℂ))
    (hP : MeasureTheory.IsProbabilityMeasure P) (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P) (i : Fin k) :
    ∫ w, ‖w i‖ ^ 2 ∂P = 1 / (k : ℝ) := by
  have hsum : ∑ l, ∫ w, ‖w l‖ ^ 2 ∂P = 1 := by
    rw [← integral_finsetSum _ (fun l _ => sph_integrable hP hsph (by fun_prop))]
    rw [integral_congr_ae (sph_ae hsph)]
    simp
  simp only [fun l => sph_sym2 hP hsph hinv l i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact this.ne'
  field_simp
  linarith

/-- Classical fact `uniform-complex-sphere-moments` (b): `E|w_i|²|w_j|² ≥ c_k > 0` for all `i, j`.
Here `c_k = 1/(2k²)`; the sharp value `1/(k(k+1))` is not needed. -/
theorem ext_sphere_fourth_moment_lower (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : MeasureTheory.Measure (Fin k → ℂ),
      MeasureTheory.IsProbabilityMeasure P → P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 →
      (∀ U : Matrix.unitaryGroup (Fin k) ℂ,
        P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P) →
      ∀ i j : Fin k, c ≤ ∫ w, ‖w i‖ ^ 2 * ‖w j‖ ^ 2 ∂P := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨1 / (2 * (k : ℝ) ^ 2), by positivity, ?_⟩
  intro P hP hsph hinv i j
  have hjen : ∀ l, 1 / (k : ℝ) ^ 2 ≤ ∫ w, ‖w l‖ ^ 2 * ‖w l‖ ^ 2 ∂P := by
    intro l
    have h2 := ext_sphere_second_moment k hk P hP hsph hinv l
    have hnn : 0 ≤ ∫ w, (‖w l‖ ^ 2 - 1 / (k : ℝ)) ^ 2 ∂P :=
      integral_nonneg (fun w => sq_nonneg _)
    have hpt : ∀ w : Fin k → ℂ, (‖w l‖ ^ 2 - 1 / (k : ℝ)) ^ 2 =
        1 * (‖w l‖ ^ 2 * ‖w l‖ ^ 2) + (-2 / (k : ℝ)) * ‖w l‖ ^ 2 + (1 / (k : ℝ)) ^ 2 * 1 := by
      intro w; ring
    simp_rw [hpt] at hnn
    rw [sph_int_lin3 hP hsph (f₃ := fun _ => (1 : ℝ)) (by fun_prop) (by fun_prop)
      (by fun_prop), h2] at hnn
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] at hnn
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have : 1 / (k : ℝ) ^ 2 = (1 / (k : ℝ)) ^ 2 := by ring
    rw [this]
    have e : -2 / (k : ℝ) * (1 / (k : ℝ)) = -2 * (1 / (k : ℝ)) ^ 2 := by ring
    rw [e] at hnn
    linarith
  by_cases hij : i = j
  · subst hij
    have := hjen i
    have h3 : 1 / (2 * (k : ℝ) ^ 2) ≤ 1 / (k : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [sq_nonneg (k : ℝ)]
    linarith
  · have := sph_fourth_rel hP hsph hinv i j hij
    have hi := hjen i
    have hj := hjen j
    have e : 1 / (2 * (k : ℝ) ^ 2) = (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) ^ 2) / 4 := by
      field_simp; ring
    rw [e]
    linarith



private theorem sph_transitive {k : ℕ} (i₀ : Fin k) (w : Fin k → ℂ)
    (hw : ∑ i, ‖w i‖ ^ 2 = 1) :
    ∃ V : Matrix.unitaryGroup (Fin k) ℂ,
      (V : Matrix (Fin k) (Fin k) ℂ) *ᵥ (Pi.single i₀ (1 : ℂ)) = w := by
  classical
  set v : EuclideanSpace ℂ (Fin k) := WithLp.toLp 2 w with hv
  have hnorm : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [hv, hw]
  have hon : Orthonormal ℂ (({i₀} : Set (Fin k)).domRestrict (fun _ => v)) := by
    refine ⟨fun i => hnorm, fun i j hij => ?_⟩
    exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
      (Set.mem_singleton_iff.1 j.2).symm)) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨⟨(EuclideanSpace.basisFun (Fin k) ℂ).toBasis.toMatrix b,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _⟩, ?_⟩
  ext i
  rw [show ((⟨_, _⟩ : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) = _ from rfl,
    Matrix.mulVec_single_one]
  have := hb i₀ (Set.mem_singleton _)
  simp [Module.Basis.toMatrix_apply, this, hv]

private theorem sph_entry_le {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ) (i j : Fin k) :
    ‖(U : Matrix (Fin k) (Fin k) ℂ) i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 U.2) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∑ l, ‖(U : Matrix (Fin k) (Fin k) ℂ) i l‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Complex.mul_conj']
  have h3 : ‖(U : Matrix (Fin k) (Fin k) ℂ) i j‖ ^ 2 ≤ 1 := by
    have := Finset.single_le_sum (f := fun l => ‖(U : Matrix (Fin k) (Fin k) ℂ) i l‖ ^ 2)
      (fun l _ => by positivity) (Finset.mem_univ j)
    beta_reduce at this
    linarith
  nlinarith [norm_nonneg ((U : Matrix (Fin k) (Fin k) ℂ) i j)]

local instance sph_secondCountable (k : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology
    {x : Fin k → Fin k → ℂ // x ∈ (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ))})

local instance sph_compact (k : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin k) ℂ) := by
  have hcl : IsClosed (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) :=
    isClosed_unitary
  have hK : IsCompact (Metric.closedBall (0 : Fin k → Fin k → ℂ) 1) := isCompact_closedBall _ _
  have hc : IsCompact (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
    refine IsCompact.of_isClosed_subset hK hcl ?_
    intro U hU
    let V : Fin k → Fin k → ℂ := U
    have key : ‖V‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      exact sph_entry_le ⟨U, hU⟩ i j
    exact mem_closedBall_zero_iff.2 key
  exact isCompact_iff_compactSpace.1 hc

private theorem sph_exists_haar (k : ℕ) :
    ∃ h : Measure (Matrix.unitaryGroup (Fin k) ℂ), IsProbabilityMeasure h ∧ h.IsMulLeftInvariant := by
  refine ⟨Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts _), ⟨?_⟩, inferInstance⟩
  have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts
    (Matrix.unitaryGroup (Fin k) ℂ)))
  simpa using this



private theorem sph_single_sumsq {k : ℕ} (i₀ : Fin k) :
    ∑ i, ‖(Pi.single i₀ (1 : ℂ) : Fin k → ℂ) i‖ ^ 2 = 1 := by
  classical
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Classical fact `uniform-complex-sphere-moments` (a), existence: a probability measure on the
unit sphere of `ℂ^k` invariant under all unitary maps (hence under multiplying any single
coordinate by a unit complex number, in particular by `-1`). It is the uniform measure. -/
theorem ext_sphere_measure_exists (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : MeasureTheory.Measure (Fin k → ℂ), MeasureTheory.IsProbabilityMeasure P ∧
      P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0 ∧
      ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
        P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P := by
  classical
  obtain ⟨h, hprob, hinv⟩ := sph_exists_haar k
  let i₀ : Fin k := ⟨0, hk⟩
  let o : Matrix.unitaryGroup (Fin k) ℂ → (Fin k → ℂ) :=
    fun U => (U : Matrix (Fin k) (Fin k) ℂ) *ᵥ Pi.single i₀ (1 : ℂ)
  have ho : Continuous o :=
    Continuous.matrix_mulVec continuous_subtype_val continuous_const
  have hom : Measurable o := ho.measurable
  have hS : MeasurableSet {w : Fin k → ℂ | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet.compl
  have := hprob
  refine ⟨h.map o, inferInstance, ?_, ?_⟩
  · rw [Measure.map_apply hom hS]
    have : o ⁻¹' {w : Fin k → ℂ | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = ∅ := by
      ext U
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, o, Set.mem_empty_iff_false,
        iff_false, not_not]
      rw [sph_sumsq_mulVec, sph_single_sumsq]
    rw [this]; simp
  · intro V
    have hV : Measurable (Matrix.mulVec (V : Matrix (Fin k) (Fin k) ℂ)) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    rw [Measure.map_map hV hom]
    have : (Matrix.mulVec (V : Matrix (Fin k) (Fin k) ℂ)) ∘ o = o ∘ (fun U => V * U) := by
      funext U
      simp only [Function.comp_apply, o]
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [this, ← Measure.map_map hom (measurable_const_mul V)]
    have := hinv
    rw [map_mul_left_eq_self]

/-- Averaging identity: an invariant sphere probability measure integrates a bounded continuous
function to its Haar average along the orbit of a fixed point. -/
private theorem sph_integral_haar {k : ℕ} (i₀ : Fin k) {P : Measure (Fin k → ℂ)}
    (hP : IsProbabilityMeasure P) (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (h : Measure (Matrix.unitaryGroup (Fin k) ℂ)) (hprob : IsProbabilityMeasure h)
    (hhinv : h.IsMulLeftInvariant) (f : (Fin k → ℂ) →ᵇ ℝ) :
    ∫ w, f w ∂P = ∫ U, f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *ᵥ
      Pi.single i₀ (1 : ℂ)) ∂h := by
  classical
  have hF : Continuous (Function.uncurry fun (U : Matrix.unitaryGroup (Fin k) ℂ) (w : Fin k → ℂ) =>
      f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *ᵥ w)) :=
    f.continuous.comp (Continuous.matrix_mulVec
      (continuous_subtype_val.comp (continuous_inv.comp continuous_fst)) continuous_snd)
  have hint : Integrable (Function.uncurry fun (U : Matrix.unitaryGroup (Fin k) ℂ)
      (w : Fin k → ℂ) => f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) :
        Matrix (Fin k) (Fin k) ℂ) *ᵥ w)) (h.prod P) :=
    Integrable.of_bound hF.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have h1 : ∫ w, f w ∂P = ∫ U, ∫ w, f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) :
      Matrix (Fin k) (Fin k) ℂ) *ᵥ w) ∂P ∂h := by
    have : ∀ U : Matrix.unitaryGroup (Fin k) ℂ, ∫ w, f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) :
        Matrix (Fin k) (Fin k) ℂ) *ᵥ w) ∂P = ∫ w, f w ∂P :=
      fun U => sph_integral_inv hinv U⁻¹ f.continuous
    simp_rw [this]
    simp
  rw [h1, integral_integral_swap hint]
  have h2 : ∀ w : Fin k → ℂ, ∑ i, ‖w i‖ ^ 2 = 1 →
      ∫ U, f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) ∂h =
      ∫ U, f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *ᵥ
        Pi.single i₀ (1 : ℂ)) ∂h := by
    intro w hw
    obtain ⟨V, hV⟩ := sph_transitive i₀ w hw
    rw [← hV]
    have := integral_mul_left_eq_self (μ := h) (fun U : Matrix.unitaryGroup (Fin k) ℂ =>
      f (((U⁻¹ : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *ᵥ
        Pi.single i₀ (1 : ℂ))) V⁻¹
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [mul_inv_rev, inv_inv]
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [integral_congr_ae ((sph_ae hsph).mono fun w hw => h2 w hw)]
  simp

/-- Certificate for the classical fact `uniform-complex-sphere-moments`: the uniform measure
on the unit sphere of `ℂ^k` is the unique `U(k)`-invariant probability measure on it. Any two
probability measures on `{∑ ‖wᵢ‖² = 1}` invariant under all unitary maps coincide
(`U(k)` acts transitively on the sphere; the proof averages over Haar measure on `U(k)`). -/
theorem ext_sphere_measure_unique (k : ℕ) (P Q : MeasureTheory.Measure (Fin k → ℂ))
    (hP : MeasureTheory.IsProbabilityMeasure P) (hsphP : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinvP : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (hQ : MeasureTheory.IsProbabilityMeasure Q) (hsphQ : Q {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinvQ : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      Q.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = Q) :
    P = Q := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exfalso
    have : {w : Fin 0 → ℂ | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = Set.univ := by
      ext w; simp
    rw [this] at hsphP
    simp at hsphP
  · obtain ⟨h, hprob, hhinv⟩ := sph_exists_haar k
    let i₀ : Fin k := ⟨0, hk⟩
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [sph_integral_haar i₀ hP hsphP hinvP h hprob hhinv f,
      sph_integral_haar i₀ hQ hsphQ hinvQ h hprob hhinv f]

private theorem sph_int_lin6 {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0) {f₁ f₂ f₃ f₄ f₅ f₆ : (Fin k → ℂ) → ℝ}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄)
    (h₅ : Continuous f₅) (h₆ : Continuous f₆) (c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) :
    ∫ w, (c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w + c₄ * f₄ w + c₅ * f₅ w + c₆ * f₆ w) ∂P =
      c₁ * ∫ w, f₁ w ∂P + c₂ * ∫ w, f₂ w ∂P + c₃ * ∫ w, f₃ w ∂P + c₄ * ∫ w, f₄ w ∂P +
        c₅ * ∫ w, f₅ w ∂P + c₆ * ∫ w, f₆ w ∂P := by
  have i₁ := (sph_integrable hP hsph h₁).const_mul c₁
  have i₂ := (sph_integrable hP hsph h₂).const_mul c₂
  have i₃ := (sph_integrable hP hsph h₃).const_mul c₃
  have i₄ := (sph_integrable hP hsph h₄).const_mul c₄
  have i₅ := (sph_integrable hP hsph h₅).const_mul c₅
  have i₆ := (sph_integrable hP hsph h₆).const_mul c₆
  have hA : Integrable (fun w => c₁ * f₁ w + c₂ * f₂ w) P := i₁.add i₂
  have hB : Integrable (fun w => c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w) P := hA.add i₃
  have hC : Integrable
      (fun w => c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w + c₄ * f₄ w) P := hB.add i₄
  have hD : Integrable
      (fun w => c₁ * f₁ w + c₂ * f₂ w + c₃ * f₃ w + c₄ * f₄ w + c₅ * f₅ w) P := hC.add i₅
  rw [integral_add hD i₆, integral_add hC i₅, integral_add hB i₄, integral_add hA i₃,
    integral_add i₁ i₂, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- The two diagonal fourth moments `E|w_i|⁴` and `E|w_j|⁴` agree. -/
private theorem sph_diag_eq {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) (hij : i ≠ j) :
    ∫ w, ‖w i‖ ^ 2 * ‖w i‖ ^ 2 ∂P = ∫ w, ‖w j‖ ^ 2 * ‖w j‖ ^ 2 ∂P := by
  obtain ⟨U, hU⟩ := sph_exists_householder i j hij
  have e1 : ∀ w : Fin k → ℂ, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 *
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) i‖ ^ 2 =
      (49 / 625) ^ 2 * (‖w i‖ ^ 2 * ‖w i‖ ^ 2) + (576 / 625) ^ 2 * (‖w j‖ ^ 2 * ‖w j‖ ^ 2) +
      (336 / 625) ^ 2 * ((w i * starRingEnd ℂ (w j)).re) ^ 2 +
      (2 * (49 / 625) * (576 / 625)) * (‖w i‖ ^ 2 * ‖w j‖ ^ 2) +
      (-2 * (49 / 625) * (336 / 625)) * (‖w i‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) +
      (-2 * (576 / 625) * (336 / 625)) * (‖w j‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) := by
    intro w
    rw [(hU w).1, sph_norm_sq_i]; ring
  have e2 : ∀ w : Fin k → ℂ, ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j‖ ^ 2 *
      ‖((U : Matrix (Fin k) (Fin k) ℂ) *ᵥ w) j‖ ^ 2 =
      (576 / 625) ^ 2 * (‖w i‖ ^ 2 * ‖w i‖ ^ 2) + (49 / 625) ^ 2 * (‖w j‖ ^ 2 * ‖w j‖ ^ 2) +
      (336 / 625) ^ 2 * ((w i * starRingEnd ℂ (w j)).re) ^ 2 +
      (2 * (49 / 625) * (576 / 625)) * (‖w i‖ ^ 2 * ‖w j‖ ^ 2) +
      (2 * (576 / 625) * (336 / 625)) * (‖w i‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) +
      (2 * (49 / 625) * (336 / 625)) * (‖w j‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re) := by
    intro w
    rw [(hU w).2, sph_norm_sq_j]; ring
  have hc := sph_cross_sq hP hsph hinv i j hij
  have z1 : ∫ w, ‖w i‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re ∂P = 0 := by
    refine sph_odd_vanish hinv j (by fun_prop) fun w => ?_
    simp [Function.update_of_ne hij]
    ring
  have z2 : ∫ w, ‖w j‖ ^ 2 * (w i * starRingEnd ℂ (w j)).re ∂P = 0 := by
    refine sph_odd_vanish hinv j (by fun_prop) fun w => ?_
    simp [Function.update_of_ne hij]
    ring
  have h1 := sph_integral_inv hinv U (g := fun w => ‖w i‖ ^ 2 * ‖w i‖ ^ 2) (by fun_prop)
  have h2 := sph_integral_inv hinv U (g := fun w => ‖w j‖ ^ 2 * ‖w j‖ ^ 2) (by fun_prop)
  simp_rw [e1] at h1
  simp_rw [e2] at h2
  rw [sph_int_lin6 hP hsph (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop), z1, z2] at h1 h2
  have key : (1 - (49 / 625) ^ 2 + (576 / 625) ^ 2) *
      (∫ w, ‖w i‖ ^ 2 * ‖w i‖ ^ 2 ∂P - ∫ w, ‖w j‖ ^ 2 * ‖w j‖ ^ 2 ∂P) = 0 := by
    linarith
  rcases mul_eq_zero.1 key with h | h
  · norm_num at h
  · linarith

/-- For `i ≠ j`: `E|w_i|⁴ = 2 E|w_i|²|w_j|²`. -/
private theorem sph_diag_offdiag {k : ℕ} {P : Measure (Fin k → ℂ)} (hP : IsProbabilityMeasure P)
    (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P)
    (i j : Fin k) (hij : i ≠ j) :
    ∫ w, ‖w i‖ ^ 2 * ‖w j‖ ^ 2 ∂P = (∫ w, ‖w i‖ ^ 2 * ‖w i‖ ^ 2 ∂P) / 2 := by
  have h1 := sph_fourth_rel hP hsph hinv i j hij
  have h2 := sph_diag_eq hP hsph hinv i j hij
  linarith

/-- Classical fact `uniform-complex-sphere-moments` (b), exact form (the sharp version of
`ext_sphere_fourth_moment_lower`): for every unitarily invariant probability measure on the unit sphere
of `ℂ^k`, `𝔼|w_i|²|w_j|² = 1/(k(k+1))` for `i ≠ j` and `𝔼|w_i|⁴ = 2/(k(k+1))`. -/
theorem ext_sphere_fourth_moment_exact (k : ℕ) (hk : 1 ≤ k) (P : MeasureTheory.Measure (Fin k → ℂ))
    (hP : MeasureTheory.IsProbabilityMeasure P) (hsph : P {w | ∑ i, ‖w i‖ ^ 2 = 1}ᶜ = 0)
    (hinv : ∀ U : Matrix.unitaryGroup (Fin k) ℂ,
      P.map (Matrix.mulVec (U : Matrix (Fin k) (Fin k) ℂ)) = P) (i j : Fin k) :
    ∫ w, ‖w i‖ ^ 2 * ‖w j‖ ^ 2 ∂P = (if i = j then 2 else 1) / ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set l0 : Fin k := ⟨0, hk⟩ with hl0
  set d : ℝ := ∫ w, ‖w l0‖ ^ 2 * ‖w l0‖ ^ 2 ∂P with hd
  have hD : ∀ l, ∫ w, ‖w l‖ ^ 2 * ‖w l‖ ^ 2 ∂P = d := by
    intro l
    by_cases h : l = l0
    · rw [h]
    · exact sph_diag_eq hP hsph hinv l l0 h
  have hX : ∀ l m, l ≠ m → ∫ w, ‖w l‖ ^ 2 * ‖w m‖ ^ 2 ∂P = d / 2 := by
    intro l m h
    rw [sph_diag_offdiag hP hsph hinv l m h, hD l]
  have hall : ∀ l m, ∫ w, ‖w l‖ ^ 2 * ‖w m‖ ^ 2 ∂P = (if l = m then d / 2 else 0) + d / 2 := by
    intro l m
    by_cases h : l = m
    · subst h; rw [hD l]; simp
    · rw [hX l m h]; simp [h]
  have hsum : ∑ l, ∑ m, ∫ w, ‖w l‖ ^ 2 * ‖w m‖ ^ 2 ∂P = 1 := by
    have e : ∀ w : Fin k → ℂ, (∑ l, ‖w l‖ ^ 2) ^ 2 = ∑ l, ∑ m, ‖w l‖ ^ 2 * ‖w m‖ ^ 2 := by
      intro w; rw [sq, Finset.sum_mul_sum]
    have h1 : ∫ w, (∑ l, ‖w l‖ ^ 2) ^ 2 ∂P = 1 := by
      have h0 : ∫ w, (∑ l, ‖w l‖ ^ 2) ^ 2 ∂P = ∫ _w, (1 : ℝ) ∂P :=
        integral_congr_ae ((sph_ae hsph).mono fun w hw => by simp [hw])
      rw [h0]
      simp
    simp_rw [e] at h1
    rw [integral_finsetSum _ (fun l _ => sph_integrable hP hsph (by fun_prop))] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ (fun m _ => sph_integrable hP hsph (by fun_prop))]
  simp_rw [hall] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hdval : d = 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    field_simp
    nlinarith
  by_cases h : i = j
  · subst h
    rw [hD i, hdval]; simp
  · rw [hX i j h, hdval]; simp [h]; field_simp

end ExtSphere

end TrackB
end RestrictedPolynomials
end
