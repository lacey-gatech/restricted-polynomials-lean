module

public import Mathlib.Analysis.Matrix.Spectrum
public import RestrictedPolynomials.TrackB.SwapNorm
public import RestrictedPolynomials.TrackB.Restrict

/-!
# Track B: singular value decomposition for the swap-norm arguments

Source: CSP_6 (arXiv:2411.15133v1 `main.tex`) L404-407 (`def:svd`), L487, L814,
L947-957 (`lemma:svdinf`).
Covers CSP_6 `def:svd`, the classical existence of the SVD, and CSP_6 `lemma:svdinf`.

The inner products are the expectation ones (`uinner u v = 𝔼 u · conj v`). Existence is
obtained from the spectral theorem for the Hermitian matrix `Mᴴ M` (counting inner product) and a
rescaling by `√|S|`, `√|T|`.
-/

@[expose] public section

open Finset
open scoped BigOperators NNRat
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section SVD
variable {S T : Type*} [Fintype S] [Fintype T]

/-- the expectation inner product `⟨u, v⟩ = 𝔼 u · conj v` on `L²(U(S))`. -/
def uinner (u v : S → ℂ) : ℂ := 𝔼 s, u s * star (v s)

/-- `‖M‖₂²` of a matrix, `𝔼_{s,t} |M s t|²`. -/
def matL2sq (M : S → T → ℂ) : ℝ := 𝔼 s, 𝔼 t, ‖M s t‖ ^ 2

/-- CSP_6 `def:svd` (the SVD `M = ∑ᵢ λᵢ gᵢ hᵢ`), for the expectation inner products; the `λᵢ` are the
nonzero singular values in decreasing order and `gᵢ`, `hᵢ` are orthonormal singular vectors. -/
structure IsSVD (M : S → T → ℂ) (r : ℕ) (lam : Fin r → ℝ) (g : Fin r → S → ℂ)
    (h : Fin r → T → ℂ) : Prop where
  pos : ∀ i, 0 < lam i
  antitone : Antitone lam
  orth_g : ∀ i j, uinner (g i) (g j) = if i = j then 1 else 0
  orth_h : ∀ i j, uinner (h i) (h j) = if i = j then 1 else 0
  decomp : ∀ s t, M s t = ∑ i, (lam i : ℂ) * g i s * h i t

/-! ### Helpers for existence -/

/-- `IsSVD` without the ordering requirement. -/
private structure PreSVD (M : S → T → ℂ) (r : ℕ) (lam : Fin r → ℝ) (g : Fin r → S → ℂ)
    (h : Fin r → T → ℂ) : Prop where
  pos : ∀ i, 0 < lam i
  orth_g : ∀ i j, uinner (g i) (g j) = if i = j then 1 else 0
  orth_h : ∀ i j, uinner (h i) (h j) = if i = j then 1 else 0
  decomp : ∀ s t, M s t = ∑ i, (lam i : ℂ) * g i s * h i t

private lemma uinner_eq_sum (u v : S → ℂ) :
    uinner u v = (∑ s, u s * star (v s)) / (Fintype.card S : ℂ) := by
  simp [uinner, Fintype.expect_eq_sum_div_card]

private lemma PreSVD.sort {M : S → T → ℂ} {r : ℕ} {lam : Fin r → ℝ} {g : Fin r → S → ℂ}
    {h : Fin r → T → ℂ} (hM : PreSVD M r lam g h) :
    ∃ (lam' : Fin r → ℝ) (g' : Fin r → S → ℂ) (h' : Fin r → T → ℂ), IsSVD M r lam' g' h' := by
  let σ := Tuple.sort (fun i => - lam i)
  have hmono : Monotone ((fun i => - lam i) ∘ σ) := Tuple.monotone_sort _
  refine ⟨lam ∘ σ, g ∘ σ, h ∘ σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hM.pos _
  · intro i j hij
    have := hmono hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  · intro i j
    simp only [Function.comp_apply]
    rw [hM.orth_g]
    simp [σ.injective.eq_iff]
  · intro i j
    simp only [Function.comp_apply]
    rw [hM.orth_h]
    simp [σ.injective.eq_iff]
  · intro s t
    rw [hM.decomp s t]
    exact (Equiv.sum_comp σ (fun k => (lam k : ℂ) * g k s * h k t)).symm

private lemma preSVD_of_std [Nonempty S] [Nonempty T] {M : S → T → ℂ} {r : ℕ} (σ : Fin r → ℝ)
    (u : Fin r → S → ℂ) (v : Fin r → T → ℂ) (hσ : ∀ i, 0 < σ i)
    (hu : ∀ i j, ∑ s, u i s * star (u j s) = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ t, star (v i t) * v j t = if i = j then 1 else 0)
    (hd : ∀ s t, M s t = ∑ i, (σ i : ℂ) * u i s * star (v i t)) :
    PreSVD M r (fun i => σ i / (Real.sqrt (Fintype.card S) * Real.sqrt (Fintype.card T)))
      (fun i s => (Real.sqrt (Fintype.card S) : ℂ) * u i s)
      (fun i t => (Real.sqrt (Fintype.card T) : ℂ) * star (v i t)) := by
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hc : 0 < Real.sqrt (Fintype.card S) := Real.sqrt_pos.2 hS
  have hd' : 0 < Real.sqrt (Fintype.card T) := Real.sqrt_pos.2 hT
  have hcc : (Real.sqrt (Fintype.card S) : ℂ) * (Real.sqrt (Fintype.card S) : ℂ) =
      (Fintype.card S : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hS.le]; simp
  have hdd : (Real.sqrt (Fintype.card T) : ℂ) * (Real.sqrt (Fintype.card T) : ℂ) =
      (Fintype.card T : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]; simp
  have hSc : (Fintype.card S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hTc : (Fintype.card T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hc0 : (Real.sqrt (Fintype.card S) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd0 : (Real.sqrt (Fintype.card T) : ℂ) ≠ 0 := by exact_mod_cast hd'.ne'
  refine ⟨fun i => div_pos (hσ i) (mul_pos hc hd'), fun i j => ?_, fun i j => ?_, fun s t => ?_⟩
  · rw [uinner_eq_sum]
    have : ∑ s, (Real.sqrt (Fintype.card S) : ℂ) * u i s *
        star ((Real.sqrt (Fintype.card S) : ℂ) * u j s) =
        (Fintype.card S : ℂ) * ∑ s, u i s * star (u j s) := by
      rw [Finset.mul_sum, ← hcc]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    rw [this, hu, mul_div_cancel_left₀ _ hSc]
  · rw [uinner_eq_sum]
    have : ∑ t, (Real.sqrt (Fintype.card T) : ℂ) * star (v i t) *
        star ((Real.sqrt (Fintype.card T) : ℂ) * star (v j t)) =
        (Fintype.card T : ℂ) * ∑ t, star (v i t) * v j t := by
      rw [Finset.mul_sum, ← hdd]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [this, hv, mul_div_cancel_left₀ _ hTc]
  · rw [hd s t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hσc : (σ i : ℂ) ≠ 0 := by exact_mod_cast (hσ i).ne'
    push_cast
    field_simp

/-- The spectral theorem for `Mᴴ M`, in the counting inner product. -/
private lemma svd_std (M : S → T → ℂ) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → S → ℂ) (v : Fin r → T → ℂ),
      (∀ i, 0 < σ i) ∧
      (∀ i j, ∑ s, u i s * star (u j s) = if i = j then 1 else 0) ∧
      (∀ i j, ∑ t, star (v i t) * v j t = if i = j then 1 else 0) ∧
      (∀ s t, M s t = ∑ i, (σ i : ℂ) * u i s * star (v i t)) := by
  classical
  let A : Matrix S T ℂ := M
  let B : Matrix T T ℂ := A.conjTranspose * A
  have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let U := hB.eigenvectorUnitary
  let V : Matrix T T ℂ := (U : Matrix T T ℂ)
  let μ : T → ℝ := hB.eigenvalues
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self U
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self U
  let col : T → T → ℂ := fun k t => V t k
  let w : T → S → ℂ := fun k => A.mulVec (col k)
  have hcol : ∀ k, (col k) = ⇑(hB.eigenvectorBasis k) := fun k => rfl
  have heig : ∀ k t, (B.mulVec (col k)) t = (μ k : ℂ) * col k t := by
    intro k t
    have := congrFun (hB.mulVec_eigenvectorBasis k) t
    rw [← hcol k] at this
    simpa [Complex.real_smul] using this
  have hcolorth : ∀ k l, ∑ t, star (col k t) * col l t = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hVV k) l
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, col] using this
  have hwinner : ∀ k l, ∑ s, star (w k s) * w l s = (μ l : ℂ) * (if k = l then 1 else 0) := by
    intro k l
    have h1 : ∑ s, star (w k s) * w l s = ∑ t, star (col k t) * (B.mulVec (col l)) t := by
      simp only [w, B, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
      rw [Finset.sum_comm (f := fun x x_1 => ∑ i, star (A x i) * star (col k i) * _)]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    rw [h1]
    simp_rw [heig, mul_left_comm _ (μ l : ℂ)]
    rw [← Finset.mul_sum, hcolorth]
  have hμ : ∀ k, μ k = ∑ s, ‖w k s‖ ^ 2 := by
    intro k
    have h := hwinner k k
    simp only [ite_true, mul_one] at h
    have : ((μ k : ℝ) : ℂ) = ((∑ s, ‖w k s‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h]; push_cast
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    exact_mod_cast this
  have hμnn : ∀ k, 0 ≤ μ k := fun k => by rw [hμ]; positivity
  have hw0 : ∀ k, μ k = 0 → ∀ s, w k s = 0 := by
    intro k hk s
    rw [hμ] at hk
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => by positivity)).1 hk s (mem_univ _)
    simpa using this
  let K : Finset T := univ.filter (fun k => μ k ≠ 0)
  let κ : Fin K.card → T := fun i => (K.equivFin.symm i : T)
  have hκinj : Function.Injective κ := fun i j h => K.equivFin.symm.injective (Subtype.ext h)
  have hκK : ∀ i, μ (κ i) ≠ 0 := fun i => (Finset.mem_filter.1 (K.equivFin.symm i).2).2
  have hμpos : ∀ i, 0 < μ (κ i) := fun i => lt_of_le_of_ne (hμnn _) (Ne.symm (hκK i))
  have hsq : ∀ i, ((Real.sqrt (μ (κ i)) : ℝ) : ℂ) * ((Real.sqrt (μ (κ i)) : ℝ) : ℂ) =
      (μ (κ i) : ℂ) := fun i => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμnn _)]
  have hσc : ∀ i, ((Real.sqrt (μ (κ i)) : ℝ) : ℂ) ≠ 0 := fun i => by
    exact_mod_cast (Real.sqrt_pos.2 (hμpos i)).ne'
  refine ⟨K.card, fun i => Real.sqrt (μ (κ i)),
    fun i s => ((Real.sqrt (μ (κ i)) : ℝ) : ℂ)⁻¹ * w (κ i) s, fun i t => col (κ i) t,
    fun i => Real.sqrt_pos.2 (hμpos i), ?_, ?_, ?_⟩
  · intro i j
    have e : ∑ s, ((Real.sqrt (μ (κ i)) : ℝ) : ℂ)⁻¹ * w (κ i) s *
        star (((Real.sqrt (μ (κ j)) : ℝ) : ℂ)⁻¹ * w (κ j) s) =
        ((Real.sqrt (μ (κ i)) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (μ (κ j)) : ℝ) : ℂ)⁻¹ *
          ∑ s, star (w (κ j) s) * w (κ i) s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal]
      ring
    rw [e, hwinner]
    by_cases hij : i = j
    · subst hij
      have : (μ (κ i) : ℂ) ≠ 0 := by exact_mod_cast hκK i
      simp only [ite_true, mul_one]
      rw [← mul_inv, hsq, inv_mul_cancel₀ this]
    · have : ¬ κ j = κ i := fun h => hij (hκinj h).symm
      simp [hij, this]
  · intro i j
    rw [hcolorth]
    simp [hκinj.eq_iff]
  · intro s t
    have hVV'' : ∀ u t, ∑ k, V u k * star (V t k) = if u = t then 1 else 0 := by
      intro u t
      have := congrFun (congrFun hVV' u) t
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this
    have hsum : M s t = ∑ k, w k s * star (col k t) := by
      have : ∑ k, w k s * star (col k t) = ∑ u, A s u * ∑ k, V u k * star (V t k) := by
        simp only [w, Matrix.mulVec, dotProduct, col, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [this]
      simp only [hVV'', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
      rfl
    have h1 : ∑ k, w k s * star (col k t) = ∑ k ∈ K, w k s * star (col k t) :=
      (Finset.sum_subset (subset_univ K) (fun k _ hk => by
        have : μ k = 0 := by simpa [K] using hk
        simp [hw0 k this])).symm
    rw [hsum, h1, ← Finset.sum_coe_sort K, ← Equiv.sum_comp K.equivFin.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hσc i
    simp only [κ] at this ⊢
    field_simp

/-- Existence of the SVD (classical). -/
theorem svd_exists (M : S → T → ℂ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (g : Fin r → S → ℂ) (h : Fin r → T → ℂ),
      IsSVD M r lam g h := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨by intro i; exact i.elim0,
      by intro a; exact a.elim0, by intro i; exact i.elim0, by intro i; exact i.elim0,
      fun s => (hS.false s).elim⟩⟩
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨by intro i; exact i.elim0,
      by intro a; exact a.elim0, by intro i; exact i.elim0, by intro i; exact i.elim0,
      fun s t => (hT.false t).elim⟩⟩
  obtain ⟨r, σ, u, v, h1, h2, h3, h4⟩ := svd_std M
  obtain ⟨lam', g', h', hs⟩ := (preSVD_of_std σ u v h1 h2 h3 h4).sort
  exact ⟨r, lam', g', h', hs⟩

/-- Parseval for orthonormal families. -/
private lemma matL2sq_sum_coeff {r : ℕ} (c : Fin r → ℝ) {g : Fin r → S → ℂ} {h : Fin r → T → ℂ}
    (hg : ∀ i j, uinner (g i) (g j) = if i = j then 1 else 0)
    (hh : ∀ i j, uinner (h i) (h j) = if i = j then 1 else 0) :
    matL2sq (fun s t => ∑ i, (c i : ℂ) * g i s * h i t) = ∑ i, c i ^ 2 := by
  apply Complex.ofReal_injective
  have e : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ∀ s t, ((‖∑ i, (c i : ℂ) * g i s * h i t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, ((c i : ℂ) * c j) * ((g i s * star (g j s)) * (h i t * star (h j t))) := by
    intro s t
    rw [e, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have hexp : ((matL2sq (fun s t => ∑ i, (c i : ℂ) * g i s * h i t) : ℝ) : ℂ) =
      𝔼 s, 𝔼 t, ((‖∑ i, (c i : ℂ) * g i s * h i t‖ ^ 2 : ℝ) : ℂ) := by
    unfold matL2sq
    simp only [Complex.ofReal_expect]
  have inner : ∀ i j, 𝔼 s, 𝔼 t, ((c i : ℂ) * c j) * ((g i s * star (g j s)) *
      (h i t * star (h j t))) = ((c i : ℂ) * c j) * (uinner (g i) (g j) * uinner (h i) (h j)) := by
    intro i j
    unfold uinner
    rw [Finset.expect_mul_expect]
    simp_rw [← Finset.mul_expect]
  rw [hexp]
  simp_rw [key]
  simp_rw [Finset.expect_sum_comm]
  simp_rw [inner]
  simp only [hg, hh]
  simp [sq]

theorem IsSVD.sum_sq_lam {M : S → T → ℂ} {r : ℕ} {lam : Fin r → ℝ} {g : Fin r → S → ℂ}
    {h : Fin r → T → ℂ} (hM : IsSVD M r lam g h) : ∑ i, lam i ^ 2 = matL2sq M := by
  rw [← matL2sq_sum_coeff lam hM.orth_g hM.orth_h]
  congr 1
  funext s t
  exact (hM.decomp s t).symm

theorem IsSVD.matL2sq_sub_rank_one {M : S → T → ℂ} {r : ℕ} {lam : Fin r → ℝ}
    {g : Fin r → S → ℂ} {h : Fin r → T → ℂ} (hM : IsSVD M r lam g h) (i : Fin r) :
    matL2sq (fun s t => M s t - (lam i : ℂ) * g i s * h i t) = matL2sq M - lam i ^ 2 := by
  let c : Fin r → ℝ := fun j => if j = i then 0 else lam j
  have hfun : (fun s t => M s t - (lam i : ℂ) * g i s * h i t) =
      fun s t => ∑ j, (c j : ℂ) * g j s * h j t := by
    funext s t
    have : ∑ j, (lam j : ℂ) * g j s * h j t =
        ∑ j, ((c j : ℂ) * g j s * h j t + if j = i then (lam i : ℂ) * g i s * h i t else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp [c]
      · simp [c, hj]
    rw [hM.decomp s t, this, Finset.sum_add_distrib]
    simp
  rw [hfun, matL2sq_sum_coeff c hM.orth_g hM.orth_h, ← hM.sum_sq_lam]
  have : ∑ j, lam j ^ 2 = ∑ j, (c j ^ 2 + if j = i then lam i ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [c]
    · simp [c, hj]
  rw [this, Finset.sum_add_distrib]
  simp

theorem IsSVD.singular_pair {M : S → T → ℂ} {r : ℕ} {lam : Fin r → ℝ} {g : Fin r → S → ℂ}
    {h : Fin r → T → ℂ} (hM : IsSVD M r lam g h) (i : Fin r) :
    (∀ s, 𝔼 t, M s t * star (h i t) = (lam i : ℂ) * g i s) ∧
      (∀ t, 𝔼 s, M s t * star (g i s) = (lam i : ℂ) * h i t) := by
  constructor
  · intro s
    have : ∀ t, M s t * star (h i t) =
        ∑ j, ((lam j : ℂ) * g j s) * (h j t * star (h i t)) := fun t => by
      rw [hM.decomp s t, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [Finset.expect_sum_comm]
    have h2 : ∀ j, 𝔼 t, ((lam j : ℂ) * g j s) * (h j t * star (h i t)) =
        ((lam j : ℂ) * g j s) * uinner (h j) (h i) := fun j => by
      rw [uinner, Finset.mul_expect]
    simp_rw [h2, hM.orth_h]
    simp
  · intro t
    have : ∀ s, M s t * star (g i s) =
        ∑ j, ((lam j : ℂ) * h j t) * (g j s * star (g i s)) := fun s => by
      rw [hM.decomp s t, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [Finset.expect_sum_comm]
    have h2 : ∀ j, 𝔼 s, ((lam j : ℂ) * h j t) * (g j s * star (g i s)) =
        ((lam j : ℂ) * h j t) * uinner (g j) (g i) := fun j => by
      rw [uinner, Finset.mul_expect]
    simp_rw [h2, hM.orth_g]
    simp

private lemma bound_aux {M : S → T → ℂ} {B lam : ℝ} (hB : ∀ s t, ‖M s t‖ ≤ B) (hlam : 0 < lam)
    (g : S → ℂ) (h : T → ℂ) (hh : uinner h h = 1)
    (hgh : ∀ s, 𝔼 t, M s t * star (h t) = (lam : ℂ) * g s) : ∀ s, ‖g s‖ ≤ B / lam := by
  intro s
  have hT : Nonempty T := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [uinner] at hh
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB s hT.some)
  rw [le_div_iff₀ hlam]
  have h1 : ‖(lam : ℂ) * g s‖ = lam * ‖g s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  have hn : 𝔼 t, ‖h t‖ ^ 2 = 1 := by
    have : ((𝔼 t, ‖h t‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hh]
      simp only [Complex.ofReal_expect, uinner]
      refine Finset.expect_congr rfl fun t _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  have h4 : 𝔼 t, ‖h t‖ ≤ 1 := by
    calc 𝔼 t, ‖h t‖ ≤ 𝔼 t, (1 / 2 * ‖h t‖ ^ 2 + 1 / 2) :=
          Finset.expect_le_expect fun t _ => by nlinarith [sq_nonneg (‖h t‖ - 1)]
      _ = 1 / 2 * 𝔼 t, ‖h t‖ ^ 2 + 1 / 2 := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
      _ = 1 := by rw [hn]; norm_num
  have h3 : 𝔼 t, ‖M s t * star (h t)‖ ≤ 𝔼 t, B * ‖h t‖ :=
    Finset.expect_le_expect fun t _ => by
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hB s t) (norm_nonneg _)
  have h2 : ‖𝔼 t, M s t * star (h t)‖ ≤ 𝔼 t, ‖M s t * star (h t)‖ :=
    RCLike.norm_expect_le (K := ℂ)
  rw [hgh s, h1] at h2
  rw [← Finset.mul_expect] at h3
  nlinarith [mul_le_mul_of_nonneg_left h4 hB0]

/-- CSP_6 `lemma:svdinf` (with the implicit hypotheses `‖M‖_∞ ≤ B`, `λ > 0`). -/
theorem svd_vectors_bounded {M : S → T → ℂ} {B lam : ℝ} (hB : ∀ s t, ‖M s t‖ ≤ B)
    (hlam : 0 < lam) (g : S → ℂ) (h : T → ℂ) (hg : uinner g g = 1) (hh : uinner h h = 1)
    (hgh : ∀ s, 𝔼 t, M s t * star (h t) = (lam : ℂ) * g s)
    (hhg : ∀ t, 𝔼 s, M s t * star (g s) = (lam : ℂ) * h t) :
    (∀ s, ‖g s‖ ≤ B / lam) ∧ (∀ t, ‖h t‖ ≤ B / lam) :=
  ⟨bound_aux hB hlam g h hh hgh, bound_aux (M := fun t s => M s t) (fun t s => hB s t) hlam h g hg hhg⟩

end SVD

section JSVD
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the matrix `M_{x,y} = f(x, y)` of `f : Σ^n → ℂ` with rows `x ∈ Σ^J` and columns `y ∈ Σ^{Jᶜ}`. -/
def jMatrix (J : Finset ι) (f : (ι → α) → ℂ) : (↥J → α) → (↥Jᶜ → α) → ℂ :=
  fun x y => f (glueFree J x y)

/-- CSP_6 `def:svd`: a `J`-SVD of `f`. -/
def IsJSVD (J : Finset ι) (f : (ι → α) → ℂ) (r : ℕ) (lam : Fin r → ℝ)
    (g : Fin r → (↥J → α) → ℂ) (h : Fin r → (↥Jᶜ → α) → ℂ) : Prop :=
  IsSVD (jMatrix J f) r lam g h

theorem jsvd_exists (J : Finset ι) (f : (ι → α) → ℂ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (g : Fin r → (↥J → α) → ℂ) (h : Fin r → (↥Jᶜ → α) → ℂ),
      IsJSVD J f r lam g h :=
  svd_exists (jMatrix J f)

theorem matL2sq_jMatrix (J : Finset ι) (f : (ι → α) → ℂ) : matL2sq (jMatrix J f) = l2sq f := by
  let e : (↥J → α) × (↥Jᶜ → α) ≃ (ι → α) :=
    { toFun := fun p => glueFree J p.1 p.2
      invFun := fun x => (fun i => x i, fun i => x i)
      left_inv := by
        rintro ⟨y, z⟩
        refine Prod.ext ?_ ?_
        · funext i; simp [glueFree, i.2]
        · funext i
          have : (i : ι) ∉ J := Finset.mem_compl.1 i.2
          simp [glueFree, this]
      right_inv := by
        intro x; funext i; by_cases h : i ∈ J <;> simp [glueFree, h] }
  unfold matL2sq l2sq
  have h1 : ∀ x y, ‖jMatrix J f x y‖ ^ 2 = (fun p : (↥J → α) × (↥Jᶜ → α) => ‖f (e p)‖ ^ 2) (x, y) :=
    fun x y => rfl
  simp_rw [h1]
  rw [← Finset.expect_product' Finset.univ Finset.univ (fun x y => ‖f (e (x, y))‖ ^ 2)]
  rw [Finset.univ_product_univ]
  exact Fintype.expect_equiv e _ _ fun p => rfl

end JSVD

end TrackB
end RestrictedPolynomials
end
