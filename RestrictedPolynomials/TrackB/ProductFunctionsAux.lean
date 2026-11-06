module

public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Track B: product functions (CSP_7 `kcsp.tex` L648-711)

Covers CSP_7 `lemma:prod1` (`#lattice-reformulation`), `lemma:prodn` (`#eta-sum-bound`) and
`lemma:replace` (`#cauchy-schwarz-tilde-fk`).

Readings of the source used here: the index type of `ℤ^S` is
`Σ i, {a // a ≠ x*ᵢ}`, which fixes the printed count `S = ∑|Aᵢ| - 1` to `∑(|Aᵢ| - 1)`
(the rank gap is closed inside `prod1_lattice_matrix_invertible`);
`∏(1-ηⱼ) = ‖𝔼‖ ≥ δ` and `∑ηⱼ ≤ log(1/δ)`; `f̃_j` is taken for an arbitrary coordinate, with
conditional expectation `y/0 = 0` and `μ_j = μ.marginalPi j`.
-/

@[expose] public section

open Finset
open scoped BigOperators
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### K7 `lemma:prod1#lattice-reformulation` -/

section LatticeReformulation
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- the coordinates `(i, a)` with `a ≠ x*ᵢ` of the lattice `ℤ^S`, `S = ∑ᵢ (|Aᵢ| - 1)`. -/
abbrev prod1LatticeIdx (xs : ∀ i, A i) : Type := Σ i : Fin k, {a : A i // a ≠ xs i}

/-- `a_x ∈ ℤ^S`, so that `⟨a_x, α⟩ = ∑ᵢ αᵢ(xᵢ)` whenever `αᵢ(x*ᵢ) = 0`. -/
def prod1LatticeVec (xs : ∀ i, A i) (x : ∀ i, A i) : prod1LatticeIdx xs → ℤ :=
  fun j => if x j.1 = j.2.1 then 1 else 0

private theorem prod1_vec_sum (xs x : ∀ i, A i) (w : ∀ i, A i → ℝ) (hw : ∀ i, w i (xs i) = 0) :
    ∑ j : prod1LatticeIdx xs, (prod1LatticeVec xs x j : ℝ) * w j.1 j.2.1 = ∑ i, w i (x i) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∑ a : {a : A i // a ≠ xs i}, (prod1LatticeVec xs x ⟨i, a⟩ : ℝ) * w i a.1
      = ∑ a : A i, (if x i = a then (1:ℝ) else 0) * w i a := by
    have h0 : ∀ a : {a : A i // a ≠ xs i}, (prod1LatticeVec xs x ⟨i, a⟩ : ℝ) * w i a.1
        = (fun a : A i => (if x i = a then (1:ℝ) else 0) * w i a) a.1 := by
      intro a
      simp [prod1LatticeVec]
    rw [Finset.sum_congr rfl fun a _ => h0 a]
    rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ xs i)) (p := fun a => a ≠ xs i)
      (fun a => by simp) (fun a => (if x i = a then (1:ℝ) else 0) * w i a)]
    rw [Finset.sum_filter_of_ne]
    intro a _ ha
    by_contra hne
    subst hne
    simp [hw] at ha
  rw [h1]
  simp

/-- no abelian embedding of `S` gives: real `αᵢ` with `∑ᵢ αᵢ(xᵢ) ∈ ℤ` on `S` have `αᵢ` constant
mod `1` (`π ∘ αᵢ` constant, `π : ℝ → ℝ/ℤ`). -/
theorem prod1_real_const_mod_one_of_noEmbedding {S : Set (∀ i, A i)}
    (h : NoNontrivialAbelianEmbeddingPi S) (α : ∀ i, A i → ℝ)
    (hα : ∀ x ∈ S, ∃ n : ℤ, ∑ i, α i (x i) = n) :
    ∀ i (a b : A i), ∃ m : ℤ, α i a - α i b = m := by
  intro i a b
  have key := h (AddCircle (1 : ℝ)) (fun i a => ((α i a : ℝ) : AddCircle (1 : ℝ))) (by
    intro x hx
    obtain ⟨n, hn⟩ := hα x hx
    rw [← QuotientAddGroup.mk_sum, hn, AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩) i a b
  have : (((α i a - α i b : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, key, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at this
  obtain ⟨m, hm⟩ := this
  exact ⟨m, by simpa using hm.symm⟩

/-- The "equivalently" clause of `lemma:prod1`: the real-embedding criterion and the lattice criterion
`⟨a_x, α⟩ ∈ ℤ ∀ x ∈ S ⇒ α ∈ ℤ^S` are equivalent (`x*` a base point of `S`). -/
theorem prod1_lattice_criterion_iff {S : Set (∀ i, A i)} {xs : ∀ i, A i} (hxs : xs ∈ S) :
    (∀ α : ∀ i, A i → ℝ, (∀ x ∈ S, ∃ n : ℤ, ∑ i, α i (x i) = n) →
        ∀ i (a b : A i), ∃ m : ℤ, α i a - α i b = m) ↔
      (∀ v : prod1LatticeIdx xs → ℝ,
        (∀ x ∈ S, ∃ n : ℤ, ∑ j, (prod1LatticeVec xs x j : ℝ) * v j = n) →
          ∀ j, ∃ m : ℤ, v j = m) := by
  constructor
  · intro H v hv j
    let α : ∀ i, A i → ℝ := fun i a => if h : a = xs i then 0 else v ⟨i, ⟨a, h⟩⟩
    have hα0 : ∀ i, α i (xs i) = 0 := fun i => by simp [α]
    have hsum : ∀ x, ∑ j, (prod1LatticeVec xs x j : ℝ) * v j = ∑ i, α i (x i) := by
      intro x
      rw [← prod1_vec_sum xs x α hα0]
      refine Finset.sum_congr rfl fun j _ => ?_
      obtain ⟨i, a, ha⟩ := j
      simp [α, ha]
    obtain ⟨i, a, ha⟩ := j
    obtain ⟨m, hm⟩ := H α (fun x hx => by
      obtain ⟨n, hn⟩ := hv x hx
      exact ⟨n, by rw [← hsum]; exact hn⟩) i a (xs i)
    exact ⟨m, by simpa [α, ha] using hm⟩
  · intro H α hα i a b
    let v : prod1LatticeIdx xs → ℝ := fun j => α j.1 j.2.1 - α j.1 (xs j.1)
    have hsum : ∀ x, ∑ j, (prod1LatticeVec xs x j : ℝ) * v j
        = ∑ i, α i (x i) - ∑ i, α i (xs i) := by
      intro x
      have := prod1_vec_sum xs x (fun i a => α i a - α i (xs i)) (fun i => by simp)
      rw [Finset.sum_sub_distrib] at this
      exact this
    obtain ⟨n0, hn0⟩ := hα xs hxs
    have hv := H v (fun x hx => by
      obtain ⟨n, hn⟩ := hα x hx
      exact ⟨n - n0, by rw [hsum, hn, hn0]; push_cast; ring⟩)
    have hc : ∀ c : A i, ∃ m : ℤ, α i c - α i (xs i) = m := by
      intro c
      by_cases hc : c = xs i
      · exact ⟨0, by simp [hc]⟩
      · exact hv ⟨i, ⟨c, hc⟩⟩
    obtain ⟨m1, h1⟩ := hc a
    obtain ⟨m2, h2⟩ := hc b
    exact ⟨m1 - m2, by push_cast; linarith⟩

/-- the lattice `L = span_ℤ(a_x)` has a spanning family of `S` vectors (`S = |prod1LatticeIdx xs|`):
`L ⊆ ℤ^S` is free of rank at most `S`; pad a basis with zeros. -/
theorem prod1_exists_lattice_spanning_family (S : Set (∀ i, A i)) (xs : ∀ i, A i) :
    ∃ a : prod1LatticeIdx xs → prod1LatticeIdx xs → ℤ,
      Submodule.span ℤ (Set.range a) = Submodule.span ℤ (prod1LatticeVec xs '' S) := by
  set L : Submodule ℤ (prod1LatticeIdx xs → ℤ) := Submodule.span ℤ (prod1LatticeVec xs '' S)
    with hL
  let b := Module.finBasis ℤ L
  have hr : Module.finrank ℤ L ≤ Fintype.card (prod1LatticeIdx xs) := by
    have := Submodule.finrank_le L
    simpa using this
  let e := Fintype.equivFin (prod1LatticeIdx xs)
  refine ⟨fun j => if h : (e j : ℕ) < Module.finrank ℤ L then ((b ⟨e j, h⟩ : L) : _ → ℤ) else 0,
    ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    dsimp only
    split_ifs
    · exact (b _).2
    · exact L.zero_mem
  · intro y hy
    have hy' : (⟨y, hy⟩ : L) ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    have : y ∈ Submodule.map L.subtype (Submodule.span ℤ (Set.range b)) :=
      ⟨_, hy', rfl⟩
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi : (i : ℕ) < Fintype.card (prod1LatticeIdx xs) :=
      lt_of_lt_of_le i.2 hr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    simp

/-- the matrix `A` with rows a spanning family of `L` is invertible over `ℤ`, i.e. `A⁻¹` has
integer entries (the rank of `L` being `S` is a consequence, not a hypothesis). -/
theorem prod1_lattice_matrix_invertible {S : Set (∀ i, A i)}
    (h : NoNontrivialAbelianEmbeddingPi S) {xs : ∀ i, A i} (hxs : xs ∈ S)
    (a : prod1LatticeIdx xs → prod1LatticeIdx xs → ℤ)
    (ha : Submodule.span ℤ (Set.range a) = Submodule.span ℤ (prod1LatticeVec xs '' S)) :
    ∃ B : Matrix (prod1LatticeIdx xs) (prod1LatticeIdx xs) ℤ,
      Matrix.of a * B = 1 ∧ B * Matrix.of a = 1 := by
  have hcrit := (prod1_lattice_criterion_iff hxs).1
    (fun α hα => prod1_real_const_mod_one_of_noEmbedding h α hα)
  -- integrality of `v` whenever `A v` is integral
  have hint : ∀ v : prod1LatticeIdx xs → ℝ,
      (∀ j, ∃ m : ℤ, ∑ l, (a j l : ℝ) * v l = m) → ∀ j, ∃ m : ℤ, v j = m := by
    intro v hv
    apply hcrit v
    intro x hx
    have hmem : prod1LatticeVec xs x ∈ Submodule.span ℤ (Set.range a) := by
      rw [ha]; exact Submodule.subset_span ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
    choose m hm using hv
    refine ⟨∑ j, c j * m j, ?_⟩
    have hx' : ∀ l, (prod1LatticeVec xs x l : ℝ) = ∑ j, (c j : ℝ) * (a j l : ℝ) := by
      intro l
      have := congrFun hc l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← this]; push_cast; rfl
    calc ∑ l, (prod1LatticeVec xs x l : ℝ) * v l
        = ∑ l, ∑ j, (c j : ℝ) * ((a j l : ℝ) * v l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hx' l, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, (c j : ℝ) * ∑ l, (a j l : ℝ) * v l := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
      _ = ((∑ j, c j * m j : ℤ) : ℝ) := by
          push_cast
          exact Finset.sum_congr rfl fun j _ => by rw [hm j]
  set M : Matrix (prod1LatticeIdx xs) (prod1LatticeIdx xs) ℝ := Matrix.of fun i j => (a i j : ℝ)
    with hM
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    have hj' : v j ≠ 0 := hj
    have := hint ((1 / (2 * v j)) • v) (fun l => ⟨0, by
      have := congrFun hv l
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, hM, Matrix.of_apply] at this
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_zero]
      calc ∑ l', (a l l' : ℝ) * (1 / (2 * v j) * v l')
          = 1 / (2 * v j) * ∑ l', (a l l' : ℝ) * v l' := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [this, mul_zero]⟩) j
    obtain ⟨m, hm⟩ := this
    simp only [Pi.smul_apply, smul_eq_mul] at hm
    have : (1 / (2 * v j)) * v j = 1 / 2 := by field_simp
    rw [this] at hm
    have h2 : (2 : ℝ) * m = 1 := by linarith
    have h3 : (2 : ℤ) * m = 1 := by exact_mod_cast h2
    omega
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have hcol : ∀ k l, ∃ m : ℤ, M⁻¹ k l = m := by
    intro k l
    apply hint (fun r => M⁻¹ r l) _ k
    intro j
    have := congrFun (congrFun hMM j) l
    refine ⟨if j = l then 1 else 0, ?_⟩
    simp only [Matrix.mul_apply, hM, Matrix.of_apply, Matrix.one_apply] at this
    rw [this]
    split_ifs <;> simp
  choose B hB using hcol
  have hAB : Matrix.of a * Matrix.of B = 1 := by
    ext i j
    have := congrFun (congrFun hMM i) j
    simp only [Matrix.mul_apply, hM, Matrix.of_apply, Matrix.one_apply] at this ⊢
    have h' : ∑ l, (a i l : ℝ) * (B l j : ℝ) = if i = j then 1 else 0 := by
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => by rw [hB l j]
    split_ifs at h' ⊢ <;> exact_mod_cast h'
  exact ⟨Matrix.of B, hAB, mul_eq_one_comm.1 hAB⟩

end LatticeReformulation

/-! ### K7 `lemma:prodn#eta-sum-bound` -/

section EtaSum
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `𝔼_{μ^{⊗n}} ∏ᵢ Pᵢ = ∏ⱼ 𝔼_μ ∏ᵢ Pᵢ^{(j)}` for the product functions `Pᵢ(x) = ∏ⱼ Pᵢ^{(j)}(xⱼ)`
(here `Q i j = Pᵢ^{(j)}` and `X j i` is the `i`-th letter of the `j`-th sample). -/
theorem prodn_cexpect_pi_prod_factor (μ : FinProb (∀ i, A i)) (Q : ∀ i, ι → A i → ℂ) :
    (μ.pi ι).cexpect (fun X => ∏ i, ∏ j, Q i j (X j i)) =
      ∏ j, μ.cexpect (fun y => ∏ i, Q i j (y i)) := by
  unfold FinProb.cexpect
  have h1 : ∀ X : ι → ∀ i, A i, (((μ.pi ι).prob X : ℝ) : ℂ) * ∏ i, ∏ j, Q i j (X j i)
      = ∏ j, ((μ.prob (X j) : ℂ) * ∏ i, Q i j (X j i)) := by
    intro X
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
    simp [FinProb.pi]
  rw [Finset.sum_congr rfl fun X _ => h1 X]
  exact (Fintype.prod_sum (fun j (a : ∀ i, A i) => (μ.prob a : ℂ) * ∏ i, Q i j (a i))).symm

/-- CSP_7 `lemma:prodn#eta-sum-bound`:`1 - ηⱼ := |𝔼_μ ∏ᵢ Pᵢ^{(j)}|`; then `∏ⱼ (1 - ηⱼ) = |𝔼_{μ^{⊗n}} ∏ᵢ Pᵢ|
≥ δ` and `∑ⱼ ηⱼ ≤ log (1/δ)` (the source's `O(log(1/δ))` with constant `1`). -/
theorem prodn_eta_sum_bound (μ : FinProb (∀ i, A i)) (Q : ∀ i, ι → A i → ℂ)
    (hQ : ∀ i j a, ‖Q i j a‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hcorr : δ ≤ ‖(μ.pi ι).cexpect (fun X => ∏ i, ∏ j, Q i j (X j i))‖)
    (η : ι → ℝ) (hη : ∀ j, η j = 1 - ‖μ.cexpect (fun y => ∏ i, Q i j (y i))‖) :
    (∀ j, 0 ≤ η j ∧ η j ≤ 1) ∧
      ∏ j, (1 - η j) = ‖(μ.pi ι).cexpect (fun X => ∏ i, ∏ j, Q i j (X j i))‖ ∧
      ∑ j, η j ≤ Real.log (1 / δ) := by
  have hE : ∀ j, ‖μ.cexpect (fun y => ∏ i, Q i j (y i))‖ ≤ 1 := by
    intro j
    unfold FinProb.cexpect
    calc ‖∑ a, (μ.prob a : ℂ) * ∏ i, Q i j (a i)‖
        ≤ ∑ a, ‖(μ.prob a : ℂ) * ∏ i, Q i j (a i)‖ := norm_sum_le _ _
      _ ≤ ∑ a, μ.prob a := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_prod, Complex.norm_real, Real.norm_of_nonneg (μ.nonneg a)]
          have : ∏ i, ‖Q i j (a i)‖ ≤ 1 :=
            Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hQ i j _
          nlinarith [μ.nonneg a]
      _ = 1 := μ.sum_eq_one
  have h1 : ∀ j, 1 - η j = ‖μ.cexpect (fun y => ∏ i, Q i j (y i))‖ := fun j => by
    rw [hη]; ring
  have hprod : ∏ j, (1 - η j) = ‖(μ.pi ι).cexpect (fun X => ∏ i, ∏ j, Q i j (X j i))‖ := by
    rw [prodn_cexpect_pi_prod_factor, norm_prod]
    exact Finset.prod_congr rfl fun j _ => h1 j
  refine ⟨fun j => ⟨?_, ?_⟩, hprod, ?_⟩
  · rw [hη]; linarith [hE j]
  · rw [hη]; linarith [norm_nonneg (μ.cexpect (fun y => ∏ i, Q i j (y i)))]
  have hle : δ ≤ Real.exp (-∑ j, η j) := by
    calc δ ≤ ∏ j, (1 - η j) := hprod ▸ hcorr
      _ ≤ ∏ j, Real.exp (-η j) := by
          refine Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_
          · rw [h1]; exact norm_nonneg _
          · linarith [Real.add_one_le_exp (-η j)]
      _ = Real.exp (-∑ j, η j) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have := Real.log_le_log hδ hle
  rw [Real.log_exp] at this
  rw [one_div, Real.log_inv]
  linarith

end EtaSum

/-! ### K7 `lemma:replace#cauchy-schwarz-tilde-fk` -/

section TildeFk
variable {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `f̃_j(x) = 𝔼_{X ∼ μ^{⊗ι}}[∏_{i ≠ j} fᵢ(Xᵢ) | X_j = x]`; the value is `0` at `x` of probability
`0` (Lean's `y / 0 = 0`, harmless). The source takes `j = k` (the last coordinate). -/
def replaceCondProdExp (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) (j : Fin k)
    (x : ι → A j) : ℂ :=
  (∑ X : ι → ∀ i, A i, if (fun t => X t j) = x then
      ((μ.pi ι).prob X : ℂ) * ∏ i ∈ univ.erase j, f i (fun t => X t i) else 0) /
    (((μ.marginalPi j).pi ι).prob x : ℂ)

/-- the numerator of `f̃_j`. -/
private def tildeNum (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) (j : Fin k)
    (x : ι → A j) : ℂ :=
  ∑ X : ι → ∀ i, A i, if (fun t => X t j) = x then
      ((μ.pi ι).prob X : ℂ) * ∏ i ∈ univ.erase j, f i (fun t => X t i) else 0

/-- the mass of a fibre `{X | X·j = x}` is the mass of `x` under `μ_j^{⊗ι}`. -/
private theorem tilde_fibre_mass (μ : FinProb (∀ i, A i)) (j : Fin k) (x : ι → A j) :
    ∑ X : ι → ∀ i, A i, (if (fun t => X t j) = x then (μ.pi ι).prob X else 0) =
      ((μ.marginalPi j).pi ι).prob x := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ.filter fun X : ι → ∀ i, A i => (fun t => X t j) = x) =
      Fintype.piFinset fun t => Finset.univ.filter fun y : ∀ i, A i => y j = x t := by
    ext X
    simp [Fintype.mem_piFinset, funext_iff]
  rw [h]
  simp only [FinProb.pi, FinProb.marginalPi]
  rw [Finset.prod_univ_sum]

private theorem tilde_num_eq (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) (j : Fin k)
    (x : ι → A j) :
    tildeNum μ f j x = (((μ.marginalPi j).pi ι).prob x : ℂ) * replaceCondProdExp μ f j x := by
  unfold replaceCondProdExp
  change tildeNum μ f j x = _ * (tildeNum μ f j x / _)
  by_cases hw : ((μ.marginalPi j).pi ι).prob x = 0
  · have hz : ∀ X : ι → ∀ i, A i, (fun t => X t j) = x → (μ.pi ι).prob X = 0 := by
      intro X hX
      have h0 := tilde_fibre_mass μ j x
      rw [hw] at h0
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun X _ => by
        split_ifs
        · exact (μ.pi ι).nonneg X
        · exact le_refl _)).1 h0 X (Finset.mem_univ _)
      simpa [hX] using this
    have : tildeNum μ f j x = 0 := by
      unfold tildeNum
      refine Finset.sum_eq_zero fun X _ => ?_
      split_ifs with hX
      · rw [hz X hX]; simp
      · rfl
    rw [this]; simp [hw]
  · have : (((μ.marginalPi j).pi ι).prob x : ℂ) ≠ 0 := by exact_mod_cast hw
    field_simp

/-- sum over fibres. -/
private theorem tilde_fiber_sum (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ) (j : Fin k)
    (H : (ι → A j) → ℂ) :
    ∑ X : ι → ∀ i, A i, ((μ.pi ι).prob X : ℂ) *
        ((∏ i ∈ univ.erase j, f i (fun t => X t i)) * H (fun t => X t j)) =
      ∑ x, H x * tildeNum μ f j x := by
  unfold tildeNum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_eq_single (fun t => X t j)]
  · simp only [ite_true]; ring
  · intro x _ hx
    simp [show ¬ (fun t => X t j) = x from fun h => hx h.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [Fintype ι] [DecidableEq ι] in
private theorem tilde_norm_pe_le (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) (j : Fin k)
    (X : ι → ∀ i, A i) : ‖∏ i ∈ univ.erase j, f i (fun t => X t i)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hf i _

/-- `f̃_j` is `1`-bounded. -/
theorem replace_condProdExp_norm_le (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (j : Fin k) (x : ι → A j) :
    ‖replaceCondProdExp μ f j x‖ ≤ 1 := by
  by_cases hw : ((μ.marginalPi j).pi ι).prob x = 0
  · unfold replaceCondProdExp; simp [hw]
  · have hpos : 0 < ((μ.marginalPi j).pi ι).prob x :=
      lt_of_le_of_ne (((μ.marginalPi j).pi ι).nonneg x) (Ne.symm hw)
    have hnum : ‖tildeNum μ f j x‖ ≤ ((μ.marginalPi j).pi ι).prob x := by
      rw [← tilde_fibre_mass μ j x]
      unfold tildeNum
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun X _ => ?_)
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ((μ.pi ι).nonneg X)]
        have := tilde_norm_pe_le f hf j X
        nlinarith [(μ.pi ι).nonneg X]
      · simp
    have h := tilde_num_eq μ f j x
    have hne : (((μ.marginalPi j).pi ι).prob x : ℂ) ≠ 0 := by exact_mod_cast hw
    have : replaceCondProdExp μ f j x = tildeNum μ f j x / (((μ.marginalPi j).pi ι).prob x : ℂ) := by
      rw [h]; field_simp
    rw [this, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_le_one hpos]
    exact hnum

/-- `𝔼_{μ^{⊗n}} ∏ᵢ fᵢ = 𝔼_{x ∼ μ_j^{⊗n}} f̃_j(x) f_j(x)`. -/
theorem replace_cexpect_prod_eq (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ)
    (j : Fin k) :
    (μ.pi ι).cexpect (fun X => ∏ i, f i (fun t => X t i)) =
      ((μ.marginalPi j).pi ι).cexpect (fun x => replaceCondProdExp μ f j x * f j x) := by
  unfold FinProb.cexpect
  have h1 : ∀ X : ι → ∀ i, A i, ((μ.pi ι).prob X : ℂ) * ∏ i, f i (fun t => X t i) =
      ((μ.pi ι).prob X : ℂ) * ((∏ i ∈ univ.erase j, f i (fun t => X t i)) *
        f j (fun t => X t j)) := by
    intro X
    rw [← Finset.mul_prod_erase univ (fun i => f i (fun t => X t i)) (Finset.mem_univ j)]
    ring
  rw [Finset.sum_congr rfl fun X _ => h1 X, tilde_fiber_sum μ f j (fun x => f j x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tilde_num_eq]; ring

/-- `|𝔼_{μ_j^{⊗n}} f̃_j f_j|² ≤ ‖f̃_j‖₂² ‖f_j‖₂² ≤ ‖f̃_j‖₂²`. -/
theorem replace_norm_sq_cexpect_le (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (j : Fin k) :
    ‖((μ.marginalPi j).pi ι).cexpect (fun x => replaceCondProdExp μ f j x * f j x)‖ ^ 2 ≤
      ∑ x, ((μ.marginalPi j).pi ι).prob x * ‖replaceCondProdExp μ f j x‖ ^ 2 := by
  set ν := (μ.marginalPi j).pi ι with hν
  unfold FinProb.cexpect
  have h1 : ‖∑ x, (ν.prob x : ℂ) * (replaceCondProdExp μ f j x * f j x)‖ ≤
      ∑ x, Real.sqrt (ν.prob x) * ‖replaceCondProdExp μ f j x‖ *
        (Real.sqrt (ν.prob x) * ‖f j x‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.nonneg x)]
    have := Real.mul_self_sqrt (ν.nonneg x)
    refine le_of_eq ?_
    calc ν.prob x * (‖replaceCondProdExp μ f j x‖ * ‖f j x‖)
        = (√(ν.prob x) * √(ν.prob x)) * (‖replaceCondProdExp μ f j x‖ * ‖f j x‖) := by
          rw [this]
      _ = _ := by ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (ν.prob x) * ‖replaceCondProdExp μ f j x‖)
    (fun x => Real.sqrt (ν.prob x) * ‖f j x‖)
  have h3 : ∑ x, (Real.sqrt (ν.prob x) * ‖f j x‖) ^ 2 ≤ 1 := by
    calc ∑ x, (Real.sqrt (ν.prob x) * ‖f j x‖) ^ 2 ≤ ∑ x, ν.prob x := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [mul_pow, Real.sq_sqrt (ν.nonneg x)]
          exact mul_le_of_le_one_right (ν.nonneg x) (pow_le_one₀ (norm_nonneg _) (hf j x))
      _ = 1 := ν.sum_eq_one
  have h4 : ∑ x, (Real.sqrt (ν.prob x) * ‖replaceCondProdExp μ f j x‖) ^ 2 =
      ∑ x, ν.prob x * ‖replaceCondProdExp μ f j x‖ ^ 2 :=
    Finset.sum_congr rfl fun x _ => by rw [mul_pow, Real.sq_sqrt (ν.nonneg x)]
  have h5 : 0 ≤ ∑ x, ν.prob x * ‖replaceCondProdExp μ f j x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (ν.nonneg x) (sq_nonneg _)
  calc ‖∑ x, (ν.prob x : ℂ) * (replaceCondProdExp μ f j x * f j x)‖ ^ 2
      ≤ (∑ x, Real.sqrt (ν.prob x) * ‖replaceCondProdExp μ f j x‖ *
        (Real.sqrt (ν.prob x) * ‖f j x‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ ∑ x, ν.prob x * ‖replaceCondProdExp μ f j x‖ ^ 2 := by
        rw [h4]
        calc _ ≤ (∑ x, ν.prob x * ‖replaceCondProdExp μ f j x‖ ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left h3 h5
          _ = _ := mul_one _

/-- `‖f̃_j‖₂² = 𝔼_{μ^{⊗n}} [∏_{i ≠ j} fᵢ(Xᵢ) · conj f̃_j(X_j)]` (a nonnegative real). -/
theorem replace_cexpect_prod_erase_mul_star (μ : FinProb (∀ i, A i))
    (f : ∀ i, (ι → A i) → ℂ) (j : Fin k) :
    (μ.pi ι).cexpect (fun X => (∏ i ∈ univ.erase j, f i (fun t => X t i)) *
        star (replaceCondProdExp μ f j (fun t => X t j))) =
      ((∑ x, ((μ.marginalPi j).pi ι).prob x * ‖replaceCondProdExp μ f j x‖ ^ 2 : ℝ) : ℂ) := by
  unfold FinProb.cexpect
  rw [tilde_fiber_sum μ f j (fun x => star (replaceCondProdExp μ f j x))]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tilde_num_eq]
  have : star (replaceCondProdExp μ f j x) * replaceCondProdExp μ f j x =
      ((‖replaceCondProdExp μ f j x‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul']
  calc star (replaceCondProdExp μ f j x) * (↑(((μ.marginalPi j).pi ι).prob x) *
        replaceCondProdExp μ f j x)
      = ↑(((μ.marginalPi j).pi ι).prob x) *
        (star (replaceCondProdExp μ f j x) * replaceCondProdExp μ f j x) := by ring
    _ = _ := by rw [this]

/-- the whole chain of `lemma:replace`:`ε ≤ |𝔼 ∏ᵢ fᵢ|` implies `ε² ≤ ‖f̃_j‖₂²`. -/
theorem replace_eps_sq_le_l2sq (μ : FinProb (∀ i, A i)) (f : ∀ i, (ι → A i) → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (j : Fin k) {ε : ℝ} (hε : 0 ≤ ε)
    (hcorr : ε ≤ ‖(μ.pi ι).cexpect (fun X => ∏ i, f i (fun t => X t i))‖) :
    ε ^ 2 ≤ ∑ x, ((μ.marginalPi j).pi ι).prob x * ‖replaceCondProdExp μ f j x‖ ^ 2 := by
  have h := replace_norm_sq_cexpect_le μ f hf j
  rw [← replace_cexpect_prod_eq] at h
  exact (pow_le_pow_left₀ hε hcorr 2).trans h

end TildeFk

end TrackB
end RestrictedPolynomials
end
