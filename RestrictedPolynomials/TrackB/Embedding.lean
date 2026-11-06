module

public import RestrictedPolynomials.FinProb
public import RestrictedPolynomials.Frozen.FinProbSupport
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Track B: the shared abelian-embedding file

One `Fin k`-indexed definition of abelian embedding and of pairwise connectedness, consumed by both
Track B regions, plus the ternary `X × Y × Z` view of the paper IV region (`Tri.ofProd`), the bridge to the
frozen `NoNontrivialAbelianEmbeddingPi`, and the leaf lemmas on embeddings.

Statements covered: paper IV `definition-abelian-embedding`, `definition-linear-reduction`,
`claim-affine-shift-zero-in-image`, `lem:bound-p-in-embed`; the paper's
`d-abelianEmbedding#full-marginal-support`; `definition-pairwise-connected` of paper IV, CSP_7 and
CSP_6; CSP_7 `obs:sub`, `obs:pc`.
-/

@[expose] public section

open Finset

noncomputable section

namespace RestrictedPolynomials
namespace TrackB

universe u

/-! ### k-ary primitives (same indexing as the frozen `NoNontrivialAbelianEmbeddingPi`) -/
section Pi
variable {k : ℕ} {A : Fin k → Type*}

/-- `σ` is an abelian embedding of `S`: `∑ᵢ σᵢ(aᵢ) = 0` on `S`. -/
def IsEmbeddingPi (S : Set (∀ i, A i)) {G : Type*} [AddCommGroup G] (σ : ∀ i, A i → G) : Prop :=
  ∀ a ∈ S, ∑ i, σ i (a i) = 0

/-- non-trivial: some component is not constant. -/
def IsNontrivialPi {G : Type*} (σ : ∀ i, A i → G) : Prop := ∃ i x y, σ i x ≠ σ i y

/-- `S` admits a non-trivial abelian embedding into the group `G`. -/
def AdmitsEmbeddingIntoPi (S : Set (∀ i, A i)) (G : Type*) [AddCommGroup G] : Prop :=
  ∃ σ : ∀ i, A i → G, IsEmbeddingPi S σ ∧ IsNontrivialPi σ

/-- `S` admits a non-trivial abelian embedding into some abelian group (universe `Type`, as frozen). -/
def AdmitsAbelianEmbeddingPi (S : Set (∀ i, A i)) : Prop :=
  ∃ (G : Type) (_ : AddCommGroup G), AdmitsEmbeddingIntoPi S G

/-- bridge to the frozen definition. -/
theorem noNontrivialAbelianEmbeddingPi_iff (S : Set (∀ i, A i)) :
    NoNontrivialAbelianEmbeddingPi S ↔ ¬ AdmitsAbelianEmbeddingPi S := by
  constructor
  · rintro h ⟨G, _, σ, hσ, i, x, y, hxy⟩
    exact hxy (h G σ hσ i x y)
  · intro h G _ σ hσ i x y
    by_contra hxy
    exact h ⟨G, inferInstance, σ, hσ, i, x, y, hxy⟩

/-- the bipartite graph `(A i ⊔ A j, supp μ_{ij})` of `S`. -/
def pairGraph (S : Set (∀ i, A i)) (i j : Fin k) : SimpleGraph (A i ⊕ A j) :=
  SimpleGraph.fromRel fun u v => ∃ a b, u = Sum.inl a ∧ v = Sum.inr b ∧ ∃ t ∈ S, t i = a ∧ t j = b

/-- pairwise connected (whole alphabets as vertices, as in the source). -/
def PairwiseConnectedSet (S : Set (∀ i, A i)) : Prop :=
  ∀ i j, i ≠ j → (pairGraph S i j).Connected

/-- a distribution is pairwise connected iff its support is. -/
def PairwiseConnectedDist [∀ i, Fintype (A i)] (μ : FinProb (∀ i, A i)) : Prop :=
  PairwiseConnectedSet μ.support
end Pi

/-! ### ternary view `X × Y × Z` as the `k = 3` case (derived, not a second definition) -/
section Tri
variable {X Y Z : Type u}

def Tri (X Y Z : Type u) : Fin 3 → Type u
  | 0 => X
  | 1 => Y
  | 2 => Z

def Tri.ofProd (p : X × Y × Z) : ∀ i, Tri X Y Z i
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2

def Tri.maps {H : Type*} (σ : X → H) (γ : Y → H) (φ : Z → H) : ∀ i, Tri X Y Z i → H
  | 0 => σ
  | 1 => γ
  | 2 => φ

def IsEmbedding3 (S : Set (X × Y × Z)) {H : Type*} [AddCommGroup H]
    (σ : X → H) (γ : Y → H) (φ : Z → H) : Prop :=
  IsEmbeddingPi (Tri.ofProd '' S) (Tri.maps σ γ φ)

def IsNontrivialEmbedding3 {H : Type*} (σ : X → H) (γ : Y → H) (φ : Z → H) : Prop :=
  IsNontrivialPi (Tri.maps σ γ φ)

def AdmitsEmbeddingInto3 (S : Set (X × Y × Z)) (H : Type*) [AddCommGroup H] : Prop :=
  AdmitsEmbeddingIntoPi (Tri.ofProd '' S) H

def AdmitsAbelianEmbedding3 (S : Set (X × Y × Z)) : Prop :=
  AdmitsAbelianEmbeddingPi (Tri.ofProd '' S)

def PairwiseConnected3 (S : Set (X × Y × Z)) : Prop :=
  PairwiseConnectedSet (Tri.ofProd '' S)

theorem isEmbedding3_iff (S : Set (X × Y × Z)) {H : Type*} [AddCommGroup H]
    (σ : X → H) (γ : Y → H) (φ : Z → H) :
    IsEmbedding3 S σ γ φ ↔ ∀ p ∈ S, σ p.1 + γ p.2.1 + φ p.2.2 = 0 := by
  unfold IsEmbedding3 IsEmbeddingPi
  simp only [Set.forall_mem_image, Fin.sum_univ_three]
  rfl

theorem isNontrivialEmbedding3_iff {H : Type*} (σ : X → H) (γ : Y → H) (φ : Z → H) :
    IsNontrivialEmbedding3 σ γ φ ↔
      ¬ ((∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b)) := by
  unfold IsNontrivialEmbedding3 IsNontrivialPi
  constructor
  · rintro ⟨i, x, y, hxy⟩ ⟨h0, h1, h2⟩
    fin_cases i
    · exact hxy (h0 x y)
    · exact hxy (h1 x y)
    · exact hxy (h2 x y)
  · intro h
    by_contra h'
    apply h
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
    · by_contra hab; exact h' ⟨0, a, b, hab⟩
    · by_contra hab; exact h' ⟨1, a, b, hab⟩
    · by_contra hab; exact h' ⟨2, a, b, hab⟩

theorem admitsEmbeddingInto3_iff (S : Set (X × Y × Z)) (H : Type*) [AddCommGroup H] :
    AdmitsEmbeddingInto3 S H ↔ ∃ (σ : X → H) (γ : Y → H) (φ : Z → H),
      IsEmbedding3 S σ γ φ ∧ IsNontrivialEmbedding3 σ γ φ := by
  unfold AdmitsEmbeddingInto3 AdmitsEmbeddingIntoPi
  constructor
  · rintro ⟨τ, hτ, hn⟩
    have e : τ = Tri.maps (τ 0) (τ 1) (τ 2) := by
      funext i; fin_cases i <;> rfl
    refine ⟨τ 0, τ 1, τ 2, ?_, ?_⟩
    · exact (congrArg (IsEmbeddingPi (Tri.ofProd '' S)) e).mp hτ
    · exact (congrArg IsNontrivialPi e).mp hn
  · rintro ⟨σ, γ, φ, h1, h2⟩
    exact ⟨_, h1, h2⟩

theorem pairGraph_connected_swap {k : ℕ} {A : Fin k → Type*} (S : Set (∀ i, A i)) (i j : Fin k) :
    (pairGraph S i j).Connected → (pairGraph S j i).Connected := by
  intro h
  have iso : pairGraph S i j ≃g pairGraph S j i :=
    { toEquiv := Equiv.sumComm _ _
      map_rel_iff' := by
        intro u v
        simp only [pairGraph, SimpleGraph.fromRel_adj, Equiv.sumComm_apply]
        rcases u with u | u <;> rcases v with v | v <;> simp <;> aesop }
  exact iso.connected_iff.mp h

theorem pairwiseConnected3_iff (S : Set (X × Y × Z)) :
    PairwiseConnected3 S ↔
      (SimpleGraph.fromRel fun (a : X ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y).Connected ∧
      (SimpleGraph.fromRel fun (a : X ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z).Connected ∧
      (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z).Connected := by
  have e01 : pairGraph (Tri.ofProd '' S) (0 : Fin 3) 1 =
      (SimpleGraph.fromRel fun (a : X ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y) := by
    unfold pairGraph
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨a, b, rfl, rfl, t, ⟨⟨x, y, z⟩, hp, rfl⟩, h1, h2⟩
      exact ⟨x, y, z, hp, by rw [← h1]; rfl, by rw [← h2]; rfl⟩
    · rintro ⟨x, y, z, hp, rfl, rfl⟩
      exact ⟨x, y, rfl, rfl, Tri.ofProd (x, y, z), ⟨_, hp, rfl⟩, rfl, rfl⟩
  have e02 : pairGraph (Tri.ofProd '' S) (0 : Fin 3) 2 =
      (SimpleGraph.fromRel fun (a : X ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z) := by
    unfold pairGraph
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨a, b, rfl, rfl, t, ⟨⟨x, y, z⟩, hp, rfl⟩, h1, h2⟩
      exact ⟨x, y, z, hp, by rw [← h1]; rfl, by rw [← h2]; rfl⟩
    · rintro ⟨x, y, z, hp, rfl, rfl⟩
      exact ⟨x, z, rfl, rfl, Tri.ofProd (x, y, z), ⟨_, hp, rfl⟩, rfl, rfl⟩
  have e12 : pairGraph (Tri.ofProd '' S) (1 : Fin 3) 2 =
      (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z) := by
    unfold pairGraph
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨a, b, rfl, rfl, t, ⟨⟨x, y, z⟩, hp, rfl⟩, h1, h2⟩
      exact ⟨x, y, z, hp, by rw [← h1]; rfl, by rw [← h2]; rfl⟩
    · rintro ⟨x, y, z, hp, rfl, rfl⟩
      exact ⟨y, z, rfl, rfl, Tri.ofProd (x, y, z), ⟨_, hp, rfl⟩, rfl, rfl⟩
  unfold PairwiseConnected3 PairwiseConnectedSet
  rw [← e01, ← e02, ← e12]
  constructor
  · intro h
    exact ⟨h 0 1 (by decide), h 0 2 (by decide), h 1 2 (by decide)⟩
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | assumption
      | exact pairGraph_connected_swap _ _ _ ‹_›

theorem noNontrivialAbelianEmbeddingPi_iff_3 (S : Set (X × Y × Z)) :
    NoNontrivialAbelianEmbeddingPi (Tri.ofProd '' S) ↔ ¬ AdmitsAbelianEmbedding3 S :=
  noNontrivialAbelianEmbeddingPi_iff _
end Tri

/-! ### Linear-algebra core of `lem:bound-p-in-embed` -/
section BoundP

/-- Clearing denominators: if every integer solution of the system `rows` kills `c`, then some
non-zero integer multiple of `c` is an integer combination of the rows. -/
theorem exists_int_combination {ι N : Type*} [Fintype ι] [Fintype N]
    (rows : ι → N → ℤ) (c : N → ℤ)
    (h : ∀ v : N → ℤ, (∀ i, ∑ j, rows i j * v j = 0) → ∑ j, c j * v j = 0) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ n : ι → ℤ, ∀ j, D * c j = ∑ i, n i * rows i j := by
  classical
  let dl : (N → ℚ) → ((N → ℚ) →ₗ[ℚ] ℚ) :=
    fun w => ∑ j, w j • (LinearMap.proj j : (N → ℚ) →ₗ[ℚ] ℚ)
  have hdl : ∀ w v, dl w v = ∑ j, w j * v j := by intro w v; simp [dl]
  have hspan : dl (fun j => (c j : ℚ)) ∈
      Submodule.span ℚ (Set.range fun i => dl (fun j => (rows i j : ℚ))) := by
    apply mem_span_of_iInf_ker_le_ker
    intro v hv
    have hv' : ∀ i, ∑ j, (rows i j : ℚ) * v j = 0 := by
      intro i
      have := (Submodule.mem_iInf _).mp hv i
      rw [LinearMap.mem_ker, hdl] at this
      exact this
    rw [LinearMap.mem_ker, hdl]
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
    choose w hw using hb
    have hw' : ∀ j, (w j : ℚ) = (b : ℤ) * v j := by
      intro j
      have := hw j
      simpa [zsmul_eq_mul] using this
    have hsys : ∀ i, ∑ j, rows i j * w j = 0 := by
      intro i
      apply Int.cast_injective (α := ℚ)
      push_cast
      simp_rw [hw']
      have : ∑ j, (rows i j : ℚ) * ((b : ℤ) * v j) = (b : ℤ) * ∑ j, (rows i j : ℚ) * v j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hv' i, mul_zero]
    have hcw := h w hsys
    have : ∑ j, (c j : ℚ) * (w j : ℚ) = 0 := by exact_mod_cast hcw
    simp_rw [hw'] at this
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have h2 : (b : ℚ) * ∑ j, (c j : ℚ) * v j = 0 := by
      rw [Finset.mul_sum]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by ring
    exact (mul_eq_zero.mp h2).resolve_left hb0
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hspan
  have hcoef : ∀ j, (c j : ℚ) = ∑ i, q i * (rows i j : ℚ) := by
    intro j
    have := congrArg (fun f => f (Pi.single j 1)) hq
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hdl, smul_eq_mul] at this
    simpa [Pi.single_apply] using this.symm
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose n hn using hb
  have hn' : ∀ i, (n i : ℚ) = (b : ℤ) * q i := by
    intro i
    have := hn i
    simpa [zsmul_eq_mul] using this
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, n, fun j => ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  simp_rw [hn']
  rw [hcoef j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- reduction of the identity of `exists_int_combination` modulo any commutative ring. -/
theorem int_combination_apply {ι N R : Type*} [Fintype ι] [Fintype N] [CommRing R]
    (rows : ι → N → ℤ) (c : N → ℤ) (D : ℤ) (n : ι → ℤ)
    (hid : ∀ j, D * c j = ∑ i, n i * rows i j) (v : N → R)
    (hv : ∀ i, ∑ j, (rows i j : R) * v j = 0) :
    (D : R) * ∑ j, (c j : R) * v j = 0 := by
  calc (D : R) * ∑ j, (c j : R) * v j
      = ∑ j, ((D * c j : ℤ) : R) * v j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    _ = ∑ j, ∑ i, (n i : R) * ((rows i j : R) * v j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hid j]; push_cast; rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, (n i : R) * ∑ j, (rows i j : R) * v j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = 0 := by simp [hv]

/-- indicator vector of a coordinate. -/
def indVec {N : Type*} [DecidableEq N] (n₀ : N) : N → ℤ := fun n => if n = n₀ then 1 else 0

theorem sum_indVec_mul {N R : Type*} [Fintype N] [DecidableEq N] [CommRing R] (n₀ : N)
    (v : N → R) : ∑ j, ((indVec n₀ j : ℤ) : R) * v j = v n₀ := by
  simp [indVec]

/-- the equation vector of a support point `(x, y, z)` on the coordinates `X ⊕ Y ⊕ Z`. -/
def rowVec {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] (s : X × Y × Z) :
    X ⊕ Y ⊕ Z → ℤ :=
  fun n => indVec (Sum.inl s.1 : X ⊕ Y ⊕ Z) n + indVec (Sum.inr (Sum.inl s.2.1) : X ⊕ Y ⊕ Z) n +
    indVec (Sum.inr (Sum.inr s.2.2) : X ⊕ Y ⊕ Z) n

theorem sum_rowVec_mul {X Y Z R : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] [CommRing R] (s : X × Y × Z) (v : X ⊕ Y ⊕ Z → R) :
    ∑ j, ((rowVec s j : ℤ) : R) * v j =
      v (Sum.inl s.1) + v (Sum.inr (Sum.inl s.2.1)) + v (Sum.inr (Sum.inr s.2.2)) := by
  simp only [rowVec, Int.cast_add, add_mul, Finset.sum_add_distrib, sum_indVec_mul]

/-- two coordinates of the same factor. -/
def SameKind {X Y Z : Type*} : (X ⊕ Y ⊕ Z) → (X ⊕ Y ⊕ Z) → Prop
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => True
  | _, _ => False

/-- all components of an embedding vector are constant on each factor. -/
theorem sameKind_eq_of_const {X Y Z H : Type*} (σ : X → H) (γ : Y → H) (φ : Z → H)
    (h : (∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b))
    (n n' : X ⊕ Y ⊕ Z) (hk : SameKind n n') :
    Sum.elim σ (Sum.elim γ φ) n = Sum.elim σ (Sum.elim γ φ) n' := by
  rcases n with a | b | c <;> rcases n' with a' | b' | c' <;> simp only [SameKind] at hk <;>
    first | exact absurd hk not_false | simp [h.1 a a'] | skip
  · simp [h.2.1 b b']
  · simp [h.2.2 c c']

/-- Per-instance bound: a support `S ⊆ X × Y × Z` with no non-trivial embedding into `ℤ` has none
into `ℤ/p` for all large primes `p`. -/
theorem exists_prime_bound_embedding (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (S : Set (X × Y × Z)) (hS : ¬ AdmitsEmbeddingInto3 S ℤ) :
    ∃ r : ℕ, ∀ p : ℕ, p.Prime → r < p → ¬ AdmitsEmbeddingInto3 S (ZMod p) := by
  classical
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
  refine ⟨Finset.univ.sup fun q => (D q).natAbs, fun p hp hpr hadm => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, γ, φ, hemb, hnt⟩ := (admitsEmbeddingInto3_iff S (ZMod p)).mp hadm
  rw [isEmbedding3_iff] at hemb
  rw [isNontrivialEmbedding3_iff] at hnt
  apply hnt
  let v : N → ZMod p := Sum.elim σ (Sum.elim γ φ)
  have hv : ∀ i : S, ∑ j, ((rows i j : ℤ) : ZMod p) * v j = 0 := by
    intro i
    simp only [rows]
    rw [sum_rowVec_mul]
    exact hemb i.1 i.2
  have step : ∀ n n' : N, SameKind n n' → v n = v n' := by
    intro n n' hk
    have hDne : ((D (n, n') : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      have h1 : (D (n, n')).natAbs ≤ Finset.univ.sup fun q => (D q).natAbs :=
        Finset.le_sup (f := fun q => (D q).natAbs) (Finset.mem_univ (n, n'))
      have h3 : (D (n, n')).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD _)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) (Int.natCast_dvd.mp h0)
      omega
    have := int_combination_apply rows (fun j => indVec n j - indVec n' j) (D (n, n')) (nn (n, n') hk)
      (hnn (n, n') hk) v hv
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sum_indVec_mul] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hDne)
  refine ⟨fun a b => step (Sum.inl a) (Sum.inl b) trivial,
    fun a b => step (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) trivial,
    fun a b => step (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) trivial⟩

end BoundP

/-! ### Paper IV definition-level and lemma statements -/

/-- Paper IV `definition-linear-reduction` (redundant clause "G ≤ H" dropped). -/
def IsLinearReduction {X Y Z : Type*} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (σ : X → G) (γ : Y → G) (φ : Z → G) (σ' : X → H) (γ' : Y → H) (φ' : Z → H) : Prop :=
  ∃ m₁ m₂ m₃ : G →+ H, Function.Injective m₁ ∧ Function.Injective m₂ ∧ Function.Injective m₃ ∧
    (∀ x, σ' x = m₁ (σ x)) ∧ (∀ y, γ' y = m₂ (γ y)) ∧ (∀ z, φ' z = m₃ (φ z))

/-- Paper IV `claim-affine-shift-zero-in-image`. -/
theorem exists_shift_zero_in_image {X Y Z : Type u} {S : Set (X × Y × Z)} (hS : S.Nonempty)
    {H : Type*} [AddCommGroup H] {σ : X → H} {γ : Y → H} {φ : Z → H}
    (h : IsEmbedding3 S σ γ φ) :
    ∃ a b c : H, a + b + c = 0 ∧
      IsEmbedding3 S (fun x => σ x - a) (fun y => γ y - b) (fun z => φ z - c) ∧
      (∃ x, σ x - a = 0) ∧ (∃ y, γ y - b = 0) ∧ (∃ z, φ z - c = 0) ∧
      (IsNontrivialEmbedding3 (fun x => σ x - a) (fun y => γ y - b) (fun z => φ z - c) ↔
        IsNontrivialEmbedding3 σ γ φ) := by
  obtain ⟨⟨x₀, y₀, z₀⟩, hp⟩ := hS
  rw [isEmbedding3_iff] at h
  have h0 := h _ hp
  refine ⟨σ x₀, γ y₀, φ z₀, h0, ?_, ⟨x₀, sub_self _⟩, ⟨y₀, sub_self _⟩, ⟨z₀, sub_self _⟩, ?_⟩
  · rw [isEmbedding3_iff]
    intro p hp'
    have := h p hp'
    have e : (σ p.1 - σ x₀) + (γ p.2.1 - γ y₀) + (φ p.2.2 - φ z₀) =
        (σ p.1 + γ p.2.1 + φ p.2.2) - (σ x₀ + γ y₀ + φ z₀) := by abel
    show (σ p.1 - σ x₀) + (γ p.2.1 - γ y₀) + (φ p.2.2 - φ z₀) = 0
    rw [e, this, h0, sub_zero]
  · rw [isNontrivialEmbedding3_iff, isNontrivialEmbedding3_iff]
    simp only [sub_left_inj]


/-- Admitting a non-trivial embedding is invariant under relabelling the alphabets (one direction). -/
theorem admitsEmbeddingInto3_map {X Y Z X' Y' Z' : Type u} (eX : X ≃ X') (eY : Y ≃ Y')
    (eZ : Z ≃ Z') (S : Set (X × Y × Z)) (H : Type*) [AddCommGroup H]
    (h : AdmitsEmbeddingInto3 S H) :
    AdmitsEmbeddingInto3 ((fun p : X × Y × Z => (eX p.1, eY p.2.1, eZ p.2.2)) '' S) H := by
  rw [admitsEmbeddingInto3_iff] at h ⊢
  obtain ⟨σ, γ, φ, he, hn⟩ := h
  refine ⟨fun x => σ (eX.symm x), fun y => γ (eY.symm y), fun z => φ (eZ.symm z), ?_, ?_⟩
  · rw [isEmbedding3_iff] at he ⊢
    rintro _ ⟨p, hp, rfl⟩
    simpa using he p hp
  · rw [isNontrivialEmbedding3_iff] at hn ⊢
    rintro ⟨h1, h2, h3⟩
    apply hn
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
    · simpa using h1 (eX a) (eX b)
    · simpa using h2 (eY a) (eY b)
    · simpa using h3 (eZ a) (eZ b)

theorem admitsEmbeddingInto3_map_iff {X Y Z X' Y' Z' : Type u} (eX : X ≃ X') (eY : Y ≃ Y')
    (eZ : Z ≃ Z') (S : Set (X × Y × Z)) (H : Type*) [AddCommGroup H] :
    AdmitsEmbeddingInto3 ((fun p : X × Y × Z => (eX p.1, eY p.2.1, eZ p.2.2)) '' S) H ↔
      AdmitsEmbeddingInto3 S H := by
  refine ⟨fun h => ?_, admitsEmbeddingInto3_map eX eY eZ S H⟩
  have := admitsEmbeddingInto3_map eX.symm eY.symm eZ.symm _ H h
  rw [Set.image_image] at this
  simpa using this

/-- Paper IV `lem:bound-p-in-embed` (Lemma 3.2); `r` depends only on `m`. -/
theorem bound_p_in_embed (m : ℕ) :
    ∃ r : ℕ, ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z],
      Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
      ∀ μ : FinProb (X × Y × Z), ¬ AdmitsEmbeddingInto3 μ.support ℤ →
        ∀ p : ℕ, p.Prime → r < p → ¬ AdmitsEmbeddingInto3 μ.support (ZMod p) := by
  classical
  let ι := Σ abc : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
    Set (Fin abc.1.val × Fin abc.2.1.val × Fin abc.2.2.val)
  have hr : ∀ q : ι, ∃ r : ℕ, ¬ AdmitsEmbeddingInto3 q.2 ℤ →
      ∀ p : ℕ, p.Prime → r < p → ¬ AdmitsEmbeddingInto3 q.2 (ZMod p) := by
    intro q
    by_cases hq : AdmitsEmbeddingInto3 q.2 ℤ
    · exact ⟨0, fun h => absurd hq h⟩
    · obtain ⟨r, hr⟩ := exists_prime_bound_embedding _ _ _ q.2 hq
      exact ⟨r, fun _ => hr⟩
  choose r hr using hr
  have : Finite ι := inferInstance
  have := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup r, ?_⟩
  intro X Y Z _ _ _ hX hY hZ μ hμ p hp hpr hadm
  let eX := Fintype.equivFin X
  let eY := Fintype.equivFin Y
  let eZ := Fintype.equivFin Z
  let q : ι := ⟨(⟨Fintype.card X, Nat.lt_succ_of_le hX⟩, ⟨Fintype.card Y, Nat.lt_succ_of_le hY⟩,
      ⟨Fintype.card Z, Nat.lt_succ_of_le hZ⟩),
    (fun t : X × Y × Z => (eX t.1, eY t.2.1, eZ t.2.2)) '' μ.support⟩
  have hqr : r q ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ q)
  have h1 : ¬ AdmitsEmbeddingInto3 q.2 ℤ := fun h =>
    hμ ((admitsEmbeddingInto3_map_iff eX eY eZ μ.support ℤ).mp h)
  exact hr q h1 p hp (lt_of_le_of_lt hqr hpr)
    ((admitsEmbeddingInto3_map_iff eX eY eZ μ.support (ZMod p)).mpr hadm)

/-- `lem:bound-p-in-embed` in the literal order of the source: for alphabets of size at most `m`
there is `r` such that, for every `μ`, every prime `p > r` ... -/
theorem bound_p_in_embed_literal (m : ℕ) (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (hX : Fintype.card X ≤ m) (hY : Fintype.card Y ≤ m) (hZ : Fintype.card Z ≤ m) :
    ∃ r : ℕ, ∀ μ : FinProb (X × Y × Z), ¬ AdmitsEmbeddingInto3 μ.support ℤ →
      ∀ p : ℕ, p.Prime → r < p → ¬ AdmitsEmbeddingInto3 μ.support (ZMod p) := by
  obtain ⟨r, hr⟩ := bound_p_in_embed m
  exact ⟨r, fun μ => hr X Y Z hX hY hZ μ⟩

/-! ### The `k`-ary statements -/
section P1
variable {k : ℕ} {A : Fin k → Type*}

/-- The paper's `d-abelianEmbedding#full-marginal-support`, part 1. -/
theorem full_marginal_support [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (μ : FinProb (∀ i, A i)) (h : NoNontrivialAbelianEmbeddingPi μ.support) (i : Fin k) (a : A i) :
    0 < (μ.marginalPi i).prob a := by
  by_contra hneg
  have hnn := (μ.marginalPi i).nonneg a
  have h0 : (μ.marginalPi i).prob a = 0 := le_antisymm (not_lt.mp hneg) hnn
  have hz : ∀ t : ∀ j, A j, t i = a → μ.prob t = 0 := by
    intro t ht
    have : ∑ t' with t' i = a, μ.prob t' = 0 := h0
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun t' _ => μ.nonneg t')).mp this
    exact hh t (by simp [ht])
  -- another symbol of positive mass
  obtain ⟨b, hb⟩ : ∃ b, (μ.marginalPi i).prob b ≠ 0 := by
    by_contra hall
    push Not at hall
    have := (μ.marginalPi i).sum_eq_one
    simp [hall] at this
  have hba : b ≠ a := by
    rintro rfl; exact hb h0
  classical
  let σ : ∀ j, A j → ℤ :=
    Function.update (fun _ _ => (0 : ℤ)) i (fun x => if x = a then 1 else 0)
  have hemb : ∀ t ∈ μ.support, ∑ j, σ j (t j) = 0 := by
    intro t ht
    rw [Finset.sum_eq_single i]
    · simp only [σ, Function.update_self]
      have : t i ≠ a := fun hta => ht (hz t hta)
      simp [this]
    · intro j _ hj
      simp [σ, Function.update_of_ne hj]
    · simp
  have := h ℤ σ hemb i a b
  simp [σ, hba] at this

/-- same node, `μ_i(a) ≥ γ` (listed in the node's SOURCE_CONCLUSION). -/
theorem marginal_atom_ge [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (μ : FinProb (∀ i, A i)) (h : NoNontrivialAbelianEmbeddingPi μ.support) {γ : ℝ}
    (hatom : ∀ a ∈ μ.support, γ ≤ μ.prob a) (i : Fin k) (a : A i) :
    γ ≤ (μ.marginalPi i).prob a := by
  have hpos := full_marginal_support μ h i a
  have hpos' : 0 < ∑ t with t i = a, μ.prob t := hpos
  obtain ⟨t, ht, htp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos'.ne'
  have hts : t ∈ μ.support := htp
  calc γ ≤ μ.prob t := hatom t hts
    _ ≤ ∑ t' with t' i = a, μ.prob t' :=
        Finset.single_le_sum (f := μ.prob) (fun t' _ => μ.nonneg t') ht

/-- same node, `|A_i| ≤ 1/γ`. -/
theorem card_le_inv_of_atom_bound [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (μ : FinProb (∀ i, A i)) (h : NoNontrivialAbelianEmbeddingPi μ.support) {γ : ℝ} (hγ : 0 < γ)
    (hatom : ∀ a ∈ μ.support, γ ≤ μ.prob a) (i : Fin k) :
    (Fintype.card (A i) : ℝ) ≤ 1 / γ := by
  rw [le_div_iff₀ hγ]
  have h1 : ∑ _a : A i, γ ≤ ∑ a : A i, (μ.marginalPi i).prob a :=
    Finset.sum_le_sum fun a _ => marginal_atom_ge μ h hatom i a
  rw [(μ.marginalPi i).sum_eq_one] at h1
  simpa [mul_comm] using h1

/-- CSP_7 `obs:sub`, set form (the support of a restriction is the image of the support). -/
theorem noNontrivialAbelianEmbeddingPi_image_succAbove {k : ℕ} {A : Fin (k + 1) → Type*}
    (j : Fin (k + 1)) (S : Set (∀ i, A i)) (h : NoNontrivialAbelianEmbeddingPi S) :
    NoNontrivialAbelianEmbeddingPi
      ((fun (t : ∀ i, A i) (i : Fin k) => t (j.succAbove i)) '' S) := by
  intro G _ σ hσ l x y
  let σ' : ∀ i, A i → G := Fin.insertNth j (fun _ => 0) σ
  have hemb : ∀ t ∈ S, ∑ i, σ' i (t i) = 0 := by
    intro t ht
    rw [Fin.sum_univ_succAbove _ j]
    simp only [σ', Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_add]
    exact hσ _ ⟨t, ht, rfl⟩
  have := h G σ' hemb (j.succAbove l) x y
  simpa [σ'] using this

/-- CSP_7 `obs:pc` (and CSP_6 `definition-pairwise-connected` via `k = 3`). -/
theorem pairwiseConnected_of_noNontrivialAbelianEmbeddingPi [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] (μ : FinProb (∀ i, A i))
    (h : NoNontrivialAbelianEmbeddingPi μ.support) : PairwiseConnectedDist μ := by
  classical
  intro i j hij
  obtain ⟨t₀, ht₀⟩ : ∃ t, t ∈ μ.support := by
    by_contra hall
    push Not at hall
    have h0 : ∀ t, μ.prob t = 0 := fun t => by
      have := hall t
      simpa [FinProb.support] using this
    have := μ.sum_eq_one
    simp [h0] at this
  have hadj : ∀ t ∈ μ.support,
      (pairGraph μ.support i j).Adj (Sum.inl (t i)) (Sum.inr (t j)) := by
    intro t ht
    simp only [pairGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨_, _, rfl, rfl, t, ht, rfl, rfl⟩⟩
  have : Nonempty (A i ⊕ A j) := ⟨Sum.inl (t₀ i)⟩
  refine ⟨?_⟩
  by_contra hpc
  unfold SimpleGraph.Preconnected at hpc
  push Not at hpc
  obtain ⟨u, v, huv⟩ := hpc
  let C : A i ⊕ A j → Prop := fun w => (pairGraph μ.support i j).Reachable u w
  have hC : ∀ t ∈ μ.support, (C (Sum.inl (t i)) ↔ C (Sum.inr (t j))) := fun t ht =>
    ⟨fun h => h.trans (hadj t ht).reachable, fun h => h.trans (hadj t ht).reachable.symm⟩
  let σ : ∀ l, A l → ℤ :=
    Function.update
      (Function.update (fun _ _ => (0 : ℤ)) i (fun x => if C (Sum.inl x) then 1 else 0))
      j (fun y => if C (Sum.inr y) then -1 else 0)
  have hemb : ∀ t ∈ μ.support, ∑ l, σ l (t l) = 0 := by
    intro t ht
    rw [Finset.sum_eq_add i j hij]
    · simp only [σ, Function.update_of_ne hij, Function.update_self]
      by_cases hc : C (Sum.inl (t i))
      · have := (hC t ht).mp hc
        simp [hc, this]
      · have : ¬ C (Sum.inr (t j)) := fun h' => hc ((hC t ht).mpr h')
        simp [hc, this]
    · intro l _ hl
      simp [σ, Function.update_of_ne hl.2, Function.update_of_ne hl.1]
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have hall := h ℤ σ hemb
  have hi : ∀ x y, (if C (Sum.inl x) then (1 : ℤ) else 0) = if C (Sum.inl y) then 1 else 0 := by
    intro x y
    have := hall i x y
    simpa [σ, Function.update_of_ne hij] using this
  have hj : ∀ x y, (if C (Sum.inr x) then (-1 : ℤ) else 0) = if C (Sum.inr y) then -1 else 0 := by
    intro x y
    exact hall j x y |> fun this => by simpa [σ] using this
  by_cases hc : C (Sum.inl (t₀ i))
  · have hc' := (hC t₀ ht₀).mp hc
    have hv : C v := by
      rcases v with x | y
      · by_contra hx
        have := hi x (t₀ i)
        simp [hx, hc] at this
      · by_contra hy
        have := hj y (t₀ j)
        simp [hy, hc'] at this
    exact huv hv
  · have hc' : ¬ C (Sum.inr (t₀ j)) := fun h' => hc ((hC t₀ ht₀).mpr h')
    have hu : C u := SimpleGraph.Reachable.refl u
    rcases u with x | y
    · have := hi x (t₀ i)
      simp [hu, hc] at this
    · have := hj y (t₀ j)
      simp [hu, hc'] at this
end P1

end TrackB
end RestrictedPolynomials
end
