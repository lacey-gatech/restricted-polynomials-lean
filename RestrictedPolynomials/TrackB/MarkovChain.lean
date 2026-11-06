module

public import RestrictedPolynomials.FinProb
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

open Finset
noncomputable section
/-!
# Track B: `L²` inner product, Markov chain operator, Lemma 2.7

Source: paper IV (`writeup_stability.tex`), §2: the `L²` inner product
(l. 1030-1037), the Markov chain operator and connectedness (l. 1148-1156), and
Lemma 2.7 `lem:mossel_MC` (l. 1222-1276). Paper IV items `definition-l2-inner-product`,
`definition-markov-chain-operator`, `lem:mossel-MC` (with its sub-steps
`self-adjointness-gap`, `dirichlet-form`, `spectral-gap-upper-bound`,
`eigenvalue-lower-bound` absorbed into the helper lemmas below).

Proof route: a reversible chain with full support is conjugate to the Hermitian matrix
`D^{1/2} T D^{-1/2}`, which gives real eigenvalues and an `L²(μ)`-orthonormal eigenbasis
(`spectral_data`). The Dirichlet identity then gives all three items.
-/

namespace RestrictedPolynomials

namespace FinProb
variable {α : Type*} [Fintype α]
/-- paper IV `definition-l2-inner-product`: `⟨f,g⟩ = 𝔼 f · conj g` (the shape used in frozen `cstab`);
source: paper IV (`writeup_stability.tex`) l. 1030-1037. -/
def cinner (π : FinProb α) (f g : α → ℂ) : ℂ := π.cexpect fun a => f a * star (g a)
end FinProb

namespace TrackB

/-- A finite Markov chain (row-stochastic matrix). -/
structure StochMat (α : Type*) [Fintype α] where
  prob : α → α → ℝ
  nonneg : ∀ a b, 0 ≤ prob a b
  row_sum : ∀ a, ∑ b, prob a b = 1

namespace StochMat
variable {α : Type*} [Fintype α] (T : StochMat α)

/-- paper IV `definition-markov-chain-operator` (paper IV l. 1148-1156): `T f(a) = 𝔼_{b ∼ T a} f(b)`. -/
def apply (f : α → ℂ) (a : α) : ℂ := ∑ b, (T.prob a b : ℂ) * f b
/-- `μ` is a stationary distribution of `T`. -/
def IsStationary (μ : FinProb α) : Prop := ∀ b, ∑ a, μ.prob a * T.prob a b = μ.prob b
/-- reversibility (detailed balance). Paper IV `lem:mossel-MC` uses it without stating it (step
`self-adjointness-gap`), so the lemmas below take it as a hypothesis; it is proved for every chain
they are applied to. -/
def IsReversible (μ : FinProb α) : Prop := ∀ a b, μ.prob a * T.prob a b = μ.prob b * T.prob b a
/-- transition graph: an edge whenever either direction has positive probability -/
def graph : SimpleGraph α := SimpleGraph.fromRel fun a b => 0 < T.prob a b
/-- `T` is connected: its transition graph is connected (paper IV l. 1152-1154). -/
def IsConnectedChain : Prop := T.graph.Connected
/-- number of connected components `k` -/
def numComponents : ℕ := Nat.card T.graph.ConnectedComponent
/-- tensor power `T^{⊗ι}` -/
def pi (ι : Type*) [Fintype ι] [DecidableEq ι] : StochMat (ι → α) where
  prob x y := ∏ i, T.prob (x i) (y i)
  nonneg _ _ := prod_nonneg fun i _ => T.nonneg _ _
  row_sum x := by
    rw [← Fintype.prod_sum (fun i b => T.prob (x i) b)]
    simp [T.row_sum]
/-- the eigenvalues of `T` with multiplicity (roots of the characteristic polynomial over `ℂ`) -/
def eigenvalues [DecidableEq α] : Multiset ℂ :=
  (Matrix.of fun a b => (T.prob a b : ℂ)).charpoly.roots
end StochMat

section Aux

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma norm_sub_sq_eq (x y : ℂ) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * (starRingEnd ℂ) y).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

omit [DecidableEq S] in
/-- Dirichlet-form identity for an eigenfunction of a stationary chain. -/
lemma dirichlet_eigen (T : StochMat S) (μ : FinProb S) (hs : T.IsStationary μ)
    (g : S → ℂ) (lam : ℝ) (hg : ∀ a, ∑ b, (T.prob a b : ℂ) * g b = lam * g a) :
    ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 =
      2 * (1 - lam) * ∑ a, μ.prob a * ‖g a‖ ^ 2 := by
  have h1 : ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a‖ ^ 2 = ∑ a, μ.prob a * ‖g a‖ ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, T.row_sum, mul_one]
  have h2 : ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g b‖ ^ 2 = ∑ a, μ.prob a * ‖g a‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, hs b]
  have h3 : ∑ a, ∑ b, μ.prob a * T.prob a b * (g a * (starRingEnd ℂ) (g b)).re =
      lam * ∑ a, μ.prob a * ‖g a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : ∑ b, μ.prob a * T.prob a b * (g a * (starRingEnd ℂ) (g b)).re =
        μ.prob a * (g a * (starRingEnd ℂ) (∑ b, (T.prob a b : ℂ) * g b)).re := by
      rw [map_sum, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, Complex.conj_ofReal,
        show g a * ((T.prob a b : ℂ) * (starRingEnd ℂ) (g b)) =
          (T.prob a b : ℂ) * (g a * (starRingEnd ℂ) (g b)) by ring, Complex.re_ofReal_mul]
      ring
    rw [this, hg a]
    have : (g a * (starRingEnd ℂ) ((lam : ℂ) * g a)).re = lam * ‖g a‖ ^ 2 := by
      rw [map_mul, Complex.conj_ofReal, show g a * ((lam : ℂ) * (starRingEnd ℂ) (g a)) =
        (lam : ℂ) * (g a * (starRingEnd ℂ) (g a)) by ring, Complex.re_ofReal_mul,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [this]; ring
  calc ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2
      = ∑ a, ∑ b, (μ.prob a * T.prob a b * ‖g a‖ ^ 2 + μ.prob a * T.prob a b * ‖g b‖ ^ 2
          - 2 * (μ.prob a * T.prob a b * (g a * (starRingEnd ℂ) (g b)).re)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [norm_sub_sq_eq]; ring
    _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3]
        ring

omit [DecidableEq S] in
lemma graph_adj_iff (T : StochMat S) (a b : S) :
    T.graph.Adj a b ↔ a ≠ b ∧ (0 < T.prob a b ∨ 0 < T.prob b a) := by
  simp [StochMat.graph, SimpleGraph.fromRel_adj]

omit [DecidableEq S] in
/-- A harmonic function of a stationary chain with full support is constant on components. -/
lemma harmonic_const (T : StochMat S) (μ : FinProb S) (hμ : ∀ a, 0 < μ.prob a)
    (hs : T.IsStationary μ) (g : S → ℂ) (hg : ∀ a, ∑ b, (T.prob a b : ℂ) * g b = g a) :
    ∀ a b, T.graph.Reachable a b → g a = g b := by
  have hd := dirichlet_eigen T μ hs g 1 (by simpa using hg)
  rw [show (2 : ℝ) * (1 - 1) * ∑ a, μ.prob a * ‖g a‖ ^ 2 = 0 by ring] at hd
  have h0 : ∀ a b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 = 0 := by
    have hnn : ∀ a ∈ (Finset.univ : Finset S),
        0 ≤ ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 := fun a _ =>
      Finset.sum_nonneg fun b _ => by
        have := μ.nonneg a; have := T.nonneg a b; positivity
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hd
    intro a b
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by
      have := μ.nonneg a; have := T.nonneg a b; positivity)).1 (h1 a (Finset.mem_univ a)) b
      (Finset.mem_univ b)
    exact h2
  have hadj : ∀ a b, T.graph.Adj a b → g a = g b := by
    intro a b hab
    have key : ∀ a b, 0 < T.prob a b → g a = g b := by
      intro a b hp
      have := h0 a b
      have hμa := hμ a
      have : ‖g a - g b‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (mul_pos hμa hp).ne'
        · exact h
      have := sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this))
      exact this
    rcases (graph_adj_iff T a b).1 hab |>.2 with h | h
    · exact key a b h
    · exact (key b a h).symm
  intro a b hab
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hadj _ _ h).trans ih

/-- Functions of the component are harmonic. -/
lemma comp_harmonic (T : StochMat S) (h : T.graph.ConnectedComponent → ℂ) (a : S) :
    ∑ b, (T.prob a b : ℂ) * h (T.graph.connectedComponentMk b) =
      h (T.graph.connectedComponentMk a) := by
  have : ∀ b, (T.prob a b : ℂ) * h (T.graph.connectedComponentMk b) =
      (T.prob a b : ℂ) * h (T.graph.connectedComponentMk a) := by
    intro b
    by_cases hp : T.prob a b = 0
    · simp [hp]
    · congr 2
      by_cases hab : a = b
      · rw [hab]
      · have hpos : 0 < T.prob a b := lt_of_le_of_ne (T.nonneg a b) (Ne.symm hp)
        have : T.graph.Adj a b := (graph_adj_iff T a b).2 ⟨hab, Or.inl hpos⟩
        exact ((SimpleGraph.ConnectedComponent.eq).2 this.reachable).symm
  rw [Finset.sum_congr rfl fun b _ => this b, ← Finset.sum_mul, ← Complex.ofReal_sum,
    T.row_sum]
  simp

/-- The eigenspace of `T` for the eigenvalue `1`. -/
def harmSpace (T : StochMat S) : Submodule ℂ (S → ℂ) :=
  Module.End.eigenspace (Matrix.toLin' (Matrix.of fun a b => (T.prob a b : ℂ))) 1

lemma mem_harmSpace (T : StochMat S) (g : S → ℂ) :
    g ∈ harmSpace T ↔ ∀ a, ∑ b, (T.prob a b : ℂ) * g b = g a := by
  simp only [harmSpace, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, one_smul]
  constructor
  · intro h a
    have := congrFun h a
    simpa [Matrix.mulVec, dotProduct] using this
  · intro h
    funext a
    simpa [Matrix.mulVec, dotProduct] using h a

lemma numComponents_le_finrank (T : StochMat S) :
    T.numComponents ≤ Module.finrank ℂ (harmSpace T) := by
  classical
  have : Fintype T.graph.ConnectedComponent := Fintype.ofFinite _
  let f : (T.graph.ConnectedComponent → ℂ) →ₗ[ℂ] harmSpace T :=
    LinearMap.codRestrict (harmSpace T) (LinearMap.funLeft ℂ ℂ T.graph.connectedComponentMk)
      (fun h => (mem_harmSpace T _).2 fun a => comp_harmonic T h a)
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact LinearMap.funLeft_injective_of_surjective ℂ ℂ _
      (fun c => c.ind fun v => ⟨v, rfl⟩) this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [StochMat.numComponents, Module.finrank_pi, Nat.card_eq_fintype_card] using this

lemma finrank_le_numComponents (T : StochMat S) (μ : FinProb S) (hμ : ∀ a, 0 < μ.prob a)
    (hs : T.IsStationary μ) :
    Module.finrank ℂ (harmSpace T) ≤ T.numComponents := by
  classical
  have : Fintype T.graph.ConnectedComponent := Fintype.ofFinite _
  let f : harmSpace T →ₗ[ℂ] (T.graph.ConnectedComponent → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun c : T.graph.ConnectedComponent => Quot.out c)) ∘ₗ
      (harmSpace T).subtype
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hd : (x.1 - y.1) ∈ harmSpace T := Submodule.sub_mem _ x.2 y.2
    have hc := harmonic_const T μ hμ hs _ ((mem_harmSpace T _).1 hd)
    funext a
    have hz : ∀ v : S, (x.1 - y.1) v = 0 := by
      intro v
      have hrep : T.graph.Reachable v (Quot.out (T.graph.connectedComponentMk v)) :=
        (SimpleGraph.ConnectedComponent.eq).1 (Quot.out_eq _).symm
      have := hc _ _ hrep
      have h2 : (x.1 - y.1) (Quot.out (T.graph.connectedComponentMk v)) = 0 := by
        have := congrFun hxy (T.graph.connectedComponentMk v)
        simp [f] at this
        simp [this]
      rw [this, h2]
    have := hz a
    simpa [sub_eq_zero] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [StochMat.numComponents, Module.finrank_pi, Nat.card_eq_fintype_card] using this

/-- Spectral data of a reversible chain with full support: real eigenvalues `lam j` together with
an `L²(μ)`-orthonormal family of eigenfunctions `g j`, such that the eigenvalue multiset of `T`
is exactly `{lam j}`. This is the (weighted) adapter, via the symmetric matrix
`D^{1/2} T D^{-1/2}`, that absorbs `lem:mossel-MC#self-adjointness-gap`. -/
lemma spectral_data (T : StochMat S) (μ : FinProb S) (hμ : ∀ a, 0 < μ.prob a)
    (hr : T.IsReversible μ) :
    ∃ (lam : S → ℝ) (g : S → S → ℂ),
      T.eigenvalues = Finset.univ.val.map (fun j => (lam j : ℂ)) ∧
      (∀ j a, ∑ b, (T.prob a b : ℂ) * g j b = lam j * g j a) ∧
      (∀ i j, ∑ a, (μ.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) = if i = j then 1 else 0) := by
  classical
  set r : S → ℝ := fun a => Real.sqrt (μ.prob a) with hrdef
  have hrpos : ∀ a, 0 < r a := fun a => Real.sqrt_pos.2 (hμ a)
  have hrsq : ∀ a, r a * r a = μ.prob a := fun a => Real.mul_self_sqrt (μ.nonneg a)
  let B : Matrix S S ℂ := Matrix.of fun a b => ((r a * T.prob a b / r b : ℝ) : ℂ)
  let A : Matrix S S ℂ := Matrix.of fun a b => (T.prob a b : ℂ)
  have hB : B.IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, B, Matrix.of_apply, Complex.star_def,
      Complex.conj_ofReal]
    congr 1
    have h := hr b a
    rw [← hrsq a, ← hrsq b] at h
    have := hrpos a; have := hrpos b
    field_simp
    linarith
  have hBA : B = Matrix.diagonal (fun a => ((r a : ℝ) : ℂ)) *
      (A * Matrix.diagonal (fun a => ((r a : ℝ) : ℂ)⁻¹)) := by
    ext a b
    simp only [B, A, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, ite_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    push_cast
    ring
  have hcp : B.charpoly = A.charpoly := by
    rw [hBA, Matrix.charpoly_mul_comm, mul_assoc, Matrix.diagonal_mul_diagonal]
    have : (fun i => ((r i : ℝ) : ℂ)⁻¹ * (r i : ℂ)) = fun _ => 1 := by
      funext i
      have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hrpos i).ne'
      field_simp
    rw [this]
    simp
  refine ⟨hB.eigenvalues, fun j a => (hB.eigenvectorBasis j) a / (r a : ℂ), ?_, ?_, ?_⟩
  · have := hB.roots_charpoly_eq_eigenvalues
    rw [hcp] at this
    show A.charpoly.roots = _
    rw [this]
    simp
  · intro j a
    have hev := congrFun (hB.mulVec_eigenvectorBasis j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, B, Matrix.of_apply] at hev
    have hra : (r a : ℂ) ≠ 0 := by exact_mod_cast (hrpos a).ne'
    have : ∑ b, (T.prob a b : ℂ) * ((hB.eigenvectorBasis j) b / (r b : ℂ)) =
        (∑ x, ((r a * T.prob a x / r x : ℝ) : ℂ) * (hB.eigenvectorBasis j) x) / (r a : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hrb : (r b : ℂ) ≠ 0 := by exact_mod_cast (hrpos b).ne'
      push_cast
      field_simp
    rw [this, hev]
    rw [Complex.real_smul]
    ring
  · intro i j
    have h := (orthonormal_iff_ite.1 hB.eigenvectorBasis.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [dotProduct, Pi.star_apply, RCLike.star_def] at h
    have hij : (if j = i then (1 : ℂ) else 0) = if i = j then 1 else 0 := by
      simp [eq_comm]
    rw [hij] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hra : (r a : ℂ) ≠ 0 := by exact_mod_cast (hrpos a).ne'
    rw [← hrsq a]
    push_cast
    simp only [map_div₀, Complex.conj_ofReal]
    field_simp

omit [DecidableEq S] in
lemma walk_diff_le (T : StochMat S) (g : S → ℂ) (E : ℝ)
    (hE : ∀ a b, T.graph.Adj a b → ‖g a - g b‖ ≤ E) {u v : S} (p : T.graph.Walk u v) :
    ‖g u - g v‖ ≤ p.length * E := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h1 := hE a b h
    calc ‖g a - g c‖ = ‖(g a - g b) + (g b - g c)‖ := by ring_nf
      _ ≤ ‖g a - g b‖ + ‖g b - g c‖ := norm_add_le _ _
      _ ≤ E + (p.length * E) := add_le_add h1 ih
      _ = ((p.cons h).length : ℝ) * E := by simp [SimpleGraph.Walk.length_cons]; ring

omit [DecidableEq S] in
open scoped Classical in
/-- Core of the second item of `lem:mossel-MC`: an eigenfunction orthogonal to the component
indicators has a large Dirichlet form (spectral gap lower bound `1 - λ ≥ α₀ ξ / (2 n³)`). -/
lemma gap_bound (T : StochMat S) (μ : FinProb S) (α₀ : ℝ) (hα : 0 < α₀)
    (hμα : ∀ a, α₀ ≤ μ.prob a) (hs : T.IsStationary μ) (n : ℝ) (hn : (Fintype.card S : ℝ) ≤ n)
    (g : S → ℂ) (lam : ℝ) (hg : ∀ a, ∑ b, (T.prob a b : ℂ) * g b = lam * g a)
    (hnorm : ∑ a, μ.prob a * ‖g a‖ ^ 2 = 1)
    (horth : ∀ x, ∑ a ∈ Finset.univ.filter
      (fun a => T.graph.connectedComponentMk a = T.graph.connectedComponentMk x),
        (μ.prob a : ℂ) * g a = 0)
    (ξ : ℝ) (hξ : 0 < ξ) (hT : ∀ a b, 0 < T.prob a b → ξ ≤ T.prob a b) :
    α₀ * ξ / (2 * n ^ 3) ≤ 1 - lam := by
  classical
  have hμpos : ∀ a, 0 < μ.prob a := fun a => lt_of_lt_of_le hα (hμα a)
  have hSne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hnorm
  have hn1 : 1 ≤ n := le_trans (by exact_mod_cast Fintype.card_pos) hn
  have hnpos : 0 < n := by linarith
  have : Fintype T.graph.ConnectedComponent := Fintype.ofFinite _
  -- pigeonhole over components
  set W : T.graph.ConnectedComponent → ℝ := fun c =>
    ∑ a ∈ Finset.univ.filter (fun a => T.graph.connectedComponentMk a = c),
      μ.prob a * ‖g a‖ ^ 2 with hW
  have hWsum : ∑ c, W c = 1 := by
    rw [← hnorm]
    exact Finset.sum_fiberwise Finset.univ (fun a => T.graph.connectedComponentMk a)
      (fun a => μ.prob a * ‖g a‖ ^ 2)
  have hcard : (Fintype.card T.graph.ConnectedComponent : ℝ) ≤ n := by
    refine le_trans ?_ hn
    exact_mod_cast Fintype.card_le_of_surjective T.graph.connectedComponentMk
      (fun c => c.ind fun v => ⟨v, rfl⟩)
  obtain ⟨c, -, hc⟩ : ∃ c ∈ (Finset.univ : Finset T.graph.ConnectedComponent), 1 / n ≤ W c := by
    by_contra hcon
    push Not at hcon
    have hne : (Finset.univ : Finset T.graph.ConnectedComponent).Nonempty :=
      ⟨T.graph.connectedComponentMk (Classical.arbitrary S), Finset.mem_univ _⟩
    have := Finset.sum_lt_sum_of_nonempty hne hcon
    rw [hWsum, Finset.sum_const, nsmul_eq_mul] at this
    have h2 : (Fintype.card T.graph.ConnectedComponent : ℝ) * (1 / n) ≤ 1 := by
      rw [mul_one_div, div_le_one hnpos]; exact hcard
    simp only [Finset.card_univ] at this
    linarith
  obtain ⟨x0, rfl⟩ : ∃ x0, T.graph.connectedComponentMk x0 = c := ⟨_, (Quot.out_eq c)⟩
  set C : Finset S := Finset.univ.filter
    (fun a => T.graph.connectedComponentMk a = T.graph.connectedComponentMk x0) with hC
  have hx0C : x0 ∈ C := by simp [hC]
  have hCne : (C ×ˢ C).Nonempty := ⟨(x0, x0), Finset.mem_product.2 ⟨hx0C, hx0C⟩⟩
  obtain ⟨⟨x, x'⟩, hxx, hmax⟩ := Finset.exists_max_image (C ×ˢ C)
    (fun p => ‖g p.1 - g p.2‖) hCne
  rw [Finset.mem_product] at hxx
  set D := ‖g x - g x'‖ with hD
  have hDmax : ∀ y ∈ C, ∀ y' ∈ C, ‖g y - g y'‖ ≤ D := fun y hy y' hy' =>
    hmax (y, y') (Finset.mem_product.2 ⟨hy, hy'⟩)
  have hμC : 0 < ∑ a ∈ C, μ.prob a := Finset.sum_pos (fun a _ => hμpos a) ⟨x0, hx0C⟩
  have hμC1 : ∑ a ∈ C, μ.prob a ≤ 1 := by
    rw [← μ.sum_eq_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => μ.nonneg a)
  have hgD : ∀ y ∈ C, ‖g y‖ ≤ D := by
    intro y hy
    have h0 : ∑ a ∈ C, (μ.prob a : ℂ) * g a = 0 := horth x0
    have h1 : ((∑ a ∈ C, μ.prob a : ℝ) : ℂ) * g y = ∑ a ∈ C, (μ.prob a : ℂ) * (g y - g a) := by
      rw [show ∑ a ∈ C, (μ.prob a : ℂ) * (g y - g a) =
        ∑ a ∈ C, (μ.prob a : ℂ) * g y - ∑ a ∈ C, (μ.prob a : ℂ) * g a by
          simp [mul_sub, Finset.sum_sub_distrib], h0, sub_zero]
      push_cast
      rw [Finset.sum_mul]
    have h2 : (∑ a ∈ C, μ.prob a) * ‖g y‖ ≤ (∑ a ∈ C, μ.prob a) * D := by
      calc (∑ a ∈ C, μ.prob a) * ‖g y‖
          = ‖((∑ a ∈ C, μ.prob a : ℝ) : ℂ) * g y‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμC.le]
        _ = ‖∑ a ∈ C, (μ.prob a : ℂ) * (g y - g a)‖ := by rw [h1]
        _ ≤ ∑ a ∈ C, ‖(μ.prob a : ℂ) * (g y - g a)‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ C, μ.prob a * D := by
            refine Finset.sum_le_sum fun a ha => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (μ.nonneg a)]
            exact mul_le_mul_of_nonneg_left (hDmax y hy a ha) (μ.nonneg a)
        _ = (∑ a ∈ C, μ.prob a) * D := by rw [Finset.sum_mul]
    exact le_of_mul_le_mul_left h2 hμC
  have hD2 : 1 / n ≤ D ^ 2 := by
    refine le_trans hc ?_
    calc W (T.graph.connectedComponentMk x0) = ∑ a ∈ C, μ.prob a * ‖g a‖ ^ 2 := rfl
      _ ≤ ∑ a ∈ C, μ.prob a * D ^ 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hgD a ha) 2) (μ.nonneg a)
      _ = (∑ a ∈ C, μ.prob a) * D ^ 2 := by rw [Finset.sum_mul]
      _ ≤ 1 * D ^ 2 := mul_le_mul_of_nonneg_right hμC1 (sq_nonneg _)
      _ = D ^ 2 := one_mul _
  have hDpos : 0 < D := by
    by_contra h
    have : D = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [this] at hD2
    have : 0 < 1 / n := by positivity
    simp at hD2
    linarith
  -- a long edge
  have hedge : ∃ a b, T.graph.Adj a b ∧ D / n ≤ ‖g a - g b‖ := by
    by_contra hcon
    push Not at hcon
    have hreach : T.graph.Reachable x x' := by
      have h1 : T.graph.connectedComponentMk x = T.graph.connectedComponentMk x0 := by
        simpa [hC] using hxx.1
      have h2 : T.graph.connectedComponentMk x' = T.graph.connectedComponentMk x0 := by
        simpa [hC] using hxx.2
      exact SimpleGraph.ConnectedComponent.eq.1 (h1.trans h2.symm)
    obtain ⟨p, hp⟩ := hreach.exists_isPath
    have hlen : (p.length : ℝ) < n := by
      have := hp.length_lt
      exact lt_of_lt_of_le (by exact_mod_cast this) hn
    have := walk_diff_le T g (D / n) (fun a b hab => (hcon a b hab).le) p
    have h3 : p.length * (D / n) < D := by
      rw [mul_div_assoc', div_lt_iff₀ hnpos]
      rw [mul_comm D n]
      exact mul_lt_mul_of_pos_right hlen hDpos
    linarith
  obtain ⟨a, b, hab, hbig⟩ := hedge
  have hbig2 : 1 / n ^ 3 ≤ ‖g a - g b‖ ^ 2 := by
    have h1 : (D / n) ^ 2 ≤ ‖g a - g b‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbig 2
    refine le_trans ?_ h1
    rw [div_pow]
    calc 1 / n ^ 3 = (1 / n) / n ^ 2 := by field_simp
      _ ≤ D ^ 2 / n ^ 2 := by gcongr
  have hd := dirichlet_eigen T μ hs g lam hg
  rw [hnorm, mul_one] at hd
  have hsingle : ∀ a b, 0 < T.prob a b → ‖g a - g b‖ ^ 2 = ‖g a - g b‖ ^ 2 →
      μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 ≤
        ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 := by
    intro a b _ _
    have hnn : ∀ a, 0 ≤ ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 := fun a =>
      Finset.sum_nonneg fun b _ => by
        have := μ.nonneg a; have := T.nonneg a b; positivity
    refine le_trans ?_ (Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_univ a))
    exact Finset.single_le_sum (f := fun b => μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2)
      (fun b _ => by have := μ.nonneg a; have := T.nonneg a b; positivity) (Finset.mem_univ b)
  have hlow : α₀ * ξ * (1 / n ^ 3) ≤ ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 := by
    rcases ((graph_adj_iff T a b).1 hab).2 with h | h
    · refine le_trans ?_ (hsingle a b h rfl)
      have h1 := hT a b h
      have h2 := hμα a
      calc α₀ * ξ * (1 / n ^ 3) ≤ α₀ * ξ * ‖g a - g b‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hbig2 (by positivity)
        _ ≤ μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul h2 h1 hξ.le (μ.nonneg a)) (sq_nonneg _)
    · refine le_trans ?_ (hsingle b a h rfl)
      have h1 := hT b a h
      have h2 := hμα b
      rw [norm_sub_rev] at hbig2
      calc α₀ * ξ * (1 / n ^ 3) ≤ α₀ * ξ * ‖g b - g a‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hbig2 (by positivity)
        _ ≤ μ.prob b * T.prob b a * ‖g b - g a‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul h2 h1 hξ.le (μ.nonneg b)) (sq_nonneg _)
  rw [hd] at hlow
  have : α₀ * ξ / (2 * n ^ 3) = (α₀ * ξ * (1 / n ^ 3)) / 2 := by field_simp
  rw [this]
  linarith

lemma norm_sum_eq_one (μ : FinProb S) (g : S → S → ℂ)
    (hgorth : ∀ i j, ∑ a, (μ.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) = if i = j then 1 else 0)
    (j : S) : ∑ a, μ.prob a * ‖g j a‖ ^ 2 = 1 := by
  have h := hgorth j j
  simp only [↓reduceIte] at h
  have h2 : ((∑ a, μ.prob a * ‖g j a‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  exact_mod_cast h2

/-- The eigenvalue-`1` eigenfunctions of the spectral data span a subspace of the harmonic
space, so there are at most `k` of them. -/
lemma card_eig_one_le (T : StochMat S) (μ : FinProb S) (hμ : ∀ a, 0 < μ.prob a)
    (hs : T.IsStationary μ) (lam : S → ℝ) (g : S → S → ℂ)
    (hgeig : ∀ j a, ∑ b, (T.prob a b : ℂ) * g j b = lam j * g j a)
    (hgorth : ∀ i j, ∑ a, (μ.prob a : ℂ) * g i a * (starRingEnd ℂ) (g j a) = if i = j then 1 else 0) :
    (Finset.univ.filter fun j => lam j = 1).card ≤ T.numComponents := by
  classical
  set J : Finset S := Finset.univ.filter fun j => lam j = 1 with hJ
  have hmem : ∀ j : J, g j ∈ harmSpace T := by
    intro j
    have hj : lam j = 1 := (Finset.mem_filter.1 j.2).2
    refine (mem_harmSpace T _).2 fun a => ?_
    have := hgeig j a
    rw [hj] at this
    simpa using this
  let v : J → harmSpace T := fun j => ⟨g j, hmem j⟩
  have hLI : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : ∀ a, ∑ j : J, c j * g j a = 0 := by
      intro a
      have := congrArg (fun f : harmSpace T => f.1 a) hc
      simpa [v, Submodule.coe_sum, Finset.sum_apply] using this
    have h2 : ∑ a, (μ.prob a : ℂ) * (∑ j : J, c j * g j a) * (starRingEnd ℂ) (g i a) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [h1 a]; simp
    have h3 : ∑ a, (μ.prob a : ℂ) * (∑ j : J, c j * g j a) * (starRingEnd ℂ) (g i a) = c i := by
      have : ∀ a, (μ.prob a : ℂ) * (∑ j : J, c j * g j a) * (starRingEnd ℂ) (g i a) =
          ∑ j : J, c j * ((μ.prob a : ℂ) * g j a * (starRingEnd ℂ) (g i a)) := by
        intro a
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      calc ∑ a, (μ.prob a : ℂ) * (∑ j : J, c j * g j a) * (starRingEnd ℂ) (g i a)
          = ∑ a, ∑ j : J, c j * ((μ.prob a : ℂ) * g j a * (starRingEnd ℂ) (g i a)) :=
            Finset.sum_congr rfl fun a _ => this a
        _ = ∑ j : J, ∑ a, c j * ((μ.prob a : ℂ) * g j a * (starRingEnd ℂ) (g i a)) :=
            Finset.sum_comm
        _ = ∑ j : J, c j * (if (j : S) = i then 1 else 0) :=
            Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, hgorth]
        _ = c i := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hj
              have : (j : S) ≠ i := fun h => hj (Subtype.ext h)
              simp [this]
            · simp
    rw [← h3, h2]
  have := hLI.fintype_card_le_finrank
  rw [Fintype.card_coe] at this
  exact this.trans (finrank_le_numComponents T μ hμ hs)

open scoped Classical in
lemma orth_of_eigen (T : StochMat S) (μ : FinProb S) (hr : T.IsReversible μ)
    (g : S → ℂ) (lam : ℝ) (hlam : lam ≠ 1)
    (hg : ∀ a, ∑ b, (T.prob a b : ℂ) * g b = lam * g a) (x : S) :
    ∑ a ∈ Finset.univ.filter
      (fun a => T.graph.connectedComponentMk a = T.graph.connectedComponentMk x),
        (μ.prob a : ℂ) * g a = 0 := by
  classical
  set ψ : S → ℂ := fun a =>
    if T.graph.connectedComponentMk a = T.graph.connectedComponentMk x then 1 else 0 with hψ
  have hTψ := comp_harmonic T
    (fun c => if c = T.graph.connectedComponentMk x then (1 : ℂ) else 0)
  have key : ∑ a, (μ.prob a : ℂ) * (∑ b, (T.prob a b : ℂ) * g b) * ψ a =
      ∑ b, (μ.prob b : ℂ) * g b * ψ b := by
    calc ∑ a, (μ.prob a : ℂ) * (∑ b, (T.prob a b : ℂ) * g b) * ψ a
        = ∑ a, ∑ b, (μ.prob a : ℂ) * (T.prob a b : ℂ) * g b * ψ a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b, ∑ a, (μ.prob b : ℂ) * (T.prob b a : ℂ) * g b * ψ a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
          have := hr a b
          have h2 : (μ.prob a : ℂ) * (T.prob a b : ℂ) = (μ.prob b : ℂ) * (T.prob b a : ℂ) := by
            exact_mod_cast this
          rw [h2]
      _ = ∑ b, (μ.prob b : ℂ) * g b * ∑ a, (T.prob b a : ℂ) * ψ a := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by
          refine Finset.sum_congr rfl fun b _ => ?_
          have := hTψ b
          rw [show ∑ a, (T.prob b a : ℂ) * ψ a = ψ b from this]
  simp_rw [hg] at key
  have h3 : ((lam : ℂ) - 1) * ∑ a, (μ.prob a : ℂ) * g a * ψ a = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero, Finset.mul_sum, ← key]
    refine Finset.sum_congr rfl fun a _ => by ring
  have hne : ((lam : ℂ) - 1) ≠ 0 := by
    intro h
    apply hlam
    have : (lam : ℂ) = 1 := sub_eq_zero.1 h
    exact_mod_cast this
  have h4 := (mul_eq_zero.1 h3).resolve_left hne
  rw [← h4, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hψ]
  split_ifs <;> simp

omit [DecidableEq S] in
lemma sq_norm_le (μ : FinProb S) (α₀ : ℝ) (hα : 0 < α₀) (hμα : ∀ a, α₀ ≤ μ.prob a)
    (g : S → ℂ) (hnorm : ∑ a, μ.prob a * ‖g a‖ ^ 2 = 1) (a : S) : ‖g a‖ ^ 2 ≤ 1 / α₀ := by
  have h1 : μ.prob a * ‖g a‖ ^ 2 ≤ 1 := by
    rw [← hnorm]
    exact Finset.single_le_sum (f := fun a => μ.prob a * ‖g a‖ ^ 2)
      (fun a _ => mul_nonneg (μ.nonneg a) (sq_nonneg _)) (Finset.mem_univ a)
  rw [le_div_iff₀ hα]
  calc ‖g a‖ ^ 2 * α₀ ≤ ‖g a‖ ^ 2 * μ.prob a :=
        mul_le_mul_of_nonneg_left (hμα a) (sq_nonneg _)
    _ ≤ 1 := by linarith

/-- Third item of `lem:mossel-MC`, for one eigenfunction. -/
lemma lower_bound_eig (T : StochMat S) (μ : FinProb S) (α₀ : ℝ) (hα : 0 < α₀)
    (hμα : ∀ a, α₀ ≤ μ.prob a) (hs : T.IsStationary μ)
    (g : S → ℂ) (lam : ℝ) (hg : ∀ a, ∑ b, (T.prob a b : ℂ) * g b = lam * g a)
    (hnorm : ∑ a, μ.prob a * ‖g a‖ ^ 2 = 1) (ξ : ℝ) (hξ : ∀ a, 1 - ξ ≤ T.prob a a) :
    1 - 2 / α₀ * ξ ≤ lam := by
  classical
  have hd := dirichlet_eigen T μ hs g lam hg
  rw [hnorm, mul_one] at hd
  have hX : ∀ a b, ‖g a - g b‖ ^ 2 ≤ 4 / α₀ := by
    intro a b
    have h1 := sq_norm_le μ α₀ hα hμα g hnorm a
    have h2 := sq_norm_le μ α₀ hα hμα g hnorm b
    have h3 : ‖g a - g b‖ ≤ ‖g a‖ + ‖g b‖ := norm_sub_le _ _
    have h4 : ‖g a - g b‖ ^ 2 ≤ 2 * (‖g a‖ ^ 2 + ‖g b‖ ^ 2) := by
      nlinarith [sq_nonneg (‖g a‖ - ‖g b‖), norm_nonneg (g a - g b), norm_nonneg (g a),
        norm_nonneg (g b)]
    calc ‖g a - g b‖ ^ 2 ≤ 2 * (‖g a‖ ^ 2 + ‖g b‖ ^ 2) := h4
      _ ≤ 2 * (1 / α₀ + 1 / α₀) := by linarith
      _ = 4 / α₀ := by ring
  have hrow : ∀ a, ∑ b, T.prob a b * ‖g a - g b‖ ^ 2 ≤ 4 / α₀ * ξ := by
    intro a
    have hterm : ∀ b, T.prob a b * ‖g a - g b‖ ^ 2 ≤
        4 / α₀ * (T.prob a b - if b = a then T.prob a b else 0) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp
      · simp only [hb, ↓reduceIte, sub_zero]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hX a b) (T.nonneg a b)
    refine le_trans (Finset.sum_le_sum fun b _ => hterm b) ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, T.row_sum, Finset.sum_ite_eq' Finset.univ a]
    simp only [Finset.mem_univ, ↓reduceIte]
    have := hξ a
    have h4 : 0 ≤ 4 / α₀ := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h4
  have hE : ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 ≤ 4 / α₀ * ξ := by
    calc ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2
        = ∑ a, μ.prob a * ∑ b, T.prob a b * ‖g a - g b‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ ∑ a, μ.prob a * (4 / α₀ * ξ) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrow a) (μ.nonneg a)
      _ = 4 / α₀ * ξ := by rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]
  rw [hd] at hE
  have : 2 / α₀ * ξ = (4 / α₀ * ξ) / 2 := by ring
  linarith

omit [DecidableEq S] in
lemma lam_le_one (T : StochMat S) (μ : FinProb S) (hs : T.IsStationary μ)
    (g : S → ℂ) (lam : ℝ) (hg : ∀ a, ∑ b, (T.prob a b : ℂ) * g b = lam * g a)
    (hnorm : ∑ a, μ.prob a * ‖g a‖ ^ 2 = 1) : lam ≤ 1 := by
  have hd := dirichlet_eigen T μ hs g lam hg
  rw [hnorm, mul_one] at hd
  have : 0 ≤ ∑ a, ∑ b, μ.prob a * T.prob a b * ‖g a - g b‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
      have := μ.nonneg a; have := T.nonneg a b; positivity
  linarith

omit [DecidableEq S] in
lemma count_one_eigenvalues (lam : S → ℝ) :
    Multiset.count (1 : ℂ) (Finset.univ.val.map fun j => (lam j : ℂ)) =
      (Finset.univ.filter fun j => lam j = 1).card := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  refine Multiset.filter_congr fun j _ => ?_
  constructor
  · intro h; exact_mod_cast h.symm
  · intro h; rw [h]; simp

lemma numComponents_le_count (T : StochMat S) :
    T.numComponents ≤ T.eigenvalues.count 1 := by
  classical
  unfold StochMat.eigenvalues
  rw [Polynomial.count_roots]
  have h1 := numComponents_le_finrank T
  have h2 := LinearMap.finrank_eigenspace_le
    (Matrix.toLin' (Matrix.of fun a b => (T.prob a b : ℂ))) 1
  rw [Matrix.charpoly_toLin'] at h2
  exact h1.trans h2


end Aux

open scoped ComplexOrder in
/-- paper IV `lem:mossel-MC` (Lemma 2.7, statement l. 1222-1235, proof l. 1236-1276), with the
reversibility premise `T.IsReversible μ` added as a hypothesis: the source uses it without stating it
(paper IV step `self-adjointness-gap`), and without it the printed eigenvalue inequalities are not
meaningful. Every consumer proves reversibility of its chain. The eigenvalues are the roots of the characteristic polynomial over `ℂ`, which for
a reversible chain is the sorted list `λ₁ ≥ … ≥ λ_m` of the source up to order. The four absorbed
sub-steps are the Dirichlet form identity (`dirichlet_eigen`), the spectral gap upper bound
(`gap_bound`), the eigenvalue lower bound (`lower_bound_eig`) and the self-adjointness adapter
(`spectral_data`). -/
theorem mossel_MC (α₀ : ℝ) (hα : 0 < α₀) (m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ : FinProb S, (∀ a, α₀ ≤ μ.prob a) →
      ∀ T : StochMat S, T.IsStationary μ → T.IsReversible μ →
        Multiset.replicate T.numComponents (1 : ℂ) ≤ T.eigenvalues ∧
        (∀ ξ : ℝ, (∀ a b, 0 < T.prob a b → ξ ≤ T.prob a b) →
          ∀ l ∈ T.eigenvalues - Multiset.replicate T.numComponents (1 : ℂ),
            l ≤ ((1 - c * ξ : ℝ) : ℂ)) ∧
        (∀ ξ : ℝ, (∀ a, 1 - ξ ≤ T.prob a a) →
          ∀ l ∈ T.eigenvalues, ((1 - C * ξ : ℝ) : ℂ) ≤ l) := by
  refine ⟨α₀ / (2 * ((m : ℝ) + 1) ^ 3), 2 / α₀, by positivity, by positivity, ?_⟩
  intro S _ _ hcard μ hμα T hs hr
  have hμpos : ∀ a, 0 < μ.prob a := fun a => lt_of_lt_of_le hα (hμα a)
  obtain ⟨lam, g, hM, hgeig, hgorth⟩ := spectral_data T μ hμpos hr
  have hnorm := norm_sum_eq_one μ g hgorth
  have hn : (Fintype.card S : ℝ) ≤ (m : ℝ) + 1 := by
    have : (Fintype.card S : ℝ) ≤ m := by exact_mod_cast hcard
    linarith
  refine ⟨Multiset.le_count_iff_replicate_le.1 (numComponents_le_count T), ?_, ?_⟩
  · intro ξ hT l hl
    have hl' := Multiset.mem_of_le (Multiset.sub_le_self _ _) hl
    rw [hM, Multiset.mem_map] at hl'
    obtain ⟨j, -, rfl⟩ := hl'
    rw [Complex.real_le_real]
    by_cases hξ : ξ ≤ 0
    · have h1 := lam_le_one T μ hs (g j) (lam j) (hgeig j) (hnorm j)
      have hc : 0 < α₀ / (2 * ((m : ℝ) + 1) ^ 3) := by positivity
      nlinarith
    · push Not at hξ
      by_cases h1 : lam j = 1
      · exfalso
        have hcount : T.eigenvalues.count 1 ≤ T.numComponents := by
          rw [hM, count_one_eigenvalues]
          exact card_eig_one_le T μ hμpos hs lam g hgeig hgorth
        rw [h1] at hl
        have hpos := Multiset.count_pos.2 (show ((1 : ℝ) : ℂ) ∈ _ from hl)
        rw [Complex.ofReal_one, Multiset.count_sub, Multiset.count_replicate_self] at hpos
        omega
      · have := gap_bound T μ α₀ hα hμα hs ((m : ℝ) + 1) hn (g j) (lam j) (hgeig j) (hnorm j)
          (orth_of_eigen T μ hr (g j) (lam j) h1 (hgeig j)) ξ hξ hT
        have e : α₀ / (2 * ((m : ℝ) + 1) ^ 3) * ξ = α₀ * ξ / (2 * ((m : ℝ) + 1) ^ 3) := by ring
        rw [e]
        linarith
  · intro ξ hξ l hl
    rw [hM, Multiset.mem_map] at hl
    obtain ⟨j, -, rfl⟩ := hl
    rw [Complex.real_le_real]
    exact lower_bound_eig T μ α₀ hα hμα hs (g j) (lam j) (hgeig j) (hnorm j) ξ hξ

end TrackB
end RestrictedPolynomials
end
