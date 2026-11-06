module

public import RestrictedPolynomials.TrackB.MarkovChain
public import RestrictedPolynomials.TrackB.StabComplex
public import RestrictedPolynomials.Frozen.FinProbPi
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

open Finset
open scoped Matrix
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Defs
variable {α : Type} [Fintype α] [DecidableEq α]

/-- `A^{⊗ι}`, with entries `∏ᵢ A (xᵢ) (yᵢ)`. -/
def kernelPow (A : Matrix α α ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun x y => ∏ i, A (x i) (y i)

/-- `V^⊥` in `L²(μ)`. -/
def orthSet (μ : FinProb α) (V : Set (α → ℂ)) : Set (α → ℂ) :=
  {g | ∀ v ∈ V, μ.cinner g v = 0}

/-- `span(V^{⊗S} ⊗ W^{⊗ (ι∖S)})` inside the functions on `ι → α`. -/
def blockSpace {ι : Type} [Fintype ι] (V W : Set (α → ℂ)) (S : Finset ι) : Submodule ℂ ((ι → α) → ℂ) :=
  Submodule.span ℂ {g | ∃ v : ι → α → ℂ, (∀ i ∈ S, v i ∈ V) ∧ (∀ i ∉ S, v i ∈ W) ∧
    g = fun x => ∏ i, v i (x i)}

/-- the functions constant on every connected component of the chain `T` -/
def StochMat.constOnComp (T : StochMat α) : Submodule ℂ (α → ℂ) where
  carrier := {g | ∀ a b, T.graph.Reachable a b → g a = g b}
  add_mem' := fun ha hb a b h => by simp [ha a b h, hb a b h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c g hg a b h => by simp [hg a b h]

/-- the transition matrix of `T` over `ℂ` -/
def StochMat.cmat (T : StochMat α) : Matrix α α ℂ := Matrix.of fun a b => (T.prob a b : ℂ)

/-- `‖f‖₂` in `L²(μ^{⊗ι})`. -/
def cl2norm {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (f : (ι → α) → ℂ) : ℝ :=
  Real.sqrt (cl2sq π f)

/-! ### Elementary calculus of `cinner` -/

end Defs

section Cinner
variable {β : Type*} [Fintype β]

lemma cinner_def (π : FinProb β) (f g : β → ℂ) :
    π.cinner f g = ∑ a, (π.prob a : ℂ) * (f a * star (g a)) := rfl

lemma cinner_comm (π : FinProb β) (f g : β → ℂ) : π.cinner g f = star (π.cinner f g) := by
  simp only [cinner_def, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show star (π.prob a : ℂ) = π.prob a by simp]
  ring

lemma cinner_add_left (π : FinProb β) (f f' g : β → ℂ) :
    π.cinner (f + f') g = π.cinner f g + π.cinner f' g := by
  simp only [cinner_def, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma cinner_smul_left (π : FinProb β) (c : ℂ) (f g : β → ℂ) :
    π.cinner (c • f) g = c * π.cinner f g := by
  simp only [cinner_def, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma cinner_smul_right (π : FinProb β) (c : ℂ) (f g : β → ℂ) :
    π.cinner f (c • g) = star c * π.cinner f g := by
  simp only [cinner_def, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, star_mul']
  exact Finset.sum_congr rfl fun a _ => by ring

lemma cinner_add_right (π : FinProb β) (f g g' : β → ℂ) :
    π.cinner f (g + g') = π.cinner f g + π.cinner f g' := by
  simp only [cinner_def, ← Finset.sum_add_distrib, Pi.add_apply, star_add]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma cinner_zero_left (π : FinProb β) (g : β → ℂ) : π.cinner 0 g = 0 := by
  simp [cinner_def]

lemma cinner_zero_right (π : FinProb β) (g : β → ℂ) : π.cinner g 0 = 0 := by
  simp [cinner_def]

lemma cinner_sum_left {γ : Type*} (π : FinProb β) (s : Finset γ) (f : γ → β → ℂ) (g : β → ℂ) :
    π.cinner (∑ i ∈ s, f i) g = ∑ i ∈ s, π.cinner (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cinner_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cinner_add_left, ih]

lemma cinner_sum_right {γ : Type*} (π : FinProb β) (s : Finset γ) (f : β → ℂ) (g : γ → β → ℂ) :
    π.cinner f (∑ i ∈ s, g i) = ∑ i ∈ s, π.cinner f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cinner_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cinner_add_right, ih]

lemma cinner_self_eq (π : FinProb β) (f : β → ℂ) :
    π.cinner f f = ((π.expect fun a => ‖f a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [cinner_def, FinProb.expect, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : f a * star (f a) = ((‖f a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [this]; push_cast; ring

end Cinner

section PiProd
variable {α : Type} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma cexpect_pi_prod (μ : FinProb α) (F : ι → α → ℂ) :
    (μ.pi ι).cexpect (fun x => ∏ i, F i (x i)) = ∏ i, μ.cexpect (F i) := by
  unfold FinProb.cexpect
  rw [Fintype.prod_sum (fun i a => (μ.prob a : ℂ) * F i a)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]
  simp [FinProb.pi]

lemma cinner_pi_prod (μ : FinProb α) (f g : ι → α → ℂ) :
    (μ.pi ι).cinner (fun x => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i)) =
      ∏ i, μ.cinner (f i) (g i) := by
  unfold FinProb.cinner
  rw [← cexpect_pi_prod]
  congr 1
  funext x
  rw [star_prod, ← Finset.prod_mul_distrib]

end PiProd

section Cl2
variable {α : Type} [Fintype α]

lemma cl2sq_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb α)
    (f : (ι → α) → ℂ) : 0 ≤ cl2sq μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg ((μ.pi ι).nonneg x) (sq_nonneg _)

lemma cl2sq_cast {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb α)
    (f : (ι → α) → ℂ) : ((cl2sq μ f : ℝ) : ℂ) = (μ.pi ι).cinner f f :=
  (cinner_self_eq (μ.pi ι) f).symm

end Cl2

section Spectral
variable {α : Type} [Fintype α] [DecidableEq α]

/-- `α → ℂ` carrying the `L²(μ)` inner product (a type synonym, so that no other norm interferes). -/
def Wt (_μ : FinProb α) : Type := α → ℂ

instance (μ : FinProb α) : AddCommGroup (Wt μ) := inferInstanceAs (AddCommGroup (α → ℂ))
instance (μ : FinProb α) : Module ℂ (Wt μ) := inferInstanceAs (Module ℂ (α → ℂ))
instance (μ : FinProb α) : FiniteDimensional ℂ (Wt μ) :=
  inferInstanceAs (FiniteDimensional ℂ (α → ℂ))

/-- The `L²(μ)` inner product space structure on `Wt μ` (needs full support). -/
@[instance_reducible]
def wtCore (μ : FinProb α) (hμ : ∀ a, 0 < μ.prob a) : InnerProductSpace.Core ℂ (Wt μ) where
  toInner := ⟨fun x y => μ.cinner (y : α → ℂ) (x : α → ℂ)⟩
  conj_inner_symm x y := by
    show star (μ.cinner (x : α → ℂ) (y : α → ℂ)) = μ.cinner (y : α → ℂ) (x : α → ℂ)
    rw [cinner_comm μ (y : α → ℂ) (x : α → ℂ)]
    exact star_star _
  re_inner_nonneg x := by
    have h : 0 ≤ μ.expect fun a => ‖(x : α → ℂ) a‖ ^ 2 :=
      Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg a) (sq_nonneg _)
    show 0 ≤ RCLike.re (μ.cinner (x : α → ℂ) (x : α → ℂ))
    rw [cinner_self_eq μ (x : α → ℂ)]
    simpa using h
  add_left x y z := by
    exact cinner_add_right μ (z : α → ℂ) (x : α → ℂ) (y : α → ℂ)
  smul_left x y r := by
    exact cinner_smul_right μ r (y : α → ℂ) (x : α → ℂ)
  definite x hx := by
    change μ.cinner (x : α → ℂ) (x : α → ℂ) = 0 at hx
    rw [cinner_self_eq μ (x : α → ℂ)] at hx
    have h0 : (μ.expect fun a => ‖(x : α → ℂ) a‖ ^ 2) = 0 := by exact_mod_cast hx
    have hnn : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ μ.prob a * ‖(x : α → ℂ) a‖ ^ 2 :=
      fun a _ => mul_nonneg (μ.nonneg a) (sq_nonneg _)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0
    funext a
    have := h1 a (Finset.mem_univ a)
    have h2 : ‖(x : α → ℂ) a‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hμ a).ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

open scoped ComplexOrder in
omit [DecidableEq α] in
/-- An orthonormal basis of `L²(μ)` adapted to `V ⊕ V^⊥` and diagonalising `A`. -/
lemma exists_adapted_basis (μ : FinProb α) (hμ : ∀ a, 0 < μ.prob a)
    (V : Submodule ℂ (α → ℂ)) (A : Matrix α α ℂ)
    (hself : ∀ f g, μ.cinner (A.mulVec f) g = μ.cinner f (A.mulVec g))
    (hV : ∀ v ∈ V, A.mulVec v = v)
    (hV' : ∀ g ∈ orthSet μ (V : Set (α → ℂ)), A.mulVec g ∈ orthSet μ (V : Set (α → ℂ)))
    {a b : ℝ} (hb : b ≤ 1)
    (heig : ∀ g ∈ orthSet μ (V : Set (α → ℂ)), g ≠ 0 → ∀ l : ℂ, A.mulVec g = l • g →
      ∃ r : ℝ, l = r ∧ a ≤ r ∧ r ≤ b) :
    ∃ (J : Type) (_ : Fintype J) (u : J → α → ℂ) (isV : J → Prop) (lam : J → ℝ),
      (∀ i, μ.cinner (u i) (u i) = 1) ∧ (∀ i j, i ≠ j → μ.cinner (u i) (u j) = 0) ∧
      (∀ f, f = ∑ j, μ.cinner f (u j) • u j) ∧
      (∀ j, isV j → u j ∈ V) ∧ (∀ j, ¬ isV j → u j ∈ orthSet μ (V : Set (α → ℂ))) ∧
      (∀ j, A.mulVec (u j) = (lam j : ℂ) • u j) ∧ (∀ j, isV j → lam j = 1) ∧
      (∀ j, ¬ isV j → a ≤ lam j ∧ lam j ≤ b) := by
  classical
  let _ := wtCore μ hμ
  let _ : NormedAddCommGroup (Wt μ) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ (Wt μ) := InnerProductSpace.ofCore _
  have hinner : ∀ x y : Wt μ, inner ℂ x y = μ.cinner (y : α → ℂ) (x : α → ℂ) := fun x y => rfl
  let V' : Submodule ℂ (Wt μ) := V
  have hmemorth : ∀ g : Wt μ, g ∈ V'ᗮ ↔ (g : α → ℂ) ∈ orthSet μ (V : Set (α → ℂ)) := by
    intro g
    rw [Submodule.mem_orthogonal]
    exact Iff.rfl
  let Alin : Wt μ →ₗ[ℂ] Wt μ := Matrix.mulVecLin A
  have hAlin : ∀ x : Wt μ, Alin x = A.mulVec (x : α → ℂ) := fun x => rfl
  have hsymA : Alin.IsSymmetric := by
    have hs : ∀ x y : α → ℂ, μ.cinner y (A.mulVec x) = μ.cinner (A.mulVec y) x := by
      intro x y
      rw [cinner_comm μ (A.mulVec x) y, hself, ← cinner_comm μ x (A.mulVec y)]
    intro x y
    exact hs (x : α → ℂ) (y : α → ℂ)
  let P : Wt μ →ₗ[ℂ] Wt μ := (V'.starProjection : Wt μ →L[ℂ] Wt μ)
  have hsymP : P.IsSymmetric := Submodule.starProjection_isSymmetric V'
  let T : Wt μ →ₗ[ℂ] Wt μ := Alin + P
  have hT : T.IsSymmetric := hsymA.add hsymP
  have key : ∀ (x : Wt μ) (l : ℝ), x ≠ 0 → T x = (l : ℂ) • x →
      x ∈ V' ∨ ((x : α → ℂ) ∈ orthSet μ (V : Set (α → ℂ)) ∧
        A.mulVec (x : α → ℂ) = (l : ℂ) • (x : α → ℂ) ∧ a ≤ l ∧ l ≤ b) := by
    intro x l hx0 hTx
    set Px : Wt μ := V'.starProjection x with hPxdef
    set w : Wt μ := x - Px with hwdef
    have hPx : Px ∈ V' := Submodule.starProjection_apply_mem V' x
    have hw : w ∈ V'ᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have hAw : Alin w ∈ V'ᗮ := (hmemorth _).2 (hV' _ ((hmemorth w).1 hw))
    have hAPx : Alin Px = Px := hV Px hPx
    have hxsplit : x = Px + w := by rw [hwdef]; abel
    have hPPx : P Px = Px := Submodule.starProjection_eq_self_iff.2 hPx
    have hPw : P w = 0 := (Submodule.starProjection_apply_eq_zero_iff V').2 hw
    have hPAw : P (Alin w) = 0 := (Submodule.starProjection_apply_eq_zero_iff V').2 hAw
    have hTx' : T x = (2 : ℂ) • Px + Alin w := by
      have h1 : T x = Alin x + P x := rfl
      have h2 : P x = Px := rfl
      rw [h1, h2]
      conv_lhs => rw [hxsplit]
      rw [map_add, hAPx, two_smul]
      abel
    have hlx : (l : ℂ) • x = (l : ℂ) • Px + (l : ℂ) • w := by
      conv_lhs => rw [hxsplit]
      rw [smul_add]
    have heq : (2 : ℂ) • Px + Alin w = (l : ℂ) • Px + (l : ℂ) • w := by
      rw [← hTx', hTx, hlx]
    have E1 : (2 : ℂ) • Px = (l : ℂ) • Px := by
      have := congrArg P heq
      rwa [map_add, map_add, map_smul, map_smul, map_smul, hPPx, hPw, hPAw, smul_zero,
        add_zero, add_zero] at this
    have E2 : Alin w = (l : ℂ) • w := by
      have h3 : Alin w = (l : ℂ) • Px + (l : ℂ) • w - (2 : ℂ) • Px := by
        rw [← heq]; abel
      rw [h3, ← E1]; abel
    by_cases hPx0 : Px = 0
    · right
      have hxw : x = w := by rw [hxsplit, hPx0, zero_add]
      have hxorth : (x : α → ℂ) ∈ orthSet μ (V : Set (α → ℂ)) := by
        rw [← hmemorth, hxw]; exact hw
      have hAx : A.mulVec (x : α → ℂ) = (l : ℂ) • (x : α → ℂ) := by
        rw [← hAlin, hxw, E2]
      obtain ⟨r, hr, har, hrb⟩ := heig _ hxorth hx0 (l : ℂ) hAx
      have : l = r := by exact_mod_cast hr
      subst this
      exact ⟨hxorth, hAx, har, hrb⟩
    · left
      have hl2 : (l : ℂ) = 2 := by
        have h4 : ((2 : ℂ) - (l : ℂ)) • Px = 0 := by rw [sub_smul, E1, sub_self]
        rcases smul_eq_zero.1 h4 with h | h
        · exact (sub_eq_zero.1 h).symm
        · exact absurd h hPx0
      by_cases hw0 : w = 0
      · rw [hxsplit, hw0, add_zero]; exact hPx
      · exfalso
        have hAw2 : A.mulVec (w : α → ℂ) = (l : ℂ) • (w : α → ℂ) := by rw [← hAlin, E2]
        obtain ⟨r, hr, -, hrb⟩ := heig _ ((hmemorth w).1 hw) hw0 (l : ℂ) hAw2
        have : l = r := by exact_mod_cast hr
        subst this
        have h2 : l = 2 := by exact_mod_cast hl2
        linarith
  let bb := hT.eigenvectorBasis (rfl : Module.finrank ℂ (Wt μ) = Module.finrank ℂ (Wt μ))
  have hbb : ∀ j, T (bb j) = ((hT.eigenvalues rfl j : ℝ) : ℂ) • bb j := fun j =>
    hT.apply_eigenvectorBasis rfl j
  have hbb0 : ∀ j, bb j ≠ 0 := fun j => bb.orthonormal.ne_zero j
  have hbbV : ∀ j, bb j ∈ V' → A.mulVec (bb j : α → ℂ) = (1 : ℂ) • (bb j : α → ℂ) := fun j hj => by
    rw [one_smul]; exact hV _ hj
  refine ⟨Fin (Module.finrank ℂ (Wt μ)), inferInstance, fun j => (bb j : α → ℂ),
    fun j => bb j ∈ V', fun j => if bb j ∈ V' then 1 else hT.eigenvalues rfl j, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro i
    have := orthonormal_iff_ite.1 bb.orthonormal i i
    rw [hinner] at this
    simpa using this
  · intro i j hij
    have := orthonormal_iff_ite.1 bb.orthonormal j i
    rw [hinner] at this
    simpa [Ne.symm hij] using this
  · intro f
    exact (bb.sum_repr' (f : Wt μ)).symm
  · intro j hj
    exact hj
  · intro j hj
    rcases key (bb j) _ (hbb0 j) (hbb j) with h | h
    · exact absurd h hj
    · exact h.1
  · intro j
    by_cases hj : bb j ∈ V'
    · beta_reduce; simp only [hj, ↓reduceIte]; exact hbbV j hj
    · beta_reduce; simp only [hj, ↓reduceIte]
      rcases key (bb j) _ (hbb0 j) (hbb j) with h | h
      · exact absurd h hj
      · exact h.2.1
  · intro j hj
    simp [hj]
  · intro j hj
    beta_reduce; simp only [hj, ↓reduceIte]
    rcases key (bb j) _ (hbb0 j) (hbb j) with h | h
    · exact absurd h hj
    · exact h.2.2

end Spectral

section Product
variable {α : Type} [Fintype α] [DecidableEq α]

/-- An orthonormal basis of `L²(μ)` adapted to `V ⊕ V^⊥`, diagonalising `A`. -/
structure AdBasis (μ : FinProb α) (V : Submodule ℂ (α → ℂ)) (A : Matrix α α ℂ) (a b : ℝ) where
  J : Type
  [instFintype : Fintype J]
  u : J → α → ℂ
  isV : J → Prop
  lam : J → ℝ
  norm1 : ∀ i, μ.cinner (u i) (u i) = 1
  orth : ∀ i j, i ≠ j → μ.cinner (u i) (u j) = 0
  expand : ∀ f, f = ∑ j, μ.cinner f (u j) • u j
  mem_V : ∀ j, isV j → u j ∈ V
  mem_W : ∀ j, ¬ isV j → u j ∈ orthSet μ (V : Set (α → ℂ))
  eigen : ∀ j, A.mulVec (u j) = (lam j : ℂ) • u j
  lam_V : ∀ j, isV j → lam j = 1
  lam_W : ∀ j, ¬ isV j → a ≤ lam j ∧ lam j ≤ b

attribute [instance] AdBasis.instFintype

namespace AdBasis
variable {μ : FinProb α} {V : Submodule ℂ (α → ℂ)} {A : Matrix α α ℂ} {a b : ℝ}
  (B : AdBasis μ V A a b) {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the product basis vector `∏ᵢ u_{σ i}(xᵢ)` -/
def U (σ : ι → B.J) : (ι → α) → ℂ := fun x => ∏ i, B.u (σ i) (x i)

/-- the coefficient of `g` on the product basis vector `σ` -/
def coef (g : (ι → α) → ℂ) (σ : ι → B.J) : ℂ := (μ.pi ι).cinner g (B.U σ)

open scoped Classical in
/-- the set of coordinates of `V`-type -/
def typ (σ : ι → B.J) : Finset ι := Finset.univ.filter fun i => B.isV (σ i)

/-- the eigenvalue of the product basis vector `σ` -/
def lamP (σ : ι → B.J) : ℝ := ∏ i, B.lam (σ i)

omit [DecidableEq α] [DecidableEq ι] in
lemma mem_typ (σ : ι → B.J) (i : ι) : i ∈ B.typ σ ↔ B.isV (σ i) := by
  classical
  simp [typ]

omit [DecidableEq α] in
lemma cinner_U_self (σ : ι → B.J) : (μ.pi ι).cinner (B.U σ) (B.U σ) = 1 := by
  unfold U
  rw [cinner_pi_prod]
  exact Finset.prod_eq_one fun i _ => B.norm1 _

omit [DecidableEq α] in
lemma cinner_U_ne {σ τ : ι → B.J} (h : σ ≠ τ) : (μ.pi ι).cinner (B.U σ) (B.U τ) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  unfold U
  rw [cinner_pi_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (B.orth _ _ hi)

lemma kernel_single (x y : α) :
    ∑ j, B.u j x * star (B.u j y) * (μ.prob y : ℂ) = if x = y then 1 else 0 := by
  have h := congrFun (B.expand (Pi.single y (1 : ℂ))) x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : μ.cinner (Pi.single y (1 : ℂ)) (B.u j) = (μ.prob y : ℂ) * star (B.u j y) := by
    simp [cinner_def, Pi.single_apply]
  rw [this]; ring

lemma kernel_pi (x y : ι → α) :
    ∑ σ : ι → B.J, B.U σ x * star (B.U σ y) * ((μ.pi ι).prob y : ℂ) =
      if x = y then 1 else 0 := by
  have h1 : ∀ σ : ι → B.J, B.U σ x * star (B.U σ y) * ((μ.pi ι).prob y : ℂ) =
      ∏ i, (B.u (σ i) (x i) * star (B.u (σ i) (y i)) * (μ.prob (y i) : ℂ)) := by
    intro σ
    simp only [U, star_prod, FinProb.pi, Complex.ofReal_prod, Finset.prod_mul_distrib]
  simp only [h1]
  rw [← Fintype.prod_sum (fun i j => B.u j (x i) * star (B.u j (y i)) * (μ.prob (y i) : ℂ))]
  simp only [kernel_single]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

lemma expand_pi (g : (ι → α) → ℂ) : g = ∑ σ : ι → B.J, B.coef g σ • B.U σ := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coef, cinner_def]
  have h2 : ∀ σ : ι → B.J, (∑ y, ((μ.pi ι).prob y : ℂ) * (g y * star (B.U σ y))) * B.U σ x =
      ∑ y, g y * (B.U σ x * star (B.U σ y) * ((μ.pi ι).prob y : ℂ)) := by
    intro σ
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [h2]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, kernel_pi]
  simp

omit [DecidableEq α] in
lemma coef_add (g g' : (ι → α) → ℂ) (σ : ι → B.J) :
    B.coef (g + g') σ = B.coef g σ + B.coef g' σ := cinner_add_left _ _ _ _

omit [DecidableEq α] in
lemma coef_smul (c : ℂ) (g : (ι → α) → ℂ) (σ : ι → B.J) :
    B.coef (c • g) σ = c * B.coef g σ := cinner_smul_left _ _ _ _

omit [DecidableEq α] in
lemma coef_sum {γ : Type*} (s : Finset γ) (g : γ → (ι → α) → ℂ) (σ : ι → B.J) :
    B.coef (∑ i ∈ s, g i) σ = ∑ i ∈ s, B.coef (g i) σ := cinner_sum_left _ _ _ _

/-- Parseval for the product basis. -/
lemma parseval (g g' : (ι → α) → ℂ) :
    (μ.pi ι).cinner g g' = ∑ σ, B.coef g σ * star (B.coef g' σ) := by
  have : (μ.pi ι).cinner g g' = (μ.pi ι).cinner (∑ σ, B.coef g σ • B.U σ)
      (∑ τ, B.coef g' τ • B.U τ) := by
    rw [← B.expand_pi g, ← B.expand_pi g']
  rw [this, cinner_sum_left]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cinner_smul_left, cinner_sum_right, Finset.mul_sum, Finset.sum_eq_single σ]
  · rw [cinner_smul_right, cinner_U_self]; ring
  · intro τ _ hτ
    rw [cinner_smul_right, cinner_U_ne B (Ne.symm hτ)]; simp
  · simp

omit [DecidableEq α] in
lemma coef_of_expansion (c : (ι → B.J) → ℂ) (τ : ι → B.J) :
    B.coef (∑ σ, c σ • B.U σ) τ = c τ := by
  rw [coef_sum]
  simp only [coef_smul]
  rw [Finset.sum_eq_single τ]
  · simp [coef, cinner_U_self]
  · intro σ _ hσ
    have h0 : B.coef (B.U σ) τ = 0 := B.cinner_U_ne hσ
    rw [h0, mul_zero]
  · simp

omit [DecidableEq α] in
lemma mulVec_U (σ : ι → B.J) :
    (kernelPow A ι).mulVec (B.U σ) = (B.lamP σ : ℂ) • B.U σ := by
  funext x
  simp only [Matrix.mulVec, dotProduct, kernelPow, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    U, lamP]
  have h1 : ∀ y : ι → α, (∏ i, A (x i) (y i)) * ∏ i, B.u (σ i) (y i) =
      ∏ i, (A (x i) (y i) * B.u (σ i) (y i)) := fun y => (Finset.prod_mul_distrib).symm
  simp only [h1]
  rw [← Fintype.prod_sum (fun i b => A (x i) b * B.u (σ i) b)]
  rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := congrFun (B.eigen (σ i)) (x i)
  simpa [Matrix.mulVec, dotProduct] using this

lemma mulVec_expand (g : (ι → α) → ℂ) :
    (kernelPow A ι).mulVec g = ∑ σ, ((B.lamP σ : ℂ) * B.coef g σ) • B.U σ := by
  conv_lhs => rw [B.expand_pi g]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mulVec_smul, mulVec_U, smul_smul, mul_comm]

lemma coef_mulVec (g : (ι → α) → ℂ) (σ : ι → B.J) :
    B.coef ((kernelPow A ι).mulVec g) σ = B.lamP σ * B.coef g σ := by
  rw [mulVec_expand, coef_of_expansion]

omit [DecidableEq α] in
lemma coef_eq_zero_of_mem_block {S : Finset ι} {g : (ι → α) → ℂ}
    (hg : g ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S)
    {σ : ι → B.J} (hσ : B.typ σ ≠ S) : B.coef g σ = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨v, hv1, hv2, rfl⟩ := hg
    have : ∃ i, ¬ (i ∈ B.typ σ ↔ i ∈ S) := by
      by_contra hcon
      push Not at hcon
      exact hσ (Finset.ext hcon)
    obtain ⟨i, hi⟩ := this
    unfold coef U
    rw [cinner_pi_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [B.mem_typ] at hi
    by_cases hS : i ∈ S
    · have hV' : ¬ B.isV (σ i) := fun h => hi ⟨fun _ => hS, fun _ => h⟩ |>.elim
      have := B.mem_W _ hV' (v i) (hv1 i hS)
      rw [cinner_comm, this]; simp
    · have hV' : B.isV (σ i) := by
        by_contra h
        exact hi ⟨fun h' => absurd h' h, fun h' => absurd h' hS⟩
      exact hv2 i hS _ (B.mem_V _ hV')
  | zero => exact cinner_zero_left _ _
  | add x y _ _ hx hy => rw [coef_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coef_smul, hx, mul_zero]

omit [DecidableEq α] [DecidableEq ι] in
lemma U_mem_block {S : Finset ι} {σ : ι → B.J} (hσ : B.typ σ = S) :
    B.U σ ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S :=
  Submodule.subset_span ⟨fun i => B.u (σ i),
    fun i hi => B.mem_V _ ((B.mem_typ σ i).1 (hσ ▸ hi)),
    fun i hi => B.mem_W _ (fun h => hi (hσ ▸ (B.mem_typ σ i).2 h)), rfl⟩

lemma mem_block_of_coef {S : Finset ι} {g : (ι → α) → ℂ}
    (h : ∀ σ, B.typ σ ≠ S → B.coef g σ = 0) :
    g ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S := by
  have e := B.expand_pi g
  rw [e]
  refine Submodule.sum_mem _ fun σ _ => ?_
  by_cases hσ : B.typ σ = S
  · exact Submodule.smul_mem _ _ (B.U_mem_block hσ)
  · rw [h σ hσ, zero_smul]; exact Submodule.zero_mem _

omit [DecidableEq α] in
lemma lamP_bounds (ha : 0 ≤ a) {σ : ι → B.J} {S : Finset ι} (hσ : B.typ σ = S) :
    a ^ (Fintype.card ι - S.card) ≤ B.lamP σ ∧ B.lamP σ ≤ b ^ (Fintype.card ι - S.card) := by
  have hS : ∀ i ∈ S, B.lam (σ i) = 1 := fun i hi =>
    B.lam_V _ ((B.mem_typ σ i).1 (hσ ▸ hi))
  have hSc : ∀ i ∈ Sᶜ, a ≤ B.lam (σ i) ∧ B.lam (σ i) ≤ b := fun i hi =>
    B.lam_W _ (fun h => (Finset.mem_compl.1 hi) (hσ ▸ (B.mem_typ σ i).2 h))
  have hsplit : B.lamP σ = (∏ i ∈ S, B.lam (σ i)) * ∏ i ∈ Sᶜ, B.lam (σ i) := by
    unfold lamP
    rw [Finset.prod_mul_prod_compl]
  have h1 : ∏ i ∈ S, B.lam (σ i) = 1 := Finset.prod_eq_one hS
  rw [hsplit, h1, one_mul]
  have hc : (Sᶜ).card = Fintype.card ι - S.card := Finset.card_compl S
  constructor
  · calc a ^ (Fintype.card ι - S.card) = ∏ i ∈ Sᶜ, a := by rw [Finset.prod_const, hc]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => ha) fun i hi => (hSc i hi).1
  · calc ∏ i ∈ Sᶜ, B.lam (σ i) ≤ ∏ i ∈ Sᶜ, b :=
          Finset.prod_le_prod₀ (fun i hi => ha.trans (hSc i hi).1) fun i hi => (hSc i hi).2
      _ = b ^ (Fintype.card ι - S.card) := by rw [Finset.prod_const, hc]

lemma mul_star_eq (x : ℂ) : x * star x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma cl2sq_eq_sum (g : (ι → α) → ℂ) : cl2sq μ g = ∑ σ, ‖B.coef g σ‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [cl2sq_cast, B.parseval, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun σ _ => mul_star_eq _

omit [DecidableEq α] in
lemma coef_decomp {g : (ι → α) → ℂ} {h : Finset ι → (ι → α) → ℂ}
    (hh : ∀ S, h S ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S)
    (hg : g = ∑ S, h S) (σ : ι → B.J) : B.coef g σ = B.coef (h (B.typ σ)) σ := by
  rw [hg, coef_sum, Finset.sum_eq_single (B.typ σ)]
  · intro S _ hS
    exact B.coef_eq_zero_of_mem_block (hh S) (Ne.symm hS)
  · simp

lemma sum_cl2sq_mul {g : (ι → α) → ℂ} {h : Finset ι → (ι → α) → ℂ}
    (hh : ∀ S, h S ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S)
    (hg : g = ∑ S, h S) (c : Finset ι → ℝ) :
    ∑ S, cl2sq μ (h S) * c S = ∑ σ, c (B.typ σ) * ‖B.coef g σ‖ ^ 2 := by
  simp only [B.cl2sq_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single (B.typ σ)]
  · rw [B.coef_decomp hh hg σ]; ring
  · intro S _ hS
    rw [B.coef_eq_zero_of_mem_block (hh S) (Ne.symm hS)]; simp
  · simp

lemma cinner_mulVec_eq (g : (ι → α) → ℂ) :
    (μ.pi ι).cinner g ((kernelPow A ι).mulVec g) =
      ((∑ σ, B.lamP σ * ‖B.coef g σ‖ ^ 2 : ℝ) : ℂ) := by
  rw [B.parseval, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coef_mulVec]
  have : star ((B.lamP σ : ℂ) * B.coef g σ) = (B.lamP σ : ℂ) * star (B.coef g σ) := by
    simp [star_mul']
  rw [this, mul_left_comm, mul_star_eq]
  push_cast
  ring

lemma cl2sq_mulVec_eq (g : (ι → α) → ℂ) :
    cl2sq μ ((kernelPow A ι).mulVec g) = ∑ σ, B.lamP σ ^ 2 * ‖B.coef g σ‖ ^ 2 := by
  rw [B.cl2sq_eq_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coef_mulVec, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

end AdBasis
end Product

section Holder
variable {α : Type} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- Parseval for an orthogonal decomposition. -/
lemma cl2sq_sum_of_orth {ι : Type} [Fintype ι] [DecidableEq ι] (μ : FinProb α)
    (f : (ι → α) → ℂ) (h : Finset ι → (ι → α) → ℂ)
    (horth : ∀ J J' : Finset ι, J ≠ J' → (μ.pi ι).cinner (h J) (h J') = 0)
    (hf : f = ∑ J, h J) : cl2sq μ f = ∑ J, cl2sq μ (h J) := by
  apply Complex.ofReal_injective
  rw [cl2sq_cast, Complex.ofReal_sum]
  simp only [cl2sq_cast]
  rw [hf, cinner_sum_left]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [cinner_sum_right, Finset.sum_eq_single J]
  · intro J' _ hJ'
    exact horth J J' (Ne.symm hJ')
  · simp

/-- Weighted Jensen (Hölder) inequality in the form `(∑ w z)^A ≤ (∑ w)^(A-1) ∑ w z^A`. -/
lemma weighted_power_mean {γ : Type*} (s : Finset γ) (w z : γ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hz : ∀ i ∈ s, 0 ≤ z i) {A : ℝ} (hA : 1 ≤ A) :
    (∑ i ∈ s, w i * z i) ^ A ≤ (∑ i ∈ s, w i) ^ (A - 1) * ∑ i ∈ s, w i * z i ^ A := by
  have hA0 : 0 < A := by linarith
  set W := ∑ i ∈ s, w i with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  rcases hW0.eq_or_lt with hW | hW
  · have hw0 : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).1 hW.symm
    rw [Finset.sum_eq_zero (fun i hi => by rw [hw0 i hi, zero_mul]),
      Finset.sum_eq_zero (fun i hi => by rw [hw0 i hi, zero_mul]), mul_zero,
      Real.zero_rpow hA0.ne']
  · have hJ := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / W) z
      (fun i hi => div_nonneg (hw i hi) hW0)
      (by rw [← Finset.sum_div, ← hWdef, div_self hW.ne']) hz hA
    have e1 : ∑ i ∈ s, w i / W * z i = (∑ i ∈ s, w i * z i) / W := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ s, w i / W * z i ^ A = (∑ i ∈ s, w i * z i ^ A) / W := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, Real.div_rpow (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hz i hi)) hW0]
      at hJ
    have hWA : 0 < W ^ A := Real.rpow_pos_of_pos hW A
    rw [div_le_div_iff₀ hWA hW] at hJ
    have h3 : W ^ A = W ^ (A - 1) * W := by
      rw [← Real.rpow_add_one hW.ne']; congr 1; ring
    rw [h3] at hJ
    have := hJ
    nlinarith [mul_pos hW (Real.rpow_pos_of_pos hW (A - 1))]

end Holder

section Chains
variable {S : Type} [Fintype S] [DecidableEq S]

lemma one_sub_rpow_le {c δ A C : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 2 * C / c ≤ A)
    (hcδ : c * δ ≤ 1) (hAcδ : A * c * δ ≤ 1) : (1 - c * δ) ^ A ≤ 1 - C * δ := by
  have hA0 : 0 ≤ A := by
    have : 0 ≤ 2 * C / c := by positivity
    linarith
  set x := c * δ with hx
  have hx0 : 0 < x := mul_pos hc hδ
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h2 : (1 - x) ^ A ≤ Real.exp (-x) ^ A :=
    Real.rpow_le_rpow (by linarith) h1 hA0
  have h3 : Real.exp (-x) ^ A = Real.exp (-(A * x)) := by
    rw [← Real.exp_mul]; congr 1; ring
  set y := A * x with hy
  have hy0 : 0 ≤ y := mul_nonneg hA0 hx0.le
  have hy1 : y ≤ 1 := by rw [hy, hx]; nlinarith
  have h4 : Real.exp (-y) ≤ 1 - y / 2 := by
    have h5 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h6 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have h7 : 0 < Real.exp (-y) := Real.exp_pos _
    nlinarith [Real.exp_pos y]
  have h8 : C * δ ≤ y / 2 := by
    rw [hy, hx]
    have : 2 * C ≤ A * c := by
      rw [div_le_iff₀ hc] at hA; linarith
    nlinarith
  calc (1 - x) ^ A ≤ Real.exp (-x) ^ A := h2
    _ = Real.exp (-y) := h3
    _ ≤ 1 - y / 2 := h4
    _ ≤ 1 - C * δ := by linarith

omit [DecidableEq S] in
lemma cmat_selfadj (T : StochMat S) (μ : FinProb S) (hr : T.IsReversible μ) (f g : S → ℂ) :
    μ.cinner (T.cmat.mulVec f) g = μ.cinner f (T.cmat.mulVec g) := by
  simp only [cinner_def, Matrix.mulVec, dotProduct, StochMat.cmat, Matrix.of_apply, star_sum,
    star_mul', Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ a b : S, (μ.prob a : ℂ) * (T.prob a b : ℂ) = (μ.prob b : ℂ) * (T.prob b a : ℂ) := by
    intro a b; exact_mod_cast hr a b
  have h2 : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => by simp
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (f a * star (g b)) * h1 b a

omit [DecidableEq S] in
lemma mulVec_eq_of_supp (T T' : StochMat S)
    (hsupp : ∀ x y, x ≠ y → 0 < T'.prob x y → 0 < T.prob x y) {v : S → ℂ}
    (hv : v ∈ T.constOnComp) : T'.cmat.mulVec v = v := by
  funext a
  simp only [Matrix.mulVec, dotProduct, StochMat.cmat, Matrix.of_apply]
  have h1 : ∀ b, (T'.prob a b : ℂ) * v b = (T'.prob a b : ℂ) * v a := by
    intro b
    by_cases hp : T'.prob a b = 0
    · simp [hp]
    · have hpos : 0 < T'.prob a b := lt_of_le_of_ne (T'.nonneg a b) (Ne.symm hp)
      by_cases hab : a = b
      · rw [hab]
      · have hT : 0 < T.prob a b := hsupp a b hab hpos
        have hadj : T.graph.Adj a b := (graph_adj_iff T a b).2 ⟨hab, Or.inl hT⟩
        rw [hv a b hadj.reachable]
  rw [Finset.sum_congr rfl fun b _ => h1 b, ← Finset.sum_mul, ← Complex.ofReal_sum, T'.row_sum]
  simp

omit [DecidableEq S] in
lemma orthSet_mulVec (T : StochMat S) (μ : FinProb S) (hr : T.IsReversible μ)
    {V : Submodule ℂ (S → ℂ)} (hV : ∀ v ∈ V, T.cmat.mulVec v = v) :
    ∀ g ∈ orthSet μ (V : Set (S → ℂ)), T.cmat.mulVec g ∈ orthSet μ (V : Set (S → ℂ)) := by
  intro g hg v hv
  rw [cmat_selfadj T μ hr, hV v hv]
  exact hg v hv

open scoped Classical in
omit [DecidableEq S] in
lemma orth_comp (T : StochMat S) (μ : FinProb S) (g : S → ℂ)
    (hg : g ∈ orthSet μ (T.constOnComp : Set (S → ℂ))) (x : S) :
    ∑ a ∈ Finset.univ.filter
      (fun a => T.graph.connectedComponentMk a = T.graph.connectedComponentMk x),
        (μ.prob a : ℂ) * g a = 0 := by
  have hmem : (fun a => if T.graph.connectedComponentMk a = T.graph.connectedComponentMk x
      then (1 : ℂ) else 0) ∈ T.constOnComp := by
    intro a b hab
    have : T.graph.connectedComponentMk a = T.graph.connectedComponentMk b :=
      SimpleGraph.ConnectedComponent.eq.2 hab
    simp only [this]
  have h := hg _ hmem
  rw [← h, cinner_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

omit [DecidableEq S] in
/-- real eigenvalue and a unit-norm rescaling of an eigenfunction of a reversible chain -/
lemma eig_info (T : StochMat S) (μ : FinProb S) (hμ : ∀ a, 0 < μ.prob a) (hr : T.IsReversible μ)
    (g : S → ℂ) (hg0 : g ≠ 0) (l : ℂ) (hl : T.cmat.mulVec g = l • g) :
    ∃ r t : ℝ, l = r ∧ 0 < t ∧
      (∀ a, ∑ b, (T.prob a b : ℂ) * ((t : ℂ) • g) b = r * ((t : ℂ) • g) a) ∧
      ∑ a, μ.prob a * ‖((t : ℂ) • g) a‖ ^ 2 = 1 := by
  have hN : 0 < ∑ a, μ.prob a * ‖g a‖ ^ 2 := by
    obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
      by_contra h; push Not at h; exact hg0 (funext h)
    exact Finset.sum_pos' (fun a _ => mul_nonneg (μ.nonneg a) (sq_nonneg _))
      ⟨a, Finset.mem_univ a, mul_pos (hμ a) (by positivity)⟩
  set N := ∑ a, μ.prob a * ‖g a‖ ^ 2 with hNdef
  have hgg : μ.cinner g g = (N : ℂ) := by
    rw [cinner_self_eq]; rfl
  have hreal : l = (l.re : ℂ) := by
    have h1 := cmat_selfadj T μ hr g g
    rw [hl, cinner_smul_left, cinner_smul_right, hgg] at h1
    have h2 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have h3 : l = star l := mul_right_cancel₀ h2 h1
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h3
      simp only [Complex.star_def, Complex.conj_im, Complex.ofReal_im] at this ⊢
      linarith
  refine ⟨l.re, 1 / Real.sqrt N, hreal, by positivity, ?_, ?_⟩
  · intro a
    have := congrFun hl a
    simp only [Matrix.mulVec, dotProduct, StochMat.cmat, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    calc ∑ b, (T.prob a b : ℂ) * ((1 / Real.sqrt N : ℝ) * g b)
        = (1 / Real.sqrt N : ℝ) * ∑ b, (T.prob a b : ℂ) * g b := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      _ = (1 / Real.sqrt N : ℝ) * (l * g a) := by rw [this]
      _ = (l.re : ℂ) * ((1 / Real.sqrt N : ℝ) * g a) := by rw [← hreal]; ring
  · have : ∀ a, μ.prob a * ‖(((1 / Real.sqrt N : ℝ) : ℂ) • g) a‖ ^ 2 =
        (1 / N) * (μ.prob a * ‖g a‖ ^ 2) := by
      intro a
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt N), mul_pow, div_pow,
        Real.sq_sqrt hN.le]
      ring
    rw [Finset.sum_congr rfl fun a _ => this a, ← Finset.mul_sum, ← hNdef]
    field_simp

end Chains

section Blocks
variable {α : Type} [Fintype α] [DecidableEq α]

theorem StochMat.apply_pi_eq_mulVec (T : StochMat α) (ι : Type) [Fintype ι] [DecidableEq ι]
    (g : (ι → α) → ℂ) : (T.pi ι).apply g = (kernelPow T.cmat ι).mulVec g := by
  funext x
  simp only [StochMat.apply, Matrix.mulVec, dotProduct, kernelPow, Matrix.of_apply, StochMat.pi,
    StochMat.cmat]
  refine Finset.sum_congr rfl fun y _ => ?_
  push_cast
  rfl

open scoped ComplexOrder in
theorem tensor_block_bound (μ : FinProb α) (hμ : ∀ a, 0 < μ.prob a)
    (V : Submodule ℂ (α → ℂ)) (A : Matrix α α ℂ)
    (hself : ∀ f g, μ.cinner (A.mulVec f) g = μ.cinner f (A.mulVec g))
    (hV : ∀ v ∈ V, A.mulVec v = v)
    (hV' : ∀ g ∈ orthSet μ (V : Set (α → ℂ)), A.mulVec g ∈ orthSet μ (V : Set (α → ℂ)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (heig : ∀ g ∈ orthSet μ (V : Set (α → ℂ)), g ≠ 0 → ∀ l : ℂ, A.mulVec g = l • g →
      ∃ r : ℝ, l = r ∧ a ≤ r ∧ r ≤ b)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    (∀ S T : Finset ι, S ≠ T →
      ∀ g ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S,
      ∀ g' ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) T,
        (μ.pi ι).cinner g g' = 0) ∧
    (∀ g : (ι → α) → ℂ, ∃ h : Finset ι → (ι → α) → ℂ,
      (∀ S, h S ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S) ∧
        g = ∑ S, h S) ∧
    (∀ S : Finset ι, ∀ g ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S,
      (kernelPow A ι).mulVec g ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S) ∧
    ∀ (g : (ι → α) → ℂ) (h : Finset ι → (ι → α) → ℂ),
      (∀ S, h S ∈ blockSpace (V : Set (α → ℂ)) (orthSet μ (V : Set (α → ℂ))) S) →
      g = ∑ S, h S →
        (((∑ S, cl2sq μ (h S) * a ^ (Fintype.card ι - S.card) : ℝ) : ℂ) ≤
            (μ.pi ι).cinner g ((kernelPow A ι).mulVec g)) ∧
        ((μ.pi ι).cinner g ((kernelPow A ι).mulVec g) ≤
            ((∑ S, cl2sq μ (h S) * b ^ (Fintype.card ι - S.card) : ℝ) : ℂ)) ∧
        (∑ S, cl2sq μ (h S) * a ^ (2 * (Fintype.card ι - S.card)) ≤
            cl2sq μ ((kernelPow A ι).mulVec g)) ∧
        (cl2sq μ ((kernelPow A ι).mulVec g) ≤
            ∑ S, cl2sq μ (h S) * b ^ (2 * (Fintype.card ι - S.card))) := by
  obtain ⟨J, hJ, u, isV, lam, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_adapted_basis μ hμ V A hself hV hV' hb heig
  let B : AdBasis μ V A a b := ⟨J, u, isV, lam, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S T hST g hg g' hg'
    rw [B.parseval g g']
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hσ : B.typ σ = S
    · rw [B.coef_eq_zero_of_mem_block hg' (hσ ▸ hST : B.typ σ ≠ T)]; simp
    · rw [B.coef_eq_zero_of_mem_block hg hσ]; simp
  · intro g
    refine ⟨fun S => ∑ σ ∈ Finset.univ.filter (fun σ => B.typ σ = S), B.coef g σ • B.U σ,
      fun S => Submodule.sum_mem _ fun σ hσ =>
        Submodule.smul_mem _ _ (B.U_mem_block (Finset.mem_filter.1 hσ).2), ?_⟩
    rw [Finset.sum_fiberwise Finset.univ (fun σ => B.typ σ) (fun σ => B.coef g σ • B.U σ)]
    exact B.expand_pi g
  · intro S g hg
    refine B.mem_block_of_coef fun σ hσ => ?_
    rw [B.coef_mulVec, B.coef_eq_zero_of_mem_block hg hσ, mul_zero]
  · intro g h hh hg
    have hlow : ∀ σ : ι → B.J, a ^ (Fintype.card ι - (B.typ σ).card) ≤ B.lamP σ :=
      fun σ => (B.lamP_bounds ha rfl).1
    have hup : ∀ σ : ι → B.J, B.lamP σ ≤ b ^ (Fintype.card ι - (B.typ σ).card) :=
      fun σ => (B.lamP_bounds ha rfl).2
    have hlam0 : ∀ σ : ι → B.J, 0 ≤ B.lamP σ := fun σ =>
      (pow_nonneg ha _).trans (hlow σ)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [B.cinner_mulVec_eq g, Complex.real_le_real,
        B.sum_cl2sq_mul hh hg (fun S => a ^ (Fintype.card ι - S.card))]
      exact Finset.sum_le_sum fun σ _ =>
        mul_le_mul_of_nonneg_right (hlow σ) (sq_nonneg _)
    · rw [B.cinner_mulVec_eq g, Complex.real_le_real,
        B.sum_cl2sq_mul hh hg (fun S => b ^ (Fintype.card ι - S.card))]
      exact Finset.sum_le_sum fun σ _ =>
        mul_le_mul_of_nonneg_right (hup σ) (sq_nonneg _)
    · rw [B.cl2sq_mulVec_eq g,
        B.sum_cl2sq_mul hh hg (fun S => a ^ (2 * (Fintype.card ι - S.card)))]
      refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [pow_mul']
      exact pow_le_pow_left₀ (pow_nonneg ha _) (hlow σ) 2
    · rw [B.cl2sq_mulVec_eq g,
        B.sum_cl2sq_mul hh hg (fun S => b ^ (2 * (Fintype.card ι - S.card)))]
      refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [pow_mul' b]
      exact pow_le_pow_left₀ (hlam0 σ) (hup σ) 2

/-- Strengthening of `block_norm_bounds` used by `compare_averaging_ops`: it also provides the
orthogonality and the existence of the block decomposition, and `c * δ₀ ≤ 1`. -/
theorem block_norm_bounds_aux (m : ℕ) {α₀ β : ℝ} (hα : 0 < α₀) (hβ : 0 < β) :
    ∃ c A δ₀ : ℝ, 0 < c ∧ 1 ≤ A ∧ 0 < δ₀ ∧ c * δ₀ ≤ 1 ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ : FinProb S, (∀ a, α₀ ≤ μ.prob a) →
      ∀ T T' : StochMat S, T.IsStationary μ → T.IsReversible μ →
        T'.IsStationary μ → T'.IsReversible μ →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        (∀ x, 1 - δ ≤ T.prob x x) → (∀ x, 1 - δ ≤ T'.prob x x) →
        (∀ x y, x ≠ y → 0 < T'.prob x y → 0 < T.prob x y) →
        (∀ x y, x ≠ y → 0 < T.prob x y → β * δ ≤ T.prob x y) →
        (∀ x y, x ≠ y → 0 < T'.prob x y → β * δ ≤ T'.prob x y) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
        (∀ J : Finset ι, ∀ g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J,
          (T.pi ι).apply g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
              (orthSet μ (T.constOnComp : Set (S → ℂ))) J ∧
          (T'.pi ι).apply g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
              (orthSet μ (T.constOnComp : Set (S → ℂ))) J) ∧
        (∀ J J' : Finset ι, J ≠ J' →
          ∀ g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J,
          ∀ g' ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J',
            (μ.pi ι).cinner g g' = 0) ∧
        (∀ f : (ι → S) → ℂ, ∃ h : Finset ι → (ι → S) → ℂ,
          (∀ J, h J ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J) ∧ f = ∑ J, h J) ∧
        ∀ (f : (ι → S) → ℂ) (h : Finset ι → (ι → S) → ℂ),
          (∀ J, h J ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J) → f = ∑ J, h J →
          cl2sq μ ((T.pi ι).apply f) ≤
              ∑ J, cl2sq μ (h J) * (1 - c * δ) ^ (2 * (Fintype.card ι - J.card)) ∧
          ∑ J, cl2sq μ (h J) * (1 - c * δ) ^ (2 * A * ((Fintype.card ι - J.card : ℕ) : ℝ)) ≤
              cl2sq μ ((T'.pi ι).apply f) := by
  set c₁ : ℝ := α₀ / (2 * ((m : ℝ) + 1) ^ 3) with hc₁
  set C : ℝ := 2 / α₀ with hC
  have hc₁0 : 0 < c₁ := by positivity
  have hC0 : 0 < C := by positivity
  set c : ℝ := c₁ * β with hc
  have hc0 : 0 < c := mul_pos hc₁0 hβ
  set A : ℝ := max 1 (2 * C / c) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAc : 2 * C / c ≤ A := le_max_right _ _
  have hAc0 : 0 < A * c := by positivity
  set δ₀ : ℝ := min (1 / (1 + β)) (min (α₀ / 2) (1 / (A * c))) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hcδ₀ : c * δ₀ ≤ 1 := by
    have h1 : δ₀ ≤ 1 / (A * c) := (min_le_right _ _).trans (min_le_right _ _)
    calc c * δ₀ ≤ c * (1 / (A * c)) := mul_le_mul_of_nonneg_left h1 hc0.le
      _ = 1 / A := by field_simp
      _ ≤ 1 := by rw [div_le_one (by linarith)]; exact hA1
  refine ⟨c, A, δ₀, hc0, hA1, hδ₀pos, hcδ₀, ?_⟩
  intro S _ _ hcard μ hμα T T' hs hr hs' hr' δ hδ hδδ₀ hd hd' hsupp hβT _ ι _ _
  have hμpos : ∀ a, 0 < μ.prob a := fun a => lt_of_lt_of_le hα (hμα a)
  have hδ1 : δ ≤ 1 / (1 + β) := hδδ₀.trans (min_le_left _ _)
  have hδ2 : δ ≤ α₀ / 2 := hδδ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : δ ≤ 1 / (A * c) := hδδ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCδ : C * δ ≤ 1 := by
    calc C * δ ≤ C * (α₀ / 2) := mul_le_mul_of_nonneg_left hδ2 hC0.le
      _ = 1 := by rw [hC]; field_simp
  have hAcδ : A * c * δ ≤ 1 := by
    calc A * c * δ ≤ A * c * (1 / (A * c)) := mul_le_mul_of_nonneg_left hδ3 hAc0.le
      _ = 1 := by field_simp
  have hcδ : c * δ ≤ 1 := by nlinarith
  have hcδ0 : 0 ≤ c * δ := by positivity
  have hβδ : β * δ ≤ 1 - δ := by
    have : δ * (1 + β) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hδ1
    nlinarith
  have hbase : (1 - c * δ) ^ A ≤ 1 - C * δ := one_sub_rpow_le hc0 hδ hC0.le hAc hcδ hAcδ
  have hCδ0 : 0 ≤ 1 - C * δ := by linarith
  have hCδ1 : 0 ≤ C * δ := by positivity
  have hn : (Fintype.card S : ℝ) ≤ (m : ℝ) + 1 := by
    have : (Fintype.card S : ℝ) ≤ m := by exact_mod_cast hcard
    linarith
  have hVfix : ∀ v ∈ T.constOnComp, T.cmat.mulVec v = v := fun v hv =>
    mulVec_eq_of_supp T T (fun x y _ h => h) hv
  have hVfix' : ∀ v ∈ T.constOnComp, T'.cmat.mulVec v = v := fun v hv =>
    mulVec_eq_of_supp T T' hsupp hv
  have hselfT := cmat_selfadj T μ hr
  have hselfT' := cmat_selfadj T' μ hr'
  have hV'T := orthSet_mulVec T μ hr hVfix
  have hV'T' := orthSet_mulVec T' μ hr' hVfix'
  have heigT : ∀ g ∈ orthSet μ (T.constOnComp : Set (S → ℂ)), g ≠ 0 → ∀ l : ℂ,
      T.cmat.mulVec g = l • g → ∃ r : ℝ, l = r ∧ 0 ≤ r ∧ r ≤ 1 - c * δ := by
    intro g hg hg0 l hl
    obtain ⟨r, t, hlr, ht, hgeig, hnorm⟩ := eig_info T μ hμpos hr g hg0 l hl
    refine ⟨r, hlr, ?_, ?_⟩
    · have h1 := lower_bound_eig T μ α₀ hα hμα hs _ r hgeig hnorm δ hd
      have h2 : 1 - 2 / α₀ * δ = 1 - C * δ := by rw [hC]
      linarith
    · have hg' : ((t : ℂ) • g) ∈ orthSet μ (T.constOnComp : Set (S → ℂ)) := by
        intro v hv
        rw [cinner_smul_left, hg v hv, mul_zero]
      have hTpos : ∀ a b, 0 < T.prob a b → β * δ ≤ T.prob a b := by
        intro a b hpos
        by_cases hab : a = b
        · subst hab; linarith [hd a]
        · exact hβT a b hab hpos
      have h1 := gap_bound T μ α₀ hα hμα hs ((m : ℝ) + 1) hn _ r hgeig hnorm
        (orth_comp T μ _ hg') (β * δ) (by positivity) hTpos
      have h2 : α₀ * (β * δ) / (2 * ((m : ℝ) + 1) ^ 3) = c * δ := by
        rw [hc, hc₁]; field_simp
      linarith
  have heigT' : ∀ g ∈ orthSet μ (T.constOnComp : Set (S → ℂ)), g ≠ 0 → ∀ l : ℂ,
      T'.cmat.mulVec g = l • g → ∃ r : ℝ, l = r ∧ 1 - C * δ ≤ r ∧ r ≤ 1 := by
    intro g _ hg0 l hl
    obtain ⟨r, t, hlr, ht, hgeig, hnorm⟩ := eig_info T' μ hμpos hr' g hg0 l hl
    refine ⟨r, hlr, ?_, lam_le_one T' μ hs' _ r hgeig hnorm⟩
    have h1 := lower_bound_eig T' μ α₀ hα hμα hs' _ r hgeig hnorm δ hd'
    have h2 : 1 - 2 / α₀ * δ = 1 - C * δ := by rw [hC]
    linarith
  obtain ⟨o1, d2, i3, b4⟩ := tensor_block_bound μ hμpos T.constOnComp T.cmat hselfT hVfix hV'T
    (a := 0) (b := 1 - c * δ) le_rfl (by linarith) (by linarith) heigT ι
  obtain ⟨o1', d2', i3', b4'⟩ := tensor_block_bound μ hμpos T.constOnComp T'.cmat hselfT' hVfix'
    hV'T' (a := 1 - C * δ) (b := 1) hCδ0 (by linarith) le_rfl heigT' ι
  refine ⟨?_, o1, d2, ?_⟩
  · intro J g hg
    rw [StochMat.apply_pi_eq_mulVec, StochMat.apply_pi_eq_mulVec]
    exact ⟨i3 J g hg, i3' J g hg⟩
  · intro f h hh hf
    obtain ⟨-, -, h3, -⟩ := b4' f h hh hf
    obtain ⟨-, -, -, h4⟩ := b4 f h hh hf
    rw [StochMat.apply_pi_eq_mulVec, StochMat.apply_pi_eq_mulVec]
    refine ⟨h4, le_trans (Finset.sum_le_sum fun J _ => ?_) h3⟩
    refine mul_le_mul_of_nonneg_left ?_ (cl2sq_nonneg μ _)
    have hx : (0 : ℝ) ≤ 1 - c * δ := by linarith
    have e : (1 - c * δ) ^ (2 * A * ((Fintype.card ι - J.card : ℕ) : ℝ)) =
        ((1 - c * δ) ^ A) ^ (2 * (Fintype.card ι - J.card)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hx _) hbase _

theorem block_norm_bounds (m : ℕ) {α₀ β : ℝ} (hα : 0 < α₀) (hβ : 0 < β) :
    ∃ c A δ₀ : ℝ, 0 < c ∧ 1 ≤ A ∧ 0 < δ₀ ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ : FinProb S, (∀ a, α₀ ≤ μ.prob a) →
      ∀ T T' : StochMat S, T.IsStationary μ → T.IsReversible μ →
        T'.IsStationary μ → T'.IsReversible μ →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        (∀ x, 1 - δ ≤ T.prob x x) → (∀ x, 1 - δ ≤ T'.prob x x) →
        (∀ x y, x ≠ y → 0 < T'.prob x y → 0 < T.prob x y) →
        (∀ x y, x ≠ y → 0 < T.prob x y → β * δ ≤ T.prob x y) →
        (∀ x y, x ≠ y → 0 < T'.prob x y → β * δ ≤ T'.prob x y) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
        (∀ J : Finset ι, ∀ g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J,
          (T.pi ι).apply g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
              (orthSet μ (T.constOnComp : Set (S → ℂ))) J ∧
          (T'.pi ι).apply g ∈ blockSpace (T.constOnComp : Set (S → ℂ))
              (orthSet μ (T.constOnComp : Set (S → ℂ))) J) ∧
        ∀ (f : (ι → S) → ℂ) (h : Finset ι → (ι → S) → ℂ),
          (∀ J, h J ∈ blockSpace (T.constOnComp : Set (S → ℂ))
            (orthSet μ (T.constOnComp : Set (S → ℂ))) J) → f = ∑ J, h J →
          cl2sq μ ((T.pi ι).apply f) ≤
              ∑ J, cl2sq μ (h J) * (1 - c * δ) ^ (2 * (Fintype.card ι - J.card)) ∧
          ∑ J, cl2sq μ (h J) * (1 - c * δ) ^ (2 * A * ((Fintype.card ι - J.card : ℕ) : ℝ)) ≤
              cl2sq μ ((T'.pi ι).apply f) := by
  obtain ⟨c, A, δ₀, hc, hA, hδ₀, -, H⟩ := block_norm_bounds_aux m hα hβ
  refine ⟨c, A, δ₀, hc, hA, hδ₀, ?_⟩
  intro S _ _ hcard μ hμα T T' hs hr hs' hr' δ hδ hδδ₀ hd hd' hsupp hβT hβT' ι _ _
  obtain ⟨h1, -, -, h4⟩ := H S hcard μ hμα T T' hs hr hs' hr' δ hδ hδδ₀ hd hd' hsupp hβT hβT' ι
  exact ⟨h1, h4⟩

theorem holder_interpolation {A q : ℝ} (hA : 1 ≤ A) (hq0 : 0 ≤ q)
    (μ : FinProb α) (ι : Type) [Fintype ι] [DecidableEq ι] (T T' : StochMat α)
    (f : (ι → α) → ℂ) (h : Finset ι → (ι → α) → ℂ)
    (horth : ∀ J J' : Finset ι, J ≠ J' → (μ.pi ι).cinner (h J) (h J') = 0)
    (hf : f = ∑ J, h J)
    (hup : cl2sq μ ((T.pi ι).apply f) ≤
      ∑ J, cl2sq μ (h J) * q ^ (2 * (Fintype.card ι - J.card)))
    (hlow : ∑ J, cl2sq μ (h J) * q ^ (2 * A * ((Fintype.card ι - J.card : ℕ) : ℝ)) ≤
      cl2sq μ ((T'.pi ι).apply f)) :
    cl2norm μ ((T.pi ι).apply f) ^ (2 * A) ≤
        cl2norm μ f ^ (2 * (A - 1)) * cl2sq μ ((T'.pi ι).apply f) ∧
    (cl2norm μ f ≤ 1 →
      cl2norm μ ((T.pi ι).apply f) ≤ cl2norm μ ((T'.pi ι).apply f) ^ (1 / A)) := by
  have hAp : 0 < A := by linarith
  have hW := cl2sq_sum_of_orth μ f h horth hf
  have hw : ∀ J ∈ (Finset.univ : Finset (Finset ι)), 0 ≤ cl2sq μ (h J) := fun J _ =>
    cl2sq_nonneg μ _
  have hz : ∀ J ∈ (Finset.univ : Finset (Finset ι)),
      0 ≤ q ^ (2 * (Fintype.card ι - J.card)) := fun J _ => pow_nonneg hq0 _
  have hzA : ∀ J : Finset ι, (q ^ (2 * (Fintype.card ι - J.card))) ^ A =
      q ^ (2 * A * ((Fintype.card ι - J.card : ℕ) : ℝ)) := by
    intro J
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
    congr 1
    push_cast
    ring
  have key := weighted_power_mean (Finset.univ : Finset (Finset ι)) (fun J => cl2sq μ (h J))
    (fun J => q ^ (2 * (Fintype.card ι - J.card))) hw hz hA
  simp only [hzA] at key
  have sqrt_pow : ∀ (x e : ℝ), 0 ≤ x → Real.sqrt x ^ (2 * e) = x ^ e := by
    intro x e hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    ring
  have hu0 : 0 ≤ cl2sq μ ((T.pi ι).apply f) := cl2sq_nonneg μ _
  have hu'0 : 0 ≤ cl2sq μ ((T'.pi ι).apply f) := cl2sq_nonneg μ _
  have hW0 : 0 ≤ cl2sq μ f := cl2sq_nonneg μ _
  have c1 : cl2norm μ ((T.pi ι).apply f) ^ (2 * A) ≤
      cl2norm μ f ^ (2 * (A - 1)) * cl2sq μ ((T'.pi ι).apply f) := by
    unfold cl2norm
    rw [sqrt_pow _ _ hu0, sqrt_pow _ _ hW0, hW]
    calc cl2sq μ ((T.pi ι).apply f) ^ A
        ≤ (∑ J, cl2sq μ (h J) * q ^ (2 * (Fintype.card ι - J.card))) ^ A :=
          Real.rpow_le_rpow hu0 hup hAp.le
      _ ≤ _ := key
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (Finset.sum_nonneg hw) _)
  refine ⟨c1, fun hf1 => ?_⟩
  have hn1 : cl2norm μ f ^ (2 * (A - 1)) ≤ 1 :=
    Real.rpow_le_one (Real.sqrt_nonneg _) hf1 (by linarith)
  have hy : cl2sq μ ((T'.pi ι).apply f) = cl2norm μ ((T'.pi ι).apply f) ^ 2 := by
    unfold cl2norm; rw [Real.sq_sqrt hu'0]
  have c2 : cl2norm μ ((T.pi ι).apply f) ^ (2 * A) ≤ cl2norm μ ((T'.pi ι).apply f) ^ 2 := by
    refine c1.trans ?_
    rw [hy]
    exact mul_le_of_le_one_left (sq_nonneg _) hn1
  have hx0 : 0 ≤ cl2norm μ ((T.pi ι).apply f) := Real.sqrt_nonneg _
  have hy0 : 0 ≤ cl2norm μ ((T'.pi ι).apply f) := Real.sqrt_nonneg _
  have := Real.rpow_le_rpow (Real.rpow_nonneg hx0 _) c2 (show 0 ≤ 1 / (2 * A) by positivity)
  rw [← Real.rpow_mul hx0, mul_one_div_cancel (by positivity), Real.rpow_one,
    ← Real.rpow_natCast, ← Real.rpow_mul hy0] at this
  convert this using 2
  push_cast
  field_simp

theorem compare_averaging_ops (m : ℕ) {α₀ β : ℝ} (hα : 0 < α₀) (hβ : 0 < β) :
    ∃ s δ₀ : ℝ, 0 < s ∧ 0 < δ₀ ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ μ : FinProb S, (∀ a, α₀ ≤ μ.prob a) →
      ∀ T T' : StochMat S, T.IsStationary μ → T.IsReversible μ →
        T'.IsStationary μ → T'.IsReversible μ →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        (∀ x, 1 - δ ≤ T.prob x x) → (∀ x, 1 - δ ≤ T'.prob x x) →
        (∀ x y, x ≠ y → 0 < T'.prob x y → 0 < T.prob x y) →
        (∀ x y, x ≠ y → 0 < T.prob x y → β * δ ≤ T.prob x y) →
        (∀ x y, x ≠ y → 0 < T'.prob x y → β * δ ≤ T'.prob x y) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → S) → ℂ), cl2norm μ f ≤ 1 →
        cl2norm μ ((T.pi ι).apply f) ≤ cl2norm μ ((T'.pi ι).apply f) ^ s := by
  obtain ⟨c, A, δ₀, hc, hA, hδ₀, hcδ₀, H⟩ := block_norm_bounds_aux m hα hβ
  refine ⟨1 / A, δ₀, by positivity, hδ₀, ?_⟩
  intro S _ _ hcard μ hμα T T' hs hr hs' hr' δ hδ hδδ₀ hd hd' hsupp hβT hβT' ι _ _ f hf
  obtain ⟨-, horth, hdec, hb⟩ :=
    H S hcard μ hμα T T' hs hr hs' hr' δ hδ hδδ₀ hd hd' hsupp hβT hβT' ι
  obtain ⟨h, hh, hfh⟩ := hdec f
  obtain ⟨hup, hlow⟩ := hb f h hh hfh
  have hq0 : 0 ≤ 1 - c * δ := by
    have := mul_le_mul_of_nonneg_left hδδ₀ hc.le
    linarith
  exact (holder_interpolation hA hq0 μ ι T T' f h
    (fun J J' hJ => horth J J' hJ (h J) (hh J) (h J') (hh J')) hfh hup hlow).2 hf

end Blocks
end TrackB
end RestrictedPolynomials
end
