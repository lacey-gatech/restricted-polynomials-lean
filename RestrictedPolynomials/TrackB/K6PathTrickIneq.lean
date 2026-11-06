module

public import RestrictedPolynomials.TrackB.K6PathTrickCore
public import RestrictedPolynomials.TrackB.K6PathTrick
public import RestrictedPolynomials.TrackB.PathTrickInequality

/-!
# Track B: the `n`-fold path-trick statements (tensorization)

Source: CSP_6, l. 699-740 (`lemma:pathtrick#h-tilde-reduction`,
`eq:biginduct`, `lemma:pathtrick`, `eq:3path`) for `μ^{⊗ι}`.

`k6ptReg μ ι` regroups the product measure on `(ι → X) × (ι → Y) × (ι → Z)`; the tensorization of
`margY`, `margZ`, `walkYZ`, `walkYY`, `pathWeight` and the path-trick expectation are proved here
(the private lemmas of `PathTrickInequality` are the model). The `n`-fold statements then follow
from the one-measure statements of `K6PathTrickCore`, applied to `k6ptReg μ ι`. `k6pt_pathtrick` uses
`from_mu_to_path_tensor`. `k6pt_eq3path` has no connectivity hypothesis (the correlation bound is the
composition of three trick inequalities). The `_eps` forms add `0 ≤ ε` as typing.
-/

@[expose] public section


open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### Regrouping `μ^{⊗ι}` as a distribution on `Σ^ι × Γ^ι × Φ^ι` -/
section K6ptTensor
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- `(ι → X × Y × Z) ≃ (ι → X) × (ι → Y) × (ι → Z)`. -/
def k6ptEqReg (X Y Z ι : Type) : (ι → X × Y × Z) ≃ (ι → X) × (ι → Y) × (ι → Z) where
  toFun p := (fun i => (p i).1, fun i => (p i).2.1, fun i => (p i).2.2)
  invFun q := fun i => (q.1 i, q.2.1 i, q.2.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `μ^{⊗ι}` as a distribution on `(ι → X) × (ι → Y) × (ι → Z)`: weight `∏ᵢ μ(xᵢ, yᵢ, zᵢ)`. -/
def k6ptReg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι] :
    FinProb ((ι → X) × (ι → Y) × (ι → Z)) :=
  k6ptPerm (k6ptEqReg X Y Z ι) (μ.pi ι)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem k6ptReg_prob (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (x : ι → X) (y : ι → Y) (z : ι → Z) :
    (k6ptReg μ ι).prob (x, y, z) = ∏ i, μ.prob (x i, y i, z i) := rfl

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem k6pt_cexpect_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (G : (ι → X) → (ι → Y) → (ι → Z) → ℂ) :
    (μ.pi ι).cexpect (fun p => G (fun i => (p i).1) (fun i => (p i).2.1) (fun i => (p i).2.2)) =
      (k6ptReg μ ι).cexpect (fun q => G q.1 q.2.1 q.2.2) :=
  (k6pt_cexpect_perm (k6ptEqReg X Y Z ι) (μ.pi ι) (fun q => G q.1 q.2.1 q.2.2)).symm

/-- `h̃(z) = 𝔼_{(x,y,z')∼μ^{⊗ι}}[conj(f(x) g(y)) | z' = z]` (K6 `#h-tilde-reduction`): the
conditional expectation under the product measure. -/
def k6ptHTilde (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) : (ι → Z) → ℂ :=
  k6ptCondC (k6ptReg μ ι) f g

/-- the left side of CSP_6 `eq:biginduct` for `n = |ι|` coordinates: the walk is run independently in
each coordinate; weight `∏ᵢ margY(yᵢ) · walkYY(labelsᵢ)(yᵢ, y'ᵢ)`, labels `(x₁, x₁', …)` collected
as the vectors `k ↦ (xₖ(i))ᵢ` (`N` even). -/
def k6ptWalkPi (μ : FinProb (X × Y × Z)) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) : ℂ :=
  ∑ p : ι → (Fin N → X) × Y × Y,
    ((∏ i, (margY μ (p i).2.1 * walkYY μ (List.ofFn (p i).1) (p i).2.1 (p i).2.2) : ℝ) : ℂ) *
      (k6ptAlt f (fun k i => (p i).1 k) *
        (g (fun i => (p i).2.1) * star (g (fun i => (p i).2.2))))

/-! Tensorization of the walk (the product measure's walk is the product of the walks). -/

private lemma k6pt_sum_pi_two {A B ι : Type} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
    (F : ι → A → B → ℝ) :
    ∑ a : ι → A, ∑ b : ι → B, ∏ i, F i (a i) (b i) = ∏ i, ∑ a, ∑ b, F i a b := by
  rw [Fintype.prod_sum (fun i a => ∑ b, F i a b)]
  exact Finset.sum_congr rfl fun a _ => (Fintype.prod_sum (fun i b => F i (a i) b)).symm

theorem k6pt_margY_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (y : ι → Y) : margY (k6ptReg μ ι) y = ∏ i, margY μ (y i) := by
  rw [margY_eq_sum]
  simp_rw [margY_eq_sum]
  exact k6pt_sum_pi_two (fun i x z => μ.prob (x, y i, z))

theorem k6pt_margZ_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (z : ι → Z) : margZ (k6ptReg μ ι) z = ∏ i, margZ μ (z i) := by
  rw [margZ_eq_sum]
  simp_rw [margZ_eq_sum]
  exact k6pt_sum_pi_two (fun i x y => μ.prob (x, y, z i))

private lemma k6pt_stepYZ_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (x : ι → X) (y : ι → Y) (z : ι → Z) :
    stepYZ (k6ptReg μ ι) x y z = ∏ i, stepYZ μ (x i) (y i) (z i) := by
  simp only [stepYZ, Matrix.of_apply]
  rw [k6pt_margY_reg, k6ptReg_prob]
  exact (Finset.prod_div_distrib _ _).symm

private lemma k6pt_stepZY_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (x : ι → X) (z : ι → Z) (y : ι → Y) :
    stepZY (k6ptReg μ ι) x z y = ∏ i, stepZY μ (x i) (z i) (y i) := by
  simp only [stepZY, Matrix.of_apply]
  rw [k6pt_margZ_reg, k6ptReg_prob]
  exact (Finset.prod_div_distrib _ _).symm

theorem k6pt_walkYZ_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (xs : List (ι → X)) (hxs : Odd xs.length) (y : ι → Y) (z : ι → Z) :
    walkYZ (k6ptReg μ ι) xs y z = ∏ i, walkYZ μ (xs.map fun x => x i) (y i) (z i) := by
  obtain ⟨m, hm⟩ := hxs
  have hm' : xs.length = 2 * m + 1 := by omega
  clear hm
  induction m generalizing xs y z with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨x₂, rest⟩⟩
    · simp at hm'
    · simp [walkYZ, k6pt_stepYZ_reg]
    · simp at hm'
  | succ m ih =>
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩
    · simp at hm'
    · simp only [List.length_singleton] at hm'
      omega
    · have hl : rest.length = 2 * m + 1 := by simp at hm'; omega
      have e : ∀ y' : ι → Y, walkYZ (k6ptReg μ ι) rest y' z =
          ∏ i, walkYZ μ (rest.map fun x => x i) (y' i) (z i) := fun y' => ih rest y' z hl
      rw [walkYZ, Matrix.mul_apply]
      simp only [List.map_cons, walkYZ, Matrix.mul_apply]
      calc ∑ y', (∑ z', stepYZ (k6ptReg μ ι) x₁ y z' * stepZY (k6ptReg μ ι) x₂ z' y') *
            walkYZ (k6ptReg μ ι) rest y' z
          = ∑ y' : ι → Y, ∑ z' : ι → Z, ∏ i, (stepYZ μ (x₁ i) (y i) (z' i) *
              stepZY μ (x₂ i) (z' i) (y' i) * walkYZ μ (rest.map fun x => x i) (y' i) (z i)) := by
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [e, Finset.sum_mul]
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [k6pt_stepYZ_reg, k6pt_stepZY_reg, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        _ = ∏ i, ∑ y', ∑ z', (stepYZ μ (x₁ i) (y i) z' * stepZY μ (x₂ i) z' y' *
              walkYZ μ (rest.map fun x => x i) y' (z i)) :=
            k6pt_sum_pi_two (fun i y' z' => stepYZ μ (x₁ i) (y i) z' * stepZY μ (x₂ i) z' y' *
              walkYZ μ (rest.map fun x => x i) y' (z i))
        _ = _ := by
            refine Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun y' _ => ?_
            rw [Finset.sum_mul]

theorem k6pt_walkYY_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι] [DecidableEq ι]
    (xs : List (ι → X)) (hxs : Even xs.length) (y y' : ι → Y) :
    walkYY (k6ptReg μ ι) xs y y' = ∏ i, walkYY μ (xs.map fun x => x i) (y i) (y' i) := by
  obtain ⟨m, hm⟩ := hxs
  have hm' : xs.length = 2 * m := by omega
  clear hm
  induction m generalizing xs y y' with
  | zero =>
    have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hm')
    subst this
    simp only [walkYY, List.map_nil]
    by_cases hy : y = y'
    · subst hy; simp
    · obtain ⟨i, hi⟩ : ∃ i, y i ≠ y' i := by
        by_contra hc
        exact hy (funext fun i => by by_contra hne; exact hc ⟨i, hne⟩)
      rw [Matrix.one_apply_ne hy]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Matrix.one_apply_ne hi])).symm
  | succ m ih =>
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩
    · simp at hm'
    · simp only [List.length_singleton] at hm'
      omega
    · have hl : rest.length = 2 * m := by simp at hm'; omega
      have e : ∀ y'' : ι → Y, walkYY (k6ptReg μ ι) rest y'' y' =
          ∏ i, walkYY μ (rest.map fun x => x i) (y'' i) (y' i) := fun y'' => ih rest y'' y' hl
      rw [walkYY, Matrix.mul_apply]
      simp only [List.map_cons, walkYY, Matrix.mul_apply]
      calc ∑ y'', (∑ z', stepYZ (k6ptReg μ ι) x₁ y z' * stepZY (k6ptReg μ ι) x₂ z' y'') *
            walkYY (k6ptReg μ ι) rest y'' y'
          = ∑ y'' : ι → Y, ∑ z' : ι → Z, ∏ i, (stepYZ μ (x₁ i) (y i) (z' i) *
              stepZY μ (x₂ i) (z' i) (y'' i) * walkYY μ (rest.map fun x => x i) (y'' i) (y' i)) := by
            refine Finset.sum_congr rfl fun y'' _ => ?_
            rw [e, Finset.sum_mul]
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [k6pt_stepYZ_reg, k6pt_stepZY_reg, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        _ = ∏ i, ∑ y'', ∑ z', (stepYZ μ (x₁ i) (y i) z' * stepZY μ (x₂ i) z' y'' *
              walkYY μ (rest.map fun x => x i) y'' (y' i)) :=
            k6pt_sum_pi_two (fun i y'' z' => stepYZ μ (x₁ i) (y i) z' * stepZY μ (x₂ i) z' y'' *
              walkYY μ (rest.map fun x => x i) y'' (y' i))
        _ = _ := by
            refine Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun y'' _ => ?_
            rw [Finset.sum_mul]

theorem k6pt_pathWeight_reg (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (w : Fin ℓ → ι → X) (y : ι → Y) (z : ι → Z) :
    pathWeight (k6ptReg μ ι) ℓ hℓ w y z =
      ∏ i, pathWeight μ ℓ hℓ (fun k => w k i) (y i) (z i) := by
  obtain ⟨m, hm⟩ := hℓ
  unfold pathWeight
  rw [k6pt_margY_reg, k6pt_walkYZ_reg μ ι _ (by simp [hm]), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [List.map_ofFn]
  rfl

omit [DecidableEq X] in
private lemma k6pt_sum_pathX (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (G : (Fin ℓ → X) → Y → Z → ℂ) :
    ∑ q : PathX μ ℓ hℓ × Y × Z,
        (pathWeight μ ℓ hℓ q.1.1 q.2.1 q.2.2 : ℂ) * G q.1.1 q.2.1 q.2.2 =
      ∑ r : (Fin ℓ → X) × Y × Z, (pathWeight μ ℓ hℓ r.1 r.2.1 r.2.2 : ℂ) * G r.1 r.2.1 r.2.2 := by
  refine Fintype.sum_of_injective (fun q : PathX μ ℓ hℓ × Y × Z => (q.1.1, q.2)) ?_ _ _ ?_ ?_
  rotate_left 2
  · intro q; rfl
  · rintro ⟨⟨w, hw⟩, y, z⟩ ⟨⟨w', hw'⟩, y', z'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · intro r hr
    have : pathWeight μ ℓ hℓ r.1 r.2.1 r.2.2 = 0 := by
      by_contra hne
      exact hr ⟨(⟨r.1, r.2.1, r.2.2, hne⟩, r.2.1, r.2.2), rfl⟩
    simp [this]

/-- `(μ^+)^{⊗ι}` (the product of the path-trick distributions) against the path trick of the
regrouped product measure. -/
theorem k6pt_cexpect_pathTrick_pi (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (G : (Fin ℓ → ι → X) → (ι → Y) → (ι → Z) → ℂ) :
    ((pathTrick μ ℓ hℓ).pi ι).cexpect (fun q =>
        G (fun k i => (q i).1.1 k) (fun i => (q i).2.1) (fun i => (q i).2.2)) =
      (pathTrick (k6ptReg μ ι) ℓ hℓ).cexpect (fun p => G p.1.1 p.2.1 p.2.2) := by
  unfold FinProb.cexpect
  refine Eq.trans ?_ (k6pt_sum_pathX (k6ptReg μ ι) hℓ (fun w y z => G w y z)).symm
  refine Fintype.sum_of_injective
    (fun q : ι → PathX μ ℓ hℓ × Y × Z =>
      ((fun k i => (q i).1.1 k, fun i => (q i).2.1, fun i => (q i).2.2) :
        (Fin ℓ → ι → X) × (ι → Y) × (ι → Z))) ?_ _ _ ?_ ?_
  rotate_left 2
  · intro q
    simp only
    rw [k6pt_pathWeight_reg]
    rfl
  · intro q q' hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    funext i
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (congrFun h2 i) (congrFun h3 i))
    funext k
    exact congrFun (congrFun h1 k) i
  · intro r hr
    have : pathWeight (k6ptReg μ ι) ℓ hℓ r.1 r.2.1 r.2.2 = 0 := by
      rw [k6pt_pathWeight_reg]
      by_contra hne
      have hne' : ∀ i, pathWeight μ ℓ hℓ (fun k => r.1 k i) (r.2.1 i) (r.2.2 i) ≠ 0 :=
        fun i => Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
      exact hr ⟨fun i => (⟨fun k => r.1 k i, r.2.1 i, r.2.2 i, hne' i⟩, r.2.1 i, r.2.2 i), rfl⟩
    simp [this]

theorem k6pt_walkPi_eq_evenExpect_reg (μ : FinProb (X × Y × Z)) {N : ℕ} (hN : Even N)
    (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) :
    k6ptWalkPi μ N ι f g = k6ptEvenExpect (k6ptReg μ ι) N f g := by
  unfold k6ptWalkPi k6ptEvenExpect
  let e : (ι → (Fin N → X) × Y × Y) ≃ (Fin N → ι → X) × (ι → Y) × (ι → Y) :=
    { toFun := fun p => (fun k i => (p i).1 k, fun i => (p i).2.1, fun i => (p i).2.2)
      invFun := fun q i => (fun k => q.1 k i, q.2.1 i, q.2.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc _ = ∑ q : (Fin N → ι → X) × (ι → Y) × (ι → Y),
        ((margY (k6ptReg μ ι) q.2.1 * walkYY (k6ptReg μ ι) (List.ofFn q.1) q.2.1 q.2.2 : ℝ) : ℂ) *
          (k6ptAlt f q.1 * (g q.2.1 * star (g q.2.2))) := by
        refine Fintype.sum_equiv e _ _ (fun p => ?_)
        show _ = ((margY (k6ptReg μ ι) (fun i => (p i).2.1) *
          walkYY (k6ptReg μ ι) (List.ofFn (fun k i => (p i).1 k)) (fun i => (p i).2.1)
            (fun i => (p i).2.2) : ℝ) : ℂ) * _
        rw [k6pt_margY_reg, k6pt_walkYY_reg μ ι _ (by simpa using hN), ← Finset.prod_mul_distrib]
        simp only [List.map_ofFn]
        rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

/-! ### n-fold statements -/

private lemma k6pt_hTilde_eq_condZPi (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (z : ι → Z) :
    k6ptHTilde μ ι f g z = condZPi μ ι f g z := by
  unfold k6ptHTilde k6ptCondC condZPi
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => X) (fun _ => Y)).symm _ _
    (fun p => ?_)
  rw [k6pt_margZ_reg, Finset.prod_div_distrib]
  rfl

private lemma k6pt_hTilde_core_reg (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    (∀ z, ‖k6ptHTilde μ ι f g z‖ ≤ 1) ∧
    ((μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        k6ptHTilde μ ι f g (fun i => (p i).2.2)) =
      ((∑ z : ι → Z, (∏ i, margZ μ (z i)) * ‖k6ptHTilde μ ι f g z‖ ^ 2 : ℝ) : ℂ)) ∧
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ 2 ≤
      ∑ z : ι → Z, (∏ i, margZ μ (z i)) * ‖k6ptHTilde μ ι f g z‖ ^ 2 := by
  have hc := k6pt_hTilde_core (k6ptReg μ ι) f g h hf hg hh
  have e1 := k6pt_cexpect_reg μ ι (fun x y z => f x * g y * k6ptHTilde μ ι f g z)
  have e2 := k6pt_cexpect_reg μ ι (fun x y z => f x * g y * h z)
  simp only [k6pt_margZ_reg] at hc
  refine ⟨hc.1, ?_, ?_⟩
  · rw [e1]
    exact hc.2.1
  · rw [e2]
    exact hc.2.2

/-- CSP_6 `lemma:pathtrick#h-tilde-reduction`. -/
theorem k6pt_hTilde_reduction (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    (∀ z, ‖k6ptHTilde μ ι f g z‖ ≤ 1) ∧
    ((μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        k6ptHTilde μ ι f g (fun i => (p i).2.2)) =
      ((∑ z : ι → Z, (∏ i, margZ μ (z i)) * ‖k6ptHTilde μ ι f g z‖ ^ 2 : ℝ) : ℂ)) ∧
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ 2 ≤
      ∑ z : ι → Z, (∏ i, margZ μ (z i)) * ‖k6ptHTilde μ ι f g z‖ ^ 2 := by
  exact k6pt_hTilde_core_reg μ ι f g h hf hg hh

/-- the source's conclusion `|𝔼 f g h̃| ≥ ε²` from `|𝔼 f g h| ≥ ε` (`ε ≥ 0`, TYPING). -/
theorem k6pt_hTilde_reduction_eps (μ : FinProb (X × Y × Z)) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ε ≤ ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖) :
    ε ^ 2 ≤ ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        k6ptHTilde μ ι f g (fun i => (p i).2.2))‖ := by
  have h2 := (k6pt_hTilde_core_reg μ ι f g h hf hg hh).2
  have h0 : 0 ≤ ∑ z : ι → Z, (∏ i, margZ μ (z i)) * ‖k6ptHTilde μ ι f g z‖ ^ 2 :=
    Finset.sum_nonneg fun z _ => mul_nonneg
      (Finset.prod_nonneg fun i _ => margZ_nonneg μ (z i)) (sq_nonneg _)
  rw [h2.1, Complex.norm_real, Real.norm_of_nonneg h0]
  exact le_trans (pow_le_pow_left₀ hε hE 2) h2.2

/-- CSP_6 `eq:biginduct` (the printed bound is true, the Markov gluing is
`k6pt_evenExpect_double`). -/
theorem k6pt_biginduct (μ : FinProb (X × Y × Z)) {r : ℕ} (hr : 1 ≤ r) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ (2 ^ r) ≤ ‖k6ptWalkPi μ (2 ^ r) ι f g‖ := by
  have hc := k6pt_biginduct_core (k6ptReg μ ι) hr f g h hf hg hh
  have hev : Even (2 ^ r) := (Nat.even_pow' (by omega)).2 even_two
  have e : (μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
      h (fun i => (p i).2.2)) =
      ∑ p : (ι → X) × (ι → Y) × (ι → Z), ((k6ptReg μ ι).prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2) :=
    k6pt_cexpect_reg μ ι (fun x y z => f x * g y * h z)
  rw [e, k6pt_walkPi_eq_evenExpect_reg μ hev ι f g]
  exact hc

theorem k6pt_biginduct_eps (μ : FinProb (X × Y × Z)) {r : ℕ} (hr : 1 ≤ r) (ι : Type)
    [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ε ≤ ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖) :
    ε ^ (2 ^ r) ≤ ‖k6ptWalkPi μ (2 ^ r) ι f g‖ := by
  exact le_trans (pow_le_pow_left₀ hε hE _) (k6pt_biginduct μ hr ι f g h hf hg hh)

/-- CSP_6 `lemma:pathtrick`, `x` path trick, `ℓ = 2^r - 1`: `|𝔼_{μ^{⊗ι}} f g h|^{2^r} ≤
|𝔼_{(μ⁺)^{⊗ι}} f⁺ g h̃|`. -/
theorem k6pt_pathtrick (μ : FinProb (X × Y × Z)) {r ℓ : ℕ} (hℓ : Odd ℓ) (hℓt : ℓ = 2 ^ r - 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ (2 ^ r) ≤
      ‖((pathTrick μ ℓ hℓ).pi ι).cexpect (fun q =>
        k6ptAlt f (fun k i => (q i).1.1 k) * g (fun i => (q i).2.1) *
          k6ptHTilde μ ι f g (fun i => (q i).2.2))‖ := by
  have := from_mu_to_path_tensor μ hℓ hℓt ι f g h hf hg hh
  simp only [← k6pt_hTilde_eq_condZPi] at this
  exact this

/-- CSP_6 `lemma:pathtrick` in the source's `∃` form. -/
theorem k6pt_pathtrick_exists (μ : FinProb (X × Y × Z)) {r ℓ : ℕ} (hℓ : Odd ℓ)
    (hℓt : ℓ = 2 ^ r - 1) (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ)
    (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hh : ∀ z, ‖h z‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ε ≤ ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖) :
    ∃ (fp : (ι → PathX μ ℓ hℓ) → ℂ) (ht : (ι → Z) → ℂ),
      (∀ q, ‖fp q‖ ≤ 1) ∧ (∀ z, ‖ht z‖ ≤ 1) ∧
      (∀ q, fp q = k6ptAlt f (fun k i => (q i).1 k)) ∧
      ε ^ (2 ^ r) ≤ ‖((pathTrick μ ℓ hℓ).pi ι).cexpect (fun q =>
        fp (fun i => (q i).1) * g (fun i => (q i).2.1) * ht (fun i => (q i).2.2))‖ := by
  refine ⟨fun q => k6ptAlt f (fun k i => (q i).1 k), k6ptHTilde μ ι f g,
    fun q => norm_k6ptAlt_le_one f (fun x => hf (x)) _,
    (k6pt_hTilde_core_reg μ ι f g h hf hg hh).1, fun q => rfl, ?_⟩
  exact le_trans (pow_le_pow_left₀ hε hE _) (k6pt_pathtrick μ hℓ hℓt ι f g h hf hg hh)

/-- CSP_6 `lemma:pathtrick`, `y` path trick: `f` (the start function) is kept, `g` (the label
function) becomes `g⁺`, `h` becomes `h̃`. -/
theorem k6pt_pathtrickY (μ : FinProb (X × Y × Z)) {r : ℕ} (hr : 1 ≤ r) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ (2 ^ r) ≤
      ‖((k6ptTrickY μ r hr).pi ι).cexpect (fun q =>
        f (fun i => (q i).1) * k6ptAlt g (fun k i => (q i).2.1.1 k) *
          k6ptHTilde (k6ptViewY μ) ι g f (fun i => (q i).2.2))‖ := by
  have key := k6pt_pathtrick (k6ptViewY μ) (r := r) (k6pt_odd hr) rfl ι g f h hg hf hh
  have hL : ((k6ptViewY μ).pi ι).cexpect (fun p => g (fun i => (p i).1) *
      f (fun i => (p i).2.1) * h (fun i => (p i).2.2)) =
      (μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2)) := by
    rw [k6ptViewY, k6pt_cexpect_pi_perm]
    congr 1
    funext p
    simp only [k6ptEqY, Equiv.coe_fn_mk]
    ring
  have hR : ((pathTrick (k6ptViewY μ) (2 ^ r - 1) (k6pt_odd hr)).pi ι).cexpect (fun q =>
        k6ptAlt g (fun k i => (q i).1.1 k) * f (fun i => (q i).2.1) *
          k6ptHTilde (k6ptViewY μ) ι g f (fun i => (q i).2.2)) =
      ((k6ptTrickY μ r hr).pi ι).cexpect (fun q =>
        f (fun i => (q i).1) * k6ptAlt g (fun k i => (q i).2.1.1 k) *
          k6ptHTilde (k6ptViewY μ) ι g f (fun i => (q i).2.2)) := by
    rw [k6ptTrickY, k6pt_cexpect_pi_perm]
    congr 1
    funext q
    simp only [k6ptEqY, Equiv.coe_fn_mk]
    ring
  rw [hL, hR] at key
  exact key

/-- CSP_6 `lemma:pathtrick`, `z` path trick: `f` kept, `h` (the label function) becomes `h⁺`,
`g` becomes `g̃`. -/
theorem k6pt_pathtrickZ (μ : FinProb (X × Y × Z)) {r : ℕ} (hr : 1 ≤ r) (ι : Type) [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖ ^ (2 ^ r) ≤
      ‖((k6ptTrickZ μ r hr).pi ι).cexpect (fun q =>
        f (fun i => (q i).1) * k6ptHTilde (k6ptViewZ μ) ι h f (fun i => (q i).2.1) *
          k6ptAlt h (fun k i => (q i).2.2.1 k))‖ := by
  have key := k6pt_pathtrick (k6ptViewZ μ) (r := r) (k6pt_odd hr) rfl ι h f g hh hf hg
  have hL : ((k6ptViewZ μ).pi ι).cexpect (fun p => h (fun i => (p i).1) *
      f (fun i => (p i).2.1) * g (fun i => (p i).2.2)) =
      (μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2)) := by
    rw [k6ptViewZ, k6pt_cexpect_pi_perm]
    congr 1
    funext p
    simp only [k6ptEqZ, Equiv.coe_fn_mk]
    ring
  have hR : ((pathTrick (k6ptViewZ μ) (2 ^ r - 1) (k6pt_odd hr)).pi ι).cexpect (fun q =>
        k6ptAlt h (fun k i => (q i).1.1 k) * f (fun i => (q i).2.1) *
          k6ptHTilde (k6ptViewZ μ) ι h f (fun i => (q i).2.2)) =
      ((k6ptTrickZ μ r hr).pi ι).cexpect (fun q =>
        f (fun i => (q i).1) * k6ptHTilde (k6ptViewZ μ) ι h f (fun i => (q i).2.1) *
          k6ptAlt h (fun k i => (q i).2.2.1 k)) := by
    rw [k6ptTrickZ, k6pt_cexpect_pi_perm]
    congr 1
    funext q
    simp only [k6ptEqZ, Equiv.symm_mk, Equiv.coe_fn_mk]
    ring
  rw [hL, hR] at key
  exact key

/-- CSP_6 `eq:3path`: after the `y` path trick (`r₁`), the `z` path trick (`r₂`) and the `x` path trick
with `r = 2`, there are `1`-bounded `g'`, `h'` with correlation at least `ε^{2^{r₁+r₂+2}}` for
`f(x₁) conj f(x₂) f(x₃) g'(y) h'(z)` under `(μ⁺)^{⊗ι}`; the correlation bound holds for all
`r₁, r₂ ≥ 1` (no connectivity hypothesis is needed for it). -/
theorem k6pt_eq3path (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ∃ (g' : (ι → K6ptGam μ r₁ hr₁) → ℂ) (h' : (ι → K6ptPhi μ r₁ hr₁ r₂ hr₂) → ℂ),
      (∀ y, ‖g' y‖ ≤ 1) ∧ (∀ z, ‖h' z‖ ≤ 1) ∧
      ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
          h (fun i => (p i).2.2))‖ ^ (2 ^ (r₁ + r₂ + 2)) ≤
        ‖((k6ptMuPlus μ r₁ hr₁ r₂ hr₂).pi ι).cexpect (fun q =>
          f (fun i => (q i).1.1 0) * star (f (fun i => (q i).1.1 1)) *
            f (fun i => (q i).1.1 2) * g' (fun i => (q i).2.1) *
              h' (fun i => (q i).2.2))‖ := by
  have h1 := k6pt_pathtrickY μ hr₁ ι f g h hf hg hh
  have hg1 : ∀ y : ι → K6ptGam μ r₁ hr₁, ‖k6ptAlt g (fun k i => (y i).1 k)‖ ≤ 1 :=
    fun y => norm_k6ptAlt_le_one g hg _
  have hh1 : ∀ z, ‖k6ptHTilde (k6ptViewY μ) ι g f z‖ ≤ 1 :=
    (k6pt_hTilde_reduction (k6ptViewY μ) ι g f (fun _ => 0) hg hf (fun _ => by simp)).1
  have h2 := k6pt_pathtrickZ (k6ptMu1 μ r₁ hr₁) hr₂ ι f
    (fun y => k6ptAlt g (fun k i => (y i).1 k)) (k6ptHTilde (k6ptViewY μ) ι g f) hf hg1 hh1
  have hg2 : ∀ y, ‖k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f)
      f y‖ ≤ 1 :=
    (k6pt_hTilde_reduction (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f
      (fun _ => 0) hh1 hf (fun _ => by simp)).1
  have hh2 : ∀ z : ι → K6ptPhi μ r₁ hr₁ r₂ hr₂,
      ‖k6ptAlt (k6ptHTilde (k6ptViewY μ) ι g f) (fun k i => (z i).1 k)‖ ≤ 1 :=
    fun z => norm_k6ptAlt_le_one _ hh1 _
  have h3 := k6pt_pathtrick (k6ptMu2 μ r₁ hr₁ r₂ hr₂) (r := 2) (ℓ := 3) k6pt_odd_three
    (by norm_num) ι f
    (k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f)
    (fun z => k6ptAlt (k6ptHTilde (k6ptViewY μ) ι g f) (fun k i => (z i).1 k)) hf hg2 hh2
  refine ⟨k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f,
    k6ptHTilde (k6ptMu2 μ r₁ hr₁ r₂ hr₂) ι f
      (k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f),
    hg2, (k6pt_hTilde_reduction (k6ptMu2 μ r₁ hr₁ r₂ hr₂) ι f _ (fun _ => 0) hf hg2
      (fun _ => by simp)).1, ?_⟩
  have e3 : ((k6ptMuPlus μ r₁ hr₁ r₂ hr₂).pi ι).cexpect (fun q =>
      f (fun i => (q i).1.1 0) * star (f (fun i => (q i).1.1 1)) *
        f (fun i => (q i).1.1 2) *
          k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f
            (fun i => (q i).2.1) *
          k6ptHTilde (k6ptMu2 μ r₁ hr₁ r₂ hr₂) ι f
            (k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f)
            (fun i => (q i).2.2)) =
      ((k6ptMuPlus μ r₁ hr₁ r₂ hr₂).pi ι).cexpect (fun q =>
        k6ptAlt f (fun k i => (q i).1.1 k) *
          k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f
            (fun i => (q i).2.1) *
          k6ptHTilde (k6ptMu2 μ r₁ hr₁ r₂ hr₂) ι f
            (k6ptHTilde (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) ι (k6ptHTilde (k6ptViewY μ) ι g f) f)
            (fun i => (q i).2.2)) := by
    unfold FinProb.cexpect
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [k6ptAlt, Fin.prod_univ_three]
    simp
  rw [e3]
  have hA := pow_le_pow_left₀ (by positivity) h1 (2 ^ r₂)
  have hB := pow_le_pow_left₀ (by positivity) (hA.trans h2) (2 ^ 2)
  have hC := hB.trans h3
  rw [← pow_mul, ← pow_mul] at hC
  have e : 2 ^ r₁ * (2 ^ r₂ * 2 ^ 2) = 2 ^ (r₁ + r₂ + 2) := by
    rw [← pow_add, ← pow_add]; ring_nf
  rw [e] at hC
  exact hC

theorem k6pt_eq3path_eps (μ : FinProb (X × Y × Z)) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ)
    (h : (ι → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ε ≤ ‖(μ.pi ι).cexpect (fun p => f (fun i => (p i).1) * g (fun i => (p i).2.1) *
        h (fun i => (p i).2.2))‖) :
    ∃ (g' : (ι → K6ptGam μ r₁ hr₁) → ℂ) (h' : (ι → K6ptPhi μ r₁ hr₁ r₂ hr₂) → ℂ),
      (∀ y, ‖g' y‖ ≤ 1) ∧ (∀ z, ‖h' z‖ ≤ 1) ∧
      ε ^ (2 ^ (r₁ + r₂ + 2)) ≤
        ‖((k6ptMuPlus μ r₁ hr₁ r₂ hr₂).pi ι).cexpect (fun q =>
          f (fun i => (q i).1.1 0) * star (f (fun i => (q i).1.1 1)) *
            f (fun i => (q i).1.1 2) * g' (fun i => (q i).2.1) *
              h' (fun i => (q i).2.2))‖ := by
  obtain ⟨g', h', hg', hh', hb⟩ := k6pt_eq3path μ hr₁ hr₂ ι f g h hf hg hh
  exact ⟨g', h', hg', hh', le_trans (pow_le_pow_left₀ hε hE _) hb⟩

end K6ptTensor
end TrackB
end RestrictedPolynomials
end
