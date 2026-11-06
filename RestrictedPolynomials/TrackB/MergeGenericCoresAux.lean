module

public import RestrictedPolynomials.TrackB.MergeGeneric

/-!
# Track B, support layer of the cores: tensor kernels and the basis-free
non-merged degree decomposition

Support for `MergeGenericCores` (paper IV `writeup_stability.tex` l. 8554-8900, the proofs of
`lem:merge` and `lem:merge2`; paper IV `lem:merge`, step `coordinate-merge-chain-eigenbasis`).

* `mgenCOp K`: the tensor operator with coordinate kernels `K i`;
* `mgenCP E B`: the block projection `∏_{k∈B} (I - E_k) ∏_{k∉B} E_k` of an idempotent kernel `E`
  (the component average), so that `f = Σ_B mgenCP E B f` is the source's split of `f` by
  non-merged degree `|B|`, with orthogonal blocks;
* the restriction identity: after a random restriction with live density `s`, the expected mass
  of `f` off non-merged degree `0` is `Σ_B (1 - (1-s)^{|B|}) ‖f^{(B)}‖²`.

Public helpers carry the prefix `mgenC` (shared with `MergeGenericCores`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

section TensorKernel
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the tensor operator with coordinate kernels `K i`: `(⊗ᵢ Kᵢ) f`. -/
def mgenCOp (K : ι → α → α → ℝ) (f : (ι → α) → ℂ) (x : ι → α) : ℂ :=
  ∑ x', ((∏ i, K i (x i) (x' i) : ℝ) : ℂ) * f x'

/-- the identity kernel. -/
def mgenCId (a b : α) : ℝ := if a = b then 1 else 0

theorem mgenCOp_comp (K L : ι → α → α → ℝ) (f : (ι → α) → ℂ) :
    mgenCOp K (mgenCOp L f) = mgenCOp (fun i a c => ∑ b, K i a b * L i b c) f := by
  funext x
  have h : ∀ x'' : ι → α, (∏ i, ∑ b, K i (x i) b * L i b (x'' i)) =
      ∑ x' : ι → α, (∏ i, K i (x i) (x' i)) * ∏ i, L i (x' i) (x'' i) := by
    intro x''
    rw [Fintype.prod_sum (fun i b => K i (x i) b * L i b (x'' i))]
    exact Finset.sum_congr rfl fun x' _ => Finset.prod_mul_distrib
  simp only [mgenCOp, h, Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mgenCOp_congr {K L : ι → α → α → ℝ} (h : ∀ i a b, K i a b = L i a b)
    (f : (ι → α) → ℂ) : mgenCOp K f = mgenCOp L f := by
  funext x
  simp only [mgenCOp, h]

theorem mgenCOp_eq_zero {K : ι → α → α → ℝ} {i₀ : ι} (h : ∀ a b, K i₀ a b = 0)
    (f : (ι → α) → ℂ) : mgenCOp K f = 0 := by
  funext x
  simp only [mgenCOp, Pi.zero_apply]
  refine Finset.sum_eq_zero fun x' _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (h _ _)]
  simp

theorem mgenCOp_id (f : (ι → α) → ℂ) : mgenCOp (fun _ => (mgenCId : α → α → ℝ)) f = f := by
  funext x
  unfold mgenCOp mgenCId
  rw [Finset.sum_eq_single x]
  · simp
  · intro x' _ hx'
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra h
      push Not at h
      exact hx' (funext h).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp
  · simp

theorem mgenCOp_add (K : ι → α → α → ℝ) (f g : (ι → α) → ℂ) :
    mgenCOp K (f + g) = mgenCOp K f + mgenCOp K g := by
  funext x
  simp only [mgenCOp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem mgenCOp_sub (K : ι → α → α → ℝ) (f g : (ι → α) → ℂ) :
    mgenCOp K (f - g) = mgenCOp K f - mgenCOp K g := by
  funext x
  simp only [mgenCOp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem mgenCOp_smul (K : ι → α → α → ℝ) (c : ℂ) (f : (ι → α) → ℂ) :
    mgenCOp K (c • f) = c • mgenCOp K f := by
  funext x
  simp only [mgenCOp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem mgenCOp_zero (K : ι → α → α → ℝ) : mgenCOp K (0 : (ι → α) → ℂ) = 0 := by
  funext x
  simp [mgenCOp]

theorem mgenCOp_sum {β : Type} (s : Finset β) (K : ι → α → α → ℝ) (F : β → (ι → α) → ℂ) :
    mgenCOp K (∑ b ∈ s, F b) = ∑ b ∈ s, mgenCOp K (F b) := by
  funext x
  simp only [mgenCOp, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

private theorem prod_add_eq_sum (u v : ι → ℝ) :
    ∏ i, (u i + v i) = ∑ B : Finset ι, ∏ i, (if i ∈ B then u i else v i) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext i
  simp

/-- `⊗ (Kᵢ + Lᵢ) = Σ_B (⊗_{B} K ⊗_{Bᶜ} L)`. -/
theorem mgenCOp_add_kernel (K L : ι → α → α → ℝ) (f : (ι → α) → ℂ) :
    mgenCOp (fun i a b => K i a b + L i a b) f =
      ∑ B : Finset ι, mgenCOp (fun i a b => if i ∈ B then K i a b else L i a b) f := by
  funext x
  simp only [mgenCOp, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [prod_add_eq_sum, Complex.ofReal_sum, Finset.sum_mul]

private theorem prod_ite_smul (B : Finset ι) (t : ℝ) (u v : ι → ℝ) :
    ∏ i, (if i ∈ B then t * u i else v i) = t ^ B.card * ∏ i, (if i ∈ B then u i else v i) := by
  have h : ∀ i, (if i ∈ B then t * u i else v i) =
      (if i ∈ B then t else 1) * (if i ∈ B then u i else v i) := by
    intro i; split_ifs <;> ring
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- self-adjointness of a tensor operator with reversible coordinate kernels. -/
theorem mgenCOp_cinner (D : FinProb α) (K : ι → α → α → ℝ)
    (hK : ∀ i a b, D.prob a * K i a b = D.prob b * K i b a) (f g : (ι → α) → ℂ) :
    (D.pi ι).cinner (mgenCOp K f) g = (D.pi ι).cinner f (mgenCOp K g) := by
  have hw : ∀ x x' : ι → α, (((D.pi ι).prob x * ∏ i, K i (x i) (x' i) : ℝ) : ℂ) =
      (((D.pi ι).prob x' * ∏ i, K i (x' i) (x i) : ℝ) : ℂ) := by
    intro x x'
    congr 1
    simp only [FinProb.pi_prob, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hK i _ _
  simp only [cinner_def, mgenCOp, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  have := hw x x'
  rw [Complex.ofReal_mul, Complex.ofReal_mul] at this
  linear_combination (f x * (starRingEnd ℂ) (g x')) * this.symm

end TensorKernel

section Blocks
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]
  (E : α → α → ℝ)

/-- `Q = I - E`. -/
def mgenCQ (a b : α) : ℝ := mgenCId a b - E a b

/-- the coordinate kernels of the block `B`: `Q` on `B`, `E` off `B`. -/
def mgenCPk (B : Finset ι) (i : ι) (a b : α) : ℝ := if i ∈ B then mgenCQ E a b else E a b

/-- the block projection `∏_{k∈B} (I - E_k) ∏_{k∉B} E_k`. -/
def mgenCP (B : Finset ι) (f : (ι → α) → ℂ) : (ι → α) → ℂ := mgenCOp (mgenCPk E B) f

variable {E}

private theorem id_comp (K : α → α → ℝ) (a c : α) : ∑ b, mgenCId a b * K b c = K a c := by
  simp [mgenCId]

private theorem comp_id (K : α → α → ℝ) (a c : α) : ∑ b, K a b * mgenCId b c = K a c := by
  simp [mgenCId]

section Idem
variable (hEE : ∀ a c, ∑ b, E a b * E b c = E a c)
include hEE

private theorem QQ (a c : α) : ∑ b, mgenCQ E a b * mgenCQ E b c = mgenCQ E a c := by
  have e : ∀ b, mgenCQ E a b * mgenCQ E b c = mgenCId a b * mgenCId b c -
      mgenCId a b * E b c - E a b * mgenCId b c + E a b * E b c := by
    intro b; unfold mgenCQ; ring
  rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, id_comp mgenCId a c, id_comp E a c, comp_id E a c, hEE a c]
  unfold mgenCQ; ring

private theorem QE (a c : α) : ∑ b, mgenCQ E a b * E b c = 0 := by
  simp only [mgenCQ, sub_mul, Finset.sum_sub_distrib, id_comp E a c, hEE a c, sub_self]

private theorem EQ (a c : α) : ∑ b, E a b * mgenCQ E b c = 0 := by
  simp only [mgenCQ, mul_sub, Finset.sum_sub_distrib, comp_id E a c, hEE a c, sub_self]

/-- `P_B P_C = [B = C] P_B`. -/
theorem mgenCP_mgenCP (B C : Finset ι) (f : (ι → α) → ℂ) :
    mgenCP E B (mgenCP E C f) = if B = C then mgenCP E B f else 0 := by
  unfold mgenCP
  rw [mgenCOp_comp]
  split_ifs with hBC
  · subst hBC
    refine mgenCOp_congr (fun i a c => ?_) f
    unfold mgenCPk
    split_ifs
    · exact QQ hEE a c
    · exact hEE a c
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ B ↔ i ∈ C) := by
      by_contra h
      push Not at h
      exact hBC (Finset.ext h)
    refine mgenCOp_eq_zero (i₀ := i) (fun a c => ?_) f
    unfold mgenCPk
    by_cases h1 : i ∈ B <;> by_cases h2 : i ∈ C
    · exact absurd (iff_of_true h1 h2) hi
    · simp only [h1, h2, ite_true, ite_false]; exact QE hEE a c
    · simp only [h1, h2, ite_true, ite_false]; exact EQ hEE a c
    · exact absurd (iff_of_false h1 h2) hi

/-- `E` on the coordinates of `J` kills the blocks meeting `J`. -/
theorem mgenCOp_E_mgenCP (J B : Finset ι) (f : (ι → α) → ℂ) :
    mgenCOp (fun i a b => if i ∈ J then E a b else mgenCId a b) (mgenCP E B f) =
      if Disjoint B J then mgenCP E B f else 0 := by
  unfold mgenCP
  rw [mgenCOp_comp]
  split_ifs with hBJ
  · refine mgenCOp_congr (fun i a c => ?_) f
    unfold mgenCPk
    by_cases h1 : i ∈ J
    · have h2 : i ∉ B := Finset.disjoint_right.1 hBJ h1
      simp only [h1, h2, ite_true, ite_false]
      exact hEE a c
    · simp only [h1, ite_false]
      exact id_comp (fun b c => if i ∈ B then mgenCQ E b c else E b c) a c
  · obtain ⟨i, hiB, hiJ⟩ := Finset.not_disjoint_iff.1 hBJ
    refine mgenCOp_eq_zero (i₀ := i) (fun a c => ?_) f
    unfold mgenCPk
    simp only [hiB, hiJ, ite_true]
    exact EQ hEE a c

/-- `Q` on the coordinates of `A` kills the blocks not containing `A`. -/
theorem mgenCOp_Q_mgenCP (A B : Finset ι) (f : (ι → α) → ℂ) :
    mgenCOp (fun i a b => if i ∈ A then mgenCQ E a b else mgenCId a b) (mgenCP E B f) =
      if A ⊆ B then mgenCP E B f else 0 := by
  unfold mgenCP
  rw [mgenCOp_comp]
  split_ifs with hAB
  · refine mgenCOp_congr (fun i a c => ?_) f
    unfold mgenCPk
    by_cases h1 : i ∈ A
    · have h2 : i ∈ B := hAB h1
      simp only [h1, h2, ite_true]
      exact QQ hEE a c
    · simp only [h1, ite_false]
      exact id_comp (fun b c => if i ∈ B then mgenCQ E b c else E b c) a c
  · obtain ⟨i, hiA, hiB⟩ := Finset.not_subset.1 hAB
    refine mgenCOp_eq_zero (i₀ := i) (fun a c => ?_) f
    unfold mgenCPk
    simp only [hiA, hiB, ite_true, ite_false]
    exact QE hEE a c

end Idem

/-- `Σ_B P_B f = f`. -/
theorem mgenCP_sum (f : (ι → α) → ℂ) : ∑ B : Finset ι, mgenCP E B f = f := by
  unfold mgenCP mgenCPk
  rw [← mgenCOp_add_kernel (fun _ => mgenCQ E) (fun _ => E)]
  conv_rhs => rw [← mgenCOp_id f]
  refine mgenCOp_congr (fun i a b => ?_) f
  simp [mgenCQ]

/-- `P_B = (E off B) ∘ (Q on B)`. -/
theorem mgenCP_eq_comp (B : Finset ι) (f : (ι → α) → ℂ) :
    mgenCP E B f = mgenCOp (fun i a b => if i ∈ B then mgenCId a b else E a b)
      (mgenCOp (fun i a b => if i ∈ B then mgenCQ E a b else mgenCId a b) f) := by
  unfold mgenCP
  rw [mgenCOp_comp]
  refine mgenCOp_congr (fun i a c => ?_) f
  unfold mgenCPk
  by_cases h : i ∈ B
  · simp only [h, ite_true]
    exact (id_comp _ a c).symm
  · simp only [h, ite_false]
    exact (comp_id E a c).symm

/-- the soft average `E + t Q` acts by `t^{|B|}` on the block `B`. -/
theorem mgenCOp_soft (t : ℝ) (f : (ι → α) → ℂ) :
    mgenCOp (fun _ a b => E a b + t * mgenCQ E a b) f =
      ∑ B : Finset ι, ((t ^ B.card : ℝ) : ℂ) • mgenCP E B f := by
  rw [show (fun (_ : ι) (a b : α) => E a b + t * mgenCQ E a b) =
      fun _ a b => t * mgenCQ E a b + E a b from by funext _ a b; ring, mgenCOp_add_kernel]
  refine Finset.sum_congr rfl fun B _ => ?_
  funext x
  simp only [mgenCOp, mgenCP, mgenCPk, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [prod_ite_smul B t (fun i => mgenCQ E (x i) (x' i)) (fun i => E (x i) (x' i))]
  push_cast
  ring

/-- reversibility of the block kernels. -/
theorem mgenCPk_rev (D : FinProb α) (hErev : ∀ a b, D.prob a * E a b = D.prob b * E b a)
    (B : Finset ι) (i : ι) (a b : α) :
    D.prob a * mgenCPk E B i a b = D.prob b * mgenCPk E B i b a := by
  unfold mgenCPk
  split_ifs
  · unfold mgenCQ mgenCId
    rw [mul_sub, mul_sub, hErev a b]
    by_cases h : a = b
    · subst h; rfl
    · simp [h, Ne.symm h]
  · exact hErev a b

/-- the blocks are orthogonal in `L²(D^{⊗ι})`. -/
theorem mgenCP_orth (D : FinProb α) (hEE : ∀ a c, ∑ b, E a b * E b c = E a c)
    (hErev : ∀ a b, D.prob a * E a b = D.prob b * E b a) {B C : Finset ι} (hBC : B ≠ C)
    (f g : (ι → α) → ℂ) : (D.pi ι).cinner (mgenCP E B f) (mgenCP E C g) = 0 := by
  unfold mgenCP
  rw [mgenCOp_cinner D _ (mgenCPk_rev D hErev B) f]
  have := mgenCP_mgenCP hEE B C g
  unfold mgenCP at this
  rw [this, if_neg hBC, cinner_zero_right]

/-- Pythagoras for a weighted sum of blocks. -/
theorem mgenCP_cl2sq_sum (D : FinProb α) (hEE : ∀ a c, ∑ b, E a b * E b c = E a c)
    (hErev : ∀ a b, D.prob a * E a b = D.prob b * E b a) (c : Finset ι → ℂ)
    (f : (ι → α) → ℂ) :
    cl2sq D (∑ B : Finset ι, c B • mgenCP E B f) =
      ∑ B : Finset ι, ‖c B‖ ^ 2 * cl2sq D (mgenCP E B f) := by
  rw [cl2sq_sum_of_orth D _ (fun B => c B • mgenCP E B f) (fun B C hBC => by
    rw [cinner_smul_left, cinner_smul_right, mgenCP_orth D hEE hErev hBC, mul_zero, mul_zero])
    rfl]
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold cl2sq FinProb.expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

theorem mgenCP_cl2sq (D : FinProb α) (hEE : ∀ a c, ∑ b, E a b * E b c = E a c)
    (hErev : ∀ a b, D.prob a * E a b = D.prob b * E b a) (f : (ι → α) → ℂ) :
    cl2sq D f = ∑ B : Finset ι, cl2sq D (mgenCP E B f) := by
  have h := mgenCP_cl2sq_sum (ι := ι) D hEE hErev (fun _ => 1) f
  simp only [one_smul, norm_one, one_pow, one_mul, mgenCP_sum] at h
  exact h

end Blocks

section GN
variable {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (G : α → α → Prop)
  [DecidableRel G]

theorem mgenC_gnE_eq (a b : α) :
    graphNoiseKernel D G 1 a b =
      (if G a b then D.prob b else 0) / ∑ c ∈ univ.filter (G a), D.prob c := by
  unfold graphNoiseKernel; ring

/-- `T_{1-ξ} = E + (1-ξ) Q`. -/
theorem mgenC_gn_soft (ξ : ℝ) (a b : α) :
    graphNoiseKernel D G ξ a b =
      graphNoiseKernel D G 1 a b + (1 - ξ) * mgenCQ (graphNoiseKernel D G 1) a b := by
  unfold mgenCQ mgenCId graphNoiseKernel; ring

variable {D G}

private theorem filter_eq_of_rel (hG : Equivalence G) {a a' : α} (h : G a a') :
    univ.filter (G a) = univ.filter (G a') := by
  ext c
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h1 => hG.trans (hG.symm h) h1, fun h1 => hG.trans h h1⟩

theorem mgenC_gnE_row (hG : Equivalence G) {a a' : α} (h : G a a') (b : α) :
    graphNoiseKernel D G 1 a b = graphNoiseKernel D G 1 a' b := by
  rw [mgenC_gnE_eq, mgenC_gnE_eq, filter_eq_of_rel hG h]
  by_cases h1 : G a b
  · have h2 : G a' b := hG.trans (hG.symm h) h1
    simp only [h1, h2, ite_true]
  · have h2 : ¬ G a' b := fun h2 => h1 (hG.trans h h2)
    simp only [h1, h2, ite_false]

theorem mgenC_gnE_idem (hG : Equivalence G) (a c : α) :
    ∑ b, graphNoiseKernel D G 1 a b * graphNoiseKernel D G 1 b c =
      graphNoiseKernel D G 1 a c := by
  have h1 : ∀ b, graphNoiseKernel D G 1 a b * graphNoiseKernel D G 1 b c =
      graphNoiseKernel D G 1 a b * graphNoiseKernel D G 1 a c := by
    intro b
    by_cases hab : G a b
    · rw [← mgenC_gnE_row hG hab c]
    · rw [mgenC_gnE_eq D G a b]
      simp [hab]
  rw [Finset.sum_congr rfl fun b _ => h1 b, ← Finset.sum_mul]
  have hs : ∑ b, graphNoiseKernel D G 1 a b =
      (∑ c ∈ univ.filter (G a), D.prob c) / ∑ c ∈ univ.filter (G a), D.prob c := by
    simp only [mgenC_gnE_eq]
    rw [← Finset.sum_div, Finset.sum_filter]
  rw [hs]
  by_cases hN : ∑ c ∈ univ.filter (G a), D.prob c = 0
  · rw [mgenC_gnE_eq D G a c, hN]
    simp
  · rw [div_self hN, one_mul]

theorem mgenC_gnE_rev (hG : Equivalence G) (a b : α) :
    D.prob a * graphNoiseKernel D G 1 a b = D.prob b * graphNoiseKernel D G 1 b a := by
  rw [mgenC_gnE_eq, mgenC_gnE_eq]
  by_cases h : G a b
  · have h' : G b a := hG.symm h
    rw [filter_eq_of_rel hG h]
    simp only [h, h', ite_true]
    ring
  · have h' : ¬ G b a := fun h'' => h (hG.symm h'')
    simp [h, h']

theorem mgenC_gn_nonneg {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (a b : α) :
    0 ≤ graphNoiseKernel D G ξ a b := by
  unfold graphNoiseKernel
  have h2 : 0 ≤ (if G a b then D.prob b else 0) := by
    split_ifs
    · exact D.nonneg b
    · exact le_rfl
  have h3 := div_nonneg h2 (Finset.sum_nonneg fun c (_ : c ∈ univ.filter (G a)) => D.nonneg c)
  have h4 : 0 ≤ (1 - ξ) * (if a = b then (1:ℝ) else 0) :=
    mul_nonneg (by linarith) (by split_ifs <;> norm_num)
  exact add_nonneg h4 (mul_nonneg h0 h3)

theorem mgenC_gn_rowsum_le {ξ : ℝ} (h0 : 0 ≤ ξ) (_h1 : ξ ≤ 1) (a : α) :
    ∑ b, graphNoiseKernel D G ξ a b ≤ 1 := by
  unfold graphNoiseKernel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
  have e1 : ∑ b, (if a = b then (1:ℝ) else 0) = 1 := by simp
  have e2 : ∑ b, (if G a b then D.prob b else 0) = ∑ c ∈ univ.filter (G a), D.prob c := by
    rw [Finset.sum_filter]
  rw [e1, e2]
  have : (∑ c ∈ univ.filter (G a), D.prob c) / ∑ c ∈ univ.filter (G a), D.prob c ≤ 1 := by
    by_cases h : ∑ c ∈ univ.filter (G a), D.prob c = 0
    · simp [h]
    · rw [div_self h]
  nlinarith

theorem mgenC_gnE_rowsum (hG : Equivalence G) {a : α} (ha : D.prob a ≠ 0) :
    ∑ b, graphNoiseKernel D G 1 a b = 1 := by
  simp only [mgenC_gnE_eq]
  rw [← Finset.sum_div, ← Finset.sum_filter]
  have hle : D.prob a ≤ ∑ c ∈ univ.filter (G a), D.prob c :=
    Finset.single_le_sum (f := D.prob) (fun c _ => D.nonneg c) (by simp [hG.refl a])
  have : ∑ c ∈ univ.filter (G a), D.prob c ≠ 0 := by
    have := D.nonneg a
    intro h; apply ha; linarith
  exact div_self this

theorem mgenC_gnE_null {b : α} (hb : D.prob b = 0) (a : α) : graphNoiseKernel D G 1 a b = 0 := by
  rw [mgenC_gnE_eq]
  split_ifs <;> simp [hb]

theorem mgenC_gnE_rel {a b : α} (h : graphNoiseKernel D G 1 a b ≠ 0) : G a b := by
  by_contra hab
  apply h
  rw [mgenC_gnE_eq]
  simp [hab]

end GN

section Restriction
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mgenC_cexpect_ofReal {β : Type} [Fintype β] (π : FinProb β) (φ : β → ℝ) :
    π.cexpect (fun a => (φ a : ℂ)) = ((π.expect φ : ℝ) : ℂ) := by
  simp [FinProb.cexpect, FinProb.expect]

private def glueEquiv (I : Finset ι) : (↥I → α) × (↥Iᶜ → α) ≃ (ι → α) where
  toFun p := glueFree I p.1 p.2
  invFun x := (fun i => x i, fun i => x i)
  left_inv := by
    rintro ⟨y, z⟩
    refine Prod.ext ?_ ?_
    · funext i; simp [glueFree, i.2]
    · funext i
      have : (i : ι) ∉ I := mem_compl.1 i.2
      simp [glueFree, this]
  right_inv := by
    intro x; funext i; by_cases h : i ∈ I <;> simp [glueFree, h]

/-- a tensor operator on the live coordinates, seen on the whole index set. -/
theorem mgenCOp_restrictFree (I : Finset ι) (z : ↥Iᶜ → α) (K : α → α → ℝ)
    (f : (ι → α) → ℂ) (y : ↥I → α) :
    mgenCOp (fun _ : ↥I => K) (restrictFree I z f) y =
      mgenCOp (fun i a b => if i ∈ I then K a b else mgenCId a b) f (glueFree I y z) := by
  have hsplit : ∀ (y' : ↥I → α) (z' : ↥Iᶜ → α),
      (∏ i, (if i ∈ I then K (glueFree I y z i) (glueFree I y' z' i)
        else mgenCId (glueFree I y z i) (glueFree I y' z' i))) =
      (∏ i : ↥I, K (y i) (y' i)) * (if z = z' then 1 else 0) := by
    intro y' z'
    rw [← Finset.prod_mul_prod_compl I]
    congr 1
    · rw [← Finset.prod_coe_sort I]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [glueFree, i.2]
    · rw [← Finset.prod_coe_sort Iᶜ]
      have h : ∀ i : ↥Iᶜ, (if (i : ι) ∈ I then K (glueFree I y z i) (glueFree I y' z' i)
          else mgenCId (glueFree I y z i) (glueFree I y' z' i)) =
          if z i = z' i then 1 else 0 := by
        intro i
        have hi : (i : ι) ∉ I := mem_compl.1 i.2
        simp [glueFree, hi, mgenCId]
      rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_boole]
      simp [funext_iff]
  unfold mgenCOp restrictFree
  rw [← (glueEquiv I).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp only [glueEquiv, Equiv.coe_fn_mk, hsplit]
  rw [Finset.sum_eq_single z]
  · simp
  · intro z' _ hz'
    simp [Ne.symm hz']
  · simp

/-- averaging the squared norm of a restriction over the frozen coordinates. -/
theorem mgenC_cexpect_cl2sq_restrict (D : FinProb α) (I : Finset ι) (u : (ι → α) → ℂ) :
    (D.pi ↥Iᶜ).cexpect (fun z => ((cl2sq D (restrictFree I z u) : ℝ) : ℂ)) =
      ((cl2sq D u : ℝ) : ℂ) := by
  have h := inner_glue D D I (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ))
  simp only [ite_self] at h
  have e1 : ∀ z, ((cl2sq D (restrictFree I z u) : ℝ) : ℂ) =
      (D.pi ↥I).cexpect (fun y => ((‖u (glueFree I y z)‖ ^ 2 : ℝ) : ℂ)) := by
    intro z
    rw [mgenC_cexpect_ofReal]
    rfl
  simp only [e1, h]
  unfold cl2sq FinProb.expect
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [FinProb.pi_prob]
  push_cast
  ring

theorem mgenC_expect_cl2sq_restrict (D : FinProb α) (I : Finset ι) (u : (ι → α) → ℂ) :
    (D.pi ↥Iᶜ).expect (fun z => cl2sq D (restrictFree I z u)) = cl2sq D u := by
  have := mgenC_cexpect_cl2sq_restrict D I u
  rw [mgenC_cexpect_ofReal] at this
  exact_mod_cast this

private theorem bern_disjoint {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (B : Finset ι) :
    ((bernoulli s hs0 hs1).pi ι).expect
      (fun σ => if Disjoint B (trueSet σ) then (1 : ℝ) else 0) = (1 - s) ^ B.card := by
  have e : ∀ σ : ι → Bool, (if Disjoint B (trueSet σ) then (1 : ℝ) else 0) =
      ∏ i, (if (i ∈ B → σ i = false) then (1 : ℝ) else 0) := by
    intro σ
    rw [Finset.prod_boole]
    congr 1
    simp [Finset.disjoint_left, trueSet]
  unfold FinProb.expect
  simp only [e, FinProb.pi_prob, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (bernoulli s hs0 hs1).prob b *
    (if (i ∈ B → b = false) then (1 : ℝ) else 0))]
  have h : ∀ i, ∑ b, (bernoulli s hs0 hs1).prob b * (if (i ∈ B → b = false) then (1 : ℝ) else 0) =
      if i ∈ B then 1 - s else 1 := by
    intro i
    by_cases hi : i ∈ B <;> simp [bernoulli, hi]
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- the restriction identity: the expected mass of a restriction off non-merged degree `0` is
`Σ_B (1 - (1-s)^{|B|}) ‖f^{(B)}‖²`. -/
theorem mgenC_restrict_identity (D : FinProb α) (G : α → α → Prop) [DecidableRel G]
    (hG : Equivalence G) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (f : (ι → α) → ℂ) :
    (mixtureRestrictionExpect s hs0 hs1 D f fun _ gt =>
        ((cl2sq D (fun x => gt x - graphNoiseOp D G 1 gt x) : ℝ) : ℂ)).re =
      ∑ B : Finset ι, (1 - (1 - s) ^ B.card) *
        cl2sq D (mgenCP (graphNoiseKernel D G 1) B f) := by
  set E := graphNoiseKernel D G 1 with hE
  have hEE : ∀ a c, ∑ b, E a b * E b c = E a c := mgenC_gnE_idem hG
  have hErev : ∀ a b, D.prob a * E a b = D.prob b * E b a := mgenC_gnE_rev hG
  set u : Finset ι → (ι → α) → ℂ := fun I =>
    f - mgenCOp (fun i a b => if i ∈ I then E a b else mgenCId a b) f with hu
  have h1 : ∀ (I : Finset ι) (z : ↥Iᶜ → α),
      (fun x => restrictFree I z f x - graphNoiseOp D G 1 (restrictFree I z f) x) =
        restrictFree I z (u I) := by
    intro I z
    funext y
    show restrictFree I z f y - mgenCOp (fun _ => E) (restrictFree I z f) y = _
    rw [mgenCOp_restrictFree]
    rfl
  have h2 : ∀ I : Finset ι, u I =
      ∑ B : Finset ι, ((if Disjoint B I then 0 else 1 : ℝ) : ℂ) • mgenCP E B f := by
    intro I
    rw [hu]
    simp only
    conv_lhs => rw [← mgenCP_sum (E := E) f]
    rw [mgenCOp_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [mgenCOp_E_mgenCP hEE]
    split_ifs <;> simp
  have h3 : ∀ I : Finset ι, cl2sq D (u I) =
      ∑ B : Finset ι, (if Disjoint B I then 0 else 1) * cl2sq D (mgenCP E B f) := by
    intro I
    rw [h2, mgenCP_cl2sq_sum D hEE hErev]
    refine Finset.sum_congr rfl fun B _ => ?_
    split_ifs <;> simp
  unfold mixtureRestrictionExpect subsetExpect
  simp only [h1, mgenC_cexpect_ofReal, Complex.ofReal_re, mgenC_expect_cl2sq_restrict, h3]
  rw [FinProb.expect_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [FinProb.expect_mul_const]
  congr 1
  have h4 : ∀ σ : ι → Bool, (if Disjoint B (trueSet σ) then (0 : ℝ) else 1) =
      1 - (if Disjoint B (trueSet σ) then (1 : ℝ) else 0) := by
    intro σ; split_ifs <;> ring
  simp only [h4, FinProb.expect_sub, FinProb.expect_const, bern_disjoint]

end Restriction

section Spectral
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mgenC_cl2sq_smul (D : FinProb α) (c : ℂ) (u : (ι → α) → ℂ) :
    cl2sq D (c • u) = ‖c‖ ^ 2 * cl2sq D u := by
  unfold cl2sq FinProb.expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

private def complEquiv : Finset ι ≃ Finset ι :=
  ⟨compl, compl, fun s => compl_compl s, fun s => compl_compl s⟩

open scoped ComplexOrder in
/-- the tensorised gap bound on a full-support alphabet: the block `B` of a weighted block sum
contributes at most `b^{|B|}` to `⟨U, A^{⊗} U⟩` (`tensor_block_bound` with `a = 0`). -/
private theorem spec_abstract (D : FinProb α) (hD : ∀ a, 0 < D.prob a) (E : α → α → ℝ)
    (T : StochMat α) (hTrev : T.IsReversible D)
    (hEcol : ∀ c, (fun a => ((E a c : ℝ) : ℂ)) ∈ T.constOnComp)
    (hQcol : ∀ c, (fun a => ((mgenCQ E a c : ℝ) : ℂ)) ∈
      orthSet D (T.constOnComp : Set (α → ℂ)))
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (heig : ∀ g ∈ orthSet D (T.constOnComp : Set (α → ℂ)), g ≠ 0 → ∀ l : ℂ,
      T.cmat.mulVec g = l • g → ∃ r : ℝ, l = r ∧ 0 ≤ r ∧ r ≤ b)
    (c : Finset ι → ℂ) (F : (ι → α) → ℂ) :
    ((D.pi ι).cinner (∑ B, c B • mgenCP E B F)
      (mgenCOp (fun _ => T.prob) (∑ B, c B • mgenCP E B F))).re ≤
      ∑ B : Finset ι, ‖c B‖ ^ 2 * b ^ B.card * cl2sq D (mgenCP E B F) := by
  have hVfix : ∀ v ∈ T.constOnComp, T.cmat.mulVec v = v := fun v hv =>
    mulVec_eq_of_supp T T (fun _ _ _ h => h) hv
  obtain ⟨-, -, -, b4⟩ := tensor_block_bound D hD T.constOnComp T.cmat (cmat_selfadj T D hTrev)
    hVfix (orthSet_mulVec T D hTrev hVfix) (a := 0) (b := b) le_rfl hb0 hb1 heig ι
  have hP : ∀ B : Finset ι, mgenCP E B F =
      ∑ x' : ι → α, F x' • (fun x => ∏ i, ((mgenCPk E B i (x i) (x' i) : ℝ) : ℂ)) := by
    intro B
    funext x
    simp only [mgenCP, mgenCOp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_prod]
    exact Finset.sum_congr rfl fun x' _ => mul_comm _ _
  have hmem : ∀ S : Finset ι, c Sᶜ • mgenCP E Sᶜ F ∈
      blockSpace (T.constOnComp : Set (α → ℂ)) (orthSet D (T.constOnComp : Set (α → ℂ))) S := by
    intro S
    refine Submodule.smul_mem _ _ ?_
    rw [hP]
    refine Submodule.sum_mem _ fun x' _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun i a => ((mgenCPk E Sᶜ i a (x' i) : ℝ) : ℂ), fun i hi => ?_, fun i hi => ?_, rfl⟩
    · have h : i ∉ Sᶜ := by simpa using hi
      simp only [mgenCPk, h, ite_false]
      exact hEcol (x' i)
    · have h : i ∈ Sᶜ := by simpa using hi
      simp only [mgenCPk, h, ite_true]
      exact hQcol (x' i)
  have hsum : ∑ B, c B • mgenCP E B F = ∑ S : Finset ι, c Sᶜ • mgenCP E Sᶜ F :=
    (Fintype.sum_equiv complEquiv (fun S => c Sᶜ • mgenCP E Sᶜ F) _ (fun _ => rfl)).symm
  obtain ⟨-, h2, -, -⟩ := b4 _ _ hmem hsum
  have hop : mgenCOp (fun _ => T.prob) (∑ B, c B • mgenCP E B F) =
      (kernelPow T.cmat ι).mulVec (∑ B, c B • mgenCP E B F) := by
    funext x
    simp only [mgenCOp, Matrix.mulVec, dotProduct, kernelPow, StochMat.cmat, Matrix.of_apply,
      Complex.ofReal_prod]
  rw [hop]
  have h3 := (Complex.le_def.1 h2).1
  rw [Complex.ofReal_re] at h3
  refine h3.trans (le_of_eq ?_)
  rw [← Fintype.sum_equiv complEquiv (fun B => ‖c B‖ ^ 2 * b ^ B.card * cl2sq D (mgenCP E B F))
    (fun S => cl2sq D (c Sᶜ • mgenCP E Sᶜ F) * b ^ (Fintype.card ι - S.card))]
  intro B
  show _ = cl2sq D (c Bᶜᶜ • mgenCP E Bᶜᶜ F) * b ^ (Fintype.card ι - Bᶜ.card)
  rw [compl_compl, mgenC_cl2sq_smul, Finset.card_compl, Nat.sub_sub_self (Finset.card_le_univ B)]
  ring

end Spectral

section PosRestrict
variable {X : Type} [Fintype X] [DecidableEq X] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem sum_pos_one (P : X → Prop) [DecidablePred P] {M : Type} [AddCommMonoid M] (φ : X → M)
    (h : ∀ a, ¬ P a → φ a = 0) : ∑ a : {a // P a}, φ a.val = ∑ a, φ a :=
  Fintype.sum_of_injective (fun a : {a // P a} => a.val) Subtype.val_injective _ _
    (fun a ha => h a (fun hp => ha ⟨⟨a, hp⟩, rfl⟩)) (fun _ => rfl)

private theorem sum_pos_pi (P : X → Prop) [DecidablePred P] {M : Type} [AddCommMonoid M] (F : (ι → X) → M)
    (h : ∀ x, (∃ i, ¬ P (x i)) → F x = 0) :
    ∑ x : ι → {a // P a}, F (fun i => (x i).val) = ∑ x, F x :=
  Fintype.sum_of_injective (fun (x : ι → {a // P a}) i => (x i).val)
    (fun x x' h => funext fun i => Subtype.ext (congrFun h i)) _ _
    (fun x hx => h x (by
      by_contra hc
      push Not at hc
      exact hx ⟨fun i => ⟨x i, hc i⟩, rfl⟩)) (fun _ => rfl)

private theorem op_pos (P : X → Prop) [DecidablePred P] (K : ι → X → X → ℝ)
    (hK : ∀ i a b, P a → ¬ P b → K i a b = 0) (f : (ι → X) → ℂ) (x : ι → {a // P a}) :
    mgenCOp K f (fun i => (x i).val) =
      mgenCOp (fun i (a b : {a // P a}) => K i a.val b.val) (fun x' => f (fun i => (x' i).val))
        x := by
  unfold mgenCOp
  symm
  exact sum_pos_pi P (fun x' => ((∏ i, K i (x i).val (x' i) : ℝ) : ℂ) * f x')
    (fun x' ⟨i, hi⟩ => by
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hK i _ _ (x i).2 hi)]
      simp)

/-- `D` restricted to its support (full support). -/
private def posProb (D : FinProb X) : FinProb {a // 0 < D.prob a} where
  prob a := D.prob a.val
  nonneg a := D.nonneg a.val
  sum_eq_one := by
    rw [sum_pos_one (fun a => 0 < D.prob a) D.prob
      (fun a ha => le_antisymm (not_lt.1 ha) (D.nonneg a))]
    exact D.sum_eq_one

private theorem pi_null {D : FinProb X} {x : ι → X} (h : ∃ i, ¬ 0 < D.prob (x i)) :
    (D.pi ι).prob x = 0 := by
  obtain ⟨i, hi⟩ := h
  rw [FinProb.pi_prob]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (le_antisymm (not_lt.1 hi) (D.nonneg _))

private theorem cinner_pos (D : FinProb X) (f g : (ι → X) → ℂ) :
    (D.pi ι).cinner f g = ((posProb D).pi ι).cinner (fun x => f (fun i => (x i).val))
      (fun x => g (fun i => (x i).val)) := by
  unfold FinProb.cinner FinProb.cexpect
  symm
  exact sum_pos_pi (fun a => 0 < D.prob a) (fun x => ((D.pi ι).prob x : ℂ) * (f x * star (g x)))
    (fun x hx => by rw [pi_null hx]; simp)

private theorem cl2sq_pos (D : FinProb X) (f : (ι → X) → ℂ) :
    cl2sq D f = cl2sq (posProb D) (fun x => f (fun i => (x i).val)) := by
  unfold cl2sq FinProb.expect
  symm
  exact sum_pos_pi (fun a => 0 < D.prob a) (fun x => (D.pi ι).prob x * ‖f x‖ ^ 2)
    (fun x hx => by rw [pi_null hx]; simp)

end PosRestrict

section ChainS
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

theorem mgenC_lawX_prob (μ : FinProb (X × Y × Z)) (a : X) :
    (lawX μ).prob a = ∑ y, ∑ z, μ.prob (a, y, z) := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.1 = a), μ.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [Fintype.sum_prod_type]
  · intro b _ hb
    simp [hb]
  · simp

private theorem prob_le_lawX (μ : FinProb (X × Y × Z)) (a : X) (y : Y) (z : Z) :
    μ.prob (a, y, z) ≤ (lawX μ).prob a := by
  rw [mgenC_lawX_prob]
  exact (Finset.single_le_sum (f := fun z => μ.prob (a, y, z)) (fun z _ => μ.nonneg _)
    (Finset.mem_univ z)).trans (Finset.single_le_sum (f := fun y => ∑ z, μ.prob (a, y, z))
      (fun y _ => Finset.sum_nonneg fun z _ => μ.nonneg _) (Finset.mem_univ y))

private theorem prob_le_one' {β : Type} [Fintype β] (π : FinProb β) (b : β) : π.prob b ≤ 1 := by
  rw [← π.sum_eq_one]
  exact Finset.single_le_sum (f := π.prob) (fun c _ => π.nonneg c) (Finset.mem_univ b)

private theorem yz_le_one (μ : FinProb (X × Y × Z)) (y : Y) (z : Z) :
    ∑ x, μ.prob (x, y, z) ≤ 1 := by
  calc ∑ x, μ.prob (x, y, z) ≤ ∑ x, (lawX μ).prob x :=
        Finset.sum_le_sum fun x _ => prob_le_lawX μ x y z
    _ = 1 := (lawX μ).sum_eq_one

private theorem lawX_null (μ : FinProb (X × Y × Z)) {a : X} (ha : ¬ 0 < (lawX μ).prob a)
    (y : Y) (z : Z) : μ.prob (a, y, z) = 0 :=
  le_antisymm ((prob_le_lawX μ a y z).trans (not_lt.1 ha)) (μ.nonneg _)

private theorem mgenS_nonneg (μ : FinProb (X × Y × Z)) (a b : X) : 0 ≤ mgenS μ a b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (div_nonneg (μ.nonneg _) ((lawX μ).nonneg _))
      (div_nonneg (μ.nonneg _) (Finset.sum_nonneg fun _ _ => μ.nonneg _))

private theorem mgenS_null (μ : FinProb (X × Y × Z)) (a : X) {b : X}
    (hb : ¬ 0 < (lawX μ).prob b) : mgenS μ a b = 0 := by
  unfold mgenS
  simp [lawX_null μ hb]

private theorem mgenS_rev_form (μ : FinProb (X × Y × Z)) (a b : X) :
    (lawX μ).prob a * mgenS μ a b =
      ∑ y, ∑ z, μ.prob (a, y, z) * μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z) := by
  by_cases ha : 0 < (lawX μ).prob a
  · unfold mgenS
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    field_simp
  · rw [le_antisymm (not_lt.1 ha) ((lawX μ).nonneg a)]
    simp [lawX_null μ ha]

private theorem mgenS_rowsum (μ : FinProb (X × Y × Z)) {a : X} (ha : 0 < (lawX μ).prob a) :
    ∑ b, mgenS μ a b = 1 := by
  unfold mgenS
  rw [Finset.sum_comm]
  have h : ∀ y, ∑ b, ∑ z, μ.prob (a, y, z) / (lawX μ).prob a *
      (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z)) = ∑ z, μ.prob (a, y, z) / (lawX μ).prob a := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_div]
    by_cases hN : ∑ x, μ.prob (x, y, z) = 0
    · have hle : μ.prob (a, y, z) ≤ ∑ x, μ.prob (x, y, z) :=
        Finset.single_le_sum (f := fun x => μ.prob (x, y, z)) (fun x _ => μ.nonneg _)
          (Finset.mem_univ a)
      have : μ.prob (a, y, z) = 0 := le_antisymm (hN ▸ hle) (μ.nonneg _)
      simp [this]
    · rw [div_self hN, mul_one]
  simp only [h]
  simp_rw [← Finset.sum_div]
  rw [← mgenC_lawX_prob, div_self ha.ne']

private theorem mgenS_pos_support (μ : FinProb (X × Y × Z)) {a b : X} (h : mgenS μ a b ≠ 0) :
    ∃ y z, μ.prob (a, y, z) ≠ 0 ∧ μ.prob (b, y, z) ≠ 0 := by
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  refine ⟨y, z, fun h1 => hz ?_, fun h2 => hz ?_⟩
  · simp [h1]
  · simp [h2]

private theorem mgenS_atom (μ : FinProb (X × Y × Z)) {α₀ : ℝ} (hα0 : 0 ≤ α₀)
    (hat : ∀ p ∈ μ.support, α₀ ≤ μ.prob p) {a b : X} (h : 0 < mgenS μ a b) :
    α₀ * α₀ ≤ mgenS μ a b := by
  obtain ⟨y, z, h1, h2⟩ := mgenS_pos_support μ h.ne'
  have hA : α₀ ≤ μ.prob (a, y, z) := hat _ h1
  have hB : α₀ ≤ μ.prob (b, y, z) := hat _ h2
  have hL : 0 < (lawX μ).prob a :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm h1)) (prob_le_lawX μ a y z)
  have hN : 0 < ∑ x, μ.prob (x, y, z) :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm h2))
      (Finset.single_le_sum (f := fun x => μ.prob (x, y, z)) (fun x _ => μ.nonneg _)
        (Finset.mem_univ b))
  have ht : μ.prob (a, y, z) / (lawX μ).prob a * (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z)) ≤
      mgenS μ a b := by
    unfold mgenS
    refine (Finset.single_le_sum (f := fun z => μ.prob (a, y, z) / (lawX μ).prob a *
      (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z))) (fun z _ => ?_) (Finset.mem_univ z)).trans
      (Finset.single_le_sum (f := fun y => ∑ z, μ.prob (a, y, z) / (lawX μ).prob a *
      (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z))) (fun y _ => Finset.sum_nonneg fun z _ => ?_)
        (Finset.mem_univ y))
    · exact mul_nonneg (div_nonneg (μ.nonneg _) ((lawX μ).nonneg _))
        (div_nonneg (μ.nonneg _) (Finset.sum_nonneg fun x _ => μ.nonneg _))
    · exact mul_nonneg (div_nonneg (μ.nonneg _) ((lawX μ).nonneg _))
        (div_nonneg (μ.nonneg _) (Finset.sum_nonneg fun x _ => μ.nonneg _))
  have e1 : α₀ ≤ μ.prob (a, y, z) / (lawX μ).prob a :=
    hA.trans (le_div_self (μ.nonneg _) hL (prob_le_one' _ a))
  have e2 : α₀ ≤ μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z) :=
    hB.trans (le_div_self (μ.nonneg _) hN (yz_le_one μ y z))
  exact (mul_le_mul e1 e2 hα0 (hα0.trans e1)).trans ht

private theorem mgenS_pos_of_adj (μ : FinProb (X × Y × Z)) {a b : X} {y : Y} {z : Z}
    (h1 : (a, y, z) ∈ μ.support) (h2 : (b, y, z) ∈ μ.support) : 0 < mgenS μ a b := by
  have hA : 0 < μ.prob (a, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h1)
  have hB : 0 < μ.prob (b, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h2)
  have hL : 0 < (lawX μ).prob a := lt_of_lt_of_le hA (prob_le_lawX μ a y z)
  have hN : 0 < ∑ x, μ.prob (x, y, z) :=
    lt_of_lt_of_le hB (Finset.single_le_sum (f := fun x => μ.prob (x, y, z))
      (fun x _ => μ.nonneg _) (Finset.mem_univ b))
  have ht : 0 < μ.prob (a, y, z) / (lawX μ).prob a * (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z)) :=
    mul_pos (div_pos hA hL) (div_pos hB hN)
  unfold mgenS
  refine lt_of_lt_of_le ht ((Finset.single_le_sum (f := fun z => μ.prob (a, y, z) /
      (lawX μ).prob a * (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z))) (fun z _ => ?_)
      (Finset.mem_univ z)).trans (Finset.single_le_sum (f := fun y => ∑ z, μ.prob (a, y, z) /
      (lawX μ).prob a * (μ.prob (b, y, z) / ∑ x, μ.prob (x, y, z)))
      (fun y _ => Finset.sum_nonneg fun z _ => ?_) (Finset.mem_univ y)))
  · exact mul_nonneg (div_nonneg (μ.nonneg _) ((lawX μ).nonneg _))
      (div_nonneg (μ.nonneg _) (Finset.sum_nonneg fun x _ => μ.nonneg _))
  · exact mul_nonneg (div_nonneg (μ.nonneg _) ((lawX μ).nonneg _))
      (div_nonneg (μ.nonneg _) (Finset.sum_nonneg fun x _ => μ.nonneg _))

private theorem lawX_atom (μ : FinProb (X × Y × Z)) {α₀ : ℝ}
    (hat : ∀ p ∈ μ.support, α₀ ≤ μ.prob p) {a : X} (ha : 0 < (lawX μ).prob a) :
    α₀ ≤ (lawX μ).prob a := by
  rw [mgenC_lawX_prob] at ha ⊢
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha.ne'
  obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  exact (hat _ hz).trans ((Finset.single_le_sum (f := fun z => μ.prob (a, y, z))
    (fun z _ => μ.nonneg _) (Finset.mem_univ z)).trans (Finset.single_le_sum
      (f := fun y => ∑ z, μ.prob (a, y, z)) (fun y _ => Finset.sum_nonneg fun z _ => μ.nonneg _)
      (Finset.mem_univ y)))

/-- positive semi-definiteness of a Gram-type kernel. -/
private theorem gram_psd {β U : Type} [Fintype β] [Fintype U] (k : β → U → ℝ) (N : U → ℝ)
    (hN : ∀ u, 0 ≤ N u) (g : β → ℂ) :
    0 ≤ (∑ a, ∑ b, ((∑ u, k a u * k b u / N u : ℝ) : ℂ) * g b * star (g a)).re := by
  set A : U → ℂ := fun u => ∑ a, (k a u : ℂ) * g a with hA
  have h : ∑ a, ∑ b, ((∑ u, k a u * k b u / N u : ℝ) : ℂ) * g b * star (g a) =
      ∑ u, ((1 / N u : ℝ) : ℂ) * (A u * star (A u)) := by
    have e : ∀ u, ((1 / N u : ℝ) : ℂ) * (A u * star (A u)) =
        ∑ a, ∑ b, ((k a u * k b u / N u : ℝ) : ℂ) * g b * star (g a) := by
      intro u
      simp only [hA, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      push_cast
      ring
    rw [Finset.sum_congr rfl fun u _ => e u]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
  rw [h, Complex.re_sum]
  refine Finset.sum_nonneg fun u _ => ?_
  rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (by have := hN u; positivity) (Complex.normSq_nonneg _)

end ChainS

section SpecX
open scoped Classical

/-- `lem:mossel_MC` for the chain `S = T*T`, tensorised (the content of
`#coordinate-merge-chain-eigenbasis`): on a weighted sum of blocks of the component average `(graphNoiseKernel (lawX μ) (mgenComp μ) 1)`,
`⟨U, S^{⊗} U⟩ ≤ Σ_B ‖c_B‖² (1-γ)^{|B|} ‖f^{(B)}‖²`, with `γ` depending on `m` and the atom bound
only. Null symbols are handled by restricting to the support of `μ_x`. -/
theorem mgenC_spec (m : ℕ) {α₀ : ℝ} (hα : 0 < α₀) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α₀ ≤ μ.prob p) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Finset ι → ℂ) (F : (ι → X) → ℂ),
          (((lawX μ).pi ι).cinner
            (∑ B, c B • mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F)
            (mgenSOp μ (∑ B, c B • mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F))).re ≤
          ∑ B : Finset ι, ‖c B‖ ^ 2 * (1 - γ) ^ B.card *
            cl2sq (lawX μ) (mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F) := by
  set γ : ℝ := min 1 (α₀ * (α₀ * α₀) / (2 * ((m : ℝ) + 1) ^ 3)) with hγ
  refine ⟨γ, lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro X Y Z _ _ _ _ _ _ hcard μ hat ι _ _ c F
  have hG : Equivalence (mgenComp μ) := SimpleGraph.reachable_is_equivalence _
  set Dp := posProb (lawX μ) with hDp
  let Ep : {a // 0 < (lawX μ).prob a} → {a // 0 < (lawX μ).prob a} → ℝ := fun a b => (graphNoiseKernel (lawX μ) (mgenComp μ) 1) a.val b.val
  let T : StochMat {a // 0 < (lawX μ).prob a} :=
    ⟨fun a b => mgenS μ a.val b.val, fun a b => mgenS_nonneg μ _ _, fun a => by
      rw [sum_pos_one (fun b => 0 < (lawX μ).prob b) (fun b => mgenS μ a.val b)
        (fun b hb => mgenS_null μ _ hb)]
      exact mgenS_rowsum μ a.2⟩
  -- the transition graph of `T` has the components of the merge graph
  have hadj : ∀ a b : {a // 0 < (lawX μ).prob a}, T.graph.Adj a b →
      (mergeGraphX μ.support).Adj a.val b.val := by
    intro a b h
    rw [graph_adj_iff] at h
    obtain ⟨hab, h1 | h1⟩ := h
    · obtain ⟨y, z, h2, h3⟩ := mgenS_pos_support μ h1.ne'
      exact (SimpleGraph.fromRel_adj _ _ _).2
        ⟨fun e => hab (Subtype.ext e), Or.inl ⟨y, z, h2, h3⟩⟩
    · obtain ⟨y, z, h2, h3⟩ := mgenS_pos_support μ h1.ne'
      exact (SimpleGraph.fromRel_adj _ _ _).2
        ⟨fun e => hab (Subtype.ext e), Or.inr ⟨y, z, h2, h3⟩⟩
  let hom : T.graph →g mergeGraphX μ.support := ⟨Subtype.val, fun h => hadj _ _ h⟩
  have hlift : ∀ (a : {a // 0 < (lawX μ).prob a}) (b : X), (mergeGraphX μ.support).Reachable a.val b →
      ∃ hb : 0 < (lawX μ).prob b, T.graph.Reachable a ⟨b, hb⟩ := by
    intro a b h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ⟨a.2, SimpleGraph.Reachable.refl _⟩
    | @tail c d _ hcd ih =>
      obtain ⟨hc, hr⟩ := ih
      obtain ⟨hne, hrel⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hcd
      obtain ⟨y, z, h1, h2⟩ : ∃ y z, (c, y, z) ∈ μ.support ∧ (d, y, z) ∈ μ.support := by
        rcases hrel with ⟨y, z, h1, h2⟩ | ⟨y, z, h1, h2⟩
        · exact ⟨y, z, h1, h2⟩
        · exact ⟨y, z, h2, h1⟩
      have hd : 0 < (lawX μ).prob d := lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm h2))
        (prob_le_lawX μ d y z)
      refine ⟨hd, hr.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact (graph_adj_iff T _ _).2 ⟨fun e => hne (congrArg Subtype.val e),
        Or.inl (mgenS_pos_of_adj μ h1 h2)⟩
  have hTG : ∀ a b : {a // 0 < (lawX μ).prob a}, T.graph.Reachable a b ↔ mgenComp μ a.val b.val := by
    intro a b
    refine ⟨fun h => h.map hom, fun h => ?_⟩
    obtain ⟨hb, hr⟩ := hlift a b.val h
    exact hr
  have hTrev : T.IsReversible Dp := by
    intro a b
    show (lawX μ).prob a.val * mgenS μ a.val b.val = (lawX μ).prob b.val * mgenS μ b.val a.val
    rw [mgenS_rev_form, mgenS_rev_form]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    ring
  have hEcol : ∀ c, (fun a => ((Ep a c : ℝ) : ℂ)) ∈ T.constOnComp := by
    intro c a b hab
    show (((graphNoiseKernel (lawX μ) (mgenComp μ) 1) a.val c.val : ℝ) : ℂ) = (((graphNoiseKernel (lawX μ) (mgenComp μ) 1) b.val c.val : ℝ) : ℂ)
    rw [mgenC_gnE_row hG ((hTG a b).1 hab)]
  have hrow : ∀ c : {a // 0 < (lawX μ).prob a}, ∑ a : {a // 0 < (lawX μ).prob a}, Ep c a = 1 := by
    intro c
    rw [sum_pos_one (fun b => 0 < (lawX μ).prob b) (fun b => (graphNoiseKernel (lawX μ) (mgenComp μ) 1) c.val b)
      (fun b hb => mgenC_gnE_null (le_antisymm (not_lt.1 hb) ((lawX μ).nonneg b)) _)]
    exact mgenC_gnE_rowsum hG c.2.ne'
  have hQcol : ∀ c, (fun a => ((mgenCQ Ep a c : ℝ) : ℂ)) ∈
      orthSet Dp (T.constOnComp : Set ({a // 0 < (lawX μ).prob a} → ℂ)) := by
    intro c v hv
    have hv' : ∀ a, Ep c a ≠ 0 → v a = v c := fun a ha =>
      (hv c a ((hTG c a).2 (mgenC_gnE_rel ha))).symm
    have hQrev : ∀ a, Dp.prob a * mgenCQ Ep a c = Dp.prob c * mgenCQ Ep c a := by
      intro a
      unfold mgenCQ mgenCId
      by_cases h : a = c
      · subst h; rfl
      · simp only [h, Ne.symm h, ite_false]
        have := mgenC_gnE_rev (D := lawX μ) hG a.val c.val
        show (lawX μ).prob a.val * (0 - (graphNoiseKernel (lawX μ) (mgenComp μ) 1) a.val c.val) = (lawX μ).prob c.val * (0 - (graphNoiseKernel (lawX μ) (mgenComp μ) 1) c.val a.val)
        linarith
    have hsum : ∑ a, ((mgenCQ Ep c a : ℝ) : ℂ) * v a = 0 := by
      have e : ∀ a, ((mgenCQ Ep c a : ℝ) : ℂ) * v a = ((mgenCQ Ep c a : ℝ) : ℂ) * v c := by
        intro a
        by_cases ha : Ep c a = 0
        · by_cases hca : c = a
          · rw [hca]
          · have : mgenCQ Ep c a = 0 := by
              unfold mgenCQ mgenCId
              rw [if_neg hca, ha]; norm_num
            rw [this]; simp
        · rw [hv' a ha]
      rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.sum_mul]
      have h0 : ∑ a, mgenCQ Ep c a = 0 := by
        unfold mgenCQ mgenCId
        rw [Finset.sum_sub_distrib, hrow, Finset.sum_ite_eq]
        simp
      rw [← Complex.ofReal_sum, h0]
      simp
    show Dp.cinner _ v = 0
    rw [cinner_def]
    have e2 : ∀ a, (Dp.prob a : ℂ) * (((mgenCQ Ep a c : ℝ) : ℂ) * star (v a)) =
        (Dp.prob c : ℂ) * star (((mgenCQ Ep c a : ℝ) : ℂ) * v a) := by
      intro a
      rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← mul_assoc,
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, hQrev a]
    rw [Finset.sum_congr rfl fun a _ => e2 a, ← Finset.mul_sum, ← star_sum, hsum, star_zero,
      mul_zero]
  have heig : ∀ g ∈ orthSet Dp (T.constOnComp : Set ({a // 0 < (lawX μ).prob a} → ℂ)), g ≠ 0 →
      ∀ l : ℂ, T.cmat.mulVec g = l • g → ∃ r : ℝ, l = r ∧ 0 ≤ r ∧ r ≤ 1 - γ := by
    intro g hg hg0 l hl
    obtain ⟨r, t, hlr, ht, hgeig, hnorm⟩ := eig_info T Dp (fun a => a.2) hTrev g hg0 l hl
    refine ⟨r, hlr, ?_, ?_⟩
    · set g' := (t : ℂ) • g with hg'
      have hpsd := gram_psd (fun (a : {a // 0 < (lawX μ).prob a}) (u : Y × Z) => μ.prob (a.val, u.1, u.2))
        (fun u => ∑ x, μ.prob (x, u.1, u.2)) (fun u => Finset.sum_nonneg fun x _ => μ.nonneg _) g'
      have hw : ∀ a b : {a // 0 < (lawX μ).prob a}, (∑ u : Y × Z, μ.prob (a.val, u.1, u.2) *
          μ.prob (b.val, u.1, u.2) / ∑ x, μ.prob (x, u.1, u.2)) = Dp.prob a * T.prob a b := by
        intro a b
        show _ = (lawX μ).prob a.val * mgenS μ a.val b.val
        rw [mgenS_rev_form, Fintype.sum_prod_type]
      simp only [hw] at hpsd
      have key : ∑ a, ∑ b, ((Dp.prob a * T.prob a b : ℝ) : ℂ) * g' b * star (g' a) = (r : ℂ) := by
        have e : ∀ a, ∑ b, ((Dp.prob a * T.prob a b : ℝ) : ℂ) * g' b * star (g' a) =
            ((Dp.prob a * ‖g' a‖ ^ 2 : ℝ) : ℂ) * r := by
          intro a
          have h1 : ∑ b, ((Dp.prob a * T.prob a b : ℝ) : ℂ) * g' b * star (g' a) =
              (Dp.prob a : ℂ) * (∑ b, (T.prob a b : ℂ) * g' b) * star (g' a) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun b _ => ?_
            push_cast; ring
          have h2 : g' a * star (g' a) = ((‖g' a‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          rw [h1, hgeig a, Complex.ofReal_mul, ← h2]
          ring
        rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.sum_mul, ← Complex.ofReal_sum, hnorm]
        simp
      rw [key, Complex.ofReal_re] at hpsd
      exact hpsd
    · have hg' : ((t : ℂ) • g) ∈ orthSet Dp (T.constOnComp : Set ({a // 0 < (lawX μ).prob a} → ℂ)) := by
        intro v hv
        rw [cinner_smul_left, hg v hv, mul_zero]
      have hstat : T.IsStationary Dp := by
        intro b
        have : ∀ a, Dp.prob a * T.prob a b = Dp.prob b * T.prob b a := fun a => hTrev a b
        simp_rw [this, ← Finset.mul_sum, T.row_sum, mul_one]
      have hn : (Fintype.card {a // 0 < (lawX μ).prob a} : ℝ) ≤ (m : ℝ) + 1 := by
        have h1 : Fintype.card {a // 0 < (lawX μ).prob a} ≤ m := (Fintype.card_subtype_le _).trans hcard
        have h2 : (Fintype.card {a // 0 < (lawX μ).prob a} : ℝ) ≤ m := by exact_mod_cast h1
        linarith
      have hTα : ∀ a b, 0 < T.prob a b → α₀ * α₀ ≤ T.prob a b :=
        fun a b h => mgenS_atom μ hα.le hat h
      have := gap_bound T Dp α₀ hα (fun a => lawX_atom μ hat a.2) hstat ((m : ℝ) + 1) hn _ r
        hgeig hnorm (orth_comp T Dp _ hg') (α₀ * α₀) (by positivity) hTα
      have hγle : γ ≤ α₀ * (α₀ * α₀) / (2 * ((m : ℝ) + 1) ^ 3) := min_le_right _ _
      linarith
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have habs := spec_abstract Dp (fun a => a.2) Ep T hTrev hEcol hQcol (b := 1 - γ)
    (by linarith) (by linarith [show 0 < γ from lt_min one_pos (by positivity)]) heig c
    (fun x => F (fun i => (x i).val))
  -- transfer from the support of `μ_x` back to `X`
  have hK : ∀ (B : Finset ι) (i : ι) (a b : X), 0 < (lawX μ).prob a → ¬ 0 < (lawX μ).prob b →
      mgenCPk (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B i a b = 0 := by
    intro B i a b ha hb
    have hEab : (graphNoiseKernel (lawX μ) (mgenComp μ) 1) a b = 0 := mgenC_gnE_null (le_antisymm (not_lt.1 hb) ((lawX μ).nonneg b)) a
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    unfold mgenCPk mgenCQ mgenCId
    simp [hab, hEab]
  have hPB : ∀ (B : Finset ι) (x : ι → {a // 0 < (lawX μ).prob a}),
      mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F (fun i => (x i).val) = mgenCP Ep B (fun x => F (fun i => (x i).val)) x := by
    intro B x
    unfold mgenCP
    rw [op_pos (fun a => 0 < (lawX μ).prob a) (mgenCPk (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B) (hK B) F x]
    refine congrFun (mgenCOp_congr (fun i a b => ?_) _) x
    unfold mgenCPk mgenCQ mgenCId
    by_cases h : a = b
    · subst h; simp [Ep]
    · have h' : a.val ≠ b.val := fun e => h (Subtype.ext e)
      simp [h, h', Ep]
  have hU : (fun x : ι → {a // 0 < (lawX μ).prob a} =>
      (∑ B, c B • mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F) (fun i => (x i).val)) =
      ∑ B, c B • mgenCP Ep B (fun x => F (fun i => (x i).val)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hPB]
  have hSop : (fun x : ι → {a // 0 < (lawX μ).prob a} =>
      mgenSOp μ (∑ B, c B • mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F) (fun i => (x i).val)) =
      mgenCOp (fun _ => T.prob) (∑ B, c B • mgenCP Ep B (fun x => F (fun i => (x i).val))) := by
    funext x
    show mgenCOp (fun _ => mgenS μ) _ _ = _
    rw [op_pos (fun a => 0 < (lawX μ).prob a) (fun _ => mgenS μ)
      (fun _ a b _ hb => mgenS_null μ a hb) _ x, hU]
  rw [cinner_pos (lawX μ), hU, hSop]
  refine habs.trans (le_of_eq (Finset.sum_congr rfl fun B _ => ?_))
  rw [cl2sq_pos (lawX μ) (mgenCP (graphNoiseKernel (lawX μ) (mgenComp μ) 1) B F)]
  simp only [hPB]
  rfl

end SpecX

end MaxT
end TrackB
end RestrictedPolynomials
end
