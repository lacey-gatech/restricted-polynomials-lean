import RestrictedPolynomials.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# The Efron–Stein decomposition

For `π` a distribution on a finite set `α` and `f : α^ι → ℝ`, with `f^{=S}` defined by the
inclusion–exclusion formula of Section 2, we prove:

* `condExp_condExp` : `𝔼(𝔼(f | x_U) | x_T) = 𝔼(f | x_{T ∩ U})`;
* `condExp_esPart` : `𝔼(f^{=S} | x_U) = f^{=S}` if `S ⊆ U`, and `0` otherwise;
* `sum_esPart` : `f = ∑_S f^{=S}`;
* `expect_esPart_mul_esPart` : the components are pairwise orthogonal;
* `noiseOp_eq` : `N_ρ f = ∑_S ρ^{|S|} f^{=S}`;
* `stab_eq` : `Stab_ρ(f) = ∑_S ρ^{|S|} ‖f^{=S}‖₂²`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (π : FinProb α)

/-! ### Two alternating-sum identities -/

/-- Sums over the supersets of `S` are sums over the subsets of its complement. -/
lemma sum_superset {M : Type*} [AddCommMonoid M] (S : Finset ι) (g : Finset ι → M) :
    ∑ T with S ⊆ T, g T = ∑ R ∈ Sᶜ.powerset, g (S ∪ R) := by
  refine sum_nbij' (fun T => T \ S) (fun R => S ∪ R) ?_ ?_ ?_ ?_ ?_
  · intro T _
    rw [mem_powerset]
    intro i hi
    rw [mem_compl]
    exact (mem_sdiff.1 hi).2
  · intro R _
    rw [mem_filter]
    exact ⟨mem_univ _, subset_union_left⟩
  · intro T hT
    exact union_sdiff_of_subset (mem_filter.1 hT).2
  · intro R hR
    rw [mem_powerset] at hR
    have hd : Disjoint S R := disjoint_left.2 fun i hS hRi => by simpa [hS] using hR hRi
    exact union_sdiff_cancel_left hd
  · intro T hT
    rw [union_sdiff_of_subset (mem_filter.1 hT).2]

lemma card_union_compl_part {S R : Finset ι} (hR : R ∈ Sᶜ.powerset) :
    (S ∪ R).card = S.card + R.card := by
  rw [card_union_of_disjoint]
  rw [mem_powerset] at hR
  exact disjoint_left.2 fun i hS hRi => by simpa [hS] using hR hRi

omit [Fintype ι] in
/-- `∑_{m ⊆ x} (-1)^{|m|} = [x = ∅]`, over `ℝ`. -/
lemma sum_powerset_neg_one_pow_card_real (x : Finset ι) :
    ∑ m ∈ x.powerset, (-1 : ℝ) ^ m.card = if x = ∅ then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := x))
  push_cast at h
  rw [h]

/-- `∑_{T ⊇ S} (-1)^{|T| - |S|} = [S = univ]`. -/
lemma sum_superset_neg_one_pow (S : Finset ι) :
    ∑ T with S ⊆ T, (-1 : ℝ) ^ (T.card - S.card) = if S = univ then 1 else 0 := by
  rw [sum_superset]
  have : ∀ R ∈ Sᶜ.powerset, (-1 : ℝ) ^ ((S ∪ R).card - S.card) = (-1) ^ R.card := by
    intro R hR; rw [card_union_compl_part hR]; simp
  rw [sum_congr rfl this, sum_powerset_neg_one_pow_card_real]
  simp [compl_eq_empty_iff]

/-- `∑_{T ⊇ S} ρ^{|T|} (1-ρ)^{|ι| - |T|} = ρ^{|S|}`. -/
lemma sum_superset_weight (S : Finset ι) (ρ : ℝ) :
    ∑ T with S ⊆ T, ρ ^ T.card * (1 - ρ) ^ (Fintype.card ι - T.card) = ρ ^ S.card := by
  rw [sum_superset]
  have hcompl : Sᶜ.card = Fintype.card ι - S.card := card_compl S
  have : ∀ R ∈ Sᶜ.powerset, ρ ^ (S ∪ R).card * (1 - ρ) ^ (Fintype.card ι - (S ∪ R).card) =
      ρ ^ S.card * (ρ ^ R.card * (1 - ρ) ^ (Sᶜ.card - R.card)) := by
    intro R hR
    rw [card_union_compl_part hR, hcompl, pow_add, Nat.sub_add_eq]
    ring
  rw [sum_congr rfl this, ← mul_sum, sum_pow_mul_eq_add_pow]
  simp

/-- `∑_{T ⊆ S} (-1)^{|S| - |T|} = [S = ∅]`. -/
lemma sum_powerset_neg_one_pow_sub (S : Finset ι) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) = if S = ∅ then 1 else 0 := by
  rw [← sum_powerset_neg_one_pow_card_real S]
  refine sum_nbij' (fun T => S \ T) (fun T => S \ T) ?_ ?_ ?_ ?_ ?_
  · intro T _; simp
  · intro T _; simp
  · intro T hT; rw [mem_powerset] at hT; exact Finset.sdiff_sdiff_eq_self hT
  · intro T hT; rw [mem_powerset] at hT; exact Finset.sdiff_sdiff_eq_self hT
  · intro T hT; rw [mem_powerset] at hT; rw [card_sdiff_of_subset hT]

/-! ### Conditional expectations -/

omit [DecidableEq α] in
lemma condExp_univ (f : (ι → α) → ℝ) (x : ι → α) : condExp π univ f x = f x := by
  simp [condExp]

omit [DecidableEq α] in
lemma condExp_empty (f : (ι → α) → ℝ) (x : ι → α) :
    condExp π ∅ f x = (π.pi ι).expect f := by
  simp [condExp]

omit [DecidableEq α] in
lemma condExp_condExp (T U : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) :
    condExp π T (condExp π U f) x = condExp π (T ∩ U) f x := by
  unfold condExp
  have key : ∀ y z : ι → α,
      U.piecewise (T.piecewise x y) z = (T ∩ U).piecewise x (U.piecewise y z) := by
    intro y z; ext i
    by_cases hU : i ∈ U <;> by_cases hT : i ∈ T <;> simp [hU, hT]
  simp only [key]
  exact π.expect_expect_piecewise U fun w => f ((T ∩ U).piecewise x w)

omit [DecidableEq α] in
lemma condExp_add (T : Finset ι) (f g : (ι → α) → ℝ) (x : ι → α) :
    condExp π T (fun y => f y + g y) x = condExp π T f x + condExp π T g x :=
  (π.pi ι).expect_add _ _

omit [DecidableEq α] in
lemma condExp_const_mul (T : Finset ι) (c : ℝ) (f : (ι → α) → ℝ) (x : ι → α) :
    condExp π T (fun y => c * f y) x = c * condExp π T f x :=
  (π.pi ι).expect_const_mul _ _

omit [DecidableEq α] in
lemma condExp_sum {β : Type*} (s : Finset β) (T : Finset ι) (f : β → (ι → α) → ℝ)
    (x : ι → α) : condExp π T (fun y => ∑ b ∈ s, f b y) x = ∑ b ∈ s, condExp π T (f b) x :=
  (π.pi ι).expect_sum _ _

omit [DecidableEq α] in
lemma condExp_const (T : Finset ι) (c : ℝ) (x : ι → α) : condExp π T (fun _ => c) x = c := by
  simp [condExp]

omit [DecidableEq α] in
/-- Conditional expectation is self-adjoint. -/
lemma expect_condExp_mul (T : Finset ι) (f g : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => condExp π T f x * g x) =
      (π.pi ι).expect (fun x => f x * condExp π T g x) := by
  unfold condExp
  simp only [← FinProb.expect_mul_const, ← FinProb.expect_const_mul]
  have := π.expect_expect_swap T fun x y => f (T.piecewise x y) * g x
  have hpw : ∀ x y : ι → α, T.piecewise (T.piecewise x y) (T.piecewise y x) = x := by
    intro x y; ext i; by_cases hi : i ∈ T <;> simp [hi]
  simp only [hpw] at this
  exact this.symm

/-! ### The Efron–Stein components -/

omit [DecidableEq α] in
lemma esPart_add (S : Finset ι) (f g : (ι → α) → ℝ) (x : ι → α) :
    esPart π S (fun y => f y + g y) x = esPart π S f x + esPart π S g x := by
  simp [esPart, condExp_add, mul_add, sum_add_distrib]

omit [DecidableEq α] in
lemma esPart_const_mul (S : Finset ι) (c : ℝ) (f : (ι → α) → ℝ) (x : ι → α) :
    esPart π S (fun y => c * f y) x = c * esPart π S f x := by
  simp [esPart, condExp_const_mul, mul_sum, mul_left_comm]

omit [DecidableEq α] in
lemma esPart_const (S : Finset ι) (c : ℝ) (x : ι → α) :
    esPart π S (fun _ => c) x = if S = ∅ then c else 0 := by
  simp only [esPart, condExp_const, ← sum_mul, sum_powerset_neg_one_pow_sub]
  split_ifs <;> simp

omit [DecidableEq α] in
lemma esPart_sub_const (S : Finset ι) (f : (ι → α) → ℝ) (c : ℝ) (x : ι → α) :
    esPart π S (fun y => f y - c) x = esPart π S f x - if S = ∅ then c else 0 := by
  have h1 := esPart_add π S f (fun _ => -c) x
  have h2 := esPart_const π S (-c) x
  simp only [← sub_eq_add_neg] at h1
  rw [h1, h2]
  split_ifs <;> ring

omit [DecidableEq α] in
lemma esPart_empty (f : (ι → α) → ℝ) (x : ι → α) : esPart π ∅ f x = (π.pi ι).expect f := by
  simp [esPart, condExp_empty]

omit [DecidableEq α] in
/-- `𝔼(f^{=S} | x_U) = f^{=S}` if `S ⊆ U`, and `0` otherwise. -/
lemma condExp_esPart (U S : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) :
    condExp π U (esPart π S f) x = if S ⊆ U then esPart π S f x else 0 := by
  have hexp : condExp π U (esPart π S f) x =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * condExp π (U ∩ T) f x := by
    unfold esPart
    rw [condExp_sum]
    refine sum_congr rfl fun T _ => ?_
    rw [condExp_const_mul, condExp_condExp]
  rw [hexp]
  split_ifs with hSU
  · refine sum_congr rfl fun T hT => ?_
    rw [inter_eq_right.2 ((mem_powerset.1 hT).trans hSU)]
  · obtain ⟨i, hiS, hiU⟩ := not_subset.1 hSU
    rw [← insert_erase hiS, sum_powerset_insert (notMem_erase i S)]
    rw [← sum_add_distrib]
    refine sum_eq_zero fun T hT => ?_
    have hiT : i ∉ T := fun h => by simpa using mem_powerset.1 hT h
    have hTc : T.card ≤ (S.erase i).card := card_le_card (mem_powerset.1 hT)
    rw [card_insert_of_notMem (notMem_erase i S), card_insert_of_notMem hiT]
    have hU : U ∩ insert i T = U ∩ T := by
      ext j; by_cases hj : j = i
      · subst hj; simp [hiU]
      · simp [hj]
    rw [hU, Nat.add_sub_add_right, show (S.erase i).card + 1 - T.card =
      (S.erase i).card - T.card + 1 by omega, pow_succ]
    ring

omit [DecidableEq α] in
/-- `f = ∑_S f^{=S}`. -/
lemma sum_esPart (f : (ι → α) → ℝ) (x : ι → α) : ∑ S : Finset ι, esPart π S f x = f x := by
  unfold esPart
  rw [sum_comm' (t' := univ) (s' := fun T => univ.filter (T ⊆ ·))
    (h := fun S T => by simp [mem_powerset])]
  simp only [← sum_mul]
  simp only [sum_superset_neg_one_pow, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
    ite_true]
  exact condExp_univ π f x

omit [DecidableEq α] in
/-- `𝔼(f | x_U) = ∑_{S ⊆ U} f^{=S}`. -/
lemma condExp_eq_sum_esPart (U : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) :
    condExp π U f x = ∑ S ∈ U.powerset, esPart π S f x := by
  have : condExp π U f x = condExp π U (fun y => ∑ S : Finset ι, esPart π S f y) x := by
    simp only [sum_esPart]
  rw [this, condExp_sum]
  simp only [condExp_esPart]
  rw [sum_ite, sum_const_zero, add_zero]
  refine sum_congr (ext fun S => by simp) fun _ _ => rfl

omit [DecidableEq α] in
/-- The Efron–Stein components are pairwise orthogonal. -/
lemma expect_esPart_mul_esPart {S S' : Finset ι} (h : S ≠ S') (f g : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => esPart π S f x * esPart π S' g x) = 0 := by
  wlog hS : ¬ S ⊆ S' generalizing S S' f g
  · have hS' : ¬ S' ⊆ S := fun h' => h (subset_antisymm (not_not.1 hS) h')
    rw [← this (Ne.symm h) g f hS']
    exact (π.pi ι).expect_congr fun x => mul_comm _ _
  obtain ⟨i, hiS, hiS'⟩ := not_subset.1 hS
  set U := univ.erase i
  have hS'U : S' ⊆ U := fun j hj => mem_erase.2 ⟨fun h => hiS' (h ▸ hj), mem_univ j⟩
  have hSU : ¬ S ⊆ U := fun h => by simpa [U] using h hiS
  have h1 : ∀ x, esPart π S' g x = condExp π U (esPart π S' g) x := fun x => by
    rw [condExp_esPart, ite_eq_left hS'U]
  simp only [h1]
  rw [← expect_condExp_mul]
  simp [condExp_esPart, hSU]

omit [DecidableEq α] in
/-- `⟨f, g^{=S}⟩ = ⟨f^{=S}, g^{=S}⟩`. -/
lemma expect_mul_esPart (S : Finset ι) (f g : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => f x * esPart π S g x) =
      (π.pi ι).expect (fun x => esPart π S f x * esPart π S g x) := by
  have : (π.pi ι).expect (fun x => f x * esPart π S g x) =
      (π.pi ι).expect (fun x => ∑ S' : Finset ι, esPart π S' f x * esPart π S g x) := by
    refine (π.pi ι).expect_congr fun x => ?_
    rw [← sum_mul, sum_esPart]
  rw [this, FinProb.expect_sum, sum_eq_single S]
  · intro S' _ hS'
    exact expect_esPart_mul_esPart π hS' f g
  · simp

omit [DecidableEq α] in
/-- Parseval for conditional expectations: `‖𝔼(f | x_U)‖₂² = ∑_{S ⊆ U} ‖f^{=S}‖₂²`. -/
lemma expect_condExp_sq (U : Finset ι) (f : (ι → α) → ℝ) :
    (π.pi ι).expect (fun x => condExp π U f x ^ 2) =
      ∑ S ∈ U.powerset, (π.pi ι).expect (fun x => esPart π S f x ^ 2) := by
  simp only [condExp_eq_sum_esPart, sq, sum_mul_sum, FinProb.expect_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [sum_eq_single S]
  · intro S' _ hS'
    exact expect_esPart_mul_esPart π (Ne.symm hS') f f
  · intro h; exact absurd hS h

/-! ### The noise operator and stability -/

/-- The one-coordinate kernel identity behind `noiseOp_eq_sum_condExp`. -/
lemma sum_prob_piecewise_eq (T : Finset ι) (x y : ι → α) :
    ∑ z : ι → α, (∏ i, π.prob (z i)) * (if T.piecewise x z = y then 1 else 0) =
      (∏ i ∈ T, if x i = y i then (1 : ℝ) else 0) * ∏ i ∈ univ \ T, π.prob (y i) := by
  have hind : ∀ z : ι → α, (if T.piecewise x z = y then (1 : ℝ) else 0) =
      ∏ i, if T.piecewise x z i = y i then (1 : ℝ) else 0 := by
    intro z
    by_cases h : T.piecewise x z = y
    · simp [h]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm
  have hz : ∀ z : ι → α, (∏ i, π.prob (z i)) * (if T.piecewise x z = y then 1 else 0) =
      ∏ i, (fun i a => π.prob a * if (if i ∈ T then x i else a) = y i then (1 : ℝ) else 0)
        i (z i) := by
    intro z
    rw [hind, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ T <;> simp [Finset.piecewise, hi]
  rw [sum_congr rfl fun z _ => hz z]
  refine ((Fintype.prod_sum (κ := fun _ : ι => α) fun i a =>
    π.prob a * if (if i ∈ T then x i else a) = y i then (1 : ℝ) else 0).symm).trans ?_
  rw [← prod_mul_prod_compl T, compl_eq_univ_sdiff]
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    simp only [hi, ite_true]
    rw [← sum_mul, π.sum_eq_one, one_mul]
  · refine prod_congr rfl fun i hi => ?_
    have hi' : i ∉ T := (mem_sdiff.1 hi).2
    simp [hi']

lemma noiseKernel_prod_expand (ρ : ℝ) (x y : ι → α) :
    ∏ i, noiseKernel π ρ (x i) (y i) =
      ∑ T : Finset ι, ρ ^ T.card * (1 - ρ) ^ (Fintype.card ι - T.card) *
        ((∏ i ∈ T, if x i = y i then (1 : ℝ) else 0) * ∏ i ∈ univ \ T, π.prob (y i)) := by
  unfold noiseKernel
  rw [prod_add]
  refine sum_congr (by simp) fun T _ => ?_
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, card_sdiff_of_subset
    (subset_univ T), card_univ]
  ring

lemma kernel_sum_eq_condExp (T : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) :
    ∑ y, ((∏ i ∈ T, if x i = y i then (1 : ℝ) else 0) * ∏ i ∈ univ \ T, π.prob (y i)) * f y =
      condExp π T f x := by
  simp only [← sum_prob_piecewise_eq, sum_mul]
  rw [sum_comm]
  unfold condExp FinProb.expect
  refine sum_congr rfl fun z _ => ?_
  simp only [FinProb.pi_prob, mul_assoc, ← mul_sum]
  congr 1
  simp [ite_mul]

/-- `N_ρ f = ∑_T ρ^{|T|} (1-ρ)^{|ι|-|T|} 𝔼(f | x_T)`. -/
lemma noiseOp_eq_sum_condExp (ρ : ℝ) (f : (ι → α) → ℝ) (x : ι → α) :
    noiseOp π ρ f x =
      ∑ T : Finset ι, ρ ^ T.card * (1 - ρ) ^ (Fintype.card ι - T.card) * condExp π T f x := by
  unfold noiseOp
  simp only [noiseKernel_prod_expand, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun T _ => ?_
  rw [← kernel_sum_eq_condExp π T f x, mul_sum]
  refine sum_congr rfl fun y _ => by ring

/-- `N_ρ f = ∑_S ρ^{|S|} f^{=S}`. -/
lemma noiseOp_eq (ρ : ℝ) (f : (ι → α) → ℝ) (x : ι → α) :
    noiseOp π ρ f x = ∑ S : Finset ι, ρ ^ S.card * esPart π S f x := by
  rw [noiseOp_eq_sum_condExp]
  simp only [condExp_eq_sum_esPart, mul_sum]
  rw [sum_comm' (t' := univ) (s' := fun S => univ.filter (S ⊆ ·))
    (h := fun T S => by simp [mem_powerset])]
  refine sum_congr rfl fun S _ => ?_
  rw [← sum_mul, sum_superset_weight]

/-- `Stab_ρ(f) = ∑_S ρ^{|S|} ‖f^{=S}‖₂²`. -/
lemma stab_eq (ρ : ℝ) (f : (ι → α) → ℝ) :
    stab π ρ f = ∑ S : Finset ι, ρ ^ S.card * (π.pi ι).expect (fun x => esPart π S f x ^ 2) := by
  unfold stab
  simp only [noiseOp_eq, mul_sum, FinProb.expect_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [show (fun x => f x * (ρ ^ S.card * esPart π S f x)) =
      fun x => ρ ^ S.card * (f x * esPart π S f x) from funext fun x => by ring,
    FinProb.expect_const_mul, expect_mul_esPart]
  simp [sq]

/-- Stability is nondecreasing in `ρ ∈ [0, 1]`. -/
lemma stab_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') (f : (ι → α) → ℝ) :
    stab π ρ f ≤ stab π ρ' f := by
  rw [stab_eq, stab_eq]
  refine sum_le_sum fun S _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ h0 h _) ((π.pi ι).expect_nonneg fun x => sq_nonneg _)

end RestrictedPolynomials

end
