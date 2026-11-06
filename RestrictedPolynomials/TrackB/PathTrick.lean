module

public import RestrictedPolynomials.FinProb
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# The path-trick walk (paper IV, Section 3)

Source: paper IV (`writeup_stability.tex`), L1740-1754 (path definition),
L1790-1796 (walk reversal and concatenation), L1907-1910 (constant word in the support).

Paper IV items: `definition-path-trick-walk`, `lem:reverse-embed` (step `constant-word-in-support`),
`lemma-path-definitions-agree` (step `walk-reversal-and-concatenation`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- `μ_Y(y)`, the `Γ`-marginal -/
def margY (μ : FinProb (X × Y × Z)) (y : Y) : ℝ := ∑ p with p.2.1 = y, μ.prob p
/-- `μ_Z(z)`, the `Φ`-marginal -/
def margZ (μ : FinProb (X × Y × Z)) (z : Z) : ℝ := ∑ p with p.2.2 = z, μ.prob p

/-- walk step `Γ → Φ` along an edge labelled `x`: weight `μ(x,y,z)/μ_Y(y)` -/
def stepYZ (μ : FinProb (X × Y × Z)) (x : X) : Matrix Y Z ℝ :=
  Matrix.of fun y z => μ.prob (x, y, z) / margY μ y
/-- walk step `Φ → Γ` along an edge labelled `x`: weight `μ(x,y,z)/μ_Z(z)` -/
def stepZY (μ : FinProb (X × Y × Z)) (x : X) : Matrix Z Y ℝ :=
  Matrix.of fun z y => μ.prob (x, y, z) / margZ μ z

/-- weight matrix of the odd-length walk `Γ → Φ` collecting labels `xs` (`ℓ` odd).
Off-domain values (wrong parity) of `walkYZ`/`walkYY` are junk and must not be used outside
parity hypotheses. -/
def walkYZ (μ : FinProb (X × Y × Z)) : List X → Matrix Y Z ℝ
  | [] => 0
  | [x] => stepYZ μ x
  | x₁ :: x₂ :: rest => (stepYZ μ x₁ * stepZY μ x₂) * walkYZ μ rest

/-- weight matrix of the even-length walk `Γ → Γ`.
Off-domain values (wrong parity) of `walkYZ`/`walkYY` are junk and must not be used outside
parity hypotheses. -/
def walkYY (μ : FinProb (X × Y × Z)) : List X → Matrix Y Y ℝ
  | x₁ :: x₂ :: rest => (stepYZ μ x₁ * stepZY μ x₂) * walkYY μ rest
  | _ => 1

/-- paper IV `definition-path-trick-walk`: unnormalised weight of `(x⃗, y, z)` under `μ_ℓ`.
Off-domain values (wrong parity) of `walkYZ`/`walkYY` are junk; use only under parity
hypotheses. -/
def pathWeight (μ : FinProb (X × Y × Z)) (ℓ : ℕ) (_hℓ : Odd ℓ) (w : Fin ℓ → X) (y : Y) (z : Z) :
    ℝ :=
  margY μ y * walkYZ μ (List.ofFn w) y z

/-! ### Auxiliary lemmas -/

lemma margY_nonneg (μ : FinProb (X × Y × Z)) (y : Y) : 0 ≤ margY μ y :=
  Finset.sum_nonneg fun p _ => μ.nonneg p

lemma margZ_nonneg (μ : FinProb (X × Y × Z)) (z : Z) : 0 ≤ margZ μ z :=
  Finset.sum_nonneg fun p _ => μ.nonneg p

lemma margY_eq_sum (μ : FinProb (X × Y × Z)) (y : Y) :
    margY μ y = ∑ x, ∑ z, μ.prob (x, y, z) := by
  unfold margY
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma margZ_eq_sum (μ : FinProb (X × Y × Z)) (z : Z) :
    margZ μ z = ∑ x, ∑ y, μ.prob (x, y, z) := by
  unfold margZ
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma sum_margY (μ : FinProb (X × Y × Z)) : ∑ y, margY μ y = 1 := by
  simp_rw [margY_eq_sum]
  rw [← μ.sum_eq_one, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

lemma prob_le_margY (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    μ.prob (x, y, z) ≤ margY μ y := by
  unfold margY
  exact Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p)
    (by simp : (x, y, z) ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.1 = y))

lemma prob_le_margZ (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    μ.prob (x, y, z) ≤ margZ μ z := by
  unfold margZ
  exact Finset.single_le_sum (f := μ.prob) (fun p _ => μ.nonneg p)
    (by simp : (x, y, z) ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.2 = z))

lemma stepYZ_nonneg (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    0 ≤ stepYZ μ x y z :=
  div_nonneg (μ.nonneg _) (margY_nonneg μ y)

lemma stepZY_nonneg (μ : FinProb (X × Y × Z)) (x : X) (z : Z) (y : Y) :
    0 ≤ stepZY μ x z y :=
  div_nonneg (μ.nonneg _) (margZ_nonneg μ z)

lemma stepYZ_pos (μ : FinProb (X × Y × Z)) {x : X} {y : Y} {z : Z} (h : μ.prob (x, y, z) ≠ 0) :
    0 < stepYZ μ x y z := by
  have h0 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)
  exact div_pos h0 (lt_of_lt_of_le h0 (prob_le_margY μ x y z))

lemma stepZY_pos (μ : FinProb (X × Y × Z)) {x : X} {y : Y} {z : Z} (h : μ.prob (x, y, z) ≠ 0) :
    0 < stepZY μ x z y := by
  have h0 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)
  exact div_pos h0 (lt_of_lt_of_le h0 (prob_le_margZ μ x y z))

lemma margY_mul_stepYZ (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    margY μ y * stepYZ μ x y z = μ.prob (x, y, z) := by
  simp only [stepYZ, Matrix.of_apply]
  by_cases h : margY μ y = 0
  · have := prob_le_margY μ x y z
    have h2 := μ.nonneg (x, y, z)
    rw [h] at this ⊢
    simp; linarith
  · field_simp

lemma margZ_mul_stepZY (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    margZ μ z * stepZY μ x z y = μ.prob (x, y, z) := by
  simp only [stepZY, Matrix.of_apply]
  by_cases h : margZ μ z = 0
  · have := prob_le_margZ μ x y z
    have h2 := μ.nonneg (x, y, z)
    rw [h] at this ⊢
    simp; linarith
  · field_simp

lemma walkYZ_nonneg (μ : FinProb (X × Y × Z)) :
    ∀ (xs : List X) (y : Y) (z : Z), 0 ≤ walkYZ μ xs y z
  | [], y, z => by simp [walkYZ]
  | [x], y, z => by simpa [walkYZ] using stepYZ_nonneg μ x y z
  | x₁ :: x₂ :: rest, y, z => by
    rw [walkYZ, Matrix.mul_apply]
    refine Finset.sum_nonneg fun y' _ => mul_nonneg ?_ (walkYZ_nonneg μ rest y' z)
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun z' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _)

lemma sum_stepYZ_mul (μ : FinProb (X × Y × Z)) (g : Z → ℝ)
    (hg : ∀ z, 0 < margZ μ z → g z = 1) (y : Y) :
    ∑ x, ∑ z, stepYZ μ x y z * g z = if 0 < margY μ y then 1 else 0 := by
  have hterm : ∀ x z, stepYZ μ x y z * g z = μ.prob (x, y, z) / margY μ y := by
    intro x z
    by_cases h : μ.prob (x, y, z) = 0
    · simp [stepYZ, h]
    · have h0 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)
      rw [hg z (lt_of_lt_of_le h0 (prob_le_margZ μ x y z)), mul_one]; rfl
  simp_rw [hterm]
  simp_rw [← Finset.sum_div]
  rw [← margY_eq_sum]
  by_cases h : 0 < margY μ y
  · rw [if_pos h, div_self h.ne']
  · rw [if_neg h, (le_antisymm (not_lt.mp h) (margY_nonneg μ y))]; simp

lemma sum_stepZY_mul (μ : FinProb (X × Y × Z)) (g : Y → ℝ)
    (hg : ∀ y, 0 < margY μ y → g y = 1) (z : Z) :
    ∑ x, ∑ y, stepZY μ x z y * g y = if 0 < margZ μ z then 1 else 0 := by
  have hterm : ∀ x y, stepZY μ x z y * g y = μ.prob (x, y, z) / margZ μ z := by
    intro x y
    by_cases h : μ.prob (x, y, z) = 0
    · simp [stepZY, h]
    · have h0 : 0 < μ.prob (x, y, z) := lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)
      rw [hg y (lt_of_lt_of_le h0 (prob_le_margY μ x y z)), mul_one]; rfl
  simp_rw [hterm]
  simp_rw [← Finset.sum_div]
  rw [← margZ_eq_sum]
  by_cases h : 0 < margZ μ z
  · rw [if_pos h, div_self h.ne']
  · rw [if_neg h, (le_antisymm (not_lt.mp h) (margZ_nonneg μ z))]; simp

lemma sum_fin_cons {n : ℕ} (F : (Fin (n + 1) → X) → ℝ) :
    ∑ w, F w = ∑ x, ∑ w' : Fin n → X, F (Fin.cons x w') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => X) (fun p => F (Fin.cons p.1 p.2)) F
    (fun p => rfl)).symm

/-- Row sums of the odd-length walks. -/
lemma sum_walkYZ_row (μ : FinProb (X × Y × Z)) (m : ℕ) (y : Y) :
    ∑ w : Fin (2 * m + 1) → X, ∑ z, walkYZ μ (List.ofFn w) y z =
      if 0 < margY μ y then 1 else 0 := by
  induction m generalizing y with
  | zero =>
    change ∑ w : Fin 1 → X, ∑ z, walkYZ μ (List.ofFn w) y z = _
    have : ∀ w : Fin 1 → X, ∑ z, walkYZ μ (List.ofFn w) y z =
        ∑ z, stepYZ μ (w 0) y z * 1 := by
      intro w
      simp [List.ofFn_succ, walkYZ]
    simp_rw [this]
    rw [← sum_stepYZ_mul μ (fun _ => 1) (fun _ _ => rfl) y]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun w => by simp)
  | succ m ih =>
    change ∑ w : Fin (2 * m + 1 + 1 + 1) → X, ∑ z, walkYZ μ (List.ofFn w) y z = _
    rw [sum_fin_cons]
    have key : ∀ x₁ x₂ : X, ∑ w' : Fin (2 * m + 1) → X,
        ∑ z, walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') :
          Fin (2 * m + 1 + 1 + 1) → X)) y z =
        ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * (if 0 < margY μ y' then 1 else 0) := by
      intro x₁ x₂
      have h1 : ∀ (w' : Fin (2 * m + 1) → X) (z : Z),
          walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') : Fin (2 * m + 1 + 1 + 1) → X)) y z =
          ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' * walkYZ μ (List.ofFn w') y' z := by
        intro w' z
        rw [List.ofFn_succ, List.ofFn_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [walkYZ, Matrix.mul_apply]
      simp_rw [h1]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Z))]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      rw [ih y']
    have h2 : ∀ x₁ : X, (∑ w'' : Fin (2 * m + 1 + 1) → X,
        ∑ z, walkYZ μ (List.ofFn (Fin.cons x₁ w'' : Fin (2 * m + 1 + 1 + 1) → X)) y z) =
        ∑ x₂, ∑ w' : Fin (2 * m + 1) → X,
        ∑ z, walkYZ μ (List.ofFn (Fin.cons x₁ (Fin.cons x₂ w') :
          Fin (2 * m + 1 + 1 + 1) → X)) y z := fun x₁ =>
      sum_fin_cons (n := 2 * m + 1) (fun w'' => ∑ z, walkYZ μ
        (List.ofFn (Fin.cons x₁ w'' : Fin (2 * m + 1 + 1 + 1) → X)) y z)
    rw [Finset.sum_congr rfl (fun x₁ _ => h2 x₁)]
    simp_rw [key]
    have e : ∀ x₁ x₂ : X, ∑ y', (stepYZ μ x₁ * stepZY μ x₂) y y' *
        (if 0 < margY μ y' then (1 : ℝ) else 0) =
        ∑ z', stepYZ μ x₁ y z' *
          ∑ y', stepZY μ x₂ z' y' * (if 0 < margY μ y' then (1 : ℝ) else 0) := by
      intro x₁ x₂
      simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    simp_rw [e]
    have e2 : ∀ x₁ : X, ∑ x₂, ∑ z', stepYZ μ x₁ y z' * ∑ y', stepZY μ x₂ z' y' *
        (if 0 < margY μ y' then (1 : ℝ) else 0) =
        ∑ z', stepYZ μ x₁ y z' * (if 0 < margZ μ z' then (1 : ℝ) else 0) := by
      intro x₁
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [← Finset.mul_sum, ← sum_stepZY_mul μ (fun y' => if 0 < margY μ y' then (1 : ℝ) else 0)
        (fun y' h => if_pos h) z']
    simp_rw [e2]
    exact sum_stepYZ_mul μ (fun z' => if 0 < margZ μ z' then (1 : ℝ) else 0)
      (fun z' h => if_pos h) y

lemma walkYZ_replicate_pos (μ : FinProb (X × Y × Z)) (x : X) (m : ℕ) :
    ∀ (y : Y) (z : Z), μ.prob (x, y, z) ≠ 0 → 0 < walkYZ μ (List.replicate (2 * m + 1) x) y z := by
  induction m with
  | zero =>
    intro y z h
    simpa [walkYZ] using stepYZ_pos μ h
  | succ m ih =>
    intro y z h
    have e : List.replicate (2 * (m + 1) + 1) x = x :: x :: List.replicate (2 * m + 1) x := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring]
      rfl
    rw [e, walkYZ, Matrix.mul_apply]
    have hnn : ∀ y', 0 ≤ (stepYZ μ x * stepZY μ x) y y' *
        walkYZ μ (List.replicate (2 * m + 1) x) y' z := fun y' => by
      refine mul_nonneg ?_ (walkYZ_nonneg μ _ _ _)
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun z' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun y' _ => hnn y') (Finset.mem_univ y))
    refine mul_pos ?_ (ih y z h)
    rw [Matrix.mul_apply]
    exact lt_of_lt_of_le (mul_pos (stepYZ_pos μ h) (stepZY_pos μ h))
      (Finset.single_le_sum (f := fun z' => stepYZ μ x y z' * stepZY μ x z' y)
        (fun z' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _))
        (Finset.mem_univ z))

/-- normalisation of `pathWeight` (the bundled `FinProb` is then `pathTrick μ ℓ hℓ`) -/
theorem sum_pathWeight (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) :
    ∑ q : (Fin ℓ → X) × Y × Z, pathWeight μ ℓ hℓ q.1 q.2.1 q.2.2 = 1 := by
  obtain ⟨m, rfl⟩ := hℓ
  simp_rw [Fintype.sum_prod_type, pathWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_walkYZ_row]
  refine Eq.trans (Finset.sum_congr rfl fun y _ => ?_) (sum_margY μ)
  by_cases h : 0 < margY μ y
  · simp [h]
  · have : margY μ y = 0 := le_antisymm (not_lt.mp h) (margY_nonneg μ y)
    simp [this]

/-- paper IV `lem:reverse-embed`, step `constant-word-in-support` -/
theorem const_word_mem_pathWeight_pos (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    {x : X} {y : Y} {z : Z} (h : μ.prob (x, y, z) ≠ 0) :
    0 < pathWeight μ ℓ hℓ (fun _ => x) y z := by
  have hy : 0 < margY μ y :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm h)) (prob_le_margY μ x y z)
  unfold pathWeight
  refine mul_pos hy ?_
  rw [List.ofFn_const]
  obtain ⟨m, rfl⟩ := hℓ
  exact walkYZ_replicate_pos μ x m y z h

/-- paper IV `lemma-path-definitions-agree`, step `walk-reversal-and-concatenation` (concatenation, `Γ → Γ`) -/
theorem walkYY_append (μ : FinProb (X × Y × Z)) (xs ys : List X) (hxs : Even xs.length)
    (hys : Even ys.length) :
    walkYY μ (xs ++ ys) = walkYY μ xs * walkYY μ ys := by
  obtain ⟨n, hn⟩ := hxs
  induction n generalizing xs with
  | zero =>
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [walkYY]
  | succ n ih =>
    match xs, hn with
    | x₁ :: x₂ :: rest, hn =>
      have h := ih rest (by simp at hn; omega)
      rw [List.cons_append, List.cons_append]
      simp only [walkYY]
      rw [h]
      simp only [Matrix.mul_assoc]
    | [_], hn => exact absurd hn (by simp <;> omega)

/-- paper IV `lemma-path-definitions-agree`, step `walk-reversal-and-concatenation` (concatenation, `Γ → Φ`) -/
theorem walkYZ_append (μ : FinProb (X × Y × Z)) (xs ys : List X) (hxs : Even xs.length)
    (hys : Odd ys.length) : walkYZ μ (xs ++ ys) = walkYY μ xs * walkYZ μ ys := by
  obtain ⟨n, hn⟩ := hxs
  induction n generalizing xs with
  | zero =>
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [walkYY]
  | succ n ih =>
    match xs, hn with
    | x₁ :: x₂ :: rest, hn =>
      have h := ih rest (by simp at hn; omega)
      rw [List.cons_append, List.cons_append]
      simp only [walkYY, walkYZ]
      rw [h]
      simp only [Matrix.mul_assoc]
    | [_], hn => exact absurd hn (by simp <;> omega)

lemma detailed_balance_step (μ : FinProb (X × Y × Z)) (x₁ x₂ : X) (y y' : Y) :
    margY μ y * (stepYZ μ x₁ * stepZY μ x₂) y y' =
      margY μ y' * (stepYZ μ x₂ * stepZY μ x₁) y' y := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← mul_assoc, ← mul_assoc, margY_mul_stepYZ, margY_mul_stepYZ]
  simp only [stepZY, Matrix.of_apply]
  ring

/-- paper IV `lemma-path-definitions-agree`, step `walk-reversal-and-concatenation` (reversal) -/
theorem walkYY_reverse (μ : FinProb (X × Y × Z)) (xs : List X) (hxs : Even xs.length)
    (y y' : Y) :
    margY μ y * walkYY μ xs y y' = margY μ y' * walkYY μ xs.reverse y' y := by
  obtain ⟨n, hn⟩ := hxs
  induction n generalizing xs y y' with
  | zero =>
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    by_cases h : y = y'
    · subst h; simp [walkYY]
    · simp [walkYY, Matrix.one_apply, h, Ne.symm h]
  | succ n ih =>
    match xs, hn with
    | [_], hn => exact absurd hn (by simp <;> omega)
    | x₁ :: x₂ :: rest, hn =>
      have hlen : rest.length = n + n := by simp at hn; omega
      have hrev : (x₁ :: x₂ :: rest).reverse = rest.reverse ++ [x₂, x₁] := by simp
      have hM : walkYY μ [x₂, x₁] = stepYZ μ x₂ * stepZY μ x₁ := by simp [walkYY]
      rw [hrev, walkYY_append μ _ _ ⟨n, by simp [hlen]⟩ ⟨1, rfl⟩, hM]
      simp only [walkYY]
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
      calc ∑ y'', margY μ y * ((stepYZ μ x₁ * stepZY μ x₂) y y'' * walkYY μ rest y'' y')
          = ∑ y'', (stepYZ μ x₂ * stepZY μ x₁) y'' y * (margY μ y'' * walkYY μ rest y'' y') := by
            refine Finset.sum_congr rfl fun y'' _ => ?_
            rw [← mul_assoc, detailed_balance_step]; ring
        _ = ∑ y'', margY μ y' * (walkYY μ rest.reverse y' y'' *
              (stepYZ μ x₂ * stepZY μ x₁) y'' y) := by
            refine Finset.sum_congr rfl fun y'' _ => ?_
            rw [ih rest y'' y' hlen]; ring

end TrackB
end RestrictedPolynomials
end
