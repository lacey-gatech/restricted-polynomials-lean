module

public import RestrictedPolynomials.Dimitrov.DubininDefs
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The zigzag path of Supplement C, Lemma 6.1 (`lem:paths`)

Source: Supplement C, Section 6 (Lemma `lem:paths`); the dips partition the *disjoint union* of the
deficit intervals.

For strictly monotone directions `θ` within one period we construct the zigzag data
`IsZigzag N θ ψ L`.

## Strategy

A path is encoded by a list of *vertex values* (`pathFn`, `pathVar`, `cnt`, `legsFrom`).
The counting part (`exists_pieces`) is a merging induction on the set of gaps: a small gap
`a_j < h` is merged into a big gap `a_k > h`, producing a gap `a_j + a_k - h` and the induction
hypothesis, then the old small gap gets a tent and the new path of the big gap gets one dip
covering the deficit interval `(a_j, h)` of `j`.  This realises the supplement's chunking of the
deficit intervals without partial sums.  The pieces of the gaps are then concatenated and
turned into the periodic function `ψ` and the list of legs.
-/

@[expose] public section

open scoped Real

noncomputable section

namespace RestrictedPolynomials

namespace ZigzagAux

/-! ## Vertex-list paths -/

/-- Sign of the step from `p` to `x`. -/
def sgn (p x : ℝ) : ℝ := if p ≤ x then 1 else -1

/-- The piecewise linear path through the vertices `p, x₁, x₂, …`, parametrised by time `s`
(slope `±1`, constant after the end). -/
def pathFn : ℝ → List ℝ → ℝ → ℝ
  | p, [], _ => p
  | p, x :: r, s => if s < |x - p| then p + sgn p x * s else pathFn x r (s - |x - p|)

/-- Total variation (= duration) of the path through `p, x₁, x₂, …`. -/
def pathVar : ℝ → List ℝ → ℝ
  | _, [] => 0
  | p, x :: r => |x - p| + pathVar x r

/-- The final vertex of the path through `p, x₁, x₂, …`. -/
def lastOf : ℝ → List ℝ → ℝ
  | p, [] => p
  | _, x :: r => lastOf x r

/-- Occupation count at level `φ`: the number of steps whose open range contains `φ`. -/
def cnt (φ : ℝ) : ℝ → List ℝ → ℕ
  | _, [] => 0
  | p, x :: r => Set.indicator (Set.Ioo (min p x) (max p x)) (fun _ => (1 : ℕ)) φ + cnt φ x r

/-- The legs of the path through `p, x₁, x₂, …` started at time `τ` (zero-length steps are
skipped). -/
def legsFrom : ℝ → ℝ → List ℝ → List Leg
  | _, _, [] => []
  | τ, p, x :: r =>
      (if p = x then [] else [⟨τ, τ + |x - p|, sgn p x, p⟩]) ++ legsFrom (τ + |x - p|) x r

theorem sgn_mul_abs (p x : ℝ) : sgn p x * |x - p| = x - p := by
  unfold sgn
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)]; ring
  · rw [abs_of_neg (by linarith)]; ring

theorem sgn_cases (p x : ℝ) : sgn p x = 1 ∨ sgn p x = -1 := by
  unfold sgn; split_ifs <;> simp

theorem abs_sgn (p x : ℝ) : |sgn p x| = 1 := by
  rcases sgn_cases p x with h | h <;> simp [h]

theorem pathFn_nil (p s : ℝ) : pathFn p [] s = p := rfl

theorem pathFn_zero (p : ℝ) (vs : List ℝ) : pathFn p vs 0 = p := by
  cases vs with
  | nil => rfl
  | cons x r =>
    simp only [pathFn]
    by_cases h : (0 : ℝ) < |x - p|
    · simp [h]
    · have : x = p := by
        have := abs_nonneg (x - p)
        have h0 : |x - p| = 0 := le_antisymm (not_lt.mp h) this
        linarith [abs_eq_zero.mp h0]
      subst this
      simp [pathFn_zero]

theorem pathVar_nonneg (p : ℝ) (vs : List ℝ) : 0 ≤ pathVar p vs := by
  induction vs generalizing p with
  | nil => simp [pathVar]
  | cons x r ih => simp only [pathVar]; exact add_nonneg (abs_nonneg _) (ih x)

/-- Gluing two 1-Lipschitz pieces. -/
theorem lip_glue {A B : ℝ → ℝ} (hA : ∀ s t, |A s - A t| ≤ |s - t|)
    (hB : ∀ s t, |B s - B t| ≤ |s - t|) {b : ℝ} (hb : A b = B 0) :
    ∀ s t, |(if s < b then A s else B (s - b)) - (if t < b then A t else B (t - b))| ≤ |s - t| := by
  intro s t
  by_cases hs : s < b <;> by_cases ht : t < b <;> simp only [hs, ht, ite_true, ite_false]
  · exact hA s t
  · have h1 := hA s b
    have h2 := hB 0 (t - b)
    rw [hb] at h1
    calc |A s - B (t - b)| = |(A s - B 0) + (B 0 - B (t - b))| := by ring_nf
      _ ≤ |A s - B 0| + |B 0 - B (t - b)| := abs_add_le _ _
      _ ≤ |s - b| + |0 - (t - b)| := add_le_add h1 h2
      _ = |s - t| := by
        rw [abs_of_neg (by linarith : s - b < 0), abs_of_nonpos (by linarith : 0 - (t - b) ≤ 0)]
        rw [abs_of_neg (by linarith : s - t < 0)]; ring
  · have h1 := hA t b
    have h2 := hB 0 (s - b)
    rw [hb] at h1
    calc |B (s - b) - A t| = |(B (s - b) - B 0) + (B 0 - A t)| := by ring_nf
      _ ≤ |B (s - b) - B 0| + |B 0 - A t| := abs_add_le _ _
      _ ≤ |s - b - 0| + |t - b| := by
          refine add_le_add (hB _ _) ?_
          rw [abs_sub_comm]; exact h1
      _ = |s - t| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ s - b - 0), abs_of_neg (by linarith : t - b < 0)]
        rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]; ring
  · have := hB (s - b) (t - b)
    simpa using this

theorem pathFn_lip (p : ℝ) (vs : List ℝ) : ∀ s t, |pathFn p vs s - pathFn p vs t| ≤ |s - t| := by
  induction vs generalizing p with
  | nil => intro s t; simp [pathFn_nil]
  | cons x r ih =>
    intro s t
    simp only [pathFn]
    refine lip_glue (A := fun s => p + sgn p x * s) (B := pathFn x r) ?_ (ih x) ?_ s t
    · intro s t
      have : p + sgn p x * s - (p + sgn p x * t) = sgn p x * (s - t) := by ring
      rw [this, abs_mul, abs_sgn, one_mul]
    · simp only [pathFn_zero]
      have := sgn_mul_abs p x
      linarith

theorem lastOf_append (p : ℝ) (u w : List ℝ) : lastOf p (u ++ w) = lastOf (lastOf p u) w := by
  induction u generalizing p with
  | nil => rfl
  | cons x r ih => simp only [List.cons_append, lastOf]; exact ih x

theorem pathVar_append (p : ℝ) (u w : List ℝ) :
    pathVar p (u ++ w) = pathVar p u + pathVar (lastOf p u) w := by
  induction u generalizing p with
  | nil => simp [pathVar, lastOf]
  | cons x r ih => simp only [List.cons_append, pathVar, lastOf, ih x]; ring

theorem cnt_append (φ p : ℝ) (u w : List ℝ) :
    cnt φ p (u ++ w) = cnt φ p u + cnt φ (lastOf p u) w := by
  induction u generalizing p with
  | nil => simp [cnt, lastOf]
  | cons x r ih => simp only [List.cons_append, cnt, lastOf, ih x]; ring

theorem pathFn_append (u w : List ℝ) : ∀ (p s : ℝ), pathVar p u ≤ s →
    pathFn p (u ++ w) s = pathFn (lastOf p u) w (s - pathVar p u) := by
  induction u with
  | nil => intro p s _; simp [pathVar, lastOf]
  | cons x r ih =>
    intro p s hs
    simp only [pathVar] at hs
    have hb : |x - p| ≤ s := le_trans (le_add_of_nonneg_right (pathVar_nonneg x r)) hs
    simp only [List.cons_append, pathFn, lastOf, pathVar, not_lt.mpr hb, ite_false]
    rw [ih x (s - |x - p|) (by linarith)]
    congr 1; ring

theorem pathFn_mem {h : ℝ} (p : ℝ) (vs : List ℝ) (hp : p ∈ Set.Icc 0 h)
    (hvs : ∀ x ∈ vs, x ∈ Set.Icc 0 h) {s : ℝ} (hs : 0 ≤ s) : pathFn p vs s ∈ Set.Icc 0 h := by
  induction vs generalizing p s with
  | nil => simpa [pathFn_nil] using hp
  | cons x r ih =>
    have hx := hvs x (by simp)
    simp only [pathFn]
    split_ifs with hlt
    · unfold sgn
      split_ifs with hpx
      · rw [abs_of_nonneg (by linarith)] at hlt
        constructor <;> nlinarith [hp.1, hp.2, hx.1, hx.2]
      · rw [abs_of_neg (by linarith)] at hlt
        constructor <;> nlinarith [hp.1, hp.2, hx.1, hx.2]
    · exact ih x hx (fun y hy => hvs y (by simp [hy])) (by linarith [not_lt.mp hlt])

/-! ## Legs of a vertex path -/

theorem legsFrom_head (vs : List ℝ) : ∀ (τ p : ℝ), ∀ l ∈ (legsFrom τ p vs).head?, l.lo = τ := by
  induction vs with
  | nil => intro τ p l hl; simp [legsFrom] at hl
  | cons x r ih =>
    intro τ p l hl
    by_cases hpx : p = x
    · subst hpx
      simp only [legsFrom, ite_true, List.nil_append, sub_self, abs_zero, add_zero] at hl
      exact ih τ p l hl
    · simp [legsFrom, hpx] at hl
      subst hl; rfl

theorem legsFrom_mem (vs : List ℝ) : ∀ (τ p : ℝ), ∀ l ∈ legsFrom τ p vs,
    τ ≤ l.lo ∧ l.hi ≤ τ + pathVar p vs ∧ l.lo < l.hi ∧ (l.sign = 1 ∨ l.sign = -1) := by
  induction vs with
  | nil => intro τ p l hl; simp [legsFrom] at hl
  | cons x r ih =>
    intro τ p l hl
    have hnn := abs_nonneg (x - p)
    by_cases hpx : p = x
    · subst hpx
      simp only [legsFrom, ite_true, List.nil_append, sub_self, abs_zero, add_zero] at hl
      have := ih τ p l hl
      simpa [pathVar] using this
    · have hpos : 0 < |x - p| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hpx))
      simp only [legsFrom, hpx, ite_false, List.cons_append, List.nil_append, List.mem_cons] at hl
      rcases hl with rfl | hl
      · refine ⟨le_rfl, ?_, by simp [hpos], sgn_cases p x⟩
        simp only [pathVar]
        linarith [pathVar_nonneg x r]
      · obtain ⟨h1, h2, h3, h4⟩ := ih (τ + |x - p|) x l hl
        refine ⟨by linarith, ?_, h3, h4⟩
        simp only [pathVar]; linarith

theorem legsFrom_psi (vs : List ℝ) : ∀ (τ p : ℝ), ∀ l ∈ legsFrom τ p vs,
    ∀ y ∈ Set.Icc l.lo l.hi, pathFn p vs (y - τ) = l.psi y := by
  induction vs with
  | nil => intro τ p l hl; simp [legsFrom] at hl
  | cons x r ih =>
    intro τ p l hl y hy
    by_cases hpx : p = x
    · subst hpx
      simp only [legsFrom, ite_true, List.nil_append, sub_self, abs_zero, add_zero] at hl
      have h1 := (legsFrom_mem r τ p l hl).1
      have := ih τ p l hl y hy
      have hy0 : ¬ (y - τ < 0) := by linarith [hy.1]
      simp only [pathFn, sub_self, abs_zero, hy0, ite_false, sub_zero]
      exact this
    · have hpos : 0 < |x - p| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hpx))
      simp only [legsFrom, hpx, ite_false, List.cons_append, List.nil_append, List.mem_cons] at hl
      rcases hl with rfl | hl
      · obtain ⟨hy1, hy2⟩ := hy
        simp only [Leg.psi] at hy1 hy2 ⊢
        simp only [pathFn]
        split_ifs with hlt
        · rfl
        · have hy' : y - τ = |x - p| := by linarith [not_lt.mp hlt]
          rw [hy', sub_self, pathFn_zero]
          have := sgn_mul_abs p x
          linarith
      · obtain ⟨hy1, hy2⟩ := hy
        obtain ⟨h1, h2, h3, h4⟩ := legsFrom_mem r (τ + |x - p|) x l hl
        have hy0 : ¬ (y - τ < |x - p|) := by linarith
        simp only [pathFn, hy0, ite_false]
        have := ih (τ + |x - p|) x l hl y ⟨hy1, hy2⟩
        rw [← this]; congr 1; ring

theorem legsFrom_chain (vs : List ℝ) : ∀ (τ p : ℝ),
    (legsFrom τ p vs).IsChain (fun a b => a.hi = b.lo) := by
  induction vs with
  | nil => intro τ p; simp [legsFrom]
  | cons x r ih =>
    intro τ p
    by_cases hpx : p = x
    · subst hpx
      simpa [legsFrom] using ih τ p
    · simp only [legsFrom, hpx, ite_false, List.cons_append, List.nil_append]
      cases hT : legsFrom (τ + |x - p|) x r with
      | nil => exact List.isChain_singleton _
      | cons l' T =>
        rw [List.isChain_cons_cons]
        refine ⟨?_, by rw [← hT]; exact ih _ _⟩
        have := legsFrom_head r (τ + |x - p|) x l' (by simp [hT])
        simpa using this.symm

theorem legsFrom_ne_nil (vs : List ℝ) : ∀ (τ p : ℝ), 0 < pathVar p vs → legsFrom τ p vs ≠ [] := by
  induction vs with
  | nil => intro τ p h; simp [pathVar] at h
  | cons x r ih =>
    intro τ p h
    by_cases hpx : p = x
    · subst hpx
      have h' : 0 < pathVar p r := by simpa [pathVar] using h
      simpa [legsFrom] using ih τ p h'
    · simp [legsFrom, hpx]

theorem legsFrom_getLast (vs : List ℝ) : ∀ (τ p : ℝ), ∀ l, (legsFrom τ p vs).getLast? = some l →
    l.hi = τ + pathVar p vs := by
  induction vs with
  | nil => intro τ p l hl; simp [legsFrom] at hl
  | cons x r ih =>
    intro τ p l hl
    by_cases hpx : p = x
    · subst hpx
      simp only [legsFrom, ite_true, List.nil_append, sub_self, abs_zero, add_zero] at hl
      have := ih τ p l hl
      simpa [pathVar] using this
    · simp only [legsFrom, hpx, ite_false, List.cons_append, List.nil_append] at hl
      cases hT : legsFrom (τ + |x - p|) x r with
      | nil =>
        rw [hT] at hl
        simp at hl
        subst hl
        have : pathVar x r = 0 := by
          by_contra hne
          exact legsFrom_ne_nil r _ _ (lt_of_le_of_ne (pathVar_nonneg x r) (Ne.symm hne)) hT
        simp [pathVar, this]
      | cons l1 T1 =>
        rw [hT] at hl
        have hl' : (legsFrom (τ + |x - p|) x r).getLast? = some l := by
          rw [hT]; simpa [List.getLast?_cons_cons] using hl
        have := ih _ _ l hl'
        simp only [pathVar]
        linarith

theorem legsFrom_count (φ : ℝ) (vs : List ℝ) : ∀ (τ p : ℝ),
    ((legsFrom τ p vs).map fun l => Set.indicator l.range (fun _ => (1 : ℕ)) φ).sum = cnt φ p vs := by
  induction vs with
  | nil => intro τ p; simp [legsFrom, cnt]
  | cons x r ih =>
    intro τ p
    by_cases hpx : p = x
    · subst hpx
      simp [legsFrom, cnt, ih]
    · simp only [legsFrom, hpx, ite_false, List.cons_append, List.nil_append, List.map_cons,
        List.sum_cons, cnt, ih]
      congr 2
      simp only [Leg.range, Leg.psi]
      have := sgn_mul_abs p x
      have e : p + sgn p x * (τ + |x - p| - τ) = x := by
        have : τ + |x - p| - τ = |x - p| := by ring
        rw [this]; linarith
      rw [e]

/-! ## Concatenation of pieces -/

/-- Every piece returns to level `0`. -/
def Good (P : List (List ℝ)) : Prop := ∀ u ∈ P, lastOf 0 u = 0

theorem lastOf_flatten {P : List (List ℝ)} (hP : Good P) : lastOf 0 P.flatten = 0 := by
  induction P with
  | nil => rfl
  | cons u P ih =>
    simp only [List.flatten_cons, lastOf_append]
    rw [hP u (by simp)]
    exact ih (fun v hv => hP v (by simp [hv]))

theorem pathVar_flatten {P : List (List ℝ)} (hP : Good P) :
    pathVar 0 P.flatten = (P.map (pathVar 0)).sum := by
  induction P with
  | nil => simp [pathVar]
  | cons u P ih =>
    simp only [List.flatten_cons, pathVar_append, List.map_cons, List.sum_cons]
    rw [hP u (by simp), ih (fun v hv => hP v (by simp [hv]))]

theorem cnt_flatten (φ : ℝ) {P : List (List ℝ)} (hP : Good P) :
    cnt φ 0 P.flatten = (P.map (cnt φ 0)).sum := by
  induction P with
  | nil => simp [cnt]
  | cons u P ih =>
    simp only [List.flatten_cons, cnt_append, List.map_cons, List.sum_cons]
    rw [hP u (by simp), ih (fun v hv => hP v (by simp [hv]))]

theorem pathFn_flatten_zero {P : List (List ℝ)} (hP : Good P) : ∀ i : ℕ,
    pathFn 0 P.flatten (((P.map (pathVar 0)).take i).sum) = 0 := by
  induction P with
  | nil => intro i; simp [pathFn_nil]
  | cons u P ih =>
    intro i
    cases i with
    | zero => simp [pathFn_zero]
    | succ i =>
      have hu := hP u (by simp)
      have hP' : Good P := fun v hv => hP v (by simp [hv])
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons, List.flatten_cons]
      have hS : 0 ≤ (((P.map (pathVar 0)).take i)).sum := by
        apply List.sum_nonneg
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hy)
        exact pathVar_nonneg _ _
      rw [pathFn_append u P.flatten 0 _ (by linarith), hu]
      have := ih hP' i
      convert this using 2
      ring

/-! ## The merging induction -/

theorem ind_of_le {φ p x : ℝ} (hpx : p ≤ x) :
    Set.indicator (Set.Ioo (min p x) (max p x)) (fun _ => (1 : ℕ)) φ =
      if p < φ ∧ φ < x then 1 else 0 := by
  rw [min_eq_left hpx, max_eq_right hpx, Set.indicator_apply]
  simp

theorem ind_of_ge {φ p x : ℝ} (hpx : x ≤ p) :
    Set.indicator (Set.Ioo (min p x) (max p x)) (fun _ => (1 : ℕ)) φ =
      if x < φ ∧ φ < p then 1 else 0 := by
  rw [min_eq_right hpx, max_eq_left hpx, Set.indicator_apply]
  simp

/-- The piece of a gap of half-length `a`: a path from `0` to `0` with values in `[0, h]`,
duration `2a`, whose first vertex is `min a h`. -/
def IsPiece (h a : ℝ) (u : List ℝ) : Prop :=
  ∃ v r, u = v :: r ∧ v = min a h ∧ (∀ x ∈ u, x ∈ Set.Icc 0 h) ∧ lastOf 0 u = 0 ∧
    pathVar 0 u = 2 * a

theorem exists_pieces {h : ℝ} (hh : 0 < h) : ∀ (n : ℕ) (s : Finset ℕ) (a : ℕ → ℝ),
    s.card = n → (∀ i ∈ s, 0 < a i) → ∑ i ∈ s, a i = n * h →
    ∃ W : ℕ → List ℝ, (∀ i ∈ s, IsPiece h (a i) (W i)) ∧
      ∀ φ ∈ Set.Ioo 0 h, (∀ i ∈ s, φ ∉ W i) → ∑ i ∈ s, cnt φ 0 (W i) = 2 * n := by
  intro n
  induction n with
  | zero =>
    intro s a hs _ _
    have : s = ∅ := Finset.card_eq_zero.mp hs
    subst this
    exact ⟨fun _ => [], by simp, by simp⟩
  | succ n ih =>
    intro s a hs hpos hsum
    by_cases hall : ∀ i ∈ s, a i = h
    · refine ⟨fun _ => [h, 0], ?_, ?_⟩
      · intro i hi
        have hai := hall i hi
        refine ⟨h, [0], rfl, by rw [hai, min_self], ?_, by simp [lastOf], ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ⟨hh.le, le_rfl⟩
          · exact ⟨le_rfl, hh.le⟩
        · simp only [pathVar, hai]
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          ring
      · intro φ hφ _
        have h1 : cnt φ 0 [h, 0] = 2 := by
          simp only [cnt]
          rw [ind_of_le hh.le, ind_of_ge hh.le]
          simp [hφ.1, hφ.2]
        simp [h1, hs, mul_comm]
    · push Not at hall
      obtain ⟨i0, hi0, hne⟩ := hall
      have hconst : ∑ i ∈ s, h = ((n + 1 : ℕ) : ℝ) * h := by
        rw [Finset.sum_const, hs]; simp
      have hj : ∃ j ∈ s, a j < h := by
        by_contra hcon
        push Not at hcon
        have : ∑ i ∈ s, h < ∑ i ∈ s, a i :=
          Finset.sum_lt_sum hcon ⟨i0, hi0, lt_of_le_of_ne (hcon i0 hi0) (Ne.symm hne)⟩
        push_cast at hconst hsum
        linarith
      have hk : ∃ k ∈ s, h < a k := by
        by_contra hcon
        push Not at hcon
        have : ∑ i ∈ s, a i < ∑ i ∈ s, h :=
          Finset.sum_lt_sum hcon ⟨i0, hi0, lt_of_le_of_ne (hcon i0 hi0) hne⟩
        push_cast at hconst hsum
        linarith
      obtain ⟨j, hjs, hjh⟩ := hj
      obtain ⟨k, hks, hkh⟩ := hk
      have hjk : j ≠ k := by rintro rfl; linarith
      have hkj : k ≠ j := Ne.symm hjk
      set s' := s.erase j with hs'
      have hks' : k ∈ s' := Finset.mem_erase.mpr ⟨hkj, hks⟩
      have hcard : s'.card = n := by
        rw [hs', Finset.card_erase_of_mem hjs, hs]; rfl
      set a' : ℕ → ℝ := Function.update a k (a j + a k - h) with ha'
      have hajpos := hpos j hjs
      have hakpos := hpos k hks
      have ha'k : a' k = a j + a k - h := by simp [ha']
      have ha'i : ∀ i, i ≠ k → a' i = a i := fun i hi => by simp [ha', hi]
      have hpos' : ∀ i ∈ s', 0 < a' i := by
        intro i hi
        by_cases hik : i = k
        · subst hik; rw [ha'k]; linarith
        · rw [ha'i i hik]; exact hpos i (Finset.mem_of_mem_erase hi)
      have hsum' : ∑ i ∈ s', a' i = n * h := by
        have e1 : ∑ i ∈ s, a i = a j + ∑ i ∈ s', a i := (Finset.add_sum_erase s a hjs).symm
        have e2 : ∑ i ∈ s', a i = a k + ∑ i ∈ s'.erase k, a i :=
          (Finset.add_sum_erase s' a hks').symm
        have e3 : ∑ i ∈ s', a' i = a' k + ∑ i ∈ s'.erase k, a' i :=
          (Finset.add_sum_erase s' a' hks').symm
        have e4 : ∑ i ∈ s'.erase k, a' i = ∑ i ∈ s'.erase k, a i :=
          Finset.sum_congr rfl (fun i hi => ha'i i (Finset.ne_of_mem_erase hi))
        push_cast at hsum
        rw [e3, e4, ha'k]
        linarith
      obtain ⟨W', hW'p, hW'c⟩ := ih s' a' hcard hpos' hsum'
      obtain ⟨v, r, hu, hv, hrange, hlast, hvar⟩ := hW'p k hks'
      rw [ha'k] at hv hvar
      have hvh : v ≤ h := (hrange v (by simp [hu])).2
      have hjv : a j < v := by rw [hv]; exact lt_min (by linarith) hjh
      refine ⟨fun i => if i = k then h :: a j :: W' k else if i = j then [a j, 0] else W' i,
        ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · subst hik
          simp only [ite_true]
          refine ⟨h, a j :: W' i, rfl, (min_eq_right hkh.le).symm, ?_, ?_, ?_⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | rfl | hx
            · exact ⟨hh.le, le_rfl⟩
            · exact ⟨hajpos.le, hjh.le⟩
            · exact hrange x hx
          · rw [hu] at hlast ⊢
            simpa [lastOf] using hlast
          · rw [hu] at hvar ⊢
            simp only [pathVar] at hvar ⊢
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ h - 0), abs_of_nonpos (by linarith : a j - h ≤ 0),
              abs_of_nonneg (by linarith : 0 ≤ v - a j)]
            rw [abs_of_nonneg (by linarith [(hrange v (by simp [hu])).1] : 0 ≤ v - 0)] at hvar
            linarith
        · by_cases hij : i = j
          · subst hij
            simp only [hik, ite_false, ite_true]
            refine ⟨a i, [0], rfl, (min_eq_left hjh.le).symm, ?_, by simp [lastOf], ?_⟩
            · intro x hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · exact ⟨hajpos.le, hjh.le⟩
              · exact ⟨le_rfl, hh.le⟩
            · simp only [pathVar]
              rw [abs_of_nonneg (by linarith : 0 ≤ a i - 0), abs_of_nonpos (by linarith : 0 - a i ≤ 0)]
              ring
          · simp only [hik, hij, ite_false]
            have := hW'p i (Finset.mem_erase.mpr ⟨hij, hi⟩)
            rwa [ha'i i hik] at this
      · intro φ hφ hnot
        have hφk := hnot k hks
        have hφj := hnot j hjs
        simp only [ite_true, hjk, hkj, ite_false, List.mem_cons, not_or] at hφk hφj
        obtain ⟨hφh, hφaj, hφW'k⟩ := hφk
        have hφv : φ ≠ v := by
          intro hc; apply hφW'k; rw [hu]; simp [hc]
        have hIH := hW'c φ hφ (by
          intro i hi
          by_cases hik : i = k
          · subst hik; exact hφW'k
          · have := hnot i (Finset.mem_of_mem_erase hi)
            simpa [hik, Finset.ne_of_mem_erase hi] using this)
        have e1 : ∑ i ∈ s, cnt φ 0 (if i = k then h :: a j :: W' k
            else if i = j then [a j, 0] else W' i) =
            cnt φ 0 [a j, 0] + (cnt φ 0 (h :: a j :: W' k) +
              ∑ i ∈ s'.erase k, cnt φ 0 (W' i)) := by
          rw [← Finset.add_sum_erase s _ hjs]
          rw [← Finset.add_sum_erase s' _ hks']
          simp only [hjk, hkj, ite_true, ite_false]
          congr 1
          refine congrArg _ (Finset.sum_congr rfl ?_)
          intro i hi
          have h1 := Finset.ne_of_mem_erase hi
          have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
          simp [h1, h2]
        have e2 : ∑ i ∈ s', cnt φ 0 (W' i) = cnt φ 0 (W' k) + ∑ i ∈ s'.erase k, cnt φ 0 (W' i) :=
          (Finset.add_sum_erase s' (fun i => cnt φ 0 (W' i)) hks').symm
        rw [e1]
        rw [e2] at hIH
        have hcore : cnt φ 0 [a j, 0] + cnt φ 0 (h :: a j :: W' k) = 2 + cnt φ 0 (W' k) := by
          rw [hu]
          simp only [cnt]
          rw [ind_of_le (φ := φ) (p := 0) (x := a j) hajpos.le,
            ind_of_ge (φ := φ) (p := a j) (x := 0) hajpos.le,
            ind_of_le (φ := φ) (p := 0) (x := h) hh.le,
            ind_of_ge (φ := φ) (p := h) (x := a j) hjh.le,
            ind_of_le (φ := φ) (p := a j) (x := v) hjv.le,
            ind_of_le (φ := φ) (p := 0) (x := v) (by linarith : (0:ℝ) ≤ v)]
          by_cases c1 : φ < a j
          · have c2 : φ < v := by linarith
            simp [c1, c2, hφ.1, hφ.2, not_lt.mpr c1.le]
          · have c1' : a j < φ := lt_of_le_of_ne (not_lt.mp c1) (Ne.symm hφaj)
            by_cases c2 : φ < v
            · simp [c1', c2, hφ.1, hφ.2, not_lt.mpr c1'.le]
              omega
            · have c2' : v < φ := lt_of_le_of_ne (not_lt.mp c2) (Ne.symm hφv)
              simp [c1', hφ.1, hφ.2, c1, c2]
              omega
        omega

/-! ## Periodic extension -/

theorem lip_periodic {F : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (t0 : ℝ)
    (hF : ∀ s t, |F s - F t| ≤ |s - t|) (h0 : F 0 = F P) (x y : ℝ) :
    |F (toIcoMod hP t0 x - t0) - F (toIcoMod hP t0 y - t0)| ≤ |x - y| := by
  have hx := self_sub_toIcoDiv_zsmul hP t0 x
  have hy := self_sub_toIcoDiv_zsmul hP t0 y
  have mx := toIcoMod_mem_Ico hP t0 x
  have my := toIcoMod_mem_Ico hP t0 y
  simp only [zsmul_eq_mul] at hx hy
  set nx := toIcoDiv hP t0 x
  set ny := toIcoDiv hP t0 y
  set x' := toIcoMod hP t0 x - t0 with hx'
  set y' := toIcoMod hP t0 y - t0 with hy'
  have hx0 : 0 ≤ x' := by simp only [hx']; linarith [mx.1]
  have hy0 : 0 ≤ y' := by simp only [hy']; linarith [my.1]
  have hxP : x' < P := by simp only [hx']; linarith [mx.2]
  have hyP : y' < P := by simp only [hy']; linarith [my.2]
  have hxy : x - y = x' - y' + ((nx - ny : ℤ) : ℝ) * P := by
    push_cast; simp only [hx', hy']; linarith
  have b0 := hF x' y'
  have b1 : |F x' - F y'| ≤ x' + (P - y') := by
    have e1 := hF x' 0
    have e2 := hF P y'
    rw [← h0] at e2
    calc |F x' - F y'| = |(F x' - F 0) + (F P - F y')| := by rw [← h0]; ring_nf
      _ ≤ |F x' - F 0| + |F P - F y'| := abs_add_le _ _
      _ ≤ |x' - 0| + |P - y'| := by rw [← h0] at *; exact add_le_add e1 (by simpa [← h0] using e2)
      _ = x' + (P - y') := by rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
  have b2 : |F x' - F y'| ≤ (P - x') + y' := by
    have e1 := hF x' P
    have e2 := hF 0 y'
    calc |F x' - F y'| = |(F x' - F P) + (F 0 - F y')| := by rw [← h0]; ring_nf
      _ ≤ |F x' - F P| + |F 0 - F y'| := abs_add_le _ _
      _ ≤ |x' - P| + |0 - y'| := add_le_add e1 e2
      _ = (P - x') + y' := by
        rw [abs_of_neg (by linarith), abs_of_nonpos (by linarith)]; ring
  rcases lt_trichotomy (nx - ny) 0 with hm | hm | hm
  · have hm' : ((nx - ny : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : nx - ny ≤ -1)
    have : y - x ≥ (P - x') + y' := by nlinarith
    rw [abs_sub_comm x y, abs_of_nonneg (show (0:ℝ) ≤ y - x by linarith)]
    linarith
  · rw [hm] at hxy
    simp only [Int.cast_zero, zero_mul, add_zero] at hxy
    rw [hxy]; exact b0
  · have hm' : (1 : ℝ) ≤ ((nx - ny : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ nx - ny)
    have : x - y ≥ x' + (P - y') := by nlinarith
    rw [abs_of_nonneg (show (0:ℝ) ≤ x - y by linarith)]
    linarith

theorem list_sum_range (f : ℕ → ℝ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem list_sum_range_nat (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem sum_take_range_map (f : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (((List.range N).map f).take k).sum = ∑ i ∈ Finset.range k, f i := by
  rw [← List.map_take, List.take_range, min_eq_left hk, list_sum_range]

end ZigzagAux

open ZigzagAux in
/-- [Supplement C, Lemma 6.1 (`lem:paths`), with the periodic gluing] For strictly monotone
directions within one period the zigzag data exists. -/
theorem exists_zigzag {N : ℕ} (hN : 1 ≤ N) (θ : Fin N → ℝ) (hθ : StrictMono θ)
    (hlt : ∀ j k, θ k < θ j + 2 * Real.pi) : ∃ (ψ : ℝ → ℝ) (L : List Leg), IsZigzag N θ ψ L := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hP : (0 : ℝ) < 2 * Real.pi := by positivity
  set h : ℝ := Real.pi / N with hhdef
  have hh : 0 < h := by positivity
  -- the extended direction sequence and the gaps
  let Θ : ℕ → ℝ := fun i => if hi : i < N then θ ⟨i, hi⟩ else θ ⟨0, hN⟩ + 2 * Real.pi
  let g : ℕ → ℝ := fun i => Θ (i + 1) - Θ i
  have hΘlt : ∀ i (hi : i < N), Θ i = θ ⟨i, hi⟩ := fun i hi => by simp [Θ, hi]
  have hΘN : Θ N = Θ 0 + 2 * Real.pi := by
    simp [Θ]
    omega
  have hgpos : ∀ i < N, 0 < g i := by
    intro i hi
    simp only [g]
    by_cases hi1 : i + 1 < N
    · rw [hΘlt i hi, hΘlt (i + 1) hi1]
      have : θ ⟨i, hi⟩ < θ ⟨i + 1, hi1⟩ := hθ (by simp [Fin.lt_def])
      linarith
    · have : i + 1 = N := by omega
      rw [this, hΘN, hΘlt i hi, hΘlt 0 (by omega)]
      have := hlt ⟨0, hN⟩ ⟨i, hi⟩
      linarith
  have hΘrange : ∀ k < N, Θ 0 ≤ Θ k ∧ Θ k < Θ 0 + 2 * Real.pi := by
    intro k hk
    rw [hΘlt k hk, hΘlt 0 (by omega)]
    refine ⟨?_, hlt ⟨0, hN⟩ ⟨k, hk⟩⟩
    exact hθ.monotone (by simp [Fin.le_def])
  have hgsum : ∀ k, ∑ i ∈ Finset.range k, g i = Θ k - Θ 0 :=
    fun k => Finset.sum_range_sub Θ k
  -- the pieces
  obtain ⟨W, hWp, hWc⟩ := exists_pieces hh N (Finset.range N) (fun i => g i / 2) (by simp)
    (fun i hi => by have := hgpos i (Finset.mem_range.mp hi); positivity)
    (by
      simp only [← Finset.sum_div, hgsum, hΘN]
      rw [hhdef]; field_simp; ring)
  have hWvar : ∀ i ∈ Finset.range N, pathVar 0 (W i) = g i := by
    intro i hi
    obtain ⟨v, r, _, _, _, _, hv⟩ := hWp i hi
    rw [hv]; ring
  let P : List (List ℝ) := (List.range N).map W
  have hGood : Good P := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    obtain ⟨v, r, _, _, _, hl, _⟩ := hWp i (Finset.mem_range.mpr (List.mem_range.mp hi))
    exact hl
  let vs : List ℝ := P.flatten
  have hvar : pathVar 0 vs = 2 * Real.pi := by
    have e1 : pathVar 0 vs = (P.map (pathVar 0)).sum := pathVar_flatten hGood
    have e2 : P.map (pathVar 0) = (List.range N).map (fun i => pathVar 0 (W i)) := by
      simp [P, List.map_map, Function.comp_def]
    rw [e1, e2, list_sum_range]
    rw [Finset.sum_congr rfl hWvar, hgsum, hΘN]; ring
  have hprefix : ∀ k ≤ N, pathFn 0 vs (Θ k - Θ 0) = 0 := by
    intro k hk
    have := pathFn_flatten_zero hGood k
    have e2 : P.map (pathVar 0) = (List.range N).map (fun i => pathVar 0 (W i)) := by
      simp [P, List.map_map, Function.comp_def]
    rw [e2, sum_take_range_map _ N k hk,
      Finset.sum_congr rfl (fun i hi => hWvar i (Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))), hgsum] at this
    exact this
  have hvsmem : ∀ x ∈ vs, x ∈ Set.Icc 0 h := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := List.mem_flatten.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    obtain ⟨v, r, _, _, hr, _, _⟩ := hWp i (Finset.mem_range.mpr (List.mem_range.mp hi))
    exact hr x hxu
  let t0 : ℝ := Θ 0
  let ψ : ℝ → ℝ := fun t => pathFn 0 vs (toIcoMod hP t0 t - t0)
  let L : List Leg := legsFrom t0 0 vs
  have hF0 : pathFn 0 vs 0 = 0 := pathFn_zero _ _
  have hFP : pathFn 0 vs (2 * Real.pi) = 0 := by
    have := hprefix N le_rfl
    rwa [hΘN, add_sub_cancel_left] at this
  have hlip : LipschitzWith 1 ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact lip_periodic hP t0 (pathFn_lip 0 vs) (by rw [hF0, hFP]) x y
  have hpsi_eq : ∀ x ∈ Set.Icc t0 (t0 + 2 * Real.pi), ψ x = pathFn 0 vs (x - t0) := by
    intro x hx
    rcases hx.2.eq_or_lt with hxe | hxlt
    · have : toIcoMod hP t0 x = t0 := by
        rw [hxe, toIcoMod_add_right]
        exact (toIcoMod_eq_self hP).mpr ⟨le_rfl, by linarith⟩
      show pathFn 0 vs (toIcoMod hP t0 x - t0) = pathFn 0 vs (x - t0)
      rw [this, sub_self, hxe, add_sub_cancel_left, hF0, hFP]
    · have : toIcoMod hP t0 x = x := (toIcoMod_eq_self hP).mpr ⟨hx.1, hxlt⟩
      simp only [ψ, this]
  have hLne : L ≠ [] := legsFrom_ne_nil vs t0 0 (by rw [hvar]; exact hP)
  refine ⟨ψ, L, hlip.continuous, ?_, hlip, ?_, ?_, ?_, legsFrom_chain vs t0 0, ?_, ?_⟩
  · intro t
    simp only [ψ, toIcoMod_add_right]
  · intro t
    refine pathFn_mem 0 vs ⟨le_rfl, hh.le⟩ hvsmem ?_
    have := toIcoMod_mem_Ico hP t0 t
    linarith [this.1]
  · intro k
    have hk := hΘrange k.val k.isLt
    have hθk : θ k = Θ k.val := by rw [hΘlt k.val k.isLt]
    have hmem : θ k ∈ Set.Ico t0 (t0 + 2 * Real.pi) := by rw [hθk]; exact hk
    have : toIcoMod hP t0 (θ k) = θ k := (toIcoMod_eq_self hP).mpr hmem
    show pathFn 0 vs (toIcoMod hP t0 (θ k) - t0) = 0
    rw [this, hθk]
    exact hprefix k.val k.isLt.le
  · intro l hl
    obtain ⟨h1, h2, h3, h4⟩ := legsFrom_mem vs t0 0 l hl
    refine ⟨h3, h4, fun y hy => ?_⟩
    rw [hvar] at h2
    rw [hpsi_eq y ⟨by linarith [hy.1], by linarith [hy.2]⟩]
    exact legsFrom_psi vs t0 0 l hl y hy
  · refine ⟨t0, ?_, ?_⟩
    · cases hL : L with
      | nil => exact absurd hL hLne
      | cons l T =>
        have := legsFrom_head vs t0 0 l (by change L.head? = some l; rw [hL]; rfl)
        simp [this]
    · cases hL : L.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hL) hLne
      | some l =>
        have := legsFrom_getLast vs t0 0 l hL
        simp [this, hvar]
  · refine ⟨vs.toFinset, fun φ hφ hφF => ?_⟩
    have hnot : ∀ i ∈ Finset.range N, φ ∉ W i := by
      intro i hi hmem
      apply hφF
      simp only [List.mem_toFinset]
      exact List.mem_flatten.mpr ⟨W i, List.mem_map.mpr ⟨i, List.mem_range.mpr
        (Finset.mem_range.mp hi), rfl⟩, hmem⟩
    have hcount := legsFrom_count φ vs t0 0
    change (L.map fun l => Set.indicator l.range (fun _ => (1 : ℕ)) φ).sum = 2 * N
    rw [hcount, cnt_flatten φ hGood]
    have e2 : P.map (cnt φ 0) = (List.range N).map (fun i => cnt φ 0 (W i)) := by
      simp [P, List.map_map, Function.comp_def]
    rw [e2, list_sum_range_nat]
    exact hWc φ hφ hnot

end RestrictedPolynomials
