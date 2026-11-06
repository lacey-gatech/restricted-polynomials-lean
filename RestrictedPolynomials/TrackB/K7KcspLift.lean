module

public import RestrictedPolynomials.TrackB.MergeLayer
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.FinProbSupport
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Defs

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Lift
variable {A : Type} [Fintype A] [DecidableEq A] {Y Z : Type} [Fintype Y] [Fintype Z]
  [DecidableEq Y] [DecidableEq Z]

/-- the lifted alphabet `Ã = Σ a, Fin (n a) = {(a, j) : j < n_a}` of Supplement H, Def. `def:lift`
(`|Ã| = M = Σ n_a`). -/
abbrev K7Lift (n : A → ℕ) : Type := Σ a : A, Fin (n a)

/-- the projection `q (a, j) = a`. -/
def k7LiftProj (n : A → ℕ) : K7Lift n → A := fun p => p.1

/-- the lift `ξ̃((a, j), y, z) = ξ(a, y, z) / n_a` of a triple law (Def. `def:lift`; `n_a ≥ 1`
makes it a law; the mass proof is complete). -/
def k7LiftFirst (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ : FinProb (A × Y × Z)) :
    FinProb (K7Lift n × Y × Z) where
  prob p := ξ.prob (p.1.1, p.2.1, p.2.2) / n p.1.1
  nonneg p := div_nonneg (ξ.nonneg _) (Nat.cast_nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Fintype.sum_sigma]
    have : ∀ a : A, ∑ j : Fin (n a), ∑ y : Y, ∑ z : Z, ξ.prob (a, y, z) / (n a : ℝ) =
        ∑ y : Y, ∑ z : Z, ξ.prob (a, y, z) := by
      intro a
      have hna : (n a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hn1 a; omega)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [← Finset.sum_div]
      field_simp
    simp only [this]
    rw [← ξ.sum_eq_one, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq Y] [DecidableEq Z] in
/-- characterisation of the data `k7LiftFirst`. -/
theorem k7LiftFirst_prob (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ : FinProb (A × Y × Z))
    (p : K7Lift n × Y × Z) :
    (k7LiftFirst n hn1 ξ).prob p = ξ.prob (p.1.1, p.2.1, p.2.2) / n p.1.1 :=
  rfl

private theorem k7lift_finProb_ext {α : Type} [Fintype α] (π ρ : FinProb α)
    (h : ∀ a, π.prob a = ρ.prob a) : π = ρ := by
  cases π; cases ρ
  simp only [FinProb.mk.injEq]
  exact funext h

omit [DecidableEq A] in
private theorem k7lift_sum_eq (π : FinProb A) (M : ℕ) (n : A → ℕ)
    (hπ : ∀ a, π.prob a = (n a : ℝ) / M) : (M : ℝ) ≠ 0 ∧ ∑ a, n a = M := by
  have h1 := π.sum_eq_one
  simp_rw [hπ] at h1
  rw [← Finset.sum_div] at h1
  have hM : (M : ℝ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h1
    exact zero_ne_one h1
  refine ⟨hM, ?_⟩
  rw [div_eq_one_iff_eq hM] at h1
  exact_mod_cast h1

omit [DecidableEq A] in
/-- `lem:rat-basic`: under `Rat(π, α)` with data `(M, n)`: `Σ n_a = M`, `|A| ≤ M ≤ 1/α`, `1/n_a ≥ α`,
`π(a) ≥ α`. -/
theorem k7_rat_basic {α : ℝ} (hα : 0 < α) (π : FinProb A) (M : ℕ) (n : A → ℕ)
    (hn : ∀ a, 1 ≤ n a ∧ n a ≤ M) (hM : (M : ℝ) ≤ 1 / α)
    (hπ : ∀ a, π.prob a = (n a : ℝ) / M) :
    ∑ a, n a = M ∧ Fintype.card A ≤ M ∧ (∀ a, α ≤ 1 / (n a : ℝ)) ∧ ∀ a, α ≤ π.prob a := by
  obtain ⟨hM0, hsum⟩ := k7lift_sum_eq π M n hπ
  have hMpos : (0 : ℝ) < M := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hM0)
  have hαM : α * M ≤ 1 := by
    rw [le_div_iff₀ hα] at hM
    linarith
  refine ⟨hsum, ?_, ?_, ?_⟩
  · calc Fintype.card A = ∑ _a : A, 1 := by simp
      _ ≤ ∑ a, n a := Finset.sum_le_sum fun a _ => (hn a).1
      _ = M := hsum
  · intro a
    have hna : (1 : ℝ) ≤ n a := by exact_mod_cast (hn a).1
    have hna' : (n a : ℝ) ≤ M := by exact_mod_cast (hn a).2
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · intro a
    have hna : (1 : ℝ) ≤ n a := by exact_mod_cast (hn a).1
    rw [hπ a, le_div_iff₀ hMpos]
    nlinarith

omit [DecidableEq A] in
/-- `|Ã| = Σ n_a`. -/
theorem k7_lift_card (n : A → ℕ) : Fintype.card (K7Lift n) = ∑ a, n a := by
  simp [Fintype.card_sigma]

omit [Fintype A] [DecidableEq A] in
/-- `Ã` is nonempty when `A` is and every `n_a ≥ 1` (needed to speak of `FinProb.uniform` on `Ã`). -/
theorem k7_lift_nonempty [Nonempty A] (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) : Nonempty (K7Lift n) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨⟨a, ⟨0, hn1 a⟩⟩⟩

/-- `lem:pushU`, first half: `q_* Ũ = π` exactly (the only place where rationality is used). -/
theorem k7_lift_pushU (π : FinProb A) (M : ℕ) (n : A → ℕ) (hn : ∀ a, 1 ≤ n a ∧ n a ≤ M)
    (hπ : ∀ a, π.prob a = (n a : ℝ) / M) [Nonempty (K7Lift n)] (a : A) :
    (mergePush (FinProb.uniform (α := K7Lift n)) (k7LiftProj n)).prob a = π.prob a := by
  obtain ⟨hM0, hsum⟩ := k7lift_sum_eq π M n hπ
  have hcard : (Fintype.card (K7Lift n) : ℝ) = M := by
    rw [k7_lift_card]; exact_mod_cast hsum
  have hu : ∀ p : K7Lift n, (FinProb.uniform (α := K7Lift n)).prob p =
      1 / (Fintype.card (K7Lift n) : ℝ) := fun p => rfl
  have hc : (Finset.univ.filter fun p : K7Lift n => k7LiftProj n p = a).card = n a := by
    rw [Finset.card_filter, Fintype.sum_sigma]
    have : ∀ x : A, (∑ _y : Fin (n x), if k7LiftProj n ⟨x, _y⟩ = a then 1 else 0) =
        if x = a then n x else 0 := by
      intro x
      by_cases hx : x = a <;> simp [k7LiftProj, hx]
    simp_rw [this]
    simp
  show ∑ p ∈ Finset.univ.filter (fun p : K7Lift n => k7LiftProj n p = a),
    (FinProb.uniform (α := K7Lift n)).prob p = _
  simp only [hu]
  rw [Finset.sum_const, hc, nsmul_eq_mul, hcard, hπ a]
  ring

omit [DecidableEq A] [DecidableEq Y] [DecidableEq Z] in
private theorem k7lift_fst_prob {B : Type} [Fintype B] [DecidableEq B] (ξ : FinProb (B × Y × Z))
    (b : B) : (mergePush ξ fun p => p.1).prob b = ∑ y : Y, ∑ z : Z, ξ.prob (b, y, z) := by
  show ∑ p ∈ Finset.univ.filter (fun p : B × Y × Z => p.1 = b), ξ.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- `lem:pushU`, second half: if `ξ₁ = π` then `ξ̃₁ = Ũ` exactly. -/
theorem k7_lift_first_marginal (π : FinProb A) (M : ℕ) (n : A → ℕ) (hn : ∀ a, 1 ≤ n a ∧ n a ≤ M)
    (hπ : ∀ a, π.prob a = (n a : ℝ) / M) (ξ : FinProb (A × Y × Z))
    (hξ : ∀ a, (mergePush ξ fun p => p.1).prob a = π.prob a) [Nonempty (K7Lift n)]
    (ã : K7Lift n) :
    (mergePush (k7LiftFirst n (fun a => (hn a).1) ξ) fun p => p.1).prob ã =
      (FinProb.uniform (α := K7Lift n)).prob ã := by
  obtain ⟨hM0, hsum⟩ := k7lift_sum_eq π M n hπ
  have hcard : (Fintype.card (K7Lift n) : ℝ) = M := by
    rw [k7_lift_card]; exact_mod_cast hsum
  have hu : (FinProb.uniform (α := K7Lift n)).prob ã =
      1 / (Fintype.card (K7Lift n) : ℝ) := rfl
  have h1 := hξ ã.1
  rw [k7lift_fst_prob, hπ] at h1
  rw [k7lift_fst_prob, hu, hcard]
  have hna : (n ã.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (hn ã.1).1; omega)
  simp only [k7LiftFirst_prob]
  simp_rw [← Finset.sum_div]
  rw [h1]
  field_simp

/-- `lem:lift` (a), law form: `(q × id × id)_* ξ̃ = ξ`. -/
theorem k7_lift_first_push (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ : FinProb (A × Y × Z))
    (p : A × Y × Z) :
    (mergePush (k7LiftFirst n hn1 ξ) fun p : K7Lift n × Y × Z => (p.1.1, p.2.1, p.2.2)).prob p =
      ξ.prob p := by
  obtain ⟨a, y, z⟩ := p
  show ∑ p' ∈ Finset.univ.filter
      (fun p' : K7Lift n × Y × Z => (p'.1.1, p'.2.1, p'.2.2) = (a, y, z)),
    (k7LiftFirst n hn1 ξ).prob p' = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_sigma]
  simp_rw [Fintype.sum_prod_type]
  have hna : (n a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hn1 a; omega)
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
  simp only [true_and]
  simp only [ite_and]
  have key : ∀ x : Fin (n a), (∑ x1 : Y, ∑ x2 : Z, if x1 = y then (if x2 = z then
      (k7LiftFirst n hn1 ξ).prob (⟨a, x⟩, x1, x2) else 0) else 0) =
      ξ.prob (a, y, z) / n a := by
    intro x
    rw [Finset.sum_eq_single y (fun x1 _ hx1 => by simp [hx1]) (by simp)]
    simp only [ite_true]
    rw [Finset.sum_eq_single z (fun x1 _ hx1 => by simp [hx1]) (by simp)]
    simp [k7LiftFirst]
  simp_rw [key]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [DecidableEq A] [DecidableEq Y] [DecidableEq Z] in
private theorem k7lift_pushforward_pi {B C : Type} [Fintype B] [Fintype C] [DecidableEq C]
    (π : FinProb B) (F : B → C) {κ : Type} [Fintype κ] [DecidableEq κ] (Φ : (κ → C) → ℂ) :
    ((π.pi κ).cexpect fun w => Φ fun t => F (w t)) =
      (((mergePush π F).pi κ).cexpect Φ) := by
  unfold FinProb.cexpect
  rw [← Finset.sum_fiberwise Finset.univ (fun w : κ → B => fun t => F (w t))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∀ w ∈ Finset.univ.filter (fun w : κ → B => (fun t => F (w t)) = u),
      ((π.pi κ).prob w : ℂ) * Φ (fun t => F (w t)) = ((π.pi κ).prob w : ℂ) * Φ u := by
    intro w hw
    rw [(Finset.mem_filter.1 hw).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  have hfib : (Finset.univ.filter fun w : κ → B => (fun t => F (w t)) = u) =
      Fintype.piFinset fun t => Finset.univ.filter fun b => F b = u t := by
    ext w
    simp [funext_iff, Fintype.mem_piFinset]
  rw [hfib, ← Complex.ofReal_sum]
  congr 1
  exact (Finset.prod_univ_sum (fun t => Finset.univ.filter fun b => F b = u t)
    (fun _ b => π.prob b)).symm

/-- `lem:lift` (a), product Fubini: `𝔼_{ξ̃^κ} Φ(q x̃, y, z) = 𝔼_{ξ^κ} Φ(x, y, z)`. -/
theorem k7_lift_first_expect (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ : FinProb (A × Y × Z))
    {κ : Type} [Fintype κ] [DecidableEq κ] (Φ : (κ → A × Y × Z) → ℂ) :
    (((k7LiftFirst n hn1 ξ).pi κ).cexpect fun w => Φ fun t => ((w t).1.1, (w t).2.1, (w t).2.2)) =
      (ξ.pi κ).cexpect Φ := by
  rw [k7lift_pushforward_pi (k7LiftFirst n hn1 ξ)
    (fun p : K7Lift n × Y × Z => (p.1.1, p.2.1, p.2.2)) Φ]
  have : mergePush (k7LiftFirst n hn1 ξ) (fun p : K7Lift n × Y × Z => (p.1.1, p.2.1, p.2.2)) = ξ :=
    k7lift_finProb_ext _ _ (k7_lift_first_push n hn1 ξ)
  rw [this]

omit [DecidableEq A] [DecidableEq Y] [DecidableEq Z] in
/-- `lem:lift` (b): `supp ξ̃ = {((a, j), y, z) : (a, y, z) ∈ supp ξ}`. -/
theorem k7_lift_first_mem_support (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ : FinProb (A × Y × Z))
    (p : K7Lift n × Y × Z) :
    p ∈ (k7LiftFirst n hn1 ξ).support ↔ (p.1.1, p.2.1, p.2.2) ∈ ξ.support := by
  have hn0 : n p.1.1 ≠ 0 := by have := hn1 p.1.1; omega
  simp [FinProb.support, k7LiftFirst, hn0]

omit [DecidableEq A] [DecidableEq Y] [DecidableEq Z] in
/-- `lem:lift` (c): every atom of `ξ` on its support `≥ α'` gives every atom of `ξ̃` `≥ α' α`
(`n_a ≤ M ≤ 1/α`). -/
theorem k7_lift_first_atom {α α' : ℝ} (hα : 0 < α) (hα' : 0 ≤ α') (M : ℕ) (n : A → ℕ)
    (hn1 : ∀ a, 1 ≤ n a) (hnM : ∀ a, n a ≤ M) (hM : (M : ℝ) ≤ 1 / α) (ξ : FinProb (A × Y × Z))
    (hξ : ∀ p ∈ ξ.support, α' ≤ ξ.prob p) :
    ∀ p ∈ (k7LiftFirst n hn1 ξ).support, α' * α ≤ (k7LiftFirst n hn1 ξ).prob p := by
  intro p hp
  rw [k7_lift_first_mem_support] at hp
  have h1 := hξ _ hp
  have hna : (1 : ℝ) ≤ n p.1.1 := by exact_mod_cast hn1 p.1.1
  have hna' : (n p.1.1 : ℝ) ≤ M := by exact_mod_cast hnM p.1.1
  have hαM : α * M ≤ 1 := by
    rw [le_div_iff₀ hα] at hM
    linarith
  have h2 : α * (n p.1.1 : ℝ) ≤ 1 := by nlinarith
  rw [k7LiftFirst_prob, le_div_iff₀ (by linarith)]
  calc α' * α * n p.1.1 = α' * (α * n p.1.1) := by ring
    _ ≤ α' * 1 := mul_le_mul_of_nonneg_left h2 hα'
    _ ≤ _ := by linarith

/-- the arithmetic of `lem:lift` (c): `α' = α²/(1+α)` gives `α' α ≥ α³/2`. -/
theorem k7_atom_cube {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) : α ^ 3 / 2 ≤ α ^ 2 / (1 + α) * α := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith [pow_pos hα0 3]

private theorem k7lift_conn {A B : Type} (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (R : A → B → Prop)
    (b0 : B)
    (h : (SimpleGraph.fromRel fun (u : A ⊕ B) v => ∃ a b, R a b ∧ u = Sum.inl a ∧
      v = Sum.inr b).Connected) :
    (SimpleGraph.fromRel fun (u : K7Lift n ⊕ B) v => ∃ a b, R a.1 b ∧ u = Sum.inl a ∧
      v = Sum.inr b).Connected := by
  set G := (SimpleGraph.fromRel fun (u : A ⊕ B) v => ∃ a b, R a b ∧ u = Sum.inl a ∧
      v = Sum.inr b) with hG
  set G' := (SimpleGraph.fromRel fun (u : K7Lift n ⊕ B) v => ∃ a b, R a.1 b ∧ u = Sum.inl a ∧
      v = Sum.inr b) with hG'
  have hadj : ∀ (ã : K7Lift n) (b : B), R ã.1 b → G'.Adj (Sum.inl ã) (Sum.inr b) := by
    intro ã b hR
    rw [hG', SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨ã, b, hR, rfl, rfl⟩⟩
  have hnbr : ∀ a, ∃ b, R a b := by
    intro a
    obtain ⟨w⟩ := h.preconnected (Sum.inl a) (Sum.inr b0)
    cases w with
    | cons hadj' _ =>
      rw [hG, SimpleGraph.fromRel_adj] at hadj'
      obtain ⟨_, ⟨a', b, hR, h1, h2⟩ | ⟨a', b, hR, h1, h2⟩⟩ := hadj'
      · exact ⟨b, by rw [Sum.inl.inj h1]; exact hR⟩
      · exact absurd h2 Sum.inl_ne_inr
  let s : A → K7Lift n := fun a => ⟨a, ⟨0, hn1 a⟩⟩
  have hclaim1 : ∀ ut : K7Lift n ⊕ B, G'.Reachable ut (Sum.map (fun ã : K7Lift n => s ã.1) id ut) := by
    intro ut
    rcases ut with ã | b
    · obtain ⟨b, hb⟩ := hnbr ã.1
      exact (hadj ã b hb).reachable.trans (hadj (s ã.1) b hb).reachable.symm
    · exact SimpleGraph.Reachable.refl _
  have hclaim2 : ∀ u v : A ⊕ B, G.Reachable u v →
      G'.Reachable (Sum.map s id u) (Sum.map s id v) := by
    rintro u v ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj' _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      rw [hG, SimpleGraph.fromRel_adj] at hadj'
      obtain ⟨_, ⟨a, b, hR, rfl, rfl⟩ | ⟨a, b, hR, rfl, rfl⟩⟩ := hadj'
      · exact (hadj (s a) b hR).reachable
      · exact (hadj (s a) b hR).reachable.symm
  have : Nonempty (K7Lift n ⊕ B) := ⟨Sum.inr b0⟩
  refine ⟨fun ut vt => ?_⟩
  have hq := hclaim2 _ _ (h.preconnected (Sum.map Sigma.fst id ut) (Sum.map Sigma.fst id vt))
  have e : ∀ ut : K7Lift n ⊕ B, Sum.map (fun ã : K7Lift n => s ã.1) id ut =
      Sum.map s id (Sum.map Sigma.fst id ut) := by
    intro ut; rcases ut with _ | _ <;> rfl
  rw [← e, ← e] at hq
  exact ((hclaim1 ut).trans hq).trans (hclaim1 vt).symm

omit [DecidableEq A] [DecidableEq Y] [DecidableEq Z] in
private theorem k7lift_exists_support (ξ : FinProb (A × Y × Z)) : ∃ p, p ∈ ξ.support := by
  by_contra hcon
  simp only [not_exists] at hcon
  have : ∀ p, ξ.prob p = 0 := fun p => by
    have := hcon p
    simpa [FinProb.support] using this
  have h1 := ξ.sum_eq_one
  simp [this] at h1

/-- `lem:lift` (d): the lift of a pairwise connected support is pairwise connected (the three graphs on
the whole alphabets, `pairwiseConnected3_iff`; lifting of paths through `q`). -/
theorem k7_lift_first_pairwiseConnected3 (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a)
    (ξ : FinProb (A × Y × Z)) (h : PairwiseConnected3 ξ.support) :
    PairwiseConnected3 (k7LiftFirst n hn1 ξ).support := by
  obtain ⟨⟨x0, y0, z0⟩, hp0⟩ := k7lift_exists_support ξ
  obtain ⟨h1, h2, h3⟩ := (pairwiseConnected3_iff _).1 h
  refine (pairwiseConnected3_iff _).2 ⟨?_, ?_, ?_⟩
  · have e0 : (SimpleGraph.fromRel fun (a : A ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ ξ.support ∧ a = Sum.inl x ∧ b = Sum.inr y) =
        SimpleGraph.fromRel fun (u : A ⊕ Y) v => ∃ a b, (∃ z, (a, b, z) ∈ ξ.support) ∧
          u = Sum.inl a ∧ v = Sum.inr b := by
      congr 1
      funext u v
      apply propext
      constructor
      · rintro ⟨x, y, z, hm, h1, h2⟩
        exact ⟨x, y, ⟨z, hm⟩, h1, h2⟩
      · rintro ⟨x, y, ⟨z, hm⟩, h1, h2⟩
        exact ⟨x, y, z, hm, h1, h2⟩
    have e1 : (SimpleGraph.fromRel fun (a : K7Lift n ⊕ Y) b =>
        ∃ x y z, (x, y, z) ∈ (k7LiftFirst n hn1 ξ).support ∧ a = Sum.inl x ∧ b = Sum.inr y) =
        SimpleGraph.fromRel fun (u : K7Lift n ⊕ Y) v => ∃ a b, (∃ z, (a.1, b, z) ∈ ξ.support) ∧
          u = Sum.inl a ∧ v = Sum.inr b := by
      congr 1
      funext u v
      apply propext
      constructor
      · rintro ⟨x, y, z, hm, h1, h2⟩
        exact ⟨x, y, ⟨z, (k7_lift_first_mem_support n hn1 ξ _).1 hm⟩, h1, h2⟩
      · rintro ⟨x, y, ⟨z, hm⟩, h1, h2⟩
        exact ⟨x, y, z, (k7_lift_first_mem_support n hn1 ξ (x, y, z)).2 hm, h1, h2⟩
    rw [e1]
    rw [e0] at h1
    exact k7lift_conn n hn1 _ y0 h1
  · have e0 : (SimpleGraph.fromRel fun (a : A ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ ξ.support ∧ a = Sum.inl x ∧ b = Sum.inr z) =
        SimpleGraph.fromRel fun (u : A ⊕ Z) v => ∃ a b, (∃ y, (a, y, b) ∈ ξ.support) ∧
          u = Sum.inl a ∧ v = Sum.inr b := by
      congr 1
      funext u v
      apply propext
      constructor
      · rintro ⟨x, y, z, hm, h1, h2⟩
        exact ⟨x, z, ⟨y, hm⟩, h1, h2⟩
      · rintro ⟨x, z, ⟨y, hm⟩, h1, h2⟩
        exact ⟨x, y, z, hm, h1, h2⟩
    have e1 : (SimpleGraph.fromRel fun (a : K7Lift n ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ (k7LiftFirst n hn1 ξ).support ∧ a = Sum.inl x ∧ b = Sum.inr z) =
        SimpleGraph.fromRel fun (u : K7Lift n ⊕ Z) v => ∃ a b, (∃ y, (a.1, y, b) ∈ ξ.support) ∧
          u = Sum.inl a ∧ v = Sum.inr b := by
      congr 1
      funext u v
      apply propext
      constructor
      · rintro ⟨x, y, z, hm, h1, h2⟩
        exact ⟨x, z, ⟨y, (k7_lift_first_mem_support n hn1 ξ _).1 hm⟩, h1, h2⟩
      · rintro ⟨x, z, ⟨y, hm⟩, h1, h2⟩
        exact ⟨x, y, z, (k7_lift_first_mem_support n hn1 ξ (x, y, z)).2 hm, h1, h2⟩
    rw [e1]
    rw [e0] at h2
    exact k7lift_conn n hn1 _ z0 h2
  · have e : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ (k7LiftFirst n hn1 ξ).support ∧ a = Sum.inl y ∧ b = Sum.inr z) =
        SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ ξ.support ∧ a = Sum.inl y ∧ b = Sum.inr z := by
      congr 1
      funext u v
      apply propext
      constructor
      · rintro ⟨x, y, z, hm, h1, h2⟩
        exact ⟨x.1, y, z, (k7_lift_first_mem_support n hn1 ξ _).1 hm, h1, h2⟩
      · rintro ⟨x, y, z, hm, h1, h2⟩
        exact ⟨⟨x, ⟨0, hn1 x⟩⟩, y, z, (k7_lift_first_mem_support n hn1 ξ (_, y, z)).2 hm, h1, h2⟩
    rw [e]
    exact h3

omit [Fintype A] [DecidableEq A] in
/-- `lem:lift` (e): `F̃_{J→ã} = (F_{J→qã}) ∘ q^{J̄}` for `F̃ = F ∘ q^ι`. -/
theorem k7_lift_restrictFix {n : A → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → A) → ℂ)
    (J : Finset ι) (ã : ↥J → K7Lift n) (w : ↥Jᶜ → K7Lift n) :
    restrictFix J ã (fun x => F fun t => (x t).1) w =
      restrictFix J (fun t => (ã t).1) F (fun t => (w t).1) := by
  unfold restrictFix glueFix
  beta_reduce
  congr 1
  funext i
  by_cases hi : i ∈ J <;> simp [hi]

/-- `lem:lift` (a) and (e) combined, in the form Step 2 of `thm:kcsp-rat` consumes: the lifted
three-slot correlation (first slot `f̃ = f ∘ q^ι` restricted at `ã`; slots `2, 3` unchanged) equals the
unlifted one at `(qã, b, c)`. -/
theorem k7_lift_first_corr (n : A → ℕ) (hn1 : ∀ a, 1 ≤ n a) (ξ : FinProb (A × Y × Z)) {ι : Type}
    [Fintype ι] [DecidableEq ι] (J : Finset ι) (ã : ↥J → K7Lift n) (b : ↥J → Y) (c : ↥J → Z)
    (f : (ι → A) → ℂ) (f₂ : (ι → Y) → ℂ) (g : (ι → Z) → ℂ) :
    (((k7LiftFirst n hn1 ξ).pi ↥Jᶜ).cexpect fun w =>
        restrictFix J ã (fun x => f fun t => (x t).1) (fun t => (w t).1) *
          star (restrictFix J b f₂ (fun t => (w t).2.1)) *
          star (restrictFix J c g (fun t => (w t).2.2))) =
      (ξ.pi ↥Jᶜ).cexpect fun w =>
        restrictFix J (fun t => (ã t).1) f (fun t => (w t).1) *
          star (restrictFix J b f₂ (fun t => (w t).2.1)) *
          star (restrictFix J c g (fun t => (w t).2.2)) := by
  simp only [k7_lift_restrictFix]
  exact k7_lift_first_expect n hn1 ξ fun w =>
    restrictFix J (fun t => (ã t).1) f (fun t => (w t).1) *
          star (restrictFix J b f₂ (fun t => (w t).2.1)) *
          star (restrictFix J c g (fun t => (w t).2.2))

end Lift

end TrackB
end RestrictedPolynomials
end
