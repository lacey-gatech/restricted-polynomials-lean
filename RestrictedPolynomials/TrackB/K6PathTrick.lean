module

public import RestrictedPolynomials.TrackB.PathTrickEmbedding
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect
public import RestrictedPolynomials.Frozen.FinProbSupport

/-!
# Track B: the CSP_6 path tricks, connectivity, `suppmu`, `mu-minus`

Source: CSP_6, l. 686-775: `def:pathtrick`,
`lemma:suppmu#apply-path-keeps-connectedness`, `lemma:suppmu`, `thm:toswap#mu-minus`.

Formalization choices: coin-selected pair for `mu-minus`; the `y`
and `z` tricks start at `Σ` and keep `f`; thresholds `2^r ≥ |start| + |end|` (sharp at equal
sizes); `PathX` word alphabets; the general form of `mu-minus` takes `hsupp` and an injective label map.
The weight `α` is not uniform here; the uniform weight is in Supplement D.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### Transport of a distribution along an equivalence of carriers -/
section K6ptPerm

/-- the law of `e a` for `a ∼ π`. -/
def k6ptPerm {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (π : FinProb α) : FinProb β where
  prob b := π.prob (e.symm b)
  nonneg _ := π.nonneg _
  sum_eq_one := by
    rw [← π.sum_eq_one]
    exact Equiv.sum_comp e.symm π.prob

theorem k6ptPerm_prob {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (π : FinProb α)
    (b : β) : (k6ptPerm e π).prob b = π.prob (e.symm b) := rfl

theorem k6ptPerm_support {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (π : FinProb α) :
    (k6ptPerm e π).support = e '' π.support := by
  ext b
  simp [FinProb.support, k6ptPerm, Equiv.image_eq_preimage_symm]

theorem k6pt_cexpect_perm {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (π : FinProb α)
    (G : β → ℂ) : (k6ptPerm e π).cexpect G = π.cexpect (fun a => G (e a)) := by
  unfold FinProb.cexpect
  rw [← Equiv.sum_comp e (fun b => (((k6ptPerm e π).prob b : ℝ) : ℂ) * G b)]
  simp [k6ptPerm]

theorem k6pt_cexpect_pi_perm {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (π : FinProb α)
    (ι : Type) [Fintype ι] [DecidableEq ι] (G : (ι → β) → ℂ) :
    ((k6ptPerm e π).pi ι).cexpect G = (π.pi ι).cexpect (fun p => G (fun i => e (p i))) := by
  unfold FinProb.cexpect
  rw [← Equiv.sum_comp (Equiv.piCongrRight fun _ : ι => e)
    (fun b => ((((k6ptPerm e π).pi ι).prob b : ℝ) : ℂ) * G b)]
  simp [FinProb.pi, k6ptPerm]
  rfl

end K6ptPerm

/-! ### The CSP_6 path tricks (`def:pathtrick`) -/
section K6ptDefs

/-- `(x, y, z) ↦ (y, x, z)`: read `μ` with labels `y`, start `x`, end `z`. -/
def k6ptEqY (X Y Z : Type) : X × Y × Z ≃ Y × X × Z where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(x, y, z) ↦ (z, x, y)`: read `μ` with labels `z`, start `x`, end `y`. -/
def k6ptEqZ (X Y Z : Type) : X × Y × Z ≃ Z × X × Y where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `2^r - 1` is odd for `r ≥ 1` (the length of the `r`-step path trick). -/
theorem k6pt_odd {r : ℕ} (hr : 1 ≤ r) : Odd (2 ^ r - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  refine ⟨2 ^ s - 1, ?_⟩
  have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  rw [pow_add, pow_one]
  omega

theorem k6pt_odd_three : Odd 3 := ⟨1, rfl⟩

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- `μ` as a distribution on `Γ × Σ × Φ`: the roles (label, start, end) of the `y` path trick. -/
def k6ptViewY (μ : FinProb (X × Y × Z)) : FinProb (Y × X × Z) := k6ptPerm (k6ptEqY X Y Z) μ

/-- `μ` as a distribution on `Φ × Σ × Γ`: the roles (label, start, end) of the `z` path trick. -/
def k6ptViewZ (μ : FinProb (X × Y × Z)) : FinProb (Z × X × Y) := k6ptPerm (k6ptEqZ X Y Z) μ

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem k6ptViewY_prob (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    (k6ptViewY μ).prob (y, x, z) = μ.prob (x, y, z) := rfl

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem k6ptViewZ_prob (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    (k6ptViewZ μ).prob (z, x, y) = μ.prob (x, y, z) := rfl

/-- `Σ⁺` of the `x` path trick: the label words that occur (the support of the `x`-marginal). -/
abbrev K6ptSigPlus (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) : Type :=
  PathX μ (2 ^ r - 1) (k6pt_odd hr)

/-- `Γ⁺` of the `y` path trick. -/
abbrev K6ptGamPlus (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) : Type :=
  PathX (k6ptViewY μ) (2 ^ r - 1) (k6pt_odd hr)

/-- `Φ⁺` of the `z` path trick. -/
abbrev K6ptPhiPlus (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) : Type :=
  PathX (k6ptViewZ μ) (2 ^ r - 1) (k6pt_odd hr)

/-- CSP_6 `def:pathtrick`, `x` path trick (labels `x`, start `y₁ ∼ μ_y`, end `z`): it IS the walk
distribution `pathTrick` of paper IV for `ℓ = 2^r - 1` (same object, reused). The law of
`((x₁, x₁', …, x_{2^{r-1}}), y₁, z_{2^{r-1}})` for the process of the source. -/
def k6ptTrickX (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) :
    FinProb (K6ptSigPlus μ r hr × Y × Z) :=
  pathTrick μ (2 ^ r - 1) (k6pt_odd hr)

/-- CSP_6 `def:pathtrick`, `y` path trick: labels `y`, start `x₁ ∼ μ_x`, end `z`;
sample `x₁ ∼ μ_x`, `(y₁, z₁) ∼ μ | x = x₁`, `(y₁', x₂) ∼ μ | z = z₁`, …; output
`(x₁, (y₁, y₁', …), z_end) ∈ Σ × Γ⁺ × Φ`. -/
def k6ptTrickY (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) :
    FinProb (X × K6ptGamPlus μ r hr × Z) :=
  k6ptPerm (k6ptEqY (K6ptGamPlus μ r hr) X Z) (pathTrick (k6ptViewY μ) (2 ^ r - 1) (k6pt_odd hr))

/-- CSP_6 `def:pathtrick`, `z` path trick: labels `z`, start `x₁ ∼ μ_x`, end `y`;
output `(x₁, y_end, (z₁, z₁', …)) ∈ Σ × Γ × Φ⁺`. -/
def k6ptTrickZ (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) :
    FinProb (X × Y × K6ptPhiPlus μ r hr) :=
  k6ptPerm (k6ptEqZ X Y (K6ptPhiPlus μ r hr)).symm
    (pathTrick (k6ptViewZ μ) (2 ^ r - 1) (k6pt_odd hr))

theorem k6ptTrickY_prob (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) (x : X)
    (w : K6ptGamPlus μ r hr) (z : Z) :
    (k6ptTrickY μ r hr).prob (x, w, z) = pathWeight (k6ptViewY μ) (2 ^ r - 1) (k6pt_odd hr) w.1 x z :=
  rfl

theorem k6ptTrickZ_prob (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) (x : X) (y : Y)
    (w : K6ptPhiPlus μ r hr) :
    (k6ptTrickZ μ r hr).prob (x, y, w) = pathWeight (k6ptViewZ μ) (2 ^ r - 1) (k6pt_odd hr) w.1 x y :=
  rfl


omit [DecidableEq Y] in
/-- `|Γ⁺| ≤ |Γ|^{2^r - 1}`: the alphabet sizes entering the thresholds of `lemma:suppmu` depend only on
`r` and `|Γ|`. -/
theorem k6pt_card_gamPlus_le (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (K6ptGamPlus μ r hr) ≤ Fintype.card Y ^ (2 ^ r - 1) := by
  calc Fintype.card (K6ptGamPlus μ r hr) ≤ Fintype.card (Fin (2 ^ r - 1) → Y) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card Y ^ (2 ^ r - 1) := by simp

omit [DecidableEq Z] in
/-- `|Φ⁺| ≤ |Φ|^{2^r - 1}`. -/
theorem k6pt_card_phiPlus_le (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (K6ptPhiPlus μ r hr) ≤ Fintype.card Z ^ (2 ^ r - 1) := by
  calc Fintype.card (K6ptPhiPlus μ r hr) ≤ Fintype.card (Fin (2 ^ r - 1) → Z) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card Z ^ (2 ^ r - 1) := by simp

omit [DecidableEq X] in
/-- `|Σ⁺| ≤ |Σ|^{2^r - 1}`. -/
theorem k6pt_card_sigPlus_le (μ : FinProb (X × Y × Z)) (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (K6ptSigPlus μ r hr) ≤ Fintype.card X ^ (2 ^ r - 1) := by
  calc Fintype.card (K6ptSigPlus μ r hr) ≤ Fintype.card (Fin (2 ^ r - 1) → X) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card X ^ (2 ^ r - 1) := by simp

section K6ptCompose
variable (μ : FinProb (X × Y × Z)) (r₁ : ℕ) (hr₁ : 1 ≤ r₁) (r₂ : ℕ) (hr₂ : 1 ≤ r₂)

/-- `Γ⁺` of the composite. -/
abbrev K6ptGam : Type := K6ptGamPlus μ r₁ hr₁

/-- `μ'`: after the `y` path trick with parameter `r₁`. -/
def k6ptMu1 : FinProb (X × K6ptGam μ r₁ hr₁ × Z) := k6ptTrickY μ r₁ hr₁

/-- `Φ⁺` of the composite (the `z` path trick is applied to `μ'`). -/
abbrev K6ptPhi : Type := K6ptPhiPlus (k6ptMu1 μ r₁ hr₁) r₂ hr₂

/-- `μ''`: after the `z` path trick with parameter `r₂`. -/
def k6ptMu2 : FinProb (X × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂) :=
  k6ptTrickZ (k6ptMu1 μ r₁ hr₁) r₂ hr₂

/-- `Σ⁺ ⊆ Σ³` of the composite. -/
abbrev K6ptSig : Type := PathX (k6ptMu2 μ r₁ hr₁ r₂ hr₂) 3 k6pt_odd_three

/-- `μ⁺` of CSP_6 `eq:3path`: `y` path trick (`r₁`), then `z` path trick (`r₂`), then `x` path trick
with `r = 2` (`ℓ = 2² - 1 = 3`), each applied to the previous distribution. -/
def k6ptMuPlus :
    FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂) :=
  pathTrick (k6ptMu2 μ r₁ hr₁ r₂ hr₂) 3 k6pt_odd_three

end K6ptCompose
end K6ptDefs

/-! ### Support layer: `#apply-path-keeps-connectedness`, `lemma:suppmu`, `#mu-minus` -/
section K6ptSupport
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma k6pt_exists_support (μ : FinProb (X × Y × Z)) : ∃ p, p ∈ μ.support := by
  by_contra hne
  have : ∀ p, μ.prob p = 0 := fun p => by
    by_contra h0; exact hne ⟨p, h0⟩
  have h1 := μ.sum_eq_one
  simp [this] at h1

/-- an odd walk of `2N+1` steps with positive weight -/
private def k6ptQpos (μ : FinProb (X × Y × Z)) (N : ℕ) (y : Y) (z : Z) : Prop :=
  ∃ xs : List X, xs.length = 2 * N + 1 ∧ 0 < walkYZ μ xs y z

private lemma k6pt_walk_prepend_pos (μ : FinProb (X × Y × Z)) {y y' : Y} {z z' : Z} {x₁ x₂ : X}
    {xs : List X} (hpos : 0 < walkYZ μ xs y' z) (h1 : μ.prob (x₁, y, z') ≠ 0)
    (h2 : μ.prob (x₂, y', z') ≠ 0) : 0 < walkYZ μ (x₁ :: x₂ :: xs) y z := by
  rw [walkYZ, Matrix.mul_apply]
  have hnn : ∀ y'', 0 ≤ (stepYZ μ x₁ * stepZY μ x₂) y y'' * walkYZ μ xs y'' z := fun y'' => by
    refine mul_nonneg ?_ (walkYZ_nonneg μ _ _ _)
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun z'' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun y'' _ => hnn y'') (Finset.mem_univ y'))
  refine mul_pos ?_ hpos
  rw [Matrix.mul_apply]
  exact lt_of_lt_of_le (mul_pos (stepYZ_pos μ h1) (stepZY_pos μ h2))
    (Finset.single_le_sum (f := fun z'' => stepYZ μ x₁ y z'' * stepZY μ x₂ z'' y')
      (fun z'' _ => mul_nonneg (stepYZ_nonneg μ _ _ _) (stepZY_nonneg μ _ _ _))
      (Finset.mem_univ z'))

private lemma k6ptQpos_zero (μ : FinProb (X × Y × Z)) {x : X} {y : Y} {z : Z}
    (h : μ.prob (x, y, z) ≠ 0) : k6ptQpos μ 0 y z :=
  ⟨[x], rfl, by simpa [walkYZ] using stepYZ_pos μ h⟩

private lemma k6ptQpos_prepend (μ : FinProb (X × Y × Z)) {N : ℕ} {y y' : Y} {z z' : Z}
    {x₁ x₂ : X} (hQ : k6ptQpos μ N y' z) (h1 : μ.prob (x₁, y, z') ≠ 0)
    (h2 : μ.prob (x₂, y', z') ≠ 0) : k6ptQpos μ (N + 1) y z := by
  obtain ⟨xs, hlen, hpos⟩ := hQ
  exact ⟨x₁ :: x₂ :: xs, by simp [hlen]; ring, k6pt_walk_prepend_pos μ hpos h1 h2⟩

private lemma k6ptQpos_mono (μ : FinProb (X × Y × Z)) {y : Y} {z : Z}
    (he : ∃ x z', μ.prob (x, y, z') ≠ 0) {N : ℕ} (hQ : k6ptQpos μ N y z) :
    ∀ k, k6ptQpos μ (N + k) y z := by
  obtain ⟨x, z', hx⟩ := he
  intro k
  induction k with
  | zero => simpa using hQ
  | succ k ih => exact k6ptQpos_prepend μ ih hx hx

private lemma k6pt_walk_claim (μ : FinProb (X × Y × Z)) :
    ∀ (u v : Y ⊕ Z) (p : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ μ.support ∧ a = Sum.inl y ∧ b = Sum.inr z).Walk u v), ∀ z, v = Sum.inr z →
      (∀ y, u = Sum.inl y → ∃ N, p.length = 2 * N + 1 ∧ k6ptQpos μ N y z) ∧
      (∀ z0, u = Sum.inr z0 → (p.length = 0 ∧ z0 = z) ∨
        ∃ N, p.length = 2 * N + 2 ∧ ∃ y1 x, μ.prob (x, y1, z0) ≠ 0 ∧ k6ptQpos μ N y1 z) := by
  intro u v p
  induction p with
  | nil =>
    intro z hv
    refine ⟨fun y hy => ?_, fun z0 hz0 => ?_⟩
    · rw [hv] at hy; cases hy
    · rw [hv] at hz0
      exact Or.inl ⟨rfl, (Sum.inr.inj hz0).symm⟩
  | @cons u v w hadj p ih =>
    intro z hw
    have ihv := ih z hw
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x, y, z', hm, rfl, rfl⟩ | ⟨x, y, z', hm, rfl, rfl⟩⟩
    · refine ⟨fun y1 hy1 => ?_, fun z0 hz0 => by cases hz0⟩
      have hy1' : y1 = y := (Sum.inl.inj hy1).symm
      subst hy1'
      rcases ihv.2 z' rfl with ⟨hl, hz⟩ | ⟨N, hl, y2, x', hx', hQ⟩
      · refine ⟨0, by simp [hl], ?_⟩
        subst hz
        exact k6ptQpos_zero μ hm
      · exact ⟨N + 1, by simp [hl]; ring, k6ptQpos_prepend μ hQ hm hx'⟩
    · refine ⟨fun y1 hy1 => (by cases hy1), fun z0 hz0 => ?_⟩
      have hz0' : z0 = z' := (Sum.inr.inj hz0).symm
      subst hz0'
      obtain ⟨N, hl, hQ⟩ := ihv.1 y rfl
      exact Or.inr ⟨N, by simp [hl], y, x, hm, hQ⟩

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma k6pt_Y_has_edge (μ : FinProb (X × Y × Z)) (z0 : Z)
    (h3 : (SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
        ∃ x y z, (x, y, z) ∈ μ.support ∧ a = Sum.inl y ∧ b = Sum.inr z).Connected) (y : Y) :
    ∃ x z, μ.prob (x, y, z) ≠ 0 := by
  obtain ⟨p⟩ := h3.preconnected (Sum.inl y) (Sum.inr z0)
  cases p with
  | cons hadj _ =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_, ⟨x, y', z, hm, h1, h2⟩ | ⟨x, y', z, hm, h1, h2⟩⟩
    · cases h1; exact ⟨x, z, hm⟩
    · cases h2

private lemma k6pt_pathWeight3_ne (μ : FinProb (X × Y × Z)) (hℓ : Odd 3) {x₁ x₂ x₃ : X}
    {y y₂ : Y} {z z₁ : Z} (h1 : μ.prob (x₁, y, z₁) ≠ 0) (h2 : μ.prob (x₂, y₂, z₁) ≠ 0)
    (h3 : μ.prob (x₃, y₂, z) ≠ 0) : pathWeight μ 3 hℓ ![x₁, x₂, x₃] y z ≠ 0 := by
  have hm : 0 < margY μ y :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm h1)) (prob_le_margY μ x₁ y z₁)
  have hw : walkYZ μ (List.ofFn ![x₁, x₂, x₃]) y z = walkYZ μ [x₁, x₂, x₃] y z := by
    simp [List.ofFn_succ]
  unfold pathWeight
  rw [hw]
  refine (mul_pos hm ?_).ne'
  exact k6pt_walk_prepend_pos μ (xs := [x₃]) (by simpa [walkYZ] using stepYZ_pos μ h3) h1 h2

/-- Explicit-threshold completeness of the walk distribution of paper IV (with an explicit threshold): if the
`Γ–Φ` graph of `μ` is connected, every odd `ℓ ≥ |Γ| + |Φ| - 1` joins every `y ∈ Γ` to every `z ∈ Φ`. -/
theorem k6pt_pathTrick_complete (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (h : PairwiseConnected3 μ.support) (hℓ' : Fintype.card Y + Fintype.card Z ≤ ℓ + 1)
    (y : Y) (z : Z) : ∃ w : PathX μ ℓ hℓ, (w, y, z) ∈ (pathTrick μ ℓ hℓ).support := by
  obtain ⟨p0, hp0⟩ := k6pt_exists_support μ
  obtain ⟨-, -, h3⟩ := (pairwiseConnected3_iff _).1 h
  obtain ⟨p, hpath, -⟩ := h3.exists_path_of_dist (Sum.inl y) (Sum.inr z)
  have hlt := hpath.length_lt
  rw [Fintype.card_sum] at hlt
  obtain ⟨N, hN, hQ⟩ := (k6pt_walk_claim μ _ _ p z rfl).1 y rfl
  obtain ⟨n, hn⟩ := id hℓ
  have hNn : N + (n - N) = n := by omega
  have hedge := k6pt_Y_has_edge μ p0.2.2 h3 y
  obtain ⟨xs, hlen, hpos⟩ := hNn ▸ k6ptQpos_mono μ hedge hQ (n - N)
  obtain ⟨x, z', hxz⟩ := hedge
  have hm : 0 < margY μ y :=
    lt_of_lt_of_le (lt_of_le_of_ne (μ.nonneg _) (Ne.symm hxz)) (prob_le_margY μ x y z')
  let w : Fin ℓ → X := fun i => xs[i.1]'(by have := i.2; omega)
  have hw : List.ofFn w = xs := by
    apply List.ext_getElem
    · simp [hlen, hn]
    · intro i h1 h2; simp [w]
  have hne : pathWeight μ ℓ hℓ w y z ≠ 0 := by
    unfold pathWeight
    rw [hw]
    exact (mul_pos hm hpos).ne'
  exact ⟨⟨w, y, z, hne⟩, hne⟩

private lemma k6pt_conn_iff_of_iff {V : Type} (R R' : V → V → Prop) (h : ∀ a b, R a b ↔ R' a b) :
    (SimpleGraph.fromRel R).Connected ↔ (SimpleGraph.fromRel R').Connected := by
  have : R = R' := funext₂ fun a b => propext (h a b)
  subst this
  exact Iff.rfl

private lemma k6pt_conn_swap {A B : Type} (R : A → B → Prop) :
    (SimpleGraph.fromRel fun (a : A ⊕ B) b => ∃ x y, R x y ∧ a = Sum.inl x ∧ b = Sum.inr y).Connected ↔
    (SimpleGraph.fromRel fun (b : B ⊕ A) a => ∃ x y, R x y ∧ b = Sum.inl y ∧ a = Sum.inr x).Connected := by
  have iso : (SimpleGraph.fromRel fun (a : A ⊕ B) b => ∃ x y, R x y ∧ a = Sum.inl x ∧ b = Sum.inr y) ≃g
      (SimpleGraph.fromRel fun (b : B ⊕ A) a => ∃ x y, R x y ∧ b = Sum.inl y ∧ a = Sum.inr x) :=
    { toEquiv := Equiv.sumComm _ _
      map_rel_iff' := by
        intro u v
        simp only [SimpleGraph.fromRel_adj, Equiv.sumComm_apply]
        rcases u with u | u <;> rcases v with v | v <;> simp }
  exact iso.connected_iff

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma k6pt_mem_eqY (S : Set (X × Y × Z)) (a : Y) (b : X) (c : Z) :
    (a, b, c) ∈ k6ptEqY X Y Z '' S ↔ (b, a, c) ∈ S := by
  rw [Equiv.image_eq_preimage_symm]; rfl

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private lemma k6pt_mem_eqZ (S : Set (X × Y × Z)) (a : Z) (b : X) (c : Y) :
    (a, b, c) ∈ k6ptEqZ X Y Z '' S ↔ (b, c, a) ∈ S := by
  rw [Equiv.image_eq_preimage_symm]; rfl

theorem k6pt_pairwiseConnected3_eqY (S : Set (X × Y × Z)) :
    PairwiseConnected3 S ↔ PairwiseConnected3 (k6ptEqY X Y Z '' S) := by
  rw [pairwiseConnected3_iff, pairwiseConnected3_iff]
  simp only [k6pt_mem_eqY]
  have e1 := k6pt_conn_swap (fun (x : X) (y : Y) => ∃ z, (x, y, z) ∈ S)
  have c1 := k6pt_conn_iff_of_iff
    (fun (a : X ⊕ Y) b => ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y)
    (fun (a : X ⊕ Y) b => ∃ x y, (∃ z, (x, y, z) ∈ S) ∧ a = Sum.inl x ∧ b = Sum.inr y)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨x, y, ⟨z, hs⟩, rfl, rfl⟩
      · rintro ⟨x, y, ⟨z, hs⟩, rfl, rfl⟩; exact ⟨x, y, z, hs, rfl, rfl⟩)
  have c2 := k6pt_conn_iff_of_iff
    (fun (a : Y ⊕ X) b => ∃ x y z, (y, x, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y)
    (fun (b : Y ⊕ X) a => ∃ x y, (∃ z, (x, y, z) ∈ S) ∧ b = Sum.inl y ∧ a = Sum.inr x)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, x, ⟨z, hs⟩, rfl, rfl⟩
      · rintro ⟨x, y, ⟨z, hs⟩, rfl, rfl⟩; exact ⟨y, x, z, hs, rfl, rfl⟩)
  have c3 := k6pt_conn_iff_of_iff
    (fun (a : Y ⊕ Z) b => ∃ x y z, (y, x, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z)
    (fun (a : Y ⊕ Z) b => ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, x, z, hs, rfl, rfl⟩
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, x, z, hs, rfl, rfl⟩)
  have c4 := k6pt_conn_iff_of_iff
    (fun (a : X ⊕ Z) b => ∃ x y z, (y, x, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z)
    (fun (a : X ⊕ Z) b => ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, x, z, hs, rfl, rfl⟩
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, x, z, hs, rfl, rfl⟩)
  rw [c1, c2, c3, c4, ← e1]
  tauto

theorem k6pt_pairwiseConnected3_eqZ (S : Set (X × Y × Z)) :
    PairwiseConnected3 S ↔ PairwiseConnected3 (k6ptEqZ X Y Z '' S) := by
  rw [pairwiseConnected3_iff, pairwiseConnected3_iff]
  simp only [k6pt_mem_eqZ]
  have e1 := k6pt_conn_swap (fun (x : X) (z : Z) => ∃ y, (x, y, z) ∈ S)
  have e2 := k6pt_conn_swap (fun (y : Y) (z : Z) => ∃ x, (x, y, z) ∈ S)
  have c1 := k6pt_conn_iff_of_iff
    (fun (a : X ⊕ Z) b => ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z)
    (fun (a : X ⊕ Z) b => ∃ x z, (∃ y, (x, y, z) ∈ S) ∧ a = Sum.inl x ∧ b = Sum.inr z)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨x, z, ⟨y, hs⟩, rfl, rfl⟩
      · rintro ⟨x, z, ⟨y, hs⟩, rfl, rfl⟩; exact ⟨x, y, z, hs, rfl, rfl⟩)
  have c2 := k6pt_conn_iff_of_iff
    (fun (a : Z ⊕ X) b => ∃ x y z, (y, z, x) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y)
    (fun (b : Z ⊕ X) a => ∃ x z, (∃ y, (x, y, z) ∈ S) ∧ b = Sum.inl z ∧ a = Sum.inr x)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, x, ⟨z, hs⟩, rfl, rfl⟩
      · rintro ⟨x, z, ⟨y, hs⟩, rfl, rfl⟩; exact ⟨z, x, y, hs, rfl, rfl⟩)
  have c3 := k6pt_conn_iff_of_iff
    (fun (a : Y ⊕ Z) b => ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z)
    (fun (a : Y ⊕ Z) b => ∃ y z, (∃ x, (x, y, z) ∈ S) ∧ a = Sum.inl y ∧ b = Sum.inr z)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, z, ⟨x, hs⟩, rfl, rfl⟩
      · rintro ⟨y, z, ⟨x, hs⟩, rfl, rfl⟩; exact ⟨x, y, z, hs, rfl, rfl⟩)
  have c4 := k6pt_conn_iff_of_iff
    (fun (a : Z ⊕ Y) b => ∃ x y z, (y, z, x) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr z)
    (fun (b : Z ⊕ Y) a => ∃ y z, (∃ x, (x, y, z) ∈ S) ∧ b = Sum.inl z ∧ a = Sum.inr y)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨z, x, ⟨y, hs⟩, rfl, rfl⟩
      · rintro ⟨y, z, ⟨x, hs⟩, rfl, rfl⟩; exact ⟨z, x, y, hs, rfl, rfl⟩)
  have c5 := k6pt_conn_iff_of_iff
    (fun (a : X ⊕ Y) b => ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl x ∧ b = Sum.inr y)
    (fun (a : X ⊕ Y) b => ∃ x y z, (y, z, x) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z)
    (fun a b => by
      constructor
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨z, x, y, hs, rfl, rfl⟩
      · rintro ⟨x, y, z, hs, rfl, rfl⟩; exact ⟨y, z, x, hs, rfl, rfl⟩)
  rw [c1, c2, c3, c4, c5, ← e1, ← e2]
  tauto

/-- CSP_6 `lemma:suppmu#apply-path-keeps-connectedness`, `x` path trick. -/
theorem k6pt_trickX_keeps (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    (r : ℕ) (hr : 1 ≤ r) :
    PairwiseConnected3 (k6ptTrickX μ r hr).support ∧
      (Fintype.card Y + Fintype.card Z ≤ 2 ^ r → ∀ (y : Y) (z : Z),
        ∃ w : K6ptSigPlus μ r hr, (w, y, z) ∈ (k6ptTrickX μ r hr).support) := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  unfold k6ptTrickX
  refine ⟨pathTrick_pairwiseConnected μ (k6pt_odd hr) h, fun hle y z => ?_⟩
  exact k6pt_pathTrick_complete μ (k6pt_odd hr) h (by omega) y z

/-- the same for the `y` path trick: `supp μ'_{x,z} = Σ × Φ` once `|Σ| + |Φ| ≤ 2^r`. -/
theorem k6pt_trickY_keeps (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    (r : ℕ) (hr : 1 ≤ r) :
    PairwiseConnected3 (k6ptTrickY μ r hr).support ∧
      (Fintype.card X + Fintype.card Z ≤ 2 ^ r → ∀ (x : X) (z : Z),
        ∃ w : K6ptGamPlus μ r hr, (x, w, z) ∈ (k6ptTrickY μ r hr).support) := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hV : PairwiseConnected3 (k6ptViewY μ).support := by
    unfold k6ptViewY
    rw [k6ptPerm_support]
    exact (k6pt_pairwiseConnected3_eqY _).1 h
  have hP := pathTrick_pairwiseConnected (k6ptViewY μ) (k6pt_odd hr) hV
  refine ⟨?_, fun hle x z => ?_⟩
  · unfold k6ptTrickY
    rw [k6ptPerm_support]
    exact (k6pt_pairwiseConnected3_eqY _).1 hP
  · obtain ⟨w, hw⟩ := k6pt_pathTrick_complete (k6ptViewY μ) (k6pt_odd hr) hV (by omega) x z
    refine ⟨w, ?_⟩
    unfold k6ptTrickY
    rw [k6ptPerm_support]
    exact ⟨(w, x, z), hw, rfl⟩

/-- the same for the `z` path trick: `supp μ''_{x,y} = Σ × Γ` once `|Σ| + |Γ| ≤ 2^r`. -/
theorem k6pt_trickZ_keeps (μ : FinProb (X × Y × Z)) (h : PairwiseConnected3 μ.support)
    (r : ℕ) (hr : 1 ≤ r) :
    PairwiseConnected3 (k6ptTrickZ μ r hr).support ∧
      (Fintype.card X + Fintype.card Y ≤ 2 ^ r → ∀ (x : X) (y : Y),
        ∃ w : K6ptPhiPlus μ r hr, (x, y, w) ∈ (k6ptTrickZ μ r hr).support) := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hV : PairwiseConnected3 (k6ptViewZ μ).support := by
    unfold k6ptViewZ
    rw [k6ptPerm_support]
    exact (k6pt_pairwiseConnected3_eqZ _).1 h
  have hP := pathTrick_pairwiseConnected (k6ptViewZ μ) (k6pt_odd hr) hV
  refine ⟨?_, fun hle x y => ?_⟩
  · unfold k6ptTrickZ
    rw [k6ptPerm_support]
    rw [k6pt_pairwiseConnected3_eqZ, Equiv.image_symm_image]
    exact hP
  · obtain ⟨w, hw⟩ := k6pt_pathTrick_complete (k6ptViewZ μ) (k6pt_odd hr) hV (by omega) x y
    refine ⟨w, ?_⟩
    unfold k6ptTrickZ
    rw [k6ptPerm_support]
    exact ⟨(w, x, y), hw, rfl⟩

/-- CSP_6 `lemma:suppmu`: for all `a, b ∈ Σ` there are `y ∈ Γ⁺`, `z ∈ Φ⁺` with `((a,a,b), y, z)` and
`((b,a,a), y, z)` both in `supp μ⁺`. The thresholds are the corrected ones (`2^r ≥ |start| + |end|`). -/
theorem k6pt_suppmu (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support)
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (h₁ : Fintype.card X + Fintype.card Z ≤ 2 ^ r₁)
    (h₂ : Fintype.card X + Fintype.card (K6ptGam μ r₁ hr₁) ≤ 2 ^ r₂) (a b : X) :
    ∃ (y : K6ptGam μ r₁ hr₁) (z : K6ptPhi μ r₁ hr₁ r₂ hr₂),
      (∃ w : K6ptSig μ r₁ hr₁ r₂ hr₂, w.1 = ![a, a, b] ∧
        (w, y, z) ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support) ∧
      (∃ w : K6ptSig μ r₁ hr₁ r₂ hr₂, w.1 = ![b, a, a] ∧
        (w, y, z) ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support) := by
  obtain ⟨hC1, hF1⟩ := k6pt_trickY_keeps μ hμ r₁ hr₁
  have hC1' : PairwiseConnected3 (k6ptMu1 μ r₁ hr₁).support := hC1
  obtain ⟨-, hF2⟩ := k6pt_trickZ_keeps (k6ptMu1 μ r₁ hr₁) hC1' r₂ hr₂
  obtain ⟨p0, -⟩ := k6pt_exists_support μ
  obtain ⟨ya, hya⟩ := hF1 h₁ a p0.2.2
  obtain ⟨yb, hyb⟩ := hF1 h₁ b p0.2.2
  have hya' : (k6ptMu1 μ r₁ hr₁).prob (a, ya, p0.2.2) ≠ 0 := hya
  have hyb' : (k6ptMu1 μ r₁ hr₁).prob (b, yb, p0.2.2) ≠ 0 := hyb
  have hodd := k6pt_odd hr₂
  have hpos : ∀ x y, (k6ptMu1 μ r₁ hr₁).prob (x, y, p0.2.2) ≠ 0 →
      0 < pathWeight (k6ptViewZ (k6ptMu1 μ r₁ hr₁)) (2 ^ r₂ - 1) hodd (fun _ => p0.2.2) x y :=
    fun x y h => const_word_mem_pathWeight_pos _ hodd (by rw [k6ptViewZ_prob]; exact h)
  let zv : K6ptPhi μ r₁ hr₁ r₂ hr₂ := ⟨fun _ => p0.2.2, a, ya, (hpos a ya hya').ne'⟩
  have hzv : ∀ x y, (k6ptMu1 μ r₁ hr₁).prob (x, y, p0.2.2) ≠ 0 →
      (k6ptMu2 μ r₁ hr₁ r₂ hr₂).prob (x, y, zv) ≠ 0 := fun x y h => (hpos x y h).ne'
  obtain ⟨z', hz'⟩ := hF2 h₂ a yb
  have hz'' : (k6ptMu2 μ r₁ hr₁ r₂ hr₂).prob (a, yb, z') ≠ 0 := hz'
  refine ⟨yb, zv, ⟨⟨![a, a, b], yb, zv, ?_⟩, rfl, ?_⟩, ⟨⟨![b, a, a], yb, zv, ?_⟩, rfl, ?_⟩⟩
  · exact k6pt_pathWeight3_ne _ k6pt_odd_three hz'' hz'' (hzv b yb hyb')
  · exact k6pt_pathWeight3_ne _ k6pt_odd_three hz'' hz'' (hzv b yb hyb')
  · exact k6pt_pathWeight3_ne _ k6pt_odd_three (hzv b yb hyb') (hzv a ya hya') (hzv a ya hya')
  · exact k6pt_pathWeight3_ne _ k6pt_odd_three (hzv b yb hyb') (hzv a ya hya') (hzv a ya hya')

end K6ptSupport

section K6ptMuMinus
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W B C : Type} [Fintype W] [Fintype B] [Fintype C]
variable [DecidableEq W] [DecidableEq B] [DecidableEq C]

private lemma k6pt_decomp {Ω : Type} [Fintype Ω] (ρ μm : FinProb Ω)
    (hs : ∀ p, 0 < μm.prob p → 0 < ρ.prob p) :
    ∃ (α : ℝ) (ν : FinProb Ω), 0 < α ∧ α ≤ 1 ∧
      ∀ p, ρ.prob p = α * μm.prob p + (1 - α) * ν.prob p := by
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := ρ.sum_eq_one
    simp at this
  let g : Ω → ℝ := fun p => if μm.prob p = 0 then 1 else ρ.prob p / μm.prob p
  let α : ℝ := min 1 (Finset.univ.inf' Finset.univ_nonempty g)
  have hgpos : ∀ p, 0 < g p := by
    intro p
    by_cases h : μm.prob p = 0
    · simp [g, h]
    · have hμ : 0 < μm.prob p := lt_of_le_of_ne (μm.nonneg p) (Ne.symm h)
      simp only [g, h, ite_false]
      exact div_pos (hs p hμ) hμ
  have hα0 : 0 < α := lt_min one_pos ((Finset.lt_inf'_iff _).2 fun p _ => hgpos p)
  have hα1 : α ≤ 1 := min_le_left _ _
  have hle : ∀ p, α * μm.prob p ≤ ρ.prob p := by
    intro p
    by_cases h : μm.prob p = 0
    · simp [h, ρ.nonneg p]
    · have hμ : 0 < μm.prob p := lt_of_le_of_ne (μm.nonneg p) (Ne.symm h)
      have h1 : α ≤ ρ.prob p / μm.prob p :=
        calc α ≤ Finset.univ.inf' Finset.univ_nonempty g := min_le_right _ _
          _ ≤ g p := Finset.inf'_le _ (Finset.mem_univ p)
          _ = ρ.prob p / μm.prob p := by simp [g, h]
      calc α * μm.prob p ≤ (ρ.prob p / μm.prob p) * μm.prob p := by gcongr
        _ = ρ.prob p := by field_simp
  by_cases hα : α = 1
  · have heq : ∀ p, ρ.prob p = μm.prob p := by
      have hsum : ∑ p, (ρ.prob p - μm.prob p) = 0 := by
        rw [Finset.sum_sub_distrib, ρ.sum_eq_one, μm.sum_eq_one]; ring
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun p _ => sub_nonneg.2 (by simpa [hα] using hle p))).1 hsum
      intro p
      have := this p (Finset.mem_univ p)
      linarith
    exact ⟨α, ρ, hα0, hα1, fun p => by rw [hα, heq p]; ring⟩
  · have hα' : 0 < 1 - α := sub_pos.2 (lt_of_le_of_ne hα1 hα)
    refine ⟨α, ⟨fun p => (ρ.prob p - α * μm.prob p) / (1 - α),
      fun p => div_nonneg (sub_nonneg.2 (hle p)) hα'.le, ?_⟩, hα0, hα1, fun p => ?_⟩
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ρ.sum_eq_one,
        μm.sum_eq_one, mul_one]
      exact div_self hα'.ne'
    · show ρ.prob p = α * μm.prob p + (1 - α) * ((ρ.prob p - α * μm.prob p) / (1 - α))
      field_simp
      ring

/-- the middle letter `c ∈ {a, b}` selected by the coin `e` (`c = a` if `e`, else `c = b`). -/
def k6ptMid (a b : X) (e : Bool) : X := if e then a else b

/-- CSP_6 `thm:toswap#mu-minus` (general form): given a distribution `ρ` on `W × B × C`
(`W` the label words, `lab` the word of an atom) all of whose pairs `(a,b)` satisfy the conclusion
of `lemma:suppmu`, the exchange-symmetric component `μ⁻` exists, with `ρ = α μ⁻ + (1-α) ν`,
`0 < α ≤ 1`. -/
theorem k6pt_mu_minus_of_supp (ρ : FinProb (W × B × C)) (lab : W → Fin 3 → X)
    (hlab : Function.Injective lab)
    (hsupp : ∀ a b : X, ∃ (y : B) (z : C),
      (∃ w, lab w = ![a, a, b] ∧ (w, y, z) ∈ ρ.support) ∧
      (∃ w, lab w = ![b, a, a] ∧ (w, y, z) ∈ ρ.support)) :
    ∃ (pt : X × X × Bool → W × B × C) (μm ν : FinProb (W × B × C)) (α : ℝ),
      0 < α ∧ α ≤ 1 ∧
      (∀ t : X × X × Bool,
        lab (pt t).1 = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1] ∧ pt t ∈ ρ.support ∧
        (∃ w', lab w' = ![t.2.1, k6ptMid t.1 t.2.1 t.2.2, t.1] ∧ (w', (pt t).2) ∈ ρ.support) ∧
        (pt (t.2.1, t.1, !t.2.2)).2 = (pt t).2) ∧
      (∀ p, μm.prob p =
        ((univ.filter fun t : X × X × Bool => pt t = p).card : ℝ) /
          (2 * (Fintype.card X : ℝ) ^ 2)) ∧
      (∀ (w w' : W) (y : B) (z : C), lab w' = ![lab w 2, lab w 1, lab w 0] →
        μm.prob (w', y, z) = μm.prob (w, y, z)) ∧
      (∀ a b : X, ∑ p ∈ univ.filter (fun p : W × B × C => lab p.1 0 = a ∧ lab p.1 2 = b),
        μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2) ∧
      (∀ p, ρ.prob p = α * μm.prob p + (1 - α) * ν.prob p) := by
  choose Sy Sz hyz using hsupp
  have key : ∀ t : X × X × Bool, ∃ w w' : W,
      lab w = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1] ∧
      lab w' = ![t.2.1, k6ptMid t.1 t.2.1 t.2.2, t.1] ∧
      (w, Sy (k6ptMid t.1 t.2.1 t.2.2) (k6ptMid t.2.1 t.1 t.2.2),
        Sz (k6ptMid t.1 t.2.1 t.2.2) (k6ptMid t.2.1 t.1 t.2.2)) ∈ ρ.support ∧
      (w', Sy (k6ptMid t.1 t.2.1 t.2.2) (k6ptMid t.2.1 t.1 t.2.2),
        Sz (k6ptMid t.1 t.2.1 t.2.2) (k6ptMid t.2.1 t.1 t.2.2)) ∈ ρ.support := by
    rintro ⟨a, b, e⟩
    cases e
    · obtain ⟨⟨w1, h1, m1⟩, ⟨w2, h2, m2⟩⟩ := hyz b a
      exact ⟨w2, w1, by simpa [k6ptMid] using h2, by simpa [k6ptMid] using h1,
        by simpa [k6ptMid] using m2, by simpa [k6ptMid] using m1⟩
    · obtain ⟨⟨w1, h1, m1⟩, ⟨w2, h2, m2⟩⟩ := hyz a b
      exact ⟨w1, w2, by simpa [k6ptMid] using h1, by simpa [k6ptMid] using h2,
        by simpa [k6ptMid] using m1, by simpa [k6ptMid] using m2⟩
  choose wp wq hwp hwq hmp hmq using key
  obtain ⟨pt, hpt1, hpt2, hpt3, hpt4⟩ : ∃ pt : X × X × Bool → W × B × C,
      (∀ t, lab (pt t).1 = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1]) ∧
      (∀ t, pt t ∈ ρ.support) ∧
      (∀ t, ∃ w', lab w' = ![t.2.1, k6ptMid t.1 t.2.1 t.2.2, t.1] ∧ (w', (pt t).2) ∈ ρ.support) ∧
      (∀ t, (pt (t.2.1, t.1, !t.2.2)).2 = (pt t).2) := by
    refine ⟨fun t => (wp t, Sy (k6ptMid t.1 t.2.1 t.2.2) (k6ptMid t.2.1 t.1 t.2.2),
      Sz (k6ptMid t.1 t.2.1 t.2.2) (k6ptMid t.2.1 t.1 t.2.2)), hwp, hmp,
      fun t => ⟨wq t, hwq t, hmq t⟩, ?_⟩
    rintro ⟨a, b, e⟩
    cases e <;> simp [k6ptMid]
  have hW : Nonempty (W × B × C) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := ρ.sum_eq_one
    simp at this
  have hXne : Nonempty X := ⟨lab hW.some.1 0⟩
  have hD : (0 : ℝ) < 2 * (Fintype.card X : ℝ) ^ 2 := by
    have : 0 < Fintype.card X := Fintype.card_pos
    positivity
  let μm : FinProb (W × B × C) :=
    { prob := fun p => ((univ.filter fun t : X × X × Bool => pt t = p).card : ℝ) /
        (2 * (Fintype.card X : ℝ) ^ 2)
      nonneg := fun p => div_nonneg (Nat.cast_nonneg _) hD.le
      sum_eq_one := by
        rw [← Finset.sum_div, ← Nat.cast_sum,
          ← Finset.card_eq_sum_card_fiberwise (f := pt) (s := univ) (t := univ)
            (fun _ _ => Finset.mem_univ _)]
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
        push_cast
        field_simp }
  have hμm : ∀ p, μm.prob p =
      ((univ.filter fun t : X × X × Bool => pt t = p).card : ℝ) /
        (2 * (Fintype.card X : ℝ) ^ 2) := fun p => rfl
  have hs : ∀ p, 0 < μm.prob p → 0 < ρ.prob p := by
    intro p hp
    rw [hμm, div_pos_iff_of_pos_right hD] at hp
    obtain ⟨t, ht⟩ := Finset.card_pos.1 (by exact_mod_cast hp)
    rw [Finset.mem_filter] at ht
    have := hpt2 t
    rw [ht.2] at this
    exact lt_of_le_of_ne (ρ.nonneg p) (Ne.symm this)
  obtain ⟨α, ν, hα0, hα1, hdec⟩ := k6pt_decomp ρ μm hs
  have hrev : ∀ w w' : W, lab w' = ![lab w 2, lab w 1, lab w 0] →
      lab w = ![lab w' 2, lab w' 1, lab w' 0] := by
    intro w w' h
    rw [h]
    funext i
    fin_cases i <;> rfl
  have hmidτ : ∀ t : X × X × Bool, k6ptMid t.2.1 t.1 (!t.2.2) = k6ptMid t.1 t.2.1 t.2.2 := by
    rintro ⟨a, b, e⟩
    cases e <;> rfl
  have claim : ∀ (w w' : W) (y : B) (z : C) (t : X × X × Bool),
      lab w' = ![lab w 2, lab w 1, lab w 0] → pt t = (w, y, z) →
      pt (t.2.1, t.1, !t.2.2) = (w', y, z) := by
    intro w w' y z t hw hpt
    have h1 : lab w = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1] := by
      rw [← hpt1 t, hpt]
    have h2 : lab w' = lab (pt (t.2.1, t.1, !t.2.2)).1 := by
      rw [hw, h1, hpt1, hmidτ]
      rfl
    have h3 : (pt (t.2.1, t.1, !t.2.2)).1 = w' := (hlab h2).symm
    have h4 : (pt (t.2.1, t.1, !t.2.2)).2 = (y, z) := by
      rw [hpt4, hpt]
    exact Prod.ext h3 h4
  have hcard : ∀ (w w' : W) (y : B) (z : C),
      lab w' = ![lab w 2, lab w 1, lab w 0] →
      (univ.filter fun t : X × X × Bool => pt t = (w', y, z)).card =
        (univ.filter fun t : X × X × Bool => pt t = (w, y, z)).card := by
    intro w w' y z hw
    refine Finset.card_bij (fun t _ => (t.2.1, t.1, !t.2.2)) ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨Finset.mem_univ _, claim w' w y z t (hrev w w' hw) ht.2⟩
    · rintro ⟨a, b, e⟩ _ ⟨a', b', e'⟩ _ h
      simp only [Prod.mk.injEq, Bool.not_inj_iff] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2
      simp [h3]
    · intro t ht
      rw [Finset.mem_filter] at ht
      refine ⟨(t.2.1, t.1, !t.2.2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, claim w w' y z t hw ht.2⟩
      · obtain ⟨a, b, e⟩ := t
        simp
  have h0 : ∀ t, lab (pt t).1 0 = t.1 := fun t => by rw [hpt1 t]; rfl
  have h2 : ∀ t, lab (pt t).1 2 = t.2.1 := fun t => by rw [hpt1 t]; rfl
  refine ⟨pt, μm, ν, α, hα0, hα1, fun t => ⟨hpt1 t, hpt2 t, hpt3 t, hpt4 t⟩, hμm, ?_, ?_, hdec⟩
  · rintro w w' y z hw
    rw [hμm, hμm, hcard w w' y z hw]
  · intro a b
    set F : Finset (W × B × C) := univ.filter (fun p => lab p.1 0 = a ∧ lab p.1 2 = b) with hF
    have hsum : ∑ p ∈ F, (univ.filter fun t : X × X × Bool => pt t = p).card =
        (univ.filter fun t : X × X × Bool => pt t ∈ F).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := pt) (s := univ.filter fun t : X × X × Bool => pt t ∈ F)
        (t := F) (fun t ht => (Finset.mem_filter.1 ht).2)]
      refine Finset.sum_congr rfl fun p hp => ?_
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨by rw [h]; exact hp, h⟩
      · exact fun h => h.2
    have hset : (univ.filter fun t : X × X × Bool => pt t ∈ F) = {(a, b, true), (a, b, false)} := by
      ext ⟨a', b', e⟩
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, h0, h2, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      cases e <;> simp [eq_comm]
    have hc : (univ.filter fun t : X × X × Bool => pt t ∈ F).card = 2 := by
      rw [hset]
      simp
    simp only [hμm]
    rw [← Finset.sum_div, ← Nat.cast_sum, hsum, hc]
    have : (Fintype.card X : ℝ) ≠ 0 := by
      have : 0 < Fintype.card X := Fintype.card_pos
      positivity
    push_cast
    field_simp

end K6ptMuMinus

section K6ptMuMinusK6
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- CSP_6 `thm:toswap#mu-minus` for `μ⁺` of `eq:3path` (hypotheses of `lemma:suppmu`). -/
theorem k6pt_mu_minus (μ : FinProb (X × Y × Z)) (hμ : PairwiseConnected3 μ.support)
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (h₁ : Fintype.card X + Fintype.card Z ≤ 2 ^ r₁)
    (h₂ : Fintype.card X + Fintype.card (K6ptGam μ r₁ hr₁) ≤ 2 ^ r₂) :
    ∃ (pt : X × X × Bool → K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂)
      (μm ν : FinProb (K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ × K6ptPhi μ r₁ hr₁ r₂ hr₂))
      (α : ℝ),
      0 < α ∧ α ≤ 1 ∧
      (∀ t : X × X × Bool,
        (pt t).1.1 = ![t.1, k6ptMid t.1 t.2.1 t.2.2, t.2.1] ∧
        pt t ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support ∧
        (∃ w' : K6ptSig μ r₁ hr₁ r₂ hr₂, w'.1 = ![t.2.1, k6ptMid t.1 t.2.1 t.2.2, t.1] ∧
          (w', (pt t).2) ∈ (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).support) ∧
        (pt (t.2.1, t.1, !t.2.2)).2 = (pt t).2) ∧
      (∀ p, μm.prob p =
        ((univ.filter fun t : X × X × Bool => pt t = p).card : ℝ) /
          (2 * (Fintype.card X : ℝ) ^ 2)) ∧
      (∀ (w w' : K6ptSig μ r₁ hr₁ r₂ hr₂) (y : K6ptGam μ r₁ hr₁)
          (z : K6ptPhi μ r₁ hr₁ r₂ hr₂),
        w'.1 = ![w.1 2, w.1 1, w.1 0] → μm.prob (w', y, z) = μm.prob (w, y, z)) ∧
      (∀ a b : X, ∑ p ∈ univ.filter (fun p : K6ptSig μ r₁ hr₁ r₂ hr₂ × K6ptGam μ r₁ hr₁ ×
          K6ptPhi μ r₁ hr₁ r₂ hr₂ => p.1.1 0 = a ∧ p.1.1 2 = b),
        μm.prob p = 1 / (Fintype.card X : ℝ) ^ 2) ∧
      (∀ p, (k6ptMuPlus μ r₁ hr₁ r₂ hr₂).prob p = α * μm.prob p + (1 - α) * ν.prob p) := by
  exact k6pt_mu_minus_of_supp (k6ptMuPlus μ r₁ hr₁ r₂ hr₂) (fun w => w.1) Subtype.val_injective
    (fun a b => k6pt_suppmu μ hμ hr₁ hr₂ h₁ h₂ a b)

end K6ptMuMinusK6

end TrackB
end RestrictedPolynomials
end
