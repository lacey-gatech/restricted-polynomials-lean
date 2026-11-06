module

public import RestrictedPolynomials.TrackB.K7KcspLemma
public import RestrictedPolynomials.TrackB.K7KcspReplace
public import RestrictedPolynomials.TrackB.K7KcspTower
public import RestrictedPolynomials.TrackB.MaxTStatements
public import RestrictedPolynomials.Frozen.InverseDelta
public import RestrictedPolynomials.ExpIterate

/-!
# Track B: the assembly of CSP_7 `thm:kcsp` and the frozen bridge

Source: CSP_7, l. 453-458 (`thm:3csp_bkm2`), l. 782-790 (`thm:kcsp`, `#k-at-most-2`,
`#uniformize-delta`); the paper's `t-inverse#near-one-regime`.
Formalization choices: `hbase` is explicit (`δ ≤ c ε^b`) and there is no `n`-threshold (frozen `n₀ = 0`).

This file holds the four declarations that do not take `hconv`:
* `k7_valid_mono` (`#uniformize-delta`, the monotone half);
* `k7_kcsp_three_of_bkm2` (base `k = 3`, from `hbase`);
* `k7_kcsp_small_k_of_bkm2` (`k ≤ 2`, padding with singleton alphabets);
* `k7_frozen_of_small_eps` (the near-one regime; it takes the small-`ε` theorem `hT` only, and its
  conclusion is the statement of the frozen `inverse_theorem_bklm`).

The three declarations `k7_kcsp_step_of_conv`, `k7_thm_kcsp_of_conv_of_bkm2` and
`k7_small_eps_exact_of_conv_of_bkm2` take the hypothesis `hconv` (CSP_7 `lemma:kcsp#convert-to-mu1`).
The proof does not need `hconv`, so they are NOT in this file; see `K7KcspFinal` for the form
without it.

Routes. The base case transports the `Fin 3`-indexed family to `A 0 × A 1 × A 2` (`mergePush` along
an injective map, so atoms, marginals and the absence of embeddings are unchanged), reduces an
arbitrary index type to `Fin n` by `padding_removes_large_n` with `n₀ = 0`, and converts the rate:
`exp(-ε^{-b'}) ≤ ε^{b'} ≤ c ε^b` for `b' = b + N`, `(1/2)^N < c`. The cases `k ≤ 2` pad with `Unit`.
The frozen bridge follows the near-one argument with natural-number exponents: `T` with
`(1-δ₁)^T ≤ 1-δ_*`, `K` with `δ_*^K < δ₁`, `M = T K`, `b = b_s M`, where `δ₁ = δ_s(1/4)` and
`δ_* = exp(-exp^{[N]} 1)`; for `ε ∈ (1/2, 1]` with `δ(ε) > δ₁` the tensor power `f^{⊗M}`
(`cstab_tensorPow`, `cexpect_pi_tensorPow`) and log-convexity (`cstab_log_convex`) give
`Stab_{1-δ(ε)}(f) ≥ (Stab_{1-δ₁} f)^T > δ_*`. All proof helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Assembly

/-! ### Stability helpers -/

section StabHelpers

variable {B : Type} [Fintype B] [DecidableEq B] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem asm_re_cstab_mono (π : FinProb B) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ')
    (f : (ι → B) → ℂ) : (cstab π ρ f).re ≤ (cstab π ρ' f).re := by
  rw [re_cstab_eq, re_cstab_eq]
  exact sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h _)
    (cw_nonneg π S f)

private theorem asm_re_cstab_nonneg (π : FinProb B) {ρ : ℝ} (h0 : 0 ≤ ρ) (f : (ι → B) → ℂ) :
    0 ≤ (cstab π ρ f).re := by
  rw [re_cstab_eq]
  exact sum_nonneg fun S _ => mul_nonneg (pow_nonneg h0 _) (cw_nonneg π S f)

open scoped ComplexOrder in
private theorem asm_ofReal_le_cstab_iff (π : FinProb B) (ρ : ℝ) (f : (ι → B) → ℂ) (δ : ℝ) :
    (δ : ℂ) ≤ cstab π ρ f ↔ δ ≤ (cstab π ρ f).re := by
  rw [Complex.le_def, Complex.ofReal_re, Complex.ofReal_im, cstab_im_eq_zero]
  simp

omit [DecidableEq B] in
private theorem asm_cl2sq_le_one (π : FinProb B) (f : (ι → B) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    cl2sq π f ≤ 1 := by
  unfold cl2sq
  exact FinProb.expect_le_const _ fun x => pow_le_one₀ (norm_nonneg _) (hf x)

end StabHelpers

/-- CSP_7 `thm:kcsp#uniformize-delta` (the monotone half): a valid `δ` stays valid when lowered
(`Stab_{1-δ''} ≥ Stab_{1-δ} ≥ δ ≥ δ''`, `cstab_mono`), pointwise in the function. -/
theorem k7_valid_mono {B : Type} [Fintype B] [DecidableEq B] {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : FinProb B) (f : (ι → B) → ℂ) {δ δ'' : ℝ} (hδ0 : 0 < δ'') (hδ : δ'' ≤ δ) (hδ1 : δ ≤ 1)
    (h : δ ≤ (cstab π (1 - δ) f).re) : δ'' ≤ (cstab π (1 - δ'') f).re := by
  have _ := hδ0
  have hm := asm_re_cstab_mono π (by linarith : 0 ≤ 1 - δ) (by linarith : 1 - δ ≤ 1 - δ'') f
  linarith

/-! ### Push-forward helpers (copies of private lemmas of `MaxTStatements`) -/

section Push

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]

private theorem asm_finProb_ext {γ : Type} [Fintype γ] {π π' : FinProb γ}
    (h : ∀ a, π.prob a = π'.prob a) : π = π' := by
  cases π
  cases π'
  congr
  funext a
  exact h a

private theorem asm_push_sum {ι : Type} [Fintype ι] [DecidableEq ι] (a : α → β) (w : ι → α → ℝ)
    (G : (ι → β) → ℂ) :
    ∑ x : ι → α, ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)) =
    ∑ b : ι → β, ((∏ i, ∑ c ∈ univ.filter (fun c => a c = b i), w i c : ℝ) : ℂ) * G b := by
  rw [← Finset.sum_fiberwise univ (fun x : ι → α => fun i => a (x i))
    (fun x => ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ x ∈ univ.filter (fun x : ι → α => (fun i => a (x i)) = b),
      ((∏ i, w i (x i) : ℝ) : ℂ) * G (fun i => a (x i)) = ((∏ i, w i (x i) : ℝ) : ℂ) * G b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Fintype.mem_piFinset, funext_iff]

private theorem asm_cexpect_pi_push {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α)
    (a : α → β) (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (asm_push_sum a (fun _ c => π.prob c) G).symm

private theorem asm_mergePush_comp {γ : Type} [Fintype γ] [DecidableEq γ] (π : FinProb α)
    (f : α → β) (g : β → γ) : mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine asm_finProb_ext fun c => ?_
  show ∑ b ∈ univ.filter (fun b => g b = c), ∑ a ∈ univ.filter (fun a => f a = b), π.prob a =
    ∑ a ∈ univ.filter (fun a => g (f a) = c), π.prob a
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun a => g (f a) = c))
    (t := univ.filter (fun b => g b = c)) (g := f) (f := π.prob)
    (fun a ha => by simpa using ha)]
  refine Finset.sum_congr rfl fun b hb => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  have hb' : g b = c := (Finset.mem_filter.1 hb).2
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ hb', h⟩, fun h => h.2⟩

private theorem asm_mergePush_prob_inj (π : FinProb α) (f : α → β) (hf : Function.Injective f)
    (a : α) : (mergePush π f).prob (f a) = π.prob a := by
  classical
  show ∑ a' ∈ univ.filter (fun a' => f a' = f a), π.prob a' = _
  rw [Finset.filter_congr (q := fun a' => a' = a) (fun a' _ => hf.eq_iff)]
  rw [Finset.filter_eq' univ a]
  simp

private theorem asm_mem_supp_push (π : FinProb α) (f : α → β) (b : β) :
    b ∈ (mergePush π f).support ↔ ∃ a, f a = b ∧ a ∈ π.support := by
  show (∑ a ∈ Finset.univ.filter (fun a => f a = b), π.prob a) ≠ 0 ↔ _
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun a _ => π.nonneg a]
  push Not
  constructor
  · rintro ⟨a, ha, hne⟩
    exact ⟨a, (Finset.mem_filter.1 ha).2, hne⟩
  · rintro ⟨a, hfa, hne⟩
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfa⟩, hne⟩

private theorem asm_supp_push_eq (π : FinProb α) (f : α → β) :
    (mergePush π f).support = f '' π.support := by
  ext b
  rw [asm_mem_supp_push]
  constructor
  · rintro ⟨a, hfa, ha⟩
    exact ⟨a, ha, hfa⟩
  · rintro ⟨a, ha, hfa⟩
    exact ⟨a, hfa, ha⟩

private theorem asm_push_atoms (π : FinProb α) (f : α → β) (hf : Function.Injective f) {a : ℝ}
    (h : ∀ x ∈ π.support, a ≤ π.prob x) :
    ∀ y ∈ (mergePush π f).support, a ≤ (mergePush π f).prob y := by
  intro y hy
  obtain ⟨x, rfl, hx⟩ := (asm_mem_supp_push π f y).1 hy
  rw [asm_mergePush_prob_inj π f hf x]
  exact h x hx

end Push

/-- the marginal of a push-forward along a map that remembers coordinate `j`. -/
private theorem asm_marginal_push {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] {β : Type} [Fintype β] [DecidableEq β] (μ : FinProb (∀ i, A i))
    (q : (∀ i, A i) → β) (j : Fin k) (r : β → A j) (h : ∀ t, r (q t) = t j) :
    mergePush (mergePush μ q) r = μ.marginalPi j := by
  rw [asm_mergePush_comp]
  refine asm_finProb_ext fun a => ?_
  show ∑ t ∈ univ.filter (fun t => r (q t) = a), μ.prob t = ∑ t ∈ univ.filter (fun t => t j = a), μ.prob t
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]

/-! ### Ternary transport: no embedding, pairwise connectedness, alphabet bounds -/

section Tern

variable {X Y Z : Type}

private instance asmTriFintype (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (i : Fin 3) :
    Fintype (Tri X Y Z i) :=
  match i with
  | 0 => (inferInstance : Fintype X)
  | 1 => (inferInstance : Fintype Y)
  | 2 => (inferInstance : Fintype Z)

private instance asmTriDecEq (X Y Z : Type) [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (i : Fin 3) : DecidableEq (Tri X Y Z i) :=
  match i with
  | 0 => (inferInstance : DecidableEq X)
  | 1 => (inferInstance : DecidableEq Y)
  | 2 => (inferInstance : DecidableEq Z)

private theorem asm_ofProd_inj :
    Function.Injective (Tri.ofProd : X × Y × Z → ∀ i, Tri X Y Z i) := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- pairwise connectedness and `|alphabet| ≤ ⌈1/α⌉` from the atom bound and the absence of
embeddings (the argument of `K7BaseCase`, whose helper is private). -/
private theorem asm_pc_card [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (μ : FinProb (X × Y × Z)) {α : ℝ} (hα : 0 < α)
    (hat : ∀ p ∈ μ.support, α ≤ μ.prob p) (hna : ¬ AdmitsAbelianEmbedding3 μ.support) :
    PairwiseConnected3 μ.support ∧ Fintype.card X ≤ ⌈1 / α⌉₊ ∧ Fintype.card Y ≤ ⌈1 / α⌉₊ ∧
      Fintype.card Z ≤ ⌈1 / α⌉₊ := by
  classical
  set ν := mergePush μ (Tri.ofProd : X × Y × Z → ∀ i, Tri X Y Z i) with hν
  have hsupp : ν.support = Tri.ofProd '' μ.support := asm_supp_push_eq μ _
  have hno : NoNontrivialAbelianEmbeddingPi ν.support := by
    rw [hsupp]; exact (noNontrivialAbelianEmbeddingPi_iff_3 _).2 hna
  have hatν : ∀ q ∈ ν.support, α ≤ ν.prob q := asm_push_atoms μ _ asm_ofProd_inj hat
  have hpc := pairwiseConnected_of_noNontrivialAbelianEmbeddingPi ν hno
  have hpc3 : PairwiseConnected3 μ.support := by
    unfold PairwiseConnected3
    rw [← hsupp]; exact hpc
  have hc : ∀ i : Fin 3, (Fintype.card (Tri X Y Z i) : ℝ) ≤ 1 / α :=
    fun i => card_le_inv_of_atom_bound ν hno hα hatν i
  have hcn : ∀ n : ℕ, (n : ℝ) ≤ 1 / α → n ≤ ⌈1 / α⌉₊ := fun n hn =>
    Nat.cast_le.1 (hn.trans (Nat.le_ceil _))
  exact ⟨hpc3, hcn _ (hc 0), hcn _ (hc 1), hcn _ (hc 2)⟩

/-- the absence of abelian embeddings transported along `q : (∀ i, A i) → X × Y × Z`, given a way to
turn a ternary embedding into a `k`-ary one with the same sums. -/
private theorem asm_noEmb_push {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (μ : FinProb (∀ i, A i)) (q : (∀ i, A i) → X × Y × Z)
    (hno : NoNontrivialAbelianEmbeddingPi μ.support)
    (H : ∀ (G : Type) [AddCommGroup G] (σ : X → G) (γ : Y → G) (φ : Z → G),
      ∃ τ : ∀ i, A i → G, (∀ t, ∑ i, τ i (t i) = σ (q t).1 + γ (q t).2.1 + φ (q t).2.2) ∧
        ((∀ i (x y : A i), τ i x = τ i y) →
          (∀ a b, σ a = σ b) ∧ (∀ a b, γ a = γ b) ∧ (∀ a b, φ a = φ b))) :
    ¬ AdmitsAbelianEmbedding3 (mergePush μ q).support := by
  rintro ⟨G, _, hG⟩
  obtain ⟨σ, γ, φ, h1, h2⟩ := (admitsEmbeddingInto3_iff _ G).1 hG
  rw [isEmbedding3_iff] at h1
  rw [isNontrivialEmbedding3_iff] at h2
  obtain ⟨τ, hτ, hconst⟩ := H G σ γ φ
  apply h2
  refine hconst fun i x y => hno G τ (fun t ht => ?_) i x y
  rw [hτ]
  exact h1 (q t) ((asm_mem_supp_push μ q (q t)).2 ⟨t, rfl, ht⟩)

end Tern

/-! ### The ternary base case in rate form -/

/-- the base case `k = 3` in ternary form with the rate `δ ≤ exp(-ε^{-b})`: from `hbase` at
`m = ⌈1/α⌉` (`b = b₀ + N` with `(1/2)^N < c`, and `exp(-x) ≤ 1/x`), the alphabet bound and pairwise
connectedness being derived from the atom bound and the absence of embeddings. -/
private theorem asm_three_core
    (hbase : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∃ (b c : ℝ), 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
          [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
          ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ c * ε ^ b →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖MaxT.corr3 μ f g h‖ →
            δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re)
    {α : ℝ} (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ δ : ℝ, 0 < δ → δ ≤ Real.exp (-(ε ^ (-b))) →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z] (μ : FinProb (X × Y × Z)), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ¬ AdmitsAbelianEmbedding3 μ.support →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          ε ≤ ‖MaxT.corr3 μ f g h‖ →
          δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
            δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re := by
  obtain ⟨b, c, hb, hc, _hc1, H⟩ := hbase ⌈1 / α⌉₊ hα
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨b + N, add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg N), ?_⟩
  intro ε hε hε2 δ hδ hδle X Y Z _ _ _ _ _ _ μ hat hna n f g h hf hg hh hcorr
  have hx : 0 < ε ^ (-(b + N)) := Real.rpow_pos_of_pos hε _
  have hδc : δ ≤ c * ε ^ b := by
    have h1 : Real.exp (-(ε ^ (-(b + N)))) ≤ (ε ^ (-(b + N)))⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hx (by linarith [Real.add_one_le_exp (ε ^ (-(b + N)))])
    have h2 : (ε ^ (-(b + (N : ℝ))))⁻¹ = ε ^ b * ε ^ N := by
      rw [Real.rpow_neg hε.le, inv_inv, Real.rpow_add hε, Real.rpow_natCast]
    have h3 : ε ^ N ≤ c := (pow_le_pow_left₀ hε.le hε2 N).trans hN.le
    have h4 : 0 ≤ ε ^ b := Real.rpow_nonneg hε.le _
    calc δ ≤ Real.exp (-(ε ^ (-(b + N)))) := hδle
      _ ≤ ε ^ b * ε ^ N := h1.trans h2.le
      _ ≤ ε ^ b * c := mul_le_mul_of_nonneg_left h3 h4
      _ = c * ε ^ b := mul_comm _ _
  obtain ⟨hpc, hX, hY, hZ⟩ := asm_pc_card μ hα hat hna
  exact H ε hε (by linarith) X Y Z hX hY hZ μ hat hpc hna δ hδ hδc n f g h hf hg hh hcorr

private theorem asm_exp_neg_rpow_lt_one {ε b : ℝ} (hε : 0 < ε) :
    Real.exp (-(ε ^ (-b))) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.rpow_pos_of_pos hε _))

/-- CSP_7 `thm:kcsp` base `k = 3` in the `Fin 3`-indexed form (`thm:3csp-bkm2`; the transport
`(∀ i : Fin 3, A i) ≃ A 0 × A 1 × A 2` with `FinProb` push-forward, and `Fin n` versus an arbitrary finite
index type through `cstab_equiv`, `cexpect_pi_equiv`; the alphabets have `|Aᵢ| ≤ 1/α`,
`card_le_inv_of_atom_bound`). `hbase` is the explicit-quantitative form of `k7_thm_3csp_bkm2_of_Q`
: `δ ≤ c ε^b` instead of an unspecified `δ₀`. -/
theorem k7_kcsp_three_of_bkm2
    (hbase : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∃ (b c : ℝ), 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
          [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
          ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ c * ε ^ b →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖MaxT.corr3 μ f g h‖ →
            δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re)
    {α : ℝ} (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin 3 → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[k7Height 3] (ε ^ (-b)))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[k7Height 3] (ε ^ (-b))))) (f i)).re) := by
  obtain ⟨b, hb, H⟩ := asm_three_core hbase hα
  refine ⟨b, hb, fun ε hε hε2 A _ _ μ hno hat => ?_⟩
  have hδe : Real.exp (-(Real.exp^[k7Height 3] (ε ^ (-b)))) = Real.exp (-(ε ^ (-b))) := rfl
  rw [hδe]
  have hδ0 : 0 < Real.exp (-(ε ^ (-b))) := Real.exp_pos _
  have hδ1 := asm_exp_neg_rpow_lt_one (b := b) hε
  have hfin : ∀ n : ℕ, 0 ≤ n → ∀ f : ∀ i, (Fin n → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
      ε ≤ ‖(μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i‖ →
      ∀ i, Real.exp (-(ε ^ (-b))) ≤
        (cstab (μ.marginalPi i) (1 - Real.exp (-(ε ^ (-b)))) (f i)).re := by
    intro n _ f hf hcorr i
    let q : (∀ i, A i) → A 0 × A 1 × A 2 := fun t => (t 0, t 1, t 2)
    have hq : Function.Injective q := by
      intro t t' htt
      simp only [q, Prod.mk.injEq] at htt
      obtain ⟨e0, e1, e2⟩ := htt
      funext j
      fin_cases j
      · exact e0
      · exact e1
      · exact e2
    have hna : ¬ AdmitsAbelianEmbedding3 (mergePush μ q).support := by
      refine asm_noEmb_push μ q hno fun G _ σ γ φ => ?_
      refine ⟨fun j => match j with
        | 0 => σ
        | 1 => γ
        | 2 => φ, fun t => ?_, fun hc => ⟨hc 0, hc 1, hc 2⟩⟩
      rw [Fin.sum_univ_three]
    have hc3 : MaxT.corr3 (mergePush μ q) (f 0) (f 1) (f 2) =
        (μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i := by
      unfold MaxT.corr3
      rw [asm_cexpect_pi_push]
      congr 1
      funext X
      rw [Fin.prod_univ_three]
    obtain ⟨h0, h1, h2⟩ := H ε hε hε2 _ hδ0 le_rfl (A 0) (A 1) (A 2) (mergePush μ q)
      (asm_push_atoms μ q hq hat) hna n (f 0) (f 1) (f 2) (hf 0) (hf 1) (hf 2) (by rw [hc3]; exact hcorr)
    rw [show MaxT.lawX (mergePush μ q) = μ.marginalPi 0 from
      asm_marginal_push μ q 0 (fun p => p.1) fun _ => rfl] at h0
    rw [show MaxT.lawY (mergePush μ q) = μ.marginalPi 1 from
      asm_marginal_push μ q 1 (fun p => p.2.1) fun _ => rfl] at h1
    rw [show MaxT.lawZ (mergePush μ q) = μ.marginalPi 2 from
      asm_marginal_push μ q 2 (fun p => p.2.2) fun _ => rfl] at h2
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  intro ι _ _ f hf hcorr i
  exact (asm_ofReal_le_cstab_iff _ _ _ _).1
    (padding_removes_large_n A μ hε hδ0 hδ1 0
      (fun n hn f hf hc i => (asm_ofReal_le_cstab_iff _ _ _ _).2 (hfin n hn f hf hc i))
      ι f hf hcorr i)

/-- CSP_7 `thm:kcsp#k-at-most-2` (padding with singleton alphabets, `μ' = μ ⊗ δ_⋆ (⊗ δ_⋆)`, `f'ᵢ = 1`;
the atom masses, the correlation, the marginals and the absence of abelian embeddings are unchanged;
`k = 0` is vacuous). -/
theorem k7_kcsp_small_k_of_bkm2
    (hbase : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∃ (b c : ℝ), 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
          [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
          ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
          PairwiseConnected3 μ.support → ¬ AdmitsAbelianEmbedding3 μ.support →
          ∀ δ : ℝ, 0 < δ → δ ≤ c * ε ^ b →
          ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
            (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
            ε ≤ ‖MaxT.corr3 μ f g h‖ →
            δ ≤ (cstab (MaxT.lawX μ) (1 - δ) f).re ∧ δ ≤ (cstab (MaxT.lawY μ) (1 - δ) g).re ∧
              δ ≤ (cstab (MaxT.lawZ μ) (1 - δ) h).re)
    (k : ℕ) (hk : k ≤ 2) {α : ℝ} (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[0] (ε ^ (-b)))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[0] (ε ^ (-b))))) (f i)).re) := by
  obtain ⟨b, hb, H⟩ := asm_three_core hbase hα
  have hone : ∀ (n : ℕ) (z : Fin n → Unit), ‖(fun _ => (1 : ℂ)) z‖ ≤ 1 := fun _ _ => by simp
  interval_cases k
  · exact ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i => i.elim0⟩
  · refine ⟨b, hb, fun ε hε hε2 A _ _ μ hno hat => ?_⟩
    have hδe : Real.exp (-(Real.exp^[0] (ε ^ (-b)))) = Real.exp (-(ε ^ (-b))) := rfl
    rw [hδe]
    have hδ0 : 0 < Real.exp (-(ε ^ (-b))) := Real.exp_pos _
    have hδ1 := asm_exp_neg_rpow_lt_one (b := b) hε
    have hfin : ∀ n : ℕ, 0 ≤ n → ∀ f : ∀ i, (Fin n → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
        ε ≤ ‖(μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i‖ →
        ∀ i, Real.exp (-(ε ^ (-b))) ≤
          (cstab (μ.marginalPi i) (1 - Real.exp (-(ε ^ (-b)))) (f i)).re := by
      intro n _ f hf hcorr i
      let q : (∀ i, A i) → A 0 × Unit × Unit := fun t => (t 0, (), ())
      have hq : Function.Injective q := by
        intro t t' htt
        simp only [q, Prod.mk.injEq] at htt
        funext j
        fin_cases j
        exact htt.1
      have hna : ¬ AdmitsAbelianEmbedding3 (mergePush μ q).support := by
        refine asm_noEmb_push μ q hno fun G _ σ γ φ => ?_
        refine ⟨fun j => match j with
          | 0 => fun x => σ x + γ () + φ (), fun t => ?_, fun hc => ⟨fun a b' => ?_,
            fun a b' => by cases a; cases b'; rfl, fun a b' => by cases a; cases b'; rfl⟩⟩
        · rw [Fin.sum_univ_one]
        · exact add_right_cancel (add_right_cancel (hc 0 a b'))
      have hc3 : MaxT.corr3 (mergePush μ q) (f 0) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) =
          (μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i := by
        unfold MaxT.corr3
        rw [asm_cexpect_pi_push]
        congr 1
        funext X
        rw [Fin.prod_univ_one, mul_one, mul_one]
      obtain ⟨h0, -, -⟩ := H ε hε hε2 _ hδ0 le_rfl (A 0) Unit Unit (mergePush μ q)
        (asm_push_atoms μ q hq hat) hna n (f 0) (fun _ => 1) (fun _ => 1) (hf 0) (hone n)
        (hone n) (by rw [hc3]; exact hcorr)
      rw [show MaxT.lawX (mergePush μ q) = μ.marginalPi 0 from
        asm_marginal_push μ q 0 (fun p => p.1) fun _ => rfl] at h0
      fin_cases i
      exact h0
    intro ι _ _ f hf hcorr i
    exact (asm_ofReal_le_cstab_iff _ _ _ _).1
      (padding_removes_large_n A μ hε hδ0 hδ1 0
        (fun n hn f hf hc i => (asm_ofReal_le_cstab_iff _ _ _ _).2 (hfin n hn f hf hc i))
        ι f hf hcorr i)
  · refine ⟨b, hb, fun ε hε hε2 A _ _ μ hno hat => ?_⟩
    have hδe : Real.exp (-(Real.exp^[0] (ε ^ (-b)))) = Real.exp (-(ε ^ (-b))) := rfl
    rw [hδe]
    have hδ0 : 0 < Real.exp (-(ε ^ (-b))) := Real.exp_pos _
    have hδ1 := asm_exp_neg_rpow_lt_one (b := b) hε
    have hfin : ∀ n : ℕ, 0 ≤ n → ∀ f : ∀ i, (Fin n → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
        ε ≤ ‖(μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i‖ →
        ∀ i, Real.exp (-(ε ^ (-b))) ≤
          (cstab (μ.marginalPi i) (1 - Real.exp (-(ε ^ (-b)))) (f i)).re := by
      intro n _ f hf hcorr i
      let q : (∀ i, A i) → A 0 × A 1 × Unit := fun t => (t 0, t 1, ())
      have hq : Function.Injective q := by
        intro t t' htt
        simp only [q, Prod.mk.injEq] at htt
        funext j
        fin_cases j
        · exact htt.1
        · exact htt.2.1
      have hna : ¬ AdmitsAbelianEmbedding3 (mergePush μ q).support := by
        refine asm_noEmb_push μ q hno fun G _ σ γ φ => ?_
        refine ⟨fun j => match j with
          | 0 => σ
          | 1 => fun y => γ y + φ (), fun t => ?_, fun hc => ⟨hc 0,
            fun a b' => add_right_cancel (hc 1 a b'), fun a b' => by cases a; cases b'; rfl⟩⟩
        rw [Fin.sum_univ_two]
        exact (add_assoc _ _ _).symm
      have hc3 : MaxT.corr3 (mergePush μ q) (f 0) (f 1) (fun _ => (1 : ℂ)) =
          (μ.pi (Fin n)).cexpect fun X => ∏ i, f i fun t => X t i := by
        unfold MaxT.corr3
        rw [asm_cexpect_pi_push]
        congr 1
        funext X
        rw [Fin.prod_univ_two, mul_one]
      obtain ⟨h0, h1, -⟩ := H ε hε hε2 _ hδ0 le_rfl (A 0) (A 1) Unit (mergePush μ q)
        (asm_push_atoms μ q hq hat) hna n (f 0) (f 1) (fun _ => 1) (hf 0) (hf 1)
        (hone n) (by rw [hc3]; exact hcorr)
      rw [show MaxT.lawX (mergePush μ q) = μ.marginalPi 0 from
        asm_marginal_push μ q 0 (fun p => p.1) fun _ => rfl] at h0
      rw [show MaxT.lawY (mergePush μ q) = μ.marginalPi 1 from
        asm_marginal_push μ q 1 (fun p => p.2.1) fun _ => rfl] at h1
      fin_cases i
      · exact h0
      · exact h1
    intro ι _ _ f hf hcorr i
    exact (asm_ofReal_le_cstab_iff _ _ _ _).1
      (padding_removes_large_n A μ hε hδ0 hδ1 0
        (fun n hn f hf hc i => (asm_ofReal_le_cstab_iff _ _ _ _).2 (hfin n hn f hf hc i))
        ι f hf hcorr i)

/-! ### The near-one regime and the frozen bridge -/

/-- `‖𝔼 ∏ᵢ fᵢ‖ ≤ 1` for `1`-bounded functions (so `ε > 1` is void). -/
private theorem asm_norm_corr_le_one {k : ℕ} {A : Fin k → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] (μ : FinProb (∀ i, A i)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ∀ i, (ι → A i) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ ≤ 1 := by
  unfold FinProb.cexpect
  calc ‖∑ x, ((μ.pi ι).prob x : ℂ) * ∏ i, f i fun t => x t i‖
        ≤ ∑ x, ‖((μ.pi ι).prob x : ℂ) * ∏ i, f i fun t => x t i‖ := norm_sum_le _ _
    _ ≤ ∑ x, (μ.pi ι).prob x := sum_le_sum fun x _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ((μ.pi ι).nonneg x), norm_prod]
        exact mul_le_of_le_one_right ((μ.pi ι).nonneg x)
          (prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hf i _)
    _ = 1 := (μ.pi ι).sum_eq_one

open scoped ComplexOrder in
/-- The paper's `t-inverse#near-one-regime` (tensor power
`tensorPow`, `cstab_tensorPow`, `cexpect_pi_tensorPow`, log-convexity `cstab_log_convex`) and the form of
the paper's `t-inverse`: the small-`ε` theorem `T` (here with `n₀ = 0`) gives the frozen statement for every
`ε > 0` (for `ε > 1` the correlation hypothesis is void). The conclusion is the statement of
`inverse_theorem_bklm`. -/
theorem k7_frozen_of_small_eps
    (hT : ∃ C₀ : ℕ, ∀ k : ℕ, ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, γ ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, (inverseDelta C₀ k b ε : ℂ) ≤
            cstab (μ.marginalPi i) (1 - inverseDelta C₀ k b ε) (f i)) :
    ∃ C₀ : ℕ, ∀ k : ℕ, ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)),
        NoNontrivialAbelianEmbeddingPi μ.support → (∀ a ∈ μ.support, γ ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], n₀ ≤ Fintype.card ι →
        ∀ f : ∀ i, (ι → A i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, (inverseDelta C₀ k b ε : ℂ) ≤
            cstab (μ.marginalPi i) (1 - inverseDelta C₀ k b ε) (f i) := by
  obtain ⟨C₀, hT⟩ := hT
  refine ⟨C₀, fun k γ hγ => ?_⟩
  obtain ⟨bs, hbs, H⟩ := hT k γ hγ
  have hdef : ∀ b ε : ℝ, inverseDelta C₀ k b ε =
      Real.exp (-(Real.exp^[k ^ (C₀ * k)] (ε ^ (-b)))) := fun _ _ => rfl
  have hE0 : ∀ y : ℝ, 0 < y → 0 < Real.exp^[k ^ (C₀ * k)] y := fun y hy =>
    hy.trans_le (le_exp_iterate _ y)
  have hlt1 : ∀ y : ℝ, 0 < y → Real.exp (-(Real.exp^[k ^ (C₀ * k)] y)) < 1 := fun y hy => by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (neg_lt_zero.2 (hE0 y hy))
  -- `δ₁ = δ_s(1/4)` and `δ_* = exp(-exp^{[N]} 1)`
  set δ₁ := inverseDelta C₀ k bs (1 / 4) with hδ₁
  set δs := Real.exp (-(Real.exp^[k ^ (C₀ * k)] 1)) with hδs
  have hδ₁0 : 0 < δ₁ := Real.exp_pos _
  have hδ₁1 : δ₁ < 1 := hlt1 _ (Real.rpow_pos_of_pos (by norm_num) _)
  have hδs1 : δs < 1 := hlt1 1 one_pos
  -- `(1 - δ₁)^T ≤ 1 - δ_*` and `δ_*^K < δ₁`; `M = T K`, `b = b_s M`
  obtain ⟨T, hT1, hTle⟩ : ∃ T : ℕ, 1 ≤ T ∧ (1 - δ₁) ^ T ≤ 1 - δs := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < 1 - δs)
      (by linarith : 1 - δ₁ < 1)
    exact ⟨n + 1, by omega,
      (pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)).trans hn.le⟩
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ₁0 hδs1
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, pow_zero] at hK
      linarith
    · exact h
  have hM1 : 1 ≤ T * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hM1' : (1 : ℝ) ≤ ((T * K : ℕ) : ℝ) := by exact_mod_cast hM1
  refine ⟨bs * (T * K : ℕ), mul_pos hbs (by linarith), fun ε hε => ⟨0, ?_⟩⟩
  intro A _ _ μ hno hat ι _ _ _ f hf hcorr i
  rw [asm_ofReal_le_cstab_iff]
  rcases le_or_gt ε (1 / 2) with hε2 | hε2
  · -- `ε ≤ 1/2`: the hypothesis at `ε`, and `δ(ε) ≤ δ_s(ε)`
    have hA := (asm_ofReal_le_cstab_iff _ _ _ _).1 (H ε hε hε2 A μ hno hat ι f hf hcorr i)
    have hd1 : inverseDelta C₀ k bs ε < 1 := hlt1 _ (Real.rpow_pos_of_pos hε _)
    have hδd : inverseDelta C₀ k (bs * (T * K : ℕ)) ε ≤ inverseDelta C₀ k bs ε := by
      rw [hdef, hdef]
      refine Real.exp_le_exp.2 (neg_le_neg (exp_iterate_mono _ ?_))
      exact Real.rpow_le_rpow_of_exponent_ge hε (by linarith) (by nlinarith)
    calc inverseDelta C₀ k (bs * (T * K : ℕ)) ε ≤ inverseDelta C₀ k bs ε := hδd
      _ ≤ (cstab (μ.marginalPi i) (1 - inverseDelta C₀ k bs ε) (f i)).re := hA
      _ ≤ _ := asm_re_cstab_mono _ (by linarith) (by linarith) _
  rcases le_or_gt ε 1 with hε1 | hε1
  swap
  · exact absurd (hcorr.trans (asm_norm_corr_le_one μ f hf)) (not_le.2 hε1)
  -- `1/2 < ε ≤ 1`
  set δ := inverseDelta C₀ k (bs * (T * K : ℕ)) ε with hδ
  have hδs' : δ ≤ δs := by
    rw [hδ, hdef, hδs]
    refine Real.exp_le_exp.2 (neg_le_neg (exp_iterate_mono _ ?_))
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by nlinarith)
  have hB := (asm_ofReal_le_cstab_iff _ _ _ _).1
    (H (1 / 4) (by norm_num) (by norm_num) A μ hno hat ι f hf (by linarith) i)
  by_cases hcase : δ ≤ δ₁
  · -- `δ(ε) ≤ δ₁`: the hypothesis at `1/4`
    calc δ ≤ δ₁ := hcase
      _ ≤ (cstab (μ.marginalPi i) (1 - δ₁) (f i)).re := hB
      _ ≤ _ := asm_re_cstab_mono _ (by linarith) (by linarith) _
  -- `δ(ε) > δ₁`: then `ε^M > 1/4`, the tensor power and log-convexity
  push Not at hcase
  have hεM : 1 / 4 < ε ^ (T * K) := by
    have hc' : Real.exp (-(Real.exp^[k ^ (C₀ * k)] ((1 / 4) ^ (-bs)))) <
        Real.exp (-(Real.exp^[k ^ (C₀ * k)] (ε ^ (-(bs * (T * K : ℕ)))))) := hcase
    have h1 := Real.exp_lt_exp.1 hc'
    have h2 : ε ^ (-(bs * (T * K : ℕ))) < (1 / 4) ^ (-bs) := by
      by_contra h
      push Not at h
      linarith [exp_iterate_mono (k ^ (C₀ * k)) h]
    have h3 : ε ^ (-(bs * (T * K : ℕ))) = (ε ^ (T * K)) ^ (-bs) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      ring_nf
    rw [h3] at h2
    by_contra h4
    push Not at h4
    linarith [Real.rpow_le_rpow_of_nonpos (pow_pos hε _) h4 (by linarith : -bs ≤ 0)]
  have hcorrM : 1 / 4 ≤ ‖(μ.pi (ι × Fin (T * K))).cexpect fun X =>
      ∏ i, tensorPow (T * K) (f i) fun t => X t i‖ := by
    rw [cexpect_pi_tensorPow, norm_pow]
    exact hεM.le.trans (pow_le_pow_left₀ hε.le hcorr _)
  have hC := (asm_ofReal_le_cstab_iff _ _ _ _).1
    (H (1 / 4) (by norm_num) (by norm_num) A μ hno hat (ι × Fin (T * K))
      (fun i => tensorPow (T * K) (f i)) (fun i x => norm_tensorPow_le _ (f i) (hf i) x) hcorrM i)
  rw [cstab_tensorPow, cstab_eq_ofReal_re, ← Complex.ofReal_pow, Complex.ofReal_re] at hC
  have hs0 : 0 ≤ (cstab (μ.marginalPi i) (1 - δ₁) (f i)).re :=
    asm_re_cstab_nonneg _ (by linarith) _
  have hv : δs < (cstab (μ.marginalPi i) (1 - δ₁) (f i)).re ^ T := by
    by_contra hv
    push Not at hv
    have h5 := pow_le_pow_left₀ (pow_nonneg hs0 T) hv K
    rw [← pow_mul] at h5
    linarith
  have hlc := cstab_log_convex (μ.marginalPi i) (ρ := 1 - δ₁) (t := (T : ℝ)) (by linarith)
    (by linarith) (by exact_mod_cast hT1) (f i) (asm_cl2sq_le_one _ (f i) (hf i))
  rw [Real.rpow_natCast, Real.rpow_natCast] at hlc
  calc δ ≤ δs := hδs'
    _ ≤ (cstab (μ.marginalPi i) (1 - δ₁) (f i)).re ^ T := hv.le
    _ ≤ (cstab (μ.marginalPi i) ((1 - δ₁) ^ T) (f i)).re := hlc
    _ ≤ (cstab (μ.marginalPi i) (1 - δ) (f i)).re :=
        asm_re_cstab_mono _ (pow_nonneg (by linarith) _) (hTle.trans (by linarith)) _

end Assembly

end TrackB
end RestrictedPolynomials
end
