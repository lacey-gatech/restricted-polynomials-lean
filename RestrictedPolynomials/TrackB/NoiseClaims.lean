module

public import RestrictedPolynomials.TrackB.OpComparison
public import RestrictedPolynomials.TrackB.NoiseChains
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.MasterEmbedding
public import Mathlib.Analysis.Complex.Order

/-!
# Track B: noise claims (paper IV `writeup_stability.tex`)

Paper IV items: `claim:rr-nestab` (Claim 4.9, L2520-2538) with its trivial-`H` form,
`claim-embed-characters-orthonormal` (L4161-4162), `claim:relaxed1` (Claim 6.12, L3771-3783).

Readings: `rr_nestab` is stated for an arbitrary map `σ : S → H`,
with `c = c(m, α₀)` independent of `β`, atoms `≥ α₀` and `|S| ≤ m`; orthonormality needs
the `x`-marginal of the relaxed theorem's hypothesis 4: `σ(x)` uniform on `H`.
The private helpers for the trivial-`H` form are bound-free, and
`embed_characters_basis_of_surjective` is an added auxiliary result.
-/

@[expose] public section

open Finset
open scoped BigOperators ComplexOrder
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### B4 `claim:rr-nestab` (Claim 4.9) -/

section RrNestab

private theorem kernel_triv_any {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (ξ : ℝ)
    (a b : α) : nonEmbedKernel D (fun _ : α => ()) ξ a b = noiseKernel D (1 - ξ) a b := by
  unfold nonEmbedKernel graphNoiseKernel noiseKernel
  have h2 : ∑ c : α, D.prob c = 1 := D.sum_eq_one
  beta_reduce
  simp [h2]

private theorem nestab_triv_any {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (ξ : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → α) → ℂ) :
    nestab D (fun _ : α => ()) ξ g = cstab D (1 - ξ) g := by
  have hk : ∀ a b : ι → α, ((∏ i : ι, nonEmbedKernel D (fun _ : α => ()) ξ (a i) (b i) : ℝ)) =
      ∏ i : ι, noiseKernel D (1 - ξ) (a i) (b i) := by
    intro a b
    exact Finset.prod_congr rfl fun i _ => kernel_triv_any D ξ _ _
  have hop : nonEmbedOp D (fun _ : α => ()) ξ g = cnoiseOp D (1 - ξ) g := by
    funext x
    unfold nonEmbedOp graphNoiseOp cnoiseOp
    refine Finset.sum_congr rfl fun y _ => ?_
    have := hk x y
    unfold nonEmbedKernel at this
    rw [this]
  unfold nestab cstab FinProb.cinner
  rw [hop]

/-- paper IV `claim:rr-nestab` (paper IV l. 2520-2538): `𝔼_{J ⊆_β [n], x'' ∼ D''^{J̄}} NEStab_{1-δ}(f_{J̄→x''}; D'^J)
≤ NEStab_{1-cβδ}(f; D^{⊗n})`, `c = c(m, α₀)` independent of `β`, `δ`, `n`. The distribution `ν` of the
source enters only through the map `σ : Σ → H` (the `x`-component of its master embedding), which is
arbitrary here. -/
theorem rr_nestab {α₀ : ℝ} (hα : 0 < α₀) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, ∀ (hβ0 : 0 < β) (hβ1 : β ≤ 1),
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ (H : Type) [DecidableEq H] (σ : S → H),
      ∀ D D' D'' : FinProb S, (∀ x, α₀ ≤ D.prob x) → (∀ x, α₀ ≤ D'.prob x) →
        (∀ x, α₀ ≤ D''.prob x) →
        (∀ x, D.prob x = β * D'.prob x + (1 - β) * D''.prob x) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → S) → ℂ),
        mixtureRestrictionExpect β hβ0.le hβ1 D'' f (fun _ g => nestab D' σ δ g) ≤
          nestab D σ (c * β * δ) f := by
  obtain ⟨c, hc, h⟩ := op_comparison_lemma_uniform hα m
  refine ⟨c, hc, fun β hβ0 hβ1 S _ _ hcard H _ σ D D' D'' hD hD' hD'' hmix δ hδ0 hδ1 ι _ _ f => ?_⟩
  exact h β hβ0 hβ1 S hcard D D' D'' hD hD' hD'' hmix (fun a b => σ a = σ b)
    ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ δ hδ0 hδ1 ι f

/-- the trivial-`H` form of the claim: the fibre graph is complete, and
the claim is the standard bound for `Stab` under a mixture random restriction. -/
theorem rr_stab_trivial_master {α₀ : ℝ} (hα : 0 < α₀) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, ∀ (hβ0 : 0 < β) (hβ1 : β ≤ 1),
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ D D' D'' : FinProb S, (∀ x, α₀ ≤ D.prob x) → (∀ x, α₀ ≤ D'.prob x) →
        (∀ x, α₀ ≤ D''.prob x) →
        (∀ x, D.prob x = β * D'.prob x + (1 - β) * D''.prob x) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → S) → ℂ),
        mixtureRestrictionExpect β hβ0.le hβ1 D'' f (fun _ g => cstab D' (1 - δ) g) ≤
          cstab D (1 - c * β * δ) f := by
  obtain ⟨c, hc, h⟩ := rr_nestab hα m
  refine ⟨c, hc, fun β hβ0 hβ1 S _ _ hcard D D' D'' hD hD' hD'' hmix δ hδ0 hδ1 ι _ _ f => ?_⟩
  have := h β hβ0 hβ1 S hcard Unit (fun _ => ()) D D' D'' hD hD' hD'' hmix δ hδ0 hδ1 ι f
  simpa only [nestab_triv_any] using this

end RrNestab

/-! ### B4 `claim-embed-characters-orthonormal` -/

section EmbedCharacters
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- hypothesis 4 of the relaxed theorem (paper IV l. 3438-3439): the law of
`(σ(x), γ(y), φ(z))` is uniform on `{(a,b,c) ∈ H³ : a + b + c = 0}` (each point has mass `1/|H|²`);
its `x`-marginal is uniform on `H`. -/
theorem embedchar_uniform_triple_marginal_x (μ : FinProb (X × Y × Z)) (σ : X → H) (γ : Y → H)
    (φ : Z → H)
    (hunif : ∀ a b c : H,
      ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)), μ.prob p =
        if a + b + c = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0) (a : H) :
    ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = a), μ.prob p = 1 / (Fintype.card H : ℝ) := by
  rw [← Finset.sum_fiberwise (univ.filter (fun p : X × Y × Z => σ p.1 = a))
    (fun p : X × Y × Z => (γ p.2.1, φ p.2.2))]
  have key : ∀ bc : H × H,
      ∑ p ∈ (univ.filter (fun p : X × Y × Z => σ p.1 = a)).filter
          (fun p => (γ p.2.1, φ p.2.2) = bc), μ.prob p =
        if a + bc.1 + bc.2 = 0 then 1 / (Fintype.card H : ℝ) ^ 2 else 0 := by
    rintro ⟨b, c⟩
    rw [← hunif a b c]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  simp_rw [key]
  rw [Fintype.sum_prod_type]
  have hc : ∀ b : H, ∑ c : H, (if a + (b, c).1 + (b, c).2 = 0 then 1 / (Fintype.card H : ℝ) ^ 2
      else 0) = 1 / (Fintype.card H : ℝ) ^ 2 := by
    intro b
    have : ∀ c : H, (a + (b, c).1 + (b, c).2 = 0) ↔ (-(a + b) = c) := by
      intro c
      simp only
      constructor
      · intro h; exact neg_eq_of_add_eq_zero_right h
      · intro h; rw [← h]; abel
    simp_rw [this]
    simp
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  field_simp

open scoped Classical in
/-- paper IV `claim-embed-characters-orthonormal`: `⟨χ∘σ, χ'∘σ⟩_{μ_x} = 1_{χ = χ'}`, given that the law of
`σ(x)` under `μ_x` is uniform on `H`. -/
theorem embed_characters_orthonormal (μ : FinProb (X × Y × Z)) (σ : X → H)
    (hx : ∀ a : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = a), μ.prob p =
      1 / (Fintype.card H : ℝ)) (χ χ' : AddChar H ℂ) :
    μ.cexpect (fun p => χ (σ p.1) * star (χ' (σ p.1))) = if χ = χ' then 1 else 0 := by
  unfold FinProb.cexpect
  rw [← Finset.sum_fiberwise univ (fun p : X × Y × Z => σ p.1)]
  have key : ∀ a : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = a),
      (μ.prob p : ℂ) * (χ (σ p.1) * star (χ' (σ p.1))) =
      (1 / (Fintype.card H : ℂ)) * (χ a * star (χ' a)) := by
    intro a
    have h1 : ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = a),
        (μ.prob p : ℂ) * (χ (σ p.1) * star (χ' (σ p.1))) =
        ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = a),
          (μ.prob p : ℂ) * (χ a * star (χ' a)) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.1 hp).2]
    rw [h1, ← Finset.sum_mul]
    congr 1
    have := hx a
    rw [← Complex.ofReal_sum, this]
    push_cast
    rfl
  have hfib : ∑ a : H, ∑ p ∈ (univ : Finset (X × Y × Z)).filter (fun p => σ p.1 = a),
      (μ.prob p : ℂ) * (χ (σ p.1) * star (χ' (σ p.1))) =
      ∑ a : H, (1 / (Fintype.card H : ℂ)) * (χ a * star (χ' a)) :=
    Finset.sum_congr rfl fun a _ => key a
  rw [hfib, ← Finset.mul_sum]
  have hψ : ∀ a : H, χ a * star (χ' a) = (χ * χ'⁻¹) a := by
    intro a
    rw [Complex.star_def, ← AddChar.map_neg_eq_conj]
    simp [AddChar.inv_apply]
  simp_rw [hψ]
  rw [AddChar.sum_eq_ite]
  have hN : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases h : χ = χ'
  · subst h
    have e0 : χ * χ⁻¹ = (0 : AddChar H ℂ) := mul_inv_cancel χ
    simp [e0, hN]
  · have : χ * χ'⁻¹ ≠ 0 := by
      intro h0
      apply h
      have h1 : χ * χ'⁻¹ = 1 := h0
      exact mul_inv_eq_one.1 h1
    simp [this, h]

omit [DecidableEq H] in
/-- `{χ∘σ}_{χ ∈ Ĥ}` is a basis of `Embed_σ(μ) = span{χ∘σ}` whenever `σ` is onto `H` (Dedekind independence of the characters composed with a surjection). -/
theorem embed_characters_basis_of_surjective {W : Type*} (σ : W → H) (hσ : Function.Surjective σ) :
    ∃ b : Module.Basis (AddChar H ℂ) ℂ (embedSpan σ),
      ∀ χ : AddChar H ℂ, ((b χ : embedSpan σ) : W → ℂ) = fun x => χ (σ x) := by
  have hli : LinearIndependent ℂ (fun χ : AddChar H ℂ => fun w => χ (σ w)) := by
    have h0 : LinearIndependent ℂ ((⇑) : AddChar H ℂ → H → ℂ) := AddChar.linearIndependent H ℂ
    have hinj : Function.Injective (LinearMap.funLeft ℂ ℂ σ) :=
      LinearMap.funLeft_injective_of_surjective ℂ ℂ σ hσ
    exact h0.map' (LinearMap.funLeft ℂ ℂ σ) (LinearMap.ker_eq_bot.2 hinj)
  exact ⟨Module.Basis.span hli, fun χ => congrArg Subtype.val (Module.Basis.span_apply hli χ)⟩

/-- `{χ∘σ}_{χ ∈ Ĥ}` is a basis of `Embed_σ(μ) = span{χ∘σ}` ("hence `B_embed` is an orthonormal basis"):
by the orthonormality it is linearly independent. -/
theorem embed_characters_basis (μ : FinProb (X × Y × Z)) (σ : X → H)
    (hx : ∀ a : H, ∑ p ∈ univ.filter (fun p : X × Y × Z => σ p.1 = a), μ.prob p =
      1 / (Fintype.card H : ℝ)) :
    ∃ b : Module.Basis (AddChar H ℂ) ℂ (embedSpan σ),
      ∀ χ : AddChar H ℂ, ((b χ : embedSpan σ) : X → ℂ) = fun x => χ (σ x) := by
  apply embed_characters_basis_of_surjective
  intro a
  by_contra hne
  push Not at hne
  have h := hx a
  have hempty : (univ.filter (fun p : X × Y × Z => σ p.1 = a)) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun hp => hne p.1 hp
  rw [hempty, Finset.sum_empty] at h
  have hN : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have : (0 : ℝ) < 1 / (Fintype.card H : ℝ) := by positivity
  linarith

end EmbedCharacters

/-! ### B4 `claim:relaxed1` (Claim 6.12) -/

section Relaxed1
variable {α : Type*} [Fintype α]

/-- paper IV `claim:relaxed1`: `𝔼_{x,x' ∈ Σ_modest}|f(x) - f(x')|² ≥ τ` implies `𝔼_{x ∈ Σ_modest}|f(x)|² ≥ τ/4`
(`T = Σ_modest` with the uniform measure; the source writes `Σ'` in the proof, read here as
`Σ_modest`). -/
theorem relaxed1_modest_mass (T : Finset α) (f : α → ℂ) {τ : ℝ}
    (h : τ ≤ 𝔼 x ∈ T, 𝔼 x' ∈ T, ‖f x - f x'‖ ^ 2) : τ / 4 ≤ 𝔼 x ∈ T, ‖f x‖ ^ 2 := by
  have hpt : ∀ x x' : α, ‖f x - f x'‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖f x'‖ ^ 2 := by
    intro x x'
    have h1 : ‖f x - f x'‖ ≤ ‖f x‖ + ‖f x'‖ := norm_sub_le _ _
    have h2 : ‖f x - f x'‖ ^ 2 ≤ (‖f x‖ + ‖f x'‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖f x‖ - ‖f x'‖)]
  have h3 : (𝔼 x ∈ T, 𝔼 x' ∈ T, ‖f x - f x'‖ ^ 2) ≤
      𝔼 x ∈ T, 𝔼 x' ∈ T, (2 * ‖f x‖ ^ 2 + 2 * ‖f x'‖ ^ 2) :=
    Finset.expect_le_expect fun x _ => Finset.expect_le_expect fun x' _ => hpt x x'
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst hT
    simp at h ⊢
    linarith
  · have h4 : (𝔼 x ∈ T, 𝔼 x' ∈ T, (2 * ‖f x‖ ^ 2 + 2 * ‖f x'‖ ^ 2)) =
        4 * 𝔼 x ∈ T, ‖f x‖ ^ 2 := by
      simp only [Finset.expect_add_distrib, Finset.expect_const hT, ← Finset.mul_expect]
      ring
    linarith

end Relaxed1

end TrackB
end RestrictedPolynomials
end
