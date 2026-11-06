module

public import RestrictedPolynomials.TrackB.MaxTInduct
public import RestrictedPolynomials.TrackB.OpComparison
public import RestrictedPolynomials.TrackB.NoiseChains
public import RestrictedPolynomials.TrackB.NoiseClaims
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.MarkovChain
public import RestrictedPolynomials.TrackB.StabComplex

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

private theorem mg_finProb_ext {α : Type} [Fintype α] {π π' : FinProb α}
    (h : ∀ a, π.prob a = π'.prob a) : π = π' := by
  cases π
  cases π'
  congr
  funext a
  exact h a

private theorem mg_mergePush_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (π : FinProb α) (f : α → β) (g : β → γ) :
    mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine mg_finProb_ext fun c => ?_
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

section Commute
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

theorem mgen_mergeDistY_lawSwapXY (μ : FinProb (X × Y × Z)) (a : X → X) :
    mergeDistY (lawSwapXY μ) a = lawSwapXY (mergeDistX μ a) := by
  unfold mergeDistY lawSwapXY mergeDistX
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_mergeDistX_lawSwapXY (μ : FinProb (X × Y × Z)) (b : Y → Y) :
    mergeDistX (lawSwapXY μ) b = lawSwapXY (mergeDistY μ b) := by
  unfold mergeDistX lawSwapXY mergeDistY
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_mergeDistZ_lawSwapXY (μ : FinProb (X × Y × Z)) (c : Z → Z) :
    mergeDistZ (lawSwapXY μ) c = lawSwapXY (mergeDistZ μ c) := by
  unfold mergeDistZ lawSwapXY
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_mergeDistX_lawSwapYZ (μ : FinProb (X × Y × Z)) (a : X → X) :
    mergeDistX (lawSwapYZ μ) a = lawSwapYZ (mergeDistX μ a) := by
  unfold mergeDistX lawSwapYZ
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_mergeDistZ_lawSwapYZ (μ : FinProb (X × Y × Z)) (b : Y → Y) :
    mergeDistZ (lawSwapYZ μ) b = lawSwapYZ (mergeDistY μ b) := by
  unfold mergeDistZ lawSwapYZ mergeDistY
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_mergeDistY_lawSwapYZ (μ : FinProb (X × Y × Z)) (c : Z → Z) :
    mergeDistY (lawSwapYZ μ) c = lawSwapYZ (mergeDistZ μ c) := by
  unfold mergeDistY lawSwapYZ mergeDistZ
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_mergeDistX_lawSwapXZ (μ : FinProb (X × Y × Z)) (c : Z → Z) :
    mergeDistX (lawSwapXZ μ) c = lawSwapXZ (mergeDistZ μ c) := by
  unfold mergeDistX lawSwapXZ mergeDistZ
  rw [mg_mergePush_comp, mg_mergePush_comp]

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem mg_mem_swapXY {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (y, x, z) ∈ swapXY S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem mg_mem_swapYZ {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (x, z, y) ∈ swapYZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem mg_mem_swapXZ {S : Set (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (z, y, x) ∈ swapXZ S ↔ (x, y, z) ∈ S := by
  constructor
  · rintro ⟨⟨x', y', z'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h
  · intro h
    exact ⟨(x, y, z), h, rfl⟩

theorem mgen_mergeGraphY_swapXY (S : Set (X × Y × Z)) :
    mergeGraphY (swapXY S) = mergeGraphX S := by
  ext u v
  simp only [mergeGraphY, mergeGraphX, SimpleGraph.fromRel_adj, mg_mem_swapXY]

theorem mgen_mergeGraphX_swapXY (S : Set (X × Y × Z)) :
    mergeGraphX (swapXY S) = mergeGraphY S := by
  ext u v
  simp only [mergeGraphY, mergeGraphX, SimpleGraph.fromRel_adj, mg_mem_swapXY]

theorem mgen_mergeGraphZ_swapXY (S : Set (X × Y × Z)) :
    mergeGraphZ (swapXY S) = mergeGraphZ S := by
  ext u v
  simp only [mergeGraphZ, SimpleGraph.fromRel_adj, mg_mem_swapXY]
  refine and_congr Iff.rfl (or_congr ?_ ?_) <;>
  · constructor
    · rintro ⟨y, x, h1, h2⟩
      exact ⟨x, y, h1, h2⟩
    · rintro ⟨y, x, h1, h2⟩
      exact ⟨x, y, h1, h2⟩

theorem mgen_mergeGraphX_swapYZ (S : Set (X × Y × Z)) :
    mergeGraphX (swapYZ S) = mergeGraphX S := by
  ext u v
  simp only [mergeGraphX, SimpleGraph.fromRel_adj, mg_mem_swapYZ]
  refine and_congr Iff.rfl (or_congr ?_ ?_) <;>
  · constructor
    · rintro ⟨y, x, h1, h2⟩
      exact ⟨x, y, h1, h2⟩
    · rintro ⟨y, x, h1, h2⟩
      exact ⟨x, y, h1, h2⟩

theorem mgen_mergeGraphZ_swapYZ (S : Set (X × Y × Z)) :
    mergeGraphZ (swapYZ S) = mergeGraphY S := by
  ext u v
  simp only [mergeGraphZ, mergeGraphY, SimpleGraph.fromRel_adj, mg_mem_swapYZ]

theorem mgen_mergeGraphY_swapYZ (S : Set (X × Y × Z)) :
    mergeGraphY (swapYZ S) = mergeGraphZ S := by
  ext u v
  simp only [mergeGraphZ, mergeGraphY, SimpleGraph.fromRel_adj, mg_mem_swapYZ]

theorem mgen_mergeGraphX_swapXZ (S : Set (X × Y × Z)) :
    mergeGraphX (swapXZ S) = mergeGraphZ S := by
  ext u v
  simp only [mergeGraphZ, mergeGraphX, SimpleGraph.fromRel_adj, mg_mem_swapXZ]
  refine and_congr Iff.rfl (or_congr ?_ ?_) <;>
  · constructor
    · rintro ⟨y, x, h1, h2⟩
      exact ⟨x, y, h1, h2⟩
    · rintro ⟨y, x, h1, h2⟩
      exact ⟨x, y, h1, h2⟩

private theorem mg_atom_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) {α₀ : ℝ} (h : ∀ p ∈ π.support, α₀ ≤ π.prob p) :
    ∀ p ∈ (mergePush π f).support, α₀ ≤ (mergePush π f).prob p := by
  intro p hp
  have hp' : (∑ a ∈ Finset.univ.filter (fun a => f a = p), π.prob a) ≠ 0 := hp
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
  have hle : π.prob a ≤ (mergePush π f).prob p :=
    Finset.single_le_sum (f := π.prob) (fun q _ => π.nonneg q) ha
  exact (h a hne).trans hle

/-- atoms of the `y`- and `z`-merged laws (the `x` case is `mergeDistX_atom_bound`). -/
theorem mgen_mergeDistY_atom_bound (μ : FinProb (X × Y × Z)) (b : Y → Y) {α₀ : ℝ}
    (h : ∀ p ∈ μ.support, α₀ ≤ μ.prob p) :
    ∀ p ∈ (mergeDistY μ b).support, α₀ ≤ (mergeDistY μ b).prob p :=
  mg_atom_push μ _ h

theorem mgen_mergeDistZ_atom_bound (μ : FinProb (X × Y × Z)) (c : Z → Z) {α₀ : ℝ}
    (h : ∀ p ∈ μ.support, α₀ ≤ μ.prob p) :
    ∀ p ∈ (mergeDistZ μ c).support, α₀ ≤ (mergeDistZ μ c).prob p :=
  mg_atom_push μ _ h

/-- `SStmt` is invariant under the slot exchange `x ↔ z` (composite of `xy`, `yz`, `xy`). -/
theorem mgen_lawSwapXZ_eq (μ : FinProb (X × Y × Z)) :
    lawSwapXZ μ = lawSwapXY (lawSwapYZ (lawSwapXY μ)) := by
  unfold lawSwapXZ lawSwapXY lawSwapYZ
  rw [mg_mergePush_comp, mg_mergePush_comp]

theorem mgen_sStmtX_iff_swapXZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtX μ M δ₀ η ↔ SStmtZ (lawSwapXZ μ) M δ₀ η := by
  rw [mgen_lawSwapXZ_eq, sStmtX_iff_swapXY, sStmtY_iff_swapYZ, sStmtZ_iff_swapXY]

theorem mgen_sStmtY_iff_swapXZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtY μ M δ₀ η ↔ SStmtY (lawSwapXZ μ) M δ₀ η := by
  rw [mgen_lawSwapXZ_eq, sStmtY_iff_swapXY, sStmtX_iff_swapYZ, sStmtX_iff_swapXY]

theorem mgen_sStmtZ_iff_swapXZ (μ : FinProb (X × Y × Z)) (M δ₀ η : ℝ) :
    SStmtZ μ M δ₀ η ↔ SStmtX (lawSwapXZ μ) M δ₀ η := by
  rw [mgen_lawSwapXZ_eq, sStmtZ_iff_swapXY, sStmtZ_iff_swapYZ, sStmtY_iff_swapXY]

end Commute
section Steps
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem mg_push_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {ι : Type} [Fintype ι] [DecidableEq ι] (a : α → β) (w : ι → α → ℝ) (G : (ι → β) → ℂ) :
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

private theorem mg_cexpect_pi_push {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (a : α → β)
    (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (mg_push_sum a (fun _ c => π.prob c) G).symm

/-- the merged law sees `f` constant on components exactly like `μ` (term (VI)); `x`, `y`, `z`. -/
theorem mgen_corr3_merge_x (μ : FinProb (X × Y × Z)) (a : X → X) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : (ι → ↥(Set.range a)) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 μ (fun x => F fun i => ⟨a (x i), Set.mem_range_self _⟩) g h =
      corr3 (mergeDistX μ a) F g h := by
  unfold corr3 mergeDistX
  rw [mg_cexpect_pi_push]

theorem mgen_corr3_merge_y (μ : FinProb (X × Y × Z)) (b : Y → Y) {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (G : (ι → ↥(Set.range b)) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 μ f (fun y => G fun i => ⟨b (y i), Set.mem_range_self _⟩) h =
      corr3 (mergeDistY μ b) f G h := by
  unfold corr3 mergeDistY
  rw [mg_cexpect_pi_push]

theorem mgen_corr3_merge_z (μ : FinProb (X × Y × Z)) (c : Z → Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (H : (ι → ↥(Set.range c)) → ℂ) :
    corr3 μ f g (fun z => H fun i => ⟨c (z i), Set.mem_range_self _⟩) =
      corr3 (mergeDistZ μ c) f g H := by
  unfold corr3 mergeDistZ
  rw [mg_cexpect_pi_push]

open scoped ComplexOrder in
/-- event `E₂` (merge and merge2): `op_comparison_lemma_uniform` at `β = s`, `ν₁ = ν₂ = D`, for the
trivial master embedding (`NEStab = Stab`, `nestab_trivial_master`): with `K = 1/c`,
`𝔼_J Stab_{1-Kδ/s}(gt; D) ≤ Stab_{1-δ}(g; D)` whenever `Kδ ≤ s`. -/
theorem mgen_restriction_event_stab (m : ℕ) {α₀ : ℝ} (hα : 0 < α₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ D : FinProb S, (∀ x, α₀ ≤ D.prob x) → ∀ s δ : ℝ, (hs0 : 0 < s) → (hs1 : s ≤ 1) →
      0 < δ → K * δ ≤ s → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : (ι → S) → ℂ),
        (mixtureRestrictionExpect s hs0.le hs1 D g fun I gt => cstab D (1 - K * δ / s) gt).re ≤
          (cstab D (1 - δ) g).re := by
  obtain ⟨c, hc, h⟩ := rr_stab_trivial_master hα m
  refine ⟨1 / c, one_div_pos.2 hc, fun S _ _ hcard D hD s δ hs0 hs1 hδ hKδ ι _ _ g => ?_⟩
  have hδ' : 1 / c * δ / s ≤ 1 := by
    rw [div_le_one hs0]; exact hKδ
  have hδ'0 : 0 < 1 / c * δ / s := by positivity
  have key := h s hs0 hs1 S hcard D D D hD hD hD
    (fun x => by ring) (1 / c * δ / s) hδ'0 hδ' ι g
  have e : c * s * (1 / c * δ / s) = δ := by field_simp
  rw [e] at key
  exact (Complex.le_def.1 key).1

end Steps

section CS
open scoped Classical
variable {X U : Type} [Fintype X] [Fintype U] {ι : Type} [Fintype ι] [DecidableEq ι]

private def mgP (ρ : FinProb (X × U)) (x : ι → X) (u : ι → U) : ℝ := ∏ i, ρ.prob (x i, u i)

private theorem mg_cexpect_split (ρ : FinProb (X × U)) (F : (ι → X × U) → ℂ) :
    (ρ.pi ι).cexpect F = ∑ u : ι → U, ∑ x : ι → X, ((mgP ρ x u : ℝ) : ℂ) * F (fun i => (x i, u i)) := by
  unfold FinProb.cexpect
  rw [← (Equiv.arrowProdEquivProdArrow ι (fun _ => X) (fun _ => U)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

private theorem mg_w (ρ : FinProb (X × U)) (u : ι → U) :
    ∑ x : ι → X, mgP ρ x u = ∏ i, ∑ a, ρ.prob (a, u i) := by
  unfold mgP
  rw [Fintype.prod_sum (fun i a => ρ.prob (a, u i))]

private def mgSU (ρ : FinProb (X × U)) (a x' : X) : ℝ :=
  ∑ u, ρ.prob (a, u) / (∑ v, ρ.prob (a, v)) * (ρ.prob (x', u) / ∑ b, ρ.prob (b, u))

private theorem mg_factor (ρ : FinProb (X × U)) (a x' : X) :
    (∑ v, ρ.prob (a, v)) * mgSU ρ a x' = ∑ u, ρ.prob (a, u) * ρ.prob (x', u) / ∑ b, ρ.prob (b, u) := by
  unfold mgSU
  by_cases h : ∑ v, ρ.prob (a, v) = 0
  · have h0 : ∀ u, ρ.prob (a, u) = 0 := fun u =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => ρ.nonneg (a, v))).1 h u (Finset.mem_univ _)
    simp [h0]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    field_simp

private theorem mg_Q (ρ : FinProb (X × U)) (x x' : ι → X) :
    (∏ i, ∑ v, ρ.prob (x i, v)) * ∏ i, mgSU ρ (x i) (x' i) =
      ∑ u : ι → U, mgP ρ x u * mgP ρ x' u / ∏ i, ∑ b, ρ.prob (b, u i) := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [mg_factor]
  rw [Fintype.prod_sum (fun i u => ρ.prob (x i, u) * ρ.prob (x' i, u) / ∑ b, ρ.prob (b, u))]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold mgP
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]

private theorem mg_mgP_nonneg (ρ : FinProb (X × U)) (x : ι → X) (u : ι → U) : 0 ≤ mgP ρ x u :=
  Finset.prod_nonneg fun i _ => ρ.nonneg _

private theorem mg_sum_w (ρ : FinProb (X × U)) :
    ∑ u : ι → U, ∏ i, ∑ b, ρ.prob (b, u i) = 1 := by
  rw [← Fintype.prod_sum (fun (i : ι) (v : U) => ∑ b, ρ.prob (b, v))]
  have : ∑ v : U, ∑ b, ρ.prob (b, v) = 1 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type', ρ.sum_eq_one]
  simp [this]

private theorem mg_A_zero (ρ : FinProb (X × U)) (f : (ι → X) → ℂ) (u : ι → U)
    (h : ∏ i, ∑ b, ρ.prob (b, u i) = 0) : ∑ x : ι → X, ((mgP ρ x u : ℝ) : ℂ) * f x = 0 := by
  rw [← mg_w] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mg_mgP_nonneg ρ x u)).1 h
  exact Finset.sum_eq_zero fun x _ => by rw [h0 x (Finset.mem_univ _)]; simp

private theorem mg_cs {ρ : FinProb (X × U)} {πx : FinProb X}
    (hπ : ∀ a, πx.prob a = ∑ u, ρ.prob (a, u)) (f : (ι → X) → ℂ) (γ : (ι → U) → ℂ)
    (hγ : ∀ u, ‖γ u‖ ≤ 1) :
    ‖(ρ.pi ι).cexpect (fun t => f (fun i => (t i).1) * γ (fun i => (t i).2))‖ ^ 2 ≤
      ((πx.pi ι).cinner f (fun x => ∑ x', ((∏ i, mgSU ρ (x i) (x' i) : ℝ) : ℂ) * f x')).re := by
  set A : (ι → U) → ℂ := fun u => ∑ x : ι → X, ((mgP ρ x u : ℝ) : ℂ) * f x with hA
  set w : (ι → U) → ℝ := fun u => ∏ i, ∑ b, ρ.prob (b, u i) with hw
  have hw0 : ∀ u, 0 ≤ w u := fun u => Finset.prod_nonneg fun i _ =>
    Finset.sum_nonneg fun b _ => ρ.nonneg _
  have h1 : (ρ.pi ι).cexpect (fun t => f (fun i => (t i).1) * γ (fun i => (t i).2)) =
      ∑ u, γ u * A u := by
    rw [mg_cexpect_split]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have h2 : ‖∑ u, γ u * A u‖ ≤ ∑ u, ‖A u‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hγ u)
  have h3 : (∑ u, ‖A u‖) ^ 2 ≤ ∑ u, ‖A u‖ ^ 2 / w u := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun u => Real.sqrt (w u))
      (fun u => ‖A u‖ / Real.sqrt (w u))
    have e1 : ∀ u, Real.sqrt (w u) * (‖A u‖ / Real.sqrt (w u)) = ‖A u‖ := by
      intro u
      by_cases hu : w u = 0
      · have : A u = 0 := mg_A_zero ρ f u hu
        simp [this]
      · have : Real.sqrt (w u) ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (hw0 u) (Ne.symm hu))).ne'
        field_simp
    have e2 : ∑ u, Real.sqrt (w u) ^ 2 = 1 := by
      simp_rw [Real.sq_sqrt (hw0 _)]
      exact mg_sum_w ρ
    have e3 : ∀ u, (‖A u‖ / Real.sqrt (w u)) ^ 2 = ‖A u‖ ^ 2 / w u := by
      intro u
      rw [div_pow, Real.sq_sqrt (hw0 u)]
    simp only [e1, e2, e3, one_mul] at this
    exact this
  have h4 : ((∑ u, ‖A u‖ ^ 2 / w u : ℝ) : ℂ) =
      ∑ x, ∑ x', ((πx.pi ι).prob x : ℂ) * ((∏ i, mgSU ρ (x i) (x' i) : ℝ) : ℂ) *
        (f x * star (f x')) := by
    have hpi : ∀ x : ι → X, (πx.pi ι).prob x = ∏ i, ∑ v, ρ.prob (x i, v) := fun x =>
      Finset.prod_congr rfl fun i _ => hπ _
    have hQ : ∀ x x' : ι → X, ((πx.pi ι).prob x : ℂ) * ((∏ i, mgSU ρ (x i) (x' i) : ℝ) : ℂ) =
        ((∑ u : ι → U, mgP ρ x u * mgP ρ x' u / w u : ℝ) : ℂ) := by
      intro x x'
      rw [← Complex.ofReal_mul, hpi, mg_Q]
    simp_rw [hQ]
    push_cast
    have hnorm : ∀ u, ((‖A u‖ ^ 2 : ℝ) : ℂ) = A u * star (A u) := by
      intro u
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [← Complex.ofReal_pow, hnorm]
    simp only [hA, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal, Finset.sum_mul,
      Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x' _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
      Finset.sum_congr rfl fun u _ => ?_
    ring
  have h5 : ((πx.pi ι).cinner f (fun x => ∑ x', ((∏ i, mgSU ρ (x i) (x' i) : ℝ) : ℂ) * f x')) =
      ∑ x, ∑ x', ((πx.pi ι).prob x : ℂ) * ((∏ i, mgSU ρ (x i) (x' i) : ℝ) : ℂ) *
        (f x * star (f x')) := by
    unfold FinProb.cinner FinProb.cexpect
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [star_sum, star_mul', Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    ring
  have h6 : ((πx.pi ι).cinner f (fun x => ∑ x', ((∏ i, mgSU ρ (x i) (x' i) : ℝ) : ℂ) * f x')).re =
      ∑ u, ‖A u‖ ^ 2 / w u := by
    rw [h5, ← h4, Complex.ofReal_re]
  rw [h6, h1]
  exact (pow_le_pow_left₀ (norm_nonneg _) h2 2).trans h3

end CS

section Defs
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the one-coordinate chain `S = T*T`. -/
def mgenS (μ : FinProb (X × Y × Z)) (a x' : X) : ℝ :=
  ∑ y, ∑ z, μ.prob (a, y, z) / (lawX μ).prob a * (μ.prob (x', y, z) / ∑ x, μ.prob (x, y, z))

def mgenSOp (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (x : ι → X) : ℂ :=
  ∑ x', ((∏ i, mgenS μ (x i) (x' i) : ℝ) : ℂ) * f x'

private theorem mg_lawX_prob (μ : FinProb (X × Y × Z)) (a : X) :
    (lawX μ).prob a = ∑ v : Y × Z, μ.prob (a, v) := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.1 = a), μ.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem mgen_corr3_sq_le (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hh : ∀ z, ‖h z‖ ≤ 1) :
    ‖corr3 μ f g h‖ ^ 2 ≤ (((lawX μ).pi ι).cinner f (mgenSOp μ f)).re := by
  have key := mg_cs (ρ := (μ : FinProb (X × (Y × Z)))) (πx := lawX μ) (mg_lawX_prob μ) f
    (fun u => g (fun i => (u i).1) * h (fun i => (u i).2)) (fun u => by
      rw [norm_mul]
      simpa using mul_le_mul (hg _) (hh _) (norm_nonneg _) zero_le_one)
  have hS : ∀ a x', mgSU (μ : FinProb (X × (Y × Z))) a x' = mgenS μ a x' := by
    intro a x'
    unfold mgSU mgenS
    rw [Fintype.sum_prod_type]
    simp_rw [mg_lawX_prob μ a]
  simp_rw [hS] at key
  have hc : corr3 μ f g h = (μ.pi ι).cexpect (fun t => f (fun i => (t i).1) *
      (g (fun i => (t i).2.1) * h (fun i => (t i).2.2))) := by
    unfold corr3
    exact congrArg _ (funext fun t => by ring)
  rw [hc]
  exact key

end Defs


section Defs2
open scoped Classical
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the components of the merge graph `G_{x,μ,merge}` (reachability). -/
def mgenComp (μ : FinProb (X × Y × Z)) : X → X → Prop := (mergeGraphX μ.support).Reachable

/-- `∏_{k∈A} (I - E_k)` applied to `f`, `E` the average over the component of the coordinate
(w.r.t. `μ_x`): `f` has non-merged degree `< d` iff this vanishes for every `|A| ≥ d`
(basis-free form of the non-merged degree of the eigenbasis `χ_{i,j}`). -/
def mgenMeanZeroOp (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (f : (ι → X) → ℂ) (x : ι → X) : ℂ :=
  ∑ x', ((∏ i, (if i ∈ A then (if x i = x' i then 1 else 0) -
      graphNoiseKernel (lawX μ) (mgenComp μ) 1 (x i) (x' i)
    else (if x i = x' i then 1 else 0)) : ℝ) : ℂ) * f x'

end Defs2

section GN
variable {S : Type} [Fintype S] [DecidableEq S] (D : FinProb S) (G : S → S → Prop) [DecidableRel G]

private def gnN (a : S) : ℝ := ∑ c ∈ univ.filter (G a), D.prob c

private theorem gnN_nonneg (a : S) : 0 ≤ gnN D G a := Finset.sum_nonneg fun c _ => D.nonneg c

private theorem gnN_ge (hG : Equivalence G) (a : S) : D.prob a ≤ gnN D G a :=
  Finset.single_le_sum (f := D.prob) (fun c _ => D.nonneg c) (by simp [hG.refl a])

private theorem gnN_congr (hG : Equivalence G) {a b : S} (h : G a b) : gnN D G a = gnN D G b := by
  unfold gnN
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h1 => hG.trans (hG.symm h) h1, fun h1 => hG.trans h h1⟩

variable {D G}

private theorem gnK_nonneg {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (a b : S) :
    0 ≤ graphNoiseKernel D G ξ a b := by
  unfold graphNoiseKernel
  have h2 : 0 ≤ (if G a b then D.prob b else 0) := by
    split_ifs
    · exact D.nonneg b
    · exact le_rfl
  have h3 := div_nonneg h2 (gnN_nonneg D G a)
  have h4 : 0 ≤ (1 - ξ) * (if a = b then (1:ℝ) else 0) := mul_nonneg (by linarith) (by split_ifs <;> norm_num)
  exact add_nonneg h4 (mul_nonneg h0 h3)

private theorem gnK_rowsum (ξ : ℝ) (a : S) :
    ∑ b, graphNoiseKernel D G ξ a b = (1 - ξ) + ξ * (gnN D G a / gnN D G a) := by
  unfold graphNoiseKernel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
  have e1 : ∑ b, (if a = b then (1:ℝ) else 0) = 1 := by simp
  have e2 : ∑ b, (if G a b then D.prob b else 0) = gnN D G a := by
    unfold gnN; rw [Finset.sum_filter]
  rw [e1, e2]; unfold gnN; ring

private theorem gnK_rowsum_le {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (a : S) :
    ∑ b, graphNoiseKernel D G ξ a b ≤ 1 := by
  rw [gnK_rowsum]
  have : gnN D G a / gnN D G a ≤ 1 := by
    by_cases h : gnN D G a = 0
    · simp [h]
    · rw [div_self h]
  nlinarith

private theorem gnK_rowsum_pos {ξ : ℝ} (hG : Equivalence G) {a : S} (ha : D.prob a ≠ 0) :
    ∑ b, graphNoiseKernel D G ξ a b = 1 := by
  rw [gnK_rowsum]
  have : gnN D G a ≠ 0 := by
    have := gnN_ge D G hG a
    have := D.nonneg a
    intro h; apply ha; linarith
  rw [div_self this]; ring

private theorem gnK_rev (hG : Equivalence G) (ξ : ℝ) (a b : S) :
    D.prob a * graphNoiseKernel D G ξ a b = D.prob b * graphNoiseKernel D G ξ b a := by
  by_cases hab : a = b
  · subst hab; rfl
  · unfold graphNoiseKernel
    by_cases h : G a b
    · have h' : G b a := hG.symm h
      have hN := gnN_congr D G hG h
      unfold gnN at hN
      rw [hN]
      simp only [hab, Ne.symm hab, h, h', if_true, if_false]
      ring
    · have h' : ¬ G b a := fun h'' => h (hG.symm h'')
      simp [hab, Ne.symm hab, h, h']

private theorem gnK_stat (hG : Equivalence G) (ξ : ℝ) (b : S) :
    ∑ a, D.prob a * graphNoiseKernel D G ξ a b = D.prob b := by
  simp_rw [gnK_rev hG ξ _ b, ← Finset.mul_sum]
  by_cases hb : D.prob b = 0
  · simp [hb]
  · rw [gnK_rowsum_pos hG hb, mul_one]

section GN2
variable {S : Type} [Fintype S] [DecidableEq S] {D : FinProb S} {G : S → S → Prop} [DecidableRel G]
  {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem gnW_nonneg {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (x y : ι → S) :
    0 ≤ ∏ i, graphNoiseKernel D G ξ (x i) (y i) :=
  Finset.prod_nonneg fun i _ => gnK_nonneg h0 h1 _ _

private theorem gnW_sum_le {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (x : ι → S) :
    ∑ y : ι → S, ∏ i, graphNoiseKernel D G ξ (x i) (y i) ≤ 1 := by
  rw [← Fintype.prod_sum (fun i b => graphNoiseKernel D G ξ (x i) b)]
  exact Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun b _ => gnK_nonneg h0 h1 _ _)
    (fun i _ => gnK_rowsum_le h0 h1 _)

private theorem gnW_stat (hG : Equivalence G) (ξ : ℝ) (y : ι → S) :
    ∑ x : ι → S, (D.pi ι).prob x * ∏ i, graphNoiseKernel D G ξ (x i) (y i) = (D.pi ι).prob y := by
  have : ∀ x : ι → S, (D.pi ι).prob x * ∏ i, graphNoiseKernel D G ξ (x i) (y i) =
      ∏ i, (D.prob (x i) * graphNoiseKernel D G ξ (x i) (y i)) := fun x => by
    show (∏ i, D.prob (x i)) * _ = _
    rw [Finset.prod_mul_distrib]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i a => D.prob a * graphNoiseKernel D G ξ a (y i))]
  exact Finset.prod_congr rfl fun i _ => gnK_stat hG ξ (y i)

private theorem gn_pointwise {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (h : (ι → S) → ℂ) (x : ι → S) :
    ‖graphNoiseOp D G ξ h x‖ ^ 2 ≤
      ∑ y, (∏ i, graphNoiseKernel D G ξ (x i) (y i)) * ‖h y‖ ^ 2 := by
  set W : (ι → S) → ℝ := fun y => ∏ i, graphNoiseKernel D G ξ (x i) (y i) with hW
  have hW0 : ∀ y, 0 ≤ W y := fun y => gnW_nonneg h0 h1 x y
  have h2 : ‖graphNoiseOp D G ξ h x‖ ≤ ∑ y, Real.sqrt (W y) * (Real.sqrt (W y) * ‖h y‖) := by
    unfold graphNoiseOp
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 y)]
    rw [← mul_assoc, Real.mul_self_sqrt (hW0 y)]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => Real.sqrt (W y))
    (fun y => Real.sqrt (W y) * ‖h y‖)
  have h4 : ∑ y, Real.sqrt (W y) ^ 2 ≤ 1 := by
    simp_rw [Real.sq_sqrt (hW0 _)]
    exact gnW_sum_le h0 h1 x
  have h5 : ∑ y, (Real.sqrt (W y) * ‖h y‖) ^ 2 = ∑ y, W y * ‖h y‖ ^ 2 := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_pow, Real.sq_sqrt (hW0 y)]
  have h6 : 0 ≤ ∑ y, (Real.sqrt (W y) * ‖h y‖) ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  calc ‖graphNoiseOp D G ξ h x‖ ^ 2 ≤ (∑ y, Real.sqrt (W y) * (Real.sqrt (W y) * ‖h y‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ (∑ y, Real.sqrt (W y) ^ 2) * ∑ y, (Real.sqrt (W y) * ‖h y‖) ^ 2 := h3
    _ ≤ 1 * ∑ y, (Real.sqrt (W y) * ‖h y‖) ^ 2 := mul_le_mul_of_nonneg_right h4 h6
    _ = ∑ y, W y * ‖h y‖ ^ 2 := by rw [one_mul, h5]

private theorem gn_contract (hG : Equivalence G) {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1)
    (h : (ι → S) → ℂ) : cl2sq D (graphNoiseOp D G ξ h) ≤ cl2sq D h := by
  unfold cl2sq FinProb.expect
  calc ∑ x, (D.pi ι).prob x * ‖graphNoiseOp D G ξ h x‖ ^ 2
      ≤ ∑ x, (D.pi ι).prob x * ∑ y, (∏ i, graphNoiseKernel D G ξ (x i) (y i)) * ‖h y‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (gn_pointwise h0 h1 h x)
          ((D.pi ι).nonneg x)
    _ = ∑ y, (∑ x, (D.pi ι).prob x * ∏ i, graphNoiseKernel D G ξ (x i) (y i)) * ‖h y‖ ^ 2 := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ y, (D.pi ι).prob y * ‖h y‖ ^ 2 := by
        simp_rw [gnW_stat hG]

private theorem gn_comm_left (hG : Equivalence G) (ξ : ℝ) (T : Finset ι) (g : (ι → S) → ℂ)
    (x : ι → S) :
    ccondExp D T (graphNoiseOp D G ξ g) x =
      ∑ w, ((∏ i, (if i ∈ T then graphNoiseKernel D G ξ (x i) (w i) else D.prob (w i)) : ℝ) : ℂ) *
        g w := by
  unfold ccondExp FinProb.cexpect graphNoiseOp
  have h1 : ∀ y : ι → S, ((D.pi ι).prob y : ℂ) * ∑ w, ((∏ i, graphNoiseKernel D G ξ
      (T.piecewise x y i) (w i) : ℝ) : ℂ) * g w =
      ∑ w, (((D.pi ι).prob y * ∏ i, graphNoiseKernel D G ξ (T.piecewise x y i) (w i) : ℝ) : ℂ) *
        g w := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  have h2 : ∀ y : ι → S, (D.pi ι).prob y * ∏ i, graphNoiseKernel D G ξ (T.piecewise x y i) (w i) =
      ∏ i, (D.prob (y i) * graphNoiseKernel D G ξ (T.piecewise x y i) (w i)) := fun y => by
    show (∏ i, D.prob (y i)) * _ = _
    rw [Finset.prod_mul_distrib]
  simp_rw [h2]
  have h3 : ∀ y : ι → S, ∏ i, (D.prob (y i) * graphNoiseKernel D G ξ (T.piecewise x y i) (w i)) =
      ∏ i, (fun (i : ι) (a : S) => D.prob a * graphNoiseKernel D G ξ
        (if i ∈ T then x i else a) (w i)) i (y i) := fun y => rfl
  simp_rw [h3]
  rw [← Fintype.prod_sum (fun (i : ι) (a : S) => D.prob a * graphNoiseKernel D G ξ
        (if i ∈ T then x i else a) (w i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ T
  · simp only [hi, if_true]
    rw [← Finset.sum_mul, D.sum_eq_one, one_mul]
  · simp only [hi, if_false]
    exact gnK_stat hG ξ (w i)

private theorem gn_swap_inv (T : Finset ι) :
    Function.Involutive (fun p : (ι → S) × (ι → S) => (T.piecewise p.1 p.2, T.piecewise p.2 p.1)) := by
  intro p
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · by_cases h : i ∈ T <;> simp [Finset.piecewise, h]

private theorem gn_comm_right (hG : Equivalence G) (ξ : ℝ) (T : Finset ι) (g : (ι → S) → ℂ)
    (x : ι → S) (hx : ∀ i, D.prob (x i) ≠ 0) :
    graphNoiseOp D G ξ (ccondExp D T g) x =
      ∑ w, ((∏ i, (if i ∈ T then graphNoiseKernel D G ξ (x i) (w i) else D.prob (w i)) : ℝ) : ℂ) *
        g w := by
  unfold graphNoiseOp ccondExp FinProb.cexpect
  have h1 : ∀ v : ι → S, ((∏ i, graphNoiseKernel D G ξ (x i) (v i) : ℝ) : ℂ) *
      ∑ y, (((D.pi ι).prob y : ℝ) : ℂ) * g (T.piecewise v y) =
      ∑ y, (((∏ i, graphNoiseKernel D G ξ (x i) (v i)) * (D.pi ι).prob y : ℝ) : ℂ) *
        g (T.piecewise v y) := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    push_cast; ring
  simp_rw [h1]
  rw [← Fintype.sum_prod_type' (f := fun (v y : ι → S) => (((∏ i, graphNoiseKernel D G ξ (x i) (v i))
    * (D.pi ι).prob y : ℝ) : ℂ) * g (T.piecewise v y))]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (gn_swap_inv (S := S) T))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : ∀ u : ι → S, T.piecewise (T.piecewise w u) (T.piecewise u w) = w := by
    intro u
    funext i
    by_cases h : i ∈ T <;> simp [Finset.piecewise, h]
  simp only [Function.Involutive.coe_toPerm, hw]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  have h2 : ∀ u : ι → S, (∏ i, graphNoiseKernel D G ξ (x i) (T.piecewise w u i)) *
      (D.pi ι).prob (T.piecewise u w) = ∏ i, (fun (i : ι) (b : S) =>
        if i ∈ T then graphNoiseKernel D G ξ (x i) (w i) * D.prob b
        else graphNoiseKernel D G ξ (x i) b * D.prob (w i)) i (u i) := by
    intro u
    show _ * ∏ i, D.prob (T.piecewise u w i) = _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ∈ T <;> simp [Finset.piecewise, h]
  simp_rw [h2]
  rw [← Fintype.prod_sum (fun (i : ι) (b : S) =>
        if i ∈ T then graphNoiseKernel D G ξ (x i) (w i) * D.prob b
        else graphNoiseKernel D G ξ (x i) b * D.prob (w i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ T
  · simp only [hi, if_true]
    rw [← Finset.mul_sum, D.sum_eq_one, mul_one]
  · simp only [hi, if_false]
    rw [← Finset.sum_mul, gnK_rowsum_pos hG (hx i), one_mul]

private theorem gn_ces_comm (hG : Equivalence G) (ξ : ℝ) (A : Finset ι) (g : (ι → S) → ℂ)
    (x : ι → S) (hx : ∀ i, D.prob (x i) ≠ 0) :
    cesPart D A (graphNoiseOp D G ξ g) x = graphNoiseOp D G ξ (cesPart D A g) x := by
  have hc : ∀ T : Finset ι, ccondExp D T (graphNoiseOp D G ξ g) x =
      graphNoiseOp D G ξ (ccondExp D T g) x := fun T => by
    rw [gn_comm_left hG, gn_comm_right hG ξ T g x hx]
  unfold cesPart
  simp_rw [hc]
  unfold graphNoiseOp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun y _ => by ring

private theorem cl2sq_congr_ae (F F' : (ι → S) → ℂ)
    (h : ∀ x, (D.pi ι).prob x ≠ 0 → F x = F' x) : cl2sq D F = cl2sq D F' := by
  unfold cl2sq FinProb.expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (D.pi ι).prob x = 0
  · rw [hx]; simp
  · beta_reduce
    rw [h x hx]

private theorem prob_ne_zero_coord {x : ι → S} (hx : (D.pi ι).prob x ≠ 0) (i : ι) :
    D.prob (x i) ≠ 0 := by
  have : ∏ i, D.prob (x i) ≠ 0 := hx
  exact (Finset.prod_ne_zero_iff.1 this) i (Finset.mem_univ i)

private theorem mg_stab_le (hG : Equivalence G) {ξ ρ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (g : (ι → S) → ℂ) :
    (cstab D ρ (graphNoiseOp D G ξ g)).re ≤ (cstab D ρ g).re := by
  have _ := hρ1
  rw [cstab_eq_sum_cl2sq_cesPart, cstab_eq_sum_cl2sq_cesPart, Complex.ofReal_re, Complex.ofReal_re]
  refine Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ0 _)
  rw [cl2sq_congr_ae (cesPart D A (graphNoiseOp D G ξ g)) (graphNoiseOp D G ξ (cesPart D A g))
    (fun x hx => gn_ces_comm hG ξ A g x (prob_ne_zero_coord hx))]
  exact gn_contract hG hξ0 hξ1 _

end GN2
end GN

/-- `Stab_ρ(R^{⊗} g) ≤ Stab_ρ(g)` for a component-average mixture `R` (the `V_t` invariance of
`merge2`, `E₁`), with `H = {0}`. -/
theorem mgen_stab_graphNoise_le {S : Type} [Fintype S] [DecidableEq S] (D : FinProb S)
    (G : S → S → Prop) [DecidableRel G] (hG : Equivalence G) {ξ ρ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → S) → ℂ) :
    (cstab D ρ (graphNoiseOp D G ξ g)).re ≤ (cstab D ρ g).re :=
  mg_stab_le hG hξ0 hξ1 hρ0 hρ1 g

end MaxT
end TrackB
end RestrictedPolynomials
end
