module

public import RestrictedPolynomials.TrackB.AppBSetting
public import RestrictedPolynomials.TrackB.MergeGenericCoresAux2

/-!
# Track B, Appendix B: Claim `soft_trunc2` (term (V)) on `𝒯`

Paper IV l. 9107-9187; Supplement E `lem:VII-prime` (y-form from `P`-maximality). Paper IV
`claim:soft-trunc2` and the steps `#noisy-mixture-and-restriction`, `#good-event-likely`,
`#maximality-bound`. `ξ` is restricted to `(0, 1/2]` (the mixture weight `ρ^{1-ξ}/2` of
l. 9120 is a probability only for `ξ ≤ 1`; the consumer uses `ξ ≤ 1/100`).

The bad event costs `2 Pr[Ē]`, since `g' = T' g` is `2`-bounded. The `y`-marginal of `μ''` has full
support, so `rr_stab_trivial_master` applies as built.
All proof helpers are `private`.
-/

@[expose] public section

open Finset
open scoped ComplexOrder
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

/-! ### private helpers: push-forwards -/

section PushHelpers

private theorem t2_fp_ext {α : Type} [Fintype α] {A B : FinProb α}
    (h : ∀ a, A.prob a = B.prob a) : A = B := by
  obtain ⟨p1, n1, s1⟩ := A
  obtain ⟨p2, n2, s2⟩ := B
  have : p1 = p2 := funext h
  subst this
  rfl

private theorem t2_push_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (π : FinProb α) (f : α → β) (g : β → γ) :
    mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine t2_fp_ext fun c => ?_
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

private theorem t2_push_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
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

private theorem t2_cexpect_pi_push {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (a : α → β)
    (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (t2_push_sum a (fun _ c => π.prob c) G).symm

private theorem t2_expect_pi_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    {κ : Type} [Fintype κ] [DecidableEq κ] (π : FinProb α) (p : α → β) (φ : (κ → β) → ℝ) :
    ((mergePush π p).pi κ).expect φ = (π.pi κ).expect (fun x => φ (fun i => p (x i))) := by
  unfold FinProb.expect
  symm
  rw [← Finset.sum_fiberwise univ (fun x : κ → α => fun i => p (x i))
    (fun x => (π.pi κ).prob x * φ (fun i => p (x i)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ x ∈ univ.filter (fun x : κ → α => (fun i => p (x i)) = b),
      (π.pi κ).prob x * φ (fun i => p (x i)) = (π.pi κ).prob x * φ b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  show _ = ∏ i, ∑ c ∈ univ.filter (fun c => p c = b i), π.prob c
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Fintype.mem_piFinset, funext_iff]

private theorem t2_norm_cexpect_le {β : Type} [Fintype β] (π : FinProb β) (c : β → ℂ) :
    ‖π.cexpect c‖ ≤ π.expect (fun b => ‖c b‖) := by
  unfold FinProb.cexpect FinProb.expect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (π.nonneg b)]

end PushHelpers

section Corr3Helpers
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
  [DecidableEq C]

private theorem t2_corr3_push {A' B' C' : Type} [Fintype A'] [Fintype B'] [Fintype C']
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinProb (A × B × C)) (Ψ : A × B × C → A' × B' × C') (F : (ι → A') → ℂ)
    (G : (ι → B') → ℂ) (H : (ι → C') → ℂ) :
    corr3 (mergePush μ Ψ) F G H = (μ.pi ι).cexpect fun t =>
      F (fun i => (Ψ (t i)).1) * G (fun i => (Ψ (t i)).2.1) * H (fun i => (Ψ (t i)).2.2) :=
  t2_cexpect_pi_push μ Ψ _

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t2_corr3_smul_left (μ : FinProb (A × B × C)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → A) → ℂ) (G : (ι → B) → ℂ) (H : (ι → C) → ℂ) :
    corr3 μ (fun x => c * F x) G H = c * corr3 μ F G H := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t2_corr3_smul_mid (μ : FinProb (A × B × C)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → A) → ℂ) (G : (ι → B) → ℂ) (H : (ι → C) → ℂ) :
    corr3 μ F (fun y => c * G y) H = c * corr3 μ F G H := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t2_norm_corr3_le {μ : FinProb (A × B × C)} {κ : Type} [Fintype κ]
    [DecidableEq κ] (F : (κ → A) → ℂ) (G : (κ → B) → ℂ) (H : (κ → C) → ℂ) {a b c : ℝ}
    (hF : ∀ x, ‖F x‖ ≤ a) (hG : ∀ y, ‖G y‖ ≤ b) (hH : ∀ z, ‖H z‖ ≤ c) :
    ‖corr3 μ F G H‖ ≤ a * b * c := by
  unfold corr3
  refine (t2_norm_cexpect_le _ _).trans (FinProb.expect_le_const _ fun t => ?_)
  rw [norm_mul, norm_mul]
  have e1 := hF (fun i => (t i).1)
  have e2 := hG (fun i => (t i).2.1)
  have e3 := hH (fun i => (t i).2.2)
  have e4 := norm_nonneg (F fun i => (t i).1)
  have e5 := norm_nonneg (G fun i => (t i).2.1)
  have e6 := norm_nonneg (H fun i => (t i).2.2)
  have ha : 0 ≤ a := e4.trans e1
  have hb : 0 ≤ b := e5.trans e2
  exact mul_le_mul (mul_le_mul e1 e2 e5 ha) e3 e6 (mul_nonneg ha hb)

/-- the joint random restriction of a correlation for the mixture `ν = β νc + (1-β) νr`. -/
private theorem t2_corr3_mix (ν νc νr : FinProb (A × B × C)) {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)
    (hmix : ∀ p, ν.prob p = β * νc.prob p + (1 - β) * νr.prob p) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : (ι → A) → ℂ) (G : (ι → B) → ℂ) (H : (ι → C) → ℂ) :
    corr3 ν F G H = subsetExpect β h0 h1 (fun I => (νr.pi ↥Iᶜ).cexpect (fun t =>
      corr3 νc (restrictFree I (fun i => (t i).1) F) (restrictFree I (fun i => (t i).2.1) G)
        (restrictFree I (fun i => (t i).2.2) H))) := by
  have key := restrict_key h0 h1 νc νr ν hmix
    (fun t : ι → A × B × C => F (fun i => (t i).1) * G (fun i => (t i).2.1) * H (fun i => (t i).2.2))
  unfold corr3
  rw [← key]
  congr 1
  funext I
  congr 1
  funext z
  congr 1
  funext y
  simp only [restrictFree]
  have e1 : (fun i => (glueFree I y z i).1) = glueFree I (fun i => (y i).1) (fun i => (z i).1) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  have e2 : (fun i => (glueFree I y z i).2.1) =
      glueFree I (fun i => (y i).2.1) (fun i => (z i).2.1) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  have e3 : (fun i => (glueFree I y z i).2.2) =
      glueFree I (fun i => (y i).2.2) (fun i => (z i).2.2) := by
    funext i; by_cases hi : i ∈ I <;> simp [glueFree, hi]
  rw [e1, e2, e3]

end Corr3Helpers

section JE
variable {ι : Type} [Fintype ι] [DecidableEq ι] {β : Type} [Fintype β] {s : ℝ} (hs0 : 0 ≤ s)
  (hs1 : s ≤ 1) (ν : FinProb β)

private theorem t2_norm_subsetExpect_le (c : (I : Finset ι) → (↥Iᶜ → β) → ℂ) :
    ‖subsetExpect s hs0 hs1 (fun I => (ν.pi ↥Iᶜ).cexpect (c I))‖ ≤
      mgenCjE s hs0 hs1 ν (fun I t => ‖c I t‖) := by
  unfold subsetExpect mgenCjE
  exact (t2_norm_cexpect_le _ _).trans (FinProb.expect_mono _ fun σ => t2_norm_cexpect_le _ _)

private theorem t2_jE_mono {Φ Ψ : (I : Finset ι) → (↥Iᶜ → β) → ℝ} (h : ∀ I t, Φ I t ≤ Ψ I t) :
    mgenCjE s hs0 hs1 ν Φ ≤ mgenCjE s hs0 hs1 ν Ψ :=
  FinProb.expect_mono _ fun _ => FinProb.expect_mono _ fun t => h _ t

private theorem t2_jE_add (Φ Ψ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => Φ I t + Ψ I t) =
      mgenCjE s hs0 hs1 ν Φ + mgenCjE s hs0 hs1 ν Ψ := by
  unfold mgenCjE
  simp only [FinProb.expect_add]

private theorem t2_jE_mul (c : ℝ) (Φ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => c * Φ I t) = c * mgenCjE s hs0 hs1 ν Φ := by
  unfold mgenCjE
  simp only [FinProb.expect_const_mul]

private theorem t2_jE_const (c : ℝ) : mgenCjE (ι := ι) s hs0 hs1 ν (fun _ _ => c) = c := by
  unfold mgenCjE
  simp

private theorem t2_jE_push {γ : Type} [Fintype γ] [DecidableEq γ] (p : β → γ)
    (Ψ : (I : Finset ι) → (↥Iᶜ → γ) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => Ψ I (fun i => p (t i))) =
      mgenCjE s hs0 hs1 (mergePush ν p) Ψ := by
  unfold mgenCjE
  congr 1
  funext σ
  exact (t2_expect_pi_push ν p _).symm

private theorem t2_mre_ofReal {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α)
    (F : (ι → α) → ℂ) (Ψ : (I : Finset ι) → ((↥I → α) → ℂ) → ℝ) :
    mixtureRestrictionExpect s hs0 hs1 D F (fun I gt => ((Ψ I gt : ℝ) : ℂ)) =
      ((mgenCjE s hs0 hs1 D (fun I z => Ψ I (restrictFree I z F)) : ℝ) : ℂ) := by
  unfold mixtureRestrictionExpect subsetExpect mgenCjE
  simp only [mgenC_cexpect_ofReal]

end JE

/-! ### sup-norm bounds for the noise operators -/

section Bounds

private theorem t2_norm_cnoiseOp_le {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → A) → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : ι → A) : ‖cnoiseOp D r f x‖ ≤ B := by
  have hK : ∀ a b : A, 0 ≤ noiseKernel D r a b := fun a b => by
    unfold noiseKernel
    have := D.nonneg b
    have h2 : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
    have h3 : 0 ≤ 1 - r := by linarith
    positivity
  have hsum : ∑ y : ι → A, ∏ i, noiseKernel D r (x i) (y i) = 1 := by
    rw [← Fintype.prod_sum fun i b => noiseKernel D r (x i) b]
    simp [sum_noiseKernel]
  have hP : ∀ y : ι → A, 0 ≤ ∏ i, noiseKernel D r (x i) (y i) := fun y =>
    Finset.prod_nonneg fun i _ => hK _ _
  unfold cnoiseOp
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y : ι → A, ‖((∏ i, noiseKernel D r (x i) (y i) : ℝ) : ℂ) * f y‖
      ≤ ∑ y : ι → A, (∏ i, noiseKernel D r (x i) (y i)) * B := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP y)]
        exact mul_le_mul_of_nonneg_left (hf y) (hP y)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

private theorem t2_norm_tNE_le {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → A) → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : ι → A) : ‖tNE D r f x‖ ≤ B := by
  rw [tNE_eq_cnoiseOp]
  exact t2_norm_cnoiseOp_le D (by linarith) (by linarith) f hf x

private theorem t2_norm_appTp_le {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → A) → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) (x : ι → A) : ‖appTp D ρ g x‖ ≤ 2 := by
  unfold appTp
  have e1 := t2_norm_tNE_le D (r := ρ / 2) (by linarith) (by linarith) g hg x
  have e2 := t2_norm_tNE_le D (r := ρ) h0 h1 g hg x
  calc ‖(tNE D (ρ / 2) g - tNE D ρ g) x‖ = ‖tNE D (ρ / 2) g x - tNE D ρ g x‖ := rfl
    _ ≤ ‖tNE D (ρ / 2) g x‖ + ‖tNE D ρ g x‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

private theorem t2_cl2norm_le_one {A : Type} [Fintype A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : FinProb A) (f : (ι → A) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) : cl2norm D f ≤ 1 := by
  unfold cl2norm
  rw [Real.sqrt_le_one]
  calc cl2sq D f ≤ ∑ x, (D.pi ι).prob x * 1 := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ((D.pi ι).nonneg x)
        have := hf x
        have h0 := norm_nonneg (f x)
        nlinarith
    _ = 1 := by simp [(D.pi ι).sum_eq_one]

end Bounds

/-! ### the targets -/

section Trunc2
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `#good-event-likely` (l. 9134-9164): `Pr[Ē] ≤ ρ^{ξ/8}` for `E = {Stab_{1-ρ^{ξ/4}}(g'') ≤
ρ^{ξ/8}}`, `g'' = (g')_{J̄→ỹ}`, `g' = T' g`, mixture weight `β = ρ^{1-ξ}/2`; here `D' = μ''_y` has
full support (`y` is unrestricted), so `rr_stab_trivial_master` applies as built. -/
theorem appB_t2_good_event (m : ℕ) {α : ℝ} (hα : 0 < α) {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 2) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₂ →
      ∀ (S : Type) [Fintype S] [DecidableEq S], Fintype.card S ≤ m →
      ∀ D D' D'' : FinProb S, (∀ x, α ≤ D.prob x) → (∀ x, α ≤ D'.prob x) →
        (∀ x, α / 2 ≤ D''.prob x) →
        (∀ x, D.prob x = ρ ^ (1 - ξ) / 2 * D'.prob x + (1 - ρ ^ (1 - ξ) / 2) * D''.prob x) →
      ∀ (h0 : 0 ≤ ρ ^ (1 - ξ) / 2) (h1 : ρ ^ (1 - ξ) / 2 ≤ 1) (ι : Type) [Fintype ι]
        [DecidableEq ι] (g : (ι → S) → ℂ), cl2norm D g ≤ 1 →
        mixtureRestrictionExpect (ρ ^ (1 - ξ) / 2) h0 h1 D'' (appTp D ρ g)
          (fun _ g'' => if ρ ^ (ξ / 8) < (cstab D' (1 - ρ ^ (ξ / 4)) g'').re then (1 : ℂ) else 0) ≤
          ((ρ ^ (ξ / 8) : ℝ) : ℂ) := by
  obtain ⟨c, hc, hrr⟩ := rr_stab_trivial_master (half_pos hα) m
  obtain ⟨δ₀, hδ₀, hg⟩ := appB_stab_gprime_le hξ hξ1
  have ht : 0 < min (c / 2) (2 / c) := lt_min (by positivity) (by positivity)
  refine ⟨min (min δ₀ 1) ((min (c / 2) (2 / c)) ^ (4 / ξ)), lt_min (lt_min hδ₀ one_pos)
    (Real.rpow_pos_of_pos ht _), ?_⟩
  intro ρ hρ0 hρle S _ _ hcard D D' D'' hD hD' hD'' hmix h0 h1 ι _ _ g hgn
  have hρδ : ρ ≤ δ₀ := (hρle.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := (hρle.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hρt : ρ ≤ (min (c / 2) (2 / c)) ^ (4 / ξ) := hρle.trans (min_le_right _ _)
  set q := ρ ^ (ξ / 8) with hqdef
  set b := ρ ^ (ξ / 4) with hbdef
  set a := ρ ^ (1 - ξ) with hadef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hρ0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hρ0 _
  have ha0 : 0 < a := Real.rpow_pos_of_pos hρ0 _
  have hq1 : q ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have hb1 : b ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have ha1 : a ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by linarith)
  have hbq : b = q ^ 2 := by
    rw [hqdef, hbdef, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1
    push_cast
    ring
  have hbt : b ≤ min (c / 2) (2 / c) := by
    have := Real.rpow_le_rpow hρ0.le hρt (by positivity : (0 : ℝ) ≤ ξ / 4)
    rw [← Real.rpow_mul ht.le] at this
    have e : 4 / ξ * (ξ / 4) = 1 := by field_simp
    rw [e, Real.rpow_one] at this
    exact this
  have hbc : b ≤ c / 2 := hbt.trans (min_le_left _ _)
  have hbc' : b ≤ 2 / c := hbt.trans (min_le_right _ _)
  have hρ2 : ρ ^ (1 - ξ / 2) = a * b ^ 2 := by
    rw [hadef, hbdef, ← Real.rpow_natCast (ρ ^ (ξ / 4)), ← Real.rpow_mul hρ0.le,
      ← Real.rpow_add hρ0]
    congr 1
    push_cast
    ring
  -- the restriction inequality
  have hD2 : ∀ x, α / 2 ≤ D.prob x := fun x => (half_le_self hα.le).trans (hD x)
  have hD2' : ∀ x, α / 2 ≤ D'.prob x := fun x => (half_le_self hα.le).trans (hD' x)
  have hβ0 : 0 < a / 2 := by positivity
  have hrr' := hrr (a / 2) hβ0 h1 S hcard D D' D'' hD2 hD2' hD'' hmix b hb0 hb1 ι (appTp D ρ g)
  have hcβδ : c * (a / 2) * b ≤ 1 := by
    have : c * b ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hbc' hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    nlinarith
  have hcmp : ρ ^ (1 - ξ / 2) ≤ c * (a / 2) * b := by
    rw [hρ2]
    nlinarith [mul_le_mul_of_nonneg_left hbc (mul_nonneg ha0.le hb0.le)]
  have hspec : (cstab D (1 - c * (a / 2) * b) (appTp D ρ g)).re ≤ b := by
    have h1' := (Complex.le_def.1 (cstab_mono D (by linarith) (by linarith : 1 - c * (a / 2) * b ≤
      1 - ρ ^ (1 - ξ / 2)) (appTp D ρ g))).1
    exact h1'.trans (hg ρ hρ0 hρδ S D ι g hgn)
  -- the real expectation
  have hre : (mixtureRestrictionExpect (a / 2) h0 h1 D'' (appTp D ρ g)
      (fun _ g'' => cstab D' (1 - b) g'')).re ≤ b := by
    have := (Complex.le_def.1 hrr').1
    exact this.trans hspec
  let Sx : (I : Finset ι) → (↥Iᶜ → S) → ℝ :=
    fun I z => (cstab D' (1 - b) (restrictFree I z (appTp D ρ g))).re
  have hjS : mgenCjE (a / 2) h0 h1 D'' Sx ≤ b := by
    have e : (mixtureRestrictionExpect (a / 2) h0 h1 D'' (appTp D ρ g)
        (fun _ g'' => cstab D' (1 - b) g'')) = mixtureRestrictionExpect (a / 2) h0 h1 D''
        (appTp D ρ g) (fun I gt => (((cstab D' (1 - b) gt).re : ℝ) : ℂ)) := by
      congr 1
      funext I gt
      exact cstab_eq_ofReal_re _ _ _
    rw [e, mgenC_jE_mix] at hre
    exact hre
  let Ψ : (I : Finset ι) → ((↥I → S) → ℂ) → ℝ :=
    fun _ gt => if q < (cstab D' (1 - b) gt).re then (1 : ℝ) else 0
  have hind : ∀ (I : Finset ι) (gt : (↥I → S) → ℂ),
      (if q < (cstab D' (1 - b) gt).re then (1 : ℂ) else 0) = ((Ψ I gt : ℝ) : ℂ) := by
    intro I gt
    simp only [Ψ]
    split_ifs <;> simp
  have e1 : mixtureRestrictionExpect (a / 2) h0 h1 D'' (appTp D ρ g)
      (fun _ g'' => if q < (cstab D' (1 - b) g'').re then (1 : ℂ) else 0) =
      mixtureRestrictionExpect (a / 2) h0 h1 D'' (appTp D ρ g) (fun I gt => ((Ψ I gt : ℝ) : ℂ)) := by
    congr 1
    funext I gt
    exact hind I gt
  show mixtureRestrictionExpect (a / 2) h0 h1 D'' (appTp D ρ g)
    (fun _ g'' => if q < (cstab D' (1 - b) g'').re then (1 : ℂ) else 0) ≤ ((q : ℝ) : ℂ)
  rw [e1, t2_mre_ofReal, Complex.real_le_real]
  have hpt : ∀ (I : Finset ι) (t : ↥Iᶜ → S), Ψ I (restrictFree I t (appTp D ρ g)) ≤
      1 / q * Sx I t := by
    intro I t
    have hσ0 : 0 ≤ Sx I t := (Complex.le_def.1 (cstab_nonneg D' (by linarith) _)).1
    simp only [Ψ, Sx]
    by_cases hσ : q < (cstab D' (1 - b) (restrictFree I t (appTp D ρ g))).re
    · rw [if_pos hσ]
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hq0, one_mul]
      exact hσ.le
    · rw [if_neg hσ]
      exact mul_nonneg (by positivity) hσ0
  calc mgenCjE (a / 2) h0 h1 D'' (fun I z => Ψ I (restrictFree I z (appTp D ρ g)))
      ≤ mgenCjE (a / 2) h0 h1 D'' (fun I t => 1 / q * Sx I t) := t2_jE_mono h0 h1 D'' hpt
    _ = 1 / q * mgenCjE (a / 2) h0 h1 D'' Sx := t2_jE_mul h0 h1 D'' _ _
    _ ≤ 1 / q * b := mul_le_mul_of_nonneg_left hjS (by positivity)
    _ = q := by rw [hbq]; field_simp

end Trunc2

/-! ### the noisy mixture (`#noisy-mixture-and-restriction`) -/

section MixHelpers

/-- abstract mixture splitting: `μ = β μ'' + (1-β) μ'''` with `supp μ'' = R` and atoms `≥ s / |R|`,
when `μ` is large on `R`. -/
private theorem t2_mix_abstract {T : Type} [Fintype T] [DecidableEq T] (μ : FinProb T)
    (R : Finset T) (hR : R.Nonempty) {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (h1 : 2 * β ≤ ∑ p ∈ R, μ.prob p)
    (h2 : ∀ p ∈ R, 2 * β * s / R.card ≤ μ.prob p) :
    ∃ μ'' μ''' : FinProb T, (∀ p, μ.prob p = β * μ''.prob p + (1 - β) * μ'''.prob p) ∧
      (∀ p, μ''.prob p ≠ 0 ↔ p ∈ R) ∧ (∀ p ∈ R, s / R.card ≤ μ''.prob p) := by
  have hcard : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have hM : 0 < ∑ p ∈ R, μ.prob p := by linarith
  set M := ∑ p ∈ R, μ.prob p with hMdef
  let mu2 : T → ℝ := fun p =>
    if p ∈ R then (1 - s) * (μ.prob p / M) + s / R.card else 0
  have hin : ∀ p ∈ R, 0 ≤ (1 - s) * (μ.prob p / M) + s / R.card := fun p _ => by
    have := μ.nonneg p
    have h3 : 0 ≤ 1 - s := by linarith
    positivity
  have hnn : ∀ p, 0 ≤ mu2 p := fun p => by
    simp only [mu2]
    split_ifs with hp
    · exact hin p hp
    · exact le_refl _
  have hsum : ∑ p, mu2 p = 1 := by
    simp only [mu2]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_div, ← hMdef, div_self hM.ne', Finset.sum_const, nsmul_eq_mul,
      mul_div_cancel₀ _ hcard.ne']
    ring
  have hdom : ∀ p, β * mu2 p ≤ μ.prob p := by
    intro p
    simp only [mu2]
    split_ifs with hp
    · have hμp := μ.nonneg p
      have e1 : β * (μ.prob p / M) ≤ μ.prob p / 2 := by
        rw [← mul_div_assoc, div_le_iff₀ hM]
        have : β * μ.prob p ≤ M / 2 * μ.prob p :=
          mul_le_mul_of_nonneg_right (by linarith) hμp
        linarith
      have e2 : β * (s / R.card) ≤ μ.prob p / 2 := by
        have := h2 p hp
        rw [mul_div_assoc] at this
        linarith
      have h3 : 0 ≤ 1 - s := by linarith
      calc β * ((1 - s) * (μ.prob p / M) + s / R.card)
          = (1 - s) * (β * (μ.prob p / M)) + β * (s / R.card) := by ring
        _ ≤ (1 - s) * (μ.prob p / 2) + μ.prob p / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left e1 h3) e2
        _ ≤ μ.prob p := by nlinarith
    · rw [mul_zero]
      exact μ.nonneg p
  have h1β : 0 < 1 - β := by linarith
  refine ⟨⟨mu2, hnn, hsum⟩, ⟨fun p => (μ.prob p - β * mu2 p) / (1 - β),
    fun p => div_nonneg (by linarith [hdom p]) h1β.le, ?_⟩, fun p => ?_, fun p => ?_, fun p hp => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, μ.sum_eq_one, hsum, mul_one,
      div_self h1β.ne']
  · show _ = β * mu2 p + (1 - β) * ((μ.prob p - β * mu2 p) / (1 - β))
    field_simp
    ring
  · show mu2 p ≠ 0 ↔ p ∈ R
    simp only [mu2]
    by_cases hp : p ∈ R
    · rw [if_pos hp]
      have := μ.nonneg p
      have h3 : 0 ≤ 1 - s := by linarith
      have : 0 < (1 - s) * (μ.prob p / M) + s / R.card := by positivity
      exact ⟨fun _ => hp, fun _ => this.ne'⟩
    · rw [if_neg hp]
      exact ⟨fun h => absurd rfl h, fun h => absurd h hp⟩
  · show s / R.card ≤ mu2 p
    simp only [mu2]
    rw [if_pos hp]
    have := μ.nonneg p
    have h3 : 0 ≤ 1 - s := by linarith
    have : 0 ≤ (1 - s) * (μ.prob p / M) := by positivity
    linarith

/-- `(lawY μ).prob y = ∑_x ∑_z μ(x,y,z)`. -/
private theorem t2_lawY_eq {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) (y : Y) :
    (lawY μ).prob y = ∑ x, ∑ z, μ.prob (x, y, z) := by
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.1 = y), μ.prob p = _
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

private theorem t2_le_lawX {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    μ.prob (x, y, z) ≤ (lawX μ).prob x :=
  Finset.single_le_sum (f := μ.prob) (fun c _ => μ.nonneg c)
    (by simp : (x, y, z) ∈ Finset.univ.filter (fun p : X × Y × Z => p.1 = x))

private theorem t2_le_lawY {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (μ : FinProb (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    μ.prob (x, y, z) ≤ (lawY μ).prob y :=
  Finset.single_le_sum (f := μ.prob) (fun c _ => μ.nonneg c)
    (by simp : (x, y, z) ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.1 = y))

private theorem t2_prob_le_one {A : Type} [Fintype A] (π : FinProb A) (a : A) : π.prob a ≤ 1 := by
  rw [← π.sum_eq_one]
  exact Finset.single_le_sum (f := π.prob) (fun b _ => π.nonneg b) (Finset.mem_univ a)

private theorem t2_modest_nonneg {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    (Sm : Finset A) (a b : A) : 0 ≤ s7ModestKernel D Sm a b := by
  unfold s7ModestKernel
  have hb := D.nonneg b
  have h5 : 0 ≤ ∑ c ∈ Sm, D.prob c := Finset.sum_nonneg fun c _ => D.nonneg c
  split_ifs <;> first | positivity | norm_num

private theorem t2_effK_nonneg {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    (Sm : Finset A) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a b : A) :
    0 ≤ s7EffKernel D Sm δ a b := by
  unfold s7EffKernel
  have h3 : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
  have h4 : 0 ≤ 1 - δ := by linarith
  have := t2_modest_nonneg D Sm a b
  positivity

private theorem t2_effK_row {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (Sm : Finset A)
    (hS : 0 < ∑ c ∈ Sm, D.prob c) (δ : ℝ) (a : A) : ∑ b, s7EffKernel D Sm δ a b = 1 := by
  have hm : ∑ b, s7ModestKernel D Sm a b = 1 := by
    unfold s7ModestKernel
    by_cases ha : a ∈ Sm
    · simp only [ha, ite_true]
      rw [show (∑ b, if b ∈ Sm then D.prob b / ∑ c ∈ Sm, D.prob c else 0) =
        ∑ b ∈ Sm, D.prob b / ∑ c ∈ Sm, D.prob c by
          rw [Finset.sum_ite_mem, Finset.univ_inter]]
      rw [← Finset.sum_div, div_self hS.ne']
    · simp [ha]
  unfold s7EffKernel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
  simp

private theorem t2_effK_stay {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    (Sm : Finset A) {δ : ℝ} (h0 : 0 ≤ δ) (a : A) : 1 - δ ≤ s7EffKernel D Sm δ a a := by
  unfold s7EffKernel
  have := t2_modest_nonneg D Sm a a
  have : 0 ≤ δ * s7ModestKernel D Sm a a := mul_nonneg h0 this
  simp only [if_true]
  linarith

private theorem t2_effK_move {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A)
    (Sm : Finset A) (hS : 0 < ∑ c ∈ Sm, D.prob c) (hS1 : ∑ c ∈ Sm, D.prob c ≤ 1) {δ : ℝ}
    (h0 : 0 ≤ δ) {a b : A} (ha : a ∈ Sm) (hb : b ∈ Sm) (hab : a ≠ b) :
    δ * D.prob b ≤ s7EffKernel D Sm δ a b := by
  unfold s7EffKernel s7ModestKernel
  rw [if_neg hab, if_pos ha, if_pos hb]
  have : D.prob b ≤ D.prob b / ∑ c ∈ Sm, D.prob c := by
    rw [le_div_iff₀ hS]
    exact mul_le_of_le_one_right (D.nonneg b) hS1
  have := mul_le_mul_of_nonneg_left this h0
  linarith

end MixHelpers

section Mixture
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `#noisy-mixture-and-restriction` (l. 9115-9132): `x' ∼ E_{non-embed,1-δ'} x`, `δ' = ρ^{1-ξ}`;
`μ' = (δ'/2) μ'' + (1-δ'/2) μ'''`, `supp μ'' = R_VII` (reading `supp μ'`, with `y`
unrestricted), atoms `≥ α'`, `y`-marginal of `μ'''` with atoms `≥ α/2`. -/
theorem appB_t2_mixture (m K : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ α' δ₁ : ℝ, 0 < α' ∧ 0 < δ₁ ∧ δ₁ ≤ 1 ∧ ∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₁ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' →
        ∃ μ' μ'' μ''' : FinProb (X × Y × Z),
          (∀ p, μ'.prob p = ∑ x', ν.prob (x', p.2.1, p.2.2) *
            s7EffKernel (lawX ν) Sm δ' x' p.1) ∧
          (∀ p, μ'.prob p = (δ' / 2) * μ''.prob p + (1 - δ' / 2) * μ'''.prob p) ∧
          μ''.support = rVII ν Sg Sm Phi' ∧ (∀ p ∈ μ''.support, α' ≤ μ''.prob p) ∧
          (∀ y, α / 2 ≤ (lawY μ''').prob y) := by
  refine ⟨α ^ 2 / ((m : ℝ) + 1) ^ 3, min (α / 2) (1 / 2), by positivity,
    lt_min (half_pos hα) (by norm_num), (min_le_right _ _).trans (by norm_num), ?_⟩
  intro δ' hδ0 hδle X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR
  classical
  have hδα : δ' ≤ α / 2 := hδle.trans (min_le_left _ _)
  have hδ12 : δ' ≤ 1 / 2 := hδle.trans (min_le_right _ _)
  obtain ⟨U, instF, instD, a, νt, hUK, hsurj, hsurj', hsub, hpm, hfm, hY2, hT⟩ := hR.wit
  have hYne : Nonempty Y := Fintype.card_pos_iff.1 (by omega)
  have hne : Nonempty (X × Y × Z) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := ν.sum_eq_one
    simp at this
  have hZne : Nonempty Z := ⟨hne.some.2.2⟩
  obtain ⟨y0⟩ := hYne
  obtain ⟨z0⟩ := hZne
  -- basic bounds
  have hα1 : α ≤ 1 := by
    obtain ⟨x, hx⟩ := hR.yz_full y0 z0
    exact (hR.atoms _ hx).trans (t2_prob_le_one ν _)
  have hlX : ∀ x ∈ Sg, α ≤ (lawX ν).prob x := by
    intro x hx
    obtain ⟨z, hz⟩ := hR.xy_full x hx y0
    exact (hR.atoms _ hz).trans (t2_le_lawX ν x y0 z)
  have hlY : ∀ y, α ≤ (lawY ν).prob y := by
    intro y
    obtain ⟨x, hx⟩ := hR.yz_full y z0
    exact (hR.atoms _ hx).trans (t2_le_lawY ν x y z0)
  obtain ⟨x0, hx0⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by norm_num) hR.two)
  have hSm : 0 < ∑ x ∈ Sm, (lawX ν).prob x :=
    lt_of_lt_of_le (lt_of_lt_of_le hα (hlX x0 (hR.sub hx0)))
      (Finset.single_le_sum (f := (lawX ν).prob) (fun c _ => (lawX ν).nonneg c) hx0)
  have hSm1 : ∑ x ∈ Sm, (lawX ν).prob x ≤ 1 := by
    rw [← (lawX ν).sum_eq_one]
    exact Finset.sum_le_univ_sum_of_nonneg fun c => (lawX ν).nonneg c
  -- the noisy law
  obtain ⟨μ', hμ'form, -⟩ := appB_noisyX_law_exists ν Sm hSm hδ0.le (by linarith)
  have hKnn : ∀ x' x, 0 ≤ s7EffKernel (lawX ν) Sm δ' x' x := fun x' x =>
    t2_effK_nonneg (lawX ν) Sm hδ0.le (by linarith) x' x
  have hμ'ge : ∀ (p : X × Y × Z) (x' : X), ν.prob (x', p.2.1, p.2.2) *
      s7EffKernel (lawX ν) Sm δ' x' p.1 ≤ μ'.prob p := by
    intro p x'
    rw [hμ'form p]
    exact Finset.single_le_sum (f := fun x' => ν.prob (x', p.2.1, p.2.2) *
      s7EffKernel (lawX ν) Sm δ' x' p.1) (fun c _ => mul_nonneg (ν.nonneg _) (hKnn _ _))
      (Finset.mem_univ x')
  -- the `y`-marginal of `μ'`
  have hμ'Y : ∀ y, (lawY μ').prob y = (lawY ν).prob y := by
    intro y
    rw [t2_lawY_eq, t2_lawY_eq]
    simp only [hμ'form]
    have e : ∀ z : Z, ∑ x : X, ∑ x' : X, ν.prob (x', y, z) * s7EffKernel (lawX ν) Sm δ' x' x =
        ∑ x' : X, ν.prob (x', y, z) := fun z => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [← Finset.mul_sum, t2_effK_row (lawX ν) Sm hSm, mul_one]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => e z
  -- the set `R`
  let Rf : Finset (X × Y × Z) := Finset.univ.filter (fun p => p ∈ rVII ν Sg Sm Phi')
  have hmemRf : ∀ p, p ∈ Rf ↔ p ∈ rVII ν Sg Sm Phi' := fun p => by simp [Rf]
  -- lower bound on `R`
  have hlow : ∀ p ∈ Rf, α ^ 2 * δ' ≤ μ'.prob p := by
    intro p hp
    obtain ⟨x, y, z⟩ := p
    obtain ⟨hxSg, hzPhi, x', hx'supp, hmod⟩ := (hmemRf _).1 hp
    have hν := hR.atoms _ hx'supp
    have hcase : x' = x ∨ (x' ∈ Sm ∧ x ∈ Sm) := by
      unfold modOf at hmod
      by_cases hx'Sm : x' ∈ Sm
      · rw [if_pos hx'Sm] at hmod
        by_cases hxx : x' = x
        · exact Or.inl hxx
        · exact Or.inr ⟨hx'Sm, hmod⟩
      · rw [if_neg hx'Sm] at hmod
        exact Or.inl (Set.mem_singleton_iff.1 hmod).symm
    have hb := hμ'ge (x, y, z) x'
    simp only at hb
    refine le_trans ?_ hb
    rcases hcase with rfl | ⟨hx'Sm, hxSm⟩
    · have hK := t2_effK_stay (lawX ν) Sm hδ0.le x'
      have h1 : (1 : ℝ) / 2 ≤ 1 - δ' := by linarith
      have h2 : α * (1 / 2) ≤ ν.prob (x', y, z) * s7EffKernel (lawX ν) Sm δ' x' x' :=
        mul_le_mul hν (h1.trans hK) (by norm_num) (ν.nonneg _)
      have : α ^ 2 * δ' ≤ α * (1 / 2) := by nlinarith
      linarith
    · by_cases hxx : x' = x
      · subst hxx
        have hK := t2_effK_stay (lawX ν) Sm hδ0.le x'
        have h1 : (1 : ℝ) / 2 ≤ 1 - δ' := by linarith
        have h2 : α * (1 / 2) ≤ ν.prob (x', y, z) * s7EffKernel (lawX ν) Sm δ' x' x' :=
          mul_le_mul hν (h1.trans hK) (by norm_num) (ν.nonneg _)
        have : α ^ 2 * δ' ≤ α * (1 / 2) := by nlinarith
        linarith
      · have hK := t2_effK_move (lawX ν) Sm hSm hSm1 hδ0.le hx'Sm hxSm hxx
        have hlx := hlX x (hR.sub hxSm)
        have h1 : δ' * α ≤ s7EffKernel (lawX ν) Sm δ' x' x :=
          (mul_le_mul_of_nonneg_left hlx hδ0.le).trans hK
        have h2 : α * (δ' * α) ≤ ν.prob (x', y, z) * s7EffKernel (lawX ν) Sm δ' x' x :=
          mul_le_mul hν h1 (by positivity) (ν.nonneg _)
        nlinarith
  -- a point of `R` with `μ' ≥ α/2`
  have hexR : ∃ p ∈ Rf, α / 2 ≤ μ'.prob p := by
    obtain ⟨_, _, _, ⟨u, v, w⟩, hq⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hT.1
    have hsq := hsub _ hq
    have hmod : ∀ x : X, x ∈ modOf Sm x := fun x => by
      unfold modOf
      split_ifs with h
      · exact h
      · exact rfl
    refine ⟨(a u, v, w.1), (hmemRf _).2 ⟨hsurj u, w.2, a u, hsq, hmod _⟩, ?_⟩
    have hν := hR.atoms _ hsq
    have hb := hμ'ge (a u, v, w.1) (a u)
    simp only at hb
    refine le_trans ?_ hb
    have hK := t2_effK_stay (lawX ν) Sm hδ0.le (a u)
    have h1 : (1 : ℝ) / 2 ≤ 1 - δ' := by linarith
    have h2 : α * (1 / 2) ≤ ν.prob (a u, v, w.1) * s7EffKernel (lawX ν) Sm δ' (a u) (a u) :=
      mul_le_mul hν (h1.trans hK) (by norm_num) (ν.nonneg _)
    linarith
  obtain ⟨p0, hp0Rf, hp0⟩ := hexR
  have hRne : Rf.Nonempty := ⟨p0, hp0Rf⟩
  have hcard1 : (1 : ℝ) ≤ Rf.card := by exact_mod_cast hRne.card_pos
  have hcardle : (Rf.card : ℝ) ≤ ((m : ℝ) + 1) ^ 3 := by
    have h1 : Rf.card ≤ Fintype.card (X × Y × Z) := Finset.card_le_univ _
    have h2 : Fintype.card (X × Y × Z) ≤ m * (m * m) := by
      rw [Fintype.card_prod, Fintype.card_prod]
      exact Nat.mul_le_mul hX (Nat.mul_le_mul hY hZ)
    have h3 : (Rf.card : ℝ) ≤ (m : ℝ) * ((m : ℝ) * m) := by exact_mod_cast h1.trans h2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg hm0 hm0, mul_nonneg hm0 (mul_nonneg hm0 hm0)]
  have hαsq : 0 < α ^ 2 := by positivity
  have hsle : α ^ 2 ≤ 1 := by nlinarith
  -- split
  have h1 : 2 * (δ' / 2) ≤ ∑ p ∈ Rf, μ'.prob p := by
    have := Finset.single_le_sum (f := μ'.prob) (fun c _ => μ'.nonneg c) hp0Rf
    linarith
  have h2 : ∀ p ∈ Rf, 2 * (δ' / 2) * α ^ 2 / Rf.card ≤ μ'.prob p := by
    intro p hp
    have hl := hlow p hp
    have : 2 * (δ' / 2) * α ^ 2 / Rf.card ≤ δ' * α ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ δ' * α ^ 2 := by positivity
      nlinarith
    linarith
  obtain ⟨μ'', μ''', hmix, hsupp, hatom⟩ := t2_mix_abstract μ' Rf hRne (β := δ' / 2)
    (s := α ^ 2) (by positivity) (by linarith) hαsq hsle h1 h2
  refine ⟨μ', μ'', μ''', hμ'form, hmix, ?_, ?_, ?_⟩
  · ext p
    exact (hsupp p).trans (hmemRf p)
  · intro p hp
    have hpR : p ∈ Rf := (hsupp p).1 hp
    refine le_trans ?_ (hatom p hpR)
    exact div_le_div_of_nonneg_left hαsq.le (by linarith) hcardle
  · intro y
    have hmixY : (lawY μ').prob y = δ' / 2 * (lawY μ'').prob y +
        (1 - δ' / 2) * (lawY μ''').prob y := by
      show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.1 = y), μ'.prob p = _ * ∑ p ∈ _, _ + _ * ∑ p ∈ _, _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => hmix p
    have h3 := hlY y
    have h4 := t2_prob_le_one (lawY μ'') y
    have h5 := (lawY μ''').nonneg y
    rw [hμ'Y] at hmixY
    have h6 : 0 ≤ δ' / 2 := by positivity
    nlinarith

end Mixture

/-! ### the maximality bound (`lem:VII-prime`) -/

section MaxHelpers

/-- the lift of `appB_lift_exists` pushes forward to `μ''`. -/
private theorem t2_lift_push {X Y Z U : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] [Fintype U] [DecidableEq U] (a : U → X) {Phi' : Finset Z}
    (μ'' : FinProb (X × Y × Z)) (hs : ∀ p ∈ μ''.support, ∃ u, a u = p.1)
    (hz : ∀ p ∈ μ''.support, p.2.2 ∈ Phi') (ν' : FinProb (U × Y × ↥Phi'))
    (hform : ∀ (u : U) (y : Y) (z : ↥Phi'), ν'.prob (u, y, z) =
      μ''.prob (a u, y, z.1) / (Finset.univ.filter (fun u' => a u' = a u)).card) :
    mergePush ν' (fun q => (a q.1, q.2.1, q.2.2.1)) = μ'' := by
  classical
  refine t2_fp_ext fun p => ?_
  obtain ⟨x, y, z⟩ := p
  show ∑ q ∈ Finset.univ.filter
    (fun q : U × Y × ↥Phi' => (a q.1, q.2.1, q.2.2.1) = (x, y, z)), ν'.prob q = _
  have hterm : ∀ q ∈ Finset.univ.filter
      (fun q : U × Y × ↥Phi' => (a q.1, q.2.1, q.2.2.1) = (x, y, z)),
      ν'.prob q = μ''.prob (x, y, z) / (Finset.univ.filter (fun u' => a u' = x)).card := by
    intro q hq
    obtain ⟨u, y', z'⟩ := q
    have h := (Finset.mem_filter.1 hq).2
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [hform, h1, h2, h3]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  by_cases hp : (x, y, z) ∈ μ''.support
  · obtain ⟨u0, hu0⟩ := hs _ hp
    have hzp : z ∈ Phi' := hz _ hp
    have hu0' : a u0 = x := hu0
    have hkpos : (0 : ℝ) < (Finset.univ.filter (fun u' => a u' = x)).card := by
      exact_mod_cast Finset.card_pos.2 ⟨u0, by simp [hu0']⟩
    have hcard : (Finset.univ.filter
        (fun q : U × Y × ↥Phi' => (a q.1, q.2.1, q.2.2.1) = (x, y, z))).card =
        (Finset.univ.filter (fun u' => a u' = x)).card := by
      refine Finset.card_bij (fun q _ => q.1) ?_ ?_ ?_
      · intro q hq
        have h := (Finset.mem_filter.1 hq).2
        simp only [Prod.mk.injEq] at h
        simp [h.1]
      · intro q1 hq1 q2 hq2 h12
        obtain ⟨u1, y1, z1⟩ := q1
        obtain ⟨u2, y2, z2⟩ := q2
        have h1 := (Finset.mem_filter.1 hq1).2
        have h2 := (Finset.mem_filter.1 hq2).2
        simp only [Prod.mk.injEq] at h1 h2 h12
        subst h12
        have hy : y1 = y2 := h1.2.1.trans h2.2.1.symm
        have hz' : z1 = z2 := Subtype.ext (h1.2.2.trans h2.2.2.symm)
        rw [hy, hz']
      · intro u hu
        have hau : a u = x := (Finset.mem_filter.1 hu).2
        refine ⟨(u, y, ⟨z, hzp⟩), ?_, rfl⟩
        simp [hau]
    rw [hcard]
    exact mul_div_cancel₀ _ hkpos.ne'
  · have h0 : μ''.prob (x, y, z) = 0 := by
      by_contra h
      exact hp h
    rw [h0]
    simp

private theorem t2_cnoiseOp_smul {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (r : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) (g : (ι → A) → ℂ) (x : ι → A) :
    cnoiseOp D r (fun y => c * g y) x = c * cnoiseOp D r g x := by
  unfold cnoiseOp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

private theorem t2_cstab_half {A : Type} [Fintype A] [DecidableEq A] (D : FinProb A) (r : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → A) → ℂ) :
    cstab D r (fun y => (1 / 2 : ℂ) * g y) = (1 / 4 : ℂ) * cstab D r g := by
  unfold cstab FinProb.cexpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  beta_reduce
  rw [t2_cnoiseOp_smul, star_mul']
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this]
  ring

end MaxHelpers

section MaxBound
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- `#maximality-bound` (l. 9166-9187; Lemma `lem:VII-prime`): for `μ''` with support `R_VII` and
atoms `≥ A`, `f'', g''` `2`-bounded, `h'` `1`-bounded, `Stab_{1-ρ^{ξ/4}}(g''; μ''_y) ≤ ρ^{ξ/8}`:
`|E_{μ''} f'' g'' h'| ≤ M ρ^η` (the `y`-form `S_y` of `P(ν'_VII)`, rescaling cost `4`). -/
theorem appB_t2_maximality_bound (m K : ℕ) {A : ℝ} (hA : 0 < A) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ M δ₃ η : ℝ, 1 ≤ M ∧ 0 < δ₃ ∧ δ₃ ≤ 1 ∧ 0 < η ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₃ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ {α : ℝ} (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' → ∀ μ'' : FinProb (X × Y × Z),
          μ''.support = rVII ν Sg Sm Phi' → (∀ p ∈ μ''.support, A ≤ μ''.prob p) →
          ∀ (n : ℕ) (f'' : (Fin n → X) → ℂ) (g'' : (Fin n → Y) → ℂ) (h' : (Fin n → Z) → ℂ),
            (∀ x, ‖f'' x‖ ≤ 2) → (∀ y, ‖g'' y‖ ≤ 2) → (∀ z, ‖h' z‖ ≤ 1) →
            (cstab (lawY μ'') (1 - ρ ^ (ξ / 4)) g'').re ≤ ρ ^ (ξ / 8) →
            ‖corr3 μ'' f'' g'' h'‖ ≤ M * ρ ^ η := by
  obtain ⟨M, δ₀, η, hM1, hδ0, hδ1, hη, hP⟩ :=
    pmax_uniform_constants (max m K) (α := A / ((K : ℝ) + 1)) (by positivity)
  refine ⟨4 * M, δ₀ ^ (8 / ξ), ξ / 8 * η, by linarith, Real.rpow_pos_of_pos hδ0 _,
    Real.rpow_le_one hδ0.le hδ1 (by positivity), by positivity, ?_⟩
  intro ρ hρ0 hρle X Y Z _ _ _ _ _ _ hX hY hZ α ν Sg Sm Phi' hR μ'' hsupp hatoms n f'' g'' h'
    hf hg hh hstab
  classical
  obtain ⟨U, instF, instD, a, νt, hUK, hsurj, hsurj', hsub, hpm, hfm, hY2, hT⟩ := hR.wit
  obtain ⟨hlift, -⟩ := appB_rVII_lift_props K hR a νt hsurj hsurj' hsub hfm hT
  have hs : ∀ p ∈ μ''.support, ∃ u, a u = p.1 := by
    intro p hp
    rw [hsupp] at hp
    exact hsurj' p.1 hp.1
  have hz : ∀ p ∈ μ''.support, p.2.2 ∈ Phi' := by
    intro p hp
    rw [hsupp] at hp
    exact hp.2.1
  obtain ⟨ν', hform, hνsupp, hνatoms⟩ := appB_lift_exists a μ'' hs hz
  have hpush := t2_lift_push a μ'' hs hz ν' hform
  have hsubset : νt.support ⊂ ν'.support := by
    rw [hνsupp, hsupp]
    exact hlift
  have hUpos : (0 : ℝ) < Fintype.card U := by
    obtain ⟨_, _, _, ⟨u, v, w⟩, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hT.1
    exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  have hat : ∀ p ∈ ν'.support, A / ((K : ℝ) + 1) ≤ ν'.prob p := by
    intro q hq
    refine le_trans ?_ (hνatoms A hatoms q hq)
    refine div_le_div_of_nonneg_left hA.le hUpos ?_
    have : (Fintype.card U : ℝ) ≤ K := by exact_mod_cast hUK
    linarith
  have hcardPhi : Fintype.card ↥Phi' ≤ max m K := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans (hZ.trans (le_max_left _ _))
  have hPS := hP U Y ↥Phi' (hUK.trans (le_max_right _ _)) (hY.trans (le_max_left _ _)) hcardPhi
    νt.support hpm ν' hsubset hat
  have hSY := hPS.2.1
  set δ := ρ ^ (ξ / 8) with hδdef
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hρ0 _
  have hρ1 : ρ ≤ 1 := hρle.trans (Real.rpow_le_one hδ0.le hδ1 (by positivity))
  have hδ1' : δ ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have hδle : δ ≤ δ₀ := by
    have := Real.rpow_le_rpow hρ0.le hρle (by positivity : (0 : ℝ) ≤ ξ / 8)
    rw [← Real.rpow_mul hδ0.le] at this
    have e : 8 / ξ * (ξ / 8) = 1 := by field_simp
    rw [e, Real.rpow_one] at this
    exact this
  have hbq : ρ ^ (ξ / 4) = δ ^ 2 := by
    rw [hδdef, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1
    push_cast
    ring
  have hlaw : lawY ν' = lawY μ'' := by
    unfold lawY
    rw [← hpush, t2_push_comp]
  -- the rescaled functions
  let F1 : (Fin n → U) → ℂ := fun w => (1 / 2 : ℂ) * f'' (fun i => a (w i))
  let G1 : (Fin n → Y) → ℂ := fun y => (1 / 2 : ℂ) * g'' y
  let H1 : (Fin n → ↥Phi') → ℂ := fun w => h' (fun i => (w i).1)
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have hF1 : ∀ w, ‖F1 w‖ ≤ 1 := fun w => by
    simp only [F1]
    rw [norm_mul, hhalf]
    have := hf (fun i => a (w i))
    linarith
  have hG1 : ∀ y, ‖G1 y‖ ≤ 1 := fun y => by
    simp only [G1]
    rw [norm_mul, hhalf]
    have := hg y
    linarith
  have hH1 : ∀ w, ‖H1 w‖ ≤ 1 := fun w => hh _
  have hst : (cstab (lawY ν') (1 - δ) G1).re ≤ δ := by
    have e : cstab (lawY ν') (1 - δ) G1 = (1 / 4 : ℂ) * cstab (lawY μ'') (1 - δ) g'' := by
      rw [hlaw]
      exact t2_cstab_half _ _ _
    have hmono := (Complex.le_def.1 (cstab_mono (lawY μ'') (by linarith : 0 ≤ 1 - δ)
      (by nlinarith : 1 - δ ≤ 1 - ρ ^ (ξ / 4)) g'')).1
    have h1 : (cstab (lawY μ'') (1 - δ) g'').re ≤ δ := by
      refine hmono.trans (hstab.trans ?_)
      exact le_refl _
    rw [e]
    have : ((1 / 4 : ℂ) * cstab (lawY μ'') (1 - δ) g'').re =
        1 / 4 * (cstab (lawY μ'') (1 - δ) g'').re := by
      have h14 : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [h14, Complex.re_ofReal_mul]
    rw [this]
    linarith
  have hbd := hSY δ hδpos hδle n F1 G1 H1 hF1 hG1 hH1 hst
  have e1 : corr3 μ'' f'' g'' h' = corr3 ν' (fun w : Fin n → U => f'' (fun i => a (w i))) g''
      H1 := by
    rw [← hpush]
    exact t2_corr3_push ν' _ f'' g'' h'
  have e2 : corr3 ν' F1 G1 H1 = (1 / 2 : ℂ) * ((1 / 2 : ℂ) * corr3 μ'' f'' g'' h') := by
    rw [e1]
    simp only [F1, G1]
    rw [t2_corr3_smul_left, t2_corr3_smul_mid]
  have e3 : corr3 μ'' f'' g'' h' = 4 * corr3 ν' F1 G1 H1 := by
    rw [e2]
    ring
  rw [e3, norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simpa using Complex.norm_natCast 4
  rw [h4]
  have hpow : δ ^ η = ρ ^ (ξ / 8 * η) := by
    rw [hδdef, ← Real.rpow_mul hρ0.le]
  rw [hpow] at hbd
  calc 4 * ‖corr3 ν' F1 G1 H1‖ ≤ 4 * (M * ρ ^ (ξ / 8 * η)) :=
        mul_le_mul_of_nonneg_left hbd (by norm_num)
    _ = 4 * M * ρ ^ (ξ / 8 * η) := by ring

end MaxBound

/-! ### assembly: Claim `soft_trunc2` -/

section Assembly
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
private theorem t2_corr3_reindex (ν : FinProb (X × Y × Z)) {κ : Type} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (e : κ ≃ Fin n) (f : (κ → X) → ℂ) (g : (κ → Y) → ℂ) (h : (κ → Z) → ℂ) :
    corr3 ν (fun x : Fin n → X => f (x ∘ e)) (fun y => g (y ∘ e)) (fun z => h (z ∘ e)) =
      corr3 ν f g h := by
  unfold corr3
  rw [← cexpect_pi_equiv e ν]
  congr 1
  funext y
  simp [Function.comp_def]

private theorem t2_cstab_reindex {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (ρ : ℝ)
    {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n) (g : (κ → α) → ℂ) :
    cstab D ρ (fun y : Fin n → α => g (y ∘ e)) = cstab D ρ g := by
  have := cstab_equiv e.symm D ρ g
  rwa [Equiv.symm_symm] at this

/-- the bound of the maximality lemma on an arbitrary finite index type. -/
private theorem t2_gen_index (μ : FinProb (X × Y × Z)) (r q B : ℝ)
    (hfin : ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
      (∀ x, ‖f x‖ ≤ 2) → (∀ y, ‖g y‖ ≤ 2) → (∀ z, ‖h z‖ ≤ 1) →
      (cstab (lawY μ) (1 - r) g).re ≤ q → ‖corr3 μ f g h‖ ≤ B)
    {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → X) → ℂ) (g : (κ → Y) → ℂ)
    (h : (κ → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 2) (hg : ∀ y, ‖g y‖ ≤ 2) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hs : (cstab (lawY μ) (1 - r) g).re ≤ q) : ‖corr3 μ f g h‖ ≤ B := by
  have := hfin (Fintype.card κ) (fun x => f (x ∘ Fintype.equivFin κ))
    (fun y => g (y ∘ Fintype.equivFin κ)) (fun z => h (z ∘ Fintype.equivFin κ))
    (fun x => hf _) (fun y => hg _) (fun z => hh _)
    (by rw [t2_cstab_reindex]; exact hs)
  rwa [t2_corr3_reindex] at this

private theorem t2_rel_basic {K : ℕ} {α : ℝ} {ν : FinProb (X × Y × Z)} {Sg Sm : Finset X}
    {Phi' : Finset Z} (hα : 0 < α) (hR : Rel67 K α ν Sg Sm Phi') :
    (∀ y, α ≤ (lawY ν).prob y) ∧ 0 < ∑ x ∈ Sm, (lawX ν).prob x := by
  obtain ⟨U, instF, instD, a, νt, hUK, hsurj, hsurj', hsub, hpm, hfm, hY2, hT⟩ := hR.wit
  have hYne : Nonempty Y := Fintype.card_pos_iff.1 (by omega)
  have hne : Nonempty (X × Y × Z) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := ν.sum_eq_one
    simp at this
  have hZne : Nonempty Z := ⟨hne.some.2.2⟩
  obtain ⟨y0⟩ := hYne
  obtain ⟨z0⟩ := hZne
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hR.yz_full y z0
    exact (hR.atoms _ hx).trans (t2_le_lawY ν x y z0)
  · obtain ⟨x0, hx0⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by norm_num) hR.two)
    obtain ⟨z, hz⟩ := hR.xy_full x0 (hR.sub hx0) y0
    have h1 : α ≤ (lawX ν).prob x0 := (hR.atoms _ hz).trans (t2_le_lawX ν x0 y0 z)
    exact lt_of_lt_of_le (lt_of_lt_of_le hα h1)
      (Finset.single_le_sum (f := (lawX ν).prob) (fun c _ => (lawX ν).nonneg c) hx0)

private theorem t2_lawY_mu {K : ℕ} {α A : ℝ} {ν : FinProb (X × Y × Z)} {Sg Sm : Finset X}
    {Phi' : Finset Z} (hR : Rel67 K α ν Sg Sm Phi') (μ'' : FinProb (X × Y × Z))
    (hsupp : μ''.support = rVII ν Sg Sm Phi') (hatoms : ∀ p ∈ μ''.support, A ≤ μ''.prob p)
    (y : Y) : A ≤ (lawY μ'').prob y := by
  obtain ⟨U, instF, instD, a, νt, hUK, hsurj, hsurj', hsub, hpm, hfm, hY2, hT⟩ := hR.wit
  obtain ⟨u, w, hq⟩ := MaxT.PairwiseConnected3.exists_atom_y hT.1 y
  have hsq := hsub _ hq
  have hmod : ∀ x : X, x ∈ modOf Sm x := fun x => by
    unfold modOf
    split_ifs with h
    · exact h
    · exact rfl
  have hp : (a u, y, w.1) ∈ μ''.support := by
    rw [hsupp]
    exact ⟨hsurj u, w.2, a u, hsq, hmod _⟩
  exact (hatoms _ hp).trans (t2_le_lawY μ'' (a u) y w.1)

private theorem t2_noisyX_lawY {ν : FinProb (X × Y × Z)} {Sm : Finset X}
    (hSm : 0 < ∑ x ∈ Sm, (lawX ν).prob x) {δ' : ℝ} (μ' : FinProb (X × Y × Z))
    (hform : ∀ p, μ'.prob p = ∑ x', ν.prob (x', p.2.1, p.2.2) *
      s7EffKernel (lawX ν) Sm δ' x' p.1) (y : Y) : (lawY μ').prob y = (lawY ν).prob y := by
  rw [t2_lawY_eq, t2_lawY_eq]
  simp only [hform]
  have e : ∀ z : Z, ∑ x : X, ∑ x' : X, ν.prob (x', y, z) * s7EffKernel (lawX ν) Sm δ' x' x =
      ∑ x' : X, ν.prob (x', y, z) := fun z => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [← Finset.mul_sum, t2_effK_row (lawX ν) Sm hSm, mul_one]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => e z

/-- Claim `soft_trunc2` (l. 9107-9110): `(V) ≤ M ρ^η` for `0 < ρ ≤ δ₀`, `0 < ξ ≤ 1/2`, constants
depending on `(m, K, α, ξ)` only. -/
theorem appB_soft_trunc2 (m K : ℕ) {α : ℝ} (hα : 0 < α) {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 2) :
    ∃ M δ₀ η : ℝ, 1 ≤ M ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ (ν : FinProb (X × Y × Z)) (Sg Sm : Finset X) (Phi' : Finset Z),
          Rel67 K α ν Sg Sm Phi' →
        ∀ (n : ℕ) (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ) (h : (Fin n → Z) → ℂ),
          (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) → (∀ z, ‖h z‖ ≤ 1) →
          termV ν Sm ρ ξ f g h ≤ M * ρ ^ η := by
  obtain ⟨α', δ₁, hα', hδ₁, hδ₁1, hmixt⟩ := appB_t2_mixture m K hα
  have hαg : 0 < min α α' := lt_min hα hα'
  obtain ⟨δ₂, hδ₂, hgood⟩ := appB_t2_good_event m hαg hξ hξ1
  obtain ⟨M₃, δ₃, η₃, hM₃, hδ₃, hδ₃1, hη₃, hmax⟩ := appB_t2_maximality_bound m K hα' hξ
  have hξ1' : 0 < 1 - ξ := by linarith
  refine ⟨M₃ + 2, min (min (δ₁ ^ (1 / (1 - ξ))) δ₂) δ₃, min η₃ (ξ / 8), by linarith,
    lt_min (lt_min (Real.rpow_pos_of_pos hδ₁ _) hδ₂) hδ₃, (min_le_right _ _).trans hδ₃1,
    lt_min hη₃ (by positivity), ?_⟩
  intro ρ hρ0 hρle X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR n f g h hf hg hh
  classical
  have hρ1 : ρ ≤ 1 := hρle.trans ((min_le_right _ _).trans hδ₃1)
  have hρδ₁ : ρ ≤ δ₁ ^ (1 / (1 - ξ)) := (hρle.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hρδ₂ : ρ ≤ δ₂ := (hρle.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hρδ₃ : ρ ≤ δ₃ := hρle.trans (min_le_right _ _)
  have hδ'0 : 0 < ρ ^ (1 - ξ) := Real.rpow_pos_of_pos hρ0 _
  have hδ'1 : ρ ^ (1 - ξ) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 hξ1'.le
  have hδ'δ₁ : ρ ^ (1 - ξ) ≤ δ₁ := by
    have := Real.rpow_le_rpow hρ0.le hρδ₁ hξ1'.le
    rw [← Real.rpow_mul hδ₁.le] at this
    have e : 1 / (1 - ξ) * (1 - ξ) = 1 := by field_simp
    rw [e, Real.rpow_one] at this
    exact this
  obtain ⟨μ', μ'', μ''', hform, hmix, hsupp, hatom, hY3⟩ :=
    hmixt (ρ ^ (1 - ξ)) hδ'0 hδ'δ₁ X Y Z hX hY hZ ν Sg Sm Phi' hR
  obtain ⟨hlYν, hSm⟩ := t2_rel_basic hα hR
  have hlaw : ∀ y, (lawY μ').prob y = (lawY ν).prob y := t2_noisyX_lawY hSm μ' hform
  have hβ0 : 0 ≤ ρ ^ (1 - ξ) / 2 := by positivity
  have hβ1 : ρ ^ (1 - ξ) / 2 ≤ 1 := by linarith
  -- the noisy law
  obtain ⟨μ0, hf0, hc0⟩ := appB_noisyX_law_exists ν Sm hSm hδ'0.le hδ'1
  have hμ0 : μ0 = μ' := t2_fp_ext fun p => by rw [hf0 p, hform p]
  set f' := tNE (lawX ν) (ρ ^ (1 + ξ)) f with hf'def
  set g' := appTp (lawY ν) ρ g with hg'def
  have hf' : ∀ x, ‖f' x‖ ≤ 1 := fun x => by
    refine t2_norm_tNE_le (lawX ν) (r := ρ ^ (1 + ξ)) (Real.rpow_pos_of_pos hρ0 _).le
      (Real.rpow_le_one hρ0.le hρ1 (by linarith)) f hf x
  have hg' : ∀ y, ‖g' y‖ ≤ 2 := fun y => t2_norm_appTp_le (lawY ν) hρ0.le hρ1 g hg y
  have hterm : termV ν Sm ρ ξ f g h = ‖corr3 μ' f' g' h‖ := by
    unfold termV
    rw [hc0, hμ0]
  -- the restriction identity
  let q : ℝ := ρ ^ (ξ / 8)
  let Ψ : (I : Finset (Fin n)) → ((↥I → Y) → ℂ) → ℝ :=
    fun _ gt => if q < (cstab (lawY μ'') (1 - ρ ^ (ξ / 4)) gt).re then (1 : ℝ) else 0
  -- good event
  have hY' : ∀ y, min α α' ≤ (lawY ν).prob y := fun y => (min_le_left _ _).trans (hlYν y)
  have hY'' : ∀ y, min α α' ≤ (lawY μ'').prob y := fun y =>
    (min_le_right _ _).trans (t2_lawY_mu hR μ'' hsupp hatom y)
  have hY''' : ∀ y, min α α' / 2 ≤ (lawY μ''').prob y := fun y => by
    have := min_le_left α α'
    exact (by linarith : min α α' / 2 ≤ α / 2).trans (hY3 y)
  have hmixY : ∀ y, (lawY ν).prob y = ρ ^ (1 - ξ) / 2 * (lawY μ'').prob y +
      (1 - ρ ^ (1 - ξ) / 2) * (lawY μ''').prob y := by
    intro y
    rw [← hlaw y]
    show ∑ p ∈ Finset.univ.filter (fun p : X × Y × Z => p.2.1 = y), μ'.prob p = _ * ∑ p ∈ _, _ +
      _ * ∑ p ∈ _, _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hmix p
  have hge := hgood ρ hρ0 hρδ₂ Y hY (lawY ν) (lawY μ'') (lawY μ''') hY' hY'' hY''' hmixY hβ0 hβ1
    (Fin n) g (t2_cl2norm_le_one _ g hg)
  have hind : ∀ (I : Finset (Fin n)) (gt : (↥I → Y) → ℂ),
      (if ρ ^ (ξ / 8) < (cstab (lawY μ'') (1 - ρ ^ (ξ / 4)) gt).re then (1 : ℂ) else 0) =
        ((Ψ I gt : ℝ) : ℂ) := by
    intro I gt
    simp only [Ψ, q]
    split_ifs <;> simp
  have hge' : mgenCjE (ρ ^ (1 - ξ) / 2) hβ0 hβ1 (lawY μ''')
      (fun I z => Ψ I (restrictFree I z g')) ≤ q := by
    have e1 : mixtureRestrictionExpect (ρ ^ (1 - ξ) / 2) hβ0 hβ1 (lawY μ''') (appTp (lawY ν) ρ g)
        (fun _ g'' => if ρ ^ (ξ / 8) < (cstab (lawY μ'') (1 - ρ ^ (ξ / 4)) g'').re then
          (1 : ℂ) else 0) = mixtureRestrictionExpect (ρ ^ (1 - ξ) / 2) hβ0 hβ1 (lawY μ''')
          (appTp (lawY ν) ρ g) (fun I gt => ((Ψ I gt : ℝ) : ℂ)) := by
      congr 1
      funext I gt
      exact hind I gt
    rw [e1, t2_mre_ofReal, Complex.real_le_real] at hge
    exact hge
  -- the pointwise estimate
  have hmaxI : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (F : (κ → X) → ℂ) (G : (κ → Y) → ℂ)
      (H : (κ → Z) → ℂ), (∀ x, ‖F x‖ ≤ 2) → (∀ y, ‖G y‖ ≤ 2) → (∀ z, ‖H z‖ ≤ 1) →
      (cstab (lawY μ'') (1 - ρ ^ (ξ / 4)) G).re ≤ ρ ^ (ξ / 8) →
      ‖corr3 μ'' F G H‖ ≤ M₃ * ρ ^ η₃ := by
    intro κ _ _ F G H hF hG hH hs
    exact t2_gen_index μ'' (ρ ^ (ξ / 4)) (ρ ^ (ξ / 8)) (M₃ * ρ ^ η₃)
      (fun n' f'' g'' h' hf'' hg'' hh' hs' =>
        hmax ρ hρ0 hρδ₃ X Y Z hX hY hZ ν Sg Sm Phi' hR μ'' hsupp hatom n' f'' g'' h' hf'' hg''
          hh' hs') F G H hF hG hH hs
  have hpt : ∀ (I : Finset (Fin n)) (t : ↥Iᶜ → X × Y × Z),
      ‖corr3 μ'' (restrictFree I (fun i => (t i).1) f') (restrictFree I (fun i => (t i).2.1) g')
        (restrictFree I (fun i => (t i).2.2) h)‖ ≤
      M₃ * ρ ^ η₃ + 2 * Ψ I (restrictFree I (fun i => (t i).2.1) g') := by
    intro I t
    have hnn : 0 ≤ M₃ * ρ ^ η₃ := mul_nonneg (by linarith) (Real.rpow_pos_of_pos hρ0 _).le
    by_cases hbad : q < (cstab (lawY μ'') (1 - ρ ^ (ξ / 4))
        (restrictFree I (fun i => (t i).2.1) g')).re
    · have h1 : Ψ I (restrictFree I (fun i => (t i).2.1) g') = 1 := by
        simp only [Ψ]
        rw [if_pos hbad]
      rw [h1]
      have h2 := t2_norm_corr3_le (μ := μ'') (restrictFree I (fun i => (t i).1) f')
        (restrictFree I (fun i => (t i).2.1) g') (restrictFree I (fun i => (t i).2.2) h)
        (a := 1) (b := 2) (c := 1) (fun _ => hf' _) (fun _ => hg' _) (fun _ => hh _)
      linarith
    · have h1 : Ψ I (restrictFree I (fun i => (t i).2.1) g') = 0 := by
        simp only [Ψ]
        rw [if_neg hbad]
      rw [h1]
      have h2 := hmaxI ↥I (restrictFree I (fun i => (t i).1) f')
        (restrictFree I (fun i => (t i).2.1) g') (restrictFree I (fun i => (t i).2.2) h)
        (fun _ => (hf' _).trans (by norm_num)) (fun _ => hg' _) (fun _ => hh _)
        (not_lt.1 hbad)
      linarith
  have hbound : ‖corr3 μ' f' g' h‖ ≤ M₃ * ρ ^ η₃ + 2 * ρ ^ (ξ / 8) := by
    rw [t2_corr3_mix μ' μ'' μ''' hβ0 hβ1 hmix f' g' h]
    refine (t2_norm_subsetExpect_le hβ0 hβ1 μ''' _).trans ?_
    refine (t2_jE_mono hβ0 hβ1 μ''' hpt).trans ?_
    rw [t2_jE_add hβ0 hβ1 μ''' (fun _ _ => M₃ * ρ ^ η₃)
      (fun I t => 2 * Ψ I (restrictFree I (fun i => (t i).2.1) g')),
      t2_jE_const hβ0 hβ1 μ''',
      t2_jE_mul hβ0 hβ1 μ''' 2 (fun I t => Ψ I (restrictFree I (fun i => (t i).2.1) g'))]
    have hp : mgenCjE (ρ ^ (1 - ξ) / 2) hβ0 hβ1 μ'''
        (fun I t => Ψ I (restrictFree I (fun i => (t i).2.1) g')) =
        mgenCjE (ρ ^ (1 - ξ) / 2) hβ0 hβ1 (lawY μ''')
          (fun I z => Ψ I (restrictFree I z g')) :=
      t2_jE_push hβ0 hβ1 μ''' (fun q => q.2.1) (fun I z => Ψ I (restrictFree I z g'))
    rw [hp]
    linarith
  -- conclusion
  rw [hterm]
  have hη1 : ρ ^ η₃ ≤ ρ ^ (min η₃ (ξ / 8)) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (min_le_left _ _)
  have hη2 : ρ ^ (ξ / 8) ≤ ρ ^ (min η₃ (ξ / 8)) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (min_le_right _ _)
  have := mul_le_mul_of_nonneg_left hη1 (by linarith : 0 ≤ M₃)
  linarith

end Assembly

end TrackB
end RestrictedPolynomials
end
