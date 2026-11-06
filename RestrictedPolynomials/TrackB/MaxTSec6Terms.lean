module

public import RestrictedPolynomials.TrackB.MaxTSec6Support
public import RestrictedPolynomials.TrackB.MergeGenericCores
public import RestrictedPolynomials.TrackB.NoiseClaims
public import RestrictedPolynomials.TrackB.PathTrickInequality
public import RestrictedPolynomials.TrackB.K6UniformAtoms

/-!
# Track B: the analytic terms of Thm 6.5′ on `𝒯`

Supplement E: `lem:III-prime` (d), (e),
`lem:VII-prime` (d), (e), `lem:ugly-prime` (§6.4), and paper IV `writeup_stability.tex` l. 3642-3684
(the same-support transfer of the proof of Thm 6.5, paper IV
`thm:nonembed-deg-must-be-small-rephrase-maximal2`, step `same-support-transfer`).

Readings:
* The same-support transfer splits `ν = β ν₀ + (1-β) ν''` with `β = α'/2`; the printed
  `(M+1) δ^{s/2}` needs `s ≤ 1`, so the exponent is `min η 1 / 2`, and the threshold is `δ ≤ κ δ₀²` with
  `κ = min(1, (cβ)²)`, `c = c(m, α'/2)` of `rr_stab_trivial_master`.
* The terms (III), (VII) are stated at the push-forward level (`hpush`); the atom bound of the lift
  is not part of the statements.
* The ugly modest case is in constants-map form and conditional on the merge core `hmerge`
  (the exact text of `mgen_sStmtY_of_mergeX`).

Route of the ugly case: the richer law `𝒟` is taken uniform on `diagSupportSet` (only its support and
atoms enter `hD`), `ν'_c` is its push-forward along `(x,y,z) ↦ (a(x,…,x), y, (z,…,z))` (so
`φ_{ν'_c}(F, g, H) = φ_𝒟(F^♯, g, H^♯)` and `𝒟_y = (ν'_c)_y` hold as identities), the split of `ν'` is the
same mixture transfer as for the same-support transfer above, then `hmerge` and Lemma 3.9 twice (`m65T_sStmtY_of_mu2`).

The two shared public helpers (prefix `m65T`, needed again by the case `|Σ_modest| = 2` in
`MaxTSec6Relaxed65`) are the path-trick reduction `m65T_sStmtY_of_mu2` and the atom bound
`m65T_mu2_atom_ge`; the alphabet bounds are instances of the built `card_pathX_le`. All other
helpers are `private`. The atom bound of a path trick is the built `k6pt_pathTrick_atom_ge`
(`K6UniformAtoms`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
namespace MaxT

/-! ### private helpers: laws, push-forwards, reindexing -/

section PushHelpers

private theorem t65_fp_ext {α : Type} [Fintype α] {A B : FinProb α}
    (h : ∀ a, A.prob a = B.prob a) : A = B := by
  obtain ⟨p1, n1, s1⟩ := A
  obtain ⟨p2, n2, s2⟩ := B
  have : p1 = p2 := funext h
  subst this
  rfl

private theorem t65_prob_le_one {α : Type} [Fintype α] (π : FinProb α) (a : α) : π.prob a ≤ 1 := by
  rw [← π.sum_eq_one]
  exact Finset.single_le_sum (f := π.prob) (fun b _ => π.nonneg b) (Finset.mem_univ a)

private theorem t65_exists_mem_support {α : Type} [Fintype α] (π : FinProb α) :
    ∃ a, a ∈ π.support := by
  by_contra h
  have h0 : ∑ a, π.prob a = 0 := Finset.sum_eq_zero fun a _ => by
    by_contra ha
    exact h ⟨a, ha⟩
  rw [π.sum_eq_one] at h0
  exact one_ne_zero h0

private theorem t65_atom_le_one {α : Type} [Fintype α] (π : FinProb α) {c : ℝ}
    (h : ∀ p ∈ π.support, c ≤ π.prob p) : c ≤ 1 := by
  obtain ⟨a, ha⟩ := t65_exists_mem_support π
  exact (h a ha).trans (t65_prob_le_one π a)

private theorem t65_push_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (π : FinProb α) (f : α → β) (g : β → γ) :
    mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine t65_fp_ext fun c => ?_
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

private theorem t65_push_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
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

private theorem t65_cexpect_pi_push {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (a : α → β)
    (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (t65_push_sum a (fun _ c => π.prob c) G).symm

private theorem t65_expect_pi_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
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

private theorem t65_norm_cexpect_le {β : Type} [Fintype β] (π : FinProb β) (c : β → ℂ) :
    ‖π.cexpect c‖ ≤ π.expect (fun b => ‖c b‖) := by
  unfold FinProb.cexpect FinProb.expect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (π.nonneg b)]

end PushHelpers

section Corr3Helpers
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
  [DecidableEq C]

/-- the correlation under a push-forward law. -/
private theorem t65_corr3_push {A' B' C' : Type} [Fintype A'] [Fintype B'] [Fintype C']
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinProb (A × B × C)) (Ψ : A × B × C → A' × B' × C') (F : (ι → A') → ℂ)
    (G : (ι → B') → ℂ) (H : (ι → C') → ℂ) :
    corr3 (mergePush μ Ψ) F G H = (μ.pi ι).cexpect fun t =>
      F (fun i => (Ψ (t i)).1) * G (fun i => (Ψ (t i)).2.1) * H (fun i => (Ψ (t i)).2.2) :=
  t65_cexpect_pi_push μ Ψ _

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t65_corr3_smul_left (μ : FinProb (A × B × C)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → A) → ℂ) (G : (ι → B) → ℂ) (H : (ι → C) → ℂ) :
    corr3 μ (fun x => c * F x) G H = c * corr3 μ F G H := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t65_corr3_smul_mid (μ : FinProb (A × B × C)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → A) → ℂ) (G : (ι → B) → ℂ) (H : (ι → C) → ℂ) :
    corr3 μ F (fun y => c * G y) H = c * corr3 μ F G H := by
  unfold corr3 FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t65_norm_corr3_le_one (μ : FinProb (A × B × C)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (F : (κ → A) → ℂ) (G : (κ → B) → ℂ) (H : (κ → C) → ℂ)
    (hF : ∀ x, ‖F x‖ ≤ 1) (hG : ∀ y, ‖G y‖ ≤ 1) (hH : ∀ z, ‖H z‖ ≤ 1) :
    ‖corr3 μ F G H‖ ≤ 1 := by
  unfold corr3
  refine (t65_norm_cexpect_le _ _).trans (FinProb.expect_le_const _ fun t => ?_)
  rw [norm_mul, norm_mul]
  have e1 := hF (fun i => (t i).1)
  have e2 := hG (fun i => (t i).2.1)
  have e3 := hH (fun i => (t i).2.2)
  have e4 := norm_nonneg (F fun i => (t i).1)
  have e5 := norm_nonneg (G fun i => (t i).2.1)
  have e6 := norm_nonneg (H fun i => (t i).2.2)
  calc ‖F fun i => (t i).1‖ * ‖G fun i => (t i).2.1‖ * ‖H fun i => (t i).2.2‖ ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul e1 e2 e5 zero_le_one) e3 e6 (by positivity)
    _ = 1 := by ring

omit [DecidableEq A] [DecidableEq C] in
private theorem t65_le_lawY (μ : FinProb (A × B × C)) (q : A × B × C) :
    μ.prob q ≤ (lawY μ).prob q.2.1 :=
  Finset.single_le_sum (f := μ.prob) (fun c _ => μ.nonneg c) (by simp)

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem t65_corr3_reindex (ν : FinProb (A × B × C)) {κ : Type} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (e : κ ≃ Fin n) (f : (κ → A) → ℂ) (g : (κ → B) → ℂ) (h : (κ → C) → ℂ) :
    corr3 ν (fun x : Fin n → A => f (x ∘ e)) (fun y => g (y ∘ e)) (fun z => h (z ∘ e)) =
      corr3 ν f g h := by
  unfold corr3
  rw [← cexpect_pi_equiv e ν]
  congr 1
  funext y
  simp [Function.comp_def]

private theorem t65_cstab_reindex {α : Type} [Fintype α] [DecidableEq α] (D : FinProb α) (ρ : ℝ)
    {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n) (g : (κ → α) → ℂ) :
    cstab D ρ (fun y : Fin n → α => g (y ∘ e)) = cstab D ρ g := by
  have := cstab_equiv e.symm D ρ g
  rwa [Equiv.symm_symm] at this

omit [DecidableEq A] [DecidableEq C] in
/-- `S_y` on an arbitrary finite index type (reindexing to `Fin`). -/
private theorem t65_sStmtY_gen {ν : FinProb (A × B × C)} {M δ₀ η : ℝ} (H : SStmtY ν M δ₀ η)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ δ₀) {κ : Type} [Fintype κ] [DecidableEq κ]
    (f : (κ → A) → ℂ) (g : (κ → B) → ℂ) (h : (κ → C) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) (hs : (cstab (lawY ν) (1 - δ) g).re ≤ δ) :
    ‖corr3 ν f g h‖ ≤ M * δ ^ η := by
  have := H δ hδ hδ' (Fintype.card κ) (fun x => f (x ∘ Fintype.equivFin κ))
    (fun y => g (y ∘ Fintype.equivFin κ)) (fun z => h (z ∘ Fintype.equivFin κ))
    (fun x => hf _) (fun y => hg _) (fun z => hh _)
    (by rw [t65_cstab_reindex]; exact hs)
  rwa [t65_corr3_reindex] at this

/-- the joint random restriction of a correlation for the mixture `ν = β νc + (1-β) νr`: the live
coordinates are drawn from `νc`, the fixed ones from `νr`. -/
private theorem t65_corr3_mix (ν νc νr : FinProb (A × B × C)) {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)
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

private theorem t65_norm_subsetExpect_le (c : (I : Finset ι) → (↥Iᶜ → β) → ℂ) :
    ‖subsetExpect s hs0 hs1 (fun I => (ν.pi ↥Iᶜ).cexpect (c I))‖ ≤
      mgenCjE s hs0 hs1 ν (fun I t => ‖c I t‖) := by
  unfold subsetExpect mgenCjE
  exact (t65_norm_cexpect_le _ _).trans (FinProb.expect_mono _ fun σ => t65_norm_cexpect_le _ _)

private theorem t65_jE_mono {Φ Ψ : (I : Finset ι) → (↥Iᶜ → β) → ℝ} (h : ∀ I t, Φ I t ≤ Ψ I t) :
    mgenCjE s hs0 hs1 ν Φ ≤ mgenCjE s hs0 hs1 ν Ψ :=
  FinProb.expect_mono _ fun _ => FinProb.expect_mono _ fun t => h _ t

private theorem t65_jE_add (Φ Ψ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => Φ I t + Ψ I t) =
      mgenCjE s hs0 hs1 ν Φ + mgenCjE s hs0 hs1 ν Ψ := by
  unfold mgenCjE
  simp only [FinProb.expect_add]

private theorem t65_jE_mul (c : ℝ) (Φ : (I : Finset ι) → (↥Iᶜ → β) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => c * Φ I t) = c * mgenCjE s hs0 hs1 ν Φ := by
  unfold mgenCjE
  simp only [FinProb.expect_const_mul]

private theorem t65_jE_const (c : ℝ) : mgenCjE (ι := ι) s hs0 hs1 ν (fun _ _ => c) = c := by
  unfold mgenCjE
  simp

private theorem t65_jE_push {γ : Type} [Fintype γ] [DecidableEq γ] (p : β → γ)
    (Ψ : (I : Finset ι) → (↥Iᶜ → γ) → ℝ) :
    mgenCjE s hs0 hs1 ν (fun I t => Ψ I (fun i => p (t i))) =
      mgenCjE s hs0 hs1 (mergePush ν p) Ψ := by
  unfold mgenCjE
  congr 1
  funext σ
  exact (t65_expect_pi_push ν p _).symm

end JE

/-! ### private core: the mixture transfer of `S_y` (paper IV l. 3642-3684, Supp. E §6.4) -/

/-- a law dominating `β νc` splits as `β νc + (1-β) νr`; the residual is at least `ν - β νc`. -/
private theorem t65_residual {α : Type} [Fintype α] (ν νc : FinProb α) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hdom : ∀ p, β * νc.prob p ≤ ν.prob p) :
    ∃ νr : FinProb α, (∀ p, ν.prob p = β * νc.prob p + (1 - β) * νr.prob p) ∧
      ∀ p, ν.prob p - β * νc.prob p ≤ νr.prob p := by
  have h1β : 0 < 1 - β := by linarith
  refine ⟨⟨fun p => (ν.prob p - β * νc.prob p) / (1 - β),
    fun p => div_nonneg (by linarith [hdom p]) h1β.le, ?_⟩, fun p => ?_, fun p => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ν.sum_eq_one, νc.sum_eq_one,
      mul_one, div_self h1β.ne']
  · show _ = _ + (1 - β) * ((ν.prob p - β * νc.prob p) / (1 - β))
    field_simp
    ring
  · show _ ≤ (ν.prob p - β * νc.prob p) / (1 - β)
    rw [le_div_iff₀ h1β]
    have := hdom p
    nlinarith

/-- the mixture transfer: with `ν = β νc + (1-β) νr` and the `y`-marginals of the three laws bounded
below, a bound `M δ'^η` for `νc` under `Stab_{1-δ'}(g; (νc)_y) ≤ δ'` (on any index type) gives
`S_y(ν; M+1, κδ₀², min η 1 / 2)` with `κ = min 1 ((cβ)²)`. The event is
`Stab_{1-δ/(cβ)}(g̃; (νc)_y) ≤ √δ`; its complement has probability `≤ √δ` by `rr_stab_trivial_master`
and Markov (in the affine form `𝟙[S > √δ] ≤ S/√δ`). -/
private theorem t65_transfer {α₀ : ℝ} (hα₀ : 0 < α₀) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
        [DecidableEq C], Fintype.card B ≤ m →
      ∀ ν νc νr : FinProb (A × B × C), (∀ p, ν.prob p = β * νc.prob p + (1 - β) * νr.prob p) →
      (∀ y, α₀ ≤ (lawY ν).prob y) → (∀ y, α₀ ≤ (lawY νc).prob y) →
      (∀ y, α₀ ≤ (lawY νr).prob y) →
      ∀ M δ₀ η : ℝ, 0 ≤ M → 0 < δ₀ → δ₀ ≤ 1 → 0 < η →
      (∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₀ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
        (F : (κ → A) → ℂ) (G : (κ → B) → ℂ) (H : (κ → C) → ℂ), (∀ x, ‖F x‖ ≤ 1) →
        (∀ y, ‖G y‖ ≤ 1) → (∀ z, ‖H z‖ ≤ 1) →
        (cstab (lawY νc) (1 - δ') G).re ≤ δ' → ‖corr3 νc F G H‖ ≤ M * δ' ^ η) →
      SStmtY ν (M + 1) (min 1 ((c * β) ^ 2) * δ₀ ^ 2) (min η 1 / 2) := by
  obtain ⟨c, hc, hrr⟩ := rr_stab_trivial_master hα₀ m
  refine ⟨c, hc, ?_⟩
  intro β hβ0 hβ1 A B C _ _ _ _ _ _ hcard ν νc νr hmix hY hYc hYr M δ₀ η hM hδ0 hδ1 hη hQ δ hδ
    hδle n f g h hf hg hh hs
  have hcβ : 0 < c * β := mul_pos hc hβ0
  have hδ₀sq : δ₀ ^ 2 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hδ1' : δ ≤ 1 :=
    hδle.trans ((mul_le_mul (min_le_left _ _) hδ₀sq (by positivity) zero_le_one).trans
      (by norm_num))
  have hδcβ : δ ≤ (c * β) ^ 2 :=
    hδle.trans ((mul_le_mul (min_le_right _ _) hδ₀sq (by positivity) (by positivity)).trans
      (by rw [mul_one]))
  have hδδ₀ : δ ≤ δ₀ ^ 2 :=
    hδle.trans ((mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (by rw [one_mul]))
  set s := Real.sqrt δ with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ
  have hss : s * s = δ := Real.mul_self_sqrt hδ.le
  have hsδ₀ : s ≤ δ₀ := (Real.sqrt_le_sqrt hδδ₀).trans_eq (Real.sqrt_sq hδ0.le)
  have hscβ : s ≤ c * β := (Real.sqrt_le_sqrt hδcβ).trans_eq (Real.sqrt_sq hcβ.le)
  have hs1 : s ≤ 1 := Real.sqrt_le_one.2 hδ1'
  set δa := δ / (c * β) with hδadef
  have hδa0 : 0 < δa := div_pos hδ hcβ
  have hδas : δa ≤ s := by
    rw [hδadef, div_le_iff₀ hcβ, ← hss]
    exact mul_le_mul_of_nonneg_left hscβ hs0.le
  have hδa1 : δa ≤ 1 := hδas.trans hs1
  have hcδa : c * β * δa = δ := by
    rw [hδadef]
    field_simp
  have hmixY : ∀ y, (lawY ν).prob y = β * (lawY νc).prob y + (1 - β) * (lawY νr).prob y := by
    intro y
    show ∑ p ∈ univ.filter (fun p : A × B × C => p.2.1 = y), ν.prob p =
      β * ∑ p ∈ univ.filter (fun p : A × B × C => p.2.1 = y), νc.prob p +
        (1 - β) * ∑ p ∈ univ.filter (fun p : A × B × C => p.2.1 = y), νr.prob p
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hmix p
  have hrr' := hrr β hβ0 hβ1.le B hcard (lawY ν) (lawY νc) (lawY νr) hY hYc hYr hmixY δa hδa0
    hδa1 (Fin n) g
  rw [hcδa] at hrr'
  set S : (I : Finset (Fin n)) → (↥Iᶜ → B) → ℝ :=
    fun I z => (cstab (lawY νc) (1 - δa) (restrictFree I z g)).re with hSdef
  have hjS : mgenCjE β hβ0.le hβ1.le (lawY νr) S ≤ δ := by
    have e : (mixtureRestrictionExpect β hβ0.le hβ1.le (lawY νr) g fun _ g' =>
        cstab (lawY νc) (1 - δa) g') = mixtureRestrictionExpect β hβ0.le hβ1.le (lawY νr) g
        (fun I gt => (((cstab (lawY νc) (1 - δa) gt).re : ℝ) : ℂ)) := by
      congr 1
      funext I gt
      exact cstab_eq_ofReal_re _ _ _
    have h1 := (Complex.le_def.1 hrr').1
    rw [e, mgenC_jE_mix] at h1
    exact h1.trans hs
  have hpt : ∀ (I : Finset (Fin n)) (t : ↥Iᶜ → A × B × C),
      ‖corr3 νc (restrictFree I (fun i => (t i).1) f) (restrictFree I (fun i => (t i).2.1) g)
          (restrictFree I (fun i => (t i).2.2) h)‖ ≤
        M * s ^ η + 1 / s * S I (fun i => (t i).2.1) := by
    intro I t
    have hσ0 : 0 ≤ S I (fun i => (t i).2.1) :=
      (Complex.le_def.1 (cstab_nonneg _ (by linarith) _)).1
    have hb1 := mgenC_restrict_bounded I (fun i => (t i).1) f hf
    have hb2 := mgenC_restrict_bounded I (fun i => (t i).2.1) g hg
    have hb3 := mgenC_restrict_bounded I (fun i => (t i).2.2) h hh
    by_cases hσ : S I (fun i => (t i).2.1) ≤ s
    · have hmono : (cstab (lawY νc) (1 - s) (restrictFree I (fun i => (t i).2.1) g)).re ≤
          S I (fun i => (t i).2.1) :=
        (Complex.le_def.1 (cstab_mono _ (by linarith) (by linarith) _)).1
      have hb := hQ s hs0 hsδ₀ (↥I) _ _ _ hb1 hb2 hb3 (hmono.trans hσ)
      have : 0 ≤ 1 / s * S I (fun i => (t i).2.1) := by positivity
      linarith
    · have hσ' : s < S I (fun i => (t i).2.1) := lt_of_not_ge hσ
      have h1 := t65_norm_corr3_le_one νc _ _ _ hb1 hb2 hb3
      have h2 : 1 < 1 / s * S I (fun i => (t i).2.1) := by
        rw [one_div, inv_mul_eq_div, one_lt_div hs0]
        exact hσ'
      have h3 : 0 ≤ M * s ^ η := by positivity
      linarith
  have hmain : ‖corr3 ν f g h‖ ≤ M * s ^ η + 1 / s * mgenCjE β hβ0.le hβ1.le (lawY νr) S := by
    rw [t65_corr3_mix ν νc νr hβ0.le hβ1.le hmix f g h]
    refine (t65_norm_subsetExpect_le hβ0.le hβ1.le νr _).trans
      ((t65_jE_mono hβ0.le hβ1.le νr hpt).trans (le_of_eq ?_))
    rw [t65_jE_add hβ0.le hβ1.le νr (fun _ _ => M * s ^ η)
      (fun I t => 1 / s * S I (fun i => (t i).2.1)), t65_jE_const hβ0.le hβ1.le νr,
      t65_jE_mul hβ0.le hβ1.le νr (1 / s) (fun I t => S I (fun i => (t i).2.1)),
      t65_jE_push hβ0.le hβ1.le νr (fun q : A × B × C => q.2.1) S]
    rfl
  have hfin : M * s ^ η + 1 / s * mgenCjE β hβ0.le hβ1.le (lawY νr) S ≤ M * s ^ η + s := by
    have h1 : 1 / s * mgenCjE β hβ0.le hβ1.le (lawY νr) S ≤ 1 / s * δ :=
      mul_le_mul_of_nonneg_left hjS (by positivity)
    have e : 1 / s * δ = s := by
      rw [← hss]
      field_simp
    linarith
  have hexp1 : s ^ η ≤ δ ^ (min η 1 / 2) := by
    rw [hsdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by have := min_le_left η 1; linarith)
  have hexp2 : s ≤ δ ^ (min η 1 / 2) := by
    rw [hsdef, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by have := min_le_right η 1; linarith)
  calc ‖corr3 ν f g h‖ ≤ M * s ^ η + s := hmain.trans hfin
    _ ≤ M * δ ^ (min η 1 / 2) + δ ^ (min η 1 / 2) := by
        have := mul_le_mul_of_nonneg_left hexp1 hM
        linarith
    _ = (M + 1) * δ ^ (min η 1 / 2) := by ring

/-! ### the uniform law on a set (the richer law `𝒟` of the ugly case) -/

open scoped Classical in
/-- the uniform law on a nonempty set. -/
private def t65_unif {α : Type} [Fintype α] (S : Set α) (hS : S.Nonempty) : FinProb α where
  prob p := if p ∈ S then 1 / ((univ.filter (fun q => q ∈ S)).card : ℝ) else 0
  nonneg p := by
    split_ifs
    · positivity
    · exact le_rfl
  sum_eq_one := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨p, hp⟩ := hS
    have hpos : 0 < (univ.filter (fun q => q ∈ S)).card :=
      Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩
    have : ((univ.filter (fun q => q ∈ S)).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

open scoped Classical in
private theorem t65_unif_support {α : Type} [Fintype α] (S : Set α) (hS : S.Nonempty) :
    (t65_unif S hS).support = S := by
  ext p
  show (if p ∈ S then 1 / ((univ.filter (fun q => q ∈ S)).card : ℝ) else 0) ≠ 0 ↔ p ∈ S
  by_cases hp : p ∈ S
  · have hpos : 0 < (univ.filter (fun q => q ∈ S)).card :=
      Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩
    simp only [hp, ↓reduceIte, iff_true]
    exact one_div_ne_zero (by exact_mod_cast hpos.ne')
  · simp [hp]

open scoped Classical in
private theorem t65_unif_atom {α : Type} [Fintype α] (S : Set α) (hS : S.Nonempty) {p : α}
    (hp : p ∈ S) : 1 / (Fintype.card α : ℝ) ≤ (t65_unif S hS).prob p := by
  show _ ≤ if p ∈ S then 1 / ((univ.filter (fun q => q ∈ S)).card : ℝ) else 0
  simp only [hp, ↓reduceIte]
  have hpos : 0 < (univ.filter (fun q => q ∈ S)).card :=
    Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩
  exact one_div_le_one_div_of_le (by exact_mod_cast hpos) (by exact_mod_cast Finset.card_le_univ _)

/-! ### Lemma 3.9 twice: from `μ'' = m65Mu2 μ` back to `μ` (shared with `MaxTSec6Relaxed65`) -/

section PathReduction
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- Lemma 3.9 in the `x`-slot on `Fin n` (`from_mu_to_path_tensor`), `g` unchanged. -/
private theorem t65_pathX_step (μ : FinProb (X × Y × Z)) {t ℓ : ℕ} (hℓ : Odd ℓ)
    (hℓt : ℓ = 2 ^ t - 1) {n : ℕ} (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ∃ (F : (Fin n → PathX μ ℓ hℓ) → ℂ) (H : (Fin n → Z) → ℂ), (∀ x, ‖F x‖ ≤ 1) ∧
      (∀ z, ‖H z‖ ≤ 1) ∧ ‖corr3 μ f g h‖ ^ (2 ^ t) ≤ ‖corr3 (pathTrick μ ℓ hℓ) F g H‖ :=
  ⟨fun v => altProd f (fun k i => (v i).1 k), condZPi μ (Fin n) f g,
    fun _ => norm_altProd_le_one f hf _, norm_condZPi_le_one μ (Fin n) f g hf hg,
    from_mu_to_path_tensor μ hℓ hℓt (Fin n) f g h hf hg hh⟩

private theorem t65_corr3_swapXZ (μ : FinProb (X × Y × Z)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → X) → ℂ) (g : (ι → Y) → ℂ) (h : (ι → Z) → ℂ) :
    corr3 (lawSwapXZ μ) h g f = corr3 μ f g h := by
  unfold lawSwapXZ
  rw [t65_corr3_push]
  unfold corr3
  congr 1
  funext t
  ring

/-- Lemma 3.9 in the `z`-slot (the `x`-slot of `lawSwapXZ μ`, swapped back), `g` unchanged. -/
private theorem t65_pathZ_step (μ : FinProb (X × Y × Z)) {t ℓ : ℕ} (hℓ : Odd ℓ)
    (hℓt : ℓ = 2 ^ t - 1) {n : ℕ} (f : (Fin n → X) → ℂ) (g : (Fin n → Y) → ℂ)
    (h : (Fin n → Z) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1) :
    ∃ (F : (Fin n → X) → ℂ) (H : (Fin n → PathX (lawSwapXZ μ) ℓ hℓ) → ℂ), (∀ x, ‖F x‖ ≤ 1) ∧
      (∀ z, ‖H z‖ ≤ 1) ∧ ‖corr3 μ f g h‖ ^ (2 ^ t) ≤ ‖corr3 (pathTrickZ μ ℓ hℓ) F g H‖ := by
  obtain ⟨F', H', hF', hH', key⟩ := t65_pathX_step (lawSwapXZ μ) hℓ hℓt h g f hh hg hf
  refine ⟨H', F', hH', hF', ?_⟩
  have e : corr3 (pathTrickZ μ ℓ hℓ) H' g F' = corr3 (pathTrick (lawSwapXZ μ) ℓ hℓ) F' g H' := by
    unfold pathTrickZ
    rw [t65_corr3_push]
    unfold corr3
    congr 1
    funext t
    ring
  rw [← t65_corr3_swapXZ μ f g h, e]
  exact key

private theorem t65_lawY_pathTrick (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) :
    lawY (pathTrick μ ℓ hℓ) = lawY μ :=
  t65_fp_ext fun y => pathTrick_marginalY μ hℓ y

private theorem t65_lawY_pathTrickZ (μ : FinProb (X × Y × Z)) {ℓ : ℕ} (hℓ : Odd ℓ) :
    lawY (pathTrickZ μ ℓ hℓ) = lawY μ := by
  have h1 : lawY (pathTrickZ μ ℓ hℓ) = lawY (pathTrick (lawSwapXZ μ) ℓ hℓ) := by
    unfold lawY pathTrickZ
    rw [t65_push_comp]
  rw [h1, t65_lawY_pathTrick]
  unfold lawY lawSwapXZ
  rw [t65_push_comp]

/-- `x ^ L ≤ M δ^η` gives `x ≤ M δ^{η/L}` for `M ≥ 1`. -/
private theorem t65_root {x M δ η : ℝ} {L : ℕ} (hL : 0 < L) (hx : 0 ≤ x) (hM : 1 ≤ M)
    (hδ : 0 < δ) (h : x ^ L ≤ M * δ ^ η) : x ≤ M * δ ^ (η / (L : ℝ)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (x ^ L) ^ ((L : ℝ)⁻¹) ≤ (M * δ ^ η) ^ ((L : ℝ)⁻¹) :=
    Real.rpow_le_rpow (pow_nonneg hx _) h (inv_nonneg.2 hL'.le)
  rw [Real.pow_rpow_inv_natCast hx hL.ne', Real.mul_rpow (by linarith) (Real.rpow_nonneg hδ.le _),
    ← Real.rpow_mul hδ.le] at h2
  have h4 : M ^ ((L : ℝ)⁻¹) ≤ M := by
    calc M ^ ((L : ℝ)⁻¹) ≤ M ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM (inv_le_one_of_one_le₀ hL1)
      _ = M := Real.rpow_one M
  calc x ≤ M ^ ((L : ℝ)⁻¹) * δ ^ (η * (L : ℝ)⁻¹) := h2
    _ ≤ M * δ ^ (η * (L : ℝ)⁻¹) := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hδ.le _)
    _ = M * δ ^ (η / (L : ℝ)) := by rw [div_eq_mul_inv]

/-- Lemma 3.9 twice (Supp. E §6.4 "Reduction", unchanged): `S_y` for `μ'' = m65Mu2 μ h₁ h₂` (the
`z`-path trick of length `ℓ₁ = 2^{t₁} - 1` followed by the `x`-path trick of length `ℓ₂ = 2^{t₂} - 1`)
gives `S_y` for `μ` with the exponent divided by `2^{t₁} 2^{t₂}`; the `y`-marginal is unchanged. -/
theorem m65T_sStmtY_of_mu2 (μ : FinProb (X × Y × Z)) {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁)
    (h₂ : Odd ℓ₂) (ht₁ : ℓ₁ = 2 ^ t₁ - 1) (ht₂ : ℓ₂ = 2 ^ t₂ - 1) {M δ₀ η : ℝ} (hM : 1 ≤ M)
    (H : SStmtY (m65Mu2 μ h₁ h₂) M δ₀ η) :
    SStmtY μ M δ₀ (η / ((2 ^ t₁ * 2 ^ t₂ : ℕ) : ℝ)) := by
  have hlaw : lawY (m65Mu2 μ h₁ h₂) = lawY μ := by
    show lawY (pathTrick (pathTrickZ μ ℓ₁ h₁) ℓ₂ h₂) = lawY μ
    rw [t65_lawY_pathTrick, t65_lawY_pathTrickZ]
  intro δ hδ hδle n f g h hf hg hh hs
  obtain ⟨F₁, H₁, hF₁, hH₁, k1⟩ := t65_pathZ_step μ h₁ ht₁ f g h hf hg hh
  obtain ⟨F₂, H₂, hF₂, hH₂, k2⟩ := t65_pathX_step (pathTrickZ μ ℓ₁ h₁) h₂ ht₂ F₁ g H₁ hF₁ hg hH₁
  have k3 := H δ hδ hδle n F₂ g H₂ hF₂ hg hH₂ (by rw [hlaw]; exact hs)
  have hL : ‖corr3 μ f g h‖ ^ (2 ^ t₁ * 2 ^ t₂) ≤ M * δ ^ η := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) k1 _).trans (k2.trans k3)
  exact t65_root (by positivity) (norm_nonneg _) hM hδ hL

/-- the atoms of `μ'' = m65Mu2 μ h₁ h₂` are `≥ (α^{ℓ₁+1})^{ℓ₂+1}` (two path tricks,
`k6pt_pathTrick_atom_ge`). -/
theorem m65T_mu2_atom_ge (μ : FinProb (X × Y × Z)) {α : ℝ} (hα : 0 < α)
    (hat : ∀ p ∈ μ.support, α ≤ μ.prob p) {ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂) :
    ∀ q ∈ (m65Mu2 μ h₁ h₂).support, (α ^ (ℓ₁ + 1)) ^ (ℓ₂ + 1) ≤ (m65Mu2 μ h₁ h₂).prob q := by
  have h1 : ∀ q ∈ (pathTrickZ μ ℓ₁ h₁).support, α ^ (ℓ₁ + 1) ≤ (pathTrickZ μ ℓ₁ h₁).prob q := by
    unfold pathTrickZ
    exact mgenC_atom_push _ _ (k6pt_pathTrick_atom_ge (lawSwapXZ μ) hα
      (by unfold lawSwapXZ; exact mgenC_atom_push μ _ hat) ℓ₁ h₁)
  exact k6pt_pathTrick_atom_ge _ (pow_pos hα _) h1 ℓ₂ h₂

end PathReduction

section Terms
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- paper IV `thm:nonembed-deg-must-be-small-rephrase-maximal2`, step `same-support-transfer` (T-reading). -/
theorem m65_sameSupport_transfer (m : ℕ) {α' : ℝ} (hα' : 0 < α') :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ M δ₀ η : ℝ, 1 ≤ M → 0 < δ₀ → δ₀ ≤ 1 → 0 < η →
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card Y ≤ m →
        ∀ ν₀ ν : FinProb (X × Y × Z), ν₀.support = ν.support → InT ν.support →
        (∀ p ∈ ν.support, α' ≤ ν.prob p) → (∀ p ∈ ν₀.support, α' ≤ ν₀.prob p) →
        SStmtY ν₀ M δ₀ η → SStmtY ν (M + 1) (κ * δ₀ ^ 2) (min η 1 / 2) := by
  obtain ⟨c, hc, H⟩ := t65_transfer (α₀ := α' / 2) (by positivity) m
  refine ⟨min 1 ((c * (α' / 2)) ^ 2), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro M δ₀ η hM hδ0 hδ1 hη X Y Z _ _ _ _ _ _ hY ν₀ ν hsupp hT hν hν₀ hS
  have hα1 : α' ≤ 1 := t65_atom_le_one ν hν
  have hβ0 : 0 < α' / 2 := by positivity
  have hβ1 : α' / 2 < 1 := by linarith
  have hdom : ∀ p, α' / 2 * ν₀.prob p ≤ ν.prob p := by
    intro p
    by_cases hp : ν.prob p = 0
    · have h0 : ν₀.prob p = 0 := by
        by_contra h0
        have h0' : p ∈ ν₀.support := h0
        rw [hsupp] at h0'
        exact h0' hp
      rw [h0, hp, mul_zero]
    · have h1 := hν p hp
      have h2 := t65_prob_le_one ν₀ p
      have h3 := ν₀.nonneg p
      nlinarith
  obtain ⟨νr, hmix, hge⟩ := t65_residual ν ν₀ hβ0 hβ1 hdom
  have hT₀ : InT ν₀.support := hsupp ▸ hT
  refine H (α' / 2) hβ0 hβ1 X Y Z hY ν ν₀ νr hmix ?_ ?_ ?_ M δ₀ η (by linarith) hδ0 hδ1 hη ?_
  · intro y
    have := mgenC_atoms_lawY hT hν y
    linarith
  · intro y
    have := mgenC_atoms_lawY hT₀ hν₀ y
    linarith
  · intro y
    obtain ⟨x, z, hq⟩ := MaxT.PairwiseConnected3.exists_atom_y hT.1 y
    have h1 := hν _ hq
    have h2 := hge (x, y, z)
    have h3 := t65_prob_le_one ν₀ (x, y, z)
    have h4 := t65_le_lawY νr (x, y, z)
    have h5 := ν₀.nonneg (x, y, z)
    nlinarith
  · intro δ' hδ'0 hδ'le κ _ _ F G H' hF hG hH hst
    exact t65_sStmtY_gen hS hδ'0 hδ'le F G H' hF hG hH hst

/-! ### III', VII' (analytic terms (e), with (d) built in) -/

/-- Supplement E `lem:III-prime` (d)+(e): the bound on term (III). `ν₃` is `ν'_III`, `μ2` is `μ''` (the law
pushed forward along `a`), `f` plays `f''` (2-bounded), and `ρ^{ξ/8} ≤ δ'` is the threshold. -/
theorem m65_termIII_bound {X₂ X₃ Y' Z₃ : Type} [Fintype X₂] [Fintype X₃] [Fintype Y'] [Fintype Z₃]
    [DecidableEq X₂] [DecidableEq X₃] [DecidableEq Y'] [DecidableEq Z₃]
    (a : X₃ → X₂) (ν₃ : FinProb (X₃ × Y' × Z₃)) (μ2 : FinProb (X₂ × Y' × Z₃))
    (hpush : mergePush ν₃ (fun p => (a p.1, p.2.1, p.2.2)) = μ2)
    {M δ' η : ℝ} (hM : 1 ≤ M) (hδ' : 0 < δ') (hη : 0 < η) (hS : SStmtX ν₃ M δ' η)
    {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hξ : 0 < ξ) (hρδ : ρ ^ (ξ / 8) ≤ δ')
    (n : ℕ) (f : (Fin n → X₂) → ℂ) (g : (Fin n → Y') → ℂ) (h : (Fin n → Z₃) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 2) (hg : ∀ y, ‖g y‖ ≤ 1) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hE : (cstab (lawX μ2) (1 - ρ ^ (ξ / 4)) f).re ≤ ρ ^ (ξ / 8)) :
    ‖corr3 μ2 f g h‖ ≤ 2 * M * ρ ^ (η * ξ / 8) := by
  have _ := hM
  have _ := hδ'
  have _ := hη
  subst hpush
  have hρ8 : 0 < ρ ^ (ξ / 8) := Real.rpow_pos_of_pos hρ0 _
  have hρ8le : ρ ^ (ξ / 8) ≤ 1 := Real.rpow_le_one hρ0.le hρ1.le (by positivity)
  have hρ48 : ρ ^ (ξ / 4) ≤ ρ ^ (ξ / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le (by linarith)
  have hlaw : lawX (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)) = mergePush (lawX ν₃) a := by
    unfold lawX
    rw [t65_push_comp, t65_push_comp]
  have hf' : ∀ x : Fin n → X₃, ‖(1 / 2 : ℂ) * f (fun i => a (x i))‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    have h1 := hf (fun i => a (x i))
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    linarith
  have hst : (cstab (lawX ν₃) (1 - ρ ^ (ξ / 8))
      (fun x => (1 / 2 : ℂ) * f (fun i => a (x i)))).re ≤ ρ ^ (ξ / 8) := by
    have e1 := cstab_smul (lawX ν₃) (1 - ρ ^ (ξ / 8)) (1 / 2 : ℂ) (fun x => f (fun i => a (x i)))
    rw [e1, cstab_pushforward, ← hlaw]
    have hm := (Complex.le_def.1 (cstab_mono (lawX (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)))
      (by linarith : (0 : ℝ) ≤ 1 - ρ ^ (ξ / 8)) (by linarith : 1 - ρ ^ (ξ / 8) ≤ 1 - ρ ^ (ξ / 4))
      f)).1
    have hn := (Complex.le_def.1 (cstab_nonneg (lawX (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)))
      (by linarith : (0 : ℝ) ≤ 1 - ρ ^ (ξ / 8)) f)).1
    have hq : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by norm_num [Complex.normSq_apply]
    rw [hq, Complex.re_ofReal_mul]
    simp only [Complex.zero_re] at hn
    linarith
  have key := hS (ρ ^ (ξ / 8)) hρ8 hρδ n (fun x => (1 / 2 : ℂ) * f (fun i => a (x i))) g h hf' hg
    hh hst
  have hcorr : corr3 (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)) f g h =
      2 * corr3 ν₃ (fun x => (1 / 2 : ℂ) * f (fun i => a (x i))) g h := by
    rw [t65_corr3_smul_left, t65_corr3_push]
    unfold corr3
    ring
  have hpow : (ρ ^ (ξ / 8)) ^ η = ρ ^ (η * ξ / 8) := by
    rw [← Real.rpow_mul hρ0.le]
    ring_nf
  calc ‖corr3 (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)) f g h‖
      = 2 * ‖corr3 ν₃ (fun x => (1 / 2 : ℂ) * f (fun i => a (x i))) g h‖ := by
        rw [hcorr, norm_mul]
        norm_num
    _ ≤ 2 * (M * (ρ ^ (ξ / 8)) ^ η) := by linarith
    _ = 2 * M * ρ ^ (η * ξ / 8) := by rw [hpow]; ring

/-- Supplement E `lem:VII-prime` (d)+(e): the bound on term (VII), unstable function on `g''`. -/
theorem m65_termVII_bound {X₂ X₃ Y' Z₃ : Type} [Fintype X₂] [Fintype X₃] [Fintype Y'] [Fintype Z₃]
    [DecidableEq X₂] [DecidableEq X₃] [DecidableEq Y'] [DecidableEq Z₃]
    (a : X₃ → X₂) (ν₃ : FinProb (X₃ × Y' × Z₃)) (μ2 : FinProb (X₂ × Y' × Z₃))
    (hpush : mergePush ν₃ (fun p => (a p.1, p.2.1, p.2.2)) = μ2)
    {M δ' η : ℝ} (hM : 1 ≤ M) (hδ' : 0 < δ') (hη : 0 < η) (hS : SStmtY ν₃ M δ' η)
    {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hξ : 0 < ξ) (hρδ : ρ ^ (ξ / 8) ≤ δ')
    (n : ℕ) (f : (Fin n → X₂) → ℂ) (g : (Fin n → Y') → ℂ) (h : (Fin n → Z₃) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 2) (hg : ∀ y, ‖g y‖ ≤ 2) (hh : ∀ z, ‖h z‖ ≤ 1)
    (hE : (cstab (lawY μ2) (1 - ρ ^ (ξ / 4)) g).re ≤ ρ ^ (ξ / 8)) :
    ‖corr3 μ2 f g h‖ ≤ 4 * M * ρ ^ (η * ξ / 8) := by
  have _ := hM
  have _ := hδ'
  have _ := hη
  subst hpush
  have hρ8 : 0 < ρ ^ (ξ / 8) := Real.rpow_pos_of_pos hρ0 _
  have hρ8le : ρ ^ (ξ / 8) ≤ 1 := Real.rpow_le_one hρ0.le hρ1.le (by positivity)
  have hρ48 : ρ ^ (ξ / 4) ≤ ρ ^ (ξ / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le (by linarith)
  have hlaw : lawY (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)) = lawY ν₃ := by
    unfold lawY
    rw [t65_push_comp]
  have hf' : ∀ x : Fin n → X₃, ‖(1 / 2 : ℂ) * f (fun i => a (x i))‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    have h1 := hf (fun i => a (x i))
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    linarith
  have hg' : ∀ y : Fin n → Y', ‖(1 / 2 : ℂ) * g y‖ ≤ 1 := by
    intro y
    rw [norm_mul]
    have h1 := hg y
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    linarith
  have hst : (cstab (lawY ν₃) (1 - ρ ^ (ξ / 8)) (fun y => (1 / 2 : ℂ) * g y)).re ≤
      ρ ^ (ξ / 8) := by
    rw [cstab_smul, ← hlaw]
    have hm := (Complex.le_def.1 (cstab_mono (lawY (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)))
      (by linarith : (0 : ℝ) ≤ 1 - ρ ^ (ξ / 8)) (by linarith : 1 - ρ ^ (ξ / 8) ≤ 1 - ρ ^ (ξ / 4))
      g)).1
    have hn := (Complex.le_def.1 (cstab_nonneg (lawY (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)))
      (by linarith : (0 : ℝ) ≤ 1 - ρ ^ (ξ / 8)) g)).1
    have hq : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by norm_num [Complex.normSq_apply]
    rw [hq, Complex.re_ofReal_mul]
    simp only [Complex.zero_re] at hn
    linarith
  have key := hS (ρ ^ (ξ / 8)) hρ8 hρδ n (fun x => (1 / 2 : ℂ) * f (fun i => a (x i)))
    (fun y => (1 / 2 : ℂ) * g y) h hf' hg' hh hst
  have hcorr : corr3 (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)) f g h =
      4 * corr3 ν₃ (fun x => (1 / 2 : ℂ) * f (fun i => a (x i))) (fun y => (1 / 2 : ℂ) * g y) h := by
    rw [t65_corr3_smul_mid, t65_corr3_smul_left, t65_corr3_push]
    unfold corr3
    ring
  have hpow : (ρ ^ (ξ / 8)) ^ η = ρ ^ (η * ξ / 8) := by
    rw [← Real.rpow_mul hρ0.le]
    ring_nf
  calc ‖corr3 (mergePush ν₃ fun p => (a p.1, p.2.1, p.2.2)) f g h‖
      = 4 * ‖corr3 ν₃ (fun x => (1 / 2 : ℂ) * f (fun i => a (x i)))
          (fun y => (1 / 2 : ℂ) * g y) h‖ := by
        rw [hcorr, norm_mul]
        norm_num
    _ ≤ 4 * (M * (ρ ^ (ξ / 8)) ^ η) := by linarith
    _ = 4 * M * ρ ^ (η * ξ / 8) := by rw [hpow]; ring

/-- Supplement E `lem:ugly-prime` (the ugly modest case, `|Σ_modest| = 1`), constants-map form, conditional on the merge core paper IV `lem:merge` (`hmerge`, the statement of `mgen_sStmtY_of_mergeX`). -/
theorem m65_ugly_case_of_hmerge
    (hmerge : ∀ (m : ℕ) {α : ℝ}, 0 < α → ∀ {M δ₀ η : ℝ}, 1 ≤ M → 0 < δ₀ → δ₀ ≤ 1 → 0 < η →
      ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        ∀ a : X → X, MergeRep (mergeGraphX μ.support) a →
          SStmtY (mergeDistX μ a) M δ₀ η → SStmtY μ M' δ₀' η')
    (m : ℕ) {α : ℝ} (hα : 0 < α) {t₁ t₂ ℓ₁ ℓ₂ : ℕ} (h₁ : Odd ℓ₁) (h₂ : Odd ℓ₂) (ht₁ : ℓ₁ = 2 ^ t₁ - 1)
    (ht₂ : ℓ₂ = 2 ^ t₂ - 1) :
    ∃ αD : ℝ, 0 < αD ∧ ∀ MD δD ηD : ℝ, 1 ≤ MD → 0 < δD → δD ≤ 1 → 0 < ηD →
      ∃ M' δ₀' η' : ℝ, 1 ≤ M' ∧ 0 < δ₀' ∧ δ₀' ≤ 1 ∧ 0 < η' ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), InT μ.support → (∀ p ∈ μ.support, α ≤ μ.prob p) →
        FullyMergedSet μ.support → 1 < Fintype.card X →
        (∀ (x : X) (y : Y), ∃ w : m65Phi μ h₁, (x, y, w) ∈ (pathTrickZ μ ℓ₁ h₁).support) →
        (∀ (y : Y) (w : m65Phi μ h₁), ∃ v : m65Sig μ h₁ h₂,
          (v, y, w) ∈ (m65Mu2 μ h₁ h₂).support) →
        ∀ a : m65Sig μ h₁ h₂ → m65Sig μ h₁ h₂,
          MergeRep (mergeGraphX (m65Mu2 μ h₁ h₂).support) a →
        ∀ (x₁ x₂ : X), x₁ ≠ x₂ → ∀ v₁ v₂ : m65Sig μ h₁ h₂,
          (∀ j, v₁.1 j = x₁) → (∀ j, v₂.1 j = x₂) → a v₁ = a v₂ →
        (∀ D : FinProb (X × Y × Z),
          D.support = diagSupportSet a (mergeDistX (m65Mu2 μ h₁ h₂) a).support
            (fun x v => ∀ j, v.1 j = x) (fun z w => ∀ j, w.1 j = z) →
          (∀ p ∈ D.support, αD ≤ D.prob p) → SStmtY D MD δD ηD) →
        SStmtY μ M' δ₀' η' := by
  set α₂ : ℝ := (α ^ (ℓ₁ + 1)) ^ (ℓ₂ + 1) with hα₂def
  set αD : ℝ := 1 / ((m : ℝ) + 1) ^ 3 with hαDdef
  have hα₂ : 0 < α₂ := by rw [hα₂def]; positivity
  have hαD : 0 < αD := by rw [hαDdef]; positivity
  obtain ⟨c, hc, Htr⟩ := t65_transfer (lt_min (half_pos hα₂) hαD : 0 < min (α₂ / 2) αD) m
  refine ⟨αD, hαD, fun MD δD ηD hMD hδD0 hδD1 hηD => ?_⟩
  set β : ℝ := α₂ / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hδν0 : 0 < min 1 ((c * β) ^ 2) * δD ^ 2 :=
    mul_pos (lt_min one_pos (by positivity)) (by positivity)
  have hδν1 : min 1 ((c * β) ^ 2) * δD ^ 2 ≤ 1 :=
    (mul_le_mul (min_le_left _ _) (pow_le_one₀ hδD0.le hδD1) (by positivity) zero_le_one).trans
      (by norm_num)
  obtain ⟨M₁, δ₁, η₁, hM₁, hδ₁0, hδ₁1, hη₁, Hm⟩ := hmerge (m ^ ℓ₁ + m ^ ℓ₂ + m) hα₂
    (show (1 : ℝ) ≤ MD + 1 by linarith) hδν0 hδν1 (show (0 : ℝ) < min ηD 1 / 2 by positivity)
  refine ⟨M₁, δ₁, η₁ / ((2 ^ t₁ * 2 ^ t₂ : ℕ) : ℝ), hM₁, hδ₁0, hδ₁1, by positivity, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hT hat _ _ hc₁ hc₂ a ha _ _ _ _ _ _ _ _ hD
  refine m65T_sStmtY_of_mu2 μ h₁ h₂ ht₁ ht₂ hM₁ ?_
  obtain ⟨-, hS2, hS3, -, -, h31, -⟩ := inT_construction μ hT h₁ h₂ hc₁ hc₂ a ha
  have hat2 : ∀ q ∈ (m65Mu2 μ h₁ h₂).support, α₂ ≤ (m65Mu2 μ h₁ h₂).prob q :=
    m65T_mu2_atom_ge μ hα hat h₁ h₂
  have hat3 : ∀ q ∈ (mergeDistX (m65Mu2 μ h₁ h₂) a).support,
      α₂ ≤ (mergeDistX (m65Mu2 μ h₁ h₂) a).prob q :=
    mergeDistX_atom_bound _ a hat2
  have hα₂1 : α₂ ≤ 1 := t65_atom_le_one _ hat2
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hcS : Fintype.card (m65Sig μ h₁ h₂) ≤ m ^ ℓ₁ + m ^ ℓ₂ + m :=
    (card_pathX_le (pathTrickZ μ ℓ₁ h₁) h₂).trans ((Nat.pow_le_pow_left hX ℓ₂).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)))
  have hcP : Fintype.card (m65Phi μ h₁) ≤ m ^ ℓ₁ + m ^ ℓ₂ + m :=
    (card_pathX_le (lawSwapXZ μ) h₁).trans ((Nat.pow_le_pow_left hZ ℓ₁).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hcY : Fintype.card Y ≤ m ^ ℓ₁ + m ^ ℓ₂ + m := hY.trans (Nat.le_add_left _ _)
  refine Hm (m65Sig μ h₁ h₂) Y (m65Phi μ h₁) hcS hcY hcP (m65Mu2 μ h₁ h₂) hS2 hat2 a ha ?_
  -- the diagonal words
  have hdx : ∀ x : X, ∃ v : m65Sig μ h₁ h₂, ∀ j, v.1 j = x := by
    intro x
    obtain ⟨y, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_x hT.1 x
    obtain ⟨w, v, -, hv, -⟩ := h31 _ hp
    exact ⟨v, hv⟩
  have hdz : ∀ z : Z, ∃ w : m65Phi μ h₁, ∀ j, w.1 j = z := by
    intro z
    obtain ⟨x, y, hp⟩ := MaxT.PairwiseConnected3.exists_atom_z hT.1 z
    obtain ⟨w, v, hw, -⟩ := h31 _ hp
    exact ⟨w, hw⟩
  choose dx hdx using hdx
  choose dz hdz using hdz
  have hdxu : ∀ x (v : m65Sig μ h₁ h₂), (∀ j, v.1 j = x) → v = dx x := fun x v hv =>
    Subtype.ext (funext fun j => (hv j).trans (hdx x j).symm)
  have hdzu : ∀ z (w : m65Phi μ h₁), (∀ j, w.1 j = z) → w = dz z := fun z w hw =>
    Subtype.ext (funext fun j => (hw j).trans (hdz z j).symm)
  -- the richer law `𝒟`: uniform on `diagSupportSet`
  set SD := diagSupportSet a (mergeDistX (m65Mu2 μ h₁ h₂) a).support
    (fun x (v : m65Sig μ h₁ h₂) => ∀ j, v.1 j = x) (fun z (w : m65Phi μ h₁) => ∀ j, w.1 j = z)
    with hSDdef
  have hmemSD : ∀ p : X × Y × Z, p ∈ SD →
      ((⟨a (dx p.1), Set.mem_range_self _⟩ : ↥(Set.range a)), p.2.1, dz p.2.2) ∈
        (mergeDistX (m65Mu2 μ h₁ h₂) a).support := by
    rintro p ⟨v, w, hv, hw, hm⟩
    obtain rfl := hdxu _ v hv
    obtain rfl := hdzu _ w hw
    exact hm
  have hμSD : ∀ p ∈ μ.support, p ∈ SD := by
    intro p hp
    obtain ⟨w, v, hw, hv, -, -, hm⟩ := h31 p hp
    exact ⟨v, w, hv, hw, hm⟩
  obtain ⟨p₀, hp₀⟩ := t65_exists_mem_support μ
  have hSDne : SD.Nonempty := ⟨p₀, hμSD p₀ hp₀⟩
  have hDsupp : (t65_unif SD hSDne).support = SD := t65_unif_support SD hSDne
  have hcard3 : (Fintype.card (X × Y × Z) : ℝ) ≤ ((m : ℝ) + 1) ^ 3 := by
    have hX' : (Fintype.card X : ℝ) ≤ m + 1 := by
      have : (Fintype.card X : ℝ) ≤ m := by exact_mod_cast hX
      linarith
    have hY' : (Fintype.card Y : ℝ) ≤ m + 1 := by
      have : (Fintype.card Y : ℝ) ≤ m := by exact_mod_cast hY
      linarith
    have hZ' : (Fintype.card Z : ℝ) ≤ m + 1 := by
      have : (Fintype.card Z : ℝ) ≤ m := by exact_mod_cast hZ
      linarith
    rw [Fintype.card_prod, Fintype.card_prod]
    push_cast
    calc (Fintype.card X : ℝ) * ((Fintype.card Y : ℝ) * Fintype.card Z)
        ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 1)) :=
          mul_le_mul hX' (mul_le_mul hY' hZ' (by positivity) (by positivity)) (by positivity)
            (by positivity)
      _ = ((m : ℝ) + 1) ^ 3 := by ring
  have hcardpos : (0 : ℝ) < Fintype.card (X × Y × Z) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨p₀⟩
  have hDatom : ∀ p ∈ SD, αD ≤ (t65_unif SD hSDne).prob p := fun p hp =>
    (one_div_le_one_div_of_le hcardpos hcard3).trans (t65_unif_atom SD hSDne hp)
  have hSDstmt : SStmtY (t65_unif SD hSDne) MD δD ηD :=
    hD _ hDsupp (fun p hp => hDatom p (hDsupp ▸ hp))
  -- `ν'_c`: the push-forward of `𝒟` along `(x, y, z) ↦ (a(x,…,x), y, (z,…,z))`
  set νc := mergePush (t65_unif SD hSDne) (fun p : X × Y × Z =>
    ((⟨a (dx p.1), Set.mem_range_self _⟩ : ↥(Set.range a)), p.2.1, dz p.2.2)) with hνcdef
  have hνc_supp : ∀ q, νc.prob q ≠ 0 → q ∈ (mergeDistX (m65Mu2 μ h₁ h₂) a).support := by
    intro q hq
    obtain ⟨p, hp, hDp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have hpq := (Finset.mem_filter.1 hp).2
    have hpS : p ∈ SD := by
      rw [← hDsupp]
      exact hDp
    rw [← hpq]
    exact hmemSD p hpS
  have hdom : ∀ q, β * νc.prob q ≤ (mergeDistX (m65Mu2 μ h₁ h₂) a).prob q := by
    intro q
    by_cases hq : νc.prob q = 0
    · rw [hq, mul_zero]
      exact (mergeDistX (m65Mu2 μ h₁ h₂) a).nonneg q
    · have h1 := hat3 q (hνc_supp q hq)
      have h2 := t65_prob_le_one νc q
      have h3 := νc.nonneg q
      rw [hβdef]
      nlinarith
  obtain ⟨νr, hmix, hge⟩ := t65_residual _ νc hβ0 hβ1 hdom
  have hlawc : lawY νc = lawY (t65_unif SD hSDne) := by
    rw [hνcdef]
    unfold lawY
    rw [t65_push_comp]
  refine Htr β hβ0 hβ1 (↥(Set.range a)) Y (m65Phi μ h₁) hY _ νc νr hmix ?_ ?_ ?_ MD δD ηD
    (by linarith) hδD0 hδD1 hηD ?_
  · intro y
    have h1 := mgenC_atoms_lawY hS3 hat3 y
    have h2 : min (α₂ / 2) αD ≤ α₂ / 2 := min_le_left _ _
    linarith
  · intro y
    rw [hlawc]
    obtain ⟨x, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_y hT.1 y
    have h1 := hDatom _ (hμSD _ hp)
    have h2 := t65_le_lawY (t65_unif SD hSDne) (x, y, z)
    have h3 : min (α₂ / 2) αD ≤ αD := min_le_right _ _
    linarith
  · intro y
    obtain ⟨x', z', hq⟩ := MaxT.PairwiseConnected3.exists_atom_y hS3.1 y
    have h1 := hat3 _ hq
    have h2 := hge (x', y, z')
    have h3 := t65_prob_le_one νc (x', y, z')
    have h4 := t65_le_lawY νr (x', y, z')
    have h5 := νc.nonneg (x', y, z')
    have h6 : min (α₂ / 2) αD ≤ α₂ / 2 := min_le_left _ _
    rw [hβdef] at h2
    nlinarith
  · intro δ' hδ'0 hδ'le κ _ _ F G H hF hG hH hst
    have e : corr3 νc F G H = corr3 (t65_unif SD hSDne)
        (fun x => F (fun i => (⟨a (dx (x i)), Set.mem_range_self _⟩ : ↥(Set.range a))))
        G (fun z => H (fun i => dz (z i))) := by
      rw [hνcdef, t65_corr3_push]
      rfl
    have hst' : (cstab (lawY (t65_unif SD hSDne)) (1 - δ') G).re ≤ δ' := by
      rw [← hlawc]
      exact hst
    rw [e]
    exact t65_sStmtY_gen hSDstmt hδ'0 hδ'le _ G _ (fun x => hF _) hG (fun z => hH _) hst'

end Terms
end MaxT
end TrackB
end RestrictedPolynomials
end
