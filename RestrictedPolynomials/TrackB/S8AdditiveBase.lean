module

public import RestrictedPolynomials.TrackB.S7Basis
public import RestrictedPolynomials.TrackB.MaxTStatements
public import RestrictedPolynomials.TrackB.TurnInfiniteFinite
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Track B: the additive base case of paper IV App. C (Claim 8.1)

Covers paper IV `claim:embedding-fns` and `claim:additive-base-case` with its two steps
`#equality-forces-embedding` and `#compactness-limit`.

Formalization choices: the compactness lemma assumes `PairwiseConnected3 S`; there are no
`hunif, γ, φ` hypotheses; the helper `s8_embedSpan_eq_of_master` is used; the constant satisfies
`c ≤ 1`.  `hsat` is kept in `s8_embedding_fns` and `s8_additive_equality_forces_embedding`.
All helpers are `private`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S8Additive
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-! ### push-forward and sum helpers -/

private theorem cexpect_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) (G : β → ℂ) : (mergePush π f).cexpect G = π.cexpect (fun a => G (f a)) := by
  unfold FinProb.cexpect
  show ∑ b, ((∑ a ∈ univ.filter (fun a => f a = b), π.prob a : ℝ) : ℂ) * G b = _
  rw [← Finset.sum_fiberwise univ f (fun a => (π.prob a : ℂ) * G (f a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]

private theorem expect_push {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (π : FinProb α)
    (f : α → β) (G : β → ℝ) : (mergePush π f).expect G = π.expect (fun a => G (f a)) := by
  unfold FinProb.expect
  show ∑ b, (∑ a ∈ univ.filter (fun a => f a = b), π.prob a) * G b = _
  rw [← Finset.sum_fiberwise univ f (fun a => π.prob a * G (f a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]

private theorem lawX_expect (μ : FinProb (X × Y × Z)) (G : X → ℝ) :
    (lawX μ).expect G = μ.expect (fun p => G p.1) := expect_push μ _ G

private theorem lawX_cexpect (μ : FinProb (X × Y × Z)) (G : X → ℂ) :
    (lawX μ).cexpect G = μ.cexpect (fun p => G p.1) := cexpect_push μ _ G

private theorem lawX_cinner (μ : FinProb (X × Y × Z)) (f v : X → ℂ) :
    (lawX μ).cinner f v = μ.cexpect (fun p => f p.1 * star (v p.1)) :=
  lawX_cexpect μ (fun x => f x * star (v x))

private theorem expect_nonneg' {α : Type} [Fintype α] (π : FinProb α) (G : α → ℝ)
    (hG : ∀ a, 0 ≤ G a) : 0 ≤ π.expect G :=
  Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg a) (hG a)

private theorem support_nonempty' {α : Type} [Fintype α] (π : FinProb α) : π.support.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h0 : ∀ a, π.prob a = 0 := fun a => by
    by_contra h
    exact (Set.eq_empty_iff_forall_notMem.1 hne) a h
  have := π.sum_eq_one
  simp [h0] at this

/-! ### master embeddings: fibres -/

private theorem master_fibre {S : Set (X × Y × Z)} (hS : S.Nonempty) {s : ℕ} (Hs : Fin s → Type)
    [∀ i, AddCommGroup (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i)
    (hM : IsMasterEmbedding S Hs σ γ φ) {G : Type} [AddCommGroup G] (σ' : X → G) (γ' : Y → G)
    (φ' : Z → G) (hemb : IsEmbedding3 S σ' γ' φ') {x x' : X} (hx : σ x = σ x') : σ' x = σ' x' := by
  obtain ⟨a, b, c, -, hemb', ⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, ⟨z₀, hz₀⟩, -⟩ :=
    exists_shift_zero_in_image hS hemb
  obtain ⟨i, m₁, m₂, m₃, -, -, -, h1, -, -⟩ := hM.2 G (fun x => σ' x - a) (fun y => γ' y - b)
    (fun z => φ' z - c) hemb' ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, ⟨z₀, hz₀⟩⟩
  have e1 : σ' x - a = m₁ (σ x i) := h1 x
  have e2 : σ' x' - a = m₁ (σ x' i) := h1 x'
  have e : σ' x - a = σ' x' - a := by rw [e1, e2, hx]
  exact sub_left_injective e

/-- real-valued relations: the fibres of a master embedding are respected. -/
private theorem master_real_fibre {S : Set (X × Y × Z)} (hS : S.Nonempty) {s : ℕ}
    (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i)
    (φ : Z → ∀ i, Hs i) (hM : IsMasterEmbedding S Hs σ γ φ) (F : X → ℝ) (G : Y → ℝ) (H : Z → ℝ)
    (hrel : ∀ p ∈ S, F p.1 + G p.2.1 + H p.2.2 = 0) {x x' : X} (hx : σ x = σ x') : F x = F x' := by
  set M : ℝ := ∑ x, |F x| with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set t : ℝ := (1 + 2 * M)⁻¹ with ht
  have hpos : 0 < 1 + 2 * M := by linarith
  have htpos : 0 < t := inv_pos.2 hpos
  have hb : ∀ x, |t * F x| < 1 / 2 := by
    intro x
    have h1 : |F x| ≤ M := Finset.single_le_sum (f := fun x => |F x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)
    rw [abs_mul, abs_of_pos htpos, ht, inv_mul_lt_iff₀ hpos]
    nlinarith
  have _ : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hemb : IsEmbedding3 S (fun x => ((t * F x : ℝ) : AddCircle (1 : ℝ)))
      (fun y => ((t * G y : ℝ) : AddCircle (1 : ℝ))) (fun z => ((t * H z : ℝ) : AddCircle (1 : ℝ))) := by
    rw [isEmbedding3_iff]
    intro p hp
    have h0 := hrel p hp
    have : t * F p.1 + t * G p.2.1 + t * H p.2.2 = 0 := by
      have : t * F p.1 + t * G p.2.1 + t * H p.2.2 = t * (F p.1 + G p.2.1 + H p.2.2) := by ring
      rw [this, h0, mul_zero]
    show ((t * F p.1 : ℝ) : AddCircle (1 : ℝ)) + ((t * G p.2.1 : ℝ) : AddCircle (1 : ℝ)) +
      ((t * H p.2.2 : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [← AddCircle.coe_add (p := (1 : ℝ)), ← AddCircle.coe_add (p := (1 : ℝ)), this]
    exact AddCircle.coe_zero (p := (1 : ℝ))
  obtain ⟨q, σ', γ', φ', hq, hemb', hequiv⟩ := turn_infinite_to_finite_zmod S _ _ _ hemb
  have h1 := master_fibre hS Hs σ γ φ hM σ' γ' φ' hemb' hx
  obtain ⟨⟨m, hm⟩, -, -⟩ := hequiv
  have h2 : m ⟨((t * F x : ℝ) : AddCircle (1 : ℝ)), x, rfl⟩ =
      m ⟨((t * F x' : ℝ) : AddCircle (1 : ℝ)), x', rfl⟩ := by
    apply Subtype.ext
    rw [hm x, hm x', h1]
  have h3 := m.injective h2
  have h4 : ((t * F x : ℝ) : AddCircle (1 : ℝ)) = ((t * F x' : ℝ) : AddCircle (1 : ℝ)) :=
    congrArg Subtype.val h3
  have hI : ∀ x, t * F x ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := fun x => by
    have := abs_lt.1 (hb x)
    constructor <;> linarith [this.1, this.2]
  have h5 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hI x) (hI x')).1 h4
  exact mul_left_cancel₀ htpos.ne' h5

/-- Paper IV `claim:embedding-fns` (Claim 4.3): if the master embeddings are saturated and
`f(x) + g(y) + h(z) = 0` on `supp μ`, then `f ∈ Embed_σ(μ)`. -/
theorem s8_embedding_fns (μ : FinProb (X × Y × Z)) {s : ℕ} (Hs : Fin s → Type)
    [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i)
    (φ : Z → ∀ i, Hs i) (hM : IsMasterEmbedding μ.support Hs σ γ φ) (hsat : IsSaturated3 σ γ φ)
    (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ)
    (hrel : ∀ p ∈ μ.support, f p.1 + g p.2.1 + h p.2.2 = 0) : f ∈ embedSpan σ := by
  have _ := hsat
  have hS := support_nonempty' μ
  rw [embedSpan_iff_fibre_constant]
  intro x x' hx
  apply Complex.ext
  · refine master_real_fibre hS Hs σ γ φ hM (fun x => (f x).re) (fun y => (g y).re)
      (fun z => (h z).re) (fun p hp => ?_) hx
    have := congrArg Complex.re (hrel p hp)
    simpa using this
  · refine master_real_fibre hS Hs σ γ φ hM (fun x => (f x).im) (fun y => (g y).im)
      (fun z => (h z).im) (fun p hp => ?_) hx
    have := congrArg Complex.im (hrel p hp)
    simpa using this

/-- Helper: all master embeddings of the same support have the same fibres, hence the same
`Embed_σ`. -/
theorem s8_embedSpan_eq_of_master (S : Set (X × Y × Z)) (hS : S.Nonempty) {s s' : ℕ}
    (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
    (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i)
    (hM : IsMasterEmbedding S Hs σ γ φ) (Hs' : Fin s' → Type) [∀ i, AddCommGroup (Hs' i)]
    [∀ i, Fintype (Hs' i)] (σ' : X → ∀ i, Hs' i) (γ' : Y → ∀ i, Hs' i) (φ' : Z → ∀ i, Hs' i)
    (hM' : IsMasterEmbedding S Hs' σ' γ' φ') : embedSpan σ = embedSpan σ' := by
  ext f
  rw [embedSpan_iff_fibre_constant, embedSpan_iff_fibre_constant]
  constructor
  · intro h w w' hw
    exact h w w' (master_fibre hS Hs' σ' γ' φ' hM' σ γ φ hM.1 hw)
  · intro h w w' hw
    exact h w w' (master_fibre hS Hs σ γ φ hM σ' γ' φ' hM'.1 hw)

/-! ### equality forces an embedding function -/

private theorem sq_dist_identity (a w z : ℂ) :
    ‖w - a * (starRingEnd ℂ) z‖ ^ 2 =
      ‖w‖ ^ 2 + ‖a‖ ^ 2 * ‖z‖ ^ 2 - 2 * ((starRingEnd ℂ) a * (z * w)).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Paper IV `claim:additive-base-case#equality-forces-embedding` (l. 4562-4569): in the limit
configuration Cauchy-Schwarz is tight, so `f(x) = θ conj(g(y) + h(z))` on `supp μ` for some `|θ| = 1`;
`s8_embedding_fns` (applied to `f, -θ conj g, -θ conj h`) gives `f ∈ Embed_σ(μ)`, and with
`f ∈ Embed_σ(μ)^⊥` this forces `‖f‖₂ = 0`, contradicting `‖f‖₂ = 1`.  Stated as the contradiction
(`False`).  (The typo "`(x,y,z) ∈ ℂ`" of l. 4567 is read `supp(μ)`.) -/
theorem s8_additive_equality_forces_embedding (μ : FinProb (X × Y × Z)) {s : ℕ} (Hs : Fin s → Type)
    [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i)
    (φ : Z → ∀ i, Hs i) (hM : IsMasterEmbedding μ.support Hs σ γ φ) (hsat : IsSaturated3 σ γ φ)
    (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ) (hf : f ∈ s7Perp (lawX μ) (embedSpan σ))
    (hfn : (lawX μ).expect (fun x => ‖f x‖ ^ 2) = 1)
    (hgh : μ.expect (fun p => ‖g p.2.1 + h p.2.2‖ ^ 2) = 1)
    (hE : 1 ≤ ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖) : False := by
  set a : ℂ := μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2)) with ha
  rw [lawX_expect] at hfn
  -- the sum of squared distances
  have hsum : μ.expect (fun p => ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2) =
      1 - ‖a‖ ^ 2 := by
    have hre : μ.expect (fun p => ((starRingEnd ℂ) a * (f p.1 * (g p.2.1 + h p.2.2))).re) =
        ‖a‖ ^ 2 := by
      have h1 : μ.cexpect (fun p => (starRingEnd ℂ) a * (f p.1 * (g p.2.1 + h p.2.2))) =
          (starRingEnd ℂ) a * a := by
        unfold FinProb.cexpect
        rw [ha, FinProb.cexpect, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
      have h2 := congrArg Complex.re h1
      have h3 : ((starRingEnd ℂ) a * a).re = ‖a‖ ^ 2 := by
        simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
          Complex.conj_im]
        ring
      rw [h3] at h2
      rw [← h2]
      unfold FinProb.cexpect
      rw [Complex.re_sum]
      simp only [Complex.re_ofReal_mul]
      rfl
    have hexp : ∀ p, μ.prob p * ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 =
        μ.prob p * ‖g p.2.1 + h p.2.2‖ ^ 2 + ‖a‖ ^ 2 * (μ.prob p * ‖f p.1‖ ^ 2) -
          2 * (μ.prob p * ((starRingEnd ℂ) a * (f p.1 * (g p.2.1 + h p.2.2))).re) := by
      intro p
      rw [sq_dist_identity]
      ring
    show ∑ p, μ.prob p * ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 = _
    simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : ∑ p, μ.prob p * ‖g p.2.1 + h p.2.2‖ ^ 2 = 1 := hgh
    have e2 : ∑ p, μ.prob p * ‖f p.1‖ ^ 2 = 1 := hfn
    have e3 : ∑ p, μ.prob p * ((starRingEnd ℂ) a * (f p.1 * (g p.2.1 + h p.2.2))).re =
        ‖a‖ ^ 2 := hre
    rw [e1, e2, e3]
    ring
  have hnn : ∀ p, 0 ≤ μ.prob p * ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 :=
    fun p => mul_nonneg (μ.nonneg p) (by positivity)
  have hsum' : ∑ p, μ.prob p * ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 =
      1 - ‖a‖ ^ 2 := hsum
  have hle1 : ‖a‖ ≤ 1 := by
    have : 0 ≤ 1 - ‖a‖ ^ 2 := by
      rw [← hsum']
      exact Finset.sum_nonneg fun p _ => hnn p
    nlinarith [norm_nonneg a]
  have ha1 : ‖a‖ = 1 := le_antisymm hle1 hE
  have hzero : ∀ p, μ.prob p * ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 = 0 := by
    have h0 : ∑ p, μ.prob p * ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 = 0 := by
      rw [hsum', ha1]; norm_num
    exact fun p => (Finset.sum_eq_zero_iff_of_nonneg fun p _ => hnn p).1 h0 p (Finset.mem_univ p)
  have hrel : ∀ p ∈ μ.support, f p.1 + (fun y => -(a * (starRingEnd ℂ) (g y))) p.2.1 +
      (fun z => -(a * (starRingEnd ℂ) (h z))) p.2.2 = 0 := by
    intro p hp
    have hp' : μ.prob p ≠ 0 := hp
    have h1 := hzero p
    have h2 : ‖(g p.2.1 + h p.2.2) - a * (starRingEnd ℂ) (f p.1)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hp'
      · exact h
    have h3 : (g p.2.1 + h p.2.2) = a * (starRingEnd ℂ) (f p.1) := by
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h2
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    have h4 : a * (starRingEnd ℂ) (g p.2.1 + h p.2.2) = f p.1 := by
      rw [h3, map_mul, Complex.conj_conj, ← mul_assoc, mul_comm a, mul_assoc, ← mul_assoc]
      have : (starRingEnd ℂ) a * a = 1 := by
        rw [Complex.conj_mul', ha1]
        simp
      rw [this, one_mul]
    simp only [map_add] at h4
    linear_combination -h4
  have hmem := s8_embedding_fns μ Hs σ γ φ hM hsat f (fun y => -(a * (starRingEnd ℂ) (g y)))
    (fun z => -(a * (starRingEnd ℂ) (h z))) hrel
  have h0 := hf f hmem
  rw [lawX_cinner] at h0
  have h5 : μ.cexpect (fun p => f p.1 * star (f p.1)) =
      ((μ.expect (fun p => ‖f p.1‖ ^ 2) : ℝ) : ℂ) := by
    unfold FinProb.cexpect FinProb.expect
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [h5, hfn] at h0
  norm_num at h0

/-! ### compactness -/

private theorem tendsto_cexpect {α : Type} [Fintype α] (π : ℕ → FinProb α) (π' : FinProb α)
    (hπ : ∀ a, Filter.Tendsto (fun k => (π k).prob a) Filter.atTop (nhds (π'.prob a)))
    (F : ℕ → α → ℂ) (F' : α → ℂ)
    (hF : ∀ a, Filter.Tendsto (fun k => F k a) Filter.atTop (nhds (F' a))) :
    Filter.Tendsto (fun k => (π k).cexpect (F k)) Filter.atTop (nhds (π'.cexpect F')) := by
  unfold FinProb.cexpect
  refine tendsto_finsetSum _ fun a _ => ?_
  exact ((Complex.continuous_ofReal.tendsto _).comp (hπ a)).mul (hF a)

private theorem tendsto_expect {α : Type} [Fintype α] (π : ℕ → FinProb α) (π' : FinProb α)
    (hπ : ∀ a, Filter.Tendsto (fun k => (π k).prob a) Filter.atTop (nhds (π'.prob a)))
    (F : ℕ → α → ℝ) (F' : α → ℝ)
    (hF : ∀ a, Filter.Tendsto (fun k => F k a) Filter.atTop (nhds (F' a))) :
    Filter.Tendsto (fun k => (π k).expect (F k)) Filter.atTop (nhds (π'.expect F')) := by
  unfold FinProb.expect
  exact tendsto_finsetSum _ fun a _ => (hπ a).mul (hF a)

private theorem walk_bound {V : Type} {G : SimpleGraph V} (w : V → ℂ) (B : ℝ)
    (hw : ∀ a b, G.Adj a b → ‖w a - w b‖ ≤ B) {u v : V} (W : G.Walk u v) :
    ‖w u - w v‖ ≤ W.length * B := by
  induction W with
  | nil => simp
  | cons hadj p ih =>
    rename_i a b c
    calc ‖w a - w c‖ = ‖(w a - w b) + (w b - w c)‖ := by ring_nf
      _ ≤ ‖w a - w b‖ + ‖w b - w c‖ := norm_add_le _ _
      _ ≤ B + (p.length * B) := add_le_add (hw _ _ hadj) ih
      _ = ((p.length + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- Paper IV `claim:additive-base-case#compactness-limit` (l. 4549-4561), with repairs of a gap in the
source: the alphabets are fixed, the support `S` is constant and pairwise
connected, the pair `(g_k, h_k)` is recentred (`(g_k + c_k, h_k - c_k)` has the same sum and
correlation), and the limit `μ_∞` again has atoms `≥ α` on `S` and support `S`.  The conclusion is
the limit configuration with `|𝔼 f(g+h)| ≥ 1`. -/
theorem s8_additive_base_compactness {H : Type} [AddCommGroup H] (σ : X → H)
    (S : Set (X × Y × Z)) (hconn : PairwiseConnected3 S) {α : ℝ} (hα : 0 < α)
    (μ : ℕ → FinProb (X × Y × Z)) (hS : ∀ k, (μ k).support = S)
    (hat : ∀ k, ∀ p ∈ S, α ≤ (μ k).prob p)
    (f : ℕ → X → ℂ) (g : ℕ → Y → ℂ) (h : ℕ → Z → ℂ)
    (hf : ∀ k, f k ∈ s7Perp (lawX (μ k)) (embedSpan σ))
    (hfn : ∀ k, (lawX (μ k)).expect (fun x => ‖f k x‖ ^ 2) = 1)
    (hgh : ∀ k, (μ k).expect (fun p => ‖g k p.2.1 + h k p.2.2‖ ^ 2) = 1)
    (hE : ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) ≤
      ‖(μ k).cexpect (fun p => f k p.1 * (g k p.2.1 + h k p.2.2))‖) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧ ∃ (μ' : FinProb (X × Y × Z)) (f' : X → ℂ) (g' : Y → ℂ)
      (h' : Z → ℂ) (c : ℕ → ℂ),
      (∀ p, Filter.Tendsto (fun k => (μ (ns k)).prob p) Filter.atTop (nhds (μ'.prob p))) ∧
      (∀ x, Filter.Tendsto (fun k => f (ns k) x) Filter.atTop (nhds (f' x))) ∧
      (∀ y, Filter.Tendsto (fun k => g (ns k) y + c k) Filter.atTop (nhds (g' y))) ∧
      (∀ z, Filter.Tendsto (fun k => h (ns k) z - c k) Filter.atTop (nhds (h' z))) ∧
      μ'.support = S ∧ (∀ p ∈ S, α ≤ μ'.prob p) ∧
      f' ∈ s7Perp (lawX μ') (embedSpan σ) ∧ (lawX μ').expect (fun x => ‖f' x‖ ^ 2) = 1 ∧
      μ'.expect (fun p => ‖g' p.2.1 + h' p.2.2‖ ^ 2) = 1 ∧
      1 ≤ ‖μ'.cexpect (fun p => f' p.1 * (g' p.2.1 + h' p.2.2))‖ := by
  obtain ⟨_, ⟨y₀⟩, _, _⟩ := MaxT.PairwiseConnected3.nonempty_alphabets hconn
  set B : ℝ := 1 + 1 / α with hB
  have hB0 : 0 ≤ B := by positivity
  have hbd : ∀ k (F : X × Y × Z → ℂ), (μ k).expect (fun p => ‖F p‖ ^ 2) = 1 →
      ∀ p ∈ S, ‖F p‖ ≤ B := by
    intro k F hF p hp
    have h1 : (μ k).prob p * ‖F p‖ ^ 2 ≤ 1 := by
      rw [← hF]
      exact Finset.single_le_sum (f := fun q => (μ k).prob q * ‖F q‖ ^ 2)
        (fun q _ => mul_nonneg ((μ k).nonneg q) (sq_nonneg _)) (Finset.mem_univ p)
    have h2 : α * ‖F p‖ ^ 2 ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right (hat k p hp) (sq_nonneg _)) h1
    have h3 : ‖F p‖ ^ 2 ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
    nlinarith [norm_nonneg (F p), sq_nonneg (‖F p‖ - 1)]
  have hfB : ∀ k x, ‖f k x‖ ≤ B := by
    intro k x
    obtain ⟨y, z, hp⟩ := MaxT.PairwiseConnected3.exists_atom_x hconn x
    exact hbd k (fun p => f k p.1) ((lawX_expect (μ k) _).symm.trans (hfn k)) (x, y, z) hp
  have hedge : ∀ k, ∀ p ∈ S, ‖g k p.2.1 + h k p.2.2‖ ≤ B := fun k =>
    hbd k (fun p => g k p.2.1 + h k p.2.2) (hgh k)
  have h23 := ((pairwiseConnected3_iff S).1 hconn).2.2
  set G : SimpleGraph (Y ⊕ Z) := SimpleGraph.fromRel fun (a : Y ⊕ Z) b =>
    ∃ x y z, (x, y, z) ∈ S ∧ a = Sum.inl y ∧ b = Sum.inr z with hG
  have hadj : ∀ (w : Y ⊕ Z → ℂ) (Bd : ℝ),
      (∀ p ∈ S, ‖w (Sum.inl p.2.1) - w (Sum.inr p.2.2)‖ ≤ Bd) →
        ∀ a b, G.Adj a b → ‖w a - w b‖ ≤ Bd := by
    intro w Bd hw a b hab
    rw [hG, SimpleGraph.fromRel_adj] at hab
    obtain ⟨-, ⟨x, y, z, hm, rfl, rfl⟩ | ⟨x, y, z, hm, rfl, rfl⟩⟩ := hab
    · exact hw (x, y, z) hm
    · rw [norm_sub_rev]; exact hw (x, y, z) hm
  have hL : ∀ v : Y ⊕ Z, ∃ n : ℕ, ∀ (w : Y ⊕ Z → ℂ) (Bd : ℝ),
      (∀ a b, G.Adj a b → ‖w a - w b‖ ≤ Bd) → ‖w (Sum.inl y₀) - w v‖ ≤ n * Bd := by
    intro v
    obtain ⟨W⟩ := h23.preconnected (Sum.inl y₀) v
    exact ⟨W.length, fun w Bd hw => walk_bound w Bd hw W⟩
  choose L hL using hL
  have hwk : ∀ k, ∀ v : Y ⊕ Z,
      ‖(Sum.elim (g k) (fun z => -h k z) : Y ⊕ Z → ℂ) (Sum.inl y₀) -
        (Sum.elim (g k) (fun z => -h k z) : Y ⊕ Z → ℂ) v‖ ≤ L v * B := by
    intro k v
    refine hL v _ B (hadj _ B fun p hp => ?_)
    have := hedge k p hp
    simpa [sub_neg_eq_add] using this
  set R : ℝ := 1 + B + ∑ v, (L v : ℝ) * B with hR
  have hLR : ∀ v, (L v : ℝ) * B ≤ R := by
    intro v
    have h1 : (L v : ℝ) * B ≤ ∑ v, (L v : ℝ) * B :=
      Finset.single_le_sum (f := fun v => (L v : ℝ) * B)
        (fun v _ => mul_nonneg (Nat.cast_nonneg _) hB0) (Finset.mem_univ v)
    linarith
  have hR1 : 1 + B ≤ R := by
    have : 0 ≤ ∑ v, (L v : ℝ) * B :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) hB0
    linarith
  have hR0 : 0 ≤ R := le_trans (mul_nonneg (Nat.cast_nonneg _) hB0) (hLR (Sum.inl y₀))
  let x : ℕ → (X × Y × Z → ℝ) × (X → ℂ) × (Y → ℂ) × (Z → ℂ) := fun k =>
    (fun p => (μ k).prob p, f k, fun y => g k y + -g k y₀, fun z => h k z - -g k y₀)
  have hx : ∀ k, x k ∈ Metric.closedBall (0 : (X × Y × Z → ℝ) × (X → ℂ) × (Y → ℂ) × (Z → ℂ)) R := by
    intro k
    rw [mem_closedBall_zero_iff]
    simp only [Prod.norm_def]
    refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun p => ?_
      have h1 : (μ k).prob p ≤ 1 := by
        calc (μ k).prob p ≤ ∑ q, (μ k).prob q :=
              Finset.single_le_sum (f := (μ k).prob) (fun q _ => (μ k).nonneg q) (Finset.mem_univ p)
          _ = 1 := (μ k).sum_eq_one
      show ‖(μ k).prob p‖ ≤ R
      rw [Real.norm_of_nonneg ((μ k).nonneg p)]
      linarith
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun p => ?_
      have := hfB k p
      show ‖f k p‖ ≤ R
      linarith
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun y => ?_
      have := hwk k (Sum.inl y)
      show ‖g k y + -g k y₀‖ ≤ R
      rw [← sub_eq_add_neg, norm_sub_rev]
      simp only [Sum.elim_inl] at this
      linarith [hLR (Sum.inl y)]
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun z => ?_
      have := hwk k (Sum.inr z)
      show ‖h k z - -g k y₀‖ ≤ R
      simp only [Sum.elim_inl, Sum.elim_inr] at this
      have e : h k z - -g k y₀ = g k y₀ - -h k z := by ring
      rw [e]
      linarith [hLR (Sum.inr z)]
  obtain ⟨a, -, ns, hns, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hx
  have hP : ∀ p, Filter.Tendsto (fun k => (μ (ns k)).prob p) Filter.atTop (nhds (a.1 p)) :=
    fun p => tendsto_pi_nhds.1 ((continuous_fst.tendsto a).comp hlim) p
  have hF : ∀ x', Filter.Tendsto (fun k => f (ns k) x') Filter.atTop (nhds (a.2.1 x')) :=
    fun x' => tendsto_pi_nhds.1
      (((continuous_fst.comp continuous_snd).tendsto a).comp hlim) x'
  have hGt : ∀ y, Filter.Tendsto (fun k => g (ns k) y + -g (ns k) y₀) Filter.atTop
      (nhds (a.2.2.1 y)) :=
    fun y => tendsto_pi_nhds.1
      (((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto a).comp hlim) y
  have hHt : ∀ z, Filter.Tendsto (fun k => h (ns k) z - -g (ns k) y₀) Filter.atTop
      (nhds (a.2.2.2 z)) :=
    fun z => tendsto_pi_nhds.1
      (((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto a).comp hlim) z
  have hnn' : ∀ p, 0 ≤ a.1 p := fun p => ge_of_tendsto' (hP p) fun k => (μ (ns k)).nonneg p
  have hsum' : ∑ p, a.1 p = 1 := by
    have h1 : Filter.Tendsto (fun k => ∑ p, (μ (ns k)).prob p) Filter.atTop
        (nhds (∑ p, a.1 p)) := tendsto_finsetSum _ fun p _ => hP p
    have h2 : (fun k => ∑ p, (μ (ns k)).prob p) = fun _ => (1 : ℝ) :=
      funext fun k => (μ (ns k)).sum_eq_one
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  let μ' : FinProb (X × Y × Z) := ⟨a.1, hnn', hsum'⟩
  have hsupp : μ'.support = S := by
    ext p
    constructor
    · intro hp
      by_contra hpS
      apply hp
      have h0 : ∀ k, (μ (ns k)).prob p = 0 := fun k => by
        by_contra hne
        exact hpS ((hS (ns k)).subset (show p ∈ (μ (ns k)).support from hne))
      have hP' := hP p
      simp only [h0] at hP'
      exact tendsto_nhds_unique hP' tendsto_const_nhds
    · intro hp
      have : α ≤ a.1 p := ge_of_tendsto' (hP p) fun k => hat (ns k) p hp
      exact ne_of_gt (lt_of_lt_of_le hα this)
  have hatoms : ∀ p ∈ S, α ≤ μ'.prob p := fun p hp =>
    ge_of_tendsto' (hP p) fun k => hat (ns k) p hp
  have hgt : ∀ k y z, (g (ns k) y + -g (ns k) y₀) + (h (ns k) z - -g (ns k) y₀) =
      g (ns k) y + h (ns k) z := fun k y z => by ring
  have hsumconv : ∀ p : X × Y × Z, Filter.Tendsto
      (fun k => g (ns k) p.2.1 + h (ns k) p.2.2) Filter.atTop
      (nhds (a.2.2.1 p.2.1 + a.2.2.2 p.2.2)) := fun p => by
    have := (hGt p.2.1).add (hHt p.2.2)
    simpa only [hgt] using this
  refine ⟨ns, hns, μ', a.2.1, a.2.2.1, a.2.2.2, fun k => -g (ns k) y₀, hP, hF, hGt, hHt, hsupp,
    hatoms, ?_, ?_, ?_, ?_⟩
  · show ∀ v ∈ embedSpan σ, (lawX μ').cinner a.2.1 v = 0
    intro v hv
    rw [lawX_cinner]
    have h1 := tendsto_cexpect (fun k => μ (ns k)) μ' hP
      (fun k p => f (ns k) p.1 * star (v p.1)) (fun p => a.2.1 p.1 * star (v p.1))
      (fun p => (hF p.1).mul_const _)
    have h0 : ∀ k, (μ (ns k)).cexpect (fun p => f (ns k) p.1 * star (v p.1)) = 0 := fun k => by
      rw [← lawX_cinner]; exact hf (ns k) v hv
    simp only [h0] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  · rw [lawX_expect]
    have h1 := tendsto_expect (fun k => μ (ns k)) μ' hP (fun k p => ‖f (ns k) p.1‖ ^ 2)
      (fun p => ‖a.2.1 p.1‖ ^ 2) (fun p => ((hF p.1).norm).pow 2)
    have h0 : ∀ k, (μ (ns k)).expect (fun p => ‖f (ns k) p.1‖ ^ 2) = 1 := fun k =>
      (lawX_expect (μ (ns k)) (fun x => ‖f (ns k) x‖ ^ 2)).symm.trans (hfn _)
    simp only [h0] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  · have h1 := tendsto_expect (fun k => μ (ns k)) μ' hP
      (fun k p => ‖g (ns k) p.2.1 + h (ns k) p.2.2‖ ^ 2)
      (fun p => ‖a.2.2.1 p.2.1 + a.2.2.2 p.2.2‖ ^ 2) (fun p => ((hsumconv p).norm).pow 2)
    simp only [hgh] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  · have h1 := tendsto_cexpect (fun k => μ (ns k)) μ' hP
      (fun k p => f (ns k) p.1 * (g (ns k) p.2.1 + h (ns k) p.2.2))
      (fun p => a.2.1 p.1 * (a.2.2.1 p.2.1 + a.2.2.2 p.2.2))
      (fun p => (hF p.1).mul (hsumconv p))
    have h2 := h1.norm
    have h3 : Filter.Tendsto (fun k : ℕ => 1 - 1 / (((ns k : ℕ) : ℝ) + 1)) Filter.atTop (nhds 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop)
      simpa using this
    exact le_of_tendsto_of_tendsto' h3 h2 (fun k => hE (ns k))

/-! ### normalisation and the fixed-shape constant -/

private theorem cexpect_zero_of_expect_zero {α : Type} [Fintype α] (π : FinProb α) (F G : α → ℂ)
    (h : π.expect (fun a => ‖F a‖ ^ 2) = 0) : π.cexpect (fun a => F a * G a) = 0 := by
  have h' : ∑ a, π.prob a * ‖F a‖ ^ 2 = 0 := h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => mul_nonneg (π.nonneg a) (sq_nonneg ‖F a‖))).1 h'
  unfold FinProb.cexpect
  refine Finset.sum_eq_zero fun a _ => ?_
  rcases mul_eq_zero.1 (h0 a (Finset.mem_univ a)) with h1 | h1
  · simp [h1]
  · have : F a = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
    simp [this]

private theorem expect_scale {α : Type} [Fintype α] (π : FinProb α) (F : α → ℂ) (t : ℝ) :
    π.expect (fun a => ‖(t : ℂ) * F a‖ ^ 2) = t ^ 2 * π.expect (fun a => ‖F a‖ ^ 2) := by
  unfold FinProb.expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  beta_reduce
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private theorem cexpect_const_mul {α : Type} [Fintype α] (π : FinProb α) (F : α → ℂ) (t : ℂ) :
    π.cexpect (fun a => t * F a) = t * π.cexpect F := by
  unfold FinProb.cexpect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

private theorem normalise (μ : FinProb (X × Y × Z)) (V : Submodule ℂ (X → ℂ)) (f : X → ℂ)
    (g : Y → ℂ) (h : Z → ℂ) (hf : f ∈ s7Perp (lawX μ) V) {c : ℝ}
    (hlt : (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
      Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2) <
      ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖) :
    ∃ (f' : X → ℂ) (g' : Y → ℂ) (h' : Z → ℂ), f' ∈ s7Perp (lawX μ) V ∧
      (lawX μ).expect (fun x => ‖f' x‖ ^ 2) = 1 ∧
      μ.expect (fun p => ‖g' p.2.1 + h' p.2.2‖ ^ 2) = 1 ∧
      1 - c ≤ ‖μ.cexpect (fun p => f' p.1 * (g' p.2.1 + h' p.2.2))‖ := by
  set A : ℝ := (lawX μ).expect fun x => ‖f x‖ ^ 2 with hA
  set B : ℝ := μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2 with hB
  have hA0 : 0 ≤ A := expect_nonneg' _ _ fun _ => sq_nonneg _
  have hB0 : 0 ≤ B := expect_nonneg' _ _ fun _ => sq_nonneg _
  have hAμ : μ.expect (fun p => ‖f p.1‖ ^ 2) = A := (lawX_expect μ (fun x => ‖f x‖ ^ 2)).symm
  rcases hA0.eq_or_lt with hA' | hApos
  · exfalso
    have := cexpect_zero_of_expect_zero μ (fun p => f p.1) (fun p => g p.2.1 + h p.2.2)
      (by rw [hAμ, ← hA'])
    rw [this, ← hA'] at hlt
    simp at hlt
  rcases hB0.eq_or_lt with hB' | hBpos
  · exfalso
    have := cexpect_zero_of_expect_zero μ (fun p => g p.2.1 + h p.2.2) (fun p => f p.1)
      hB'.symm
    have e : (fun p : X × Y × Z => f p.1 * (g p.2.1 + h p.2.2)) =
        fun p => (g p.2.1 + h p.2.2) * f p.1 := funext fun p => mul_comm _ _
    rw [e, this, ← hB'] at hlt
    simp at hlt
  set r : ℝ := (Real.sqrt A)⁻¹ with hr
  set s : ℝ := (Real.sqrt B)⁻¹ with hs
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
  have hr0 : 0 < r := inv_pos.2 hsA
  have hs0 : 0 < s := inv_pos.2 hsB
  refine ⟨(r : ℂ) • f, (s : ℂ) • g, (s : ℂ) • h, Submodule.smul_mem _ _ hf, ?_, ?_, ?_⟩
  · rw [lawX_expect]
    have := expect_scale μ (fun p => f p.1) r
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [this, hAμ, hr, inv_pow, Real.sq_sqrt hA0]
    field_simp
  · have e : (fun p : X × Y × Z => ‖((s : ℂ) • g) p.2.1 + ((s : ℂ) • h) p.2.2‖ ^ 2) =
        fun p => ‖(s : ℂ) * (g p.2.1 + h p.2.2)‖ ^ 2 := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul, mul_add]
    rw [e, expect_scale μ (fun p => g p.2.1 + h p.2.2) s, hs, inv_pow, Real.sq_sqrt hB0]
    field_simp
    rfl
  · have e : (fun p : X × Y × Z => ((r : ℂ) • f) p.1 * (((s : ℂ) • g) p.2.1 + ((s : ℂ) • h) p.2.2)) =
        fun p => ((r * s : ℝ) : ℂ) * (f p.1 * (g p.2.1 + h p.2.2)) := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e, cexpect_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos hr0 hs0)]
    have hrs : r * s * (Real.sqrt A * Real.sqrt B) = 1 := by
      rw [hr, hs]; field_simp
    have h1 : (r * s) * ((1 - c) * Real.sqrt A * Real.sqrt B) ≤ (r * s) * ‖μ.cexpect
        (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ :=
      mul_le_mul_of_nonneg_left hlt.le (mul_pos hr0 hs0).le
    have h2 : (r * s) * ((1 - c) * Real.sqrt A * Real.sqrt B) = 1 - c := by
      calc (r * s) * ((1 - c) * Real.sqrt A * Real.sqrt B)
          = (1 - c) * (r * s * (Real.sqrt A * Real.sqrt B)) := by ring
        _ = 1 - c := by rw [hrs, mul_one]
    linarith

/-- Fixed shape: for a fixed pairwise connected support `S` with a saturated master embedding, the
base-case constant exists (the compactness argument). -/
private theorem shape_const (S : Set (X × Y × Z)) (hconn : PairwiseConnected3 S) {s : ℕ}
    (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
    (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i)
    (hM : IsMasterEmbedding S Hs σ γ φ) (hsat : IsSaturated3 σ γ φ) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ : FinProb (X × Y × Z), μ.support = S → (∀ p ∈ S, α ≤ μ.prob p) →
      ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ), f ∈ s7Perp (lawX μ) (embedSpan σ) →
        ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ ≤
          (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
            Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2) := by
  by_contra hne
  push Not at hne
  have hex := fun k : ℕ => hne (1 / ((k : ℝ) + 1)) (by positivity)
  choose μ hS hat f g h hf hlt using hex
  have hn := fun k => normalise (μ k) (embedSpan σ) (f k) (g k) (h k) (hf k) (hlt k)
  choose f' g' h' hf' hfn' hgh' hE' using hn
  obtain ⟨ns, -, μ', f'', g'', h'', c, -, -, -, -, hsupp, -, hperp, hn1, hn2, hcorr⟩ :=
    s8_additive_base_compactness (X := X) (Y := Y) (Z := Z) (fun x => σ x) S hconn hα μ hS hat
      f' g' h' hf' hfn' hgh' hE'
  have hM' : IsMasterEmbedding μ'.support Hs σ γ φ := by rw [hsupp]; exact hM
  exact s8_additive_equality_forces_embedding μ' Hs σ γ φ hM' hsat f'' g'' h'' hperp hn1 hn2 hcorr

/-! ### relabelling to fixed shapes -/

private theorem mem_relabel_iff {X' Y' Z' : Type} {S : Set (X × Y × Z)} (eX : X ≃ X')
    (eY : Y ≃ Y') (eZ : Z ≃ Z') (p : X' × Y' × Z') :
    p ∈ relabelSet eX eY eZ S ↔ (eX.symm p.1, eY.symm p.2.1, eZ.symm p.2.2) ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨_, h, by simp⟩

private theorem master_relabel {X' Y' Z' : Type} {S : Set (X × Y × Z)} {s : ℕ} (Hs : Fin s → Type)
    [∀ i, AddCommGroup (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i)
    (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z') (hM : IsMasterEmbedding S Hs σ γ φ) :
    IsMasterEmbedding (relabelSet eX eY eZ S) Hs (fun x => σ (eX.symm x)) (fun y => γ (eY.symm y))
      (fun z => φ (eZ.symm z)) := by
  refine ⟨?_, ?_⟩
  · rw [isEmbedding3_iff]
    intro p hp
    rw [mem_relabel_iff] at hp
    exact (isEmbedding3_iff _ _ _ _).1 hM.1 _ hp
  · intro G _ σ'' γ'' φ'' hemb hzero
    have hemb' : IsEmbedding3 S (fun x => σ'' (eX x)) (fun y => γ'' (eY y))
        (fun z => φ'' (eZ z)) := by
      rw [isEmbedding3_iff]
      intro q hq
      exact (isEmbedding3_iff _ _ _ _).1 hemb (eX q.1, eY q.2.1, eZ q.2.2)
        ((mem_relabel_iff eX eY eZ _).2 (by simpa using hq))
    obtain ⟨⟨x0, hx0⟩, ⟨y0, hy0⟩, ⟨z0, hz0⟩⟩ := hzero
    obtain ⟨i, m₁, m₂, m₃, i1, i2, i3, e1, e2, e3⟩ := hM.2 G _ _ _ hemb'
      ⟨⟨eX.symm x0, by simpa using hx0⟩, ⟨eY.symm y0, by simpa using hy0⟩,
        ⟨eZ.symm z0, by simpa using hz0⟩⟩
    exact ⟨i, m₁, m₂, m₃, i1, i2, i3, fun x' => by simpa using e1 (eX.symm x'),
      fun y' => by simpa using e2 (eY.symm y'), fun z' => by simpa using e3 (eZ.symm z')⟩

private theorem saturated_relabel {X' : Type} {H : Type} [AddCommGroup H] (σ : X → H) (e : X ≃ X')
    (h : IsSaturated σ) : IsSaturated (fun x => σ (e.symm x)) := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, by rw [hK]; exact (e.symm.surjective.range_comp σ).symm⟩

private theorem perp_relabel {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z'] (μ : FinProb (X × Y × Z)) {H : Type}
    [AddCommGroup H] [Finite H] (σ : X → H) (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (f : X → ℂ) (hf : f ∈ s7Perp (lawX μ) (embedSpan σ)) :
    (fun x' => f (eX.symm x')) ∈
      s7Perp (lawX (lawRelabel eX eY eZ μ)) (embedSpan (fun x => σ (eX.symm x))) := by
  intro v' hv'
  rw [embedSpan_iff_fibre_constant] at hv'
  have hv : (fun x => v' (eX x)) ∈ embedSpan σ := by
    rw [embedSpan_iff_fibre_constant]
    intro x x' hx
    exact hv' _ _ (by simpa using hx)
  have h1 := hf _ hv
  rw [lawX_cinner] at h1 ⊢
  unfold lawRelabel
  rw [cexpect_push]
  simpa using h1

/-- the shape statement for a fixed support `S ⊆ X × Y × Z`. -/
private abbrev ShapeProp {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] (α : ℝ) (S : Set (X × Y × Z)) (c : ℝ) : Prop :=
  ∀ μ : FinProb (X × Y × Z), μ.support = S → (∀ p ∈ S, α ≤ μ.prob p) → PairwiseConnected3 S →
    ∀ {s : ℕ} (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
      (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i),
      IsMasterEmbedding S Hs σ γ φ → IsSaturated3 σ γ φ →
      ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ), f ∈ s7Perp (lawX μ) (embedSpan σ) →
        ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ ≤
          (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
            Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2)

private theorem shape_exists (α : ℝ) (hα : 0 < α) (S : Set (X × Y × Z)) :
    ∃ c : ℝ, 0 < c ∧ ShapeProp α S c := by
  by_cases hgood : PairwiseConnected3 S ∧ ∃ (s : ℕ) (Hs : Fin s → Type)
      (_ : ∀ i, AddCommGroup (Hs i)) (_ : ∀ i, Fintype (Hs i)) (σ : X → ∀ i, Hs i)
      (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i), IsMasterEmbedding S Hs σ γ φ ∧ IsSaturated3 σ γ φ
  · obtain ⟨hconn, s, Hs, i1, i2, σ, γ, φ, hM, hsat⟩ := hgood
    obtain ⟨c, hc, hcP⟩ := shape_const S hconn Hs σ γ φ hM hsat hα
    refine ⟨c, hc, ?_⟩
    intro μ hsupp hat hpc s' Hs' j1 j2 σ' γ' φ' hM' hsat' f g h hf
    have hS := (MaxT.PairwiseConnected3.nonempty_alphabets hconn).2.2.2
    have heq := s8_embedSpan_eq_of_master S hS Hs' σ' γ' φ' hM' Hs σ γ φ hM
    rw [heq] at hf
    exact hcP μ hsupp hat f g h hf
  · exact ⟨1, one_pos, fun μ _ _ hpc s Hs j1 j2 σ γ φ hM hsat f g h hf =>
      absurd ⟨hpc, s, Hs, j1, j2, σ, γ, φ, hM, hsat⟩ hgood⟩

end S8Additive

section S8Main

/-- Paper IV `claim:additive-base-case` (Claim 8.1, l. 4538-4570): there is `c = c(m, α) > 0`, `c ≤ 1`,
depending on `(m, α)` only (the printed order of quantifiers; the compactness proof varies
`μ`), such that for every `μ` as in the relaxed theorem (atoms `≥ α`, alphabets of size `≤ m`,
pairwise connected, saturated master embedding into a finite group with the uniform law of
hypothesis 4, `μ_{y,z}` uniform) and every `f ∈ Embed_σ(μ)^⊥`,
`|𝔼 f(x)(g(y) + h(z))| ≤ (1 - c) ‖f‖₂ ‖g + h‖₂`.  Hypotheses 6-9 of the relaxed theorem (modest set,
`ν`-data) are not used by the proof and are not assumed (a strengthening); `hu` and the uniform law
of hypothesis 4 are not used either. -/
theorem s8_additive_base_case (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
        [DecidableEq Z], Fintype.card X ≤ m → Fintype.card Y ≤ m → Fintype.card Z ≤ m →
        ∀ μ : FinProb (X × Y × Z), (∀ p ∈ μ.support, α ≤ μ.prob p) →
        PairwiseConnected3 μ.support →
        (∀ (y : Y) (z : Z), ∑ x, μ.prob (x, y, z) = 1 / ((Fintype.card Y : ℝ) * Fintype.card Z)) →
        ∀ {s : ℕ} (Hs : Fin s → Type) [∀ i, AddCommGroup (Hs i)] [∀ i, Fintype (Hs i)]
          [∀ i, DecidableEq (Hs i)] (σ : X → ∀ i, Hs i) (γ : Y → ∀ i, Hs i) (φ : Z → ∀ i, Hs i),
        IsMasterEmbedding μ.support Hs σ γ φ → IsSaturated3 σ γ φ →
        (∀ a b c : ∀ i, Hs i,
          ∑ p ∈ univ.filter (fun p : X × Y × Z => (σ p.1, γ p.2.1, φ p.2.2) = (a, b, c)),
            μ.prob p = if a + b + c = 0 then 1 / (Fintype.card (∀ i, Hs i) : ℝ) ^ 2 else 0) →
        ∀ (f : X → ℂ) (g : Y → ℂ) (h : Z → ℂ), f ∈ s7Perp (lawX μ) (embedSpan σ) →
          ‖μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2))‖ ≤
            (1 - c) * Real.sqrt ((lawX μ).expect fun x => ‖f x‖ ^ 2) *
              Real.sqrt (μ.expect fun p => ‖g p.2.1 + h p.2.2‖ ^ 2) := by
  classical
  let I := Σ i : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
    Set (Fin i.1.val × Fin i.2.1.val × Fin i.2.2.val)
  have hfin : Finite I := inferInstance
  have key : ∀ i : I, ∃ c : ℝ, 0 < c ∧ ShapeProp α i.2 c := fun i => shape_exists α hα i.2
  choose c hc0 hcS using key
  have hd : ∃ d : ℝ, 0 < d ∧ ∀ i : I, d ≤ c i := by
    rcases isEmpty_or_nonempty I with hI | hI
    · exact ⟨1, one_pos, fun i => (hI.false i).elim⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min c
      exact ⟨c i0, hc0 i0, hi0⟩
  obtain ⟨d, hd0, hdc⟩ := hd
  refine ⟨min d 1, lt_min hd0 one_pos, min_le_right _ _, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ μ hat hpc _ s Hs _ _ _ σ γ φ hM hsat _ f g h hf
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let eY : Y ≃ Fin (Fintype.card Y) := Fintype.equivFin Y
  let eZ : Z ≃ Fin (Fintype.card Z) := Fintype.equivFin Z
  let i : I := ⟨(⟨Fintype.card X, Nat.lt_succ_of_le hX⟩, ⟨Fintype.card Y, Nat.lt_succ_of_le hY⟩,
    ⟨Fintype.card Z, Nat.lt_succ_of_le hZ⟩), relabelSet eX eY eZ μ.support⟩
  have hshape := hcS i
  have hsuppeq : (lawRelabel eX eY eZ μ).support = relabelSet eX eY eZ μ.support :=
    lawRelabel_support eX eY eZ μ
  have hat' : ∀ p ∈ relabelSet eX eY eZ μ.support, α ≤ (lawRelabel eX eY eZ μ).prob p := by
    rintro p ⟨⟨x, y, z⟩, hq, rfl⟩
    show α ≤ (lawRelabel eX eY eZ μ).prob (eX x, eY y, eZ z)
    rw [lawRelabel_prob]
    exact hat _ hq
  have hpc' : PairwiseConnected3 (relabelSet eX eY eZ μ.support) :=
    (pairwiseConnected3_relabelSet_iff eX eY eZ _).2 hpc
  have hM' := master_relabel Hs σ γ φ eX eY eZ hM
  have hsat' : IsSaturated3 (fun x => σ (eX.symm x)) (fun y => γ (eY.symm y))
      (fun z => φ (eZ.symm z)) :=
    ⟨saturated_relabel σ eX hsat.1, saturated_relabel γ eY hsat.2.1,
      saturated_relabel φ eZ hsat.2.2⟩
  have hf' := perp_relabel μ σ eX eY eZ f hf
  have hmain := hshape (lawRelabel eX eY eZ μ) hsuppeq hat' hpc' Hs _ _ _ hM' hsat'
    (fun x' => f (eX.symm x')) (fun y' => g (eY.symm y')) (fun z' => h (eZ.symm z')) hf'
  have e1 : (lawRelabel eX eY eZ μ).cexpect (fun p => f (eX.symm p.1) *
      (g (eY.symm p.2.1) + h (eZ.symm p.2.2))) = μ.cexpect (fun p => f p.1 * (g p.2.1 + h p.2.2)) := by
    unfold lawRelabel
    rw [cexpect_push]
    simp
  have e2 : (lawX (lawRelabel eX eY eZ μ)).expect (fun x => ‖f (eX.symm x)‖ ^ 2) =
      (lawX μ).expect (fun x => ‖f x‖ ^ 2) := by
    rw [lawX_expect, lawX_expect]
    unfold lawRelabel
    rw [expect_push]
    simp
  have e3 : (lawRelabel eX eY eZ μ).expect (fun p => ‖g (eY.symm p.2.1) + h (eZ.symm p.2.2)‖ ^ 2) =
      μ.expect (fun p => ‖g p.2.1 + h p.2.2‖ ^ 2) := by
    unfold lawRelabel
    rw [expect_push]
    simp
  rw [e1, e2, e3] at hmain
  have hci : min d 1 ≤ c i := (min_le_left _ _).trans (hdc i)
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end S8Main

end TrackB
end RestrictedPolynomials
end
