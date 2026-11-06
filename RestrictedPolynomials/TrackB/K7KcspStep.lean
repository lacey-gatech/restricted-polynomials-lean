module

public import RestrictedPolynomials.TrackB.K7KcspRat
public import RestrictedPolynomials.TrackB.K7KcspReduce
public import RestrictedPolynomials.TrackB.K7KcspReplace
public import RestrictedPolynomials.TrackB.K7KcspTower
public import RestrictedPolynomials.TrackB.K7ProductFunctions
public import RestrictedPolynomials.TrackB.K7KcspAssembly
public import RestrictedPolynomials.ExpIterate

/-!
# Track B, `K7KcspStep`: the induction step of CSP_7 `thm:kcsp`

Source: Supplement H, §13; CSP7 `kcsp.tex`, `thm:kcsp` (steps `induction-on-k`, `apply-cor-replace-and-fstab`,
`uniformize-delta`). No convexity hypothesis `hconv` is needed. The step has no extra
hypothesis, hence no `_of_*` suffix.

* `k7_kcsp_step_unif` (`V_k ⇒ V̂_{k+1}`): for a law `μ` uniform on its support, every marginal is rational
  with `M = |supp μ| ≤ 1/α` (`k7_unif_marginal_counts`, `k7_suppSize_le`), so the rational-class
  `k7_lemma_kcsp_rat_of_ih` applies at every coordinate (`k7_kcsp_any_coordinate`). The round parameter
  `τ(η)` is its `τ` at correlation `η²`, with the induction hypothesis used at `η⁴/2`; `k7_tower_tau` bounds
  it below by a tower of height `N + 1`. Then `cor:replace` (`k7_cor_replace_of_kcsp`, built on
  `lemma:replace`) with `k` rounds, `k7_tower_rounds` (height `k (N + 3)`), the passage to stability
  (`k7_kcsp_apply_cor_replace_and_fstab`, built on `k7_lemma_fstab`) with
  `γ = min(1/2, c η'²/log(1/η'))`, `k7_tower_final` (`+1`) and `cstab_mono`.
* `k7_kcsp_step` (`V_k ⇒ V_{k+1}`, the general class): `k7_kcsp_step_unif` then `k7_tower_reduce` (the
  reduction to `Unif(supp μ)`, `prop:reduce`, `lem:absorb`); proof as in Supplement H.

All proof helpers are `private` (prefix `k7st_`).
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB
section Step

/-! ### Private helpers -/

/-- `exp(-1) ≤ 1/2`. -/
private theorem k7st_exp_neg_one_le : Real.exp (-1) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  have hpos := Real.exp_pos 1
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- a tower value at a point of `(0, 1]` is at most `1/2`. -/
private theorem k7st_tower_le_half (N : ℕ) {x b : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hb : 0 < b) :
    Real.exp (-(Real.exp^[N] (x ^ (-b)))) ≤ 1 / 2 := by
  have h1 : 1 ≤ x ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by linarith)
  have h2 : 1 ≤ Real.exp^[N] (x ^ (-b)) := h1.trans (le_exp_iterate N _)
  calc Real.exp (-(Real.exp^[N] (x ^ (-b)))) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    _ ≤ 1 / 2 := k7st_exp_neg_one_le

/-- `(η²)^(-b) = η^(-(2b))` for `η ≥ 0`. -/
private theorem k7st_sq_rpow {η : ℝ} (hη : 0 ≤ η) (b : ℝ) : (η ^ 2) ^ (-b) = η ^ (-(2 * b)) := by
  rw [← Real.rpow_natCast_mul hη]
  congr 1
  push_cast
  ring

/-- the round parameter of `cor:replace`: a function `τ` of the correlation only (chosen before the
alphabets, `μ`, `ι`, `f`) such that for every `η ∈ (0, 1]`, `τ(η) ∈ (0, 1]` is a valid `τ` of the
rational-class `lemma:kcsp` at correlation `η²` (`k7_lemma_kcsp_rat_of_ih`, with the induction hypothesis
`hih` at `η⁴/2`), and `τ(η) ≥ exp(-exp^{[N+1]}(η^{-b₁}))` for `η ≤ 1/2` (`k7_tower_tau` at `η²`). -/
private theorem k7st_round_tau (k : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (N : ℕ) {b : ℝ}
    (hb : 0 < b)
    (Hih : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[N] (ε ^ (-b)))) ≤
            (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[N] (ε ^ (-b))))) (f i)).re)) :
    ∃ b₁ : ℝ, 0 < b₁ ∧ ∃ τf : ℝ → ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      0 < τf η ∧ τf η ≤ 1 ∧
      (η ≤ 1 / 2 → Real.exp (-(Real.exp^[N + 1] (η ^ (-b₁)))) ≤ τf η) ∧
      ∀ (h0 : 0 ≤ τf η) (h1 : τf η ≤ 1) (A : Fin (k + 1) → Type) [∀ i, Fintype (A i)]
        [∀ i, DecidableEq (A i)] (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k),
        PairwiseConnectedDist μ → (∀ a ∈ μ.support, α ≤ μ.prob a) →
        NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support →
        (∃ (M : ℕ) (n : A (j.succAbove s) → ℕ), (∀ a, 1 ≤ n a ∧ n a ≤ M) ∧ (M : ℝ) ≤ 1 / α ∧
          ∀ a, (μ.marginalPi (j.succAbove s)).prob a = (n a : ℝ) / M) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ),
          (∀ i x, ‖f i x‖ ≤ 1) →
          η ^ 2 ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          τf η ≤ k7EventProb (μ.marginalPi (j.succAbove s)) (μ.marginalPi (j.succAbove s))
            (τf η) (τf η) h0 h1 (f (j.succAbove s)) := by
  obtain ⟨B, c₁, hB, hc0, hc1, H⟩ := k7_lemma_kcsp_rat_of_ih hα0 hα1 k
  obtain ⟨b₁, hb₁, Htau⟩ := k7_tower_tau N hb hB hc0 hc1
  have key : ∀ η : ℝ, ∃ τ : ℝ, 0 < η → η ≤ 1 →
      0 < τ ∧ τ ≤ 1 ∧
      (η ≤ 1 / 2 → Real.exp (-(Real.exp^[N + 1] (η ^ (-(2 * b₁))))) ≤ τ) ∧
      ∀ (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (A : Fin (k + 1) → Type) [∀ i, Fintype (A i)]
        [∀ i, DecidableEq (A i)] (μ : FinProb (∀ i, A i)) (j : Fin (k + 1)) (s : Fin k),
        PairwiseConnectedDist μ → (∀ a ∈ μ.support, α ≤ μ.prob a) →
        NoNontrivialAbelianEmbeddingPi (k7DropMarg μ j).support →
        (∃ (M : ℕ) (n : A (j.succAbove s) → ℕ), (∀ a, 1 ≤ n a ∧ n a ≤ M) ∧ (M : ℝ) ≤ 1 / α ∧
          ∀ a, (μ.marginalPi (j.succAbove s)).prob a = (n a : ℝ) / M) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ),
          (∀ i x, ‖f i x‖ ≤ 1) →
          η ^ 2 ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          τ ≤ k7EventProb (μ.marginalPi (j.succAbove s)) (μ.marginalPi (j.succAbove s)) τ τ h0 h1
            (f (j.succAbove s)) := by
    intro η
    by_cases hη : 0 < η ∧ η ≤ 1
    · obtain ⟨hη0, hη1⟩ := hη
      have hsq1 : η ^ 2 ≤ 1 := by nlinarith
      have hx0 : 0 < (η ^ 2) ^ 2 / 2 := by positivity
      have hx1 : (η ^ 2) ^ 2 / 2 ≤ 1 / 2 := by
        have : (η ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg η]
        linarith
      have hδ1 : Real.exp (-(Real.exp^[N] (((η ^ 2) ^ 2 / 2) ^ (-b)))) ≤ 1 / 2 :=
        k7st_tower_le_half N hx0 (by linarith) hb
      obtain ⟨τ, hτ0, hτ1, hlow, Hτ⟩ := H (η ^ 2)
        (Real.exp (-(Real.exp^[N] (((η ^ 2) ^ 2 / 2) ^ (-b))))) (by positivity) hsq1
        (Real.exp_pos _) hδ1 (Hih _ hx0 hx1)
      have hpos : 0 < τ := by
        refine lt_of_lt_of_le ?_ hlow
        refine mul_pos (mul_pos hc0 (mul_pos (by positivity) (Real.exp_pos _))) (Real.exp_pos _)
      refine ⟨τ, fun _ _ => ⟨hpos, hτ1, fun hη2 => ?_, fun h0 h1 A _ _ μ j s hpc hat hno hrat ι _ _
        f hf hc => Hτ A μ j s hpc hat hno hrat ι f hf hc⟩⟩
      have hη2' : η ^ 2 ≤ 1 / 2 := by nlinarith
      obtain ⟨-, hT⟩ := Htau (η ^ 2) (by positivity) hη2'
        (Real.exp (-(Real.exp^[N] (((η ^ 2) ^ 2 / 2) ^ (-b))))) rfl
      rw [k7st_sq_rpow hη0.le] at hT
      exact hT.trans hlow
    · exact ⟨1, fun h0 h1 => absurd ⟨h0, h1⟩ hη⟩
  choose τf hτf using key
  exact ⟨2 * b₁, by positivity, τf, fun η h0 h1 => hτf η h0 h1⟩

/-! ### The step -/

/-- the induction step at the UNIFORM law, `V_k ⇒ V̂_{k+1}` (Supplement H): for `k ≥ 3`, the
explicit-tower hypothesis `hih` (the general class at level `k`, height `N`) gives the explicit tower
`k (N+3) + 1` at level `k+1` for the laws UNIFORM ON THEIR SUPPORT. The proof: for such `μ` every marginal
is rational with `M = |supp μ| ≤ 1/α` (`k7_unif_marginal_counts`, `k7_suppSize_le`), so
`k7_lemma_kcsp_rat_of_ih` applies at every coordinate; `taufun` from it at correlation `η²`
(IH at `η⁴/2`), `hlk` for every coordinate by `k7_kcsp_any_coordinate`, `k7_cor_replace_of_kcsp` with
`m = k`, `k7_tower_rounds` (`h' = N+1` from `k7_tower_tau`, height `k (N+3)`),
`k7_kcsp_apply_cor_replace_and_fstab` with `γ = min(1/2, c η'²/log(1/η'))`, `k7_tower_final` (`+1`) and
`k7_valid_mono`. The induction hypothesis is used at `μ_{-j}`, in the general class
(`k7_dropMarg_atom_bound`, `noNontrivialAbelianEmbeddingPi_image_succAbove`); no `hconv`, no `hbase`. -/
theorem k7_kcsp_step_unif
    (k : ℕ) (hk : 3 ≤ k) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (N : ℕ)
    (hih : ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[N] (ε ^ (-b)))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[N] (ε ^ (-b))))) (f i)).re)) :
    ∃ b' : ℝ, 0 < b' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin (k + 1) → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        (∀ a ∈ μ.support, ∀ b ∈ μ.support, μ.prob a = μ.prob b) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[k * (N + 3) + 1] (ε ^ (-b')))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[k * (N + 3) + 1] (ε ^ (-b'))))) (f i)).re) := by
  obtain ⟨b, hb, Hih⟩ := hih
  obtain ⟨b₁, hb₁, τf, hτf⟩ := k7st_round_tau k hα0 hα1 N hb Hih
  obtain ⟨b₂, hb₂, Hr⟩ := k7_tower_rounds (N + 1) k hb₁
  obtain ⟨c, hc, Hfs⟩ := k7_kcsp_apply_cor_replace_and_fstab k hα0
  obtain ⟨b₃, hb₃, Hf⟩ := k7_tower_final (k * (N + 1 + 2)) hb₂ hc
  refine ⟨b₃, hb₃, fun ε hε0 hε1 A _ _ μ hno hatom hunif ι _ _ f hf hcorr i => ?_⟩
  have hτ : ∀ η : ℝ, 0 < η → η ≤ 1 → 0 < τf η ∧ τf η ≤ 1 := fun η h0 h1 =>
    ⟨(hτf η h0 h1).1, (hτf η h0 h1).2.1⟩
  -- every marginal of a law uniform on its support is rational with `M = |supp μ| ≤ 1/α`
  have hrat : ∀ i : Fin (k + 1), ∃ (M : ℕ) (n : A i → ℕ), (∀ a, 1 ≤ n a ∧ n a ≤ M) ∧
      (M : ℝ) ≤ 1 / α ∧ ∀ a, (μ.marginalPi i).prob a = (n a : ℝ) / M := by
    intro i
    obtain ⟨n, hn, hm⟩ := k7_unif_marginal_counts μ hno hunif i
    exact ⟨k7SuppSize μ, n, hn, k7_suppSize_le hα0 μ hatom, hm⟩
  -- `lemma:kcsp` at every coordinate, for every round correlation `η²`
  have hlk : ∀ (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1) (i₁ : Fin (k + 1)) (ι' : Type) [Fintype ι']
      [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ), (∀ i x, ‖F i x‖ ≤ 1) →
      η ^ 2 ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
      τf η ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) (τf η) (τf η)
        (hτ η h0 h1).1.le (hτ η h0 h1).2 (F i₁) := fun η h0 h1 =>
    k7_kcsp_any_coordinate μ (by omega) hno (hτ η h0 h1).1.le (hτ η h0 h1).2
      (fun j s hpc hno' ι' _ _ F hF hc =>
        (hτf η h0 h1).2.2.2 (hτ η h0 h1).1.le (hτ η h0 h1).2 A μ j s hpc hatom hno' (hrat _) ι' F
          hF hc)
  -- `cor:replace`, `k` rounds, the survivor `i`
  obtain ⟨R, p, η', hR0, hR1, hRdef, hpdef, hηdef, hp⟩ :=
    k7_cor_replace_of_kcsp μ i τf hτ hlk f hf hε0 (by linarith) hcorr
  -- the tower side of the rounds
  have hround : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      Real.exp (-(Real.exp^[N + 1] (η ^ (-b₁)))) ≤ τf η ∧ τf η ≤ 1 := fun η h0 h1 =>
    ⟨(hτf η h0 (by linarith)).2.2.1 h1, (hτf η h0 (by linarith)).2.1⟩
  obtain ⟨hRlow, hplow, hηlow, hηup⟩ := Hr τf hround ε hε0 hε1
  rw [← hRdef] at hRlow
  rw [← hpdef] at hplow
  rw [← hηdef] at hηlow hηup
  have hiter : ∀ r : ℕ, 0 < (fun x => τf x / 2)^[r] ε ∧ (fun x => τf x / 2)^[r] ε ≤ 1 := by
    intro r
    induction r with
    | zero =>
      show 0 < ε ∧ ε ≤ 1
      exact ⟨hε0, by linarith⟩
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h0, h1⟩ := hτ _ ih.1 ih.2
      constructor <;> linarith
  have hp1 : p ≤ 1 := by
    rw [hpdef]
    refine Finset.prod_le_one₀ (fun r _ => by positivity) (fun r _ => ?_)
    obtain ⟨h0, h1⟩ := hτ _ (hiter r).1 (hiter r).2
    nlinarith
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hRlow
  have hηpos : 0 < η' := lt_of_lt_of_le (Real.exp_pos _) hηlow
  obtain ⟨hδR, hδp⟩ := Hf ε hε0 hε1 R p η' hRlow hplow hηlow hηup hR1 hp1
  -- the passage to stability (`lemma:fstab`)
  have hlog : 0 < Real.log (1 / η') := Real.log_pos (by rw [lt_div_iff₀ hηpos]; linarith)
  have hγ0 : 0 < min (1 / 2 : ℝ) (c * η' ^ 2 / Real.log (1 / η')) :=
    lt_min (by norm_num) (div_pos (mul_pos hc (pow_pos hηpos 2)) hlog)
  have hγh : min (1 / 2 : ℝ) (c * η' ^ 2 / Real.log (1 / η')) ≤ 1 / 2 := min_le_left _ _
  have hfs := Hfs A μ hno hatom i ι f hf R p η' hRpos hR1 hηpos (by linarith) hp
    (min (1 / 2 : ℝ) (c * η' ^ 2 / Real.log (1 / η'))) hγ0 (by linarith) (min_le_right _ _)
  have he : k * (N + 1 + 2) + 1 = k * (N + 3) + 1 := by ring
  rw [he] at hδR hδp
  have hδpos := Real.exp_pos (-(Real.exp^[k * (N + 3) + 1] (ε ^ (-b₃))))
  have hγR : min (1 / 2 : ℝ) (c * η' ^ 2 / Real.log (1 / η')) * R ≤ 1 / 2 := by nlinarith
  -- `uniformize-delta`: lower the parameter (`cstab_mono`)
  have hmono := (Complex.le_def.1 (cstab_mono (μ.marginalPi i)
    (by linarith : 0 ≤ 1 - min (1 / 2 : ℝ) (c * η' ^ 2 / Real.log (1 / η')) * R)
    (by linarith : 1 - min (1 / 2 : ℝ) (c * η' ^ 2 / Real.log (1 / η')) * R ≤
      1 - Real.exp (-(Real.exp^[k * (N + 3) + 1] (ε ^ (-b₃))))) (f i))).1
  linarith


/-- the induction step of CSP_7 `thm:kcsp`, step `induction-on-k`, for `k ≥ 3`, `V_k ⇒ V_{k+1}` in the GENERAL class
(no convexity hypothesis `hconv` is needed): `k7_kcsp_step_unif`
at the uniform laws, then `k7_tower_reduce` (`prop:reduce`, `lem:absorb`, the lowering `k7_valid_mono`).
This is WHERE THE REDUCTION ENTERS `thm:kcsp`. It has no extra hypothesis (the induction hypothesis `hih` is
the premise of an implication, not a gap), hence no `_of_*` suffix. -/
theorem k7_kcsp_step
    (k : ℕ) (hk : 3 ≤ k) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (N : ℕ)
    (hih : ∃ b : ℝ, 0 < b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin k → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[N] (ε ^ (-b)))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[N] (ε ^ (-b))))) (f i)).re)) :
    ∃ b' : ℝ, 0 < b' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ (A : Fin (k + 1) → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[k * (N + 3) + 1] (ε ^ (-b')))) ≤ (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[k * (N + 3) + 1] (ε ^ (-b'))))) (f i)).re) := by
  obtain ⟨b', hb', hU⟩ := k7_kcsp_step_unif k hk hα0 hα1 N hih
  obtain ⟨b'', hb'', H⟩ := k7_tower_reduce (k + 1) (k * (N + 3) + 1) hα0 hα1 hb'
    (fun ε' h0 h1 => hU ε' h0 h1)
  exact ⟨b'', hb'', fun ε h0 h1 => H ε h0 h1⟩

/-- INTERFACE CHECK (compile time): `k7_lemma_kcsp_rat_of_ih` at a fixed `μ` whose every marginal is
rational (`hrat`; for a law uniform on its support this is `k7_unif_marginal_counts` with
`k7_suppSize_le`) feeds `k7_kcsp_any_coordinate` exactly: the premise `hF3` is discharged with no
adapter. This is how `k7_kcsp_step_unif` consumes the rational lemma at every coordinate. -/
example {k : ℕ} (hk : 1 ≤ k) {α ε δ' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1 / 2)
    (ih : ∀ (A' : Fin k → Type) [∀ i, Fintype (A' i)] [∀ i, DecidableEq (A' i)]
      (μ' : FinProb (∀ i, A' i)), NoNontrivialAbelianEmbeddingPi μ'.support →
      (∀ a ∈ μ'.support, α ≤ μ'.prob a) →
      ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (f' : ∀ i, (ι' → A' i) → ℂ),
        (∀ i x, ‖f' i x‖ ≤ 1) →
        ε ^ 2 / 2 ≤ ‖(μ'.pi ι').cexpect fun X => ∏ i, f' i fun t => X t i‖ →
        ∀ i, δ' ≤ (cstab (μ'.marginalPi i) (1 - δ') (f' i)).re)
    {A : Fin (k + 1) → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (μ : FinProb (∀ i, A i)) (hno : NoNontrivialAbelianEmbeddingPi μ.support)
    (hatom : ∀ a ∈ μ.support, α ≤ μ.prob a)
    (hrat : ∀ i : Fin (k + 1), ∃ (M : ℕ) (n : A i → ℕ), (∀ a, 1 ≤ n a ∧ n a ≤ M) ∧
      (M : ℝ) ≤ 1 / α ∧ ∀ a, (μ.marginalPi i).prob a = (n a : ℝ) / M) :
    ∃ (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1),
      ∀ (i₁ : Fin (k + 1)) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (F : ∀ i, (ι' → A i) → ℂ),
        (∀ i x, ‖F i x‖ ≤ 1) → ε ≤ ‖(μ.pi ι').cexpect fun X => ∏ i, F i fun t => X t i‖ →
        τ ≤ k7EventProb (μ.marginalPi i₁) (μ.marginalPi i₁) τ τ hτ0 hτ1 (F i₁) := by
  obtain ⟨B, c₁, -, -, -, H⟩ := k7_lemma_kcsp_rat_of_ih hα0 hα1 k
  obtain ⟨τ, hτ0, hτ1, -, Hτ⟩ := H ε δ' hε0 hε1 hδ0 hδ1 ih
  exact ⟨τ, hτ0, hτ1, k7_kcsp_any_coordinate μ hk hno hτ0 hτ1
    (fun j s hpc hno' ι' _ _ F hF hcorr => Hτ A μ j s hpc hatom hno' (hrat _) ι' F hF hcorr)⟩

end Step

end TrackB
end RestrictedPolynomials
end
