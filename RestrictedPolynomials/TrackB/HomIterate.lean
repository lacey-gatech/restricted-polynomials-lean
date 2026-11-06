module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Real

/-!
# Track B: the iteration of `delta_inductive` and the parameter hierarchy of Thm 7.14

Paper IV Section 9.4 (l. 5936-5960, "Finishing the Proof of Theorem
`nonembed_homogenous`"). SETTING-FREE: the objects are a function `δ : ℕ → ℕ → ℝ≥0∞` (in the
application `δ n d' = δ_{n,d'}[μ]`, `s7DeltaParam μ hμ Bx.u n d'`) and real parameters.

* `hom_iterate_delta_of_step`: the telescoping of l. 5946-5953, for ANY `k` steps whose side conditions
  `n - i ≤ (e' - i) A` hold (the source applies Lemma 9.3 "`e'/2` times"; the `+ 1` below is the
  integer rounding).
* `hom_delta_decay_of_step`: the choice `A = 4 L d^ξ` of l. 5944-5946 made explicit: from
  `n' ≤ L d`, `d' ≤ 2 e'`, `d^{1-ξ} ≤ d'` one gets `n' - i ≤ (e' - i) A` for `i ≤ e'/2`. The
  hypothesis `hstep` is the SHAPE of the conclusion of Lemma 9.3 at `μ`; the main theorem
  discharges it from `s9d_delta_inductive` (no printed proof step is a binder there).
* `hom_constants`: `#parameter-hierarchy` and `#exponent-reconciliation`. From `(L, ε)` of
  Lemma 8.12 and `C'` of Lemma 9.3 it produces `ξ` (small in terms of `C'`: `ξ ≤ 1/(4 C'²)`,
  `ξ ≤ 1/2`) and then `c` (small in terms of `ε`, `L`, `C'`: `c ≤ ε/2`, `c ≤ (4L)^{-C'}/4`), with
  the two decay estimates in the final form `(1 + c)^{-d'^{1-√ξ}}` (the printed `1 - 2ξ` is
  not what the proof gives).

The order is `L, ε, C'` before `ξ` before `c` (source l. 5937-5940, `#parameter-hierarchy`), stated
as `∃ ξ c` after `(L, ε, C')`.
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Iterate

/-- the telescoping `δ_{n,e'} ≤ (1 - 1/A^{C})^k δ_{n-k,e'-k}` of l. 5946-5953, abstract: `k` steps
of `hstep` (the shape of Lemma 9.3 with ratio `A`), each admissible because
`n - i ≤ (e' - i) A`, `1 ≤ e' - i`, `e' - i ≤ n - i`; then the trivial bound `δ ≤ 1`
(paper IV `claim-beta-trivial-bound`). `q` is `1 - A^{-C}` in the application. -/
theorem hom_iterate_delta_of_step (δ : ℕ → ℕ → ℝ≥0∞) {A q : ℝ} (hδ1 : ∀ n d' : ℕ, δ n d' ≤ 1)
    (hstep : ∀ n d' : ℕ, 1 ≤ d' → d' ≤ n → (n : ℝ) ≤ d' * A →
      δ n d' ≤ ENNReal.ofReal q * δ (n - 1) (d' - 1)) :
    ∀ k n e' : ℕ, k ≤ e' → e' ≤ n →
      (∀ i < k, ((n - i : ℕ) : ℝ) ≤ ((e' - i : ℕ) : ℝ) * A) →
      δ n e' ≤ ENNReal.ofReal q ^ k := by
  intro k
  induction k with
  | zero => intro n e' _ _ _; simpa using hδ1 n e'
  | succ k ih =>
    intro n e' hk hen hside
    have h0 := hside 0 (by omega)
    simp only [Nat.sub_zero] at h0
    have h1 := hstep n e' (by omega) hen h0
    have h2 := ih (n - 1) (e' - 1) (by omega) (by omega) (by
      intro i hi
      have := hside (i + 1) (by omega)
      have e1 : n - (i + 1) = n - 1 - i := by omega
      have e2 : e' - (i + 1) = e' - 1 - i := by omega
      rwa [e1, e2] at this)
    calc δ n e' ≤ ENNReal.ofReal q * δ (n - 1) (e' - 1) := h1
      _ ≤ ENNReal.ofReal q * ENNReal.ofReal q ^ k := by gcongr
      _ = ENNReal.ofReal q ^ (k + 1) := by rw [pow_succ']

/-- `#iterate-delta-inductive` (l. 5944-5960) with the explicit ratio `A = 4 L d^ξ`: if
`n' ≤ L d` (stopping point, `s9_beta_bound_iterated_stopping`), `d' ≤ 2 e'`, `d^{1-ξ} ≤ d'`,
`1 ≤ d'`, `d' ≤ d`, `e' ≤ e ≤ n'`, then `δ_{n',e'} ≤ (1 - A^{-C'})^{⌊e'/2⌋+1}`. `hstep` is the
conclusion shape of `s9d_delta_inductive` at `μ` (for every `A ≥ 2`; here `A ≥ 8`). The exponent is
at least `d'/4`, which `hom_constants` converts into `(1+c)^{-d'^{1-√ξ}}`. -/
theorem hom_delta_decay_of_step (δ : ℕ → ℕ → ℝ≥0∞) {L C' ξ : ℝ} (hL : 2 ≤ L) (hC' : 0 < C')
    (hξ : 0 < ξ) (hδ1 : ∀ n d' : ℕ, δ n d' ≤ 1)
    (hstep : ∀ A : ℝ, 2 ≤ A → ∀ n d' : ℕ, 1 ≤ d' → d' ≤ n → (n : ℝ) ≤ d' * A →
      δ n d' ≤ ENNReal.ofReal (1 - 1 / A ^ C') * δ (n - 1) (d' - 1))
    {d d' e e' n' : ℕ} (hd' : 1 ≤ d') (hd'd : d' ≤ d) (hdd' : (d : ℝ) ^ (1 - ξ) ≤ d')
    (he' : d' ≤ 2 * e') (he'e : e' ≤ e) (hen' : e ≤ n') (hn' : (n' : ℝ) ≤ L * d) :
    δ n' e' ≤ ENNReal.ofReal ((1 - 1 / (4 * L * (d : ℝ) ^ ξ) ^ C') ^ (e' / 2 + 1)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd'.trans hd'd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdξ : 1 ≤ (d : ℝ) ^ ξ := Real.one_le_rpow hd1 hξ.le
  have hA8 : 8 ≤ 4 * L * (d : ℝ) ^ ξ := by nlinarith
  have hAC : 1 ≤ (4 * L * (d : ℝ) ^ ξ) ^ C' := Real.one_le_rpow (by linarith) hC'.le
  have hq0 : 0 ≤ 1 - 1 / (4 * L * (d : ℝ) ^ ξ) ^ C' := by
    have : 1 / (4 * L * (d : ℝ) ^ ξ) ^ C' ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hAC
    linarith
  have hdsplit : (d : ℝ) = (d : ℝ) ^ (1 - ξ) * (d : ℝ) ^ ξ := by
    rw [← Real.rpow_add hdpos]; simp
  have key := hom_iterate_delta_of_step δ hδ1 (fun n d1 h1 h2 h3 => hstep (4 * L * (d : ℝ) ^ ξ) (by linarith) n d1 h1 h2 h3)
    (e' / 2 + 1) n' e' (by omega) (by omega) (by
      intro i hi
      have hi2 : 2 * i ≤ e' := by omega
      have h2e : (e' : ℝ) ≤ 2 * ((e' - i : ℕ) : ℝ) := by
        have : e' ≤ 2 * (e' - i) := by omega
        exact_mod_cast this
      have hd'r : (d' : ℝ) ≤ 2 * e' := by exact_mod_cast he'
      have hni : ((n' - i : ℕ) : ℝ) ≤ n' := by exact_mod_cast Nat.sub_le n' i
      have hdξ0 : (0 : ℝ) ≤ (d : ℝ) ^ ξ := by positivity
      calc ((n' - i : ℕ) : ℝ) ≤ n' := hni
        _ ≤ L * d := hn'
        _ = L * ((d : ℝ) ^ (1 - ξ) * (d : ℝ) ^ ξ) := by rw [← hdsplit]
        _ ≤ L * ((d' : ℝ) * (d : ℝ) ^ ξ) := by gcongr
        _ ≤ L * ((2 * e' : ℝ) * (d : ℝ) ^ ξ) := by gcongr
        _ ≤ L * ((4 * ((e' - i : ℕ) : ℝ)) * (d : ℝ) ^ ξ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hdξ0) (by linarith)
        _ = ((e' - i : ℕ) : ℝ) * (4 * L * (d : ℝ) ^ ξ) := by ring)
  rw [← ENNReal.ofReal_pow hq0] at key
  exact key

end Iterate

section Constants

/-- `#parameter-hierarchy` (l. 5937-5940, `0 ≪ ξ ≪ C^{-1} ≪ L^{-1} ≪ α, m^{-1}`) and
`#exponent-reconciliation`, as a real-analytic theorem: given `L ≥ 2`, `ε ∈ (0, 1)` and
`C' > 0` there are `ξ ∈ (0, 1)` and `c > 0` such that
(1) `(1 - ε)^{d'/2} ≤ (1 + c)^{-d'^{1-√ξ}}` for all `d'` (case 1 of Lemma 8.12), and
(2) `(1 - (4 L d^ξ)^{-C'})^{⌊e'/2⌋+1} ≤ (1 + c)^{-d'^{1-√ξ}}` whenever `1 ≤ d' ≤ d`,
`d^{1-ξ} ≤ d'` and `d' ≤ 2 e'` (case 2, the end of l. 5957-5958).
Route: `ξ = min(1/2, 1/(4C'^2))` so that `d^{ξC'} ≤ d'^{ξC'/(1-ξ)} ≤ d'^{√ξ}`;
`c = min(ε/2, (4L)^{-C'}/4)`; `(1 - x)^k ≤ e^{-kx}`, `log(1 + c) ≤ c`; the exponent
`⌊e'/2⌋ + 1 ≥ d'/4`. Numerically checked (400,000 random instances, no failure). -/
theorem hom_constants {L ε C' : ℝ} (hL : 2 ≤ L) (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < C') :
    ∃ ξ c : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < c ∧
      (∀ d' : ℕ, (1 - ε) ^ ((d' : ℝ) / 2) ≤ (1 + c) ^ (-((d' : ℝ) ^ (1 - Real.sqrt ξ)))) ∧
      (∀ d d' e' : ℕ, 1 ≤ d' → d' ≤ d → (d : ℝ) ^ (1 - ξ) ≤ d' → d' ≤ 2 * e' →
        (1 - 1 / (4 * L * (d : ℝ) ^ ξ) ^ C') ^ (e' / 2 + 1) ≤
          (1 + c) ^ (-((d' : ℝ) ^ (1 - Real.sqrt ξ)))) := by
  have hξpos : 0 < min (1 / 2 : ℝ) (1 / (4 * C' ^ 2)) := lt_min (by norm_num) (by positivity)
  generalize hξdef : min (1 / 2 : ℝ) (1 / (4 * C' ^ 2)) = ξ at hξpos
  have hξle : ξ ≤ 1 / 2 := hξdef ▸ min_le_left _ _
  have hξC : ξ ≤ 1 / (4 * C' ^ 2) := hξdef ▸ min_le_right _ _
  have hs2 : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt hξpos.le
  have hspos : 0 < Real.sqrt ξ := Real.sqrt_pos.2 hξpos
  generalize hsdef : Real.sqrt ξ = s at hs2 hspos ⊢
  have hs1 : s < 1 := by nlinarith
  have hξC' : ξ * C' ^ 2 ≤ 1 / 4 := by
    have h4 : (0 : ℝ) < 4 * C' ^ 2 := by positivity
    have := (le_div_iff₀ h4).1 hξC
    linarith
  have hsC : s * C' ≤ 1 / 2 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hspos hC]
  have hP : 0 < (4 * L) ^ C' := Real.rpow_pos_of_pos (by linarith) _
  have hcpos : 0 < min (ε / 2) (1 / (4 * (4 * L) ^ C')) := lt_min (by linarith) (by positivity)
  generalize hcdef : min (ε / 2) (1 / (4 * (4 * L) ^ C')) = c at hcpos
  have hc1 : c ≤ ε / 2 := hcdef ▸ min_le_left _ _
  have hc2 : c ≤ 1 / (4 * (4 * L) ^ C') := hcdef ▸ min_le_right _ _
  have rhs_ge : ∀ t : ℝ, 0 ≤ t → Real.exp (-(c * t)) ≤ (1 + c) ^ (-t) := by
    intro t ht
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.2
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + c by linarith)
    nlinarith
  refine ⟨ξ, c, hξpos, by linarith, hcpos, ?_, ?_⟩
  all_goals simp only [hsdef]
  · intro d'
    have ht0 : 0 ≤ (d' : ℝ) ^ (1 - s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have htle : (d' : ℝ) ^ (1 - s) ≤ d' := by
      rcases Nat.eq_zero_or_pos d' with h | h
      · subst h
        simp [Real.zero_rpow (by linarith : 1 - s ≠ 0)]
      · have h1 : (1 : ℝ) ≤ d' := by exact_mod_cast h
        calc (d' : ℝ) ^ (1 - s) ≤ (d' : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ = d' := Real.rpow_one _
    have hlhs : (1 - ε) ^ ((d' : ℝ) / 2) ≤ Real.exp (-(ε * ((d' : ℝ) / 2))) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2
      have := Real.log_le_sub_one_of_pos (show 0 < 1 - ε by linarith)
      have hd0 : (0 : ℝ) ≤ (d' : ℝ) / 2 := by positivity
      nlinarith
    calc (1 - ε) ^ ((d' : ℝ) / 2) ≤ Real.exp (-(ε * ((d' : ℝ) / 2))) := hlhs
      _ ≤ Real.exp (-(c * (d' : ℝ) ^ (1 - s))) := by
          apply Real.exp_le_exp.2
          have : c * (d' : ℝ) ^ (1 - s) ≤ (ε / 2) * d' := mul_le_mul hc1 htle ht0 (by linarith)
          linarith
      _ ≤ _ := rhs_ge _ ht0
  · intro d d' e' hd'1 hd'd hdd' hd'e'
    have hd'1r : (1 : ℝ) ≤ d' := by exact_mod_cast hd'1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd'1.trans hd'd
    have hdpos : (0 : ℝ) < d := by linarith
    have hd'pos : (0 : ℝ) < d' := by linarith
    have hdξ : 1 ≤ (d : ℝ) ^ ξ := Real.one_le_rpow hd1 hξpos.le
    have hA : 8 ≤ 4 * L * (d : ℝ) ^ ξ := by nlinarith
    have hR0 : 0 ≤ ((d : ℝ) ^ ξ) ^ C' := Real.rpow_nonneg (by positivity) _
    have hAC : (4 * L * (d : ℝ) ^ ξ) ^ C' = (4 * L) ^ C' * ((d : ℝ) ^ ξ) ^ C' :=
      Real.mul_rpow (by linarith) (by positivity)
    have hR : ((d : ℝ) ^ ξ) ^ C' ≤ (d' : ℝ) ^ s := by
      have hu : ξ * C' / (1 - ξ) ≤ s := by
        rw [div_le_iff₀ (by linarith)]
        have e1 : ξ * C' = s * (s * C') := by rw [← hs2]; ring
        have e2 : s * (s * C') ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left hsC hspos.le
        have e3 : 0 ≤ s * (1 / 2 - ξ) := mul_nonneg hspos.le (by linarith)
        nlinarith
      have hu0 : 0 ≤ ξ * C' / (1 - ξ) := by
        have : 0 < 1 - ξ := by linarith
        positivity
      calc ((d : ℝ) ^ ξ) ^ C' = ((d : ℝ) ^ (1 - ξ)) ^ (ξ * C' / (1 - ξ)) := by
            rw [← Real.rpow_mul hdpos.le, ← Real.rpow_mul hdpos.le]
            have hne : (1 - ξ) ≠ 0 := by linarith
            congr 1
            field_simp
        _ ≤ (d' : ℝ) ^ (ξ * C' / (1 - ξ)) :=
            Real.rpow_le_rpow (by positivity) hdd' hu0
        _ ≤ (d' : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hd'1r hu
    have hQ : 0 < (d' : ℝ) ^ s := Real.rpow_pos_of_pos hd'pos _
    have hAC1 : 1 ≤ ((d : ℝ) ^ ξ) ^ C' := Real.one_le_rpow hdξ hC.le
    have hAC0 : 0 < (4 * L * (d : ℝ) ^ ξ) ^ C' := Real.rpow_pos_of_pos (by linarith) _
    have hx0 : 0 ≤ 1 - 1 / (4 * L * (d : ℝ) ^ ξ) ^ C' := by
      have : 1 / (4 * L * (d : ℝ) ^ ξ) ^ C' ≤ 1 := by
        rw [div_le_one hAC0, hAC]
        have : 1 ≤ (4 * L) ^ C' := Real.one_le_rpow (by linarith) hC.le
        nlinarith
      linarith
    have hxlow : 1 / ((4 * L) ^ C' * (d' : ℝ) ^ s) ≤ 1 / (4 * L * (d : ℝ) ^ ξ) ^ C' := by
      apply one_div_le_one_div_of_le hAC0
      rw [hAC]
      exact mul_le_mul_of_nonneg_left hR hP.le
    have hk : (d' : ℝ) ≤ 4 * ((e' / 2 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : d' ≤ 4 * (e' / 2 + 1))
    have ht : (d' : ℝ) ^ (1 - s) = d' / (d' : ℝ) ^ s := by
      rw [Real.rpow_sub hd'pos, Real.rpow_one]
    have ht0 : 0 ≤ (d' : ℝ) ^ (1 - s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hmain : c * (d' : ℝ) ^ (1 - s) ≤
        ((e' / 2 + 1 : ℕ) : ℝ) * (1 / (4 * L * (d : ℝ) ^ ξ) ^ C') := by
      calc c * (d' : ℝ) ^ (1 - s) ≤ (1 / (4 * (4 * L) ^ C')) * (d' : ℝ) ^ (1 - s) :=
            mul_le_mul_of_nonneg_right hc2 ht0
        _ = ((d' : ℝ) / 4) * (1 / ((4 * L) ^ C' * (d' : ℝ) ^ s)) := by
            rw [ht]; field_simp
        _ ≤ ((e' / 2 + 1 : ℕ) : ℝ) * (1 / (4 * L * (d : ℝ) ^ ξ) ^ C') := by
            apply mul_le_mul (by linarith) hxlow (by positivity) (by positivity)
    calc (1 - 1 / (4 * L * (d : ℝ) ^ ξ) ^ C') ^ (e' / 2 + 1)
        ≤ (Real.exp (-(1 / (4 * L * (d : ℝ) ^ ξ) ^ C'))) ^ (e' / 2 + 1) :=
          pow_le_pow_left₀ hx0 (Real.one_sub_le_exp_neg _) _
      _ = Real.exp (-(((e' / 2 + 1 : ℕ) : ℝ) * (1 / (4 * L * (d : ℝ) ^ ξ) ^ C'))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-(c * (d' : ℝ) ^ (1 - s))) := Real.exp_le_exp.2 (by linarith)
      _ ≤ _ := rhs_ge _ ht0

end Constants

end TrackB
end RestrictedPolynomials
end
