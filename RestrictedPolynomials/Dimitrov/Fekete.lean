module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Fekete transfinite diameter

Supplement B, §1 (Definition 1.1 and Lemmas 1.2-1.8; labels
`def:fekete`, `lem:max`, `lem:mono`, `lem:monoK`, `lem:tau`, `cor:tau`).

For `m` points `z : Fin m → ℂ` the norm of the Vandermonde product is
`W_m(z) = ∏_{a<b} ‖z_a − z_b‖`; `δ_m(K) = sup_{z ∈ K^m} W_m(z)`, `d_m(K) = δ_m(K)^{2/(m(m−1))}` and
`d(K) = inf_{m ≥ 2} d_m(K)`.  We prove that Fekete tuples exist, that `d_m` is antitone, that
`d_m → d`, monotonicity in `K`, and the existence of monic polynomials `T` of degree `n` with
`sup_K ‖T‖ ≤ d_{n+1}(K)^n`.  We also record that hedgehogs are compact.

This file is the definitional source of truth for the transfinite diameter.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- The hedgehog `K(V) = ⋃_{v ∈ V} [0, v]` (README, shared definition). -/
def hedgehog (V : Multiset ℂ) : Set ℂ := ⋃ v ∈ V, segment ℝ (0 : ℂ) v

/-- `W_m(z) = ∏_{a<b} ‖z_a − z_b‖`. -/
noncomputable def vandermondeNorm {m : ℕ} (z : Fin m → ℂ) : ℝ :=
  ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2), ‖z p.1 - z p.2‖

/-- `δ_m(K) = sup_{z ∈ K^m} W_m(z)`. -/
noncomputable def feketeDelta (m : ℕ) (K : Set ℂ) : ℝ :=
  sSup (vandermondeNorm '' Set.pi Set.univ (fun _ : Fin m => K))

/-- `d_m(K) = δ_m(K)^{2/(m(m−1))}`. -/
noncomputable def feketeDiam (m : ℕ) (K : Set ℂ) : ℝ :=
  feketeDelta m K ^ ((2 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)))

/-- The Fekete transfinite diameter `d(K) = inf_{m ≥ 2} d_m(K)` (README, shared definition). -/
noncomputable def transfiniteDiameter (K : Set ℂ) : ℝ :=
  ⨅ m : {m : ℕ // 2 ≤ m}, feketeDiam m K

/-! ### Basic properties -/

lemma vandermondeNorm_nonneg {m : ℕ} (z : Fin m → ℂ) : 0 ≤ vandermondeNorm z :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

lemma continuous_vandermondeNorm (m : ℕ) :
    Continuous (vandermondeNorm : (Fin m → ℂ) → ℝ) := by
  unfold vandermondeNorm
  refine continuous_finsetProd _ fun p _ => ?_
  fun_prop

lemma isCompact_pi_fin {K : Set ℂ} (hK : IsCompact K) (m : ℕ) :
    IsCompact (Set.pi Set.univ (fun _ : Fin m => K)) :=
  isCompact_univ_pi fun _ => hK

lemma nonempty_pi_fin {K : Set ℂ} (hne : K.Nonempty) (m : ℕ) :
    (Set.pi Set.univ (fun _ : Fin m => K)).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨fun _ => x, fun _ _ => hx⟩

/-- [B, Lemma lem:max] Fekete tuples exist. -/
theorem exists_fekete_tuple {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) (m : ℕ) :
    ∃ z : Fin m → ℂ, (∀ i, z i ∈ K) ∧ vandermondeNorm z = feketeDelta m K ∧
      ∀ w : Fin m → ℂ, (∀ i, w i ∈ K) → vandermondeNorm w ≤ vandermondeNorm z := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_pi_fin hK m).exists_isMaxOn (nonempty_pi_fin hne m)
    (continuous_vandermondeNorm m).continuousOn
  have hz' : ∀ i, z i ∈ K := fun i => hz i (Set.mem_univ i)
  have hle : ∀ w : Fin m → ℂ, (∀ i, w i ∈ K) → vandermondeNorm w ≤ vandermondeNorm z :=
    fun w hw => hmax (fun i _ => hw i)
  refine ⟨z, hz', ?_, hle⟩
  have : IsGreatest (vandermondeNorm '' Set.pi Set.univ (fun _ : Fin m => K))
      (vandermondeNorm z) := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hle w fun i => hw i (Set.mem_univ i)
  exact (this.csSup_eq).symm

lemma feketeDelta_nonneg (m : ℕ) (K : Set ℂ) : 0 ≤ feketeDelta m K :=
  Real.sSup_nonneg (by rintro _ ⟨w, -, rfl⟩; exact vandermondeNorm_nonneg w)

lemma feketeDiam_nonneg (m : ℕ) (K : Set ℂ) : 0 ≤ feketeDiam m K :=
  Real.rpow_nonneg (feketeDelta_nonneg m K) _

/-! ### Ordered-pair product -/

/-- The product over all ordered pairs of distinct indices; it equals `W²`. -/
def pairProd {m : ℕ} (z : Fin m → ℂ) : ℝ :=
  ∏ c, ∏ d, if c = d then (1 : ℝ) else ‖z c - z d‖

lemma pairProd_eq_sq {m : ℕ} (z : Fin m → ℂ) : pairProd z = vandermondeNorm z ^ 2 := by
  classical
  unfold pairProd vandermondeNorm
  rw [← Finset.prod_product' (f := fun c d => if c = d then (1 : ℝ) else ‖z c - z d‖),
    Finset.univ_product_univ]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin m × Fin m))
    (fun p => p.1 < p.2)]
  have h1 : ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2),
      (if p.1 = p.2 then (1 : ℝ) else ‖z p.1 - z p.2‖) =
      ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2),
        ‖z p.1 - z p.2‖ := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have : p.1 < p.2 := (Finset.mem_filter.1 hp).2
    simp [this.ne]
  have h2 : ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => ¬ p.1 < p.2),
      (if p.1 = p.2 then (1 : ℝ) else ‖z p.1 - z p.2‖) =
      ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2),
        ‖z p.1 - z p.2‖ := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => ¬ p.1 < p.2)) (fun p => p.1 = p.2)]
    have hA : ∏ p ∈ ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => ¬ p.1 < p.2)).filter
        (fun p => p.1 = p.2), (if p.1 = p.2 then (1 : ℝ) else ‖z p.1 - z p.2‖) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      simp [(Finset.mem_filter.1 hp).2]
    rw [hA, one_mul]
    refine Finset.prod_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact lt_of_le_of_ne (not_lt.1 hp.1) (Ne.symm hp.2)
    · intro p _ q _ h
      simpa [Prod.ext_iff, and_comm] using h
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨not_lt.2 hq.le, hq.ne'⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [hp.2, norm_sub_rev]
  rw [h1, h2, sq]

lemma pairProd_nonneg {m : ℕ} (z : Fin m → ℂ) : 0 ≤ pairProd z := by
  rw [pairProd_eq_sq]; positivity

/-- Splitting off the index `k` from `pairProd`. -/
lemma pairProd_split {n : ℕ} (u : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    pairProd u = pairProd (u ∘ k.succAbove) * (∏ b, ‖u k - u (k.succAbove b)‖) ^ 2 := by
  unfold pairProd
  rw [Fin.prod_univ_succAbove _ k]
  simp only [Fin.prod_univ_succAbove _ k, ite_true, one_mul, Finset.prod_mul_distrib,
    Fin.succAbove_ne, ite_false, Function.comp_apply, Fin.succAbove_right_inj,
    (Fin.succAbove_ne k _).symm]
  have h : ∏ x : Fin n, ‖u (k.succAbove x) - u k‖ = ∏ b, ‖u k - u (k.succAbove b)‖ :=
    Finset.prod_congr rfl fun _ _ => norm_sub_rev _ _
  rw [h]
  ring

lemma prod_succAbove_eq_prod_ite {M : Type*} [CommMonoid M] {n : ℕ} (g : Fin (n + 1) → M)
    (k : Fin (n + 1)) : ∏ a : Fin n, g (k.succAbove a) = ∏ c, if c = k then 1 else g c := by
  rw [Fin.prod_univ_succAbove _ k]
  simp [Fin.succAbove_ne]

lemma card_filter_ne_two {n : ℕ} {c d : Fin (n + 2)} (h : c ≠ d) :
    (Finset.univ.filter (fun k : Fin (n + 2) => ¬ (c = k ∨ d = k))).card = n := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2)))) (fun k : Fin (n + 2) => c = k ∨ d = k)
  have h2 : (Finset.univ.filter (fun k : Fin (n + 2) => c = k ∨ d = k)) = {c, d} := by
    ext k; simp [eq_comm]
  rw [h2, Finset.card_pair h] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- The pair-counting identity: each unordered pair lies in `n` of the `n + 2` sub-tuples. -/
lemma pairProd_pow_eq_prod {n : ℕ} (z : Fin (n + 2) → ℂ) :
    pairProd z ^ n = ∏ k : Fin (n + 2), pairProd (z ∘ Fin.succAbove k) := by
  set g : Fin (n + 2) → Fin (n + 2) → ℝ := fun c d => if c = d then (1 : ℝ) else ‖z c - z d‖
    with hg
  have h1 : ∀ k : Fin (n + 2), pairProd (z ∘ Fin.succAbove k) =
      ∏ c, ∏ d, if (c = k ∨ d = k) then (1 : ℝ) else g c d := by
    intro k
    unfold pairProd
    have e1 : ∀ a : Fin (n + 1), ∏ b : Fin (n + 1), (if a = b then (1 : ℝ) else
        ‖(z ∘ k.succAbove) a - (z ∘ k.succAbove) b‖) =
        ∏ d, if d = k then (1 : ℝ) else g (k.succAbove a) d := by
      intro a
      rw [← prod_succAbove_eq_prod_ite (fun d => g (k.succAbove a) d) k]
      simp [hg]
    simp_rw [e1]
    rw [prod_succAbove_eq_prod_ite (fun c => ∏ d, if d = k then (1 : ℝ) else g c d) k]
    refine Finset.prod_congr rfl fun c _ => ?_
    by_cases hc : c = k
    · simp [hc]
    · simp [hc]
  simp_rw [h1]
  rw [Finset.prod_comm]
  have h3 : ∀ c : Fin (n + 2), ∏ k : Fin (n + 2), ∏ d : Fin (n + 2),
      (if (c = k ∨ d = k) then (1 : ℝ) else g c d) = ∏ d : Fin (n + 2), g c d ^ n := by
    intro c
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun d _ => ?_
    by_cases hcd : c = d
    · subst hcd
      simp [hg]
    · rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
      rw [card_filter_ne_two hcd]
  rw [Finset.prod_congr rfl fun c _ => h3 c]
  unfold pairProd
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← Finset.prod_pow]

lemma vandermondeNorm_le_feketeDelta {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {m : ℕ}
    {w : Fin m → ℂ} (hw : ∀ i, w i ∈ K) : vandermondeNorm w ≤ feketeDelta m K := by
  obtain ⟨z, -, hz, hmax⟩ := exists_fekete_tuple hK hne m
  exact hz ▸ hmax w hw

/-- `δ_{m+1}^{m-1} ≤ δ_m^{m+1}`, written with `m = n + 2`. -/
lemma feketeDelta_pow_le {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) (n : ℕ) :
    feketeDelta (n + 3) K ^ (n + 1) ≤ feketeDelta (n + 2) K ^ (n + 3) := by
  obtain ⟨z, hzK, hz, -⟩ := exists_fekete_tuple hK hne (n + 3)
  have h1 : (vandermondeNorm z ^ (n + 1)) ^ 2 =
      ∏ k : Fin (n + 3), vandermondeNorm (z ∘ Fin.succAbove k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, ← pairProd_eq_sq, pairProd_pow_eq_prod (n := n + 1) z]
    exact Finset.prod_congr rfl fun k _ => pairProd_eq_sq _
  have h2 : ∏ k : Fin (n + 3), vandermondeNorm (z ∘ Fin.succAbove k) ^ 2 ≤
      ∏ k : Fin (n + 3), feketeDelta (n + 2) K ^ 2 := by
    refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
    exact pow_le_pow_left₀ (vandermondeNorm_nonneg _)
      (vandermondeNorm_le_feketeDelta hK hne fun i => hzK _) 2
  have h3 : (feketeDelta (n + 3) K ^ (n + 1)) ^ 2 ≤ (feketeDelta (n + 2) K ^ (n + 3)) ^ 2 := by
    rw [← hz]
    calc (vandermondeNorm z ^ (n + 1)) ^ 2 ≤ _ := h1.le.trans h2
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul,
          mul_comm]
  exact (pow_le_pow_iff_left₀ (pow_nonneg (feketeDelta_nonneg _ _) _)
    (pow_nonneg (feketeDelta_nonneg _ _) _) two_ne_zero).1 h3

/-- [B, Lemma lem:mono] `d_{m+1} ≤ d_m`. -/
theorem feketeDiam_succ_le {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {m : ℕ} (hm : 2 ≤ m) :
    feketeDiam (m + 1) K ≤ feketeDiam m K := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have h := feketeDelta_pow_le hK hne n
  set e : ℝ := 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) with he
  have he0 : 0 ≤ e := by positivity
  have h2 := Real.rpow_le_rpow (pow_nonneg (feketeDelta_nonneg _ _) _) h he0
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (feketeDelta (n + 2) K), ← Real.rpow_mul
    (feketeDelta_nonneg _ _), ← Real.rpow_mul (feketeDelta_nonneg _ _)] at h2
  have e1 : ((n + 1 : ℕ) : ℝ) * e =
      2 / (((n + 2 + 1 : ℕ) : ℝ) * (((n + 2 + 1 : ℕ) : ℝ) - 1)) := by
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
    have h4 : (n : ℝ) + 2 + 1 - 1 = n + 2 := by ring
    rw [he]; push_cast; rw [h4]; field_simp; ring
  have e2 : ((n + 3 : ℕ) : ℝ) * e =
      2 / (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) := by
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
    have h4 : (n : ℝ) + 2 - 1 = n + 1 := by ring
    rw [he]; push_cast; rw [h4]; field_simp
  rw [e1, e2] at h2
  exact h2

instance : Nonempty {m : ℕ // 2 ≤ m} := ⟨⟨2, le_rfl⟩⟩

lemma bddBelow_feketeDiam (K : Set ℂ) :
    BddBelow (Set.range fun m : {m : ℕ // 2 ≤ m} => feketeDiam m K) :=
  ⟨0, by rintro _ ⟨m, rfl⟩; exact feketeDiam_nonneg _ _⟩

/-- [B, Lemma lem:mono] `d = lim d_m`. -/
theorem tendsto_feketeDiam {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) :
    Filter.Tendsto (fun m => feketeDiam m K) Filter.atTop (nhds (transfiniteDiameter K)) := by
  let f : ℕ → ℝ := fun n => feketeDiam (n + 2) K
  have hanti : Antitone f :=
    antitone_nat_of_succ_le fun n => feketeDiam_succ_le hK hne (m := n + 2) (by omega)
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨n, rfl⟩; exact feketeDiam_nonneg _ _⟩
  have ht := tendsto_atTop_ciInf hanti hbdd
  let e : ℕ ≃ {m : ℕ // 2 ≤ m} :=
    { toFun := fun n => ⟨n + 2, by omega⟩
      invFun := fun m => m.1 - 2
      left_inv := fun n => by simp
      right_inv := fun m => by ext; simp; omega }
  have hinf : (⨅ n, f n) = transfiniteDiameter K := by
    unfold transfiniteDiameter
    rw [← Equiv.iInf_comp e]
    rfl
  rw [hinf] at ht
  exact (Filter.tendsto_add_atTop_iff_nat 2).1 ht

lemma feketeDelta_mono {K L : Set ℂ} (hL : IsCompact L) (hKne : K.Nonempty) (hKL : K ⊆ L) (m : ℕ) :
    feketeDelta m K ≤ feketeDelta m L := by
  apply csSup_le_csSup
  · exact ((isCompact_pi_fin hL m).image (continuous_vandermondeNorm m)).bddAbove
  · exact (nonempty_pi_fin hKne m).image _
  · exact Set.image_mono fun w hw i hi => hKL (hw i hi)

/-- [B, Lemma lem:monoK] monotonicity in `K`. -/
theorem transfiniteDiameter_mono {K L : Set ℂ} (hL : IsCompact L) (hKne : K.Nonempty)
    (hKL : K ⊆ L) : transfiniteDiameter K ≤ transfiniteDiameter L := by
  unfold transfiniteDiameter
  refine ciInf_mono (bddBelow_feketeDiam K) fun m => ?_
  unfold feketeDiam
  refine Real.rpow_le_rpow (feketeDelta_nonneg _ _) (feketeDelta_mono hL hKne hKL _) ?_
  have : (0 : ℝ) ≤ (m.1 : ℝ) * ((m.1 : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by have : (2 : ℝ) ≤ m.1 := by exact_mod_cast m.2
                                       linarith)
  positivity

/-! ### Hedgehogs -/

/-- Hedgehogs are compact. -/
theorem isCompact_hedgehog (V : Multiset ℂ) : IsCompact (hedgehog V) := by
  classical
  have : hedgehog V = ⋃ v ∈ V.toFinset, segment ℝ (0 : ℂ) v := by
    ext x; simp [hedgehog]
  rw [this]
  refine V.toFinset.isCompact_biUnion fun v _ => ?_
  rw [segment_eq_image']
  exact (isCompact_Icc).image (by fun_prop)

/-- Hedgehogs are nonempty when `V ≠ 0`. -/
theorem hedgehog_nonempty {V : Multiset ℂ} (hV : V ≠ 0) : (hedgehog V).Nonempty := by
  obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hV
  exact ⟨0, Set.mem_iUnion₂.2 ⟨v, hv, left_mem_segment ℝ _ _⟩⟩

/-! ### Fekete polynomials -/

/-- Degenerate case of Lemma 1.7: if `δ_{n+1}(K) = 0` then `K` has at most `n` points. -/
lemma exists_monic_eval_eq_zero_of_feketeDelta_eq_zero {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) {n : ℕ} (h0 : feketeDelta (n + 1) K = 0) :
    ∃ T : ℂ[X], T.Monic ∧ T.natDegree = n ∧ ∀ x ∈ K, T.eval x = 0 := by
  classical
  have hF : ∃ F : Finset ℂ, F.card ≤ n ∧ K ⊆ ↑F := by
    by_contra hcon
    push Not at hcon
    have hbuild : ∀ j, j ≤ n + 1 → ∃ F : Finset ℂ, ↑F ⊆ K ∧ F.card = j := by
      intro j
      induction j with
      | zero => intro _; exact ⟨∅, by simp, rfl⟩
      | succ j ih =>
        intro hj
        obtain ⟨F, hFK, hFc⟩ := ih (by omega)
        obtain ⟨x, hxK, hxF⟩ := Set.not_subset.1 (hcon F (by omega))
        refine ⟨insert x F, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hxK
          · exact hFK hy
        · rw [Finset.card_insert_of_notMem (by simpa using hxF), hFc]
    obtain ⟨F, hFK, hFc⟩ := hbuild (n + 1) le_rfl
    let e := Finset.equivFinOfCardEq hFc
    let z : Fin (n + 1) → ℂ := fun i => ((e.symm i : F) : ℂ)
    have hzinj : Function.Injective z := fun a b hab =>
      e.symm.injective (Subtype.ext hab)
    have hpos : 0 < vandermondeNorm z := by
      refine Finset.prod_pos fun p hp => ?_
      have hlt : p.1 < p.2 := (Finset.mem_filter.1 hp).2
      exact norm_pos_iff.2 (sub_ne_zero.2 fun h => hlt.ne (hzinj h))
    have := vandermondeNorm_le_feketeDelta hK hne (m := n + 1) (w := z)
      fun i => hFK (e.symm i).2
    linarith
  obtain ⟨F, hFc, hKF⟩ := hF
  refine ⟨X ^ (n - F.card) * ∏ x ∈ F, (X - C x), ?_, ?_, ?_⟩
  · exact (monic_X_pow _).mul (monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x)
  · rw [natDegree_mul (pow_ne_zero _ X_ne_zero)
      (monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero, natDegree_X_pow,
      natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C x]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  · intro x hx
    rw [eval_mul, eval_prod]
    have : ∏ a ∈ F, (X - C a).eval x = 0 :=
      Finset.prod_eq_zero (hKF hx) (by simp)
    rw [this, mul_zero]

/-- The product of the distances from the `k`-th point of a tuple to the others. -/
lemma prod_dist_eq_prod_ite {n : ℕ} (z : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    ∏ b : Fin n, ‖z k - z (k.succAbove b)‖ =
      ∏ d, if k = d then (1 : ℝ) else ‖z k - z d‖ := by
  rw [Fin.prod_univ_succAbove _ k]
  simp [(Fin.succAbove_ne k _).symm]

lemma prod_dist_eq_pairProd {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ∏ k, ∏ b : Fin n, ‖z k - z (k.succAbove b)‖ = pairProd z := by
  unfold pairProd
  exact Finset.prod_congr rfl fun k _ => prod_dist_eq_prod_ite z k

/-- The replace-one-entry estimate. -/
lemma norm_prod_le_of_fekete {K : Set ℂ} {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hzK : ∀ i, z i ∈ K) (hmax : ∀ w : Fin (n + 1) → ℂ, (∀ i, w i ∈ K) →
      vandermondeNorm w ≤ vandermondeNorm z)
    (hpos : 0 < pairProd z) (k : Fin (n + 1)) {x : ℂ} (hx : x ∈ K) :
    ∏ b : Fin n, ‖x - z (k.succAbove b)‖ ≤ ∏ b : Fin n, ‖z k - z (k.succAbove b)‖ := by
  set w : Fin (n + 1) → ℂ := Function.update z k x with hw
  have hwK : ∀ i, w i ∈ K := by
    intro i
    by_cases hi : i = k
    · subst hi; simpa [hw] using hx
    · simpa [hw, hi] using hzK i
  have hwc : w ∘ k.succAbove = z ∘ k.succAbove := by
    funext b; simp [hw, Fin.succAbove_ne]
  have hs1 := pairProd_split w k
  have hs2 := pairProd_split z k
  rw [hwc] at hs1
  have hwk : w k = x := by simp [hw]
  have hwb : ∀ b, w (k.succAbove b) = z (k.succAbove b) := fun b => by
    simp [hw, Fin.succAbove_ne]
  simp only [hwk, hwb] at hs1
  have hle : pairProd w ≤ pairProd z := by
    rw [pairProd_eq_sq, pairProd_eq_sq]
    exact pow_le_pow_left₀ (vandermondeNorm_nonneg _) (hmax w hwK) 2
  have hA : 0 < pairProd (z ∘ k.succAbove) := by
    refine lt_of_le_of_ne (pairProd_nonneg _) fun h => ?_
    rw [hs2, ← h, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [hs1, hs2] at hle
  have := le_of_mul_le_mul_left hle hA
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) two_ne_zero).1 this

/-- [B, Lemma lem:tau] `τ ≤ d`: a monic Fekete polynomial. -/
theorem exists_monic_le_feketeDiam_pow {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ T : ℂ[X], T.Monic ∧ T.natDegree = n ∧ ∀ x ∈ K, ‖T.eval x‖ ≤ feketeDiam (n + 1) K ^ n := by
  have hδ0 := feketeDelta_nonneg (n + 1) K
  have hdiam0 : 0 ≤ feketeDiam (n + 1) K ^ n := pow_nonneg (feketeDiam_nonneg _ _) _
  rcases hδ0.eq_or_lt with h0 | hpos
  · obtain ⟨T, hT, hdeg, hev⟩ :=
      exists_monic_eval_eq_zero_of_feketeDelta_eq_zero hK hne h0.symm
    exact ⟨T, hT, hdeg, fun x hx => by rw [hev x hx, norm_zero]; exact hdiam0⟩
  · obtain ⟨z, hzK, hz, hmax⟩ := exists_fekete_tuple hK hne (n + 1)
    have hpp : 0 < pairProd z := by rw [pairProd_eq_sq, hz]; positivity
    set c : ℝ := feketeDelta (n + 1) K ^ ((2 : ℝ) / ((n : ℝ) + 1)) with hc
    have hcpos : 0 < c := Real.rpow_pos_of_pos hpos _
    have hcpow : c ^ (n + 1) = feketeDelta (n + 1) K ^ 2 := by
      rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hδ0]
      have : (2 : ℝ) / ((n : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) = (2 : ℕ) := by
        push_cast; field_simp
      rw [this, Real.rpow_natCast]
    have hex : ∃ k : Fin (n + 1), ∏ b : Fin n, ‖z k - z (k.succAbove b)‖ ≤ c := by
      by_contra hcon
      push Not at hcon
      have hlt := Finset.prod_lt_prod_of_nonempty₀ (s := (Finset.univ : Finset (Fin (n + 1))))
        (f := fun _ => c) (g := fun k => ∏ b : Fin n, ‖z k - z (k.succAbove b)‖)
        (fun _ _ => hcpos) (fun k _ => hcon k) Finset.univ_nonempty
      rw [prod_dist_eq_pairProd, pairProd_eq_sq, hz, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hcpow] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨k, hk⟩ := hex
    refine ⟨∏ b : Fin n, (X - C (z (k.succAbove b))), ?_, ?_, ?_⟩
    · exact monic_prod_of_monic _ _ fun b _ => monic_X_sub_C _
    · rw [natDegree_prod_of_monic _ _ fun b _ => monic_X_sub_C _]
      simp
    · intro x hx
      have hcd : c = feketeDiam (n + 1) K ^ n := by
        rw [hc]
        unfold feketeDiam
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0]
        congr 1
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        push_cast
        rw [add_sub_cancel_right]
        field_simp
      rw [← hcd]
      refine le_trans ?_ hk
      rw [eval_prod, norm_prod]
      simpa using norm_prod_le_of_fekete hzK hmax hpp k hx

/-- [B, Corollary cor:tau (b)] -/
theorem exists_monic_lt_one_of_transfiniteDiameter_lt_one {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) (hd : transfiniteDiameter K < 1) :
    ∃ T : ℂ[X], T.Monic ∧ 1 ≤ T.natDegree ∧ ∃ c < 1, ∀ x ∈ K, ‖T.eval x‖ ≤ c := by
  obtain ⟨⟨m, hm⟩, hlt⟩ := exists_lt_of_ciInf_lt (f := fun m : {m : ℕ // 2 ≤ m} =>
    feketeDiam m K) hd
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨T, hT, hdeg, hbound⟩ := exists_monic_le_feketeDiam_pow hK hne (n := n) (by omega)
  refine ⟨T, hT, by omega, feketeDiam (n + 1) K ^ n, ?_, hbound⟩
  exact pow_lt_one₀ (feketeDiam_nonneg _ _) hlt (by omega)
