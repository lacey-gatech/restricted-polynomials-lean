module

public import RestrictedPolynomials.Dimitrov.Contour
public import RestrictedPolynomials.Dimitrov.PolyaAlg
public import RestrictedPolynomials.Dimitrov.Kronecker
public import RestrictedPolynomials.Dimitrov.Fekete
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The Pólya bound and rationality for hedgehogs

Source: Supplement B, §3 and §4: Lemma `lem:Lgamma`,
Theorem `thm:polya` and Theorem `thm:CRI`.

* `polya_hankel_bound`: `‖D_N(a)‖ ≤ (N+1)! C^{N+1} ρ^{N(N+1)}`.
* `polya_hankel_eventually_zero`: for integer coefficients the Hankel determinants vanish eventually.
* `rational_of_transfiniteDiameter_lt_one`: rationality of the generating series when the
  transfinite diameter of the hedgehog is `< 1`.
-/

@[expose] public section

open Polynomial
open scoped Matrix

noncomputable section

namespace RestrictedPolynomials

namespace Polya

/-- Leibniz bound for the determinant of a matrix with entries `≤ C ρ^{i+j}`. -/
theorem norm_det_le_of_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C ρ : ℝ)
    (hA : ∀ i j : Fin n, ‖A i j‖ ≤ C * ρ ^ ((i : ℕ) + j)) :
    ‖A.det‖ ≤ n.factorial * C ^ n * ρ ^ (n * (n - 1)) := by
  rw [Matrix.det_apply']
  have hsum : ∀ σ : Equiv.Perm (Fin n), ∑ i : Fin n, ((σ i : ℕ) + (i : ℕ)) = n * (n - 1) := by
    intro σ
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i : Fin n => (i : ℕ))]
    have h := Finset.sum_range_id_mul_two n
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
    omega
  calc ‖∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ i, A (σ i) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), C ^ n * ρ ^ (n * (n - 1)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [norm_mul, norm_prod]
        have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [h1, one_mul]
        calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i : Fin n, (C * ρ ^ ((σ i : ℕ) + (i : ℕ))) :=
              by
                apply Finset.prod_le_prod₀
                · exact fun _ _ => norm_nonneg _
                · exact fun i _ => hA _ _
          _ = C ^ n * ρ ^ (n * (n - 1)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
                hsum σ, Finset.card_univ, Fintype.card_fin]
    _ = n.factorial * C ^ n * ρ ^ (n * (n - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/-- A point of norm at least `R` lies off the hedgehog when all `‖v‖ < R`. -/
theorem notMem_hedgehog_of_le_norm {V : Multiset ℂ} {R : ℝ} (hR : ∀ v ∈ V, ‖v‖ < R) {z : ℂ}
    (hz : R ≤ ‖z‖) : z ∉ hedgehog V := by
  intro h
  obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.1 h
  rw [segment_eq_image'] at hzv
  obtain ⟨t, ht, rfl⟩ := hzv
  have : ‖(0 : ℂ) + t • (v - 0)‖ ≤ ‖v‖ := by
    rw [zero_add, sub_zero, norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  linarith [hR v hv]

/-- The `ℂ`-linear functional `q ↦ (2πi)⁻¹ ∮_{|z|=R₀} F q`. -/
theorem exists_circle_functional (F : ℂ → ℂ) (R₀ : ℝ)
    (hint : ∀ q : ℂ[X], CircleIntegrable (fun z => F z * q.eval z) 0 R₀) :
    ∃ L : ℂ[X] →ₗ[ℂ] ℂ, ∀ q, L q = (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(0, R₀), F z * q.eval z :=
  ⟨{ toFun := fun q => (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(0, R₀), F z * q.eval z
     map_add' := fun p q => by
       have : (fun z => F z * (p + q).eval z) = fun z => F z * p.eval z + F z * q.eval z := by
         ext z; simp [mul_add]
       rw [this, circleIntegral.integral_add (hint p) (hint q), mul_add]
     map_smul' := fun c q => by
       have : (fun z => F z * (c • q).eval z) = fun z => c • (F z * q.eval z) := by
         ext z; simp [mul_left_comm]
       rw [this, circleIntegral.integral_smul]
       simp only [smul_eq_mul, RingHom.id_apply]
       ring }, fun _ => rfl⟩

/-- Norm bound on the loop. -/
theorem exists_loop_bound (F : ℂ → ℂ) (Γ : ℝ → ℂ) (hΓ : ContDiff ℝ 1 Γ)
    (hFc : Continuous (fun θ => F (Γ θ))) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (q : ℂ[X]) (M : ℝ), (∀ θ, ‖q.eval (Γ θ)‖ ≤ M) →
      ‖(2 * Real.pi * Complex.I)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
          F (Γ θ) * q.eval (Γ θ) * deriv Γ θ‖ ≤ Λ * M := by
  have hcont : Continuous (fun θ => F (Γ θ) * deriv Γ θ) :=
    hFc.mul (hΓ.continuous_deriv le_rfl)
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hpi := Real.pi_pos
  refine ⟨max K1 0, le_max_right _ _, fun q M hM => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h1 : ‖∫ θ in (0 : ℝ)..2 * Real.pi, F (Γ θ) * q.eval (Γ θ) * deriv Γ θ‖ ≤
      (M * max K1 0) * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    have hθ' : θ ∈ Set.Icc 0 (2 * Real.pi) := by
      rw [Set.uIoc_of_le (by positivity)] at hθ
      exact ⟨hθ.1.le, hθ.2⟩
    calc ‖F (Γ θ) * q.eval (Γ θ) * deriv Γ θ‖
        = ‖q.eval (Γ θ)‖ * ‖F (Γ θ) * deriv Γ θ‖ := by
          rw [← norm_mul]; congr 1; ring
      _ ≤ M * max K1 0 :=
          mul_le_mul (hM θ) ((hK1 θ hθ').trans (le_max_left _ _)) (norm_nonneg _) hM0
  rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi - 0)] at h1
  rw [norm_mul, norm_inv]
  have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [abs_of_pos hpi]
  rw [h2]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, F (Γ θ) * q.eval (Γ θ) * deriv Γ θ‖
      ≤ (2 * Real.pi)⁻¹ * ((M * max K1 0) * (2 * Real.pi - 0)) := by gcongr
    _ = max K1 0 * M := by field_simp; ring

end Polya

open Polya in
/-- [B, Theorem thm:polya], the bound. -/
theorem polya_hankel_bound (V : Multiset ℂ) (hV : V ≠ 0) (a : ℕ → ℂ) (F : ℂ → ℂ) {ρ₀ : ℝ}
    (hρ : 0 ≤ ρ₀) (hFd : DifferentiableOn ℂ F (hedgehog V)ᶜ)
    (hF : ∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => a k * z⁻¹ ^ k) (F z))
    (T : ℂ[X]) (hT : T.Monic) (hTdeg : 1 ≤ T.natDegree)
    (hTK : ∃ c < 1, ∀ x ∈ hedgehog V, ‖T.eval x‖ ≤ c) :
    ∃ C ≥ (1 : ℝ), ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ N : ℕ,
      ‖hankelDet a 1 (N + 1)‖ ≤ (N + 1).factorial * C ^ (N + 1) * ρ ^ (N * (N + 1)) := by
  classical
  -- radii
  obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ v ∈ V, ‖v‖ < R := by
    refine ⟨(∑ v ∈ V.toFinset, ‖v‖) + 1, ?_, fun v hv => ?_⟩
    · have : 0 ≤ ∑ v ∈ V.toFinset, ‖v‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
    · have := Finset.single_le_sum (f := fun v : ℂ => ‖v‖) (fun _ _ => norm_nonneg _)
        (Multiset.mem_toFinset.2 hv)
      linarith
  set R₀ : ℝ := max R ρ₀ + 1 with hR₀def
  have hRR₀ : R < R₀ := by have := le_max_left R ρ₀; linarith
  have hρR₀ : ρ₀ < R₀ := by have := le_max_right R ρ₀; linarith
  have hR₀pos : 0 < R₀ := by linarith
  have hcompl : IsOpen (hedgehog V)ᶜ := (isCompact_hedgehog V).isClosed.isOpen_compl
  have hFcont : ContinuousOn F (hedgehog V)ᶜ := hFd.continuousOn
  have hsph : Metric.sphere (0 : ℂ) R₀ ⊆ (hedgehog V)ᶜ := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    exact notMem_hedgehog_of_le_norm hR (by linarith)
  have hint : ∀ q : ℂ[X], CircleIntegrable (fun z => F z * q.eval z) 0 R₀ := fun q =>
    ContinuousOn.circleIntegrable hR₀pos.le
      ((hFcont.mono hsph).mul q.continuous.continuousOn)
  obtain ⟨L, hLdef⟩ := exists_circle_functional F R₀ hint
  have hL : ∀ n, L (X ^ n) = a (n + 1) := fun n => by
    rw [hLdef]
    simpa using circleIntegral_mul_pow_eq_coeff a F hρ hρR₀ hF n
  -- contour
  obtain ⟨c, hc1, hc⟩ := hTK
  set c' : ℝ := max c 0 with hc'
  set α : ℝ := (1 + c') / 2 with hαdef
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hc'1 : c' < 1 := max_lt hc1 one_pos
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hcα : c < α := by rw [hαdef]; have := le_max_left c 0; linarith
  have hO : IsOpen {z : ℂ | ‖T.eval z‖ < α} :=
    isOpen_lt (T.continuous.norm) continuous_const
  have hKO : hedgehog V ⊆ {z : ℂ | ‖T.eval z‖ < α} := fun x hx => (hc x hx).trans_lt hcα
  obtain ⟨Γ, hΓd, -, hΓmem, hΓint⟩ := exists_hedgehog_loop V hV hR hRR₀ hO hKO
  have hLΓ : ∀ q : ℂ[X], L q = (2 * Real.pi * Complex.I)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi, F (Γ θ) * q.eval (Γ θ) * deriv Γ θ := fun q => by
    rw [hLdef, hΓint (fun z => F z * q.eval z)
      ((show DifferentiableOn ℂ F (⋃ v ∈ V, segment ℝ (0 : ℂ) v)ᶜ from hFd).mul
        q.differentiable.differentiableOn)]
  have hFΓ : Continuous (fun θ => F (Γ θ)) :=
    hFcont.comp_continuous hΓd.continuous (fun θ => (hΓmem θ).2.1)
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_loop_bound F Γ hΓd hFΓ
  -- the polynomials
  set m : ℕ := T.natDegree with hm
  have hm0 : 0 < m := hTdeg
  set ρ : ℝ := α ^ (1 / (m : ℝ)) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hα0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hα0.le hα1 (by positivity)
  have hρm : ρ ^ m = α := by
    rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hα0.le]
    have : (1 / (m : ℝ)) * (m : ℝ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  set P : ℕ → ℂ[X] := fun i => X ^ (i % m) * T ^ (i / m) with hP
  have hPmonic : ∀ i, (P i).Monic ∧ (P i).natDegree = i := fun i => by
    refine ⟨(monic_X_pow _).mul (hT.pow _), ?_⟩
    rw [hP]
    simp only
    rw [(monic_X_pow _).natDegree_mul (hT.pow _), natDegree_X_pow, hT.natDegree_pow, ← hm]
    have := Nat.mod_add_div i m
    linarith
  have hPb : ∀ i θ, ‖(P i).eval (Γ θ)‖ ≤ (R / ρ) ^ (m - 1) * ρ ^ i := by
    intro i θ
    obtain ⟨hOθ, -, hRΓ⟩ := hΓmem θ
    have hTΓ : ‖T.eval (Γ θ)‖ ≤ α := (show ‖T.eval (Γ θ)‖ < α from hOθ).le
    have h1 : ‖(P i).eval (Γ θ)‖ ≤ R ^ (i % m) * ρ ^ (m * (i / m)) := by
      simp only [hP, eval_mul, eval_pow, eval_X, norm_mul, norm_pow]
      rw [pow_mul, hρm]
      gcongr
    have hr : i % m ≤ m - 1 := by have := Nat.mod_lt i hm0; omega
    have hRρ : 1 ≤ R / ρ := by rw [le_div_iff₀ hρ0]; linarith
    calc ‖(P i).eval (Γ θ)‖ ≤ R ^ (i % m) * ρ ^ (m * (i / m)) := h1
      _ = (R / ρ) ^ (i % m) * ρ ^ i := by
          have : ρ ^ i = ρ ^ (i % m) * ρ ^ (m * (i / m)) := by
            rw [← pow_add, Nat.mod_add_div]
          rw [this, div_pow]
          field_simp
      _ ≤ (R / ρ) ^ (m - 1) * ρ ^ i :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hRρ hr) (by positivity)
  set C1 : ℝ := (R / ρ) ^ (m - 1) with hC1
  have hC1pos : 0 ≤ C1 := by positivity
  set C : ℝ := max 1 (Λ * C1 ^ 2) with hCdef
  have hCentry : ∀ i j : ℕ, ‖L (P i * P j)‖ ≤ C * ρ ^ (i + j) := by
    intro i j
    rw [hLΓ]
    refine (hΛ (P i * P j) ((C1 * ρ ^ i) * (C1 * ρ ^ j)) (fun θ => ?_)).trans ?_
    · rw [eval_mul, norm_mul]
      exact mul_le_mul (hPb i θ) (hPb j θ) (norm_nonneg _) (by positivity)
    · calc Λ * ((C1 * ρ ^ i) * (C1 * ρ ^ j)) = (Λ * C1 ^ 2) * ρ ^ (i + j) := by ring
        _ ≤ C * ρ ^ (i + j) := by
          gcongr
          exact le_max_right _ _
  refine ⟨C, le_max_left _ _, ρ, hρ0, hρ1, fun N => ?_⟩
  have hdet := det_linearFunctional_monic_basis L a hL N (fun i => P i) (fun i => hPmonic i)
  rw [← hdet]
  have key := norm_det_le_of_entry_bound (Matrix.of fun i j : Fin (N + 1) => L (P i * P j)) C ρ
    (fun i j => hCentry i j)
  have e : (N + 1) * (N + 1 - 1) = N * (N + 1) := by simp [mul_comm]
  rw [e] at key
  exact key

/-- [B, Theorem thm:polya], the integer case. -/
theorem polya_hankel_eventually_zero (V : Multiset ℂ) (hV : V ≠ 0) (a : ℕ → ℤ) (F : ℂ → ℂ)
    {ρ₀ : ℝ} (hρ : 0 ≤ ρ₀) (hFd : DifferentiableOn ℂ F (hedgehog V)ᶜ)
    (hF : ∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => (a k : ℂ) * z⁻¹ ^ k) (F z))
    (T : ℂ[X]) (hT : T.Monic) (hTdeg : 1 ≤ T.natDegree)
    (hTK : ∃ c < 1, ∀ x ∈ hedgehog V, ‖T.eval x‖ ≤ c) :
    ∃ N₀, ∀ N ≥ N₀, hankelDet a 1 (N + 1) = 0 := by
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ :=
    polya_hankel_bound V hV (fun k => (a k : ℂ)) F hρ hFd hF T hT hTdeg hTK
  have hcast : ∀ N, ((hankelDet a 1 (N + 1) : ℤ) : ℂ) =
      hankelDet (fun k => (a k : ℂ)) 1 (N + 1) := fun N => by
    have := (Int.castRingHom ℂ).map_det (Matrix.of fun i j : Fin (N + 1) => a ((i : ℕ) + j + 1))
    have hmat : (Matrix.of fun i j : Fin (N + 1) => ((a ((i : ℕ) + j + 1) : ℤ) : ℂ)) =
        (Matrix.of fun i j : Fin (N + 1) => a ((i : ℕ) + j + 1)).map (Int.castRingHom ℂ) := by
      ext i j; simp
    simp only [hankelDet, hmat]
    simpa [RingHom.mapMatrix_apply] using this
  have hlim : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1) * C * ρ ^ N) Filter.atTop (nhds 0) := by
    have h := ((tendsto_self_mul_const_pow_of_lt_one hρ0.le hρ1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1)).const_mul C
    rw [add_zero, mul_zero] at h
    refine h.congr fun N => ?_
    ring
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨N₀, fun N hN => ?_⟩
  have hx := hN₀ N hN
  set x : ℝ := ((N : ℝ) + 1) * C * ρ ^ N with hxdef
  have hx0 : 0 ≤ x := by
    have : 0 ≤ C := by linarith
    positivity
  have hx1 : x < 1 := by linarith
  have hfac : ((N + 1).factorial : ℝ) ≤ ((N : ℝ) + 1) ^ (N + 1) := by
    exact_mod_cast Nat.factorial_le_pow (N + 1)
  have hbd : ‖hankelDet (fun k => (a k : ℂ)) 1 (N + 1)‖ < 1 := by
    refine (hb N).trans_lt ?_
    calc ((N + 1).factorial : ℝ) * C ^ (N + 1) * ρ ^ (N * (N + 1))
        ≤ ((N : ℝ) + 1) ^ (N + 1) * C ^ (N + 1) * ρ ^ (N * (N + 1)) := by gcongr
      _ = x ^ (N + 1) := by rw [hxdef, mul_pow, mul_pow, ← pow_mul]
      _ < 1 := pow_lt_one₀ hx0 hx1 (by omega)
  rw [← hcast, Complex.norm_intCast] at hbd
  have : |hankelDet a 1 (N + 1)| < 1 := by exact_mod_cast hbd
  exact Int.abs_lt_one_iff.1 this

/-- [B, Theorem thm:CRI] rationality, hedgehog case. -/
theorem rational_of_transfiniteDiameter_lt_one (V : Multiset ℂ) (hV : V ≠ 0)
    (hd : transfiniteDiameter (hedgehog V) < 1) (a : ℕ → ℤ) (F : ℂ → ℂ) {ρ₀ : ℝ} (hρ : 0 ≤ ρ₀)
    (hFd : DifferentiableOn ℂ F (hedgehog V)ᶜ)
    (hF : ∀ z : ℂ, ρ₀ < ‖z‖ → HasSum (fun k => (a k : ℂ) * z⁻¹ ^ k) (F z)) :
    ∃ B : ℚ[X], B.coeff 0 = 1 ∧ ∃ A : ℚ[X],
      (B : PowerSeries ℚ) * PowerSeries.mk (fun k => (a k : ℚ)) = (A : PowerSeries ℚ) := by
  obtain ⟨T, hT, hTdeg, hTK⟩ := exists_monic_lt_one_of_transfiniteDiameter_lt_one
    (isCompact_hedgehog V) (hedgehog_nonempty hV) hd
  exact kronecker_int a
    (polya_hankel_eventually_zero V hV a F hρ hFd hF T hT hTdeg hTK)

end RestrictedPolynomials
