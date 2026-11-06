module

public import RestrictedPolynomials.TrackB.K7KcspMatrix
public import RestrictedPolynomials.TrackB.K7KcspArith
public import RestrictedPolynomials.TrackB.Restrict
public import RestrictedPolynomials.TrackB.StabComplex
public import RestrictedPolynomials.TrackB.MergeLayer
public import RestrictedPolynomials.TrackB.Embedding
public import RestrictedPolynomials.Frozen.NoNontrivialAbelianEmbeddingPi
public import RestrictedPolynomials.Frozen.FinProbMarginalPi
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Defs
public import RestrictedPolynomials.TrackB.K7KcspUnif

/-!
# Track B, `K7KcspReduce`: the two-law identity and the reduction to `Unif(supp μ)`

Source: Supplement H, section
`sec:psd`: `lem:two-law` (l. 304-313) and `prop:reduce` (l. 347-368, with the explicit stability
chain in Step 4); section `sec:constants`: `cor:tower` (l. 380-389). The `Unif` material is in
`K7KcspUnif`.

Proof routes.
* `k7_stab_eq_kron`: `cstab_eq_joint` and `k7_TMat_eq_jointNoise`; the expectation of
  `g(x) conj g(x')` under a product pair law is the plain-pairing form of its Kronecker power.
* `k7_two_law_stab`: `mixture_calculus` on the alphabet `A × A` for the law
  `Q_d = (1-λ) Δ(μ'') + λ J^{π̂}_{1-d}` (`Δ(μ'') = jointNoise μ'' 1`, `joint_one_diag`), as in the
  single-law `stab_eq_expect_restriction`.
* `k7_reduce_to_unifSupp`: Step 1 is `mixture_calculus` on `∏ A_i` with the junk law `μ''` of
  `k7_unifSupp_decomp`; Steps 1-2 (Markov and averaging) are done in one go through the pointwise
  affine bound `d (|c| - ε/2) ≤ Re Stab` (`hhat` on the good event, `cstab_nonneg` off it); Step 3 is
  `k7_two_law_stab` (after pushing `w ↦ w^{(i)}` forward to the marginal), `k7_loewner_Q_le_T`
  with `k7_var_compare` and `k7_unif_marginal_counts`, `k7_kron_form_mono` and `k7_stab_eq_kron`;
  Step 4 is `cstab_mono`. No threshold on `|ι|`: `hhat` is applied at the index type `↥Kᶜ` of every
  size, including `Kᶜ = ∅`.
* `k7_tower_reduce`: `k7_reduce_to_unifSupp` at `ε/2`, `k7_absorb_half` and the lowering
  `k7_valid_mono`, re-proved privately (`k7rd_valid_mono`) so that this file does not import
  `K7KcspAssembly`.

Private helpers carry the prefix `k7rd_`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

/-! ### Private helpers: expectations -/

section ExpectAux

/-- the real part of an expectation is the expectation of the real part. -/
private theorem k7rd_re_cexpect {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) :
    (P.cexpect f).re = ∑ k, P.prob k * (f k).re := by
  unfold FinProb.cexpect
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => Complex.re_ofReal_mul _ _

/-- an affine lower bound on real parts passes through an expectation. -/
private theorem k7rd_affine_le {κ : Type} [Fintype κ] (P : FinProb κ) (f g : κ → ℂ) (a b : ℝ)
    (h : ∀ k, a * (f k).re + b ≤ (g k).re) : a * (P.cexpect f).re + b ≤ (P.cexpect g).re := by
  rw [k7rd_re_cexpect, k7rd_re_cexpect]
  have e1 : ∑ k, P.prob k * (a * (f k).re + b) =
      a * ∑ k, P.prob k * (f k).re + b * ∑ k, P.prob k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [P.sum_eq_one, mul_one] at e1
  rw [← e1]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (P.nonneg k)

/-- the triangle inequality for an expectation. -/
private theorem k7rd_norm_cexpect_le {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ) :
    ‖P.cexpect f‖ ≤ (P.cexpect fun k => ((‖f k‖ : ℝ) : ℂ)).re := by
  rw [k7rd_re_cexpect]
  unfold FinProb.cexpect
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P.nonneg k), Complex.ofReal_re]

/-- an expectation of a `1`-bounded function is `1`-bounded. -/
private theorem k7rd_norm_cexpect_le_one {κ : Type} [Fintype κ] (P : FinProb κ) (f : κ → ℂ)
    (hf : ∀ k, ‖f k‖ ≤ 1) : ‖P.cexpect f‖ ≤ 1 := by
  unfold FinProb.cexpect
  calc ‖∑ k, (P.prob k : ℂ) * f k‖ ≤ ∑ k, ‖(P.prob k : ℂ) * f k‖ := norm_sum_le _ _
    _ ≤ ∑ k, P.prob k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P.nonneg k)]
        exact mul_le_of_le_one_right (P.nonneg k) (hf k)
    _ = 1 := P.sum_eq_one

/-- Steps 1-2 of `prop:reduce` (Markov and averaging), in affine form: if the restricted
correlations `C(K, w)` are `1`-bounded with average modulus `≥ ε`, and `Re S(K, w) ≥ 0` always and
`≥ d` whenever `|C(K, w)| ≥ ε/2`, then `Re 𝔼_{K,w} S ≥ d ε/2`. -/
private theorem k7rd_avg {β : Type} [Fintype β] [DecidableEq β] {ι : Type} [Fintype ι]
    [DecidableEq ι] {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (ν : FinProb β)
    (C S : (K : Finset ι) → (↥K → β) → ℂ) {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hC1 : ∀ K w, ‖C K w‖ ≤ 1)
    (hgood : ∀ K w, ε / 2 ≤ ‖C K w‖ → d ≤ (S K w).re)
    (hS0 : ∀ K w, 0 ≤ (S K w).re)
    (hcorr : ε ≤ ‖subsetExpect q h0 h1 fun K => (ν.pi ↥K).cexpect (C K)‖) :
    d * (ε / 2) ≤ (subsetExpect q h0 h1 fun K => (ν.pi ↥K).cexpect (S K)).re := by
  unfold subsetExpect at hcorr ⊢
  -- the pointwise affine bound `d |C| - d ε/2 ≤ Re S`
  have hpt : ∀ K w, d * (((‖C K w‖ : ℝ) : ℂ)).re + -(d * (ε / 2)) ≤ (S K w).re := by
    intro K w
    rw [Complex.ofReal_re]
    by_cases hc : ε / 2 ≤ ‖C K w‖
    · have h := hgood K w hc
      have hb := mul_le_mul_of_nonneg_left (hC1 K w) hd
      nlinarith [mul_nonneg hd hε]
    · push Not at hc
      have h := hS0 K w
      nlinarith [mul_le_mul_of_nonneg_left hc.le hd]
  have h2 : ∀ K : Finset ι, d * ((ν.pi ↥K).cexpect fun w => ((‖C K w‖ : ℝ) : ℂ)).re +
      -(d * (ε / 2)) ≤ ((ν.pi ↥K).cexpect (S K)).re :=
    fun K => k7rd_affine_le _ _ _ d _ (hpt K)
  have h3 := k7rd_affine_le ((bernoulli q h0 h1).pi ι) _ _ d _ fun s => h2 (trueSet s)
  -- the triangle inequality at both levels
  have hn1 := k7rd_norm_cexpect_le ((bernoulli q h0 h1).pi ι)
    fun s => (ν.pi ↥(trueSet s)).cexpect (C (trueSet s))
  have hn2 := k7rd_affine_le ((bernoulli q h0 h1).pi ι)
    (fun s => ((‖(ν.pi ↥(trueSet s)).cexpect (C (trueSet s))‖ : ℝ) : ℂ))
    (fun s => (ν.pi ↥(trueSet s)).cexpect fun w => ((‖C (trueSet s) w‖ : ℝ) : ℂ)) 1 0
    fun s => by
      rw [Complex.ofReal_re, one_mul, add_zero]
      exact k7rd_norm_cexpect_le _ _
  rw [one_mul, add_zero] at hn2
  have hE := hcorr.trans (hn1.trans hn2)
  nlinarith [mul_le_mul_of_nonneg_left hE hd]

end ExpectAux

/-! ### Private helpers: pair laws, marginals and stability -/

section PairAux
variable {A : Type} [Fintype A] [DecidableEq A] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq A] in
/-- the expectation of `g(x) conj g(x')` under a product pair law is the plain-pairing form of the
Kronecker power of the pair law. -/
private theorem k7rd_pair_cexpect_eq_qform (P : FinProb (A × A)) (M : Matrix A A ℂ)
    (hM : ∀ a a', M a a' = ((P.prob (a, a') : ℝ) : ℂ)) (g : (ι → A) → ℂ) :
    (P.pi ι).cexpect (fun p => g (fun i => (p i).1) * star (g (fun i => (p i).2))) =
      k7QForm (k7KronPow M ι) g := by
  let e : (ι → A × A) ≃ (ι → A) × (ι → A) :=
    Equiv.arrowProdEquivProdArrow ι (fun _ => A) (fun _ => A)
  unfold FinProb.cexpect k7QForm
  rw [← Fintype.sum_equiv e.symm (fun q : (ι → A) × (ι → A) => (((P.pi ι).prob (e.symm q) : ℝ) : ℂ) *
      (g q.1 * star (g q.2))) _ (fun q => by simp [e]), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  congr 1
  simp only [k7KronPow, Matrix.of_apply, hM, FinProb.pi, e]
  push_cast
  rfl

/-- the law `Q_d = (1-λ) Δ(μ'') + λ J^{π̂}_{1-d}` on `A × A` (`Δ(μ'') = jointNoise μ'' 1`). -/
private def k7rdQLaw (lam : ℝ) (πh μ2 : FinProb A) (d : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) : FinProb (A × A) where
  prob p := (1 - lam) * (jointNoise μ2 1 zero_le_one le_rfl).prob p +
    lam * (jointNoise πh (1 - d) (by linarith) (by linarith)).prob p
  nonneg p := add_nonneg (mul_nonneg (by linarith) (FinProb.nonneg _ _))
    (mul_nonneg hlam0 (FinProb.nonneg _ _))
  sum_eq_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FinProb.sum_eq_one,
      FinProb.sum_eq_one]
    ring

/-- the `i`-th letters of a glued point are the glued `i`-th letters. -/
private theorem k7rd_glue_comp {m : ℕ} {B : Fin m → Type} (I : Finset ι) (z : ↥I → ∀ j, B j)
    (Y : ↥Iᶜ → ∀ j, B j) (j : Fin m) :
    (fun t => glueFix I z Y t j) = glueFix I (fun t => z t j) (fun t => Y t j) := by
  funext t
  unfold glueFix
  split_ifs <;> rfl

end PairAux

section MargAux
variable {m : ℕ} {B : Fin m → Type} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]

/-- the mass of a fibre `{X | X·j = x}` is the mass of `x` under `μ_j^{⊗κ}`. -/
private theorem k7rd_fibre_mass (μ : FinProb (∀ j, B j)) (j : Fin m) {κ : Type} [Fintype κ]
    [DecidableEq κ] (x : κ → B j) :
    ∑ X : κ → ∀ i, B i, (if (fun t => X t j) = x then (μ.pi κ).prob X else 0) =
      ((μ.marginalPi j).pi κ).prob x := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ.filter fun X : κ → ∀ i, B i => (fun t => X t j) = x) =
      Fintype.piFinset fun t => Finset.univ.filter fun y : ∀ i, B i => y j = x t := by
    ext X
    simp [Fintype.mem_piFinset, funext_iff]
  rw [h]
  simp only [FinProb.pi, FinProb.marginalPi]
  rw [Finset.prod_univ_sum]

/-- the expectation of a function of one coordinate is an expectation under the marginal. -/
private theorem k7rd_cexpect_marginal (μ : FinProb (∀ j, B j)) (j : Fin m) {κ : Type}
    [Fintype κ] [DecidableEq κ] (G : (κ → B j) → ℂ) :
    (μ.pi κ).cexpect (fun X => G (fun t => X t j)) = ((μ.marginalPi j).pi κ).cexpect G := by
  unfold FinProb.cexpect
  have h : ∀ X : κ → ∀ i, B i, ((μ.pi κ).prob X : ℂ) * G (fun t => X t j) =
      ∑ x, (if (fun t => X t j) = x then ((μ.pi κ).prob X : ℂ) else 0) * G x := by
    intro X
    rw [Finset.sum_eq_single (fun t => X t j)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  rw [Finset.sum_congr rfl fun X _ => h X, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [← k7rd_fibre_mass μ j x]
  push_cast
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs <;> simp

end MargAux

section StabAux
open scoped ComplexOrder
variable {B : Type} [Fintype B] [DecidableEq B] {κ : Type} [Fintype κ] [DecidableEq κ]

/-- `Re Stab_ρ ≥ 0` for `ρ ≥ 0` (`cstab_nonneg`). -/
private theorem k7rd_re_cstab_nonneg (π : FinProb B) {ρ : ℝ} (h0 : 0 ≤ ρ) (g : (κ → B) → ℂ) :
    0 ≤ (cstab π ρ g).re := by
  have h := (Complex.le_def.1 (cstab_nonneg π h0 g)).1
  simpa using h

/-- `Re Stab_ρ` is nondecreasing in `ρ ≥ 0` (`cstab_mono`). -/
private theorem k7rd_re_cstab_mono (π : FinProb B) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ')
    (g : (κ → B) → ℂ) : (cstab π ρ g).re ≤ (cstab π ρ' g).re :=
  (Complex.le_def.1 (cstab_mono π h0 h g)).1

/-- the lowering `k7_valid_mono` of `K7KcspAssembly`, re-proved here: a valid `δ` stays valid when
lowered (`Stab_{1-δ''} ≥ Stab_{1-δ} ≥ δ ≥ δ''`). -/
private theorem k7rd_valid_mono (π : FinProb B) (f : (κ → B) → ℂ) {δ δ'' : ℝ}
    (hδ : δ'' ≤ δ) (hδ1 : δ ≤ 1) (h : δ ≤ (cstab π (1 - δ) f).re) :
    δ'' ≤ (cstab π (1 - δ'') f).re := by
  have hm := k7rd_re_cstab_mono π (by linarith : 0 ≤ 1 - δ) (by linarith : 1 - δ ≤ 1 - δ'') f
  linarith

end StabAux

section LoewnerAux
open scoped ComplexOrder MatrixOrder
variable {A : Type} [Fintype A] [DecidableEq A] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `prop:loewner` and `lem:kron` combined: `⟨g, Q_d^{⊗ι} g⟩ ≤ ⟨g, (T'_{αd})^{⊗ι} g⟩`. -/
private theorem k7rd_form_le (μ πh μ2 : FinProb A) {α N lam d : ℝ} (hα0 : 0 < α)
    (hlam : lam = α * N) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hmix : ∀ a, μ.prob a = lam * πh.prob a + (1 - lam) * μ2.prob a)
    (hvar : ∀ g : A → ℂ, k7Var μ g ≤ N * k7Var πh g) (g : (ι → A) → ℂ) :
    (k7QForm (k7KronPow (k7QMat lam πh μ2 d) ι) g).re ≤
      (k7QForm (k7KronPow (k7TMat μ (α * d)) ι) g).re := by
  obtain ⟨h0, h1⟩ := k7_loewner_Q_le_T μ πh μ2 hα0 hlam hlam0 hlam1 hd0 hd1 hmix hvar
  have hY : (k7QMat lam πh μ2 d).PosSemidef := Matrix.nonneg_iff_posSemidef.1 h0
  have hXY : (k7TMat μ (α * d) - k7QMat lam πh μ2 d).PosSemidef := Matrix.le_iff.1 h1
  exact k7_kron_form_mono _ _ hY hXY g

end LoewnerAux

section TwoLaw
variable {A : Type} [Fintype A] [DecidableEq A] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `T'_c` form is the stability: `Stab^π_{1-c}(g) = ⟨g, (T'_c)^{⊗ι} g⟩` (`cstab_eq_joint`). -/
theorem k7_stab_eq_kron (π : FinProb A) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (g : (ι → A) → ℂ) :
    cstab π (1 - c) g = k7QForm (k7KronPow (k7TMat π c) ι) g := by
  rw [cstab_eq_joint π (1 - c) (by linarith) (by linarith) g]
  exact k7rd_pair_cexpect_eq_qform _ _ (fun a a' => k7_TMat_eq_jointNoise π hc0 hc1 a a') g

/-- `lem:two-law` (the new two-law stability identity): `𝔼_{K ∼_{1-λ} ι} 𝔼_{w ∼ (μ'')^K}
Stab^{π̂}_{1-d}(g_{K→w}) = ⟨g, Q_d^{⊗ι} g⟩` (`mixture_calculus` on the alphabet `A × A` with the
diagonal fixing law `Δ(μ'')`, `cstab_eq_joint`). The single-law `stab_eq_expect_restriction` is the case
`μ'' = π̂`. -/
theorem k7_two_law_stab (πh μ2 : FinProb A) {lam d : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (g : (ι → A) → ℂ) :
    subsetExpect (1 - lam) (by linarith) (by linarith) (fun K =>
      (μ2.pi ↥K).cexpect fun w => cstab πh (1 - d) (restrictFix K w g)) =
      k7QForm (k7KronPow (k7QMat lam πh μ2 d) ι) g := by
  have hd0' : 0 ≤ 1 - d := by linarith
  have hd1' : 1 - d ≤ 1 := by linarith
  have hmix : ∀ p, (k7rdQLaw lam πh μ2 d hlam0 hlam1 hd0 hd1).prob p =
      (1 - lam) * (jointNoise μ2 1 zero_le_one le_rfl).prob p +
        lam * (jointNoise πh (1 - d) hd0' hd1').prob p := fun p => rfl
  have hQM : ∀ a a', k7QMat lam πh μ2 d a a' =
      (((k7rdQLaw lam πh μ2 d hlam0 hlam1 hd0 hd1).prob (a, a') : ℝ) : ℂ) := by
    intro a a'
    rw [hmix]
    simp only [k7QMat, Matrix.of_apply, jointNoise, noiseKernel]
    congr 1
    ring
  rw [← k7rd_pair_cexpect_eq_qform _ _ hQM g,
    mixture_calculus hlam0 hlam1 (k7rdQLaw lam πh μ2 d hlam0 hlam1 hd0 hd1) _ _ hmix]
  congr 1
  funext K
  rw [joint_one_diag]
  congr 1
  funext z
  rw [cstab_eq_joint πh (1 - d) hd0' hd1']
  congr 1
  funext p
  simp only [restrictFix]
  have h1 : (fun i => (glueFix K (fun j => (z j, z j)) p i).1) =
      glueFix K z (fun i => (p i).1) := by
    funext i
    by_cases h : i ∈ K <;> simp [glueFix, h]
  have h2 : (fun i => (glueFix K (fun j => (z j, z j)) p i).2) =
      glueFix K z (fun i => (p i).2) := by
    funext i
    by_cases h : i ∈ K <;> simp [glueFix, h]
  rw [h1, h2]

end TwoLaw

section Reduce

/-- `prop:reduce` (`k7_reduce_to_unifSupp`; Supplement H; the Loewner reduction): `V̂_n(α, ε/2,
δ̂) ⇒ V_n(α, ε, δ)` with `δ = (α ε/2) δ̂`, for ALL `n` (`n = 0` is vacuous), no threshold on `|ι|`
(including `K̄ = ∅`). `hhat` is the conclusion of `thm:kcsp` for the laws UNIFORM ON THEIR SUPPORT
(`∀ a b ∈ supp, μ a = μ b`), at correlation `ε/2` and the single parameter `δ̂`. The proof proves
`0 ≤ Q_d`, `Q_d ≤ T'_{αd}` and the Kronecker telescoping (`k7_QMat_posSemidef`, `k7_loewner_Q_le_T`,
`k7_kron_sub_posSemidef`), then the chain
`Re Stab^{μ_i}_{1-δ} ≥ Stab^{μ_i}_{1-αd} ≥ E_i ≥ (ε/2) d ≥ δ`, `d = δ̂`. -/
theorem k7_reduce_to_unifSupp (n : ℕ) {α ε δh : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hδ0 : 0 < δh) (hδ1 : δh ≤ 1)
    (hhat : ∀ (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      (∀ a ∈ μ.support, ∀ b ∈ μ.support, μ.prob a = μ.prob b) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
        ε / 2 ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
        ∀ i, δh ≤ (cstab (μ.marginalPi i) (1 - δh) (f i)).re) :
    ∀ (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
      (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
      (∀ a ∈ μ.support, α ≤ μ.prob a) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
        ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
        ∀ i, α * ε / 2 * δh ≤
          (cstab (μ.marginalPi i) (1 - α * ε / 2 * δh) (f i)).re := by
  intro A _ _ μ hno hatom ι _ _ f hf hcorr i
  -- `lem:unif`: `μ̂ = Unif(S)`, `λ = α |S|`, `μ = λ μ̂ + (1-λ) μ''`
  obtain ⟨hlam0, hlam1, μ2, hmix⟩ := k7_unifSupp_decomp hα0 μ hatom
  have hnoh : NoNontrivialAbelianEmbeddingPi (k7UnifSupp μ).support := by
    rw [k7_unifSupp_support]
    exact hno
  have hatomh := k7_unifSupp_atom hα0 μ hatom
  have hunifh := k7_unifSupp_unif μ
  have hsz := k7_suppSize_unifSupp μ
  generalize k7UnifSupp μ = μh at hnoh hatomh hunifh hsz hmix
  generalize hlam : α * (k7SuppSize μ : ℝ) = lam at hlam0 hlam1 hmix
  have hq0 : 0 ≤ 1 - lam := by linarith
  have hq1 : 1 - lam ≤ 1 := by linarith
  -- Step 1: the junk restriction, common to all coordinates
  have hmix' : ∀ a, μ.prob a = (1 - lam) * μ2.prob a + lam * μh.prob a := fun a => by
    rw [hmix a]
    ring
  have hstep1 := mixture_calculus hlam0.le hlam1 μ μ2 μh hmix'
    (fun X : ι → ∀ j, A j => ∏ j, f j fun t => X t j)
  have hE : (μ.pi ι).cexpect (fun X => ∏ j, f j fun t => X t j) =
      subsetExpect (1 - lam) hq0 hq1 fun K => (μ2.pi ↥K).cexpect fun w =>
        (μh.pi ↥Kᶜ).cexpect fun Y => ∏ j, restrictFix K (fun s => w s j) (f j) fun t => Y t j := by
    rw [hstep1]
    refine congrArg (subsetExpect (1 - lam) hq0 hq1) (funext fun K => ?_)
    refine congrArg (FinProb.cexpect (μ2.pi ↥K)) (funext fun w => ?_)
    refine congrArg (FinProb.cexpect (μh.pi ↥Kᶜ)) (funext fun Y => ?_)
    simp only [restrictFix]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [k7rd_glue_comp]
  -- Steps 1-2: Markov and averaging, through `hhat` on `↥Kᶜ`
  have key : δh * (ε / 2) ≤ (subsetExpect (1 - lam) hq0 hq1 fun K => (μ2.pi ↥K).cexpect fun w =>
      cstab (μh.marginalPi i) (1 - δh) (restrictFix K (fun s => w s i) (f i))).re := by
    refine k7rd_avg hq0 hq1 μ2
      (fun K w => (μh.pi ↥Kᶜ).cexpect fun Y =>
        ∏ j, restrictFix K (fun s => w s j) (f j) fun t => Y t j)
      (fun K w => cstab (μh.marginalPi i) (1 - δh) (restrictFix K (fun s => w s i) (f i)))
      hε0.le hδ0.le ?_ ?_ ?_ ?_
    · intro K w
      refine k7rd_norm_cexpect_le_one _ _ fun Y => ?_
      refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun j _ => hf j _)
    · intro K w hc
      exact hhat A μh hnoh hatomh hunifh (↥Kᶜ) (fun j => restrictFix K (fun s => w s j) (f j))
        (fun j x => hf j _) hc i
    · intro K w
      exact k7rd_re_cstab_nonneg _ (by linarith) _
    · rw [← hE]
      exact hcorr
  -- Step 3: the two-law identity (after the push-forward to the `i`-th marginal)
  have hΦ : (subsetExpect (1 - lam) hq0 hq1 fun K => (μ2.pi ↥K).cexpect fun w =>
      cstab (μh.marginalPi i) (1 - δh) (restrictFix K (fun s => w s i) (f i))) =
      k7QForm (k7KronPow (k7QMat lam (μh.marginalPi i) (μ2.marginalPi i) δh) ι) (f i) := by
    rw [← k7_two_law_stab (μh.marginalPi i) (μ2.marginalPi i) hlam0.le hlam1 hδ0.le hδ1 (f i)]
    congr 1
    funext K
    exact k7rd_cexpect_marginal μ2 i
      (fun w' => cstab (μh.marginalPi i) (1 - δh) (restrictFix K w' (f i)))
  rw [hΦ] at key
  -- Step 3: Loewner, through the rational marginals of `μ̂`
  obtain ⟨cnt, hcnt, hπ⟩ := k7_unif_marginal_counts μh hnoh hunifh i
  rw [hsz] at hcnt hπ
  have hvar : ∀ g : A i → ℂ, k7Var (μ.marginalPi i) g ≤
      (k7SuppSize μ : ℝ) * k7Var (μh.marginalPi i) g := fun g =>
    k7_var_compare (μh.marginalPi i) (μ.marginalPi i) (k7SuppSize μ) cnt (fun a => (hcnt a).1)
      hπ g
  have hQT := k7rd_form_le (ι := ι) (μ.marginalPi i) (μh.marginalPi i) (μ2.marginalPi i) hα0
    hlam.symm hlam0.le hlam1 hδ0.le hδ1 (fun x => k7_marginal_mix μ μh μ2 hmix i x) hvar (f i)
  have hαd0 : 0 ≤ α * δh := mul_nonneg hα0.le hδ0.le
  have hαd1 : α * δh ≤ 1 := by nlinarith
  rw [← k7_stab_eq_kron (μ.marginalPi i) hαd0 hαd1 (f i)] at hQT
  -- Step 4: the stability chain
  have hle : 1 - α * δh ≤ 1 - α * ε / 2 * δh := by nlinarith
  have hmono := k7rd_re_cstab_mono (μ.marginalPi i) (by linarith : 0 ≤ 1 - α * δh) hle (f i)
  have hfin : α * ε / 2 * δh ≤ δh * (ε / 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hα1) (mul_nonneg hδ0.le hε0.le)]
  linarith

/-- `cor:tower` (the tower is unchanged; `k7_reduce_to_unifSupp` at `ε' = ε/2`, `k7_absorb_half`, and
the lowering `k7_valid_mono` of `K7KcspAssembly`, re-proved privately from `cstab_mono`
so that this file does not import `K7KcspAssembly`): from `V̂` with the explicit tower
`δ̂ = exp(-exp^{[N]}(ε'^{-b'}))` for all `ε' ∈ (0, 1/2]` to `V` with the tower
`exp(-exp^{[N]}(ε^{-b''}))`, `b'' = b''(α, b')`, the SAME height `N`. -/
theorem k7_tower_reduce (n N : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {b' : ℝ} (hb' : 0 < b')
    (hhat : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 / 2 →
      ∀ (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        (∀ a ∈ μ.support, ∀ b ∈ μ.support, μ.prob a = μ.prob b) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε' ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[N] (ε' ^ (-b')))) ≤
            (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[N] (ε' ^ (-b'))))) (f i)).re) :
    ∃ b'' : ℝ, 0 < b'' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
        (μ : FinProb (∀ i, A i)), NoNontrivialAbelianEmbeddingPi μ.support →
        (∀ a ∈ μ.support, α ≤ μ.prob a) →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ∀ i, (ι → A i) → ℂ), (∀ i x, ‖f i x‖ ≤ 1) →
          ε ≤ ‖(μ.pi ι).cexpect fun X => ∏ i, f i fun t => X t i‖ →
          ∀ i, Real.exp (-(Real.exp^[N] (ε ^ (-b'')))) ≤
            (cstab (μ.marginalPi i) (1 - Real.exp (-(Real.exp^[N] (ε ^ (-b''))))) (f i)).re := by
  obtain ⟨b'', hb'', habs⟩ := k7_absorb_half N hα0 hα1 hb'
  refine ⟨b'', hb'', fun ε hε0 hε1 A _ _ μ hno hatom ι _ _ f hf hcorr i => ?_⟩
  have hδ0 : 0 < Real.exp (-(Real.exp^[N] ((ε / 2) ^ (-b')))) := Real.exp_pos _
  have hδ1 : Real.exp (-(Real.exp^[N] ((ε / 2) ^ (-b')))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact (Real.rpow_nonneg (by linarith) _).trans (le_exp_iterate _ _)
  have hred := k7_reduce_to_unifSupp n hα0 hα1 hε0 (by linarith) hδ0 hδ1
    (fun A _ _ μ hno hat hu ι _ _ f hf hc i =>
      hhat (ε / 2) (by linarith) (by linarith) A μ hno hat hu ι f hf hc i)
    A μ hno hatom ι f hf hcorr i
  have hδ1' : α * ε / 2 * Real.exp (-(Real.exp^[N] ((ε / 2) ^ (-b')))) ≤ 1 := by
    have h1 : α * ε / 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ α * ε / 2 := by positivity
    nlinarith
  exact k7rd_valid_mono (μ.marginalPi i) (f i) (habs ε hε0 hε1) hδ1' hred

end Reduce

end TrackB
end RestrictedPolynomials
end
