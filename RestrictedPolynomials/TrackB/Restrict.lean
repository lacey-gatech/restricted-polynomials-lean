module

public import RestrictedPolynomials.Restriction
public import RestrictedPolynomials.TrackB.StabComplex
public import RestrictedPolynomials.Frozen.CStab
public import RestrictedPolynomials.Frozen.FinProbPi
public import RestrictedPolynomials.Frozen.FinProbCExpect

/-!
# Track B: random restrictions and the mixture calculus

Sources: paper IV (`writeup_stability.tex`) L1114-1135 (restriction triple); CSP_6 `main.tex`
L231-237, L752-753 (random restriction, mixture calculus part 1); CSP_7 `kcsp.tex` L541-543,
L765-767 (mixture restriction part 1, final restriction identity).

Covers paper IV `definition-restriction`, `definition-mixture-restriction` and
`claim-mixture-restriction-preserves-measure`; CSP_6 `definition-random-restriction` and
`definition-random-restriction#mixture-calculus` (part 1 only); CSP_7
`lemma:kcsp#mixture-random-restriction` (part 1 only) and `thm:kcsp#final-restriction-identity`.

Two source conventions share one Bernoulli model (`subsetExpect`): `restrictFree` (paper IV: the set
`L` is live) and `restrictFix` (CSP_6/CSP_7: the set `F` is fixed); `restrictFree_eq_restrictFix` is the
bridge (`F = Lᶜ`), and `subsetExpect_compl` flips the probability `q ↔ 1 - q`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Restrict
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the point `(x_F = z, x_{Fᶜ} = y)` -/
def glueFix (F : Finset ι) (z : F → α) (y : ↥Fᶜ → α) : ι → α :=
  fun i => if h : i ∈ F then z ⟨i, h⟩ else y ⟨i, mem_compl.2 h⟩

/-- `f_{F→z}` fixing the coordinates in `F` (CSP6/CSP7 convention). -/
def restrictFix (F : Finset ι) (z : F → α) (f : (ι → α) → ℂ) : (↥Fᶜ → α) → ℂ :=
  fun y => f (glueFix F z y)

/-- the point `(x_L = y, x_{Lᶜ} = z)` -/
def glueFree (L : Finset ι) (y : L → α) (z : ↥Lᶜ → α) : ι → α :=
  fun i => if h : i ∈ L then y ⟨i, h⟩ else z ⟨i, mem_compl.2 h⟩

/-- `f_{Lᶜ→z}` as a function of the live coordinates `L` (paper IV convention). -/
def restrictFree (L : Finset ι) (z : ↥Lᶜ → α) (f : (ι → α) → ℂ) : (L → α) → ℂ :=
  fun y => f (glueFree L y z)

/-- `𝔼_{I ∼_q [n]} G(I)`: `I` contains each coordinate independently with probability `q`. -/
def subsetExpect (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (G : Finset ι → ℂ) : ℂ :=
  ((bernoulli q h0 h1).pi ι).cexpect fun s => G (trueSet s)

/-- `𝔼_{I ⊆_ρ [n], z ∼ D₂^{Ī}} Φ(I, f_{Ī→z})`. -/
def mixtureRestrictionExpect (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (D₂ : FinProb α)
    (f : (ι → α) → ℂ) (Φ : ∀ I : Finset ι, ((↥I → α) → ℂ) → ℂ) : ℂ :=
  subsetExpect ρ h0 h1 fun I => (D₂.pi ↥Iᶜ).cexpect fun z => Φ I (restrictFree I z f)

theorem restrictFree_eq_restrictFix (L : Finset ι) (z : ↥Lᶜ → α) (f : (ι → α) → ℂ)
    (y : L → α) :
    restrictFree L z f y = restrictFix Lᶜ z f (fun i => y ⟨i.1, by simpa using i.2⟩) := by
  unfold restrictFree restrictFix
  congr 1
  funext i
  by_cases h : i ∈ L
  · have h' : i ∉ Lᶜ := by simpa using h
    simp [glueFree, glueFix, h, h']
  · have h' : i ∈ Lᶜ := by simpa using h
    simp [glueFree, glueFix, h, h']

/-! ### Helpers -/

/-- Flipping the sampled set: `𝔼_{I ∼_q} G(I) = 𝔼_{I ∼_{1-q}} G(Iᶜ)`. -/
theorem subsetExpect_compl (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (G : Finset ι → ℂ) :
    subsetExpect q h0 h1 G =
      subsetExpect (1 - q) (by linarith) (by linarith) (fun I => G Iᶜ) := by
  unfold subsetExpect FinProb.cexpect
  let e : (ι → Bool) ≃ (ι → Bool) := Equiv.piCongrRight fun _ => (⟨not, not, Bool.not_not, Bool.not_not⟩ : Bool ≃ Bool)
  refine Fintype.sum_equiv e _ _ fun s => ?_
  have hs : trueSet (e s) = (trueSet s)ᶜ := by
    ext i; simp [e, trueSet]
  show _ = (((bernoulli (1 - q) _ _).pi ι).prob (e s) : ℂ) * G (trueSet (e s))ᶜ
  have hp : ((bernoulli q h0 h1).pi ι).prob s = ((bernoulli (1 - q) (by linarith)
      (by linarith)).pi ι).prob (e s) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [e, Equiv.piCongrRight_apply]
    cases h : s i <;> simp [bernoulli, h]
  rw [hs, compl_compl, hp]

/-- evaluating the weighted sum over a glued pair -/
theorem inner_glue (A B : FinProb α) (I : Finset ι) (G : (ι → α) → ℂ) :
    (B.pi ↥Iᶜ).cexpect (fun z => (A.pi ↥I).cexpect fun y => G (glueFree I y z)) =
      ∑ x, ((∏ i, (if i ∈ I then A.prob (x i) else B.prob (x i)) : ℝ) : ℂ) * G x := by
  let e : (↥I → α) × (↥Iᶜ → α) ≃ (ι → α) :=
    { toFun := fun p => glueFree I p.1 p.2
      invFun := fun x => (fun i => x i, fun i => x i)
      left_inv := by
        rintro ⟨y, z⟩
        refine Prod.ext ?_ ?_
        · funext i; simp [glueFree, i.2]
        · funext i
          have : (i : ι) ∉ I := mem_compl.1 i.2
          simp [glueFree, this]
      right_inv := by
        intro x; funext i; by_cases h : i ∈ I <;> simp [glueFree, h] }
  have hw : ∀ p : (↥I → α) × (↥Iᶜ → α),
      (∏ i, (if i ∈ I then A.prob (e p i) else B.prob (e p i)) : ℝ) =
        (A.pi ↥I).prob p.1 * (B.pi ↥Iᶜ).prob p.2 := by
    intro p
    rw [← prod_mul_prod_compl I]
    have h1 : ∏ i ∈ I, (if i ∈ I then A.prob (e p i) else B.prob (e p i)) =
        (A.pi ↥I).prob p.1 := by
      rw [prod_congr rfl (g := fun i => A.prob (e p i)) (fun i hi => by simp [hi]),
        ← prod_coe_sort I]
      exact prod_congr rfl fun i _ => by simp [e, glueFree, i.2]
    have h2 : ∏ i ∈ Iᶜ, (if i ∈ I then A.prob (e p i) else B.prob (e p i)) =
        (B.pi ↥Iᶜ).prob p.2 := by
      rw [prod_congr rfl (g := fun i => B.prob (e p i)) (fun i hi => by simp at hi; simp [hi]),
        ← prod_coe_sort Iᶜ]
      refine prod_congr rfl fun i _ => ?_
      have : (i : ι) ∉ I := mem_compl.1 i.2
      simp [e, glueFree, this]
    rw [h1, h2]
  symm
  rw [← Fintype.sum_equiv e (fun p => ((∏ i, (if i ∈ I then A.prob (e p i)
      else B.prob (e p i)) : ℝ) : ℂ) * G (e p)) _ (fun p => rfl)]
  simp only [hw, FinProb.cexpect, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  simp only [e, Equiv.coe_fn_mk]
  push_cast
  ring

/-- the Bernoulli average of the glued weights -/
theorem subsetExpect_weights {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (A B : FinProb α)
    (W : Finset ι → (ι → α) → ℂ)
    (hW : ∀ I x, W I x = ((∏ i, (if i ∈ I then A.prob (x i) else B.prob (x i)) : ℝ) : ℂ)) 
    (G : (ι → α) → ℂ) :
    subsetExpect q h0 h1 (fun I => ∑ x, W I x * G x) =
      ∑ x, ((∏ i, (q * A.prob (x i) + (1 - q) * B.prob (x i)) : ℝ) : ℂ) * G x := by
  have hr : ∀ x : ι → α, ∑ s : ι → Bool, ((bernoulli q h0 h1).pi ι).prob s *
      (∏ i, (if i ∈ trueSet s then A.prob (x i) else B.prob (x i))) =
      ∏ i, (q * A.prob (x i) + (1 - q) * B.prob (x i)) := by
    intro x
    have : ∀ s : ι → Bool, ((bernoulli q h0 h1).pi ι).prob s *
        (∏ i, (if i ∈ trueSet s then A.prob (x i) else B.prob (x i))) =
        ∏ i, ((bernoulli q h0 h1).prob (s i) *
          (if s i = true then A.prob (x i) else B.prob (x i))) := by
      intro s
      rw [prod_mul_distrib]
      simp [FinProb.pi, trueSet]
    simp only [this]
    rw [← Fintype.prod_sum (fun i b => (bernoulli q h0 h1).prob b *
          (if b = true then A.prob (x i) else B.prob (x i)))]
    refine prod_congr rfl fun i _ => ?_
    simp [bernoulli]
  unfold subsetExpect FinProb.cexpect
  simp only [hW, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  have h2 : ∑ s : ι → Bool, (((bernoulli q h0 h1).pi ι).prob s : ℂ) *
      (((∏ i, (if i ∈ trueSet s then A.prob (x i) else B.prob (x i)) : ℝ) : ℂ) * G x) =
      ((∏ i, (q * A.prob (x i) + (1 - q) * B.prob (x i)) : ℝ) : ℂ) * G x := by
    rw [← hr x]
    push_cast
    rw [Finset.sum_mul]
    exact sum_congr rfl fun s _ => by ring
  exact h2

/-- Exchanging two complex expectations. -/
theorem cexpect_comm {β γ : Type} [Fintype β] [Fintype γ] (P : FinProb β) (Q : FinProb γ)
    (g : β → γ → ℂ) :
    P.cexpect (fun a => Q.cexpect fun b => g a b) = Q.cexpect fun b => P.cexpect fun a => g a b := by
  simp only [FinProb.cexpect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring

/-- The glued Bernoulli average: the point has law `q A + (1-q) B` coordinatewise. -/
theorem restrict_key {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (A B μ : FinProb α)
    (hmix : ∀ a, μ.prob a = q * A.prob a + (1 - q) * B.prob a) (G : (ι → α) → ℂ) :
    subsetExpect q h0 h1 (fun I => (B.pi ↥Iᶜ).cexpect fun z =>
      (A.pi ↥I).cexpect fun y => G (glueFree I y z)) = (μ.pi ι).cexpect G := by
  have h : (fun I : Finset ι => (B.pi ↥Iᶜ).cexpect fun z =>
      (A.pi ↥I).cexpect fun y => G (glueFree I y z)) =
      fun I => ∑ x, ((∏ i, (if i ∈ I then A.prob (x i) else B.prob (x i)) : ℝ) : ℂ) * G x :=
    funext fun I => inner_glue A B I G
  rw [h, subsetExpect_weights h0 h1 A B (fun I x =>
    ((∏ i, (if i ∈ I then A.prob (x i) else B.prob (x i)) : ℝ) : ℂ)) (fun _ _ => rfl) G]
  unfold FinProb.cexpect
  refine sum_congr rfl fun x _ => ?_
  congr 2
  exact prod_congr rfl fun i _ => (hmix (x i)).symm

theorem mixture_restriction_law {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (μ D₁ D₂ : FinProb α)
    (hmix : ∀ a, μ.prob a = ρ * D₁.prob a + (1 - ρ) * D₂.prob a) (x : ι → α) :
    subsetExpect ρ hρ0.le hρ1.le (fun I => (D₂.pi ↥Iᶜ).cexpect fun z =>
      (D₁.pi ↥I).cexpect fun y => if glueFree I y z = x then (1 : ℂ) else 0) =
      (((μ.pi ι).prob x : ℝ) : ℂ) := by
  rw [restrict_key hρ0.le hρ1.le D₁ D₂ μ hmix (fun x' => if x' = x then (1 : ℂ) else 0)]
  simp [FinProb.cexpect]

theorem mixture_restriction_expect {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (μ D₁ D₂ : FinProb α)
    (hmix : ∀ a, μ.prob a = ρ * D₁.prob a + (1 - ρ) * D₂.prob a) (f : (ι → α) → ℂ) :
    mixtureRestrictionExpect ρ hρ0.le hρ1.le D₂ f (fun I g => (D₁.pi ↥I).cexpect g) =
      (μ.pi ι).cexpect f :=
  restrict_key hρ0.le hρ1.le D₁ D₂ μ hmix f

theorem mixture_restriction_sqNorm {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (μ D₁ D₂ : FinProb α)
    (hmix : ∀ a, μ.prob a = ρ * D₁.prob a + (1 - ρ) * D₂.prob a) (f : (ι → α) → ℂ) :
    mixtureRestrictionExpect ρ hρ0.le hρ1.le D₂ f (fun I g => ((cl2sq D₁ g : ℝ) : ℂ)) =
      ((cl2sq μ f : ℝ) : ℂ) := by
  have hc : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (ν : FinProb α) (g : (κ → α) → ℂ),
      ((cl2sq ν g : ℝ) : ℂ) = (ν.pi κ).cexpect fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ) := by
    intro κ _ _ ν g
    simp [cl2sq, FinProb.expect, FinProb.cexpect]
  rw [hc μ f]
  have := restrict_key hρ0.le hρ1.le D₁ D₂ μ hmix (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ))
  rw [← this]
  unfold mixtureRestrictionExpect
  simp only [hc D₁]
  rfl

theorem mixture_calculus {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (π ν π' : FinProb α)
    (hmix : ∀ a, π.prob a = (1 - ρ) * ν.prob a + ρ * π'.prob a) (F : (ι → α) → ℂ) :
    (π.pi ι).cexpect F =
      subsetExpect (1 - ρ) (by linarith) (by linarith) fun I =>
        (ν.pi ↥I).cexpect fun w => (π'.pi ↥Iᶜ).cexpect (restrictFix I w F) := by
  have := restrict_key (q := 1 - ρ) (by linarith) (by linarith) ν π' π
    (fun a => by rw [hmix a]; ring) F
  rw [← this]
  congr 1
  funext I
  exact cexpect_comm _ _ _

/-! ### The joint law of one coordinate pair under the noise kernel -/

/-- the law of `(x, y)` with `x ∼ π` and `y ∼_ρ x`, on the alphabet `α × α` -/
def jointNoise (π : FinProb α) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : FinProb (α × α) where
  prob p := π.prob p.1 * noiseKernel π ρ p.1 p.2
  nonneg p := mul_nonneg (π.nonneg _) (by
    unfold noiseKernel
    exact add_nonneg (mul_nonneg h0 (by split_ifs <;> norm_num))
      (mul_nonneg (by linarith) (π.nonneg _)))
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    have : ∀ a, ∑ b, π.prob a * noiseKernel π ρ a b = π.prob a := by
      intro a
      simp only [noiseKernel, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        π.sum_eq_one]
      simp
    simp only [this, π.sum_eq_one]

omit [DecidableEq ι] in
/-- complex stability as an expectation over pairs -/
theorem cstab_eq_joint (π : FinProb α) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    {κ : Type} [Fintype κ] [DecidableEq κ] (g : (κ → α) → ℂ) :
    cstab π ρ g = ((jointNoise π ρ h0 h1).pi κ).cexpect
      fun p => g (fun i => (p i).1) * star (g (fun i => (p i).2)) := by
  let e : (κ → α × α) ≃ (κ → α) × (κ → α) :=
    Equiv.arrowProdEquivProdArrow κ (fun _ => α) (fun _ => α)
  unfold cstab cnoiseOp FinProb.cexpect
  rw [← Fintype.sum_equiv e.symm (fun q : (κ → α) × (κ → α) => (((jointNoise π ρ h0 h1).pi κ).prob
      (e.symm q) : ℂ) * (g q.1 * star (g q.2))) _ (fun p => by simp [e]),
    Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  beta_reduce
  rw [star_sum, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have : ((jointNoise π ρ h0 h1).pi κ).prob (e.symm (x, y)) =
      ((π.pi κ).prob x) * ∏ i, noiseKernel π ρ (x i) (y i) := by
    simp only [FinProb.pi, jointNoise, e, prod_mul_distrib]
    rfl
  rw [this, star_mul', show star (((∏ i, noiseKernel π ρ (x i) (y i) : ℝ)) : ℂ) =
    ((∏ i, noiseKernel π ρ (x i) (y i) : ℝ) : ℂ) from Complex.conj_ofReal _]
  push_cast
  ring

omit [DecidableEq ι] in
/-- at `ρ = 1` the pair is supported on the diagonal -/
theorem joint_one_diag (π : FinProb α) {κ : Type} [Fintype κ] [DecidableEq κ]
    (H : (κ → α × α) → ℂ) :
    ((jointNoise π 1 zero_le_one le_rfl).pi κ).cexpect H =
      (π.pi κ).cexpect fun z => H (fun j => (z j, z j)) := by
  let e : (κ → α × α) ≃ (κ → α) × (κ → α) :=
    Equiv.arrowProdEquivProdArrow κ (fun _ => α) (fun _ => α)
  unfold FinProb.cexpect
  rw [← Fintype.sum_equiv e.symm (fun q : (κ → α) × (κ → α) => (((jointNoise π 1 zero_le_one
      le_rfl).pi κ).prob (e.symm q) : ℂ) * H (e.symm q)) _ (fun p => by simp [e]),
    Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => ?_
  have hJ : ∀ z2 : κ → α, ((jointNoise π 1 zero_le_one le_rfl).pi κ).prob (e.symm (z, z2)) =
      (π.pi κ).prob z * (if z = z2 then 1 else 0) := by
    intro z2
    have : ∀ j, (jointNoise π 1 zero_le_one le_rfl).prob (z j, z2 j) =
        π.prob (z j) * (if z j = z2 j then 1 else 0) := by
      intro j; simp [jointNoise, noiseKernel]
    simp only [FinProb.pi, e]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, this, prod_mul_distrib,
      Finset.prod_boole, mem_univ, forall_true_left, funext_iff]
  simp only [hJ]
  rw [Finset.sum_eq_single z]
  · simp only [ite_true, mul_one]; rfl
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem stab_eq_expect_restriction (π : FinProb α) {γ δ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (f : (ι → α) → ℂ) :
    cstab π (1 - γ * δ) f =
      subsetExpect (1 - δ) (by linarith) (by linarith) fun I =>
        (π.pi ↥I).cexpect fun z => cstab π (1 - γ) (restrictFix I z f) := by
  have hgd0 : 0 ≤ γ * δ := mul_nonneg hγ0 hδ0
  have hgd1 : γ * δ ≤ 1 := by nlinarith
  have hJ0 : 0 ≤ 1 - γ * δ := by linarith
  have hJ1 : 1 - γ * δ ≤ 1 := by linarith
  have hK0 : 0 ≤ 1 - γ := by linarith
  have hK1 : 1 - γ ≤ 1 := by linarith
  have hmix : ∀ a : α × α, (jointNoise π (1 - γ * δ) hJ0 hJ1).prob a =
      (1 - δ) * (jointNoise π 1 zero_le_one le_rfl).prob a +
        δ * (jointNoise π (1 - γ) hK0 hK1).prob a := by
    intro a
    simp only [jointNoise, noiseKernel]
    ring
  rw [cstab_eq_joint π (1 - γ * δ) hJ0 hJ1 f,
    mixture_calculus hδ0 hδ1 (jointNoise π (1 - γ * δ) hJ0 hJ1) (jointNoise π 1 zero_le_one le_rfl)
      (jointNoise π (1 - γ) hK0 hK1) hmix]
  congr 1
  funext I
  rw [joint_one_diag]
  congr 1
  funext z
  rw [cstab_eq_joint π (1 - γ) hK0 hK1]
  congr 1
  funext p
  simp only [restrictFix]
  have h1 : (fun i => (glueFix I (fun j => (z j, z j)) p i).1) = glueFix I z (fun i => (p i).1) := by
    funext i; by_cases h : i ∈ I <;> simp [glueFix, h]
  have h2 : (fun i => (glueFix I (fun j => (z j, z j)) p i).2) = glueFix I z (fun i => (p i).2) := by
    funext i; by_cases h : i ∈ I <;> simp [glueFix, h]
  rw [h1, h2]

end Restrict
end TrackB
end RestrictedPolynomials
end
