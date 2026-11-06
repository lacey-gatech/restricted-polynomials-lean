module

public import RestrictedPolynomials.TrackB.Restrict

/-!
# Track B: nested random restrictions

Sources: CSP6 `main.tex` L753 (`#mixture-calculus` (2); use sites L1148, L1167, L1277) and CSP7
`kcsp.tex` L541-543 (`#mixture-random-restriction`, second sentence).

Two nested restrictions compose into one: `composeSet`, `composeVals`, `composeEquiv` identify the
fixed set, its values and the free coordinates; `restrictFix_compose` is the function identity,
`nested_restriction_law` the equality of laws of the pair (fixed set, fixed values),
`cexpect_pi_composeEquiv` the transport of the free measure, and `nested_restriction_expect` the
combined statement. The law is proved by encoding `(J, v)` as a point of `ι → Option α`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section Compose
variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `J = I ∪ I'`: the first fixed set `I ⊆ ι` together with a second fixed set `I'`, chosen among the
free coordinates `↥Iᶜ`, as a subset of `ι`. -/
def composeSet (I : Finset ι) (I' : Finset ↥Iᶜ) : Finset ι :=
  I ∪ I'.map (Function.Embedding.subtype _)

theorem mem_composeSet {I : Finset ι} {I' : Finset ↥Iᶜ} {i : ι} :
    i ∈ composeSet I I' ↔ i ∈ I ∨ ∃ h : i ∉ I, (⟨i, mem_compl.2 h⟩ : ↥Iᶜ) ∈ I' := by
  simp [composeSet]

/-- the combined fixing `(w, w')` of the coordinates of `J = I ∪ I'`. -/
def composeVals (I : Finset ι) (I' : Finset ↥Iᶜ) (w : I → α) (w' : I' → α) :
    composeSet I I' → α :=
  fun j => if h : j.1 ∈ I then w ⟨j.1, h⟩ else
    w' ⟨⟨j.1, mem_compl.2 h⟩, by
      have := j.2
      rw [mem_composeSet] at this
      rcases this with h' | ⟨_, h'⟩
      · exact absurd h' h
      · exact h'⟩

/-- the identification of the free coordinates: those of `J = I ∪ I'` and those left after the
second restriction. -/
def composeEquiv (I : Finset ι) (I' : Finset ↥Iᶜ) : ↥(composeSet I I')ᶜ ≃ ↥I'ᶜ where
  toFun j := ⟨⟨j.1, by
      have := j.2
      simp only [mem_compl, mem_composeSet, not_or, not_exists] at this
      exact mem_compl.2 this.1⟩, by
      have := j.2
      simp only [mem_compl, mem_composeSet, not_or, not_exists] at this
      exact mem_compl.2 (this.2 this.1)⟩
  invFun a := ⟨a.1.1, by
      have h1 := a.2
      have h2 := a.1.2
      simp only [mem_compl, mem_composeSet, not_or, not_exists] at h1 h2 ⊢
      exact ⟨h2, fun _ => h1⟩⟩
  left_inv j := rfl
  right_inv a := rfl

/-- `(F_{I→w})_{I'→w'} = F_{(I∪I')→(w,w')}` (K6 `#mixture-calculus` (2), second clause). -/
theorem restrictFix_compose (I : Finset ι) (I' : Finset ↥Iᶜ) (w : I → α) (w' : I' → α)
    (f : (ι → α) → ℂ) (y : ↥I'ᶜ → α) :
    restrictFix I' w' (restrictFix I w f) y =
      restrictFix (composeSet I I') (composeVals I I' w w') f
        (fun j => y (composeEquiv I I' j)) := by
  unfold restrictFix
  congr 1
  funext i
  by_cases hi : i ∈ I
  · have hJ : i ∈ composeSet I I' := mem_composeSet.2 (Or.inl hi)
    simp [glueFix, hi, hJ, composeVals]
  · by_cases hi' : (⟨i, mem_compl.2 hi⟩ : ↥Iᶜ) ∈ I'
    · have hJ : i ∈ composeSet I I' := mem_composeSet.2 (Or.inr ⟨hi, hi'⟩)
      simp [glueFix, hi, hi', hJ, composeVals]
    · have hJ : i ∉ composeSet I I' := by
        intro h
        rcases mem_composeSet.1 h with h1 | ⟨_, h2⟩
        · exact hi h1
        · exact hi' h2
      simp [glueFix, hi, hi', hJ, composeEquiv]

/-! ### Encoding `(J, v)` as a point of `ι → Option α` -/

/-- `ν` pushed forward along `some`, as a measure on `Option α`. -/
private def liftSome (ν : FinProb α) : FinProb (Option α) where
  prob o := match o with
    | none => 0
    | some a => ν.prob a
  nonneg o := by
    cases o
    · exact le_rfl
    · exact ν.nonneg _
  sum_eq_one := by
    rw [Fintype.sum_option]
    simp [ν.sum_eq_one]

/-- the Dirac mass at `none`. -/
private def noneP : FinProb (Option α) where
  prob o := if o = none then 1 else 0
  nonneg o := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-- the mixture `q A + (1 - q) B`. -/
private def mixP {β : Type} [Fintype β] (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (A B : FinProb β) :
    FinProb β where
  prob x := q * A.prob x + (1 - q) * B.prob x
  nonneg x := add_nonneg (mul_nonneg h0 (A.nonneg _)) (mul_nonneg (by linarith) (B.nonneg _))
  sum_eq_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, A.sum_eq_one, B.sum_eq_one]
    ring

private theorem cexpect_liftSome {κ : Type} [Fintype κ] [DecidableEq κ] (ν : FinProb α)
    (H : (κ → Option α) → ℂ) :
    ((liftSome ν).pi κ).cexpect H = (ν.pi κ).cexpect fun w => H (fun i => some (w i)) := by
  unfold FinProb.cexpect
  symm
  refine Fintype.sum_of_injective (fun (w : κ → α) (i : κ) => some (w i)) ?_ _ _ ?_ ?_
  · intro w w' h
    funext i
    exact Option.some.inj (congrFun h i)
  · intro y hy
    have : ∃ i, y i = none := by
      by_contra hne
      push Not at hne
      apply hy
      refine ⟨fun i => (y i).get (Option.isSome_iff_ne_none.2 (hne i)), ?_⟩
      funext i
      simp
    obtain ⟨i, hi⟩ := this
    have : (liftSome ν).prob (y i) = 0 := by simp [liftSome, hi]
    rw [FinProb.pi_prob, Finset.prod_eq_zero (Finset.mem_univ i) this]
    simp
  · intro w
    simp [FinProb.pi_prob, liftSome]

private theorem cexpect_noneP {κ : Type} [Fintype κ] [DecidableEq κ]
    (H : (κ → Option α) → ℂ) :
    ((noneP (α := α)).pi κ).cexpect H = H (fun _ => none) := by
  unfold FinProb.cexpect
  rw [Finset.sum_eq_single (fun _ => none)]
  · simp [FinProb.pi_prob, noneP]
  · intro y _ hy
    have : ∃ i, y i ≠ none := by
      by_contra hne
      push Not at hne
      exact hy (funext hne)
    obtain ⟨i, hi⟩ := this
    have : (noneP (α := α)).prob (y i) = 0 := by simp [noneP, hi]
    rw [FinProb.pi_prob, Finset.prod_eq_zero (Finset.mem_univ i) this]
    simp
  · simp

/-- the code `x : ι → Option α` of a pair `(J, v)` back to the fixed set -/
private def codeSet (x : ι → Option α) : Finset ι := univ.filter fun i => (x i).isSome

private def codeVals (x : ι → Option α) : ↥(codeSet x) → α :=
  fun j => (x j.1).get (by simpa [codeSet] using j.2)

private def codeΦ (Φ : ∀ J : Finset ι, (↥J → α) → ℂ) (x : ι → Option α) : ℂ :=
  Φ (codeSet x) (codeVals x)

omit [DecidableEq α] in
private theorem Phi_congr (Φ : ∀ J : Finset ι, (↥J → α) → ℂ) {J J' : Finset ι} (h : J = J')
    {v : J → α} {v' : J' → α} (hv : ∀ i (hi : i ∈ J), v ⟨i, hi⟩ = v' ⟨i, h ▸ hi⟩) :
    Φ J v = Φ J' v' := by
  subst h
  congr 1
  funext j
  exact hv j.1 j.2

private theorem restrict_key_opt {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℝ} (h0 : 0 ≤ q)
    (h1 : q ≤ 1) (ν : FinProb α) (B μ : FinProb (Option α))
    (hmix : ∀ x, μ.prob x = q * (liftSome ν).prob x + (1 - q) * B.prob x)
    (G : (ι → Option α) → ℂ) :
    subsetExpect q h0 h1 (fun I => (B.pi ↥Iᶜ).cexpect fun z => (ν.pi ↥I).cexpect fun w =>
      G (glueFree I (fun j => some (w j)) z)) = (μ.pi ι).cexpect G := by
  rw [← restrict_key h0 h1 (liftSome ν) B μ hmix G]
  congr 1
  funext I
  congr 1
  funext z
  rw [cexpect_liftSome]

private theorem codeΦ_single (Φ : ∀ J : Finset ι, (↥J → α) → ℂ) (J : Finset ι) (w : J → α) :
    codeΦ Φ (glueFree J (fun j => some (w j)) (fun _ => (none : Option α))) = Φ J w := by
  unfold codeΦ
  have hJ : codeSet (glueFree J (fun j => some (w j)) (fun _ => (none : Option α))) = J := by
    ext i
    by_cases hi : i ∈ J <;> simp [codeSet, glueFree, hi]
  refine Phi_congr Φ hJ fun i hi => ?_
  have hi' : i ∈ J := hJ ▸ hi
  simp [codeVals, glueFree, hi']

private theorem codeΦ_compose (Φ : ∀ J : Finset ι, (↥J → α) → ℂ) (I : Finset ι)
    (I' : Finset ↥Iᶜ) (w : I → α) (w' : I' → α) :
    codeΦ Φ (glueFree I (fun j => some (w j))
      (glueFree I' (fun j => some (w' j)) (fun _ => (none : Option α)))) =
      Φ (composeSet I I') (composeVals I I' w w') := by
  unfold codeΦ
  have hJ : codeSet (glueFree I (fun j => some (w j))
      (glueFree I' (fun j => some (w' j)) (fun _ => (none : Option α)))) = composeSet I I' := by
    ext i
    rw [mem_composeSet]
    by_cases hi : i ∈ I
    · simp [codeSet, glueFree, hi]
    · by_cases hi' : (⟨i, mem_compl.2 hi⟩ : ↥Iᶜ) ∈ I'
      · simp [codeSet, glueFree, hi, hi']
      · simp [codeSet, glueFree, hi, hi']
  refine Phi_congr Φ hJ fun i hi => ?_
  by_cases hiI : i ∈ I
  · simp [codeVals, glueFree, hiI, composeVals]
  · have hi' : (⟨i, mem_compl.2 hiI⟩ : ↥Iᶜ) ∈ I' := by
      rcases mem_composeSet.1 (hJ ▸ hi) with h | ⟨_, h⟩
      · exact absurd h hiI
      · exact h
    simp [codeVals, glueFree, hiI, hi', composeVals]

/-- K6 `#mixture-calculus` (2), first clause, and the second sentence of K7 `#mixture-random-restriction`:
the pair (fixed set, fixed values) of two nested restrictions has the law of one restriction by
`(ρρ', ν̄)`, `(1 - ρρ') ν̄ = (1 - ρ) ν + ρ (1 - ρ') ν'`. -/
theorem nested_restriction_law {ρ ρ' : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ'0 : 0 ≤ ρ')
    (hρ'1 : ρ' ≤ 1) (ν ν' νbar : FinProb α)
    (hbar : ∀ a, (1 - ρ * ρ') * νbar.prob a =
      (1 - ρ) * ν.prob a + ρ * (1 - ρ') * ν'.prob a)
    (Φ : ∀ J : Finset ι, (↥J → α) → ℂ) :
    subsetExpect (1 - ρ) (by linarith) (by linarith) (fun I =>
      (ν.pi ↥I).cexpect fun w =>
        subsetExpect (ι := ↥Iᶜ) (1 - ρ') (by linarith) (by linarith) fun I' =>
          (ν'.pi ↥I').cexpect fun w' => Φ (composeSet I I') (composeVals I I' w w')) =
      subsetExpect (1 - ρ * ρ') (by nlinarith [mul_nonneg hρ0 hρ'0])
        (by nlinarith [mul_nonneg hρ0 hρ'0]) (fun J => (νbar.pi ↥J).cexpect (Φ J)) := by
  have hq0 : 0 ≤ 1 - ρ * ρ' := by nlinarith [mul_nonneg hρ0 hρ'0]
  have hq1 : 1 - ρ * ρ' ≤ 1 := by nlinarith [mul_nonneg hρ0 hρ'0]
  let μ' : FinProb (Option α) :=
    mixP (1 - ρ') (by linarith) (by linarith) (liftSome ν') noneP
  let M : FinProb (Option α) := mixP (1 - ρ * ρ') hq0 hq1 (liftSome νbar) noneP
  have hM : ∀ x, M.prob x = (1 - ρ) * (liftSome ν).prob x + (1 - (1 - ρ)) * μ'.prob x := by
    intro x
    cases x with
    | none => simp [M, μ', mixP, liftSome, noneP]
    | some a =>
      simp only [M, μ', mixP, liftSome, noneP]
      simp
      linear_combination hbar a
  -- the right side
  have hR : subsetExpect (1 - ρ * ρ') hq0 hq1 (fun J => (νbar.pi ↥J).cexpect (Φ J)) =
      (M.pi ι).cexpect (codeΦ Φ) := by
    rw [← restrict_key_opt hq0 hq1 νbar noneP M (fun x => rfl) (codeΦ Φ)]
    congr 1
    funext J
    rw [cexpect_noneP]
    simp only [codeΦ_single]
  have hL : ∀ (I : Finset ι) (w : I → α),
      subsetExpect (ι := ↥Iᶜ) (1 - ρ') (by linarith) (by linarith) (fun I' =>
        (ν'.pi ↥I').cexpect fun w' => Φ (composeSet I I') (composeVals I I' w w')) =
      (μ'.pi ↥Iᶜ).cexpect fun u => codeΦ Φ (glueFree I (fun j => some (w j)) u) := by
    intro I w
    rw [← restrict_key_opt (ι := ↥Iᶜ) (by linarith : 0 ≤ 1 - ρ') (by linarith) ν' noneP μ'
      (fun x => rfl) (fun u => codeΦ Φ (glueFree I (fun j => some (w j)) u))]
    congr 1
    funext I'
    rw [cexpect_noneP]
    congr 1
    funext w'
    exact (codeΦ_compose Φ I I' w w').symm
  rw [hR, ← restrict_key_opt (by linarith : 0 ≤ 1 - ρ) (by linarith) ν μ' M hM (codeΦ Φ)]
  congr 1
  funext I
  calc (ν.pi ↥I).cexpect (fun w => subsetExpect (ι := ↥Iᶜ) (1 - ρ') (by linarith) (by linarith)
          (fun I' => (ν'.pi ↥I').cexpect fun w' => Φ (composeSet I I') (composeVals I I' w w')))
      = (ν.pi ↥I).cexpect fun w => (μ'.pi ↥Iᶜ).cexpect fun u =>
          codeΦ Φ (glueFree I (fun j => some (w j)) u) := by
        congr 1
        funext w
        exact hL I w
    _ = _ := cexpect_comm _ _ _

/-- K6 `#mixture-calculus` (2), free-measure clause: the free measure `π''` on `↥I'ᶜ` is carried to the
free measure `π''` on `↥(I ∪ I')ᶜ` by `composeEquiv`. -/
theorem cexpect_pi_composeEquiv (π'' : FinProb α) (I : Finset ι) (I' : Finset ↥Iᶜ)
    (g : (↥I'ᶜ → α) → ℂ) :
    (π''.pi ↥I'ᶜ).cexpect g =
      (π''.pi ↥(composeSet I I')ᶜ).cexpect
        (fun y => g (fun a => y ((composeEquiv I I').symm a))) :=
  (cexpect_pi_equiv (composeEquiv I I') π'' g).symm

omit [DecidableEq α] in
/-- the mixture identity for the composite: `π = (1 - ρρ') ν̄ + ρρ' π''`. -/
theorem compose_mixture {ρ ρ' : ℝ} (π ν π' π'' ν' νbar : FinProb α)
    (hmix : ∀ a, π.prob a = (1 - ρ) * ν.prob a + ρ * π'.prob a)
    (hmix' : ∀ a, π'.prob a = (1 - ρ') * ν'.prob a + ρ' * π''.prob a)
    (hbar : ∀ a, (1 - ρ * ρ') * νbar.prob a =
      (1 - ρ) * ν.prob a + ρ * (1 - ρ') * ν'.prob a) (a : α) :
    π.prob a = (1 - ρ * ρ') * νbar.prob a + ρ * ρ' * π''.prob a := by
  rw [hmix a, hmix' a]
  linear_combination (-1) * hbar a

/-- the composed random restriction acts on every `F` like the single restriction by `(ρρ', ν̄)`
with free measure `π''` (law, function identity and free measure together). -/
theorem nested_restriction_expect {ρ ρ' : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ'0 : 0 ≤ ρ')
    (hρ'1 : ρ' ≤ 1) (π ν π' π'' ν' νbar : FinProb α)
    (hmix : ∀ a, π.prob a = (1 - ρ) * ν.prob a + ρ * π'.prob a)
    (hmix' : ∀ a, π'.prob a = (1 - ρ') * ν'.prob a + ρ' * π''.prob a)
    (hbar : ∀ a, (1 - ρ * ρ') * νbar.prob a =
      (1 - ρ) * ν.prob a + ρ * (1 - ρ') * ν'.prob a) (F : (ι → α) → ℂ) :
    subsetExpect (1 - ρ) (by linarith) (by linarith) (fun I =>
      (ν.pi ↥I).cexpect fun w =>
        subsetExpect (ι := ↥Iᶜ) (1 - ρ') (by linarith) (by linarith) fun I' =>
          (ν'.pi ↥I').cexpect fun w' =>
            (π''.pi ↥I'ᶜ).cexpect (restrictFix I' w' (restrictFix I w F))) =
      subsetExpect (1 - ρ * ρ') (by nlinarith [mul_nonneg hρ0 hρ'0])
        (by nlinarith [mul_nonneg hρ0 hρ'0]) (fun J =>
          (νbar.pi ↥J).cexpect fun v => (π''.pi ↥Jᶜ).cexpect (restrictFix J v F)) := by
  have h := nested_restriction_law hρ0 hρ1 hρ'0 hρ'1 ν ν' νbar hbar
    (fun J v => (π''.pi ↥Jᶜ).cexpect (restrictFix J v F))
  have hfun : ∀ (I : Finset ι) (w : I → α) (I' : Finset ↥Iᶜ) (w' : I' → α),
      (π''.pi ↥I'ᶜ).cexpect (restrictFix I' w' (restrictFix I w F)) =
        (π''.pi ↥(composeSet I I')ᶜ).cexpect
          (restrictFix (composeSet I I') (composeVals I I' w w') F) := by
    intro I w I' w'
    rw [cexpect_pi_composeEquiv π'' I I' (restrictFix I' w' (restrictFix I w F))]
    congr 1
    funext y
    rw [restrictFix_compose]
    congr 1
  simp only [hfun]
  exact h

end Compose
end TrackB
end RestrictedPolynomials
end
