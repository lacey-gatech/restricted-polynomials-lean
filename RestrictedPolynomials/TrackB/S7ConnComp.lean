module

public import RestrictedPolynomials.TrackB.S7Chains
public import RestrictedPolynomials.TrackB.MaxTStatements

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section S7CC
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- the marginal `μ_{y,z}` on `Γ × Φ`. -/
def s7LawYZ (μ : FinProb (X × Y × Z)) : FinProb (Y × Z) :=
  mergePush μ fun p => (p.2.1, p.2.2)

/-- "the value of `(y,z)` determines `x`, and every `(y,z)` occurs": for every `(y, z)` there is a
unique `x` with `(x,y,z) ∈ S`. This is hypothesis 5 (full support of `ν_{y,z}`) together with
hypothesis 7 (`y,z` imply `x`) of the relaxed theorem, which Def. of `W` (l. 4359-4368) uses
(paper IV `definition-W-map`). -/
def S7YZImpliesX (S : Set (X × Y × Z)) : Prop := ∀ (y : Y) (z : Z), ∃! x : X, (x, y, z) ∈ S

/-- the unique `x` of `(y, z)` (`∃!` is `S7YZImpliesX`); characterised by `s7Pre_mem`,
`s7Pre_unique`. -/
def s7Pre {S : Set (X × Y × Z)} (h : S7YZImpliesX S) (y : Y) (z : Z) : X := (h y z).choose

theorem s7Pre_mem {S : Set (X × Y × Z)} (h : S7YZImpliesX S) (y : Y) (z : Z) :
    (s7Pre h y z, y, z) ∈ S := (h y z).choose_spec.1

theorem s7Pre_unique {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {x : X} {y : Y} {z : Z}
    (hx : (x, y, z) ∈ S) : x = s7Pre h y z := (h y z).choose_spec.2 x hx

/-- Paper IV `definition-W-map` (l. 4362-4368): `(W f)(y,z) = f(x)` where `x ∈ Σ^ι` is the unique point
with `(xᵢ, yᵢ, zᵢ) ∈ supp μ` for all `i`. `Γ^n × Φ^n` is carried as `ι → Γ × Φ`. -/
def s7W {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {ι : Type} (f : (ι → X) → ℂ) :
    (ι → Y × Z) → ℂ :=
  fun w => f (fun i => s7Pre h (w i).1 (w i).2)

/-- characterisation of `W`: `(W f)(y,z) = f(x)` for every `x` compatible with `(y,z)`. -/
theorem s7W_spec {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {ι : Type} (f : (ι → X) → ℂ)
    (x : ι → X) (w : ι → Y × Z) (hx : ∀ i, (x i, (w i).1, (w i).2) ∈ S) : s7W h f w = f x := by
  unfold s7W
  congr 1
  funext i
  exact (s7Pre_unique h (hx i)).symm

/-- Paper IV `def:const-on-ccs` (Def. 7.17, l. 4370-4373): `F` is constant on connected components. -/
def S7ConstOnCC {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {ι : Type}
    (F : (ι → Y × Z) → ℂ) : Prop :=
  ∃ f : (ι → X) → ℂ, s7W h f = F

/-- Paper IV `definition-connected-component-graph` (l. 4374-4377; typo "both in `Γ × Φ`" read "both in
`supp μ`"): `(y,z) ∼ (y',z')` iff some `x` has `(x,y,z), (x,y',z') ∈ S`. -/
def s7CCAdj (S : Set (X × Y × Z)) (v v' : Y × Z) : Prop :=
  ∃ x : X, (x, v.1, v.2) ∈ S ∧ (x, v'.1, v'.2) ∈ S

/-- the tensor power `(V,E)^{⊗ι}`: coordinatewise adjacency (the source's proof, l. 4395-4397, uses
coordinatewise adjacency including loops; `fromRel` symmetrises and forgets loops, which does not
change `Reachable`). -/
def s7CCGraph (S : Set (X × Y × Z)) (ι : Type) : SimpleGraph (ι → Y × Z) :=
  SimpleGraph.fromRel fun w w' => ∀ i, s7CCAdj S (w i) (w' i)

/-- `W⁻¹ F`, the function `f` with `F = W f` (unique: `s7W_injective`). -/
def s7WInv {S : Set (X × Y × Z)} {h : S7YZImpliesX S}
    (_hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ S) {ι : Type} {F : (ι → Y × Z) → ℂ}
    (hF : S7ConstOnCC h F) : (ι → X) → ℂ := Classical.choose hF

theorem s7W_s7WInv {S : Set (X × Y × Z)} {h : S7YZImpliesX S}
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ S) {ι : Type}
    {F : (ι → Y × Z) → ℂ} (hF : S7ConstOnCC h F) : s7W h (s7WInv hocc hF) = F :=
  Classical.choose_spec hF

/-- coefficient `F̂(Wχ) = ⟨F, Wχ⟩` in `L²(μ_{y,z}^{⊗ι})` (l. 4426). -/
def s7CCCoef (μ : FinProb (X × Y × Z)) (h : S7YZImpliesX μ.support) {J : Type} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u : J → X → ℂ) (F : (ι → Y × Z) → ℂ) (c : ι → J) : ℂ :=
  ((s7LawYZ μ).pi ι).cinner F (s7W h (s7Mono u c))

variable {H : Type} [AddCommGroup H] [Fintype H] {K₁ K₂ : Type}
  (μ : FinProb (X × Y × Z)) (h : S7YZImpliesX μ.support) (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)

/-- cc version of complete embedding homogeneity (Def. l. 4421-4429). -/
def S7CCCompEmbedHom {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Y × Z) → ℂ)
    (Dtot : ℕ) : Prop :=
  ∃ Da : AddChar H ℂ → ℕ, ∑ a, Da a = Dtot ∧
    ∀ c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7CCCoef μ h u F c ≠ 0 → ∀ a, s7EmbedDegA a c = Da a

/-- cc version of non-embedding homogeneity (Def. l. 4432-4436). -/
def S7CCNeHom {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Y × Z) → ℂ) (d : ℕ) : Prop :=
  ∀ c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7CCCoef μ h u F c ≠ 0 → s7NeDeg c = d

/-- cc version of effective non-embedding degree at least `d'` (Def. l. 4439-4442). -/
def S7CCEffDegGE {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Y × Z) → ℂ) (d' : ℕ) : Prop :=
  ∀ c : ι → AddChar H ℂ ⊕ (K₁ ⊕ K₂), s7CCCoef μ h u F c ≠ 0 → d' ≤ s7EffDeg c

/-- Paper IV `definition-cc-class-F` (Def. l. 4445-4449): `F_{n,d,d'}`. -/
def s7ClassF (n d d' : ℕ) : Set ((Fin n → Y × Z) → ℂ) :=
  {F | S7ConstOnCC h F ∧ (∃ Dtot, S7CCCompEmbedHom μ h u F Dtot) ∧ S7CCNeHom μ h u F d ∧
    S7CCEffDegGE μ h u F d'}

/-- Paper IV `definition-class-F-n-dprime` (Def. 9.1, l. 5247-5250): `F_{n,d'}`, no homogeneity
requirement. -/
def s7ClassFn (n d' : ℕ) : Set ((Fin n → Y × Z) → ℂ) :=
  {F | S7ConstOnCC h F ∧ S7CCEffDegGE μ h u F d'}

/-- Paper IV `definition-cc-influences` (Def. l. 4489-4501): `I_{i,modest}[F] := I_{i,modest}[f]`,
`F = W f`. -/
def s7CCModestInf (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support) (Sm : Finset X)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : (ι → Y × Z) → ℂ}
    (hF : S7ConstOnCC h F) (i : ι) : ℝ :=
  s7ModestInf (lawX μ) Sm (s7WInv hocc hF) i

/-- total modest influence of `F`. -/
def s7CCModestTotalInf (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    (Sm : Finset X) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : (ι → Y × Z) → ℂ} (hF : S7ConstOnCC h F) : ℝ :=
  ∑ i, s7CCModestInf μ h hocc Sm hF i

variable [DecidableEq H]

/-- `I_{j,non-embed}[F] := I_{j,non-embed}[f]`. -/
def s7CCNonEmbedInf (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    (σ : X → H) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : (ι → Y × Z) → ℂ} (hF : S7ConstOnCC h F) (j : ι) : ℝ :=
  s7NonEmbedInf (lawX μ) σ (s7WInv hocc hF) j

/-- total non-embedding influence of `F`. -/
def s7CCNonEmbedTotalInf (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    (σ : X → H) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : (ι → Y × Z) → ℂ} (hF : S7ConstOnCC h F) : ℝ :=
  ∑ j, s7CCNonEmbedInf μ h hocc σ hF j

end S7CC

/-! ### Theorems of file 3 (targets) -/

section S7CCThms
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

private theorem s7_finProb_ext {α : Type} [Fintype α] {π π' : FinProb α}
    (h : ∀ a, π.prob a = π'.prob a) : π = π' := by
  cases π
  cases π'
  congr
  funext a
  exact h a

private theorem s7_mergePush_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (π : FinProb α) (f : α → β) (g : β → γ) :
    mergePush (mergePush π f) g = mergePush π (fun a => g (f a)) := by
  refine s7_finProb_ext fun c => ?_
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

private theorem s7_push_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
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

private theorem s7_cexpect_pi_push {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {ι : Type} [Fintype ι] [DecidableEq ι] (π : FinProb α) (a : α → β)
    (G : (ι → β) → ℂ) :
    ((mergePush π a).pi ι).cexpect G = (π.pi ι).cexpect (fun x => G (fun i => a (x i))) :=
  (s7_push_sum a (fun _ c => π.prob c) G).symm

private theorem s7_lawX_eq (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) :
    lawX μ = mergePush (s7LawYZ μ) (fun v => s7Pre hμ v.1 v.2) := by
  unfold s7LawYZ
  rw [s7_mergePush_comp]
  unfold lawX
  refine s7_finProb_ext fun b => ?_
  show ∑ p ∈ univ.filter (fun p : X × Y × Z => p.1 = b), μ.prob p =
    ∑ p ∈ univ.filter (fun p : X × Y × Z => s7Pre hμ p.2.1 p.2.2 = b), μ.prob p
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h0 : μ.prob p = 0
  · simp [h0]
  · have hp : (p.1, p.2.1, p.2.2) ∈ μ.support := h0
    have : p.1 = s7Pre hμ p.2.1 p.2.2 := s7Pre_unique hμ hp
    simp only [this]

private theorem s7_cexpect_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : (ι → X) → ℂ) :
    ((s7LawYZ μ).pi ι).cexpect (fun w => G (fun i => s7Pre hμ (w i).1 (w i).2)) =
      ((lawX μ).pi ι).cexpect G := by
  rw [s7_lawX_eq μ hμ, s7_cexpect_pi_push]

private theorem s7W_sum_smul {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {ι : Type} {J : Type}
    [Fintype J] (a : J → ℂ) (g : J → (ι → X) → ℂ) :
    s7W h (∑ c, a c • g c) = ∑ c, a c • s7W h (g c) := by
  funext w
  simp [s7W, Finset.sum_apply]

private theorem s7W_add {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {ι : Type}
    (f g : (ι → X) → ℂ) : s7W h (f + g) = s7W h f + s7W h g := rfl

private theorem s7W_smul {S : Set (X × Y × Z)} (h : S7YZImpliesX S) {ι : Type}
    (a : ℂ) (f : (ι → X) → ℂ) : s7W h (a • f) = a • s7W h f := rfl

theorem s7_yzImpliesX_iff (S : Set (X × Y × Z)) :
    S7YZImpliesX S ↔ (∀ (y : Y) (z : Z), ∃ x : X, (x, y, z) ∈ S) ∧ mergeImpliesX S := by
  constructor
  · intro h
    exact ⟨fun y z => (h y z).exists, fun y z x x' hx hx' => (h y z).unique hx hx'⟩
  · rintro ⟨hex, hm⟩ y z
    obtain ⟨x, hx⟩ := hex y z
    exact ⟨x, hx, fun x' hx' => hm y z x' x hx' hx⟩

/-- `W` is injective as soon as every `x` occurs in the support (l. 4486: "`W` is a 1-to-1
correspondence"). -/
theorem s7W_injective {S : Set (X × Y × Z)} (h : S7YZImpliesX S)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ S) (ι : Type) :
    Function.Injective (s7W (ι := ι) h) := by
  intro f f' hff
  funext x
  choose y z hyz using fun i => hocc (x i)
  have hx : ∀ i, (x i, ((fun i => (y i, z i)) i).1, ((fun i => (y i, z i)) i).2) ∈ S := hyz
  rw [← s7W_spec h f x (fun i => (y i, z i)) hx, ← s7W_spec h f' x (fun i => (y i, z i)) hx, hff]

/-- uniqueness of `W⁻¹` (the `∃!` behind `s7WInv`). -/
theorem s7WInv_unique {S : Set (X × Y × Z)} (h : S7YZImpliesX S)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ S) {ι : Type} {F : (ι → Y × Z) → ℂ}
    (hF : S7ConstOnCC h F) (f : (ι → X) → ℂ) (hf : s7W h f = F) : f = s7WInv hocc hF := by
  exact s7W_injective h hocc ι (hf.trans (s7W_s7WInv hocc hF).symm)

/-- Paper IV `claim-w-isometry` (l. 4410-4416), inner products: `⟨W f, W f'⟩_{μ_{y,z}^{⊗ι}}
= ⟨f, f'⟩_{μ_x^{⊗ι}}` (the law of `x` is `μ_x`, and `x` is the function of `(y,z)` that `W` uses). -/
theorem s7_W_cinner (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {ι : Type}
    [Fintype ι] [DecidableEq ι] (f f' : (ι → X) → ℂ) :
    ((s7LawYZ μ).pi ι).cinner (s7W hμ f) (s7W hμ f') = ((lawX μ).pi ι).cinner f f' := by
  unfold FinProb.cinner
  exact s7_cexpect_W μ hμ (fun x => f x * star (f' x))

/-- Paper IV `claim-w-isometry`: norms. -/
theorem s7_cl2norm_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {ι : Type}
    [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) :
    cl2norm (s7LawYZ μ) (s7W hμ f) = cl2norm (lawX μ) f := by
  unfold cl2norm
  congr 1
  apply Complex.ofReal_injective
  rw [cl2sq_cast, cl2sq_cast]
  exact s7_W_cinner μ hμ f f

/-- Paper IV `claim-w-isometry`: `{W χ}` is orthonormal when `u` is orthonormal in `L²(μ_x)`. -/
theorem s7_W_mono_orthonormal (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    {J : Type} [DecidableEq J] (u : J → X → ℂ)
    (hu : ∀ i j, (lawX μ).cinner (u i) (u j) = if i = j then 1 else 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (c c' : ι → J) :
    ((s7LawYZ μ).pi ι).cinner (s7W hμ (s7Mono u c)) (s7W hμ (s7Mono u c')) =
      if c = c' then 1 else 0 := by
  rw [s7_W_cinner μ hμ]
  exact s7_mono_orthonormal _ u hu c c'

/-- the coefficients of `W f` against `Wχ` are those of `f` against `χ` (consequence of the
isometry; the transfer step of §7.3.1, l. 4479-4481). -/
theorem s7CCCoef_W (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support) {J : Type}
    {ι : Type} [Fintype ι] [DecidableEq ι] (u : J → X → ℂ) (f : (ι → X) → ℂ) (c : ι → J) :
    s7CCCoef μ hμ u (s7W hμ f) c = s7Coef (lawX μ) u f c := by
  unfold s7CCCoef s7Coef
  exact s7_W_cinner μ hμ f (s7Mono u c)

/-- Paper IV `claim-w-isometry`, basis part: `W f = ∑_χ f̂(χ) Wχ`. -/
theorem s7_W_expansion (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hD : ∀ a, 0 < (lawX μ).prob a) {J : Type} [Fintype J] (u : J → X → ℂ)
    (hu : S7IsONB (lawX μ) u) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) :
    s7W hμ f = ∑ c : ι → J, s7Coef (lawX μ) u f c • s7W hμ (s7Mono u c) := by
  have hf := s7_fourier_expansion (lawX μ) hD u hu f
  calc s7W hμ f = s7W hμ (∑ c : ι → J, s7Coef (lawX μ) u f c • s7Mono u c) := congrArg _ hf
    _ = _ := s7W_sum_smul hμ _ _

/-- Paper IV `lem:constant-on-ccs-equiv` (1)⇔(2) (l. 4378-4399): `F` is constant on connected components
iff `F` is constant on each connected component of `(V,E)^{⊗n}`. No occurrence hypothesis is
needed: `f x := F w` for any `w` compatible with `x` (and `0` if there is none); the point
`pre w₀` of any `w₀` is compatible with `w₀`. -/
theorem s7_constOnCC_iff_reachable {S : Set (X × Y × Z)} (h : S7YZImpliesX S)
    {ι : Type} (F : (ι → Y × Z) → ℂ) :
    S7ConstOnCC h F ↔ ∀ w w', (s7CCGraph S ι).Reachable w w' → F w = F w' := by
  have key : ∀ b c : ι → Y × Z, (s7CCGraph S ι).Adj b c → ∃ x : ι → X,
      (∀ i, (x i, (b i).1, (b i).2) ∈ S) ∧ ∀ i, (x i, (c i).1, (c i).2) ∈ S := by
    intro b c hadj
    rw [s7CCGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hr | hr
    · have hr' : ∀ i, ∃ x : X, (x, (b i).1, (b i).2) ∈ S ∧ (x, (c i).1, (c i).2) ∈ S := hr
      choose x hx using hr'
      exact ⟨x, fun i => (hx i).1, fun i => (hx i).2⟩
    · have hr' : ∀ i, ∃ x : X, (x, (c i).1, (c i).2) ∈ S ∧ (x, (b i).1, (b i).2) ∈ S := hr
      choose x hx using hr'
      exact ⟨x, fun i => (hx i).2, fun i => (hx i).1⟩
  constructor
  · rintro ⟨f, rfl⟩ w w' hr
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => rfl
    | @tail b c _ hadj ih =>
      rw [ih]
      obtain ⟨x, hb, hc⟩ := key b c hadj
      rw [s7W_spec h f x b hb, s7W_spec h f x c hc]
  · intro H
    classical
    refine ⟨fun x => if hx : ∃ w : ι → Y × Z, ∀ i, (x i, (w i).1, (w i).2) ∈ S
      then F (Classical.choose hx) else 0, ?_⟩
    funext w0
    have hx : ∃ w : ι → Y × Z, ∀ i,
        (s7Pre h (w0 i).1 (w0 i).2, (w i).1, (w i).2) ∈ S :=
      ⟨w0, fun i => s7Pre_mem h _ _⟩
    show (if hx' : ∃ w : ι → Y × Z, ∀ i, (s7Pre h (w0 i).1 (w0 i).2, (w i).1, (w i).2) ∈ S
      then F (Classical.choose hx') else 0) = F w0
    rw [dif_pos hx]
    apply H
    by_cases he : Classical.choose hx = w0
    · rw [he]
    · apply SimpleGraph.Adj.reachable
      rw [s7CCGraph, SimpleGraph.fromRel_adj]
      refine ⟨he, Or.inl fun i => ⟨s7Pre h (w0 i).1 (w0 i).2, Classical.choose_spec hx i,
        s7Pre_mem h _ _⟩⟩

/-- Paper IV `lem:constant-on-ccs-equiv` (1)⇔(3): `F ∈ span{Wχ : χ ∈ (B_embed ∪ B_non-embed ∪ B_modest)^{⊗n}}`;
`u` any orthonormal basis of `L²(μ_x)`. -/
theorem s7_constOnCC_iff_mem_span (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
    (hD : ∀ a, 0 < (lawX μ).prob a) {J : Type} [Fintype J] (u : J → X → ℂ)
    (hu : S7IsONB (lawX μ) u) {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Y × Z) → ℂ) :
    S7ConstOnCC hμ F ↔
      F ∈ Submodule.span ℂ (Set.range fun c : ι → J => s7W hμ (s7Mono u c)) := by
  constructor
  · rintro ⟨f, rfl⟩
    rw [s7_W_expansion μ hμ hD u hu f]
    exact Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · intro hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨c, rfl⟩ := hF
      exact ⟨s7Mono u c, rfl⟩
    | zero => exact ⟨0, rfl⟩
    | add F G _ _ hF hG =>
      obtain ⟨f, rfl⟩ := hF
      obtain ⟨g, rfl⟩ := hG
      exact ⟨f + g, rfl⟩
    | smul a F _ hF =>
      obtain ⟨f, rfl⟩ := hF
      exact ⟨a • f, rfl⟩

section Classes
variable {H : Type} [AddCommGroup H] [Fintype H] {K₁ K₂ : Type}
  (μ : FinProb (X × Y × Z)) (hμ : S7YZImpliesX μ.support)
  (u : AddChar H ℂ ⊕ (K₁ ⊕ K₂) → X → ℂ)

/-- the cc classes are the `W`-images of the `x` classes (l. 4479-4481: `F = W f` is completely
embedding homogeneous, non-embedding homogeneous of degree `d`, effective degree `≥ d'`). -/
theorem s7_mem_classF_iff (n d d' : ℕ) (F : (Fin n → Y × Z) → ℂ) :
    F ∈ s7ClassF μ hμ u n d d' ↔
      ∃ f : (Fin n → X) → ℂ, s7W hμ f = F ∧ f ∈ s7ClassFp (lawX μ) u n d d' := by
  constructor
  · rintro ⟨⟨f, rfl⟩, ⟨Dtot, h1⟩, h2, h3⟩
    refine ⟨f, rfl, ⟨Dtot, ?_⟩, ?_, ?_⟩
    · simpa only [S7CCCompEmbedHom, S7CompEmbedHom, s7CCCoef_W] using h1
    · simpa only [S7CCNeHom, S7NeHom, s7CCCoef_W] using h2
    · simpa only [S7CCEffDegGE, S7EffDegGE, s7CCCoef_W] using h3
  · rintro ⟨f, rfl, ⟨Dtot, h1⟩, h2, h3⟩
    refine ⟨⟨f, rfl⟩, ⟨Dtot, ?_⟩, ?_, ?_⟩
    · simpa only [S7CCCompEmbedHom, S7CompEmbedHom, s7CCCoef_W] using h1
    · simpa only [S7CCNeHom, S7NeHom, s7CCCoef_W] using h2
    · simpa only [S7CCEffDegGE, S7EffDegGE, s7CCCoef_W] using h3

theorem s7_mem_classFn_iff (n d' : ℕ) (F : (Fin n → Y × Z) → ℂ) :
    F ∈ s7ClassFn μ hμ u n d' ↔
      ∃ f : (Fin n → X) → ℂ, s7W hμ f = F ∧ S7EffDegGE (lawX μ) u f d' := by
  constructor
  · rintro ⟨⟨f, rfl⟩, h3⟩
    refine ⟨f, rfl, ?_⟩
    simpa only [S7CCEffDegGE, S7EffDegGE, s7CCCoef_W] using h3
  · rintro ⟨f, rfl, h3⟩
    refine ⟨⟨f, rfl⟩, ?_⟩
    simpa only [S7CCEffDegGE, S7EffDegGE, s7CCCoef_W] using h3

/-- `F_{n,d,d'} ⊆ F_{n,d'}` (paper IV `definition-class-F-n-dprime`). -/
theorem s7_classF_subset_classFn (n d d' : ℕ) :
    s7ClassF μ hμ u n d d' ⊆ s7ClassFn μ hμ u n d' := by
  rintro F ⟨hc, _, _, h3⟩
  exact ⟨hc, h3⟩

/-- `F_{n,d'}` is closed under addition (used implicitly in Lemma 9.3, l. 5444-5445). -/
theorem s7_classFn_add (n d' : ℕ) {F G : (Fin n → Y × Z) → ℂ} (hF : F ∈ s7ClassFn μ hμ u n d')
    (hG : G ∈ s7ClassFn μ hμ u n d') : F + G ∈ s7ClassFn μ hμ u n d' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨f, rfl⟩ := hF.1
    obtain ⟨g, rfl⟩ := hG.1
    exact ⟨f + g, rfl⟩
  · intro c hc
    have hadd : s7CCCoef μ hμ u (F + G) c = s7CCCoef μ hμ u F c + s7CCCoef μ hμ u G c :=
      cinner_add_left _ _ _ _
    rw [hadd] at hc
    by_cases h0 : s7CCCoef μ hμ u F c = 0
    · rw [h0, zero_add] at hc
      exact hG.2 c hc
    · exact hF.2 c h0

/-- `F_{n,d'}` is closed under scalar multiplication. -/
theorem s7_classFn_smul (n d' : ℕ) (a : ℂ) {F : (Fin n → Y × Z) → ℂ}
    (hF : F ∈ s7ClassFn μ hμ u n d') : a • F ∈ s7ClassFn μ hμ u n d' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨f, rfl⟩ := hF.1
    exact ⟨a • f, rfl⟩
  · intro c hc
    have hs : s7CCCoef μ hμ u (a • F) c = a * s7CCCoef μ hμ u F c := cinner_smul_left _ _ _ _
    rw [hs] at hc
    exact hF.2 c (right_ne_zero_of_mul hc)

theorem s7_zero_mem_classFn (n d' : ℕ) : (fun _ => 0) ∈ s7ClassFn μ hμ u n d' := by
  refine ⟨⟨fun _ => 0, rfl⟩, ?_⟩
  intro c hc
  exact absurd (cinner_zero_left _ _) hc

/-- `I_{i,modest}[F] = I_{i,modest}[f]` for `F = W f` (Def. l. 4489-4501; uses uniqueness of `f`). -/
theorem s7CCModestInf_W (Sm : Finset X) (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (i : ι) :
    s7CCModestInf μ hμ hocc Sm (F := s7W hμ f) ⟨f, rfl⟩ i = s7ModestInf (lawX μ) Sm f i := by
  unfold s7CCModestInf
  rw [← s7WInv_unique hμ hocc ⟨f, rfl⟩ f rfl]

variable [DecidableEq H]

theorem s7CCNonEmbedInf_W (σ : X → H)
    (hocc : ∀ x : X, ∃ (y : Y) (z : Z), (x, y, z) ∈ μ.support)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → X) → ℂ) (j : ι) :
    s7CCNonEmbedInf μ hμ hocc σ (F := s7W hμ f) ⟨f, rfl⟩ j = s7NonEmbedInf (lawX μ) σ f j := by
  unfold s7CCNonEmbedInf
  rw [← s7WInv_unique hμ hocc ⟨f, rfl⟩ f rfl]

end Classes
end S7CCThms

end TrackB
end RestrictedPolynomials
end
