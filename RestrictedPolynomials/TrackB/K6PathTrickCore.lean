module

public import RestrictedPolynomials.TrackB.PathTrickEmbedding
public import RestrictedPolynomials.TrackB.PathTrickInequality
public import RestrictedPolynomials.Frozen.FinProbCExpect

/-!
# Track B: the CSP_6 path trick for one measure

Source: CSP_6, l. 699-723 (`lemma:pathtrick`,
`lemma:pathtrick#h-tilde-reduction`, `eq:biginduct`).

For ONE measure `ν` on `A × B × C` (roles: labels `A`, start `B`, end `C`) this file proves

* `k6pt_hTilde_core`: the `h̃`-reduction (`h̃` is `1`-bounded, `𝔼 f g h̃ = ‖h̃‖₂²`,
  `|𝔼 f g h|² ≤ ‖h̃‖₂²`);
* the Markov gluing `k6pt_evenExpect_double` (the step of CSP_6 `eq:biginduct` that the source leaves implicit):
  `Q_{N+N} = ∑_y margY(y) |R_N(y)|²`, with base case `Q₂ = 𝔼 f g h̃` (`k6pt_evenExpect_two`);
* `k6pt_biginduct_core` (`eq:biginduct`): `|𝔼 f g h|^{2^r} ≤ |Q_{2^r}|`;
* `k6pt_pathtrick_core` (`lemma:pathtrick`), which is `from_mu_to_path`.

`k6ptAlt` and `k6ptCondC` are definitionally `altProd` and `condZ`.
-/

@[expose] public section

open Finset
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

section K6ptCore
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- `F(w) = ∏ₖ f(wₖ)` for even `k`, `conj f(wₖ)` for odd `k` (`k` is `0`-indexed). For `ℓ = 2^r - 1`
this is the source's `f⁺(x) = ∏_{i=1}^{2^{r-1}} f(xᵢ) ∏_{i=1}^{2^{r-1}-1} conj f(xᵢ')` on the labels
`(x₁, x₁', …, x_{2^{r-1}})`. -/
def k6ptAlt {W : Type} (f : W → ℂ) {ℓ : ℕ} (w : Fin ℓ → W) : ℂ :=
  ∏ k : Fin ℓ, if k.val % 2 = 0 then f (w k) else star (f (w k))

/-- `f⁺` is `1`-bounded when `f` is. -/
theorem norm_k6ptAlt_le_one {W : Type} (f : W → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) {ℓ : ℕ}
    (w : Fin ℓ → W) : ‖k6ptAlt f w‖ ≤ 1 := by
  unfold k6ptAlt
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  split_ifs
  · exact hf _
  · simpa using hf _

/-- `h̃(c) = 𝔼_{(a,b,c')∼ν}[conj(f(a) g(b)) | c' = c]` (K6 `#h-tilde-reduction`); with Lean's
`x / 0 = 0` it is `0` where `ν_C(c) = 0`. -/
def k6ptCondC (ν : FinProb (A × B × C)) (f : A → ℂ) (g : B → ℂ) (c : C) : ℂ :=
  ∑ p : A × B, ((ν.prob (p.1, p.2, c) / margZ ν c : ℝ) : ℂ) * (star (f p.1) * star (g p.2))

/-- The left side of CSP_6 `eq:biginduct` for one measure `ν` on `A × B × C`: the expectation over the
`N`-step walk `y₁ → y_{N/2+1}` of the alternating product of `f` along its `N` labels times
`g(y₁) conj g(y_end)`; weights `margY ν y₁ · walkYY ν labels y₁ y_end` (`N` even). -/
def k6ptEvenExpect (ν : FinProb (A × B × C)) (N : ℕ) (f : A → ℂ) (g : B → ℂ) : ℂ :=
  ∑ w : Fin N → A, ∑ y : B, ∑ y' : B,
    ((margY ν y * walkYY ν (List.ofFn w) y y' : ℝ) : ℂ) * (k6ptAlt f w * (g y * star (g y')))

/-- `R_N(y) = ∑_{v, y'} walk_N(v)(y, y') · F(v) · conj g(y')`: the contribution of a walk of `N`
steps started at `y` (used in the Markov gluing). -/
def k6ptEvenR (ν : FinProb (A × B × C)) (N : ℕ) (f : A → ℂ) (g : B → ℂ) (y : B) : ℂ :=
  ∑ v : Fin N → A, ∑ y' : B,
    ((walkYY ν (List.ofFn v) y y' : ℝ) : ℂ) * (k6ptAlt f v * star (g y'))

/-! ### Private helpers -/

/-- weighted sesquilinear form -/
private def ipk {α : Type} [Fintype α] (w : α → ℝ) (a b : α → ℂ) : ℂ :=
  ∑ i, (w i : ℂ) * (star (a i) * b i)

private lemma ipk_self {α : Type} [Fintype α] (w : α → ℝ) (a : α → ℂ) :
    ipk w a a = ((∑ i, w i * ‖a i‖ ^ 2 : ℝ) : ℂ) := by
  unfold ipk
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (a i) * a i = ((‖a i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
  rw [this]

private lemma norm_ipk_le {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a b : α → ℂ) :
    ‖ipk w a b‖ ^ 2 ≤ (∑ i, w i * ‖a i‖ ^ 2) * (∑ i, w i * ‖b i‖ ^ 2) := by
  have h1 : ‖ipk w a b‖ ≤ ∑ i, Real.sqrt (w i) * ‖a i‖ * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, norm_star, Real.norm_of_nonneg (hw i)]
    rw [show Real.sqrt (w i) * ‖a i‖ * (Real.sqrt (w i) * ‖b i‖) =
      (Real.sqrt (w i) * Real.sqrt (w i)) * (‖a i‖ * ‖b i‖) by ring, Real.mul_self_sqrt (hw i)]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => Real.sqrt (w i) * ‖a i‖)
    (fun i => Real.sqrt (w i) * ‖b i‖)
  have e1 : ∀ i, (Real.sqrt (w i) * ‖a i‖) ^ 2 = w i * ‖a i‖ ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have e2 : ∀ i, (Real.sqrt (w i) * ‖b i‖) ^ 2 = w i * ‖b i‖ ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simp only [e1, e2] at h2
  calc ‖ipk w a b‖ ^ 2 ≤ (∑ i, Real.sqrt (w i) * ‖a i‖ * (Real.sqrt (w i) * ‖b i‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

private lemma sum_xy_eq_k6 (ν : FinProb (A × B × C)) (f : A → ℂ) (g : B → ℂ) (c : C) :
    ∑ p : A × B, (ν.prob (p.1, p.2, c) : ℂ) * (f p.1 * g p.2) =
      (margZ ν c : ℂ) * star (k6ptCondC ν f g c) := by
  unfold k6ptCondC
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have c2 : (margZ ν c : ℂ) * ((ν.prob (p.1, p.2, c) / margZ ν c : ℝ) : ℂ) =
      (ν.prob (p.1, p.2, c) : ℂ) := by
    have := margZ_mul_stepZY ν p.1 p.2 c
    simp only [stepZY, Matrix.of_apply] at this
    exact_mod_cast this
  simp only [star_mul', Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination (f p.1 * g p.2) * (-c2)

private lemma sum_reorder5 {M : Type} [AddCommMonoid M] (T : A → A → B → B → C → M) :
    ∑ a₁, ∑ a₂, ∑ y, ∑ y', ∑ c, T a₁ a₂ y y' c =
      ∑ c, ∑ a₁, ∑ a₂, ∑ y, ∑ y', T a₁ a₂ y y' c := by
  calc ∑ a₁, ∑ a₂, ∑ y, ∑ y', ∑ c, T a₁ a₂ y y' c
      = ∑ a₁, ∑ a₂, ∑ y, ∑ c, ∑ y', T a₁ a₂ y y' c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₁, ∑ a₂, ∑ c, ∑ y, ∑ y', T a₁ a₂ y y' c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₁, ∑ c, ∑ a₂, ∑ y, ∑ y', T a₁ a₂ y y' c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma sum_reorder5b {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] {M : Type} [AddCommMonoid M] (T : α → β → γ → δ → ε → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T a b c d e = ∑ e, ∑ a, ∑ c, ∑ b, ∑ d, T a b c d e := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T a b c d e
      = ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, T a b c d e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, T a b c d e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, T a b c d e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, T a b c d e := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma k6ptAlt_append {m n : ℕ} (hm : Even m) (f : A → ℂ) (u : Fin m → A)
    (v : Fin n → A) : k6ptAlt f (Fin.append u v) = k6ptAlt f u * k6ptAlt f v := by
  obtain ⟨k, hk⟩ := hm
  unfold k6ptAlt
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [Fin.append_left]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have : (m + i.val) % 2 = i.val % 2 := by omega
    simp [Fin.append_right, this]

private lemma k6ptAlt_rev {N : ℕ} (hN : Even N) (f : A → ℂ) (u : Fin N → A) :
    k6ptAlt f (u ∘ Fin.rev) = star (k6ptAlt f u) := by
  obtain ⟨k, hk⟩ := hN
  unfold k6ptAlt
  rw [star_prod]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  have h1 : (Fin.revPerm i).val = N - (i.val + 1) := by simp [Fin.revPerm, Fin.val_rev]
  simp only [Function.comp, Fin.revPerm_apply]
  by_cases hi : (Fin.rev i).val % 2 = 0
  · have : ¬ (i.val % 2 = 0) := by
      have := Fin.val_rev i
      omega
    have hi' : (N - (i.val + 1)) % 2 = 0 := by rw [← Fin.val_rev]; exact hi
    simp [this, hi']
  · have : i.val % 2 = 0 := by
      have := Fin.val_rev i
      omega
    have hi' : ¬ (N - (i.val + 1)) % 2 = 0 := by rw [← Fin.val_rev]; exact hi
    simp [this, hi']

private lemma ofFn_rev_k6 {N : ℕ} (u : Fin N → A) :
    (List.ofFn u).reverse = List.ofFn (u ∘ Fin.rev) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_ofFn, Function.comp]
  congr 1
  ext
  simp only [Fin.val_rev, List.length_ofFn]
  omega

private def revEquivK6 (N : ℕ) : (Fin N → A) ≃ (Fin N → A) where
  toFun u := u ∘ Fin.rev
  invFun u := u ∘ Fin.rev
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp

private lemma sum_four_mul {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (L : α → β → ℂ) (Rr : γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, L a b * Rr c d = (∑ a, ∑ b, L a b) * ∑ c, ∑ d, Rr c d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

/-- the left factor of the gluing: `∑_{u,y} margY(y) walk_u(y,m) F(u) g(y) = margY(m) conj R_N(m)`. -/
private lemma k6pt_gluing_left (ν : FinProb (A × B × C)) {N : ℕ} (hN : Even N) (f : A → ℂ)
    (g : B → ℂ) (m : B) :
    ∑ u : Fin N → A, ∑ y, ((margY ν y * walkYY ν (List.ofFn u) y m : ℝ) : ℂ) *
        (k6ptAlt f u * g y) =
      (margY ν m : ℂ) * star (k6ptEvenR ν N f g m) := by
  have h1 : ∀ u : Fin N → A, ∑ y, ((margY ν y * walkYY ν (List.ofFn u) y m : ℝ) : ℂ) *
        (k6ptAlt f u * g y) =
      ∑ y, ((margY ν m * walkYY ν (List.ofFn (u ∘ Fin.rev)) m y : ℝ) : ℂ) *
        (star (k6ptAlt f (u ∘ Fin.rev)) * g y) := by
    intro u
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [walkYY_reverse ν (List.ofFn u) (by simpa using hN) y m, ofFn_rev_k6, k6ptAlt_rev hN,
      star_star]
  rw [Finset.sum_congr rfl fun u _ => h1 u]
  refine (Fintype.sum_equiv (revEquivK6 N) _
    (fun u => ∑ y, ((margY ν m * walkYY ν (List.ofFn u) m y : ℝ) : ℂ) *
        (star (k6ptAlt f u) * g y)) (fun u => rfl)).trans ?_
  unfold k6ptEvenR
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  ring

private lemma sum_reorder5c {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] {M : Type} [AddCommMonoid M] (T : α → β → γ → δ → ε → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T a b c d e = ∑ b, ∑ c, ∑ e, ∑ a, ∑ d, T a b c d e := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T a b c d e
      = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, T a b c d e := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, T a b c d e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ e, ∑ d, T a b c d e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma k6ptCondC_sum (ν : FinProb (A × B × C)) (f : A → ℂ) (g : B → ℂ) (c : C) :
    k6ptCondC ν f g c =
      ∑ a, ∑ y', ((stepZY ν a c y' : ℝ) : ℂ) * (star (f a) * star (g y')) := by
  unfold k6ptCondC
  rw [Fintype.sum_prod_type]
  rfl

private lemma walkYY_snoc_k6 (ν : FinProb (A × B × C)) (a : A) :
    ∀ (k : ℕ) (w : List A), w.length = 2 * k + 1 →
      walkYY ν (w ++ [a]) = walkYZ ν w * stepZY ν a := by
  intro k
  induction k with
  | zero =>
    intro w hw
    match w, hw with
    | [x], _ => simp [walkYY, walkYZ]
  | succ k ih =>
    intro w hw
    match w, hw with
    | x₁ :: x₂ :: rest, hw =>
      have hr : rest.length = 2 * k + 1 := by simp at hw; omega
      have := ih rest hr
      simp only [List.cons_append, walkYY, walkYZ]
      rw [this]
      simp only [Matrix.mul_assoc]

private lemma sum_pathX_k6 (ν : FinProb (A × B × C)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (G : (Fin ℓ → A) → B → C → ℂ) :
    ∑ q : PathX ν ℓ hℓ × B × C,
        (pathWeight ν ℓ hℓ q.1.1 q.2.1 q.2.2 : ℂ) * G q.1.1 q.2.1 q.2.2 =
      ∑ r : (Fin ℓ → A) × B × C, (pathWeight ν ℓ hℓ r.1 r.2.1 r.2.2 : ℂ) * G r.1 r.2.1 r.2.2 := by
  refine Fintype.sum_of_injective (fun q : PathX ν ℓ hℓ × B × C => (q.1.1, q.2)) ?_ _ _ ?_ ?_
  rotate_left 2
  · intro q; rfl
  rotate_right 2
  · rintro ⟨⟨w, hw⟩, y, z⟩ ⟨⟨w', hw'⟩, y', z'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · intro r hr
    have : pathWeight ν ℓ hℓ r.1 r.2.1 r.2.2 = 0 := by
      by_contra hne
      exact hr ⟨(⟨r.1, r.2.1, r.2.2, hne⟩, r.2.1, r.2.2), rfl⟩
    simp [this]

/-- K6 `#h-tilde-reduction`, one measure: (1) `h̃` is `1`-bounded, (2) `𝔼[f g h̃] = ‖h̃‖₂²`, (3)
`|𝔼 f g h|² ≤ ‖h̃‖₂²` (Cauchy-Schwarz, `‖h‖ ≤ 1`). -/
theorem k6pt_hTilde_core (ν : FinProb (A × B × C)) (f : A → ℂ) (g : B → ℂ) (h : C → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1) (hh : ∀ c, ‖h c‖ ≤ 1) :
    (∀ c, ‖k6ptCondC ν f g c‖ ≤ 1) ∧
    (∑ p : A × B × C, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * k6ptCondC ν f g p.2.2) =
      ((∑ c, margZ ν c * ‖k6ptCondC ν f g c‖ ^ 2 : ℝ) : ℂ)) ∧
    ‖∑ p : A × B × C, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ^ 2 ≤
      ∑ c, margZ ν c * ‖k6ptCondC ν f g c‖ ^ 2 := by
  have hb := from_mu_to_path_base ν f g h hf hg hh
  exact ⟨fun c => norm_condZ_le_one ν f g hf hg c, hb.1, hb.2⟩

/-- regrouping: `Q_N = ∑_y margY(y) g(y) R_N(y)` (no parity needed). -/
theorem k6pt_evenExpect_eq (ν : FinProb (A × B × C)) (N : ℕ) (f : A → ℂ) (g : B → ℂ) :
    k6ptEvenExpect ν N f g = ∑ y, (margY ν y : ℂ) * (g y * k6ptEvenR ν N f g y) := by
  unfold k6ptEvenExpect k6ptEvenR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y' _ => ?_
  push_cast
  ring

/-- base case (identity (a)): `Q_2 = 𝔼[f g h̃] = ∑_c ν_C(c) ‖h̃(c)‖²`. -/
theorem k6pt_evenExpect_two (ν : FinProb (A × B × C)) (f : A → ℂ) (g : B → ℂ) :
    k6ptEvenExpect ν 2 f g = ((∑ c, margZ ν c * ‖k6ptCondC ν f g c‖ ^ 2 : ℝ) : ℂ) := by
  have e1 : k6ptEvenExpect ν 2 f g = ∑ a₁, ∑ a₂, ∑ y, ∑ y', ∑ c,
      ((ν.prob (a₁, y, c) : ℝ) : ℂ) * (f a₁ * g y) *
        (((stepZY ν a₂ c y' : ℝ) : ℂ) * (star (f a₂) * star (g y'))) := by
    unfold k6ptEvenExpect
    refine (Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => A) _
      (fun p : A × A => ∑ y, ∑ y', ∑ c, ((ν.prob (p.1, y, c) : ℝ) : ℂ) * (f p.1 * g y) *
        (((stepZY ν p.2 c y' : ℝ) : ℂ) * (star (f p.2) * star (g y')))) (fun w => ?_)).trans
      (Fintype.sum_prod_type _) |>.trans ?_
    · refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
      simp only [piFinTwoEquiv_apply, List.ofFn_succ, List.ofFn_zero, walkYY, k6ptAlt,
        Fin.prod_univ_two, Fin.succ_zero_eq_one]
      simp only [Matrix.mul_one]
      simp only [Matrix.mul_apply, Fin.val_zero, Fin.val_one, Nat.zero_mod, if_true,
        Nat.one_mod, one_ne_zero, if_false]
      simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← margY_mul_stepYZ ν (w 0) y c]
      push_cast
      ring
    · rfl
  have e2 : ∀ c, ((margZ ν c * ‖k6ptCondC ν f g c‖ ^ 2 : ℝ) : ℂ) =
      (∑ a₁, ∑ y, ((ν.prob (a₁, y, c) : ℝ) : ℂ) * (f a₁ * g y)) *
        (∑ a₂, ∑ y', ((stepZY ν a₂ c y' : ℝ) : ℂ) * (star (f a₂) * star (g y'))) := by
    intro c
    have hh : k6ptCondC ν f g c =
        ∑ a₂, ∑ y', ((stepZY ν a₂ c y' : ℝ) : ℂ) * (star (f a₂) * star (g y')) := by
      unfold k6ptCondC
      rw [Fintype.sum_prod_type]
      rfl
    have hs := sum_xy_eq_k6 ν f g c
    rw [Fintype.sum_prod_type] at hs
    rw [hs, ← hh]
    have hc : star (k6ptCondC ν f g c) * k6ptCondC ν f g c = ((‖k6ptCondC ν f g c‖ : ℝ) : ℂ) ^ 2 :=
      Complex.conj_mul' _
    push_cast
    rw [← hc]
    ring
  rw [e1, Complex.ofReal_sum]
  simp only [e2, Finset.sum_mul_sum]
  exact sum_reorder5 (fun a₁ a₂ y y' c => ((ν.prob (a₁, y, c) : ℝ) : ℂ) * (f a₁ * g y) *
        (((stepZY ν a₂ c y' : ℝ) : ℂ) * (star (f a₂) * star (g y'))))

/-- THE MARKOV GLUING: the walk of `N + N` steps is a walk of `N` steps glued to an
independent walk of `N` steps (`walkYY_append`), and the first half is the reversal of a walk
started at the gluing vertex (`walkYY_reverse`); since `N` is even the alternating product of the
reversed word is the complex conjugate (`F(rev u) = conj F(u)`), hence `Q_{N+N} = ∑_y margY(y)
|R_N(y)|²`, a nonnegative real. -/
theorem k6pt_evenExpect_double (ν : FinProb (A × B × C)) {N : ℕ} (hN : Even N) (f : A → ℂ)
    (g : B → ℂ) :
    k6ptEvenExpect ν (N + N) f g = ((∑ y, margY ν y * ‖k6ptEvenR ν N f g y‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ (u v : Fin N → A) (y y' : B),
      ((margY ν y * walkYY ν (List.ofFn (Fin.append u v)) y y' : ℝ) : ℂ) *
        (k6ptAlt f (Fin.append u v) * (g y * star (g y'))) =
      ∑ m, (((margY ν y * walkYY ν (List.ofFn u) y m : ℝ) : ℂ) * (k6ptAlt f u * g y)) *
        (((walkYY ν (List.ofFn v) m y' : ℝ) : ℂ) * (k6ptAlt f v * star (g y'))) := by
    intro u v y y'
    rw [List.ofFn_fin_append, walkYY_append ν _ _ (by simpa using hN) (by simpa using hN),
      k6ptAlt_append hN, Matrix.mul_apply, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  unfold k6ptEvenExpect
  rw [← (Fin.appendEquiv N N).sum_comp, Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => hterm u v y y').trans ?_
  rw [sum_reorder5b]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine (sum_four_mul (fun (u : Fin N → A) (y : B) =>
      ((margY ν y * walkYY ν (List.ofFn u) y m : ℝ) : ℂ) * (k6ptAlt f u * g y))
    (fun (v : Fin N → A) (y' : B) =>
      ((walkYY ν (List.ofFn v) m y' : ℝ) : ℂ) * (k6ptAlt f v * star (g y')))).trans ?_
  rw [k6pt_gluing_left ν hN f g m]
  have hc : star (k6ptEvenR ν N f g m) * k6ptEvenR ν N f g m =
      ((‖k6ptEvenR ν N f g m‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
  push_cast
  rw [mul_assoc]
  exact congrArg _ hc

/-- the Cauchy-Schwarz step `|Q_N|² ≤ Q_{N+N}`. -/
theorem k6pt_evenExpect_sq_le (ν : FinProb (A × B × C)) {N : ℕ} (hN : Even N) (f : A → ℂ)
    (g : B → ℂ) (hg : ∀ b, ‖g b‖ ≤ 1) :
    ‖k6ptEvenExpect ν N f g‖ ^ 2 ≤ ‖k6ptEvenExpect ν (N + N) f g‖ := by
  have hQ : k6ptEvenExpect ν N f g =
      ipk (margY ν) (fun y => star (g y)) (k6ptEvenR ν N f g) := by
    rw [k6pt_evenExpect_eq]
    unfold ipk
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [star_star]
  have hw : ∀ y, 0 ≤ margY ν y := margY_nonneg ν
  have hcs := norm_ipk_le (margY ν) hw (fun y => star (g y)) (k6ptEvenR ν N f g)
  have hg2 : ∑ y, margY ν y * ‖star (g y)‖ ^ 2 ≤ 1 := by
    rw [← sum_margY ν]
    refine Finset.sum_le_sum fun y _ => ?_
    have h0 := norm_nonneg (g y)
    rw [norm_star]
    calc margY ν y * ‖g y‖ ^ 2 ≤ margY ν y * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 (hg y)) (hw y)
      _ = margY ν y := mul_one _
  have hR0 : 0 ≤ ∑ y, margY ν y * ‖k6ptEvenR ν N f g y‖ ^ 2 :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hw y) (sq_nonneg _)
  rw [k6pt_evenExpect_double ν hN f g, Complex.norm_real, Real.norm_of_nonneg hR0, hQ]
  calc _ ≤ _ := hcs
    _ ≤ 1 * (∑ y, margY ν y * ‖k6ptEvenR ν N f g y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hg2 hR0
    _ = _ := one_mul _

/-- the `(ℓ+1)`-step walk is the `ℓ`-step path trick with the last label and endpoint averaged into
`h̃`: `walkYY (w ++ [a]) = walkYZ w * stepZY a`, `F(w ++ [a]) = F(w) conj f(a)` for `ℓ` odd. -/
theorem k6pt_evenExpect_eq_pathTrick (ν : FinProb (A × B × C)) {ℓ : ℕ} (hℓ : Odd ℓ)
    (f : A → ℂ) (g : B → ℂ) :
    k6ptEvenExpect ν (ℓ + 1) f g =
      ∑ q : PathX ν ℓ hℓ × B × C, ((pathTrick ν ℓ hℓ).prob q : ℂ) *
        (k6ptAlt f q.1.1 * g q.2.1 * k6ptCondC ν f g q.2.2) := by
  obtain ⟨m, hm⟩ := id hℓ
  have hterm : ∀ (a : A) (w : Fin ℓ → A) (y y' : B),
      ((margY ν y * walkYY ν (List.ofFn (Fin.snoc (α := fun _ => A) w a : Fin (ℓ + 1) → A))
          y y' : ℝ) : ℂ) *
        (k6ptAlt f (Fin.snoc (α := fun _ => A) w a : Fin (ℓ + 1) → A) * (g y * star (g y'))) =
      ∑ z, ((margY ν y * walkYZ ν (List.ofFn w) y z : ℝ) : ℂ) *
        (k6ptAlt f w * g y * (((stepZY ν a z y' : ℝ) : ℂ) * (star (f a) * star (g y')))) := by
    intro a w y y'
    have hl : List.ofFn (Fin.snoc (α := fun _ => A) w a : Fin (ℓ + 1) → A) =
        List.ofFn w ++ [a] := by
      rw [List.ofFn_succ']
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    have ha : k6ptAlt f (Fin.snoc (α := fun _ => A) w a : Fin (ℓ + 1) → A) =
        k6ptAlt f w * star (f a) := by
      unfold k6ptAlt
      rw [Fin.prod_univ_castSucc]
      have h1 : ¬ ((Fin.last ℓ).val % 2 = 0) := by
        rw [Fin.val_last]
        omega
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, h1, if_false]
    rw [hl, ha, walkYY_snoc_k6 ν a m _ (by simp [hm]), Matrix.mul_apply, Finset.mul_sum,
      Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    push_cast
    ring
  unfold k6ptEvenExpect
  rw [← (Fin.snocEquiv fun _ : Fin (ℓ + 1) => A).sum_comp, Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => hterm a w y y').trans ?_
  rw [sum_reorder5c]
  refine Eq.trans ?_ (sum_pathX_k6 ν hℓ
    (fun w y z => k6ptAlt f w * g y * k6ptCondC ν f g z)).symm
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  rw [k6ptCondC_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rfl

/-- CSP_6 `eq:biginduct` for one measure: `|𝔼 f g h|^{2^r} ≤ |Q_{2^r}|`. -/
theorem k6pt_biginduct_core (ν : FinProb (A × B × C)) {r : ℕ} (hr : 1 ≤ r) (f : A → ℂ)
    (g : B → ℂ) (h : C → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1)
    (hh : ∀ c, ‖h c‖ ≤ 1) :
    ‖∑ p : A × B × C, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ^ (2 ^ r) ≤
      ‖k6ptEvenExpect ν (2 ^ r) f g‖ := by
  induction r, hr using Nat.le_induction with
  | base =>
    have h3 := (k6pt_hTilde_core ν f g h hf hg hh).2.2
    have h0 : 0 ≤ ∑ c, margZ ν c * ‖k6ptCondC ν f g c‖ ^ 2 :=
      Finset.sum_nonneg fun c _ => mul_nonneg (margZ_nonneg ν c) (sq_nonneg _)
    rw [pow_one, k6pt_evenExpect_two, Complex.norm_real, Real.norm_of_nonneg h0]
    exact h3
  | succ r hr ih =>
    have hev : Even (2 ^ r) := (Nat.even_pow' (by omega)).2 even_two
    have h2 := k6pt_evenExpect_sq_le ν hev f g hg
    have e : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
    rw [e]
    calc _ = (‖∑ p : A × B × C, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ^ (2 ^ r)) ^ 2 := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ ‖k6ptEvenExpect ν (2 ^ r) f g‖ ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
      _ ≤ _ := h2

/-- CSP_6 `lemma:pathtrick` for one measure, `ℓ = 2^r - 1`. -/
theorem k6pt_pathtrick_core (ν : FinProb (A × B × C)) {r ℓ : ℕ} (hℓ : Odd ℓ)
    (hℓt : ℓ = 2 ^ r - 1) (f : A → ℂ) (g : B → ℂ) (h : C → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1) (hh : ∀ c, ‖h c‖ ≤ 1) :
    ‖∑ p : A × B × C, (ν.prob p : ℂ) * (f p.1 * g p.2.1 * h p.2.2)‖ ^ (2 ^ r) ≤
      ‖∑ q : PathX ν ℓ hℓ × B × C, ((pathTrick ν ℓ hℓ).prob q : ℂ) *
        (k6ptAlt f q.1.1 * g q.2.1 * k6ptCondC ν f g q.2.2)‖ :=
  from_mu_to_path ν hℓ hℓt f g h hf hg hh

end K6ptCore
end TrackB
end RestrictedPolynomials
end
