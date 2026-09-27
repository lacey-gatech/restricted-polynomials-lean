import RestrictedPolynomials.Defs
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Reduction to cyclic groups of prime order (Lemma 3.1)

If `S ⊆ α^k` admits a nontrivial abelian embedding into some abelian group, then it admits one
into `ℤ/qℤ` for some prime `q`.
-/

open Finset

noncomputable section

namespace RestrictedPolynomials

variable {k : ℕ} {α : Type} (S : Set (Fin k → α))

/-- Composing an abelian embedding with a group homomorphism gives an abelian embedding. -/
lemma IsAbelianEmbedding.comp {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {σ : Fin k → α → G} (hσ : IsAbelianEmbedding S σ) (φ : G →+ H) :
    IsAbelianEmbedding S fun i a => φ (σ i a) := by
  intro t ht
  rw [← map_sum, hσ t ht, map_zero]

/-- Case 1 of Lemma 3.1: an embedding into `ℤ`. -/
lemma cyclic_reduction_int (τ : Fin k → α → ℤ) (hτ : IsAbelianEmbedding S τ)
    (hnt : ∃ i a b, τ i a ≠ τ i b) :
    ∃ q : ℕ, q.Prime ∧ ∃ τ' : Fin k → α → ZMod q, IsAbelianEmbedding S τ' ∧
      ∃ i a b, τ' i a ≠ τ' i b := by
  obtain ⟨i, a, b, hab⟩ := hnt
  set D := (τ i a - τ i b).natAbs with hD
  have hD0 : 0 < D := Int.natAbs_pos.2 (sub_ne_zero.2 hab)
  obtain ⟨q, hqD, hq⟩ := Nat.exists_infinite_primes (D + 1)
  refine ⟨q, hq, fun j c => (τ j c : ZMod q), hτ.comp S (Int.castAddHom (ZMod q)), i, a, b, ?_⟩
  intro h
  simp only at h
  have h0 : ((τ i a - τ i b : ℤ) : ZMod q) = 0 := by push_cast; rw [h, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have := Nat.le_of_dvd hD0 (Int.natAbs_dvd_natAbs.2 h0)
  simp at this
  omega

/-- Case 2 of Lemma 3.1: an embedding into `ℤ/q^eℤ`. -/
lemma cyclic_reduction_primePow (q e : ℕ) (hq : q.Prime) (τ : Fin k → α → ZMod (q ^ e))
    (hτ : IsAbelianEmbedding S τ) (hnt : ∃ i a b, τ i a ≠ τ i b) :
    ∃ τ' : Fin k → α → ZMod q, IsAbelianEmbedding S τ' ∧ ∃ i a b, τ' i a ≠ τ' i b := by
  classical
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have : NeZero (q ^ e) := ⟨pow_ne_zero _ hq.ne_zero⟩
  -- integer lifts
  set t : Fin k → α → ℤ := fun i a => ((τ i a).val : ℤ) with ht
  have hcast : ∀ i a, ((t i a : ℤ) : ZMod (q ^ e)) = τ i a := fun i a => by
    simp [ht]
  have hdvd : ∀ s ∈ S, ((q : ℤ) ^ e) ∣ ∑ i, t i (s i) := by
    intro s hs
    have h := hτ s hs
    have : ((q ^ e : ℕ) : ℤ) ∣ ∑ i, t i (s i) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [hcast]
      exact h
    exact_mod_cast this
  -- the largest `v` such that `q^v` divides every difference
  let P : ℕ → Prop := fun m => ∀ i a b, ((q : ℤ) ^ m) ∣ t i a - t i b
  have hP0 : P 0 := fun _ _ _ => by simp
  have hPe : ¬ P e := by
    intro h
    obtain ⟨i, a, b, hab⟩ := hnt
    apply hab
    rw [← hcast, ← hcast, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h i a b
  set v := Nat.findGreatest P e with hv
  have hPv : P v := Nat.findGreatest_spec (Nat.zero_le e) hP0
  have hve : v ≤ e := Nat.findGreatest_le e
  have hvlt : v < e := lt_of_le_of_ne hve fun h => hPe (h ▸ hPv)
  have hPv1 : ¬ P (v + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self v) hvlt
  obtain ⟨i₁, a₁, b₁, hi₁⟩ : ∃ i a b, ¬ ((q : ℤ) ^ (v + 1)) ∣ t i a - t i b := by
    by_contra! h; exact hPv1 h
  -- the rescaled maps `φ_i(a) = (t_i(a) - t_i(a₁)) / q^v`
  set φ : Fin k → α → ℤ := fun i a => (t i a - t i a₁) / (q : ℤ) ^ v with hφ
  have hφmul : ∀ i a, (q : ℤ) ^ v * φ i a = t i a - t i a₁ := fun i a =>
    Int.mul_ediv_cancel' (hPv i a a₁)
  have hφne : ¬ (q : ℤ) ∣ φ i₁ a₁ - φ i₁ b₁ := by
    intro h
    apply hi₁
    have : t i₁ a₁ - t i₁ b₁ = (q : ℤ) ^ v * (φ i₁ a₁ - φ i₁ b₁) := by
      rw [mul_sub, hφmul, hφmul]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ h
  -- the constant `∑ᵢ tᵢ(a₁) = q^v c`
  have hcexists : ∃ c : ℤ, ∀ s ∈ S, (q : ℤ) ∣ c + ∑ i, φ i (s i) := by
    by_cases hS : ∃ s₀, s₀ ∈ S
    · obtain ⟨s₀, hs₀⟩ := hS
      have hsum : ∀ s : Fin k → α, ∑ i, t i (s i) =
          ∑ i, t i a₁ + (q : ℤ) ^ v * ∑ i, φ i (s i) := by
        intro s
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by rw [hφmul]; ring
      have hC : ((q : ℤ) ^ v) ∣ ∑ i, t i a₁ := by
        have h1 := hdvd s₀ hs₀
        rw [hsum] at h1
        have h2 : ((q : ℤ) ^ v) ∣ (q : ℤ) ^ e := pow_dvd_pow _ hve
        have := (h2.trans h1)
        exact (dvd_add_left (dvd_mul_right _ _)).1 this
      obtain ⟨c, hc⟩ := hC
      refine ⟨c, fun s hs => ?_⟩
      have h1 := hdvd s hs
      rw [hsum, hc, ← mul_add] at h1
      have h2 : ((q : ℤ) ^ v * (q : ℤ) ^ (e - v)) ∣ (q : ℤ) ^ v * (c + ∑ i, φ i (s i)) := by
        rwa [← pow_add, Nat.add_sub_cancel' hve]
      have h3 := Int.dvd_of_mul_dvd_mul_left (pow_ne_zero _ hq0) h2
      exact (dvd_pow_self (q : ℤ) (by omega)).trans h3
    · push Not at hS
      exact ⟨0, fun s hs => absurd hs (hS s)⟩
  obtain ⟨c, hc⟩ := hcexists
  refine ⟨fun i a => ((φ i a + if i = i₁ then c else 0 : ℤ) : ZMod q), ?_, i₁, a₁, b₁, ?_⟩
  · intro s hs
    have : ∑ i, ((φ i (s i) + if i = i₁ then c else 0 : ℤ) : ZMod q) =
        ((c + ∑ i, φ i (s i) : ℤ) : ZMod q) := by
      push_cast
      rw [sum_add_distrib, sum_ite_eq' univ i₁]
      simp only [mem_univ, ite_true]
      ring
    simp only
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hc s hs
  · intro h
    simp only [ite_true] at h
    apply hφne
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    push_cast at h
    linear_combination h

/-- **Lemma 3.1.** If `S` admits a nontrivial abelian embedding into some abelian group, then it
admits a nontrivial abelian embedding into `ℤ/qℤ` for some prime `q`. -/
theorem cyclic_reduction [Finite α] {G : Type} [AddCommGroup G] (σ : Fin k → α → G)
    (hσ : IsAbelianEmbedding S σ) (hnt : ∃ i a b, σ i a ≠ σ i b) :
    ∃ q : ℕ, q.Prime ∧ ∃ τ : Fin k → α → ZMod q, IsAbelianEmbedding S τ ∧
      ∃ i a b, τ i a ≠ τ i b := by
  -- pass to the finitely generated subgroup spanned by the values
  set V : Set G := Set.range fun z : Fin k × α => σ z.1 z.2 with hV
  have hVfin : V.Finite := Set.finite_range _
  have : Finite V := hVfin.to_subtype
  set H := AddSubgroup.closure V with hH
  let σ' : Fin k → α → H := fun i a => ⟨σ i a, AddSubgroup.subset_closure ⟨(i, a), rfl⟩⟩
  have hσ' : IsAbelianEmbedding S σ' := by
    intro t ht
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    exact hσ t ht
  obtain ⟨i₀, a₀, b₀, hab₀⟩ := hnt
  have hnt' : σ' i₀ a₀ ≠ σ' i₀ b₀ := fun h => hab₀ (congrArg Subtype.val h)
  -- the structure theorem
  obtain ⟨n, ι, _, pr, hpr, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod H
  have hφ : IsAbelianEmbedding S fun i a => φ (σ' i a) := hσ'.comp S φ.toAddMonoidHom
  have hne : φ (σ' i₀ a₀) ≠ φ (σ' i₀ b₀) := fun h => hnt' (φ.injective h)
  by_cases h1 : (φ (σ' i₀ a₀)).1 = (φ (σ' i₀ b₀)).1
  · -- a torsion coordinate distinguishes the two values
    have h2 : (φ (σ' i₀ a₀)).2 ≠ (φ (σ' i₀ b₀)).2 := fun h2 => hne (Prod.ext h1 h2)
    obtain ⟨j, hj⟩ : ∃ j, (φ (σ' i₀ a₀)).2 j ≠ (φ (σ' i₀ b₀)).2 j := by
      by_contra! h; exact h2 (DFinsupp.ext h)
    let ψ : (Fin n →₀ ℤ) × (DirectSum ι fun j => ZMod (pr j ^ e j)) →+ ZMod (pr j ^ e j) :=
      (DFinsupp.evalAddMonoidHom j).comp (AddMonoidHom.snd _ _)
    obtain ⟨τ', hτ', hnt''⟩ := cyclic_reduction_primePow S (pr j) (e j) (hpr j)
      (fun i a => ψ (φ (σ' i a))) (hφ.comp S ψ) ⟨i₀, a₀, b₀, hj⟩
    exact ⟨pr j, hpr j, τ', hτ', hnt''⟩
  · -- a free coordinate distinguishes the two values
    obtain ⟨m, hm⟩ : ∃ m, (φ (σ' i₀ a₀)).1 m ≠ (φ (σ' i₀ b₀)).1 m := by
      by_contra! h; exact h1 (Finsupp.ext h)
    let ψ : (Fin n →₀ ℤ) × (DirectSum ι fun j => ZMod (pr j ^ e j)) →+ ℤ :=
      (Finsupp.applyAddHom m).comp (AddMonoidHom.fst _ _)
    exact cyclic_reduction_int S (fun i a => ψ (φ (σ' i a))) (hφ.comp S ψ) ⟨i₀, a₀, b₀, hm⟩

end RestrictedPolynomials

end
