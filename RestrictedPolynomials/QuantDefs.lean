module

public import RestrictedPolynomials.MinorIdeal

/-!
# Parameters of the quantitative proof of Proposition 5.1 (Section 5.3)

* `rowsFin ℓ M` : the strictly increasing row choices `2 ≤ a_0 < ⋯ < a_{ℓ-1} ≤ M`, i.e. the
  `ℓ × ℓ` minors `Δ_1, …, Δ_t` of `A_{ℓ,M}(z)` (Lemma 5.8: these are monic).
* `dℓ ℓ = ∑_{r=1}^ℓ (r+1)^r` : the degree of the minor with rows `2, …, ℓ+1`.
* `nℓ ℓ M = ∑_{r=1}^ℓ (M-ℓ+r)^r` : the bound for the degree of every minor of `A_{ℓ,M}`.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- The strictly increasing rows `2 ≤ a_0 < ⋯ < a_{ℓ-1} ≤ M`. -/
def rowsFin (ℓ M : ℕ) : Finset (Fin ℓ → ℕ) :=
  (Fintype.piFinset fun _ => Icc 2 M).filter fun a => StrictMono a

lemma mem_rowsFin {ℓ M : ℕ} {a : Fin ℓ → ℕ} :
    a ∈ rowsFin ℓ M ↔ StrictMono a ∧ ∀ r, 2 ≤ a r ∧ a r ≤ M := by
  simp [rowsFin, Fintype.mem_piFinset, and_comm]

/-- `d_ℓ = ∑_{r=1}^ℓ (r+1)^r`. -/
def dℓ (ℓ : ℕ) : ℕ := ∑ r ∈ range ℓ, (r + 2) ^ (r + 1)

/-- `n_ℓ = ∑_{r=1}^ℓ (M-ℓ+r)^r`. -/
def nℓ (ℓ M : ℕ) : ℕ := ∑ r ∈ range ℓ, (M - ℓ + 1 + r) ^ (r + 1)

end RestrictedPolynomials

end
