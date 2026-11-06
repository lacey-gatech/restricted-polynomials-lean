module

public import RestrictedPolynomials.Dimitrov.Graeffe
public import RestrictedPolynomials.Dimitrov.CyclotomicExclusion

/-!
# [Dim19, Lemma square], direction (ii) ⇒ (i)

Source: arXiv:1912.12545v1 `main.tex`, Lemma `square`, l. 274-319. If `P_2 = P_4` for a
monic irreducible integer polynomial of degree `> 1`, then the squares and fourth powers of its
complex roots agree, so `P` is cyclotomic.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RestrictedPolynomials

/-- [Dim19, Lemma square], direction (ii) ⇒ (i):
if `P_2 = P_4`, then `P` is cyclotomic. -/
theorem cyclotomic_of_P2_eq_P4 (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) (h : P2 P = P4 P) : ∃ N : ℕ, 0 < N ∧ P = cyclotomic N ℤ := by
  apply cyclotomic_of_roots_sq_eq_roots_four P hmon hirr hdeg
  have h2 := map_P2 P hmon
  have h4 := map_P4 P hmon
  rw [h, h4] at h2
  have := congrArg Polynomial.roots h2
  unfold ancillary at this
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this
  exact this.symm
