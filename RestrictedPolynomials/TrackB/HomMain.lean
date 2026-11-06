module

public import RestrictedPolynomials.TrackB.HomBridge
public import RestrictedPolynomials.TrackB.HomIterate
public import RestrictedPolynomials.TrackB.S9ReduceBeta
public import RestrictedPolynomials.TrackB.S9DeltaInductive
public import RestrictedPolynomials.TrackB.AppBTrunc3

/-!
# Track B: the homogeneous theorems, Thm 7.14 and Thm 7.14′

Paper IV: Thm 7.14 (`thm:nonembed_homogenous`, l. 4464-4470), its proof
(Section 9.4, l. 5936-5960, on top of Lemma 8.12 and Lemma 9.3), and Thm 7.14′
(`thm:nonembed_homogenous'`, l. 4337-4345) by the reduction `β′ ≤ β` (l. 4473-4483). At the trivial
embedding group with the hypotheses `Rel67`, `RelaxedBaseCase` (Supplement E).

The theorems are UNCONDITIONAL: `nonembed_homogenous : HomStmt` and
`nonembed_homogenous_prime : HomPStmt`. Their only inputs are the Section 8 and Section 9 theorems
`s9_beta_bound_iterated_stopping` and `s9d_delta_inductive` (called, never hypotheses), the bridge
of `HomBridge` and the constants of `HomIterate`. No hypothesis `hocc` is added anywhere: it is derived from
`Rel67.inT` (`hom_hocc_x_of_pc3`).

Status: `S9ReduceBeta` (Section 8) and `S9DeltaInductive` (Section 9) are BUILT; the proof uses only
`d' ≤ 2e'`, `e' ≤ e ≤ n'`, `n' ≤ L d` and the `β` inequality from the stopping lemma. 
Formalization choices: the quantifier shape of the conclusion is `HomStmt` (constants
`(crb, Crb)` before `(ξ, c)`, `ξ < 1`); the parameter order is that of `HomIterate`; the `d' = 0` case
is the trivial bound `β ≤ 1` (Lemma 9.3 needs `1 ≤ d'`); the transport is that of `HomBridge`; the
trivial master embedding is used for the Section 8 statements.
-/

@[expose] public section

open Finset
open scoped ENNReal
noncomputable section
namespace RestrictedPolynomials
namespace TrackB

open MaxT

section Main

/-- Thm 7.14 (paper IV `thm:nonembed-homogenous`, `cc` form, `β`), exponent `1 - √ξ`, at `H = {0}`:
for every `m, K, (crb, Crb), α` there are `ξ ∈ (0, 1)` and `c > 0` such that for every `ν` with the
hypotheses of Thm 6.7′ (`Rel67`, `RelaxedBaseCase`), every choice of the Section-7 bases and every
`n ≥ d ≥ d'` with `d' ≥ d^{1-ξ}`: `β_{n,d,d'} ≤ (1 + c)^{-d'^{1-√ξ}}`.

Route. `(L, ε)` from `s9_beta_bound_iterated_stopping m hα` (they depend on `(m, α)` only), `C'` from
`s9d_delta_inductive m hα (c := crb) (C := Crb)` (it depends on `(crb, Crb)`), then
`(ξ, c)` from `hom_constants L ε C'`. For a setting: `hocc` and the positivity of the marginals
from `ν`'s `InT`, `hind` from `Rel67.yz_unif` (`s8_hind_of_uniform`), the trivial master
embedding `Hs := fun _ : Fin 1 => Unit` (built `trivial_master_embedding`, `hom_uniform_law_of_subsingleton`)
and the transported bases (`S7ModestBasis.congrTrivial`, `s7Beta_congrTrivial`). Case 1 of
the stopping lemma is `hom_constants` (1). Case 2: the built `s7_beta_le_deltaParam` (`#beta-at-most-delta`), then
`hom_delta_decay_of_step` with `hstep` from `s9d_delta_inductive` at `H := Unit`, then
`hom_constants` (2). `d' = 0`: `s7_beta_le_one`. -/
theorem nonembed_homogenous : HomStmt := by
  intro m K crb Crb α hα hcrb hCrb
  obtain ⟨L, ε, hL, hε, hε1, hit⟩ := s9_beta_bound_iterated_stopping m hα
  obtain ⟨C', hC', hdel⟩ := s9d_delta_inductive m hα hcrb hCrb
  obtain ⟨ξ, c, hξ0, hξ1, hc, hP1, hP2⟩ := hom_constants hL hε hε1 hC'
  refine ⟨ξ, c, hξ0, hξ1, hc, ?_⟩
  intro X Y Z _ _ _ _ _ _ hX hY hZ ν Sg Sm Phi' hR hRB hν Bx By Bz n d d' hdn hd'd hdd'
  have hT : InT ν.support := hR.inT
  have hocc := hom_hocc_x_of_pc3 hT.1
  obtain ⟨hpx, hpy, hpz⟩ := hom_marginals_pos_of_pc3 ν hT.1
  have hind := s8_hind_of_uniform ν hR.yz_unif
  obtain ⟨hM, hsat, -⟩ := trivial_master_embedding ν hT.2
  have e1 := fun n d d' => s7Beta_congrTrivial ν hν Bx By Bz
    (fun _ _ => (0 : Unit) : X → ∀ i : Fin 1, Unit) (fun _ _ => (0 : Unit) : Y → ∀ i : Fin 1, Unit)
    (fun _ _ => (0 : Unit) : Z → ∀ i : Fin 1, Unit) n d d'
  have hit' := hit ξ hξ0 X Y Z hX hY hZ ν hR.atoms hT.1 hR.yz_unif hν hpx hpy hpz
    (fun _ : Fin 1 => Unit) _ _ _ hM hsat
    (fun a b c => hom_uniform_law_of_subsingleton ν
      (fun _ _ => (0 : Unit) : X → ∀ i : Fin 1, Unit) (fun _ _ => (0 : Unit) : Y → ∀ i : Fin 1, Unit)
      (fun _ _ => (0 : Unit) : Z → ∀ i : Fin 1, Unit) a b c) Sm
    (fun _ _ _ _ => Subsingleton.elim _ _) (Bx.congrTrivial _) (By.congrTrivial _)
    (Bz.congrTrivial _) n d d' hd'd hdn hdd'
  rcases hit' with h1 | ⟨e, e', n', h2e, hed, hd'e', he'd', he'e, hen', hn', hLd, hle⟩
  · rw [e1] at h1
    exact h1.trans (ENNReal.ofReal_le_ofReal (hP1 d'))
  · by_cases hd0 : d' = 0
    · subst hd0
      have hone : s7Beta ν hν Bx.u By.u Bz.u n d 0 ≤ 1 :=
        s7_beta_le_one ν hν hind _ _ _ n d 0
      refine hone.trans ?_
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa using hP1 0)
    · have hd1 : 1 ≤ d' := Nat.one_le_iff_ne_zero.2 hd0
      calc s7Beta ν hν Bx.u By.u Bz.u n d d' = s7Beta ν hν (Bx.congrTrivial _).u
            (By.congrTrivial _).u (Bz.congrTrivial _).u n d d' := (e1 n d d').symm
        _ ≤ s7Beta ν hν (Bx.congrTrivial _).u (By.congrTrivial _).u (Bz.congrTrivial _).u n' e e' :=
            hle
        _ = s7Beta ν hν Bx.u By.u Bz.u n' e e' := e1 n' e e'
        _ ≤ s7DeltaParam ν hν Bx.u n' e' := s7_beta_le_deltaParam ν hν _ _ _ n' e e'
        _ ≤ ENNReal.ofReal ((1 - 1 / (4 * L * (d : ℝ) ^ ξ) ^ C') ^ (e' / 2 + 1)) :=
            hom_delta_decay_of_step (fun n d' => s7DeltaParam ν hν Bx.u n d') hL hC' hξ0
              (fun n d' => s7_deltaParam_le_one ν hν hind Bx.u n d')
              (fun A hA n d'' h1 h2 h3 => hdel A hA n d'' h1 h2 h3 X Y Z hX hY hZ ν hR.atoms hν hocc
                hR.yz_unif Unit (fun _ => ()) Sm (fun _ _ _ _ => rfl) hRB Bx)
              hd1 hd'd hdd' hd'e' he'e hen' hn'
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hP2 d d' e' hd1 hd'd hdd' hd'e')

/-- Thm 7.14′ (paper IV `thm:nonembed-homogenous-`, `β′`, x-functions): from Thm 7.14 by the built
`appB_homPAt_of_homAt` (the reduction `β′ ≤ β`, l. 4473-4483, `s7_betaP_le_beta`;
`#transfer-via-W`). This is the `hhomP` of the producer `maxT_thm_6_7_prime_of_hhomP`. -/
theorem nonembed_homogenous_prime : HomPStmt :=
  appB_homP_of_hom nonembed_homogenous

end Main

end TrackB
end RestrictedPolynomials
end
