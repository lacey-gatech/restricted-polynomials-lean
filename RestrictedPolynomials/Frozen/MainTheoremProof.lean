-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import RestrictedPolynomials.Frozen.MainTheorem
public import RestrictedPolynomials.Main

/-!
# Frozen statement: Theorem 1.1

The statement `MainTheorem` was fixed and approved by the author before any proof work, and has
not changed since. The proof is `RestrictedPolynomials.main_theorem_proof`, in
`RestrictedPolynomials.Main`.
-/

@[expose] public section

namespace RestrictedPolynomials

/-- **Theorem 1.1.** -/
theorem main_theorem : MainTheorem :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact RestrictedPolynomials.main_theorem_proof
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end RestrictedPolynomials
-- FROZEN_ANCHOR_SUFFIX_END
