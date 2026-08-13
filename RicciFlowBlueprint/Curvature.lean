/-
Riemann curvature of a covariant derivative.

Upstream target: `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature.lean`.
Drafted on the `riemann-curvature` branch; rebase before editing here.

Signatures below are schematic and must be reconciled against the pinned
Mathlib commit before this file builds.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

namespace RicciFlowBlueprint

open CovariantDerivative

-- BENCH: curvature-antisymm
-- The curvature operator is antisymmetric in its first two arguments:
-- R(X, Y)Z = -R(Y, X)Z.
theorem curvature_antisymm : True := by
  sorry

-- BENCH: bianchi-first
-- First Bianchi identity: for a torsion-free connection,
-- R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0.
-- Blocked upstream on the bracket-as-derivation lemma for `VectorField.mlieBracket`
-- and on Z-slot tensoriality (`TensorialAt` gives only first-order hypotheses,
-- and there is no `mkHom₃`).
theorem bianchi_first : True := by
  sorry

-- BENCH: sectional-scaling
-- Sectional curvature is invariant under rescaling of the spanning pair:
-- K(aX, bY) = K(X, Y) for nonzero a, b.
theorem sectionalCurvature_smul : True := by
  sorry

end RicciFlowBlueprint
