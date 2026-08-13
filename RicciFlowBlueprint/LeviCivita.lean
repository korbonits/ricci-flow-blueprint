/-
The Levi-Civita connection.

Mathlib has the two ingredients as of 2026-08 —
`CovariantDerivative/Metric.lean` (metric compatibility) and
`CovariantDerivative/Torsion.lean` — but not the existence/uniqueness theorem.
Check `#maths` on the Lean Zulip before investing here; someone upstream is
plausibly walking toward the same result.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.Riemannian.Basic

namespace RicciFlowBlueprint

-- BENCH: koszul-uniqueness
-- There is exactly one torsion-free covariant derivative compatible with a
-- given Riemannian metric. Uniqueness is the Koszul formula; existence
-- constructs the connection from it.
theorem exists_unique_leviCivita : True := by
  sorry

end RicciFlowBlueprint
