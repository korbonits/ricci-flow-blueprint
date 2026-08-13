/-
The Levi-Civita connection.

Mathlib has both ingredients as of 2026-08 —
`CovariantDerivative.IsMetricCompatible` (`.../CovariantDerivative/Metric.lean`)
and `CovariantDerivative.torsion` (`.../CovariantDerivative/Torsion.lean`) —
but not the existence/uniqueness theorem.

Check `#maths` on the Lean Zulip before investing here; someone upstream is
plausibly walking toward the same result.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.Riemannian.Basic

open Bundle
open scoped Manifold ContDiff

namespace RicciFlowBlueprint

-- The tangent bundle carries its metric via `RiemannianBundle`, not via a raw
-- `[∀ x, InnerProductSpace ℝ (TangentSpace I x)]` binder: the fibers already
-- have a topology, and the raw binder creates a diamond.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

-- BENCH: koszul-uniqueness
-- The fundamental theorem of Riemannian geometry: there is exactly one
-- torsion-free covariant derivative on `TM` compatible with the metric.
-- Uniqueness is the Koszul formula; existence constructs the connection from it.
theorem exists_unique_leviCivita :
    ∃! cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
      cov.IsMetricCompatible ∧ cov.torsion = 0 := by
  sorry

end RicciFlowBlueprint
