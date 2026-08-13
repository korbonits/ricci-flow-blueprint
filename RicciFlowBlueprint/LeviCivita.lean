/-
The Levi-Civita connection.

UPSTREAM IN FLIGHT: mathlib4 PR #36845 (`grunweg`, opened 2026-03-19, reviewed
by `sgouezel`, `awaiting-author` since 2026-07-28) adds
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`
with the Koszul formula, uniqueness, the construction, and the proof that it is
compatible and torsion-free. Do not duplicate it — either help finish it or
build on it.

  https://github.com/leanprover-community/mathlib4/pull/36845

Consequently the statement below is NOT a benchmark task: its proof has been
public since March 2026, so it fails the contamination bar the benchmark exists
to enforce. It stays here as a blueprint node so the dependency graph is
complete.
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

-- Not a benchmark task: see the contamination note above.
-- The fundamental theorem of Riemannian geometry: there is exactly one
-- torsion-free covariant derivative on `TM` compatible with the metric.
-- Uniqueness is the Koszul formula; existence constructs the connection from it.
theorem exists_unique_leviCivita :
    ∃! cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
      cov.IsMetricCompatible ∧ cov.torsion = 0 := by
  sorry

end RicciFlowBlueprint
