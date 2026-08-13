/-
The beachhead: Ricci flow on left-invariant metrics.

On a Lie group, a left-invariant metric is determined by an inner product on
the Lie algebra, so `∂g/∂t = -2 Ric(g)` becomes an ODE on a finite-dimensional
space. Mathlib already has ODE existence and uniqueness
(`Mathlib/Analysis/ODE/PicardLindelof.lean`, `Mathlib/Geometry/Manifold/IntegralCurve/`),
so this branch needs no PDE theory at all — it is the part of the blueprint
that can actually be closed.

Nothing here is a benchmark task yet: a task must be a real statement with a
real proof, and these are still prose. The plan is to phrase them over an
abstract `ric : InnerProductSpace ℝ 𝔤 → (𝔤 →L[ℝ] 𝔤)` so the branch can be
developed *before* `Ricci.lean` is unblocked, then instantiate `ric` with the
genuine Ricci endomorphism.

TODO:
* `ricciFlow_leftInvariant_isODE` — the normalized flow is a locally Lipschitz
  vector field on the space of inner products on `𝔤`.
* `ricciFlow_leftInvariant_exists_unique` — unique maximal solution, by
  Picard–Lindelöf.
-/
import RicciFlowBlueprint.Ricci

namespace RicciFlowBlueprint

end RicciFlowBlueprint
