/-
The beachhead: Ricci flow on left-invariant metrics.

On a Lie group, a left-invariant metric is determined by an inner product on
the Lie algebra, so the flow ∂g/∂t = -2 Ric(g) becomes an ODE on a
finite-dimensional space. Mathlib already has ODE existence and uniqueness
(`Mathlib/Analysis/ODE/PicardLindelof.lean`, `IntegralCurve`), so this branch
needs no PDE theory at all — it is the part of the blueprint that can actually
be closed.
-/
import RicciFlowBlueprint.Ricci

namespace RicciFlowBlueprint

-- BENCH: ricci-lie-ode
-- For a left-invariant metric on a Lie group, the Ricci endomorphism is a
-- smooth function of the metric alone, so the normalized Ricci flow is a
-- locally Lipschitz ODE on the space of inner products on the Lie algebra.
theorem ricciFlow_leftInvariant_isODE : True := by
  sorry

-- BENCH: ricci-lie-shortTime
-- Short-time existence and uniqueness for the left-invariant flow, by
-- Picard–Lindelöf. No parabolic theory required.
theorem ricciFlow_leftInvariant_exists_unique : True := by
  sorry

end RicciFlowBlueprint
