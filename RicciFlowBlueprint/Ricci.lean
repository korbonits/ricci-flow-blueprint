/-
Ricci and scalar curvature: the trace contractions of the curvature tensor.

Blocked on packaging: `Ric(Y, Z) = tr (X ↦ R(X, Y)Z)` needs the curvature
operator to descend from vector *fields* to vectors in its first slot, i.e.
first-slot tensoriality. Upstream that is blocked on `TensorialAt` supplying
only first-order (`MDiffAt`) hypotheses and on the absence of `mkHom₃`. Until
that lands, Ricci curvature cannot be defined, only described — so these are
placeholders, not benchmark tasks.
-/
import RicciFlowBlueprint.Curvature
import RicciFlowBlueprint.LeviCivita

namespace RicciFlowBlueprint

-- BLOCKED on first-slot tensoriality of `CovariantDerivative.curvature`.
-- The Ricci tensor of the Levi-Civita connection is symmetric.
-- theorem ricci_symm ...

-- BLOCKED likewise.
-- Scalar curvature is the metric trace of the Ricci tensor.
-- theorem scalarCurvature_eq_trace_ricci ...

end RicciFlowBlueprint
