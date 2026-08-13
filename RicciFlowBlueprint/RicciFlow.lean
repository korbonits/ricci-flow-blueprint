/-
Ricci flow on a closed manifold, and the terminal statement.

Everything here is blocked on analysis Mathlib does not have: quasilinear
parabolic systems on sections of vector bundles, elliptic regularity, and
Sobolev spaces of bundle sections. These are recorded in prose so the
dependency graph is honest about where the frontier is, not because they are
close.

* `IsRicciFlow` — a smooth family of metrics with `∂g/∂t = -2 Ric(g)`.
  Needs `Ricci.lean` unblocked first.

* Short-time existence on a closed manifold (Hamilton 1982; DeTurck 1983).
  Needs quasilinear parabolic systems on sections of vector bundles, hence
  Sobolev spaces of bundle sections and elliptic regularity. Mathlib's entire
  PDE surface is `Analysis/Distribution/Sobolev.lean` and
  `Analysis/FunctionalSpaces/SobolevInequality.lean`; none of the above exists.

* Hamilton 1982: a closed 3-manifold admitting a metric of positive Ricci
  curvature admits a metric of constant positive sectional curvature.
  Additionally needs the tensor maximum principle, the pinching estimates,
  Shi's derivative estimates, and convergence of the normalized flow.

Mathlib already carries the terminal statement of the road this sits on, in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`.
-/
import RicciFlowBlueprint.Homogeneous

namespace RicciFlowBlueprint

end RicciFlowBlueprint
