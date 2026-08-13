/-
Ricci flow on a closed manifold, and the terminal statement.

Everything in this file is blocked on analysis Mathlib does not have: quasilinear
parabolic systems on sections of vector bundles, elliptic regularity, and
Sobolev spaces of bundle sections. These are stated so the dependency graph is
honest about where the frontier is, not because they are close.
-/
import RicciFlowBlueprint.Homogeneous

namespace RicciFlowBlueprint

-- The flow itself: a smooth family of metrics with ∂g/∂t = -2 Ric(g).
def IsRicciFlow : Prop := True  -- TODO

-- BLOCKED: needs parabolic PDE. Not a benchmark task.
-- Short-time existence on a closed manifold (Hamilton 1982; DeTurck 1983).
theorem ricciFlow_shortTime_existence : True := by
  sorry

-- BLOCKED: needs the tensor maximum principle and the pinching estimates.
-- Hamilton 1982: a closed 3-manifold admitting a metric of positive Ricci
-- curvature admits a metric of constant positive sectional curvature.
theorem hamilton_positive_ricci_three_manifold : True := by
  sorry

end RicciFlowBlueprint
