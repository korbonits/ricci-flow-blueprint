/-
**`HasParallelTransport` is not vacuous: the tangent bundle satisfies it.**

`GeodesicSecondDerivative.lean` carries parallel transport along curves as a *predicate*,
because this repo builds it on the tangent bundle (`ParallelTransportGlobal.lean`) and on
`End(TM)` (`EndTransport.lean`) but not yet for an arbitrary bundle. A predicate with no
instantiation asserts nothing, so this file supplies one.

**The only work is the shape of the initial condition.** `HasParallelTransport` states it as
one equation in the total space --- `⟨γ t₀, N t₀⟩ = ⟨x, n⟩` --- so that a use site with a
curve through a *named* point needs no dependent-type cast, the device `IsGeodesicRun.init`
uses. The tangent-bundle transport theorem states it as `V t₀ = v` in the fibre over `γ t₀`,
so the bridge is one `subst` and one `rw`, done here once rather than at every use.
-/
import RicciFlowBlueprint.GeodesicSecondDerivative
import RicciFlowBlueprint.ParallelTransportGlobal

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **The tangent bundle admits parallel transport along curves.**

`ParallelTransportGlobal.lean`'s `exists_isParallelAlong_global` restated in the total-space
form the geodesic argument consumes. Everything substantial is there; the `subst` is what
turns "through `n` in the fibre over `γ t₀`" into "through `n` in the fibre over a named `x`",
and the bridge between `MDiffAlongAt`/`IsParallelAlong` and their section forms is `rfl` for
the first and `isParallelAlongSection_iff_isParallelAlong` for the second.

**No metric compatibility is needed** --- transport exists for any connection; it is an
*isometry* only for a metric one, and that is a different statement
(`TransportIsometry.lean`). -/
theorem hasParallelTransport_tangent :
    HasParallelTransport I E (fun (x : M) ↦ TangentSpace I x) cov := by
  intro γ s hs hconn hγ hγv t₀ ht₀ x n hx
  subst hx
  obtain ⟨W, hW0, hWd, hWp⟩ := exists_isParallelAlong_global cov hs hconn hγ hγv ht₀ n
  refine ⟨W, ?_, hWd, ?_⟩
  · rw [hW0]
  · exact (isParallelAlongSection_iff_isParallelAlong cov hγ hWd).mpr hWp

end CovariantDerivative
