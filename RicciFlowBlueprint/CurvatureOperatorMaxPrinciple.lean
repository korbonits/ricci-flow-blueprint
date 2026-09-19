/-
**The bundle maximum principle, applied to `Rm₃` on `End(TM)`.**
-/
import RicciFlowBlueprint.CurvatureOperatorSection
import RicciFlowBlueprint.EndMetricCompat
import RicciFlowBlueprint.BundleMaximumPrinciple

open Bundle Manifold CovariantDerivative
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

section Apply

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [I.Boundaryless]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (EndTangent I (M := M))]
  [IsContMDiffRiemannianBundle I 1 (E →L[ℝ] E) (EndTangent I (M := M))]
  [IsContMDiffRiemannianBundle I 2 (E →L[ℝ] E) (EndTangent I (M := M))]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

set_option maxSynthPendingDepth 4

/-- **The touching-point maximum principle, fed Hamilton's curvature operator.**

This is the falsification check for the whole `End(TM)` line: the general `Bundle*` layer is
stated for an arbitrary bundle, and until now the only thing it could be applied to was the
tangent bundle itself, where the `rfl`-bridges check well-typedness and nothing more. Here it
is applied to a *real tensor bundle* — with the induced connection (`HomBundle.lean`), the
Hilbert–Schmidt fibre metric (`EndBundleMetric.lean`), their compatibility
(`EndMetricCompat.lean`), the connection's smoothness (`HomBundleSmooth.lean`) and a genuine
`C²` section to run on (`CurvatureOperatorSection.lean`) all supplied.

Every hypothesis is discharged; only the Riemannian structure of `EndTangent` is left as a
binder, and `isContMDiffRiemannianBundle_endTangent` instantiates it at the metric built. -/
theorem exists_section_inner_laplacian_curvatureOperator_nonpos
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hinner : ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q)
    (x : M) (n : EndTangent I x) :
    ∃ (N : Π y : M, EndTangent I y)
      (_ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := EndTangent I (M := M)) y (N y))),
      N x = n ∧
        (IsLocalMax (fun y ↦ ⟪N y, cov.curvatureOperator y⟫) x →
          ⟪n, CovariantDerivative.laplacianSection (endTangentCov cov) cov
            (cov.contMDiff_curvatureOperator_endTangent) x⟫ ≤ 0) :=
  CovariantDerivative.exists_section_inner_laplacianSection_nonpos
    (endTangentCov cov) cov (isMetricCompatible_endTangentCov cov hmet hinner)
    (cov.contMDiff_curvatureOperator_endTangent) n

end Apply

end RicciFlowBlueprint
