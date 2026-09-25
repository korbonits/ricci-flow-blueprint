/-
**The connection Laplacian of `Rm₃` on `End(TM)`.**

`⟪(Δ Rm₃)v, w⟫ = (Δ scal)⟪v,w⟫ − 2(Δ_g Ric)(v,w)`: the spatial half of the evolution of
`Rm₃`, stated the way the bundle maximum principle sees it --- as the Laplacian of a *section of
`End(TM)`* for the induced connection. Two bridges already proved compose into it:
`SharpLaplacian.lean` turns the Laplacian of an endomorphism field into the Laplacian of the
bilinear form it raises, and `CurvatureFormThree.lean` computes the latter for
`Rm₃♭ = scal·g − 2Ric`. What is added here is only the interface --- `⟪Rm₃ v, w⟫ = Rm₃♭(v,w)`
(`inner_curvatureOperator`) --- and the two differentiability criteria for the sum
`scal·g + (−2)Ric`.
-/
import RicciFlowBlueprint.SharpLaplacian
import RicciFlowBlueprint.CurvatureFormThree

open Bundle Filter RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

set_option maxSynthPendingDepth 4

-- BENCH: curvature-operator-laplacian
/-- **`⟪(Δ Rm₃)p, q⟫ = (Δ scal)⟪p,q⟫ − 2(Δ_g Ric)(p,q)`**, `Δ` the connection Laplacian of
`Rm₃` as a section of `End(TM)` --- what the bundle maximum principle sees. -/
theorem inner_laplacianSection_curvatureOperator_eq
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {P Q : Π y : M, TangentSpace I y} {x : M}
    (hscal : ∀ y, MDiffAt (fun z ↦ cov.scalarCurvatureAt z) y)
    (hdscal : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y : TangentSpace I y →L[ℝ] ℝ)) x)
    (hP : CMDiff 2 (T% P)) (hQ : CMDiff 2 (T% Q))
    (hRic : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y)
    (hcb : cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) P Q x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    ⟪(endCov cov).laplacianSection cov (cov.contMDiff_curvatureOperator) x (P x), Q x⟫
      = cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x * ⟪P x, Q x⟫
        - 2 * cov.laplacianBilin (fun y ↦ cov.ricciForm y) P Q x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hPm : ∀ y, MDiffAt (T% P) y := hP.mdifferentiable h2
  have hQm : ∀ y, MDiffAt (T% Q) y := hQ.mdifferentiable h2
  -- the two summands of `Rm₃♭`
  set h₁ : M → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y ↦ (cov.scalarCurvatureAt y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ) with hh₁
  set h₂ : M → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ) with hh₂
  have hsum : cov.curvatureFormThree I = fun y ↦ (h₁ y + h₂ y : E →L[ℝ] E →L[ℝ] ℝ) := rfl
  have hb₁ : IsMDiffBilinAt (I := I) h₁ x :=
    isMDiffBilinAt_fun_smul_metricForm (I := I) (hscal x)
  have hb₂ : IsMDiffBilinAt (I := I) h₂ x := cov.isMDiffBilinAt_neg_two_ricciForm hRic x
  have hbil : IsMDiffBilinAt (I := I) (cov.curvatureFormThree I) x := by
    intro U V hU hV
    rw [hsum]
    exact (hb₁ U V hU hV).add (hb₂ U V hU hV)
  have hc₁ : cov.IsMDiffCovBilinAt h₁ P Q x :=
    cov.isMDiffCovBilinAt_fun_smul_metricForm hmet hscal hdscal hPm hQm
  have hc₂ : cov.IsMDiffCovBilinAt h₂ P Q x := cov.isMDiffCovBilinAt_neg_two_ricciForm hRic hcb
  have hcov : cov.IsMDiffCovBilinAt (cov.curvatureFormThree I) P Q x := by
    intro V hV
    have hfun : (fun y ↦ cov.covBilin (cov.curvatureFormThree I) V P Q y)
        = fun y ↦ cov.covBilin h₁ V P Q y + cov.covBilin h₂ V P Q y := by
      funext y
      rw [hsum]
      exact cov.covBilin_add_form h₁ h₂
        ((hscal y).mul (MDifferentiableAt.inner_bundle' (hPm y) (hQm y)))
        (mdifferentiableAt_const.mul (hRic P Q y))
    rw [hfun]
    exact (hc₁ V hV).add (hc₂ V hV)
  rw [cov.inner_laplacianSection_eq_laplacianBilin hmet
      (fun y v w ↦ by rw [cov.inner_curvatureOperator, curvatureFormThree_apply])
      (cov.contMDiff_curvatureOperator) hbil hcov hP hQ hfr b hbv,
    cov.laplacianBilin_curvatureFormThree hmet hscal hdscal hP hQ hRic hcb hfr b hbv]

end CovariantDerivative
