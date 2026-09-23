/-
**The dimension-three curvature operator with its indices down, and its Laplacian.**

`CurvatureOperatorThree.lean` builds `Rm₃ = scal · Id − 2 Ric♯` as an endomorphism, which is
what Hamilton's pinching set is a set of. But `Rm₃` carries the metric *twice* --- once in
`scal` and once in the index raising --- and the index raising is where a moving fibre metric
bites (`SharpLaplacian.lean`). The `(0,2)` form

  `Rm₃♭ = scal · g − 2 Ric`

has no index raising at all, and everything it needs is now in place: `Ric`'s calculus was
already there, and `MetricParallel.lean` supplies the rest --- `∇g = 0`, the varying-scalar
Leibniz rule, and linearity of `Δ_g` in the form.

What is proved here is the **spatial** half: `Δ_g(Rm₃♭) = (Δ scal)·g − 2 Δ_g Ric`. The time
derivative is a separate matter and is *not* settled by this file: `Rm₃♭` still depends on
`g_t` through `scal` and through `g` itself, so `∂ₜ` of it produces a `∂ₜg` term, which under
the flow is `−2 Ric` and so algebraic. Assembling that is the next step.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.MetricParallel
import RicciFlowBlueprint.RicciSection

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

variable (I) in
/-- **`Rm₃♭ = scal · g − 2 Ric`**, the dimension-three curvature operator with its indices
down. Written as a sum rather than a difference so that the linearity lemmas apply on the
nose: the second summand is the *constant* multiple `(−2) • Ric`. -/
noncomputable def curvatureFormThree (y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (cov.scalarCurvatureAt y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ)
    + ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ)

omit [CompleteSpace E] in
@[simp] theorem curvatureFormThree_apply (y : M) (v w : TangentSpace I y) :
    cov.curvatureFormThree I y v w
      = cov.scalarCurvatureAt y * ⟪v, w⟫ - 2 * cov.ricciForm y v w := by
  show cov.scalarCurvatureAt y * ⟪v, w⟫ + (-2 : ℝ) * cov.ricciForm y v w = _
  ring

omit [CompleteSpace E] in
/-- `(−2) • Ric` is differentiable against differentiable fields whenever `Ric` is. -/
theorem isMDiffBilinAt_neg_two_ricciForm
    (hRic : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y) (y : M) :
    IsMDiffBilinAt (I := I) (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ)) y := by
  intro U V _ _
  have hfun : (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ) (U z) (V z))
      = fun z ↦ (-2 : ℝ) * cov.ricciForm z (U z) (V z) := by funext z; rfl
  rw [hfun]
  exact mdifferentiableAt_const.mul (hRic U V y)

omit [CompleteSpace E] in
/-- `∇((−2)·Ric)` is differentiable in the base point whenever `∇Ric` is. -/
theorem isMDiffCovBilinAt_neg_two_ricciForm
    (hRic : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y)
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hcb : cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) Y Z x) :
    cov.IsMDiffCovBilinAt
      (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ)) Y Z x := by
  intro V hV
  have hfun : (fun y ↦ cov.covBilin
        (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ)) V Y Z y)
      = fun y ↦ (-2 : ℝ) * cov.covBilin (fun z ↦ cov.ricciForm z) V Y Z y := by
    funext y
    exact cov.covBilin_smul_form _ _ (hRic Y Z y)
  rw [hfun]
  exact mdifferentiableAt_const.mul (hcb V hV)

variable [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] in
-- BENCH: curvature-form-three-laplacian
/-- **`Δ_g(scal · g − 2 Ric) = (Δ scal) · g − 2 Δ_g Ric`.**

Both summands are handled by the metric calculus: the scalar one because `∇g = 0` collapses
`∇²(f·g)` to `∇²f ⊗ g`, whose trace is `(Δf)·g` --- and that trace is free because `∇²f` *is*
`∇` of the one-form `df`, so both sides come off the same frame; the Ricci one because `Δ_g`
is linear in the form it traces.

**This is the whole spatial content of the dimension-three evolution equation.** What remains
is the time derivative, and there `Rm₃♭` picks up a `∂ₜg` term that the equation turns into a
term algebraic in `Ric` --- no new differential identity. -/
theorem laplacianBilin_curvatureFormThree
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hscal : ∀ y, MDiffAt (fun z ↦ cov.scalarCurvatureAt z) y)
    (hdscal : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y : TangentSpace I y →L[ℝ] ℝ)) x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hRic : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y)
    (hcb : cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) Y Z x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    cov.laplacianBilin (cov.curvatureFormThree I) Y Z x
      = cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x * ⟪Y x, Z x⟫
        - 2 * cov.laplacianBilin (fun y ↦ cov.ricciForm y) Y Z x := by
  unfold curvatureFormThree
  rw [
    cov.laplacianBilin_fun_smul_metricForm_add hmet _ hscal hdscal hY hZ
      (cov.isMDiffBilinAt_neg_two_ricciForm hRic)
      (cov.isMDiffCovBilinAt_neg_two_ricciForm hRic hcb) hfr b hbv,
    cov.laplacianBilin_smul_form (-2 : ℝ) _ hRic hcb]
  ring

end CovariantDerivative
