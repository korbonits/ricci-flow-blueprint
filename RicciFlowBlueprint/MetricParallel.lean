/-
**The metric is parallel, and a function times the metric.**

`∇g = 0` is the definition of a metric connection rearranged, and the repo had never stated
it as a fact about `covBilin` — every use so far went through `IsMetricCompatible` directly.
Stating it is what makes the *metric itself* an input to the bilinear-form calculus:
`covBilin`, `cov2Bilin` and `laplacianBilin` all vanish on it, so a term like `scal · g`
differentiates as if `g` were a constant.

**That is what the dimension-three curvature operator needs, read with its indices down.**
`Rm₃ = scal·Id − 2 Ric♯` has the metric in it twice — once in `scal` and once in the index
raising — and the index raising is where the moving fibre metric bites
(`SharpLaplacian.lean`). The `(0,2)` form `scal·g − 2 Ric` has no index raising at all, and
this file is the part of its calculus that `Ric` does not already supply.

**Nothing here is about dimension three or about the flow.** The Leibniz rule
`∇(f·h) = df ⊗ h + f ∇h` is stated for an arbitrary bilinear form field; only its
specialisation at `h = g` collapses.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.BilinLaplacian
import RicciFlowBlueprint.Bochner
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 3

variable (I) in
/-- **The metric as a bilinear form field**, typed on `E` so that the whole `covBilin`
calculus applies to it. Declared at the `E` type for the reason `curvatureBilinFst` is: at
the `TangentSpace` type it is defeq but no later `rw` matches. -/
noncomputable def metricForm (y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] in
@[simp] theorem metricForm_apply (y : M) (v w : TangentSpace I y) :
    metricForm I y v w = ⟪v, w⟫ := rfl

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `g` is differentiable against differentiable fields: this is the Leibniz rule for the
inner product. -/
theorem isMDiffBilinAt_metricForm (x : M) :
    IsMDiffBilinAt (I := I) (metricForm I (M := M)) x := fun _ _ hU hV ↦
  MDifferentiableAt.inner_bundle' hU hV

omit [CompleteSpace E] in
-- BENCH: metric-parallel
/-- **The metric is parallel**, `∇g = 0`. Metric compatibility says the derivative of
`⟪Y,Z⟫` is `⟪∇Y,Z⟫ + ⟪Y,∇Z⟫`, and those are exactly the two corrections `∇g` subtracts. -/
theorem covBilin_metricForm (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (X : Π y : M, TangentSpace I y) {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    cov.covBilin (metricForm I) X Y Z x = 0 := by
  have h := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X hY hZ
  have h' : mvfderiv I (fun y ↦ (metricForm I (M := M) y) (Y y) (Z y)) x (X x)
      = ⟪cov Y x (X x), Z x⟫ + ⟪Y x, cov Z x (X x)⟫ := h
  rw [covBilin, h']
  show _ - ⟪cov Y x (X x), Z x⟫ - ⟪Y x, cov Z x (X x)⟫ = 0
  ring

omit [CompleteSpace E] in
/-- `∇g = 0` as a function of the base point, which is what differentiating it needs. -/
theorem covBilin_metricForm_eq_zero
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (X : Π y : M, TangentSpace I y) {Y Z : Π y : M, TangentSpace I y}
    (hY : ∀ y, MDiffAt (T% Y) y) (hZ : ∀ y, MDiffAt (T% Z) y) :
    (fun y ↦ cov.covBilin (metricForm I) X Y Z y) = fun _ ↦ (0 : ℝ) :=
  funext fun y ↦ cov.covBilin_metricForm hmet X (hY y) (hZ y)

variable [ContMDiffCovariantDerivative cov 1]

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] in
/-- `∇g = 0` is differentiable, being the zero function. -/
theorem isMDiffCovBilinAt_metricForm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {Y Z : Π y : M, TangentSpace I y} (hY : ∀ y, MDiffAt (T% Y) y)
    (hZ : ∀ y, MDiffAt (T% Z) y) (x : M) :
    cov.IsMDiffCovBilinAt (metricForm I) Y Z x := by
  intro V _
  rw [cov.covBilin_metricForm_eq_zero hmet V hY hZ]
  exact mdifferentiableAt_const

omit [CompleteSpace E] in
-- BENCH: metric-parallel-second
/-- **`∇²g = 0`.** Every one of the four terms is `∇g`: the three corrections directly, and
the leading one because it differentiates the zero function. -/
theorem cov2Bilin_metricForm (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {W X Y Z : Π y : M, TangentSpace I y} {x : M} (hW : MDiffAt (T% W) x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.cov2Bilin (metricForm I) W X Y Z x = 0 := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hYm : ∀ y, MDiffAt (T% Y) y := hY.mdifferentiable h2
  have hZm : ∀ y, MDiffAt (T% Z) y := hZ.mdifferentiable h2
  have hlead : mvfderiv I (fun y ↦ cov.covBilin (metricForm I) X Y Z y) x (W x) = 0 := by
    rw [cov.covBilin_metricForm_eq_zero hmet X hYm hZm, mvfderiv_const]
    rfl
  have hDY : MDiffAt (T% (fun z ↦ cov Y z (W z))) x := cov.mdiffAt_cov_apply hY hW
  have hDZ : MDiffAt (T% (fun z ↦ cov Z z (W z))) x := cov.mdiffAt_cov_apply hZ hW
  rw [cov2Bilin, hlead, cov.covBilin_metricForm hmet _ (hYm x) (hZm x),
    cov.covBilin_metricForm hmet _ hDY (hZm x),
    cov.covBilin_metricForm hmet _ (hYm x) hDZ]
  ring

variable [T2Space M]

omit [CompleteSpace E] in
open RicciFlowBlueprint in
-- BENCH: metric-parallel-laplacian
/-- **`Δ_g g = 0`.** The trace of a vanishing Hessian; the frame is the canonical one the
definition is written on, so no frame argument is needed. -/
theorem laplacianBilin_metricForm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.laplacianBilin (metricForm I) Y Z x = 0 := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  show cov.cov2Bilin (metricForm I) _ _ Y Z x = 0
  exact cov.cov2Bilin_metricForm hmet
    ((exists_contMDiff_two_extension
      (stdOrthonormalBasis ℝ (TangentSpace I x) i)).choose_spec.1.mdifferentiable h2 x) hY hZ

end CovariantDerivative
