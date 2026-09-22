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
import RicciFlowBlueprint.OneForm
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

section FunSmul

/-! ### A function times a bilinear form

The Leibniz rule `∇(f·h) = df ⊗ h + f ∇h` for a *varying* scalar. The repo had only the
constant case (`covBilin_smul_form`), which is all a rescaling `-2 Ric` needs; a term like
`scal · g` needs the general one. Specialised at `h = g`, where `∇g` vanishes, every
derivative of `f · g` is a derivative of `f` tensored with `g`, and the trace is `Δf · g`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov 1] [T2Space M] in
/-- **`∇(f·h) = df ⊗ h + f ∇h`**, the Leibniz rule in the form slot with a varying scalar.
The two corrections `∇h` subtracts each pick up the factor `f x`, and the Leibniz term of
the leading derivative is the tensor `df ⊗ h`. -/
theorem covBilin_fun_smul (f : M → ℝ) (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hf : MDiffAt f x) (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x) :
    cov.covBilin (fun y ↦ (f y • h y : E →L[ℝ] E →L[ℝ] ℝ)) X Y Z x
      = mvfderiv I f x (X x) * h x (Y x) (Z x) + f x * cov.covBilin h X Y Z x := by
  have hfun : (fun y ↦ (f y • h y : E →L[ℝ] E →L[ℝ] ℝ) (Y y) (Z y))
      = fun y ↦ f y * h y (Y y) (Z y) := by
    funext y; rfl
  have hd : mvfderiv I (fun y ↦ f y * h y (Y y) (Z y)) x (X x)
      = f x * mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)
        + mvfderiv I f x (X x) * h x (Y x) (Z x) := by
    rw [mvfderiv_fun_mul hf hh]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have e₁ : (f x • h x : E →L[ℝ] E →L[ℝ] ℝ) (cov Y x (X x)) (Z x)
      = f x * h x (cov Y x (X x)) (Z x) := rfl
  have e₂ : (f x • h x : E →L[ℝ] E →L[ℝ] ℝ) (Y x) (cov Z x (X x))
      = f x * h x (Y x) (cov Z x (X x)) := rfl
  simp only [covBilin, hfun]
  rw [hd, e₁, e₂]
  ring

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] [T2Space M] in
/-- **`∇(f·g) = df ⊗ g`**: the metric contributes nothing, being parallel. -/
theorem covBilin_fun_smul_metricForm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (f : M → ℝ)
    {X Y Z : Π y : M, TangentSpace I y} {x : M} (hf : MDiffAt f x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    cov.covBilin (fun y ↦ (f y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ)) X Y Z x
      = mvfderiv I f x (X x) * ⟪Y x, Z x⟫ := by
  rw [cov.covBilin_fun_smul f (metricForm I) hf (MDifferentiableAt.inner_bundle' hY hZ),
    cov.covBilin_metricForm hmet X hY hZ]
  simp

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] [T2Space M] in
/-- `∇(f·g) = df ⊗ g` as a function of the base point, which is what differentiating it
needs. -/
theorem covBilin_fun_smul_metricForm_eq
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (f : M → ℝ)
    {X Y Z : Π y : M, TangentSpace I y} (hf : ∀ y, MDiffAt f y)
    (hY : ∀ y, MDiffAt (T% Y) y) (hZ : ∀ y, MDiffAt (T% Z) y) :
    (fun y ↦ cov.covBilin (fun z ↦ (f z • metricForm I z : E →L[ℝ] E →L[ℝ] ℝ)) X Y Z y)
      = fun y ↦ mvfderiv I f y (X y) * ⟪Y y, Z y⟫ :=
  funext fun y ↦ cov.covBilin_fun_smul_metricForm hmet f (hf y) (hY y) (hZ y)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1]
  [T2Space M] in
/-- `f · g` is differentiable against differentiable fields. -/
theorem isMDiffBilinAt_fun_smul_metricForm {f : M → ℝ} {x : M} (hf : MDiffAt f x) :
    IsMDiffBilinAt (I := I) (fun y ↦ (f y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ)) x := by
  intro U V hU hV
  have : (fun y ↦ (f y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ) (U y) (V y))
      = fun y ↦ f y * ⟪U y, V y⟫ := by funext y; rfl
  rw [this]
  exact hf.mul (MDifferentiableAt.inner_bundle' hU hV)

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] [T2Space M] in
/-- `∇(f·g)` is differentiable in the base point: it is `df ⊗ g`, so what it asks of `f` is
exactly that `df` be a differentiable one-form. -/
theorem isMDiffCovBilinAt_fun_smul_metricForm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) {f : M → ℝ}
    {Y Z : Π y : M, TangentSpace I y} {x : M} (hf : ∀ y, MDiffAt f y)
    (hdf : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I f y : TangentSpace I y →L[ℝ] ℝ)) x)
    (hY : ∀ y, MDiffAt (T% Y) y) (hZ : ∀ y, MDiffAt (T% Z) y) :
    cov.IsMDiffCovBilinAt (fun y ↦ (f y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ)) Y Z x := by
  intro V hV
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  rw [cov.covBilin_fun_smul_metricForm_eq hmet f hf hY hZ]
  exact (hdf V (hV.mdifferentiable h1 x)).mul (MDifferentiableAt.inner_bundle' (hY x) (hZ x))

omit [CompleteSpace E] [T2Space M] in
-- BENCH: metric-parallel-fun-second
/-- **`∇²(f·g) = ∇²f ⊗ g`.** The leading term splits by the product rule; metric
compatibility turns the derivative of `⟪Y,Z⟫` into the two corrections in `Y` and `Z`, which
cancel against the ones `∇²` subtracts, and what is left is the Hessian of `f` times `g`. -/
theorem cov2Bilin_fun_smul_metricForm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) {f : M → ℝ}
    {W X Y Z : Π y : M, TangentSpace I y} {x : M} (hf : ∀ y, MDiffAt f y)
    (hdf : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I f y : TangentSpace I y →L[ℝ] ℝ)) x)
    (hW : MDiffAt (T% W) x) (hX : MDiffAt (T% X) x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.cov2Bilin (fun y ↦ (f y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ)) W X Y Z x
      = cov.hessianFun f W X x * ⟪Y x, Z x⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hYm : ∀ y, MDiffAt (T% Y) y := hY.mdifferentiable h2
  have hZm : ∀ y, MDiffAt (T% Z) y := hZ.mdifferentiable h2
  have hDY : MDiffAt (T% (fun z ↦ cov Y z (W z))) x := cov.mdiffAt_cov_apply hY hW
  have hDZ : MDiffAt (T% (fun z ↦ cov Z z (W z))) x := cov.mdiffAt_cov_apply hZ hW
  -- the derivative of `⟪Y,Z⟫`, read off `∇g = 0`
  have hinner : mvfderiv I (fun y ↦ (⟪Y y, Z y⟫ : ℝ)) x (W x)
      = ⟪cov Y x (W x), Z x⟫ + ⟪Y x, cov Z x (W x)⟫ := by
    have h := cov.covBilin_metricForm hmet W (hYm x) (hZm x)
    rw [covBilin] at h
    have h' : mvfderiv I (fun y ↦ (metricForm I (M := M) y) (Y y) (Z y)) x (W x)
        - ⟪cov Y x (W x), Z x⟫ - ⟪Y x, cov Z x (W x)⟫ = 0 := h
    have h'' : mvfderiv I (fun y ↦ (⟪Y y, Z y⟫ : ℝ)) x (W x)
        - ⟪cov Y x (W x), Z x⟫ - ⟪Y x, cov Z x (W x)⟫ = 0 := h'
    linarith
  -- the leading term
  have hlead : mvfderiv I (fun y ↦ cov.covBilin
        (fun z ↦ (f z • metricForm I z : E →L[ℝ] E →L[ℝ] ℝ)) X Y Z y) x (W x)
      = mvfderiv I (fun y ↦ mvfderiv I f y (X y)) x (W x) * ⟪Y x, Z x⟫
        + mvfderiv I f x (X x) * (⟪cov Y x (W x), Z x⟫ + ⟪Y x, cov Z x (W x)⟫) := by
    have hdfX : MDiffAt (fun y ↦ mvfderiv I f y (X y)) x := hdf X hX
    rw [cov.covBilin_fun_smul_metricForm_eq hmet f hf hYm hZm,
      mvfderiv_fun_mul hdfX (MDifferentiableAt.inner_bundle' (hYm x) (hZm x))]
    simp only [add_apply, smul_apply, smul_eq_mul, hinner]
    ring
  rw [cov2Bilin, hlead,
    cov.covBilin_fun_smul_metricForm hmet f (hf x) (hYm x) (hZm x),
    cov.covBilin_fun_smul_metricForm hmet f (hf x) hDY (hZm x),
    cov.covBilin_fun_smul_metricForm hmet f (hf x) (hYm x) hDZ, hessianFun]
  ring

omit [CompleteSpace E] in
-- BENCH: metric-parallel-fun-laplacian
/-- **`Δ_g(f·g) = (Δf)·g`.** Both traces are read off the same frame --- the left by
`laplacianBilin_eq_sum_frame`, the right by `laplacianFun_eq_sum_frame`, which is free
because `∇²f` *is* `∇` of the one-form `df` --- and then it is `cov2Bilin_fun_smul_metricForm`
termwise. -/
theorem laplacianBilin_fun_smul_metricForm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) {f : M → ℝ}
    {Y Z : Π y : M, TangentSpace I y} {x : M} (hf : ∀ y, MDiffAt f y)
    (hdf : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I f y : TangentSpace I y →L[ℝ] ℝ)) x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    cov.laplacianBilin (fun y ↦ (f y • metricForm I y : E →L[ℝ] E →L[ℝ] ℝ)) Y Z x
      = cov.laplacianFun f x * ⟪Y x, Z x⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr i).mdifferentiable h2 x
  rw [cov.laplacianBilin_eq_sum_frame (isMDiffBilinAt_fun_smul_metricForm (I := I) (hf x))
      (cov.isMDiffCovBilinAt_fun_smul_metricForm hmet hf hdf
        (hY.mdifferentiable h2) (hZ.mdifferentiable h2)) hY hZ hfr b hbv,
    cov.laplacianFun_eq_sum_frame hdf hfr1 b hbv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦
    cov.cov2Bilin_fun_smul_metricForm hmet hf hdf (hfr1 i) (hfr1 i) hY hZ

end FunSmul

end CovariantDerivative
