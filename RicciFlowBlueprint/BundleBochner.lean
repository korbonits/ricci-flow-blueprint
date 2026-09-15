/-
**The Bochner identity for a section of a general vector bundle.**

`Bochner.lean` proves `Δ⟪σ,τ⟫ = ⟪Δσ,τ⟫ + ⟪σ,Δτ⟫ + 2∑ᵢ⟪∇_{eᵢ}σ,∇_{eᵢ}τ⟫` for vector
fields. The maximum principle for Hamilton's pinching set needs it one bundle up: the
direction `n` is spread into a section `N` of `V`, and the scalar the principle tests is
`y ↦ ⟪N y, u t y⟫`, whose Laplacian has to be expanded before the second-derivative test
can be applied to it. At a *normal* section (`∇N(x) = 0`, `ΔN(x) = 0`) the expansion
collapses to `⟪N x, Δu x⟫` — which is the whole reason `NormalSection.lean` exists.

Nothing changes in the proof. Metric compatibility is applied twice, and the Hessian's
correction `−(∇_XY)⟪σ,τ⟫` expands, again by compatibility, into exactly the two corrections
that turn the iterated derivatives into `∇²σ` and `∇²τ`. Mathlib's
`IsMetricCompatible.mvfderiv_inner_eq` is already stated for a general bundle, and the
`(V := fun y : M ↦ TangentSpace I y)` annotations that `Bochner.lean` needs against
lean4#14949 are unnecessary here — the fibre instances are binders, so there is nothing to
see through.

Two connections appear, as in `BundleHessian.lean`: `cov` on `V`, which must be metric, and
`covT` on `TM`, which supplies the correction term and the trace. `covT` is *not* required
to be metric or torsion-free.
-/
import RicciFlowBlueprint.BundleHessian
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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle 1 F V I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]
  (covT : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))


omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
-- BENCH: bundle-bochner-hessian
/-- **The Bochner identity for a bundle section, Hessian form**:
`∇²⟪σ,τ⟫(X,Y) = ⟪∇²_{X,Y}σ,τ⟫ + ⟪σ,∇²_{X,Y}τ⟫ + ⟪∇_Yσ,∇_Xτ⟫ + ⟪∇_Xσ,∇_Yτ⟫`. -/
theorem hessianFun_inner_section_eq (hmet : cov.IsMetricCompatible)
    {σ τ : Π y : M, V y} {X Y : Π y : M, TangentSpace I y} {x : M}
    (hσ : CMDiff 2 (T% σ)) (hτ : CMDiff 2 (T% τ)) (hY : MDiffAt (T% Y) x) :
    covT.hessianFun (fun y ↦ ⟪σ y, τ y⟫) X Y x
      = ⟪cov.hessianSection covT X Y σ x, τ x⟫ + ⟪σ x, cov.hessianSection covT X Y τ x⟫
        + ⟪cov σ x (Y x), cov τ x (X x)⟫ + ⟪cov σ x (X x), cov τ x (Y x)⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hσm : ∀ y, MDiffAt (T% σ) y := hσ.mdifferentiable h2
  have hτm : ∀ y, MDiffAt (T% τ) y := hτ.mdifferentiable h2
  have hDσ : MDiffAt (T% (fun y ↦ cov σ y (Y y))) x := cov.mdiffAt_cov_apply_section hσ hY
  have hDτ : MDiffAt (T% (fun y ↦ cov τ y (Y y))) x := cov.mdiffAt_cov_apply_section hτ hY
  have hinner : (fun y ↦ mvfderiv I (fun z ↦ ⟪σ z, τ z⟫) y (Y y))
      = fun y ↦ ⟪cov σ y (Y y), τ y⟫ + ⟪σ y, cov τ y (Y y)⟫ := by
    funext y
    exact hmet.mvfderiv_inner_eq Y (hσm y) (hτm y)
  have hA : MDiffAt (fun y ↦ ⟪cov σ y (Y y), τ y⟫) x :=
    MDifferentiableAt.inner_bundle hDσ (hτm x)
  have hB : MDiffAt (fun y ↦ ⟪σ y, cov τ y (Y y)⟫) x :=
    MDifferentiableAt.inner_bundle (hσm x) hDτ
  have hAX := hmet.mvfderiv_inner_eq X hDσ (hτm x)
  have hBX := hmet.mvfderiv_inner_eq X (hσm x) hDτ
  have hcorr := hmet.mvfderiv_inner_eq (fun y ↦ covT Y y (X y)) (hσm x) (hτm x)
  simp only [hessianFun, hinner, mvfderiv_fun_add hA hB, _root_.add_apply, hAX, hBX, hcorr,
    hessianSection, inner_sub_left, inner_sub_right]
  ring

omit [CompleteSpace E] in
-- BENCH: bundle-bochner-laplacian
/-- **The Bochner identity for a bundle section**:
`Δ⟪σ,τ⟫ = ⟪Δσ,τ⟫ + ⟪σ,Δτ⟫ + 2∑ᵢ⟪∇_{eᵢ}σ,∇_{eᵢ}τ⟫`. -/
theorem laplacianFun_inner_section_eq (hmet : cov.IsMetricCompatible)
    {σ τ : Π y : M, V y} {x : M} (hσ : CMDiff 2 (T% σ)) (hτ : CMDiff 2 (T% τ)) :
    covT.laplacianFun (fun y ↦ ⟪σ y, τ y⟫) x
      = ⟪cov.laplacianSection covT hσ x, τ x⟫ + ⟪σ x, cov.laplacianSection covT hτ x⟫
        + 2 * ∑ i, ⟪cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i),
            cov τ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)⟫ := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  have hfrm : ∀ i, MDiffAt (T% (FiberBundle.extend E
      (stdOrthonormalBasis ℝ (TangentSpace I x) i))) x := fun _ ↦
    FiberBundle.mdifferentiableAt_extend ..
  have hfrv : ∀ i, FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i) x
      = stdOrthonormalBasis ℝ (TangentSpace I x) i := fun _ ↦ FiberBundle.extend_apply_self ..
  have hlapσ : cov.laplacianSection covT hσ x = ∑ i, cov.hessianSection covT
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) σ x :=
    cov.laplacianSection_eq_sum_frame covT hσ hfrm _ hfrv
  have hlapτ : cov.laplacianSection covT hτ x = ∑ i, cov.hessianSection covT
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) τ x :=
    cov.laplacianSection_eq_sum_frame covT hτ hfrm _ hfrv
  rw [laplacianFun, hlapσ, hlapτ, sum_inner, inner_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cov.hessianFun_inner_section_eq covT hmet hσ hτ (hfrm i), hfrv i]
  ring

omit [CompleteSpace E] in
/-- **The Bochner identity for the squared norm of a bundle section**:
`Δ|σ|² = 2⟪Δσ,σ⟫ + 2∑ᵢ|∇_{eᵢ}σ|²`. -/
theorem laplacianFun_inner_self_section_eq (hmet : cov.IsMetricCompatible)
    {σ : Π y : M, V y} {x : M} (hσ : CMDiff 2 (T% σ)) :
    covT.laplacianFun (fun y ↦ ⟪σ y, σ y⟫) x
      = 2 * ⟪cov.laplacianSection covT hσ x, σ x⟫
        + 2 * ∑ i, ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2 := by
  rw [cov.laplacianFun_inner_section_eq covT hmet hσ hσ]
  have e : ⟪σ x, cov.laplacianSection covT hσ x⟫ = ⟪cov.laplacianSection covT hσ x, σ x⟫ :=
    real_inner_comm _ _
  rw [e]
  have e2 : ∀ i, ⟪cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i),
      cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)⟫
      = ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2 := fun i ↦
    real_inner_self_eq_norm_sq _
  simp only [e2]
  ring

omit [CompleteSpace E] in
/-- **`Δ|σ|² ≥ 2⟪Δσ,σ⟫`** for a bundle section: the gradient term is a sum of squares. -/
theorem two_mul_inner_laplacianSection_le (hmet : cov.IsMetricCompatible)
    {σ : Π y : M, V y} {x : M} (hσ : CMDiff 2 (T% σ)) :
    2 * ⟪cov.laplacianSection covT hσ x, σ x⟫
      ≤ covT.laplacianFun (fun y ↦ ⟪σ y, σ y⟫) x := by
  rw [cov.laplacianFun_inner_self_section_eq covT hmet hσ]
  have hnn : (0 : ℝ) ≤ ∑ i, ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  linarith

section Tangent

/-! ### `Bochner.lean` is the tangent-bundle case

The general identity above had, until this section, **no instantiations at all** — and an
unfalsified general theorem is a liability, not an asset. Specialising it to `V = TM` and
landing on the statement `Bochner.lean` proves independently is the check.

It only typechecks because nothing in `BundleHessian.lean` asks `V` for a norm and the
fibre metric here arrives as a `RiemannianBundle` — the same instance `Bochner.lean` uses —
rather than as a bare `NormedAddCommGroup` binder, which `T_xM` would match ambiguously
(the model space's norm and the metric's are different norms on that one type). -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

variable {σ τ : Π y : M, TangentSpace I y} {x : M}

omit [CompleteSpace E] in
/-- **The Bochner identity of `Bochner.lean`, derived from the general-bundle one.** -/
theorem laplacianFun_inner_eq_of_bundle
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hσ : CMDiff 2 (T% σ)) (hτ : CMDiff 2 (T% τ)) :
    cov.laplacianFun (fun y ↦ ⟪σ y, τ y⟫) x
      = ⟪cov.laplacian hσ x, τ x⟫ + ⟪σ x, cov.laplacian hτ x⟫
        + 2 * ∑ i, ⟪cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i),
            cov τ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)⟫ :=
  cov.laplacianFun_inner_section_eq cov hmet hσ hτ

/-- The statements really are the same one, not merely similar: this `rfl` forces the two
constants' **types** to be definitionally equal, which is the whole claim. -/
example : @laplacianFun_inner_eq_of_bundle = @laplacianFun_inner_eq := rfl

end Tangent

end CovariantDerivative
