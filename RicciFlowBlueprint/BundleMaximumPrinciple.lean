/-
**The touching-point step of the maximum principle, on a general vector bundle.**

`ManifoldMaximumPrinciple.lean` runs the tensor maximum principle for a section of a
**trivial** bundle, where the direction `n` against which the section is tested is one and
the same vector at every point of `M` and `x ↦ ⟪n, u t x⟫` parses on the nose. Hamilton's
curvature operator is a section of `Sym²(Λ²TM)`, which is not trivial, and there `n ∈ V x₀`
only. The direction must be spread into a *section* `N` of `V`, and the scalar the principle
tests becomes `y ↦ ⟪N y, u t y⟫` — whose Laplacian then picks up corrections in `∇N` and
`ΔN`.

This file is the step that makes those corrections vanish. At a **normal** section — one
with `∇N(x) = 0` and `ΔN(x) = 0`, which `BundleNormalSection.lean` produces through any
prescribed `n ∈ V x` — the Bochner expansion of `Δ⟪N,u⟫` collapses to `⟪N x, Δu x⟫`, with
*both* remaining terms killed by `∇N(x) = 0`: the gradient pairing `∑ᵢ⟪∇_{eᵢ}N,∇_{eᵢ}u⟫`
directly, and `⟪ΔN,u⟫` by the second-order condition. So the second-derivative test at a
spatial maximum of `y ↦ ⟪N y, u y⟫` reads off as `⟪n, Δu(x)⟫ ≤ 0`, which is exactly the
hypothesis `TensorMaximumPrinciple.lean` consumes at the touching point.

**No parallel transport and no exponential map are used**, and that is the point: only the
*first and second order* behaviour of `N` at the single point `x` matters, and that is what
`NormalSection.lean` arranges by linear algebra. The radial-transport construction of a
normal frame would have put this step behind the regularity of `exp`, which is an open ODE
gap.

Three connections' worth of hypotheses appear, as in `BundleBochner.lean`: `cov` on `V`,
which must be metric, and `covT` on `TM`, which supplies the Hessian's correction term and
the trace and need be neither metric nor torsion-free. Boundarylessness of `I` enters
exactly once, through the second-derivative test.
-/
import RicciFlowBlueprint.BundleBochner
import RicciFlowBlueprint.BundleNormalSection
import RicciFlowBlueprint.SecondDerivativeTest

open Bundle Filter Module RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V]
  [IsContMDiffRiemannianBundle I 2 F V]
  [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 2 F V I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]
  (covT : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [IsContMDiffRiemannianBundle I 2 F V]
  [ContMDiffVectorBundle 2 F V I] in
-- BENCH: bundle-laplacian-normal
/-- **The Bochner expansion collapses at a normal section**: if `∇N(x) = 0` and `ΔN(x) = 0`
then `Δ⟪N,u⟫(x) = ⟪N x, Δu(x)⟫`.

Both correction terms die on `∇N(x) = 0` alone — the gradient pairing because each summand
carries a factor `∇_{eᵢ}N(x)`, and `⟪ΔN,u⟫` because `ΔN(x) = 0` is what
`BundleNormalSection.lean` arranges on top of it at no cost to the first-order condition. -/
theorem laplacianFun_inner_normal_eq (hmet : cov.IsMetricCompatible)
    {N u : Π y : M, V y} {x : M} (hN : CMDiff 2 (T% N)) (hu : CMDiff 2 (T% u))
    (hNc : cov N x = 0) (hNl : cov.laplacianSection covT hN x = 0) :
    covT.laplacianFun (fun y ↦ ⟪N y, u y⟫) x = ⟪N x, cov.laplacianSection covT hu x⟫ := by
  rw [cov.laplacianFun_inner_section_eq covT hmet hN hu, hNl, hNc]
  simp

omit [T2Space M] [ContMDiffVectorBundle 2 F V I] in
-- BENCH: bundle-touching-point-max
/-- **The touching-point inequality**: at a spatial *maximum* of `y ↦ ⟪N y, u y⟫` for a
normal `N`, `⟪N x, Δu(x)⟫ ≤ 0`.

This is the step the tensor maximum principle applies at the first time the solution touches
the boundary of the invariant set. Everything about the bundle is already discharged by
`laplacianFun_inner_normal_eq`; what remains is the scalar second-derivative test. -/
theorem inner_laplacianSection_nonpos_of_isLocalMax (hmet : cov.IsMetricCompatible)
    {N u : Π y : M, V y} {x : M} (hN : CMDiff 2 (T% N)) (hu : CMDiff 2 (T% u))
    (hNc : cov N x = 0) (hNl : cov.laplacianSection covT hN x = 0)
    (hmax : IsLocalMax (fun y ↦ ⟪N y, u y⟫) x) :
    ⟪N x, cov.laplacianSection covT hu x⟫ ≤ 0 := by
  rw [← cov.laplacianFun_inner_normal_eq covT hmet hN hu hNc hNl]
  exact laplacianFun_nonpos_of_isLocalMax covT ((hN x).inner_bundle (hu x)) hmax

omit [T2Space M] [ContMDiffVectorBundle 2 F V I] in
/-- The mirror statement at a spatial *minimum*. -/
theorem inner_laplacianSection_nonneg_of_isLocalMin (hmet : cov.IsMetricCompatible)
    {N u : Π y : M, V y} {x : M} (hN : CMDiff 2 (T% N)) (hu : CMDiff 2 (T% u))
    (hNc : cov N x = 0) (hNl : cov.laplacianSection covT hN x = 0)
    (hmin : IsLocalMin (fun y ↦ ⟪N y, u y⟫) x) :
    0 ≤ ⟪N x, cov.laplacianSection covT hu x⟫ := by
  rw [← cov.laplacianFun_inner_normal_eq covT hmet hN hu hNc hNl]
  exact laplacianFun_nonneg_of_isLocalMin covT ((hN x).inner_bundle (hu x)) hmin

-- BENCH: bundle-touching-point-exists
/-- **The touching-point step, packaged**: for every direction `n ∈ V x` there is a global
`C²` section `N` through `n` whose associated scalar `y ↦ ⟪N y, u y⟫` tests `Δu` honestly —
a spatial maximum of it at `x` forces `⟪n, Δu(x)⟫ ≤ 0`.

The direction is a vector in **one fibre** and the conclusion is about that vector; the
section is an artefact of the proof, which is why it is bound existentially here. This is
the form a maximum principle on a non-trivial bundle consumes. -/
theorem exists_section_inner_laplacianSection_nonpos (hmet : cov.IsMetricCompatible)
    {u : Π y : M, V y} (hu : CMDiff 2 (T% u)) {x : M} (n : V x) :
    ∃ (N : Π y : M, V y) (_ : CMDiff 2 (T% N)), N x = n ∧
      (IsLocalMax (fun y ↦ ⟪N y, u y⟫) x → ⟪n, cov.laplacianSection covT hu x⟫ ≤ 0) := by
  obtain ⟨N, hN, hNx, hNc, hNl⟩ := cov.exists_contMDiff_section_normal_of_bundle covT n
  refine ⟨N, hN, hNx, fun hmax ↦ ?_⟩
  rw [← hNx]
  exact cov.inner_laplacianSection_nonpos_of_isLocalMax covT hmet hN hu hNc hNl hmax

section Tangent

/-! ### The tangent bundle is a case of this file

The general statements above have no other instantiation, and an unfalsified general
theorem is a liability. Specialising to `V = TM`, where the fibre metric is the Riemannian
metric itself, is the check that they say what they are meant to say. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

variable {N u : Π y : M, TangentSpace I y} {x : M}

omit [CompleteSpace E] [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- The collapse at a normal vector field, for the tangent bundle. -/
theorem laplacianFun_inner_normal_eq_tangent
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hN : CMDiff 2 (T% N)) (hu : CMDiff 2 (T% u))
    (hNc : cov N x = 0) (hNl : cov.laplacian hN x = 0) :
    cov.laplacianFun (fun y ↦ ⟪N y, u y⟫) x = ⟪N x, cov.laplacian hu x⟫ :=
  cov.laplacianFun_inner_normal_eq cov hmet hN hu hNc hNl

omit [T2Space M] in
/-- The touching-point inequality for the tangent bundle. -/
theorem inner_laplacian_nonpos_of_isLocalMax_tangent
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hN : CMDiff 2 (T% N)) (hu : CMDiff 2 (T% u))
    (hNc : cov N x = 0) (hNl : cov.laplacian hN x = 0)
    (hmax : IsLocalMax (fun y ↦ ⟪N y, u y⟫) x) :
    ⟪N x, cov.laplacian hu x⟫ ≤ 0 :=
  cov.inner_laplacianSection_nonpos_of_isLocalMax cov hmet hN hu hNc hNl hmax

end Tangent

end CovariantDerivative
