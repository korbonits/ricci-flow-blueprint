/-
The second covariant derivative and the Laplacian.

`∇²_{X,Y} Z = ∇_X (∇_Y Z) - ∇_{∇_X Y} Z` is the Hessian of a section; its
antisymmetric part is the curvature (the Ricci identity), and for a function
`∇²f(X, Y) = X(Yf) - (∇_X Y)f` is symmetric when the connection is torsion-free.
The Laplacian is the metric trace of the Hessian. These are the objects the
evolution equations of Ricci flow are written in (`lem:evolution-rm`), and the
Laplacian is what supplies the differential inequality at a minimum that the
abstract maximum principle (`MaximumPrinciple.lean`) takes as its hypothesis.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Curvature
import RicciFlowBlueprint.LieBracketDerivation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Bundle VectorField
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- The **second covariant derivative** of a vector field:
`∇²_{X,Y} Z = ∇_X (∇_Y Z) - ∇_{∇_X Y} Z`. -/
noncomputable def hessian (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  cov (fun y ↦ cov Z y (Y y)) x (X x) - cov Z x (cov Y x (X x))

-- BENCH: ricci-identity
/-- **The Ricci identity**: for a torsion-free connection the antisymmetric part of the
second covariant derivative is the curvature, `∇²_{X,Y} Z - ∇²_{Y,X} Z = R(X,Y) Z`. -/
theorem hessian_sub_hessian_swap (hcov : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.hessian X Y Z x - cov.hessian Y X Z x = cov.curvature X Y Z x := by
  have h := (torsion_eq_zero_iff cov).mp hcov hX hY
  simp only [hessian, curvature]
  rw [← h, map_sub]
  abel

/-- The **Hessian of a function**: `∇²f(X, Y) = X(Yf) - (∇_X Y) f`. -/
noncomputable def hessianFun (f : M → ℝ) (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ mvfderiv I f y (Y y)) x (X x) - mvfderiv I f x (cov Y x (X x))

-- BENCH: hessian-symm
/-- **The Hessian of a function is symmetric** for a torsion-free connection: the
antisymmetric part is `[X,Y]f - (∇_X Y - ∇_Y X) f = 0`. -/
theorem hessianFun_symm (hcov : cov.torsion = 0) {f : M → ℝ}
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.hessianFun f X Y x = cov.hessianFun f Y X x := by
  have h := (torsion_eq_zero_iff cov).mp hcov hX hY
  have key := VectorField.mlieBracket_apply_fun hf hX hY
  rw [← h, map_sub] at key
  simp only [hessianFun]
  linarith

section Tensorial

variable [ContMDiffCovariantDerivative cov 1]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- `∇²_{X,Y} Z` is pointwise linear in `X`. -/
theorem hessian_smul_left {f : M → ℝ} {X Y Z : Π y : M, TangentSpace I y} {x : M} :
    cov.hessian (f • X) Y Z x = f x • cov.hessian X Y Z x := by
  simp [hessian, smul_sub]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
theorem hessian_add_left {X X' Y Z : Π y : M, TangentSpace I y} {x : M} :
    cov.hessian (X + X') Y Z x = cov.hessian X Y Z x + cov.hessian X' Y Z x := by
  simp only [hessian, Pi.add_apply, map_add]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇²_{X,Y} Z` is tensorial in `Y`: the `X(f)` terms of the Leibniz rule cancel between
`∇_X (f ∇_Y Z)` and `∇_{∇_X (fY)} Z`. -/
theorem hessian_smul_right {f : M → ℝ} {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) :
    cov.hessian X (f • Y) Z x = f x • cov.hessian X Y Z x := by
  have hsec : (fun y ↦ cov Z y ((f • Y) y)) = f • (fun y ↦ cov Z y (Y y)) := by
    funext y
    simp
  simp only [hessian]
  rw [hsec, cov.isCovariantDerivativeOn.leibniz (cov.mdiffAt_cov_apply hZ hY) hf,
    cov.isCovariantDerivativeOn.leibniz hY hf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem hessian_add_right {X Y Y' Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    cov.hessian X (Y + Y') Z x = cov.hessian X Y Z x + cov.hessian X Y' Z x := by
  have hsec : (fun y ↦ cov Z y ((Y + Y') y)) =
      (fun y ↦ cov Z y (Y y)) + (fun y ↦ cov Z y (Y' y)) := by
    funext y
    simp
  simp only [hessian]
  rw [hsec, cov.isCovariantDerivativeOn.add (cov.mdiffAt_cov_apply hZ hY)
    (cov.mdiffAt_cov_apply hZ hY'), cov.isCovariantDerivativeOn.add hY hY']
  simp only [add_apply, map_add]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
theorem tensorialAt_hessian_fst (Y Z : Π y : M, TangentSpace I y) (x : M) :
    TensorialAt I E (fun X ↦ cov.hessian X Y Z x) x where
  smul _ _ := cov.hessian_smul_left
  add _ _ := cov.hessian_add_left

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem tensorialAt_hessian_snd {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z))
    (X : Π y : M, TangentSpace I y) (x : M) :
    TensorialAt I E (fun Y ↦ cov.hessian X Y Z x) x where
  smul hf hσ := cov.hessian_smul_right hZ hf hσ
  add hσ hσ' := cov.hessian_add_right hZ hσ hσ'

/-- The Hessian of a `C²` vector field at `x`, as a bilinear map on `T_xM`. -/
noncomputable def hessianAt {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z)) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂ (fun X Y ↦ cov.hessian X Y Z x) x
    (fun Y _ ↦ cov.tensorialAt_hessian_fst Y Z x)
    (fun X _ ↦ cov.tensorialAt_hessian_snd hZ X x)

omit [CompleteSpace E] in
theorem hessianAt_apply {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z))
    {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.hessianAt hZ x (X x) (Y x) = cov.hessian X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

end Tensorial

end CovariantDerivative

section OrthonormalTrace

open scoped RealInnerProductSpace

/-- The sum `∑ᵢ B(bᵢ, bᵢ)` of a bilinear map over an orthonormal basis does not depend on the
basis: it is the metric trace of `B`. -/
theorem OrthonormalBasis.sum_apply_self_eq {F G : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ F) (c : OrthonormalBasis κ ℝ F) (B : F →L[ℝ] F →L[ℝ] G) :
    ∑ i, B (b i) (b i) = ∑ j, B (c j) (c j) := by
  classical
  have hc := orthonormal_iff_ite.mp c.orthonormal
  calc ∑ i, B (b i) (b i)
      = ∑ i, B (∑ j, ⟪c j, b i⟫ • c j) (∑ k, ⟪c k, b i⟫ • c k) := by
        simp_rw [c.sum_repr']
    _ = ∑ i, ∑ j, ∑ k, (⟪c j, b i⟫ * ⟪c k, b i⟫) • B (c j) (c k) := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        rw [mul_comm]
    _ = ∑ j, ∑ k, (∑ i, ⟪c j, b i⟫ * ⟪c k, b i⟫) • B (c j) (c k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.sum_smul]
    _ = ∑ j, ∑ k, ⟪c j, c k⟫ • B (c j) (c k) := by
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        congr 1
        rw [← b.sum_inner_mul_inner (c j) (c k)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [real_inner_comm (c k) (b i)]
    _ = ∑ j, B (c j) (c j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp [hc]

end OrthonormalTrace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

/-- The **rough Laplacian** of a `C²` vector field: the metric trace of its Hessian,
`ΔZ = ∑ᵢ ∇²_{eᵢ,eᵢ} Z` over an orthonormal basis of `T_xM`. -/
noncomputable def laplacian {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z)) (x : M) :
    TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.hessianAt hZ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

/-- The **Laplacian of a function**: `Δf = ∑ᵢ ∇²f(eᵢ, eᵢ)` over an orthonormal basis of `T_xM`,
each `eᵢ` extended to a local section by `FiberBundle.extend`. -/
noncomputable def laplacianFun (f : M → ℝ) (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.hessianFun f (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
    (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) x

omit [CompleteSpace E] in
/-- The Laplacian is the trace of the Hessian over any orthonormal basis. -/
theorem laplacian_eq_sum {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z)) {x : M}
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.laplacian hZ x = ∑ i, cov.hessianAt hZ x (b i) (b i) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  exact OrthonormalBasis.sum_apply_self_eq _ b _

end CovariantDerivative
