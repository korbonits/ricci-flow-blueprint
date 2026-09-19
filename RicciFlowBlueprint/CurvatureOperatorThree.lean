/-
**Hamilton's curvature operator in dimension three, as an endomorphism field.**

In dimension three the Weyl tensor vanishes, so the whole `(0,4)` curvature tensor is carried
by the *endomorphism* `Rm₃ = scal · Id − 2 Ric♯` of `T_xM`. That is what makes the
three-dimensional pinching argument run on `End(TM)` — which now has a connection
(`HomBundle.lean`), a fibre metric (`EndBundleMetric.lean`) and their compatibility
(`EndMetricCompat.lean`) — and need no `Λ²`, whose elaboration wall is therefore not on the
critical path.

This file is the **pointwise algebra**. `sharp` turns a continuous bilinear form on a real
Hilbert space into the endomorphism representing it, by the Riesz isomorphism
(`InnerProductSpace.toDual`); `ricciSharp` and `curvatureOperator` are its instances, and
`inner_curvatureOperator` is the defining identity
`⟪Rm₃ v, w⟫ = scal·⟪v,w⟫ − 2 Ric(v,w)`.

**The dimension-three content is `CurvatureThree.lean` cashed in**, and it is cheap for the
reason recorded there: the trace identity `Ric(b_m,b_m) = ∑_n K(b_m,b_n)` plus pair symmetry
gives the diagonal, and the *same* identity read off-diagonally gives that a Ricci eigenbasis
diagonalises `Rm₃` — in dimension three `Ric(b₀,b₁)` has a single surviving summand, so the
off-diagonal curvature component *is* the off-diagonal Ricci component. **No vanishing of the
Weyl tensor is used and no four-linear expansion over a basis**; the literature's route
through the dimension-three decomposition `Rm = f(Ric)` is a genuine theorem and is not
required.

Three checks against `Pinching.lean`'s normalisation, where `λ, μ, ν` are *twice* the
sectional curvatures and `R = λ + μ + ν`: the diagonal entries are twice the sectional
curvature of the **opposite** plane (`inner_curvatureOperator_self`), the off-diagonal
entries vanish in a Ricci eigenbasis (`inner_curvatureOperator_eq_zero`, which needs neither
metric compatibility nor torsion-freeness), and the trace is `scal`
(`sum_inner_curvatureOperator_self`). On the unit `S³` the first reads `6 − 4 = 2 = 2·1`.

Gotcha: a nested `namespace CovariantDerivative` inside `namespace RicciFlowBlueprint` makes a
*different* namespace, and the symptom is an unelaborated `cov` with a metavariable binder
type far from the cause — close the outer namespace first.
-/
import RicciFlowBlueprint.CurvatureThree
import RicciFlowBlueprint.RicciSymm
import Mathlib.Analysis.InnerProductSpace.Dual

open Bundle Filter
open scoped Manifold ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace RicciFlowBlueprint

section Sharp

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- **The sharp of a bilinear form**: the endomorphism representing it in the inner product,
`⟪B♯ v, w⟫ = B v w`. -/
noncomputable def sharp (B : W →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] W :=
  ((InnerProductSpace.toDual ℝ W).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp B

@[simp]
theorem inner_sharp (B : W →L[ℝ] W →L[ℝ] ℝ) (v w : W) : ⟪sharp B v, w⟫ = B v w :=
  InnerProductSpace.toDual_symm_apply

/-- A symmetric bilinear form has a self-adjoint sharp. -/
theorem inner_sharp_comm (B : W →L[ℝ] W →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (v w : W) :
    ⟪sharp B v, w⟫ = ⟪v, sharp B w⟫ := by
  rw [inner_sharp, real_inner_comm, inner_sharp]
  exact hB v w

end Sharp

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

variable {x : M}

/-- **The Ricci endomorphism** `Ric♯`, with `⟪Ric♯ v, w⟫ = Ric(v,w)`. -/
noncomputable def ricciSharp (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : CompleteSpace (TangentSpace I x) := VectorBundle.completeSpace ℝ E ..
  sharp (cov.ricciForm x : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
@[simp]
theorem inner_ricciSharp (v w : TangentSpace I x) :
    ⟪cov.ricciSharp x v, w⟫ = cov.ricciForm x v w :=
  haveI : CompleteSpace (TangentSpace I x) := VectorBundle.completeSpace ℝ E ..
  inner_sharp _ v w

/-- **Hamilton's curvature operator in dimension three**, `scal · Id − 2 Ric♯`.

In dimension three the Weyl tensor vanishes, so the whole `(0,4)` curvature tensor is carried
by this *endomorphism* field — which is why the three-dimensional pinching argument runs on
`End(TM)` and needs no `Λ²`. Its eigenvalues are the `λ, μ, ν` of `Pinching.lean`.

Nothing in the definition is three-dimensional; only the theorems below are. -/
noncomputable def curvatureOperator (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  cov.scalarCurvatureAt x • ContinuousLinearMap.id ℝ (TangentSpace I x)
    - (2 : ℝ) • cov.ricciSharp x

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
@[simp]
theorem inner_curvatureOperator (v w : TangentSpace I x) :
    ⟪cov.curvatureOperator x v, w⟫
      = cov.scalarCurvatureAt x * ⟪v, w⟫ - 2 * cov.ricciForm x v w := by
  rw [curvatureOperator]
  rw [_root_.sub_apply, inner_sub_left, smul_apply, smul_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_smul_left,
    inner_ricciSharp]

/-- The curvature operator is self-adjoint, `Ric` being symmetric. -/
theorem inner_curvatureOperator_comm
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    (v w : TangentSpace I x) :
    ⟪cov.curvatureOperator x v, w⟫ = ⟪v, cov.curvatureOperator x w⟫ := by
  have e : ⟪v, cov.curvatureOperator x w⟫ = ⟪cov.curvatureOperator x w, v⟫ :=
    real_inner_comm _ _
  have e' : ⟪w, v⟫ = ⟪v, w⟫ := real_inner_comm _ _
  rw [e, inner_curvatureOperator, inner_curvatureOperator, e',
    cov.ricciForm_symm hmetric htor w v]

section Three

variable (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
  (htor : cov.torsion = 0) (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x))

include hmetric htor in
/-- **The diagonal of the curvature operator in dimension three is twice the sectional
curvature of the opposite plane**: `⟪Rm₃ b₀, b₀⟫ = 2 Rm(b₁,b₂,b₂,b₁)`.

This is the normalisation of `Pinching.lean`, where `λ, μ, ν` are *twice* the sectional
curvatures and `R = λ + μ + ν`. On the unit `S³` it reads `6 − 4 = 2 = 2·1`. -/
theorem inner_curvatureOperator_self :
    ⟪cov.curvatureOperator x (b 0), b 0⟫
      = 2 * cov.curvatureTensorAt (b 1) (b 2) (b 2) (b 1) := by
  have h1 : ⟪b 0, b 0⟫ = (1 : ℝ) := by
    rw [orthonormal_iff_ite.mp b.orthonormal 0 0]; simp
  rw [inner_curvatureOperator, h1, mul_one, cov.ricciForm_apply]
  exact cov.scalarCurvatureAt_sub_two_ricciAt hmetric htor b

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **In a Ricci eigenbasis the curvature operator is diagonal.** The off-diagonal entry is
`−2 Ric(b₀,b₁)` outright, the inner product term vanishing on an orthonormal basis; so the
Ricci eigenbasis diagonalises the whole operator, with no appeal to the dimension-three
decomposition of `Rm`. -/
theorem inner_curvatureOperator_eq_zero {i j : Fin 3} (hij : i ≠ j)
    (h : cov.ricciAt x (b i) (b j) = 0) :
    ⟪cov.curvatureOperator x (b i), b j⟫ = 0 := by
  have h0 : ⟪b i, b j⟫ = (0 : ℝ) := by
    rw [orthonormal_iff_ite.mp b.orthonormal i j]
    simp only [hij, ↓reduceIte]
  rw [inner_curvatureOperator, h0, cov.ricciForm_apply, h]
  ring

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **The trace of the curvature operator is the scalar curvature**, in dimension three:
`3·scal − 2·scal = scal`. This is `R = λ + μ + ν` of `Pinching.lean`, so the normalisation
of the two files agrees on the trace as well as on the diagonal. -/
theorem sum_inner_curvatureOperator_self :
    ∑ i, ⟪cov.curvatureOperator x (b i), b i⟫ = cov.scalarCurvatureAt x := by
  have hone : ∀ i, ⟪b i, b i⟫ = (1 : ℝ) := by
    intro i
    rw [orthonormal_iff_ite.mp b.orthonormal i i]; simp
  have hterm : ∀ i, ⟪cov.curvatureOperator x (b i), b i⟫
      = cov.scalarCurvatureAt x - 2 * cov.ricciAt x (b i) (b i) := by
    intro i
    rw [inner_curvatureOperator, hone i, mul_one, cov.ricciForm_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← cov.scalarCurvatureAt_eq_sum_basis b]
  simp
  ring

end Three

end CovariantDerivative
