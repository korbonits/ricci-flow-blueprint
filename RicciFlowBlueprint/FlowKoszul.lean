/-
Wiring the first variation of the connection into the Koszul machinery.

`CurvatureVariation.lean` delivers `∂ₜ∇` as `derivDifferenceE`, characterised by the Koszul
combination of `h = ∂ₜ g` (`inner_derivDifferenceE_eq`), and `∂ₜ Rm` as a difference of
`covEnd`s. `KoszulSecondDeriv.lean` proves, for *any* tensor with that characterisation, that
its covariant derivative satisfies the same combination one level up and that the double trace
is `div div h − tr_g(Δ_g h)`. This file connects the two:

* `covEnd_eq_covTwoTensor` --- the two `∇` of a `(1,2)`-tensor agree up to the order of the
  last two slots, which is how `∂ₜ Rm` arrives;
* `isKoszulOf_derivDifference` --- `∂ₜ∇`, flipped into `(direction, argument)` order, is
  Koszul for `h`.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureVariation
import RicciFlowBlueprint.KoszulSecondDeriv

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇` of a `(1,2)`-tensor, the two ways.** `covEnd` (used by the first variation of the
curvature) takes the tensor with its argument first and its direction second, matching
`differenceE`; `covTwoTensor` (used by the Koszul machinery) takes the direction first. So the
two agree on flipped tensors, term for term. -/
theorem covEnd_eq_covTwoTensor_flip (A : M → E →L[ℝ] E →L[ℝ] E)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    cov.covEnd A X Y Z x
      = cov.covTwoTensor (fun y ↦ ((A y).flip :
          TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)) X Y Z x := rfl

end CovariantDerivative

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

section Flow

set_option maxSynthPendingDepth 3

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- **`∂ₜ∇` as a `(1,2)`-tensor in `(direction, argument)` order.** `derivDifferenceE` takes
the section value first and the direction second, matching `differenceE`; the Koszul machinery
takes the direction first, so this is the flip. -/
noncomputable def derivDifferenceTensor
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (t₀ : ℝ)
    (y : M) : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y :=
  ((derivDifferenceE g t₀ y).flip : E →L[ℝ] E →L[ℝ] E)

omit [CompleteSpace E] in
-- BENCH: koszul-of-deriv-difference
/-- **`∂ₜ∇` is Koszul for `h = ∂ₜ g`.** `inner_derivDifferenceE_eq` states this on the
constant-in-a-trivialisation extensions of the two vectors; the `covBilin` congr lemmas
transfer it to arbitrary differentiable fields, which is the form `KoszulSecondDeriv.lean`
consumes. -/
theorem isKoszulOf_derivDifference
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    (hb : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    (leviCivitaOfMetric (g t₀)).IsKoszulOf (derivDifferenceTensor g t₀) h := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  intro P Q R hP hQ hR y
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hPy : MDiffAt (T% P) y := hP.mdifferentiable h1 y
  have hQy : MDiffAt (T% Q) y := hQ.mdifferentiable h1 y
  have hRy : MDiffAt (T% R) y := hR.mdifferentiable h1 y
  have hEP : MDiffAt (T% (FiberBundle.extend E (show TangentSpace I y from P y))) y :=
    FiberBundle.mdifferentiableAt_extend ..
  have hEQ : MDiffAt (T% (FiberBundle.extend E (show TangentSpace I y from Q y))) y :=
    FiberBundle.mdifferentiableAt_extend ..
  have hvP : (FiberBundle.extend E (show TangentSpace I y from P y) : Π z : M,
      TangentSpace I z) y = P y := FiberBundle.extend_apply_self ..
  have hvQ : (FiberBundle.extend E (show TangentSpace I y from Q y) : Π z : M,
      TangentSpace I z) y = Q y := FiberBundle.extend_apply_self ..
  have key := inner_derivDifferenceE_eq hg hcomm y (P y) (Q y) hRy
  set cov := leviCivitaOfMetric (g t₀) with hcovdef
  have e₁ : cov.covBilin h (FiberBundle.extend E (show TangentSpace I y from P y))
      (FiberBundle.extend E (show TangentSpace I y from Q y)) R y
      = cov.covBilin h P Q R y := by
    rw [cov.covBilin_congr_dir (X' := P) hvP,
      cov.covBilin_congr_snd (hb y) P hEQ hQy hRy hvQ]
  have e₂ : cov.covBilin h (FiberBundle.extend E (show TangentSpace I y from Q y)) R
      (FiberBundle.extend E (show TangentSpace I y from P y)) y
      = cov.covBilin h Q R P y := by
    rw [cov.covBilin_congr_dir (X' := Q) hvQ,
      cov.covBilin_congr_thd (hb y) Q hRy hEP hPy hvP]
  have e₃ : cov.covBilin h R (FiberBundle.extend E (show TangentSpace I y from P y))
      (FiberBundle.extend E (show TangentSpace I y from Q y)) y
      = cov.covBilin h R P Q y := by
    rw [cov.covBilin_congr_snd (hb y) R hEP hPy hEQ hvP,
      cov.covBilin_congr_thd (hb y) R hPy hEQ hQy hvQ]
  rw [← e₁, ← e₂, ← e₃]
  exact key

omit [CompleteSpace E] in
-- BENCH: variation-curvature-as-koszul-tensor
/-- **`∂ₜ Rm` in the Koszul machinery's language**: `∂ₜ Rm(X,Y)Z = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)`
with `Ȧ = ∂ₜ∇` written as a `(1,2)`-tensor in `(direction, argument)` order. This is exactly
the `Rm_A` whose double trace `sum_inner_covTwoTensor_eq` computes. -/
theorem hasDerivAt_curvatureE_covTwoTensor
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXYZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (Y y))
        x (X x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (Y y)) x (X x)) t₀)
    (hYXZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (X y))
        x (Y x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (X y)) x (Y x)) t₀) :
    HasDerivAt (fun t ↦ curvatureE (leviCivitaOfMetric (g t)) X Y Z x)
      ((leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X Y Z x
        - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y X Z x) t₀ :=
  hasDerivAt_curvatureE_leviCivitaOfMetric hg hcomm hZ hX hY hXYZ hYXZ

end Flow

end RicciFlowBlueprint
