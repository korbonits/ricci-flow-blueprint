/-
**The first variation of `Rm`, with the commutator term separated out.**

`KoszulSecondDeriv.lean` gives `∂ₜRm` as three antisymmetrised pairs of `∇²h`:

  `⟪∂ₜRm(X,Y)Z, W⟫ = ½[(∇²_{X,Y}h)(Z,W) − (∇²_{Y,X}h)(Z,W)]
      + ½[(∇²_{X,Z}h)(W,Y) − (∇²_{Y,Z}h)(W,X)] − ½[(∇²_{X,W}h)(Y,Z) − (∇²_{Y,W}h)(X,Z)]`.

**The three pairs are not alike, and the whole evolution equation is that asymmetry.** Only
the *first* is antisymmetrised in `∇²h`'s two **derivative** slots, so only it is a
commutator: the Ricci identity for a bilinear form collapses it to curvature terms with no
derivatives left, and under the flow — where `h = −2Ric` — those terms are quadratic in `Rm`.
The other two pairs antisymmetrise a derivative slot against an *argument* slot, which is not
a commutator at all; they keep their derivatives and become `Δ Rm`.

So this file does the cheap half of `∂ₜRm = ΔRm + Q`: it turns the first pair into curvature
and leaves the other two alone.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`, and
`cov2Bilin h W X Y Z` is `(∇²_{W,X}h)(Y,Z)`.
-/
import RicciFlowBlueprint.KoszulSecondDeriv
import RicciFlowBlueprint.RicciIdentity

open Bundle Filter Module VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

variable {h : M → E →L[ℝ] E →L[ℝ] ℝ}
  {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}

-- BENCH: first-variation-commutator
/-- **The first variation of `Rm`, with the commutator pair collapsed to curvature.**

  `⟪∂ₜRm(X,Y)Z, W⟫ = ½[−h(R(X,Y)Z,W) − h(Z,R(X,Y)W)]
      + ½[(∇²_{X,Z}h)(W,Y) − (∇²_{Y,Z}h)(W,X)] − ½[(∇²_{X,W}h)(Y,Z) − (∇²_{Y,W}h)(X,Z)]`

The first pair of `inner_curvatureOfTwoTensor_eq` is `∇²h` antisymmetrised in its two
*derivative* slots, which is exactly what `cov2Bilin_sub_swap` evaluates — so it loses its
derivatives entirely and becomes `h` applied to `Rm`. **Under the flow this is `Q`**: with
`h = −2Ric` it is `Ric` paired against `Rm`, quadratic in the curvature.

The other two pairs are untouched, and must be: they antisymmetrise a derivative slot against
an argument slot, so no commutation rule applies to them. They are what the trace step of
`BianchiDeriv.lean` turns into `Δ Rm`. -/
theorem inner_curvatureOfTwoTensor_eq_curvature
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hA : cov.IsKoszulOf A h) (hb : IsMDiffBilinAt (I := I) h x)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 2 (T% W))
    (hf2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ h y (Z y) (W y)) x)
    (hAf : ∀ P Q : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      MDiffAt (T% (fun y ↦ A y (P y) (Q y))) x)
    (hd : ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      CMDiff 2 (T% R) → MDiffAt (fun y ↦ cov.covBilin h P Q R y) x) :
    ⟪cov.covTwoTensor A X Y Z x, W x⟫ - ⟪cov.covTwoTensor A Y X Z x, W x⟫
      = (-h x (cov.curvature X Y Z x) (W x) - h x (Z x) (cov.curvature X Y W x)) / 2
        + (cov.cov2Bilin h X Z W Y x - cov.cov2Bilin h Y Z W X x) / 2
        - (cov.cov2Bilin h X W Y Z x - cov.cov2Bilin h Y W X Z x) / 2 := by
  rw [cov.inner_curvatureOfTwoTensor_eq hmet hA hX hY hZ hW hAf hd,
    cov.cov2Bilin_sub_swap htor hb (hX.of_le (by norm_num)) (hY.of_le (by norm_num)) hZ hW
      hf2 (hd Y Z W hY hZ hW) (hd X Z W hX hZ hW)]

end CovariantDerivative
