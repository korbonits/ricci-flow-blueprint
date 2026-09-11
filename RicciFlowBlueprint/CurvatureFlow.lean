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
import RicciFlowBlueprint.BianchiDeriv

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

section Flow

variable [T2Space M] [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov 2] [ContMDiffCovariantDerivative cov 3]

-- BENCH: evolution-rm
/-- **`∂ₜRm = Δ Rm + Q`.**

  `⟪∂ₜRm(X,Y)Z, W⟫ = ⟪Δ Rm(X,Y)Z, W⟫ + Q₁ + Q₂ + Ric(R(X,Y)Z,W) + Ric(Z,R(X,Y)W)`

with `Q₁`, `Q₂` the two commutator sums of the trace step. **Every term on the right is
either `Δ Rm` or quadratic in the curvature**, and the two sources of quadratic terms are
different: `Q₁ + Q₂` is what reordering the derivative slots of `∇²Rm` cost, while the two
`Ric`-against-`Rm` terms are what commuting the two derivative slots of `∇²h` cost. Neither
is bolted on; each is a commutator defect.

The two halves are joined by `covDivCurvature_eq_cov2Bilin`, which puts the trace step's
output into the `∇²Ric` language the flow side speaks. **Four `∇²Ric` terms then cancel in
pairs, and they cancel by symmetry of `Ric` alone** (`cov2Bilin_symm`, from
`ricciForm_symm`) — the flow side produces `(∇²_{X,W}Ric)(Y,Z)` where the trace step
produces `(∇²_{X,W}Ric)(Z,Y)`. That is the last thing the derivation needs, and it is free. -/
theorem inner_derivCurvature_eq_curvatureLaplacian_add
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hA : cov.IsKoszulOf A (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ)))
    (hb : IsMDiffBilinAt (I := I)
      (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ)) x)
    (hX : CMDiff 4 (T% X)) (hY : CMDiff 4 (T% Y)) (hZ : CMDiff 4 (T% Z))
    (hW : CMDiff 4 (T% W))
    (hf2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2
      (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ) (Z y) (W y)) x)
    (hAf : ∀ P Q : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      MDiffAt (T% (fun y ↦ A y (P y) (Q y))) x)
    (hd : ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      CMDiff 2 (T% R) → MDiffAt (fun y ↦ cov.covBilin
        (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ)) P Q R y) x)
    (hRic : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y)
    (hcovR : ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
      CMDiff 3 (T% R) → MDiffAt (fun y ↦ cov.covRicci P Q R y) x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hfr : ∀ i, CMDiff 4 (T% (fr i)))
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i) :
    ⟪cov.covTwoTensor A X Y Z x, W x⟫ - ⟪cov.covTwoTensor A Y X Z x, W x⟫
      = ⟪cov.curvatureLaplacian X Y Z x, W x⟫
        + ∑ i, ⟪cov.curvatureCommutator (fr i) X Y (fr i) Z x, W x⟫
        + ∑ i, ⟪cov.curvatureCommutator (fr i) Y (fr i) X Z x, W x⟫
        + cov.ricciForm x (cov.curvature X Y Z x) (W x)
        + cov.ricciForm x (Z x) (cov.curvature X Y W x) := by
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hX3 : CMDiff 3 (T% X) := hX.of_le (by norm_num)
  have hY3 : CMDiff 3 (T% Y) := hY.of_le (by norm_num)
  have hZ3 : CMDiff 3 (T% Z) := hZ.of_le (by norm_num)
  have hW3 : CMDiff 3 (T% W) := hW.of_le (by norm_num)
  -- `∇Ric` is differentiable in the `covBilin` phrasing too: the two are the same function
  have hcb : ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
      CMDiff 3 (T% R) →
      MDiffAt (fun y ↦ cov.covBilin (fun z ↦ cov.ricciForm z) P Q R y) x := by
    intro P Q R hP hQ hR
    have e : (fun y ↦ cov.covBilin (fun z ↦ cov.ricciForm z) P Q R y)
        = fun y ↦ cov.covRicci P Q R y :=
      funext fun y ↦ cov.covBilin_ricciForm_eq_covRicci hP hQ hR
    rw [e]; exact hcovR P Q R hP hQ hR
  have hsymmRic : ∀ (y : M) (v w : E), cov.ricciForm y v w = cov.ricciForm y w v :=
    fun y v w ↦ cov.ricciForm_symm (x := y) hmet htor v w
  rw [cov.inner_curvatureOfTwoTensor_eq_curvature hmet htor hA hb hX2 hY2 hZ2 hW2 hf2 hAf hd,
    cov.inner_curvatureLaplacian_eq hmet htor hX hY hZ hW hfr hs hu hx b hbv,
    cov.covDivCurvature_eq_cov2Bilin hX3 hY hZ hW (hcovR Z W Y hZ2 hW3 hY3)
      (hcovR W Z Y hW2 hZ3 hY3),
    cov.covDivCurvature_eq_cov2Bilin hY3 hX hZ hW (hcovR Z W X hZ2 hW3 hX3)
      (hcovR W Z X hW2 hZ3 hX3),
    cov.cov2Bilin_smul_form (-2 : ℝ) _ hRic (hcb Z W Y hZ2 hW3 hY3),
    cov.cov2Bilin_smul_form (-2 : ℝ) _ hRic (hcb Z W X hZ2 hW3 hX3),
    cov.cov2Bilin_smul_form (-2 : ℝ) _ hRic (hcb W Y Z hW2 hY3 hZ3),
    cov.cov2Bilin_smul_form (-2 : ℝ) _ hRic (hcb W X Z hW2 hX3 hZ3),
    cov.cov2Bilin_symm hsymmRic X W Y Z x, cov.cov2Bilin_symm hsymmRic Y W X Z x]
  have hsm1 : ((-2 : ℝ) • cov.ricciForm x : E →L[ℝ] E →L[ℝ] ℝ)
        (cov.curvature X Y Z x) (W x)
      = (-2 : ℝ) * cov.ricciForm x (cov.curvature X Y Z x) (W x) := rfl
  have hsm2 : ((-2 : ℝ) • cov.ricciForm x : E →L[ℝ] E →L[ℝ] ℝ)
        (Z x) (cov.curvature X Y W x)
      = (-2 : ℝ) * cov.ricciForm x (Z x) (cov.curvature X Y W x) := rfl
  rw [hsm1, hsm2]
  ring

end Flow

end CovariantDerivative
