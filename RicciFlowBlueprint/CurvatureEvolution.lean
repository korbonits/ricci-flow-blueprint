/-
**Hamilton's evolution equation for the curvature tensor, for an actual Ricci flow.**

`CurvatureFlow.lean` proves `∂ₜRm = Δ Rm + Q` for the *Koszul tensor* of `h = −2 Ric`: the
statement is about an abstract `(1,2)`-tensor `A` satisfying the Koszul characterisation. This
file specialises it to a genuine `IsRicciFlowAt`, exactly as `ScalarFlow.lean` specialises the
scalar equation.

The two ingredients are already in place and neither is new mathematics:

* `isKoszulOf_derivDifference` (`FlowKoszul.lean`) --- `∂ₜ∇` is Koszul for `h = ∂ₜ g`;
* `innerE_deriv_eq_of_isRicciFlowAt'` (`RicciVariation.lean`) --- under the flow `h = −2 Ric`.

What the specialisation costs is bookkeeping: every hypothesis has to be written under a
two-step `letI` (the `RiemannianBundle` of `g t₀` **and** the `C¹` regularity of its
Levi-Civita connection), and the levels the curvature tower consumes --- a `C³` metric and a
`C³` connection --- are carried as explicit hypotheses, a `C²` metric giving only a `C¹`
connection.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureFlow
import RicciFlowBlueprint.FlowKoszul

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]

section Flow

set_option maxSynthPendingDepth 3

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

-- BENCH: evolution-rm-flow
/-- **`∂ₜRm = Δ Rm + Q` for an actual Ricci flow.**

  `⟪∂ₜRm(X,Y)Z, W⟫ = ⟪Δ Rm(X,Y)Z, W⟫ + Q₁ + Q₂ + Ric(R(X,Y)Z,W) + Ric(Z,R(X,Y)W)`

`CurvatureFlow.lean` proves this for any tensor `A` Koszul for `h = −2 Ric`; here `A` is
`∂ₜ∇` and `h = ∂ₜ g`, so the two hypotheses it needs are theorems:
`isKoszulOf_derivDifference` says `∂ₜ∇` is Koszul for `∂ₜ g`, and
`innerE_deriv_eq_of_isRicciFlowAt'` says `∂ₜ g = −2 Ric` under the flow. -/
theorem inner_derivCurvature_eq_curvatureLaplacian_add_of_isRicciFlowAt
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hAt : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt I M g t₀)
    (hrb3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    (hlc3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3)
    (hX : CMDiff 4 (T% X)) (hY : CMDiff 4 (T% Y)) (hZ : CMDiff 4 (T% Z))
    (hW : CMDiff 4 (T% W))
    (hRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hRic2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ContMDiffAt I 𝓘(ℝ, ℝ) 2
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y (Z y) (W y)) x)
    (hdRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
        CMDiff 2 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) P Q R y) x)
    (hcovR : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
        CMDiff 3 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covRicci P Q R y) x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hfr : ∀ i, CMDiff 4 (T% (fr i)))
    (hs : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      IsOrthonormalFrameOn I E 1 fr u)
    (hu : IsOpen u) (hx : x ∈ u)
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
    ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X Y Z x, W x⟫
        - ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y X Z x, W x⟫
      = ⟪(leviCivitaOfMetric (g t₀)).curvatureLaplacian X Y Z x, W x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator (fr i) X Y (fr i) Z x, W x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator (fr i) Y (fr i) X Z x, W x⟫
        + (leviCivitaOfMetric (g t₀)).ricciForm x
            ((leviCivitaOfMetric (g t₀)).curvature X Y Z x) (W x)
        + (leviCivitaOfMetric (g t₀)).ricciForm x (Z x)
            ((leviCivitaOfMetric (g t₀)).curvature X Y W x) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 := hlc2
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3 := hlc3
  set cov := leviCivitaOfMetric (g t₀) with hcovdef
  -- under the flow, `h = −2 Ric`
  have hheq : h = fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ) := by
    funext y
    exact innerE_deriv_eq_of_isRicciFlowAt' hg y hflow
  -- `∂ₜ∇` is Koszul for `−2 Ric`
  have hA : cov.IsKoszulOf (derivDifferenceTensor g t₀)
      (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ)) := by
    rw [← hheq]
    exact isKoszulOf_derivDifference hg hcomm hbil
  have hb : CovariantDerivative.IsMDiffBilinAt (I := I)
      (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ)) x := by
    rw [← hheq]; exact hbil x
  have hf2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2
      (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ) (Z y) (W y)) x := by
    have e : (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ) (Z y) (W y))
        = fun y ↦ (-2 : ℝ) * cov.ricciForm y (Z y) (W y) := by funext y; rfl
    rw [e]
    exact (contDiffAt_const.mul contDiffAt_id).comp_contMDiffAt hRic2
  have hAf : ∀ P Q : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      MDiffAt (T% (fun y ↦ derivDifferenceTensor g t₀ y (P y) (Q y))) x := by
    intro P Q hP hQ
    exact hAt P Q (hP.mdifferentiable (by norm_num) x) (hQ.mdifferentiable (by norm_num) x)
  have hd : ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      CMDiff 2 (T% R) → MDiffAt (fun y ↦ cov.covBilin
        (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ)) P Q R y) x := by
    intro P Q R hP hQ hR
    have e : (fun y ↦ cov.covBilin
          (fun z ↦ ((-2 : ℝ) • cov.ricciForm z : E →L[ℝ] E →L[ℝ] ℝ)) P Q R y)
        = fun y ↦ (-2 : ℝ) * cov.covBilin (fun z ↦ cov.ricciForm z) P Q R y := by
      funext y
      exact cov.covBilin_smul_form _ _ (hRic Q R y)
    rw [e]
    exact mdifferentiableAt_const.mul (hdRic P Q R hP hQ hR)
  exact cov.inner_derivCurvature_eq_curvatureLaplacian_add
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
    (torsion_leviCivitaOfMetric_eq_zero (g t₀))
    hA hb hX hY hZ hW hf2 hAf hd hRic hcovR hfr hs hu hx b hbv

-- BENCH: evolution-rm-flow-deriv
/-- **Hamilton's evolution equation for the curvature tensor**, as a derivative in `t`:

  `∂ₜ ⟪Rm(X,Y)Z, W⟫ = ⟪Δ Rm(X,Y)Z, W⟫ + Q₁ + Q₂ + Ric(R(X,Y)Z,W) + Ric(Z,R(X,Y)W)`

where the pairing is against the metric *frozen at `t₀`*, so the left-hand side is the time
derivative of the `(1,3)`-tensor `Rm` and no `∂ₜ g` term appears in it.

This is `inner_derivCurvature_eq_curvatureLaplacian_add_of_isRicciFlowAt` composed with
`hasDerivAt_curvatureE_covTwoTensor`, which delivers `∂ₜ Rm` as the `Rm_A` of `∂ₜ∇`. It is the
curvature counterpart of `hasDerivAt_scalarCurvatureOfMetricAt_eq_laplacian_add`. -/
theorem hasDerivAt_inner_curvatureE_eq_curvatureLaplacian_add_of_isRicciFlowAt
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hAt : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt I M g t₀)
    (hrb3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    (hlc3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3)
    (hX : CMDiff 4 (T% X)) (hY : CMDiff 4 (T% Y)) (hZ : CMDiff 4 (T% Z))
    (hW : CMDiff 4 (T% W))
    (hRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hRic2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ContMDiffAt I 𝓘(ℝ, ℝ) 2
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y (Z y) (W y)) x)
    (hdRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
        CMDiff 2 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) P Q R y) x)
    (hcovR : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
        CMDiff 3 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covRicci P Q R y) x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hfr : ∀ i, CMDiff 4 (T% (fr i)))
    (hs : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      IsOrthonormalFrameOn I E 1 fr u)
    (hu : IsOpen u) (hx : x ∈ u)
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i)
    (hXYZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (Y y))
        x (X x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (Y y)) x (X x)) t₀)
    (hYXZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (X y))
        x (Y x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (X y)) x (Y x)) t₀) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
    HasDerivAt (fun t ↦ innerE (g t₀) x (curvatureE (leviCivitaOfMetric (g t)) X Y Z x) (W x))
      (⟪(leviCivitaOfMetric (g t₀)).curvatureLaplacian X Y Z x, W x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator (fr i) X Y (fr i) Z x, W x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator (fr i) Y (fr i) X Z x, W x⟫
        + (leviCivitaOfMetric (g t₀)).ricciForm x
            ((leviCivitaOfMetric (g t₀)).curvature X Y Z x) (W x)
        + (leviCivitaOfMetric (g t₀)).ricciForm x (Z x)
            ((leviCivitaOfMetric (g t₀)).curvature X Y W x)) t₀ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  have hD := hasDerivAt_curvatureE_covTwoTensor hg hcomm (hZ.of_le (by norm_num))
    (hX.mdifferentiable (by norm_num) x) (hY.mdifferentiable (by norm_num) x) hXYZ hYXZ
  have hL := (((innerE (g t₀) x).flip (W x)).hasFDerivAt).comp_hasDerivAt t₀ hD
  refine hL.congr_deriv ?_
  have hsub : ((innerE (g t₀) x).flip (W x))
        ((leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X Y Z x
          - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y X Z x)
      = ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X Y Z x, W x⟫
        - ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y X Z x,
            W x⟫ :=
    map_sub _ _ _
  rw [hsub]
  exact inner_derivCurvature_eq_curvatureLaplacian_add_of_isRicciFlowAt hg hcomm hbil hAt hflow
    hrb3 hlc2 hlc3 hX hY hZ hW hRic hRic2 hdRic hcovR hfr hs hu hx b hbv


end Flow

end RicciFlowBlueprint
