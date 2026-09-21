/-
**Hamilton's evolution equation for the Ricci tensor.**

`CurvatureEvolution.lean` gives `∂ₜRm = Δ Rm + Q` for an actual Ricci flow, paired against a
fourth field. Tracing that identity in the *first* slot of `Rm` against its output slot turns

* the left-hand side into `∂ₜRic`, because `Ric(Y,Z) = ∑ᵢ ⟪Rm(eᵢ,Y)Z, eᵢ⟫` and the
  time derivative passes through the trace (`derivRicciFormOfMetric_eq_sum`, extracted from
  the double-trace argument of `FlowKoszul.lean`);
* `Δ Rm` into `Δ_g Ric`, which is `CurvatureTrace.lean`;
* the four quadratic terms into four sums, all algebraic in `Rm` and `Ric`.

So `∂ₜ Ric = Δ_g Ric + Q_{Ric}`, with `Q_{Ric}` carrying no derivatives. Together with
`∂ₜ scal = Δ scal + 2|Ric|²` (`ScalarFlow.lean`) this is what the dimension-three curvature
operator `Rm₃ = scal·Id − 2 Ric♯` evolves by, since `Rm₃` is built from exactly those two.

**Nothing new is computed here.** Both traces are lemmas; what this file does is take them at
the same frame and line the two sides up.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureEvolution
import RicciFlowBlueprint.CurvatureTrace

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

section Trace

set_option maxSynthPendingDepth 3

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **The first-slot trace of `∂ₜRm` is `∂ₜRic`**:
`∂ₜRic(Y,Z) = ∑ᵢ ⟪∂ₜRm(eᵢ,Y)Z, eᵢ⟫`, with `∂ₜRm` in the Koszul machinery's form
`(∇_{eᵢ}Ȧ)(Y,Z) − (∇_Y Ȧ)(eᵢ,Z)`.

This is the *inner* half of `metricTraceE_derivRicciFormOfMetric_eq`'s argument, extracted:
`derivRicciFormOfMetric_apply` says `∂ₜRic(v,w)` is the trace of `∂ₜ[u ↦ Rm(u,V)W]`,
`LinearMap.trace_eq_sum_inner` reads that trace off the frame, and
`derivCurvatureEndoE_apply_field` evaluates the summand. -/
theorem derivRicciFormOfMetric_eq_sum
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {x : M} (hA : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    {Y Z : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i)))
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    derivRicciFormOfMetric g t₀ x (Y x) (Z x)
      = ∑ i, ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
            (fr i) Y Z x
          - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
            Y (fr i) Z x, fr i x⟫ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  have hfin : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr i).mdifferentiable h2 x
  have hY1 : MDiffAt (T% Y) x := hY.mdifferentiable h2 x
  rw [derivRicciFormOfMetric_apply (V := Y) (W := Z) hg hcomm hcov x (Y x) (Z x) hY hZ rfl rfl]
  let T : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    (derivCurvatureEndoE g t₀ Y hZ x).toLinearMap
  change LinearMap.trace ℝ (TangentSpace I x) T = _
  rw [LinearMap.trace_eq_sum_inner T b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : ⟪b i, T (b i)⟫ = ⟪T (b i), b i⟫ := real_inner_comm _ _
  have hT : (T (b i) : TangentSpace I x)
      = (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) (fr i) Y Z x
        - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y (fr i) Z x := by
    show derivCurvatureEndoE g t₀ Y hZ x (b i) = _
    rw [← hbv i, derivCurvatureEndoE_apply_field hg hcomm hcov hA (hfr1 i) hY1 hZ]
  rw [e, hT, hbv i]

set_option maxHeartbeats 1000000 in
-- BENCH: evolution-ricci-flow
/-- **Hamilton's evolution equation for the Ricci tensor**:

  `∂ₜRic(Y,Z) = (Δ_g Ric)(Y,Z) + Q₁ + Q₂ + ∑ᵢ Ric(R(eᵢ,Y)Z, eᵢ) + ∑ᵢ Ric(Z, R(eᵢ,Y)eᵢ)`,

the first-slot trace of `∂ₜRm = Δ Rm + Q`. Every term on the right is either `Δ_g Ric` or
algebraic in `Rm` and `Ric`; no derivatives survive in `Q`.

Nothing new is computed: the left-hand side is `derivRicciFormOfMetric_eq_sum` and the
leading term on the right is `sum_inner_curvatureLaplacian_fst_eq_laplacianBilin`. What the
proof does is take the curvature evolution equation at `X = W = eⱼ`, sum over `j`, and line
the two traces up at the same frame. -/
theorem derivRicciFormOfMetric_eq_laplacianBilin_add_of_isRicciFlowAt
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    {Y Z : Π y : M, TangentSpace I y} {x : M}
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
    (hY : CMDiff 4 (T% Y)) (hZ : CMDiff 4 (T% Z))
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
      ∀ P : Π y : M, TangentSpace I y, CMDiff 4 (T% P) → ContMDiffAt I 𝓘(ℝ, ℝ) 2
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y (Z y) (P y)) x)
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
    (hcb : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      (leviCivitaOfMetric (g t₀)).IsMDiffCovBilinAt
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) Y Z x)
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
    derivRicciFormOfMetric g t₀ x (Y x) (Z x)
      = (leviCivitaOfMetric (g t₀)).laplacianBilin
            (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) Y Z x
        + ∑ j, ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) (fr j) Y (fr i) Z x, fr j x⟫
        + ∑ j, ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) Y (fr i) (fr j) Z x, fr j x⟫
        + ∑ j, (leviCivitaOfMetric (g t₀)).ricciForm x
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) Y Z x) (fr j x)
        + ∑ j, (leviCivitaOfMetric (g t₀)).ricciForm x (Z x)
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) Y (fr j) x) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 := hlc2
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3 := hlc3
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  have hfr3 : ∀ i, CMDiff 3 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  have hbilric : CovariantDerivative.IsMDiffBilinAt (I := I)
      (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) x := fun U V _ _ ↦ hRic U V x
  -- the curvature evolution equation with both outer slots on the frame
  have key : ∀ j, ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
        (fr j) Y Z x, fr j x⟫
      - ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
        Y (fr j) Z x, fr j x⟫
      = ⟪(leviCivitaOfMetric (g t₀)).curvatureLaplacian (fr j) Y Z x, fr j x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) (fr j) Y (fr i) Z x, fr j x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) Y (fr i) (fr j) Z x, fr j x⟫
        + (leviCivitaOfMetric (g t₀)).ricciForm x
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) Y Z x) (fr j x)
        + (leviCivitaOfMetric (g t₀)).ricciForm x (Z x)
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) Y (fr j) x) := fun j ↦
    inner_derivCurvature_eq_curvatureLaplacian_add_of_isRicciFlowAt hg hcomm hbil hAt hflow
      hrb3 hlc2 hlc3 (hfr j) hY hZ (hfr j) hRic (hRic2 _ (hfr j)) hdRic hcovR hfr hs hu hx b hbv
  rw [derivRicciFormOfMetric_eq_sum hg hcomm hcov hAt hY2 hZ2 hfr2 b hbv]
  have hL : ∀ j, ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
        (fr j) Y Z x
      - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y (fr j) Z x,
      fr j x⟫
      = ⟪(leviCivitaOfMetric (g t₀)).curvatureLaplacian (fr j) Y Z x, fr j x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) (fr j) Y (fr i) Z x, fr j x⟫
        + ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) Y (fr i) (fr j) Z x, fr j x⟫
        + (leviCivitaOfMetric (g t₀)).ricciForm x
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) Y Z x) (fr j x)
        + (leviCivitaOfMetric (g t₀)).ricciForm x (Z x)
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) Y (fr j) x) := by
    intro j
    rw [inner_sub_left]
    exact key j
  rw [Finset.sum_congr rfl fun j _ ↦ hL j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    (leviCivitaOfMetric (g t₀)).sum_inner_curvatureLaplacian_fst_eq_laplacianBilin
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
      hY hZ hbilric hcb hs hu hx hfr3 b hbv]

end Trace

end RicciFlowBlueprint
