/-
**Hamilton–Ivey pinching is preserved by the Ricci flow on a closed three-manifold.**

The assembly. The maximum principle runs on `u(t,x) = mat_{e(t,x)} Rm₃(g_t)(x)`, the matrix of
the curvature operator in the Uhlenbeck frame `e(t,x) = ι(t,x) e₀(x)`: a point of the fixed
Euclidean space `Mat3`, so no bundle metric is ever an instance while another is in scope.

* `∂ₜu = mat(∂ₜRm₃)`, the Uhlenbeck commutator vanishing (`hasDerivAt_metric_dysonSum_conj`);
* `∂ₜRm₃ = ΔRm₃ + Q(Rm₃)` (`exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt`) and
  `mat(Q(Rm₃)) = Q_mat(u)` (`toMat_hamiltonReaction`);
* at a spatial maximum of the distance to `K_mat`, `⟪u − p, mat ΔRm₃⟫ ≤ 0`
  (`inner_toMat_laplacian_curvatureOperator_nonpos`), the frame being invisible;
* `Q_mat` satisfies Nagumo's condition on `K_mat` and is Lipschitz on balls, `0 ∈ K_mat`.

This file first packages the touching step **at one time**, for any family of orthonormal
frames, under the single `letI` of `g_t`.
-/
import RicciFlowBlueprint.CurvatureOperatorEvolution
import RicciFlowBlueprint.IveyTouching
import RicciFlowBlueprint.FibrewiseMaximumPrinciple

open Bundle Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

open CovariantDerivative Pinching ContinuousLinearMap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 4

/-- **The matrix of `Rm₃` in a family of vectors**, for a metric carried as a value. -/
noncomputable def curvatureMat (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) (b : Fin 3 → E) : Mat3 :=
  WithLp.toLp 2 fun ij ↦ innerE g x (curvatureOperatorE g x (b ij.1)) (b ij.2)

/-- `Rm₃` for a metric carried as a value is the curvature operator of its Levi-Civita
connection. -/
theorem curvatureOperatorE_apply_eq
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M) (v : E) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one g
    curvatureOperatorE g x v = (leviCivitaOfMetric g).curvatureOperator x v := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g
  have h := sharpE_apply_eq_sharp (g := fun _ ↦ g) (t₀ := 0) x (ricciFormOfMetric g x) v
  show scalarCurvatureOfMetricAt g x • v - (2 : ℝ) • sharpE g x (ricciFormOfMetric g x) v = _
  rw [h]
  rfl

variable [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

-- BENCH: hamilton-ivey-touching-time
/-- **The touching step of Hamilton–Ivey at one time, for any family of orthonormal frames.**
If `D x` is the time derivative of `Rm₃` at `x`, then at a spatial maximum of the distance from
`u x = mat_{fr x} Rm₃` to `K_mat`, the outward normal pairs with `mat_{fr x} D` no more than with
Hamilton's reaction. -/
theorem inner_curvatureMat_deriv_le_reaction [I.Boundaryless] (hdim : finrank ℝ E = 3)
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    (hAt : ∀ x, CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt I M g t₀)
    (hrb3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hrb4 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    (hlc3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3)
    (hRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hRic2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ Z P : Π y : M, TangentSpace I y, CMDiff 4 (T% Z) → CMDiff 4 (T% P) →
        ContMDiffAt I 𝓘(ℝ, ℝ) 2
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y (Z y) (P y)) x)
    (hdRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
        CMDiff 2 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) P Q R y) x)
    (hcovR : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
        CMDiff 3 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covRicci P Q R y) x)
    (hcb : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ Y Z : Π y : M, TangentSpace I y, CMDiff 4 (T% Y) → CMDiff 4 (T% Z) →
        (leviCivitaOfMetric (g t₀)).IsMDiffCovBilinAt
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) Y Z x)
    (hscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ y, MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y)
    (hdscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, CovariantDerivative.IsMDiffOneFormAt (I := I)
        (fun y ↦ (mvfderiv I (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, CovariantDerivative.IsMDiffOneFormAt (I := I)
        ((leviCivitaOfMetric (g t₀)).divBilinOneForm
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) (fun y U V _ _ ↦ hRic U V y)) x)
    (fr : M → Fin 3 → E)
    (hfr : ∀ x i j, innerE (g t₀) x (fr x i) (fr x j) = if i = j then 1 else 0)
    {D : M → E →L[ℝ] E} (hD : ∀ x, HasDerivAt (fun t ↦ curvatureOperatorE (g t) x) (D x) t₀)
    {x₀ : M} {p : Mat3} (hp : p ∈ pinchedMat)
    (hpmin : ‖curvatureMat (g t₀) x₀ (fr x₀) - p‖
      = infDist (curvatureMat (g t₀) x₀ (fr x₀)) pinchedMat)
    (hhalf : ∀ q ∈ pinchedMat, ⟪curvatureMat (g t₀) x₀ (fr x₀) - p, q - p⟫ ≤ 0)
    (hmax : ∀ x, infDist (curvatureMat (g t₀) x (fr x)) pinchedMat
      ≤ infDist (curvatureMat (g t₀) x₀ (fr x₀)) pinchedMat) :
    ⟪curvatureMat (g t₀) x₀ (fr x₀) - p,
        WithLp.toLp 2 fun ij ↦ innerE (g t₀) x₀ (D x₀ (fr x₀ ij.1)) (fr x₀ ij.2)⟫
      ≤ ⟪curvatureMat (g t₀) x₀ (fr x₀) - p, reactionMat (curvatureMat (g t₀) x₀ (fr x₀))⟫ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
  let _ : IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x) := hrb4
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 := hlc2
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3 := hlc3
  let _ : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
  let _ : IsContMDiffRiemannianBundle I 1 (E →L[ℝ] E) (EndTangent I (M := M)) :=
    isContMDiffRiemannianBundle_endTangent (n := 1)
  have hfd : ∀ x : M, FiniteDimensional ℝ (TangentSpace I x) := fun _ ↦
    inferInstanceAs (FiniteDimensional ℝ E)
  have hnt : ∀ x : M, Nontrivial (TangentSpace I x) := fun x ↦
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := TangentSpace I x)
      (show 0 < finrank ℝ (TangentSpace I x) by
        rw [show finrank ℝ (TangentSpace I x) = 3 from hdim]; norm_num)
  have hinner : ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q :=
    fun _ _ _ ↦ rfl
  -- the frames are orthonormal bases
  have hbasis : ∀ x : M, ∃ e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x), ∀ i, e i = fr x i := by
    intro x
    obtain ⟨v, hv⟩ : ∃ v : Fin 3 → TangentSpace I x, v = fun i ↦ fr x i := ⟨_, rfl⟩
    have hon : Orthonormal ℝ v :=
      orthonormal_iff_ite.mpr fun i j ↦ by rw [hv]; exact hfr x i j
    have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
      rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank'
        (by simp only [Fintype.card_fin]; exact hdim.symm)]
    refine ⟨OrthonormalBasis.mk hon hsp, fun i ↦ ?_⟩
    rw [congrFun (OrthonormalBasis.coe_mk hon hsp) i, hv]
  choose e he using hbasis
  have hu : ∀ x, curvatureMat (g t₀) x (fr x)
      = toMat (e x) ((leviCivitaOfMetric (g t₀)).curvatureOperator x) := by
    intro x
    ext ij
    rw [toMat_apply, he, he]
    show innerE (g t₀) x (curvatureOperatorE (g t₀) x (fr x ij.1)) (fr x ij.2) = _
    rw [curvatureOperatorE_apply_eq]
    rfl
  -- the evolution equation at the touching point
  obtain ⟨D', hD', hid⟩ := exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt hdim hg hcomm
    hcov hbil (hAt x₀) hflow hrb3 hrb4 hlc2 hlc3 hRic (hRic2 x₀) (hdRic x₀) (hcovR x₀) (hcb x₀)
    hscal (hdscal x₀) (hw x₀)
  have hDD : D x₀ = D' := (hD x₀).unique hD'
  set Lap := (endCov (leviCivitaOfMetric (g t₀))).laplacianSection (leviCivitaOfMetric (g t₀))
    ((leviCivitaOfMetric (g t₀)).contMDiff_curvatureOperator) x₀ with hLap
  have hut : (WithLp.toLp 2 fun ij ↦ innerE (g t₀) x₀ (D x₀ (fr x₀ ij.1)) (fr x₀ ij.2) : Mat3)
      = toMat (e x₀) Lap
        + reactionMat (curvatureMat (g t₀) x₀ (fr x₀)) := by
    rw [hu, ← toMat_hamiltonReaction, ← map_add]
    ext ij
    rw [toMat_apply, he, he]
    show innerE (g t₀) x₀ (D x₀ (fr x₀ ij.1)) (fr x₀ ij.2) = _
    rw [hDD]
    exact hid _ _
  have htouch := inner_toMat_laplacian_curvatureOperator_nonpos (leviCivitaOfMetric (g t₀))
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)) hinner e
    (fun x ↦ by rw [← hu, ← hu]; exact hmax x) hp (by rw [← hu]; exact hpmin)
    (by rw [← hu]; exact hhalf)
  rw [← hu] at htouch
  have h2 : ⟪curvatureMat (g t₀) x₀ (fr x₀) - p, toMat (e x₀) Lap⟫ ≤ 0 := htouch
  rw [hut, inner_add_right]
  linarith

end RicciFlowBlueprint
