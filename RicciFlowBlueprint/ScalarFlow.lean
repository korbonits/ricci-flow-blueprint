/-
The evolution equation of the scalar curvature under the Ricci flow.

This file is the join of the two halves that were built separately:

* `FlowKoszul.lean` — the *analytic* half. `∂ₜ ∇` is Koszul for `h = ∂ₜ g`, `∂ₜ Rm` is the
  associated `Rm_A`, and tracing twice gives
  `tr_g(∂ₜ Ric) = div div h − tr_g(Δ_g h)` with **no curvature terms**.
* `ScalarEvolution.lean` — the *geometric* half. At `h = −2 Ric` those two double traces are
  `−Δ scal` and `−2 Δ scal`, so their difference is `Δ scal`; this is the second contraction
  of the second Bianchi identity, differentiated once more.

Composing them with `RicciVariation.lean`'s `∂ₜ R = tr_g(∂ₜ Ric) + 2 |Ric|²` gives Hamilton's
equation `∂ₜ R = Δ R + 2 |Ric|²`, on a general manifold.

The connection of a varying metric is introduced by `letI`, so every statement here that
mentions it is written under one; see CLAUDE.md's rule about `IsMetricCompatible`.
-/
import RicciFlowBlueprint.FlowKoszul
import RicciFlowBlueprint.ScalarEvolution

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

-- BENCH: trace-ricci-variation-is-laplacian-scal-flow
/-- **`tr_g(∂ₜ Ric) = Δ scal` for the actual flow.** `FlowKoszul.lean` delivers the left-hand
side as the difference of the two canonical double traces of `∇²h`; under the flow `h = −2 Ric`
(`innerE_deriv_eq_of_isRicciFlowAt'`), and `ScalarEvolution.lean` evaluates that difference at
`−2 Ric` to `Δ scal`. -/
theorem metricTraceE_derivRicciFormOfMetric_eq_laplacian
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    {x : M} (hA : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      IsRicciFlowAt I M g t₀)
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    {ι : Type*} [Fintype ι]
    (hbg : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffBilin (I := I)
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y))
    (hscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffOneFormAt (I := I)
        (fun y ↦ (mvfderiv I (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffOneFormAt (I := I)
        ((leviCivitaOfMetric (g t₀)).divBilinOneForm
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) hbg) x)
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      IsOrthonormalFrameOn I E 1 fr u)
    (hu : IsOpen u) (hx : x ∈ u) (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i)
    (hh : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hd : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ a c d, MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
        (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) (fr a) (fr c) (fr d) y) x)
    (hcb : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ j, (leviCivitaOfMetric (g t₀)).IsMDiffCovBilinAt
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) (fr j) (fr j) x) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
    metricTraceE (g t₀) x (derivRicciFormOfMetric g t₀ x)
      = (leviCivitaOfMetric (g t₀)).laplacianFun
          (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) x := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 := hlc2
  -- under the flow, `h = −2 Ric`
  have hheq : h = fun y ↦ ((-2 : ℝ) • (leviCivitaOfMetric (g t₀)).ricciForm y :
      E →L[ℝ] E →L[ℝ] ℝ) := by
    funext y
    exact innerE_deriv_eq_of_isRicciFlowAt' hg y hflow
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  -- `∇h` is `−2 ∇Ric`, so the differentiability hypothesis transports
  have hdh : ∀ a c d, MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin h
      (fr a) (fr c) (fr d) y) x := by
    intro a c d
    have hfun : (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin h (fr a) (fr c) (fr d) y)
        = fun y ↦ (-2 : ℝ) * (leviCivitaOfMetric (g t₀)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) (fr a) (fr c) (fr d) y := by
      funext y
      rw [hheq]
      exact (leviCivitaOfMetric (g t₀)).covBilin_smul_form _ _ (hh (fr c) (fr d) y)
    rw [hfun]
    exact mdifferentiableAt_const.mul (hd a c d)
  have hsymm : ∀ (y : M) (v w : E), h y v w = h y w v := by
    intro y v w
    rw [hheq]
    exact congrArg (fun r : ℝ ↦ (-2 : ℝ) * r)
      ((leviCivitaOfMetric (g t₀)).ricciForm_symm
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
        (torsion_leviCivitaOfMetric_eq_zero (g t₀)) v w)
  rw [metricTraceE_derivRicciFormOfMetric_eq_sub hg hcomm hcov hbil hsymm
    hA hfr2 b hbv hdh, hheq]
  exact (leviCivitaOfMetric (g t₀)).sum_cov2Bilin_neg_two_ricciForm_eq
    (torsion_leviCivitaOfMetric_eq_zero (g t₀))
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
    hbg hscal hw hs hu hx hfr b hbv hh hd hcb


-- BENCH: evolution-scalar-flow
/-- **Hamilton's evolution equation for the scalar curvature**, on a general manifold:
`∂ₜ R = Δ R + 2 |Ric|²_g`, where `|Ric|²_g = tr_g(Ric ∘ Ric♯)`.

This is the join of the two halves. `RicciVariation.lean` gives
`∂ₜ R = tr_g(∂ₜ Ric) + 2 |Ric|²` from the first variation of the metric trace; the trace of the
Ricci variation is `Δ R` by `metricTraceE_derivRicciFormOfMetric_eq_laplacian`, i.e. by the
Koszul second-derivative identity followed by the two contractions of the second Bianchi
identity. No curvature terms appear anywhere in between — they cancel at the Koszul step. -/
theorem hasDerivAt_scalarCurvatureOfMetricAt_eq_laplacian_add
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    {x : M} (hA : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      IsRicciFlowAt I M g t₀)
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    {ι : Type*} [Fintype ι]
    (hbg : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffBilin (I := I)
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y))
    (hscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffOneFormAt (I := I)
        (fun y ↦ (mvfderiv I (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffOneFormAt (I := I)
        ((leviCivitaOfMetric (g t₀)).divBilinOneForm
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) hbg) x)
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      IsOrthonormalFrameOn I E 1 fr u)
    (hu : IsOpen u) (hx : x ∈ u) (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i)
    (hh : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hd : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ a c d, MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
        (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) (fr a) (fr c) (fr d) y) x)
    (hcb : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
        ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ j, (leviCivitaOfMetric (g t₀)).IsMDiffCovBilinAt
        (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) (fr j) (fr j) x) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
    HasDerivAt (fun t ↦ scalarCurvatureOfMetricAt (g t) x)
      ((leviCivitaOfMetric (g t₀)).laplacianFun
          (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) x
        + 2 * metricTraceE (I := I) (M := M) (g t₀) x
            (ricciFormOfMetric (g t₀) x ∘L
              sharpE (I := I) (M := M) (g t₀) x (ricciFormOfMetric (g t₀) x))) t₀ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  rw [← metricTraceE_derivRicciFormOfMetric_eq_laplacian hg hcomm hcov hbil hA hflow hlc2
    hbg hscal hw hs hu hx hfr b hbv hh hd hcb]
  exact hasDerivAt_scalarCurvatureOfMetricAt_of_isRicciFlowAt hg hcomm hcov x hflow

end Flow

end RicciFlowBlueprint
