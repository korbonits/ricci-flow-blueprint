/-
**The dimension-three curvature operator under the Ricci flow, at a point, with the metric
moving.**

`Rm₃ = scal·1 − 2Ric♯` carries the metric twice: once inside `scal` and `Ric`, and once in the
index raising `♯`. The spatial calculus (`SharpLaplacian.lean`, `CurvatureFormThree.lean`)
freezes the metric; the *time* derivative cannot, and this file computes what the moving `♯`
contributes. Under `∂ₜg = −2Ric`, `∂ₜ(g⁻¹) = 2 g⁻¹ Ric g⁻¹`, so

`∂ₜ Ric♯ = 2 Ric♯∘Ric♯ + (∂ₜRic)♯`,

and therefore `∂ₜ Rm₃ = (∂ₜscal)·1 − 4 Ric♯² − 2(∂ₜRic)♯`. The `Ric♯²` term is the whole
contribution of the moving index raising; it is quadratic in the curvature and joins the
reaction term.

**Everything is at one point and in `E`**, the metrics carried as values, so that the
Uhlenbeck frame of `UhlenbeckPointwise.lean` can be applied to it directly: its coefficient is
`A t = Ric♯_{g t}`, and the conjugation commutator `[Rm₃, A]` vanishes because `Rm₃` is a
polynomial in `A` (`curvatureOperatorE_comm`).
-/
import RicciFlowBlueprint.UhlenbeckPointwise
import RicciFlowBlueprint.RicciVariation

open Set ContinuousLinearMap Bundle
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

set_option maxSynthPendingDepth 3

section Sharp

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {t₀ : ℝ} {x : M}

/-- **The time derivative of a sharp**, the metric moving: `∂ₜ(g⁻¹B) = −g⁻¹ ġ g⁻¹ B + g⁻¹ Ḃ`. -/
theorem hasDerivAt_sharpE {B : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {B' h : E →L[ℝ] E →L[ℝ] ℝ}
    (hg : HasDerivAt (fun t ↦ innerE (g t) x) h t₀) (hB : HasDerivAt B B' t₀) :
    HasDerivAt (fun t ↦ sharpE (g t) x (B t))
      (-((innerE (g t₀) x).inverse ∘L h ∘L (innerE (g t₀) x).inverse) ∘L B t₀
        + (innerE (g t₀) x).inverse ∘L B') t₀ :=
  (hasDerivAt_inverse_innerE (h := fun _ ↦ h) hg).clm_comp hB

end Sharp

variable [T2Space M] [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]

/-- **The dimension-three curvature operator** at a point, for a metric carried as a value:
`Rm₃ = scal·1 − 2 Ric♯`, as an endomorphism of `E = T_xM`. -/
noncomputable def curvatureOperatorE
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M) :
    E →L[ℝ] E :=
  scalarCurvatureOfMetricAt g x • ContinuousLinearMap.id ℝ E
    - (2 : ℝ) • sharpE g x (ricciFormOfMetric g x)

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **`Rm₃` commutes with `Ric♯`** --- it is a polynomial in it. This is what makes the
commutator in Uhlenbeck's conjugation vanish in dimension three. -/
theorem curvatureOperatorE_comm
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M) :
    curvatureOperatorE g x ∘L sharpE g x (ricciFormOfMetric g x)
      = sharpE g x (ricciFormOfMetric g x) ∘L curvatureOperatorE g x := by
  unfold curvatureOperatorE
  ext v
  simp only [comp_apply, sub_apply, smul_apply, id_apply, map_sub, map_smul]

section Flow

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {t₀ : ℝ} {x : M}

omit [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
-- BENCH: curvature-operator-time-derivative
/-- **`∂ₜ Rm₃` under the Ricci flow, the moving index raising included**:
`∂ₜ Rm₃ = (∂ₜscal)·1 − 2(2 Ric♯∘Ric♯ + (∂ₜRic)♯)`.

The `Ric♯∘Ric♯` term is the whole contribution of the moving metric in the `♯`, and is what
`SharpLaplacian.lean`'s frozen-metric identity could not see. -/
theorem hasDerivAt_curvatureOperatorE_of_flow
    (hg : HasDerivAt (fun t ↦ innerE (g t) x) ((-2 : ℝ) • ricciFormOfMetric (g t₀) x) t₀)
    {R' : E →L[ℝ] E →L[ℝ] ℝ} (hRic : HasDerivAt (fun t ↦ ricciFormOfMetric (g t) x) R' t₀)
    {s' : ℝ} (hscal : HasDerivAt (fun t ↦ scalarCurvatureOfMetricAt (g t) x) s' t₀) :
    HasDerivAt (fun t ↦ curvatureOperatorE (g t) x)
      (s' • ContinuousLinearMap.id ℝ E
        - (2 : ℝ) • ((2 : ℝ) • (sharpE (g t₀) x (ricciFormOfMetric (g t₀) x)
            ∘L sharpE (g t₀) x (ricciFormOfMetric (g t₀) x))
          + sharpE (g t₀) x R')) t₀ := by
  have hs := hasDerivAt_sharpE hg hRic
  have h := (hscal.smul_const (ContinuousLinearMap.id ℝ E)).sub (hs.const_smul (2 : ℝ))
  refine h.congr_deriv ?_
  unfold sharpE
  ext v
  simp only [sub_apply, smul_apply, add_apply, neg_apply, comp_apply, id_apply, map_smul]
  module

end Flow

end RicciFlowBlueprint
