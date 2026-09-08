/-
The geodesic equation as an ODE in a chart.

`CovariantAlongCurve.lean` gives `D/dt` and, in the fibre coordinates of a trivialisation
`e` around `γ t`, the formula `D/dt V = c' + Γ(γ t)(γ'(t))(c(t))`. To *solve*
`∇_{γ'}γ' = 0` one more identification is needed: the tangent-bundle trivialisation **is** the
chart. Mathlib says so — `TangentBundle.trivializationAt_apply` unfolds to
`tangentCoordChange` — and the consequence is that the chart position
`p t = extChartAt I x₀ (γ t)` has `p'(t)` equal to the fibre coordinate of the velocity.

So the geodesic equation becomes an ODE for `p` on an open subset of the model space, which is
the form Picard–Lindelöf consumes.

The chart-side manoeuvre is Mathlib's own, from `IntegralCurve/Basic.lean`: turn
`HasMFDerivAt` of the curve into `HasDerivAt` of the chart composite, and the
`mfderiv` of the chart into `tangentCoordChange`.
-/
import RicciFlowBlueprint.CovariantAlongCurve

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable {γ : ℝ → M} {t : ℝ}

omit [IsManifold I ω M] in
/-- **The differential of a curve is its velocity.** A continuous linear map out of `ℝ` is
determined by its value at `1`, so `mfderiv` of a curve is the `smulRight` of its velocity —
with no differentiability hypothesis, both sides being junk together. -/
theorem mfderiv_eq_smulRight_velocity (γ : ℝ → M) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I γ t
      = (1 : ℝ →L[ℝ] ℝ).smulRight (velocity (I := I) γ t) := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  have key : ∀ b : ℝ, mfderiv 𝓘(ℝ, ℝ) I γ t (show TangentSpace 𝓘(ℝ, ℝ) t from b)
      = b • velocity (I := I) γ t := by
    intro b
    rw [velocity, ← map_smul]
    congr 1
    show b = b • (1 : ℝ)
    rw [smul_eq_mul, mul_one]
  exact key a

set_option backward.isDefEq.respectTransparency false in
-- BENCH: geodesic-chart-velocity
/-- **The chart position's derivative is the velocity's fibre coordinate.** With
`p t = extChartAt I x₀ (γ t)`, `p'(t) = tangentCoordChange I (γ t) x₀ (γ t) (γ'(t))`.

This is `IntegralCurve/Basic.lean`'s argument with the integral-curve hypothesis replaced by
plain differentiability: compose `HasMFDerivAt` of `γ` with that of the chart, then rewrite the
chart's `mfderiv` as `tangentCoordChange`. -/
theorem hasDerivAt_extChartAt_comp {x₀ : M}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hsrc : γ t ∈ (chartAt H x₀).source) :
    HasDerivAt (fun u ↦ extChartAt I x₀ (γ u))
      (tangentCoordChange I (γ t) x₀ (γ t) (velocity (I := I) γ t)) t := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  refine (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) hγ.hasMFDerivAt).congr_mfderiv ?_
  rw [ContinuousLinearMap.ext_iff]
  intro a
  simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_smulRight_velocity,
    ContinuousLinearMap.smulRight_apply, map_smul,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl


/-- **The tangent-bundle trivialisation *is* the chart**: its fibre coordinate is the
change-of-coordinates derivative. Both sides unfold to the same `fderivWithin`. -/
theorem trivializationAt_snd_eq_tangentCoordChange (x₀ : M) {y : M} (v : TangentSpace I y) :
    (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ ⟨y, v⟩).2
      = tangentCoordChange I y x₀ y v := rfl

set_option backward.isDefEq.respectTransparency false in
-- BENCH: geodesic-chart-coordinate
/-- **The chart position's derivative is the velocity read in the trivialisation at `x₀`.**
This is the identification that turns `∇_{γ'}γ' = 0` into an ODE: the unknown of the
coordinate equation, `p' = (extChartAt I x₀ ∘ γ)'`, *is* the fibre coordinate of `γ'`. -/
theorem deriv_extChartAt_comp_eq_trivializationAt {x₀ : M}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hsrc : γ t ∈ (chartAt H x₀).source) :
    deriv (fun u ↦ extChartAt I x₀ (γ u)) t
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀
          ⟨γ t, velocity (I := I) γ t⟩).2 :=
  (hasDerivAt_extChartAt_comp hγ hsrc).deriv.trans
    (trivializationAt_snd_eq_tangentCoordChange x₀ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **`coeffAlong` for the velocity is the chart position's derivative**, read off the model
basis. So the coordinate form of `D/dt γ'` from `CovariantAlongCurve.lean` is literally an
equation in `p'` and `p''`. -/
theorem coeffAlong_velocity_eq [FiniteDimensional ℝ E] {x₀ : M}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hsrc : γ t ∈ (chartAt H x₀).source)
    (i : Fin (Module.finrank ℝ E)) :
    coeffAlong γ (velocity (I := I) γ) x₀ i t
      = (Module.finBasis ℝ E).repr (deriv (fun u ↦ extChartAt I x₀ (γ u)) t) i := by
  rw [coeffAlong, deriv_extChartAt_comp_eq_trivializationAt hγ hsrc]

end CovariantDerivative
