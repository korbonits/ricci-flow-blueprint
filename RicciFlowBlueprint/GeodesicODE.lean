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


section ODE

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M]

omit [IsManifold I ω M] [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
/-- **Differentiating a curve in `E` coordinatewise recovers it.** The basis expansion of
`q'(t)` has the derivatives of the coordinates as its coefficients. -/
theorem sum_deriv_repr_smul {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {q : ℝ → E} (hq : DifferentiableAt ℝ q t) :
    ∑ i, deriv (fun u ↦ b.repr (q u) i) t • b i = deriv q t := by
  have hcoord : ∀ i, deriv (fun u ↦ b.repr (q u) i) t = b.repr (deriv q t) i := fun i ↦
    (((b.coord i).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hq.hasDerivAt).deriv
  simp only [hcoord]
  exact b.sum_repr (deriv q t)

-- BENCH: geodesic-ode-vector-form
/-- **`D/dt` in a trivialisation, as a vector equation in `E`.** With `q u = (e⟨γ u, V u⟩)₂` the
fibre coordinates of `V`,
`(D/dt V)ᵉ = q'(t) + Γ(γ t)(γ'(t))(q(t))`.
This is `covAlong_eq_sum_of_frame` pushed through the trivialisation, and it is the shape the
ODE is solved in — no basis appears in the statement. -/
theorem trivializationAt_covAlong_eq
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
    (hW : ∀ i, CMDiff 1 (T% (W i))) (hWU : ∀ i, ∀ y ∈ U, W i y = e.localFrame b i y)
    {V : Π t : ℝ, TangentSpace I (γ t)} (hγU : γ t ∈ U)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t) :
    (e ⟨γ t, covAlong cov γ V t⟩).2
      = deriv (fun u ↦ (e ⟨γ u, V u⟩).2) t
        + christoffel cov e b W (γ t) (velocity (I := I) γ t) ((e ⟨γ t, V t⟩).2) := by
  have hmem : γ t ∈ e.baseSet := hUe hγU
  have hq : DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, V u⟩).2) t :=
    (mdiffAlongAt_iff_of_mem hγ hmem).mp hV
  have hlin : ∀ v : TangentSpace I (γ t), (e ⟨γ t, v⟩).2
      = e.continuousLinearEquivAt ℝ (γ t) hmem v := fun _ ↦ rfl
  have hWt : ∀ i, W i (γ t) = e.localFrame b i (γ t) := fun i ↦ hWU i (γ t) hγU
  rw [covAlong_eq_sum_of_frame_on cov b hU hUe hW hWU hγU hγ hV, hlin, map_sum]
  rw [christoffel, ← sum_deriv_repr_smul b hq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_add, map_smul, map_smul, hWt i, ← hlin, ← hlin,
    repr_apply_localFrame b hmem i]
  exact add_comm _ _


-- BENCH: geodesic-ode
/-- **The geodesic equation as an ODE in the chart.** With `p = extChartAt I x₀ ∘ γ`, the
`e`-coordinate of `D/dt γ'` is `p'' + Γ(γ t)(γ'(t))(p'(t))`.

Everything on the right lives in the model space `E`: `p''` is an honest second derivative of a
curve in `E`, and `Γ` is `C^k` in the point (`contMDiffAt_christoffelCoord`). -/
theorem trivializationAt_covAlong_velocity_eq
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (hW : ∀ i, CMDiff 1 (T% (W i)))
    (hWU : ∀ i, ∀ y ∈ U, W i y
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).localFrame b i y)
    (hγU : γ t ∈ U) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hγC : ∀ᶠ u in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hV : MDiffAlongAt γ (velocity (I := I) γ) t) :
    ((trivializationAt E (fun z : M ↦ TangentSpace I z) x₀)
        ⟨γ t, covAlong cov γ (velocity (I := I) γ) t⟩).2
      = deriv (deriv (fun u ↦ extChartAt I x₀ (γ u))) t
        + christoffel cov (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀) b W (γ t)
            (velocity (I := I) γ t) (deriv (fun u ↦ extChartAt I x₀ (γ u)) t) := by
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) x₀
  have hsrcU : ∀ y ∈ U, y ∈ (chartAt H x₀).source := fun y hy ↦ hbase ▸ hUe hy
  have hnear : (fun u ↦ (e ⟨γ u, velocity (I := I) γ u⟩).2)
      =ᶠ[𝓝 t] fun u ↦ deriv (fun s ↦ extChartAt I x₀ (γ s)) u := by
    filter_upwards [hγ.continuousAt (hU.mem_nhds hγU), hγC] with u hu hdu
    exact (deriv_extChartAt_comp_eq_trivializationAt hdu (hsrcU (γ u) hu)).symm
  have hval : (e ⟨γ t, velocity (I := I) γ t⟩).2
      = deriv (fun s ↦ extChartAt I x₀ (γ s)) t := hnear.eq_of_nhds
  rw [trivializationAt_covAlong_eq cov b hU hUe hW hWU hγU hγ hV, hnear.deriv_eq, hval]

/-- **The geodesic equation, solved for `p''`.** `∇_{γ'}γ' = 0` at `t` is exactly
`p''(t) = −Γ(γ t)(γ'(t))(p'(t))` — an ODE on an open subset of the model space, which is what
Picard–Lindelöf consumes. -/
theorem covAlong_velocity_eq_zero_iff
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (hW : ∀ i, CMDiff 1 (T% (W i)))
    (hWU : ∀ i, ∀ y ∈ U, W i y
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).localFrame b i y)
    (hγU : γ t ∈ U) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hγC : ∀ᶠ u in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hV : MDiffAlongAt γ (velocity (I := I) γ) t) :
    covAlong cov γ (velocity (I := I) γ) t = 0 ↔
      deriv (deriv (fun u ↦ extChartAt I x₀ (γ u))) t
        = -christoffel cov (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀) b W (γ t)
            (velocity (I := I) γ t) (deriv (fun u ↦ extChartAt I x₀ (γ u)) t) := by
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hmem : γ t ∈ e.baseSet := hUe hγU
  have hzero : covAlong cov γ (velocity (I := I) γ) t = 0
      ↔ (e ⟨γ t, covAlong cov γ (velocity (I := I) γ) t⟩).2 = 0 := by
    constructor
    · intro h; rw [h]; exact map_zero (e.continuousLinearEquivAt ℝ (γ t) hmem)
    · intro h
      have := (e.continuousLinearEquivAt ℝ (γ t) hmem).map_eq_zero_iff.mp h
      exact this
  rw [hzero, trivializationAt_covAlong_velocity_eq cov x₀ b hU hUe hW hWU hγU hγ hγC hV,
    add_eq_zero_iff_eq_neg]

end ODE

end CovariantDerivative
