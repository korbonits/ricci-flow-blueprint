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
import Mathlib.Analysis.ODE.ExistUnique
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

set_option maxSynthPendingDepth 3

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


/-! ### Γ as a bilinear map on the model space

For Picard–Lindelöf the Christoffel symbols must be a *continuous bilinear map* `E → E → E`
depending on the base point, not a family of scalars: the geodesic system on `E × E` is
`(p, v) ↦ (v, −Γ(p)(v)(v))`, and its `C¹`-ness is what the ODE theorem asks for.
-/

/-- **Γ as a continuous bilinear map on the model space.** `Γ(y)(a)(c) = ∑ᵢⱼ aʲcⁱ Γᵢⱼ(y)`,
assembled from the scalar symbols with two `smulRight`s so that no `mk₂` and no bilinearity
proof is needed — continuity and linearity in both slots hold by construction. -/
noncomputable def christoffelB
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (y : M) : E →L[ℝ] E →L[ℝ] E :=
  ∑ i, ∑ j, ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E) (b.coord j).toContinuousLinearMap
    (ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap
      (christoffelCoord cov e W i j y))

omit [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
theorem christoffelB_apply
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) {W : ι → Π y : M, TangentSpace I y}
    (y : M) (a c : E) :
    christoffelB cov e b W y a c
      = ∑ i, ∑ j, (b.repr c i * b.repr a j) • christoffelCoord cov e W i j y := by
  rw [christoffelB]
  simp only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, smul_smul]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm]


omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
/-- `christoffelB` computes `christoffel`, with the velocity read in the trivialisation. -/
theorem christoffel_eq_christoffelB
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {y : M} (hy : y ∈ e.baseSet)
    (hWy : ∀ i, W i y = e.localFrame b i y) (v : TangentSpace I y) (c : E) :
    christoffel cov e b W y v c = christoffelB cov e b W y ((e ⟨y, v⟩).2) c := by
  rw [christoffel_eq_sum cov b hy hWy v c, christoffelB_apply]

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
-- BENCH: geodesic-christoffel-regularity
/-- **Γ is `C^k` in the base point as a bilinear map.** Each scalar symbol is `C^k`
(`contMDiffAt_christoffelCoord`) and the assembly is by fixed continuous linear maps, so the
regularity survives. This is the hypothesis Picard–Lindelöf will consume. -/
theorem contMDiffAt_christoffelB
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞ω}
    [ContMDiffCovariantDerivative cov k]
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} (hW : ∀ i, CMDiff (k + 1) (T% (W i)))
    {y : M} (hy : y ∈ e.baseSet) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) k (christoffelB cov e b W) y := by
  refine ContMDiffAt.sum fun i _ ↦ ContMDiffAt.sum fun j _ ↦ ?_
  have hin : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) k
      (ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap) :=
    ContinuousLinearMap.contMDiff _
  have hout : ContMDiff 𝓘(ℝ, E →L[ℝ] E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) k
      (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E) (b.coord j).toContinuousLinearMap) :=
    ContinuousLinearMap.contMDiff _
  exact ContMDiffAt.comp y (hout _)
    (ContMDiffAt.comp y (hin _) (contMDiffAt_christoffelCoord cov hW hy i j))

section Chart

/-- **Γ as a function of the chart coordinate.** `christoffelB` is a function of the base
point `y : M`; Picard–Lindelöf wants a vector field on an open subset of the model space, so
compose with the inverse chart. -/
noncomputable def christoffelChart
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (p : E) : E →L[ℝ] E →L[ℝ] E :=
  christoffelB cov (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀) b W
    ((extChartAt I x₀).symm p)

omit [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
theorem christoffelChart_apply
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (p : E) :
    christoffelChart cov x₀ b W p
      = christoffelB cov (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀) b W
          ((extChartAt I x₀).symm p) := rfl

variable [I.Boundaryless]

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
-- BENCH: geodesic-christoffel-chart-regularity
/-- **`Γ̃` is `C^k` on the chart target.** The inverse chart is `C^ω` on `range I`, which is
everything when `M` is boundaryless, so the composite inherits `contMDiffAt_christoffelB`;
being a map between open subsets of normed spaces it is then `ContDiffAt` in the ordinary
sense, which is what the ODE theory consumes. **Boundarylessness enters exactly here**: for a
general `ModelWithCorners` the chart target is not open in `E` and `ContDiffAt` would be the
wrong predicate. -/
theorem contDiffAt_christoffelChart
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞ω}
    [ContMDiffCovariantDerivative cov k] (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} (hW : ∀ i, CMDiff (k + 1) (T% (W i)))
    {p : E} (hp : p ∈ (extChartAt I x₀).target)
    (hb : (extChartAt I x₀).symm p
      ∈ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet) :
    ContDiffAt ℝ k (christoffelChart cov x₀ b W) p := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I k (extChartAt I x₀).symm p := by
    have h := contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ω) x₀ hp
    rw [I.range_eq_univ, contMDiffWithinAt_univ] at h
    exact h.of_le le_top
  exact (ContMDiffAt.comp p (contMDiffAt_christoffelB cov b hW hb) hsymm).contDiffAt

/-! ### The geodesic system and Picard–Lindelöf

`p'' = −Γ̃(p)(p')(p')` is second order; the first-order system it is equivalent to is
`(p, v) ↦ (v, −Γ̃(p)(v)(v))` on `E × E`. Its `C^k`-ness is inherited from `Γ̃`, evaluation of a
continuous bilinear map being smooth, so Mathlib's `C¹` existence theorem applies with no
Lipschitz estimate done by hand.
-/

/-- **The geodesic vector field** on `E × E`. -/
noncomputable def geodesicField
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (z : E × E) : E × E :=
  (z.2, -christoffelChart cov x₀ b W z.1 z.2 z.2)

omit [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M]
  [I.Boundaryless] in
/-- **The geodesic field is as regular as `Γ̃`.** -/
theorem contDiffAt_geodesicField
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞ω} (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    {z : E × E} (hΓ : ContDiffAt ℝ k (christoffelChart cov x₀ b W) z.1) :
    ContDiffAt ℝ k (geodesicField cov x₀ b W) z := by
  refine ContDiffAt.prodMk contDiff_snd.contDiffAt ?_
  exact (((ContDiffAt.comp z hΓ contDiff_fst.contDiffAt).clm_apply
    contDiff_snd.contDiffAt).clm_apply contDiff_snd.contDiffAt).neg

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
-- BENCH: geodesic-ode-existence
/-- **The geodesic system has a local solution.** Picard–Lindelöf, in the form Mathlib states
for a `C¹` vector field on a normed space — so no Lipschitz estimate is done here. -/
theorem exists_solution_geodesicField
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞ω} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov k] (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} (hW : ∀ i, CMDiff (k + 1) (T% (W i)))
    {p₀ : E} (hp : p₀ ∈ (extChartAt I x₀).target)
    (hb : (extChartAt I x₀).symm p₀
      ∈ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (v₀ : E) (t₀ : ℝ) :
    ∃ z : ℝ → E × E, z t₀ = (p₀, v₀) ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt z (geodesicField cov x₀ b W (z t)) t := by
  exact ((contDiffAt_geodesicField cov x₀ b W
    (contDiffAt_christoffelChart cov x₀ b hW hp hb)).of_le
    hk).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-! ### From the ODE solution back to a geodesic

Pulling the solution back through `(extChartAt I x₀).symm` gives a curve on `M`, and
`covAlong_velocity_eq_zero_iff` — read from right to left — says it is a geodesic. Everything
the *iff* asks on the manifold side (differentiability of `γ`, differentiability of the velocity
*along* `γ`) is read off the solution through the same identification: the chart coordinate of
the velocity is `p'`, which is the second component of the solution.
-/

-- BENCH: geodesic-existence
/-- **Local existence of geodesics.** Through any point, in any direction, there is a geodesic
on some interval about `0`. The initial condition is stated in the total space of `TM`, which
packages `γ 0 = x₀` and `γ'(0) = v₀` into one equation with no dependent-type cast. -/
theorem exists_isGeodesicOn
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞ω} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov k] (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} (hW : ∀ i, CMDiff (k + 1) (T% (W i)))
    {U : Set M} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hUe : U ⊆ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (hWU : ∀ i, ∀ y ∈ U, W i y
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).localFrame b i y)
    (v₀ : TangentSpace I x₀) :
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M,
      (⟨c 0, velocity (I := I) c 0⟩ : TangentBundle I M) = ⟨x₀, v₀⟩ ∧
        IsGeodesicOn cov c (Set.Ioo (-ε) ε) := by
  classical
  have hW1 : ∀ i, CMDiff (1 : ℕ∞ω) (T% (W i)) := fun i ↦ (hW i).of_le le_add_self
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := hUe hx₀U
  have hp₀t : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target := mem_extChartAt_target x₀
  have hsymm₀ : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := extChartAt_to_inv x₀
  obtain ⟨z, hz0, ε₁, hε₁, hzd⟩ :=
    exists_solution_geodesicField cov hk x₀ b hW hp₀t (by rw [hsymm₀]; exact hx₀e)
      ((e ⟨x₀, v₀⟩).2) 0
  simp only [zero_sub, zero_add] at hzd
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-ε₁) ε₁ := ⟨neg_lt_zero.mpr hε₁, hε₁⟩
  -- the two components of the solution
  have hqd : ∀ u ∈ Set.Ioo (-ε₁) ε₁, HasDerivAt (fun s ↦ (z s).1) (z u).2 u := fun u hu ↦
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt u (hzd u hu)
  have hvd : ∀ u ∈ Set.Ioo (-ε₁) ε₁, HasDerivAt (fun s ↦ (z s).2)
      (-christoffelChart cov x₀ b W (z u).1 (z u).2 (z u).2) u := fun u hu ↦
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt u (hzd u hu)
  set c : ℝ → M := fun u ↦ (extChartAt I x₀).symm (z u).1 with hcdef
  have hq0 : (z 0).1 = extChartAt I x₀ x₀ := by rw [hz0]
  have hc0 : c 0 = x₀ := by simp only [hcdef, hq0, hsymm₀]
  -- shrink the interval so that the chart and the frame are both available
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ),
      u ∈ Set.Ioo (-ε₁) ε₁ ∧ (z u).1 ∈ (extChartAt I x₀).target ∧ c u ∈ U := by
    have hqc : ContinuousAt (fun s ↦ (z s).1) 0 := (hqd 0 hmem0).continuousAt
    have h1 : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Set.Ioo (-ε₁) ε₁ := isOpen_Ioo.mem_nhds hmem0
    have h2 : ∀ᶠ u in 𝓝 (0 : ℝ), (z u).1 ∈ (extChartAt I x₀).target :=
      hqc.preimage_mem_nhds ((isOpen_extChartAt_target x₀).mem_nhds (by rw [hq0]; exact hp₀t))
    have hcc : ContinuousAt c 0 :=
      (continuousAt_extChartAt_symm'' (by rw [hq0]; exact hp₀t)).comp hqc
    have h3 : ∀ᶠ u in 𝓝 (0 : ℝ), c u ∈ U :=
      hcc.preimage_mem_nhds (hU.mem_nhds (by rw [hc0]; exact hx₀U))
    filter_upwards [h1, h2, h3] with u a₁ a₂ a₃ using ⟨a₁, a₂, a₃⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hgood : ∀ u ∈ Set.Ioo (-δ) δ,
      u ∈ Set.Ioo (-ε₁) ε₁ ∧ (z u).1 ∈ (extChartAt I x₀).target ∧ c u ∈ U := by
    intro u hu
    exact hball (by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨hu.1, hu.2⟩)
  have h0δ : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  -- the manifold-side facts, all read off the solution
  have hchart : ∀ u ∈ Set.Ioo (-δ) δ, extChartAt I x₀ (c u) = (z u).1 := fun u hu ↦
    PartialEquiv.right_inv _ (hgood u hu).2.1
  have hcdiff : ∀ u ∈ Set.Ioo (-δ) δ, MDifferentiableAt 𝓘(ℝ, ℝ) I c u := by
    intro u hu
    have hsymmC : ContMDiffAt 𝓘(ℝ, E) I (1 : ℕ∞ω) (extChartAt I x₀).symm (z u).1 := by
      have h := contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ω) x₀ (hgood u hu).2.1
      rw [I.range_eq_univ, contMDiffWithinAt_univ] at h
      exact h.of_le le_top
    have hqm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s ↦ (z s).1) u :=
      mdifferentiableAt_iff_differentiableAt.mpr (hqd u (hgood u hu).1).differentiableAt
    exact (hsymmC.mdifferentiableAt one_ne_zero).comp u hqm
  have hsrc : ∀ u ∈ Set.Ioo (-δ) δ, c u ∈ (chartAt H x₀).source := by
    intro u hu
    have h := hUe (hgood u hu).2.2
    rwa [he, TangentBundle.trivializationAt_baseSet (I := I) x₀] at h
  have hderivq : ∀ u ∈ Set.Ioo (-δ) δ,
      deriv (fun s ↦ extChartAt I x₀ (c s)) u = (z u).2 := by
    intro u hu
    have heq : (fun s ↦ extChartAt I x₀ (c s)) =ᶠ[𝓝 u] fun s ↦ (z s).1 := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs using hchart s hs
    rw [heq.deriv_eq]
    exact (hqd u (hgood u hu).1).deriv
  have hcoord : ∀ u ∈ Set.Ioo (-δ) δ, (e ⟨c u, velocity (I := I) c u⟩).2 = (z u).2 := by
    intro u hu
    rw [he, ← deriv_extChartAt_comp_eq_trivializationAt (hcdiff u hu) (hsrc u hu)]
    exact hderivq u hu
  have hV : ∀ u ∈ Set.Ioo (-δ) δ, MDiffAlongAt c (velocity (I := I) c) u := by
    intro u hu
    rw [mdiffAlongAt_iff_of_mem (e := e) (hcdiff u hu) (hUe (hgood u hu).2.2)]
    have heq : (fun s ↦ (e ⟨c s, velocity (I := I) c s⟩).2) =ᶠ[𝓝 u] fun s ↦ (z s).2 := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs using hcoord s hs
    exact ((hvd u (hgood u hu).1).differentiableAt).congr_of_eventuallyEq heq
  refine ⟨δ, hδ, c, ?_, ?_⟩
  · have hs1 : (⟨c 0, velocity (I := I) c 0⟩ : TangentBundle I M) ∈ e.source :=
      e.mem_source.mpr (hUe (hgood 0 h0δ).2.2)
    have hs2 : (⟨x₀, v₀⟩ : TangentBundle I M) ∈ e.source := e.mem_source.mpr hx₀e
    refine e.toPartialHomeomorph.injOn hs1 hs2 ?_
    show (e ⟨c 0, velocity (I := I) c 0⟩ : M × E) = e ⟨x₀, v₀⟩
    refine Prod.ext ?_ ?_
    · rw [e.coe_fst hs1, e.coe_fst hs2]; exact hc0
    · rw [hcoord 0 h0δ, hz0]
  · intro t ht
    have hmemU : c t ∈ U := (hgood t ht).2.2
    rw [covAlong_velocity_eq_zero_iff cov x₀ b hU hUe hW1 hWU hmemU (hcdiff t ht)
      (by filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hcdiff s hs) (hV t ht)]
    have h1 : deriv (fun s ↦ extChartAt I x₀ (c s)) =ᶠ[𝓝 t] fun s ↦ (z s).2 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hderivq s hs
    rw [h1.deriv_eq, (hvd t (hgood t ht).1).deriv,
      christoffel_eq_christoffelB cov b (hUe hmemU) (fun i ↦ hWU i (c t) hmemU),
      hcoord t ht, hderivq t ht, christoffelChart]

-- BENCH: geodesic-existence-clean
/-- **Local existence of geodesics, with no frame data.** The frame comes from
`exists_frame_on_open` around `x₀`, at the level the Christoffel symbols need. -/
theorem exists_isGeodesicOn'
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    (x₀ : M) (v₀ : TangentSpace I x₀) :
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M,
      (⟨c 0, velocity (I := I) c 0⟩ : TangentBundle I M) = ⟨x₀, v₀⟩ ∧
        IsGeodesicOn cov c (Set.Ioo (-ε) ε) := by
  obtain ⟨U, W, hU, hx₀U, hUe, hW, hWU⟩ :=
    exists_frame_on_open (n := k + 1) (e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀)
      (Module.finBasis ℝ E) (mem_baseSet_trivializationAt E _ x₀)
  refine exists_isGeodesicOn cov (k := (k : ℕ∞ω)) (by exact_mod_cast hk) x₀
    (Module.finBasis ℝ E) (fun i ↦ ?_) hU hx₀U hUe hWU v₀
  have h := hW i
  have hcast : ((k + 1 : ℕ∞) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by norm_cast
  rwa [hcast] at h

/-! ### Uniqueness

The same identification runs backwards: a geodesic, read in the chart, *solves* the system, so
Mathlib's ODE uniqueness applies. The hypotheses are exactly the ones the geodesic equation
already needs — `c` differentiable and its velocity differentiable *along* `c` — because the
chart coordinate of the velocity is `p'`, so differentiability along `c` is what makes `p'`
differentiable.
-/

omit [I.Boundaryless] in
-- BENCH: geodesic-solves-system
/-- **A geodesic solves the first-order system**, in the chart at `x₀`. -/
theorem hasDerivAt_geodesicField_of_isGeodesic
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (hW : ∀ i, CMDiff (1 : ℕ∞ω) (T% (W i)))
    (hWU : ∀ i, ∀ y ∈ U, W i y
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).localFrame b i y)
    {c : ℝ → M} {t : ℝ} (hcU : ∀ᶠ u in 𝓝 t, c u ∈ U)
    (hcd : ∀ᶠ u in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I c u)
    (hcV : ∀ᶠ u in 𝓝 t, MDiffAlongAt c (velocity (I := I) c) u)
    (hg : ∀ᶠ u in 𝓝 t, covAlong cov c (velocity (I := I) c) u = 0) :
    HasDerivAt (fun u ↦ (extChartAt I x₀ (c u),
        ((trivializationAt E (fun z : M ↦ TangentSpace I z) x₀)
          ⟨c u, velocity (I := I) c u⟩).2))
      (geodesicField cov x₀ b W (extChartAt I x₀ (c t),
        ((trivializationAt E (fun z : M ↦ TangentSpace I z) x₀)
          ⟨c t, velocity (I := I) c t⟩).2)) t := by
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) x₀
  have hsrc : ∀ u ∈ {u | c u ∈ U}, c u ∈ (chartAt H x₀).source := fun u hu ↦ hbase ▸ hUe hu
  have hsrct : c t ∈ (chartAt H x₀).source := hsrc t hcU.self_of_nhds
  -- the chart position differentiates to the fibre coordinate of the velocity
  have hpos : ∀ᶠ u in 𝓝 t, HasDerivAt (fun s ↦ extChartAt I x₀ (c s))
      ((e ⟨c u, velocity (I := I) c u⟩).2) u := by
    filter_upwards [hcU, hcd] with u hu hdu
    exact (hasDerivAt_extChartAt_comp hdu (hsrc u hu)).congr_deriv
      (trivializationAt_snd_eq_tangentCoordChange x₀ _).symm
  have hderiv : ∀ᶠ u in 𝓝 t, deriv (fun s ↦ extChartAt I x₀ (c s) : ℝ → E) u
      = (e ⟨c u, velocity (I := I) c u⟩).2 := by
    filter_upwards [hpos] with u hu using hu.deriv
  -- and that coordinate differentiates to the Christoffel term
  have hdiff : DifferentiableAt ℝ (fun u ↦ (e ⟨c u, velocity (I := I) c u⟩).2) t :=
    (mdiffAlongAt_iff_of_mem (e := e) hcd.self_of_nhds
      (hUe hcU.self_of_nhds)).mp hcV.self_of_nhds
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ (c t)) = c t :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hsrct)
  have hval : deriv (fun u ↦ (e ⟨c u, velocity (I := I) c u⟩).2) t
      = -christoffelChart cov x₀ b W (extChartAt I x₀ (c t))
          ((e ⟨c t, velocity (I := I) c t⟩).2) ((e ⟨c t, velocity (I := I) c t⟩).2) := by
    have heqf : (fun u ↦ (e ⟨c u, velocity (I := I) c u⟩).2)
        =ᶠ[𝓝 t] deriv (fun s ↦ extChartAt I x₀ (c s) : ℝ → E) := by
      filter_upwards [hderiv] with u hu using hu.symm
    rw [heqf.deriv_eq]
    rw [(covAlong_velocity_eq_zero_iff cov x₀ b hU hUe hW hWU hcU.self_of_nhds
      hcd.self_of_nhds hcd hcV.self_of_nhds).mp hg.self_of_nhds]
    rw [christoffel_eq_christoffelB cov b (hUe hcU.self_of_nhds)
      (fun i ↦ hWU i (c t) hcU.self_of_nhds), hderiv.self_of_nhds, christoffelChart, hleft]
  refine (hpos.self_of_nhds.prodMk ?_)
  rw [← hval]
  exact hdiff.hasDerivAt

-- BENCH: geodesic-unique
/-- **Uniqueness of geodesics.** Two geodesics through the same point with the same velocity
agree near that time. Read in the chart both solve the same `C¹` system, so Mathlib's
`ODE_solution_unique_of_eventually` applies; the Lipschitz constant comes from
`ContDiffAt.exists_lipschitzOnWith`, not from any estimate done here. -/
theorem eventuallyEq_of_isGeodesic
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞ω} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov k] (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} (hW : ∀ i, CMDiff (k + 1) (T% (W i)))
    {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (hWU : ∀ i, ∀ y ∈ U, W i y
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).localFrame b i y)
    {c₁ c₂ : ℝ → M} {t₀ : ℝ}
    (h₁U : ∀ᶠ u in 𝓝 t₀, c₁ u ∈ U)
    (h₁d : ∀ᶠ u in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I c₁ u)
    (h₁V : ∀ᶠ u in 𝓝 t₀, MDiffAlongAt c₁ (velocity (I := I) c₁) u)
    (h₁g : ∀ᶠ u in 𝓝 t₀, covAlong cov c₁ (velocity (I := I) c₁) u = 0)
    (h₂U : ∀ᶠ u in 𝓝 t₀, c₂ u ∈ U)
    (h₂d : ∀ᶠ u in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I c₂ u)
    (h₂V : ∀ᶠ u in 𝓝 t₀, MDiffAlongAt c₂ (velocity (I := I) c₂) u)
    (h₂g : ∀ᶠ u in 𝓝 t₀, covAlong cov c₂ (velocity (I := I) c₂) u = 0)
    (hinit : (⟨c₁ t₀, velocity (I := I) c₁ t₀⟩ : TangentBundle I M)
      = ⟨c₂ t₀, velocity (I := I) c₂ t₀⟩) :
    c₁ =ᶠ[𝓝 t₀] c₂ := by
  have hW1 : ∀ i, CMDiff (1 : ℕ∞ω) (T% (W i)) := fun i ↦ (hW i).of_le le_add_self
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) x₀
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ℝ → E × E, z₁ = fun u ↦
      (extChartAt I x₀ (c₁ u), (e ⟨c₁ u, velocity (I := I) c₁ u⟩).2) := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z₂ : ℝ → E × E, z₂ = fun u ↦
      (extChartAt I x₀ (c₂ u), (e ⟨c₂ u, velocity (I := I) c₂ u⟩).2) := ⟨_, rfl⟩
  have hsol₁ : ∀ᶠ u in 𝓝 t₀, HasDerivAt z₁ (geodesicField cov x₀ b W (z₁ u)) u := by
    filter_upwards [eventually_eventually_nhds.mpr h₁U, eventually_eventually_nhds.mpr h₁d,
      eventually_eventually_nhds.mpr h₁V, eventually_eventually_nhds.mpr h₁g] with u a₁ a₂ a₃ a₄
    rw [hz₁]
    exact hasDerivAt_geodesicField_of_isGeodesic cov x₀ b hU hUe hW1 hWU a₁ a₂ a₃ a₄
  have hsol₂ : ∀ᶠ u in 𝓝 t₀, HasDerivAt z₂ (geodesicField cov x₀ b W (z₂ u)) u := by
    filter_upwards [eventually_eventually_nhds.mpr h₂U, eventually_eventually_nhds.mpr h₂d,
      eventually_eventually_nhds.mpr h₂V, eventually_eventually_nhds.mpr h₂g] with u a₁ a₂ a₃ a₄
    rw [hz₂]
    exact hasDerivAt_geodesicField_of_isGeodesic cov x₀ b hU hUe hW1 hWU a₁ a₂ a₃ a₄
  have hb0 : c₁ t₀ = c₂ t₀ := congrArg TotalSpace.proj hinit
  have hinit' : z₁ t₀ = z₂ t₀ := by
    rw [hz₁, hz₂]
    refine Prod.ext ?_ ?_
    · show extChartAt I x₀ (c₁ t₀) = extChartAt I x₀ (c₂ t₀)
      rw [hb0]
    · show (e ⟨c₁ t₀, velocity (I := I) c₁ t₀⟩).2 = (e ⟨c₂ t₀, velocity (I := I) c₂ t₀⟩).2
      rw [hinit]
  -- the field is `C¹` at the common initial point, hence locally Lipschitz
  have hsrc₁ : c₁ t₀ ∈ (chartAt H x₀).source := hbase ▸ hUe h₁U.self_of_nhds
  have hptgt : extChartAt I x₀ (c₁ t₀) ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrc₁)
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ (c₁ t₀)) = c₁ t₀ :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hsrc₁)
  have hΓ : ContDiffAt ℝ 1 (christoffelChart cov x₀ b W) (extChartAt I x₀ (c₁ t₀)) :=
    (contDiffAt_christoffelChart cov x₀ b hW hptgt (by rw [hleft]; exact hUe h₁U.self_of_nhds)).of_le
      hk
  have hF : ContDiffAt ℝ 1 (geodesicField cov x₀ b W) (z₁ t₀) := by
    refine contDiffAt_geodesicField cov x₀ b W ?_
    rw [hz₁]
    exact hΓ
  obtain ⟨K, S, hS, hlip⟩ := hF.exists_lipschitzOnWith
  have hmem₁ : ∀ᶠ u in 𝓝 t₀, z₁ u ∈ S :=
    hsol₁.self_of_nhds.continuousAt.preimage_mem_nhds hS
  have hmem₂ : ∀ᶠ u in 𝓝 t₀, z₂ u ∈ S :=
    hsol₂.self_of_nhds.continuousAt.preimage_mem_nhds (hinit' ▸ hS)
  have hzeq : z₁ =ᶠ[𝓝 t₀] z₂ :=
    ODE_solution_unique_of_eventually (v := fun _ ↦ geodesicField cov x₀ b W)
      (s := fun _ ↦ S) (K := K) (Filter.Eventually.of_forall fun _ ↦ hlip)
      (by filter_upwards [hsol₁, hmem₁] with u a₁ a₂ using ⟨a₁, a₂⟩)
      (by filter_upwards [hsol₂, hmem₂] with u a₁ a₂ using ⟨a₁, a₂⟩) hinit'
  -- pull the equality back through the chart
  filter_upwards [hzeq, h₁U, h₂U] with u hu hu₁ hu₂
  have e₁ : (extChartAt I x₀).symm (extChartAt I x₀ (c₁ u)) = c₁ u :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hbase ▸ hUe hu₁)
  have e₂ : (extChartAt I x₀).symm (extChartAt I x₀ (c₂ u)) = c₂ u :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hbase ▸ hUe hu₂)
  have : extChartAt I x₀ (c₁ u) = extChartAt I x₀ (c₂ u) := by
    have := congrArg Prod.fst hu
    rwa [hz₁, hz₂] at this
  rw [← e₁, ← e₂, this]

-- BENCH: geodesic-unique-clean
/-- **Uniqueness of geodesics, with no frame data.** The frame comes from
`exists_frame_on_open` around the common initial point, and the two curves stay in its open set
by continuity. -/
theorem eventuallyEq_of_isGeodesic'
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    {c₁ c₂ : ℝ → M} {t₀ : ℝ}
    (h₁d : ∀ᶠ u in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I c₁ u)
    (h₁V : ∀ᶠ u in 𝓝 t₀, MDiffAlongAt c₁ (velocity (I := I) c₁) u)
    (h₁g : ∀ᶠ u in 𝓝 t₀, covAlong cov c₁ (velocity (I := I) c₁) u = 0)
    (h₂d : ∀ᶠ u in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I c₂ u)
    (h₂V : ∀ᶠ u in 𝓝 t₀, MDiffAlongAt c₂ (velocity (I := I) c₂) u)
    (h₂g : ∀ᶠ u in 𝓝 t₀, covAlong cov c₂ (velocity (I := I) c₂) u = 0)
    (hinit : (⟨c₁ t₀, velocity (I := I) c₁ t₀⟩ : TangentBundle I M)
      = ⟨c₂ t₀, velocity (I := I) c₂ t₀⟩) :
    c₁ =ᶠ[𝓝 t₀] c₂ := by
  have hb0 : c₁ t₀ = c₂ t₀ := congrArg TotalSpace.proj hinit
  obtain ⟨U, W, hU, hx₀U, hUe, hW, hWU⟩ :=
    exists_frame_on_open (n := k + 1)
      (e := trivializationAt E (fun z : M ↦ TangentSpace I z) (c₁ t₀))
      (Module.finBasis ℝ E) (mem_baseSet_trivializationAt E _ (c₁ t₀))
  have hcast : ((k + 1 : ℕ∞) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by norm_cast
  have h₁U : ∀ᶠ u in 𝓝 t₀, c₁ u ∈ U :=
    h₁d.self_of_nhds.continuousAt.preimage_mem_nhds (hU.mem_nhds hx₀U)
  have h₂U : ∀ᶠ u in 𝓝 t₀, c₂ u ∈ U :=
    h₂d.self_of_nhds.continuousAt.preimage_mem_nhds (hU.mem_nhds (hb0 ▸ hx₀U))
  exact eventuallyEq_of_isGeodesic cov (k := (k : ℕ∞ω)) (by exact_mod_cast hk) (c₁ t₀)
    (Module.finBasis ℝ E) (fun i ↦ by have h := hW i; rwa [hcast] at h) hU hUe hWU
    h₁U h₁d h₁V h₁g h₂U h₂d h₂V h₂g hinit

end Chart


end ODE

end CovariantDerivative
