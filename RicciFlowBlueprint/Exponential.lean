/-
Affine reparametrisation of geodesics, and the exponential map.

`GeodesicODE.lean` turns `∇_{γ'}γ' = 0` into `p'' = −Γ̃(p)(p')(p')` in a chart and solves it
both ways. The next fact `exp` needs is that the equation is invariant under `t ↦ t·a`, and in
the chart that is immediate: `p_σ'' = a² p_γ''` while `Γ̃` is bilinear, so the two factors of
`a` on the right match the `a²` on the left. **No new work on `IsCovDerivAlong` is needed** —
this is `covAlong_velocity_eq_zero_iff_chart` plus the chain rule.
-/
import RicciFlowBlueprint.GeodesicODE

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-! ### The velocity under an affine reparametrisation -/

omit [IsManifold I ω M] in
set_option backward.isDefEq.respectTransparency false in
-- BENCH: velocity-comp-mul
/-- **The chain rule for `velocity`.** Scaling the parameter scales the velocity. -/
theorem velocity_comp_mul {γ : ℝ → M} (a t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (t * a)) :
    velocity (I := I) (fun s ↦ γ (s * a)) t = a • velocity (I := I) γ (t * a) := by
  have hd : HasDerivAt (fun s : ℝ ↦ s * a) a t := by
    simpa using (hasDerivAt_id t).mul_const a
  have hfd : HasFDerivAt (fun s : ℝ ↦ s * a) ((1 : ℝ →L[ℝ] ℝ).smulRight a) t :=
    hasDerivAt_iff_hasFDerivAt.mp hd
  have hf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ s * a) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight a) := hasMFDerivAt_iff_hasFDerivAt.mpr hfd
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ γ (s * a)) t
      ((mfderiv 𝓘(ℝ, ℝ) I γ (t * a)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight a)) :=
    hγ.hasMFDerivAt.comp t hf
  have hv : velocity (I := I) (fun s ↦ γ (s * a)) t
      = mfderiv 𝓘(ℝ, ℝ) I γ (t * a) (((1 : ℝ →L[ℝ] ℝ).smulRight a) (1 : ℝ)) := by
    rw [velocity, hcomp.mfderiv]
    rfl
  rw [hv, mfderiv_eq_smulRight_velocity]
  show ((1 : ℝ →L[ℝ] ℝ) (((1 : ℝ →L[ℝ] ℝ).smulRight a) (1 : ℝ)))
      • velocity (I := I) γ (t * a) = a • velocity (I := I) γ (t * a)
  norm_num

/-! ### Affine reparametrisation

In the chart the geodesic equation is `p'' = −Γ̃(p)(p')(p')`. Under `t ↦ t·a` the left side
picks up `a²` and each slot of `Γ̃` picks up one `a`, so the equation is invariant — and since
`Γ̃` is *bilinear by construction* (`christoffelB`), that is one `map_smul` on each side.
No case split on `a = 0` is needed: there both sides are zero.
-/

section Reparam

set_option maxSynthPendingDepth 3

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]

omit [I.Boundaryless] in
-- BENCH: geodesic-reparam
/-- **An affine reparametrisation of a geodesic is a geodesic.** The chart equation is
`p'' = −Γ̃(p)(p')(p')`; reparametrising by `s ↦ s·a` multiplies the left side by `a²` and each
slot of `Γ̃` by `a`, so it is invariant. Note that boundarylessness is **not** needed: the
argument reads the equation in a chart but never differentiates the inverse chart. -/
theorem covAlong_velocity_comp_mul_eq_zero
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (x₀ : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).baseSet)
    (hW : ∀ i, CMDiff (1 : ℕ∞ω) (T% (W i)))
    (hWU : ∀ i, ∀ y ∈ U, W i y
      = (trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).localFrame b i y)
    {c : ℝ → M} {t a : ℝ}
    (hcU : ∀ᶠ u in 𝓝 (t * a), c u ∈ U)
    (hcd : ∀ᶠ u in 𝓝 (t * a), MDifferentiableAt 𝓘(ℝ, ℝ) I c u)
    (hcV : ∀ᶠ u in 𝓝 (t * a), MDiffAlongAt c (velocity (I := I) c) u)
    (hg : ∀ᶠ u in 𝓝 (t * a), covAlong cov c (velocity (I := I) c) u = 0) :
    covAlong cov (fun s ↦ c (s * a)) (velocity (I := I) (fun s ↦ c (s * a))) t = 0 := by
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) x₀
  -- the solution attached to `c`
  obtain ⟨p, hp⟩ : ∃ p : ℝ → E, p = fun u ↦ extChartAt I x₀ (c u) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ → E, v = fun u ↦ (e ⟨c u, velocity (I := I) c u⟩).2 := ⟨_, rfl⟩
  have hsol : ∀ᶠ u in 𝓝 (t * a), HasDerivAt (fun s ↦ (p s, v s))
      (geodesicField cov x₀ b W (p u, v u)) u := by
    filter_upwards [eventually_eventually_nhds.mpr hcU, eventually_eventually_nhds.mpr hcd,
      eventually_eventually_nhds.mpr hcV, eventually_eventually_nhds.mpr hg] with u a₁ a₂ a₃ a₄
    rw [hp, hv]
    exact hasDerivAt_geodesicField_of_isGeodesic cov x₀ b hU hUe hW hWU a₁ a₂ a₃ a₄
  have hpd : ∀ᶠ u in 𝓝 (t * a), HasDerivAt p (v u) u := by
    filter_upwards [hsol] with u hu
    exact (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt u hu
  have hvd : ∀ᶠ u in 𝓝 (t * a),
      HasDerivAt v (-christoffelChart cov x₀ b W (p u) (v u) (v u)) u := by
    filter_upwards [hsol] with u hu
    exact (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt u hu
  -- transport the hypotheses along `s ↦ s * a`
  have hmul : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ r * a) a s := fun s ↦ by
    simpa using (hasDerivAt_id s).mul_const a
  have htend : Filter.Tendsto (fun s : ℝ ↦ s * a) (𝓝 t) (𝓝 (t * a)) :=
    (hmul t).continuousAt
  have hfm : ∀ s : ℝ, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ r * a) s := fun s ↦
    mdifferentiableAt_iff_differentiableAt.mpr (hmul s).differentiableAt
  set σ : ℝ → M := fun s ↦ c (s * a) with hσ
  have hσU : ∀ᶠ u in 𝓝 t, σ u ∈ U := htend.eventually hcU
  have hσd : ∀ᶠ u in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I σ u := by
    filter_upwards [htend.eventually hcd] with u hu
    exact hu.comp u (hfm u)
  -- the chart position of `σ` is `p (· * a)`
  have hchart : (fun u ↦ extChartAt I x₀ (σ u)) = fun u ↦ p (u * a) := by
    funext u; rw [hp]
  -- the fibre coordinate of `σ'` is `a • v (· * a)`
  have hcoord : ∀ u ∈ {u : ℝ | σ u ∈ U}, MDifferentiableAt 𝓘(ℝ, ℝ) I c (u * a) →
      (e ⟨σ u, velocity (I := I) σ u⟩).2 = a • v (u * a) := by
    intro u hu hdu
    have hmem : σ u ∈ e.baseSet := hUe hu
    have hlin : ∀ w : TangentSpace I (σ u), (e ⟨σ u, w⟩).2
        = e.continuousLinearEquivAt ℝ (σ u) hmem w := fun _ ↦ rfl
    have hvel : velocity (I := I) σ u = a • velocity (I := I) c (u * a) :=
      velocity_comp_mul a u hdu
    rw [hvel, hlin, map_smul, ← hlin, hv]
  have hσcoord : (fun u ↦ (e ⟨σ u, velocity (I := I) σ u⟩).2) =ᶠ[𝓝 t] fun u ↦ a • v (u * a) := by
    filter_upwards [hσU, htend.eventually hcd] with u hu hdu using hcoord u hu hdu
  -- the two derivatives of the reparametrised chart position
  have hqd : ∀ᶠ u in 𝓝 t, HasDerivAt (fun s ↦ p (s * a)) (a • v (u * a)) u := by
    filter_upwards [htend.eventually hpd] with u hu
    exact HasDerivAt.scomp u hu (hmul u)
  have hq'd : ∀ᶠ u in 𝓝 t, HasDerivAt (fun s ↦ a • v (s * a))
      (a • (a • -christoffelChart cov x₀ b W (p (u * a)) (v (u * a)) (v (u * a)))) u := by
    filter_upwards [htend.eventually hvd] with u hu
    exact (HasDerivAt.scomp u hu (hmul u)).const_smul a
  have hderivq : deriv (fun u ↦ extChartAt I x₀ (σ u) : ℝ → E) =ᶠ[𝓝 t]
      fun u ↦ a • v (u * a) := by
    filter_upwards [hqd] with u hu
    rw [hchart]
    exact hu.deriv
  have hσV : MDiffAlongAt σ (velocity (I := I) σ) t := by
    rw [mdiffAlongAt_iff_of_mem (e := e) hσd.self_of_nhds (hUe hσU.self_of_nhds)]
    exact ((hq'd.self_of_nhds).differentiableAt).congr_of_eventuallyEq hσcoord
  -- and the equation, by bilinearity of `Γ̃`
  have hpt : extChartAt I x₀ (σ t) = p (t * a) := by rw [hp]
  rw [covAlong_velocity_eq_zero_iff_chart cov x₀ b hU hUe hW hWU hσU.self_of_nhds
    hσd.self_of_nhds hσd hσV, hderivq.deriv_eq, hderivq.self_of_nhds, hpt,
    (hq'd.self_of_nhds).deriv]
  simp only [map_smul, smul_apply, smul_neg, smul_smul]

omit [I.Boundaryless] in
/-- **Reparametrisation with no frame data.** -/
theorem covAlong_velocity_comp_mul_eq_zero'
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {c : ℝ → M} {t a : ℝ}
    (hcd : ∀ᶠ u in 𝓝 (t * a), MDifferentiableAt 𝓘(ℝ, ℝ) I c u)
    (hcV : ∀ᶠ u in 𝓝 (t * a), MDiffAlongAt c (velocity (I := I) c) u)
    (hg : ∀ᶠ u in 𝓝 (t * a), covAlong cov c (velocity (I := I) c) u = 0) :
    covAlong cov (fun s ↦ c (s * a)) (velocity (I := I) (fun s ↦ c (s * a))) t = 0 := by
  obtain ⟨U, W, hU, hxU, hUe, hW, hWU⟩ :=
    exists_frame_on_open (n := 1)
      (e := trivializationAt E (fun z : M ↦ TangentSpace I z) (c (t * a)))
      (Module.finBasis ℝ E) (mem_baseSet_trivializationAt E _ (c (t * a)))
  have hcU : ∀ᶠ u in 𝓝 (t * a), c u ∈ U :=
    hcd.self_of_nhds.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
  exact covAlong_velocity_comp_mul_eq_zero cov (c (t * a)) (Module.finBasis ℝ E) hU hUe
    (by exact_mod_cast hW) hWU hcU hcd hcV hg

omit [I.Boundaryless] in
-- BENCH: geodesic-reparam-set
/-- **`IsGeodesicOn` is invariant under `t ↦ t·a`.** -/
theorem isGeodesicOn_comp_mul
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {c : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s) (a : ℝ)
    (hcd : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c u)
    (hcV : ∀ u ∈ s, MDiffAlongAt c (velocity (I := I) c) u)
    (hg : IsGeodesicOn cov c s) :
    IsGeodesicOn cov (fun r ↦ c (r * a)) {u : ℝ | u * a ∈ s} := by
  intro t ht
  have hmem : ∀ᶠ u in 𝓝 (t * a), u ∈ s := hs.mem_nhds ht
  exact covAlong_velocity_comp_mul_eq_zero' cov
    (by filter_upwards [hmem] with u hu using hcd u hu)
    (by filter_upwards [hmem] with u hu using hcV u hu)
    (by filter_upwards [hmem] with u hu using hg u hu)

end Reparam

end CovariantDerivative
