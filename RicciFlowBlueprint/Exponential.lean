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

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] in
/-- **The velocity of a reparametrised curve is differentiable along it.** Its fibre coordinate
is `a • v(u·a)` with `v` the coordinate for the original curve, which
`mdiffAlongAt_iff_of_mem` says is differentiable. -/
theorem mdiffAlongAt_velocity_comp_mul {c : ℝ → M} {t a : ℝ}
    (hcd : ∀ᶠ u in 𝓝 (t * a), MDifferentiableAt 𝓘(ℝ, ℝ) I c u)
    (hcV : ∀ᶠ u in 𝓝 (t * a), MDiffAlongAt c (velocity (I := I) c) u) :
    MDiffAlongAt (fun s ↦ c (s * a)) (velocity (I := I) (fun s ↦ c (s * a))) t := by
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) (c (t * a)) with he
  have hmem₀ : c (t * a) ∈ e.baseSet := mem_baseSet_trivializationAt E _ (c (t * a))
  have hb : ∀ᶠ u in 𝓝 (t * a), c u ∈ e.baseSet :=
    hcd.self_of_nhds.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hmem₀)
  have hmul : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ r * a) a s := fun s ↦ by
    simpa using (hasDerivAt_id s).mul_const a
  have htend : Filter.Tendsto (fun s : ℝ ↦ s * a) (𝓝 t) (𝓝 (t * a)) := (hmul t).continuousAt
  have hvdiff : DifferentiableAt ℝ (fun r ↦ (e ⟨c r, velocity (I := I) c r⟩).2) (t * a) :=
    (mdiffAlongAt_iff_of_mem (e := e) hcd.self_of_nhds hmem₀).mp hcV.self_of_nhds
  have hσd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ c (s * a)) t :=
    hcd.self_of_nhds.comp t
      (mdifferentiableAt_iff_differentiableAt.mpr (hmul t).differentiableAt)
  rw [mdiffAlongAt_iff_of_mem (e := e) hσd hmem₀]
  have heq : (fun u ↦ (e ⟨c (u * a), velocity (I := I) (fun s ↦ c (s * a)) u⟩).2)
      =ᶠ[𝓝 t] fun u ↦ a • (e ⟨c (u * a), velocity (I := I) c (u * a)⟩).2 := by
    filter_upwards [htend.eventually hb, htend.eventually hcd] with u hu hdu
    have hlin : ∀ w : TangentSpace I (c (u * a)), (e ⟨c (u * a), w⟩).2
        = e.continuousLinearEquivAt ℝ (c (u * a)) hu w := fun _ ↦ rfl
    rw [velocity_comp_mul a u hdu, hlin, map_smul, ← hlin]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact (hvdiff.comp t (hmul t).differentiableAt).const_smul a


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

/-! ### Uniqueness on an interval

`eventuallyEq_of_isGeodesic` is local. `exp_x v = c(1)` needs two runs agreeing at `0` to agree
at `1`, which is the usual clopen argument: the agreement set is open by local uniqueness and
closed by continuity. Mathlib has no `T2Space` instance on the total space of a bundle, so
closedness is taken in two pieces — the base in `M`, the fibre coordinate in `E`, both
Hausdorff — and reassembled with the injectivity of a trivialisation on its source.
-/

section Interval

/-- **Two functions continuous at `x` and agreeing on `A` agree at any `x ∈ closure A`.**
The usual `IsClosed {f = g}` wants continuity everywhere; this needs it only at `x`. -/
theorem eq_of_mem_closure_of_continuousAt {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] {f g : α → β} {A : Set α} {x : α}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hA : ∀ u ∈ A, f u = g u)
    (hx : x ∈ closure A) : f x = g x := by
  have hclosed : IsClosed {q : β × β | q.1 = q.2} := isClosed_eq continuous_fst continuous_snd
  have himg : (fun u ↦ (f u, g u)) '' A ⊆ {q : β × β | q.1 = q.2} := by
    rintro _ ⟨u, hu, rfl⟩
    exact hA u hu
  have := (hf.prodMk hg).continuousWithinAt.mem_closure_image hx
  exact hclosed.closure_subset (closure_mono himg this)

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]

set_option maxSynthPendingDepth 3

-- BENCH: geodesic-unique-interval
/-- **Uniqueness of geodesics on a preconnected open set.** Two geodesic runs on `s` agreeing at
one time — position *and* velocity — agree on all of `s`.

Openness of the agreement set is `eventuallyEq_of_isGeodesic'` (agreeing near a point makes the
two curves the same function there, so their velocities agree too, `mfderiv` being local).
Closedness is `eq_of_mem_closure_of_continuousAt` applied twice: to the base in `M`, and to the
fibre coordinate `(e ⟨c u, c'(u)⟩).2` in `E` — the latter is continuous at the point because
`mdiffAlongAt_iff_of_mem` turns differentiability *along* the curve into differentiability of
exactly that coordinate. -/
theorem forall_totalSpace_eq_of_isGeodesicOn
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    {c₁ c₂ : ℝ → M} {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h₁d : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c₁ u)
    (h₁V : ∀ u ∈ s, MDiffAlongAt c₁ (velocity (I := I) c₁) u)
    (h₁g : IsGeodesicOn cov c₁ s)
    (h₂d : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c₂ u)
    (h₂V : ∀ u ∈ s, MDiffAlongAt c₂ (velocity (I := I) c₂) u)
    (h₂g : IsGeodesicOn cov c₂ s)
    (hinit : (⟨c₁ t₀, velocity (I := I) c₁ t₀⟩ : TangentBundle I M)
      = ⟨c₂ t₀, velocity (I := I) c₂ t₀⟩) :
    ∀ u ∈ s, (⟨c₁ u, velocity (I := I) c₁ u⟩ : TangentBundle I M)
      = ⟨c₂ u, velocity (I := I) c₂ u⟩ := by
  obtain ⟨A, hAdef⟩ : ∃ A : Set ℝ, A = s ∩ {u | (⟨c₁ u, velocity (I := I) c₁ u⟩
      : TangentBundle I M) = ⟨c₂ u, velocity (I := I) c₂ u⟩} := ⟨_, rfl⟩
  have hAsub : A ⊆ s := by rw [hAdef]; exact Set.inter_subset_left
  have hAmem : ∀ u ∈ A, (⟨c₁ u, velocity (I := I) c₁ u⟩ : TangentBundle I M)
      = ⟨c₂ u, velocity (I := I) c₂ u⟩ := by
    intro u hu; rw [hAdef] at hu; exact hu.2
  -- open, by local uniqueness
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxs : x ∈ s := hAsub hx
    have hmem : ∀ᶠ u in 𝓝 x, u ∈ s := hs.mem_nhds hxs
    have heq : c₁ =ᶠ[𝓝 x] c₂ :=
      eventuallyEq_of_isGeodesic' cov hk
        (by filter_upwards [hmem] with u hu using h₁d u hu)
        (by filter_upwards [hmem] with u hu using h₁V u hu)
        (by filter_upwards [hmem] with u hu using h₁g u hu)
        (by filter_upwards [hmem] with u hu using h₂d u hu)
        (by filter_upwards [hmem] with u hu using h₂V u hu)
        (by filter_upwards [hmem] with u hu using h₂g u hu)
        (hAmem x hx)
    obtain ⟨V, hVsub, hVopen, hVx⟩ := mem_nhds_iff.mp heq
    rw [hAdef]
    filter_upwards [hs.mem_nhds hxs, hVopen.mem_nhds hVx] with u hu hVu
    refine ⟨hu, ?_⟩
    have hloc : c₁ =ᶠ[𝓝 u] c₂ := Filter.eventually_of_mem (hVopen.mem_nhds hVu) hVsub
    have hb : c₁ u = c₂ u := hloc.eq_of_nhds
    have hv : velocity (I := I) c₁ u = velocity (I := I) c₂ u := by
      rw [velocity, velocity, hloc.mfderiv_eq]
      rfl
    exact congr(⟨$hb, $hv⟩)
  -- closed in `s`, by continuity of the base and of the fibre coordinate
  have hAclosed : closure A ∩ s ⊆ A := by
    rintro x ⟨hxcl, hxs⟩
    have hb : c₁ x = c₂ x :=
      eq_of_mem_closure_of_continuousAt (h₁d x hxs).continuousAt (h₂d x hxs).continuousAt
        (fun u hu ↦ congrArg TotalSpace.proj (hAmem u hu)) hxcl
    set e := trivializationAt E (fun z : M ↦ TangentSpace I z) (c₁ x) with he
    have hm₁ : c₁ x ∈ e.baseSet := mem_baseSet_trivializationAt E _ (c₁ x)
    have hm₂ : c₂ x ∈ e.baseSet := hb ▸ hm₁
    have hc₁ : ContinuousAt (fun u ↦ (e ⟨c₁ u, velocity (I := I) c₁ u⟩).2) x :=
      (((mdiffAlongAt_iff_of_mem (e := e) (h₁d x hxs) hm₁).mp (h₁V x hxs))).continuousAt
    have hc₂ : ContinuousAt (fun u ↦ (e ⟨c₂ u, velocity (I := I) c₂ u⟩).2) x :=
      (((mdiffAlongAt_iff_of_mem (e := e) (h₂d x hxs) hm₂).mp (h₂V x hxs))).continuousAt
    have hvv : (e ⟨c₁ x, velocity (I := I) c₁ x⟩).2 = (e ⟨c₂ x, velocity (I := I) c₂ x⟩).2 :=
      eq_of_mem_closure_of_continuousAt hc₁ hc₂
        (fun u hu ↦ congrArg (fun q ↦ (e q).2) (hAmem u hu)) hxcl
    have hs1 : (⟨c₁ x, velocity (I := I) c₁ x⟩ : TangentBundle I M) ∈ e.source :=
      e.mem_source.mpr hm₁
    have hs2 : (⟨c₂ x, velocity (I := I) c₂ x⟩ : TangentBundle I M) ∈ e.source :=
      e.mem_source.mpr hm₂
    rw [hAdef]
    refine ⟨hxs, ?_⟩
    refine e.toPartialHomeomorph.injOn hs1 hs2 ?_
    show (e ⟨c₁ x, velocity (I := I) c₁ x⟩ : M × E) = e ⟨c₂ x, velocity (I := I) c₂ x⟩
    refine Prod.ext ?_ hvv
    rw [e.coe_fst hs1, e.coe_fst hs2]
    exact hb
  have hAne : (s ∩ A).Nonempty := ⟨t₀, ht₀, by rw [hAdef]; exact ⟨ht₀, hinit⟩⟩
  intro u hu
  exact hAmem u (hsc.subset_of_closure_inter_subset hAopen hAne hAclosed hu)

/-- **Uniqueness of geodesics on a preconnected open set**, as an equality of curves. -/
theorem eqOn_of_isGeodesicOn
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    {c₁ c₂ : ℝ → M} {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h₁d : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c₁ u)
    (h₁V : ∀ u ∈ s, MDiffAlongAt c₁ (velocity (I := I) c₁) u)
    (h₁g : IsGeodesicOn cov c₁ s)
    (h₂d : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c₂ u)
    (h₂V : ∀ u ∈ s, MDiffAlongAt c₂ (velocity (I := I) c₂) u)
    (h₂g : IsGeodesicOn cov c₂ s)
    (hinit : (⟨c₁ t₀, velocity (I := I) c₁ t₀⟩ : TangentBundle I M)
      = ⟨c₂ t₀, velocity (I := I) c₂ t₀⟩) :
    Set.EqOn c₁ c₂ s := fun u hu ↦
  congrArg TotalSpace.proj (forall_totalSpace_eq_of_isGeodesicOn cov hk hs hsc ht₀
    h₁d h₁V h₁g h₂d h₂V h₂g hinit u hu)

end Interval

/-! ### The exponential map

With existence, uniqueness on an interval and reparametrisation in hand, `exp` is a definition
and three short lemmas. A *geodesic run* packages a geodesic together with everything the
uniqueness theorem asks of it; two runs with the same initial data agree wherever both are
defined, because the intersection of two order-connected sets is order-connected. `expMap` is
then defined by choice on the runs that reach time `1`, and is well defined by that agreement.
-/

section Exp

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]

set_option maxSynthPendingDepth 3

/-- **A geodesic run**: a geodesic on an open preconnected set of times containing `0`, with
the regularity the equation needs, and with prescribed initial position and velocity. -/
structure IsGeodesicRun (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (c : ℝ → M) (s : Set ℝ) (x : M) (v : TangentSpace I x) : Prop where
  isOpen : IsOpen s
  isPreconnected : IsPreconnected s
  mem_zero : (0 : ℝ) ∈ s
  mdiff : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c u
  mdiffAlong : ∀ u ∈ s, MDiffAlongAt c (velocity (I := I) c) u
  geodesic : IsGeodesicOn cov c s
  init : (⟨c 0, velocity (I := I) c 0⟩ : TangentBundle I M) = ⟨x, v⟩

-- BENCH: geodesic-run-exists
/-- **Every initial condition has a run.** -/
theorem exists_isGeodesicRun
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {k : ℕ∞} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    (x : M) (v : TangentSpace I x) :
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M, IsGeodesicRun cov c (Set.Ioo (-ε) ε) x v := by
  obtain ⟨ε, hε, c, hinit, hd, hV, hg⟩ := exists_isGeodesicOn' cov hk x v
  exact ⟨ε, hε, c, isOpen_Ioo, isPreconnected_Ioo, ⟨neg_lt_zero.mpr hε, hε⟩, hd, hV, hg, hinit⟩

-- BENCH: geodesic-run-unique
/-- **Two runs with the same initial data agree wherever both are defined.** The intersection of
two order-connected sets is order-connected, so `eqOn_of_isGeodesicOn` applies to it. -/
theorem IsGeodesicRun.eq_of_mem
    {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
    {c₁ c₂ : ℝ → M} {s₁ s₂ : Set ℝ} {x : M} {v : TangentSpace I x}
    (h₁ : IsGeodesicRun cov c₁ s₁ x v) {k : ℕ∞} (hk : 1 ≤ k)
    [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    (h₂ : IsGeodesicRun cov c₂ s₂ x v) {t : ℝ} (ht₁ : t ∈ s₁) (ht₂ : t ∈ s₂) : c₁ t = c₂ t := by
  have hord : (s₁ ∩ s₂).OrdConnected :=
    (isPreconnected_iff_ordConnected.mp h₁.isPreconnected).inter
      (isPreconnected_iff_ordConnected.mp h₂.isPreconnected)
  exact eqOn_of_isGeodesicOn cov hk (h₁.isOpen.inter h₂.isOpen)
    (isPreconnected_iff_ordConnected.mpr hord) ⟨h₁.mem_zero, h₂.mem_zero⟩
    (fun u hu ↦ h₁.mdiff u hu.1) (fun u hu ↦ h₁.mdiffAlong u hu.1)
    (fun u hu ↦ h₁.geodesic u hu.1)
    (fun u hu ↦ h₂.mdiff u hu.2) (fun u hu ↦ h₂.mdiffAlong u hu.2)
    (fun u hu ↦ h₂.geodesic u hu.2) (h₁.init.trans h₂.init.symm) ⟨ht₁, ht₂⟩

omit [I.Boundaryless] in
-- BENCH: geodesic-run-reparam
/-- **A run reparametrised.** `t ↦ c(ta)` is a run for the initial velocity `a·v`. -/
theorem IsGeodesicRun.comp_mul
    {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
    {c : ℝ → M} {s : Set ℝ} {x : M} {v : TangentSpace I x}
    (h : IsGeodesicRun cov c s x v) (a : ℝ) :
    IsGeodesicRun cov (fun u ↦ c (u * a)) {u : ℝ | u * a ∈ s} x (a • v) := by
  have hcont : Continuous fun u : ℝ ↦ u * a := continuous_id.mul continuous_const
  have hord : s.OrdConnected := isPreconnected_iff_ordConnected.mp h.isPreconnected
  have hzero : (0 : ℝ) * a ∈ s := by rw [zero_mul]; exact h.mem_zero
  have hnbhd : ∀ u ∈ {u : ℝ | u * a ∈ s}, ∀ᶠ r in 𝓝 (u * a), r ∈ s := fun u hu ↦
    h.isOpen.mem_nhds hu
  have hmulmem : ∀ u ∈ {u : ℝ | u * a ∈ s},
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r ↦ c (r * a)) u := by
    intro u hu
    have hd : HasDerivAt (fun r : ℝ ↦ r * a) a u := by simpa using (hasDerivAt_id u).mul_const a
    exact (h.mdiff (u * a) hu).comp u
      (mdifferentiableAt_iff_differentiableAt.mpr hd.differentiableAt)
  refine ⟨hcont.isOpen_preimage _ h.isOpen, isPreconnected_iff_ordConnected.mpr ?_, hzero,
    hmulmem, ?_, ?_, ?_⟩
  · refine ⟨fun p hp q hq r hr ↦ ?_⟩
    rcases le_or_gt 0 a with ha | ha
    · exact hord.out hp hq ⟨mul_le_mul_of_nonneg_right hr.1 ha,
        mul_le_mul_of_nonneg_right hr.2 ha⟩
    · exact hord.out hq hp ⟨mul_le_mul_of_nonpos_right hr.2 ha.le,
        mul_le_mul_of_nonpos_right hr.1 ha.le⟩
  · intro u hu
    exact mdiffAlongAt_velocity_comp_mul
      (by filter_upwards [hnbhd u hu] with r hr using h.mdiff r hr)
      (by filter_upwards [hnbhd u hu] with r hr using h.mdiffAlong r hr)
  · intro u hu
    exact covAlong_velocity_comp_mul_eq_zero' cov
      (by filter_upwards [hnbhd u hu] with r hr using h.mdiff r hr)
      (by filter_upwards [hnbhd u hu] with r hr using h.mdiffAlong r hr)
      (by filter_upwards [hnbhd u hu] with r hr using h.geodesic r hr)
  · have hvel : velocity (I := I) (fun r ↦ c (r * a)) 0 = a • velocity (I := I) c (0 * a) :=
      velocity_comp_mul a 0 (h.mdiff (0 * a) hzero)
    rw [zero_mul] at hvel
    have hF := congrArg
      (fun q : TangentBundle I M ↦ (⟨q.proj, a • q.2⟩ : TangentBundle I M)) h.init
    show (⟨c (0 * a), velocity (I := I) (fun u ↦ c (u * a)) 0⟩ : TangentBundle I M) = ⟨x, a • v⟩
    rw [zero_mul, hvel]
    exact hF

open scoped Classical in
/-- **The exponential map.** `expMap cov x v` is `c 1` for a geodesic run `c` with initial data
`(x, v)` that reaches time `1`, and `x` when no such run exists. Well defined by
`IsGeodesicRun.eq_of_mem` (see `expMap_eq`). -/
noncomputable def expMap (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (x : M) (v : TangentSpace I x) : M :=
  if h : ∃ cs : (ℝ → M) × Set ℝ, IsGeodesicRun cov cs.1 cs.2 x v ∧ (1 : ℝ) ∈ cs.2 then
    h.choose.1 1
  else x

-- BENCH: exp-eq
/-- **`expMap` is computed by any run reaching time `1`** — which is what makes it well
defined. -/
theorem expMap_eq (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {k : ℕ∞} (hk : 1 ≤ k) [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    {c : ℝ → M} {s : Set ℝ} {x : M} {v : TangentSpace I x}
    (h : IsGeodesicRun cov c s x v) (h1 : (1 : ℝ) ∈ s) : expMap cov x v = c 1 := by
  classical
  have hex : ∃ cs : (ℝ → M) × Set ℝ, IsGeodesicRun cov cs.1 cs.2 x v ∧ (1 : ℝ) ∈ cs.2 :=
    ⟨(c, s), h, h1⟩
  rw [expMap]
  split
  · next hP => exact hP.choose_spec.1.eq_of_mem hk h hP.choose_spec.2 h1
  · next hP => exact absurd hex hP

-- BENCH: exp-homogeneous
/-- **Homogeneity of `exp`**: `exp_x(a v) = γ_v(a)`, the geodesic with initial velocity `v`
evaluated at time `a`. This is the affine reparametrisation cashed in, and it is what makes
`exp` a map on a neighbourhood of the origin rather than a single value. -/
theorem expMap_smul_eq (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {k : ℕ∞} (hk : 1 ≤ k) [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    {c : ℝ → M} {s : Set ℝ} {x : M} {v : TangentSpace I x}
    (h : IsGeodesicRun cov c s x v) {a : ℝ} (ha : a ∈ s) :
    expMap cov x (a • v) = c a := by
  have h1 : (1 : ℝ) ∈ {u : ℝ | u * a ∈ s} := by simpa using ha
  have := expMap_eq cov hk (h.comp_mul a) h1
  simpa using this

-- BENCH: exp-zero
/-- **`exp_x 0 = x`.** -/
theorem expMap_zero (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {k : ℕ∞} (hk : 1 ≤ k) [ContMDiffCovariantDerivative cov (k : ℕ∞ω)]
    [ContMDiffVectorBundle ((k + 1 : ℕ∞) : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    (x : M) : expMap cov x (0 : TangentSpace I x) = x := by
  obtain ⟨ε, hε, c, hrun⟩ := exists_isGeodesicRun cov hk x (0 : TangentSpace I x)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hkey := expMap_smul_eq cov hk hrun h0
  rw [smul_zero] at hkey
  rw [hkey]
  exact congrArg TotalSpace.proj hrun.init

end Exp

end CovariantDerivative
