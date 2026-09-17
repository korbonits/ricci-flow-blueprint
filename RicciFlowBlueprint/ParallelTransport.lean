/-
**Parallel transport along a curve.**

`CovariantAlongCurve.lean` defines `IsParallelAlong` but proves nothing about it beyond the
identification with every other `D/dt`. This file supplies what was missing: through every
vector in every fibre along a curve there **is** a parallel section, it is unique, and
transport is a linear isomorphism between fibres.

**Why this is reachable now, and geodesics were not.** In a trivialisation the equation
`D/dt V = 0` reads `q'(t) = −Γ(γ t)(γ'(t))(q(t))` (`GeodesicODE.lean`), and `Γ` is bilinear
by construction — so in the unknown `q` this is a **linear** ODE `q' = A(t)q`, with the
curve's own data sitting entirely inside the coefficient `A`. The geodesic equation, by
contrast, is `p'' = −Γ̃(p)(p')(p')`, quadratic in the unknown. That is the whole difference:
`LinearODE.lean`'s Dyson series solves `q' = A(t)q` on the *entire* interval with no
smallness hypothesis, where `exists_isGeodesicOn` had to accept whatever interval
Picard–Lindelöf gave it. **So parallel transport is not behind the ODE-regularity gap that
`exp` sits behind** — the working notes recorded it as though it were.

`transportCoeff` is `A`; `covAlong_eq_zero_iff_deriv` is the identification. Existence runs
the coefficient through `Set.projIcc` so that the Dyson series, which wants a globally
bounded continuous coefficient on all of `ℝ`, sees one — the extension is invisible on the
interval, being the identity there.
-/
import RicciFlowBlueprint.GeodesicODE
import RicciFlowBlueprint.LinearODE

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable {γ : ℝ → M} {t : ℝ}

section Coefficient

set_option maxSynthPendingDepth 3

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M]

/-- **The coefficient of the parallel-transport ODE** in the trivialisation `e`:
`A(t) = −Γ(γ t)(γ'(t))`, a continuous linear map on the model fibre. The unknown does not
appear in it — that is what makes the equation linear. -/
noncomputable def transportCoeff
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (γ : ℝ → M) (t : ℝ) : E →L[ℝ] E :=
  -christoffelB cov e b W (γ t) ((e ⟨γ t, velocity (I := I) γ t⟩).2)

-- BENCH: parallel-transport-ode
/-- **The parallel-transport equation, solved for `q'`.** With `q u = (e⟨γ u, V u⟩)₂`, the
condition `D/dt V = 0` at `t` is exactly `q'(t) = A(t)(q(t))`.

The *iff* is free because a trivialisation is a linear equivalence on each fibre, so
vanishing may be tested in coordinates — the same step `covAlong_velocity_eq_zero_iff` makes
for geodesics. -/
theorem covAlong_eq_zero_iff_deriv
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
    (hW : ∀ i, CMDiff 1 (T% (W i))) (hWU : ∀ i, ∀ y ∈ U, W i y = e.localFrame b i y)
    {V : Π t : ℝ, TangentSpace I (γ t)} (hγU : γ t ∈ U)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t) :
    covAlong cov γ V t = 0 ↔
      deriv (fun u ↦ (e ⟨γ u, V u⟩).2) t
        = transportCoeff cov e b W γ t ((e ⟨γ t, V t⟩).2) := by
  have hmem : γ t ∈ e.baseSet := hUe hγU
  have hzero : covAlong cov γ V t = 0 ↔ (e ⟨γ t, covAlong cov γ V t⟩).2 = 0 := by
    constructor
    · intro h; rw [h]; exact map_zero (e.continuousLinearEquivAt ℝ (γ t) hmem)
    · intro h; exact (e.continuousLinearEquivAt ℝ (γ t) hmem).map_eq_zero_iff.mp h
  rw [hzero, trivializationAt_covAlong_eq cov b hU hUe hW hWU hγU hγ hV,
    christoffel_eq_christoffelB cov b hmem (fun i ↦ hWU i (γ t) hγU), transportCoeff]
  constructor
  · intro h
    rw [_root_.neg_apply, eq_neg_iff_add_eq_zero]
    exact h
  · intro h
    rw [_root_.neg_apply, eq_neg_iff_add_eq_zero] at h
    exact h

omit [T2Space M] in
-- BENCH: parallel-transport-coeff-continuous
/-- **The coefficient is continuous**, which is all the Dyson series asks of it in the
`t` variable. Three pieces: the curve is continuous because it is differentiable; `Γ` is
continuous in the base point because the connection is `C¹`; and the velocity's fibre
coordinate is continuous because `mdiffAlongAt_iff_of_mem` turns differentiability *along*
the curve into differentiability of exactly that coordinate. -/
theorem continuousOn_transportCoeff
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1]
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} (hW : ∀ i, CMDiff 2 (T% (W i)))
    {U : Set M} (hUe : U ⊆ e.baseSet) {s : Set ℝ}
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    (hγU : ∀ u ∈ s, γ u ∈ U) :
    ContinuousOn (transportCoeff cov e b W γ) s := by
  intro u hu
  have hmem : γ u ∈ e.baseSet := hUe (hγU u hu)
  have hγc : ContinuousAt γ u := (hγ u hu).continuousAt
  have hchr : ContinuousAt (fun y : M ↦ christoffelB cov e b W y) (γ u) :=
    (contMDiffAt_christoffelB cov (k := 1) b hW hmem).continuousAt
  have hvel : ContinuousAt (fun r ↦ (e ⟨γ r, velocity (I := I) γ r⟩).2) u :=
    (((mdiffAlongAt_iff_of_mem (hγ u hu) hmem).mp (hγv u hu))).continuousAt
  exact (((hchr.comp hγc).clm_apply hvel).neg).continuousWithinAt

end Coefficient

section Existence

set_option maxSynthPendingDepth 3

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] [CompleteSpace E]

/-- **The coefficient, extended to all of `ℝ`.** The Dyson construction wants a continuous,
globally bounded coefficient on all of `ℝ`; a curve supplies one only where it is defined and
differentiable. Reparametrising by `Set.projIcc` extends by the boundary values, and is the
identity on `[a,c]`, so the solution there is the one wanted. -/
noncomputable def transportCoeffExt
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (γ : ℝ → M) {a c : ℝ} (hac : a ≤ c) (t : ℝ) : E →L[ℝ] E :=
  transportCoeff cov e b W γ ((Set.projIcc a c hac t : Icc a c) : ℝ)

omit [T2Space M] [CompleteSpace E] [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- On `[a,c]` the extension is invisible. -/
theorem transportCoeffExt_of_mem
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (W : ι → Π y : M, TangentSpace I y)
    (γ : ℝ → M) {a c : ℝ} (hac : a ≤ c) {t : ℝ} (ht : t ∈ Icc a c) :
    transportCoeffExt cov e b W γ hac t = transportCoeff cov e b W γ t := by
  show transportCoeff cov e b W γ ((Set.projIcc a c hac t : Icc a c) : ℝ) = _
  rw [Set.projIcc_of_mem hac ht]

section Data

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
  [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
  {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
  (hW : ∀ i, CMDiff 2 (T% (W i))) (hWU : ∀ i, ∀ y ∈ U, W i y = e.localFrame b i y)
  {s : Set ℝ} (hs : IsOpen s)
  (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
  (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
  (hγU : ∀ u ∈ s, γ u ∈ U)
  {a c : ℝ} (hac : a ≤ c) (hsub : Icc a c ⊆ s)

omit [T2Space M] [CompleteSpace E] in
include hUe hW hγ hγv hγU hac hsub in
/-- The extended coefficient is continuous and globally bounded — the two facts the Dyson
series consumes. The bound is compactness of `[a,c]`; there is nothing else to it. -/
theorem exists_bound_transportCoeffExt :
    ∃ C : ℝ, Continuous (transportCoeffExt cov e b W γ hac) ∧
      ∀ u, ‖transportCoeffExt cov e b W γ hac u‖ ≤ C := by
  have hAc : ContinuousOn (transportCoeff cov e b W γ) (Icc a c) :=
    (continuousOn_transportCoeff cov b hW hUe hγ hγv hγU).mono hsub
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn hAc
  exact ⟨C, hAc.domRestrict.comp continuous_projIcc,
    fun u ↦ hC _ (Set.projIcc a c hac u).2⟩

include hU hUe hW hWU hs hγ hγv hγU hac hsub in
-- BENCH: parallel-transport-exists
/-- **Parallel transport exists, on the whole interval.**

Through every `v` in the fibre at `γ t₀` there is a section parallel along `γ` on all of
`[a,c]` — **not on some smaller interval the fixed-point theorem happens to give**. That is
the dividend of linearity: `LinearODE.lean`'s Dyson series converges at every time because
its bound carries a factorial, so unlike `exists_isGeodesicOn` there is no shrinking step
and no smallness hypothesis anywhere. -/
theorem exists_isParallelAlong {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a c) (v : TangentSpace I (γ t₀)) :
    ∃ V : Π u : ℝ, TangentSpace I (γ u), V t₀ = v ∧
      (∀ u ∈ Icc a c, MDiffAlongAt γ V u) ∧ IsParallelAlong cov γ V (Icc a c) := by
  classical
  obtain ⟨C, hA'c, hC'⟩ := exists_bound_transportCoeffExt cov b hUe hW hγ hγv hγU hac hsub
  set A' := transportCoeffExt cov e b W γ hac with hA'
  set vc : E := (e ⟨γ t₀, v⟩).2 with hvc
  set q : ℝ → E := fun u ↦ dysonFrom A' t₀ u vc with hq
  have hqd : ∀ u, HasDerivAt q (A' u (q u)) u := fun u ↦
    hasDerivAt_dysonFrom_apply hA'c hC' t₀ vc u
  have hq0 : q t₀ = vc := by rw [hq]; simp
  -- Name the section by its *coordinate*, not by a formula: what the proof uses is only
  -- that `(e⟨γ u, V u⟩)₂ = q u`, and characterising `V` that way keeps the trivialisation's
  -- bundle argument determined by the ascription.
  obtain ⟨V, hcoord⟩ : ∃ V : Π u : ℝ, TangentSpace I (γ u),
      ∀ u ∈ s, (e ⟨γ u, V u⟩).2 = q u := by
    refine ⟨fun u ↦ if h : γ u ∈ e.baseSet then
      (e.continuousLinearEquivAt ℝ (γ u) h).symm (q u) else 0, ?_⟩
    intro u hu
    have hmem : γ u ∈ e.baseSet := hUe (hγU u hu)
    simp only [hmem, ↓reduceDIte]
    exact (e.continuousLinearEquivAt ℝ (γ u) hmem).apply_symm_apply (q u)
  have heq : ∀ u ∈ Icc a c, (fun r ↦ (e ⟨γ r, V r⟩).2) =ᶠ[𝓝 u] q := fun u hu ↦
    Filter.eventuallyEq_of_mem (hs.mem_nhds (hsub hu)) hcoord
  have hVdiff : ∀ u ∈ Icc a c, MDiffAlongAt γ V u := by
    intro u hu
    exact (mdiffAlongAt_iff_of_mem (hγ u (hsub hu)) (hUe (hγU u (hsub hu)))).mpr
      ((hqd u).differentiableAt.congr_of_eventuallyEq (heq u hu))
  refine ⟨V, ?_, hVdiff, ?_⟩
  · -- the initial value: the coordinates agree and the trivialisation is injective on fibres
    have hmem : γ t₀ ∈ e.baseSet := hUe (hγU t₀ (hsub ht₀))
    refine (e.continuousLinearEquivAt ℝ (γ t₀) hmem).injective ?_
    have h1 : e.continuousLinearEquivAt ℝ (γ t₀) hmem (V t₀) = (e ⟨γ t₀, V t₀⟩).2 := rfl
    have h2 : e.continuousLinearEquivAt ℝ (γ t₀) hmem v = (e ⟨γ t₀, v⟩).2 := rfl
    rw [h1, h2, hcoord t₀ (hsub ht₀), hq0]
  · intro u hu
    have hus : u ∈ s := hsub hu
    rw [covAlong_eq_zero_iff_deriv cov b hU hUe (fun i ↦ (hW i).of_le (by norm_num)) hWU
      (hγU u hus) (hγ u hus) (hVdiff u hu)]
    rw [(heq u hu).deriv_eq, (hqd u).deriv, hcoord u hus, hA',
      transportCoeffExt_of_mem cov e b W γ hac hu]

include hU hUe hW hWU hγ hγv hγU hac hsub in
-- BENCH: parallel-transport-coord
/-- **Every parallel section is the Dyson solution in coordinates.**

This is the one ODE-uniqueness argument in the file; the transport map and the uniqueness of
transport are both read off it. A linear field is Lipschitz with a constant uniform in `t`
once the coefficient is bounded, which compactness of `[a,c]` supplies, so mathlib's
`ODE_solution_unique_of_mem_Icc` applies with no work — and it concludes on the **closed**
interval, endpoints included. -/
theorem coord_eq_dysonFrom {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a c)
    {V : Π u : ℝ, TangentSpace I (γ u)} (hV : ∀ u ∈ Icc a c, MDiffAlongAt γ V u)
    (hPV : IsParallelAlong cov γ V (Icc a c)) {t : ℝ} (ht : t ∈ Icc a c) :
    (e ⟨γ t, V t⟩).2
      = dysonFrom (transportCoeffExt cov e b W γ hac) t₀ t ((e ⟨γ t₀, V t₀⟩).2) := by
  obtain ⟨C, hA'c, hC'⟩ := exists_bound_transportCoeffExt cov b hUe hW hγ hγv hγU hac hsub
  set A' := transportCoeffExt cov e b W γ hac with hA'
  have hCnn : ‖(0 : E →L[ℝ] E)‖ ≤ C := le_trans (by simp) (hC' 0)
  have hlip : ∀ u, LipschitzOnWith C.toNNReal (fun x ↦ A' u x) Set.univ := by
    intro u
    refine ((A' u).lipschitzWith.weaken ?_).lipschitzOnWith
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_trans (norm_nonneg _) hCnn)]
    exact hC' u
  have hqd : ∀ u, HasDerivAt (fun r ↦ dysonFrom A' t₀ r ((e ⟨γ t₀, V t₀⟩).2))
      (A' u (dysonFrom A' t₀ u ((e ⟨γ t₀, V t₀⟩).2))) u := fun u ↦
    hasDerivAt_dysonFrom_apply hA'c hC' t₀ _ u
  have hVd : ∀ u ∈ Icc a c, DifferentiableAt ℝ (fun r ↦ (e ⟨γ r, V r⟩).2) u := fun u hu ↦
    (mdiffAlongAt_iff_of_mem (hγ u (hsub hu)) (hUe (hγU u (hsub hu)))).mp (hV u hu)
  have hVsol : ∀ u ∈ Ioo a c, HasDerivAt (fun r ↦ (e ⟨γ r, V r⟩).2)
      (A' u ((e ⟨γ u, V u⟩).2)) u := by
    intro u hu
    have huc : u ∈ Icc a c := Ioo_subset_Icc_self hu
    have hus : u ∈ s := hsub huc
    have hd := (covAlong_eq_zero_iff_deriv cov b hU hUe
      (fun i ↦ (hW i).of_le (by norm_num)) hWU (hγU u hus) (hγ u hus) (hV u huc)).mp (hPV u huc)
    rw [← transportCoeffExt_of_mem cov e b W γ hac huc] at hd
    exact hd ▸ (hVd u huc).hasDerivAt
  refine ODE_solution_unique_of_mem_Icc (K := C.toNNReal) (s := fun _ ↦ Set.univ)
    (v := fun u x ↦ A' u x) (fun u _ ↦ hlip u) ht₀
    (fun u hu ↦ ((hVd u hu).continuousAt).continuousWithinAt) hVsol
    (fun _ _ ↦ Set.mem_univ _)
    (fun u _ ↦ ((hqd u).differentiableAt.continuousAt).continuousWithinAt)
    (fun u _ ↦ hqd u) (fun _ _ ↦ Set.mem_univ _) (by simp) ht

include hU hUe hW hWU hγ hγv hγU hac hsub in
-- BENCH: parallel-transport-equiv
/-- **Parallel transport is a linear isomorphism between the fibres.**

There is a continuous linear equivalence `P : T_{γ t₀}M ≃L T_{γ t}M` such that *every*
section parallel along `γ` satisfies `V t = P (V t₀)`. Together with
`exists_isParallelAlong` (something to transport) and `eqOn_of_isParallelAlong` (nothing
else to transport it to), this is parallel transport.

**Invertibility is not extra work**: `P` is the trivialisation at `γ t₀`, then the Dyson
propagator, then the inverse trivialisation at `γ t`, and the middle factor is invertible by
`bijective_dysonSum` — which is itself two uniqueness arguments, forwards and backwards. The
fibres need no norm for `≃L[ℝ]` to elaborate, only their topology and module structure, so
no metric appears anywhere in this statement. -/
theorem exists_parallelTransportEquiv {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a c) {t : ℝ}
    (ht : t ∈ Icc a c) :
    ∃ P : TangentSpace I (γ t₀) ≃L[ℝ] TangentSpace I (γ t),
      ∀ V : Π u : ℝ, TangentSpace I (γ u), (∀ u ∈ Icc a c, MDiffAlongAt γ V u) →
        IsParallelAlong cov γ V (Icc a c) → V t = P (V t₀) := by
  obtain ⟨C, hA'c, hC'⟩ := exists_bound_transportCoeffExt cov b hUe hW hγ hγv hγU hac hsub
  set A' := transportCoeffExt cov e b W γ hac with hA'
  have hmem₀ : γ t₀ ∈ e.baseSet := hUe (hγU t₀ (hsub (Ioo_subset_Icc_self ht₀)))
  have hmem : γ t ∈ e.baseSet := hUe (hγU t (hsub ht))
  have hA'' : Continuous fun r ↦ A' (r + t₀) := hA'c.comp (continuous_id.add continuous_const)
  refine ⟨((e.continuousLinearEquivAt ℝ (γ t₀) hmem₀).trans
      (dysonEquiv hA'' (fun r ↦ hC' _) (t - t₀))).trans
      (e.continuousLinearEquivAt ℝ (γ t) hmem).symm, ?_⟩
  intro V hV hPV
  refine (e.continuousLinearEquivAt ℝ (γ t) hmem).injective ?_
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    dysonEquiv_apply]
  exact coord_eq_dysonFrom cov b hU hUe hW hWU hγ hγv hγU hac hsub ht₀ hV hPV ht

include hU hUe hW hWU hγ hγv hγU hac hsub in
-- BENCH: parallel-transport-unique
/-- **Parallel transport is unique**, on the closed interval: two sections parallel along `γ`
that agree at one time agree throughout. So "the" parallel translate of a vector is well
defined, and `exists_isParallelAlong` is not merely producing one of many. -/
theorem eqOn_of_isParallelAlong {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a c)
    {V V' : Π u : ℝ, TangentSpace I (γ u)}
    (hV : ∀ u ∈ Icc a c, MDiffAlongAt γ V u) (hV' : ∀ u ∈ Icc a c, MDiffAlongAt γ V' u)
    (hPV : IsParallelAlong cov γ V (Icc a c)) (hPV' : IsParallelAlong cov γ V' (Icc a c))
    (hinit : V t₀ = V' t₀) :
    ∀ u ∈ Icc a c, V u = V' u := by
  intro u hu
  obtain ⟨P, hP⟩ := exists_parallelTransportEquiv cov b hU hUe hW hWU hγ hγv hγU hac hsub
    ht₀ hu
  rw [hP V hV hPV, hP V' hV' hPV', hinit]

end Data

end Existence

end CovariantDerivative
