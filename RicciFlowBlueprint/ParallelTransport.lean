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

-- BENCH: parallel-transport-exists
/-- **Parallel transport exists, on the whole interval.**

Through every `v` in the fibre at `γ t₀` there is a section parallel along `γ` on all of
`[a,c]` — **not on some smaller interval the fixed-point theorem happens to give**. That is
the dividend of linearity: `LinearODE.lean`'s Dyson series converges at every time because
its bound carries a factorial, so unlike `exists_isGeodesicOn` there is no shrinking step
and no smallness hypothesis anywhere.

The coefficient is pushed through `Set.projIcc` before the series sees it. The Dyson
construction wants a continuous, globally bounded coefficient on all of `ℝ`; the curve
supplies one only on `[a,c]`. Reparametrising by `projIcc` extends it by its boundary values,
which is continuous, bounded by compactness — and **invisible on `[a,c]`**, where `projIcc`
is the identity, so the solution there is the one wanted. -/
theorem exists_isParallelAlong
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1]
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
    (hW : ∀ i, CMDiff 2 (T% (W i))) (hWU : ∀ i, ∀ y ∈ U, W i y = e.localFrame b i y)
    {s : Set ℝ} (hs : IsOpen s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    (hγU : ∀ u ∈ s, γ u ∈ U)
    {a c : ℝ} (hac : a ≤ c) (hsub : Icc a c ⊆ s) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a c)
    (v : TangentSpace I (γ t₀)) :
    ∃ V : Π u : ℝ, TangentSpace I (γ u), V t₀ = v ∧
      (∀ u ∈ Icc a c, MDiffAlongAt γ V u) ∧ IsParallelAlong cov γ V (Icc a c) := by
  classical
  set A := transportCoeff cov e b W γ with hA
  have hAc : ContinuousOn A (Icc a c) :=
    (continuousOn_transportCoeff cov b hW hUe hγ hγv hγU).mono hsub
  -- extend the coefficient to all of `ℝ` by `projIcc`
  set A' : ℝ → (E →L[ℝ] E) := fun u ↦ A ((Set.projIcc a c hac u : Icc a c) : ℝ) with hA'
  have hA'c : Continuous A' := hAc.domRestrict.comp continuous_projIcc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn hAc
  have hC' : ∀ u, ‖A' u‖ ≤ C := fun u ↦ hC _ (Set.projIcc a c hac u).2
  have hA'eq : ∀ u ∈ Icc a c, A' u = A u := by
    intro u hu
    show A ((Set.projIcc a c hac u : Icc a c) : ℝ) = A u
    rw [Set.projIcc_of_mem hac hu]
  -- solve the linear ODE
  set vc : E := (e ⟨γ t₀, v⟩).2 with hvc
  set q : ℝ → E := fun u ↦ dysonFrom A' t₀ u vc with hq
  have hqd : ∀ u, HasDerivAt q (A' u (q u)) u := fun u ↦
    hasDerivAt_dysonFrom_apply hA'c hC' t₀ vc u
  have hq0 : q t₀ = vc := by rw [hq]; simp
  -- transport the solution back to a section along `γ`
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
    rw [(heq u hu).deriv_eq, (hqd u).deriv, hcoord u hus, hA'eq u hu]

omit [CompleteSpace E] in
-- BENCH: parallel-transport-unique
/-- **Parallel transport is unique.** Two sections parallel along `γ` that agree at one time
agree throughout — so "the" parallel translate of a vector is well defined, and
`exists_isParallelAlong` is not merely producing one of many.

The argument is ODE uniqueness in the trivialisation. A linear field is Lipschitz with a
constant uniform in `t` once the coefficient is bounded, which compactness of `[a,c]`
supplies, so mathlib's `ODE_solution_unique_of_mem_Ioo` applies with no work. Note the
differentiability hypotheses are the ones the equation already needs: `MDiffAlongAt` *is*
differentiability of the fibre coordinate. -/
theorem eqOn_of_isParallelAlong
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1]
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
    (hW : ∀ i, CMDiff 2 (T% (W i))) (hWU : ∀ i, ∀ y ∈ U, W i y = e.localFrame b i y)
    {s : Set ℝ}
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    (hγU : ∀ u ∈ s, γ u ∈ U)
    {a c : ℝ} (hsub : Icc a c ⊆ s) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a c)
    {V V' : Π u : ℝ, TangentSpace I (γ u)}
    (hV : ∀ u ∈ Icc a c, MDiffAlongAt γ V u) (hV' : ∀ u ∈ Icc a c, MDiffAlongAt γ V' u)
    (hPV : IsParallelAlong cov γ V (Icc a c)) (hPV' : IsParallelAlong cov γ V' (Icc a c))
    (hinit : V t₀ = V' t₀) :
    ∀ u ∈ Ioo a c, V u = V' u := by
  set A := transportCoeff cov e b W γ with hA
  have hAc : ContinuousOn A (Icc a c) :=
    (continuousOn_transportCoeff cov b hW hUe hγ hγv hγU).mono hsub
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn hAc
  have hCnn : ∀ u ∈ Icc a c, ‖A u‖₊ ≤ C.toNNReal := by
    intro u hu
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_trans (norm_nonneg _) (hC u hu))]
    exact hC u hu
  -- the coordinates of the two sections solve the same linear equation on `Ioo a c`
  have hsolve : ∀ (Z : Π u : ℝ, TangentSpace I (γ u)),
      (∀ u ∈ Icc a c, MDiffAlongAt γ Z u) → IsParallelAlong cov γ Z (Icc a c) →
      ∀ u ∈ Ioo a c, HasDerivAt (fun r ↦ (e ⟨γ r, Z r⟩).2)
        (A u ((e ⟨γ u, Z u⟩).2)) u := by
    intro Z hZ hPZ u hu
    have huc : u ∈ Icc a c := Ioo_subset_Icc_self hu
    have hus : u ∈ s := hsub huc
    have hd : DifferentiableAt ℝ (fun r ↦ (e ⟨γ r, Z r⟩).2) u :=
      (mdiffAlongAt_iff_of_mem (hγ u hus) (hUe (hγU u hus))).mp (hZ u huc)
    have := (covAlong_eq_zero_iff_deriv cov b hU hUe (fun i ↦ (hW i).of_le (by norm_num)) hWU
      (hγU u hus) (hγ u hus) (hZ u huc)).mp (hPZ u huc)
    exact this ▸ hd.hasDerivAt
  have hkey : EqOn (fun r ↦ (e ⟨γ r, V r⟩).2) (fun r ↦ (e ⟨γ r, V' r⟩).2) (Ioo a c) := by
    refine ODE_solution_unique_of_mem_Ioo (K := C.toNNReal) (s := fun _ ↦ Set.univ)
      (v := fun u x ↦ A u x) ?_ ht₀ ?_ ?_ ?_
    · exact fun u hu ↦ ((A u).lipschitzWith.weaken
        (hCnn u (Ioo_subset_Icc_self hu))).lipschitzOnWith
    · exact fun u hu ↦ ⟨hsolve V hV hPV u hu, Set.mem_univ _⟩
    · exact fun u hu ↦ ⟨hsolve V' hV' hPV' u hu, Set.mem_univ _⟩
    · show (e ⟨γ t₀, V t₀⟩).2 = (e ⟨γ t₀, V' t₀⟩).2
      rw [hinit]
  intro u hu
  have hmem : γ u ∈ e.baseSet := hUe (hγU u (hsub (Ioo_subset_Icc_self hu)))
  refine (e.continuousLinearEquivAt ℝ (γ u) hmem).injective ?_
  have h1 : e.continuousLinearEquivAt ℝ (γ u) hmem (V u) = (e ⟨γ u, V u⟩).2 := rfl
  have h2 : e.continuousLinearEquivAt ℝ (γ u) hmem (V' u) = (e ⟨γ u, V' u⟩).2 := rfl
  rw [h1, h2]
  exact hkey hu

end Existence

end CovariantDerivative
