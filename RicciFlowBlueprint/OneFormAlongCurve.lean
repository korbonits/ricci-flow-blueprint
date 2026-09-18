/-
**The Leibniz rule for a one-form along a curve**, and the second derivative of a function
along a geodesic.

`TransportIsometry.lean` proves `d/dt⟪V,W⟫ = ⟪D/dt V, W⟫ + ⟪V, D/dt W⟫` for a *metric*
connection. This is the same rule for the pairing of a **one-form field** with a section
along the curve, and it needs no metric at all:

  `d/dt [ω(V)] = (∇_{γ'}ω)(V) + ω(D/dt V)`.

At `ω = df` and `V = γ'` along a **geodesic** the second term dies and what is left is

  `(f ∘ γ)''(t) = ∇²f(γ'(t), γ'(t))`,

which is the identity that makes `Δ` at a point a sum of ordinary second derivatives along
`n` geodesics.

**Why this is wanted.** Hamilton's cross-fibre argument extends the tested direction `n` by
parallel transport over a *neighbourhood*, which is radial transport and so sits behind the
regularity of `exp` — a genuine mathlib gap. But the conclusion is only ever used through
`Δ`, and `Δ` at a point is a sum of second derivatives along `n` geodesics **taken one at a
time**. Transport along a single fixed curve is `ParallelTransport.lean`, which needs no
dependence-on-initial-conditions theory whatsoever. So the argument can be run curve by
curve, and the `exp` gap is never touched.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.TransportIsometry
import RicciFlowBlueprint.OneForm

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

section Algebra

/-! ### Two bilinearity identities, over a bare topological module

Stated here rather than inline for the documented reason: a `Finset.sum` over
`Π t, T_{γ t}\M` picks an `AddCommMonoid` only *defeq* to the fibre's own, so `rw [map_sum]`
fails on a goal that prints correctly. Stated over a variable `F` and applied with `exact`,
the same steps go through up to definitional equality.

**`F` carries no norm**, and that is load-bearing rather than tidiness: `T_x\M` has a norm
only through a `RiemannianBundle` instance, i.e. only once a metric is chosen, and this whole
file is metric-free. A `ContinuousLinearMap` into `ℝ` needs nothing beyond a topological
module structure. -/

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {ι : Type*} [Fintype ι]

theorem map_sum_smul (L : F →L[ℝ] ℝ) (c : ι → ℝ) (a : ι → F) :
    L (∑ i, c i • a i) = ∑ i, c i * L (a i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul]
  rfl

theorem map_sum_add_smul (L : F →L[ℝ] ℝ) (c d : ι → ℝ) (a b : ι → F) :
    L (∑ i, (c i • a i + d i • b i)) = ∑ i, (c i * L (a i) + d i * L (b i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_add, map_smul, map_smul]
  rfl

end Algebra

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  {γ : ℝ → M} {V : Π t : ℝ, TangentSpace I (γ t)} {w : M → E →L[ℝ] ℝ} {t : ℝ}

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] in
-- BENCH: oneform-leibniz-along
/-- **The Leibniz rule for a one-form along a curve**:
`d/dt [ω(V)] = (∇_{γ'}ω)(V) + ω(D/dt V)`.

`V` is expanded in a local frame by `exists_frame_expansion`, which needs no hypothesis on
the frame. The product rule contributes the `cᵢ'` terms, which are exactly the coordinate
part of `D/dt V`; the derivative of each `ω(Aᵢ)` along the curve is, by the *definition* of
`∇ω`, the connection part plus `(∇_{γ'}ω)(Aᵢ)`. Nothing is left over, which is why the frame
carries no hypotheses and no metric appears. -/
theorem hasDerivAt_oneForm_along (hw : IsMDiffOneFormAt (I := I) w (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t) :
    HasDerivAt (fun u ↦ w (γ u) (V u))
      (cov.covOneFormAt hw (velocity (I := I) γ t) (V t)
        + w (γ t) (covAlong cov γ V t)) t := by
  classical
  obtain ⟨ι, _, A, c, hA, hc, hVexp⟩ := exists_frame_expansion hγ hV
  have hAm : ∀ i, MDiffAt (T% (A i)) (γ t) := fun i ↦ (hA i).mdifferentiable one_ne_zero (γ t)
  set X : Π y : M, TangentSpace I y := FiberBundle.extend E (velocity (I := I) γ t) with hX
  have hXm : MDiffAt (T% X) (γ t) := FiberBundle.mdifferentiableAt_extend ..
  have hXv : X (γ t) = velocity (I := I) γ t := FiberBundle.extend_apply_self ..
  -- the derivative of each frame pairing, by the definition of `∇ω`
  have hpd : ∀ i, HasDerivAt (fun u ↦ w (γ u) (A i (γ u)))
      (cov.covOneForm w X (A i) (γ t) + w (γ t) (cov (A i) (γ t) (velocity (I := I) γ t))) t := by
    intro i
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ w y (A i y)) (γ t) := hw _ (hAm i)
    have hdiff : DifferentiableAt ℝ (fun u ↦ w (γ u) (A i (γ u))) t := by
      rw [← mdifferentiableAt_iff_differentiableAt]
      exact hmd.comp t hγ
    have hval : deriv (fun u ↦ w (γ u) (A i (γ u))) t
        = cov.covOneForm w X (A i) (γ t)
          + w (γ t) (cov (A i) (γ t) (velocity (I := I) γ t)) := by
      rw [deriv_comp_curve hmd hγ, covOneForm, hXv]
      ring
    exact hval ▸ hdiff.hasDerivAt
  -- the pairing, expanded in the frame
  have hexp : (fun u ↦ w (γ u) (V u)) =ᶠ[𝓝 t]
      fun u ↦ ∑ i, c i u * w (γ u) (A i (γ u)) := by
    filter_upwards [hVexp] with u hu
    rw [hu]
    exact map_sum_smul (F := TangentSpace I (γ u)) _ _ _
  have hd : HasDerivAt (fun u ↦ ∑ i, c i u * w (γ u) (A i (γ u)))
      (∑ i, (deriv (c i) t * w (γ t) (A i (γ t))
        + c i t * (cov.covOneForm w X (A i) (γ t)
          + w (γ t) (cov (A i) (γ t) (velocity (I := I) γ t))))) t :=
    HasDerivAt.fun_sum fun i _ ↦ (hc i).hasDerivAt.mul (hpd i)
  have hmain := hd.congr_of_eventuallyEq hexp
  -- and the value matches
  have hVc : covAlong cov γ V t
      = ∑ i, (c i t • cov (A i) (γ t) (velocity (I := I) γ t) + deriv (c i) t • A i (γ t)) :=
    (isCovDerivAlong_covAlong cov γ).eq_sum_of_expansion hγ hV hγ hA hc hVexp
  have hVt : V t = ∑ i, c i t • A i (γ t) := hVexp.eq_of_nhds
  have hfst : cov.covOneFormAt hw (velocity (I := I) γ t) (V t)
      = ∑ i, c i t * cov.covOneForm w X (A i) (γ t) := by
    rw [hVt]
    rw [map_sum_smul (F := TangentSpace I (γ t)) (cov.covOneFormAt hw (velocity (I := I) γ t))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hXv]
    exact congrArg (fun r ↦ c i t * r) (cov.covOneFormAt_apply hw hXm (hAm i))
  have hsnd : w (γ t) (covAlong cov γ V t)
      = ∑ i, (c i t * w (γ t) (cov (A i) (γ t) (velocity (I := I) γ t))
        + deriv (c i) t * w (γ t) (A i (γ t))) := by
    rw [hVc]
    exact map_sum_add_smul (F := TangentSpace I (γ t)) (w (γ t)) _ _ _ _
  have hvalue : cov.covOneFormAt hw (velocity (I := I) γ t) (V t)
        + w (γ t) (covAlong cov γ V t)
      = ∑ i, (deriv (c i) t * w (γ t) (A i (γ t))
        + c i t * (cov.covOneForm w X (A i) (γ t)
          + w (γ t) (cov (A i) (γ t) (velocity (I := I) γ t)))) := by
    rw [hfst, hsnd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hvalue]
  exact hmain

omit [CompleteSpace E] [T2Space M] [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- `∇ω` at a pair of tangent vectors is the Hessian when `ω = df`: `hessianFun` and
`covOneForm` are the same expression (`hessianFun_eq_covOneForm` is `rfl`), so this is just
`covOneFormAt_apply` read at `ω = df`. -/
theorem covOneFormAt_mvfderiv_eq_hessianFun {f : M → ℝ} {x : M}
    (hw : IsMDiffOneFormAt (I := I) (fun y ↦ mvfderiv I f y) x)
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.covOneFormAt hw (X x) (Y x) = cov.hessianFun f X Y x :=
  cov.covOneFormAt_apply hw hX hY

omit [CompleteSpace E] in
-- BENCH: geodesic-second-derivative
/-- **The second derivative of a function along a geodesic is its Hessian**:
`(f ∘ γ)''(t) = ∇²f(γ'(t), γ'(t))` when `D/dt γ' = 0`.

This is the Leibniz rule above at `ω = df` and `V = γ'`, where the correction term
`df(D/dt γ')` vanishes on the geodesic equation — and it is the identity that turns `Δ` at a
point into a sum of ordinary second derivatives along `n` geodesics, each of which is a
*single* curve. Nothing here varies the curve, so the regularity of `exp` never enters. -/
theorem hasDerivAt_mvfderiv_velocity_of_geodesic {f : M → ℝ}
    (hw : IsMDiffOneFormAt (I := I) (fun y ↦ mvfderiv I f y) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : MDiffAlongAt γ (velocity (I := I) γ) t)
    (hgeo : covAlong cov γ (velocity (I := I) γ) t = 0) :
    HasDerivAt (fun u ↦ mvfderiv I f (γ u) (velocity (I := I) γ u))
      (cov.covOneFormAt hw (velocity (I := I) γ t) (velocity (I := I) γ t)) t := by
  refine (cov.hasDerivAt_oneForm_along (w := fun y ↦ mvfderiv I f y) hw hγ hV).congr_deriv ?_
  rw [hgeo, add_eq_left]
  exact map_zero _

end CovariantDerivative
