/-
**Parallel transport of a section of a GENERAL bundle is an isometry.**

`TransportIsometry.lean` proves `d/dt ⟪V,W⟫ = ⟪D/dt V, W⟫ + ⟪V, D/dt W⟫` on the tangent
bundle. This is the same rule for a section of an arbitrary vector bundle carrying a metric
connection --- the port `BundleHessian.lean` and `BundleCovariantAlongCurve.lean` were, under
the same discipline: the *direction* stays in `TM` (`velocity γ t` is a tangent vector and
`cov σ y` is a map out of `T_yM`), while the sections differentiated and the fibres they take
values in are arbitrary.

**The argument does not change at all.** Expand both sections in local frames by
`exists_frame_expansion_section` --- not the same frame, and neither orthonormal nor parallel
--- so the pairing is a double sum `∑ᵢⱼ fᵢ gⱼ ⟪Aᵢ∘γ, Bⱼ∘γ⟫`; the product rule contributes the
`fᵢ'`, `gⱼ'` terms, which *are* the coordinate parts of `D/dt`, and metric compatibility
contributes each frame pairing's derivative, which *is* the connection part. Nothing is left
over, which is why the frames carry no hypotheses. The two algebraic identities are reused
from `TransportIsometry.lean` unchanged: they are stated over a bare inner product space
precisely so that they apply to any fibre.

**Why it is wanted.** The cross-fibre half of the bundle maximum principle turns a spatial
maximum of `dist(u(t,x), K_x)` into one of `⟪N, u⟫`, and that needs `N` to be an *isometric*
image of the outward normal --- over a neighbourhood only radial transport or a normal
orthonormal frame supplies one, both expensive. Along a *single curve* it is free: transport
is an isometry, so `‖N‖` is constant, and `IveyParallel.lean` carries the pinching set, so the
support function is constant too. Since `Δ` at a point is a sum of ordinary second derivatives
along finitely many geodesics --- one curve at a time --- that is all the argument needs, and
this rule is the first brick of it. The **fibre metric arrives as `[RiemannianBundle V]`**, not
as plain norm binders, which is what keeps the tangent-bundle case an instance of this one
(corrected belief 4).
-/
import RicciFlowBlueprint.BundleCovariantAlongCurve
import RicciFlowBlueprint.TransportIsometry
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V)
  {γ : ℝ → M} {σ τ : Π t : ℝ, V (γ t)} {t : ℝ}

set_option maxSynthPendingDepth 3

section Leibniz

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Metric compatibility at a bare tangent vector rather than along a vector field. Mathlib's
`IsMetricCompatible.mvfderiv_inner_eq` quantifies over a field `X` but uses only `X x`, so a
`FiberBundle.extend` of the vector discharges it --- `mvfderiv_inner_eq_apply` one bundle up,
and the direction is still a tangent vector, so the extension is the same one. -/
theorem mvfderiv_inner_eq_apply_section (hmet : cov.IsMetricCompatible)
    {ρ ρ' : Π y : M, V y} {x : M} (hρ : MDiffAt (T% ρ) x) (hρ' : MDiffAt (T% ρ') x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ⟪ρ y, ρ' y⟫) x v = ⟪cov ρ x v, ρ' x⟫ + ⟪ρ x, cov ρ' x v⟫ := by
  have h := hmet.mvfderiv_inner_eq (FiberBundle.extend E v) hρ hρ'
  simp only [FiberBundle.extend_apply_self] at h
  exact h

-- BENCH: bundle-transport-leibniz
/-- **The Leibniz rule for `D/dt` against the fibre metric, on a general bundle**:
`d/dt ⟪σ,τ⟫ = ⟪D/dt σ, τ⟫ + ⟪σ, D/dt τ⟫` for a metric connection.

Both sections are expanded in local frames by `exists_frame_expansion_section` --- not
necessarily the same frame, and neither orthonormal nor parallel. Every term matches on the
nose, so no hypothesis on the frames is needed. -/
theorem hasDerivAt_inner_along_section (hmet : cov.IsMetricCompatible)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hσ : MDiffAlongSectionAt I F V γ σ t)
    (hτ : MDiffAlongSectionAt I F V γ τ t) :
    HasDerivAt (fun u ↦ ⟪σ u, τ u⟫)
      (⟪covAlongSection cov γ σ t, τ t⟫ + ⟪σ t, covAlongSection cov γ τ t⟫) t := by
  classical
  obtain ⟨ι, _, A, f, hA, hf, hσexp⟩ := exists_frame_expansion_section hγ hσ
  obtain ⟨κ, _, B, g, hB, hg, hτexp⟩ := exists_frame_expansion_section hγ hτ
  have hAm : ∀ i, MDiffAt (T% (A i)) (γ t) := fun i ↦ (hA i).mdifferentiable one_ne_zero (γ t)
  have hBm : ∀ j, MDiffAt (T% (B j)) (γ t) := fun j ↦ (hB j).mdifferentiable one_ne_zero (γ t)
  have hpd : ∀ i j, HasDerivAt (fun u ↦ (⟪A i (γ u), B j (γ u)⟫ : ℝ))
      (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
        + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫) t := by
    intro i j
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ ⟪A i y, B j y⟫) (γ t) :=
      MDifferentiableAt.inner_bundle (hAm i) (hBm j)
    have hdiff : DifferentiableAt ℝ (fun u ↦ (⟪A i (γ u), B j (γ u)⟫ : ℝ)) t := by
      rw [← mdifferentiableAt_iff_differentiableAt]
      exact hmd.comp t hγ
    have hval : deriv (fun u ↦ (⟪A i (γ u), B j (γ u)⟫ : ℝ)) t
        = ⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
          + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫ := by
      rw [deriv_comp_curve hmd hγ, mvfderiv_inner_eq_apply_section cov hmet (hAm i) (hBm j)]
    exact hval ▸ hdiff.hasDerivAt
  have hexp : (fun u ↦ (⟪σ u, τ u⟫ : ℝ)) =ᶠ[𝓝 t]
      fun u ↦ ∑ i, ∑ j, f i u * g j u * ⟪A i (γ u), B j (γ u)⟫ := by
    filter_upwards [hσexp, hτexp] with u hu hu'
    rw [hu, hu']
    exact inner_sum_smul_sum (F := V (γ u)) _ _ _ _
  have hd : HasDerivAt (fun u ↦ ∑ i, ∑ j, f i u * g j u * ⟪A i (γ u), B j (γ u)⟫)
      (∑ i, ∑ j, (deriv (f i) t * g j t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * deriv (g j) t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
          + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫))) t := by
    refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ ?_
    have h := ((hf i).hasDerivAt.mul (hg j).hasDerivAt).mul (hpd i j)
    have e : (deriv (f i) t * g j t + f i t * deriv (g j) t) * ⟪A i (γ t), B j (γ t)⟫
          + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
            + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫)
        = deriv (f i) t * g j t * ⟪A i (γ t), B j (γ t)⟫
          + f i t * deriv (g j) t * ⟪A i (γ t), B j (γ t)⟫
          + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
            + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫) := by ring
    exact e ▸ h
  have hmain := hd.congr_of_eventuallyEq hexp
  have hσc : covAlongSection cov γ σ t
      = ∑ i, (f i t • cov (A i) (γ t) (velocity γ t) + deriv (f i) t • A i (γ t)) :=
    (isCovDerivAlongSection_covAlongSection cov γ).eq_sum_of_expansion hγ hσ hγ hA hf hσexp
  have hτc : covAlongSection cov γ τ t
      = ∑ j, (g j t • cov (B j) (γ t) (velocity γ t) + deriv (g j) t • B j (γ t)) :=
    (isCovDerivAlongSection_covAlongSection cov γ).eq_sum_of_expansion hγ hτ hγ hB hg hτexp
  have hσt : σ t = ∑ i, f i t • A i (γ t) := hσexp.self_of_nhds
  have hτt : τ t = ∑ j, g j t • B j (γ t) := hτexp.self_of_nhds
  have hvalue : ⟪covAlongSection cov γ σ t, τ t⟫ + ⟪σ t, covAlongSection cov γ τ t⟫
      = ∑ i, ∑ j, (deriv (f i) t * g j t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * deriv (g j) t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
          + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫)) := by
    rw [hσc, hτc, hσt, hτt]
    exact inner_expansion_add (F := V (γ t)) (fun i ↦ f i t)
      (fun i ↦ deriv (f i) t) (fun j ↦ g j t) (fun j ↦ deriv (g j) t)
      (fun i ↦ A i (γ t)) (fun i ↦ cov (A i) (γ t) (velocity γ t))
      (fun j ↦ B j (γ t)) (fun j ↦ cov (B j) (γ t) (velocity γ t))
  rw [hvalue]
  exact hmain

end Leibniz

section Constant

/-! ### Parallel sections have constant pairings

The Leibniz rule cashed in. Nothing here is new relative to the tangent-bundle case: along a
parallel pair the derivative is `⟪0,τ⟫ + ⟪σ,0⟫`, and the rest is
`constant_of_has_deriv_right_zero`. -/

variable {a c : ℝ} {s : Set ℝ}

/-- **A metric connection transports parallel sections with their pairing intact**, on a
closed interval. -/
theorem inner_eq_of_isParallelAlongSection (hmet : cov.IsMetricCompatible)
    (hγ : ∀ u ∈ Icc a c, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hσ : ∀ u ∈ Icc a c, MDiffAlongSectionAt I F V γ σ u)
    (hτ : ∀ u ∈ Icc a c, MDiffAlongSectionAt I F V γ τ u)
    (hPσ : IsParallelAlongSection I F V cov γ σ (Icc a c))
    (hPτ : IsParallelAlongSection I F V cov γ τ (Icc a c))
    {u : ℝ} (hu : u ∈ Icc a c) :
    ⟪σ u, τ u⟫ = ⟪σ a, τ a⟫ := by
  have key : ∀ r ∈ Icc a c, HasDerivAt (fun y ↦ (⟪σ y, τ y⟫ : ℝ)) 0 r := by
    intro r hr
    have h := hasDerivAt_inner_along_section cov hmet (hγ r hr) (hσ r hr) (hτ r hr)
    rwa [hPσ r hr, hPτ r hr, inner_zero_left, inner_zero_right, add_zero] at h
  exact constant_of_has_deriv_right_zero
    (fun r hr ↦ (key r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (key r (Ico_subset_Icc_self hr)).hasDerivWithinAt) u hu

/-- The same on a preconnected set and based at an arbitrary time: in `ℝ` preconnected is
order-connected, so the closed interval between the two times lies in `s`, and it is two
cases rather than a new argument. -/
theorem inner_eq_of_isParallelAlongSection_global (hmet : cov.IsMetricCompatible)
    (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hσ : ∀ u ∈ s, MDiffAlongSectionAt I F V γ σ u)
    (hτ : ∀ u ∈ s, MDiffAlongSectionAt I F V γ τ u)
    (hPσ : IsParallelAlongSection I F V cov γ σ s)
    (hPτ : IsParallelAlongSection I F V cov γ τ s)
    {t₀ u : ℝ} (ht₀ : t₀ ∈ s) (hu : u ∈ s) :
    ⟪σ u, τ u⟫ = ⟪σ t₀, τ t₀⟫ := by
  rw [isPreconnected_iff_ordConnected] at hconn
  rcases le_total t₀ u with h | h
  · have hsub : Icc t₀ u ⊆ s := hconn.out ht₀ hu
    exact inner_eq_of_isParallelAlongSection cov hmet (fun w hw ↦ hγ w (hsub hw))
      (fun w hw ↦ hσ w (hsub hw)) (fun w hw ↦ hτ w (hsub hw))
      (fun w hw ↦ hPσ w (hsub hw)) (fun w hw ↦ hPτ w (hsub hw)) (right_mem_Icc.mpr h)
  · have hsub : Icc u t₀ ⊆ s := hconn.out hu ht₀
    exact (inner_eq_of_isParallelAlongSection cov hmet (fun w hw ↦ hγ w (hsub hw))
      (fun w hw ↦ hσ w (hsub hw)) (fun w hw ↦ hτ w (hsub hw))
      (fun w hw ↦ hPσ w (hsub hw)) (fun w hw ↦ hPτ w (hsub hw)) (right_mem_Icc.mpr h)).symm

/-- **Parallel transport of a bundle section preserves lengths.** This is what makes `‖N‖ ≡ 1`
free in the cross-fibre maximum principle: the tested direction, carried along a curve, keeps
its norm with no normalisation step. -/
theorem norm_eq_of_isParallelAlongSection_global (hmet : cov.IsMetricCompatible)
    (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hσ : ∀ u ∈ s, MDiffAlongSectionAt I F V γ σ u)
    (hPσ : IsParallelAlongSection I F V cov γ σ s)
    {t₀ u : ℝ} (ht₀ : t₀ ∈ s) (hu : u ∈ s) :
    ‖σ u‖ = ‖σ t₀‖ := by
  have h := inner_eq_of_isParallelAlongSection_global cov hmet hconn hγ hσ hσ hPσ hPσ ht₀ hu
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (σ u), norm_nonneg (σ t₀)]

end Constant

section Tangent

/-! ### The tangent bundle is an instance

`TransportIsometry.lean`'s Leibniz rule derived from the general one --- the falsification
check, without which the general statement has no instantiations and asserts nothing. The
bridge is not `rfl`: `covAlongSection` and `covAlong` are identified by *uniqueness*, not by
definition, which is exactly the discipline `BundleCovariantAlongCurve.lean` set up. -/

variable
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  (covT : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  {W W' : Π t : ℝ, TangentSpace I (γ t)}

theorem hasDerivAt_inner_along_of_section
    (hmet : covT.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hW : MDiffAlongAt γ W t)
    (hW' : MDiffAlongAt γ W' t) :
    HasDerivAt (fun u ↦ ⟪W u, W' u⟫)
      (⟪covAlong covT γ W t, W' t⟫ + ⟪W t, covAlong covT γ W' t⟫) t := by
  have h := hasDerivAt_inner_along_section (V := fun x : M ↦ TangentSpace I x) covT hmet hγ
    hW hW'
  rwa [covAlongSection_eq_covAlong covT hγ hW, covAlongSection_eq_covAlong covT hγ hW'] at h

end Tangent

end CovariantDerivative
