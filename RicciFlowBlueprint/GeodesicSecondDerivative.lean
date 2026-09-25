/-
**The second derivative along a geodesic of a bundle-valued pairing.**

For `N` parallel along a geodesic `γ` and `u` a `C²` section of a bundle `V` with a metric
connection,
`d/ds ⟪N, u∘γ⟫ = ⟪N, ∇_{γ'}u⟫` and `d²/ds² ⟪N, u∘γ⟫ = ⟪N, ∇²_{γ',γ'}u⟫`.

**The second one looks like it needs a global field agreeing with `velocity γ` along the
curve, and it does not.** Such a field does not exist in general (the curve need not be
embedded), and the way round is that **`∇u` is itself a global section of `Hom(TM,V)`** ---
which is exactly what `ContMDiffCovariantDerivative` asserts to be `C¹`. So `D/ds` of its
restriction to `γ` is `homCov` in the direction `γ'` by the `restrict` axiom, and
`HomBundleAlongCurve.lean`'s Leibniz rule `D/ds(Aσ) = (D/dt A)σ + A(D/ds σ)` at `A = (∇u)∘γ`,
`σ = γ'` **kills the correction because `D/ds γ' = 0` on a geodesic**. Finally `homCov`
applied to `∇u` *is* the Hessian: `covHom covT cov A X σ = ∇_X(Aσ) − A(∇_Xσ)` is
`hessianSection`'s definition with `A = ∇u`, so the bridge is `rfl`.

**Why this is wanted.** The cross-fibre half of the bundle maximum principle turns a spatial
maximum of `dist(u(t,x), K_x)` into one of `⟪N,u⟫`, and that needs `N` to be an *isometric*
image of the outward normal. Over a neighbourhood only radial transport (hence `exp`, hence
mathlib's dependence-on-initial-conditions gap) or a normal orthonormal frame (hence
differentiating Gram–Schmidt) supplies one. Along a *single curve* it is free: transport is an
isometry, so `‖N‖` is constant, and `IveyParallel.lean` carries the pinching set, so the
support function is constant too. And that suffices, because `Δ` at a point is a sum of
ordinary second derivatives along finitely many geodesics --- one curve at a time. This file
is the second derivative that argument differentiates.
-/
import RicciFlowBlueprint.BundleTransportIsometry
import RicciFlowBlueprint.HomBundleAlongCurve
import RicciFlowBlueprint.BundleHessian
import RicciFlowBlueprint.SecondDerivativeTest

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]
  (covT : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  {γ : ℝ → M} {N : Π s : ℝ, V (γ s)} {u : Π y : M, V y} {t : ℝ}

set_option maxSynthPendingDepth 3

omit [FiniteDimensional ℝ E] [T2Space M]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [FiniteDimensional ℝ F]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V] [ContMDiffVectorBundle 1 F V I] in
/-- **`∇u` is a global section of `Hom(TM,V)`.** This is what
`ContMDiffCovariantDerivative cov 1` says in so many words, extracted at a point; the whole
file rests on it, because it is what lets `D/ds` be taken of `∇u` as a *section* rather than
of its value on a field that does not exist. -/
theorem mdiffAt_cov_section (hu : CMDiff 2 (T% u)) (x : M) :
    MDiffAt (fun y : M ↦ (TotalSpace.mk' (E →L[ℝ] F)
      (E := fun y : M ↦ (TangentSpace I y →L[ℝ] V y)) y (cov u y))) x := by
  have hcovu : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun y : M ↦ (⟨y, cov u y⟩ :
        TotalSpace (E →L[ℝ] F) fun y ↦ (TangentSpace I y →L[ℝ] V y))) Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 1)).contMDiff
      (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hu.contMDiffOn)
  have h := hcovu x (Set.mem_univ x)
  rw [contMDiffWithinAt_univ] at h
  exact h.mdifferentiableAt one_ne_zero

omit [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **The first derivative**: against a parallel section, only the connection term survives,
and `D/ds` of a restricted global section is `∇` in the direction `γ'`. -/
theorem hasDerivAt_inner_parallel_section (hmet : cov.IsMetricCompatible)
    (hu : CMDiff 2 (T% u)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hN : MDiffAlongSectionAt I F V γ N t)
    (hNp : covAlongSection cov γ N t = 0) :
    HasDerivAt (fun s ↦ ⟪N s, u (γ s)⟫) ⟪N t, cov u (γ t) (velocity γ t)⟫ t := by
  have hum : ∀ y, MDiffAt (T% u) y := hu.mdifferentiable (by norm_num)
  have hres : MDiffAlongSectionAt I F V γ (fun s ↦ u (γ s)) t := (hum (γ t)).comp t hγ
  have h := hasDerivAt_inner_along_section cov hmet hγ hN hres
  rw [hNp, inner_zero_left, zero_add,
    (isCovDerivAlongSection_covAlongSection cov γ).restrict (hum (γ t)) hγ hγ] at h
  exact h

/-- **The second derivative**, in the form the Hom bundle produces it. The correction
`A(D/ds γ')` of the Leibniz rule is what the geodesic hypothesis kills. -/
theorem hasDerivAt_inner_parallel_section_second (hmet : cov.IsMetricCompatible)
    (hu : CMDiff 2 (T% u)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hγv : MDiffAlongAt γ (velocity (I := I) γ) t)
    (hgeo : covAlong covT γ (velocity (I := I) γ) t = 0)
    (hN : MDiffAlongSectionAt I F V γ N t)
    (hNp : covAlongSection cov γ N t = 0) :
    HasDerivAt (fun s ↦ ⟪N s, cov u (γ s) (velocity (I := I) γ s)⟫)
      ⟪N t, homCov covT cov (fun y ↦ cov u y) (γ t) (velocity (I := I) γ t)
        (velocity (I := I) γ t)⟫ t := by
  have hA : MDiffAlongSectionAt I (E →L[ℝ] F)
      (fun y : M ↦ TangentSpace I y →L[ℝ] V y) γ (fun s ↦ cov u (γ s)) t :=
    (mdiffAt_cov_section cov hu (γ t)).comp t hγ
  have hprod : MDiffAlongSectionAt I F V γ
      (fun s ↦ cov u (γ s) (velocity (I := I) γ s)) t :=
    MDifferentiableAt.clm_bundle_apply hA hγv
  have h := hasDerivAt_inner_along_section cov hmet hγ hN hprod
  rw [hNp, inner_zero_left, zero_add] at h
  have hleib := covAlongSection_hom_apply covT cov hγ hA hγv
  have hvel : covAlongSection covT γ (velocity (I := I) γ) t = 0 := by
    rw [covAlongSection_eq_covAlong covT hγ hγv]; exact hgeo
  rw [hvel, map_zero, add_zero,
    (isCovDerivAlongSection_covAlongSection (homCov covT cov) γ).restrict
      (mdiffAt_cov_section cov hu (γ t)) hγ hγ] at hleib
  rw [hleib] at h
  exact h

/-- **The second derivative as a Hessian.** `homCov` applied to `∇u` *is* `∇²u`: with
`A = ∇u` the definition `covHom covT cov A X σ = ∇_X(Aσ) − A(∇_Xσ)` is literally
`hessianSection`'s, so the bridge is `rfl` and all that is added is a field whose value at
the point is the velocity. -/
theorem hasDerivAt_inner_parallel_section_hessian (hmet : cov.IsMetricCompatible)
    (hu : CMDiff 2 (T% u)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hγv : MDiffAlongAt γ (velocity (I := I) γ) t)
    (hgeo : covAlong covT γ (velocity (I := I) γ) t = 0)
    (hN : MDiffAlongSectionAt I F V γ N t)
    (hNp : covAlongSection cov γ N t = 0)
    {X : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) (γ t))
    (hXγ : X (γ t) = velocity (I := I) γ t) :
    HasDerivAt (fun s ↦ ⟪N s, cov u (γ s) (velocity (I := I) γ s)⟫)
      ⟪N t, cov.hessianSection covT X X u (γ t)⟫ t := by
  have hbridge : homCov covT cov (fun y ↦ cov u y) (γ t) (velocity (I := I) γ t)
      (velocity (I := I) γ t) = cov.hessianSection covT X X u (γ t) := by
    rw [← hXγ]
    exact homCov_apply (isMDiffHomAt_of_section (mdiffAt_cov_section cov hu (γ t))) hX hX
  rw [← hbridge]
  exact hasDerivAt_inner_parallel_section_second cov covT hmet hu hγ hγv hgeo hN hNp

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section Laplacian

/-! ### From maxima along geodesics to the Laplacian

The payoff. `Δ` at a point is the trace of `∇²` over an orthonormal frame, and each diagonal
entry is the second derivative along a geodesic in that direction. So `n` geodesics, each
carrying the tested direction by parallel transport, deliver `⟪n, Δu⟫ ≤ 0` from `n` ordinary
one-dimensional second-derivative tests.

**Nothing varies the curve**, which is why none of this touches mathlib's missing
dependence-on-initial-conditions theory: each geodesic is fixed, and along a fixed curve
parallel transport is a linear equation. -/

/-- Bilinearity in the right slot against a finite sum, stated over an abstract inner product
space: `inner_sum` will not `rw` on a `Finset.sum` of fibre-typed terms. -/
theorem inner_sum_fibre {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {κ : Type*} [Fintype κ] (w : W) (z : κ → W) :
    (⟪w, ∑ i, z i⟫ : ℝ) = ∑ i, ⟪w, z i⟫ := by rw [inner_sum]

/-- **The touching-point step, one curve at a time.**

If through `x₀` there are geodesics in the directions of an orthonormal basis, each carrying
the tested direction `n` by parallel transport, and along each of them `s ↦ ⟪N,u∘γ⟫` has a
local maximum at `0`, then `⟪n, Δu(x₀)⟫ ≤ 0`.

**The direction never leaves its own fibre in the statement**: `n ∈ V x₀` and the conclusion is
about `n`, the parallel sections being an artefact of the proof --- the same shape as
`BundleMaximumPrinciple.lean`'s touching-point lemma, but reached along curves rather than
through a normal section, so that `‖N‖` and any transport-invariant constraint on `N` are
*constant* rather than merely critical at `x₀`. That is what the cross-fibre comparison needs
and what a normal section cannot give.

The initial condition is **one equation in the total space**, which packages `γ i 0 = x₀` and
`N i 0 = n` with no dependent-type cast; `congrArg` along a map out of the total space is then
what transports the conclusion to the fibre over `x₀`. -/
theorem inner_laplacianSection_nonpos_of_geodesic_max (hmet : cov.IsMetricCompatible)
    (hu : CMDiff 2 (T% u)) {x₀ : M} {n : V x₀}
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, MDiffAt (T% (fr i)) x₀) (b : OrthonormalBasis ι ℝ (TangentSpace I x₀))
    (hb : ∀ i, fr i x₀ = b i)
    {γ : ι → ℝ → M} {N : ∀ i, Π s : ℝ, V (γ i s)}
    (hγ : ∀ i, ∀ᶠ s in 𝓝 0, MDifferentiableAt 𝓘(ℝ, ℝ) I (γ i) s)
    (hN : ∀ i, ∀ᶠ s in 𝓝 0, MDiffAlongSectionAt I F V (γ i) (N i) s)
    (hNp : ∀ i, ∀ᶠ s in 𝓝 0, covAlongSection cov (γ i) (N i) s = 0)
    (hγv : ∀ i, MDiffAlongAt (γ i) (velocity (I := I) (γ i)) 0)
    (hgeo : ∀ i, covAlong covT (γ i) (velocity (I := I) (γ i)) 0 = 0)
    (hvel : ∀ i, fr i (γ i 0) = velocity (I := I) (γ i) 0)
    (hinit : ∀ i, (⟨γ i 0, N i 0⟩ : TotalSpace F V) = ⟨x₀, n⟩)
    (hmax : ∀ i, IsLocalMax (fun s ↦ (⟪N i s, u (γ i s)⟫ : ℝ)) 0) :
    (⟪n, cov.laplacianSection covT hu x₀⟫ : ℝ) ≤ 0 := by
  have hproj : ∀ i, γ i 0 = x₀ := fun i ↦ congrArg TotalSpace.proj (hinit i)
  have hd2 : ∀ i,
      (⟪N i 0, cov.hessianSection covT (fr i) (fr i) u (γ i 0)⟫ : ℝ) ≤ 0 := by
    intro i
    have h1 : ∀ᶠ s in 𝓝 0, HasDerivAt (fun r ↦ (⟪N i r, u (γ i r)⟫ : ℝ))
        (⟪N i s, cov u (γ i s) (velocity (I := I) (γ i) s)⟫) s := by
      filter_upwards [hγ i, hN i, hNp i] with s h1 h2 h3
      exact hasDerivAt_inner_parallel_section cov hmet hu h1 h2 h3
    have h2 := hasDerivAt_inner_parallel_section_hessian cov covT hmet hu
      (hγ i).self_of_nhds (hγv i) (hgeo i) (hN i).self_of_nhds (hNp i).self_of_nhds
      ((hproj i) ▸ hfr i) (hvel i)
    exact deriv2_nonpos_of_isLocalMax h1 h2 (hmax i)
  have hkey : ∀ i, (⟪n, cov.hessianSection covT (fr i) (fr i) u x₀⟫ : ℝ) ≤ 0 := fun i ↦ by
    have h := congrArg (fun p : TotalSpace F V ↦
      (⟪p.2, cov.hessianSection covT (fr i) (fr i) u p.proj⟫ : ℝ)) (hinit i)
    exact h ▸ hd2 i
  rw [cov.laplacianSection_eq_sum_frame covT hu hfr b hb,
    inner_sum_fibre (W := V x₀) n (fun i ↦ cov.hessianSection covT (fr i) (fr i) u x₀)]
  exact Finset.sum_nonpos fun i _ ↦ hkey i

end Laplacian

end CovariantDerivative
