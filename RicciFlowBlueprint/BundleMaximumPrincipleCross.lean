/-
**Hamilton's tensor maximum principle on a non-trivial bundle.**

The composition. `FibrewiseMaximumPrinciple.lean` runs the first-touching-time argument on a
family of fibres, with the touching-point inequality as a hypothesis;
`BundleDistanceMax.lean` discharges that hypothesis for a section of a Riemannian bundle
obeying `∂ₜu = Δu + F(u)`, because at a spatial maximum of the distance to a parallel family
of closed convex sets the Laplacian points inwards.

**What this closes.** `TensorMaximumPrinciple.lean` and `ManifoldMaximumPrinciple.lean` run on
a *trivial* bundle --- the tested direction is literally the same vector at every point --- and
`TensorPreservation.lean` records that the non-trivial bundle, not the moving metric, was the
obstruction. `BundleMaximumPrinciple.lean` did the touching-point half for a direction in one
fibre, with the maximum of `⟪N,u⟫` assumed. What was missing was the cross-fibre comparison,
and this is it: the maximum is now assumed only of the *distance*, which is what the
first-touching-time argument actually produces.

**What it still does not do**: the fibre metric is fixed in `t`. Under the Ricci flow the
Hilbert--Schmidt metric on `End(TM)` moves with `g_t`, and that is Uhlenbeck's trick (or
Hamilton 1982 §9) --- a different bill, and the one the `log(1+t)` line pays.
-/
import RicciFlowBlueprint.BundleDistanceMax
import RicciFlowBlueprint.FibrewiseMaximumPrinciple

open Bundle Filter Set Metric RicciFlowBlueprint RicciFlowBlueprint.MaximumPrinciple
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [CompactSpace M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle 1 F V I] [∀ x : M, CompleteSpace (V x)]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]
  (covT : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative covT 1]

set_option maxSynthPendingDepth 3

-- BENCH: max-principle-bundle-cross
/-- **The tensor maximum principle on a bundle.**

`M` closed, `V` a Riemannian bundle with a metric connection admitting parallel transport,
`K x ⊆ V x` a parallel family of closed convex sets preserved by the reaction, and
`∂ₜu = Δu + F(u)` on `[0,T]`. If `u 0 x ∈ K x` for every `x`, then `u t x ∈ K x` for every
`t ∈ [0,T]`.

**The whole content of the composition is one line**: at a spatial maximum of the distance,
`⟪n, ∂ₜu⟫ = ⟪n, Δu⟫ + ⟪n, F(u)⟫ ≤ ⟪n, F(u)⟫`, because the Laplacian term is nonpositive.
Everything else is in the two files this one joins.

The orthonormal basis of each tangent space is `stdOrthonormalBasis`, so no frame data is
carried in the statement. -/
theorem mem_of_laplacianSection_of_isParallelSet (hmet : cov.IsMetricCompatible)
    (hpar : HasParallelTransport I F V cov) {K : Π x : M, Set (V x)}
    (hKcl : ∀ x, IsClosed (K x)) (hKcv : ∀ x, Convex ℝ (K x)) (hKne : ∀ x, (K x).Nonempty)
    (hK : IsParallelSet I F V cov K)
    {u ut : ℝ → Π x : M, V x} {Fr : Π x : M, V x → V x} {L : ℝ≥0} {T : ℝ}
    (hureg : ∀ t, CMDiff 2 (T% (u t)))
    (hdc : Continuous fun p : ℝ × M ↦ infDist (u p.1 p.2) (K p.2))
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hF : ∀ x, LipschitzWith L (Fr x))
    (hflow : ∀ t ∈ Icc 0 T, ∀ x,
      ut t x = cov.laplacianSection covT (hureg t) x + Fr x (u t x))
    (hKinv : ∀ x : M, ∀ p ∈ K x, ∀ n : V x,
      (∀ q ∈ K x, (⟪n, q - p⟫ : ℝ) ≤ 0) → (⟪n, Fr x p⟫ : ℝ) ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K x) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K x := by
  refine mem_of_infDist_max (V := V) hKcl hKcv hKne hdc hut hF ?_ hKinv h0
  intro t ht x₀ p _ hpmin hhalf hmaxf
  have hlap := inner_laplacianSection_nonpos_of_infDist_le cov covT hmet hpar hKne hK
    (hureg t) hmaxf hpmin hhalf (stdOrthonormalBasis ℝ (TangentSpace I x₀))
  rw [hflow t ht x₀, inner_add_right]
  linarith

end CovariantDerivative
