/-
**A spatial maximum of the distance to a parallel family of convex sets is a maximum of the
pairing with the outward normal, along every geodesic.**

This is the step that makes the cross-fibre maximum principle a statement the touching-point
machinery can consume. Hamilton's device is to carry the outward normal `n = w(x₀) − p` away
from `x₀` by parallel transport; the point of doing it *along one curve at a time* is that
transport along a fixed curve is a linear equation (`ParallelTransport.lean`), is an
**isometry** (`TransportIsometry.lean`, so `‖N‖` is constant), and **carries the family `K`**
(the hypothesis `IsParallelSet`, which `IveyParallel.lean` supplies for Hamilton's pinching
set). None of that is available for an extension over a *neighbourhood* without radial
transport or a normal orthonormal frame.

**No support function is needed as a definition.** `TensorMaximumPrinciple.lean`'s
`inner_sub_le_norm_mul_infDist` --- the supporting half-space bounds the distance from below
--- is exactly the inequality wanted, and the half-space property in the fibre over `γ r` is
the one at `x₀` transported term by term. What survives is

`⟪N r, w(γ r)⟫ ≤ ‖n‖ · dist(w(γ r), K_{γ r}) + ⟪n, p⟫ ≤ ‖n‖² + ⟪n, p⟫ = ⟪n, w(x₀)⟫`,

with equality at `r = 0`: the two constants are constant precisely because transport is an
isometry and carries `K`.
-/
import RicciFlowBlueprint.GeodesicSecondDerivative
import RicciFlowBlueprint.TensorMaximumPrinciple

open Bundle Filter Set Metric RicciFlowBlueprint RicciFlowBlueprint.MaximumPrinciple
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
  [ContMDiffVectorBundle 1 F V I] [∀ x : M, CompleteSpace (V x)]
  (cov : CovariantDerivative I F V)

set_option maxSynthPendingDepth 3

variable (I F V) in
/-- **A parallel family of subsets**: membership is preserved by parallel transport along any
curve. For Hamilton's pinching set on `End(TM)` this is `IveyParallel.lean` --- every fibre
isometry preserves the set, and transport for a metric connection is one. -/
def IsParallelSet (K : Π x : M, Set (V x)) : Prop :=
  ∀ (γ : ℝ → M) (s : Set ℝ), IsOpen s → IsPreconnected s →
    (∀ r ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r) →
    (∀ r ∈ s, MDiffAlongAt γ (velocity (I := I) γ) r) →
    ∀ N : Π r : ℝ, V (γ r), (∀ r ∈ s, MDiffAlongSectionAt I F V γ N r) →
      IsParallelAlongSection I F V cov γ N s →
      ∀ t₀ ∈ s, ∀ t ∈ s, (N t ∈ K (γ t) ↔ N t₀ ∈ K (γ t₀))

omit [∀ (x : M), CompleteSpace (V x)] in
/-- **The half-space property travels with the normal.**

At `x₀` the nearest point `p` puts `K x₀` in the half-space `⟪n, · − p⟫ ≤ 0`. Transporting
`n` and `p` along `γ`, the same holds in the fibre over `γ r`: every `q` there is the value of
a parallel section whose value at `0` lies in `K x₀`, and the pairing of two parallel sections
is constant. -/
theorem inner_sub_nonpos_of_isParallelSet (hmet : cov.IsMetricCompatible)
    (hpar : HasParallelTransport I F V cov) {K : Π x : M, Set (V x)}
    (hK : IsParallelSet I F V cov K) {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ r ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r)
    (hγv : ∀ r ∈ s, MDiffAlongAt γ (velocity (I := I) γ) r)
    {N Q : Π r : ℝ, V (γ r)}
    (hNd : ∀ r ∈ s, MDiffAlongSectionAt I F V γ N r)
    (hNp : IsParallelAlongSection I F V cov γ N s)
    (hQd : ∀ r ∈ s, MDiffAlongSectionAt I F V γ Q r)
    (hQp : IsParallelAlongSection I F V cov γ Q s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hhalf : ∀ q ∈ K (γ t₀), (⟪N t₀, q - Q t₀⟫ : ℝ) ≤ 0)
    {r : ℝ} (hr : r ∈ s) :
    ∀ q ∈ K (γ r), (⟪N r, q - Q r⟫ : ℝ) ≤ 0 := by
  intro q hq
  obtain ⟨Q', hQ'0, hQ'd, hQ'p⟩ := hpar γ s hs hconn hγ hγv r hr (γ r) q rfl
  have hQ'r : Q' r = q := by
    simp only [TotalSpace.mk.injEq, heq_eq_eq, true_and] at hQ'0
    exact hQ'0
  have hmem : Q' t₀ ∈ K (γ t₀) := by
    have hiff := hK γ s hs hconn hγ hγv Q' hQ'd hQ'p t₀ ht₀ r hr
    rw [hQ'r] at hiff
    exact hiff.mp hq
  have h1 : (⟪N r, Q' r⟫ : ℝ) = ⟪N t₀, Q' t₀⟫ :=
    inner_eq_of_isParallelAlongSection_global cov hmet hconn hγ hNd hQ'd hNp hQ'p ht₀ hr
  have h2 : (⟪N r, Q r⟫ : ℝ) = ⟪N t₀, Q t₀⟫ :=
    inner_eq_of_isParallelAlongSection_global cov hmet hconn hγ hNd hQd hNp hQp ht₀ hr
  have h3 := hhalf (Q' t₀) hmem
  rw [hQ'r] at h1
  rw [inner_sub_right] at h3 ⊢
  linarith

omit [∀ (x : M), CompleteSpace (V x)] in
/-- **A spatial maximum of the distance is a maximum of the pairing, along every geodesic.**

`n = w(x₀) − p` is the outward normal at the nearest point; `N` carries it along `γ`. The
bound is

`⟪N r, w(γ r)⟫ = ⟪N r, w(γ r) − Q r⟫ + ⟪N r, Q r⟫ ≤ ‖n‖·dist(w(γ r), K_{γ r}) + ⟪n, p⟫`,

whose two constants are constant because transport is an **isometry** and **carries `K`**;
the distance is then at most its value at `x₀`, which is `‖n‖`, and the right-hand side is
`‖n‖² + ⟪n,p⟫ = ⟪n, w(x₀)⟫`, the value at `r = 0`.

The curve is *not* required to be a geodesic here --- only differentiable. The geodesic
hypothesis enters one level up, where the second derivative of this function is identified
with `⟪n, ∇²w⟫`. -/
theorem isLocalMax_inner_of_infDist_le (hmet : cov.IsMetricCompatible)
    (hpar : HasParallelTransport I F V cov) {K : Π x : M, Set (V x)}
    (hKne : ∀ x, (K x).Nonempty) (hK : IsParallelSet I F V cov K)
    {w : Π x : M, V x} {x₀ : M}
    (hmaxf : ∀ x, infDist (w x) (K x) ≤ infDist (w x₀) (K x₀))
    {p : V x₀} (hpmin : ‖w x₀ - p‖ = infDist (w x₀) (K x₀))
    (hhalf : ∀ q ∈ K x₀, (⟪w x₀ - p, q - p⟫ : ℝ) ≤ 0)
    {γ : ℝ → M} {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s) (h0 : (0 : ℝ) ∈ s)
    (hγ : ∀ r ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r)
    (hγv : ∀ r ∈ s, MDiffAlongAt γ (velocity (I := I) γ) r)
    (hγ0 : γ 0 = x₀) {N : Π r : ℝ, V (γ r)}
    (hNd : ∀ r ∈ s, MDiffAlongSectionAt I F V γ N r)
    (hNp : IsParallelAlongSection I F V cov γ N s)
    (hN0 : (⟨γ 0, N 0⟩ : TotalSpace F V) = ⟨x₀, w x₀ - p⟩) :
    IsLocalMax (fun r ↦ (⟪N r, w (γ r)⟫ : ℝ)) 0 := by
  subst hγ0
  have hN0' : N 0 = w (γ 0) - p := by
    simp only [TotalSpace.mk.injEq, heq_eq_eq, true_and] at hN0
    exact hN0
  obtain ⟨Q, hQ0, hQd, hQp⟩ := hpar γ s hs hconn hγ hγv 0 h0 (γ 0) p rfl
  have hQ0' : Q 0 = p := by
    simp only [TotalSpace.mk.injEq, heq_eq_eq, true_and] at hQ0
    exact hQ0
  have hhalf0 : ∀ q ∈ K (γ 0), (⟪N 0, q - Q 0⟫ : ℝ) ≤ 0 := by
    rw [hN0', hQ0']; exact hhalf
  have hval0 : (⟪N 0, w (γ 0)⟫ : ℝ) = ‖N 0‖ * ‖N 0‖ + ⟪N 0, Q 0⟫ := by
    rw [hQ0', ← real_inner_self_eq_norm_mul_norm, ← inner_add_right]
    congr 1
    rw [hN0']
    abel
  refine Filter.eventually_of_mem (hs.mem_nhds h0) fun r hr ↦ ?_
  have hhalfr : ∀ q ∈ K (γ r), (⟪N r, q - Q r⟫ : ℝ) ≤ 0 :=
    inner_sub_nonpos_of_isParallelSet cov hmet hpar hK hs hconn hγ hγv hNd hNp hQd hQp
      h0 hhalf0 hr
  have hbound := inner_sub_le_norm_mul_infDist (V := V (γ r)) (hKne (γ r)) hhalfr (w (γ r))
  have hnorm : ‖N r‖ = ‖N 0‖ :=
    norm_eq_of_isParallelAlongSection_global cov hmet hconn hγ hNd hNp h0 hr
  have hinner : (⟪N r, Q r⟫ : ℝ) = ⟪N 0, Q 0⟫ :=
    inner_eq_of_isParallelAlongSection_global cov hmet hconn hγ hNd hQd hNp hQp h0 hr
  have hdist : infDist (w (γ r)) (K (γ r)) ≤ ‖N 0‖ := by
    rw [hN0', hpmin]; exact hmaxf (γ r)
  have hmul : ‖N r‖ * infDist (w (γ r)) (K (γ r)) ≤ ‖N 0‖ * ‖N 0‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
  rw [inner_sub_right] at hbound
  show (⟪N r, w (γ r)⟫ : ℝ) ≤ ⟪N 0, w (γ 0)⟫
  rw [hval0]
  linarith

section TouchingPoint

variable [ContMDiffCovariantDerivative cov 1]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [I.Boundaryless]
  (covT : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative covT 1]

omit [∀ (x : M), CompleteSpace (V x)] in
/-- **The cross-fibre touching-point step.**

Where the distance to a parallel family of closed convex sets is maximal over `M`, the
Laplacian of the section points *into* the family: `⟪n, Δw(x₀)⟫ ≤ 0` for the outward normal
`n = w(x₀) − p` at the nearest point.

**This is the half of the bundle maximum principle that `BundleMaximumPrinciple.lean` does
not do.** There the tested direction is a vector of one fibre and the maximum is assumed of
`⟪N,u⟫` already; here it is assumed of the *distance*, which is what the first-touching-time
argument actually produces, and turning one into the other is what needs the direction to be
carried between fibres. It is carried one curve at a time: transport along a fixed curve is a
linear equation, is an isometry, and carries `K`.

The direction is an artefact-free existential: `p` is the nearest point, which exists because
the fibres are complete and `K x₀` is closed, convex and nonempty. -/
theorem inner_laplacianSection_nonpos_of_infDist_le (hmet : cov.IsMetricCompatible)
    (hpar : HasParallelTransport I F V cov) {K : Π x : M, Set (V x)}
    (hKne : ∀ x, (K x).Nonempty)
    (hK : IsParallelSet I F V cov K) {w : Π y : M, V y} (hw : CMDiff 2 (T% w)) {x₀ : M}
    (hmaxf : ∀ x, infDist (w x) (K x) ≤ infDist (w x₀) (K x₀))
    {p : V x₀} (hpmin : ‖w x₀ - p‖ = infDist (w x₀) (K x₀))
    (hhalf : ∀ q ∈ K x₀, (⟪w x₀ - p, q - p⟫ : ℝ) ≤ 0)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x₀)) :
    (⟪w x₀ - p, cov.laplacianSection covT hw x₀⟫ : ℝ) ≤ 0 := by
  refine inner_laplacianSection_nonpos_of_forall_geodesic_max cov covT hmet hpar hw b ?_
  intro v γ sset N hrun hN0 hNd hNp
  exact isLocalMax_inner_of_infDist_le cov hmet hpar hKne hK hmaxf hpmin hhalf
    hrun.isOpen hrun.isPreconnected hrun.mem_zero hrun.mdiff hrun.mdiffAlong
    (congrArg TotalSpace.proj hrun.init) hNd hNp hN0

/-- The same with the nearest point constructed rather than given: it exists because the
fibres are complete and `K x₀` is closed, convex and nonempty. -/
theorem exists_nearest_inner_laplacianSection_nonpos (hmet : cov.IsMetricCompatible)
    (hpar : HasParallelTransport I F V cov) {K : Π x : M, Set (V x)}
    (hKcl : ∀ x, IsClosed (K x)) (hKcv : ∀ x, Convex ℝ (K x)) (hKne : ∀ x, (K x).Nonempty)
    (hK : IsParallelSet I F V cov K) {w : Π y : M, V y} (hw : CMDiff 2 (T% w)) {x₀ : M}
    (hmaxf : ∀ x, infDist (w x) (K x) ≤ infDist (w x₀) (K x₀))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x₀)) :
    ∃ p ∈ K x₀, ‖w x₀ - p‖ = infDist (w x₀) (K x₀) ∧
      (⟪w x₀ - p, cov.laplacianSection covT hw x₀⟫ : ℝ) ≤ 0 := by
  obtain ⟨p, hp, hpmin, hhalf⟩ :=
    exists_nearest_point (V := V x₀) (hKcl x₀) (hKcv x₀) (hKne x₀) (w x₀)
  exact ⟨p, hp, hpmin,
    inner_laplacianSection_nonpos_of_infDist_le cov covT hmet hpar hKne hK hw hmaxf hpmin
      hhalf b⟩

end TouchingPoint

end CovariantDerivative
