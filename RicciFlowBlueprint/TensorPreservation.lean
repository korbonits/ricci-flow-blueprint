/-
**The maximum principles with a MOVING metric**, scalar and tensor.

`ManifoldMaximumPrinciple.lean` proves the principle for one fixed connection, and
`mem_of_laplacian_time` lets the *reaction* depend on `t`. What a Ricci flow actually
produces is a *Laplacian* that depends on `t`: the equation `∂ₜu = Δ_{g_t}u + F t (u)` is
solved against a metric that is itself evolving.

**That costs nothing, and isolating it is what shows where Uhlenbeck's trick is really
forced.** The maximum principle never looks at the Laplacian except to ask that
`Δ⟪n, u t ·⟫ ≥ 0` at a spatial minimum of `⟪n, u t ·⟫`, and that holds for each metric
separately (`laplacianFun_nonneg_of_isLocalMin`). So the abstract
`TensorMaximumPrinciple.mem_of_deriv_le_at_max_time` applies directly, with the metric's
`RiemannianBundle` instance introduced inside the proof, one time at a time --- exactly the
manoeuvre `ScalarPreservation.lean` makes one level down.

**What this does NOT buy, and do not claim otherwise**: the fibre `V` is a *fixed* inner
product space here. Hamilton's curvature operator lives in `Λ²T_xM`, whose inner product
moves with `g_t`, and trivialising *that* is the content of Uhlenbeck's trick. This theorem
is what the trick is applied *to* --- the last piece of the manifold-side machinery that can
be built without it.

The scalar version (`le_of_laplacian_moving`) is the abstract form of the argument
`ScalarPreservation.lean` makes inline, and is recorded here so that the two live together.
-/
import RicciFlowBlueprint.ManifoldMaximumPrinciple
import RicciFlowBlueprint.Variation

open Set Bundle CovariantDerivative
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint
namespace MaximumPrinciple

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [CompactSpace M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

set_option maxSynthPendingDepth 3

-- BENCH: max-principle-scalar-moving
/-- **The scalar maximum principle on a closed manifold whose metric moves.** `u` solves
`∂ₜu = Δ_{g_t}u + F t (u)` on `[0, T]`, `φ` solves the comparison ODE `φ' = F t (φ)`, and
`φ 0 ≤ u 0` everywhere; then `φ t ≤ u t x` throughout.

This is `le_of_laplacian` with the connection allowed to vary, and the abstract form of the
argument `ScalarPreservation.lean` makes inline. -/
theorem le_of_laplacian_moving
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
    {u ut : ℝ → M → ℝ} {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x, ContMDiffAt I 𝓘(ℝ, ℝ) 2 (u t) x)
    (hF : ∀ t, LipschitzWith K (F t))
    (heq : ∀ t ∈ Icc 0 T, ∀ x,
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      ut t x = (leviCivitaOfMetric (g t)).laplacianFun (u t) x + F t (u t x))
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (F t (φ t)) t)
    (h0 : ∀ x, φ 0 ≤ u 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x, φ t ≤ u t x := by
  refine le_of_deriv_ge_at_min_time hT hu hut hF ?_ hφ h0
  intro t ht x₀ hmin
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  have h1 := laplacianFun_nonneg_of_isLocalMin (leviCivitaOfMetric (g t)) (hreg t ht x₀)
    (Filter.Eventually.of_forall hmin)
  have h2 := heq t ht x₀
  linarith

-- BENCH: max-principle-tensor-moving
/-- **Hamilton's tensor maximum principle on a closed manifold whose metric moves.**

`u : ℝ → M → V` takes values in a *fixed* inner product space, but the equation
`∂ₜu = Δ_{g_t}u + F t (u)` is read against the Levi-Civita connection of `g t`, so both the
Laplacian and the reaction move with `t`. If `K ⊆ V` is closed, convex, nonempty and
preserved by the non-autonomous ODE `v' = F t (v)` in Nagumo's form, then `u 0 x ∈ K`
everywhere gives `u t x ∈ K` everywhere, for `t ∈ [0, T]`.

The proof is `mem_of_deriv_le_at_max_time` with its touching-point hypothesis discharged by
`laplacianFun_nonneg_of_isLocalMin` **for the metric `g t` alone** --- the `letI` lives
inside the proof and is re-introduced at each time, which is what makes a moving metric
free. A maximum of `⟪n, u t ·⟫` is a minimum of `⟪-n, u t ·⟫`, so no linearity lemma for
the Laplacian is needed either. -/
theorem mem_of_laplacian_moving
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
    {u ut : ℝ → M → V} {F : ℝ → V → V} {K : Set V} {L : NNReal} {T : ℝ}
    (hKcl : IsClosed K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x, ContMDiffAt I 𝓘(ℝ, V) 2 (u t) x)
    (hF : ∀ t, LipschitzWith L (F t))
    (heq : ∀ t ∈ Icc 0 T, ∀ x, ∀ n : V,
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      ⟪n, ut t x⟫ = (leviCivitaOfMetric (g t)).laplacianFun (fun y ↦ ⟪n, u t y⟫) x
        + ⟪n, F t (u t x)⟫)
    (hK : ∀ t ∈ Icc 0 T, ∀ p ∈ K, ∀ n : V, (∀ q ∈ K, ⟪n, q - p⟫ ≤ 0) → ⟪n, F t p⟫ ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K := by
  refine mem_of_deriv_le_at_max_time hKcl hKc hKne hu hut hF ?_ hK h0
  intro t ht x₀ n hmax
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  -- a maximum of `⟪n, u t ·⟫` is a minimum of `⟪-n, u t ·⟫`
  have hloc : IsLocalMin (fun y ↦ ⟪-n, u t y⟫) x₀ := Filter.Eventually.of_forall fun x ↦ by
    simp only [inner_neg_left]
    linarith [hmax x]
  have hreg' : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ ⟪-n, u t y⟫) x₀ :=
    ((innerSL ℝ (-n)).contMDiff.contMDiffAt).comp x₀ (hreg t ht x₀)
  have h1 := laplacianFun_nonneg_of_isLocalMin (leviCivitaOfMetric (g t)) hreg' hloc
  have h2 := heq t ht x₀ (-n)
  rw [inner_neg_left, inner_neg_left] at h2
  linarith

end MaximumPrinciple
end RicciFlowBlueprint
