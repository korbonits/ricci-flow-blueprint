/-
The maximum principles on a Riemannian manifold.

`MaximumPrinciple.lean` and `TensorMaximumPrinciple.lean` prove the scalar and
tensor maximum principles on an arbitrary compact space, with the differential
inequality at a spatial extremum taken as a hypothesis. Here that hypothesis is
discharged on a closed (compact, boundaryless) Riemannian manifold from the
evolution equation `∂ₜu = Δu + F(u)` and the second-derivative test
(`SecondDerivativeTest.lean`): at a spatial minimum of `u(t, ·)` the Laplacian
is `≥ 0`, so `∂ₜu ≥ F(u)` there.

For the tensor version, `u` takes values in a real inner product space `V` (the
trivial bundle `M × V`), and the equation is stated componentwise:
`⟪n, ∂ₜu⟫ = Δ⟪n, u⟫ + ⟪n, F(u)⟫` for every fixed `n ∈ V`. On a trivial bundle
this is the equation `∂ₜu = Δu + F(u)`, the Laplacian of a `V`-valued function
being the Laplacian of its components; the bundle version, with an evolving
metric on the fibres, is Hamilton's setting and needs the Laplacian on sections
(`CovariantDerivative.laplacian`) together with Uhlenbeck's trick.

The connection is arbitrary: the second-derivative test holds for every `cov`,
because the connection term `(∇_X X) f` vanishes at a critical point.
-/
import RicciFlowBlueprint.TensorMaximumPrinciple
import RicciFlowBlueprint.SecondDerivativeTest

open Set Filter Topology Bundle CovariantDerivative
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint
namespace MaximumPrinciple

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [CompactSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

-- BENCH: max-principle-scalar-manifold
/-- **The scalar maximum principle on a closed Riemannian manifold.** If `u` solves
`∂ₜu = Δu + F(u)` on `[0, T]` with `F` Lipschitz, `u(t, ·)` is `C²`, and `φ` solves
`φ' = F(φ)` with `φ 0 ≤ u 0` everywhere, then `φ t ≤ u t x` for all `t ∈ [0, T]` and `x`. -/
theorem le_of_laplacian {u ut : ℝ → M → ℝ} {F φ : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x, ContMDiffAt I 𝓘(ℝ, ℝ) 2 (u t) x)
    (hF : LipschitzWith K F)
    (heq : ∀ t ∈ Icc 0 T, ∀ x, ut t x = cov.laplacianFun (u t) x + F (u t x))
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (F (φ t)) t)
    (h0 : ∀ x, φ 0 ≤ u 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x, φ t ≤ u t x := by
  refine le_of_deriv_ge_at_min hT hu hut hF ?_ hφ h0
  intro t ht x₀ hmin
  have hloc : IsLocalMin (u t) x₀ := Eventually.of_forall hmin
  have := laplacianFun_nonneg_of_isLocalMin cov (hreg t ht x₀) hloc
  rw [heq t ht x₀]
  linarith

-- BENCH: max-principle-scalar-manifold-upper
/-- **The scalar maximum principle on a closed Riemannian manifold, upper bound.** -/
theorem le_of_laplacian' {u ut : ℝ → M → ℝ} {F φ : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x, ContMDiffAt I 𝓘(ℝ, ℝ) 2 (u t) x)
    (hF : LipschitzWith K F)
    (heq : ∀ t ∈ Icc 0 T, ∀ x, ut t x = cov.laplacianFun (u t) x + F (u t x))
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (F (φ t)) t)
    (h0 : ∀ x, u 0 x ≤ φ 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ φ t := by
  refine le_of_deriv_le_at_max hT hu hut hF ?_ hφ h0
  intro t ht x₀ hmax
  -- a maximum of `u t` is a minimum of `-u t`
  have hloc : IsLocalMin (-u t) x₀ := Eventually.of_forall fun x ↦ by
    simpa using hmax x
  have hreg' : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (-u t) x₀ := (hreg t ht x₀).neg
  have h1 := laplacianFun_nonneg_of_isLocalMin cov hreg' hloc
  rw [cov.laplacianFun_neg] at h1
  rw [heq t ht x₀]
  linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

-- BENCH: max-principle-tensor-manifold
/-- **Hamilton's tensor maximum principle on a closed Riemannian manifold**, for the trivial
bundle `M × V`. If `u : ℝ → M → V` solves `∂ₜu = Δu + F(u)` on `[0, T]`, stated componentwise
as `⟪n, ∂ₜu⟫ = Δ⟪n, u⟫ + ⟪n, F(u)⟫` for every `n`, with `F` Lipschitz and `u(t, ·)` `C²`, and
`K ⊆ V` is closed, convex, nonempty and preserved by the ODE `v' = F(v)` in Nagumo's form,
then `u 0 x ∈ K` for all `x` implies `u t x ∈ K` for all `t ∈ [0, T]` and `x`. -/
theorem mem_of_laplacian {u ut : ℝ → M → V} {F : V → V} {K : Set V} {L : NNReal} {T : ℝ}
    (hKcl : IsClosed K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x, ContMDiffAt I 𝓘(ℝ, V) 2 (u t) x)
    (hF : LipschitzWith L F)
    (heq : ∀ t ∈ Icc 0 T, ∀ x, ∀ n : V,
      ⟪n, ut t x⟫ = cov.laplacianFun (fun y ↦ ⟪n, u t y⟫) x + ⟪n, F (u t x)⟫)
    (hK : ∀ p ∈ K, ∀ n : V, (∀ q ∈ K, ⟪n, q - p⟫ ≤ 0) → ⟪n, F p⟫ ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K := by
  refine mem_of_deriv_le_at_max hKcl hKc hKne hu hut hF ?_ hK h0
  intro t ht x₀ n hmax
  -- a maximum of `⟪n, u t ·⟫` is a minimum of `⟪-n, u t ·⟫`
  have hloc : IsLocalMin (fun y ↦ ⟪-n, u t y⟫) x₀ := Eventually.of_forall fun x ↦ by
    simp only [inner_neg_left]
    linarith [hmax x]
  have hreg' : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ ⟪-n, u t y⟫) x₀ :=
    ((innerSL ℝ (-n)).contMDiff.contMDiffAt).comp x₀ (hreg t ht x₀)
  have h1 := laplacianFun_nonneg_of_isLocalMin cov hreg' hloc
  have h2 := heq t ht x₀ (-n)
  rw [inner_neg_left, inner_neg_left] at h2
  linarith

end MaximumPrinciple
end RicciFlowBlueprint
