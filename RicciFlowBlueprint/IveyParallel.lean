/-
**Hamilton's pinching set is a parallel subbundle.**

The cross-fibre half of the tensor maximum principle compares `dist(u(t,x), K_x)` between
*different* fibres, and Hamilton's argument asks that the family `x ↦ K_x` be preserved by
parallel transport. For `K_x = iveyEndoSet (T_xM)` that is not a hypothesis to be checked
against a connection: **every** fibre isometry preserves the set (`mem_iveyEndoSet_conj_iff`,
since the trace and `λ_min` are conjugation-invariant), and parallel transport for a metric
connection is an isometry (`ParallelTransportGlobal.lean`). So the two compose and there is
no transport computation at all.

**Why state it separately.** The naturality lemma is about an abstract isometry and says
nothing about a connection; the transport theorem is about a connection and says nothing
about the set. Neither on its own is the hypothesis the maximum principle wants, and a
general lemma that is never instantiated is a liability. One line joins them, and that line
is the statement the cross-fibre argument will quote.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.IveyEndo
import RicciFlowBlueprint.ParallelTransportGlobal

open Bundle Set CovariantDerivative
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  {γ : ℝ → M} {s : Set ℝ}

set_option maxSynthPendingDepth 3

-- BENCH: ivey-parallel-subbundle
/-- **The pinching set is preserved by parallel transport.**

Parallel transport along `γ` is a linear isometry of fibres for a metric connection, and the
pinching set is invariant under every fibre isometry — so the transported operator lies in
the set exactly when the original does. Nothing about the connection enters beyond metric
compatibility, and nothing about the set enters beyond its naturality.

The transport isometry is returned alongside, since the cross-fibre argument needs the same
map for `u` and for `K`. -/
theorem exists_parallelTransport_mem_iveyEndoSet_iff
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (hγv : ∀ w ∈ s, MDiffAlongAt γ (velocity (I := I) γ) w)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {t : ℝ} (ht : t ∈ s)
    [Nontrivial (TangentSpace I (γ t₀))] [FiniteDimensional ℝ (TangentSpace I (γ t₀))]
    [Nontrivial (TangentSpace I (γ t))] [FiniteDimensional ℝ (TangentSpace I (γ t))] :
    ∃ P : TangentSpace I (γ t₀) ≃ₗᵢ[ℝ] TangentSpace I (γ t),
      (∀ V : Π u : ℝ, TangentSpace I (γ u), (∀ u ∈ s, MDiffAlongAt γ V u) →
          IsParallelAlong cov γ V s → V t = P (V t₀)) ∧
        ∀ A : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀),
          (endoConj P A ∈ Pinching.iveyEndoSet (TangentSpace I (γ t))
            ↔ A ∈ Pinching.iveyEndoSet (TangentSpace I (γ t₀))) := by
  obtain ⟨P, hP⟩ :=
    exists_parallelTransportIsometry_global cov hmet hs hconn hγ hγv ht₀ ht
  exact ⟨P, hP, fun A ↦ Pinching.mem_iveyEndoSet_conj_iff P A⟩

end RicciFlowBlueprint
