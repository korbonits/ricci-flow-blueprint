/-
**Hamilton's pinching condition on the curvature operator itself.**

`IveyEndo.lean` puts the pinching set on endomorphisms of an abstract inner product space;
`CurvatureOperatorThree.lean` builds `Rm₃ = scal·Id − 2 Ric♯` and shows it self-adjoint. This
file joins them: `Rm₃` is diagonalisable at every point, and membership of the endomorphism
pinching set *is* `IsIveyPinched` of its eigenvalues.

**The spectral theorem is used once and mathlib does all of it.** `Rm₃` is self-adjoint
(`inner_curvatureOperator_comm`, which needs the connection metric and torsion-free only
because `Ric` is symmetric), so `LinearMap.IsSymmetric.eigenvectorBasis` hands over an
orthonormal eigenbasis — and mathlib's `eigenvalues` is **already sorted in decreasing
order** (`eigenvalues_antitone`), which is exactly `λ ≥ μ ≥ ν`. So no sorting permutation
and no reindexing appears anywhere.

**What this closes.** The dimension-three route claims that Hamilton's pinching condition,
stated in `Pinching.lean` on an eigenvalue triple obeying an ODE, is a condition on a section
of `End(TM)` that a maximum principle can be run on. Between those two statements sit four
files, and until this one the chain was never composed. Composing it is what checks that the
convexity proved in `IveyEndo.lean` is convexity of *Hamilton's* set and not of some other
one.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureOperatorThree
import RicciFlowBlueprint.IveyEndo

open Bundle Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

open RicciFlowBlueprint RicciFlowBlueprint.Pinching

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

variable {x : M}

/-- **`Rm₃` is a symmetric operator**, in the form the spectral theorem wants. This is
`inner_curvatureOperator_comm` restated, and it rests on nothing but symmetry of `Ric`. -/
theorem isSymmetric_curvatureOperator
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    (x : M) :
    LinearMap.IsSymmetric
      ((cov.curvatureOperator x : TangentSpace I x →ₗ[ℝ] TangentSpace I x)) :=
  fun v w ↦ cov.inner_curvatureOperator_comm hmet htor v w

/-- **`Rm₃` is diagonalisable at every point, with eigenvalues in decreasing order.**

The eigenvalues are the `λ ≥ μ ≥ ν` of `Pinching.lean`: `CurvatureOperatorThree.lean` checks
the normalisation three ways, the diagonal entries being twice the sectional curvature of the
opposite plane and the trace being `scal`. -/
theorem exists_orthonormalBasis_curvatureOperator
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    (x : M) {n : ℕ} (hdim : finrank ℝ (TangentSpace I x) = n) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (TangentSpace I x)) (e : Fin n → ℝ),
      Antitone e ∧ ∀ i, cov.curvatureOperator x (b i) = e i • (b i : TangentSpace I x) := by
  have hs := cov.isSymmetric_curvatureOperator hmet htor x
  refine ⟨hs.eigenvectorBasis hdim, hs.eigenvalues hdim, hs.eigenvalues_antitone hdim,
    fun i ↦ ?_⟩
  exact hs.apply_eigenvectorBasis hdim i

section Pinched

variable [Nontrivial (TangentSpace I x)] [FiniteDimensional ℝ (TangentSpace I x)]

-- BENCH: curvature-operator-pinched
/-- **Hamilton's pinching condition on `Rm₃`.**

At every point of a three-dimensional manifold there are reals `λ ≥ μ ≥ ν` — the eigenvalues
of `Rm₃` — such that `Rm₃` lies in the endomorphism pinching set exactly when
`IsIveyPinched λ μ ν` holds. So the set `IveyConvex.lean` proves closed and convex, and which
`Pinching.lean` proves invariant under the curvature ODE, is a condition on the operator that
the maximum principle on `End(TM)` can be run against.

**This is the composition the dimension-three route has been claiming.** Every step of it was
present — the operator, its self-adjointness, the endomorphism set, the eigenvalue
dictionary — and none of them said anything to the others until they were composed. -/
theorem exists_mem_iveyEndoSet_iff
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    (hdim : finrank ℝ (TangentSpace I x) = 3) :
    ∃ e : Fin 3 → ℝ, Antitone e ∧
      (cov.curvatureOperator x ∈ iveyEndoSet (TangentSpace I x)
        ↔ IsIveyPinched (e 0) (e 1) (e 2)) := by
  obtain ⟨b, e, he, hA⟩ := cov.exists_orthonormalBasis_curvatureOperator hmet htor x hdim
  exact ⟨e, he, mem_iveyEndoSet_iff_isIveyPinched_antitone b hA he⟩

end Pinched

end CovariantDerivative
