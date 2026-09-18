/-
**The curvature operator in dimension three**, from the Ricci tensor alone.

Hamilton's pinching argument is about the eigenvalues `λ ≥ μ ≥ ν` of the curvature operator,
which lives on `Λ²T_x\M`. `CurvatureLambda.lean` records an elaboration obstruction that has
kept `curvatureForm` — the operator as a bilinear form on `Λ²` — out of reach.

**In dimension three that object is not needed.** The Weyl tensor vanishes, and the whole
`(0,4)` tensor is carried by an *endomorphism* of `T_x\M`:

  `Rm₃ = scal · Id − 2 Ric♯`,  eigenvalues `λ = R − 2r₁` etc.

and `HomBundle.lean` supplies `End(TM)` with a connection on it. This file proves the two
algebraic facts that identification rests on, and **neither needs the Weyl tensor, an
algebraic decomposition theorem, or any expansion of a four-linear form over a basis.**

*The dictionary.* `Ric(bᵢ,bᵢ) = ∑ⱼ K(bᵢ,bⱼ)` is the definition of Ricci as a trace, true in
every dimension. In dimension three that reads `r₀ = p + q`, `r₁ = p + r`, `r₂ = q + r` with
`p,q,r` the three sectional curvatures, so `R = 2(p+q+r)` and `R − 2r₀ = 2r` — exactly
`Pinching.lean`'s normalisation, in which `λ,μ,ν` are *twice* the sectional curvatures. The
only input beyond the trace identity is pair symmetry, to know `K(bᵢ,bⱼ) = K(bⱼ,bᵢ)`.

*The diagonalisation.* If `b` is a Ricci eigenbasis then `Rm` is diagonal in it, and this is
the same trace identity read the other way: `Ric(b₀,b₁) = ∑ⱼ Rm(bⱼ,b₀,b₁,bⱼ)` has only
*one* surviving term in dimension three, the other two dying on the two antisymmetries. So
the off-diagonal component is the Ricci component, and vanishes with it. **The literature
routes this through the vanishing of the Weyl tensor; it does not have to.**

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureOperator
import RicciFlowBlueprint.RicciForm

open Bundle Filter
open scoped Manifold ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace CovariantDerivative

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

private theorem two_ne_zero₅ : (2 : ℕ∞ω) ≠ 0 := by norm_num

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **Ricci is the first-slot trace of the `(0,4)` tensor**, pointwise and against any
orthonormal basis of `T_x\M`: `Ric(v,w) = ∑ᵢ Rm(bᵢ, v, w, bᵢ)`.

This is `ricci_eq_sum_inner_frame` read on the global `C²` extensions `curvatureTensorAt` is
defined through, so the two sides are the same expression once `extendTwo_apply_self` has
fired. -/
theorem ricciAt_eq_sum_curvatureTensorAt {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (v w : TangentSpace I x) :
    cov.ricciAt x v w = ∑ i, cov.curvatureTensorAt (b i) v w (b i) := by
  have hv : CMDiff 2 (T% (extendTwo (I := I) v)) := contMDiff_extendTwo v
  have hw : CMDiff 2 (T% (extendTwo (I := I) w)) := contMDiff_extendTwo w
  have e1 : cov.ricciAt x v w
      = cov.ricci (extendTwo (I := I) v) (extendTwo (I := I) w) x := by
    have h := cov.ricciAt_eq (x := x) hv hw
    rwa [extendTwo_apply_self, extendTwo_apply_self] at h
  rw [e1, cov.ricci_eq_sum_inner_frame hw (fr := fun i ↦ extendTwo (I := I) (b i)) b
    (fun i ↦ ((contMDiff_extendTwo (b i)).mdifferentiable two_ne_zero₅) x)
    (fun i ↦ extendTwo_apply_self (b i))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [extendTwo_apply_self]
  rfl

variable {a b c d : TangentSpace I x}

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] [CompleteSpace E] in
/-- `Rm(v,v,c,d) = 0`. -/
theorem curvatureTensorAt_self_fst (v : TangentSpace I x) :
    cov.curvatureTensorAt v v c d = 0 := by
  have h := cov.curvatureTensorAt_antisymm_fst_snd (a := v) (b := v) (c := c) (d := d)
  linarith

/-- `Rm(a,b,v,v) = 0`. -/
theorem curvatureTensorAt_self_thd
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (v : TangentSpace I x) :
    cov.curvatureTensorAt a b v v = 0 := by
  have h := cov.curvatureTensorAt_antisymm_thd_fth (a := a) (b := b) (c := v) (d := v)
    hmetric htor
  linarith

/-- `Rm(v,w,w,v) = Rm(w,v,v,w)`: the sectional curvature of a plane does not depend on the
order of the spanning pair. Pair symmetry, directly. -/
theorem curvatureTensorAt_sec_comm
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (v w : TangentSpace I x) :
    cov.curvatureTensorAt v w w v = cov.curvatureTensorAt w v v w :=
  cov.curvatureTensorAt_pair_symm hmetric htor

section Three

variable (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
  (htor : cov.torsion = 0) (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x))

include hmetric htor in
/-- **Ricci against a three-dimensional orthonormal basis is the sum of the two sectional
curvatures of the planes through that vector**: `r_m = ∑_{n ≠ m} K(b_m, b_n)`. -/
theorem ricciAt_diag_eq_sum_sec (m : Fin 3) :
    cov.ricciAt x (b m) (b m)
      = ∑ n, cov.curvatureTensorAt (b m) (b n) (b n) (b m) := by
  rw [cov.ricciAt_eq_sum_curvatureTensorAt b]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  exact (cov.curvatureTensorAt_pair_symm hmetric htor).symm

include hmetric htor in
/-- **The eigenvalue dictionary in dimension three**:
`scal − 2 Ric(b₀,b₀) = 2 Rm(b₁,b₂,b₂,b₁)`.

So the endomorphism `scal · Id − 2 Ric♯` has, in any orthonormal basis, diagonal entries
twice the sectional curvatures of the *opposite* planes — which is exactly the normalisation
of `Pinching.lean`, where `λ, μ, ν` are twice the sectional curvatures and `R = λ+μ+ν`. On
the unit `S³` this reads `6 − 4 = 2 = 2·1`.

**No vanishing of the Weyl tensor is used**, and no expansion of a four-linear form over a
basis: only the trace identity for `Ric` and pair symmetry. -/
theorem scalarCurvatureAt_sub_two_ricciAt :
    cov.scalarCurvatureAt x - 2 * cov.ricciAt x (b 0) (b 0)
      = 2 * cov.curvatureTensorAt (b 1) (b 2) (b 2) (b 1) := by
  have hdiag : ∀ m n : Fin 3, cov.curvatureTensorAt (b m) (b n) (b n) (b m)
      = cov.curvatureTensorAt (b n) (b m) (b m) (b n) := fun m n ↦
    cov.curvatureTensorAt_sec_comm hmetric htor _ _
  have hzero : ∀ m : Fin 3, cov.curvatureTensorAt (b m) (b m) (b m) (b m) = 0 := fun m ↦
    cov.curvatureTensorAt_self_fst (b m)
  have hric : ∀ m : Fin 3, cov.ricciAt x (b m) (b m)
      = ∑ n, cov.curvatureTensorAt (b m) (b n) (b n) (b m) :=
    cov.ricciAt_diag_eq_sum_sec hmetric htor b
  have hscal : cov.scalarCurvatureAt x = ∑ m, cov.ricciAt x (b m) (b m) :=
    cov.scalarCurvatureAt_eq_sum_basis b
  simp only [hric, Fin.sum_univ_three] at hscal ⊢
  rw [hscal]
  have h01 := hdiag 0 1
  have h02 := hdiag 0 2
  have h12 := hdiag 1 2
  have e0 := hzero 0
  have e1 := hzero 1
  have e2 := hzero 2
  linarith

include hmetric htor in
/-- **In dimension three a Ricci eigenbasis diagonalises the curvature tensor.**

`Ric(b₀,b₁) = ∑ⱼ Rm(bⱼ,b₀,b₁,bⱼ)` has only one surviving summand: at `j = 0` the first pair
is `(b₀,b₀)` and at `j = 1` the second pair is `(b₁,b₁)`, so the two antisymmetries kill them.
What is left is the single off-diagonal component, which therefore vanishes with the Ricci
component. **This is the whole content of "Weyl vanishes in dimension three" as far as the
pinching argument is concerned**, and it costs three lines rather than a decomposition
theorem. -/
theorem curvatureTensorAt_eq_zero_of_ricciAt_eq_zero
    (h : cov.ricciAt x (b 0) (b 1) = 0) :
    cov.curvatureTensorAt (b 2) (b 0) (b 1) (b 2) = 0 := by
  have hsum := cov.ricciAt_eq_sum_curvatureTensorAt b (b 0) (b 1)
  rw [h, Fin.sum_univ_three] at hsum
  have h0 : cov.curvatureTensorAt (b 0) (b 0) (b 1) (b 0) = 0 :=
    cov.curvatureTensorAt_self_fst (b 0)
  have h1 : cov.curvatureTensorAt (b 1) (b 0) (b 1) (b 1) = 0 :=
    cov.curvatureTensorAt_self_thd hmetric htor (b 1)
  linarith

end Three

end CovariantDerivative
