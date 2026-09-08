/-
**The divergence of the curvature tensor.**

`div Rm(Y,Z,W) = ∑ᵢ ⟪(∇_{eᵢ}Rm)(Y,Z)W, eᵢ⟫` is the trace of `∇Rm` over its direction
slot against its fourth. It is what the contracted second Bianchi identity is about, and
through that identity what `Δ scal` is about.

Two facts from `CurvatureDeriv.lean` make it well defined, and neither is free:

* `(∇_X Rm)(Y,Z)W` at `x` depends only on `X x` (`covCurvature_congr_dir`), so
  `v ↦ (∇_v Rm)(Y,Z)W` is a function on `T_xM` at all;
* it is `C^∞(M)`-linear there (`covCurvature_smul_dir`, `covCurvature_add_dir`), so that
  function is linear.

Together they give a genuine endomorphism of `T_xM`, and the divergence is its trace —
so frame-independence is the algebraic `LinearMap.trace_eq_sum_inner`, not a computation.
This is the same route `RicciForm.lean` took to the scalar curvature, one level up:
there the object traced was a bilinear form and the trace was metric, here it is an
endomorphism and the trace is not.

The tangent-vector-valued function is built on globally `C²` extensions
(`exists_contMDiff_two_extension`), exactly as `ricciAt` is.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureDeriv
import RicciFlowBlueprint.RicciForm

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]

section Pointwise

/-- **`(∇_v Rm)(Y,Z)W` as a function of a tangent vector.** Evaluated on a globally `C²`
extension of `v`, which exists by `exists_contMDiff_two_extension` and gives the same
answer by `covCurvature_congr_dir`. -/
noncomputable def covCurvatureAt (Y Z W : Π y : M, TangentSpace I y) (x : M)
    (v : TangentSpace I x) : TangentSpace I x :=
  cov.covCurvature (RicciFlowBlueprint.exists_contMDiff_two_extension v).choose Y Z W x

omit [CompleteSpace E] in
-- BENCH: cov-curvature-at-eq
/-- `covCurvatureAt` computes `covCurvature` on any globally `C²` direction field. -/
theorem covCurvatureAt_eq {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvatureAt Y Z W x (X x) = cov.covCurvature X Y Z W x := by
  obtain ⟨hc, hv⟩ := (RicciFlowBlueprint.exists_contMDiff_two_extension (X x)).choose_spec
  exact cov.covCurvature_congr_dir hc hX hY hZ hW hv

omit [CompleteSpace E] in
/-- Additivity in the tangent vector, from `covCurvature_add_dir`. -/
theorem covCurvatureAt_add {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (v w : TangentSpace I x) :
    cov.covCurvatureAt Y Z W x (v + w)
      = cov.covCurvatureAt Y Z W x v + cov.covCurvatureAt Y Z W x w := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  obtain ⟨U, hU, hUw⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w
  have e1 : cov.covCurvatureAt Y Z W x (V x) = cov.covCurvature V Y Z W x :=
    cov.covCurvatureAt_eq hV hY hZ hW
  have e2 : cov.covCurvatureAt Y Z W x (U x) = cov.covCurvature U Y Z W x :=
    cov.covCurvatureAt_eq hU hY hZ hW
  have e3 : cov.covCurvatureAt Y Z W x ((V + U) x) = cov.covCurvature (V + U) Y Z W x :=
    cov.covCurvatureAt_eq (hV.add_section hU) hY hZ hW
  have hsum : (V + U) x = v + w := by show V x + U x = v + w; rw [hVv, hUw]
  rw [← hsum, e3, cov.covCurvature_add_dir hV hU hY hZ hW, ← e1, ← e2, hVv, hUw]

omit [CompleteSpace E] in
/-- Homogeneity in the tangent vector, from `covCurvature_smul_dir` applied to a constant
coefficient. -/
theorem covCurvatureAt_smul {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (c : ℝ) (v : TangentSpace I x) :
    cov.covCurvatureAt Y Z W x (c • v) = c • cov.covCurvatureAt Y Z W x v := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun _ : M ↦ c) := contMDiff_const
  have e1 : cov.covCurvatureAt Y Z W x (V x) = cov.covCurvature V Y Z W x :=
    cov.covCurvatureAt_eq hV hY hZ hW
  have e3 : cov.covCurvatureAt Y Z W x (((fun _ : M ↦ c) • V) x)
      = cov.covCurvature ((fun _ : M ↦ c) • V) Y Z W x :=
    cov.covCurvatureAt_eq (hf.smul_section hV) hY hZ hW
  have hsmul : ((fun _ : M ↦ c) • V) x = c • v := by show c • V x = c • v; rw [hVv]
  rw [← hsmul, e3, cov.covCurvature_smul_dir hf hV hY hZ hW, ← e1, hVv]

open scoped Classical in
/-- **`v ↦ (∇_v Rm)(Y,Z)W` as a linear endomorphism of `T_xM`.** Junk (`0`) off the
regularity `covCurvatureAt_add` and `covCurvatureAt_smul` need, exactly as `ricci` is
junk off its own. -/
noncomputable def covCurvatureEndo (Y Z W : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
  if h : CMDiff 2 (T% Y) ∧ CMDiff 2 (T% Z) ∧ CMDiff 3 (T% W) then
    { toFun := cov.covCurvatureAt Y Z W x
      map_add' := cov.covCurvatureAt_add h.1 h.2.1 h.2.2
      map_smul' := fun c v ↦ cov.covCurvatureAt_smul h.1 h.2.1 h.2.2 c v }
  else 0

omit [CompleteSpace E] in
theorem covCurvatureEndo_apply {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (v : TangentSpace I x) :
    cov.covCurvatureEndo Y Z W x v = cov.covCurvatureAt Y Z W x v := by
  have h : CMDiff 2 (T% Y) ∧ CMDiff 2 (T% Z) ∧ CMDiff 3 (T% W) := ⟨hY, hZ, hW⟩
  simp only [covCurvatureEndo, h, and_self, ↓reduceDIte]
  rfl

end Pointwise

section Divergence

/-- **The divergence of the curvature tensor**, `div Rm(Y,Z,W)(x)`: the trace of the
endomorphism `v ↦ (∇_v Rm)(Y,Z)W` of `T_xM`. No metric enters — this is an endomorphism
trace, not the metric trace the scalar curvature is. -/
noncomputable def divCurvature (Y Z W : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  LinearMap.trace ℝ (TangentSpace I x) (cov.covCurvatureEndo Y Z W x)

omit [CompleteSpace E] in
-- BENCH: div-curvature-frame-independent
/-- **`div Rm` is the frame sum, over any orthonormal basis of `T_xM`.** Hypothesis-free
in the frame: the trace of an endomorphism does not depend on the basis. -/
theorem divCurvature_eq_sum_basis {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.divCurvature Y Z W x = ∑ i, ⟪cov.covCurvatureAt Y Z W x (b i), b i⟫ := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  rw [divCurvature, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : ⟪b i, cov.covCurvatureEndo Y Z W x (b i)⟫
      = ⟪cov.covCurvatureEndo Y Z W x (b i), b i⟫ := real_inner_comm _ _
  rw [e, cov.covCurvatureEndo_apply hY hZ hW]

omit [CompleteSpace E] in
/-- **`div Rm` computed from a `C²` frame** whose values at `x` are orthonormal:
`div Rm(Y,Z,W)(x) = ∑ᵢ ⟪(∇_{eᵢ}Rm)(Y,Z)W, eᵢ⟫`. -/
theorem divCurvature_eq_sum_frame {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {ι : Type*} [Fintype ι] {b : ι → Π y : M, TangentSpace I y}
    (hb : ∀ i, CMDiff 2 (T% (b i))) (v : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, b i x = v i) :
    cov.divCurvature Y Z W x = ∑ i, ⟪cov.covCurvature (b i) Y Z W x, b i x⟫ := by
  rw [cov.divCurvature_eq_sum_basis hY hZ hW v]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hbv i, ← cov.covCurvatureAt_eq (hb i) hY hZ hW, hbv i]

end Divergence

end CovariantDerivative
