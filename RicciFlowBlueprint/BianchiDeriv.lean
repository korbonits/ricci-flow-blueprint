/-
**The differentiated second Bianchi identity.**

The second Bianchi identity is a cyclic identity in the *direction* slot of `∇Rm` and the
first two slots of `Rm`, with `Rm`'s last slot a spectator:

  `(∇_X Rm)(Y,Z)W + (∇_Y Rm)(Z,X)W + (∇_Z Rm)(X,Y)W = 0`.

Differentiating it once more gives the same cyclic identity for `∇²Rm`:

  `(∇²_{X,Y}Rm)(A,B)C + (∇²_{X,A}Rm)(B,Y)C + (∇²_{X,B}Rm)(Y,A)C = 0`,

and this is what the trace step of `∂ₜRm = ΔRm + Q` consumes: summing it over `Y = eᵢ`
with `X = eᵢ` turns `Δ Rm` into two traces of `∇²Rm` with the derivative slots in the
*wrong* order, which the Ricci identity for the curvature tensor then reorders at the cost
of terms quadratic in `Rm`.

**Nothing is differentiated twice by hand.** `∇²Rm` is `∇Rm` differentiated once with one
correction per slot, so the cyclic sum splits into a leading term and four correction
groups, and *every one of the five vanishes by the undifferentiated identity*:

* the leading terms combine, by additivity of `∇` on sections, into `∇` of the section
  `u ↦ (∇_Y Rm)(A,B)C u + (∇_A Rm)(B,Y)C u + (∇_B Rm)(Y,A)C u`, which is the zero section
  by `bianchi_second` at every point, and `∇` of the zero section is zero;
* the four correction groups are the cyclic sum with one field replaced by its derivative
  — `∇_X Y`, `∇_X A`, `∇_X B`, `∇_X C` — so each is `bianchi_second` again.

So the proof is five applications of `bianchi_second` and one `IsCovariantDerivativeOn.zero`.
The regrouping is what carries the content: the corrections do *not* cancel in pairs, they
cancel three at a time, one group per differentiated field.

Regularity is one derivative above `bianchi_second` throughout, and the last slot stays the
expensive one: `C` is asked for four derivatives so that `∇_X C` still has the three that
`bianchi_second` wants of its spectator slot.

**No metric is needed**, exactly as for `bianchi_second` itself: the three Riemannian
instances of the ambient section are `omit`ted. That is worth knowing before the trace
step, which is where a metric first becomes unavoidable.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureLaplacian

open Bundle Filter Module VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

variable {X Y A B C : Π y : M, TangentSpace I y} {x : M}

omit [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
-- BENCH: bianchi-second-deriv
/-- **The differentiated second Bianchi identity.**

`(∇²_{X,Y}Rm)(A,B)C + (∇²_{X,A}Rm)(B,Y)C + (∇²_{X,B}Rm)(Y,A)C = 0`, the cyclic identity of
`bianchi_second` one derivative up.

The five terms of `cov2Curvature` split the cyclic sum into a leading part and four
correction groups. The leading parts combine into `∇_X` of the section that
`bianchi_second` says is zero. Each correction group is the cyclic sum with one field
replaced by its covariant derivative, so is `bianchi_second` again — the corrections cancel
three at a time, one group per differentiated field, not in pairs. -/
theorem cov2Curvature_cyclic_eq_zero (hcov : cov.torsion = 0)
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y)) (hA : CMDiff 3 (T% A))
    (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X Y A B C x + cov.cov2Curvature X A B Y C x
      + cov.cov2Curvature X B Y A C x = 0 := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  -- Lower-regularity copies of the hypotheses.
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  -- The covariant derivatives that appear in the corrections, at the levels
  -- `bianchi_second` asks of each slot.
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY hX2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA hX2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB hX2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC hX
  -- The three `∇Rm` sections whose cyclic sum vanishes.
  have hs1 : CMDiff 1 (T% (fun u ↦ cov.covCurvature Y A B C u)) :=
    cov.contMDiff_covCurvature hY hA hB hC
  have hs2 : CMDiff 1 (T% (fun u ↦ cov.covCurvature A B Y C u)) :=
    cov.contMDiff_covCurvature hA hB hY hC
  have hs3 : CMDiff 1 (T% (fun u ↦ cov.covCurvature B Y A C u)) :=
    cov.contMDiff_covCurvature hB hY hA hC
  -- The leading terms: `∇_X` of a section that is identically zero.
  have hzero : (fun u ↦ cov.covCurvature Y A B C u + cov.covCurvature A B Y C u
      + cov.covCurvature B Y A C u) = (0 : Π y : M, TangentSpace I y) := by
    funext u
    exact cov.bianchi_second hcov hY2 hA2 hB2 hC3
  have hsum : cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
      + cov (fun u ↦ cov.covCurvature A B Y C u) x (X x)
      + cov (fun u ↦ cov.covCurvature B Y A C u) x (X x) = 0 := by
    -- Additivity of `∇`, stated in applied form: `rw` will not match the Pi-typed `+`
    -- that `IsCovariantDerivativeOn.add` produces against a lambda-typed one.
    have hadd1 : cov (fun u ↦ cov.covCurvature Y A B C u
          + cov.covCurvature A B Y C u) x (X x)
        = cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
          + cov (fun u ↦ cov.covCurvature A B Y C u) x (X x) :=
      congrArg (fun L ↦ L (X x)) (cov.isCovariantDerivativeOn.add
        ((hs1.mdifferentiable h1) x) ((hs2.mdifferentiable h1) x))
    have hadd2 : cov (fun u ↦ (cov.covCurvature Y A B C u + cov.covCurvature A B Y C u)
          + cov.covCurvature B Y A C u) x (X x)
        = cov (fun u ↦ cov.covCurvature Y A B C u + cov.covCurvature A B Y C u) x (X x)
          + cov (fun u ↦ cov.covCurvature B Y A C u) x (X x) :=
      congrArg (fun L ↦ L (X x)) (cov.isCovariantDerivativeOn.add
        (((hs1.add_section hs2).mdifferentiable h1) x) ((hs3.mdifferentiable h1) x))
    have hval : cov (fun u ↦ (cov.covCurvature Y A B C u + cov.covCurvature A B Y C u)
        + cov.covCurvature B Y A C u) x (X x) = 0 := by
      have hz : cov (0 : Π y : M, TangentSpace I y) x = 0 :=
        cov.isCovariantDerivativeOn.zero
      rw [hzero, hz]
      exact zero_apply _
    rw [← hval, hadd2, hadd1]
  -- The four correction groups, one per differentiated field.
  have kY := cov.bianchi_second hcov (x := x) hDY hA2 hB2 hC3
  have kA := cov.bianchi_second hcov (x := x) hY2 hDA hB2 hC3
  have kB := cov.bianchi_second hcov (x := x) hY2 hA2 hDB hC3
  have kC := cov.bianchi_second hcov (x := x) hY2 hA2 hB2 hDC
  unfold cov2Curvature
  linear_combination (norm := module) hsum - kY - kA - kB - kC

end CovariantDerivative
