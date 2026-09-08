/-
**The second covariant derivative of the curvature tensor.**

`∇²Rm` is `∇` of `∇Rm`, so it carries one correction per slot of `∇Rm` — five in all:

  `(∇²_{X,Y}Rm)(A,B)C = ∇_X((∇_Y Rm)(A,B)C) − (∇_{∇_X Y}Rm)(A,B)C
      − (∇_Y Rm)(∇_X A,B)C − (∇_Y Rm)(A,∇_X B)C − (∇_Y Rm)(A,B)(∇_X C)`.

The outer direction slot `X` is free, as it was for `∇Rm`: every term is either a
continuous linear map evaluated at `X x` or `∇Rm` in a slot where `∇Rm` is now known to be
pointwise (`covCurvature_congr_dir`, `_congr_snd`, `_congr_thd`, `_congr_fth`) applied to a
field whose value at `x` depends only on `X x`. The inner slot `Y` is the familiar
cancellation: the Leibniz term of `∇_X(f·(∇_Y Rm)(A,B)C)` is matched by the one from
`(∇_{∇_X(f•Y)}Rm)(A,B)C`.

Regularity is inherited from the four-slot pointwise lemmas, and the last slot is the
expensive one throughout: `covCurvature_congr_fth` asks a `C³` coefficient, so `C` is asked
for four derivatives and `X` for three.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Divergence

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

variable {f : M → ℝ} {X X' Y A B C : Π y : M, TangentSpace I y} {x : M}

/-- **The second covariant derivative of the curvature tensor**,
`(∇²_{X,Y}Rm)(A,B)C`: one correction for each of `∇Rm`'s four slots, plus the leading
term. -/
noncomputable def cov2Curvature (X Y A B C : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x :=
  cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
    - cov.covCurvature (fun u ↦ cov Y u (X u)) A B C x
    - cov.covCurvature Y (fun u ↦ cov A u (X u)) B C x
    - cov.covCurvature Y A (fun u ↦ cov B u (X u)) C x
    - cov.covCurvature Y A B (fun u ↦ cov C u (X u)) x

omit [CompleteSpace E] in
-- BENCH: cov2-curvature-congr-dir
/-- **`(∇²_{X,Y}Rm)(A,B)C` at `x` depends only on `X x`.** Each of the five terms is
separately pointwise in `X`: the first is a continuous linear map evaluated at `X x`, and
the other four are `∇Rm` in a slot where it is pointwise, applied to a field whose value
at `x` is determined by `X x`. -/
theorem cov2Curvature_congr_dir
    (hX : CMDiff 3 (T% X)) (hX' : CMDiff 3 (T% X')) (hY : CMDiff 3 (T% Y))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (hval : X x = X' x) :
    cov.cov2Curvature X Y A B C x = cov.cov2Curvature X' Y A B C x := by
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hX'2 : CMDiff 2 (T% X') := hX'.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hA3 : CMDiff ((2 : ℕ∞ω) + 1) (T% A) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hA
  have hB3 : CMDiff ((2 : ℕ∞ω) + 1) (T% B) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hB
  have hC4 : CMDiff ((3 : ℕ∞ω) + 1) (T% C) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hC
  -- the four difference fields, and the values they take at `x`
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY3 hX2
  have hDY' : CMDiff 2 (T% (fun u ↦ cov Y u (X' u))) := cov.contMDiff_cov_apply hY3 hX'2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA3 hX2
  have hDA' : CMDiff 2 (T% (fun u ↦ cov A u (X' u))) := cov.contMDiff_cov_apply hA3 hX'2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB3 hX2
  have hDB' : CMDiff 2 (T% (fun u ↦ cov B u (X' u))) := cov.contMDiff_cov_apply hB3 hX'2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC4 hX
  have hDC' : CMDiff 3 (T% (fun u ↦ cov C u (X' u))) := cov.contMDiff_cov_apply hC4 hX'
  have vY : (fun u ↦ cov Y u (X u)) x = (fun u ↦ cov Y u (X' u)) x := by
    show cov Y x (X x) = cov Y x (X' x); rw [hval]
  have vA : (fun u ↦ cov A u (X u)) x = (fun u ↦ cov A u (X' u)) x := by
    show cov A x (X x) = cov A x (X' x); rw [hval]
  have vB : (fun u ↦ cov B u (X u)) x = (fun u ↦ cov B u (X' u)) x := by
    show cov B x (X x) = cov B x (X' x); rw [hval]
  have vC : (fun u ↦ cov C u (X u)) x = (fun u ↦ cov C u (X' u)) x := by
    show cov C x (X x) = cov C x (X' x); rw [hval]
  have e1 : cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
      = cov (fun u ↦ cov.covCurvature Y A B C u) x (X' x) := by rw [hval]
  have e2 := cov.covCurvature_congr_dir hDY hDY' hA2 hB2 hC3 vY
  have e3 := cov.covCurvature_congr_snd hY2 hDA hDA' hB2 hC3 vA
  have e4 := cov.covCurvature_congr_thd hY2 hA2 hDB hDB' hC3 vB
  have e5 := cov.covCurvature_congr_fth hY2 hA2 hB2 hDC hDC' vC
  simp only [cov2Curvature, e1, e2, e3, e4, e5]

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇²Rm` is `C^∞(M)`-linear in its outer direction slot.** Each of the five terms
picks up one `f x`: the first by linearity of `∇`, the others because `∇_{f•X} = f∇_X` and
`∇Rm` is tensorial in the slot that lands in. -/
theorem cov2Curvature_smul_dir
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature (f • X) Y A B C x = f x • cov.cov2Curvature X Y A B C x := by
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f := hf.of_le (by norm_num)
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hA3 : CMDiff ((2 : ℕ∞ω) + 1) (T% A) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hA
  have hB3 : CMDiff ((2 : ℕ∞ω) + 1) (T% B) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hB
  have hC4 : CMDiff ((3 : ℕ∞ω) + 1) (T% C) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hC
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY3 hX2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA3 hX2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB3 hX2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC4 hX
  have e1 : cov (fun u ↦ cov.covCurvature Y A B C u) x ((f • X) x)
      = f x • cov (fun u ↦ cov.covCurvature Y A B C u) x (X x) := by
    show cov (fun u ↦ cov.covCurvature Y A B C u) x (f x • X x) = _
    exact map_smul _ _ _
  have e2 : cov.covCurvature (fun u ↦ cov Y u ((f • X) u)) A B C x
      = f x • cov.covCurvature (fun u ↦ cov Y u (X u)) A B C x := by
    rw [cov.cov_smul_dir Y f X]
    exact cov.covCurvature_smul_dir hf2 hDY hA2 hB2 hC3
  have e3 : cov.covCurvature Y (fun u ↦ cov A u ((f • X) u)) B C x
      = f x • cov.covCurvature Y (fun u ↦ cov A u (X u)) B C x := by
    rw [cov.cov_smul_dir A f X]
    exact cov.covCurvature_smul_snd hf2 hY2 hDA hB2 hC3
  have e4 : cov.covCurvature Y A (fun u ↦ cov B u ((f • X) u)) C x
      = f x • cov.covCurvature Y A (fun u ↦ cov B u (X u)) C x := by
    rw [cov.cov_smul_dir B f X]
    exact cov.covCurvature_smul_thd hf2 hY2 hA2 hDB hC3
  have e5 : cov.covCurvature Y A B (fun u ↦ cov C u ((f • X) u)) x
      = f x • cov.covCurvature Y A B (fun u ↦ cov C u (X u)) x := by
    rw [cov.cov_smul_dir C f X]
    exact cov.covCurvature_smul_fth hf hY2 hA2 hB2 hDC
  simp only [cov2Curvature, e1, e2, e3, e4, e5]
  module

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇²Rm` is additive in its outer direction slot.** -/
theorem cov2Curvature_add_dir
    (hX : CMDiff 3 (T% X)) (hX' : CMDiff 3 (T% X')) (hY : CMDiff 3 (T% Y))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature (X + X') Y A B C x
      = cov.cov2Curvature X Y A B C x + cov.cov2Curvature X' Y A B C x := by
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hX'2 : CMDiff 2 (T% X') := hX'.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hA3 : CMDiff ((2 : ℕ∞ω) + 1) (T% A) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hA
  have hB3 : CMDiff ((2 : ℕ∞ω) + 1) (T% B) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hB
  have hC4 : CMDiff ((3 : ℕ∞ω) + 1) (T% C) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hC
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY3 hX2
  have hDY' : CMDiff 2 (T% (fun u ↦ cov Y u (X' u))) := cov.contMDiff_cov_apply hY3 hX'2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA3 hX2
  have hDA' : CMDiff 2 (T% (fun u ↦ cov A u (X' u))) := cov.contMDiff_cov_apply hA3 hX'2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB3 hX2
  have hDB' : CMDiff 2 (T% (fun u ↦ cov B u (X' u))) := cov.contMDiff_cov_apply hB3 hX'2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC4 hX
  have hDC' : CMDiff 3 (T% (fun u ↦ cov C u (X' u))) := cov.contMDiff_cov_apply hC4 hX'
  have hsY : (fun u ↦ cov Y u ((X + X') u))
      = (fun u ↦ cov Y u (X u)) + (fun u ↦ cov Y u (X' u)) := by
    funext u; show cov Y u (X u + X' u) = _; exact map_add _ _ _
  have hsA : (fun u ↦ cov A u ((X + X') u))
      = (fun u ↦ cov A u (X u)) + (fun u ↦ cov A u (X' u)) := by
    funext u; show cov A u (X u + X' u) = _; exact map_add _ _ _
  have hsB : (fun u ↦ cov B u ((X + X') u))
      = (fun u ↦ cov B u (X u)) + (fun u ↦ cov B u (X' u)) := by
    funext u; show cov B u (X u + X' u) = _; exact map_add _ _ _
  have hsC : (fun u ↦ cov C u ((X + X') u))
      = (fun u ↦ cov C u (X u)) + (fun u ↦ cov C u (X' u)) := by
    funext u; show cov C u (X u + X' u) = _; exact map_add _ _ _
  have e1 : cov (fun u ↦ cov.covCurvature Y A B C u) x ((X + X') x)
      = cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
        + cov (fun u ↦ cov.covCurvature Y A B C u) x (X' x) := by
    show cov (fun u ↦ cov.covCurvature Y A B C u) x (X x + X' x) = _
    exact map_add _ _ _
  simp only [cov2Curvature, e1, hsY, hsA, hsB, hsC,
    cov.covCurvature_add_dir hDY hDY' hA2 hB2 hC3,
    cov.covCurvature_add_snd hY2 hDA hDA' hB2 hC3,
    cov.covCurvature_add_thd hY2 hA2 hDB hDB' hC3,
    cov.covCurvature_add_fth hY2 hA2 hB2 hDC hDC']
  module

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇²Rm` is `C^∞(M)`-linear in its inner direction slot.** As with the second slot of
`∇Rm`, this is a cancellation: the Leibniz term of `∇_X(f·(∇_Y Rm)(A,B)C)` is matched by
the one `∇_X(f•Y) = f∇_X Y + (Xf)Y` produces in the second term. -/
theorem cov2Curvature_smul_snd
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X (f • Y) A B C x = f x • cov.cov2Curvature X Y A B C x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f := hf.of_le (by norm_num)
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hA3 : CMDiff ((2 : ℕ∞ω) + 1) (T% A) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hA
  have hB3 : CMDiff ((2 : ℕ∞ω) + 1) (T% B) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hB
  have hC4 : CMDiff ((3 : ℕ∞ω) + 1) (T% C) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hC
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY3 hX2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA3 hX2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB3 hX2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC4 hX
  have hfm : ∀ y, MDiffAt f y := hf2.mdifferentiable h2
  have hYm : ∀ y, MDiffAt (T% Y) y := hY2.mdifferentiable h2
  -- `Xf` is `C²`: this is what `f ∈ C³` buys, exactly as in `covCurvature_smul_fth`
  have hg : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun y ↦ d% f y (X y)) := fun y ↦
    RicciFlowBlueprint.contMDiffAt_mvfderiv_apply (hf y) (hX2 y) (by norm_num)
  have hS : MDiffAt (T% (fun u ↦ cov.covCurvature Y A B C u)) x :=
    ((cov.contMDiff_covCurvature hY hA hB hC).mdifferentiable h1) x
  have esec : (fun u ↦ cov.covCurvature (f • Y) A B C u)
      = f • (fun u ↦ cov.covCurvature Y A B C u) := by
    funext u
    exact cov.covCurvature_smul_dir hf2 hY2 hA2 hB2 hC3
  have t1 : cov (fun u ↦ cov.covCurvature (f • Y) A B C u) x (X x)
      = f x • cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
        + (d% f x (X x)) • cov.covCurvature Y A B C x := by
    rw [esec, cov.isCovariantDerivativeOn.leibniz hS (hfm x)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have e2sec : (fun u ↦ cov (f • Y) u (X u))
      = f • (fun u ↦ cov Y u (X u)) + ((fun u ↦ d% f u (X u)) • Y) := by
    funext u
    rw [cov.isCovariantDerivativeOn.leibniz (hYm u) (hfm u)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have t2 : cov.covCurvature (fun u ↦ cov (f • Y) u (X u)) A B C x
      = f x • cov.covCurvature (fun u ↦ cov Y u (X u)) A B C x
        + (d% f x (X x)) • cov.covCurvature Y A B C x := by
    rw [e2sec, cov.covCurvature_add_dir (hf2.smul_section hDY) (hg.smul_section hY2) hA2 hB2 hC3,
      cov.covCurvature_smul_dir hf2 hDY hA2 hB2 hC3,
      cov.covCurvature_smul_dir hg hY2 hA2 hB2 hC3]
  have t3 : cov.covCurvature (f • Y) (fun u ↦ cov A u (X u)) B C x
      = f x • cov.covCurvature Y (fun u ↦ cov A u (X u)) B C x :=
    cov.covCurvature_smul_dir hf2 hY2 hDA hB2 hC3
  have t4 : cov.covCurvature (f • Y) A (fun u ↦ cov B u (X u)) C x
      = f x • cov.covCurvature Y A (fun u ↦ cov B u (X u)) C x :=
    cov.covCurvature_smul_dir hf2 hY2 hA2 hDB hC3
  have t5 : cov.covCurvature (f • Y) A B (fun u ↦ cov C u (X u)) x
      = f x • cov.covCurvature Y A B (fun u ↦ cov C u (X u)) x :=
    cov.covCurvature_smul_dir hf2 hY2 hA2 hB2 hDC
  simp only [cov2Curvature, t1, t2, t3, t4, t5]
  module

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇²Rm` is additive in its inner direction slot.** -/
theorem cov2Curvature_add_snd {Y' : Π y : M, TangentSpace I y}
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y)) (hY' : CMDiff 3 (T% Y'))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X (Y + Y') A B C x
      = cov.cov2Curvature X Y A B C x + cov.cov2Curvature X Y' A B C x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hY'2 : CMDiff 2 (T% Y') := hY'.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hY'3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y') := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY'
  have hA3 : CMDiff ((2 : ℕ∞ω) + 1) (T% A) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hA
  have hB3 : CMDiff ((2 : ℕ∞ω) + 1) (T% B) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hB
  have hC4 : CMDiff ((3 : ℕ∞ω) + 1) (T% C) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hC
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY3 hX2
  have hDY' : CMDiff 2 (T% (fun u ↦ cov Y' u (X u))) := cov.contMDiff_cov_apply hY'3 hX2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA3 hX2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB3 hX2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC4 hX
  have hS : MDiffAt (T% (fun u ↦ cov.covCurvature Y A B C u)) x :=
    ((cov.contMDiff_covCurvature hY hA hB hC).mdifferentiable h1) x
  have hS' : MDiffAt (T% (fun u ↦ cov.covCurvature Y' A B C u)) x :=
    ((cov.contMDiff_covCurvature hY' hA hB hC).mdifferentiable h1) x
  have esec : (fun u ↦ cov.covCurvature (Y + Y') A B C u)
      = (fun u ↦ cov.covCurvature Y A B C u) + (fun u ↦ cov.covCurvature Y' A B C u) := by
    funext u
    exact cov.covCurvature_add_dir hY2 hY'2 hA2 hB2 hC3
  have t1 : cov (fun u ↦ cov.covCurvature (Y + Y') A B C u) x (X x)
      = cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
        + cov (fun u ↦ cov.covCurvature Y' A B C u) x (X x) := by
    rw [esec, cov.isCovariantDerivativeOn.add hS hS']
    simp only [add_apply]
  have e2sec : (fun u ↦ cov (Y + Y') u (X u))
      = (fun u ↦ cov Y u (X u)) + (fun u ↦ cov Y' u (X u)) := by
    funext u
    rw [cov.isCovariantDerivativeOn.add (hY2.mdifferentiable h2 u)
      (hY'2.mdifferentiable h2 u)]
    simp only [add_apply]
    rfl
  simp only [cov2Curvature, t1, e2sec,
    cov.covCurvature_add_dir hDY hDY' hA2 hB2 hC3,
    cov.covCurvature_add_dir hY2 hY'2 hDA hB2 hC3,
    cov.covCurvature_add_dir hY2 hY'2 hA2 hDB hC3,
    cov.covCurvature_add_dir hY2 hY'2 hA2 hB2 hDC]
  module

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
/-- `∇²Rm` kills the zero field in its inner direction slot. -/
theorem cov2Curvature_zero_snd
    (hX : CMDiff 3 (T% X)) (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B))
    (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X 0 A B C x = 0 := by
  have hz3 : CMDiff 3 (T% (0 : Π y : M, TangentSpace I y)) := contMDiff_zeroSection _ _
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 3 (fun _ : M ↦ (0 : ℝ)) := contMDiff_const
  have hzs : ((fun _ : M ↦ (0 : ℝ)) • (0 : Π y : M, TangentSpace I y))
      = (0 : Π y : M, TangentSpace I y) := by funext y; simp
  calc cov.cov2Curvature X 0 A B C x
      = cov.cov2Curvature X ((fun _ : M ↦ (0 : ℝ)) • (0 : Π y : M, TangentSpace I y))
          A B C x := by rw [hzs]
    _ = (fun _ : M ↦ (0 : ℝ)) x
          • cov.cov2Curvature X (0 : Π y : M, TangentSpace I y) A B C x :=
        cov.cov2Curvature_smul_snd hf hX hz3 hA hB hC
    _ = 0 := by simp

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **The inner direction slot of `∇²Rm` applied to a finite `C³` combination.** -/
theorem cov2Curvature_sum_smul_snd {ι : Type*} {s : Finset ι} {g : ι → M → ℝ}
    {V : ι → Π y : M, TangentSpace I y}
    (hg : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) 3 (g i)) (hV : ∀ i ∈ s, CMDiff 3 (T% (V i)))
    (hX : CMDiff 3 (T% X)) (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B))
    (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X (fun y ↦ ∑ i ∈ s, g i y • V i y) A B C x
      = ∑ i ∈ s, g i x • cov.cov2Curvature X (V i) A B C x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y ↦ ∑ i ∈ (∅ : Finset ι), g i y • V i y)
          = (0 : Π y : M, TangentSpace I y) := by funext y; simp
      rw [hz, cov.cov2Curvature_zero_snd hX hA hB hC, Finset.sum_empty]
  | insert a t ha ih =>
      have hga : ContMDiff I 𝓘(ℝ, ℝ) 3 (g a) := hg a (Finset.mem_insert_self a t)
      have hVa : CMDiff 3 (T% (V a)) := hV a (Finset.mem_insert_self a t)
      have hgt : ∀ i ∈ t, ContMDiff I 𝓘(ℝ, ℝ) 3 (g i) := fun i hi ↦
        hg i (Finset.mem_insert_of_mem hi)
      have hVt : ∀ i ∈ t, CMDiff 3 (T% (V i)) := fun i hi ↦ hV i (Finset.mem_insert_of_mem hi)
      have hsum : CMDiff 3 (T% (fun y ↦ ∑ i ∈ t, g i y • V i y)) :=
        ContMDiff.sum_section fun i hi ↦ (hgt i hi).smul_section (hVt i hi)
      have hsplit : (fun y ↦ ∑ i ∈ insert a t, g i y • V i y)
          = (g a • V a) + (fun y ↦ ∑ i ∈ t, g i y • V i y) := by
        funext y
        show ∑ i ∈ insert a t, g i y • V i y = g a y • V a y + ∑ i ∈ t, g i y • V i y
        rw [Finset.sum_insert ha]
      rw [hsplit, cov.cov2Curvature_add_snd hX (hga.smul_section hVa) hsum hA hB hC,
        cov.cov2Curvature_smul_snd hga hX hVa hA hB hC, ih hgt hVt, Finset.sum_insert ha]

omit [CompleteSpace E] in
/-- **`∇²Rm` is local in its inner direction slot.** Only the leading term needs the germ;
the other four are `∇Rm` in its direction slot, which is pointwise. -/
theorem cov2Curvature_congr_snd_of_eventuallyEq {Y' : Π y : M, TangentSpace I y}
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y)) (hY' : CMDiff 3 (T% Y'))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (h : Y =ᶠ[𝓝 x] Y') :
    cov.cov2Curvature X Y A B C x = cov.cov2Curvature X Y' A B C x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hY'2 : CMDiff 2 (T% Y') := hY'.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hY'3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y') := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY'
  have hA3 : CMDiff ((2 : ℕ∞ω) + 1) (T% A) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hA
  have hB3 : CMDiff ((2 : ℕ∞ω) + 1) (T% B) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hB
  have hC4 : CMDiff ((3 : ℕ∞ω) + 1) (T% C) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hC
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY3 hX2
  have hDY' : CMDiff 2 (T% (fun u ↦ cov Y' u (X u))) := cov.contMDiff_cov_apply hY'3 hX2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA3 hX2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB3 hX2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC4 hX
  obtain ⟨U, hUeq, hUopen, hxU⟩ := eventually_nhds_iff.mp h
  have hsec : (fun u ↦ cov.covCurvature Y A B C u)
      =ᶠ[𝓝 x] fun u ↦ cov.covCurvature Y' A B C u :=
    eventually_nhds_iff.mpr ⟨U, fun u hu ↦
      cov.covCurvature_congr_dir hY2 hY'2 hA2 hB2 hC3 (hUeq u hu), hUopen, hxU⟩
  have hcovY : cov Y x = cov Y' x :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq (hY2.mdifferentiable h2 x)
      (hY'2.mdifferentiable h2 x) Filter.univ_mem h
  have vY : (fun u ↦ cov Y u (X u)) x = (fun u ↦ cov Y' u (X u)) x := by
    show cov Y x (X x) = cov Y' x (X x); rw [hcovY]
  have e1 : cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
      = cov (fun u ↦ cov.covCurvature Y' A B C u) x (X x) := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((cov.contMDiff_covCurvature hY hA hB hC).mdifferentiable h1 x)
      ((cov.contMDiff_covCurvature hY' hA hB hC).mdifferentiable h1 x) Filter.univ_mem hsec]
  have e2 := cov.covCurvature_congr_dir hDY hDY' hA2 hB2 hC3 vY
  have e3 := cov.covCurvature_congr_dir hY2 hY'2 hDA hB2 hC3 (hUeq x hxU)
  have e4 := cov.covCurvature_congr_dir hY2 hY'2 hA2 hDB hC3 (hUeq x hxU)
  have e5 := cov.covCurvature_congr_dir hY2 hY'2 hA2 hB2 hDC (hUeq x hxU)
  simp only [cov2Curvature, e1, e2, e3, e4, e5]

omit [CompleteSpace E] in
-- BENCH: cov2-curvature-congr-snd
/-- **`(∇²_{X,Y}Rm)(A,B)C` at `x` depends only on `Y x`.** The frame-and-globalise argument
at `C³`, since `cov2Curvature_smul_snd` asks its coefficient for three derivatives. -/
theorem cov2Curvature_congr_snd {Y' : Π y : M, TangentSpace I y}
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y)) (hY' : CMDiff 3 (T% Y'))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (hval : Y x = Y' x) :
    cov.cov2Curvature X Y A B C x = cov.cov2Curvature X Y' A B C x := by
  classical
  set e := trivializationAt E (TangentSpace I (M := M)) x with he
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hu : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hxe
  set b := Module.finBasis ℝ E with hb
  obtain ⟨fr, hs, hfrsm⟩ : ∃ fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      IsOrthonormalFrameOn I E 3 fr e.baseSet ∧ ∀ i, CMDiff[e.baseSet] 3 (T% (fr i)) :=
    ⟨_, b.orthonormalFrame_isOrthonormalFrameOn (IB := I) (n := 3) e,
      fun i ↦ b.contMDiffOn_orthonormalFrame_baseSet e i⟩
  have hframe : ∀ i, ∃ Ei : Π y : M, TangentSpace I y, CMDiff 3 (T% Ei) ∧
      Ei =ᶠ[𝓝 x] fr i := by
    intro i
    obtain ⟨Ei, hEi, hEieq⟩ := RicciFlowBlueprint.exists_contMDiff_eventuallyEq (n := 3) hu
      (hfrsm i)
    exact ⟨Ei, by simpa using hEi, hEieq⟩
  choose Ei hEi hEieq using hframe
  have hcoeff : ∀ (V : Π y : M, TangentSpace I y), CMDiff 3 (T% V) → ∀ i,
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 3 g ∧
        g =ᶠ[𝓝 x] (LinearMap.piApply (hs.coeff i) V) := by
    intro V hV i
    obtain ⟨g, hg, hgeq⟩ := RicciFlowBlueprint.exists_contMDiff_eventuallyEq_fun (n := 3) hu
      (hs.contMDiffOn_coeff hV.contMDiffOn i)
    exact ⟨g, by simpa using hg, hgeq⟩
  have key : ∀ (V : Π y : M, TangentSpace I y) (hV : CMDiff 3 (T% V)),
      cov.cov2Curvature X V A B C x
        = ∑ i, hs.coeff i x (V x) • cov.cov2Curvature X (Ei i) A B C x := by
    intro V hV
    choose g hg hgeq using hcoeff V hV
    have hsum : CMDiff 3 (T% (fun y ↦ ∑ i, g i y • Ei i y)) :=
      ContMDiff.sum_section fun i _ ↦ (hg i).smul_section (hEi i)
    have heq : V =ᶠ[𝓝 x] fun y ↦ ∑ i, g i y • Ei i y := by
      have hall : ∀ᶠ y in 𝓝 x, ∀ i, g i y = hs.coeff i y (V y) ∧ Ei i y = fr i y :=
        Filter.eventually_all.mpr fun i ↦ (hgeq i).and (hEieq i)
      filter_upwards [hs.toIsLocalFrameOn.eventually_eq_sum_coeff_smul V hu, hall] with y hy hy'
      rw [hy]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [(hy' i).1, (hy' i).2]
    rw [cov.cov2Curvature_congr_snd_of_eventuallyEq hX hV hsum hA hB hC heq,
      cov.cov2Curvature_sum_smul_snd (fun i _ ↦ hg i) (fun i _ ↦ hEi i) hX hA hB hC]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hgeq i).eq_of_nhds]
    rfl
  rw [key Y hY, key Y' hY']
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [hs.toIsLocalFrameOn.coeff_congr hval i]

section Laplacian

/-- **`∇²Rm` as a function of two tangent vectors.** Evaluated on globally `C³` extensions,
which exist by `exists_contMDiff_three_extension` and give the same answer by
`cov2Curvature_congr_dir` and `cov2Curvature_congr_snd`. -/
noncomputable def cov2CurvatureAt (A B C : Π y : M, TangentSpace I y) (x : M)
    (v w : TangentSpace I x) : TangentSpace I x :=
  cov.cov2Curvature (RicciFlowBlueprint.exists_contMDiff_three_extension v).choose
    (RicciFlowBlueprint.exists_contMDiff_three_extension w).choose A B C x

omit [CompleteSpace E] in
theorem cov2CurvatureAt_eq
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2CurvatureAt A B C x (X x) (Y x) = cov.cov2Curvature X Y A B C x := by
  obtain ⟨hXc, hXv⟩ :=
    (RicciFlowBlueprint.exists_contMDiff_three_extension (X x)).choose_spec
  obtain ⟨hYc, hYv⟩ :=
    (RicciFlowBlueprint.exists_contMDiff_three_extension (Y x)).choose_spec
  rw [cov2CurvatureAt, cov.cov2Curvature_congr_dir hXc hX hYc hA hB hC hXv]
  exact cov.cov2Curvature_congr_snd hX hYc hY hA hB hC hYv

omit [CompleteSpace E] in
theorem cov2CurvatureAt_add_left
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (v v' w : TangentSpace I x) :
    cov.cov2CurvatureAt A B C x (v + v') w
      = cov.cov2CurvatureAt A B C x v w + cov.cov2CurvatureAt A B C x v' w := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension v
  obtain ⟨V', hV', hV'v⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension v'
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension w
  have hsum : (V + V') x = v + v' := by show V x + V' x = v + v'; rw [hVv, hV'v]
  have e0 : cov.cov2CurvatureAt A B C x ((V + V') x) (W x)
      = cov.cov2Curvature (V + V') W A B C x :=
    cov.cov2CurvatureAt_eq (hV.add_section hV') hW hA hB hC
  have e1 : cov.cov2CurvatureAt A B C x (V x) (W x) = cov.cov2Curvature V W A B C x :=
    cov.cov2CurvatureAt_eq hV hW hA hB hC
  have e2 : cov.cov2CurvatureAt A B C x (V' x) (W x) = cov.cov2Curvature V' W A B C x :=
    cov.cov2CurvatureAt_eq hV' hW hA hB hC
  rw [← hsum, ← hWw, e0, cov.cov2Curvature_add_dir hV hV' hW hA hB hC, ← e1, ← e2,
    hVv, hV'v]

omit [CompleteSpace E] in
theorem cov2CurvatureAt_smul_left
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (c : ℝ) (v w : TangentSpace I x) :
    cov.cov2CurvatureAt A B C x (c • v) w = c • cov.cov2CurvatureAt A B C x v w := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension v
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension w
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 3 (fun _ : M ↦ c) := contMDiff_const
  have hsm : ((fun _ : M ↦ c) • V) x = c • v := by show c • V x = c • v; rw [hVv]
  have e0 : cov.cov2CurvatureAt A B C x (((fun _ : M ↦ c) • V) x) (W x)
      = cov.cov2Curvature ((fun _ : M ↦ c) • V) W A B C x :=
    cov.cov2CurvatureAt_eq (hf.smul_section hV) hW hA hB hC
  have e1 : cov.cov2CurvatureAt A B C x (V x) (W x) = cov.cov2Curvature V W A B C x :=
    cov.cov2CurvatureAt_eq hV hW hA hB hC
  rw [← hsm, ← hWw, e0, cov.cov2Curvature_smul_dir hf hV hW hA hB hC, ← e1, hVv]

omit [CompleteSpace E] in
theorem cov2CurvatureAt_add_right
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (v w w' : TangentSpace I x) :
    cov.cov2CurvatureAt A B C x v (w + w')
      = cov.cov2CurvatureAt A B C x v w + cov.cov2CurvatureAt A B C x v w' := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension v
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension w
  obtain ⟨W', hW', hW'w⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension w'
  have hsum : (W + W') x = w + w' := by show W x + W' x = w + w'; rw [hWw, hW'w]
  have e0 : cov.cov2CurvatureAt A B C x (V x) ((W + W') x)
      = cov.cov2Curvature V (W + W') A B C x :=
    cov.cov2CurvatureAt_eq hV (hW.add_section hW') hA hB hC
  have e1 : cov.cov2CurvatureAt A B C x (V x) (W x) = cov.cov2Curvature V W A B C x :=
    cov.cov2CurvatureAt_eq hV hW hA hB hC
  have e2 : cov.cov2CurvatureAt A B C x (V x) (W' x) = cov.cov2Curvature V W' A B C x :=
    cov.cov2CurvatureAt_eq hV hW' hA hB hC
  rw [← hsum, ← hVv, e0, cov.cov2Curvature_add_snd hV hW hW' hA hB hC, ← e1, ← e2,
    hWw, hW'w]

omit [CompleteSpace E] in
theorem cov2CurvatureAt_smul_right
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (c : ℝ) (v w : TangentSpace I x) :
    cov.cov2CurvatureAt A B C x v (c • w) = c • cov.cov2CurvatureAt A B C x v w := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension v
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_three_extension w
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 3 (fun _ : M ↦ c) := contMDiff_const
  have hsm : ((fun _ : M ↦ c) • W) x = c • w := by show c • W x = c • w; rw [hWw]
  have e0 : cov.cov2CurvatureAt A B C x (V x) (((fun _ : M ↦ c) • W) x)
      = cov.cov2Curvature V ((fun _ : M ↦ c) • W) A B C x :=
    cov.cov2CurvatureAt_eq hV (hf.smul_section hW) hA hB hC
  have e1 : cov.cov2CurvatureAt A B C x (V x) (W x) = cov.cov2Curvature V W A B C x :=
    cov.cov2CurvatureAt_eq hV hW hA hB hC
  rw [← hsm, ← hVv, e0, cov.cov2Curvature_smul_snd hf hV hW hA hB hC, ← e1, hWw]

/-- **`∇²Rm` as a continuous bilinear map** `T_xM × T_xM → T_xM`. -/
noncomputable def cov2CurvatureBilin (A B C : Π y : M, TangentSpace I y) (x : M)
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (TangentSpace I x →ₗ[ℝ] TangentSpace I x)
        ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun v w ↦ cov.cov2CurvatureAt A B C x v w)
        (fun v v' w ↦ cov.cov2CurvatureAt_add_left hA hB hC v v' w)
        (fun c v w ↦ cov.cov2CurvatureAt_smul_left hA hB hC c v w)
        (fun v w w' ↦ cov.cov2CurvatureAt_add_right hA hB hC v w w')
        (fun c v w ↦ cov.cov2CurvatureAt_smul_right hA hB hC c v w))

omit [CompleteSpace E] in
@[simp] theorem cov2CurvatureBilin_apply
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    (v w : TangentSpace I x) :
    cov.cov2CurvatureBilin A B C x hA hB hC v w = cov.cov2CurvatureAt A B C x v w := rfl

/-- **`Δ Rm`**, the connection Laplacian of the curvature tensor: the metric trace of
`∇²Rm` in its two derivative slots. The definition uses the standard orthonormal basis of
`T_xM`; `curvatureLaplacian_eq_sum_basis` shows every orthonormal basis gives the same
value. -/
noncomputable def curvatureLaplacian (A B C : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.cov2CurvatureAt A B C x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

omit [CompleteSpace E] in
-- BENCH: curvature-laplacian-frame-independent
/-- **`Δ Rm` is frame-independent**: it is the trace of a bilinear map, and
`OrthonormalBasis.sum_apply_self_eq` traces bilinear maps basis-independently --- into any
normed space, so no pairing against a covector is needed. -/
theorem curvatureLaplacian_eq_sum_basis
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.curvatureLaplacian A B C x = ∑ i, cov.cov2CurvatureAt A B C x (b i) (b i) := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  exact OrthonormalBasis.sum_apply_self_eq _ b (cov.cov2CurvatureBilin A B C x hA hB hC)

omit [CompleteSpace E] in
/-- **`Δ Rm` read off a `C³` frame** whose values at `x` are orthonormal:
`Δ Rm(A,B)C = ∑ᵢ (∇²_{eᵢ,eᵢ}Rm)(A,B)C`. -/
theorem curvatureLaplacian_eq_sum_frame
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hb : ∀ i, fr i x = b i) :
    cov.curvatureLaplacian A B C x = ∑ i, cov.cov2Curvature (fr i) (fr i) A B C x := by
  rw [cov.curvatureLaplacian_eq_sum_basis hA hB hC b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hb i, cov.cov2CurvatureAt_eq (hfr i) (hfr i) hA hB hC]

end Laplacian

end CovariantDerivative
