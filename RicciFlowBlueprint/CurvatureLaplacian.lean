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

end CovariantDerivative
