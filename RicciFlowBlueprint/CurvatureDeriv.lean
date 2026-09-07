/-
**`∇R` is tensorial in its direction slot.**

`Bianchi.lean` defines `(∇_X R)(Y,Z)W = ∇_X(R(Y,Z)W) − R(∇_X Y,Z)W − R(Y,∇_X Z)W
− R(Y,Z)(∇_X W)` (`covCurvature`) and proves the second Bianchi identity for it,
but says nothing about how it depends on `X`. It is `C^∞(M)`-linear there, and
the reason is uniform across the four terms: `∇_{fX}` is `f∇_X` on the nose, and
each of the last three feeds that into a slot of `R` in which `R` is already
tensorial. So every term picks up exactly one factor of `f(x)`.

That is what makes the *divergence* `div Rm (Y,Z,W) = ∑ᵢ ⟪(∇_{eᵢ}R)(Y,Z)W, eᵢ⟫`
well-defined — the trace is over the direction slot — and the divergence is what
the contracted second Bianchi identity, and hence `Δ scal`, are about.

The other three slots are not done here, and they are not the same problem.

`Y` and `Z` are tensorial too, but the proof is not a copy of this one: under
`Y ↦ f•Y` the *first* term picks up a Leibniz term, because
`∇_X(f • R(Y,Z)W) = f ∇_X(R(Y,Z)W) + (Xf) R(Y,Z)W`, and it is cancelled by the
matching term from `R(∇_X(f•Y), Z)W`. Applying Leibniz there needs
`y ↦ R(Y,Z)W y` to be a *differentiable section*, which nothing in this project
establishes — `covCurvature` is well defined without it, since `cov` is total.
The missing lemma is smoothness of the curvature section, and it is reachable:
the two `∇∇` terms are `contMDiff_cov_apply` twice, and the bracket term needs
smoothness of `mlieBracket`, which Mathlib has as
`ContMDiffAt.mlieBracket_vectorField` (`Mathlib/Geometry/Manifold/VectorField/
LieBracket.lean`). Expect to spend the regularity budget: `C^{k+2}` fields for a
`C^k` curvature section.

`W` is the analogue of the curvature's third slot and will need the same
frame-and-globalise argument as `CurvaturePointwise.lean`.

Regularity follows `bianchi_second`: `W` is `C³`, `X`, `Y`, `Z` are `C²`, and the
connection is `C²`, so that `∇_X W` is `C²` and can be fed to the third slot.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Bianchi
import RicciFlowBlueprint.CurvaturePointwise

open Bundle VectorField
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]

section Direction

variable {f : M → ℝ} {X Y Z W : Π y : M, TangentSpace I y} {x : M}

private theorem two_ne_zero₃ : (2 : ℕ∞ω) ≠ 0 := by norm_num

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2] in
/-- `∇_{f•X} σ = f • ∇_X σ`, pointwise, by linearity of the direction slot. -/
theorem cov_smul_dir (σ : Π y : M, TangentSpace I y) (f : M → ℝ)
    (X : Π y : M, TangentSpace I y) :
    (fun y ↦ cov σ y ((f • X) y)) = f • (fun y ↦ cov σ y (X y)) := by
  funext y
  show cov σ y (f y • X y) = f y • cov σ y (X y)
  exact map_smul _ _ _

omit [CompleteSpace E] in
-- BENCH: cov-curvature-smul-dir
/-- **`∇R` is `C^∞(M)`-linear in its direction slot**: `(∇_{f•X} R)(Y,Z)W = f(x)·(∇_X R)(Y,Z)W`.
Each of the four terms picks up exactly one factor of `f(x)`: the first by linearity of
`∇` in the direction, the other three because `∇_{f•X}` is `f∇_X` and `R` is tensorial in
the slot it lands in. -/
theorem covCurvature_smul_dir
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvature (f • X) Y Z W x = f x • cov.covCurvature X Y Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hfm : MDiffAt f x := (hf.mdifferentiable two_ne_zero₃) x
  -- the three difference fields `∇_X Y`, `∇_X Z`, `∇_X W`
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY hX1
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hDYm : MDiffAt (T% (fun y ↦ cov Y y (X y))) x := (hDY.mdifferentiable h1) x
  have hDZm : MDiffAt (T% (fun y ↦ cov Z y (X y))) x := (hDZ.mdifferentiable h1) x
  have hYm : MDiffAt (T% Y) x := (hY.mdifferentiable two_ne_zero₃) x
  have hZm : MDiffAt (T% Z) x := (hZ.mdifferentiable two_ne_zero₃) x
  -- the four terms, each with its factor of `f x`
  have e1 : cov (fun y ↦ cov.curvature Y Z W y) x ((f • X) x)
      = f x • cov (fun y ↦ cov.curvature Y Z W y) x (X x) := by
    show cov (fun y ↦ cov.curvature Y Z W y) x (f x • X x) = _
    exact map_smul _ _ _
  have e2 : cov.curvature (fun y ↦ cov Y y ((f • X) y)) Z W x
      = f x • cov.curvature (fun y ↦ cov Y y (X y)) Z W x := by
    rw [cov.cov_smul_dir Y f X]
    exact cov.curvature_smul_left f _ Z W hfm hDYm
      (cov.mdiffAt_cov_apply hW2 hDYm)
  have e3 : cov.curvature Y (fun y ↦ cov Z y ((f • X) y)) W x
      = f x • cov.curvature Y (fun y ↦ cov Z y (X y)) W x := by
    rw [cov.cov_smul_dir Z f X]
    exact cov.curvature_smul_middle f Y _ W hfm hDZm
      (cov.mdiffAt_cov_apply hW2 hDZm)
  have e4 : cov.curvature Y Z (fun y ↦ cov W y ((f • X) y)) x
      = f x • cov.curvature Y Z (fun y ↦ cov W y (X y)) x := by
    rw [cov.cov_smul_dir W f X]
    exact cov.curvature_smul_third hf (hY x) (hZ x) hDW
  simp only [covCurvature, e1, e2, e3, e4]
  module

omit [CompleteSpace E] in
/-- **`∇R` is additive in its direction slot.** -/
theorem covCurvature_add_dir {X' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hX' : CMDiff 2 (T% X')) (hY : CMDiff 2 (T% Y))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    cov.covCurvature (X + X') Y Z W x
      = cov.covCurvature X Y Z W x + cov.covCurvature X' Y Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hX'1 : CMDiff 1 (T% X') := hX'.of_le (by norm_num)
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY hX1
  have hDY' : CMDiff 1 (T% (fun y ↦ cov Y y (X' y))) := cov.contMDiff_cov_apply hY hX'1
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX1
  have hDZ' : CMDiff 1 (T% (fun y ↦ cov Z y (X' y))) := cov.contMDiff_cov_apply hZ hX'1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hDW' : CMDiff 2 (T% (fun y ↦ cov W y (X' y))) := cov.contMDiff_cov_apply hW hX'
  have hYm : MDiffAt (T% Y) x := (hY.mdifferentiable two_ne_zero₃) x
  have hZm : MDiffAt (T% Z) x := (hZ.mdifferentiable two_ne_zero₃) x
  have hsY : (fun y ↦ cov Y y ((X + X') y))
      = (fun y ↦ cov Y y (X y)) + (fun y ↦ cov Y y (X' y)) := by
    funext y; show cov Y y (X y + X' y) = _; exact map_add _ _ _
  have hsZ : (fun y ↦ cov Z y ((X + X') y))
      = (fun y ↦ cov Z y (X y)) + (fun y ↦ cov Z y (X' y)) := by
    funext y; show cov Z y (X y + X' y) = _; exact map_add _ _ _
  have hsW : (fun y ↦ cov W y ((X + X') y))
      = (fun y ↦ cov W y (X y)) + (fun y ↦ cov W y (X' y)) := by
    funext y; show cov W y (X y + X' y) = _; exact map_add _ _ _
  have e1 : cov (fun y ↦ cov.curvature Y Z W y) x ((X + X') x)
      = cov (fun y ↦ cov.curvature Y Z W y) x (X x)
        + cov (fun y ↦ cov.curvature Y Z W y) x (X' x) := by
    show cov (fun y ↦ cov.curvature Y Z W y) x (X x + X' x) = _
    exact map_add _ _ _
  simp only [covCurvature, e1, hsY, hsZ, hsW,
    cov.curvature_add_left hW2 ((hDY.mdifferentiable h1) x) ((hDY'.mdifferentiable h1) x),
    cov.curvature_add_middle hW2 ((hDZ.mdifferentiable h1) x) ((hDZ'.mdifferentiable h1) x),
    cov.curvature_add_right hDW hDW' hYm hZm]
  module

end Direction

end CovariantDerivative
