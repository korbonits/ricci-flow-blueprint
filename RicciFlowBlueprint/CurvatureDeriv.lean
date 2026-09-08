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
That lemma is `contMDiff_curvature`, proved below: the two `∇∇` terms are
`contMDiff_cov_apply` twice and the bracket term is the same fed Mathlib's
`ContMDiffAt.mlieBracket_vectorField`. The regularity is what one expects —
`C³` fields for a `C¹` curvature section — so the `Y`/`Z` slots will cost one
more derivative than the direction slot did.

`W` is the analogue of the curvature's third slot and will need the same
frame-and-globalise argument as `CurvaturePointwise.lean`.

Regularity follows `bianchi_second`: `W` is `C³`, `X`, `Y`, `Z` are `C²`, and the
connection is `C²`, so that `∇_X W` is `C²` and can be fed to the third slot.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Bianchi
import RicciFlowBlueprint.CurvaturePointwise

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]

section Smoothness

omit [FiniteDimensional ℝ E] in
-- BENCH: contMDiff-curvature-section
/-- **The curvature of `C³` fields is a `C¹` section.** This is the lemma the `Y` and `Z`
slots of `∇R` need: without it there is no Leibniz rule for `∇_X(f • R(Y,Z)W)`.

`R(Y,Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W`, so the two iterated terms are
`contMDiff_cov_apply` twice and the bracket term is `contMDiff_cov_apply` fed the smoothness
of `mlieBracket`, which Mathlib supplies. The regularity is what one expects: two derivatives
are spent on `W`, one on the directions. -/
theorem contMDiff_curvature {Y Z W : Π y : M, TangentSpace I y}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    CMDiff 1 (T% (fun y ↦ cov.curvature Y Z W y)) := by
  have hW3 : CMDiff ((2 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hW
  have hW2 : CMDiff ((1 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hW.of_le (by norm_num)
  have hY1 : CMDiff 1 (T% Y) := hY.of_le (by norm_num)
  have hZ1 : CMDiff 1 (T% Z) := hZ.of_le (by norm_num)
  -- `∇_Z W` and `∇_Y W` are `C²`
  have hZW : CMDiff ((1 : ℕ∞ω) + 1) (T% (fun u ↦ cov W u (Z u))) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]
    exact cov.contMDiff_cov_apply hW3 hZ
  have hYW : CMDiff ((1 : ℕ∞ω) + 1) (T% (fun u ↦ cov W u (Y u))) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]
    exact cov.contMDiff_cov_apply hW3 hY
  -- the three terms
  have t1 : CMDiff 1 (T% (fun y ↦ cov (fun u ↦ cov W u (Z u)) y (Y y))) :=
    cov.contMDiff_cov_apply hZW hY1
  have t2 : CMDiff 1 (T% (fun y ↦ cov (fun u ↦ cov W u (Y u)) y (Z y))) :=
    cov.contMDiff_cov_apply hYW hZ1
  have hb : CMDiff 1 (T% (mlieBracket I Y Z)) := fun y ↦
    (hY y).mlieBracket_vectorField (n := 2) (m := 1) (hZ y) (by norm_num)
  have t3 : CMDiff 1 (T% (fun y ↦ cov W y (mlieBracket I Y Z y))) :=
    cov.contMDiff_cov_apply hW2 hb
  -- `T%` wraps the section, so `rw` cannot see the definition of `curvature`; `show` can
  show CMDiff 1 (T% (((fun y ↦ cov (fun u ↦ cov W u (Z u)) y (Y y))
    - (fun y ↦ cov (fun u ↦ cov W u (Y u)) y (Z y)))
    - (fun y ↦ cov W y (mlieBracket I Y Z y))))
  exact (t1.sub_section t2).sub_section t3

omit [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
-- BENCH: contMDiff-curvature-section-two
/-- **The curvature of `C⁴` fields is a `C²` section** --- `contMDiff_curvature` one level
up, which is what differentiating `∇Rm` needs. The level is hard-coded rather than
parametrised because Mathlib's `ContMDiffAt.mlieBracket_vectorField` indexes smoothness by
`ℕ∞` while `ContMDiff` indexes it by `ℕ∞ω`, and carrying a variable level across that
boundary costs more cast bookkeeping than the twin proof does. -/
theorem contMDiff_curvature_two [ContMDiffCovariantDerivative cov 3]
    {Y Z W : Π y : M, TangentSpace I y}
    (hY : CMDiff 3 (T% Y)) (hZ : CMDiff 3 (T% Z)) (hW : CMDiff 4 (T% W)) :
    CMDiff 2 (T% (fun y ↦ cov.curvature Y Z W y)) := by
  have hW4 : CMDiff ((3 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hW
  have hW3 : CMDiff ((2 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hW.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  -- `∇_Z W` and `∇_Y W` are `C³`
  have hZW : CMDiff ((2 : ℕ∞ω) + 1) (T% (fun u ↦ cov W u (Z u))) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]
    exact cov.contMDiff_cov_apply hW4 hZ
  have hYW : CMDiff ((2 : ℕ∞ω) + 1) (T% (fun u ↦ cov W u (Y u))) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]
    exact cov.contMDiff_cov_apply hW4 hY
  -- the three terms
  have t1 : CMDiff 2 (T% (fun y ↦ cov (fun u ↦ cov W u (Z u)) y (Y y))) :=
    cov.contMDiff_cov_apply hZW hY2
  have t2 : CMDiff 2 (T% (fun y ↦ cov (fun u ↦ cov W u (Y u)) y (Z y))) :=
    cov.contMDiff_cov_apply hYW hZ2
  have hb : CMDiff 2 (T% (mlieBracket I Y Z)) := fun y ↦
    (hY y).mlieBracket_vectorField (n := 3) (m := 2) (hZ y) (by norm_num)
  have t3 : CMDiff 2 (T% (fun y ↦ cov W y (mlieBracket I Y Z y))) :=
    cov.contMDiff_cov_apply hW3 hb
  show CMDiff 2 (T% (((fun y ↦ cov (fun u ↦ cov W u (Z u)) y (Y y))
    - (fun y ↦ cov (fun u ↦ cov W u (Y u)) y (Z y)))
    - (fun y ↦ cov W y (mlieBracket I Y Z y))))
  exact (t1.sub_section t2).sub_section t3

omit [FiniteDimensional ℝ E] in
-- BENCH: contMDiff-cov-curvature-section
/-- **`∇Rm` of `C³`/`C⁴` fields is a `C¹` section.** This is what differentiating `∇Rm`
again needs — the first step towards `Δ Rm`. Each of the four terms costs its own
regularity: the leading one wants the curvature section itself to be `C²`
(`contMDiff_curvature_two`), and the last wants `∇_X W` to be `C³`, which is where `W`'s
fourth derivative goes. -/
theorem contMDiff_covCurvature [ContMDiffCovariantDerivative cov 3]
    {X Y Z W : Π y : M, TangentSpace I y}
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y)) (hZ : CMDiff 3 (T% Z))
    (hW : CMDiff 4 (T% W)) :
    CMDiff 1 (T% (fun y ↦ cov.covCurvature X Y Z W y)) := by
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  have hW3 : CMDiff 3 (T% W) := hW.of_le (by norm_num)
  have hY3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Y) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hY
  have hZ3 : CMDiff ((2 : ℕ∞ω) + 1) (T% Z) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hZ
  have hW4 : CMDiff ((3 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((3 : ℕ∞ω) + 1) = 4 by norm_num]; exact hW
  have hcurv : CMDiff ((1 : ℕ∞ω) + 1) (T% (fun y ↦ cov.curvature Y Z W y)) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]
    exact cov.contMDiff_curvature_two hY hZ hW
  -- the four terms
  have t1 : CMDiff 1 (T% (fun y ↦ cov (fun u ↦ cov.curvature Y Z W u) y (X y))) :=
    cov.contMDiff_cov_apply hcurv hX1
  have hDY : CMDiff 2 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY3 hX2
  have hDZ : CMDiff 2 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ3 hX2
  have hDW : CMDiff 3 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW4 hX
  have t2 : CMDiff 1 (T% (fun y ↦ cov.curvature (fun u ↦ cov Y u (X u)) Z W y)) :=
    cov.contMDiff_curvature hDY hZ2 hW3
  have t3 : CMDiff 1 (T% (fun y ↦ cov.curvature Y (fun u ↦ cov Z u (X u)) W y)) :=
    cov.contMDiff_curvature hY2 hDZ hW3
  have t4 : CMDiff 1 (T% (fun y ↦ cov.curvature Y Z (fun u ↦ cov W u (X u)) y)) :=
    cov.contMDiff_curvature hY2 hZ2 hDW
  show CMDiff 1 (T% ((((fun y ↦ cov (fun u ↦ cov.curvature Y Z W u) y (X y))
    - (fun y ↦ cov.curvature (fun u ↦ cov Y u (X u)) Z W y))
    - (fun y ↦ cov.curvature Y (fun u ↦ cov Z u (X u)) W y))
    - (fun y ↦ cov.curvature Y Z (fun u ↦ cov W u (X u)) y)))
  exact ((t1.sub_section t2).sub_section t3).sub_section t4

end Smoothness

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

omit [CompleteSpace E] in
-- BENCH: cov-curvature-smul-snd
/-- **`∇R` is `C^∞(M)`-linear in its second slot**: `(∇_X R)(f•Y, Z)W = f(x)·(∇_X R)(Y,Z)W`.

Unlike the direction slot this is *not* four independent rescalings. The first term picks up
a Leibniz term, `∇_X(f · R(Y,Z)W) = f ∇_X(R(Y,Z)W) + (Xf) R(Y,Z)W`, and the second picks up
the matching one from `∇_X(f•Y) = f ∇_X Y + (Xf) Y`; they cancel. Applying Leibniz at all is
what `contMDiff_curvature` is for. -/
theorem covCurvature_smul_snd
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X (f • Y) Z W x = f x • cov.covCurvature X Y Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hfm : ∀ y, MDiffAt f y := hf.mdifferentiable two_ne_zero₃
  have hYm : ∀ y, MDiffAt (T% Y) y := hY.mdifferentiable two_ne_zero₃
  have hYW : ∀ y, MDiffAt (T% (fun u ↦ cov W u (Y u))) y := fun y ↦
    cov.mdiffAt_cov_apply hW2 (hYm y)
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY hX1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hDYm : MDiffAt (T% (fun y ↦ cov Y y (X y))) x := (hDY.mdifferentiable h1) x
  have hcs : MDiffAt (T% (fun y ↦ cov.curvature Y Z W y)) x :=
    ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1) x
  have hXf : MDiffAt (fun y ↦ d% f y (X y)) x :=
    (RicciFlowBlueprint.contMDiffAt_mvfderiv_apply (hf x) (hX1 x)
      (by norm_num)).mdifferentiableAt h1
  -- term 1: the curvature section rescales, then Leibniz
  have e1 : (fun y ↦ cov.curvature (f • Y) Z W y) = f • (fun y ↦ cov.curvature Y Z W y) := by
    funext y
    exact cov.curvature_smul_left f Y Z W (hfm y) (hYm y) (hYW y)
  have t1 : cov (fun y ↦ cov.curvature (f • Y) Z W y) x (X x)
      = f x • cov (fun y ↦ cov.curvature Y Z W y) x (X x)
        + (d% f x (X x)) • cov.curvature Y Z W x := by
    rw [e1, cov.isCovariantDerivativeOn.leibniz hcs (hfm x)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  -- term 2: `∇_X(f•Y) = f ∇_X Y + (Xf) Y`, and the Leibniz term reappears
  have e2 : (fun y ↦ cov (f • Y) y (X y))
      = f • (fun y ↦ cov Y y (X y)) + ((fun y ↦ d% f y (X y)) • Y) := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (hYm y) (hfm y)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have t2 : cov.curvature (fun y ↦ cov (f • Y) y (X y)) Z W x
      = f x • cov.curvature (fun y ↦ cov Y y (X y)) Z W x
        + (d% f x (X x)) • cov.curvature Y Z W x := by
    rw [e2, cov.curvature_add_left hW2 ((hfm x).smul_section hDYm) (hXf.smul_section (hYm x)),
      cov.curvature_smul_left f _ Z W (hfm x) hDYm (cov.mdiffAt_cov_apply hW2 hDYm),
      cov.curvature_smul_left _ Y Z W hXf (hYm x) (hYW x)]
  have t3 : cov.curvature (f • Y) (fun y ↦ cov Z y (X y)) W x
      = f x • cov.curvature Y (fun y ↦ cov Z y (X y)) W x :=
    cov.curvature_smul_left f Y _ W (hfm x) (hYm x) (hYW x)
  have t4 : cov.curvature (f • Y) Z (fun y ↦ cov W y (X y)) x
      = f x • cov.curvature Y Z _ x :=
    cov.curvature_smul_left f Y Z _ (hfm x) (hYm x) (cov.mdiffAt_cov_apply hDW (hYm x))
  simp only [covCurvature, t1, t2, t3, t4]
  module

omit [CompleteSpace E] in
-- BENCH: cov-curvature-antisymm
/-- **`∇R` inherits the antisymmetry of `R` in the two curvature slots**:
`(∇_X R)(Y,Z)W = -(∇_X R)(Z,Y)W`. Every term of `covCurvature` flips sign — the first
because `∇` negates a differentiable section (`neg_apply`, which is where
`contMDiff_curvature` is needed), the other three by `curvature_antisymm`.

Halves the remaining work: whatever is proved about the `Y` slot transfers to `Z`. -/
theorem covCurvature_antisymm (X : Π y : M, TangentSpace I y)
    {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X Y Z W x = -cov.covCurvature X Z Y W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hc : MDiffAt (T% (fun y ↦ cov.curvature Y Z W y)) x :=
    ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1) x
  have hneg : (fun y ↦ cov.curvature Z Y W y) = -(fun y ↦ cov.curvature Y Z W y) := by
    funext y
    exact cov.curvature_antisymm Z Y W y
  simp only [covCurvature, hneg, cov.neg_apply hc, _root_.neg_apply,
    cov.curvature_antisymm (fun y ↦ cov Z y (X y)) Y W x,
    cov.curvature_antisymm Z (fun y ↦ cov Y y (X y)) W x,
    cov.curvature_antisymm Z Y (fun y ↦ cov W y (X y)) x]
  module

omit [CompleteSpace E] in
-- BENCH: cov-curvature-add-snd
/-- **`∇R` is additive in its second slot.** No Leibniz term here: `∇_X(Y+Y')` splits with
nothing left over. -/
theorem covCurvature_add_snd {Y' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y'))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X (Y + Y') Z W x
      = cov.covCurvature X Y Z W x + cov.covCurvature X Y' Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hYm : ∀ y, MDiffAt (T% Y) y := hY.mdifferentiable two_ne_zero₃
  have hY'm : ∀ y, MDiffAt (T% Y') y := hY'.mdifferentiable two_ne_zero₃
  have hXm : MDiffAt (T% X) x := (hX.mdifferentiable two_ne_zero₃) x
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hDYm : MDiffAt (T% (fun y ↦ cov Y y (X y))) x := cov.mdiffAt_cov_apply hY hXm
  have hDY'm : MDiffAt (T% (fun y ↦ cov Y' y (X y))) x := cov.mdiffAt_cov_apply hY' hXm
  have hcs : MDiffAt (T% (fun y ↦ cov.curvature Y Z W y)) x :=
    ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1) x
  have hcs' : MDiffAt (T% (fun y ↦ cov.curvature Y' Z W y)) x :=
    ((cov.contMDiff_curvature hY' hZ hW).mdifferentiable h1) x
  have e1 : (fun y ↦ cov.curvature (Y + Y') Z W y)
      = (fun y ↦ cov.curvature Y Z W y) + (fun y ↦ cov.curvature Y' Z W y) := by
    funext y
    exact cov.curvature_add_left hW2 (hYm y) (hY'm y)
  have e2 : (fun y ↦ cov (Y + Y') y (X y))
      = (fun y ↦ cov Y y (X y)) + (fun y ↦ cov Y' y (X y)) := by
    funext y
    rw [cov.isCovariantDerivativeOn.add (hYm y) (hY'm y)]
    rfl
  simp only [covCurvature, e1, e2, cov.isCovariantDerivativeOn.add hcs hcs', add_apply,
    cov.curvature_add_left hW2 hDYm hDY'm,
    cov.curvature_add_left hW2 (hYm x) (hY'm x),
    cov.curvature_add_left hDW (hYm x) (hY'm x)]
  module

omit [CompleteSpace E] in
-- BENCH: cov-curvature-smul-thd
/-- **`∇R` is `C^∞(M)`-linear in its third slot** — free from the second, by
`covCurvature_antisymm`. -/
theorem covCurvature_smul_thd
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X Y (f • Z) W x = f x • cov.covCurvature X Y Z W x := by
  have hfZ : CMDiff 2 (T% (f • Z)) := hf.smul_section hZ
  rw [cov.covCurvature_antisymm X hY hfZ hW,
    cov.covCurvature_smul_snd hf hX hZ hY hW,
    cov.covCurvature_antisymm X hZ hY hW]
  module

omit [CompleteSpace E] in
/-- **`∇R` is additive in its third slot** — free from the second, by
`covCurvature_antisymm`. -/
theorem covCurvature_add_thd {Z' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hZ' : CMDiff 2 (T% Z')) (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X Y (Z + Z') W x
      = cov.covCurvature X Y Z W x + cov.covCurvature X Y Z' W x := by
  have hZZ' : CMDiff 2 (T% (Z + Z')) := hZ.add_section hZ'
  rw [cov.covCurvature_antisymm X hY hZZ' hW,
    cov.covCurvature_add_snd hX hZ hZ' hY hW,
    cov.covCurvature_antisymm X hZ hY hW,
    cov.covCurvature_antisymm X hZ' hY hW]
  module

omit [CompleteSpace E] in
-- BENCH: cov-curvature-smul-fth
/-- **`∇R` is `C^∞(M)`-linear in its fourth slot**: `(∇_X R)(Y,Z)(f•W) = f(x)·(∇_X R)(Y,Z)W`.

Like the second slot and unlike the direction, this is a cancellation rather than four
independent rescalings. `R(Y,Z)(f•W) = f·R(Y,Z)W` as *sections*, so the leading
`∇_X` produces a Leibniz term `(Xf)·R(Y,Z)W`; the last term produces the matching one,
because `∇_X(f•W) = f·∇_X W + (Xf)·W` and `R` is tensorial in the slot that lands in.

`f` is asked for one derivative more than elsewhere, and that is not slack: the second of
those Leibniz terms is `R(Y,Z)((Xf)•W)`, and tensoriality in the third slot needs its
coefficient `Xf` to be `C²`, which costs `f ∈ C³`. -/
theorem covCurvature_smul_fth
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X Y Z (f • W) x = f x • cov.covCurvature X Y Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f := hf.of_le (by norm_num)
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hY1 : CMDiff 1 (T% Y) := hY.of_le (by norm_num)
  have hZ1 : CMDiff 1 (T% Z) := hZ.of_le (by norm_num)
  have hfm : ∀ y, MDiffAt f y := hf2.mdifferentiable two_ne_zero₃
  have hWm : ∀ y, MDiffAt (T% W) y := hW2.mdifferentiable two_ne_zero₃
  have hYm : MDiffAt (T% Y) x := (hY1.mdifferentiable h1) x
  have hZm : MDiffAt (T% Z) x := (hZ1.mdifferentiable h1) x
  -- `Xf` is `C²` here, one better than in the other slots: this is what `f ∈ C³` buys
  have hg : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun y ↦ d% f y (X y)) := fun y ↦
    RicciFlowBlueprint.contMDiffAt_mvfderiv_apply (hf y) (hX y) (by norm_num)
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY hX1
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hcs : MDiffAt (T% (fun y ↦ cov.curvature Y Z W y)) x :=
    ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1) x
  have e1 : (fun y ↦ cov.curvature Y Z (f • W) y) = f • (fun y ↦ cov.curvature Y Z W y) := by
    funext y
    exact cov.curvature_smul_third hf2 (hY y) (hZ y) hW2
  have t1 : cov (fun y ↦ cov.curvature Y Z (f • W) y) x (X x)
      = f x • cov (fun y ↦ cov.curvature Y Z W y) x (X x)
        + (d% f x (X x)) • cov.curvature Y Z W x := by
    rw [e1, cov.isCovariantDerivativeOn.leibniz hcs (hfm x)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have t2 : cov.curvature (fun y ↦ cov Y y (X y)) Z (f • W) x
      = f x • cov.curvature (fun y ↦ cov Y y (X y)) Z W x :=
    cov.curvature_smul_third' hf2 (hDY x) (hZ1 x) hW2
  have t3 : cov.curvature Y (fun y ↦ cov Z y (X y)) (f • W) x
      = f x • cov.curvature Y (fun y ↦ cov Z y (X y)) W x :=
    cov.curvature_smul_third' hf2 (hY1 x) (hDZ x) hW2
  have e2 : (fun y ↦ cov (f • W) y (X y))
      = f • (fun y ↦ cov W y (X y)) + ((fun y ↦ d% f y (X y)) • W) := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (hWm y) (hfm y)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have t4 : cov.curvature Y Z (fun y ↦ cov (f • W) y (X y)) x
      = f x • cov.curvature Y Z (fun y ↦ cov W y (X y)) x
        + (d% f x (X x)) • cov.curvature Y Z W x := by
    rw [e2, cov.curvature_add_right (hf2.smul_section hDW) (hg.smul_section hW2) hYm hZm,
      cov.curvature_smul_third' hf2 (hY1 x) (hZ1 x) hDW,
      cov.curvature_smul_third' hg (hY1 x) (hZ1 x) hW2]
  simp only [covCurvature, t1, t2, t3, t4]
  module

omit [CompleteSpace E] in
-- BENCH: cov-curvature-add-fth
/-- **`∇R` is additive in its fourth slot.** -/
theorem covCurvature_add_fth {W' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) (hW' : CMDiff 3 (T% W')) :
    cov.covCurvature X Y Z (W + W') x
      = cov.covCurvature X Y Z W x + cov.covCurvature X Y Z W' x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hW'2 : CMDiff 2 (T% W') := hW'.of_le (by norm_num)
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hY1 : CMDiff 1 (T% Y) := hY.of_le (by norm_num)
  have hZ1 : CMDiff 1 (T% Z) := hZ.of_le (by norm_num)
  have hWm : ∀ y, MDiffAt (T% W) y := hW2.mdifferentiable two_ne_zero₃
  have hW'm : ∀ y, MDiffAt (T% W') y := hW'2.mdifferentiable two_ne_zero₃
  have hYm : MDiffAt (T% Y) x := (hY1.mdifferentiable h1) x
  have hZm : MDiffAt (T% Z) x := (hZ1.mdifferentiable h1) x
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY hX1
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hDW' : CMDiff 2 (T% (fun y ↦ cov W' y (X y))) := cov.contMDiff_cov_apply hW' hX
  have hcs : MDiffAt (T% (fun y ↦ cov.curvature Y Z W y)) x :=
    ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1) x
  have hcs' : MDiffAt (T% (fun y ↦ cov.curvature Y Z W' y)) x :=
    ((cov.contMDiff_curvature hY hZ hW').mdifferentiable h1) x
  have e1 : (fun y ↦ cov.curvature Y Z (W + W') y)
      = (fun y ↦ cov.curvature Y Z W y) + (fun y ↦ cov.curvature Y Z W' y) := by
    funext y
    exact cov.curvature_add_right hW2 hW'2 (hY1.mdifferentiable h1 y) (hZ1.mdifferentiable h1 y)
  have t1 : cov (fun y ↦ cov.curvature Y Z (W + W') y) x (X x)
      = cov (fun y ↦ cov.curvature Y Z W y) x (X x)
        + cov (fun y ↦ cov.curvature Y Z W' y) x (X x) := by
    rw [e1, cov.isCovariantDerivativeOn.add hcs hcs']
    simp only [add_apply]
  have e2 : (fun y ↦ cov (W + W') y (X y))
      = (fun y ↦ cov W y (X y)) + (fun y ↦ cov W' y (X y)) := by
    funext y
    rw [cov.isCovariantDerivativeOn.add (hWm y) (hW'm y)]
    simp only [add_apply]
    rfl
  have t4 : cov.curvature Y Z (fun y ↦ cov (W + W') y (X y)) x
      = cov.curvature Y Z (fun y ↦ cov W y (X y)) x
        + cov.curvature Y Z (fun y ↦ cov W' y (X y)) x := by
    rw [e2, cov.curvature_add_right hDW hDW' hYm hZm]
  simp only [covCurvature, t1, t4,
    cov.curvature_add_right hW2 hW'2 ((hDY.mdifferentiable h1) x) hZm,
    cov.curvature_add_right hW2 hW'2 hYm ((hDZ.mdifferentiable h1) x)]
  module

end Direction

section Pointwise

variable {X Y Z W : Π y : M, TangentSpace I y} {x : M}
variable [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] in
-- BENCH: cov-curvature-congr-dir
/-- **`(∇_X Rm)(Y,Z)W` at `x` depends only on `X x`.** No new frame argument: each of the
four terms is separately pointwise in `X`. The first is a continuous linear map evaluated
at `X x`; the next two are `Rm` in a slot where it is tensorial, applied to `∇_X Y` and
`∇_X Z`, whose values at `x` are `∇_{X x} Y` and `∇_{X x} Z`; the last is `Rm`'s third
slot, applied to `∇_X W`, and that is Lemma `curvature_congr_third`.

Together with tensoriality in the direction slot this is what makes the trace
`div Rm(Y,Z,W) = ∑ᵢ ⟪(∇_{eᵢ}Rm)(Y,Z)W, eᵢ⟫` an honest endomorphism trace. -/
theorem covCurvature_congr_dir {X X' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hX' : CMDiff 2 (T% X'))
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (hval : X x = X' x) :
    cov.covCurvature X Y Z W x = cov.covCurvature X' Y Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hX'1 : CMDiff 1 (T% X') := hX'.of_le (by norm_num)
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) := cov.contMDiff_cov_apply hY hX1
  have hDY' : CMDiff 1 (T% (fun y ↦ cov Y y (X' y))) := cov.contMDiff_cov_apply hY hX'1
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX1
  have hDZ' : CMDiff 1 (T% (fun y ↦ cov Z y (X' y))) := cov.contMDiff_cov_apply hZ hX'1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hDW' : CMDiff 2 (T% (fun y ↦ cov W y (X' y))) := cov.contMDiff_cov_apply hW hX'
  have vY : (fun y ↦ cov Y y (X y)) x = (fun y ↦ cov Y y (X' y)) x := by
    show cov Y x (X x) = cov Y x (X' x); rw [hval]
  have vZ : (fun y ↦ cov Z y (X y)) x = (fun y ↦ cov Z y (X' y)) x := by
    show cov Z x (X x) = cov Z x (X' x); rw [hval]
  have vW : (fun y ↦ cov W y (X y)) x = (fun y ↦ cov W y (X' y)) x := by
    show cov W x (X x) = cov W x (X' x); rw [hval]
  have e1 : cov (fun y ↦ cov.curvature Y Z W y) x (X x)
      = cov (fun y ↦ cov.curvature Y Z W y) x (X' x) := by rw [hval]
  have e2 := (cov.tensorialAt_curvature_fst (V := Z) hW2 x).pointwise
    ((hDY.mdifferentiable h1) x) ((hDY'.mdifferentiable h1) x) vY
  have e3 := (cov.tensorialAt_curvature_snd (V := Y) hW2 x).pointwise
    ((hDZ.mdifferentiable h1) x) ((hDZ'.mdifferentiable h1) x) vZ
  have e4 := cov.curvature_congr_third (hY x) (hZ x) hDW hDW' vW
  simp only [covCurvature, e1, e2, e3, e4]

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- `∇Rm` kills the zero field in its second slot. -/
theorem covCurvature_zero_snd (hX : CMDiff 2 (T% X)) (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X 0 Z W x = 0 := by
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hz0 : cov (0 : Π y : M, TangentSpace I y) = 0 := cov.zero
  have hzsec : (fun y ↦ cov.curvature (0 : Π y : M, TangentSpace I y) Z W y)
      = (0 : Π y : M, TangentSpace I y) :=
    funext fun y ↦ (cov.tensorialAt_curvature_fst (V := Z) hW2 y).zero
  have z1 : cov (fun y ↦ cov.curvature (0 : Π y : M, TangentSpace I y) Z W y) x (X x)
      = 0 := by rw [hzsec, hz0]; simp
  have z2 : cov.curvature (fun y ↦ cov (0 : Π y : M, TangentSpace I y) y (X y)) Z W x
      = 0 := by
    have hzD : (fun y ↦ cov (0 : Π y : M, TangentSpace I y) y (X y))
        = (0 : Π y : M, TangentSpace I y) := by funext y; rw [hz0]; simp
    rw [hzD]
    exact (cov.tensorialAt_curvature_fst (V := Z) hW2 x).zero
  have z3 : cov.curvature (0 : Π y : M, TangentSpace I y)
      (fun y ↦ cov Z y (X y)) W x = 0 :=
    (cov.tensorialAt_curvature_fst (V := fun y ↦ cov Z y (X y)) hW2 x).zero
  have z4 : cov.curvature (0 : Π y : M, TangentSpace I y) Z
      (fun y ↦ cov W y (X y)) x = 0 :=
    (cov.tensorialAt_curvature_fst (V := Z) (Z := fun y ↦ cov W y (X y)) hDW x).zero
  show cov (fun y ↦ cov.curvature (0 : Π y : M, TangentSpace I y) Z W y) x (X x)
      - cov.curvature (fun y ↦ cov (0 : Π y : M, TangentSpace I y) y (X y)) Z W x
      - cov.curvature (0 : Π y : M, TangentSpace I y) (fun y ↦ cov Z y (X y)) W x
      - cov.curvature (0 : Π y : M, TangentSpace I y) Z (fun y ↦ cov W y (X y)) x = 0
  rw [z1, z2, z3, z4]
  module

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **The second slot of `∇Rm` applied to a finite `C²` combination `∑ gᵢ • Aᵢ`.** -/
theorem covCurvature_sum_smul_snd {ι : Type*} {s : Finset ι} {g : ι → M → ℝ}
    {A : ι → Π y : M, TangentSpace I y}
    (hg : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) 2 (g i)) (hA : ∀ i ∈ s, CMDiff 2 (T% (A i)))
    (hX : CMDiff 2 (T% X)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X (fun y ↦ ∑ i ∈ s, g i y • A i y) Z W x
      = ∑ i ∈ s, g i x • cov.covCurvature X (A i) Z W x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y ↦ ∑ i ∈ (∅ : Finset ι), g i y • A i y)
          = (0 : Π y : M, TangentSpace I y) := by funext y; simp
      rw [hz, cov.covCurvature_zero_snd hX hW, Finset.sum_empty]
  | insert a t ha ih =>
      have hga : ContMDiff I 𝓘(ℝ, ℝ) 2 (g a) := hg a (Finset.mem_insert_self a t)
      have hAa : CMDiff 2 (T% (A a)) := hA a (Finset.mem_insert_self a t)
      have hgt : ∀ i ∈ t, ContMDiff I 𝓘(ℝ, ℝ) 2 (g i) := fun i hi ↦
        hg i (Finset.mem_insert_of_mem hi)
      have hAt : ∀ i ∈ t, CMDiff 2 (T% (A i)) := fun i hi ↦ hA i (Finset.mem_insert_of_mem hi)
      have hsum : CMDiff 2 (T% (fun y ↦ ∑ i ∈ t, g i y • A i y)) :=
        ContMDiff.sum_section fun i hi ↦ (hgt i hi).smul_section (hAt i hi)
      have hsplit : (fun y ↦ ∑ i ∈ insert a t, g i y • A i y)
          = (g a • A a) + (fun y ↦ ∑ i ∈ t, g i y • A i y) := by
        funext y
        show ∑ i ∈ insert a t, g i y • A i y = g a y • A a y + ∑ i ∈ t, g i y • A i y
        rw [Finset.sum_insert ha]
      rw [hsplit, cov.covCurvature_add_snd hX (hga.smul_section hAa) hsum hZ hW,
        cov.covCurvature_smul_snd hga hX hAa hZ hW, ih hgt hAt, Finset.sum_insert ha]

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇Rm` is local in its second slot.** Only the leading term needs an argument: the
other three are `Rm` in its first slot, which is tensorial and hence pointwise. -/
theorem covCurvature_congr_snd_of_eventuallyEq {Y' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y'))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) (h : Y =ᶠ[𝓝 x] Y') :
    cov.covCurvature X Y Z W x = cov.covCurvature X Y' Z W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hYm : ∀ y, MDiffAt (T% Y) y := hY.mdifferentiable h2
  have hY'm : ∀ y, MDiffAt (T% Y') y := hY'.mdifferentiable h2
  obtain ⟨U, hUeq, hUopen, hxU⟩ := eventually_nhds_iff.mp h
  -- the curvature sections agree near `x`, slotwise
  have hcs : (fun y ↦ cov.curvature Y Z W y) =ᶠ[𝓝 x] fun y ↦ cov.curvature Y' Z W y :=
    eventually_nhds_iff.mpr ⟨U, fun y hy ↦
      (cov.tensorialAt_curvature_fst (V := Z) hW2 y).pointwise (hYm y) (hY'm y) (hUeq y hy),
      hUopen, hxU⟩
  -- `cov Y x = cov Y' x`, so the three `∇_X` fields have equal values at `x`
  have hcovY : cov Y x = cov Y' x :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq (hYm x) (hY'm x) Filter.univ_mem h
  have hDY : (fun y ↦ cov Y y (X y)) x = (fun y ↦ cov Y' y (X y)) x := by
    show cov Y x (X x) = cov Y' x (X x); rw [hcovY]
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX1
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have e1 : cov (fun y ↦ cov.curvature Y Z W y) x (X x)
      = cov (fun y ↦ cov.curvature Y' Z W y) x (X x) := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1 x)
      ((cov.contMDiff_curvature hY' hZ hW).mdifferentiable h1 x) Filter.univ_mem hcs]
  have e2 := (cov.tensorialAt_curvature_fst (V := Z) hW2 x).pointwise
    ((cov.contMDiff_cov_apply hY hX1).mdifferentiable h1 x)
    ((cov.contMDiff_cov_apply hY' hX1).mdifferentiable h1 x) hDY
  have e3 := (cov.tensorialAt_curvature_fst (V := fun y ↦ cov Z y (X y)) hW2 x).pointwise
    (hYm x) (hY'm x) (hUeq x hxU)
  have e4 := (cov.tensorialAt_curvature_fst (V := Z)
    (Z := fun y ↦ cov W y (X y)) hDW x).pointwise (hYm x) (hY'm x) (hUeq x hxU)
  simp only [covCurvature, e1, e2, e3, e4]

omit [CompleteSpace E] in
-- BENCH: cov-curvature-congr-snd
/-- **`(∇_X Rm)(Y,Z)W` at `x` depends only on `Y x`.** Expand `Y` in a local frame,
globalise the frame fields and the coefficients, and use tensoriality in the second slot ---
the same argument as `curvature_congr_third`, one level up. -/
theorem covCurvature_congr_snd {Y' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y'))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) (hval : Y x = Y' x) :
    cov.covCurvature X Y Z W x = cov.covCurvature X Y' Z W x := by
  classical
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  set e := trivializationAt E (TangentSpace I (M := M)) x with he
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hu : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hxe
  set b := Module.finBasis ℝ E with hb
  obtain ⟨fr, hs, hfrsm⟩ : ∃ fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      IsOrthonormalFrameOn I E 2 fr e.baseSet ∧ ∀ i, CMDiff[e.baseSet] 2 (T% (fr i)) :=
    ⟨_, b.orthonormalFrame_isOrthonormalFrameOn (IB := I) (n := 2) e,
      fun i ↦ b.contMDiffOn_orthonormalFrame_baseSet e i⟩
  have hframe : ∀ i, ∃ Ei : Π y : M, TangentSpace I y, CMDiff 2 (T% Ei) ∧
      Ei =ᶠ[𝓝 x] fr i := by
    intro i
    obtain ⟨Ei, hEi, hEieq⟩ := RicciFlowBlueprint.exists_contMDiff_eventuallyEq (n := 2) hu
      (hfrsm i)
    exact ⟨Ei, by simpa using hEi, hEieq⟩
  choose Ei hEi hEieq using hframe
  have hcoeff : ∀ (V : Π y : M, TangentSpace I y), CMDiff 2 (T% V) → ∀ i,
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 2 g ∧
        g =ᶠ[𝓝 x] (LinearMap.piApply (hs.coeff i) V) := by
    intro V hV i
    obtain ⟨g, hg, hgeq⟩ := RicciFlowBlueprint.exists_contMDiff_eventuallyEq_fun (n := 2) hu
      (hs.contMDiffOn_coeff hV.contMDiffOn i)
    exact ⟨g, by simpa using hg, hgeq⟩
  have key : ∀ (V : Π y : M, TangentSpace I y) (hV : CMDiff 2 (T% V)),
      cov.covCurvature X V Z W x
        = ∑ i, hs.coeff i x (V x) • cov.covCurvature X (Ei i) Z W x := by
    intro V hV
    choose g hg hgeq using hcoeff V hV
    have hsum : CMDiff 2 (T% (fun y ↦ ∑ i, g i y • Ei i y)) :=
      ContMDiff.sum_section fun i _ ↦ (hg i).smul_section (hEi i)
    have heq : V =ᶠ[𝓝 x] fun y ↦ ∑ i, g i y • Ei i y := by
      have hall : ∀ᶠ y in 𝓝 x, ∀ i, g i y = hs.coeff i y (V y) ∧ Ei i y = fr i y :=
        Filter.eventually_all.mpr fun i ↦ (hgeq i).and (hEieq i)
      filter_upwards [hs.toIsLocalFrameOn.eventually_eq_sum_coeff_smul V hu, hall] with y hy hy'
      rw [hy]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [(hy' i).1, (hy' i).2]
    rw [cov.covCurvature_congr_snd_of_eventuallyEq hX hV hsum hZ hW heq,
      cov.covCurvature_sum_smul_snd (fun i _ ↦ hg i) (fun i _ ↦ hEi i) hX hZ hW]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hgeq i).eq_of_nhds]
    rfl
  rw [key Y hY, key Y' hY']
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [hs.toIsLocalFrameOn.coeff_congr hval i]

omit [CompleteSpace E] in
/-- **`(∇_X Rm)(Y,Z)W` at `x` depends only on `Z x`** --- free from the second slot, by
`covCurvature_antisymm`. -/
theorem covCurvature_congr_thd {Z' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hZ' : CMDiff 2 (T% Z')) (hW : CMDiff 3 (T% W)) (hval : Z x = Z' x) :
    cov.covCurvature X Y Z W x = cov.covCurvature X Y Z' W x := by
  rw [cov.covCurvature_antisymm X hY hZ hW, cov.covCurvature_antisymm X hY hZ' hW,
    cov.covCurvature_congr_snd hX hZ hZ' hY hW hval]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2] in
/-- `∇Rm` kills the zero field in its fourth slot. -/
theorem covCurvature_zero_fth : cov.covCurvature X Y Z 0 x = 0 := by
  have hz0 : cov (0 : Π y : M, TangentSpace I y) = 0 := cov.zero
  have hzsec : (fun y ↦ cov.curvature Y Z (0 : Π y : M, TangentSpace I y) y)
      = (0 : Π y : M, TangentSpace I y) := funext fun _ ↦ cov.curvature_zero_right
  have hzD : (fun y ↦ cov (0 : Π y : M, TangentSpace I y) y (X y))
      = (0 : Π y : M, TangentSpace I y) := by funext y; rw [hz0]; simp
  have z1 : cov (fun y ↦ cov.curvature Y Z (0 : Π y : M, TangentSpace I y) y) x (X x)
      = 0 := by rw [hzsec, hz0]; simp
  have z4 : cov.curvature Y Z (fun y ↦ cov (0 : Π y : M, TangentSpace I y) y (X y)) x
      = 0 := by rw [hzD]; exact cov.curvature_zero_right
  show cov (fun y ↦ cov.curvature Y Z (0 : Π y : M, TangentSpace I y) y) x (X x)
      - cov.curvature (fun y ↦ cov Y y (X y)) Z (0 : Π y : M, TangentSpace I y) x
      - cov.curvature Y (fun y ↦ cov Z y (X y)) (0 : Π y : M, TangentSpace I y) x
      - cov.curvature Y Z (fun y ↦ cov (0 : Π y : M, TangentSpace I y) y (X y)) x = 0
  rw [z1, z4, cov.curvature_zero_right, cov.curvature_zero_right]
  module

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **The fourth slot of `∇Rm` applied to a finite `C³` combination `∑ gᵢ • Cᵢ`.** The
coefficients are asked for `C³`, as `covCurvature_smul_fth` asks. -/
theorem covCurvature_sum_smul_fth {ι : Type*} {s : Finset ι} {g : ι → M → ℝ}
    {C : ι → Π y : M, TangentSpace I y}
    (hg : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) 3 (g i)) (hC : ∀ i ∈ s, CMDiff 3 (T% (C i)))
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.covCurvature X Y Z (fun y ↦ ∑ i ∈ s, g i y • C i y) x
      = ∑ i ∈ s, g i x • cov.covCurvature X Y Z (C i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y ↦ ∑ i ∈ (∅ : Finset ι), g i y • C i y)
          = (0 : Π y : M, TangentSpace I y) := by funext y; simp
      rw [hz, cov.covCurvature_zero_fth, Finset.sum_empty]
  | insert a t ha ih =>
      have hga : ContMDiff I 𝓘(ℝ, ℝ) 3 (g a) := hg a (Finset.mem_insert_self a t)
      have hCa : CMDiff 3 (T% (C a)) := hC a (Finset.mem_insert_self a t)
      have hgt : ∀ i ∈ t, ContMDiff I 𝓘(ℝ, ℝ) 3 (g i) := fun i hi ↦
        hg i (Finset.mem_insert_of_mem hi)
      have hCt : ∀ i ∈ t, CMDiff 3 (T% (C i)) := fun i hi ↦ hC i (Finset.mem_insert_of_mem hi)
      have hsum : CMDiff 3 (T% (fun y ↦ ∑ i ∈ t, g i y • C i y)) :=
        ContMDiff.sum_section fun i hi ↦ (hgt i hi).smul_section (hCt i hi)
      have hsplit : (fun y ↦ ∑ i ∈ insert a t, g i y • C i y)
          = (g a • C a) + (fun y ↦ ∑ i ∈ t, g i y • C i y) := by
        funext y
        show ∑ i ∈ insert a t, g i y • C i y = g a y • C a y + ∑ i ∈ t, g i y • C i y
        rw [Finset.sum_insert ha]
      rw [hsplit, cov.covCurvature_add_fth hX hY hZ (hga.smul_section hCa) hsum,
        cov.covCurvature_smul_fth hga hX hY hZ hCa, ih hgt hCt, Finset.sum_insert ha]

omit [CompleteSpace E] [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇Rm` is local in its fourth slot.** Every term is `Rm` in its third slot, which is
local (`curvature_congr_third_of_eventuallyEq`); the leading one needs the curvature
sections to agree near `x`, which is the same fact applied at each nearby point. -/
theorem covCurvature_congr_fth_of_eventuallyEq {W' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) (hW' : CMDiff 3 (T% W')) (h : W =ᶠ[𝓝 x] W') :
    cov.covCurvature X Y Z W x = cov.covCurvature X Y Z W' x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hW'2 : CMDiff 2 (T% W') := hW'.of_le (by norm_num)
  have hX1 : CMDiff 1 (T% X) := hX.of_le (by norm_num)
  have hYm : ∀ y, MDiffAt (T% Y) y := hY.mdifferentiable h2
  have hZm : ∀ y, MDiffAt (T% Z) y := hZ.mdifferentiable h2
  have hWm : ∀ y, MDiffAt (T% W) y := hW2.mdifferentiable h2
  have hW'm : ∀ y, MDiffAt (T% W') y := hW'2.mdifferentiable h2
  obtain ⟨U, hUeq, hUopen, hxU⟩ := eventually_nhds_iff.mp h
  have hnear : ∀ y ∈ U, W =ᶠ[𝓝 y] W' := fun y hy ↦
    eventually_nhds_iff.mpr ⟨U, hUeq, hUopen, hy⟩
  have hcs : (fun y ↦ cov.curvature Y Z W y) =ᶠ[𝓝 x] fun y ↦ cov.curvature Y Z W' y :=
    eventually_nhds_iff.mpr ⟨U, fun y hy ↦ cov.curvature_congr_third_of_eventuallyEq
      hW2 hW'2 (hYm y) (hZm y) (hnear y hy), hUopen, hxU⟩
  have hcovW : ∀ y ∈ U, cov W y = cov W' y := fun y hy ↦
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq (hWm y) (hW'm y) Filter.univ_mem
      (hnear y hy)
  have hDW : (fun y ↦ cov W y (X y)) =ᶠ[𝓝 x] fun y ↦ cov W' y (X y) :=
    eventually_nhds_iff.mpr ⟨U, fun y hy ↦ by
      show cov W y (X y) = cov W' y (X y)
      rw [hcovW y hy], hUopen, hxU⟩
  have e1 : cov (fun y ↦ cov.curvature Y Z W y) x (X x)
      = cov (fun y ↦ cov.curvature Y Z W' y) x (X x) := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((cov.contMDiff_curvature hY hZ hW).mdifferentiable h1 x)
      ((cov.contMDiff_curvature hY hZ hW').mdifferentiable h1 x) Filter.univ_mem hcs]
  have e2 := cov.curvature_congr_third_of_eventuallyEq (X := fun y ↦ cov Y y (X y)) (Y := Z)
    hW2 hW'2 ((cov.contMDiff_cov_apply hY hX1).mdifferentiable h1 x) (hZm x) h
  have e3 := cov.curvature_congr_third_of_eventuallyEq (X := Y)
    (Y := fun y ↦ cov Z y (X y)) hW2 hW'2 (hYm x)
    ((cov.contMDiff_cov_apply hZ hX1).mdifferentiable h1 x) h
  have e4 := cov.curvature_congr_third_of_eventuallyEq (X := Y) (Y := Z)
    (cov.contMDiff_cov_apply hW hX) (cov.contMDiff_cov_apply hW' hX) (hYm x) (hZm x) hDW
  simp only [covCurvature, e1, e2, e3, e4]

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
-- BENCH: cov-curvature-congr-fth
/-- **`(∇_X Rm)(Y,Z)W` at `x` depends only on `W x`.** The frame argument again, now at
`C³`: `covCurvature_smul_fth` asks its coefficient for three derivatives, so the frame
fields and the coefficient functions have to be globalised at that level. -/
theorem covCurvature_congr_fth
    [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
    {W' : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) (hW' : CMDiff 3 (T% W')) (hval : W x = W' x) :
    cov.covCurvature X Y Z W x = cov.covCurvature X Y Z W' x := by
  classical
  have h3 : (3 : ℕ∞ω) ≠ 0 := by norm_num
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
      cov.covCurvature X Y Z V x
        = ∑ i, hs.coeff i x (V x) • cov.covCurvature X Y Z (Ei i) x := by
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
    rw [cov.covCurvature_congr_fth_of_eventuallyEq hX hY hZ hV hsum heq,
      cov.covCurvature_sum_smul_fth (fun i _ ↦ hg i) (fun i _ ↦ hEi i) hX hY hZ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hgeq i).eq_of_nhds]
    rfl
  rw [key W hW, key W' hW']
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [hs.toIsLocalFrameOn.coeff_congr hval i]

end Pointwise

end CovariantDerivative
