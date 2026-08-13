/-
Riemann curvature of a covariant derivative.

Upstream target: `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature.lean`.
A richer version — curvature packaged as a tensor, with first-two-slot
tensoriality — is drafted on the `riemann-curvature` branch of mathlib4; rebase
that before extending this file. What is here is the bare operator, enough to
state the identities the blueprint depends on.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorField.LieBracket

open Bundle VectorField
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- The curvature operator `R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.

Note the nonstandard argument order inherited from `CovariantDerivative`:
`cov σ x (X x)` is `(∇_X σ) x` on paper. -/
noncomputable def curvature (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov (fun y ↦ cov Z y (Y y)) x (X x) - cov (fun y ↦ cov Z y (X y)) x (Y x)
    - cov Z x (mlieBracket I X Y x)

-- BENCH: curvature-antisymm
-- The curvature operator is antisymmetric in its first two arguments:
-- R(X, Y)Z = -R(Y, X)Z.
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem curvature_antisymm (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    cov.curvature X Y Z x = - cov.curvature Y X Z x := by
  simp only [curvature, mlieBracket_swap_apply (I := I) (V := Y) (W := X), map_neg]
  abel

-- BENCH: bianchi-first
-- First Bianchi identity: for a torsion-free connection,
-- R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0.
--
-- The C² hypotheses are not decoration. Both ingredients demand them:
-- `torsion_eq_zero_iff` yields ∇_X Y - ∇_Y X = [X, Y] only for `MDiffAt` fields,
-- and `leibniz_identity_mlieBracket_apply` (Jacobi) wants
-- `CMDiffAt (minSmoothness 𝕜 2)`. Without them the statement is false: `cov`
-- applied to a non-differentiable section is unconstrained.
--
-- Proof sketch. Regroup the cyclic sum using torsion-freeness on each pair,
--   Σ R(X,Y)Z = ∇_X [Y,Z] - ∇_[Y,Z] X + ∇_Y [Z,X] - ∇_[Z,X] Y
--                 + ∇_Z [X,Y] - ∇_[X,Y] Z,
-- apply torsion-freeness once more to each difference to get
-- [X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]], then close with Jacobi. The second
-- application is why C² rather than C¹ is needed: it is applied to the pair
-- (X, [Y,Z]), so the bracket itself must be differentiable.
theorem bianchi_first (hcov : cov.torsion = 0) (X Y Z : Π x : M, TangentSpace I x)
    {x : M}
    (hX : CMDiffAt (minSmoothness ℝ 2) (T% X) x)
    (hY : CMDiffAt (minSmoothness ℝ 2) (T% Y) x)
    (hZ : CMDiffAt (minSmoothness ℝ 2) (T% Z) x) :
    cov.curvature X Y Z x + cov.curvature Y Z X x + cov.curvature Z X Y x = 0 := by
  sorry

-- Sectional curvature needs the metric, so it is stated alongside the
-- Levi-Civita connection once `sectionalCurvature` is ported from the
-- `riemann-curvature` branch.

end CovariantDerivative
