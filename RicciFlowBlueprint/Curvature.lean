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

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `cov` negates. -/
lemma neg_apply {τ : Π y : M, TangentSpace I y} {y : M} (hτ : MDiffAt (T% τ) y) :
    cov (-τ) y = -cov τ y := by
  have h : (-τ) = (-1 : ℝ) • τ := by funext z; simp
  rw [h, cov.isCovariantDerivativeOn.smul_const (-1 : ℝ) hτ]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `cov` is additive on differences of differentiable sections. -/
lemma sub_apply {σ τ : Π y : M, TangentSpace I y} {y : M}
    (hσ : MDiffAt (T% σ) y) (hτ : MDiffAt (T% τ) y) :
    cov (σ - τ) y = cov σ y - cov τ y := by
  have h : σ - τ = σ + (-τ) := by funext z; simp [sub_eq_add_neg]
  rw [h, cov.isCovariantDerivativeOn.add hσ (mdifferentiableAt_neg_section hτ),
    cov.neg_apply hτ]
  module



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
/-- First Bianchi identity, with the differentiability side conditions taken as explicit
hypotheses. -/
theorem bianchi_first_of_mdiff (hcov : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z))
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x)
    (hZY : MDiffAt (T% (fun y ↦ cov Y y (Z y))) x)
    (hZX : MDiffAt (T% (fun y ↦ cov X y (Z y))) x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x)
    (hXY : MDiffAt (T% (fun y ↦ cov Y y (X y))) x)
    (hYX : MDiffAt (T% (fun y ↦ cov X y (Y y))) x)
    (hbYZ : MDiffAt (T% (mlieBracket I Y Z)) x)
    (hbZX : MDiffAt (T% (mlieBracket I Z X)) x)
    (hbXY : MDiffAt (T% (mlieBracket I X Y)) x)
    (hjac : mlieBracket I X (mlieBracket I Y Z) x + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x = 0) :
    cov.curvature X Y Z x + cov.curvature Y Z X x + cov.curvature Z X Y x = 0 := by
  have htf : ∀ {A B : Π y : M, TangentSpace I y} {y : M},
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      cov B y (A y) - cov A y (B y) = mlieBracket I A B y :=
    (torsion_eq_zero_iff cov).mp hcov
  -- Torsion-freeness as an identity of sections.
  have eYZ : (fun y ↦ cov Z y (Y y)) - (fun y ↦ cov Y y (Z y)) = mlieBracket I Y Z := by
    funext y; exact htf (hY y) (hZ y)
  have eZX : (fun y ↦ cov X y (Z y)) - (fun y ↦ cov Z y (X y)) = mlieBracket I Z X := by
    funext y; exact htf (hZ y) (hX y)
  have eXY : (fun y ↦ cov Y y (X y)) - (fun y ↦ cov X y (Y y)) = mlieBracket I X Y := by
    funext y; exact htf (hX y) (hY y)
  -- Group the cyclic sum by the direction slot.
  have gX : cov (fun y ↦ cov Z y (Y y)) x (X x) - cov (fun y ↦ cov Y y (Z y)) x (X x)
      = cov (mlieBracket I Y Z) x (X x) := by
    rw [← _root_.sub_apply, ← cov.sub_apply hYZ hZY, eYZ]
  have gY : cov (fun y ↦ cov X y (Z y)) x (Y x) - cov (fun y ↦ cov Z y (X y)) x (Y x)
      = cov (mlieBracket I Z X) x (Y x) := by
    rw [← _root_.sub_apply, ← cov.sub_apply hZX hXZ, eZX]
  have gZ : cov (fun y ↦ cov Y y (X y)) x (Z x) - cov (fun y ↦ cov X y (Y y)) x (Z x)
      = cov (mlieBracket I X Y) x (Z x) := by
    rw [← _root_.sub_apply, ← cov.sub_apply hXY hYX, eXY]
  -- Torsion-freeness again, now on the pairs (X, [Y,Z]) and cyclic.
  have tX := htf (hX x) hbYZ
  have tY := htf (hY x) hbZX
  have tZ := htf (hZ x) hbXY
  simp only [curvature]
  linear_combination (norm := module) gX + gY + gZ + tX + tY + tZ + hjac


-- TODO: the clean form of `bianchi_first`, deriving the differentiability side
-- conditions from smoothness of `X`, `Y`, `Z` rather than assuming them. Needs
-- `[ContMDiffCovariantDerivative cov k]` (smoothness of `∇` is a typeclass, not
-- part of `CovariantDerivative`) plus a lemma applying a `C^k` Hom-bundle
-- section to a `C^k` section. Brackets come from
-- `ContDiff.mlieBracket_vectorField`, and Jacobi from
-- `leibniz_identity_mlieBracket_apply` combined with `mlieBracket_swap_apply`.
-- That is bookkeeping, not mathematics: the content is `bianchi_first_of_mdiff`.

-- Sectional curvature needs the metric, so it is stated alongside the
-- Levi-Civita connection once `sectionalCurvature` is ported from the
-- `riemann-curvature` branch.

end CovariantDerivative
