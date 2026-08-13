/- Statement of Hamilton's 1982 theorem.

   Hamilton, "Three-manifolds with positive Ricci curvature",
   J. Differential Geometry 17 (1982), 255-306.

   The theorem is stated, not proved. It is years away: it needs short-time
   existence for a quasilinear parabolic system on sections of a vector bundle,
   Hamilton's tensor maximum principle, the three-dimensional pinching
   estimates, Shi's derivative estimates, and convergence of the normalized
   flow -- none of which Mathlib has.

   The point of writing it down is that until today it could not be *stated*:
   `Ric` and `K` did not exist in any Lean library. -/
import RicciFlowBlueprint.Sectional
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Batteries.Util.ProofWanted

open Bundle CovariantDerivative
open scoped Manifold ContDiff

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- Strictly positive Ricci curvature: `Ric(X,X) > 0` for every `C²` field
non-vanishing at the point. -/
def HasPositiveRicci : Prop :=
  ∀ (x : M) (X : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → X x ≠ 0 →
    0 < cov.ricci X X x

/-- Constant sectional curvature `k`: every 2-plane at every point has `K = k`.
The hypothesis is that `X x`, `Y x` actually span a plane -- the Gram determinant
is non-zero -- since `sectionalCurvature` takes a junk value otherwise. -/
def HasConstantSectionalCurvature (k : ℝ) : Prop :=
  ∀ (x : M) (X Y : Π y : M, TangentSpace I y),
    ‖X x‖ ^ 2 * ‖Y x‖ ^ 2 - ⟪X x, Y x⟫ ^ 2 ≠ 0 →
      Scratch4.sectionalCurvature cov X Y x = k

end RicciFlowBlueprint

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]

/-
## The full statement: blocked, and precisely where

The two predicates above compile and are the substance -- `Ric > 0` and
`K ≡ k` are now expressible, which they were not before today.

Quantifying over *metrics*, which "admits a metric of ..." requires, does not
yet go through. The intended statement is:

    def AdmitsPositiveRicciMetric : Prop :=
      ∃ g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x),
        letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
        ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
          cov.IsMetricCompatible ∧ cov.torsion = 0 ∧ HasPositiveRicci cov

    proof_wanted hamilton_1982 ... [CompactSpace M] [I.Boundaryless]
        (hdim : Module.finrank ℝ E = 3) :
        AdmitsPositiveRicciMetric I M → AdmitsConstantPositiveCurvatureMetric I M

`cov.IsMetricCompatible` fails to elaborate there with an application type
mismatch: `IsMetricCompatible` wants the fiber structures that come from
`InnerProductSpace` (`NormedAddCommGroup.toAddCommGroup`,
`InnerProductSpace.toNormedSpace.toModule`, ...), while a `cov` whose type is
ascribed as `CovariantDerivative I E (fun x ↦ TangentSpace I x)` carries
`instAddCommGroupTangentSpace I` and friends. This is the tangent-bundle
topology diamond that `LeviCivita.lean` warns about, and it bites here because
the metric is installed by `letI` rather than being an ambient instance.

`exists_unique_leviCivita` in `LeviCivita.lean` states the same conjunction
successfully because there the metric is ambient and `cov` is bound by `∃!`,
so the instance arguments are solved together rather than forced by an
ascription.

WHAT IS ACTUALLY MISSING: not mathematics, and not Ricci or sectional
curvature -- those are done. It is the ability to quantify over Riemannian
metrics on a fixed manifold while keeping the fiber instances coherent. That
is the same class of packaging problem as the tensoriality one, one level up:
`RiemannianBundle` is designed for a single ambient metric, and Hamilton's
theorem is inherently a statement about *two different* metrics on one
manifold.

BOTH ESCAPE ROUTES TESTED AND CLOSED (2026-08-13):

* ascribing `cov : CovariantDerivative I E (fun x ↦ TangentSpace I x)` under the
  `letI` -> `IsMetricCompatible` application type mismatch (instance paths differ:
  `instAddCommGroupTangentSpace` vs `NormedAddCommGroup.toAddCommGroup`);
* leaving `cov` unascribed so unification drives it -> `cov`'s type stays a
  metavariable, "Invalid field notation" / "typeclass instance problem is stuck".
  This fails for `cov.IsMetricCompatible` and for `HasPositiveRicci cov`
  independently, so it is the `letI` binding, not either predicate.

Dropping `IsMetricCompatible` would make it compile but would no longer be
Hamilton's theorem -- a torsion-free connection unrelated to the metric says
nothing. A statement that compiles and is wrong is worse than none, so it is
recorded here rather than shipped.
-/

end RicciFlowBlueprint
