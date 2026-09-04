/-
The Levi-Civita connection.

Mathlib has it as of September 2026:
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`
(mathlib4 PR #36845 — Massot, Rothgang, Macbeth) provides

* `CovariantDerivative.IsLeviCivitaConnection` — torsion-free and compatible;
* `IsLeviCivitaConnection.apply_eq` — the Koszul formula;
* `IsLeviCivitaConnection.uniqueness` — any two Levi-Civita connections agree
  on every vector field *differentiable at the point*;
* `CovariantDerivative.leviCivitaConnection I M` — a construction, by the
  musical isomorphism applied to the Koszul (2,0)-tensor, together with
  `isLeviCivitaConnection_leviCivitaConnection`.

Smoothness of `leviCivitaConnection` is *not* there yet (mathlib says "future
PRs"); that is the one thing still separating the flow definition in
`Flow.lean` from the textbook `∂g/∂t = -2 Ric(g)` with `Ric` a function of `g`.

## What replaced the `∃!`

The statement this file used to carry as its only `sorry`,

    ∃! cov, cov.IsMetricCompatible ∧ cov.torsion = 0,

is not the right statement and was never going to be proved: a
`CovariantDerivative` is unconstrained on sections that are not
differentiable at the point (both `IsCovariantDerivativeOn` laws and the
compatibility/torsion predicates only quantify over differentiable sections),
so a Levi-Civita connection can be altered there and stay Levi-Civita.
Uniqueness holds exactly on differentiable sections — `leviCivita_unique` —
and that is all that any curvature computation needs: `curvature_eq_of_isLeviCivita`
and `ricci_eq_of_isLeviCivita` below show that `C¹` Levi-Civita connections
have the same curvature and Ricci tensor on `C²` fields, which is what makes
the existentially quantified definitions in `Hamilton.lean` and `Flow.lean`
well-posed.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import RicciFlowBlueprint.Sectional

open Bundle CovariantDerivative
open scoped Manifold ContDiff

namespace RicciFlowBlueprint

section ExistenceUniqueness

-- The tangent bundle carries its metric via `RiemannianBundle`, not via a raw
-- `[∀ x, InnerProductSpace ℝ (TangentSpace I x)]` binder: the fibers already
-- have a topology, and the raw binder creates a diamond.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- BENCH: levi-civita-exists
/-- **Existence of the Levi-Civita connection**: there is a torsion-free covariant
derivative on `TM` compatible with the metric. Witness: Mathlib's
`leviCivitaConnection I M`. -/
theorem exists_leviCivita :
    ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
      cov.IsMetricCompatible ∧ cov.torsion = 0 :=
  ⟨leviCivitaConnection I M, isMetricCompatible_leviCivitaConnection I,
    torsion_leviCivitaConnection_eq_zero I⟩

-- BENCH: levi-civita-unique
/-- **Uniqueness of the Levi-Civita connection**, on differentiable sections: two
torsion-free metric-compatible connections agree on every vector field that is
differentiable at the point. (They may differ on non-differentiable sections,
where a `CovariantDerivative` is unconstrained — so this, not `∃!`, is the
fundamental theorem of Riemannian geometry.) -/
theorem leviCivita_unique
    {cov cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
    (h : cov.IsLeviCivitaConnection) (h' : cov'.IsLeviCivitaConnection)
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    cov Y x v = cov' Y x v :=
  IsLeviCivitaConnection.uniqueness I h h' hY v

/-- The two spellings of "Levi-Civita" in this repository agree: the pair
`IsMetricCompatible ∧ torsion = 0` used inside the existentials of
`Hamilton.lean` and `Flow.lean`, and Mathlib's structure. -/
theorem isLeviCivitaConnection_iff
    {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)} :
    cov.IsLeviCivitaConnection ↔ cov.IsMetricCompatible ∧ cov.torsion = 0 :=
  ⟨fun h ↦ ⟨h.isMetricCompatible, h.torsion⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end ExistenceUniqueness

section Curvature

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  {cov cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}

/-- Two Levi-Civita connections, one of them `C¹`, have the same curvature on a
`C²` field `Z` and fields `X`, `Y` differentiable at the point. Only `cov` needs
to be `C¹`: that is what makes `∇_Y Z` differentiable at `x`, so that uniqueness
applies to the outer derivative. -/
theorem curvature_eq_of_isLeviCivita [ContMDiffCovariantDerivative cov 1]
    (h : cov.IsLeviCivitaConnection) (h' : cov'.IsLeviCivitaConnection)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiff 2 (T% Z)) :
    cov.curvature X Y Z x = cov'.curvature X Y Z x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hZ' : ∀ y, MDiffAt (T% Z) y := fun y ↦ (hZ.mdifferentiable h2) y
  have e1 : (fun y ↦ cov Z y (Y y)) = fun y ↦ cov' Z y (Y y) := by
    funext y; exact leviCivita_unique h h' (hZ' y) (Y y)
  have e2 : (fun y ↦ cov Z y (X y)) = fun y ↦ cov' Z y (X y) := by
    funext y; exact leviCivita_unique h h' (hZ' y) (X y)
  simp only [curvature]
  rw [leviCivita_unique h h' (cov.mdiffAt_cov_apply hZ hY) (X x),
    leviCivita_unique h h' (cov.mdiffAt_cov_apply hZ hX) (Y x),
    leviCivita_unique h h' (hZ' x), e1, e2]

-- BENCH: ricci-well-defined
/-- **The Ricci tensor of a metric is well defined**: two `C¹` Levi-Civita
connections have the same Ricci curvature on a `C²` field `Y` and a field `X`
differentiable at the point. Hence the existentially quantified `Ric` in
`Hamilton.lean` and `Flow.lean` does not depend on the choice of connection. -/
theorem ricci_eq_of_isLeviCivita
    [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov' 1]
    (h : cov.IsLeviCivitaConnection) (h' : cov'.IsLeviCivitaConnection)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y)) :
    cov.ricci X Y x = cov'.ricci X Y x := by
  rw [cov.ricci_eq_trace hY x, cov'.ricci_eq_trace hY x]
  congr 2
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend]
  exact curvature_eq_of_isLeviCivita h h' (mdifferentiableAt_extend I E v) hX hY

/-- Two `C¹` Levi-Civita connections have the same sectional curvature on `C²`
fields, so `HasConstSecLC` in `Hamilton.lean` is a statement about the metric. -/
theorem sectionalCurvature_eq_of_isLeviCivita [ContMDiffCovariantDerivative cov 1]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    (h : cov.IsLeviCivitaConnection) (h' : cov'.IsLeviCivitaConnection)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) :
    sectionalCurvature cov X Y x = sectionalCurvature cov' X Y x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  unfold sectionalCurvature
  rw [curvature_eq_of_isLeviCivita h h' ((hX.mdifferentiable h2) x) ((hY.mdifferentiable h2) x) hY]

end Curvature

end RicciFlowBlueprint
