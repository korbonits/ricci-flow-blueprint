/- Statement of Hamilton's 1982 theorem.

   Hamilton, "Three-manifolds with positive Ricci curvature",
   J. Differential Geometry 17 (1982), 255-306.

   Stated, not proved -- it needs short-time existence for a quasilinear
   parabolic system on sections of a vector bundle, the tensor maximum
   principle, three-dimensional pinching, Shi's estimates, and convergence of
   the normalized flow, none of which Mathlib has. Written with `proof_wanted`,
   so there is no `sorry` and no added axiom: the statement is elaborated and
   type-checked, nothing more.

   Until 2026-08-13 it could not be *stated*: `Ric` and `K` existed in no Lean
   library. Since the Levi-Civita connection landed in Mathlib (see
   `LeviCivita.lean`), the existentially quantified connection in the
   hypotheses below is known to be well-posed: it exists, and every `C¹`
   choice gives the same `Ric` and `K` on `C²` fields
   (`ricci_eq_of_isLeviCivita`, `sectionalCurvature_eq_of_isLeviCivita`).

   ## The pattern that makes metric quantification work

   "M admits a metric such that ..." must quantify over metrics, but the metric
   reaches `TM` as a typeclass instance via `RiemannianBundle`. Introducing that
   instance inside a term with `letI` and then writing `cov.IsMetricCompatible`
   fails to elaborate -- see the analysis below. Two conditions turn out to be
   jointly necessary:

     1. the `RiemannianBundle` instance must be an ambient *binder*, not
        introduced by `letI`/`haveI` in a term;
     2. `cov` must be bound by the existential, not an explicit parameter or a
        structure field.

   So the predicates `HasPositiveRicciLC` / `HasConstSecLC` are elaborated ONCE
   in that context, and the `Admits*` definitions merely *apply* the resulting
   constants under `letI`. Applying a constant to an instance argument needs no
   re-elaboration of `IsMetricCompatible`, so it goes through.

   The fibre instances are definitionally equal either way -- both

     example (x : M) : (inferInstance : AddCommGroup (TangentSpace I x))
         = instAddCommGroupTangentSpace I x := rfl
     example (x : M) : (inferInstance : TopologicalSpace (TangentSpace I x))
         = instTopologicalSpaceTangentSpace I x := rfl

   succeed, and `#synth AddCommGroup (TangentSpace I x)` returns
   `instAddCommGroupTangentSpace`. `RiemannianBundle`'s no-diamond design works
   as documented; what failed was elaboration over defeq terms, and the pattern
   above sidesteps it rather than fixing it. A cleaner idiom would be welcome. -/
import RicciFlowBlueprint.Sectional
import RicciFlowBlueprint.LeviCivitaSmooth
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
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

/-- The ambient metric has strictly positive Ricci curvature: there is a `C¹`
Levi-Civita connection whose Ricci tensor is positive on every nonzero value of a
`C²` vector field. The `C¹` requirement and the `C²` test fields are not
decoration: `ricci` takes the junk value `0` unless the first curvature slot is
tensorial, which needs both, and by `ricci_eq_of_isLeviCivita` the value is then
the same for every `C¹` Levi-Civita connection — so the existential is a genuine
statement about the metric. -/
def HasPositiveRicciLC (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] : Prop :=
  ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
    ContMDiffCovariantDerivative cov 1 ∧ cov.IsMetricCompatible ∧ cov.torsion = 0 ∧
      ∀ (x : M) (X : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → X x ≠ 0 →
        0 < cov.ricci X X x

/-- The ambient metric has constant sectional curvature `k`: there is a `C¹`
Levi-Civita connection whose sectional curvature is `k` on every pair of `C²`
vector fields that are linearly independent at the point. Restricting to `C²`
fields matters: `curvature X Y Y x` involves `[X, Y]` and `∇_X ∇_Y Y`, which are
junk on fields that are not differentiable at `x`, and an earlier version of this
predicate quantified over all fields and so demanded equalities between junk
values. -/
def HasConstSecLC (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] (k : ℝ) : Prop :=
  ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
    ContMDiffCovariantDerivative cov 1 ∧ cov.IsMetricCompatible ∧ cov.torsion = 0 ∧
      ∀ (x : M) (X Y : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → CMDiff 2 (T% Y) →
        ‖X x‖ ^ 2 * ‖Y x‖ ^ 2 - ⟪X x, Y x⟫ ^ 2 ≠ 0 →
          sectionalCurvature cov X Y x = k

section Canonical

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]

/-- Positive Ricci curvature, tested with the canonical Levi-Civita connection. -/
theorem hasPositiveRicciLC_iff :
    HasPositiveRicciLC I M ↔
      ∀ (x : M) (X : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → X x ≠ 0 →
        0 < (leviCivitaConnection I M).ricci X X x := by
  constructor
  · rintro ⟨cov, hsm, hcompat, htor, hpos⟩ x X hX hx
    have := hsm
    have h' : cov.IsLeviCivitaConnection := ⟨hcompat, htor⟩
    rw [← ricci_eq_of_isLeviCivita h' (isLeviCivitaConnection_leviCivitaConnection I)
      ((hX.mdifferentiable (by norm_num)) x) hX]
    exact hpos x X hX hx
  · intro h
    exact ⟨leviCivitaConnection I M, inferInstance, isMetricCompatible_leviCivitaConnection I,
      torsion_leviCivitaConnection_eq_zero I, h⟩

/-- Constant sectional curvature, tested with the canonical Levi-Civita connection. -/
theorem hasConstSecLC_iff {k : ℝ} :
    HasConstSecLC I M k ↔
      ∀ (x : M) (X Y : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → CMDiff 2 (T% Y) →
        ‖X x‖ ^ 2 * ‖Y x‖ ^ 2 - ⟪X x, Y x⟫ ^ 2 ≠ 0 →
          sectionalCurvature (leviCivitaConnection I M) X Y x = k := by
  constructor
  · rintro ⟨cov, hsm, hcompat, htor, hk⟩ x X Y hX hY hXY
    have := hsm
    have h' : cov.IsLeviCivitaConnection := ⟨hcompat, htor⟩
    rw [← sectionalCurvature_eq_of_isLeviCivita h' (isLeviCivitaConnection_leviCivitaConnection I)
      hX hY]
    exact hk x X Y hX hY hXY
  · intro h
    exact ⟨leviCivitaConnection I M, inferInstance, isMetricCompatible_leviCivitaConnection I,
      torsion_leviCivitaConnection_eq_zero I, h⟩

end Canonical

/-- `M` admits a metric of strictly positive Ricci curvature. -/
def AdmitsPositiveRicciMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] : Prop :=
  ∃ g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x),
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    HasPositiveRicciLC I M

/-- `M` admits a metric of constant positive sectional curvature. -/
def AdmitsConstPositiveSecMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] : Prop :=
  ∃ (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (k : ℝ),
    0 < k ∧
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      HasConstSecLC I M k

/-- `AdmitsPositiveRicciMetric`, with `Ric` a function of the metric: there is a `C²` metric `g`
whose Ricci curvature `ricciOfMetric g` is positive on nonzero values of `C²` fields. -/
theorem admitsPositiveRicciMetric_iff :
    AdmitsPositiveRicciMetric I M ↔
      ∃ g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x),
        ∀ (x : M) (X : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → X x ≠ 0 →
          0 < ricciOfMetric g X X x := by
  unfold AdmitsPositiveRicciMetric
  refine exists_congr fun g ↦ ?_
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact hasPositiveRicciLC_iff

/-- `AdmitsConstPositiveSecMetric`, with `K` a function of the metric. -/
theorem admitsConstPositiveSecMetric_iff :
    AdmitsConstPositiveSecMetric I M ↔
      ∃ (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (k : ℝ), 0 < k ∧
        ∀ (x : M) (X Y : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → CMDiff 2 (T% Y) →
          g.inner x (X x) (X x) * g.inner x (Y x) (Y x) - g.inner x (X x) (Y x) ^ 2 ≠ 0 →
            sectionalCurvatureOfMetric g X Y x = k := by
  unfold AdmitsConstPositiveSecMetric
  refine exists_congr fun g ↦ exists_congr fun k ↦ and_congr_right fun _ ↦ ?_
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [hasConstSecLC_iff]
  refine forall_congr' fun x ↦ forall_congr' fun X ↦ forall_congr' fun Y ↦
    imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ imp_congr_left ?_
  simp only [← real_inner_self_eq_norm_sq]
  exact Iff.rfl

/-- **Hamilton's theorem (1982).** -/
proof_wanted hamilton_1982
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [CompactSpace M] [I.Boundaryless]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    (hdim : Module.finrank ℝ E = 3) :
    AdmitsPositiveRicciMetric I M → AdmitsConstPositiveSecMetric I M

end RicciFlowBlueprint
