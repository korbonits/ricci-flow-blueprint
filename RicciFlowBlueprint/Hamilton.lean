/- Statement of Hamilton's 1982 theorem.

   Hamilton, "Three-manifolds with positive Ricci curvature",
   J. Differential Geometry 17 (1982), 255-306.

   Stated, not proved -- it needs short-time existence for a quasilinear
   parabolic system on sections of a vector bundle, the tensor maximum
   principle, three-dimensional pinching, Shi's estimates, and convergence of
   the normalized flow, none of which Mathlib has. Written with `proof_wanted`,
   so there is no `sorry` and no added axiom: the statement is elaborated and
   type-checked, nothing more.

   Until today it could not be *stated*: `Ric` and `K` existed in no Lean
   library.

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
import Batteries.Util.ProofWanted
open Bundle CovariantDerivative
open scoped Manifold ContDiff
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

def HasPositiveRicciLC (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] : Prop :=
  ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
    cov.IsMetricCompatible ∧ cov.torsion = 0 ∧
      ∀ (x : M) (X : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → X x ≠ 0 →
        0 < cov.ricci X X x

def HasConstSecLC (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] (k : ℝ) : Prop :=
  ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
    cov.IsMetricCompatible ∧ cov.torsion = 0 ∧
      ∀ (x : M) (X Y : Π y : M, TangentSpace I y),
        ‖X x‖ ^ 2 * ‖Y x‖ ^ 2 - ⟪X x, Y x⟫ ^ 2 ≠ 0 →
          Scratch4.sectionalCurvature cov X Y x = k

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
