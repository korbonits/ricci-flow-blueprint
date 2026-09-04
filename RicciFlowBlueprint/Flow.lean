/- Ricci flow: `∂g/∂t = -2 Ric(g t)`, as a predicate on a one-parameter family
   of metrics.

   ## Why the connection is existentially quantified

   Mathlib now constructs a Levi-Civita connection (`leviCivitaConnection`,
   see `LeviCivita.lean`) but does not yet prove it is `C¹`, and `ricci` of a
   connection that is not known to be `C¹` is junk. So "the Ricci curvature
   of `g t`" is still not usable as a function of `g t`, and the flow is
   stated existentially: at each time `t` there is a connection, `C¹`,
   metric-compatible with `g t` and torsion-free (i.e. *a* Levi-Civita
   connection of `g t`), whose Ricci curvature is minus half the time
   derivative of the metric. This is equivalent to the textbook equation, and
   the equivalence is now a theorem rather than a remark:
   `isRicciFlowAt_iff_of_isLeviCivita` trades the existential for *any* `C¹`
   Levi-Civita connection, because all of them have the same Ricci tensor on
   `C²` fields (`ricci_eq_of_isLeviCivita`). Once smoothness of
   `leviCivitaConnection` lands upstream, that lemma applied to it gives the
   function `g ↦ Ric (g)`. Note the quantifier order: `∀ t, ∃ cov` rather than
   `∃ cov : ℝ → _, ∀ t` — these are equivalent by choice since no regularity
   in `t` is demanded of `cov`, and the pointwise form is the one the
   metric-quantification pattern (below) can express.

   ## The metric-quantification pattern, time-dependent version

   See `Hamilton.lean` for the pattern and its two jointly necessary
   conditions: (1) the `RiemannianBundle` instance must be an ambient binder
   where `cov.IsMetricCompatible` is elaborated, and (2) `cov` must be bound by
   an existential. A one-parameter family adds a twist: the compatibility
   condition at time `t` needs the instance *of `g t`*, while the evolution
   equation needs the whole family `g` (the derivative is in the time
   direction). The resolution: the time-slice predicate `IsRicciFlowAt` takes
   the *family* `g` and the time `t` as arguments but elaborates
   `IsMetricCompatible` against the one ambient instance — the evolution
   equation itself mentions `g` only through the structure field
   `(g u).inner`, which needs no instance at all. `IsRicciFlowOn` /
   `IsRicciFlow` then apply the constant under
   `letI := ⟨(g t).toRiemannianMetric⟩` per time slice, exactly as
   `Admits*` do in `Hamilton.lean`. The pattern holds verbatim; nothing new
   was needed.

   ## What the predicate does and does not say

   * `IsRicciFlowAt I M g t` — at time `t` there is a `C¹` Levi-Civita
     connection `cov` of the ambient metric with
     `d/du (g u)(X, Y)|ₜ = -2 Ric_cov(X, Y)` at every point, tested against
     all global `C²` vector fields `X`, `Y`. `HasDerivAt` makes this an
     ordinary real derivative of the scalar function
     `u ↦ (g u).inner x (X x) (Y x)`.
   * The `C¹` hypothesis on `cov` is part of the existential: without it
     `ricci` can silently take its junk value `0` (the first curvature slot
     need not be tensorial) and the equation would degenerate to
     `∂g/∂t = 0`.
   * No joint regularity of `(t, x) ↦ g t x` is imposed beyond existence of
     the pointwise time derivative; that matches the literal PDE and keeps the
     definition orthogonal to the (missing) parabolic theory.
   * `isRicciFlowAt_const_iff` — sanity check: a stationary family is a flow
     at `t` iff it has a Ricci-flat Levi-Civita connection; the nontrivial
     direction is uniqueness of derivatives against `hasDerivAt_const`.
   * `ricciFlow_shortTime_existence` — Hamilton 1982 / DeTurck 1983, as
     `proof_wanted`: on a closed manifold every metric is the initial value of
     a Ricci flow on some `(0, T)`, with the metric coefficients continuous up
     to `t = 0`. Blocked on quasilinear parabolic systems on bundle sections;
     see the survey below.

   ## Where the analytic frontier is

   Everything past the definition is blocked on analysis Mathlib does not
   have. It is recorded here so the dependency graph is honest about where the
   frontier is, not because any of it is close.

   * Short-time existence on a closed manifold (Hamilton 1982; DeTurck 1983)
     needs quasilinear parabolic systems on sections of vector bundles, hence
     Sobolev spaces of bundle sections and elliptic regularity. Mathlib's
     entire PDE surface is `Analysis/Distribution/Sobolev.lean` and
     `Analysis/FunctionalSpaces/SobolevInequality.lean`; none of the above
     exists.
   * Hamilton 1982 (`Hamilton.lean`) additionally needs the tensor maximum
     principle, the three-dimensional pinching estimates, Shi's derivative
     estimates, and convergence of the normalized flow.
   * Now that the Levi-Civita connection exists in Mathlib
     (`LeviCivita.lean`), the function `g ↦ Ric(g)` is definable; DeTurck's
     trick and the curvature evolution equations are the first consumers.

   Mathlib already carries the terminal statement of the road this sits on, in
   `Mathlib/Geometry/Manifold/PoincareConjecture.lean`. -/
import RicciFlowBlueprint.LeviCivita
import Mathlib.Analysis.Calculus.Deriv.Basic
import Batteries.Util.ProofWanted

open Bundle CovariantDerivative
open scoped Manifold ContDiff

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

/-- The Ricci flow equation `∂g/∂t = -2 Ric(g t)` at a single time `t`, elaborated
against the ambient `RiemannianBundle` instance (which `IsRicciFlowOn` and
`IsRicciFlow` instantiate with the metric `g t`). Since Levi-Civita existence is
not available, the connection is bound existentially: there is a `C¹`
torsion-free connection compatible with the ambient metric whose Ricci
curvature is `-½ ∂g/∂t`, tested against all global `C²` vector fields. -/
def IsRicciFlowAt (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (t : ℝ) : Prop :=
  ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
    ContMDiffCovariantDerivative cov 1 ∧ cov.IsMetricCompatible ∧ cov.torsion = 0 ∧
      ∀ (x : M) (X Y : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → CMDiff 2 (T% Y) →
        HasDerivAt (fun u ↦ (g u).inner x (X x) (Y x)) (-2 * cov.ricci X Y x) t

/-- `g` is a Ricci flow on the set `s` of times: at each `t ∈ s`, the tangent
bundle metrized by `g t` satisfies the flow equation. -/
def IsRicciFlowOn (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s,
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    IsRicciFlowAt I M g t

-- BENCH: ricci-flow-def
/-- **Ricci flow**: a one-parameter family of metrics `g` with
`∂g/∂t = -2 Ric(g t)` for all `t`. -/
def IsRicciFlow (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) : Prop :=
  ∀ t : ℝ,
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    IsRicciFlowAt I M g t

theorem isRicciFlow_iff_isRicciFlowOn_univ
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) :
    IsRicciFlow I M g ↔ IsRicciFlowOn I M g Set.univ :=
  ⟨fun h t _ ↦ h t, fun h t ↦ h t (Set.mem_univ t)⟩

section StationaryMetric

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]

-- BENCH: ricci-flow-stationary-ricci-flat
/-- Sanity check for the definition: a stationary family satisfies the flow
equation at `t` iff it has a Ricci-flat (`C¹`, torsion-free, compatible)
connection — `∂g/∂t = 0` forces `Ric = 0` by uniqueness of derivatives, and
conversely. (Both sides keep `cov` bound by the existential; binding it as an
explicit parameter breaks elaboration of `IsMetricCompatible` — condition (2)
of the pattern in `Hamilton.lean`.) -/
theorem isRicciFlowAt_const_iff
    {g₀ : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)} {t : ℝ} :
    IsRicciFlowAt I M (fun _ ↦ g₀) t ↔
      ∃ cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x),
        ContMDiffCovariantDerivative cov 1 ∧ cov.IsMetricCompatible ∧ cov.torsion = 0 ∧
          ∀ (x : M) (X Y : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → CMDiff 2 (T% Y) →
            cov.ricci X Y x = 0 := by
  constructor
  · rintro ⟨cov, hsm, hcompat, htor, heq⟩
    refine ⟨cov, hsm, hcompat, htor, fun x X Y hX hY ↦ ?_⟩
    have h0 : -2 * cov.ricci X Y x = 0 :=
      (heq x X Y hX hY).unique (hasDerivAt_const t _)
    linarith
  · rintro ⟨cov, hsm, hcompat, htor, hflat⟩
    refine ⟨cov, hsm, hcompat, htor, fun x X Y hX hY ↦ ?_⟩
    rw [hflat x X Y hX hY]
    simpa using hasDerivAt_const t (g₀.inner x (X x) (Y x))

/-- The existential in `IsRicciFlowAt` can be discharged by *any* `C¹` Levi-Civita
connection of the ambient metric: the flow equation holds for one iff it holds
for every one, since `C¹` Levi-Civita connections share their Ricci tensor on
`C²` fields (`ricci_eq_of_isLeviCivita`). This is the textbook equation
`∂g/∂t = -2 Ric(g)` with `Ric` computed by a specified connection. -/
theorem isRicciFlowAt_iff_of_isLeviCivita
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)} {t : ℝ}
    {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
    [ContMDiffCovariantDerivative cov 1] (h : cov.IsLeviCivitaConnection) :
    IsRicciFlowAt I M g t ↔
      ∀ (x : M) (X Y : Π y : M, TangentSpace I y), CMDiff 2 (T% X) → CMDiff 2 (T% Y) →
        HasDerivAt (fun u ↦ (g u).inner x (X x) (Y x)) (-2 * cov.ricci X Y x) t := by
  constructor
  · rintro ⟨cov', hsm', hcompat', htor', heq⟩ x X Y hX hY
    have := hsm'
    have h' : cov'.IsLeviCivitaConnection := ⟨hcompat', htor'⟩
    rw [ricci_eq_of_isLeviCivita h h' ((hX.mdifferentiable (by norm_num)) x) hY]
    exact heq x X Y hX hY
  · intro H
    exact ⟨cov, inferInstance, h.isMetricCompatible, h.torsion, H⟩

end StationaryMetric

-- BENCH: ricci-flow-short-time
/-- **Short-time existence for the Ricci flow** (Hamilton 1982; DeTurck 1983):
on a closed manifold, every metric is the initial condition of a Ricci flow on
some interval `(0, T)`, with the metric coefficients continuous up to `t = 0`.

Blocked on quasilinear parabolic systems on sections of vector bundles — see
the frontier survey in the header of this file. Stated with `proof_wanted`: elaborated
and type-checked, no `sorry`, no axiom. -/
proof_wanted ricciFlow_shortTime_existence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [CompactSpace M] [I.Boundaryless]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    (g₀ : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) :
    ∃ (T : ℝ) (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)),
      0 < T ∧ g 0 = g₀ ∧ IsRicciFlowOn I M g (Set.Ioo 0 T) ∧
        ∀ (x : M) (v w : TangentSpace I x),
          ContinuousOn (fun u ↦ (g u).inner x v w) (Set.Ico 0 T)

end RicciFlowBlueprint
