/-
**A lower bound on the scalar curvature is preserved by the Ricci flow.**

This is the first inequality of Hamilton's pinching set `K` (`Pinching.lean`'s `le_scal`,
`IveyConvex.lean`'s first condition), proved here on a closed manifold rather than for the ODE.

**It needs no Uhlenbeck trick**, and that is the point of isolating it. The tensor maximum
principle is applied to a section of a bundle whose fibre metric moves with `t`, which is why
Hamilton's argument has to trivialise that bundle first; the *scalar* equation has no fibre at
all, so the only thing that moves is the Laplacian itself --- and the maximum principle never
looks at the Laplacian except to ask that it be `≥ 0` at a spatial minimum, which holds for
every metric separately. So `MaximumPrinciple.le_of_deriv_ge_at_min` is applied directly, with
the per-time `letI` supplying the metric only inside the proof.

The two inputs are `ScalarFlow.lean`'s `∂ₜ R = Δ R + 2|Ric|²` and the fact that `|Ric|²_g` is a
sum of squares (`metricTraceE_comp_sharpE_self_nonneg`), so the reaction term never pushes `R`
down. The comparison function is the constant `C`, i.e. `F = 0` in the maximum principle.
-/
import RicciFlowBlueprint.ScalarFlow
import RicciFlowBlueprint.ManifoldMaximumPrinciple

open Set Bundle CovariantDerivative
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [CompactSpace M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] [I.Boundaryless] [CompactSpace M] in
-- BENCH: ricci-form-of-metric-symm
/-- **The Ricci form of a metric is symmetric.** `RicciSymm.lean` proves this for any metric
torsion-free connection; the canonical Levi-Civita connection of `g` is one. -/
theorem ricciFormOfMetric_symm
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M) (v w : E) :
    ricciFormOfMetric g x v w = ricciFormOfMetric g x w v := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (leviCivitaConnection I M).ricciForm_symm
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
    (torsion_leviCivitaConnection_eq_zero I) v w

-- BENCH: scalar-lower-bound-preserved
/-- **A lower bound on the scalar curvature is preserved by the Ricci flow.** If `R ≥ C`
everywhere at time `0`, then `R ≥ C` everywhere for as long as the flow is given.

The hypothesis `heq` is the evolution equation `∂ₜ R = Δ R + 2|Ric|²`, in the form
`ScalarFlow.lean` delivers it, asked for at each time separately --- the Laplacian and the
norm are both taken with respect to `g t`, so both move with `t`. The maximum principle does
not mind: it uses the Laplacian only through `laplacianFun_nonneg_of_isLocalMin`, which holds
for each metric on its own. The reaction term is nonnegative
(`metricTraceE_comp_sharpE_self_nonneg`, `Ric` being symmetric), so the comparison ODE is
`φ' = 0` and the constant `C` is a subsolution. -/
theorem scalarCurvatureOfMetricAt_ge_of_hasDerivAt
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
    {R' : ℝ → M → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hcont : Continuous fun p : ℝ × M ↦ scalarCurvatureOfMetricAt (g p.1) p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivAt (fun s ↦ scalarCurvatureOfMetricAt (g s) x) (R' t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x,
      ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x)
    (heq : ∀ t ∈ Icc 0 T, ∀ x,
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      R' t x = (leviCivitaOfMetric (g t)).laplacianFun
          (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x
        + 2 * metricTraceE (g t) x
            (ricciFormOfMetric (g t) x ∘L sharpE (g t) x (ricciFormOfMetric (g t) x)))
    (h0 : ∀ x, C ≤ scalarCurvatureOfMetricAt (g 0) x) :
    ∀ t ∈ Icc 0 T, ∀ x, C ≤ scalarCurvatureOfMetricAt (g t) x := by
  refine MaximumPrinciple.le_of_deriv_ge_at_min (F := fun _ ↦ (0 : ℝ)) (φ := fun _ ↦ C)
    (K := 0) hT hcont hut (LipschitzWith.const 0) ?_ (fun t _ ↦ hasDerivAt_const t C) h0
  intro t ht x₀ hmin
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  have hlap : 0 ≤ (leviCivitaOfMetric (g t)).laplacianFun
      (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x₀ :=
    laplacianFun_nonneg_of_isLocalMin _ (hreg t ht x₀) (Filter.Eventually.of_forall hmin)
  have hric : 0 ≤ metricTraceE (g t) x₀
      (ricciFormOfMetric (g t) x₀ ∘L sharpE (g t) x₀ (ricciFormOfMetric (g t) x₀)) :=
    metricTraceE_comp_sharpE_self_nonneg (g t) x₀ (ricciFormOfMetric (g t) x₀)
      (ricciFormOfMetric_symm (g t) x₀)
  rw [heq t ht x₀]
  linarith

/-- The right-hand side of the scalar evolution equation, `Δ_{g t} R + 2|Ric_{g t}|²_{g t}`, as a
function of `t` and `x`. Both the Laplacian and the norm move with `t`, so the metric's
`RiemannianBundle` instance is introduced inside the definition, as `scalarCurvatureOfMetricAt`
does. -/
noncomputable def scalarFlowRHS
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (t : ℝ) (x : M) :
    ℝ :=
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  (leviCivitaOfMetric (g t)).laplacianFun (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x
    + 2 * metricTraceE (g t) x
        (ricciFormOfMetric (g t) x ∘L sharpE (g t) x (ricciFormOfMetric (g t) x))

-- BENCH: scalar-lower-bound-preserved-flow
/-- **A lower bound on the scalar curvature is preserved by the Ricci flow**, with the evolution
equation as the single hypothesis --- and that hypothesis is exactly what `ScalarFlow.lean`'s
`hasDerivAt_scalarCurvatureOfMetricAt_eq_laplacian_add` concludes, so the statement is not
vacuous. -/
theorem scalarCurvatureOfMetricAt_ge_of_hasDerivAt_scalarFlowRHS
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
    {T C : ℝ} (hT : 0 ≤ T)
    (hcont : Continuous fun p : ℝ × M ↦ scalarCurvatureOfMetricAt (g p.1) p.2)
    (hev : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivAt (fun s ↦ scalarCurvatureOfMetricAt (g s) x) (scalarFlowRHS g t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x,
      ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x)
    (h0 : ∀ x, C ≤ scalarCurvatureOfMetricAt (g 0) x) :
    ∀ t ∈ Icc 0 T, ∀ x, C ≤ scalarCurvatureOfMetricAt (g t) x :=
  scalarCurvatureOfMetricAt_ge_of_hasDerivAt hT hcont hev hreg (fun _ _ _ ↦ rfl) h0

omit [CompleteSpace E] [I.Boundaryless] [CompactSpace M] in
-- BENCH: scalar-flow-rhs-bridge
/-- **`scalarFlowRHS` is exactly what `ScalarFlow.lean` produces.** The two sides are the same
term up to the `letI` that introduces the metric's instance, so the bridge is the identity ---
but stating it is what makes "the hypothesis of the preservation theorem is a theorem" a
checked claim rather than a remark. -/
theorem hasDerivAt_scalarFlowRHS_of_hasDerivAt_scalarCurvatureAt
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)} {t₀ : ℝ} {x : M}
    (h : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      HasDerivAt (fun t ↦ scalarCurvatureOfMetricAt (g t) x)
        ((leviCivitaOfMetric (g t₀)).laplacianFun
            (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) x
          + 2 * metricTraceE (I := I) (M := M) (g t₀) x
              (ricciFormOfMetric (g t₀) x ∘L
                sharpE (I := I) (M := M) (g t₀) x (ricciFormOfMetric (g t₀) x))) t₀) :
    HasDerivAt (fun t ↦ scalarCurvatureOfMetricAt (g t) x) (scalarFlowRHS g t₀ x) t₀ := h

end RicciFlowBlueprint
