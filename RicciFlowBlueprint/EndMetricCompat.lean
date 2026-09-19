/-
**The induced connection on `End(TM)` is metric for the Hilbert–Schmidt form.**

`HomBundle.lean` builds the connection, `EndBundleMetric.lean` the fibre metric; this file
says they agree, which is what `BundleBochner.lean` and `BundleMaximumPrinciple.lean` require
of the pair. With it, `End(TM)` is the first bundle in this development other than `TM` itself
carrying a *compatible* connection and metric — the general `Bundle*` layer's first real
instantiation.

**The proof is `TraceCov.lean`'s, with one new ingredient.** Expand `⟨A,B⟩` over a local
orthonormal frame of `TM`, differentiate each term by metric compatibility downstairs, and
substitute
`∇_X(A e_i) = (∇_X A)(e_i) + A(∇_X e_i)` — which is exactly `endCov_apply`, the definition of
`∇A` rearranged. Four groups of terms result. Two are the Hilbert–Schmidt forms of `∇_X A` and
`∇_X B` read off the same frame. The other two are the corrections, and they cancel for the
reason the metric trace commutes with `∇`: the frame is **not parallel**, so
`⟪∇_X e_i, e_j⟫` survives, but those coefficients are antisymmetric
(`inner_cov_antisymm`) while `⟪A v, B w⟫ + ⟪A w, B v⟫` is symmetric, so
`sum_bilin_of_antisymm` kills them. Nothing here asks the frame to be parallel and nothing
constructs one.

`mvfderiv_hsFibre_eq` is the frame-free form. `isMetricCompatible_endTangentCov` then packages
it as Mathlib's predicate on the type synonym `EndTangent`, against an **ambient
`RiemannianBundle` binder** whose inner product is `hsFibre` — the only shape
`IsMetricCompatible` elaborates in, per `CLAUDE.md`. `isMetricCompatible_endTangentCov_hs`
instantiates that at the metric actually built, which is the falsification check.

Gotchas: `MDifferentiableAt.inner_bundle'` lives in `Bochner.lean` and needs its explicit
name, dot notation resolving through `ChartedSpace.LiftPropWithinAt`; `mvfderiv_inner_eq`
returns a statement full of beta-redexes that `rw` cannot match, so restate it with an
ascribed `have … := h`; the bilinear form fed to `sum_bilin_of_antisymm` must be *declared* at
the `E` type, so introduce it by an ascribed existential (`set` drops the expected type); and
`isMetricCompatible_iff` wants `[IsContMDiffRiemannianBundle I 1 (E →L[ℝ] E) (EndTangent I)]`,
which has to be carried as a binder alongside the abstract `RiemannianBundle`.
-/
import RicciFlowBlueprint.EndBundleMetric
import RicciFlowBlueprint.Bochner

open Bundle CovariantDerivative Manifold
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace RicciFlowBlueprint

section Compat

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

set_option maxSynthPendingDepth 4

omit [CompleteSpace E] in
/-- **The Leibniz rule for the Hilbert–Schmidt form**, read off a local orthonormal frame. -/
theorem mvfderiv_hsFibre_eq_of_frame
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {A B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {X : Π y : M, TangentSpace I y} {x : M}
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hX : MDiffAt (T% X) x)
    (hA : IsMDiffHomAt (I := I) E E A x) (hB : IsMDiffHomAt (I := I) E E B x) :
    mvfderiv I (fun y ↦ hsFibre (I := I) y (A y) (B y)) x (X x)
      = hsFibre (I := I) x (endCov cov A x (X x)) (B x)
        + hsFibre (I := I) x (A x) (endCov cov B x (X x)) := by
  classical
  obtain ⟨b, hb⟩ := CovariantDerivative.exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  have hfr : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦
    (hs.toIsLocalFrameOn.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero
  have hAfr : ∀ i, MDiffAt (T% (fun y ↦ A y (fr i y))) x := fun i ↦ hA _ (hfr i)
  have hBfr : ∀ i, MDiffAt (T% (fun y ↦ B y (fr i y))) x := fun i ↦ hB _ (hfr i)
  have hconst : ∀ i j, (fun y ↦ ⟪fr i y, fr j y⟫) =ᶠ[𝓝 x] fun _ ↦ ⟪fr i x, fr j x⟫ := by
    intro i j
    filter_upwards [hu.mem_nhds hx] with y hy
    rw [orthonormal_iff_ite.mp (hs.orthonormal hy) i j,
      orthonormal_iff_ite.mp (hs.orthonormal hx) i j]
  -- the cross terms, with the bilinear form declared at the `E` type
  obtain ⟨Bform, hBform⟩ : ∃ Bform : E →L[ℝ] E →L[ℝ] ℝ,
      ∀ v w : TangentSpace I x, Bform v w = ⟪A x v, B x w⟫ :=
    ⟨((((innerSL ℝ).comp (A x)).flip.comp (B x)).flip :
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ), fun _ _ ↦ rfl⟩
  have hD : ∀ i j, ⟪cov (fr i) x (X x), b j⟫ = -⟪cov (fr j) x (X x), b i⟫ := by
    intro i j
    rw [hb i, hb j]
    exact cov.inner_cov_antisymm hcov hfr hconst i j
  have hcross : ∑ i, (⟪A x (cov (fr i) x (X x)), B x (fr i x)⟫
      + ⟪A x (fr i x), B x (cov (fr i) x (X x))⟫) = 0 := by
    have h0 := sum_bilin_of_antisymm b Bform (fun i ↦ cov (fr i) x (X x)) hD
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hBform, hBform, hb i]
  -- the Leibniz rule for `A` on the frame
  have hLeibA : ∀ i, cov (fun y ↦ A y (fr i y)) x (X x)
      = endCov cov A x (X x) (fr i x) + A x (cov (fr i) x (X x)) := by
    intro i
    rw [endCov_apply hA hX (hfr i)]
    abel
  have hLeibB : ∀ i, cov (fun y ↦ B y (fr i y)) x (X x)
      = endCov cov B x (X x) (fr i x) + B x (cov (fr i) x (X x)) := by
    intro i
    rw [endCov_apply hB hX (hfr i)]
    abel
  -- differentiate the frame sum
  have heq : (fun y ↦ hsFibre (I := I) y (A y) (B y))
      =ᶠ[𝓝 x] fun y ↦ ∑ i, ⟪A y (fr i y), B y (fr i y)⟫ := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact hsFibre_eq_sum_frame hs hy (A y) (B y)
  rw [heq.mvfderiv_eq,
    mvfderiv_fun_sum (fun i _ ↦ MDifferentiableAt.inner_bundle' (hAfr i) (hBfr i)), _root_.sum_apply]
  have hterm : ∀ i, mvfderiv I (fun y ↦ ⟪A y (fr i y), B y (fr i y)⟫) x (X x)
      = (⟪endCov cov A x (X x) (fr i x), B x (fr i x)⟫
          + ⟪A x (fr i x), endCov cov B x (X x) (fr i x)⟫)
        + (⟪A x (cov (fr i) x (X x)), B x (fr i x)⟫
          + ⟪A x (fr i x), B x (cov (fr i) x (X x))⟫) := by
    intro i
    have h := hcov.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X (hAfr i) (hBfr i)
    have h' : mvfderiv I (fun y ↦ ⟪A y (fr i y), B y (fr i y)⟫) x (X x)
        = ⟪cov (fun y ↦ A y (fr i y)) x (X x), B x (fr i x)⟫
          + ⟪A x (fr i x), cov (fun y ↦ B y (fr i y)) x (X x)⟫ := h
    rw [h', hLeibA i, hLeibB i, inner_add_left, inner_add_right]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib, hcross, add_zero,
    hsFibre_eq_sum_frame hs hx (endCov cov A x (X x)) (B x),
    hsFibre_eq_sum_frame hs hx (A x) (endCov cov B x (X x)), ← Finset.sum_add_distrib]

omit [CompleteSpace E] in
/-- **The induced connection on `End(TM)` is metric for the Hilbert–Schmidt form.**
`X⟨A,B⟩ = ⟨∇_X A, B⟩ + ⟨A, ∇_X B⟩`, with no frame in the statement.

The frame the proof uses is **not parallel**, and nothing makes it so: the `2n²` correction
terms cancel for `TraceCov.lean`'s reason — the connection coefficients of an orthonormal
frame are antisymmetric while `⟪A v, B w⟫ + ⟪A w, B v⟫` is symmetric. What is new is only that
the Leibniz rule being fed to each frame vector *is* the definition of `∇A` rearranged
(`endCov_apply`), so the two surviving sums are the Hilbert–Schmidt forms of `∇_X A` and
`∇_X B` read off the same frame. -/
theorem mvfderiv_hsFibre_eq
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {A B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {X : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x)
    (hA : IsMDiffHomAt (I := I) E E A x) (hB : IsMDiffHomAt (I := I) E E B x) :
    mvfderiv I (fun y ↦ hsFibre (I := I) y (A y) (B y)) x (X x)
      = hsFibre (I := I) x (endCov cov A x (X x)) (B x)
        + hsFibre (I := I) x (A x) (endCov cov B x (X x)) := by
  classical
  set e := trivializationAt E (fun y : M ↦ TangentSpace I y) x with he
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E _ x
  set bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbE
  exact mvfderiv_hsFibre_eq_of_frame cov hcov (bE.orthonormalFrame_isOrthonormalFrameOn e)
    e.open_baseSet hx hX hA hB

end Compat

section Synonym

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (EndTangent I (M := M))]
  [IsContMDiffRiemannianBundle I 1 (E →L[ℝ] E) (EndTangent I (M := M))]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

set_option maxSynthPendingDepth 4

/-- **The induced connection on `End(TM)`, transported to the synonym.** Definitional, like
the metric: `EndTangent I` and the raw endomorphism bundle differ by `delta` and `eta`. -/
noncomputable def endTangentCov :
    CovariantDerivative I (E →L[ℝ] E) (EndTangent I (M := M)) :=
  endCov cov

/-- **`endCov` is a metric connection for the Hilbert–Schmidt metric.** Stated against an
ambient `RiemannianBundle` binder whose inner product is `hsFibre`, which is the only shape
`IsMetricCompatible` elaborates in (see `CLAUDE.md`). -/
theorem isMetricCompatible_endTangentCov
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hinner : ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q) :
    (endTangentCov cov).IsMetricCompatible (M := M) (V := EndTangent I) := by
  rw [CovariantDerivative.isMetricCompatible_iff]
  intro x X σ τ hX hσ hτ
  have hA : IsMDiffHomAt (I := I) E E σ x := isMDiffHomAt_of_section hσ
  have hB : IsMDiffHomAt (I := I) E E τ x := isMDiffHomAt_of_section hτ
  have hmain := mvfderiv_hsFibre_eq cov hcov hX hA hB
  have hfun : (fun y ↦ ⟪σ y, τ y⟫) = fun y ↦ hsFibre (I := I) y (σ y) (τ y) :=
    funext fun y ↦ hinner y (σ y) (τ y)
  show mvfderiv I (fun y ↦ ⟪σ y, τ y⟫) x (X x)
      = ⟪endTangentCov cov σ x (X x), τ x⟫ + ⟪σ x, endTangentCov cov τ x (X x)⟫
  rw [hfun, hmain, hinner x _ (τ x), hinner x (σ x) _]
  rfl

end Synonym

section Instantiated

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

set_option maxSynthPendingDepth 4

/-- The Hilbert–Schmidt metric's inner product **is** `hsFibre`, by `rfl`. -/
theorem inner_endTangentRiemannianBundle :
    letI : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
    ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q :=
  fun _ _ _ ↦ rfl

/-- **`endCov` is metric for the Hilbert–Schmidt metric it is actually paired with.** The
falsification check for the file: the abstract statement above is instantiated at the metric
`EndBundleMetric.lean` builds, so connection and fibre metric now sit on the same non-tangent
bundle and agree. -/
theorem isMetricCompatible_endTangentCov_hs
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) :
    letI : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
    (endTangentCov cov).IsMetricCompatible (M := M) (V := EndTangent I) :=
  letI : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
  haveI := isContMDiffRiemannianBundle_endTangent (I := I) (M := M) (n := 1)
  isMetricCompatible_endTangentCov cov hcov inner_endTangentRiemannianBundle

end Instantiated

end RicciFlowBlueprint
