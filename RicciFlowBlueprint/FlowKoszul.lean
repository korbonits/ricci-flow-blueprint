/-
Wiring the first variation of the connection into the Koszul machinery.

`CurvatureVariation.lean` delivers `∂ₜ∇` as `derivDifferenceE`, characterised by the Koszul
combination of `h = ∂ₜ g` (`inner_derivDifferenceE_eq`), and `∂ₜ Rm` as a difference of
`covEnd`s. `KoszulSecondDeriv.lean` proves, for *any* tensor with that characterisation, that
its covariant derivative satisfies the same combination one level up and that the double trace
is `div div h − tr_g(Δ_g h)`. This file connects the two:

* `covEnd_eq_covTwoTensor` --- the two `∇` of a `(1,2)`-tensor agree up to the order of the
  last two slots, which is how `∂ₜ Rm` arrives;
* `isKoszulOf_derivDifference` --- `∂ₜ∇`, flipped into `(direction, argument)` order, is
  Koszul for `h`.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureVariation
import RicciFlowBlueprint.RicciVariation
import RicciFlowBlueprint.KoszulSecondDeriv

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇` of a `(1,2)`-tensor, the two ways.** `covEnd` (used by the first variation of the
curvature) takes the tensor with its argument first and its direction second, matching
`differenceE`; `covTwoTensor` (used by the Koszul machinery) takes the direction first. So the
two agree on flipped tensors, term for term. -/
theorem covEnd_eq_covTwoTensor_flip (A : M → E →L[ℝ] E →L[ℝ] E)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    cov.covEnd A X Y Z x
      = cov.covTwoTensor (fun y ↦ ((A y).flip :
          TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)) X Y Z x := rfl

end CovariantDerivative

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

section Flow

set_option maxSynthPendingDepth 3

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- **`∂ₜ∇` as a `(1,2)`-tensor in `(direction, argument)` order.** `derivDifferenceE` takes
the section value first and the direction second, matching `differenceE`; the Koszul machinery
takes the direction first, so this is the flip. -/
noncomputable def derivDifferenceTensor
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (t₀ : ℝ)
    (y : M) : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y :=
  ((derivDifferenceE g t₀ y).flip : E →L[ℝ] E →L[ℝ] E)

omit [CompleteSpace E] in
-- BENCH: koszul-of-deriv-difference
/-- **`∂ₜ∇` is Koszul for `h = ∂ₜ g`.** `inner_derivDifferenceE_eq` states this on the
constant-in-a-trivialisation extensions of the two vectors; the `covBilin` congr lemmas
transfer it to arbitrary differentiable fields, which is the form `KoszulSecondDeriv.lean`
consumes. -/
theorem isKoszulOf_derivDifference
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    (hb : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    (leviCivitaOfMetric (g t₀)).IsKoszulOf (derivDifferenceTensor g t₀) h := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  intro P Q R hP hQ hR y
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hPy : MDiffAt (T% P) y := hP.mdifferentiable h1 y
  have hQy : MDiffAt (T% Q) y := hQ.mdifferentiable h1 y
  have hRy : MDiffAt (T% R) y := hR.mdifferentiable h1 y
  have hEP : MDiffAt (T% (FiberBundle.extend E (show TangentSpace I y from P y))) y :=
    FiberBundle.mdifferentiableAt_extend ..
  have hEQ : MDiffAt (T% (FiberBundle.extend E (show TangentSpace I y from Q y))) y :=
    FiberBundle.mdifferentiableAt_extend ..
  have hvP : (FiberBundle.extend E (show TangentSpace I y from P y) : Π z : M,
      TangentSpace I z) y = P y := FiberBundle.extend_apply_self ..
  have hvQ : (FiberBundle.extend E (show TangentSpace I y from Q y) : Π z : M,
      TangentSpace I z) y = Q y := FiberBundle.extend_apply_self ..
  have key := inner_derivDifferenceE_eq hg hcomm y (P y) (Q y) hRy
  set cov := leviCivitaOfMetric (g t₀) with hcovdef
  have e₁ : cov.covBilin h (FiberBundle.extend E (show TangentSpace I y from P y))
      (FiberBundle.extend E (show TangentSpace I y from Q y)) R y
      = cov.covBilin h P Q R y := by
    rw [cov.covBilin_congr_dir (X' := P) hvP,
      cov.covBilin_congr_snd (hb y) P hEQ hQy hRy hvQ]
  have e₂ : cov.covBilin h (FiberBundle.extend E (show TangentSpace I y from Q y)) R
      (FiberBundle.extend E (show TangentSpace I y from P y)) y
      = cov.covBilin h Q R P y := by
    rw [cov.covBilin_congr_dir (X' := Q) hvQ,
      cov.covBilin_congr_thd (hb y) Q hRy hEP hPy hvP]
  have e₃ : cov.covBilin h R (FiberBundle.extend E (show TangentSpace I y from P y))
      (FiberBundle.extend E (show TangentSpace I y from Q y)) y
      = cov.covBilin h R P Q y := by
    rw [cov.covBilin_congr_snd (hb y) R hEP hPy hEQ hvP,
      cov.covBilin_congr_thd (hb y) R hPy hEQ hQy hvQ]
  rw [← e₁, ← e₂, ← e₃]
  exact key

omit [CompleteSpace E] in
-- BENCH: variation-curvature-as-koszul-tensor
/-- **`∂ₜ Rm` in the Koszul machinery's language**: `∂ₜ Rm(X,Y)Z = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)`
with `Ȧ = ∂ₜ∇` written as a `(1,2)`-tensor in `(direction, argument)` order. This is exactly
the `Rm_A` whose double trace `sum_inner_covTwoTensor_eq` computes. -/
theorem hasDerivAt_curvatureE_covTwoTensor
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXYZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (Y y))
        x (X x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (Y y)) x (X x)) t₀)
    (hYXZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (X y))
        x (Y x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (X y)) x (Y x)) t₀) :
    HasDerivAt (fun t ↦ curvatureE (leviCivitaOfMetric (g t)) X Y Z x)
      ((leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X Y Z x
        - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) Y X Z x) t₀ :=
  hasDerivAt_curvatureE_leviCivitaOfMetric hg hcomm hZ hX hY hXYZ hYXZ

/-- **`∂ₜ[v ↦ Rm(v,X)Y]` on arbitrary differentiable fields.** `derivCurvatureEndoE_apply`
states it on the constant-in-a-trivialisation extension of `v`; the direction slot of `∇A` is
pointwise for free and its argument slot by `covTwoTensor_congr_snd`, so it transfers. -/
theorem derivCurvatureEndoE_apply_field
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {x : M} (hA : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    {V X Y : Π y : M, TangentSpace I y}
    (hV : MDiffAt (T% V) x) (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y)) :
    derivCurvatureEndoE g t₀ X hY x (V x)
      = (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) V X Y x
        - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X V Y x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hY1 : MDiffAt (T% Y) x := hY.mdifferentiable h2 x
  have hE : MDiffAt (T% (FiberBundle.extend E (show TangentSpace I x from V x))) x :=
    FiberBundle.mdifferentiableAt_extend ..
  have hEv : (FiberBundle.extend E (show TangentSpace I x from V x) : Π z : M,
      TangentSpace I z) x = V x := FiberBundle.extend_apply_self ..
  rw [derivCurvatureEndoE_apply hg hcomm hcov hX hY (V x)]
  rw [show covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀)
      (FiberBundle.extend E (show TangentSpace I x from V x)) X Y x
      = (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
        (FiberBundle.extend E (show TangentSpace I x from V x)) X Y x from rfl,
    show covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀) X
      (FiberBundle.extend E (show TangentSpace I x from V x)) Y x
      = (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀) X
        (FiberBundle.extend E (show TangentSpace I x from V x)) Y x from rfl,
    (leviCivitaOfMetric (g t₀)).covTwoTensor_congr_dir (U' := V) hEv,
    (leviCivitaOfMetric (g t₀)).covTwoTensor_congr_snd hA X hE hV hY1 hEv]
  rfl

variable [T2Space M]

/-- `∂ₜ Ric(v,w)` is the trace of `∂ₜ[u ↦ Rm(u,V)W]`, for any `C²` fields taking those values
at `x`. Uniqueness of derivatives against `hasDerivAt_ricciFormOfMetric`. -/
theorem derivRicciFormOfMetric_apply
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (x : M) (v w : TangentSpace I x) {V W : Π y : M, TangentSpace I y}
    (hV : CMDiff 2 (T% V)) (hW : CMDiff 2 (T% W)) (hVv : V x = v) (hWw : W x = w) :
    derivRicciFormOfMetric g t₀ x v w = traceCLM (derivCurvatureEndoE g t₀ V hW x) := by
  have hd : HasDerivAt (fun t ↦ ricciFormOfMetric (g t) x v w)
      (derivRicciFormOfMetric g t₀ x v w) t₀ := by
    have := ((hasDerivAt_ricciFormOfMetric hg hcomm hcov x).clm_apply
      (hasDerivAt_const (F := E) t₀ v)).clm_apply (hasDerivAt_const (F := E) t₀ w)
    simp only [map_zero, add_zero] at this
    exact this
  exact hd.unique
    (hasDerivAt_ricciFormOfMetric_apply hg hcomm hcov x v w hV hW hVv hWw)

set_option maxHeartbeats 1000000 in
-- BENCH: metric-trace-of-ricci-variation
/-- **`tr_g(∂ₜ Ric)` is the double trace of `Rm_A`.** The outer trace is `metricTraceE_eq_sum`,
the inner one `LinearMap.trace_eq_sum_inner`, and the summand is
`derivCurvatureEndoE_apply_field`; one `Finset.sum_comm` lines the two up with
`sum_inner_covTwoTensor_eq`. -/
theorem metricTraceE_derivRicciFormOfMetric_eq
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {x : M} (hA : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i)))
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis iota ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    metricTraceE (g t₀) x (derivRicciFormOfMetric g t₀ x)
      = ∑ i, ∑ j, ⟪(leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
            (fr i) (fr j) (fr j) x
          - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
            (fr j) (fr i) (fr j) x, fr i x⟫ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  have hfin : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr i).mdifferentiable h2 x
  rw [metricTraceE_eq_sum (I := I) (M := M) (g t₀) x _ b]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hbv j, derivRicciFormOfMetric_apply (V := fr j) (W := fr j) hg hcomm hcov x
    (fr j x) (fr j x) (hfr j) (hfr j) rfl rfl]
  -- the trace as a frame sum, in the `→ₗ` form `metricTraceE_eq_sum` uses: ascribing an
  -- `E →L[ℝ] E` to the `TangentSpace` type grinds, but `→ₗ[ℝ]` needs only the module instances
  let T : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    (derivCurvatureEndoE g t₀ (fr j) (hfr j) x).toLinearMap
  change LinearMap.trace ℝ (TangentSpace I x) T = _
  rw [LinearMap.trace_eq_sum_inner T b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : ⟪b i, T (b i)⟫ = ⟪T (b i), b i⟫ := real_inner_comm _ _
  -- the summand, as an equation between tangent vectors: no inner product, so no `Inner ℝ E`
  have hT : (T (b i) : TangentSpace I x)
      = (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
          (fr i) (fr j) (fr j) x
        - (leviCivitaOfMetric (g t₀)).covTwoTensor (derivDifferenceTensor g t₀)
          (fr j) (fr i) (fr j) x := by
    show derivCurvatureEndoE g t₀ (fr j) (hfr j) x (b i) = _
    rw [← hbv i, derivCurvatureEndoE_apply_field hg hcomm hcov hA (hfr1 i) (hfr1 j) (hfr j)]
  rw [e, hT, hbv i]

set_option maxHeartbeats 1000000 in
-- BENCH: trace-of-ricci-variation-koszul
/-- **`tr_g(∂ₜ Ric) = div div h − tr_g(Δ_g h)`**, with `h = ∂ₜ g` and no curvature terms:
the last identification the evolution of the scalar curvature needs. The double trace of
`∂ₜ Rm` is computed by `sum_inner_covTwoTensor_eq`, and `∂ₜ∇` supplies its Koszul hypothesis
by `isKoszulOf_derivDifference`. -/
theorem metricTraceE_derivRicciFormOfMetric_eq_sub
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    (hsymm : ∀ (y : M) (v w : E), h y v w = h y w v)
    {x : M} (hA : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i)))
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      OrthonormalBasis iota ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i)
    (hd : ∀ a c d, MDiffAt
      (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin h (fr a) (fr c) (fr d) y) x) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    metricTraceE (g t₀) x (derivRicciFormOfMetric g t₀ x)
      = (∑ i, ∑ j, (leviCivitaOfMetric (g t₀)).cov2Bilin h (fr i) (fr j) (fr j) (fr i) x)
        - ∑ i, ∑ j, (leviCivitaOfMetric (g t₀)).cov2Bilin h (fr i) (fr i) (fr j) (fr j) x := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr i).mdifferentiable h2 x
  rw [metricTraceE_derivRicciFormOfMetric_eq hg hcomm hcov hA hfr b hbv]
  simp only [inner_sub_left]
  exact (leviCivitaOfMetric (g t₀)).sum_inner_covTwoTensor_eq
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
    (isKoszulOf_derivDifference hg hcomm hbil) hsymm hfr
    (fun i j ↦ hA _ _ (hfr1 i) (hfr1 j)) hd

end Flow

end RicciFlowBlueprint
