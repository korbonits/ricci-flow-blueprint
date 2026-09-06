/-
The first variations of the Ricci and scalar curvatures.

Ricci curvature is the trace of the endomorphism `v ↦ R(v, X)Y` of `T_xM`
(`curvatureEndoE`), so along a family of metrics `∂ₜ Ric(X,Y) = tr(∂ₜ [v ↦ R(v,X)Y])`
with no correction from the metric (`hasDerivAt_ricciOfMetric`); the endomorphism's
derivative is the first variation of the curvature (`CurvatureVariation.lean`),
`∂ₜ R(v,X)Y = (∇_v Ȧ)(X,Y) − (∇_X Ȧ)(v,Y)`.

Scalar curvature is the *metric* trace of the Ricci form, `R = tr_g Ric`, so the
metric enters: `∂ₜ R = tr_g(∂ₜ Ric) − ⟨h, Ric⟩_g` (`hasDerivAt_scalarCurvature`,
from `MetricTrace.lean`), and under the flow `h = −2 Ric` the correction is
`2|Ric|²`: `∂ₜ R = tr_g(∂ₜ Ric) + 2|Ric|²` (`hasDerivAt_scalarCurvature_of_isRicciFlowAt`).
The remaining step to `∂ₜ R = ΔR + 2|Ric|²` is the identification
`tr_g(∂ₜ Ric) = ΔR` under the flow, which is the contracted second Bianchi identity
and needs the trace to commute with `∇` on the manifold.

The Ricci variation is on any manifold. The scalar curvature is on the model space
`M = E`, where `Scalar.lean` defines it: its definition feeds an orthonormal basis
into *both* slots of `ricci`, and the second slot needs globally `C²` fields, which
constant fields are on `E` and `FiberBundle.extend` is not on a general manifold.

Two commutation hypotheses are stated in the form used, both joint regularity in
`(t, x)`: `CommutesWithMvfderiv` (`CurvatureVariation.lean`) and `CommutesWithCov`,
that `∂ₜ` commutes with `∇_X` on the sections `Aᵗ(Y,Z)` of the difference tensor.
-/
import RicciFlowBlueprint.MetricTrace
import RicciFlowBlueprint.CurvatureVariation
import RicciFlowBlueprint.Scalar
import RicciFlowBlueprint.Flow

open Bundle CovariantDerivative
open scoped Manifold ContDiff

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

set_option maxSynthPendingDepth 3

section Ricci

/-- **The commutation hypothesis for the curvature variation**: `∂ₜ` commutes with `∇_X` on
the sections `y ↦ Aᵗ(Y,Z)(y)` of the difference tensor `Aᵗ = ∇ᵗ − ∇ᵗ⁰`, for all fields. -/
def CommutesWithCov (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (t₀ : ℝ) : Prop :=
  ∀ (X Y Z : Π y : M, TangentSpace I y) (x : M),
    MDiffAt (T% X) x → MDiffAt (T% Y) x → CMDiff 2 (T% Z) →
    HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (Y y))
        x (X x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (Y y)) x (X x)) t₀

/-- The **curvature endomorphism** `v ↦ R(v, X)Y` of `T_xM`, on `E`, for the Levi-Civita
connection of `g`; its trace is `Ric(X, Y)`. -/
noncomputable def curvatureEndoE
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y))
    (x : M) : E →L[ℝ] E :=
  haveI := contMDiffCovariantDerivative_leviCivitaOfMetric_one g
  (TensorialAt.mkHom (fun W ↦ (leviCivitaOfMetric g).curvature W X Y x) x
    ((leviCivitaOfMetric g).tensorialAt_curvature_fst hY x) :
      TangentSpace I x →L[ℝ] TangentSpace I x)

theorem curvatureEndoE_apply
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y))
    (x : M) (v : E) :
    curvatureEndoE g X hY x v
      = curvatureE (leviCivitaOfMetric g) (FiberBundle.extend E (show TangentSpace I x from v))
          X Y x := by
  have := contMDiffCovariantDerivative_leviCivitaOfMetric_one g
  unfold curvatureEndoE
  rfl

/-- `Ric(X, Y) = tr (v ↦ R(v, X)Y)`. -/
theorem ricciOfMetric_eq_trace
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y))
    (x : M) :
    ricciOfMetric g X Y x = traceCLM (curvatureEndoE g X hY x) := by
  have := contMDiffCovariantDerivative_leviCivitaOfMetric_one g
  exact ricci_eq_trace_of_apply (leviCivitaOfMetric g) hY
    (fun v ↦ curvatureEndoE_apply g X hY x v)

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- The derivative of the curvature endomorphism `v ↦ R(v, X)Y` along the family. -/
noncomputable def derivCurvatureEndoE
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (t₀ : ℝ)
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y))
    (x : M) : E →L[ℝ] E :=
  deriv (fun t ↦ curvatureEndoE (g t) X hY x) t₀

/-- Each value `R_t(v, X)Y` is differentiable in `t`: the first variation of the curvature
on the field `extend v`. -/
theorem hasDerivAt_curvatureEndoE_apply
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y))
    (v : E) :
    HasDerivAt (fun t ↦ curvatureEndoE (g t) X hY x v)
      (covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀)
          (FiberBundle.extend E (show TangentSpace I x from v)) X Y x
        - covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀) X
          (FiberBundle.extend E (show TangentSpace I x from v)) Y x) t₀ := by
  have hW := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I x from v)
  have hfun : (fun t ↦ curvatureEndoE (g t) X hY x v) = fun t ↦
      curvatureE (leviCivitaOfMetric (g t)) (FiberBundle.extend E (show TangentSpace I x from v))
        X Y x := by
    funext t; exact curvatureEndoE_apply (g t) X hY x v
  rw [hfun]
  exact hasDerivAt_curvatureE_leviCivitaOfMetric hg hcomm hY hW hX
    (hcov _ X Y x hW hX hY) (hcov X _ Y x hX hW hY)

/-- **The curvature endomorphism is differentiable in `t`.** -/
theorem hasDerivAt_curvatureEndoE
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y)) :
    HasDerivAt (fun t ↦ curvatureEndoE (g t) X hY x) (derivCurvatureEndoE g t₀ X hY x) t₀ := by
  obtain ⟨T', hT'⟩ := exists_hasDerivAt_clm_of_apply
    (B := fun t ↦ curvatureEndoE (g t) X hY x) (t₀ := t₀)
    (fun v ↦ ⟨_, hasDerivAt_curvatureEndoE_apply hg hcomm hcov hX hY v⟩)
  exact hT'.differentiableAt.hasDerivAt

/-- **`∂ₜ [v ↦ R(v,X)Y] = (∇_v Ȧ)(X,Y) − (∇_X Ȧ)(v,Y)`**, with `Ȧ = ∂ₜ ∇`. -/
theorem derivCurvatureEndoE_apply
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y))
    (v : E) :
    derivCurvatureEndoE g t₀ X hY x v
      = covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀)
          (FiberBundle.extend E (show TangentSpace I x from v)) X Y x
        - covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀) X
          (FiberBundle.extend E (show TangentSpace I x from v)) Y x := by
  have h1 : HasDerivAt (fun t ↦ curvatureEndoE (g t) X hY x v)
      (derivCurvatureEndoE g t₀ X hY x v) t₀ := by
    have := (hasDerivAt_curvatureEndoE hg hcomm hcov hX hY).clm_apply
      (hasDerivAt_const (F := E) t₀ v)
    simp only [map_zero, add_zero] at this
    exact this
  exact h1.unique (hasDerivAt_curvatureEndoE_apply hg hcomm hcov hX hY v)

-- BENCH: variation-ricci
/-- **First variation of the Ricci curvature**: `∂ₜ Ric_t(X,Y)(x) = tr(∂ₜ [v ↦ R_t(v,X)Y])`.
No correction from the metric appears: Ricci is the trace of an endomorphism. -/
theorem hasDerivAt_ricciOfMetric
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y)) :
    HasDerivAt (fun t ↦ ricciOfMetric (g t) X Y x)
      (traceCLM (derivCurvatureEndoE g t₀ X hY x)) t₀ := by
  have hfun : (fun t ↦ ricciOfMetric (g t) X Y x)
      = fun t ↦ traceCLM (curvatureEndoE (g t) X hY x) := by
    funext t; exact ricciOfMetric_eq_trace (g t) X hY x
  rw [hfun]
  exact traceCLM.hasFDerivAt.comp_hasDerivAt t₀ (hasDerivAt_curvatureEndoE hg hcomm hcov hX hY)

end Ricci

/-! ### Scalar curvature on the model space

On `M = E` constant fields are global smooth sections, so `Ric(v, w) = Ric(v̄, w̄)(x)` with `v̄`,
`w̄` constant is a bilinear form on `E` (`ricciE`), the scalar curvature of `Scalar.lean` is its
metric trace, and `MetricTrace.lean` differentiates it. -/

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

set_option maxSynthPendingDepth 3

/-- The constant vector field `v̄` on the model space. -/
def constField (v : E) : Π y : E, TangentSpace 𝓘(ℝ, E) y := fun _ ↦ v

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem constField_add (v v' : E) : constField (v + v') = constField v + constField v' := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem constField_smul (c : ℝ) (v : E) :
    constField (c • v) = (fun _ : E ↦ c) • constField v := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem constField_smul' (c : ℝ) (v : E) : constField (c • v) = c • constField v := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem contMDiff_constField (v : E) {n : ℕ∞ω} : CMDiff n (T% (constField v)) :=
  contMDiff_const_section rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem mdiffAt_constField (v : E) (x : E) : MDiffAt (T% (constField v)) x :=
  (contMDiff_constField (n := 2) v).mdifferentiable (by norm_num) x

/-- Ricci curvature on the second slot is additive on constant fields. -/
theorem ricci_add_right_const
    (cov : CovariantDerivative 𝓘(ℝ, E) E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)) [ContMDiffCovariantDerivative cov 1]
    {X : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E} (hX : MDiffAt (T% X) x) (w w' : E) :
    cov.ricci X (constField (w + w')) x
      = cov.ricci X (constField w) x + cov.ricci X (constField w') x := by
  rw [cov.ricci_eq_trace (contMDiff_constField _) x, cov.ricci_eq_trace (contMDiff_constField _) x,
    cov.ricci_eq_trace (contMDiff_constField _) x, ← map_add]
  congr 1
  ext v
  simp only [ContinuousLinearMap.coe_coe, LinearMap.add_apply, TensorialAt.mkHom_apply_eq_extend]
  rw [constField_add]
  exact cov.curvature_add_right (contMDiff_constField w) (contMDiff_constField w')
    (FiberBundle.mdifferentiableAt_extend _ E v) hX

/-- Ricci curvature on the second slot is homogeneous on constant fields. -/
theorem ricci_smul_right_const
    (cov : CovariantDerivative 𝓘(ℝ, E) E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)) [ContMDiffCovariantDerivative cov 1]
    {X : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E} (hX : MDiffAt (T% X) x) (c : ℝ) (w : E) :
    cov.ricci X (constField (c • w)) x = c * cov.ricci X (constField w) x := by
  rw [cov.ricci_eq_trace (contMDiff_constField _) x, cov.ricci_eq_trace (contMDiff_constField _) x,
    show c * _ = c • LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, E) x)
      (TensorialAt.mkHom (fun W ↦ cov.curvature W X (constField w) x) x
        (cov.tensorialAt_curvature_fst (contMDiff_constField w) x)).toLinearMap from rfl,
    ← map_smul]
  congr 1
  ext v
  simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, TensorialAt.mkHom_apply_eq_extend]
  rw [constField_smul']
  exact cov.curvature_smul_const_right c (contMDiff_constField w)
    (FiberBundle.mdifferentiableAt_extend _ E v) hX

variable (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) 2 E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x))

/-- **The Ricci form** of `g` at `x`, as a bilinear form on `E`: `Ric(v, w) = Ric(v̄, w̄)(x)` for
the constant fields `v̄`, `w̄`. -/
noncomputable def ricciE (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  have := contMDiffCovariantDerivative_leviCivitaOfMetric_one g
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun v w ↦ ricciOfMetric (I := 𝓘(ℝ, E)) (M := E) g (constField v) (constField w) x)
        (fun v v' w ↦ by
          rw [constField_add]
          exact (leviCivitaOfMetric g).ricci_add_left (contMDiff_constField w)
            (mdiffAt_constField v x) (mdiffAt_constField v' x))
        (fun c v w ↦ by
          rw [constField_smul]
          exact (leviCivitaOfMetric g).ricci_smul_left (contMDiff_constField w)
            mdifferentiableAt_const (mdiffAt_constField v x))
        (fun v w w' ↦ ricci_add_right_const (leviCivitaOfMetric g) (mdiffAt_constField v x) w w')
        (fun c v w ↦ ricci_smul_right_const (leviCivitaOfMetric g) (mdiffAt_constField v x) c w))

theorem ricciE_apply (x : E) (v w : E) :
    ricciE g x v w = ricciOfMetric (I := 𝓘(ℝ, E)) (M := E) g (constField v) (constField w) x :=
  rfl

/-- **The scalar curvature of a metric on the model space**, `Scalar.lean`'s
`scalarCurvature` for the Levi-Civita connection of `g`. -/
noncomputable def scalarCurvatureOfMetric' (x : E) : ℝ :=
  letI : RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  (leviCivitaOfMetric g).scalarCurvature x

/-- **Scalar curvature is the metric trace of the Ricci form.** -/
theorem scalarCurvatureOfMetric'_eq_metricTraceE (x : E) :
    scalarCurvatureOfMetric' g x = metricTraceE (I := 𝓘(ℝ, E)) (M := E) g x (ricciE g x) := by
  let _ : RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  rw [metricTraceE_eq_sum (I := 𝓘(ℝ, E)) (M := E) g x _
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x))]
  rfl

variable {g : ℝ → ContMDiffRiemannianMetric 𝓘(ℝ, E) 2 E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)} {h : E → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- Each value `Ric_t(v, w)(x)` is differentiable in `t`. -/
theorem hasDerivAt_ricciE_apply
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀) (x v w : E) :
    HasDerivAt (fun t ↦ ricciE (g t) x v w)
      (traceCLM (derivCurvatureEndoE g t₀ (constField v) (contMDiff_constField w) x)) t₀ := by
  have hfun : (fun t ↦ ricciE (g t) x v w)
      = fun t ↦ ricciOfMetric (I := 𝓘(ℝ, E)) (M := E) (g t) (constField v) (constField w) x := by
    funext t; rfl
  rw [hfun]
  exact hasDerivAt_ricciOfMetric hg hcomm hcov (mdiffAt_constField v x) (contMDiff_constField w)

/-- The derivative `∂ₜ Ric` of the Ricci form along the family. -/
noncomputable def derivRicciE (g : ℝ → ContMDiffRiemannianMetric 𝓘(ℝ, E) 2 E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)) (t₀ : ℝ)
    (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  deriv (fun t ↦ ricciE (g t) x) t₀

/-- **The Ricci form is differentiable in `t`.** -/
theorem hasDerivAt_ricciE
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀) (x : E) :
    HasDerivAt (fun t ↦ ricciE (g t) x) (derivRicciE g t₀ x) t₀ := by
  obtain ⟨R', hR'⟩ := exists_hasDerivAt_clm₂_of_apply (B := fun t ↦ ricciE (g t) x) (t₀ := t₀)
    (fun v w ↦ ⟨_, hasDerivAt_ricciE_apply hg hcomm hcov x v w⟩)
  exact hR'.differentiableAt.hasDerivAt

/-- `∂ₜ Ric(v, w) = tr (∂ₜ [u ↦ R(u, v̄)w̄])`. -/
theorem derivRicciE_apply
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀) (x v w : E) :
    derivRicciE g t₀ x v w
      = traceCLM (derivCurvatureEndoE g t₀ (constField v) (contMDiff_constField w) x) := by
  have h1 : HasDerivAt (fun t ↦ ricciE (g t) x v w) (derivRicciE g t₀ x v w) t₀ := by
    have := ((hasDerivAt_ricciE hg hcomm hcov x).clm_apply
      (hasDerivAt_const (F := E) t₀ v)).clm_apply (hasDerivAt_const (F := E) t₀ w)
    simp only [map_zero, add_zero] at this
    exact this
  exact h1.unique (hasDerivAt_ricciE_apply hg hcomm hcov x v w)

-- BENCH: variation-scalar
/-- **First variation of the scalar curvature**: `∂ₜ R = tr_g(∂ₜ Ric) − ⟨h, Ric⟩_g`. -/
theorem hasDerivAt_scalarCurvatureOfMetric'
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀) (x : E) :
    HasDerivAt (fun t ↦ scalarCurvatureOfMetric' (g t) x)
      (metricTraceE (I := 𝓘(ℝ, E)) (M := E) (g t₀) x (derivRicciE g t₀ x)
        - metricTraceE (I := 𝓘(ℝ, E)) (M := E) (g t₀) x
            (h x ∘L sharpE (I := 𝓘(ℝ, E)) (M := E) (g t₀) x (ricciE (g t₀) x))) t₀ := by
  have hfun : (fun t ↦ scalarCurvatureOfMetric' (g t) x)
      = fun t ↦ metricTraceE (I := 𝓘(ℝ, E)) (M := E) (g t) x (ricciE (g t) x) := by
    funext t; exact scalarCurvatureOfMetric'_eq_metricTraceE (g t) x
  rw [hfun]
  exact hasDerivAt_metricTraceE (hg x) (hasDerivAt_ricciE hg hcomm hcov x)

/-- Under the flow, `∂ₜ g = −2 Ric` as bilinear forms at `x`. -/
theorem innerE_deriv_eq_of_isRicciFlowAt
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀) (x : E)
    (hflow : letI : RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt 𝓘(ℝ, E) E g t₀) :
    h x = (-2 : ℝ) • ricciE (g t₀) x := by
  let _ : RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨(g t₀).toRiemannianMetric⟩
  ext v w
  have h1 := hasDerivAt_inner_apply hg x v w
  have h2 := (isRicciFlowAt_iff_leviCivita (I := 𝓘(ℝ, E)) (M := E)).mp hflow x (constField v)
    (constField w) (contMDiff_constField v) (contMDiff_constField w)
  have := h1.unique h2
  simp only [smul_apply, smul_eq_mul]
  rw [this]
  rfl

-- BENCH: evolution-scalar-trace
/-- **Scalar curvature under the Ricci flow**: `∂ₜ R = tr_g(∂ₜ Ric) + 2 |Ric|²_g`, where
`|Ric|²_g = tr_g (Ric ∘ Ric♯) = ∑ᵢⱼ Ric(eᵢ,eⱼ) Ric(eⱼ,eᵢ)` (`metricTraceE_comp_sharpE_eq_sum`).
What remains for `∂ₜ R = ΔR + 2|Ric|²` is `tr_g(∂ₜ Ric) = ΔR`, the contracted second Bianchi
identity. -/
theorem hasDerivAt_scalarCurvatureOfMetric'_of_isRicciFlowAt
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀) (x : E)
    (hflow : letI : RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt 𝓘(ℝ, E) E g t₀) :
    HasDerivAt (fun t ↦ scalarCurvatureOfMetric' (g t) x)
      (metricTraceE (I := 𝓘(ℝ, E)) (M := E) (g t₀) x (derivRicciE g t₀ x)
        + 2 * metricTraceE (I := 𝓘(ℝ, E)) (M := E) (g t₀) x
            (ricciE (g t₀) x ∘L sharpE (I := 𝓘(ℝ, E)) (M := E) (g t₀) x (ricciE (g t₀) x))) t₀ := by
  have := hasDerivAt_scalarCurvatureOfMetric' hg hcomm hcov x
  rw [innerE_deriv_eq_of_isRicciFlowAt hg x hflow] at this
  refine this.congr_deriv ?_
  rw [ContinuousLinearMap.smul_comp, metricTraceE_smul]
  ring

end ModelSpace

end RicciFlowBlueprint
