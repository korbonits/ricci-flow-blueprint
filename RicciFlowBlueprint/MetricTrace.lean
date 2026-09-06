/-
The metric trace of a bilinear form, and its time derivative.

For a metric `g` on `T_xM` and a bilinear form `B` on `T_xM`, the metric trace is
`tr_g B = ∑ᵢ B(eᵢ, eᵢ)` over a `g`-orthonormal basis, equivalently the trace of the
endomorphism `g♯⁻¹ ∘ B♭`. Along a family of metrics `g t` with `∂ₜ g = h` and a
family of forms `B t` with `∂ₜ B = Ḃ`,

  `∂ₜ tr_{g_t} B_t = tr_g Ḃ − ⟨h, B⟩_g`,  `⟨h, B⟩_g = ∑ᵢⱼ B(eᵢ,eⱼ) h(eⱼ,eᵢ)`,

because `∂ₜ (g♯)⁻¹ = −(g♯)⁻¹ h♭ (g♯)⁻¹`. This is what turns the first variation of
the curvature (`CurvatureVariation.lean`) into the first variations of the Ricci
and scalar curvatures: `Ric = tr_g Rm` and `R = tr_g Ric`, and under the flow
`h = −2 Ric`, so the correction term `−⟨h, Ric⟩` is the `2|Ric|²` of
`∂ₜ R = ΔR + 2|Ric|²`.

Everything here is at one point, on the model space `E = T_xM`: the metric is
`innerE g x : E →L E →L ℝ` (`Variation.lean`), invertible by positive definiteness
(`isInvertible_innerE`).
-/
import RicciFlowBlueprint.Variation
import Mathlib.Analysis.InnerProductSpace.Trace

open Bundle
open scoped Manifold ContDiff

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

set_option maxSynthPendingDepth 3

section MetricTrace

/-- The endomorphism `g♯⁻¹ ∘ B♭` of `E = T_xM` associated with a bilinear form `B` by the
metric `g` at `x`: `g(B♯ v, w) = B(v, w)`. -/
noncomputable def sharpE (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (innerE g x).inverse ∘L B

/-- **The metric trace** of a bilinear form on `T_xM`: `tr_g B = tr (g♯⁻¹ ∘ B♭)`. -/
noncomputable def metricTraceE
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) (B : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  LinearMap.trace ℝ E (sharpE g x B).toLinearMap

variable (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M)

omit [CompleteSpace E] in
/-- `g(B♯ v, w) = B(v, w)`. -/
theorem innerE_sharpE (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    innerE g x (sharpE g x B v) w = B v w := by
  have h := (isInvertible_innerE g x).self_comp_inverse
  have : innerE g x (sharpE g x B v) = B v := by
    change (innerE g x ∘L (innerE g x).inverse) (B v) = B v
    rw [h]
    rfl
  rw [this]

omit [CompleteSpace E] in
/-- **The metric trace is the trace over any `g`-orthonormal basis.** -/
theorem metricTraceE_eq_sum (B : E →L[ℝ] E →L[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x)) :
    metricTraceE g x B = ∑ i, B (b i) (b i) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let T : TangentSpace I x →ₗ[ℝ] TangentSpace I x := (sharpE g x B).toLinearMap
  change LinearMap.trace ℝ (TangentSpace I x) T = _
  rw [LinearMap.trace_eq_sum_inner T b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 : inner ℝ (b i) (T (b i)) = g.inner x (b i) (sharpE g x B (b i)) := rfl
  have h2 : g.inner x (b i) (sharpE g x B (b i)) = g.inner x (sharpE g x B (b i)) (b i) :=
    g.symm x _ _
  rw [h1, h2]
  exact innerE_sharpE g x B (b i) (b i)

omit [CompleteSpace E] in
/-- `B♯ v` expanded in a `g`-orthonormal basis: `B♯ v = ∑ⱼ B(v, bⱼ) bⱼ`. -/
theorem sharpE_apply_eq_sum (B : E →L[ℝ] E →L[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x)) (v : E) :
    sharpE g x B v = ∑ j, B v (b j) • (b j : E) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have := (b.sum_repr' (show TangentSpace I x from sharpE g x B v)).symm
  refine this.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  congr 1
  have h1 : inner ℝ (b j) (show TangentSpace I x from sharpE g x B v)
      = g.inner x (b j) (sharpE g x B v) := rfl
  have h2 : g.inner x (b j) (sharpE g x B v) = g.inner x (sharpE g x B v) (b j) :=
    g.symm x _ _
  rw [h1, h2]
  exact innerE_sharpE g x B v (b j)

omit [CompleteSpace E] in
/-- **The pairing `⟨h, B⟩_g`** as a trace: `tr (g♯⁻¹ h♭ g♯⁻¹ B♭) = ∑ᵢⱼ B(bᵢ,bⱼ) h(bⱼ,bᵢ)`. -/
theorem metricTraceE_comp_sharpE_eq_sum (h B : E →L[ℝ] E →L[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (b : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x)) :
    metricTraceE g x (h ∘L sharpE g x B) = ∑ i, ∑ j, B (b i) (b j) * h (b j) (b i) := by
  rw [metricTraceE_eq_sum g x _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change h (sharpE g x B (b i)) (b i) = _
  rw [sharpE_apply_eq_sum g x B b (b i)]
  -- stated for plain vectors of `E`, to keep the rewrites clear of `TangentSpace`
  have key : ∀ (c : ι → ℝ) (e : ι → E) (w : E),
      h (∑ j, c j • e j) w = ∑ j, c j * h (e j) w := by
    intro c e w
    rw [map_sum, FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact key (fun j ↦ B (b i) (b j)) (fun j ↦ b j) (b i)

omit [CompleteSpace E] in
/-- `tr_g (g♭ ∘ T) = tr T`: the metric trace of the form `(v, w) ↦ g(T v, w)` is the trace of
`T`. -/
theorem metricTraceE_innerE_comp (T : E →L[ℝ] E) :
    metricTraceE g x (innerE g x ∘L T) = LinearMap.trace ℝ E T.toLinearMap := by
  unfold metricTraceE sharpE
  rw [← ContinuousLinearMap.comp_assoc, (isInvertible_innerE g x).inverse_comp_self,
    ContinuousLinearMap.id_comp]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The metric trace is linear in the form. -/
theorem metricTraceE_smul (c : ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    metricTraceE g x (c • B) = c * metricTraceE g x B := by
  unfold metricTraceE sharpE
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]

end MetricTrace

section Ricci

open CovariantDerivative

omit [CompleteSpace E] in
/-- **Ricci is the trace of any endomorphism that agrees with `W ↦ R(W, X)Y` on constant
extensions**: the pointwise curvature endomorphism `mkHom` is characterised by its values. -/
theorem _root_.CovariantDerivative.ricci_eq_trace_of_apply
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1]
    {X Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y)) {x : M}
    {T : E →L[ℝ] E}
    (hT : ∀ v : TangentSpace I x, T v = cov.curvature (FiberBundle.extend E v) X Y x) :
    cov.ricci X Y x = LinearMap.trace ℝ E T.toLinearMap := by
  rw [cov.ricci_eq_trace hY x]
  have : TensorialAt.mkHom (fun W ↦ cov.curvature W X Y x) x
      (cov.tensorialAt_curvature_fst hY x) = T := by
    ext v
    rw [TensorialAt.mkHom_apply_eq_extend]
    exact (hT v).symm
  rw [this]
  rfl

omit [CompleteSpace E] in
/-- **Ricci as a metric trace**: `Ric(X,Y) = tr_g (g(R(·,X)Y, ·))`, for any endomorphism `T`
with `T v = R(v, X)Y` on constant extensions. -/
theorem ricci_eq_metricTraceE
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1]
    {X Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y)) {x : M}
    {T : E →L[ℝ] E}
    (hT : ∀ v : TangentSpace I x, T v = cov.curvature (FiberBundle.extend E v) X Y x) :
    cov.ricci X Y x = metricTraceE g x (innerE g x ∘L T) := by
  rw [metricTraceE_innerE_comp, cov.ricci_eq_trace_of_apply hY hT]

end Ricci

section Derivative

/-- The trace of an endomorphism of `E`, as a continuous linear functional on `E →L[ℝ] E`. -/
noncomputable def traceCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))

omit [CompleteSpace E] in
theorem traceCLM_apply (T : E →L[ℝ] E) : traceCLM T = LinearMap.trace ℝ E T.toLinearMap := rfl

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ} {x : M}

-- BENCH: inverse-metric-derivative
/-- **The inverse metric is differentiable**, with `∂ₜ (g♯)⁻¹ = −(g♯)⁻¹ h♭ (g♯)⁻¹`. -/
theorem hasDerivAt_inverse_innerE (hg : HasDerivAt (fun t ↦ innerE (g t) x) (h x) t₀) :
    HasDerivAt (fun t ↦ (innerE (g t) x).inverse)
      (-((innerE (g t₀) x).inverse ∘L (h x) ∘L (innerE (g t₀) x).inverse)) t₀ := by
  -- differentiable, with some derivative `D`
  obtain ⟨Eq, hEq⟩ := isInvertible_innerE (g t₀) x
  have hinv : HasFDerivAt ContinuousLinearMap.inverse
      (fderiv ℝ ContinuousLinearMap.inverse (innerE (g t₀) x)) (innerE (g t₀) x) := by
    have := (contDiffAt_map_inverse (n := 1) Eq).differentiableAt (by norm_num)
    rw [hEq] at this
    exact this.hasFDerivAt
  have hD : HasDerivAt (fun t ↦ (innerE (g t) x).inverse)
      (fderiv ℝ ContinuousLinearMap.inverse (innerE (g t₀) x) (h x)) t₀ :=
    HasFDerivAt.comp_hasDerivAt (f := fun t ↦ innerE (g t) x) (x := t₀) hinv hg
  set D := fderiv ℝ ContinuousLinearMap.inverse (innerE (g t₀) x) (h x) with hDdef
  -- differentiate `g ∘ g⁻¹ = id`: `h ∘ g⁻¹ + g ∘ D = 0`
  have hid : HasDerivAt (fun t ↦ innerE (g t) x ∘L (innerE (g t) x).inverse)
      ((h x) ∘L (innerE (g t₀) x).inverse + innerE (g t₀) x ∘L D) t₀ := hg.clm_comp hD
  have hconst : (fun t ↦ innerE (g t) x ∘L (innerE (g t) x).inverse)
      = fun _ ↦ ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ) := by
    funext t; exact (isInvertible_innerE (g t) x).self_comp_inverse
  rw [hconst] at hid
  have h0 := hid.unique (hasDerivAt_const t₀ _)
  -- hence `D = −g⁻¹ ∘ h ∘ g⁻¹`
  have h1 := congrArg (fun A ↦ (innerE (g t₀) x).inverse ∘L A) h0
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_zero] at h1
  have h2 : (innerE (g t₀) x).inverse ∘L (innerE (g t₀) x ∘L D) = D := by
    rw [← ContinuousLinearMap.comp_assoc, (isInvertible_innerE (g t₀) x).inverse_comp_self,
      ContinuousLinearMap.id_comp]
  rw [h2] at h1
  have hDeq : D = -((innerE (g t₀) x).inverse ∘L (h x) ∘L (innerE (g t₀) x).inverse) :=
    eq_neg_of_add_eq_zero_right h1
  rw [← hDeq]
  exact hD

-- BENCH: metric-trace-derivative
/-- **The time derivative of the metric trace**: along `∂ₜ g = h` and `∂ₜ B = B'`,
`∂ₜ tr_{g_t} B_t = tr_g B' − tr_g (h ∘ B♯) = tr_g B' − ⟨h, B⟩_g`. -/
theorem hasDerivAt_metricTraceE (hg : HasDerivAt (fun t ↦ innerE (g t) x) (h x) t₀)
    {B : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {B' : E →L[ℝ] E →L[ℝ] ℝ} (hB : HasDerivAt B B' t₀) :
    HasDerivAt (fun t ↦ metricTraceE (g t) x (B t))
      (metricTraceE (g t₀) x B' - metricTraceE (g t₀) x ((h x) ∘L sharpE (g t₀) x (B t₀))) t₀ := by
  have hsharp : HasDerivAt (fun t ↦ sharpE (g t) x (B t))
      ((-((innerE (g t₀) x).inverse ∘L (h x) ∘L (innerE (g t₀) x).inverse)) ∘L B t₀
        + (innerE (g t₀) x).inverse ∘L B') t₀ :=
    (hasDerivAt_inverse_innerE hg).clm_comp hB
  have hfun : (fun t ↦ metricTraceE (g t) x (B t)) = fun t ↦ traceCLM (sharpE (g t) x (B t)) :=
    rfl
  rw [hfun]
  have := traceCLM.hasFDerivAt.comp_hasDerivAt t₀ hsharp
  refine this.congr_deriv ?_
  rw [map_add, ContinuousLinearMap.neg_comp, map_neg, traceCLM_apply, traceCLM_apply]
  unfold metricTraceE sharpE
  simp only [ContinuousLinearMap.comp_assoc]
  ring

end Derivative

end RicciFlowBlueprint
