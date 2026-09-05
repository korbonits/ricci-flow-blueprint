/-
The second-derivative test, on the line, in a normed space, and for the Hessian
and Laplacian on the model space.

This is the joint between `Hessian.lean` and `MaximumPrinciple.lean`: the
abstract maximum principle assumes the differential inequality at a spatial
minimum, and the second-derivative test is what a Laplacian supplies there:
`∇f = 0` and `Δf ≥ 0` at a local minimum.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import RicciFlowBlueprint.Hessian

open Set Filter Topology

namespace RicciFlowBlueprint

/-- **Second-derivative test on the line.** If `g` is differentiable near `t₀` with
derivative `g'`, `g'` is differentiable at `t₀` with derivative `g''`, and `g` has a local
minimum at `t₀`, then `g'' ≥ 0`. -/
theorem deriv2_nonneg_of_isLocalMin {g g' : ℝ → ℝ} {g'' t₀ : ℝ}
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (g' t) t) (hg' : HasDerivAt g' g'' t₀)
    (hmin : IsLocalMin g t₀) : 0 ≤ g'' := by
  by_contra hneg
  push Not at hneg
  have h0 : g' t₀ = 0 := hmin.hasDerivAt_eq_zero hg.self_of_nhds
  -- `g' < 0` just to the right of `t₀`
  have hslope : ∀ᶠ t in 𝓝[>] t₀, g' t < 0 := by
    have h1 : ∀ᶠ t in 𝓝[≠] t₀, slope g' t₀ t < 0 :=
      (hasDerivAt_iff_tendsto_slope.mp hg').eventually (gt_mem_nhds hneg)
    have h2 : ∀ᶠ t in 𝓝[>] t₀, slope g' t₀ t < 0 :=
      h1.filter_mono (nhdsWithin_mono _ fun t ht ↦ ne_of_gt ht)
    filter_upwards [h2, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero] at ht
    rcases div_neg_iff.mp ht with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (not_lt.2 (sub_nonneg.2 (le_of_lt ht')))
    · exact h
  -- a right neighbourhood on which `g' < 0`, `g` is differentiable, and `g t₀ ≤ g t`
  have hev : ∀ᶠ t in 𝓝[>] t₀, g' t < 0 ∧ HasDerivAt g (g' t) t ∧ g t₀ ≤ g t :=
    hslope.and ((hg.and hmin).filter_mono nhdsWithin_le_nhds)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set t₁ := (t₀ + u) / 2 with ht₁
  have ht₀₁ : t₀ < t₁ := by rw [ht₁]; linarith [mem_Ioi.mp hu]
  have ht₁u : t₁ < u := by rw [ht₁]; linarith [mem_Ioi.mp hu]
  have hmem : ∀ t ∈ Ioc t₀ t₁, g' t < 0 ∧ HasDerivAt g (g' t) t ∧ g t₀ ≤ g t :=
    fun t ht ↦ hsub ⟨ht.1, ht.2.trans_lt ht₁u⟩
  -- the mean value theorem on `[t₀, t₁]`
  have hcont : ContinuousOn g (Icc t₀ t₁) := by
    intro t ht
    rcases ht.1.lt_or_eq with h | h
    · exact (hmem t ⟨h, ht.2⟩).2.1.continuousAt.continuousWithinAt
    · rw [← h]
      exact hg.self_of_nhds.continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' ht₀₁ hcont
    fun t ht ↦ (hmem t ⟨ht.1, ht.2.le⟩).2.1
  have hc' := (hmem c ⟨hc.1, hc.2.le⟩).1
  have h₁ := (hmem t₁ ⟨ht₀₁, le_rfl⟩).2.2
  rw [hcs] at hc'
  have : g t₁ - g t₀ < 0 := by
    have hpos : 0 < t₁ - t₀ := by linarith
    rcases div_neg_iff.mp hc' with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact h
  linarith

/-- **Second-derivative test in a normed space**, along a direction: for `f` twice
continuously differentiable at a local minimum `x₀`, `D²f(x₀)(v, v) ≥ 0`. -/
theorem fderiv2_nonneg_of_isLocalMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x₀ : E} (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x₀ v v := by
  set L : ℝ → E := fun t ↦ x₀ + t • v with hL
  have hLc : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hL0 : L 0 = x₀ := by simp [L]
  have hLd : ∀ t, HasDerivAt L v t := fun t ↦
    (((hasDerivAt_id t).smul_const v).const_add x₀).congr_deriv (one_smul ℝ v)
  have hgmin : IsLocalMin (f ∘ L) 0 := by
    have : IsLocalMin f (L 0) := hL0 ▸ hmin
    exact this.comp_continuous hLc.continuousAt
  -- `fderiv f` is `C¹`, hence differentiable, at `x₀`
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x₀) x₀ :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  -- first derivative of `f ∘ L`, near `0`
  have hev : ∀ᶠ t in 𝓝 0, HasDerivAt (f ∘ L) (fderiv ℝ f (L t) v) t := by
    have h1 : ∀ᶠ y in 𝓝 (L 0), ContDiffAt ℝ 2 f y := by
      rw [hL0]
      exact hf.eventually (by simp)
    have h2 : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ 2 f (L t) := hLc.continuousAt.eventually h1
    filter_upwards [h2] with t ht
    exact HasFDerivAt.comp_hasDerivAt (f := L) (x := t)
      (ht.differentiableAt (by norm_num)).hasFDerivAt (hLd t)
  -- second derivative of `f ∘ L` at `0`
  have hF : HasFDerivAt (fun y ↦ fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) x₀).flip v) (L 0) := by
    rw [hL0]
    have := hDf.clm_apply (hasFDerivAt_const v x₀)
    refine this.congr_fderiv ?_
    ext w
    simp
  have hg' : HasDerivAt (fun t ↦ fderiv ℝ f (L t) v) (fderiv ℝ (fderiv ℝ f) x₀ v v) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (f := L) (x := 0) hF (hLd 0)
    rw [ContinuousLinearMap.flip_apply] at this
    exact this
  exact deriv2_nonneg_of_isLocalMin hev hg' hgmin

section ModelSpace

open Bundle CovariantDerivative
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
-- BENCH: hessian-nonneg-min
/-- **The Hessian is nonnegative at a local minimum** (model space): for `f` twice
continuously differentiable with a local minimum at `x₀`, and any covariant derivative `∇`,
`∇²f(X, X)(x₀) ≥ 0` for every vector field `X` differentiable at `x₀`. At a critical point the
connection term `(∇_X X) f` vanishes, and what remains is `D²f(X x₀, X x₀)`. -/
theorem hessianFun_nonneg_of_isLocalMin_model {f : E → ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    {X : E → E} {X' : E →L[ℝ] E} (hX : HasFDerivAt X X' x₀) :
    0 ≤ cov.hessianFun f X X x₀ := by
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x₀) x₀ :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have h0 : fderiv ℝ f x₀ = 0 := hmin.fderiv_eq_zero
  have hprod : HasFDerivAt (fun y ↦ fderiv ℝ f y (X y))
      ((fderiv ℝ f x₀).comp X' + (fderiv ℝ (fderiv ℝ f) x₀).flip (X x₀)) x₀ :=
    hDf.clm_apply hX
  simp only [hessianFun, VectorField.mvfderiv_eq_fderiv]
  show 0 ≤ fderiv ℝ (fun y ↦ fderiv ℝ f y (X y)) x₀ (X x₀) - fderiv ℝ f x₀ (cov X x₀ (X x₀))
  have h1 : fderiv ℝ f x₀ (cov X x₀ (X x₀)) = 0 := by rw [h0]; rfl
  have h2 : fderiv ℝ f x₀ (X' (X x₀)) = 0 := by rw [h0]; rfl
  rw [hprod.fderiv, h1, sub_zero, add_apply, ContinuousLinearMap.comp_apply,
    h2, zero_add, ContinuousLinearMap.flip_apply]
  exact fderiv2_nonneg_of_isLocalMin hf hmin (X x₀)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- On the model space, the extension of a tangent vector to a section is the constant
section. -/
theorem extend_model_space {x : E} (v : TangentSpace 𝓘(ℝ, E) x) (y : E) :
    (FiberBundle.extend E v : Π y : E, TangentSpace 𝓘(ℝ, E) y) y = v := by
  have hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet := by
    simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
  simp only [FiberBundle.extend]
  rw [← (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL_apply (R := ℝ) hy,
    TangentBundle.symmL_model_space]
  simp only [trivializationAt_model_space_apply]
  rfl

variable [RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)]

omit [CompleteSpace E] in
-- BENCH: laplacian-nonneg-min
/-- **The Laplacian is nonnegative at a local minimum** (model space): the trace of a
nonnegative Hessian. This is the hypothesis the abstract maximum principle
(`MaximumPrinciple.le_of_deriv_ge_at_min`) asks for at a spatial minimum. -/
theorem laplacianFun_nonneg_of_isLocalMin_model {f : E → ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) :
    0 ≤ cov.laplacianFun f x₀ := by
  unfold laplacianFun
  refine Finset.sum_nonneg fun i _ ↦ ?_
  have hc : HasFDerivAt ((FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x₀) i)
      : Π y : E, TangentSpace 𝓘(ℝ, E) y) : E → E) (0 : E →L[ℝ] E) x₀ := by
    have : ((FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x₀) i)
        : Π y : E, TangentSpace 𝓘(ℝ, E) y) : E → E) =
        fun _ ↦ stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x₀) i := by
      funext y
      exact extend_model_space _ y
    rw [this]
    exact hasFDerivAt_const _ _
  exact hessianFun_nonneg_of_isLocalMin_model cov hf hmin hc

end ModelSpace

end RicciFlowBlueprint
