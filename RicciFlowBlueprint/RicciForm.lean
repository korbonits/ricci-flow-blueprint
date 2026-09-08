/-
The Ricci tensor as a bilinear form, and the scalar curvature, on a general manifold.

`CurvaturePointwise.lean` makes `Ric(X,Y)(x)` depend on `X x` and `Y x` alone
(`ricci_congr_of_eq`) and packages that as `ricciAt x : T_xM → T_xM → ℝ`. Here that
function is shown to be **bilinear** — each slot's linearity is read off the field-level
statements (`ricci_add_left`, `ricci_smul_left`, `ricci_add_right`,
`ricci_smul_const_right`) applied to globally `C²` extensions, which exist by
`exists_contMDiff_two_extension` — so it bundles as a continuous bilinear form
`ricciForm x : E →L[ℝ] E →L[ℝ] ℝ`.

The scalar curvature is then its metric trace, `scal(x) = ∑ᵢ Ric(eᵢ, eᵢ)` over an
orthonormal basis of `T_xM`, and **frame-independence is free**: it is the purely
algebraic `OrthonormalBasis.sum_apply_self_eq` applied to a genuine bilinear form.
`Scalar.lean`'s `scalarCurvatureWith_congr` had to assume pointwise dependence of the
curvature's third slot in a form (`MDiffAt` in the first slot) that
`curvature_congr_third` does not supply; going through the bilinear form avoids the
hypothesis altogether, and `scalarCurvatureAt_eq_scalarCurvatureWith` transfers the
conclusion back.

This closes the gap recorded in `CLAUDE.md` as "the scalar curvature is on the model
space only".

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvaturePointwise
import RicciFlowBlueprint.Hessian
import RicciFlowBlueprint.TraceCov

open Bundle Filter Module
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

open RicciFlowBlueprint

set_option maxSynthPendingDepth 3

section Bilinear

variable {x : M}

private theorem two_ne_zero' : (2 : ℕ∞ω) ≠ 0 := by norm_num

omit [CompleteSpace E] in
/-- `Ric(·, w)` is additive. -/
theorem ricciAt_add_left (v v' w : TangentSpace I x) :
    cov.ricciAt x (v + v') w = cov.ricciAt x v w + cov.ricciAt x v' w := by
  obtain ⟨V, hV, hVv⟩ := exists_contMDiff_two_extension v
  obtain ⟨V', hV', hV'v⟩ := exists_contMDiff_two_extension v'
  obtain ⟨W, hW, hWw⟩ := exists_contMDiff_two_extension w
  have hsum : CMDiff 2 (T% (V + V')) := hV.add_section hV'
  have hval : (V + V') x = v + v' := by
    show V x + V' x = v + v'
    rw [hVv, hV'v]
  calc cov.ricciAt x (v + v') w
      = cov.ricciAt x ((V + V') x) (W x) := by rw [hval, hWw]
    _ = cov.ricci (V + V') W x := cov.ricciAt_eq hsum hW
    _ = cov.ricci V W x + cov.ricci V' W x :=
        cov.ricci_add_left hW ((hV.mdifferentiable two_ne_zero') x)
          ((hV'.mdifferentiable two_ne_zero') x)
    _ = cov.ricciAt x v w + cov.ricciAt x v' w := by
        rw [← cov.ricciAt_eq hV hW, ← cov.ricciAt_eq hV' hW, hVv, hV'v, hWw]

omit [CompleteSpace E] in
/-- `Ric(·, w)` is homogeneous. -/
theorem ricciAt_smul_left (c : ℝ) (v w : TangentSpace I x) :
    cov.ricciAt x (c • v) w = c * cov.ricciAt x v w := by
  obtain ⟨V, hV, hVv⟩ := exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := exists_contMDiff_two_extension w
  have hsmul : CMDiff 2 (T% (c • V)) := hV.const_smul_section
  have hval : (c • V) x = c • v := by
    show c • V x = c • v
    rw [hVv]
  have hfun : ((fun _ : M ↦ c) • V) = c • V := rfl
  calc cov.ricciAt x (c • v) w
      = cov.ricciAt x ((c • V) x) (W x) := by rw [hval, hWw]
    _ = cov.ricci (c • V) W x := cov.ricciAt_eq hsmul hW
    _ = cov.ricci ((fun _ : M ↦ c) • V) W x := by rw [hfun]
    _ = c * cov.ricci V W x :=
        cov.ricci_smul_left hW mdifferentiableAt_const ((hV.mdifferentiable two_ne_zero') x)
    _ = c * cov.ricciAt x v w := by rw [← cov.ricciAt_eq hV hW, hVv, hWw]

omit [CompleteSpace E] in
/-- `Ric(v, ·)` is additive. -/
theorem ricciAt_add_right (v w w' : TangentSpace I x) :
    cov.ricciAt x v (w + w') = cov.ricciAt x v w + cov.ricciAt x v w' := by
  obtain ⟨V, hV, hVv⟩ := exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := exists_contMDiff_two_extension w
  obtain ⟨W', hW', hW'w⟩ := exists_contMDiff_two_extension w'
  have hsum : CMDiff 2 (T% (W + W')) := hW.add_section hW'
  have hval : (W + W') x = w + w' := by
    show W x + W' x = w + w'
    rw [hWw, hW'w]
  calc cov.ricciAt x v (w + w')
      = cov.ricciAt x (V x) ((W + W') x) := by rw [hval, hVv]
    _ = cov.ricci V (W + W') x := cov.ricciAt_eq hV hsum
    _ = cov.ricci V W x + cov.ricci V W' x :=
        cov.ricci_add_right hW hW' ((hV.mdifferentiable two_ne_zero') x)
    _ = cov.ricciAt x v w + cov.ricciAt x v w' := by
        rw [← cov.ricciAt_eq hV hW, ← cov.ricciAt_eq hV hW', hVv, hWw, hW'w]

omit [CompleteSpace E] in
/-- `Ric(v, ·)` is homogeneous. -/
theorem ricciAt_smul_right (c : ℝ) (v w : TangentSpace I x) :
    cov.ricciAt x v (c • w) = c * cov.ricciAt x v w := by
  obtain ⟨V, hV, hVv⟩ := exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := exists_contMDiff_two_extension w
  have hsmul : CMDiff 2 (T% (c • W)) := hW.const_smul_section
  have hval : (c • W) x = c • w := by
    show c • W x = c • w
    rw [hWw]
  calc cov.ricciAt x v (c • w)
      = cov.ricciAt x (V x) ((c • W) x) := by rw [hval, hVv]
    _ = cov.ricci V (c • W) x := cov.ricciAt_eq hV hsmul
    _ = c * cov.ricci V W x :=
        cov.ricci_smul_const_right c hW ((hV.mdifferentiable two_ne_zero') x)
    _ = c * cov.ricciAt x v w := by rw [← cov.ricciAt_eq hV hW, hVv, hWw]

-- BENCH: ricci-form
/-- **The Ricci tensor as a continuous bilinear form on `T_xM`**, on a general manifold.
Bilinearity is `ricciAt_add_left` and friends; continuity is automatic in finite
dimension. -/
noncomputable def ricciForm (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun v w ↦ cov.ricciAt x v w)
        (fun v v' w ↦ cov.ricciAt_add_left v v' w)
        (fun c v w ↦ by rw [smul_eq_mul]; exact cov.ricciAt_smul_left c v w)
        (fun v w w' ↦ cov.ricciAt_add_right v w w')
        (fun c v w ↦ by rw [smul_eq_mul]; exact cov.ricciAt_smul_right c v w))

omit [CompleteSpace E] in
theorem ricciForm_apply (v w : TangentSpace I x) :
    cov.ricciForm x v w = cov.ricciAt x v w := rfl

omit [CompleteSpace E] in
/-- The Ricci form computes `ricci` on any globally `C²` fields. -/
theorem ricciForm_apply_field {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) :
    cov.ricciForm x (X x) (Y x) = cov.ricci X Y x :=
  cov.ricciAt_eq hX hY

end Bilinear

section Scalar

variable {x : M}

/-- **The scalar curvature on a general manifold**: the metric trace of the Ricci form,
`scal(x) = ∑ᵢ Ric(eᵢ, eᵢ)` over an orthonormal basis of `T_xM`. The definition uses the
standard basis; `scalarCurvatureAt_eq_sum_basis` shows every orthonormal basis gives the
same value. -/
-- BENCH: scalar-manifold-def
noncomputable def scalarCurvatureAt (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.ricciForm x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

omit [CompleteSpace E] in
-- BENCH: scalar-well-defined-manifold
/-- **Well-definedness of the scalar curvature on a general manifold**, hypothesis-free:
the trace of a genuine bilinear form does not depend on the orthonormal basis. -/
theorem scalarCurvatureAt_eq_sum_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.scalarCurvatureAt x = ∑ i, cov.ricciAt x (b i) (b i) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  exact OrthonormalBasis.sum_apply_self_eq _ b (cov.ricciForm x)

omit [CompleteSpace E] in
/-- The scalar curvature as a sum over any `C²` frame whose values at `x` are an
orthonormal basis --- which is `Scalar.lean`'s `scalarCurvatureWith`, so this is
frame-independence of that sum on a general manifold, with no hypothesis on the
curvature's third slot. -/
theorem scalarCurvatureAt_eq_scalarCurvatureWith {ι : Type*} [Fintype ι]
    {b : ι → Π y : M, TangentSpace I y} (hb : ∀ i, CMDiff 2 (T% (b i)))
    (v : OrthonormalBasis ι ℝ (TangentSpace I x)) (hbv : ∀ i, b i x = v i) :
    cov.scalarCurvatureAt x = cov.scalarCurvatureWith b x := by
  rw [cov.scalarCurvatureAt_eq_sum_basis v]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hbv i, cov.ricciAt_eq (hb i) (hb i)]

omit [CompleteSpace E] in
/-- **Frame-independence of `scalarCurvatureWith` on a general manifold**, with the
hypothesis `h3` of `scalarCurvatureWith_congr` discharged. -/
theorem scalarCurvatureWith_congr' {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : ι → Π y : M, TangentSpace I y} {c : κ → Π y : M, TangentSpace I y}
    (hb : ∀ i, CMDiff 2 (T% (b i))) (hc : ∀ j, CMDiff 2 (T% (c j)))
    (v : OrthonormalBasis ι ℝ (TangentSpace I x))
    (w : OrthonormalBasis κ ℝ (TangentSpace I x))
    (hbv : ∀ i, b i x = v i) (hcw : ∀ j, c j x = w j) :
    cov.scalarCurvatureWith b x = cov.scalarCurvatureWith c x := by
  rw [← cov.scalarCurvatureAt_eq_scalarCurvatureWith hb v hbv,
    ← cov.scalarCurvatureAt_eq_scalarCurvatureWith hc w hcw]

end Scalar

section Derivative

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
-- BENCH: deriv-scalar-eq-trace-cov-ricci
/-- **`X(scal) = tr_g(∇_X Ric)`**: the derivative of the scalar curvature is the metric
trace of `∇Ric`. This is `TraceCov.lean`'s trace lemma applied to the Ricci form; the only
input beyond it is that the scalar curvature is the frame sum at every nearby point, which
is `scalarCurvatureAt_eq_sum_basis` at the orthonormal basis the frame gives there.

The remaining hypothesis is genuine regularity, not bookkeeping: `y ↦ Ric(eᵢ, eᵢ)(y)` must
be differentiable at `x`, which asks the connection for one more derivative than
`ContMDiffCovariantDerivative cov 1` supplies. -/
theorem mvfderiv_scalarCurvatureAt_eq_sum_covBilin
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X : Π y : M, TangentSpace I y} {x : M}
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hRic : ∀ i, MDiffAt (fun y ↦ cov.ricciForm y (fr i y) (fr i y)) x) :
    mvfderiv I (fun y ↦ cov.scalarCurvatureAt y) x (X x)
      = ∑ i, cov.covBilin (fun y ↦ cov.ricciForm y) X (fr i) (fr i) x := by
  have heq : (fun y ↦ cov.scalarCurvatureAt y)
      =ᶠ[𝓝 x] fun y ↦ ∑ i, cov.ricciForm y (fr i y) (fr i y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
    rw [cov.scalarCurvatureAt_eq_sum_basis b]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [hb i]; exact (cov.ricciForm_apply _ _).symm
  rw [heq.mvfderiv_eq]
  exact cov.mvfderiv_sum_eq_sum_covBilin_of_frame hcov hs hu hx hRic

end Derivative

end CovariantDerivative
