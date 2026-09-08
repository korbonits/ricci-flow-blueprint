/-
**The Bochner identity for the rough Laplacian.**

For a metric connection, `Δ⟪σ,τ⟫ = ⟪Δσ,τ⟫ + ⟪σ,Δτ⟫ + 2∑ᵢ⟪∇_{eᵢ}σ, ∇_{eᵢ}τ⟫`. The
pointwise statement behind it is the Hessian version,

  `∇²⟪σ,τ⟫(X,Y) = ⟪∇²_{X,Y}σ, τ⟫ + ⟪σ, ∇²_{X,Y}τ⟫ + ⟪∇_Yσ, ∇_Xτ⟫ + ⟪∇_Xσ, ∇_Yτ⟫`,

which is metric compatibility applied twice: once to differentiate `⟪σ,τ⟫` along `Y`, and
once to differentiate the result along `X`. The correction `−(∇_X Y)⟪σ,τ⟫` in the Hessian
is precisely what turns the two second-derivative terms into `∇²σ` and `∇²τ` rather than
bare iterated derivatives.

The trace is taken over the frame `laplacian` and `laplacianFun` are themselves defined
on --- the canonical extensions of the standard orthonormal basis of `T_xM` --- so no
frame-independence is needed as an input. It comes out as a *corollary*: the other three
terms of the identity are frame-free, so `∑ᵢ⟪∇_{eᵢ}σ, ∇_{eᵢ}τ⟫` must be too.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Bianchi
import RicciFlowBlueprint.CurvaturePointwise
import RicciFlowBlueprint.Hessian

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

variable {σ τ X Y : Π y : M, TangentSpace I y} {x : M}

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- `MDifferentiableAt.inner_bundle` restated for the tangent bundle. Applying the general
version directly infers the wrong fibre instances (lean4#14949); this is the
`MDifferentiableAt` counterpart of `ContMDiffAt.inner_bundle'`. -/
lemma _root_.MDifferentiableAt.inner_bundle' {V W : Π y : M, TangentSpace I y} {x : M}
    (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    MDiffAt (fun y ↦ ⟪V y, W y⟫) x :=
  MDifferentiableAt.inner_bundle (E := fun y : M ↦ TangentSpace I y) hV hW

omit [CompleteSpace E] in
-- BENCH: bochner-hessian
/-- **The Bochner identity, Hessian form**: for a metric connection,
`∇²⟪σ,τ⟫(X,Y) = ⟪∇²_{X,Y}σ, τ⟫ + ⟪σ, ∇²_{X,Y}τ⟫ + ⟪∇_Yσ, ∇_Xτ⟫ + ⟪∇_Xσ, ∇_Yτ⟫`.

Metric compatibility twice. The Hessian's correction term `−(∇_XY)⟪σ,τ⟫` expands, again by
metric compatibility, into exactly the two corrections that turn the iterated derivatives
into `∇²σ` and `∇²τ`. -/
theorem hessianFun_inner_eq
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hσ : CMDiff 2 (T% σ)) (hτ : CMDiff 2 (T% τ)) (hY : MDiffAt (T% Y) x) :
    cov.hessianFun (fun y ↦ ⟪σ y, τ y⟫) X Y x
      = ⟪cov.hessian X Y σ x, τ x⟫ + ⟪σ x, cov.hessian X Y τ x⟫
        + ⟪cov σ x (Y x), cov τ x (X x)⟫ + ⟪cov σ x (X x), cov τ x (Y x)⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hσm : ∀ y, MDiffAt (T% σ) y := hσ.mdifferentiable h2
  have hτm : ∀ y, MDiffAt (T% τ) y := hτ.mdifferentiable h2
  -- `∇_Yσ` and `∇_Yτ` are differentiable at `x`
  have hDσ : MDiffAt (T% (fun y ↦ cov σ y (Y y))) x := cov.mdiffAt_cov_apply hσ hY
  have hDτ : MDiffAt (T% (fun y ↦ cov τ y (Y y))) x := cov.mdiffAt_cov_apply hτ hY
  -- the first derivative of `⟪σ,τ⟫` along `Y`, as a function
  have hinner : (fun y ↦ mvfderiv I (fun z ↦ ⟪σ z, τ z⟫) y (Y y))
      = fun y ↦ ⟪cov σ y (Y y), τ y⟫ + ⟪σ y, cov τ y (Y y)⟫ := by
    funext y
    exact hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) Y (hσm y) (hτm y)
  -- the two summands are differentiable at `x`
  have hA : MDiffAt (fun y ↦ ⟪cov σ y (Y y), τ y⟫) x := hDσ.inner_bundle' (hτm x)
  have hB : MDiffAt (fun y ↦ ⟪σ y, cov τ y (Y y)⟫) x := (hσm x).inner_bundle' hDτ
  -- differentiate each along `X`
  have hAX := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X hDσ (hτm x)
  have hBX := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X (hσm x) hDτ
  -- the Hessian's correction term, expanded along the field `∇_X Y`
  have hcorr := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y)
    (fun y ↦ cov Y y (X y)) (hσm x) (hτm x)
  simp only [hessianFun, hinner, mvfderiv_fun_add hA hB, _root_.add_apply, hAX, hBX, hcorr,
    hessian, inner_sub_left, inner_sub_right]
  ring

omit [CompleteSpace E] in
-- BENCH: bochner-laplacian
/-- **The Bochner identity**: for a metric connection,
`Δ⟪σ,τ⟫ = ⟪Δσ, τ⟫ + ⟪σ, Δτ⟫ + 2∑ᵢ⟪∇_{eᵢ}σ, ∇_{eᵢ}τ⟫`.

The trace of `hessianFun_inner_eq` over the frame `laplacian` and `laplacianFun` are
themselves defined on, so no frame-independence is needed as an input. The two cross terms
of the Hessian identity coincide when `X = Y`, which is where the factor `2` comes from. -/
theorem laplacianFun_inner_eq
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hσ : CMDiff 2 (T% σ)) (hτ : CMDiff 2 (T% τ)) :
    cov.laplacianFun (fun y ↦ ⟪σ y, τ y⟫) x
      = ⟪cov.laplacian hσ x, τ x⟫ + ⟪σ x, cov.laplacian hτ x⟫
        + 2 * ∑ i, ⟪cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i),
            cov τ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)⟫ := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  have hfrm : ∀ i, MDiffAt (T% (FiberBundle.extend E
      (stdOrthonormalBasis ℝ (TangentSpace I x) i))) x := fun _ ↦ FiberBundle.mdifferentiableAt_extend ..
  have hfrv : ∀ i, FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i) x
      = stdOrthonormalBasis ℝ (TangentSpace I x) i := fun _ ↦ FiberBundle.extend_apply_self ..
  have hlapσ : cov.laplacian hσ x = ∑ i, cov.hessian
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) σ x :=
    cov.laplacian_eq_sum_frame hσ hfrm _ hfrv
  have hlapτ : cov.laplacian hτ x = ∑ i, cov.hessian
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
      (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) τ x :=
    cov.laplacian_eq_sum_frame hτ hfrm _ hfrv
  rw [laplacianFun, hlapσ, hlapτ, sum_inner, inner_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cov.hessianFun_inner_eq hmet hσ hτ (hfrm i), hfrv i]
  ring

omit [CompleteSpace E] in
/-- **The Bochner identity for the squared norm**:
`Δ|σ|² = 2⟪Δσ, σ⟫ + 2∑ᵢ|∇_{eᵢ}σ|²`. The gradient term is a sum of squares, so `Δ|σ|² ≥
2⟪Δσ, σ⟫` --- which is the form maximum-principle arguments use. -/
theorem laplacianFun_inner_self_eq
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hσ : CMDiff 2 (T% σ)) :
    cov.laplacianFun (fun y ↦ ⟪σ y, σ y⟫) x
      = 2 * ⟪cov.laplacian hσ x, σ x⟫
        + 2 * ∑ i, ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2 := by
  rw [cov.laplacianFun_inner_eq hmet hσ hσ]
  have e : ⟪σ x, cov.laplacian hσ x⟫ = ⟪cov.laplacian hσ x, σ x⟫ := real_inner_comm _ _
  rw [e]
  have e2 : ∀ i, ⟪cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i),
      cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)⟫
      = ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2 := fun i ↦
    real_inner_self_eq_norm_sq _
  simp only [e2]
  ring

omit [CompleteSpace E] in
/-- **`Δ|σ|² ≥ 2⟪Δσ, σ⟫`**, the form the maximum principle consumes: the gradient term of
the Bochner identity is a sum of squares. -/
theorem two_mul_inner_laplacian_le
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hσ : CMDiff 2 (T% σ)) :
    2 * ⟪cov.laplacian hσ x, σ x⟫ ≤ cov.laplacianFun (fun y ↦ ⟪σ y, σ y⟫) x := by
  rw [cov.laplacianFun_inner_self_eq hmet hσ]
  have hnn : (0 : ℝ) ≤ ∑ i, ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov 1] in
/-- **The gradient pairing `∑ᵢ ⟪∇_{eᵢ}σ, ∇_{eᵢ}τ⟫` does not depend on the frame.** It is
the metric trace of `(v,w) ↦ ⟪∇_v σ, ∇_w τ⟫`, which is a genuine continuous bilinear form
because `∇σ` and `∇τ` are continuous linear maps at each point --- so this needs neither
metric compatibility nor the Bochner identity. -/
theorem sum_inner_cov_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (c : OrthonormalBasis κ ℝ (TangentSpace I x)) :
    ∑ i, ⟪cov σ x (b i), cov τ x (b i)⟫ = ∑ j, ⟪cov σ x (c j), cov τ x (c j)⟫ :=
  OrthonormalBasis.sum_apply_self_eq b c
    ((((innerSL ℝ).comp (cov σ x)).flip.comp (cov τ x)).flip)

end CovariantDerivative
