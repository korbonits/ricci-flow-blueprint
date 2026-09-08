/-
Differentiating the Koszul combination once more.

The first variation of the connection along a family of metrics is a `(1,2)`-tensor `A`
characterised by the Koszul combination of `h = ∂ₜ g` (`Variation.lean`,
`CurvatureVariation.lean`):

  `⟪A(P,Q), R⟫ = ½[(∇_P h)(Q,R) + (∇_Q h)(R,P) − (∇_R h)(P,Q)]`.

Differentiating covariantly once more, for a **metric** connection, gives the same combination
one level up, with `∇h` replaced by `∇²h` and **no curvature terms**:

  `⟪(∇_U A)(P,Q), R⟫ = ½[(∇²_{U,P}h)(Q,R) + (∇²_{U,Q}h)(R,P) − (∇²_{U,R}h)(P,Q)]`.

This is what turns `∂ₜ Rm = (∇ A)(·,·) − (∇ A)(·,·)` into a statement about `∇²h`, and hence
`tr_g(∂ₜ Ric)` into `div div h − Δ(tr_g h)`.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.BilinLaplacian
import RicciFlowBlueprint.Bianchi
import RicciFlowBlueprint.Bochner
import RicciFlowBlueprint.OneForm

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- The **covariant derivative of a `(1,2)`-tensor field**:
`(∇_U A)(P,Q) = ∇_U(A(P,Q)) − A(∇_U P, Q) − A(P, ∇_U Q)`. -/
noncomputable def covTwoTensor
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
    (U P Q : Π y : M, TangentSpace I y) (x : M) : TangentSpace I x :=
  cov (fun y ↦ A y (P y) (Q y)) x (U x) - A x (cov P x (U x)) (Q x)
    - A x (P x) (cov Q x (U x))

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1]

variable {h : M → E →L[ℝ] E →L[ℝ] ℝ}
  {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}

/-- The Koszul characterisation of `A` in terms of `h`, as a hypothesis: this is what
`inner_derivDifferenceE_eq` supplies for `A = ∂ₜ∇`. It is asserted on `C¹` fields, which is
what makes both sides depend on the same data. -/
def IsKoszulOf (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
    (h : M → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 1 (T% P) → CMDiff 1 (T% Q) → CMDiff 1 (T% R) →
    ∀ y : M, ⟪A y (P y) (Q y), R y⟫
      = (cov.covBilin h P Q R y + cov.covBilin h Q R P y - cov.covBilin h R P Q y) / 2

omit [CompleteSpace E] in
-- BENCH: koszul-second-derivative
/-- **Differentiating the Koszul combination**: for a metric connection,
`⟪(∇_U A)(P,Q), R⟫ = ½[(∇²_{U,P}h)(Q,R) + (∇²_{U,Q}h)(R,P) − (∇²_{U,R}h)(P,Q)]`.

The same combination one level up, with **no curvature terms**: metric compatibility moves
`∇_U` onto the pairing, the germ identity differentiates the three `∇h`-terms into
`∇²h`-terms, and the nine correction terms regroup into exactly the three `A`-corrections that
`∇_U A` subtracts. -/
theorem inner_covTwoTensor_eq (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hA : cov.IsKoszulOf A h) {U P Q R : Π y : M, TangentSpace I y} {x : M}
    (hU : CMDiff 1 (T% U)) (hP : CMDiff 2 (T% P)) (hQ : CMDiff 2 (T% Q))
    (hR : CMDiff 2 (T% R))
    (hAPQ : MDiffAt (T% (fun y ↦ A y (P y) (Q y))) x)
    (hd₁ : MDiffAt (fun y ↦ cov.covBilin h P Q R y) x)
    (hd₂ : MDiffAt (fun y ↦ cov.covBilin h Q R P y) x)
    (hd₃ : MDiffAt (fun y ↦ cov.covBilin h R P Q y) x) :
    ⟪cov.covTwoTensor A U P Q x, R x⟫
      = (cov.cov2Bilin h U P Q R x + cov.cov2Bilin h U Q R P x
          - cov.cov2Bilin h U R P Q x) / 2 := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hP1 : CMDiff 1 (T% P) := hP.of_le (by norm_num)
  have hQ1 : CMDiff 1 (T% Q) := hQ.of_le (by norm_num)
  have hR1 : CMDiff 1 (T% R) := hR.of_le (by norm_num)
  have hDP : CMDiff 1 (T% (fun y ↦ cov P y (U y))) := cov.contMDiff_cov_apply
    (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hP) hU
  have hDQ : CMDiff 1 (T% (fun y ↦ cov Q y (U y))) := cov.contMDiff_cov_apply
    (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hQ) hU
  have hDR : CMDiff 1 (T% (fun y ↦ cov R y (U y))) := cov.contMDiff_cov_apply
    (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hR) hU
  -- metric compatibility moves `∇_U` onto the pairing
  have hmet : mvfderiv I (fun y ↦ ⟪A y (P y) (Q y), R y⟫) x (U x)
      = ⟪cov (fun y ↦ A y (P y) (Q y)) x (U x), R x⟫
        + ⟪(fun y ↦ A y (P y) (Q y)) x, cov R x (U x)⟫ :=
    hcov.mvfderiv_inner_eq U hAPQ (hR1.mdifferentiable h1 x)
  -- the germ identity, differentiated
  have hF : MDiffAt (fun y ↦ ⟪A y (P y) (Q y), R y⟫) x :=
    hAPQ.inner_bundle' (hR1.mdifferentiable h1 x)
  have hgerm : (fun y ↦ cov.covBilin h P Q R y + cov.covBilin h Q R P y
      - cov.covBilin h R P Q y) = fun y ↦ 2 * ⟪A y (P y) (Q y), R y⟫ := by
    funext y
    rw [hA P Q R hP1 hQ1 hR1 y]
    ring
  have hsum : mvfderiv I (fun y ↦ cov.covBilin h P Q R y + cov.covBilin h Q R P y
        - cov.covBilin h R P Q y) x (U x)
      = mvfderiv I (fun y ↦ cov.covBilin h P Q R y) x (U x)
        + mvfderiv I (fun y ↦ cov.covBilin h Q R P y) x (U x)
        - mvfderiv I (fun y ↦ cov.covBilin h R P Q y) x (U x) := by
    have hadd : MDiffAt (fun y ↦ cov.covBilin h P Q R y + cov.covBilin h Q R P y) x :=
      hd₁.add hd₂
    rw [mvfderiv_fun_sub hadd hd₃, mvfderiv_fun_add hd₁ hd₂]
    simp only [_root_.sub_apply, _root_.add_apply]
  have hder : mvfderiv I (fun y ↦ cov.covBilin h P Q R y + cov.covBilin h Q R P y
        - cov.covBilin h R P Q y) x (U x)
      = 2 * mvfderiv I (fun y ↦ ⟪A y (P y) (Q y), R y⟫) x (U x) := by
    rw [hgerm, mvfderiv_fun_mul mdifferentiableAt_const hF, mvfderiv_const]
    simp only [_root_.smul_apply, smul_eq_mul, smul_zero, add_zero]
  -- the three corrections `∇_U A` subtracts, each by the Koszul identity
  have k₁ : ⟪A x (cov P x (U x)) (Q x), R x⟫
      = (cov.covBilin h (fun y ↦ cov P y (U y)) Q R x
          + cov.covBilin h Q R (fun y ↦ cov P y (U y)) x
          - cov.covBilin h R (fun y ↦ cov P y (U y)) Q x) / 2 :=
    hA _ Q R hDP hQ1 hR1 x
  have k₂ : ⟪A x (P x) (cov Q x (U x)), R x⟫
      = (cov.covBilin h P (fun y ↦ cov Q y (U y)) R x
          + cov.covBilin h (fun y ↦ cov Q y (U y)) R P x
          - cov.covBilin h R P (fun y ↦ cov Q y (U y)) x) / 2 :=
    hA P _ R hP1 hDQ hR1 x
  have k₃ : ⟪A x (P x) (Q x), cov R x (U x)⟫
      = (cov.covBilin h P Q (fun y ↦ cov R y (U y)) x
          + cov.covBilin h Q (fun y ↦ cov R y (U y)) P x
          - cov.covBilin h (fun y ↦ cov R y (U y)) P Q x) / 2 :=
    hA P Q _ hP1 hQ1 hDR x
  -- assemble
  have hlhs : ⟪cov.covTwoTensor A U P Q x, R x⟫
      = ⟪cov (fun y ↦ A y (P y) (Q y)) x (U x), R x⟫
        - ⟪A x (cov P x (U x)) (Q x), R x⟫ - ⟪A x (P x) (cov Q x (U x)), R x⟫ := by
    rw [covTwoTensor]
    rw [inner_sub_left, inner_sub_left]
  have e₁ : cov.cov2Bilin h U P Q R x
      = mvfderiv I (fun y ↦ cov.covBilin h P Q R y) x (U x)
        - cov.covBilin h (fun y ↦ cov P y (U y)) Q R x
        - cov.covBilin h P (fun y ↦ cov Q y (U y)) R x
        - cov.covBilin h P Q (fun y ↦ cov R y (U y)) x := rfl
  have e₂ : cov.cov2Bilin h U Q R P x
      = mvfderiv I (fun y ↦ cov.covBilin h Q R P y) x (U x)
        - cov.covBilin h (fun y ↦ cov Q y (U y)) R P x
        - cov.covBilin h Q (fun y ↦ cov R y (U y)) P x
        - cov.covBilin h Q R (fun y ↦ cov P y (U y)) x := rfl
  have e₃ : cov.cov2Bilin h U R P Q x
      = mvfderiv I (fun y ↦ cov.covBilin h R P Q y) x (U x)
        - cov.covBilin h (fun y ↦ cov R y (U y)) P Q x
        - cov.covBilin h R (fun y ↦ cov P y (U y)) Q x
        - cov.covBilin h R P (fun y ↦ cov Q y (U y)) x := rfl
  rw [hlhs]
  linarith [hmet, hsum, hder, k₁, k₂, k₃, e₁, e₂, e₃]

omit [CompleteSpace E] in
-- BENCH: koszul-double-trace
/-- **The double trace of the Koszul curvature.** For a metric connection, a *symmetric* `h`
and `A` Koszul for `h`, the object `Rm_A(X,Y)Z = (∇_X A)(Y,Z) − (∇_Y A)(X,Z)` --- which is what
`∂ₜ Rm` equals along a family of metrics --- has Ricci-type double trace
\[
  ∑_{i,j} ⟪Rm_A(e_i,e_j)e_j, e_i⟫
    = ∑_{i,j} (∇²_{e_i,e_j}h)(e_j,e_i) - ∑_{i,j} (∇²_{e_i,e_i}h)(e_j,e_j),
\]
the two canonical double traces of `∇²h`: `div div h` and `tr_g(Δ_g h)`. **No curvature terms
appear at any stage.** Symmetry of `h` is what collapses the six sums to two: it identifies
`(∇²_{U,a}h)(b,c)` with `(∇²_{U,a}h)(c,b)`, which merges the first two terms of each Koszul
combination. -/
theorem sum_inner_covTwoTensor_eq
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (hA : cov.IsKoszulOf A h)
    (hsymm : ∀ (y : M) (v w : E), h y v w = h y w v)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y} {x : M}
    (hfr : ∀ i, CMDiff 2 (T% (fr i)))
    (hAf : ∀ i j, MDiffAt (T% (fun y ↦ A y (fr i y) (fr j y))) x)
    (hd : ∀ a b c, MDiffAt (fun y ↦ cov.covBilin h (fr a) (fr b) (fr c) y) x) :
    ∑ i, ∑ j, (⟪cov.covTwoTensor A (fr i) (fr j) (fr j) x, fr i x⟫
        - ⟪cov.covTwoTensor A (fr j) (fr i) (fr j) x, fr i x⟫)
      = (∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr j) (fr j) (fr i) x)
        - ∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x := by
  have hfr1 : ∀ i, CMDiff 1 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  -- the pointwise reduction: each pair of Koszul combinations collapses by symmetry
  have key : ∀ i j, ⟪cov.covTwoTensor A (fr i) (fr j) (fr j) x, fr i x⟫
      - ⟪cov.covTwoTensor A (fr j) (fr i) (fr j) x, fr i x⟫
      = cov.cov2Bilin h (fr i) (fr j) (fr j) (fr i) x
        - cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x / 2
        - cov.cov2Bilin h (fr j) (fr j) (fr i) (fr i) x / 2 := by
    intro i j
    have e₁ := cov.inner_covTwoTensor_eq hcov hA (hfr1 i) (hfr j) (hfr j) (hfr i)
      (hAf j j) (hd j j i) (hd j i j) (hd i j j)
    have e₂ := cov.inner_covTwoTensor_eq hcov hA (hfr1 j) (hfr i) (hfr j) (hfr i)
      (hAf i j) (hd i j i) (hd j i i) (hd i i j)
    have s₁ : cov.cov2Bilin h (fr i) (fr j) (fr i) (fr j) x
        = cov.cov2Bilin h (fr i) (fr j) (fr j) (fr i) x :=
      cov.cov2Bilin_symm hsymm _ _ _ _ x
    have s₂ : cov.cov2Bilin h (fr j) (fr i) (fr j) (fr i) x
        = cov.cov2Bilin h (fr j) (fr i) (fr i) (fr j) x :=
      cov.cov2Bilin_symm hsymm _ _ _ _ x
    rw [e₁, e₂, s₁, s₂]
    ring
  -- sum, and fold the two copies of `tr_g(Δ_g h)` together
  have hswap : ∑ i, ∑ j, cov.cov2Bilin h (fr j) (fr j) (fr i) (fr i) x
      = ∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x := Finset.sum_comm
  calc ∑ i, ∑ j, (⟪cov.covTwoTensor A (fr i) (fr j) (fr j) x, fr i x⟫
        - ⟪cov.covTwoTensor A (fr j) (fr i) (fr j) x, fr i x⟫)
      = ∑ i, ∑ j, (cov.cov2Bilin h (fr i) (fr j) (fr j) (fr i) x
          - cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x / 2
          - cov.cov2Bilin h (fr j) (fr j) (fr i) (fr i) x / 2) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ key i j
    _ = (∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr j) (fr j) (fr i) x)
          - (∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x) / 2
          - (∑ i, ∑ j, cov.cov2Bilin h (fr j) (fr j) (fr i) (fr i) x) / 2 := by
        simp only [Finset.sum_sub_distrib, Finset.sum_div]
    _ = (∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr j) (fr j) (fr i) x)
          - ∑ i, ∑ j, cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x := by
        rw [hswap]; ring

section Named

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]

omit [CompleteSpace E] in
-- BENCH: koszul-double-trace-named
/-- **`tr_g(∂ₜ Ric) = div div h − tr_g(Δ_g h)`, in the abstract.** The previous lemma's two
canonical double traces of `∇²h` named: the first is the double divergence `divDivBilin`, the
second the metric trace of the connection Laplacian `laplacianBilin`. Specialised to `A = ∂ₜ∇` and `h = ∂ₜ g` this
is the first variation of the scalar curvature with no curvature terms; under the Ricci flow
`h = −2 Ric` and the two contracted Bianchi identities turn the right-hand side into
`Δ scal`. -/
theorem sum_inner_covTwoTensor_eq_divDiv
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (hA : cov.IsKoszulOf A h)
    (hsymm : ∀ (y : M) (v w : E), h y v w = h y w v)
    (hbg : IsMDiffBilin (I := I) h)
    (hw : IsMDiffOneFormAt (I := I) (cov.divBilinOneForm h hbg) x)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (b : OrthonormalBasis iota ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i)
    (hfr : ∀ i, CMDiff 2 (T% (fr i)))
    (hcb : ∀ i, cov.IsMDiffCovBilinAt h (fr i) (fr i) x)
    (hAf : ∀ i j, MDiffAt (T% (fun y ↦ A y (fr i y) (fr j y))) x)
    (hd : ∀ a b c, MDiffAt (fun y ↦ cov.covBilin h (fr a) (fr b) (fr c) y) x) :
    ∑ i, ∑ j, (⟪cov.covTwoTensor A (fr i) (fr j) (fr j) x, fr i x⟫
        - ⟪cov.covTwoTensor A (fr j) (fr i) (fr j) x, fr i x⟫)
      = cov.divDivBilin h hbg x - ∑ j, cov.laplacianBilin h (fr j) (fr j) x := by
  rw [cov.sum_inner_covTwoTensor_eq hcov hA hsymm hfr hAf hd,
    cov.divDivBilin_eq_sum hcov hbg hw hs hu hx hfr (fun j i ↦ hd i i j) b hbv]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦
    (cov.laplacianBilin_eq_sum_frame (hbg x) (hcb j) (hfr j) (hfr j) hfr b hbv).symm

end Named

end CovariantDerivative
