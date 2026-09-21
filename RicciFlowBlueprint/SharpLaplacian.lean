/-
**The index-raising isomorphism commutes with `∇`, `∇²` and `Δ`.**

An endomorphism field `A` of `TM` and a bilinear form field `h` related by
`⟪A v, w⟫ = h(v,w)` — index raising, `A = h♯` — have covariant derivatives related the same
way, and the relation survives both derivatives and the trace:

  `⟪(∇_X A)v, w⟫ = (∇_X h)(v,w)`,
  `⟪(∇²_{X,Y}A)v, w⟫ = (∇²_{X,Y}h)(v,w)`,
  `⟪(Δ A)v, w⟫ = (Δ_g h)(v,w)`.

**This is the bridge the dimension-three maximum principle needs.** Hamilton's curvature
operator `Rm₃ = scal·Id − 2 Ric♯` is a section of `End(TM)`, and the touching-point principle
on that bundle (`BundleMaximumPrinciple.lean`, applied in
`CurvatureOperatorMaxPrinciple.lean`) speaks of `laplacianSection`, the connection Laplacian
of `endCov`. Every evolution equation proved here, by contrast, is about *bilinear forms*:
`∂ₜRic = Δ_g Ric + Q` (`RicciEvolution.lean`) has `Δ_g Ric` on the right. Without this file
the two say nothing to each other.

**There is no `sharp` in the statements and none in the proofs.** The interface is the
hypothesis `⟪A y v, w⟫ = h y v w`, which `inner_ricciSharp` and `inner_curvatureOperator`
supply on the nose; carrying the Riesz isomorphism through the argument would only make the
rewriting harder.

**Metric compatibility is the whole content and it is used once per derivative.** `∇A` is
`∇(Aσ) − A(∇σ)` by definition; pairing the first term with `σ'` and moving `∇` onto the
pairing turns it into `X(h(σ,σ')) − h(σ,∇σ')`, and the second term is `h(∇σ,σ')` — which
is `∇h` written out. The second derivative is that argument applied twice, with the two
connection corrections matching term for term, and the trace is then free.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.HomBundle
import RicciFlowBlueprint.BilinLaplacian
import RicciFlowBlueprint.BundleHessian
import RicciFlowBlueprint.Bochner
import RicciFlowBlueprint.HomBundleSmooth
import RicciFlowBlueprint.CurvatureOperatorSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

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
  [ContMDiffVectorBundle 1 E (fun (y : M) ↦ TangentSpace I y) I]
  [ContMDiffVectorBundle 2 E (fun (y : M) ↦ TangentSpace I y) I] [T2Space M]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

variable {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {X P Q : Π y : M, TangentSpace I y} {x : M}

omit [CompleteSpace E] in
omit [ContMDiffCovariantDerivative cov 1] [ContMDiffVectorBundle 2 E (fun (y : M) ↦ TangentSpace I y) I] [T2Space M] in
/-- **Index raising commutes with `∇`**: `⟪(∇_X A)v, w⟫ = (∇_X h)(v,w)` whenever
`⟪A v, w⟫ = h(v,w)`.

`∇A` is `∇(AP) − A(∇P)` by definition. Metric compatibility moves `∇_X` off the first term
and onto the pairing, turning it into `X(h(P,Q)) − h(P, ∇_X Q)`; the second term is
`h(∇_X P, Q)`. Those three are `(∇_X h)(P,Q)`. -/
theorem inner_endCov_eq_covBilin
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hAh : ∀ (y : M) (v w : TangentSpace I y), ⟪A y v, w⟫ = h y v w)
    (hA : IsMDiffHomAt (I := I) E E A x)
    (hAP : MDiffAt (T% (fun y ↦ A y (P y))) x)
    (hX : MDiffAt (T% X) x) (hP : MDiffAt (T% P) x) (hQ : MDiffAt (T% Q) x) :
    ⟪endCov cov A x (X x) (P x), Q x⟫ = cov.covBilin h X P Q x := by
  rw [endCov_apply hA hX hP, inner_sub_left]
  have hmc := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X hAP hQ
  have hfun : (fun y ↦ ⟪A y (P y), Q y⟫) = fun y ↦ h y (P y) (Q y) := by
    funext y; exact hAh y (P y) (Q y)
  have hmc' : mvfderiv I (fun y ↦ h y (P y) (Q y)) x (X x)
      = ⟪cov (fun y ↦ A y (P y)) x (X x), Q x⟫ + ⟪A x (P x), cov Q x (X x)⟫ := by
    rw [← hfun]; exact hmc
  rw [covBilin]
  linarith [hmc', hAh x (cov P x (X x)) (Q x), hAh x (P x) (cov Q x (X x))]

variable {U V₀ : Π y : M, TangentSpace I y}

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (y : M) ↦ TangentSpace I y) I]
  [T2Space M] in
/-- **Index raising commutes with `∇²`**: `⟪(∇²_{U,V}A)p, q⟫ = (∇²_{U,V}h)(p,q)`.

The one-derivative bridge applied twice. `∇²A` is `∇_U(∇_V A) − ∇_{∇_U V}A`; pairing the
first term and moving `∇_U` onto the pairing by metric compatibility gives the derivative of
`(∇_V h)(P,Q)` minus the two corrections in `∇_U P` and `∇_U Q`, and the second term is
`(∇_{∇_U V}h)(P,Q)`. Those four are the four terms of `∇²h`. -/
theorem inner_hessianSection_eq_cov2Bilin
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hAh : ∀ (y : M) (v w : TangentSpace I y), ⟪A y v, w⟫ = h y v w)
    (hAy : ∀ y : M, IsMDiffHomAt (I := I) E E A y)
    (hAP : ∀ R : Π y : M, TangentSpace I y, (∀ y, MDiffAt (T% R) y) →
      ∀ y, MDiffAt (T% (fun z ↦ A z (R z))) y)
    (hB : IsMDiffHomAt (I := I) E E (fun y ↦ endCov cov A y (V₀ y)) x)
    (hBP : MDiffAt (T% (fun y ↦ endCov cov A y (V₀ y) (P y))) x)
    (hU : CMDiff 2 (T% U)) (hV₀ : CMDiff 2 (T% V₀))
    (hP : CMDiff 2 (T% P)) (hQ : CMDiff 2 (T% Q)) :
    ⟪(endCov cov).hessianSection cov U V₀ A x (P x), Q x⟫
      = cov.cov2Bilin h U V₀ P Q x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hUm : ∀ y, MDiffAt (T% U) y := hU.mdifferentiable h2
  have hV₀m : ∀ y, MDiffAt (T% V₀) y := hV₀.mdifferentiable h2
  have hPm : ∀ y, MDiffAt (T% P) y := hP.mdifferentiable h2
  have hQm : ∀ y, MDiffAt (T% Q) y := hQ.mdifferentiable h2
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hU1 : CMDiff 1 (T% U) := hU.of_le (by norm_num)
  have hDV₀g : ∀ y, MDiffAt (T% (fun z ↦ cov V₀ z (U z))) y :=
    (cov.contMDiff_cov_apply hV₀ hU1).mdifferentiable h1
  have hDPg : ∀ y, MDiffAt (T% (fun z ↦ cov P z (U z))) y :=
    (cov.contMDiff_cov_apply hP hU1).mdifferentiable h1
  have hDQg : ∀ y, MDiffAt (T% (fun z ↦ cov Q z (U z))) y :=
    (cov.contMDiff_cov_apply hQ hU1).mdifferentiable h1
  -- the one-derivative bridge, in the four places it is used
  have S : ∀ (Y R S' : Π y : M, TangentSpace I y) (y : M), MDiffAt (T% Y) y →
      (∀ z, MDiffAt (T% R) z) → MDiffAt (T% S') y →
      ⟪endCov cov A y (Y y) (R y), S' y⟫ = cov.covBilin h Y R S' y := fun Y R S' y hY hR hS' ↦
    cov.inner_endCov_eq_covBilin hmet hAh (hAy y) (hAP R hR y) hY (hR y) hS'
  -- `⟪(∇_V A)(P), Q⟫` as a function of the base point
  have hfun : (fun y ↦ ⟪endCov cov A y (V₀ y) (P y), Q y⟫)
      = fun y ↦ cov.covBilin h V₀ P Q y :=
    funext fun y ↦ S V₀ P Q y (hV₀m y) hPm (hQm y)
  -- metric compatibility on the section `y ↦ (∇_V A)(P) y`
  have hmc := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) U hBP (hQm x)
  have hmc' : mvfderiv I (fun y ↦ cov.covBilin h V₀ P Q y) x (U x)
      = ⟪cov (fun y ↦ endCov cov A y (V₀ y) (P y)) x (U x), Q x⟫
        + ⟪endCov cov A x (V₀ x) (P x), cov Q x (U x)⟫ := by
    rw [← hfun]; exact hmc
  -- the three pointwise values
  have e1 : ⟪endCov cov A x (V₀ x) (P x), cov Q x (U x)⟫
      = cov.covBilin h V₀ P (fun y ↦ cov Q y (U y)) x :=
    S V₀ P (fun y ↦ cov Q y (U y)) x (hV₀m x) hPm (hDQg x)
  have e2 : ⟪endCov cov A x (V₀ x) (cov P x (U x)), Q x⟫
      = cov.covBilin h V₀ (fun y ↦ cov P y (U y)) Q x :=
    S V₀ (fun y ↦ cov P y (U y)) Q x (hV₀m x) hDPg (hQm x)
  have e3 : ⟪endCov cov A x (cov V₀ x (U x)) (P x), Q x⟫
      = cov.covBilin h (fun y ↦ cov V₀ y (U y)) P Q x :=
    S (fun y ↦ cov V₀ y (U y)) P Q x (hDV₀g x) hPm (hQm x)
  -- expand the Hessian
  have hexp : (endCov cov).hessianSection cov U V₀ A x (P x)
      = cov (fun y ↦ endCov cov A y (V₀ y) (P y)) x (U x)
        - endCov cov A x (V₀ x) (cov P x (U x))
        - endCov cov A x (cov V₀ x (U x)) (P x) := by
    show ((endCov cov) (fun y ↦ endCov cov A y (V₀ y)) x (U x)
      - endCov cov A x (cov V₀ x (U x))) (P x) = _
    rw [_root_.sub_apply,
      show (endCov cov) (fun y ↦ endCov cov A y (V₀ y)) x (U x) (P x)
        = endCov cov (fun y ↦ endCov cov A y (V₀ y)) x (U x) (P x) from rfl,
      endCov_apply hB (hUm x) (hPm x)]
  rw [hexp, inner_sub_left, inner_sub_left, cov2Bilin]
  linarith [hmc', e1, e2, e3]


/-- Expanding a finite sum of endomorphisms applied to a vector, then paired. Stated over a
variable inner product space, `rw` not being able to see a `TangentSpace`-typed `Finset.sum`
as the sum it is. -/
theorem sum_apply_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (T : ι → F →L[ℝ] F) (v w : F) :
    ⟪(∑ i, T i) v, w⟫ = ∑ i, ⟪T i v, w⟫ := by
  rw [_root_.sum_apply, sum_inner]

omit [CompleteSpace E] in
/-- **Index raising commutes with `Δ`**: `⟪(Δ A)p, q⟫ = (Δ_g h)(p,q)`.

The Hessian bridge traced. Both Laplacians are the trace of their Hessian over the same
orthonormal frame, so the identity is termwise and nothing further is computed.

**This is what connects the maximum principle on `End(TM)` to the evolution equations.** The
touching-point principle concludes `⟪n, Δ u⟫ ≤ 0` with `Δ` the connection Laplacian of
`endCov`; every evolution equation in this development has `Δ_g` of a bilinear form on its
right. -/
theorem inner_laplacianSection_eq_laplacianBilin
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hAh : ∀ (y : M) (v w : TangentSpace I y), ⟪A y v, w⟫ = h y v w)
    (hAsm : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y (A y)))
    (hbil : IsMDiffBilinAt (I := I) h x) (hcb : cov.IsMDiffCovBilinAt h P Q x)
    (hP : CMDiff 2 (T% P)) (hQ : CMDiff 2 (T% Q))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    ⟪(endCov cov).laplacianSection cov hAsm x (P x), Q x⟫
      = cov.laplacianBilin h P Q x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hAy : ∀ y : M, IsMDiffHomAt (I := I) E E A y := fun y ↦
    isMDiffHomAt_of_section (V₁ := fun z : M ↦ TangentSpace I z)
      (V₂ := fun z : M ↦ TangentSpace I z) (hAsm.mdifferentiable h2 y)
  have hAP : ∀ R : Π y : M, TangentSpace I y, (∀ y, MDiffAt (T% R) y) →
      ∀ y, MDiffAt (T% (fun z ↦ A z (R z))) y := fun R hR y ↦ hAy y R (hR y)
  have hBsec : ∀ R : Π y : M, TangentSpace I y, CMDiff 2 (T% R) →
      IsMDiffHomAt (I := I) E E (fun y ↦ endCov cov A y (R y)) x := fun R hR ↦
    isMDiffHomAt_of_section (V₁ := fun z : M ↦ TangentSpace I z)
      (V₂ := fun z : M ↦ TangentSpace I z)
      ((endCov cov).mdiffAt_cov_apply_section hAsm (hR.mdifferentiable h2 x))
  have hBP : ∀ R S' : Π y : M, TangentSpace I y, CMDiff 2 (T% R) → CMDiff 2 (T% S') →
      MDiffAt (T% (fun y ↦ endCov cov A y (R y) (S' y))) x := fun R S' hR hS' ↦
    hBsec R hR S' (hS'.mdifferentiable h2 x)
  rw [(endCov cov).laplacianSection_eq_sum_frame cov hAsm
      (fun i ↦ (hfr i).mdifferentiable h2 x) b hbv,
    cov.laplacianBilin_eq_sum_frame hbil hcb hP hQ hfr b hbv,
    sum_apply_inner (fun i ↦ (endCov cov).hessianSection cov (fr i) (fr i) A x) (P x) (Q x)]
  exact Finset.sum_congr rfl fun i _ ↦
    cov.inner_hessianSection_eq_cov2Bilin hmet hAh hAy hAP (hBsec (fr i) (hfr i))
      (hBP (fr i) P (hfr i) hP) (hfr i) (hfr i) hP hQ


section RicciSharp

/-! ### The falsification check: `Δ(Ric♯) = (Δ_g Ric)♯`

A general theorem with no instantiations is unverified. `Ric♯` is the object the whole
bridge exists for, and it satisfies the interface hypothesis on the nose
(`inner_ricciSharp`) and the smoothness hypothesis by `contMDiff_ricciSharp`. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

set_option maxSynthPendingDepth 4

omit [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`⟪Δ(Ric♯)p, q⟫ = (Δ_g Ric)(p,q)`.** The general bridge at the object it was built for:
the connection Laplacian of `Ric♯` as a section of `End(TM)` — which is what the maximum
principle on that bundle sees — is the index-raised Laplacian of the Ricci form, which is
what the evolution equations produce. -/
theorem inner_laplacianSection_ricciSharp_eq_laplacianBilin
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {P Q : Π y : M, TangentSpace I y} {x : M}
    (hbil : IsMDiffBilinAt (I := I) (fun y ↦ cov.ricciForm y) x)
    (hcb : cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) P Q x)
    (hP : CMDiff 2 (T% P)) (hQ : CMDiff 2 (T% Q))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    ⟪(endCov cov).laplacianSection cov cov.contMDiff_ricciSharp x (P x), Q x⟫
      = cov.laplacianBilin (fun y ↦ cov.ricciForm y) P Q x :=
  cov.inner_laplacianSection_eq_laplacianBilin hmet
    (fun y v w ↦ cov.inner_ricciSharp (x := y) v w) cov.contMDiff_ricciSharp
    hbil hcb hP hQ hfr b hbv

end RicciSharp

end CovariantDerivative
