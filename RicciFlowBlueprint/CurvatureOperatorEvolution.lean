/-
**`∂ₜRm₃ = ΔRm₃ + Q(Rm₃)` under the Ricci flow — the geometric assembly.**

`CurvatureOperatorFlow.lean` did the algebra in a Ricci eigenbasis; what it needs from the
geometry is (i) a Ricci eigenbasis at the point, (ii) a frame of globally `C⁴` fields,
orthonormal on a neighbourhood, passing through that eigenbasis --- every evolution equation in
the repo reads its traces off such a frame --- and (iii) the evolution equations themselves.

(i) is the spectral theorem on `Rm₃` (`exists_orthonormalBasis_curvatureOperator`): an
eigenbasis of `Rm₃ = scal·1 − 2Ric♯` is one of `Ric♯`. (ii) is a **constant rotation** of the
orthonormal frame `RicciSection.lean` builds: `frᵢ = ∑ⱼ ⟪bᵢ, Frⱼ(x)⟫ Frⱼ` stays orthonormal
wherever `Fr` is, since the coefficient matrix is orthogonal, and at `x` it is `b` by Parseval.
-/
import RicciFlowBlueprint.CurvatureOperatorFlow
import RicciFlowBlueprint.CurvatureOperatorPinched
import RicciFlowBlueprint.RicciSection
import RicciFlowBlueprint.RicciReactionThree
import RicciFlowBlueprint.CurvatureOperatorLaplacian
import RicciFlowBlueprint.UhlenbeckFlow
import RicciFlowBlueprint.RicciEvolution
import RicciFlowBlueprint.ScalarFlow

open Bundle Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 4

-- BENCH: orthonormal-frame-through
/-- **A globally `C^n` frame, orthonormal on a neighbourhood of `x`, through any prescribed
orthonormal basis of `T_xM`.** A constant orthogonal rotation of `exists_orthonormal_frame_on_open`:
`frᵢ = ∑ⱼ ⟪bᵢ, Frⱼ(x)⟫ Frⱼ`. -/
theorem exists_orthonormal_frame_through {n : ℕ∞}
    [ContMDiffVectorBundle (n : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    [IsContMDiffRiemannianBundle I (n : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x)]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
    (hn : 1 ≤ n) {x : M} {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∃ (u : Set M) (fr : ι → Π y : M, TangentSpace I y),
      IsOpen u ∧ x ∈ u ∧ (∀ i, CMDiff (n : ℕ∞ω) (T% (fr i))) ∧
      IsOrthonormalFrameOn I E 1 fr u ∧ ∀ i, fr i x = b i := by
  classical
  obtain ⟨U, Fr, hU, hxU, hFr, hon⟩ := exists_orthonormal_frame_on_open (I := I) (n := n) x
  obtain ⟨α, hα⟩ := hon x hxU
  set c : ι → Fin (finrank ℝ E) → ℝ := fun i j ↦ ⟪Fr j x, (b i : TangentSpace I x)⟫ with hc
  set fr : ι → Π y : M, TangentSpace I y := fun i y ↦ ∑ j, c i j • Fr j y with hfr
  have hfrs : ∀ i, CMDiff (n : ℕ∞ω) (T% (fr i)) := fun i ↦
    ContMDiff.sum_section fun j _ ↦ (hFr j).const_smul_section (a := c i j)
  -- the rotated frame is orthonormal wherever `Fr` is
  have hcc : ∀ i k, ∑ j, c i j * c k j = ⟪(b i : TangentSpace I x), b k⟫ := fun i k ↦ by
    rw [← α.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hc, hα]
    rw [real_inner_comm (α j) (b i)]
  have honu : ∀ y ∈ U, Orthonormal ℝ (fun i ↦ fr i y) := by
    intro y hy
    obtain ⟨β, hβ⟩ := hon y hy
    rw [orthonormal_iff_ite]
    intro i k
    have hβo := orthonormal_iff_ite.mp β.orthonormal
    simp only [hfr, hβ, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      hβo, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [show ∑ j, c k j * c i j = ∑ j, c i j * c k j from
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _, hcc i k]
    exact orthonormal_iff_ite.mp b.orthonormal i k
  have hcard : Fintype.card ι = finrank ℝ E := (finrank_eq_card_basis b.toBasis).symm
  refine ⟨U, fr, hU, hxU, hfrs, ?_, fun i ↦ ?_⟩
  · have hn' : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := by exact_mod_cast hn
    refine
      { linearIndependent := fun hy ↦ (honu _ hy).linearIndependent
        generating := fun {y} hy ↦ ?_
        contMDiffOn := fun i ↦ ((hfrs i).of_le hn').contMDiffOn
        orthonormal := fun hy ↦ honu _ hy }
    have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
    rw [(honu _ hy).linearIndependent.span_eq_top_of_card_eq_finrank' (by exact hcard)]
  · show ∑ j, c i j • Fr j x = b i
    simp only [hc, hα]
    exact α.sum_repr' (b i)

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint RicciFlowBlueprint.Pinching ContinuousLinearMap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 4

/-- **A Ricci eigenbasis at every point of a three-manifold**: an eigenbasis of `Rm₃ = scal·1 −
2Ric♯` diagonalises `Ric`, since `⟪Rm₃ bᵢ, bⱼ⟫ = scal⟪bᵢ,bⱼ⟫ − 2Ric(bᵢ,bⱼ)`. -/
theorem exists_ricci_eigenbasis
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    (x : M) (hdim : finrank ℝ (TangentSpace I x) = 3) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x),
      ∀ i j, i ≠ j → cov.ricciAt x (b i) (b j) = 0 := by
  obtain ⟨b, e, -, he⟩ := cov.exists_orthonormalBasis_curvatureOperator hmet htor x hdim
  refine ⟨b, fun i j hij ↦ ?_⟩
  have h := cov.inner_curvatureOperator (b i) (b j)
  have h0 : ⟪(b i : TangentSpace I x), b j⟫ = 0 := b.orthonormal.2 hij
  rw [he i, real_inner_smul_left, h0, ricciForm_apply] at h
  linarith

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- On a Ricci eigenbasis, `Ric♯ bₖ = Ric(bₖ,bₖ) bₖ`. -/
theorem ricciSharp_apply_eigenbasis {x : M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hric : ∀ i j, i ≠ j → cov.ricciAt x (b i) (b j) = 0) (k : ι) :
    cov.ricciSharp x (b k) = cov.ricciAt x (b k) (b k) • (b k : TangentSpace I x) := by
  rw [← b.sum_repr' (cov.ricciSharp x (b k))]
  have hc : ∀ l, ⟪(b l : TangentSpace I x), cov.ricciSharp x (b k)⟫
      = if k = l then cov.ricciAt x (b k) (b k) else 0 := fun l ↦ by
    rw [real_inner_comm, inner_ricciSharp, ricciForm_apply]
    rcases eq_or_ne k l with h | h
    · subst h; simp
    · simp only [h, ↓reduceIte]; exact hric k l h
  simp only [hc, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 2] [ContMDiffCovariantDerivative cov 3]

-- BENCH: curvature-operator-evolution-pointwise
/-- **`∂ₜRm₃ = ΔRm₃ + Q(Rm₃)`, pointwise, from the evolution of `scal` and `Ric`.** Given
`D = s'·1 − 2(2Ric♯² + R'♯)` --- the time derivative of `Rm₃` as `UhlenbeckFlow.lean` delivers
it --- with `s' = Δscal + 2|Ric|²` and `R'(bₖ,bₗ)` the right-hand side of Hamilton's Ricci
evolution on a frame through a Ricci eigenbasis, `D` is the connection Laplacian of `Rm₃` on
`End(TM)` plus Hamilton's reaction. -/
theorem eq_laplacianSection_add_hamiltonReaction
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) (htor : cov.torsion = 0)
    {x : M} [FiniteDimensional ℝ (TangentSpace I x)] (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x))
    (hric : ∀ i j, i ≠ j → cov.ricciAt x (b i) (b j) = 0)
    {fr : Fin 3 → Π y : M, TangentSpace I y} (hfr : ∀ i, CMDiff 4 (T% (fr i)))
    (hfrx : ∀ i, fr i x = b i)
    (hscal : ∀ y, MDiffAt (fun z ↦ cov.scalarCurvatureAt z) y)
    (hdscal : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y : TangentSpace I y →L[ℝ] ℝ)) x)
    (hRic : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y)
    (hcb : ∀ k l, cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) (fr k) (fr l) x)
    {D : TangentSpace I x →L[ℝ] TangentSpace I x} {s' : ℝ}
    {R' : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hD : D = s' • ContinuousLinearMap.id ℝ (TangentSpace I x)
      - (2 : ℝ) • ((2 : ℝ) • (cov.ricciSharp x ∘L cov.ricciSharp x) + sharp R'))
    (hs' : s' = cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x
      + 2 * ∑ i, (cov.ricciAt x (b i) (b i)) ^ 2)
    (hR' : ∀ k l, R' (b k) (b l)
      = cov.laplacianBilin (fun y ↦ cov.ricciForm y) (fr k) (fr l) x
        + ∑ j, ∑ i, ⟪cov.curvatureCommutator (fr i) (fr j) (fr k) (fr i) (fr l) x, fr j x⟫
        + ∑ j, ∑ i, ⟪cov.curvatureCommutator (fr i) (fr k) (fr i) (fr j) (fr l) x, fr j x⟫
        + ∑ j, cov.ricciForm x (cov.curvature (fr j) (fr k) (fr l) x) (fr j x)
        + ∑ j, cov.ricciForm x (fr l x) (cov.curvature (fr j) (fr k) (fr j) x)) :
    D = (endCov cov).laplacianSection cov (cov.contMDiff_curvatureOperator) x
      + hamiltonReaction (cov.curvatureOperator x) := by
  classical
  set K := cov.secAt b with hKdef
  have hr : ∀ k, cov.ricciAt x (b k) (b k) = ∑ n, K k n := fun k ↦ by
    rw [cov.ricciAt_eq_secAt hmet htor b hric k k]; simp [hKdef]
  have hscalK : cov.scalarCurvatureAt x = ∑ i, ∑ n, K i n := by
    rw [cov.scalarCurvatureAt_eq_sum_basis b]
    exact Finset.sum_congr rfl fun i _ ↦ hr i
  have hRm : cov.curvatureOperator x = (∑ i, ∑ n, K i n) • ContinuousLinearMap.id ℝ _
      - (2 : ℝ) • cov.ricciSharp x := by
    rw [curvatureOperator, hscalK]
  have hL : ∀ k l, ⟪(endCov cov).laplacianSection cov (cov.contMDiff_curvatureOperator) x
      (b k), b l⟫ = (if k = l then cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x else 0)
        - 2 * cov.laplacianBilin (fun y ↦ cov.ricciForm y) (fr k) (fr l) x := fun k l ↦ by
    have h2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
    have h := cov.inner_laplacianSection_curvatureOperator_eq hmet hscal hdscal (h2 k) (h2 l)
      hRic (hcb k l) h2 b hfrx
    rw [hfrx, hfrx, orthonormal_iff_ite.mp b.orthonormal k l] at h
    rw [h]
    split_ifs <;> ring
  rw [hRm]
  refine eq_add_hamiltonReaction_of_eigenbasis b K (fun i j ↦ cov.secAt_comm hmet htor b i j)
    (fun i ↦ cov.secAt_self b i) (fun k ↦ ?_) _ hD ?_ (fun k l ↦ ?_) hL
  · rw [cov.ricciSharp_apply_eigenbasis b hric k, hr k]
  · rw [hs']
    simp only [hr]
  · rw [inner_sharp, hR' k l, add_assoc, add_assoc, add_assoc,
      ← cov.ricciReaction_three hmet htor b hric hfr hfrx k l]
    ring

end CovariantDerivative

namespace RicciFlowBlueprint

open CovariantDerivative Pinching ContinuousLinearMap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 4

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- The sharp of a metric carried as a value is the Riesz sharp of the instance it induces. -/
theorem sharpE_apply_eq_sharp (x : M) (B : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
    haveI : CompleteSpace (TangentSpace I x) := VectorBundle.completeSpace ℝ E ..
    sharpE (g t₀) x B v = sharp (W := TangentSpace I x) B v := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  have : CompleteSpace (TangentSpace I x) := VectorBundle.completeSpace ℝ E ..
  refine ext_inner_right (E := TangentSpace I x) ℝ fun w ↦ ?_
  exact (innerE_sharpE (g t₀) x B v w).trans (inner_sharp (W := TangentSpace I x) B v w).symm

variable [T2Space M]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]

-- BENCH: curvature-operator-evolution-flow
/-- **`∂ₜRm₃ = ΔRm₃ + Q(Rm₃)` under the Ricci flow on a three-manifold.** `Rm₃ = scal·1 −
2Ric♯` as the endomorphism `curvatureOperatorE (g t) x` of `E = T_xM`, the metric moving in
both `scal` and the index raising; its time derivative `D`, tested against the metric at
`t₀`, is the connection Laplacian of `Rm₃` on `End(TM)` plus Hamilton's reaction. -/
theorem exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt (hdim : finrank ℝ E = 3)
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    {x : M}
    (hAt : CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt I M g t₀)
    (hrb3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hrb4 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    (hlc3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3)
    (hRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hRic2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ Z P : Π y : M, TangentSpace I y, CMDiff 4 (T% Z) → CMDiff 4 (T% P) →
        ContMDiffAt I 𝓘(ℝ, ℝ) 2
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y (Z y) (P y)) x)
    (hdRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
        CMDiff 2 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) P Q R y) x)
    (hcovR : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
        CMDiff 3 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covRicci P Q R y) x)
    (hcb : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ Y Z : Π y : M, TangentSpace I y, CMDiff 4 (T% Y) → CMDiff 4 (T% Z) →
        (leviCivitaOfMetric (g t₀)).IsMDiffCovBilinAt
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) Y Z x)
    (hscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ y, MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y)
    (hdscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffOneFormAt (I := I)
        (fun y ↦ (mvfderiv I (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      CovariantDerivative.IsMDiffOneFormAt (I := I)
        ((leviCivitaOfMetric (g t₀)).divBilinOneForm
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) (fun y U V _ _ ↦ hRic U V y)) x) :
    ∃ D : E →L[ℝ] E, HasDerivAt (fun t ↦ curvatureOperatorE (g t) x) D t₀ ∧
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
      letI : IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x) := hrb4
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 :=
        hlc2
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3 :=
        hlc3
      letI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∀ v w : TangentSpace I x, innerE (g t₀) x (D v) w
        = ⟪((endCov (leviCivitaOfMetric (g t₀))).laplacianSection (leviCivitaOfMetric (g t₀))
              ((leviCivitaOfMetric (g t₀)).contMDiff_curvatureOperator) x
            + hamiltonReaction ((leviCivitaOfMetric (g t₀)).curvatureOperator x)) v, w⟫ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
  let _ : IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x) := hrb4
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 := hlc2
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3 := hlc3
  let _ : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := VectorBundle.completeSpace ℝ E ..
  have hmet : (leviCivitaOfMetric (g t₀)).IsMetricCompatible (M := M) (V := TangentSpace I) :=
    CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)
  have htor : (leviCivitaOfMetric (g t₀)).torsion = 0 := torsion_leviCivitaOfMetric_eq_zero (g t₀)
  obtain ⟨b, hric⟩ := (leviCivitaOfMetric (g t₀)).exists_ricci_eigenbasis hmet htor x hdim
  obtain ⟨u, fr, hu, hxu, hfr, hs, hbv⟩ :=
    exists_orthonormal_frame_through (I := I) (n := 4) (by norm_num) b
  have hfr4 : ∀ i, CMDiff 4 (T% (fr i)) := hfr
  have hfr3 : ∀ i, CMDiff 3 (T% (fr i)) := fun i ↦ (hfr4 i).of_le (by norm_num)
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr4 i).of_le (by norm_num)
  -- the three time derivatives
  have hgx : HasDerivAt (fun t ↦ innerE (g t) x)
      ((-2 : ℝ) • ricciFormOfMetric (g t₀) x) t₀ := by
    rw [← innerE_deriv_eq_of_isRicciFlowAt' hg x hflow]; exact hg x
  have hRicT := hasDerivAt_ricciFormOfMetric hg hcomm hcov x
  have hScalT := hasDerivAt_scalarCurvatureOfMetricAt_eq_laplacian_add hg hcomm hcov hbil hAt
    hflow hlc2 (fun y U V _ _ ↦ hRic U V y) hdscal hw hs hu hxu hfr3 b (fun i ↦ hbv i) hRic
    (fun a c d ↦ hdRic _ _ _ (hfr2 a) (hfr2 c) (hfr2 d)) (fun j ↦ hcb _ _ (hfr4 j) (hfr4 j))
  have hDer := hasDerivAt_curvatureOperatorE_of_flow hgx hRicT hScalT
  refine ⟨_, hDer, ?_⟩
  obtain ⟨R'T, hR'T⟩ : ∃ R'T : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ,
      R'T = derivRicciFormOfMetric g t₀ x := ⟨_, rfl⟩
  set s' := (leviCivitaOfMetric (g t₀)).laplacianFun
        (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) x
      + 2 * metricTraceE (I := I) (M := M) (g t₀) x
        (ricciFormOfMetric (g t₀) x ∘L sharpE (I := I) (M := M) (g t₀) x
          (ricciFormOfMetric (g t₀) x)) with hs'def
  have hS : ∀ v : E, sharpE (g t₀) x (ricciFormOfMetric (g t₀) x) v
      = (leviCivitaOfMetric (g t₀)).ricciSharp x v := fun v ↦
    sharpE_apply_eq_sharp (I := I) (g := g) x _ v
  have hs' : s' = (leviCivitaOfMetric (g t₀)).laplacianFun
        (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) x
      + 2 * ∑ i, ((leviCivitaOfMetric (g t₀)).ricciAt x (b i) (b i)) ^ 2 := by
    rw [hs'def, metricTraceE_eq_sum (g t₀) x _ b]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hRf : ricciFormOfMetric (g t₀) x = (leviCivitaOfMetric (g t₀)).ricciForm x := rfl
    show ricciFormOfMetric (g t₀) x (sharpE (g t₀) x (ricciFormOfMetric (g t₀) x) (b i)) (b i) = _
    have e1 : sharpE (g t₀) x (ricciFormOfMetric (g t₀) x) (b i)
        = (leviCivitaOfMetric (g t₀)).ricciAt x (b i) (b i) • (b i : TangentSpace I x) :=
      (hS (b i)).trans ((leviCivitaOfMetric (g t₀)).ricciSharp_apply_eigenbasis b hric i)
    have e2 : ∀ (c : ℝ) (v : E), ricciFormOfMetric (g t₀) x (c • v) v
        = c * ricciFormOfMetric (g t₀) x v v := fun c v ↦ by
      rw [map_smul, smul_apply, smul_eq_mul]
    rw [e1]
    exact (e2 _ _).trans (by rw [sq]; rfl)
  have hR' : ∀ k l, R'T (b k) (b l)
      = (leviCivitaOfMetric (g t₀)).laplacianBilin
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) (fr k) (fr l) x
        + ∑ j, ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) (fr j) (fr k) (fr i) (fr l) x, fr j x⟫
        + ∑ j, ∑ i, ⟪(leviCivitaOfMetric (g t₀)).curvatureCommutator
            (fr i) (fr k) (fr i) (fr j) (fr l) x, fr j x⟫
        + ∑ j, (leviCivitaOfMetric (g t₀)).ricciForm x
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) (fr k) (fr l) x) (fr j x)
        + ∑ j, (leviCivitaOfMetric (g t₀)).ricciForm x (fr l x)
            ((leviCivitaOfMetric (g t₀)).curvature (fr j) (fr k) (fr j) x) := fun k l ↦ by
    have h := derivRicciFormOfMetric_eq_laplacianBilin_add_of_isRicciFlowAt hg hcomm hcov hbil
      hAt hflow hrb3 hlc2 hlc3 (hfr4 k) (hfr4 l) hRic (fun P hP ↦ hRic2 _ _ (hfr4 l) hP) hdRic
      hcovR (hcb _ _ (hfr4 k) (hfr4 l)) hfr4 hs hu hxu b hbv
    rw [hR'T, ← hbv k, ← hbv l]
    exact h
  obtain ⟨D'', hD''⟩ : ∃ D'' : TangentSpace I x →L[ℝ] TangentSpace I x,
      D'' = s' • ContinuousLinearMap.id ℝ (TangentSpace I x)
        - (2 : ℝ) • ((2 : ℝ) • ((leviCivitaOfMetric (g t₀)).ricciSharp x
          ∘L (leviCivitaOfMetric (g t₀)).ricciSharp x) + sharp R'T) := ⟨_, rfl⟩
  have key := (leviCivitaOfMetric (g t₀)).eq_laplacianSection_add_hamiltonReaction hmet htor b
    hric hfr4 hbv hscal hdscal hRic (fun k l ↦ hcb _ _ (hfr4 k) (hfr4 l)) hD'' hs' hR'
  intro v w
  rw [← key]
  have e3 : sharpE (g t₀) x (derivRicciFormOfMetric g t₀ x) v = sharp R'T v := by
    rw [hR'T]; exact sharpE_apply_eq_sharp (I := I) (g := g) x _ v
  have e4 : sharpE (g t₀) x (ricciFormOfMetric (g t₀) x)
      (sharpE (g t₀) x (ricciFormOfMetric (g t₀) x) v)
      = (leviCivitaOfMetric (g t₀)).ricciSharp x ((leviCivitaOfMetric (g t₀)).ricciSharp x v) :=
    (hS _).trans (congrArg _ (hS v))
  have hDv : (s' • ContinuousLinearMap.id ℝ E
        - (2 : ℝ) • ((2 : ℝ) • (sharpE (g t₀) x (ricciFormOfMetric (g t₀) x)
            ∘L sharpE (g t₀) x (ricciFormOfMetric (g t₀) x))
          + sharpE (g t₀) x (derivRicciFormOfMetric g t₀ x))) v = D'' v := by
    rw [hD'']
    show s' • (show E from v) - (2 : ℝ) • ((2 : ℝ) • sharpE (g t₀) x (ricciFormOfMetric (g t₀) x)
        (sharpE (g t₀) x (ricciFormOfMetric (g t₀) x) v)
        + sharpE (g t₀) x (derivRicciFormOfMetric g t₀ x) v) = _
    rw [e3, e4]
    rfl
  rw [hDv]
  rfl

end RicciFlowBlueprint
