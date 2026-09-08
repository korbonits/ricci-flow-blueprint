/-
**The divergence of the curvature tensor.**

`div Rm(Y,Z,W) = ∑ᵢ ⟪(∇_{eᵢ}Rm)(Y,Z)W, eᵢ⟫` is the trace of `∇Rm` over its direction
slot against its fourth. It is what the contracted second Bianchi identity is about, and
through that identity what `Δ scal` is about.

Two facts from `CurvatureDeriv.lean` make it well defined, and neither is free:

* `(∇_X Rm)(Y,Z)W` at `x` depends only on `X x` (`covCurvature_congr_dir`), so
  `v ↦ (∇_v Rm)(Y,Z)W` is a function on `T_xM` at all;
* it is `C^∞(M)`-linear there (`covCurvature_smul_dir`, `covCurvature_add_dir`), so that
  function is linear.

Together they give a genuine endomorphism of `T_xM`, and the divergence is its trace —
so frame-independence is the algebraic `LinearMap.trace_eq_sum_inner`, not a computation.
This is the same route `RicciForm.lean` took to the scalar curvature, one level up:
there the object traced was a bilinear form and the trace was metric, here it is an
endomorphism and the trace is not.

The tangent-vector-valued function is built on globally `C²` extensions
(`exists_contMDiff_two_extension`), exactly as `ricciAt` is.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureDeriv
import RicciFlowBlueprint.CurvatureSymm
import RicciFlowBlueprint.RicciForm

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]

section Pointwise

/-- **`(∇_v Rm)(Y,Z)W` as a function of a tangent vector.** Evaluated on a globally `C²`
extension of `v`, which exists by `exists_contMDiff_two_extension` and gives the same
answer by `covCurvature_congr_dir`. -/
noncomputable def covCurvatureAt (Y Z W : Π y : M, TangentSpace I y) (x : M)
    (v : TangentSpace I x) : TangentSpace I x :=
  cov.covCurvature (RicciFlowBlueprint.exists_contMDiff_two_extension v).choose Y Z W x

omit [CompleteSpace E] in
-- BENCH: cov-curvature-at-eq
/-- `covCurvatureAt` computes `covCurvature` on any globally `C²` direction field. -/
theorem covCurvatureAt_eq {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvatureAt Y Z W x (X x) = cov.covCurvature X Y Z W x := by
  obtain ⟨hc, hv⟩ := (RicciFlowBlueprint.exists_contMDiff_two_extension (X x)).choose_spec
  exact cov.covCurvature_congr_dir hc hX hY hZ hW hv

omit [CompleteSpace E] in
/-- Additivity in the tangent vector, from `covCurvature_add_dir`. -/
theorem covCurvatureAt_add {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (v w : TangentSpace I x) :
    cov.covCurvatureAt Y Z W x (v + w)
      = cov.covCurvatureAt Y Z W x v + cov.covCurvatureAt Y Z W x w := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  obtain ⟨U, hU, hUw⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w
  have e1 : cov.covCurvatureAt Y Z W x (V x) = cov.covCurvature V Y Z W x :=
    cov.covCurvatureAt_eq hV hY hZ hW
  have e2 : cov.covCurvatureAt Y Z W x (U x) = cov.covCurvature U Y Z W x :=
    cov.covCurvatureAt_eq hU hY hZ hW
  have e3 : cov.covCurvatureAt Y Z W x ((V + U) x) = cov.covCurvature (V + U) Y Z W x :=
    cov.covCurvatureAt_eq (hV.add_section hU) hY hZ hW
  have hsum : (V + U) x = v + w := by show V x + U x = v + w; rw [hVv, hUw]
  rw [← hsum, e3, cov.covCurvature_add_dir hV hU hY hZ hW, ← e1, ← e2, hVv, hUw]

omit [CompleteSpace E] in
/-- Homogeneity in the tangent vector, from `covCurvature_smul_dir` applied to a constant
coefficient. -/
theorem covCurvatureAt_smul {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (c : ℝ) (v : TangentSpace I x) :
    cov.covCurvatureAt Y Z W x (c • v) = c • cov.covCurvatureAt Y Z W x v := by
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun _ : M ↦ c) := contMDiff_const
  have e1 : cov.covCurvatureAt Y Z W x (V x) = cov.covCurvature V Y Z W x :=
    cov.covCurvatureAt_eq hV hY hZ hW
  have e3 : cov.covCurvatureAt Y Z W x (((fun _ : M ↦ c) • V) x)
      = cov.covCurvature ((fun _ : M ↦ c) • V) Y Z W x :=
    cov.covCurvatureAt_eq (hf.smul_section hV) hY hZ hW
  have hsmul : ((fun _ : M ↦ c) • V) x = c • v := by show c • V x = c • v; rw [hVv]
  rw [← hsmul, e3, cov.covCurvature_smul_dir hf hV hY hZ hW, ← e1, hVv]

open scoped Classical in
/-- **`v ↦ (∇_v Rm)(Y,Z)W` as a linear endomorphism of `T_xM`.** Junk (`0`) off the
regularity `covCurvatureAt_add` and `covCurvatureAt_smul` need, exactly as `ricci` is
junk off its own. -/
noncomputable def covCurvatureEndo (Y Z W : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
  if h : CMDiff 2 (T% Y) ∧ CMDiff 2 (T% Z) ∧ CMDiff 3 (T% W) then
    { toFun := cov.covCurvatureAt Y Z W x
      map_add' := cov.covCurvatureAt_add h.1 h.2.1 h.2.2
      map_smul' := fun c v ↦ cov.covCurvatureAt_smul h.1 h.2.1 h.2.2 c v }
  else 0

omit [CompleteSpace E] in
theorem covCurvatureEndo_apply {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    (v : TangentSpace I x) :
    cov.covCurvatureEndo Y Z W x v = cov.covCurvatureAt Y Z W x v := by
  have h : CMDiff 2 (T% Y) ∧ CMDiff 2 (T% Z) ∧ CMDiff 3 (T% W) := ⟨hY, hZ, hW⟩
  simp only [covCurvatureEndo, h, and_self, ↓reduceDIte]
  rfl

end Pointwise

section Divergence

/-- **The divergence of the curvature tensor**, `div Rm(Y,Z,W)(x)`: the trace of the
endomorphism `v ↦ (∇_v Rm)(Y,Z)W` of `T_xM`. No metric enters — this is an endomorphism
trace, not the metric trace the scalar curvature is. -/
noncomputable def divCurvature (Y Z W : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  LinearMap.trace ℝ (TangentSpace I x) (cov.covCurvatureEndo Y Z W x)

omit [CompleteSpace E] in
-- BENCH: div-curvature-frame-independent
/-- **`div Rm` is the frame sum, over any orthonormal basis of `T_xM`.** Hypothesis-free
in the frame: the trace of an endomorphism does not depend on the basis. -/
theorem divCurvature_eq_sum_basis {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.divCurvature Y Z W x = ∑ i, ⟪cov.covCurvatureAt Y Z W x (b i), b i⟫ := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  rw [divCurvature, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : ⟪b i, cov.covCurvatureEndo Y Z W x (b i)⟫
      = ⟪cov.covCurvatureEndo Y Z W x (b i), b i⟫ := real_inner_comm _ _
  rw [e, cov.covCurvatureEndo_apply hY hZ hW]

omit [CompleteSpace E] in
/-- **`div Rm` computed from a `C²` frame** whose values at `x` are orthonormal:
`div Rm(Y,Z,W)(x) = ∑ᵢ ⟪(∇_{eᵢ}Rm)(Y,Z)W, eᵢ⟫`. -/
theorem divCurvature_eq_sum_frame {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {ι : Type*} [Fintype ι] {b : ι → Π y : M, TangentSpace I y}
    (hb : ∀ i, CMDiff 2 (T% (b i))) (v : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, b i x = v i) :
    cov.divCurvature Y Z W x = ∑ i, ⟪cov.covCurvature (b i) Y Z W x, b i x⟫ := by
  rw [cov.divCurvature_eq_sum_basis hY hZ hW v]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hbv i, ← cov.covCurvatureAt_eq (hb i) hY hZ hW, hbv i]

end Divergence

section ContractedBianchi

-- BENCH: traced-bianchi-second
/-- **The traced second Bianchi identity**, in the form the metric contraction leaves it:
`div Rm(Y,Z,W) = ∑ᵢ ⟪(∇_Y Rm)(eᵢ,Z)W, eᵢ⟫ − ∑ᵢ ⟪(∇_Z Rm)(eᵢ,Y)W, eᵢ⟫`.

Trace the second Bianchi identity `(∇_{eᵢ}Rm)(Y,Z)W + (∇_Y Rm)(Z,eᵢ)W + (∇_Z Rm)(eᵢ,Y)W
= 0` against `eᵢ`, using antisymmetry of `∇Rm` in its second and third slots to turn the
middle term round. No derivative of the frame appears: the identity is pointwise in `eᵢ`,
and it is summed, not differentiated.

The two sums on the right are `(∇_Y Ric)(Z,W)` and `(∇_Z Ric)(Y,W)` — that is the trace
commuting with `∇` for the curvature endomorphism, which is a separate theorem and is not
proved here. -/
theorem divCurvature_eq_sub_sum (hcov : cov.torsion = 0)
    {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {ι : Type*} [Fintype ι] {b : ι → Π y : M, TangentSpace I y}
    (hb : ∀ i, CMDiff 2 (T% (b i))) (v : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, b i x = v i) :
    cov.divCurvature Y Z W x
      = (∑ i, ⟪cov.covCurvature Y (b i) Z W x, b i x⟫)
        - ∑ i, ⟪cov.covCurvature Z (b i) Y W x, b i x⟫ := by
  rw [cov.divCurvature_eq_sum_frame hY hZ hW hb v hbv, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hbi := hb i
  have hbianchi := cov.bianchi_second hcov hbi hY hZ hW (x := x)
  have hanti : cov.covCurvature Y Z (b i) W x = -cov.covCurvature Y (b i) Z W x :=
    cov.covCurvature_antisymm Y hZ hbi hW
  rw [hanti] at hbianchi
  have key : cov.covCurvature (b i) Y Z W x
      = cov.covCurvature Y (b i) Z W x - cov.covCurvature Z (b i) Y W x := by
    linear_combination (norm := module) hbianchi
  rw [key, inner_sub_left]

end ContractedBianchi

section TraceDeriv

open RicciFlowBlueprint

variable {ι : Type*} [Fintype ι]

/-- **The curvature as a continuous bilinear form** `(u,v) ↦ ⟪Rm(u,Z)W, v⟫` on `T_xM`.
Linear in `u` because the curvature is tensorial in its first slot; this is the form the
frame-derivative cancellation in `sum_inner_covCurvature_eq` is fed. -/
noncomputable def curvatureBilinFst (Z W : Π y : M, TangentSpace I y) (x : M)
    (hW : CMDiff 2 (T% W)) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace I x)).comp
    (TensorialAt.mkHom (fun V ↦ cov.curvature V Z W x) x
      (cov.tensorialAt_curvature_fst (V := Z) hW x) :
        TangentSpace I x →L[ℝ] TangentSpace I x)

omit [T2Space M] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov 2] in
theorem curvatureBilinFst_apply {Z W : Π y : M, TangentSpace I y} {x : M}
    (hW : CMDiff 2 (T% W)) {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov.curvatureBilinFst Z W x hW (σ x) v = ⟪cov.curvature σ Z W x, v⟫ := by
  show ⟪(TensorialAt.mkHom (fun V ↦ cov.curvature V Z W x) x
      (cov.tensorialAt_curvature_fst (V := Z) hW x)) (σ x), v⟫ = _
  rw [TensorialAt.mkHom_apply _ hσ]

/-- **`(∇_X Ric)(Z,W)`**, written out: the covariant derivative of the Ricci tensor,
in the same shape `Variation.lean`'s `covBilin` gives for a bilinear form field. Kept as
its own definition because `Ric` is not carried here as a `M → E →L[ℝ] E →L[ℝ] ℝ`. -/
noncomputable def covRicci (X Z W : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ cov.ricci Z W y) x (X x)
    - cov.ricci (fun y ↦ cov Z y (X y)) W x
    - cov.ricci Z (fun y ↦ cov W y (X y)) x

omit [T2Space M] in
/-- **The first-slot trace commutes with `∇` for the curvature**:
`∑ᵢ ⟪(∇_X Rm)(eᵢ,Z)W, eᵢ⟫ = X(Ric(Z,W)) − Ric(∇_X Z, W) − Ric(Z, ∇_X W)`,
whose right-hand side is `(∇_X Ric)(Z,W)`.

This is the analogue for the curvature endomorphism of `TraceCov.lean`'s metric-trace
lemma, and has the same shape: the frame is not parallel, so the coefficients
`⟪∇_X eᵢ, eⱼ⟫` appear, and they are antisymmetric (`inner_cov_antisymm`) against a
symmetric pairing, hence sum to zero (`sum_bilin_of_antisymm`). The pairing is
`curvatureBilinFst`. -/
theorem sum_inner_covCurvature_eq
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) :
    ∑ i, ⟪cov.covCurvature X (fr i) Z W x, fr i x⟫ = cov.covRicci X Z W x := by
  classical
  rw [covRicci]
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hfrm : ∀ (y : M) (i : ι), MDiffAt (T% (fr i)) y := fun y i ↦ (hfr i).mdifferentiable h2 y
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hcs : ∀ i, MDiffAt (T% (fun y ↦ cov.curvature (fr i) Z W y)) x := fun i ↦
    ((cov.contMDiff_curvature (hfr i) hZ hW).mdifferentiable h1) x
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  -- `Ric(Z,W)` is the frame sum on a neighbourhood of `x`
  have hloc : (fun y ↦ cov.ricci Z W y)
      =ᶠ[𝓝 x] fun y ↦ ∑ i, ⟪cov.curvature (fr i) Z W y, fr i y⟫ := by
    filter_upwards [hu.mem_nhds hx] with y hy
    obtain ⟨c, hc⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
    exact cov.ricci_eq_sum_inner_frame hW2 c (fun i ↦ hfrm y i) (fun i ↦ (hc i).symm)
  -- differentiate it, term by term, by metric compatibility
  have hinner : ∀ i, MDiffAt (fun y ↦ ⟪cov.curvature (fr i) Z W y, fr i y⟫) x := fun i ↦
    (((cov.contMDiff_curvature (hfr i) hZ hW) x).inner_bundle'
      (((hfr i).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) x)).mdifferentiableAt h1
  have hderiv : mvfderiv I (fun y ↦ cov.ricci Z W y) x (X x)
      = ∑ i, (⟪cov (fun y ↦ cov.curvature (fr i) Z W y) x (X x), fr i x⟫
          + ⟪cov.curvature (fr i) Z W x, cov (fr i) x (X x)⟫) := by
    rw [hloc.mvfderiv_eq, mvfderiv_fun_sum (fun i _ ↦ hinner i), _root_.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦
      hcov.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X (hcs i) (hfrm x i)
  -- the two `Ric` terms
  have hC : ∑ i, ⟪cov.curvature (fr i) (fun y ↦ cov Z y (X y)) W x, fr i x⟫
      = cov.ricci (fun y ↦ cov Z y (X y)) W x :=
    (cov.ricci_eq_sum_inner_frame hW2 b (fun i ↦ hfrm x i) (fun i ↦ (hb i).symm)).symm
  have hD : ∑ i, ⟪cov.curvature (fr i) Z (fun y ↦ cov W y (X y)) x, fr i x⟫
      = cov.ricci Z (fun y ↦ cov W y (X y)) x :=
    (cov.ricci_eq_sum_inner_frame hDW b (fun i ↦ hfrm x i) (fun i ↦ (hb i).symm)).symm
  -- the frame-derivative terms cancel: antisymmetric coefficients against a symmetric pairing
  have hDF : ∀ i j, ⟪cov (fr i) x (X x), b j⟫ = -⟪cov (fr j) x (X x), b i⟫ := by
    intro i j
    rw [hb i, hb j]
    exact cov.inner_cov_antisymm (X := X) hcov (fun i ↦ hfrm x i)
      (fun i j ↦ by
        filter_upwards [hu.mem_nhds hx] with y hy
        rw [orthonormal_iff_ite.mp (hs.orthonormal hy) i j,
          orthonormal_iff_ite.mp (hs.orthonormal hx) i j]) i j
  have hcancel : ∑ i, (⟪cov.curvature (fun y ↦ cov (fr i) y (X y)) Z W x, fr i x⟫
      + ⟪cov.curvature (fr i) Z W x, cov (fr i) x (X x)⟫) = 0 := by
    have hzero := sum_bilin_of_antisymm b (cov.curvatureBilinFst Z W x hW2)
      (fun i ↦ cov (fr i) x (X x)) hDF
    rw [← hzero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hDfr : MDiffAt (T% (fun y ↦ cov (fr i) y (X y))) x :=
      cov.mdiffAt_cov_apply (hfr i) (hX.mdifferentiable h2 x)
    have e1 := cov.curvatureBilinFst_apply (Z := Z) (W := W) (x := x) hW2 hDfr (fr i x)
    have e2 := cov.curvatureBilinFst_apply (Z := Z) (W := W) (x := x) hW2 (hfrm x i)
      (cov (fr i) x (X x))
    rw [hb i, e1, e2]
  -- expand the left-hand side and combine
  have hexp : ∑ i, ⟪cov.covCurvature X (fr i) Z W x, fr i x⟫
      = (∑ i, ⟪cov (fun y ↦ cov.curvature (fr i) Z W y) x (X x), fr i x⟫)
        - (∑ i, ⟪cov.curvature (fun y ↦ cov (fr i) y (X y)) Z W x, fr i x⟫)
        - (∑ i, ⟪cov.curvature (fr i) (fun y ↦ cov Z y (X y)) W x, fr i x⟫)
        - ∑ i, ⟪cov.curvature (fr i) Z (fun y ↦ cov W y (X y)) x, fr i x⟫ := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show ⟪cov (fun y ↦ cov.curvature (fr i) Z W y) x (X x)
        - cov.curvature (fun y ↦ cov (fr i) y (X y)) Z W x
        - cov.curvature (fr i) (fun y ↦ cov Z y (X y)) W x
        - cov.curvature (fr i) Z (fun y ↦ cov W y (X y)) x, fr i x⟫ = _
    rw [inner_sub_left, inner_sub_left, inner_sub_left]
  rw [Finset.sum_add_distrib] at hderiv hcancel
  rw [hexp, ← hC, ← hD]
  linarith [hderiv, hcancel]

/-- **The contracted second Bianchi identity, first contraction**:
`div Rm(Y,Z,W) = (∇_Y Ric)(Z,W) − (∇_Z Ric)(Y,W)`.

The traced second Bianchi identity with both of its sums identified as covariant
derivatives of `Ric`. Needs the connection to be both torsion-free and metric --- i.e.
Levi-Civita: torsion-freeness for the second Bianchi identity itself, metric
compatibility for the trace to commute with `∇`. -/
theorem divCurvature_eq_covRicci_sub (hcov : cov.torsion = 0)
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W))
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) :
    cov.divCurvature Y Z W x = cov.covRicci Y Z W x - cov.covRicci Z Y W x := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  rw [cov.divCurvature_eq_sub_sum hcov hY hZ hW hfr b (fun i ↦ (hb i).symm),
    cov.sum_inner_covCurvature_eq hmet hY hZ hW hs hu hx hfr,
    cov.sum_inner_covCurvature_eq hmet hZ hY hW hs hu hx hfr]

end TraceDeriv

section PairSymm

omit [T2Space M] in
/-- **`∇Rm` paired against a vector, expanded.** For a metric connection the leading
`∇_X` of `⟪Rm(A,B)C, D⟫` can be moved onto the pairing, which turns
`⟪(∇_X Rm)(A,B)C, D⟫` into the derivative of the `(0,4)` tensor minus one correction per
slot --- four from `∇Rm` itself and a fifth, `⟪Rm(A,B)C, ∇_X D⟫`, from the metric. -/
theorem inner_covCurvature_expand
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X A B C D : Π y : M, TangentSpace I y} {x : M}
    (hA : CMDiff 2 (T% A)) (hB : CMDiff 2 (T% B)) (hC : CMDiff 3 (T% C))
    (hD : CMDiff 2 (T% D)) :
    ⟪cov.covCurvature X A B C x, D x⟫
      = mvfderiv I (fun y ↦ ⟪cov.curvature A B C y, D y⟫) x (X x)
        - ⟪cov.curvature (fun y ↦ cov A y (X y)) B C x, D x⟫
        - ⟪cov.curvature A (fun y ↦ cov B y (X y)) C x, D x⟫
        - ⟪cov.curvature A B (fun y ↦ cov C y (X y)) x, D x⟫
        - ⟪cov.curvature A B C x, cov D x (X x)⟫ := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hcs : MDiffAt (T% (fun y ↦ cov.curvature A B C y)) x :=
    ((cov.contMDiff_curvature hA hB hC).mdifferentiable h1) x
  have hlead := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X hcs
    ((hD.mdifferentiable h2) x)
  show ⟪cov (fun y ↦ cov.curvature A B C y) x (X x)
      - cov.curvature (fun y ↦ cov A y (X y)) B C x
      - cov.curvature A (fun y ↦ cov B y (X y)) C x
      - cov.curvature A B (fun y ↦ cov C y (X y)) x, D x⟫ = _
  rw [inner_sub_left, inner_sub_left, inner_sub_left, hlead]
  ring

omit [T2Space M] in
/-- **Pair symmetry of `∇Rm`**: `⟪(∇_X Rm)(A,B)C, D⟫ = ⟪(∇_X Rm)(C,D)A, B⟫`.

The `(0,4)` tensor `⟪Rm(A,B)C,D⟫` has this symmetry pointwise
(`inner_curvature_pair_symm`), and `inner_covCurvature_expand` writes `∇Rm` entirely in
terms of it: the derivative of the tensor, plus one correction per slot. The correction
terms of the two sides are the same five numbers in a different order. -/
theorem inner_covCurvature_pair_symm
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    {X A B C D : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B))
    (hC : CMDiff 3 (T% C)) (hD : CMDiff 3 (T% D)) :
    ⟪cov.covCurvature X A B C x, D x⟫ = ⟪cov.covCurvature X C D A x, B x⟫ := by
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC2 : CMDiff 2 (T% C) := hC.of_le (by norm_num)
  have hD2 : CMDiff 2 (T% D) := hD.of_le (by norm_num)
  have hDA : CMDiff 2 (T% (fun y ↦ cov A y (X y))) := cov.contMDiff_cov_apply hA hX
  have hDB : CMDiff 2 (T% (fun y ↦ cov B y (X y))) := cov.contMDiff_cov_apply hB hX
  have hDC : CMDiff 2 (T% (fun y ↦ cov C y (X y))) := cov.contMDiff_cov_apply hC hX
  have hDD : CMDiff 2 (T% (fun y ↦ cov D y (X y))) := cov.contMDiff_cov_apply hD hX
  have hfun : (fun y ↦ ⟪cov.curvature A B C y, D y⟫)
      = fun y ↦ ⟪cov.curvature C D A y, B y⟫ := by
    funext y
    exact cov.inner_curvature_pair_symm hmet htor hA2 hB2 hC2 hD2
  rw [cov.inner_covCurvature_expand hmet hA2 hB2 hC hD2,
    cov.inner_covCurvature_expand hmet hC2 hD2 hA hB2, hfun,
    cov.inner_curvature_pair_symm (X := fun y ↦ cov A y (X y)) hmet htor hDA hB2 hC2 hD2,
    cov.inner_curvature_pair_symm (X := A) (Y := fun y ↦ cov B y (X y)) hmet htor hA2 hDB
      hC2 hD2,
    cov.inner_curvature_pair_symm (Z := fun y ↦ cov C y (X y)) hmet htor hA2 hB2 hDC hD2,
    cov.inner_curvature_pair_symm (W := fun y ↦ cov D y (X y)) hmet htor hA2 hB2 hC2 hDD]
  ring

end PairSymm

section SecondContraction

open RicciFlowBlueprint

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
/-- `∇Ric` computed through `covBilin` on the Ricci form agrees with `covRicci`. The
fields are asked for `C³` so that `∇_X Z` and `∇_X W` are `C²`, which is what
`ricciForm_apply_field` needs of them. -/
theorem covBilin_ricciForm_eq_covRicci {X Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hZ : CMDiff 3 (T% Z)) (hW : CMDiff 3 (T% W)) :
    cov.covBilin (fun y ↦ cov.ricciForm y) X Z W x = cov.covRicci X Z W x := by
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hDZ : CMDiff 2 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hfun : (fun y ↦ cov.ricciForm y (Z y) (W y)) = fun y ↦ cov.ricci Z W y := by
    funext y; exact cov.ricciForm_apply_field hZ2 hW2
  have e1 := cov.ricciForm_apply_field (X := fun y ↦ cov Z y (X y)) (Y := W) (x := x) hDZ hW2
  have e2 := cov.ricciForm_apply_field (X := Z) (Y := fun y ↦ cov W y (X y)) (x := x) hZ2 hDW
  simp only [covBilin, covRicci, hfun, e1, e2]

/-- **`∇Ric` is symmetric**, because `Ric` is (`ricci_symm`, so a Levi-Civita
connection). -/
theorem covRicci_symm (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) {X Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hZ : CMDiff 3 (T% Z)) (hW : CMDiff 3 (T% W)) :
    cov.covRicci X Z W x = cov.covRicci X W Z x := by
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hDZ : CMDiff 2 (T% (fun y ↦ cov Z y (X y))) := cov.contMDiff_cov_apply hZ hX
  have hDW : CMDiff 2 (T% (fun y ↦ cov W y (X y))) := cov.contMDiff_cov_apply hW hX
  have hfun : (fun y ↦ cov.ricci Z W y) = fun y ↦ cov.ricci W Z y := by
    funext y; exact cov.ricci_symm hmet htor hZ2 hW2
  simp only [covRicci, hfun,
    cov.ricci_symm (X := fun y ↦ cov Z y (X y)) (Y := W) hmet htor hDZ hW2,
    cov.ricci_symm (X := Z) (Y := fun y ↦ cov W y (X y)) hmet htor hZ2 hDW]
  ring

/-- **The contracted second Bianchi identity, second contraction**:
`2 · div Ric(Y) = Y(scal)`, i.e. `div Ric = ½ d scal`.

Contract the first contraction over the remaining two slots. Both sides of
`div Rm(Y,eⱼ,eⱼ) = (∇_Y Ric)(eⱼ,eⱼ) − (∇_{eⱼ}Ric)(Y,eⱼ)` are summed over `j`. On the
right that gives `Y(scal) − div Ric(Y)`, the first sum by the metric trace commuting with
`∇` and the second by symmetry of `∇Ric`. On the left, pair symmetry of `∇Rm` turns
`⟪(∇_{eᵢ}Rm)(Y,eⱼ)eⱼ, eᵢ⟫` into `⟪(∇_{eᵢ}Rm)(eⱼ,eᵢ)Y, eⱼ⟫`, whose sum over `j` is
`(∇_{eᵢ}Ric)(eᵢ,Y)`; summing over `i` gives `div Ric(Y)` again. Hence
`div Ric(Y) = Y(scal) − div Ric(Y)`.

`div Ric` appears here as a frame sum rather than as a definition; the right-hand side
does not mention the frame, so the statement contains its own frame-independence. -/
theorem two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt
    (htor : cov.torsion = 0)
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {Y : Π y : M, TangentSpace I y} {x : M} (hY : CMDiff 3 (T% Y))
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    2 * ∑ i, cov.covRicci (fr i) (fr i) Y x
      = mvfderiv I (fun y ↦ cov.scalarCurvatureAt y) x (Y x) := by
  classical
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  have hfrm : ∀ (y : M) (i : ι), MDiffAt (T% (fr i)) y := fun y i ↦
    (hfr2 i).mdifferentiable h2 y
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  -- `Ric(eⱼ,eⱼ)` is differentiable at `x`: near `x` it is a frame sum of inner products
  have hRic : ∀ i, MDiffAt (fun y ↦ cov.ricciForm y (fr i y) (fr i y)) x := by
    intro i
    have heq : (fun y ↦ ∑ k, ⟪cov.curvature (fr k) (fr i) (fr i) y, fr k y⟫)
        =ᶠ[𝓝 x] fun y ↦ cov.ricciForm y (fr i y) (fr i y) := by
      filter_upwards [hu.mem_nhds hx] with y hy
      obtain ⟨c, hc⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
      rw [cov.ricciForm_apply_field (x := y) (hfr2 i) (hfr2 i)]
      exact (cov.ricci_eq_sum_inner_frame (x := y) (hfr2 i) c (fun k ↦ hfrm y k)
        (fun k ↦ (hc k).symm)).symm
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
    exact mdifferentiableAt_fun_sum fun k _ ↦
      (((cov.contMDiff_curvature (hfr2 k) (hfr2 i) (hfr i)) x).inner_bundle'
        (((hfr2 k).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) x)).mdifferentiableAt h1
  -- right-hand side: the `Y`-derivative of the scalar curvature
  have hscal : mvfderiv I (fun y ↦ cov.scalarCurvatureAt y) x (Y x)
      = ∑ i, cov.covRicci Y (fr i) (fr i) x := by
    rw [cov.mvfderiv_scalarCurvatureAt_eq_sum_covBilin hmet hs hu hx hRic]
    exact Finset.sum_congr rfl fun i _ ↦
      cov.covBilin_ricciForm_eq_covRicci hY2 (hfr i) (hfr i)
  -- the first contraction, summed over the frame
  have hfirst : ∑ i, cov.divCurvature Y (fr i) (fr i) x
      = (∑ i, cov.covRicci Y (fr i) (fr i) x) - ∑ i, cov.covRicci (fr i) Y (fr i) x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      cov.divCurvature_eq_covRicci_sub htor hmet hY2 (hfr2 i) (hfr i) hs hu hx hfr2
  -- the left-hand side is `div Ric` again, by pair symmetry of `∇Rm`
  have hleft : ∑ i, cov.divCurvature Y (fr i) (fr i) x
      = ∑ i, cov.covRicci (fr i) (fr i) Y x := by
    have hstep : ∀ i, cov.divCurvature Y (fr i) (fr i) x
        = ∑ j, ⟪cov.covCurvature (fr j) Y (fr i) (fr i) x, fr j x⟫ := fun i ↦
      cov.divCurvature_eq_sum_frame hY2 (hfr2 i) (hfr i) hfr2 b (fun k ↦ (hb k).symm)
    calc ∑ i, cov.divCurvature Y (fr i) (fr i) x
        = ∑ i, ∑ j, ⟪cov.covCurvature (fr j) Y (fr i) (fr i) x, fr j x⟫ :=
          Finset.sum_congr rfl fun i _ ↦ hstep i
      _ = ∑ j, ∑ i, ⟪cov.covCurvature (fr j) (fr i) (fr j) Y x, fr i x⟫ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦
            cov.inner_covCurvature_pair_symm hmet htor (hfr2 j) hY (hfr i) (hfr i) (hfr j)
      _ = ∑ j, cov.covRicci (fr j) (fr j) Y x :=
          Finset.sum_congr rfl fun j _ ↦
            cov.sum_inner_covCurvature_eq hmet (hfr2 j) (hfr2 j) hY hs hu hx hfr2
  -- `∇Ric` is symmetric, so the two `div Ric` sums agree
  have hsymm : ∑ i, cov.covRicci (fr i) Y (fr i) x = ∑ i, cov.covRicci (fr i) (fr i) Y x :=
    Finset.sum_congr rfl fun i _ ↦
      cov.covRicci_symm hmet htor (hfr2 i) hY (hfr i)
  rw [hscal]
  rw [hleft, hsymm] at hfirst
  linarith [hfirst]

end SecondContraction

end CovariantDerivative
