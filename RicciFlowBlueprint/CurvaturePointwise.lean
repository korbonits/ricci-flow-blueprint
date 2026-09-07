/-
`R(X,Y)Z` at `x` depends only on `Z x`.

The curvature is `C^∞(M)`-linear in its third slot (`curvature_smul_right`,
`curvature_sum_right`) and local there (`curvature_congr_third_of_eventuallyEq`).
Expanding `Z` in a local frame and globalising the pieces
(`exists_contMDiff_eventuallyEq`, `exists_contMDiff_eventuallyEq_fun`) turns those
into genuine pointwise dependence.

Note the target is a *congruence*, not `TensorialAt`: that structure demands its
identities for merely differentiable sections, which the third slot cannot satisfy,
since `∇_X ∇_Y Z` is meaningless for such `Z`. See `CLAUDE.md`, corrected belief #1.
-/
import RicciFlowBlueprint.GlobalExtension
import RicciFlowBlueprint.OrthonormalFrame
import RicciFlowBlueprint.LeviCivitaSmooth
import RicciFlowBlueprint.Scalar

open Bundle Filter Module
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

omit [CompleteSpace E] in
-- BENCH: curvature-smul-third-global
/-- **`C^∞(M)`-linearity in the third slot**, with every side condition discharged from
globally `C²` data: `R(X,Y)(f • Z) = f(x) • R(X,Y)Z`. -/
theorem curvature_smul_third {f : M → ℝ} {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiff 2 (T% Z)) :
    cov.curvature X Y (f • Z) x = f x • cov.curvature X Y Z x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have h12 : (1 : ℕ∞ω) + 1 ≤ 2 := by norm_num
  have hXm : MDiffAt (T% X) x := hX.mdifferentiableAt h2
  have hYm : MDiffAt (T% Y) x := hY.mdifferentiableAt h2
  have hZm : MDiff (T% Z) := hZ.mdifferentiable h2
  have hfm : MDiff f := hf.mdifferentiable h2
  -- the two directional derivatives of `f`, `C¹` hence differentiable
  have hYf : MDiffAt (fun y ↦ d% f y (Y y)) x :=
    (RicciFlowBlueprint.contMDiffAt_mvfderiv_apply (hf x) (hY.of_le (by norm_num)) h12).mdifferentiableAt
      one_ne_zero
  have hXf : MDiffAt (fun y ↦ d% f y (X y)) x :=
    (RicciFlowBlueprint.contMDiffAt_mvfderiv_apply (hf x) (hX.of_le (by norm_num)) h12).mdifferentiableAt
      one_ne_zero
  have hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x := cov.mdiffAt_cov_apply hZ hYm
  have hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x := cov.mdiffAt_cov_apply hZ hXm
  exact cov.curvature_smul_right f X Y Z hfm (hf x) hXm hYm hZm hYZ hXZ hYf hXf
    ((hfm x).smul_section hYZ) ((hfm x).smul_section hXZ)
    (hYf.smul_section (hZm x)) (hXf.smul_section (hZm x))

omit [CompleteSpace E] in
-- BENCH: curvature-sum-smul-third
/-- The third slot applied to a finite `C²` combination `∑ fᵢ • Zᵢ`. -/
theorem curvature_sum_smul_third {ι : Type*} {s : Finset ι} {f : ι → M → ℝ}
    {Z : ι → Π y : M, TangentSpace I y} {X Y : Π y : M, TangentSpace I y} {x : M}
    (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) 2 (f i))
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : ∀ i ∈ s, CMDiff 2 (T% (Z i))) :
    cov.curvature X Y (fun y ↦ ∑ i ∈ s, f i y • Z i y) x
      = ∑ i ∈ s, f i x • cov.curvature X Y (Z i) x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hsec : ∀ i ∈ s, CMDiff 2 (T% (f i • Z i)) := fun i hi ↦ (hf i hi).smul_section (hZ i hi)
  have e : (fun y ↦ ∑ i ∈ s, f i y • Z i y) = fun y ↦ ∑ i ∈ s, (f i • Z i) y := rfl
  rw [e, cov.curvature_sum_right hsec (hX.mdifferentiableAt h2) (hY.mdifferentiableAt h2)]
  exact Finset.sum_congr rfl fun i hi ↦ cov.curvature_smul_third (hf i hi) hX hY (hZ i hi)

section Pointwise

variable [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]

open RicciFlowBlueprint

omit [CompleteSpace E] in
-- BENCH: curvature-pointwise-third
/-- **`R(X,Y)Z` at `x` depends only on `Z x`.** Expand `Z` in a local frame near `x`,
globalise the frame fields and the coefficients, and use `C^∞(M)`-linearity in the third
slot; the coefficients at `x` are determined by `Z x`. -/
theorem curvature_congr_third {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiff 2 (T% Z)) (hZ' : CMDiff 2 (T% Z'))
    (hval : Z x = Z' x) :
    cov.curvature X Y Z x = cov.curvature X Y Z' x := by
  classical
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  set e := trivializationAt E (TangentSpace I (M := M)) x with he
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hu : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hxe
  set b := Module.finBasis ℝ E with hb
  -- the frame, made opaque: writing `b.orthonormalFrame e` again would re-elaborate the
  -- bundle and pick `Trivial.topologicalSpace` (lean4#14949)
  obtain ⟨fr, hs, hfrsm⟩ : ∃ fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      IsOrthonormalFrameOn I E 2 fr e.baseSet ∧ ∀ i, CMDiff[e.baseSet] 2 (T% (fr i)) :=
    ⟨_, b.orthonormalFrame_isOrthonormalFrameOn (IB := I) (n := 2) e,
      fun i ↦ b.contMDiffOn_orthonormalFrame_baseSet e i⟩
  -- globalise the frame fields
  have hframe : ∀ i, ∃ Ei : Π y : M, TangentSpace I y, CMDiff 2 (T% Ei) ∧
      Ei =ᶠ[𝓝 x] fr i := by
    intro i
    obtain ⟨Ei, hEi, hEieq⟩ := exists_contMDiff_eventuallyEq (n := 2) hu (hfrsm i)
    exact ⟨Ei, by simpa using hEi, hEieq⟩
  choose Ei hEi hEieq using hframe
  -- globalise the coefficients of a section
  have hcoeff : ∀ (W : Π y : M, TangentSpace I y), CMDiff 2 (T% W) → ∀ i,
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 2 g ∧
        g =ᶠ[𝓝 x] (LinearMap.piApply (hs.coeff i) W) := by
    intro W hW i
    obtain ⟨g, hg, hgeq⟩ :=
      exists_contMDiff_eventuallyEq_fun (n := 2) hu (hs.contMDiffOn_coeff hW.contMDiffOn i)
    exact ⟨g, by simpa using hg, hgeq⟩
  -- the expansion of a section as a global `C²` combination, valid near `x`
  have key : ∀ (W : Π y : M, TangentSpace I y) (hW : CMDiff 2 (T% W)),
      cov.curvature X Y W x
        = ∑ i, hs.coeff i x (W x) • cov.curvature X Y (Ei i) x := by
    intro W hW
    choose g hg hgeq using hcoeff W hW
    have hsum : CMDiff 2 (T% (fun y ↦ ∑ i, g i y • Ei i y)) :=
      ContMDiff.sum_section fun i _ ↦ (hg i).smul_section (hEi i)
    have heq : W =ᶠ[𝓝 x] fun y ↦ ∑ i, g i y • Ei i y := by
      have hall : ∀ᶠ y in 𝓝 x, ∀ i, g i y = hs.coeff i y (W y) ∧
          Ei i y = fr i y :=
        Filter.eventually_all.mpr fun i ↦ (hgeq i).and (hEieq i)
      filter_upwards [hs.toIsLocalFrameOn.eventually_eq_sum_coeff_smul W hu, hall] with y hy hy'
      rw [hy]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [(hy' i).1, (hy' i).2]
    rw [cov.curvature_congr_third_of_eventuallyEq hW hsum
        (hX.mdifferentiableAt h2) (hY.mdifferentiableAt h2) heq,
      cov.curvature_sum_smul_third (fun i _ ↦ hg i) hX hY (fun i _ ↦ hEi i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hgeq i).eq_of_nhds]
    rfl
  rw [key Z hZ, key Z' hZ']
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [hs.toIsLocalFrameOn.coeff_congr hval i]

omit [CompleteSpace E] in
-- BENCH: ricci-congr-snd-manifold
/-- **Ricci depends on its second argument only through its value at `x`**, on a general
manifold. This discharges the hypothesis `h3` that `Scalar.lean`'s `ricci_congr_snd` had to
assume (it was a theorem on the model space only). -/
theorem ricci_congr_snd_of_eq {X Y Y' : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y'))
    (hval : Y x = Y' x) :
    cov.ricci X Y x = cov.ricci X Y' x := by
  rw [cov.ricci_eq_trace hY x, cov.ricci_eq_trace hY' x]
  congr 1
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend, ContinuousLinearMap.coe_coe]
  exact cov.curvature_congr_third (FiberBundle.contMDiffAt_extend I E v) hX hY hY' hval

omit [CompleteSpace E] in
-- BENCH: ricci-congr-manifold
/-- **Ricci depends on both arguments only through their values at `x`.** -/
theorem ricci_congr_of_eq {X X' Y Y' : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hX' : CMDiff 2 (T% X'))
    (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y'))
    (hxx : X x = X' x) (hyy : Y x = Y' x) :
    cov.ricci X Y x = cov.ricci X' Y' x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  rw [cov.ricci_congr_fst hY ((hX.mdifferentiable h2) x) ((hX'.mdifferentiable h2) x) hxx]
  exact cov.ricci_congr_snd_of_eq (hX' x) hY hY' hyy

/-- **Ricci curvature as a function of tangent vectors.** Evaluated on globally `C²`
extensions, which exist by `exists_contMDiff_two_extension` and give the same answer by
`ricci_congr_of_eq`. This is the shape Chow-Liao-Qin's `metricRicciAt` has, reached here
without a tensor bundle. -/
noncomputable def ricciAt (x : M) (v w : TangentSpace I x) : ℝ :=
  cov.ricci (RicciFlowBlueprint.exists_contMDiff_two_extension v).choose
    (RicciFlowBlueprint.exists_contMDiff_two_extension w).choose x

omit [CompleteSpace E] in
-- BENCH: ricci-at-eq
/-- `ricciAt` computes `ricci` on any globally `C²` fields with the given values. -/
theorem ricciAt_eq {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) :
    cov.ricciAt x (X x) (Y x) = cov.ricci X Y x := by
  obtain ⟨hXc, hXv⟩ := (RicciFlowBlueprint.exists_contMDiff_two_extension (X x)).choose_spec
  obtain ⟨hYc, hYv⟩ := (RicciFlowBlueprint.exists_contMDiff_two_extension (Y x)).choose_spec
  exact cov.ricci_congr_of_eq hXc hX hYc hY hXv hYv

end Pointwise

end CovariantDerivative
