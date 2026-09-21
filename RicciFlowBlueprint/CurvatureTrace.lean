/-
**The first-slot trace of `∇²Rm` is `∇²Ric`, and hence `tr₁(Δ Rm) = Δ_g Ric`.**

`Divergence.lean` proves that the first-slot trace commutes with one covariant derivative
(`sum_inner_covCurvature_eq`: `∑ᵢ ⟪(∇_X Rm)(eᵢ,Z)W, eᵢ⟫ = (∇_X Ric)(Z,W)`). This file does
the same one level up, which is what the evolution equation of the dimension-3 curvature
operator `Rm₃ = scal·Id − 2 Ric♯` consumes: tracing `∂ₜRm = Δ Rm + Q` in its first slot
turns the left-hand side into `∂ₜRic` and `Δ Rm` into `Δ_g Ric`.

**The five corrections of `∇²Rm` meet the three of `∇²h` exactly.** Of `cov2Curvature`'s
five terms, three are `∇Rm` with one of `V`, `X`, `Z` differentiated, and each traces to
the matching term of `cov2Bilin` by `sum_inner_covCurvature_eq`. The remaining two — the
leading `∇_U` of the traced section, and the correction in the *frame* slot — must together
produce `mvfderiv` of the traced function, and the difference between them is exactly the
frame-derivative residue

  `∑ᵢ [⟪(∇_V Rm)(∇_U eᵢ, X)Z, eᵢ⟫ + ⟪(∇_V Rm)(eᵢ,X)Z, ∇_U eᵢ⟫] = 0`,

antisymmetric coefficients against a symmetric pairing, as in `TraceCov.lean`.

**But `sum_bilin_of_antisymm` does NOT apply here**, and that is the one real obstacle. That
lemma wants a bundled `B : E →L[ℝ] E →L[ℝ] ℝ`, and the pairing at hand is `∇Rm` in its
*second* slot, where tensoriality (`covCurvature_smul_snd`) demands a `C²` coefficient — so
`TensorialAt.mkHom`, which quantifies over merely differentiable sections, is unavailable
(corrected belief 1). The remedy is to expand the frame derivative in the frame with
**constant** coefficients `cᵢⱼ = ⟪∇_U eᵢ, eⱼ⟫`, legitimate because the second slot is
*pointwise* (`covCurvature_congr_snd`) and constants are smooth; the cancellation is then
purely combinatorial (`sum_antisymm_pair_eq_zero`) and no bilinear form is ever bundled.

Regularity: the outer direction `U` and inner direction `V` at `C³`, the frame at `C³`, and
the two `Rm` slots `X`, `Z` at `C⁴` — the last slot expensive as everywhere in this tower,
and `X` one level above `V` because `∇_U X` has to keep the `C³` that
`covBilin_ricciForm_eq_covRicci` wants of a form slot.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.BianchiDeriv
import RicciFlowBlueprint.BilinLaplacian
import RicciFlowBlueprint.Divergence

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

section Algebra

/-- **An antisymmetric coefficient matrix against a symmetrised pairing sums to zero.**
The summand at `(i,j)` is the negative of the one at `(j,i)`, so the double sum is its own
negative. This is `TraceCov.lean`'s `sum_bilin_of_antisymm` with the bilinearity stripped
out: nothing here needs `P` to come from a bilinear form, which is what makes it usable in
a slot where no bundled form exists. -/
theorem sum_antisymm_pair_eq_zero {ι : Type*} [Fintype ι] (c P : ι → ι → ℝ)
    (hc : ∀ i j, c i j = -c j i) :
    ∑ i, ∑ j, c i j * (P i j + P j i) = 0 := by
  classical
  have hS : ∑ i, ∑ j, c i j * (P i j + P j i)
      = -∑ i, ∑ j, c i j * (P i j + P j i) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hc j i]; ring
  linarith [hS]

/-- Expanding the second slot of a real inner product over a finite linear combination. -/
theorem inner_sum_smul_right {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (v : F) (c : ι → ℝ) (e : ι → F) :
    ⟪v, ∑ j, c j • e j⟫ = ∑ j, c j * ⟪v, e j⟫ := by
  rw [inner_sum]
  exact Finset.sum_congr rfl fun j _ ↦ real_inner_smul_right _ _ _

/-- Expanding the first slot of a real inner product over a finite linear combination. -/
theorem inner_sum_smul_left {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (e : ι → F) (w : F) :
    ⟪∑ j, c j • e j, w⟫ = ∑ j, c j * ⟪e j, w⟫ := by
  rw [sum_inner]
  exact Finset.sum_congr rfl fun j _ ↦ real_inner_smul_left _ _ _

/-- The first slot of a real inner product over a finite sum, stated over a variable inner
product space so that it applies to `TangentSpace`-typed sums (where `rw` with mathlib's
`sum_inner` picks `E`'s own additive structure). -/
theorem sum_inner_fin {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (e : ι → F) (w : F) :
    ⟪∑ j, e j, w⟫ = ∑ j, ⟪e j, w⟫ := sum_inner _ _ _

end Algebra

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

variable {ι : Type*} [Fintype ι]

open RicciFlowBlueprint

/-- **The first-slot trace commutes with `∇²`**:
`∑ᵢ ⟪(∇²_{U,V}Rm)(eᵢ,X)Z, eᵢ⟫ = (∇²_{U,V}Ric)(X,Z)`.

`Divergence.lean`'s `sum_inner_covCurvature_eq` one level up. Three of `∇²Rm`'s five
corrections trace to the three of `∇²Ric` directly; the other two combine into the
derivative of the traced function, up to the frame-derivative residue, which vanishes
because the frame's connection coefficients are antisymmetric. -/
theorem sum_inner_cov2Curvature_fst_eq_cov2Bilin
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {U V X Z : Π y : M, TangentSpace I y} {x : M}
    (hU : CMDiff 3 (T% U)) (hV : CMDiff 3 (T% V)) (hX : CMDiff 4 (T% X))
    (hZ : CMDiff 4 (T% Z))
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    ∑ i, ⟪cov.cov2Curvature U V (fr i) X Z x, fr i x⟫
      = cov.cov2Bilin (fun y ↦ cov.ricciForm y) U V X Z x := by
  classical
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hU2 : CMDiff 2 (T% U) := hU.of_le (by norm_num)
  have hV2 : CMDiff 2 (T% V) := hV.of_le (by norm_num)
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hX3 : CMDiff 3 (T% X) := hX.of_le (by norm_num)
  have hZ3 : CMDiff 3 (T% Z) := hZ.of_le (by norm_num)
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  have hfrm : ∀ (y : M) (i : ι), MDiffAt (T% (fr i)) y := fun y i ↦
    (hfr i).mdifferentiable (by norm_num) y
  -- the differentiated fields
  have hDV : CMDiff 2 (T% (fun y ↦ cov V y (U y))) := cov.contMDiff_cov_apply hV hU2
  have hDX : CMDiff 3 (T% (fun y ↦ cov X y (U y))) := cov.contMDiff_cov_apply hX hU
  have hDZ : CMDiff 3 (T% (fun y ↦ cov Z y (U y))) := cov.contMDiff_cov_apply hZ hU
  have hDX2 : CMDiff 2 (T% (fun y ↦ cov X y (U y))) := hDX.of_le (by norm_num)
  have hDfr : ∀ i, CMDiff 2 (T% (fun y ↦ cov (fr i) y (U y))) := fun i ↦
    cov.contMDiff_cov_apply (hfr i) hU2
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  -- the three corrections that match termwise
  have hT2 : ∑ i, ⟪cov.covCurvature (fun y ↦ cov V y (U y)) (fr i) X Z x, fr i x⟫
      = cov.covBilin (fun y ↦ cov.ricciForm y) (fun y ↦ cov V y (U y)) X Z x := by
    rw [cov.covBilin_ricciForm_eq_covRicci hDV hX3 hZ3]
    exact cov.sum_inner_covCurvature_eq hmet hDV hX2 hZ3 hs hu hx hfr2
  have hT4 : ∑ i, ⟪cov.covCurvature V (fr i) (fun y ↦ cov X y (U y)) Z x, fr i x⟫
      = cov.covBilin (fun y ↦ cov.ricciForm y) V (fun y ↦ cov X y (U y)) Z x := by
    rw [cov.covBilin_ricciForm_eq_covRicci hV2 hDX hZ3]
    exact cov.sum_inner_covCurvature_eq hmet hV2 hDX2 hZ3 hs hu hx hfr2
  have hT5 : ∑ i, ⟪cov.covCurvature V (fr i) X (fun y ↦ cov Z y (U y)) x, fr i x⟫
      = cov.covBilin (fun y ↦ cov.ricciForm y) V X (fun y ↦ cov Z y (U y)) x := by
    rw [cov.covBilin_ricciForm_eq_covRicci hV2 hX3 hDZ]
    exact cov.sum_inner_covCurvature_eq hmet hV2 hX2 hDZ hs hu hx hfr2
  -- the leading term: the traced function is the frame sum near `x`
  have hfun : (fun y ↦ cov.covBilin (fun z ↦ cov.ricciForm z) V X Z y)
      = fun y ↦ cov.covRicci V X Z y :=
    funext fun _ ↦ cov.covBilin_ricciForm_eq_covRicci hV2 hX3 hZ3
  have hloc : (fun y ↦ cov.covRicci V X Z y)
      =ᶠ[𝓝 x] fun y ↦ ∑ i, ⟪cov.covCurvature V (fr i) X Z y, fr i y⟫ := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact (cov.sum_inner_covCurvature_eq hmet hV2 hX2 hZ3 hs hu hy hfr2).symm
  have hsec : ∀ i, CMDiff 1 (T% (fun y ↦ cov.covCurvature V (fr i) X Z y)) := fun i ↦
    cov.contMDiff_covCurvature hV (hfr i) hX3 hZ
  have hinner : ∀ i, MDiffAt (fun y ↦ ⟪cov.covCurvature V (fr i) X Z y, fr i y⟫) x := fun i ↦
    (((hsec i) x).inner_bundle' (((hfr i).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)) x)).mdifferentiableAt h1
  have hderiv : mvfderiv I (fun y ↦ cov.covBilin (fun z ↦ cov.ricciForm z) V X Z y) x (U x)
      = ∑ i, (⟪cov (fun y ↦ cov.covCurvature V (fr i) X Z y) x (U x), fr i x⟫
          + ⟪cov.covCurvature V (fr i) X Z x, cov (fr i) x (U x)⟫) := by
    rw [hfun, hloc.mvfderiv_eq, mvfderiv_fun_sum (fun i _ ↦ hinner i), _root_.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦
      hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) U
        ((hsec i).mdifferentiable h1 x) (hfrm x i)
  -- the frame-derivative residue vanishes
  obtain ⟨c, hcdef⟩ : ∃ c : ι → ι → ℝ, c = fun i j ↦ ⟪(b j : TangentSpace I x),
      cov (fr i) x (U x)⟫ := ⟨_, rfl⟩
  have hexp : ∀ i, cov (fr i) x (U x) = ∑ j, c i j • fr j x := by
    intro i
    have e := (b.sum_repr' (cov (fr i) x (U x))).symm
    refine e.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    simp only [hcdef]
    rw [hb j]
  have hanti : ∀ i j, c i j = -c j i := by
    intro i j
    have e1 : ⟪(b j : TangentSpace I x), cov (fr i) x (U x)⟫
        = ⟪cov (fr i) x (U x), (b j : TangentSpace I x)⟫ := real_inner_comm _ _
    have e2 : ⟪(b i : TangentSpace I x), cov (fr j) x (U x)⟫
        = ⟪cov (fr j) x (U x), (b i : TangentSpace I x)⟫ := real_inner_comm _ _
    simp only [hcdef]
    rw [e1, e2, hb j, hb i]
    exact cov.inner_cov_antisymm (X := U) hmet (fun i ↦ hfrm x i)
      (fun i j ↦ by
        filter_upwards [hu.mem_nhds hx] with y hy
        rw [orthonormal_iff_ite.mp (hs.orthonormal hy) i j,
          orthonormal_iff_ite.mp (hs.orthonormal hx) i j]) i j
  have hT3 : ∀ i, cov.covCurvature V (fun y ↦ cov (fr i) y (U y)) X Z x
      = ∑ j, c i j • cov.covCurvature V (fr j) X Z x := by
    intro i
    have hsm : CMDiff 2 (T% (fun y ↦ ∑ j, (fun _ : M ↦ c i j) y • fr j y)) :=
      ContMDiff.sum_section fun j _ ↦ (contMDiff_const).smul_section (hfr2 j)
    have hval : (fun y ↦ cov (fr i) y (U y)) x
        = (fun y ↦ ∑ j, (fun _ : M ↦ c i j) y • fr j y) x := hexp i
    rw [cov.covCurvature_congr_snd hV2 (hDfr i) hsm hX2 hZ3 hval,
      cov.covCurvature_sum_smul_snd (fun j _ ↦ contMDiff_const) (fun j _ ↦ hfr2 j) hV2 hX2 hZ3]
  have hcancel : ∑ i, (⟪cov.covCurvature V (fun y ↦ cov (fr i) y (U y)) X Z x, fr i x⟫
      + ⟪cov.covCurvature V (fr i) X Z x, cov (fr i) x (U x)⟫) = 0 := by
    have hstep : ∀ i, ⟪cov.covCurvature V (fun y ↦ cov (fr i) y (U y)) X Z x, fr i x⟫
        + ⟪cov.covCurvature V (fr i) X Z x, cov (fr i) x (U x)⟫
        = ∑ j, c i j * (⟪cov.covCurvature V (fr j) X Z x, fr i x⟫
            + ⟪cov.covCurvature V (fr i) X Z x, fr j x⟫) := by
      intro i
      rw [hT3 i, inner_sum_smul_left (c i) (fun j ↦ cov.covCurvature V (fr j) X Z x) (fr i x),
        hexp i, inner_sum_smul_right (cov.covCurvature V (fr i) X Z x) (c i) (fun j ↦ fr j x),
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i]
    exact sum_antisymm_pair_eq_zero c
      (fun i j ↦ ⟪cov.covCurvature V (fr j) X Z x, fr i x⟫) hanti
  -- expand the left-hand side and combine
  have hexpand : ∑ i, ⟪cov.cov2Curvature U V (fr i) X Z x, fr i x⟫
      = (∑ i, ⟪cov (fun y ↦ cov.covCurvature V (fr i) X Z y) x (U x), fr i x⟫)
        - (∑ i, ⟪cov.covCurvature (fun y ↦ cov V y (U y)) (fr i) X Z x, fr i x⟫)
        - (∑ i, ⟪cov.covCurvature V (fun y ↦ cov (fr i) y (U y)) X Z x, fr i x⟫)
        - (∑ i, ⟪cov.covCurvature V (fr i) (fun y ↦ cov X y (U y)) Z x, fr i x⟫)
        - ∑ i, ⟪cov.covCurvature V (fr i) X (fun y ↦ cov Z y (U y)) x, fr i x⟫ := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show ⟪cov (fun y ↦ cov.covCurvature V (fr i) X Z y) x (U x)
        - cov.covCurvature (fun y ↦ cov V y (U y)) (fr i) X Z x
        - cov.covCurvature V (fun y ↦ cov (fr i) y (U y)) X Z x
        - cov.covCurvature V (fr i) (fun y ↦ cov X y (U y)) Z x
        - cov.covCurvature V (fr i) X (fun y ↦ cov Z y (U y)) x, fr i x⟫ = _
    rw [inner_sub_left, inner_sub_left, inner_sub_left, inner_sub_left]
  rw [Finset.sum_add_distrib] at hderiv hcancel
  show _ = mvfderiv I (fun y ↦ cov.covBilin (fun z ↦ cov.ricciForm z) V X Z y) x (U x)
    - cov.covBilin (fun y ↦ cov.ricciForm y) (fun y ↦ cov V y (U y)) X Z x
    - cov.covBilin (fun y ↦ cov.ricciForm y) V (fun y ↦ cov X y (U y)) Z x
    - cov.covBilin (fun y ↦ cov.ricciForm y) V X (fun y ↦ cov Z y (U y)) x
  rw [hexpand, ← hT2, ← hT4, ← hT5]
  linarith [hderiv, hcancel]

/-- **The first-slot trace of `Δ Rm` is `Δ_g Ric`**:
`∑ᵢ ⟪(Δ Rm)(eᵢ,X)Z, eᵢ⟫ = (Δ_g Ric)(X,Z)`.

`sum_inner_cov2Curvature_fst_eq_cov2Bilin` traced once more, over the two derivative slots.
Both Laplacians are read off the same frame, so the only work is one `Finset.sum_comm`:
the trace defining `Δ` and the trace defining `Ric` are independent sums. -/
theorem sum_inner_curvatureLaplacian_fst_eq_laplacianBilin
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 4 (T% X)) (hZ : CMDiff 4 (T% Z))
    (hbil : IsMDiffBilinAt (I := I) (fun y ↦ cov.ricciForm y) x)
    (hcb : cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) X Z x)
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i) :
    ∑ i, ⟪ cov.curvatureLaplacian (fr i) X Z x, fr i x⟫
      = cov.laplacianBilin (fun y ↦ cov.ricciForm y) X Z x := by
  classical
  have hX3 : CMDiff 3 (T% X) := hX.of_le (by norm_num)
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hZ2 : CMDiff 2 (T% Z) := hZ.of_le (by norm_num)
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  rw [cov.laplacianBilin_eq_sum_frame hbil hcb hX2 hZ2 hfr2 b hbv]
  have hstep : ∀ i, ⟪ cov.curvatureLaplacian (fr i) X Z x, fr i x⟫
      = ∑ k, ⟪ cov.cov2Curvature (fr k) (fr k) (fr i) X Z x, fr i x⟫ := by
    intro i
    rw [cov.curvatureLaplacian_eq_sum_frame (hfr i) hX3 hZ hfr b hbv]
    exact sum_inner_fin (fun k ↦ cov.cov2Curvature (fr k) (fr k) (fr i) X Z x) (fr i x)
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦
    cov.sum_inner_cov2Curvature_fst_eq_cov2Bilin hmet (hfr k) (hfr k) hX hZ hs hu hx hfr

end CovariantDerivative
