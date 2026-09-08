/-
The second covariant derivative of a bilinear form field, and its trace.

`BilinDeriv.lean` makes `∇h` a `(0,3)`-tensor. This differentiates it once more:

  `(∇²_{W,X} h)(Y,Z) = W((∇_X h)(Y,Z)) − (∇_{∇_W X} h)(Y,Z)
                        − (∇_X h)(∇_W Y, Z) − (∇_X h)(Y, ∇_W Z)`,

**one correction per slot of `∇h`, so three** — against the five of `∇²Rm`
(`CurvatureLaplacian.lean`), whose inner tensor has four slots and whose values are vectors.

The connection Laplacian `Δ_g h` is the metric trace over the two derivative slots, and it is
what `tr_g(∂ₜ Ric) = Δ scal` is assembled from: tracing the first variation of `Rm` twice
against the Koszul formula for `∂ₜ∇` gives `tr_g(∂ₜ Ric) = div div h − Δ(tr_g h)`, with no
curvature terms.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.BilinDeriv
import RicciFlowBlueprint.GlobalExtension
import RicciFlowBlueprint.OrthonormalFrame

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- **The second covariant derivative of a bilinear form field**,
`(∇²_{W,X} h)(Y,Z) = W((∇_X h)(Y,Z)) − (∇_{∇_W X} h)(Y,Z) − (∇_X h)(∇_W Y, Z)
− (∇_X h)(Y, ∇_W Z)`: one correction per slot of `∇h`. -/
noncomputable def cov2Bilin (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (W X Y Z : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x (W x)
    - cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x
    - cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x
    - cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x

variable [ContMDiffCovariantDerivative cov 1] {h : M → E →L[ℝ] E →L[ℝ] ℝ}

omit [CompleteSpace E] in
/-- **`∇²h` is pointwise in its outer direction**, with no frame argument: the leading term is
a continuous linear map at `W x`, and each correction is `∇h` in a slot it is already pointwise
in, applied to a field whose value at `x` is determined by `W x`. -/
theorem cov2Bilin_congr_dir (hb : IsMDiffBilinAt (I := I) h x)
    {W W' X Y Z : Π y : M, TangentSpace I y}
    (hW : MDiffAt (T% W) x) (hW' : MDiffAt (T% W') x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) (hWW' : W x = W' x) :
    cov.cov2Bilin h W X Y Z x = cov.cov2Bilin h W' X Y Z x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hY1 := (hY.mdifferentiable h2) x
  have hZ1 := (hZ.mdifferentiable h2) x
  have e₁ : cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x
      = cov.covBilin h (fun y ↦ cov X y (W' y)) Y Z x :=
    cov.covBilin_congr_dir (by simp only [hWW'])
  have e₂ : cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x
      = cov.covBilin h X (fun y ↦ cov Y y (W' y)) Z x :=
    cov.covBilin_congr_snd hb X (cov.mdiffAt_cov_apply hY hW)
      (cov.mdiffAt_cov_apply hY hW') hZ1 (by simp only [hWW'])
  have e₃ : cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x
      = cov.covBilin h X Y (fun y ↦ cov Z y (W' y)) x :=
    cov.covBilin_congr_thd hb X hY1 (cov.mdiffAt_cov_apply hZ hW)
      (cov.mdiffAt_cov_apply hZ hW') (by simp only [hWW'])
  simp only [cov2Bilin, hWW', e₁, e₂, e₃]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇²h` is linear in its outer direction** under scaling. Each of the four terms picks up
one `f x`: the leading one because `mvfderiv` is a continuous linear map, the corrections
because `∇h` is already tensorial in the slot each lands in. -/
theorem cov2Bilin_smul_dir (hb : IsMDiffBilinAt (I := I) h x)
    {f : M → ℝ} {W X Y Z : Π y : M, TangentSpace I y}
    (hf : MDiffAt f x) (hW : MDiffAt (T% W) x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.cov2Bilin h (f • W) X Y Z x = f x * cov.cov2Bilin h W X Y Z x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hY1 := (hY.mdifferentiable h2) x
  have hZ1 := (hZ.mdifferentiable h2) x
  have hfx : (f • W) x = f x • W x := rfl
  have hd : mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x ((f • W) x)
      = f x * mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x (W x) := by
    rw [hfx, map_smul]; rfl
  have hfield : ∀ V : Π y : M, TangentSpace I y,
      (fun y ↦ cov V y ((f • W) y)) = f • fun y ↦ cov V y (W y) := by
    intro V
    funext y
    exact map_smul _ _ _
  have e₁ : cov.covBilin h (fun y ↦ cov X y ((f • W) y)) Y Z x
      = f x * cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x := by
    rw [hfield X]; exact cov.covBilin_smul_dir
  have e₂ : cov.covBilin h X (fun y ↦ cov Y y ((f • W) y)) Z x
      = f x * cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x := by
    rw [hfield Y]
    exact cov.covBilin_smul_snd hf (cov.mdiffAt_cov_apply hY hW)
      (hb _ _ (cov.mdiffAt_cov_apply hY hW) hZ1)
  have e₃ : cov.covBilin h X Y (fun y ↦ cov Z y ((f • W) y)) x
      = f x * cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x := by
    rw [hfield Z]
    exact cov.covBilin_smul_thd hf (cov.mdiffAt_cov_apply hZ hW)
      (hb _ _ hY1 (cov.mdiffAt_cov_apply hZ hW))
  simp only [cov2Bilin]
  rw [hd, e₁, e₂, e₃]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇²h` is additive in its outer direction.** -/
theorem cov2Bilin_add_dir (hb : IsMDiffBilinAt (I := I) h x)
    {W W' X Y Z : Π y : M, TangentSpace I y}
    (hW : MDiffAt (T% W) x) (hW' : MDiffAt (T% W') x)
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.cov2Bilin h (W + W') X Y Z x
      = cov.cov2Bilin h W X Y Z x + cov.cov2Bilin h W' X Y Z x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hY1 := (hY.mdifferentiable h2) x
  have hZ1 := (hZ.mdifferentiable h2) x
  have hd : mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x ((W + W') x)
      = mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x (W x)
        + mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x (W' x) := map_add _ _ _
  have hfield : ∀ V : Π y : M, TangentSpace I y,
      (fun y ↦ cov V y ((W + W') y))
        = (fun y ↦ cov V y (W y)) + fun y ↦ cov V y (W' y) := by
    intro V
    funext y
    exact map_add _ _ _
  have e₁ : cov.covBilin h (fun y ↦ cov X y ((W + W') y)) Y Z x
      = cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x
        + cov.covBilin h (fun y ↦ cov X y (W' y)) Y Z x := by
    rw [hfield X]; exact cov.covBilin_add_dir
  have e₂ : cov.covBilin h X (fun y ↦ cov Y y ((W + W') y)) Z x
      = cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x
        + cov.covBilin h X (fun y ↦ cov Y y (W' y)) Z x := by
    rw [hfield Y]
    exact cov.covBilin_add_snd (cov.mdiffAt_cov_apply hY hW) (cov.mdiffAt_cov_apply hY hW')
      (hb _ _ (cov.mdiffAt_cov_apply hY hW) hZ1) (hb _ _ (cov.mdiffAt_cov_apply hY hW') hZ1)
  have e₃ : cov.covBilin h X Y (fun y ↦ cov Z y ((W + W') y)) x
      = cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x
        + cov.covBilin h X Y (fun y ↦ cov Z y (W' y)) x := by
    rw [hfield Z]
    exact cov.covBilin_add_thd (cov.mdiffAt_cov_apply hZ hW) (cov.mdiffAt_cov_apply hZ hW')
      (hb _ _ hY1 (cov.mdiffAt_cov_apply hZ hW)) (hb _ _ hY1 (cov.mdiffAt_cov_apply hZ hW'))
  simp only [cov2Bilin]
  rw [hd, e₁, e₂, e₃]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- **`∇²h` is linear in its inner direction**, by the Leibniz cancellation: `W(f·(∇_Xh)(Y,Z))`
contributes `(Wf)(∇_Xh)(Y,Z)`, and `∇_W(f•X) = f∇_WX + (Wf)X` contributes the match through
`−(∇_{∇_W(f•X)}h)(Y,Z)`. Every other step is the *direction* slot of `∇h`, which needs no
hypotheses at all, so the only inputs are differentiability of `f` and of `(∇_X h)(Y,Z)`. -/
theorem cov2Bilin_smul_snd {f : M → ℝ} {W X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hcb : MDiffAt (fun y ↦ cov.covBilin h X Y Z y) x) :
    cov.cov2Bilin h W (f • X) Y Z x = f x * cov.cov2Bilin h W X Y Z x := by
  have hlin : (fun y ↦ cov.covBilin h (f • X) Y Z y) = fun y ↦ f y * cov.covBilin h X Y Z y := by
    funext y
    exact cov.covBilin_smul_dir
  -- the value at `x` of `∇_W (f • X)`, as a field built from tensorial pieces
  have hval : cov (f • X) x (W x)
      = (f • (fun y ↦ cov X y (W y))
          + (fun y ↦ mvfderiv I f y (W y)) • X) x := by
    rw [cov.isCovariantDerivativeOn.leibniz hX hf]
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      Pi.add_apply]
    rfl
  have e₁ : cov.covBilin h (fun y ↦ cov (f • X) y (W y)) Y Z x
      = f x * cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x
        + mvfderiv I f x (W x) * cov.covBilin h X Y Z x := by
    rw [cov.covBilin_congr_dir (X' := f • (fun y ↦ cov X y (W y))
      + (fun y ↦ mvfderiv I f y (W y)) • X) hval, cov.covBilin_add_dir,
      cov.covBilin_smul_dir, cov.covBilin_smul_dir]
  have e₂ : cov.covBilin h (f • X) (fun y ↦ cov Y y (W y)) Z x
      = f x * cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x := cov.covBilin_smul_dir
  have e₃ : cov.covBilin h (f • X) Y (fun y ↦ cov Z y (W y)) x
      = f x * cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x := cov.covBilin_smul_dir
  simp only [cov2Bilin, hlin]
  rw [mvfderiv_fun_mul hf hcb, e₁, e₂, e₃]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- **`∇²h` is additive in its inner direction.** -/
theorem cov2Bilin_add_snd {W X X' Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hcb : MDiffAt (fun y ↦ cov.covBilin h X Y Z y) x)
    (hcb' : MDiffAt (fun y ↦ cov.covBilin h X' Y Z y) x) :
    cov.cov2Bilin h W (X + X') Y Z x
      = cov.cov2Bilin h W X Y Z x + cov.cov2Bilin h W X' Y Z x := by
  have hlin : (fun y ↦ cov.covBilin h (X + X') Y Z y)
      = fun y ↦ cov.covBilin h X Y Z y + cov.covBilin h X' Y Z y := by
    funext y
    exact cov.covBilin_add_dir
  have hval : cov (X + X') x (W x)
      = ((fun y ↦ cov X y (W y)) + fun y ↦ cov X' y (W y)) x := by
    rw [cov.isCovariantDerivativeOn.add hX hX']
    rfl
  have e₁ : cov.covBilin h (fun y ↦ cov (X + X') y (W y)) Y Z x
      = cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x
        + cov.covBilin h (fun y ↦ cov X' y (W y)) Y Z x := by
    rw [cov.covBilin_congr_dir (X' := (fun y ↦ cov X y (W y)) + fun y ↦ cov X' y (W y)) hval,
      cov.covBilin_add_dir]
  have e₂ : cov.covBilin h (X + X') (fun y ↦ cov Y y (W y)) Z x
      = cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x
        + cov.covBilin h X' (fun y ↦ cov Y y (W y)) Z x := cov.covBilin_add_dir
  have e₃ : cov.covBilin h (X + X') Y (fun y ↦ cov Z y (W y)) x
      = cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x
        + cov.covBilin h X' Y (fun y ↦ cov Z y (W y)) x := cov.covBilin_add_dir
  simp only [cov2Bilin, hlin]
  rw [mvfderiv_fun_add hcb hcb', e₁, e₂, e₃]
  simp only [_root_.add_apply]
  ring

/-- **`∇h` is differentiable in the base point against `C¹` direction fields.** The hypothesis
the inner direction slot of `∇²h` needs, and the only one: `cov2Bilin_smul_snd` asks for
`MDifferentiableAt (y ↦ (∇_V h)(Y,Z)) x`, which merely-`MDifferentiableAt` `V` cannot supply
(the leading term of `∇h` differentiates `h(Y,Z)` in the direction `V`, so it sees the germ of
`V`). Quantifying over `C¹` fields makes it satisfiable. -/
def IsMDiffCovBilinAt (h : M → E →L[ℝ] E →L[ℝ] ℝ) (Y Z : Π y : M, TangentSpace I y) (x : M) :
    Prop :=
  ∀ V : Π y : M, TangentSpace I y, CMDiff 1 (T% V) →
    MDiffAt (fun y ↦ cov.covBilin h V Y Z y) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- `∇h` kills the zero field in its direction slot. -/
theorem covBilin_zero_dir {Y Z : Π y : M, TangentSpace I y} {x : M} :
    cov.covBilin h 0 Y Z x = 0 := by
  have hz : ((fun _ : M ↦ (0 : ℝ)) • (0 : Π y : M, TangentSpace I y))
      = (0 : Π y : M, TangentSpace I y) := by funext y; simp
  calc cov.covBilin h 0 Y Z x
      = cov.covBilin h ((fun _ : M ↦ (0 : ℝ)) • (0 : Π y : M, TangentSpace I y)) Y Z x := by
        rw [hz]
    _ = (0 : ℝ) * cov.covBilin h (0 : Π y : M, TangentSpace I y) Y Z x :=
        cov.covBilin_smul_dir
    _ = 0 := by ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- `∇²h` kills the zero field in its inner direction slot. -/
theorem cov2Bilin_zero_snd {W Y Z : Π y : M, TangentSpace I y} {x : M}
    (hcb : cov.IsMDiffCovBilinAt h Y Z x) :
    cov.cov2Bilin h W 0 Y Z x = 0 := by
  have hz1 : CMDiff 1 (T% (0 : Π y : M, TangentSpace I y)) := contMDiff_zeroSection _ _
  have hzs : ((fun _ : M ↦ (0 : ℝ)) • (0 : Π y : M, TangentSpace I y))
      = (0 : Π y : M, TangentSpace I y) := by funext y; simp
  calc cov.cov2Bilin h W 0 Y Z x
      = cov.cov2Bilin h W ((fun _ : M ↦ (0 : ℝ)) • (0 : Π y : M, TangentSpace I y)) Y Z x := by
        rw [hzs]
    _ = (fun _ : M ↦ (0 : ℝ)) x
          * cov.cov2Bilin h W (0 : Π y : M, TangentSpace I y) Y Z x :=
        cov.cov2Bilin_smul_snd mdifferentiableAt_const (hz1.mdifferentiable (by norm_num) x)
          (hcb _ hz1)
    _ = 0 := by simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- **The inner direction slot of `∇²h` applied to a finite `C¹` combination.** -/
theorem cov2Bilin_sum_smul_snd {ι : Type*} {s : Finset ι} {g : ι → M → ℝ}
    {V : ι → Π y : M, TangentSpace I y} {W Y Z : Π y : M, TangentSpace I y} {x : M}
    (hg : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) 1 (g i)) (hV : ∀ i ∈ s, CMDiff 1 (T% (V i)))
    (hcb : cov.IsMDiffCovBilinAt h Y Z x) :
    cov.cov2Bilin h W (fun y ↦ ∑ i ∈ s, g i y • V i y) Y Z x
      = ∑ i ∈ s, g i x * cov.cov2Bilin h W (V i) Y Z x := by
  classical
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y ↦ ∑ i ∈ (∅ : Finset ι), g i y • V i y)
          = (0 : Π y : M, TangentSpace I y) := by funext y; simp
      rw [hz, cov.cov2Bilin_zero_snd hcb, Finset.sum_empty]
  | insert a t ha ih =>
      have hga : ContMDiff I 𝓘(ℝ, ℝ) 1 (g a) := hg a (Finset.mem_insert_self a t)
      have hVa : CMDiff 1 (T% (V a)) := hV a (Finset.mem_insert_self a t)
      have hgt : ∀ i ∈ t, ContMDiff I 𝓘(ℝ, ℝ) 1 (g i) := fun i hi ↦
        hg i (Finset.mem_insert_of_mem hi)
      have hVt : ∀ i ∈ t, CMDiff 1 (T% (V i)) := fun i hi ↦ hV i (Finset.mem_insert_of_mem hi)
      have hsum : CMDiff 1 (T% (fun y ↦ ∑ i ∈ t, g i y • V i y)) :=
        ContMDiff.sum_section fun i hi ↦ (hgt i hi).smul_section (hVt i hi)
      have hsplit : (fun y ↦ ∑ i ∈ insert a t, g i y • V i y)
          = (g a • V a) + (fun y ↦ ∑ i ∈ t, g i y • V i y) := by
        funext y
        show ∑ i ∈ insert a t, g i y • V i y = g a y • V a y + ∑ i ∈ t, g i y • V i y
        rw [Finset.sum_insert ha]
      rw [hsplit,
        cov.cov2Bilin_add_snd ((hga.smul_section hVa).mdifferentiable h1 x)
          (hsum.mdifferentiable h1 x) (hcb _ (hga.smul_section hVa)) (hcb _ hsum),
        cov.cov2Bilin_smul_snd (hga.mdifferentiable h1 x) (hVa.mdifferentiable h1 x)
          (hcb _ hVa), ih hgt hVt, Finset.sum_insert ha]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- **`∇²h` is local in its inner direction slot.** Only the leading term needs the germ; the
other three are `∇h` in its direction slot, which is pointwise with no hypotheses at all. -/
theorem cov2Bilin_congr_snd_of_eventuallyEq {W X X' Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hXX' : X =ᶠ[𝓝 x] X') :
    cov.cov2Bilin h W X Y Z x = cov.cov2Bilin h W X' Y Z x := by
  obtain ⟨U, hUeq, hUopen, hxU⟩ := eventually_nhds_iff.mp hXX'
  have hsec : (fun y ↦ cov.covBilin h X Y Z y) =ᶠ[𝓝 x] fun y ↦ cov.covBilin h X' Y Z y :=
    eventually_nhds_iff.mpr
      ⟨U, fun y hy ↦ cov.covBilin_congr_dir (hUeq y hy), hUopen, hxU⟩
  have hcovX : cov X x = cov X' x :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hX hX' Filter.univ_mem hXX'
  have e₁ : mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x
      = mvfderiv I (fun y ↦ cov.covBilin h X' Y Z y) x := hsec.mvfderiv_eq
  have e₂ : cov.covBilin h (fun y ↦ cov X y (W y)) Y Z x
      = cov.covBilin h (fun y ↦ cov X' y (W y)) Y Z x :=
    cov.covBilin_congr_dir (by show cov X x (W x) = cov X' x (W x); rw [hcovX])
  have e₃ : cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x
      = cov.covBilin h X' (fun y ↦ cov Y y (W y)) Z x :=
    cov.covBilin_congr_dir hXX'.eq_of_nhds
  have e₄ : cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x
      = cov.covBilin h X' Y (fun y ↦ cov Z y (W y)) x :=
    cov.covBilin_congr_dir hXX'.eq_of_nhds
  simp only [cov2Bilin, e₁, e₂, e₃, e₄]

section Frame

variable [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] in
-- BENCH: cov2-bilin-congr-snd
/-- **`(∇²_{W,X} h)(Y,Z)` at `x` depends only on `X x`.** The frame-and-globalise argument,
and it runs at `C¹` only --- `cov2Bilin_smul_snd` asks its coefficient for one derivative,
against the three that `cov2Curvature_smul_snd` asks. Expand `X` in a local orthonormal frame,
globalise the frame and the coefficients, move the sum out with `cov2Bilin_sum_smul_snd`, and
use locality; the frame coefficients at `x` depend only on `X x`. -/
theorem cov2Bilin_congr_snd {W X X' Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 1 (T% X)) (hX' : CMDiff 1 (T% X'))
    (hcb : cov.IsMDiffCovBilinAt h Y Z x) (hval : X x = X' x) :
    cov.cov2Bilin h W X Y Z x = cov.cov2Bilin h W X' Y Z x := by
  classical
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  set e := trivializationAt E (TangentSpace I (M := M)) x with he
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hu : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hxe
  set b := Module.finBasis ℝ E with hb
  obtain ⟨fr, hs, hfrsm⟩ : ∃ fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      IsOrthonormalFrameOn I E 1 fr e.baseSet ∧ ∀ i, CMDiff[e.baseSet] 1 (T% (fr i)) :=
    ⟨_, b.orthonormalFrame_isOrthonormalFrameOn (IB := I) (n := 1) e,
      fun i ↦ b.contMDiffOn_orthonormalFrame_baseSet e i⟩
  have hframe : ∀ i, ∃ Ei : Π y : M, TangentSpace I y, CMDiff 1 (T% Ei) ∧
      Ei =ᶠ[𝓝 x] fr i := by
    intro i
    obtain ⟨Ei, hEi, hEieq⟩ := RicciFlowBlueprint.exists_contMDiff_eventuallyEq (n := 1) hu
      (hfrsm i)
    exact ⟨Ei, by simpa using hEi, hEieq⟩
  choose Ei hEi hEieq using hframe
  have hcoeff : ∀ (V : Π y : M, TangentSpace I y), CMDiff 1 (T% V) → ∀ i,
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 g ∧
        g =ᶠ[𝓝 x] (LinearMap.piApply (hs.coeff i) V) := by
    intro V hV i
    obtain ⟨g, hg, hgeq⟩ := RicciFlowBlueprint.exists_contMDiff_eventuallyEq_fun (n := 1) hu
      (hs.contMDiffOn_coeff hV.contMDiffOn i)
    exact ⟨g, by simpa using hg, hgeq⟩
  have key : ∀ (V : Π y : M, TangentSpace I y), CMDiff 1 (T% V) →
      cov.cov2Bilin h W V Y Z x
        = ∑ i, hs.coeff i x (V x) * cov.cov2Bilin h W (Ei i) Y Z x := by
    intro V hV
    choose g hg hgeq using hcoeff V hV
    have hsum : CMDiff 1 (T% (fun y ↦ ∑ i, g i y • Ei i y)) :=
      ContMDiff.sum_section fun i _ ↦ (hg i).smul_section (hEi i)
    have heq : V =ᶠ[𝓝 x] fun y ↦ ∑ i, g i y • Ei i y := by
      have hall : ∀ᶠ y in 𝓝 x, ∀ i, g i y = hs.coeff i y (V y) ∧ Ei i y = fr i y :=
        Filter.eventually_all.mpr fun i ↦ (hgeq i).and (hEieq i)
      filter_upwards [hs.toIsLocalFrameOn.eventually_eq_sum_coeff_smul V hu, hall] with y hy hy'
      rw [hy]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [(hy' i).1, (hy' i).2]
    rw [cov.cov2Bilin_congr_snd_of_eventuallyEq (hV.mdifferentiable h1 x)
        (hsum.mdifferentiable h1 x) heq,
      cov.cov2Bilin_sum_smul_snd (fun i _ ↦ hg i) (fun i _ ↦ hEi i) hcb]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hgeq i).eq_of_nhds]
    rfl
  rw [key X hX, key X' hX']
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [hs.toIsLocalFrameOn.coeff_congr hval i]

end Frame

section Laplacian

variable [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

variable {Y Z : Π y : M, TangentSpace I y} {x : M}

/-- **`∇²h` as a function of two tangent vectors.** Evaluated on the global `C²` extensions of
`exists_contMDiff_two_extension`, which give the same answer by `cov2Bilin_congr_dir` and
`cov2Bilin_congr_snd`. -/
noncomputable def cov2BilinAt (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (Y Z : Π y : M, TangentSpace I y) (x : M) (v w : TangentSpace I x) : ℝ :=
  cov.cov2Bilin h (RicciFlowBlueprint.exists_contMDiff_two_extension v).choose
    (RicciFlowBlueprint.exists_contMDiff_two_extension w).choose Y Z x

omit [CompleteSpace E] in
theorem cov2BilinAt_eq (hb : IsMDiffBilinAt (I := I) h x) (hcb : cov.IsMDiffCovBilinAt h Y Z x)
    {W X : Π y : M, TangentSpace I y} (hW : CMDiff 2 (T% W)) (hX : CMDiff 2 (T% X))
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.cov2BilinAt h Y Z x (W x) (X x) = cov.cov2Bilin h W X Y Z x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  obtain ⟨hWc, hWv⟩ :=
    (RicciFlowBlueprint.exists_contMDiff_two_extension (W x)).choose_spec
  obtain ⟨hXc, hXv⟩ :=
    (RicciFlowBlueprint.exists_contMDiff_two_extension (X x)).choose_spec
  rw [cov2BilinAt, cov.cov2Bilin_congr_dir hb (hWc.mdifferentiable h2 x)
    (hW.mdifferentiable h2 x) hY hZ hWv]
  exact cov.cov2Bilin_congr_snd (hXc.of_le (by norm_num)) (hX.of_le (by norm_num)) hcb hXv

section Bilinear

variable (hb : IsMDiffBilinAt (I := I) h x) (hcb : cov.IsMDiffCovBilinAt h Y Z x)
  (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))

include hb hcb hY hZ

omit [CompleteSpace E] in
theorem cov2BilinAt_add_left (v v' w : TangentSpace I x) :
    cov.cov2BilinAt h Y Z x (v + v') w
      = cov.cov2BilinAt h Y Z x v w + cov.cov2BilinAt h Y Z x v' w := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  obtain ⟨V', hV', hV'v⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v'
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w
  have hsum : (V + V') x = v + v' := by show V x + V' x = v + v'; rw [hVv, hV'v]
  rw [← hsum, ← hWw, cov.cov2BilinAt_eq hb hcb (hV.add_section hV') hW hY hZ,
    cov.cov2Bilin_add_dir hb (hV.mdifferentiable h2 x) (hV'.mdifferentiable h2 x) hY hZ,
    ← cov.cov2BilinAt_eq hb hcb hV hW hY hZ, ← cov.cov2BilinAt_eq hb hcb hV' hW hY hZ,
    hVv, hV'v]

omit [CompleteSpace E] in
theorem cov2BilinAt_smul_left (c : ℝ) (v w : TangentSpace I x) :
    cov.cov2BilinAt h Y Z x (c • v) w = c • cov.cov2BilinAt h Y Z x v w := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun _ : M ↦ c) := contMDiff_const
  have hsm : ((fun _ : M ↦ c) • V) x = c • v := by show c • V x = c • v; rw [hVv]
  rw [← hsm, ← hWw, cov.cov2BilinAt_eq hb hcb (hf.smul_section hV) hW hY hZ,
    cov.cov2Bilin_smul_dir hb (hf.mdifferentiable h2 x) (hV.mdifferentiable h2 x) hY hZ,
    ← cov.cov2BilinAt_eq hb hcb hV hW hY hZ, hVv]
  rfl

omit [CompleteSpace E] in
theorem cov2BilinAt_add_right (v w w' : TangentSpace I x) :
    cov.cov2BilinAt h Y Z x v (w + w')
      = cov.cov2BilinAt h Y Z x v w + cov.cov2BilinAt h Y Z x v w' := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w
  obtain ⟨W', hW', hW'w⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w'
  have hsum : (W + W') x = w + w' := by show W x + W' x = w + w'; rw [hWw, hW'w]
  rw [← hsum, ← hVv, cov.cov2BilinAt_eq hb hcb hV (hW.add_section hW') hY hZ,
    cov.cov2Bilin_add_snd (hW.mdifferentiable h2 x) (hW'.mdifferentiable h2 x)
      (hcb _ (hW.of_le (by norm_num))) (hcb _ (hW'.of_le (by norm_num))),
    ← cov.cov2BilinAt_eq hb hcb hV hW hY hZ, ← cov.cov2BilinAt_eq hb hcb hV hW' hY hZ,
    hWw, hW'w]

omit [CompleteSpace E] in
theorem cov2BilinAt_smul_right (c : ℝ) (v w : TangentSpace I x) :
    cov.cov2BilinAt h Y Z x v (c • w) = c • cov.cov2BilinAt h Y Z x v w := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  obtain ⟨V, hV, hVv⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := RicciFlowBlueprint.exists_contMDiff_two_extension w
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun _ : M ↦ c) := contMDiff_const
  have hsm : ((fun _ : M ↦ c) • W) x = c • w := by show c • W x = c • w; rw [hWw]
  rw [← hsm, ← hVv, cov.cov2BilinAt_eq hb hcb hV (hf.smul_section hW) hY hZ,
    cov.cov2Bilin_smul_snd (hf.mdifferentiable h2 x) (hW.mdifferentiable h2 x)
      (hcb _ (hW.of_le (by norm_num))),
    ← cov.cov2BilinAt_eq hb hcb hV hW hY hZ, hWw]
  rfl

/-- **`∇²h` as a continuous bilinear form on `T_xM`**, in its two derivative slots. -/
noncomputable def cov2BilinForm :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (TangentSpace I x →ₗ[ℝ] ℝ)
        ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun v w ↦ cov.cov2BilinAt h Y Z x v w)
        (fun v v' w ↦ cov.cov2BilinAt_add_left hb hcb hY hZ v v' w)
        (fun c v w ↦ cov.cov2BilinAt_smul_left hb hcb hY hZ c v w)
        (fun v w w' ↦ cov.cov2BilinAt_add_right hb hcb hY hZ v w w')
        (fun c v w ↦ cov.cov2BilinAt_smul_right hb hcb hY hZ c v w))

omit [CompleteSpace E] in
@[simp] theorem cov2BilinForm_apply (v w : TangentSpace I x) :
    cov.cov2BilinForm hb hcb hY hZ v w = cov.cov2BilinAt h Y Z x v w := rfl

end Bilinear

/-- **`Δ_g h`**, the connection Laplacian of a bilinear form field: the metric trace of `∇²h`
in its two derivative slots. The definition uses the standard orthonormal basis of `T_xM`;
`laplacianBilin_eq_sum_basis` shows every orthonormal basis gives the same value. -/
noncomputable def laplacianBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (Y Z : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.cov2BilinAt h Y Z x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

omit [CompleteSpace E] in
-- BENCH: bilin-laplacian-frame-independent
/-- **`Δ_g h` is frame-independent**: it is the trace of a bilinear form. -/
theorem laplacianBilin_eq_sum_basis (hb : IsMDiffBilinAt (I := I) h x)
    (hcb : cov.IsMDiffCovBilinAt h Y Z x) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.laplacianBilin h Y Z x = ∑ i, cov.cov2BilinAt h Y Z x (b i) (b i) := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  exact OrthonormalBasis.sum_apply_self_eq _ b (cov.cov2BilinForm hb hcb hY hZ)

omit [CompleteSpace E] in
/-- **`Δ_g h` read off a `C²` frame** orthonormal at `x`:
`(Δ_g h)(Y,Z) = ∑ᵢ (∇²_{eᵢ,eᵢ}h)(Y,Z)`. -/
theorem laplacianBilin_eq_sum_frame (hb : IsMDiffBilinAt (I := I) h x)
    (hcb : cov.IsMDiffCovBilinAt h Y Z x) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    cov.laplacianBilin h Y Z x = ∑ i, cov.cov2Bilin h (fr i) (fr i) Y Z x := by
  rw [cov.laplacianBilin_eq_sum_basis hb hcb hY hZ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hbv i, cov.cov2BilinAt_eq hb hcb (hfr i) (hfr i) hY hZ]

end Laplacian

section Symmetric

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- **`∇h` inherits the symmetry of `h`.** -/
theorem covBilin_symm (hsymm : ∀ (y : M) (v w : E), h y v w = h y w v)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    cov.covBilin h X Y Z x = cov.covBilin h X Z Y x := by
  have hfun : (fun y ↦ h y (Y y) (Z y)) = fun y ↦ h y (Z y) (Y y) := by
    funext y
    exact hsymm y (Y y) (Z y)
  simp only [covBilin, hfun]
  rw [hsymm x (cov Y x (X x)) (Z x), hsymm x (Y x) (cov Z x (X x))]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1] in
/-- **`∇²h` inherits the symmetry of `h`** in its last two slots: each of the four terms is
`∇h` in a slot pair the previous lemma swaps. -/
theorem cov2Bilin_symm (hsymm : ∀ (y : M) (v w : E), h y v w = h y w v)
    (W X Y Z : Π y : M, TangentSpace I y) (x : M) :
    cov.cov2Bilin h W X Y Z x = cov.cov2Bilin h W X Z Y x := by
  have hfun : (fun y ↦ cov.covBilin h X Y Z y) = fun y ↦ cov.covBilin h X Z Y y := by
    funext y
    exact cov.covBilin_symm hsymm X Y Z y
  simp only [cov2Bilin, hfun]
  rw [cov.covBilin_symm hsymm (fun y ↦ cov X y (W y)) Y Z,
    cov.covBilin_symm hsymm X (fun y ↦ cov Y y (W y)) Z,
    cov.covBilin_symm hsymm X Y (fun y ↦ cov Z y (W y))]
  ring

section MetricTrace

open scoped RealInnerProductSpace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **`tr_g h`, the metric trace of a bilinear form field, as a function on `M`.** -/
noncomputable def traceBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ) (y : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I y) := VectorBundle.finiteDimensional ℝ E _ y
  ∑ i, h y (stdOrthonormalBasis ℝ (TangentSpace I y) i)
    (stdOrthonormalBasis ℝ (TangentSpace I y) i)

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] in
/-- `tr_g h` is frame-independent: `h y` is already a continuous bilinear form. -/
theorem traceBilin_eq_sum_basis (h : M → E →L[ℝ] E →L[ℝ] ℝ) (y : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I y)) :
    traceBilin (I := I) h y = ∑ i, h y (b i) (b i) := by
  have hfin : FiniteDimensional ℝ (TangentSpace I y) :=
    VectorBundle.finiteDimensional ℝ E _ y
  exact OrthonormalBasis.sum_apply_self_eq _ b
    ((h y : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

/-- `∇_Y h` at each point, as a field of bilinear forms: what `d(tr_g h)` is the frame sum of. -/
noncomputable def covBilinFormAux (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ y : M, IsMDiffBilinAt (I := I) h y) (Y : Π y : M, TangentSpace I y) :
    M → E →L[ℝ] E →L[ℝ] ℝ :=
  fun y ↦ (cov.covBilinForm (hb y) Y : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)

omit [CompleteSpace E] in
-- BENCH: hessian-metric-trace
/-- **The Hessian of `tr_g h` is the trace of `∇²h`**:
`∇²(tr_g h)(X,Y) = ∑ᵢ (∇²_{X,Y}h)(eᵢ,eᵢ)`. The same "trace commutes with `∇`" mechanism as the
divergence, one level up: differentiating the frame sum twice produces `∇²h` plus exactly the
term `(tr_g ∇_{∇_X Y} h)` that the Hessian's connection correction subtracts. -/
theorem hessianFun_traceBilin_eq
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hb : ∀ y : M, IsMDiffBilinAt (I := I) h y)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : CMDiff 2 (T% Y))
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr2 : ∀ i, CMDiff 2 (T% (fr i)))
    (hh : ∀ y ∈ u, ∀ i, MDiffAt (fun y' ↦ h y' (fr i y') (fr i y')) y)
    (hd : ∀ i, MDiffAt (fun y ↦ cov.covBilin h Y (fr i) (fr i) y) x) :
    cov.hessianFun (traceBilin (I := I) h) X Y x
      = ∑ i, cov.cov2Bilin h X Y (fr i) (fr i) x := by
  classical
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hY1 : MDiffAt (T% Y) x := hY.mdifferentiable h2 x
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr2 i).mdifferentiable h2 x
  have hDY : MDiffAt (T% (fun y ↦ cov Y y (X y))) x := cov.mdiffAt_cov_apply hY hX
  set B := cov.covBilinFormAux h hb Y with hBdef
  obtain ⟨b, hbv⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  -- `d(tr_g h)` is the frame sum of `∇h`, at every point of `u`
  have hgrad : ∀ y ∈ u, ∀ V : Π z : M, TangentSpace I z,
      mvfderiv I (traceBilin (I := I) h) y (V y)
        = ∑ i, cov.covBilin h V (fr i) (fr i) y := by
    intro y hy V
    obtain ⟨c, hcv⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
    have hsum : traceBilin (I := I) h =ᶠ[𝓝 y] fun z ↦ ∑ i, h z (fr i z) (fr i z) := by
      filter_upwards [hu.mem_nhds hy] with z hz
      obtain ⟨d, hdv⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hz
      rw [traceBilin_eq_sum_basis (I := I) h z d]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hdv i]
    rw [hsum.mvfderiv_eq]
    exact cov.mvfderiv_sum_eq_sum_covBilin_of_frame hcov hs hu hy (fun i ↦ hh y hy i)
  -- the leading term of the Hessian, by the trace lemma one level up
  have hBapp : ∀ y ∈ u, ∀ i, B y (fr i y) (fr i y) = cov.covBilin h Y (fr i) (fr i) y := by
    intro y hy i
    have hfy : MDiffAt (T% (fr i)) y :=
      (hs.toIsLocalFrameOn.contMDiffAt hu hy i).mdifferentiableAt one_ne_zero
    exact cov.covBilinForm_apply (hb y) hfy hfy
  have hgerm : (fun y ↦ mvfderiv I (traceBilin (I := I) h) y (Y y))
      =ᶠ[𝓝 x] fun y ↦ ∑ i, B y (fr i y) (fr i y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    rw [hgrad y hy Y]
    exact Finset.sum_congr rfl fun i _ ↦ (hBapp y hy i).symm
  have hBd : ∀ i, MDiffAt (fun y ↦ B y (fr i y) (fr i y)) x := by
    intro i
    refine (hd i).congr_of_eventuallyEq ?_
    filter_upwards [hu.mem_nhds hx] with y hy
    exact hBapp y hy i
  have hlead : mvfderiv I (fun y ↦ mvfderiv I (traceBilin (I := I) h) y (Y y)) x (X x)
      = ∑ i, cov.covBilin B X (fr i) (fr i) x := by
    rw [hgerm.mvfderiv_eq]
    exact cov.mvfderiv_sum_eq_sum_covBilin_of_frame hcov hs hu hx hBd
  -- each summand is `∇²h` plus the term the Hessian's connection correction subtracts
  have hexpand : ∀ i, cov.covBilin B X (fr i) (fr i) x
      = cov.cov2Bilin h X Y (fr i) (fr i) x
        + cov.covBilin h (fun y ↦ cov Y y (X y)) (fr i) (fr i) x := by
    intro i
    have hmg : (fun y ↦ B y (fr i y) (fr i y))
        =ᶠ[𝓝 x] fun y ↦ cov.covBilin h Y (fr i) (fr i) y := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact hBapp y hy i
    have hm' : mvfderiv I (fun y ↦ B y (fr i y) (fr i y)) x (X x)
        = mvfderiv I (fun y ↦ cov.covBilin h Y (fr i) (fr i) y) x (X x) := by
      rw [hmg.mvfderiv_eq]
    -- values passed explicitly: matching `covBilinForm_apply` against a beta-redex sends the
    -- unifier through `mkHom₂` into the trivialisations behind `FiberBundle.extend`
    have key : ∀ (v w : TangentSpace I x) (V W : Π y : M, TangentSpace I y),
        MDiffAt (T% V) x → MDiffAt (T% W) x → V x = v → W x = w →
        B x v w = cov.covBilin h Y V W x := by
      intro v w V W hV hW hVv hWw
      rw [← hVv, ← hWw]
      exact cov.covBilinForm_apply (hb x) hV hW
    have e₁ : B x (cov (fr i) x (X x)) (fr i x)
        = cov.covBilin h Y (fun y ↦ cov (fr i) y (X y)) (fr i) x :=
      key (cov (fr i) x (X x)) (fr i x) (fun y ↦ cov (fr i) y (X y)) (fr i)
        (cov.mdiffAt_cov_apply (hfr2 i) hX) (hfr1 i) rfl rfl
    have e₂ : B x (fr i x) (cov (fr i) x (X x))
        = cov.covBilin h Y (fr i) (fun y ↦ cov (fr i) y (X y)) x :=
      key (fr i x) (cov (fr i) x (X x)) (fr i) (fun y ↦ cov (fr i) y (X y))
        (hfr1 i) (cov.mdiffAt_cov_apply (hfr2 i) hX) rfl rfl
    have hcB : cov.covBilin B X (fr i) (fr i) x
        = mvfderiv I (fun y ↦ B y (fr i y) (fr i y)) x (X x)
          - B x (cov (fr i) x (X x)) (fr i x) - B x (fr i x) (cov (fr i) x (X x)) := rfl
    have hc2 : cov.cov2Bilin h X Y (fr i) (fr i) x
        = mvfderiv I (fun y ↦ cov.covBilin h Y (fr i) (fr i) y) x (X x)
          - cov.covBilin h (fun y ↦ cov Y y (X y)) (fr i) (fr i) x
          - cov.covBilin h Y (fun y ↦ cov (fr i) y (X y)) (fr i) x
          - cov.covBilin h Y (fr i) (fun y ↦ cov (fr i) y (X y)) x := rfl
    rw [hcB, hc2, hm', e₁, e₂]
    ring
  -- the Hessian's connection correction is the same frame sum
  have hsub : mvfderiv I (traceBilin (I := I) h) x (cov Y x (X x))
      = ∑ i, cov.covBilin h (fun y ↦ cov Y y (X y)) (fr i) (fr i) x :=
    hgrad x hx (fun y ↦ cov Y y (X y))
  simp only [hessianFun]
  rw [hlead, hsub, Finset.sum_congr rfl fun i _ ↦ hexpand i, Finset.sum_add_distrib]
  ring

end MetricTrace

end Symmetric


end CovariantDerivative
