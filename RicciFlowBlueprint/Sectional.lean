/- Sectional curvature. Namespaces `Scratch2`..`Scratch5` are the agent's incremental
   layers, each with its own instance requirements; kept verbatim because this is the
   form that compiles clean. Consolidating them is cosmetic follow-up work. -/
import RicciFlowBlueprint.Ricci
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Bundle VectorField FiberBundle
open scoped Manifold ContDiff

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- Workaround for the instance-through-type-synonym problem (lean4#9077), following the
pattern of mathlib PR #36845: the inner product of two vector fields is differentiable at `x`
when both fields are. -/
lemma mdiffAt_inner_vectorField [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y ↦ ⟪X y, Y y⟫) x :=
  MDifferentiableAt.inner_bundle (E := TangentSpace I) (F := E) hX hY

/-- `C^n` version of `mdiffAt_inner_vectorField`. -/
lemma cmdiff_inner_vectorField {n : ℕ∞ω}
    [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]
    {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff n (T% X)) (hY : CMDiff n (T% Y)) :
    CMDiff n (fun y ↦ ⟪X y, Y y⟫) :=
  ContMDiff.inner_bundle (E := TangentSpace I) (F := E) hX hY

variable [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- For a metric-compatible connection, `⟪R(X,Y)Z, Z⟫ = 0`. -/
theorem inner_curvature_self_right [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiff 2 (T% Z)) :
    ⟪cov.curvature X Y Z x, Z x⟫ = 0 := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hZm : MDiff (T% Z) := hZ.mdifferentiable h2
  -- the sections ∇_Y Z and ∇_X Z are differentiable at x
  have hAx : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x := cov.mdiffAt_cov_apply hZ hY
  have hBx : MDiffAt (T% (fun y ↦ cov Z y (X y))) x := cov.mdiffAt_cov_apply hZ hX
  -- f = ⟪Z, Z⟫ is C² at x
  have hfC2 : CMDiffAt 2 (fun y ↦ ⟪Z y, Z y⟫) x := (cmdiff_inner_vectorField hZ hZ) x
  -- first derivative of f in any direction field V, as a function identity
  have hdf : ∀ V : Π y : M, TangentSpace I y,
      (fun y ↦ d% (fun z ↦ ⟪Z z, Z z⟫) y (V y))
        = (fun y ↦ ⟪cov Z y (V y), Z y⟫) + (fun y ↦ ⟪Z y, cov Z y (V y)⟫) := by
    intro V
    funext y
    exact hcov.mvfderiv_inner_eq V (hZm y) (hZm y)
  -- second derivatives
  have e1 : d% (fun y ↦ d% (fun z ↦ ⟪Z z, Z z⟫) y (Y y)) x (X x)
      = (⟪cov (fun y ↦ cov Z y (Y y)) x (X x), Z x⟫ + ⟪cov Z x (Y x), cov Z x (X x)⟫)
        + (⟪cov Z x (X x), cov Z x (Y x)⟫ + ⟪Z x, cov (fun y ↦ cov Z y (Y y)) x (X x)⟫) := by
    rw [hdf Y, mvfderiv_add (mdiffAt_inner_vectorField hAx (hZm x))
      (mdiffAt_inner_vectorField (hZm x) hAx), ContinuousLinearMap.add_apply,
      hcov.mvfderiv_inner_eq X hAx (hZm x), hcov.mvfderiv_inner_eq X (hZm x) hAx]
  have e2 : d% (fun y ↦ d% (fun z ↦ ⟪Z z, Z z⟫) y (X y)) x (Y x)
      = (⟪cov (fun y ↦ cov Z y (X y)) x (Y x), Z x⟫ + ⟪cov Z x (X x), cov Z x (Y x)⟫)
        + (⟪cov Z x (Y x), cov Z x (X x)⟫ + ⟪Z x, cov (fun y ↦ cov Z y (X y)) x (Y x)⟫) := by
    rw [hdf X, mvfderiv_add (mdiffAt_inner_vectorField hBx (hZm x))
      (mdiffAt_inner_vectorField (hZm x) hBx), ContinuousLinearMap.add_apply,
      hcov.mvfderiv_inner_eq Y hBx (hZm x), hcov.mvfderiv_inner_eq Y (hZm x) hBx]
  -- the bracket term
  have ebr : d% (fun z ↦ ⟪Z z, Z z⟫) x (mlieBracket I X Y x)
      = ⟪cov Z x (mlieBracket I X Y x), Z x⟫ + ⟪Z x, cov Z x (mlieBracket I X Y x)⟫ :=
    hcov.mvfderiv_inner_eq (mlieBracket I X Y) (hZm x) (hZm x)
  -- second-derivative symmetry: the bracket acts as a derivation
  have hsym := VectorField.mlieBracket_apply_fun (f := fun y ↦ ⟪Z y, Z y⟫) hfC2 hX hY
  -- symmetry facts for the inner product
  have c1 : ⟪Z x, cov (fun y ↦ cov Z y (Y y)) x (X x)⟫
      = ⟪cov (fun y ↦ cov Z y (Y y)) x (X x), Z x⟫ := real_inner_comm _ _
  have c2 : ⟪Z x, cov (fun y ↦ cov Z y (X y)) x (Y x)⟫
      = ⟪cov (fun y ↦ cov Z y (X y)) x (Y x), Z x⟫ := real_inner_comm _ _
  have c3 : ⟪cov Z x (Y x), cov Z x (X x)⟫ = ⟪cov Z x (X x), cov Z x (Y x)⟫ :=
    real_inner_comm _ _
  have c4 : ⟪Z x, cov Z x (mlieBracket I X Y x)⟫ = ⟪cov Z x (mlieBracket I X Y x), Z x⟫ :=
    real_inner_comm _ _
  simp only [curvature, inner_sub_left]
  linarith

end CovariantDerivative

namespace Scratch2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

open CovariantDerivative

/-- Skew-symmetry of the curvature in its last two (metric) slots. -/
theorem inner_curvature_right_skew [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫ = - ⟪cov.curvature X Y W x, Z x⟫ := by
  have h0 := cov.inner_curvature_self_right hcov hX hY (hZ.add_section hW)
  rw [cov.curvature_add_right hZ hW hX hY] at h0
  have hz := cov.inner_curvature_self_right hcov hX hY hZ
  have hw := cov.inner_curvature_self_right hcov hX hY hW
  simp only [Pi.add_apply, inner_add_left, inner_add_right] at h0
  linarith [real_inner_comm (cov.curvature X Y Z x) (W x),
    real_inner_comm (cov.curvature X Y W x) (Z x)]

/-- The curvature operator vanishes when its first two arguments agree. -/
theorem curvature_self_left (X Z : Π y : M, TangentSpace I y) (x : M) :
    cov.curvature X X Z x = 0 := by
  have h := cov.curvature_antisymm X X Z x
  have h2 : (2 : ℝ) • cov.curvature X X Z x = 0 := by
    linear_combination (norm := module) h
  simpa using h2

/-- Constant-scalar homogeneity in the first slot. -/
theorem curvature_smul_const_fst [ContMDiffCovariantDerivative cov 1]
    (a : ℝ) {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hZ : CMDiff 2 (T% Z)) :
    cov.curvature (a • X) Y Z x = a • cov.curvature X Y Z x := by
  have h : (a • X) = (fun _ : M ↦ a) • X := rfl
  rw [h, cov.curvature_smul_left (fun _ ↦ a) X Y Z (mdifferentiableAt_const)
    hX (cov.mdiffAt_cov_apply hZ hX)]

/-- Constant-scalar homogeneity in the middle slot. -/
theorem curvature_smul_const_snd [ContMDiffCovariantDerivative cov 1]
    (a : ℝ) {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : CMDiff 2 (T% Z)) :
    cov.curvature X (a • Y) Z x = a • cov.curvature X Y Z x := by
  have h : (a • Y) = (fun _ : M ↦ a) • Y := rfl
  rw [h, cov.curvature_smul_middle (fun _ ↦ a) X Y Z (mdifferentiableAt_const)
    hY (cov.mdiffAt_cov_apply hZ hY)]

end Scratch2

namespace Scratch3

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

open CovariantDerivative Scratch2

/-- The sectional-curvature numerator scales by `(ad - bc)²` under a constant-coefficient
change of the spanning fields. -/
theorem inner_curvature_basis_change [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (a b c d : ℝ) :
    ⟪cov.curvature (a • X + b • Y) (c • X + d • Y) (c • X + d • Y) x, (a • X + b • Y) x⟫
      = (a * d - b * c) ^ 2 * ⟪cov.curvature X Y Y x, X x⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hXx : MDiffAt (T% X) x := (hX.mdifferentiable h2) x
  have hYx : MDiffAt (T% Y) x := (hY.mdifferentiable h2) x
  have haX : CMDiff 2 (T% (a • X)) := hX.const_smul_section
  have hbY : CMDiff 2 (T% (b • Y)) := hY.const_smul_section
  have hcX : CMDiff 2 (T% (c • X)) := hX.const_smul_section
  have hdY : CMDiff 2 (T% (d • Y)) := hY.const_smul_section
  have hX' : CMDiff 2 (T% (a • X + b • Y)) := haX.add_section hbY
  have hY' : CMDiff 2 (T% (c • X + d • Y)) := hcX.add_section hdY
  have haXx : MDiffAt (T% (a • X)) x := (haX.mdifferentiable h2) x
  have hbYx : MDiffAt (T% (b • Y)) x := (hbY.mdifferentiable h2) x
  have hcXx : MDiffAt (T% (c • X)) x := (hcX.mdifferentiable h2) x
  have hdYx : MDiffAt (T% (d • Y)) x := (hdY.mdifferentiable h2) x
  have hX'x : MDiffAt (T% (a • X + b • Y)) x := (hX'.mdifferentiable h2) x
  have hY'x : MDiffAt (T% (c • X + d • Y)) x := (hY'.mdifferentiable h2) x
  -- slot-3 expansion
  have h3 : cov.curvature (a • X + b • Y) (c • X + d • Y) (c • X + d • Y) x
      = c • cov.curvature (a • X + b • Y) (c • X + d • Y) X x
        + d • cov.curvature (a • X + b • Y) (c • X + d • Y) Y x := by
    rw [cov.curvature_add_right hcX hdY hX'x hY'x,
      cov.curvature_smul_const_right c hX hX'x hY'x,
      cov.curvature_smul_const_right d hY hX'x hY'x]
  -- full reduction of the two slot-3 pieces
  have hR1 : cov.curvature (a • X + b • Y) (c • X + d • Y) X x
      = (a * d - b * c) • cov.curvature X Y X x := by
    rw [cov.curvature_add_left hX haXx hbYx,
      curvature_smul_const_fst cov a hXx hX, curvature_smul_const_fst cov b hYx hX,
      cov.curvature_add_middle (X := X) hX hcXx hdYx,
      cov.curvature_add_middle (X := Y) hX hcXx hdYx,
      curvature_smul_const_snd cov (X := X) c hXx hX,
      curvature_smul_const_snd cov (X := X) d hYx hX,
      curvature_smul_const_snd cov (X := Y) c hXx hX,
      curvature_smul_const_snd cov (X := Y) d hYx hX,
      curvature_self_left cov X X x, curvature_self_left cov Y X x,
      cov.curvature_antisymm Y X X x]
    module
  have hR2 : cov.curvature (a • X + b • Y) (c • X + d • Y) Y x
      = (a * d - b * c) • cov.curvature X Y Y x := by
    rw [cov.curvature_add_left hY haXx hbYx,
      curvature_smul_const_fst cov a hXx hY, curvature_smul_const_fst cov b hYx hY,
      cov.curvature_add_middle (X := X) hY hcXx hdYx,
      cov.curvature_add_middle (X := Y) hY hcXx hdYx,
      curvature_smul_const_snd cov (X := X) c hXx hY,
      curvature_smul_const_snd cov (X := X) d hYx hY,
      curvature_smul_const_snd cov (X := Y) c hXx hY,
      curvature_smul_const_snd cov (X := Y) d hYx hY,
      curvature_self_left cov X Y x, curvature_self_left cov Y Y x,
      cov.curvature_antisymm Y X Y x]
    module
  -- inner-product base values
  have s0 : ⟪cov.curvature X Y X x, X x⟫ = 0 :=
    cov.inner_curvature_self_right hcov hXx hYx hX
  have s1 : ⟪cov.curvature X Y Y x, Y x⟫ = 0 :=
    cov.inner_curvature_self_right hcov hXx hYx hY
  have s2 : ⟪cov.curvature X Y X x, Y x⟫ = - ⟪cov.curvature X Y Y x, X x⟫ :=
    inner_curvature_right_skew cov hcov hXx hYx hX hY
  rw [h3, hR1, hR2]
  simp only [Pi.add_apply, Pi.smul_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [s0, s1, s2]
  ring

end Scratch3

namespace Scratch4

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

open CovariantDerivative Scratch2 Scratch3

/-- Sectional curvature: `K(X,Y) = ⟪R(X,Y)Y, X⟫ / (‖X‖²‖Y‖² - ⟪X,Y⟫²)` at `x`,
with junk value `0` when `X x`, `Y x` are linearly dependent (division by zero). -/
noncomputable def sectionalCurvature (X Y : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  ⟪cov.curvature X Y Y x, X x⟫ / (‖X x‖ ^ 2 * ‖Y x‖ ^ 2 - ⟪X x, Y x⟫ ^ 2)

/-- Gram determinant transformation under change of basis. -/
lemma gram_det_basis_change {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u v : F) (a b c d : ℝ) :
    ‖a • u + b • v‖ ^ 2 * ‖c • u + d • v‖ ^ 2 - ⟪a • u + b • v, c • u + d • v⟫ ^ 2
      = (a * d - b * c) ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u]
  ring

/-- Sectional curvature is invariant under a constant-coefficient invertible change of the
spanning fields. -/
theorem sectionalCurvature_basis_change [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    {a b c d : ℝ} (h : a * d - b * c ≠ 0) :
    sectionalCurvature cov (a • X + b • Y) (c • X + d • Y) x
      = sectionalCurvature cov X Y x := by
  unfold sectionalCurvature
  have hnum := inner_curvature_basis_change (x := x) cov hcov hX hY a b c d
  have hden : ‖(a • X + b • Y) x‖ ^ 2 * ‖(c • X + d • Y) x‖ ^ 2
      - ⟪(a • X + b • Y) x, (c • X + d • Y) x⟫ ^ 2
      = (a * d - b * c) ^ 2 * (‖X x‖ ^ 2 * ‖Y x‖ ^ 2 - ⟪X x, Y x⟫ ^ 2) := by
    simp only [Pi.add_apply, Pi.smul_apply]
    exact gram_det_basis_change (X x) (Y x) a b c d
  rw [hnum, hden]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 h)

/-- Curvature depends on the first slot only through its value at `x`. -/
theorem curvature_congr_fst [ContMDiffCovariantDerivative cov 1]
    {X X' V Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiff 2 (T% Z))
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hxx : X x = X' x) :
    cov.curvature X V Z x = cov.curvature X' V Z x :=
  (cov.tensorialAt_curvature_fst hZ x).pointwise hX hX' hxx

/-- Curvature depends on the middle slot only through its value at `x`. -/
theorem curvature_congr_snd [ContMDiffCovariantDerivative cov 1]
    {V Y Y' Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiff 2 (T% Z))
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hyy : Y x = Y' x) :
    cov.curvature V Y Z x = cov.curvature V Y' Z x :=
  (cov.tensorialAt_curvature_snd hZ x).pointwise hY hY' hyy

end Scratch4

namespace Scratch5

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

open CovariantDerivative Scratch2 Scratch3 Scratch4

/-- Well-definedness of the sectional curvature: it depends only on the plane spanned by the
values at `x`, given pointwise dependence of the curvature's third slot (hypothesis `h3`,
a theorem on the model space). -/
theorem sectionalCurvature_congr [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y X' Y' : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hX' : CMDiff 2 (T% X')) (hY' : CMDiff 2 (T% Y'))
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0)
    (hXx : X' x = a • X x + b • Y x) (hYx : Y' x = c • X x + d • Y x)
    (h3 : ∀ W W' : Π y : M, TangentSpace I y, CMDiff 2 (T% W) → CMDiff 2 (T% W') →
      W x = W' x → cov.curvature X' Y' W x = cov.curvature X' Y' W' x) :
    sectionalCurvature cov X' Y' x = sectionalCurvature cov X Y x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hX'' : CMDiff 2 (T% (a • X + b • Y)) :=
    (hX.const_smul_section).add_section (hY.const_smul_section)
  have hY'' : CMDiff 2 (T% (c • X + d • Y)) :=
    (hX.const_smul_section).add_section (hY.const_smul_section)
  have hxx' : X' x = (a • X + b • Y) x := by simp [hXx]
  have hyy' : Y' x = (c • X + d • Y) x := by simp [hYx]
  have step : sectionalCurvature cov X' Y' x
      = sectionalCurvature cov (a • X + b • Y) (c • X + d • Y) x := by
    unfold sectionalCurvature
    rw [h3 Y' (c • X + d • Y) hY' hY'' hyy',
      curvature_congr_fst cov hY'' ((hX'.mdifferentiable h2) x) ((hX''.mdifferentiable h2) x) hxx',
      curvature_congr_snd cov hY'' ((hY'.mdifferentiable h2) x) ((hY''.mdifferentiable h2) x) hyy',
      hxx', hyy']
  rw [step]
  exact sectionalCurvature_basis_change cov hcov hX hY hdet

end Scratch5

section ScratchModel

open CovariantDerivative Scratch2 Scratch3 Scratch4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) 2 E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)]
  [ContMDiffVectorBundle 1 E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, E)]

variable (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))

/-- On the model space, sectional curvature is genuinely well-defined on planes:
hypothesis-free, since the third slot of the curvature is pointwise there. -/
theorem sectionalCurvature_congr_model [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.IsMetricCompatible (M := E) (V := TangentSpace 𝓘(ℝ, E)))
    {X Y X' Y' : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hX' : CMDiff 2 (T% X')) (hY' : CMDiff 2 (T% Y'))
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0)
    (hXx : X' x = a • X x + b • Y x) (hYx : Y' x = c • X x + d • Y x) :
    sectionalCurvature cov X' Y' x = sectionalCurvature cov X Y x :=
  Scratch5.sectionalCurvature_congr cov hcov hX hY hX' hY' hdet hXx hYx
    (fun _ _ hW hW' hww ↦ cov.curvature_third_slot_pointwise_model hX' hY' hW hW' hww)

end ScratchModel
