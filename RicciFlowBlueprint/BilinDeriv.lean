/-
The covariant derivative of a bilinear form field, as a tensor.

`Variation.lean` defines `(∇_X h)(Y,Z) = X(h(Y,Z)) − h(∇_X Y, Z) − h(Y, ∇_X Z)` as an
operator on *fields*. Here it is shown to be a genuine `(0,3)`-tensor: linear and pointwise
in all three slots, hence a continuous trilinear form `covBilinAt h x` on `T_xM`.

All three slots are cheap, unlike the four slots of `∇Rm`:

* the **direction** slot is free — `mvfderiv I f x` and `cov Y x` are already continuous
  linear maps out of `T_xM`, so `covBilin` is by construction a CLM in `X x`;
* the **`Y`** and **`Z`** slots are the usual Leibniz cancellation, needing only
  `MDifferentiableAt` of the fields (as `hessian_smul_right` does, not the
  frame-and-globalise argument that `curvature`'s third slot needs).

So `TensorialAt.mkHom₂` applies to the last two slots directly, and one more `mkHom`
assembles the direction. This is the object `Δ_g h` and `div div h` are traces of.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Variation
import RicciFlowBlueprint.TraceCov
import RicciFlowBlueprint.Hessian

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

section Slots

variable {h : M → E →L[ℝ] E →L[ℝ] ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is linear in the direction under scaling: `(∇_{f•X} h)(Y,Z) = f (∇_X h)(Y,Z)`.
No differentiability is needed — each term is a continuous linear map applied to `X x`. -/
theorem covBilin_smul_dir {f : M → ℝ} {X Y Z : Π y : M, TangentSpace I y} {x : M} :
    cov.covBilin h (f • X) Y Z x = f x * cov.covBilin h X Y Z x := by
  have key₁ : ∀ (c : ℝ) (v w : E), (h x) (c • v) w = c * (h x) v w := by
    intro c v w; rw [map_smul]; rfl
  have key₂ : ∀ (c : ℝ) (v w : E), (h x) v (c • w) = c * (h x) v w := by
    intro c v w; rw [map_smul]; rfl
  have hd : mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (f x • X x)
      = f x * mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x) := by
    rw [map_smul]; rfl
  have e₁ : (h x) (cov Y x (f x • X x)) (Z x) = f x * (h x) (cov Y x (X x)) (Z x) := by
    rw [show cov Y x (f x • X x) = f x • cov Y x (X x) from map_smul _ _ _]
    exact key₁ (f x) _ _
  have e₂ : (h x) (Y x) (cov Z x (f x • X x)) = f x * (h x) (Y x) (cov Z x (X x)) := by
    rw [show cov Z x (f x • X x) = f x • cov Z x (X x) from map_smul _ _ _]
    exact key₂ (f x) _ _
  have hfx : (f • X) x = f x • X x := rfl
  simp only [covBilin, hfx]
  rw [hd, e₁, e₂]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is additive in the direction. -/
theorem covBilin_add_dir {X X' Y Z : Π y : M, TangentSpace I y} {x : M} :
    cov.covBilin h (X + X') Y Z x = cov.covBilin h X Y Z x + cov.covBilin h X' Y Z x := by
  have key₁ : ∀ v v' w : E, (h x) (v + v') w = (h x) v w + (h x) v' w :=
    fun v v' w ↦ by rw [map_add]; rfl
  have key₂ : ∀ v w w' : E, (h x) v (w + w') = (h x) v w + (h x) v w' :=
    fun v w w' ↦ map_add _ _ _
  have e₁ : (h x) (cov Y x ((X + X') x)) (Z x)
      = (h x) (cov Y x (X x)) (Z x) + (h x) (cov Y x (X' x)) (Z x) := by
    rw [show cov Y x ((X + X') x) = cov Y x (X x) + cov Y x (X' x) from map_add _ _ _]
    exact key₁ _ _ _
  have e₂ : (h x) (Y x) (cov Z x ((X + X') x))
      = (h x) (Y x) (cov Z x (X x)) + (h x) (Y x) (cov Z x (X' x)) := by
    rw [show cov Z x ((X + X') x) = cov Z x (X x) + cov Z x (X' x) from map_add _ _ _]
    exact key₂ _ _ _
  have hd : mvfderiv I (fun y ↦ h y (Y y) (Z y)) x ((X + X') x)
      = mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X' x) := map_add _ _ _
  simp only [covBilin]
  rw [hd, e₁, e₂]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is **pointwise** in the direction: `(∇_X h)(Y,Z)` at `x` depends on `X` only through
`X x`. -/
theorem covBilin_congr_dir {X X' Y Z : Π y : M, TangentSpace I y} {x : M} (hXX' : X x = X' x) :
    cov.covBilin h X Y Z x = cov.covBilin h X' Y Z x := by
  simp only [covBilin, hXX']

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is linear in the second slot: the Leibniz term of `X(f · h(Y,Z))` is cancelled by
the Leibniz term of `∇_X (f • Y)`. -/
theorem covBilin_smul_snd {f : M → ℝ} {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x) :
    cov.covBilin h X (f • Y) Z x = f x * cov.covBilin h X Y Z x := by
  have key₁ : ∀ (z : M) (c : ℝ) (v w : E), (h z) (c • v) w = c * (h z) v w := by
    intro z c v w; rw [map_smul]; rfl
  have key₂ : ∀ (c d : ℝ) (v v' w : E), (h x) (c • v + d • v') w
      = c * (h x) v w + d * (h x) v' w := by
    intro c d v v' w
    rw [map_add, map_smul, map_smul]; rfl
  have hprod : (fun y ↦ h y ((f • Y) y) (Z y)) = fun y ↦ f y * h y (Y y) (Z y) := by
    funext y
    exact key₁ y (f y) (Y y) (Z y)
  have hcov : cov (f • Y) x (X x)
      = f x • cov Y x (X x) + mvfderiv I f x (X x) • Y x := by
    rw [cov.isCovariantDerivativeOn.leibniz hY hf]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have e₁ : (h x) (cov (f • Y) x (X x)) (Z x)
      = f x * (h x) (cov Y x (X x)) (Z x)
        + mvfderiv I f x (X x) * (h x) (Y x) (Z x) := by
    rw [hcov]
    exact key₂ (f x) (mvfderiv I f x (X x)) (cov Y x (X x)) (Y x) (Z x)
  have e₂ : (h x) ((f • Y) x) (cov Z x (X x)) = f x * (h x) (Y x) (cov Z x (X x)) :=
    key₁ x (f x) (Y x) (cov Z x (X x))
  simp only [covBilin]
  rw [hprod, mvfderiv_fun_mul hf hh, e₁, e₂]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is additive in the second slot. -/
theorem covBilin_add_snd {X Y Y' Z : Π y : M, TangentSpace I y} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x)
    (hh' : MDiffAt (fun y ↦ h y (Y' y) (Z y)) x) :
    cov.covBilin h X (Y + Y') Z x = cov.covBilin h X Y Z x + cov.covBilin h X Y' Z x := by
  have key : ∀ (z : M) (v v' w : E), (h z) (v + v') w = (h z) v w + (h z) v' w := by
    intro z v v' w; rw [map_add]; rfl
  have hsum : (fun y ↦ h y ((Y + Y') y) (Z y))
      = fun y ↦ h y (Y y) (Z y) + h y (Y' y) (Z y) := by
    funext y
    exact key y (Y y) (Y' y) (Z y)
  have e₁ : (h x) (cov (Y + Y') x (X x)) (Z x)
      = (h x) (cov Y x (X x)) (Z x) + (h x) (cov Y' x (X x)) (Z x) := by
    rw [cov.isCovariantDerivativeOn.add hY hY']
    exact key x (cov Y x (X x)) (cov Y' x (X x)) (Z x)
  have e₂ : (h x) ((Y + Y') x) (cov Z x (X x))
      = (h x) (Y x) (cov Z x (X x)) + (h x) (Y' x) (cov Z x (X x)) :=
    key x (Y x) (Y' x) (cov Z x (X x))
  simp only [covBilin]
  rw [hsum, mvfderiv_fun_add hh hh', e₁, e₂]
  simp only [add_apply]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is linear in the third slot, by the same cancellation as the second. -/
theorem covBilin_smul_thd {f : M → ℝ} {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hf : MDiffAt f x) (hZ : MDiffAt (T% Z) x)
    (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x) :
    cov.covBilin h X Y (f • Z) x = f x * cov.covBilin h X Y Z x := by
  have key₁ : ∀ (z : M) (c : ℝ) (v w : E), (h z) v (c • w) = c * (h z) v w := by
    intro z c v w; rw [map_smul]; rfl
  have key₂ : ∀ (c d : ℝ) (v w w' : E), (h x) v (c • w + d • w')
      = c * (h x) v w + d * (h x) v w' := by
    intro c d v w w'
    rw [map_add, map_smul, map_smul]; rfl
  have hprod : (fun y ↦ h y (Y y) ((f • Z) y)) = fun y ↦ f y * h y (Y y) (Z y) := by
    funext y
    exact key₁ y (f y) (Y y) (Z y)
  have hcov : cov (f • Z) x (X x)
      = f x • cov Z x (X x) + mvfderiv I f x (X x) • Z x := by
    rw [cov.isCovariantDerivativeOn.leibniz hZ hf]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have e₁ : (h x) (cov Y x (X x)) ((f • Z) x) = f x * (h x) (cov Y x (X x)) (Z x) :=
    key₁ x (f x) (cov Y x (X x)) (Z x)
  have e₂ : (h x) (Y x) (cov (f • Z) x (X x))
      = f x * (h x) (Y x) (cov Z x (X x))
        + mvfderiv I f x (X x) * (h x) (Y x) (Z x) := by
    rw [hcov]
    exact key₂ (f x) (mvfderiv I f x (X x)) (Y x) (cov Z x (X x)) (Z x)
  simp only [covBilin]
  rw [hprod, mvfderiv_fun_mul hf hh, e₁, e₂]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇h` is additive in the third slot. -/
theorem covBilin_add_thd {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x)
    (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x)
    (hh' : MDiffAt (fun y ↦ h y (Y y) (Z' y)) x) :
    cov.covBilin h X Y (Z + Z') x = cov.covBilin h X Y Z x + cov.covBilin h X Y Z' x := by
  have key : ∀ (z : M) (v w w' : E), (h z) v (w + w') = (h z) v w + (h z) v w' :=
    fun z v w w' ↦ map_add _ _ _
  have hsum : (fun y ↦ h y (Y y) ((Z + Z') y))
      = fun y ↦ h y (Y y) (Z y) + h y (Y y) (Z' y) := by
    funext y
    exact key y (Y y) (Z y) (Z' y)
  have e₁ : (h x) (cov Y x (X x)) ((Z + Z') x)
      = (h x) (cov Y x (X x)) (Z x) + (h x) (cov Y x (X x)) (Z' x) :=
    key x (cov Y x (X x)) (Z x) (Z' x)
  have e₂ : (h x) (Y x) (cov (Z + Z') x (X x))
      = (h x) (Y x) (cov Z x (X x)) + (h x) (Y x) (cov Z' x (X x)) := by
    rw [cov.isCovariantDerivativeOn.add hZ hZ']
    exact key x (Y x) (cov Z x (X x)) (cov Z' x (X x))
  simp only [covBilin]
  rw [hsum, mvfderiv_fun_add hh hh', e₁, e₂]
  simp only [add_apply]
  ring

end Slots

section Tensor

variable {h : M → E →L[ℝ] E →L[ℝ] ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇h` is tensorial in its direction, with no hypotheses at all.** Each of the three terms
of `(∇_X h)(Y,Z)` is a continuous linear map applied to `X x`, so no Leibniz rule and no
differentiability is involved. -/
theorem tensorialAt_covBilin_dir (Y Z : Π y : M, TangentSpace I y) (x : M) :
    TensorialAt I E (fun X ↦ cov.covBilin h X Y Z x) x where
  smul _ _ := cov.covBilin_smul_dir
  add _ _ := cov.covBilin_add_dir

/-- **The direction slot of `∇h`, as a continuous linear form on `T_xM`**: `v ↦ (∇_v h)(Y,Z)`.
Together with `covBilinForm` below this makes `∇h` a genuine `(0,3)`-tensor. -/
noncomputable def covBilinDir (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (Y Z : Π y : M, TangentSpace I y) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom (fun X ↦ cov.covBilin h X Y Z x) x (cov.tensorialAt_covBilin_dir Y Z x)

omit [CompleteSpace E] in
theorem covBilinDir_apply (Y Z : Π y : M, TangentSpace I y) {X : Π y : M, TangentSpace I y}
    {x : M} (hX : MDiffAt (T% X) x) :
    cov.covBilinDir h Y Z x (X x) = cov.covBilin h X Y Z x :=
  TensorialAt.mkHom_apply _ hX

/-- **`h` is differentiable against differentiable fields at `x`.** The hypothesis the second
and third slots of `∇h` need: it is what makes `y ↦ h y (Y y) (Z y)` a differentiable function
whose Leibniz rule can be applied. Implied by `h` being `C¹` into `E →L[ℝ] E →L[ℝ] ℝ`, and
verified directly for the tensors of interest (`ricciForm`, the metric). -/
def IsMDiffBilinAt (h : M → E →L[ℝ] E →L[ℝ] ℝ) (x : M) : Prop :=
  ∀ U V : Π y : M, TangentSpace I y, MDiffAt (T% U) x → MDiffAt (T% V) x →
    MDiffAt (fun y ↦ h y (U y) (V y)) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem tensorialAt_covBilin_snd (hb : IsMDiffBilinAt (I := I) h x)
    (X : Π y : M, TangentSpace I y) {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun Y ↦ cov.covBilin h X Y Z x) x where
  smul hf hY := cov.covBilin_smul_snd hf hY (hb _ _ hY hZ)
  add hY hY' := cov.covBilin_add_snd hY hY' (hb _ _ hY hZ) (hb _ _ hY' hZ)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem tensorialAt_covBilin_thd (hb : IsMDiffBilinAt (I := I) h x)
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z ↦ cov.covBilin h X Y Z x) x where
  smul hf hZ := cov.covBilin_smul_thd hf hZ (hb _ _ hY hZ)
  add hZ hZ' := cov.covBilin_add_thd hZ hZ' (hb _ _ hY hZ) (hb _ _ hY hZ')

/-- **`∇_X h` as a continuous bilinear form on `T_xM`.** With `covBilinDir` supplying the
direction slot, this makes `∇h` a genuine `(0,3)`-tensor. -/
noncomputable def covBilinForm (hb : IsMDiffBilinAt (I := I) h x)
    (X : Π y : M, TangentSpace I y) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun Y Z ↦ cov.covBilin h X Y Z x) x
    (fun _ hZ ↦ cov.tensorialAt_covBilin_snd hb X hZ)
    (fun _ hY ↦ cov.tensorialAt_covBilin_thd hb X hY)

omit [CompleteSpace E] in
theorem covBilinForm_apply (hb : IsMDiffBilinAt (I := I) h x)
    {X Y Z : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    cov.covBilinForm hb X (Y x) (Z x) = cov.covBilin h X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hY hZ

omit [CompleteSpace E] in
/-- **`∇h` is pointwise in its second slot** (among differentiable fields): `(∇_X h)(Y,Z)` at
`x` depends on `Y` only through `Y x`. Immediate from `covBilinForm_apply`, no frame argument
needed. -/
theorem covBilin_congr_snd (hb : IsMDiffBilinAt (I := I) h x)
    (X : Π y : M, TangentSpace I y) {Y Y' Z : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x)
    (hYY' : Y x = Y' x) :
    cov.covBilin h X Y Z x = cov.covBilin h X Y' Z x := by
  rw [← cov.covBilinForm_apply hb hY hZ, ← cov.covBilinForm_apply hb hY' hZ, hYY']

omit [CompleteSpace E] in
/-- **`∇h` is pointwise in its third slot** (among differentiable fields). -/
theorem covBilin_congr_thd (hb : IsMDiffBilinAt (I := I) h x)
    (X : Π y : M, TangentSpace I y) {Y Z Z' : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x)
    (hZZ' : Z x = Z' x) :
    cov.covBilin h X Y Z x = cov.covBilin h X Y Z' x := by
  rw [← cov.covBilinForm_apply hb hY hZ, ← cov.covBilinForm_apply hb hY hZ', hZZ']

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇h` is linear in `h`** under a constant rescaling. -/
theorem covBilin_smul_form (c : ℝ) (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x) :
    cov.covBilin (fun y ↦ (c • h y : E →L[ℝ] E →L[ℝ] ℝ)) X Y Z x
      = c * cov.covBilin h X Y Z x := by
  have hfun : (fun y ↦ (c • h y : E →L[ℝ] E →L[ℝ] ℝ) (Y y) (Z y))
      = fun y ↦ c * h y (Y y) (Z y) := by
    funext y; rfl
  have hd : mvfderiv I (fun y ↦ c * h y (Y y) (Z y)) x (X x)
      = c * mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x) := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const hh, mvfderiv_const]
    simp
  have e₁ : (c • h x : E →L[ℝ] E →L[ℝ] ℝ) (cov Y x (X x)) (Z x)
      = c * h x (cov Y x (X x)) (Z x) := rfl
  have e₂ : (c • h x : E →L[ℝ] E →L[ℝ] ℝ) (Y x) (cov Z x (X x))
      = c * h x (Y x) (cov Z x (X x)) := rfl
  simp only [covBilin, hfun]
  rw [hd, e₁, e₂]
  ring

end Tensor

section Trace

open scoped RealInnerProductSpace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] {h : M → E →L[ℝ] E →L[ℝ] ℝ}

omit [CompleteSpace E] in
/-- **The metric trace of `∇_X h` is frame-independent.** `∇_X h` is a continuous bilinear form
(`covBilinForm`), so `OrthonormalBasis.sum_apply_self_eq` applies with no further input: the
sum `∑ᵢ (∇_X h)(eᵢ,eᵢ)` that `TraceCov.lean` computes does not depend on the orthonormal basis
it is taken over. -/
theorem sum_covBilin_congr (hb : IsMDiffBilinAt (I := I) h x)
    (X : Π y : M, TangentSpace I y) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (c : OrthonormalBasis κ ℝ (TangentSpace I x)) :
    ∑ i, cov.covBilinForm hb X (b i) (b i) = ∑ j, cov.covBilinForm hb X (c j) (c j) :=
  OrthonormalBasis.sum_apply_self_eq b c (cov.covBilinForm hb X)

end Trace

end CovariantDerivative
