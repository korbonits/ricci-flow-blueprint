/-
Scalar curvature: the metric trace of the Ricci curvature, `scal = tr_g Ric`.

The metric is a *fixed* `RiemannianBundle` instance, as in `Sectional.lean` — no
quantification over metrics, so the `Hamilton.lean` elaboration pattern is not
needed here. (It WILL be needed the day `scal` must vary with a flowing metric —
e.g. for Perelman's `F` and `W` functionals — exactly as `Admits*` in
`Hamilton.lean`: elaborate the statement once with the instance as an ambient
binder, then apply under `letI`.)

## The obstruction on a general manifold, and what exists instead

`scal(x) = Σᵢ Ric(bᵢ, bᵢ)(x)` needs an orthonormal basis of `TangentSpace I x`
fed into *both* slots of `ricci`. The first slot is genuinely tensorial
(`tensorialAt_ricci_fst`, whence `ricci_congr_fst`), but the second slot is the
curvature's third slot, which the connection differentiates: `ricci_eq_trace`
demands a globally `C²` field there, and the canonical bundle extension
`FiberBundle.extend` of a tangent vector is only smooth *near* `x`
(`contMDiffAt_extend`). So on a general manifold two pieces of machinery are
missing, both hypotheses in the tradition of `ricci_sub_ricci_swap`:

1. global `C²` extensions of tangent vectors (bump-function sections);
2. pointwise dependence of the curvature's third slot (`h3` below), which is a
   theorem only on the model space (`curvature_third_slot_pointwise_model`).

Consequently the general-manifold definition is *frame-relative*
(`scalarCurvatureWith`, the sum `Σᵢ Ric(bᵢ, bᵢ)` over a finite family of
fields), with frame-independence proved modulo `h3`
(`scalarCurvatureWith_congr`: any two `C²` families whose values at `x` are
orthonormal bases agree). On the model space both missing pieces are theorems —
constant sections extend globally and `h3` holds (`curvature_congr_third_model`,
which upgrades `curvature_third_slot_pointwise_model` to a merely differentiable
first slot via first-slot tensoriality) — so `scalarCurvature` is defined
outright and is hypothesis-free well-defined (`scalarCurvature_eq_sum`).

Supporting API, general manifold:

* `ricci_add_right` / `ricci_smul_const_right` / `ricci_sum_right` /
  `ricci_zero_right` — linearity of Ricci in its second argument (the first is
  `ricci_add_left`/`ricci_smul_left` in `Ricci.lean`), through the traced
  endomorphism via `curvature_add_right`/`curvature_smul_const_right`.
* `ricci_congr_fst` / `ricci_congr_snd` — pointwise dependence (the latter
  relative to `h3`).
* `ricci_eq_sum_inner_curvature` — Ricci as an orthonormal-frame sum
  `Ric(X,Y)(x) = Σᵢ ⟪bᵢ, R(extend bᵢ, X)Y⟫`, hypothesis-free on a general
  Riemannian manifold: the trace is computed by `LinearMap.trace_eq_sum_inner`
  and the traced endomorphism applied via `extend` (which only needs `MDiffAt`).
* `ricci_combination_expand` — bilinearity of Ricci over finite combinations,
  the computational heart of frame-independence (with Parseval,
  `OrthonormalBasis.sum_inner_mul_inner`).
-/
import RicciFlowBlueprint.Sectional
import Mathlib.Analysis.InnerProductSpace.Trace

open Bundle VectorField FiberBundle
open scoped Manifold ContDiff

local notation "⟪" x ", " y "⟫" => inner ℝ x y

set_option maxSynthPendingDepth 3

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-! ### Second-slot linearity and congruence of the Ricci curvature -/

/-- Ricci curvature kills the zero section in its second argument. -/
theorem ricci_zero_right [ContMDiffCovariantDerivative cov 1]
    {X : Π y : M, TangentSpace I y} {x : M} :
    cov.ricci X 0 x = 0 := by
  have h0 : CMDiff 2 (T% (0 : Π y : M, TangentSpace I y)) := contMDiff_zeroSection _ _
  rw [cov.ricci_eq_trace h0 x]
  convert map_zero (LinearMap.trace ℝ (TangentSpace I x))
  ext v
  simpa only [TensorialAt.mkHom_apply_eq_extend, ContinuousLinearMap.coe_coe,
    LinearMap.zero_apply] using cov.curvature_zero_right

/-- Ricci curvature is additive in its second argument. -/
theorem ricci_add_right [ContMDiffCovariantDerivative cov 1]
    {X Y Y' : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y')) (hX : MDiffAt (T% X) x) :
    cov.ricci X (Y + Y') x = cov.ricci X Y x + cov.ricci X Y' x := by
  rw [cov.ricci_eq_trace (hY.add_section hY') x, cov.ricci_eq_trace hY x,
    cov.ricci_eq_trace hY' x, ← map_add]
  congr 1
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend, LinearMap.add_apply,
    ContinuousLinearMap.coe_coe]
  exact cov.curvature_add_right hY hY' (mdifferentiableAt_extend ..) hX

/-- Ricci curvature commutes with constant scalars in its second argument. -/
theorem ricci_smul_const_right [ContMDiffCovariantDerivative cov 1]
    (c : ℝ) {X Y : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hX : MDiffAt (T% X) x) :
    cov.ricci X (c • Y) x = c * cov.ricci X Y x := by
  rw [cov.ricci_eq_trace hY.const_smul_section x, cov.ricci_eq_trace hY x,
    show c * _ = c • LinearMap.trace ℝ (TangentSpace I x)
      (TensorialAt.mkHom (fun W ↦ cov.curvature W X Y x) x
        (cov.tensorialAt_curvature_fst hY x)).toLinearMap from rfl, ← map_smul]
  congr 1
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe]
  exact cov.curvature_smul_const_right c hY (mdifferentiableAt_extend ..) hX

/-- Ricci curvature commutes with finite sums in its second argument. -/
theorem ricci_sum_right [ContMDiffCovariantDerivative cov 1]
    {ι : Type*} {s : Finset ι} {X : Π y : M, TangentSpace I y}
    {Z : ι → Π y : M, TangentSpace I y} {x : M}
    (hZ : ∀ i ∈ s, CMDiff 2 (T% (Z i))) (hX : MDiffAt (T% X) x) :
    cov.ricci X (fun y ↦ ∑ i ∈ s, Z i y) x = ∑ i ∈ s, cov.ricci X (Z i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      have h : (fun y : M ↦ ∑ i ∈ (∅ : Finset ι), Z i y)
          = (0 : Π y : M, TangentSpace I y) := by
        funext y; simp
      rw [h, cov.ricci_zero_right]
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hZ
      have hsum : (fun y : M ↦ ∑ i ∈ insert a s, Z i y)
          = Z a + fun y ↦ ∑ i ∈ s, Z i y := by
        funext y; simp [Finset.sum_insert ha]
      rw [hsum, Finset.sum_insert ha, ← h hZ.2,
        cov.ricci_add_right hZ.1 (.sum_section hZ.2) hX]

/-- First-argument tensoriality of the Ricci curvature in the sense of `TensorialAt`,
packaging `ricci_add_left` and `ricci_smul_left`. -/
theorem tensorialAt_ricci_fst [ContMDiffCovariantDerivative cov 1]
    {Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y)) (x : M) :
    TensorialAt I E (fun X ↦ cov.ricci X Y x) x where
  smul hf hσ := cov.ricci_smul_left hY hf hσ
  add hσ hσ' := cov.ricci_add_left hY hσ hσ'

/-- Ricci depends on its first argument only through the value at `x`. -/
theorem ricci_congr_fst [ContMDiffCovariantDerivative cov 1]
    {X X' Y : Π y : M, TangentSpace I y} {x : M} (hY : CMDiff 2 (T% Y))
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hxx : X x = X' x) :
    cov.ricci X Y x = cov.ricci X' Y x :=
  (cov.tensorialAt_ricci_fst hY x).pointwise hX hX' hxx

/-- Ricci congruence in the second argument, relative to pointwise dependence of the
curvature's third slot (hypothesis `h3`, a theorem on the model space). -/
theorem ricci_congr_snd [ContMDiffCovariantDerivative cov 1]
    {X Y Y' : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hY' : CMDiff 2 (T% Y'))
    (h3 : ∀ W : Π y : M, TangentSpace I y, MDiffAt (T% W) x →
      cov.curvature W X Y x = cov.curvature W X Y' x) :
    cov.ricci X Y x = cov.ricci X Y' x := by
  rw [cov.ricci_eq_trace hY x, cov.ricci_eq_trace hY' x]
  congr 1
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend, ContinuousLinearMap.coe_coe]
  exact h3 (extend E v) (mdifferentiableAt_extend ..)

/-- Bilinear expansion of Ricci over a finite combination of `C²` fields in both
arguments: `Ric(Σⱼ rⱼcⱼ, Σₖ rₖcₖ) = Σⱼₖ rⱼrₖ Ric(cⱼ, cₖ)` at `x`. -/
theorem ricci_combination_expand [ContMDiffCovariantDerivative cov 1]
    {κ : Type*} [Fintype κ] {c : κ → Π y : M, TangentSpace I y} {x : M}
    (hc : ∀ j, CMDiff 2 (T% (c j))) (r : κ → ℝ) :
    cov.ricci (fun y ↦ ∑ j, (r j • c j) y) (fun y ↦ ∑ j, (r j • c j) y) x
      = ∑ j, ∑ k, (r j * r k) * cov.ricci (c j) (c k) x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hcomb : CMDiff 2 (T% (fun y ↦ ∑ j, (r j • c j) y)) :=
    ContMDiff.sum_section fun j _ ↦ (hc j).const_smul_section
  have hT := cov.tensorialAt_ricci_fst hcomb x
  rw [hT.sum (fun j ↦ r j • c j)
    (fun j _ ↦ ((hc j).const_smul_section.mdifferentiable h2) x)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hsm : cov.ricci (r j • c j) (fun y ↦ ∑ k, (r k • c k) y) x
      = r j * cov.ricci (c j) (fun y ↦ ∑ k, (r k • c k) y) x :=
    hT.smul (f := fun _ ↦ r j) mdifferentiableAt_const ((hc j).mdifferentiable h2 x)
  rw [hsm, cov.ricci_sum_right (fun k _ ↦ (hc k).const_smul_section)
    ((hc j).mdifferentiable h2 x), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [cov.ricci_smul_const_right (r k) (hc k) ((hc j).mdifferentiable h2 x)]
  ring

/-! ### Scalar curvature -/

section Metric

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **Ricci curvature as an orthonormal-frame sum** on a Riemannian manifold:
`Ric(X, Y)(x) = Σᵢ ⟪bᵢ, R(extend bᵢ, X) Y (x)⟫` for any orthonormal basis `b` of the
tangent space at `x`, where `extend` is the canonical local extension of a tangent
vector to a section. -/
-- BENCH: ricci-orthonormal-frame-sum
theorem ricci_eq_sum_inner_curvature [ContMDiffCovariantDerivative cov 1]
    {ι : Type*} [Fintype ι] {X Y : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.ricci X Y x = ∑ i, ⟪b i, cov.curvature (extend E (b i)) X Y x⟫ := by
  rw [cov.ricci_eq_trace hY x, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- The scalar curvature relative to a finite family of vector fields: the sum
`Σᵢ Ric(bᵢ, bᵢ)(x)`. When the values `bᵢ x` form an orthonormal basis of the tangent
space at `x` this is the metric trace of the Ricci curvature; frame-independence is
`scalarCurvatureWith_congr`. -/
noncomputable def scalarCurvatureWith {ι : Type*} [Fintype ι]
    (b : ι → Π y : M, TangentSpace I y) (x : M) : ℝ :=
  ∑ i, cov.ricci (b i) (b i) x

/-- **Frame-independence of the scalar curvature**: two `C²` families of fields whose
values at `x` are orthonormal bases of the tangent space give the same `Σᵢ Ric(bᵢ,bᵢ)`,
provided the third slot of the curvature is pointwise at `x` (hypothesis `h3`, a
theorem on the model space). -/
-- BENCH: scalar-frame-independent
theorem scalarCurvatureWith_congr [ContMDiffCovariantDerivative cov 1]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : ι → Π y : M, TangentSpace I y} {c : κ → Π y : M, TangentSpace I y} {x : M}
    (hb : ∀ i, CMDiff 2 (T% (b i))) (hc : ∀ j, CMDiff 2 (T% (c j)))
    (v : OrthonormalBasis ι ℝ (TangentSpace I x))
    (w : OrthonormalBasis κ ℝ (TangentSpace I x))
    (hbv : ∀ i, b i x = v i) (hcw : ∀ j, c j x = w j)
    (h3 : ∀ W X Y Y' : Π y : M, TangentSpace I y, MDiffAt (T% W) x →
      CMDiff 2 (T% X) → CMDiff 2 (T% Y) → CMDiff 2 (T% Y') → Y x = Y' x →
      cov.curvature W X Y x = cov.curvature W X Y' x) :
    cov.scalarCurvatureWith b x = cov.scalarCurvatureWith c x := by
  classical
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  -- the `κ`-combinations of the `c`-frame matching `b` at `x`
  have hcomb : ∀ i : ι, CMDiff 2 (T% (fun y ↦ ∑ j, (⟪w j, v i⟫ • c j) y)) :=
    fun i ↦ ContMDiff.sum_section fun j _ ↦ (hc j).const_smul_section
  have hBx : ∀ i, (fun y ↦ ∑ j, (⟪w j, v i⟫ • c j) y) x = b i x := by
    intro i
    rw [hbv i]
    show (∑ j, ⟪w j, v i⟫ • c j x : TangentSpace I x) = v i
    calc (∑ j, ⟪w j, v i⟫ • c j x : TangentSpace I x)
        = ∑ j, ⟪w j, v i⟫ • w j := Finset.sum_congr rfl fun j _ ↦ by rw [hcw j]
      _ = v i := w.sum_repr' (v i)
  -- expansion of each diagonal Ricci value over the `c`-frame
  have step : ∀ i, cov.ricci (b i) (b i) x
      = ∑ j, ∑ k, (⟪w j, v i⟫ * ⟪w k, v i⟫) * cov.ricci (c j) (c k) x := by
    intro i
    have hbix : MDiffAt (T% (b i)) x := (hb i).mdifferentiable h2 x
    have hBix : MDiffAt (T% (fun y ↦ ∑ j, (⟪w j, v i⟫ • c j) y)) x :=
      (hcomb i).mdifferentiable h2 x
    calc cov.ricci (b i) (b i) x
        = cov.ricci (fun y ↦ ∑ j, (⟪w j, v i⟫ • c j) y) (b i) x :=
          cov.ricci_congr_fst (hb i) hbix hBix (hBx i).symm
      _ = cov.ricci (fun y ↦ ∑ j, (⟪w j, v i⟫ • c j) y)
            (fun y ↦ ∑ j, (⟪w j, v i⟫ • c j) y) x :=
          cov.ricci_congr_snd (hb i) (hcomb i)
            (fun W hW ↦ h3 W _ (b i) _ hW (hcomb i) (hb i) (hcomb i) (hBx i).symm)
      _ = ∑ j, ∑ k, (⟪w j, v i⟫ * ⟪w k, v i⟫) * cov.ricci (c j) (c k) x :=
          cov.ricci_combination_expand hc (fun j ↦ ⟪w j, v i⟫)
  -- sum over `i`, swap the sums, and contract with Parseval
  calc cov.scalarCurvatureWith b x
      = ∑ i, ∑ j, ∑ k, (⟪w j, v i⟫ * ⟪w k, v i⟫) * cov.ricci (c j) (c k) x :=
        Finset.sum_congr rfl fun i _ ↦ step i
    _ = ∑ j, ∑ k, (∑ i, ⟪w j, v i⟫ * ⟪w k, v i⟫) * cov.ricci (c j) (c k) x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ (Finset.sum_mul ..).symm
    _ = ∑ j, ∑ k, ⟪w j, w k⟫ * cov.ricci (c j) (c k) x := by
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        congr 1
        calc ∑ i, ⟪w j, v i⟫ * ⟪w k, v i⟫
            = ∑ i, ⟪w j, v i⟫ * ⟪v i, w k⟫ :=
              Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm (w k) (v i)]
          _ = ⟪w j, w k⟫ := v.sum_inner_mul_inner _ _
    _ = ∑ j, cov.ricci (c j) (c j) x := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [orthonormal_iff_ite.mp w.orthonormal, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ = cov.scalarCurvatureWith c x := rfl

end Metric

end CovariantDerivative

/-! ### The model space -/

namespace CovariantDerivative
section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x)]

variable (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))

local instance (x : E) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace 𝓘(ℝ, E)) x

omit [RiemannianBundle fun x : E ↦ TangentSpace 𝓘(ℝ, E) x] in
/-- On the model space, the third slot of the curvature is pointwise for a merely
differentiable first slot: the strengthening of `curvature_third_slot_pointwise_model`
that discharges the hypothesis `h3` of `scalarCurvatureWith_congr`. -/
theorem curvature_congr_third_model [ContMDiffCovariantDerivative cov 1]
    {W X Y Y' : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hW : MDiffAt (T% W) x) (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hY' : CMDiff 2 (T% Y')) (hyy : Y x = Y' x) :
    cov.curvature W X Y x = cov.curvature W X Y' x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  calc cov.curvature W X Y x
      = cov.curvature (fun _ ↦ W x) X Y x :=
        (cov.tensorialAt_curvature_fst hY x).pointwise hW
          (((contMDiff_const_section rfl).mdifferentiable h2) x) rfl
    _ = cov.curvature (fun _ ↦ W x) X Y' x :=
        cov.curvature_third_slot_pointwise_model (contMDiff_const_section rfl) hX hY hY' hyy
    _ = cov.curvature W X Y' x :=
        ((cov.tensorialAt_curvature_fst hY' x).pointwise hW
          (((contMDiff_const_section rfl).mdifferentiable h2) x) rfl).symm

/-- **The scalar curvature on the model space**: the metric trace of the Ricci
curvature, `scal(x) = Σᵢ Ric(bᵢ, bᵢ)(x)` over (the constant extensions of) an
orthonormal basis of the tangent space at `x`. The definition uses the standard
orthonormal basis; `scalarCurvature_eq_sum` shows any `C²` frame with orthonormal
values at `x` gives the same value. -/
-- BENCH: scalar-def
noncomputable def scalarCurvature (x : E) : ℝ :=
  cov.scalarCurvatureWith
    (fun i _ ↦ stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x) i) x

/-- **Well-definedness of the scalar curvature on the model space**, hypothesis-free:
`scal(x)` is `Σᵢ Ric(bᵢ, bᵢ)(x)` for every `C²` family `b` of vector fields whose
values at `x` form an orthonormal basis of the tangent space. -/
-- BENCH: scalar-well-defined-model
theorem scalarCurvature_eq_sum [ContMDiffCovariantDerivative cov 1]
    {ι : Type*} [Fintype ι] {x : E}
    {b : ι → Π y : E, TangentSpace 𝓘(ℝ, E) y}
    (hb : ∀ i, CMDiff 2 (T% (b i)))
    (v : OrthonormalBasis ι ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hbv : ∀ i, b i x = v i) :
    cov.scalarCurvature x = ∑ i, cov.ricci (b i) (b i) x :=
  cov.scalarCurvatureWith_congr
    (fun _ ↦ contMDiff_const_section rfl) hb
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, E) x)) v
    (fun _ ↦ rfl) hbv
    (fun _ _ _ _ hW hX hY hY' hyy ↦
      cov.curvature_congr_third_model hW hX hY hY' hyy)

/-- Scalar curvature as a sum over the constant extensions of any orthonormal basis
of the tangent space. -/
theorem scalarCurvature_eq_sum_const [ContMDiffCovariantDerivative cov 1]
    {ι : Type*} [Fintype ι] {x : E}
    (v : OrthonormalBasis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    cov.scalarCurvature x = ∑ i, cov.ricci (fun _ ↦ v i) (fun _ ↦ v i) x :=
  cov.scalarCurvature_eq_sum (fun _ ↦ contMDiff_const_section rfl) v (fun _ ↦ rfl)

end ModelSpace
end CovariantDerivative
