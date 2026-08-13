/-
Ricci curvature: the trace contraction of the curvature tensor.

`Ric(X, Y) = tr (W ↦ R(W, X) Y)`. The trace only makes sense once the curvature
operator descends from vector fields to tangent vectors in its first slot; that
is `CovariantDerivative.tensorialAt_curvature_fst` (`RicciFlowBlueprint.Curvature`),
which packages `curvature_smul_left` and `curvature_add_left` as a `TensorialAt`
and hands the pointwise endomorphism to `TensorialAt.mkHom`. No `mkHom₃` (nor
full three-slot tensoriality) is needed for the definition: the middle and third
slots may stay vector fields, since the trace is taken in the first slot only.

Main results:

* `ricci` — the definition, as the trace of the pointwise curvature endomorphism
  `W x ↦ R(W, X) Y x`; `ricci_eq_trace` unfolds it once `Y` is `C²` and `∇` is `C¹`.
* `ricci_add_left`, `ricci_smul_left` — Ricci is itself `C^∞(M)`-tensorial in `X`.
* `ricci_sub_ricci_swap` — the trace of the first Bianchi identity: for a
  torsion-free connection the antisymmetric part of Ricci is minus the trace of
  the endomorphism `v ↦ R(X, Y) v`. (Ricci of a torsion-free connection is NOT
  symmetric in general; symmetry is exactly the vanishing of that trace, which
  for metric connections follows from skew-symmetry of `R(X, Y)`.) The third
  slot of the curvature is not known to be pointwise on a general manifold —
  that would need either global `C²` extensions of tangent vectors (bump
  functions) or a `C²`-graded tensoriality machinery, since `TensorialAt`'s
  `MDiffAt`-class hypotheses are too weak for a slot in which the connection
  differentiates — so the endomorphism is taken as a hypothesis (`hL`), together
  with pointwise surjectivity of evaluation of global `C²` fields (`hsur`).
* `ricci_symm_of_traceless` — under the same hypotheses, Ricci is symmetric at
  `x` when that trace vanishes.
* On the model space `M = E` both hypotheses are theorems: constant sections are
  global smooth fields (`exists_global_section_model`), and the third slot IS
  pointwise (`curvature_third_slot_pointwise_model`, by decomposing over the
  global constant frame of a basis — `curvature_decompose_model`), so the
  curvature endomorphism `curvatureEndoModel` exists unconditionally and
  `ricci_sub_ricci_swap_model` is hypothesis-free.
-/
import RicciFlowBlueprint.Curvature
import Mathlib.LinearAlgebra.Trace

open Bundle VectorField FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

open scoped Classical in
-- BENCH: ricci-def
/-- The Ricci curvature of a covariant derivative on the tangent bundle:
`Ric(X, Y) = tr (W ↦ R(W, X) Y)`, the trace of the pointwise endomorphism of
`TangentSpace I x` obtained from the first slot of the curvature operator via the
tensoriality criterion. Junk value `0` when the first slot is not tensorial at `x`
(it is tensorial whenever `cov` is `C¹` and `Y` is `C²`, by
`tensorialAt_curvature_fst`). -/
noncomputable def ricci (X Y : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  if h : TensorialAt I E (fun W ↦ cov.curvature W X Y x) x then
    LinearMap.trace ℝ (TangentSpace I x) (TensorialAt.mkHom _ x h).toLinearMap
  else 0

/-- For a `C¹` connection and `C²` field `Y`, the Ricci curvature is the trace of the
pointwise curvature endomorphism produced by `TensorialAt.mkHom`. -/
theorem ricci_eq_trace [ContMDiffCovariantDerivative cov 1]
    {X Y : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y)) (x : M) :
    cov.ricci X Y x = LinearMap.trace ℝ (TangentSpace I x)
      (TensorialAt.mkHom (fun W ↦ cov.curvature W X Y x) x
        (cov.tensorialAt_curvature_fst hY x)).toLinearMap := by
  have h := cov.tensorialAt_curvature_fst (V := X) hY x
  simp only [ricci, h, reduceDIte]

/-- The pointwise curvature endomorphism traced by `ricci` agrees with the curvature
operator on values of sections differentiable at `x`. -/
theorem mkHom_curvature_fst_apply [ContMDiffCovariantDerivative cov 1]
    {X Y W : Π y : M, TangentSpace I y} (hY : CMDiff 2 (T% Y)) {x : M}
    (hW : MDiffAt (T% W) x) :
    TensorialAt.mkHom (fun W ↦ cov.curvature W X Y x) x
      (cov.tensorialAt_curvature_fst hY x) (W x)
      = cov.curvature W X Y x :=
  TensorialAt.mkHom_apply _ hW

/-- Ricci curvature is additive in its first argument. -/
theorem ricci_add_left [ContMDiffCovariantDerivative cov 1]
    {X X' Y : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) :
    cov.ricci (X + X') Y x = cov.ricci X Y x + cov.ricci X' Y x := by
  rw [cov.ricci_eq_trace hY x, cov.ricci_eq_trace hY x, cov.ricci_eq_trace hY x]
  rw [← map_add]
  congr 1
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend, LinearMap.add_apply,
    ContinuousLinearMap.coe_coe]
  exact cov.curvature_add_middle hY hX hX'

/-- Ricci curvature is `C^∞(M)`-homogeneous in its first argument: together with
`ricci_add_left`, Ricci is itself tensorial in `X`. -/
theorem ricci_smul_left [ContMDiffCovariantDerivative cov 1]
    {f : M → ℝ} {X Y : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) :
    cov.ricci (f • X) Y x = f x * cov.ricci X Y x := by
  rw [cov.ricci_eq_trace hY x, cov.ricci_eq_trace hY x]
  rw [show f x * _ = f x • LinearMap.trace ℝ (TangentSpace I x)
    (TensorialAt.mkHom (fun W ↦ cov.curvature W X Y x) x
      (cov.tensorialAt_curvature_fst hY x)).toLinearMap from rfl, ← map_smul]
  congr 1
  ext v
  simp only [TensorialAt.mkHom_apply_eq_extend, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe]
  exact cov.curvature_smul_middle f (extend E v) X Y hf hX (cov.mdiffAt_cov_apply hY hX)

-- BENCH: ricci-antisym-trace
/-- The trace of the first Bianchi identity: for a torsion-free `C¹` connection,
`Ric(X, Y) - Ric(Y, X) = -tr (v ↦ R(X, Y) v)`.

The endomorphism `v ↦ R(X, Y) v` (third slot of the curvature, pointwise) is supplied
as a hypothesis `L`/`hL`, because on a general manifold the third slot is not known to
descend to tangent vectors; `hsur` asks that every tangent vector at `x` extend to a
global `C²` field. Both hypotheses are theorems on the model space — see
`ricci_sub_ricci_swap_model`. In particular Ricci of a torsion-free connection is
symmetric at `x` iff `tr L = 0` (`ricci_symm_of_traceless`); for a general torsion-free
connection this trace need not vanish, so torsion-freeness alone does NOT make Ricci
symmetric. -/
theorem ricci_sub_ricci_swap [ContMDiffCovariantDerivative cov 1] (hcov : cov.torsion = 0)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hsur : ∀ v : TangentSpace I x, ∃ W : Π y : M, TangentSpace I y,
      CMDiff 2 (T% W) ∧ W x = v)
    {L : TangentSpace I x →ₗ[ℝ] TangentSpace I x}
    (hL : ∀ W : Π y : M, TangentSpace I y, CMDiff 2 (T% W) →
      L (W x) = cov.curvature X Y W x) :
    cov.ricci X Y x - cov.ricci Y X x = - LinearMap.trace ℝ (TangentSpace I x) L := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  set A := (TensorialAt.mkHom (fun W ↦ cov.curvature W X Y x) x
    (cov.tensorialAt_curvature_fst hY x)).toLinearMap with hA
  set C := (TensorialAt.mkHom (fun W ↦ cov.curvature W Y X x) x
    (cov.tensorialAt_curvature_fst hX x)).toLinearMap with hC
  -- The linear-map identity underlying the trace identity: `A - C + L = 0`,
  -- which is the first Bianchi identity tested against global `C²` fields.
  have key : A - C + L = 0 := by
    ext v
    obtain ⟨W, hW, rfl⟩ := hsur v
    have hWx : MDiffAt (T% W) x := (hW.mdifferentiable h2) x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply, hA, hC,
      ContinuousLinearMap.coe_coe]
    rw [cov.mkHom_curvature_fst_apply hY hWx, cov.mkHom_curvature_fst_apply hX hWx, hL W hW]
    have hb := cov.bianchi_first (x := x) hcov hW hX hY
    have ha : cov.curvature Y W X x = - cov.curvature W Y X x := cov.curvature_antisymm ..
    linear_combination (norm := module) hb - ha
  have htr : LinearMap.trace ℝ (TangentSpace I x) A - LinearMap.trace ℝ (TangentSpace I x) C
      + LinearMap.trace ℝ (TangentSpace I x) L = 0 := by
    have := congrArg (LinearMap.trace ℝ (TangentSpace I x)) key
    simpa [map_sub, map_add] using this
  rw [cov.ricci_eq_trace hY x, cov.ricci_eq_trace hX x]
  rw [← hA, ← hC]
  linarith

/-- Ricci curvature of a torsion-free connection is symmetric at `x` when the curvature
endomorphism `v ↦ R(X, Y) v` is traceless there (as it is for metric connections). -/
theorem ricci_symm_of_traceless [ContMDiffCovariantDerivative cov 1] (hcov : cov.torsion = 0)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hsur : ∀ v : TangentSpace I x, ∃ W : Π y : M, TangentSpace I y,
      CMDiff 2 (T% W) ∧ W x = v)
    {L : TangentSpace I x →ₗ[ℝ] TangentSpace I x}
    (hL : ∀ W : Π y : M, TangentSpace I y, CMDiff 2 (T% W) →
      L (W x) = cov.curvature X Y W x)
    (hL0 : LinearMap.trace ℝ (TangentSpace I x) L = 0) :
    cov.ricci X Y x = cov.ricci Y X x := by
  have := cov.ricci_sub_ricci_swap hcov hX hY hsur hL
  rw [hL0] at this
  linarith

end CovariantDerivative

/-! ### The model space

On `M = E` every tangent vector extends to a *global* smooth (constant) field, and the
tangent bundle has a global constant frame. This discharges both hypotheses of
`ricci_sub_ricci_swap`: the third slot of the curvature becomes genuinely pointwise
(`curvature_third_slot_pointwise_model`), the curvature endomorphism `v ↦ R(X, Y) v`
exists as an honest linear map (`curvatureEndoModel`), and the trace of the first
Bianchi identity holds unconditionally (`ricci_sub_ricci_swap_model`).
-/

namespace CovariantDerivative

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Constant sections of the tangent bundle of the model space are smooth. -/
lemma contMDiff_const_section {W : Π y : E, TangentSpace 𝓘(ℝ, E) y} {v : E}
    (hW : W = fun _ ↦ v) {n : ℕ∞ω} : CMDiff n (T% W) := by
  subst hW
  exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

/-- On the model space, every tangent vector is the value of a global smooth field. -/
lemma exists_global_section_model (x : E) (v : TangentSpace 𝓘(ℝ, E) x) :
    ∃ W : Π y : E, TangentSpace 𝓘(ℝ, E) y, CMDiff 2 (T% W) ∧ W x = v :=
  ⟨fun _ ↦ v, contMDiff_const_section rfl, rfl⟩

variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable (cov : CovariantDerivative 𝓘(ℝ, E) E (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x))

/-- On the model space, the curvature applied in the third slot to a `C²` field
decomposes over the constant frame of a basis:
`R(X,Y)W x = ∑ i, (W x)ᵢ • R(X,Y)(bᵢ) x`. In particular the third slot depends on `W`
only through `W x`. -/
theorem curvature_decompose_model [ContMDiffCovariantDerivative cov 1]
    {X Y W : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hW : CMDiff 2 (T% W)) :
    cov.curvature X Y W x
      = ∑ i, (Module.finBasis ℝ E).repr (W x) i •
          cov.curvature X Y (fun _ ↦ ((Module.finBasis ℝ E) i : E)) x := by
  classical
  set b := Module.finBasis ℝ E with hb
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hXx : MDiffAt (T% X) x := (hX.mdifferentiable h2) x
  have hYx : MDiffAt (T% Y) x := (hY.mdifferentiable h2) x
  have hWcd : ContDiff ℝ 2 W := contMDiff_vectorSpace_iff_contDiff.mp hW
  have hXcd : ContDiff ℝ 2 X := contMDiff_vectorSpace_iff_contDiff.mp hX
  have hYcd : ContDiff ℝ 2 Y := contMDiff_vectorSpace_iff_contDiff.mp hY
  -- the coefficient functions of `W` in the frame, as continuous linear maps applied to `W`
  set ℓ : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i) with hℓ
  have hc : ∀ i, ContDiff ℝ 2 (fun y ↦ ℓ i (W y)) := fun i ↦ (ℓ i).contDiff.comp hWcd
  -- the decomposition of `W` into coefficient functions times constant frame fields
  have hdec : W = fun y ↦ ∑ i,
      ((fun z ↦ ℓ i (W z)) • ((fun _ ↦ (b i : E)) : Π y : E, TangentSpace 𝓘(ℝ, E) y)) y := by
    funext y
    have := b.sum_repr (W y)
    simp only [Pi.smul_apply', hℓ, LinearMap.coe_toContinuousLinearMap']
    exact this.symm
  -- differentiability of the coefficient-derivative pairings
  have hdf : ∀ (i : Fin (Module.finrank ℝ E)) (V : Π y : E, TangentSpace 𝓘(ℝ, E) y),
      ContDiff ℝ 2 V →
      MDiffAt (fun y ↦ d% (fun z ↦ ℓ i (W z)) y (V y)) x := by
    intro i V hV
    have heq : (fun y ↦ d% (fun z ↦ ℓ i (W z)) y (V y))
        = fun y ↦ fderiv ℝ (fun z ↦ ℓ i (W z)) y (V y) := by
      funext y; rw [mvfderiv_eq_fderiv]; rfl
    rw [heq]
    apply mdifferentiableAt_iff_differentiableAt.mpr
    exact (((hc i).fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero).differentiableAt.clm_apply
      ((hV.differentiable (by norm_num)).differentiableAt)
  refine (congrArg (fun s ↦ cov.curvature X Y s x) hdec).trans ?_
  refine (cov.curvature_sum_right (s := Finset.univ)
    (Z := fun i ↦ (fun z ↦ ℓ i (W z)) • ((fun _ ↦ (b i : E)) : Π y : E, TangentSpace 𝓘(ℝ, E) y))
    (fun i _ ↦ contMDiff_vectorSpace_iff_contDiff.mpr
      (by exact (((ℓ i).contDiff.comp hWcd).smul contDiff_const))) hXx hYx).trans ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsm := cov.curvature_smul_right (fun z ↦ ℓ i (W z)) X Y (fun _ ↦ (b i : E))
    ((contMDiff_iff_contDiff.mpr (hc i)).mdifferentiable h2)
    (contMDiff_iff_contDiff.mpr (hc i)).contMDiffAt
    hXx hYx
    ((contMDiff_const_section rfl).mdifferentiable h2)
    (cov.mdiffAt_cov_apply (contMDiff_const_section rfl) hYx)
    (cov.mdiffAt_cov_apply (contMDiff_const_section rfl) hXx)
    (hdf i Y hYcd) (hdf i X hXcd)
    (((contMDiff_iff_contDiff.mpr (hc i)).mdifferentiable h2 x).smul_section
      (cov.mdiffAt_cov_apply (contMDiff_const_section rfl) hYx))
    (((contMDiff_iff_contDiff.mpr (hc i)).mdifferentiable h2 x).smul_section
      (cov.mdiffAt_cov_apply (contMDiff_const_section rfl) hXx))
    ((hdf i Y hYcd).smul_section (((contMDiff_const_section rfl).mdifferentiable h2) x))
    ((hdf i X hXcd).smul_section (((contMDiff_const_section rfl).mdifferentiable h2) x))
  refine hsm.trans ?_
  congr 1

-- BENCH: curvature-third-slot-pointwise-model
/-- On the model space, the third slot of the curvature operator is pointwise on `C²`
fields: `R(X,Y)Z x` depends on `Z` only through `Z x`. (This is the fact that is out of
reach of `TensorialAt` on a general manifold, since the connection differentiates its
third slot and `TensorialAt`'s hypothesis class is only `MDiffAt`.) -/
theorem curvature_third_slot_pointwise_model [ContMDiffCovariantDerivative cov 1]
    {X Y Z Z' : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hZ : CMDiff 2 (T% Z)) (hZ' : CMDiff 2 (T% Z')) (hzz : Z x = Z' x) :
    cov.curvature X Y Z x = cov.curvature X Y Z' x := by
  rw [cov.curvature_decompose_model hX hY hZ, cov.curvature_decompose_model hX hY hZ', hzz]

open scoped Classical in
/-- The curvature endomorphism `v ↦ R(X, Y) v` of a tangent space of the model space,
via constant extension in the third slot. Junk value `0` if `X` or `Y` is not `C²`. -/
noncomputable def curvatureEndoModel (X Y : Π y : E, TangentSpace 𝓘(ℝ, E) y) (x : E)
    [ContMDiffCovariantDerivative cov 1] :
    TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  if h : CMDiff 2 (T% X) ∧ CMDiff 2 (T% Y) then
    { toFun := fun v ↦ cov.curvature X Y (fun _ ↦ v) x
      map_add' := fun v w ↦ by
        have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
        exact cov.curvature_add_right (contMDiff_const_section rfl)
          (contMDiff_const_section rfl) ((h.1.mdifferentiable h2) x) ((h.2.mdifferentiable h2) x)
      map_smul' := fun c v ↦ by
        have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
        exact cov.curvature_smul_const_right c (contMDiff_const_section rfl)
          ((h.1.mdifferentiable h2) x) ((h.2.mdifferentiable h2) x) }
  else 0

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma curvatureEndoModel_apply [ContMDiffCovariantDerivative cov 1]
    {X Y : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (v : TangentSpace 𝓘(ℝ, E) x) :
    curvatureEndoModel cov X Y x v = cov.curvature X Y (fun _ ↦ v) x := by
  simp only [curvatureEndoModel, hX, hY, and_self, reduceDIte]
  rfl

/-- The curvature endomorphism agrees with the curvature operator on values of `C²`
fields: `R(X, Y) (W x) = (R(X, Y) W) x` on the model space. -/
lemma curvatureEndoModel_apply_section [ContMDiffCovariantDerivative cov 1]
    {X Y W : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hW : CMDiff 2 (T% W)) :
    curvatureEndoModel cov X Y x (W x) = cov.curvature X Y W x := by
  rw [curvatureEndoModel_apply cov hX hY]
  exact cov.curvature_third_slot_pointwise_model hX hY (contMDiff_const_section rfl) hW rfl

-- BENCH: ricci-antisym-trace-model
/-- The trace of the first Bianchi identity on the model space, hypothesis-free:
for a torsion-free `C¹` connection on the tangent bundle of `E` and `C²` fields
`X`, `Y`, the antisymmetric part of Ricci is minus the trace of the curvature
endomorphism: `Ric(X, Y) - Ric(Y, X) = -tr (v ↦ R(X, Y) v)`. -/
theorem ricci_sub_ricci_swap_model [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.torsion = 0)
    {X Y : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) :
    cov.ricci X Y x - cov.ricci Y X x
      = - LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, E) x) (curvatureEndoModel cov X Y x) :=
  cov.ricci_sub_ricci_swap hcov hX hY (exists_global_section_model x)
    (fun _ hW ↦ curvatureEndoModel_apply_section cov hX hY hW)

/-- On the model space, Ricci curvature of a torsion-free connection is symmetric at
points where the curvature endomorphism is traceless. -/
theorem ricci_symm_of_traceless_model [ContMDiffCovariantDerivative cov 1]
    (hcov : cov.torsion = 0)
    {X Y : Π y : E, TangentSpace 𝓘(ℝ, E) y} {x : E}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hL0 : LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, E) x) (curvatureEndoModel cov X Y x) = 0) :
    cov.ricci X Y x = cov.ricci Y X x := by
  have := cov.ricci_sub_ricci_swap_model (x := x) hcov hX hY
  rw [hL0] at this
  linarith

end ModelSpace

end CovariantDerivative
