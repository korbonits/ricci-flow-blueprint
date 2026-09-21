/-
**The induced connection on a Hom bundle**, and the endomorphism bundle of `TM`.

Every "tensor" in this development so far is either a pointwise construction (`ricciForm`,
`curvatureTensorAt`) or an operator on *fields* (`covBilin`, `covCurvature`, `covTwoTensor`).
None of them is a **section of a vector bundle**, and that is why the general-bundle layer —
`BundleHessian`, `BundleBochner`, `BundleNormalSection`, `BundleMaximumPrinciple` — has never
been instantiated at anything but the tangent bundle itself. A maximum principle for a tensor
needs a genuine bundle, with a connection on it.

Mathlib supplies the bundle: `ContMDiffVectorBundle.continuousLinearMap` makes
`fun x ↦ V₁ x →L[ℝ] V₂ x` a `C^n` vector bundle. What it does not supply is the induced
connection. That is this file:

  `(∇_X A)(σ) = ∇²_X(A σ) − A(∇¹_X σ)`,

with **two** terms, so — exactly as for `covOneForm`, and unlike `covCurvature`'s four —
*both* slots are free of any frame-and-globalise argument. The direction is a continuous
linear map by construction; the `σ` slot is the plain Leibniz cancellation, the two Leibniz
terms `(Xf)·A(σ)` coming from `∇²` and from `∇¹` being literally equal. So
`TensorialAt.mkHom₂` applies directly and `∇A` is a genuine element of the fibre
`T_xM →L[ℝ] (V₁ x →L[ℝ] V₂ x)` of `Hom(TM, Hom(V₁,V₂))`.

The headline instance is `End(TM) = Hom(TM,TM)`: in dimension three the Hamilton curvature
operator is `scal · Id − 2 Ric♯`, an endomorphism field, so the pinching argument needs no
`Λ²` at all.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Hessian
import Mathlib.Geometry.Manifold.VectorBundle.Hom

open Bundle Filter Module
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x : M, AddCommGroup (V₁ x)] [∀ x : M, Module ℝ (V₁ x)]
  [∀ x : M, TopologicalSpace (V₁ x)] [∀ x : M, IsTopologicalAddGroup (V₁ x)]
  [∀ x : M, ContinuousSMul ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x : M, AddCommGroup (V₂ x)] [∀ x : M, Module ℝ (V₂ x)]
  [∀ x : M, TopologicalSpace (V₂ x)] [∀ x : M, IsTopologicalAddGroup (V₂ x)]
  [∀ x : M, ContinuousSMul ℝ (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)

set_option maxSynthPendingDepth 3

/-- The **covariant derivative of a bundle morphism field**:
`(∇_X A)(σ) = ∇²_X(A σ) − A(∇¹_X σ)`. -/
noncomputable def covHom (A : Π y : M, V₁ y →L[ℝ] V₂ y)
    (X : Π y : M, TangentSpace I y) (σ : Π y : M, V₁ y) (x : M) : V₂ x :=
  cov₂ (fun y ↦ A y (σ y)) x (X x) - A x (cov₁ σ x (X x))

variable {cov₁ cov₂} {A : Π y : M, V₁ y →L[ℝ] V₂ y}
  {X X' : Π y : M, TangentSpace I y} {σ σ' : Π y : M, V₁ y} {f : M → ℝ} {x : M}

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- `∇A` is homogeneous in the direction, with no hypotheses: both terms are continuous linear
maps evaluated at `X x`. -/
theorem covHom_smul_dir : covHom cov₁ cov₂ A (f • X) σ x = f x • covHom cov₁ cov₂ A X σ x := by
  have hfx : (f • X) x = f x • X x := rfl
  have h1 : cov₂ (fun y ↦ A y (σ y)) x (f x • X x)
      = f x • cov₂ (fun y ↦ A y (σ y)) x (X x) := map_smul _ _ _
  have h2 : A x (cov₁ σ x (f x • X x)) = f x • A x (cov₁ σ x (X x)) := by
    rw [map_smul, map_smul]
  rw [covHom, covHom, hfx, h1, h2, smul_sub]

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- `∇A` is additive in the direction, with no hypotheses. -/
theorem covHom_add_dir :
    covHom cov₁ cov₂ A (X + X') σ x = covHom cov₁ cov₂ A X σ x + covHom cov₁ cov₂ A X' σ x := by
  have hfx : (X + X') x = X x + X' x := rfl
  have h1 : cov₂ (fun y ↦ A y (σ y)) x (X x + X' x)
      = cov₂ (fun y ↦ A y (σ y)) x (X x) + cov₂ (fun y ↦ A y (σ y)) x (X' x) := map_add _ _ _
  have h2 : A x (cov₁ σ x (X x + X' x))
      = A x (cov₁ σ x (X x)) + A x (cov₁ σ x (X' x)) := by
    rw [map_add, map_add]
  rw [covHom, covHom, covHom, hfx, h1, h2]
  abel

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- `∇A` at `x` depends on the direction only through `X x`. -/
theorem covHom_congr_dir (hXX' : X x = X' x) :
    covHom cov₁ cov₂ A X σ x = covHom cov₁ cov₂ A X' σ x := by
  simp only [covHom, hXX']

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- **The Leibniz cancellation.** `∇²_X(f·A σ)` produces `(Xf)·A(σ)` and `A(∇¹_X(f·σ))`
produces the same term, so the two cancel and only `MDifferentiableAt` of the data is used. -/
theorem covHom_smul_snd (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x)
    (hAσ : MDiffAt (T% fun y ↦ A y (σ y)) x) :
    covHom cov₁ cov₂ A X (f • σ) x = f x • covHom cov₁ cov₂ A X σ x := by
  have hprod : (fun y ↦ A y ((f • σ) y)) = f • (fun y ↦ A y (σ y)) := by
    funext y
    show A y (f y • σ y) = f y • A y (σ y)
    exact map_smul _ _ _
  have h1 : cov₂ (fun y ↦ A y ((f • σ) y)) x (X x)
      = f x • cov₂ (fun y ↦ A y (σ y)) x (X x) + (d% f x) (X x) • A x (σ x) := by
    rw [hprod, cov₂.isCovariantDerivativeOn.leibniz hAσ hf]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have h2 : A x (cov₁ (f • σ) x (X x))
      = f x • A x (cov₁ σ x (X x)) + (d% f x) (X x) • A x (σ x) := by
    rw [cov₁.isCovariantDerivativeOn.leibniz hσ hf]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  rw [covHom, covHom, h1, h2, smul_sub]
  abel

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- `∇A` is additive in the section slot. -/
theorem covHom_add_snd (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hAσ : MDiffAt (T% fun y ↦ A y (σ y)) x) (hAσ' : MDiffAt (T% fun y ↦ A y (σ' y)) x) :
    covHom cov₁ cov₂ A X (σ + σ') x
      = covHom cov₁ cov₂ A X σ x + covHom cov₁ cov₂ A X σ' x := by
  have hsum : (fun y ↦ A y ((σ + σ') y)) = (fun y ↦ A y (σ y)) + (fun y ↦ A y (σ' y)) := by
    funext y
    show A y (σ y + σ' y) = A y (σ y) + A y (σ' y)
    exact map_add _ _ _
  have h1 : cov₂ (fun y ↦ A y ((σ + σ') y)) x (X x)
      = cov₂ (fun y ↦ A y (σ y)) x (X x) + cov₂ (fun y ↦ A y (σ' y)) x (X x) := by
    rw [hsum, cov₂.isCovariantDerivativeOn.add hAσ hAσ']
    simp only [add_apply]
  have h2 : A x (cov₁ (σ + σ') x (X x))
      = A x (cov₁ σ x (X x)) + A x (cov₁ σ' x (X x)) := by
    rw [cov₁.isCovariantDerivativeOn.add hσ hσ']
    simp only [add_apply]
    exact map_add _ _ _
  rw [covHom, covHom, covHom, h1, h2]
  abel

variable (F₁ F₂) in
/-- **`A` is differentiable against differentiable sections at `x`** — what the slot laws of
`∇A` actually consume. Mirrors `IsMDiffOneFormAt` and `IsMDiffBilinAt`. -/
def IsMDiffHomAt (A : Π y : M, V₁ y →L[ℝ] V₂ y) (x : M) : Prop :=
  ∀ σ : Π y : M, V₁ y, MDiffAt (fun y ↦ TotalSpace.mk' F₁ (E := V₁) y (σ y)) x →
    MDiffAt (fun y ↦ TotalSpace.mk' F₂ (E := V₂) y (A y (σ y))) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] [FiniteDimensional ℝ F₁]
  [∀ x : M, IsTopologicalAddGroup (V₁ x)] [∀ x : M, ContinuousSMul ℝ (V₁ x)]
  [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- A differentiable **section of the Hom bundle** has that property: this is
`MDifferentiableAt.clm_bundle_apply`. It is the only place the Hom bundle's own smooth
structure is used, and it is what lets the connection below be a genuine
`CovariantDerivative` on that bundle rather than an operator on fields. -/
theorem isMDiffHomAt_of_section
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun z : M ↦ V₁ z →L[ℝ] V₂ z) y (A y)) x) :
    IsMDiffHomAt (I := I) F₁ F₂ A x :=
  fun _ hσ ↦ hA.clm_bundle_apply hσ

omit [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I] [VectorBundle ℝ F₂ V₂] in
theorem tensorialAt_covHom_dir (σ : Π y : M, V₁ y) (x : M) :
    TensorialAt I E (fun X ↦ covHom cov₁ cov₂ A X σ x) x where
  smul _ _ := covHom_smul_dir
  add _ _ := covHom_add_dir

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I] [VectorBundle ℝ F₂ V₂] in
theorem tensorialAt_covHom_snd (hA : IsMDiffHomAt (I := I) F₁ F₂ A x)
    (X : Π y : M, TangentSpace I y) :
    TensorialAt I F₁ (fun σ ↦ covHom cov₁ cov₂ A X σ x) x where
  smul hf hσ := covHom_smul_snd hf hσ (hA _ hσ)
  add hσ hσ' := covHom_add_snd hσ hσ' (hA _ hσ) (hA _ hσ')

/-- **`∇A` as an element of the fibre of `Hom(TM, Hom(V₁,V₂))` at `x`.** No frame argument is
needed anywhere: `∇A` has two terms, so both slots are `TensorialAt` on merely differentiable
sections. -/
noncomputable def covHomAt (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂) (A : Π y : M, V₁ y →L[ℝ] V₂ y) (x : M)
    (hA : IsMDiffHomAt (I := I) F₁ F₂ A x) :
    TangentSpace I x →L[ℝ] V₁ x →L[ℝ] V₂ x :=
  TensorialAt.mkHom₂ (fun X σ ↦ covHom cov₁ cov₂ A X σ x) x
    (fun σ _ ↦ tensorialAt_covHom_dir σ x)
    (fun X _ ↦ tensorialAt_covHom_snd hA X)

omit [CompleteSpace E] [VectorBundle ℝ F₂ V₂] in
theorem covHomAt_apply (hA : IsMDiffHomAt (I := I) F₁ F₂ A x) (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x) :
    covHomAt cov₁ cov₂ A x hA (X x) (σ x) = covHom cov₁ cov₂ A X σ x :=
  TensorialAt.mkHom₂_apply _ _ hX hσ

omit [CompleteSpace E] [VectorBundle ℝ F₂ V₂] in
/-- `∇A` evaluated at bare vectors, through the canonical extensions. -/
theorem covHomAt_apply_extend (hA : IsMDiffHomAt (I := I) F₁ F₂ A x)
    (v : TangentSpace I x) (w : V₁ x) :
    covHomAt cov₁ cov₂ A x hA v w
      = covHom cov₁ cov₂ A (FiberBundle.extend E v) (FiberBundle.extend F₁ w) x := by
  have h := covHomAt_apply (cov₁ := cov₁) (cov₂ := cov₂) hA
    (X := FiberBundle.extend E v) (σ := FiberBundle.extend F₁ w)
    (FiberBundle.mdifferentiableAt_extend ..) (FiberBundle.mdifferentiableAt_extend ..)
  simpa only [FiberBundle.extend_apply_self] using h

section Connection

variable {A' : Π y : M, V₁ y →L[ℝ] V₂ y} {g : M → ℝ}

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- `∇A` is additive in `A` — the axiom `add` of a covariant derivative on `Hom(V₁,V₂)`. -/
theorem covHom_add_hom (hA : IsMDiffHomAt (I := I) F₁ F₂ A x)
    (hA' : IsMDiffHomAt (I := I) F₁ F₂ A' x) (hσ : MDiffAt (T% σ) x) :
    covHom cov₁ cov₂ (A + A') X σ x
      = covHom cov₁ cov₂ A X σ x + covHom cov₁ cov₂ A' X σ x := by
  have hsum : (fun y ↦ (A + A') y (σ y)) = (fun y ↦ A y (σ y)) + (fun y ↦ A' y (σ y)) := by
    funext y
    show (A y + A' y) (σ y) = A y (σ y) + A' y (σ y)
    exact add_apply _ _ _
  have h1 : cov₂ (fun y ↦ (A + A') y (σ y)) x (X x)
      = cov₂ (fun y ↦ A y (σ y)) x (X x) + cov₂ (fun y ↦ A' y (σ y)) x (X x) := by
    rw [hsum, cov₂.isCovariantDerivativeOn.add (hA σ hσ) (hA' σ hσ)]
    simp only [add_apply]
  have h2 : (A + A') x (cov₁ σ x (X x))
      = A x (cov₁ σ x (X x)) + A' x (cov₁ σ x (X x)) := rfl
  rw [covHom, covHom, covHom, h1, h2]
  abel

omit [IsManifold I ω M] [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [VectorBundle ℝ F₁ V₁] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₁ V₁ I] in
/-- `∇(g·A) = g·∇A + dg ⊗ A` — the axiom `leibniz`. Note the correction is `dg ⊗ A`, not
`dg ⊗ (A σ)`: the derivative lands on `A` as a section of `Hom(V₁,V₂)`. -/
theorem covHom_smul_hom (hg : MDiffAt g x) (hA : IsMDiffHomAt (I := I) F₁ F₂ A x)
    (hσ : MDiffAt (T% σ) x) :
    covHom cov₁ cov₂ (g • A) X σ x
      = g x • covHom cov₁ cov₂ A X σ x + (d% g x) (X x) • A x (σ x) := by
  have hprod : (fun y ↦ (g • A) y (σ y)) = g • (fun y ↦ A y (σ y)) := by
    funext y
    show (g y • A y) (σ y) = g y • A y (σ y)
    exact smul_apply _ _ _
  have h1 : cov₂ (fun y ↦ (g • A) y (σ y)) x (X x)
      = g x • cov₂ (fun y ↦ A y (σ y)) x (X x) + (d% g x) (X x) • A x (σ x) := by
    rw [hprod, cov₂.isCovariantDerivativeOn.leibniz (hA σ hσ) hg]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have h2 : (g • A) x (cov₁ σ x (X x)) = g x • A x (cov₁ σ x (X x)) := rfl
  rw [covHom, covHom, h1, h2, smul_sub]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] [FiniteDimensional ℝ F₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I] [∀ x : M, IsTopologicalAddGroup (V₁ x)]
  [∀ x : M, ContinuousSMul ℝ (V₁ x)] [VectorBundle ℝ F₁ V₁]
  [∀ x : M, ContinuousSMul ℝ (V₂ x)] in
theorem IsMDiffHomAt.add (hA : IsMDiffHomAt (I := I) F₁ F₂ A x)
    (hA' : IsMDiffHomAt (I := I) F₁ F₂ A' x) :
    IsMDiffHomAt (I := I) F₁ F₂ (A + A') x :=
  fun σ hσ ↦ mdifferentiableAt_add_section (hA σ hσ) (hA' σ hσ)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] [FiniteDimensional ℝ F₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I] [∀ x : M, IsTopologicalAddGroup (V₁ x)]
  [∀ x : M, ContinuousSMul ℝ (V₁ x)] [VectorBundle ℝ F₁ V₁]
  [∀ x : M, IsTopologicalAddGroup (V₂ x)] in
theorem IsMDiffHomAt.smul (hg : MDiffAt g x) (hA : IsMDiffHomAt (I := I) F₁ F₂ A x) :
    IsMDiffHomAt (I := I) F₁ F₂ (g • A) x :=
  fun σ hσ ↦ hg.smul_section (hA σ hσ)

variable (cov₁ cov₂)

open scoped Classical in
/-- **The induced connection on the bundle `Hom(V₁,V₂)`.** This is the first covariant
derivative in this development on a bundle other than `TM` itself, and it is what the
general-bundle layer (`BundleHessian`, `BundleBochner`, `BundleNormalSection`,
`BundleMaximumPrinciple`) has been waiting for: those files all take
`cov : CovariantDerivative I F V` as a hypothesis and until now had nothing but the tangent
bundle to instantiate it at.

The junk branch is the usual one — a covariant derivative is a total function, while `∇A` is
only meaningful where `A` is a differentiable section, and every axiom of
`IsCovariantDerivativeOn` is guarded by exactly that hypothesis. -/
noncomputable def homCov :
    CovariantDerivative I (F₁ →L[ℝ] F₂) (fun y : M ↦ V₁ y →L[ℝ] V₂ y) where
  toFun A y := if h : IsMDiffHomAt (I := I) F₁ F₂ A y then covHomAt cov₁ cov₂ A y h else 0
  isCovariantDerivativeOnUniv := by
    constructor
    · intro A A' y hA hA' _
      have h1 := isMDiffHomAt_of_section hA
      have h2 := isMDiffHomAt_of_section hA'
      have h3 := h1.add h2
      simp only [h1, h2, h3, ↓reduceDIte]
      ext v w
      rw [covHomAt_apply_extend, add_apply, add_apply, covHomAt_apply_extend,
        covHomAt_apply_extend]
      exact covHom_add_hom h1 h2 (FiberBundle.mdifferentiableAt_extend ..)
    · intro A g y hA hg _
      have h1 := isMDiffHomAt_of_section hA
      have h3 := h1.smul hg
      simp only [h1, h3, ↓reduceDIte]
      ext v w
      have hL := covHomAt_apply_extend (cov₁ := cov₁) (cov₂ := cov₂) h3 v w
      have hR := covHomAt_apply_extend (cov₁ := cov₁) (cov₂ := cov₂) h1 v w
      have key := covHom_smul_hom (cov₁ := cov₁) (cov₂ := cov₂) (X := FiberBundle.extend E v)
        (σ := FiberBundle.extend F₁ w) hg h1 (FiberBundle.mdifferentiableAt_extend ..)
      simp only [FiberBundle.extend_apply_self] at key
      rw [hL, key, ← hR]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

variable {cov₁ cov₂}

omit [CompleteSpace E] in
/-- **`homCov` computes `∇A` by the formula** on differentiable data — the only thing a
covariant derivative built through a junk branch has to be checked to do. -/
theorem homCov_apply (hA : IsMDiffHomAt (I := I) F₁ F₂ A x) (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x) :
    homCov cov₁ cov₂ A x (X x) (σ x) = covHom cov₁ cov₂ A X σ x := by
  classical
  show (if h : IsMDiffHomAt (I := I) F₁ F₂ A x then covHomAt cov₁ cov₂ A x h else 0)
      (X x) (σ x) = _
  simp only [hA, ↓reduceDIte]
  exact covHomAt_apply hA hX hσ

end Connection

section Endomorphism

variable [ContMDiffVectorBundle 1 E (fun (y : M) ↦ TangentSpace I y) I]

/-- **The induced connection on `End(TM) = Hom(TM, TM)`.**

In dimension three the Hamilton curvature operator is `scal · Id − 2 Ric♯` — the Weyl tensor
vanishes, so the whole `(0,4)` tensor is carried by an *endomorphism* field. That is why the
three-dimensional pinching argument needs no `Λ²` and runs on this bundle.

This instantiation is also the falsification check on everything above: `homCov` is stated for
two arbitrary bundles, and a general construction with no instantiations is unverified. -/
noncomputable def endCov (cov : CovariantDerivative I E (fun y : M ↦ TangentSpace I y)) :
    CovariantDerivative I (E →L[ℝ] E) (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) :=
  homCov cov cov

omit [CompleteSpace E] in
/-- **`∇A` for an endomorphism field is `∇(A W) − A(∇W)`**, on differentiable data. -/
theorem endCov_apply {cov : CovariantDerivative I E (fun y : M ↦ TangentSpace I y)}
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {X W : Π y : M, TangentSpace I y} {x : M}
    (hA : IsMDiffHomAt (I := I) E E A x) (hX : MDiffAt (T% X) x) (hW : MDiffAt (T% W) x) :
    endCov cov A x (X x) (W x) = cov (fun y ↦ A y (W y)) x (X x) - A x (cov W x (X x)) :=
  homCov_apply hA hX hW

end Endomorphism

end CovariantDerivative
