/-
**The Hessian and the rough Laplacian of a section of a general vector bundle.**

`Hessian.lean` builds `∇²` and `Δ` for a *vector field*, i.e. a section of `TM`. Hamilton's
pinching estimate needs them for a section of `Sym²(Λ²TM)`, so the tangent bundle is the
wrong level of generality: a maximum principle for the curvature operator cannot quantify
over a constant direction vector, and the object it differentiates is not a vector field.

Two connections appear, and they are genuinely different: `cov` on `V`, which is what is
being differentiated, and `covT` on `TM`, which supplies the correction `−∇_{∇_XY}σ`. For
`V = TM` and `cov = covT` every definition here **is** its `Hessian.lean` counterpart, by
`rfl` (`hessianSection_eq_hessian`, `hessianSectionAt_eq_hessianAt`,
`laplacianSection_eq_laplacian`).

**Nothing here asks `V` for a norm, and that is what makes the bridge possible.** The
fibres carry mathlib's standard general-bundle binders — `AddCommGroup`, `Module`,
`TopologicalSpace` and the two continuity classes — and no more. A fibre *norm* would
break the specialisation outright, and not for a plumbing reason: `TangentSpace I x`
reduces to `E`, so `E`'s own norm typechecks as a fibre norm while instance search finds
the Riemannian metric's, and the two are genuinely different norms on the same type
(lean4#14949; mathlib's scoped priority-80 `RiemannianBundle` instances exist precisely to
keep them apart). Dropping the norm removes the choice rather than resolving it.

The trace defining `Δ` survives the loss because
`OrthonormalBasis.sum_apply_self_eq` needs nothing metric in its *codomain* — it is an
algebraic rearrangement of a finite sum, with no estimate anywhere. The inner product used
is `T_xM`'s, in the slot being traced, and that one is unambiguous.

-/
import RicciFlowBlueprint.Hessian

open Bundle Filter Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : CovariantDerivative I F V)
  (covT : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇_Y σ` is differentiable at `x` when `∇` is `C¹`, `σ` is `C²` and `Y` is differentiable.
The general-bundle form of `mdiffAt_cov_apply`: `y ↦ cov σ y` is a section of `Hom(TM, V)`,
which is exactly what `ContMDiffCovariantDerivative` asserts to be `C¹`. -/
lemma mdiffAt_cov_apply_section [ContMDiffCovariantDerivative cov 1]
    {σ : Π y : M, V y} {Y : Π y : M, TangentSpace I y} {x : M}
    (hσ : CMDiff 2 (T% σ)) (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (fun y ↦ cov σ y (Y y))) x := by
  have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun y : M ↦ (⟨y, cov σ y⟩ :
        TotalSpace (E →L[ℝ] F) fun y ↦ (TangentSpace I y →L[ℝ] V y))) Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 1)).contMDiff
      (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hσ.contMDiffOn)
  have h1 : MDiffAt (fun y : M ↦ (TotalSpace.mk' (E →L[ℝ] F)
      (E := fun y : M ↦ (TangentSpace I y →L[ℝ] V y)) y (cov σ y))) x := by
    have h := hcovσ x (Set.mem_univ x)
    rw [contMDiffWithinAt_univ] at h
    exact h.mdifferentiableAt one_ne_zero
  exact h1.clm_bundle_apply hY

/-- The **second covariant derivative of a section of `V`**:
`∇²_{X,Y}σ = ∇_X(∇_Yσ) − ∇_{∇_XY}σ`, with `∇_XY` taken in the tangent connection `covT`. -/
noncomputable def hessianSection (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    V x :=
  cov (fun y ↦ cov σ y (Y y)) x (X x) - cov σ x (covT Y x (X x))

section Tensorial

omit [CompleteSpace E] [FiniteDimensional ℝ E] [VectorBundle ℝ F V] in
/-- `∇²_{X,Y}σ` is pointwise linear in `X`. -/
theorem hessianSection_smul_left {f : M → ℝ} {X Y : Π y : M, TangentSpace I y}
    {σ : Π y : M, V y} {x : M} :
    cov.hessianSection covT (f • X) Y σ x = f x • cov.hessianSection covT X Y σ x := by
  simp [hessianSection, smul_sub]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [VectorBundle ℝ F V] in
theorem hessianSection_add_left {X X' Y : Π y : M, TangentSpace I y}
    {σ : Π y : M, V y} {x : M} :
    cov.hessianSection covT (X + X') Y σ x
      = cov.hessianSection covT X Y σ x + cov.hessianSection covT X' Y σ x := by
  simp only [hessianSection, Pi.add_apply, map_add]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇²_{X,Y}σ` is tensorial in `Y`: the `X(f)` terms of the two Leibniz rules cancel between
`∇_X(f ∇_Yσ)` and `∇_{∇_X(fY)}σ`. -/
theorem hessianSection_smul_right [ContMDiffCovariantDerivative cov 1] {f : M → ℝ}
    {X Y : Π y : M, TangentSpace I y} {σ : Π y : M, V y} {x : M}
    (hσ : CMDiff 2 (T% σ)) (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) :
    cov.hessianSection covT X (f • Y) σ x = f x • cov.hessianSection covT X Y σ x := by
  have hsec : (fun y ↦ cov σ y ((f • Y) y)) = f • (fun y ↦ cov σ y (Y y)) := by
    funext y
    simp
  simp only [hessianSection]
  rw [hsec, cov.isCovariantDerivativeOn.leibniz (cov.mdiffAt_cov_apply_section hσ hY) hf,
    covT.isCovariantDerivativeOn.leibniz hY hf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem hessianSection_add_right [ContMDiffCovariantDerivative cov 1]
    {X Y Y' : Π y : M, TangentSpace I y} {σ : Π y : M, V y} {x : M}
    (hσ : CMDiff 2 (T% σ)) (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    cov.hessianSection covT X (Y + Y') σ x
      = cov.hessianSection covT X Y σ x + cov.hessianSection covT X Y' σ x := by
  have hsec : (fun y ↦ cov σ y ((Y + Y') y)) =
      (fun y ↦ cov σ y (Y y)) + (fun y ↦ cov σ y (Y' y)) := by
    funext y
    simp
  simp only [hessianSection]
  rw [hsec, cov.isCovariantDerivativeOn.add (cov.mdiffAt_cov_apply_section hσ hY)
    (cov.mdiffAt_cov_apply_section hσ hY'), covT.isCovariantDerivativeOn.add hY hY']
  simp only [add_apply, map_add]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [VectorBundle ℝ F V] in
theorem tensorialAt_hessianSection_fst (Y : Π y : M, TangentSpace I y) (σ : Π y : M, V y)
    (x : M) :
    TensorialAt I E (fun X ↦ cov.hessianSection covT X Y σ x) x where
  smul _ _ := cov.hessianSection_smul_left covT
  add _ _ := cov.hessianSection_add_left covT

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem tensorialAt_hessianSection_snd [ContMDiffCovariantDerivative cov 1]
    {σ : Π y : M, V y} (hσ : CMDiff 2 (T% σ)) (X : Π y : M, TangentSpace I y) (x : M) :
    TensorialAt I E (fun Y ↦ cov.hessianSection covT X Y σ x) x where
  smul hf hY := cov.hessianSection_smul_right covT hσ hf hY
  add hY hY' := cov.hessianSection_add_right covT hσ hY hY'

/-- The Hessian of a `C²` section at `x`, as a bilinear map `T_xM → T_xM → V x`. -/
noncomputable def hessianSectionAt [ContMDiffCovariantDerivative cov 1] {σ : Π y : M, V y}
    (hσ : CMDiff 2 (T% σ)) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  TensorialAt.mkHom₂ (fun X Y ↦ cov.hessianSection covT X Y σ x) x
    (fun Y _ ↦ cov.tensorialAt_hessianSection_fst covT Y σ x)
    (fun X _ ↦ cov.tensorialAt_hessianSection_snd covT hσ X x)

omit [CompleteSpace E] in
theorem hessianSectionAt_apply [ContMDiffCovariantDerivative cov 1] {σ : Π y : M, V y}
    (hσ : CMDiff 2 (T% σ)) {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.hessianSectionAt covT hσ x (X x) (Y x) = cov.hessianSection covT X Y σ x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

end Tensorial

section Laplacian

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov 1]

/-- The **rough Laplacian of a section of `V`**: the metric trace of its Hessian,
`Δσ = ∑ᵢ ∇²_{eᵢ,eᵢ}σ` over an orthonormal basis of `T_xM`. -/
noncomputable def laplacianSection {σ : Π y : M, V y} (hσ : CMDiff 2 (T% σ)) (x : M) : V x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.hessianSectionAt covT hσ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

omit [CompleteSpace E] in
/-- The Laplacian is the trace of the Hessian over **any** orthonormal basis of `T_xM`. The
target `V x` needs only a norm: `OrthonormalBasis.sum_apply_self_eq` traces a bilinear map
into an arbitrary normed space. -/
theorem laplacianSection_eq_sum {σ : Π y : M, V y} (hσ : CMDiff 2 (T% σ)) {x : M}
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.laplacianSection covT hσ x = ∑ i, cov.hessianSectionAt covT hσ x (b i) (b i) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  exact OrthonormalBasis.sum_apply_self_eq _ b _

omit [CompleteSpace E] in
/-- **The rough Laplacian read off a frame of vector fields** whose values at `x` are
orthonormal. -/
theorem laplacianSection_eq_sum_frame {σ : Π y : M, V y} (hσ : CMDiff 2 (T% σ)) {x : M}
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, MDiffAt (T% (fr i)) x) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hb : ∀ i, fr i x = b i) :
    cov.laplacianSection covT hσ x = ∑ i, cov.hessianSection covT (fr i) (fr i) σ x := by
  rw [cov.laplacianSection_eq_sum covT hσ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hb i, cov.hessianSectionAt_apply covT hσ (hfr i) (hfr i)]

end Laplacian

section Tangent

/-! ### The tangent bundle is a case of this file

`Hessian.lean` builds `∇²` and `Δ` for vector fields directly. The two towers are not
merely analogous: at `V = TM` with the same connection in both slots, every definition
above **is** the corresponding one there, by `rfl`. These three lemmas are what make that
a checked claim rather than a reading of the source, and they are what lets a fact proved
on either side be used on the other.

They need no `RiemannianBundle` except where the statement itself does (`laplacian` traces
over `stdOrthonormalBasis`), because nothing above asks `TM`'s fibres for a norm — see the
file header for why a fibre norm would have made this unstatable. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇²` on a bundle section is `∇²` on a vector field**, at `V = TM`. -/
theorem hessianSection_eq_hessian (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    cov.hessianSection cov X Y Z x = cov.hessian X Y Z x := rfl

omit [CompleteSpace E] in
/-- The bilinear packagings agree too. -/
theorem hessianSectionAt_eq_hessianAt [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [ContMDiffCovariantDerivative cov 1] {Z : Π y : M, TangentSpace I y}
    (hZ : CMDiff 2 (T% Z)) (x : M) :
    cov.hessianSectionAt cov hZ x = cov.hessianAt hZ x := rfl

omit [CompleteSpace E] in
/-- **The rough Laplacian of a bundle section is the rough Laplacian of a vector field**,
at `V = TM`. -/
theorem laplacianSection_eq_laplacian [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [ContMDiffCovariantDerivative cov 1] {Z : Π y : M, TangentSpace I y}
    (hZ : CMDiff 2 (T% Z)) (x : M) :
    cov.laplacianSection cov hZ x = cov.laplacian hZ x := rfl

end Tangent

end CovariantDerivative
