/-
**The Hilbert–Schmidt Riemannian metric on `End(TM)`.**

`EndMetric.lean` builds the Hilbert–Schmidt form on `End(W)` for a bare finite-dimensional
inner product space `W`. This file turns that pointwise algebra into a genuine
`ContMDiffRiemannianMetric` on the endomorphism bundle of a Riemannian manifold, and then
registers it — so that `End(TM)` is a Riemannian bundle in Mathlib's sense and the whole
`Bundle*` layer (`BundleHessian`, `BundleBochner`, `BundleNormalSection`,
`BundleMaximumPrinciple`) can finally be fed a real tensor bundle. Mathlib supplies no inner
product on `→L` and its only `IsContMDiffRiemannianBundle` instances are the trivial bundle
and index lowering, so both halves have to be built here.

**The smoothness field.** `contMDiff` goes through `contMDiffAt_hom_bundle`, which reduces
smoothness of a section of `Hom(End TM, Hom(End TM, ℝ))` to smoothness of its `inCoordinates`
representative. Two facts carry it:

* **`inCoordinates_bilin`** — for a *bilinear form on the fibre* the coordinate representative
  is the form itself evaluated on the trivialisation's inverse,
  `inCoordinates … Φ u u' = Φ (e.symmL x u) (e.symmL x u')`. The nested hom bundle unfolds
  twice and the inner unfolding lands on the **trivial** bundle `B × ℝ`, whose trivialisation
  is the identity — which is why no coordinate change survives. `hom_trivializationAt_apply`
  is a `rfl`, so the whole computation is two rewrites and a `rfl`. **This is the step that
  looked like the risk and was not.**
* **`contMDiffAt_clm_of_basis`** (from `LeviCivitaSmooth.lean`), applied **twice**: the model
  fibre `E →L[ℝ] E` is finite-dimensional, so smoothness into `L →L[ℝ] L →L[ℝ] ℝ` reduces to
  smoothness of the scalar functions `y ↦ hsFibre y (σ_y u) (σ_y u')`, with `σ_y u` a smooth
  section by `localFrame_eq_symmL'` plus `contMDiffAt_localFrame_of_mem`.

That scalar smoothness is `contMDiffAt_hsFibre_apply`, and it is where the *tangent* bundle's
own Riemannian structure enters: a local **orthonormal frame** of `TM` computes `hsFibre` as a
finite sum of inner products of tangent vectors (`hsForm_congr` — frame independence), each
term smooth by `ContMDiffAt.clm_bundle_apply` then `ContMDiffAt.inner_bundle`.

**The real obstruction was elsewhere, and it is a genuine finding.** The metric cannot be
attached to `fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y` through `RiemannianBundle` at
all: that fibre already carries the **operator norm** at default instance priority, while the
norm `RiemannianBundle` induces is a *scoped* instance at priority `80`. So
`InnerProductSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x)` resolves to nothing — the
operator-norm `NormedAddCommGroup` wins the first search and no `InnerProductSpace` matches
it. `TangentSpace` escapes this only because it is a **non-reducible type synonym** with no
competing head symbol; mathlib says so in as many words ("The definition of `TangentSpace` is
not reducible so that type class inference does not pick wrong instances"). This is
`CLAUDE.md`'s corrected belief 4 — "a fibre norm would break the bridge outright" — one type
former up, and the priority-80 trick does not save it.

So `EndTangent I x` is the same synonym one level up, with the nine fibre and bundle instances
transported by `inferInstanceAs`. **The transport of the metric itself is definitional**
(`endTangentMetric := endMetric`): `EndTangent I` and the raw bundle are equal by `delta` and
`eta`, and every transported instance is literally the raw one. That is what lets the *proofs*
stay in the raw world, where every mathlib hom-bundle lemma applies syntactically, while the
*statement* lives on the synonym, where instance search behaves.

Gotchas: `set_option maxSynthPendingDepth 4` is needed for
`(E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] ℝ`, one deeper than the `3` the rest of the repo uses;
and `endTangentRiemannianBundle` must be `@[instance_reducible]`, since mathlib's
`IsContMDiffRiemannianBundle` instance matches on a `RiemannianBundle` of the syntactic shape
`⟨g.toRiemannianMetric⟩` and cannot see through a semireducible wrapper.
-/
import RicciFlowBlueprint.EndMetric
import RicciFlowBlueprint.TraceCov

open Bundle Manifold ContinuousLinearMap
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

section General

variable
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : B → Type*} [∀ y, AddCommGroup (E₁ y)] [∀ y, Module ℝ (E₁ y)]
  [∀ y, TopologicalSpace (E₁ y)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]

/-- **The coordinate representative of a bilinear form on a fibre.** In the trivialisation it
is the form itself, evaluated on the images of the coordinates under the trivialisation's
inverse. The inner unfolding lands on the trivial bundle, whose trivialisation is the
identity, so no coordinate change survives. -/
theorem inCoordinates_bilin (x₀ x : B) (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (Φ : E₁ x →L[ℝ] E₁ x →L[ℝ] ℝ) (u u' : F₁) :
    ContinuousLinearMap.inCoordinates F₁ E₁ (F₁ →L[ℝ] ℝ) (fun y ↦ E₁ y →L[ℝ] ℝ)
        x₀ x x₀ x Φ u u'
      = Φ ((trivializationAt F₁ E₁ x₀).symmL ℝ x u)
          ((trivializationAt F₁ E₁ x₀).symmL ℝ x u') := by
  have hx2 : x ∈ (trivializationAt (F₁ →L[ℝ] ℝ) (fun y ↦ E₁ y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [ContinuousLinearMap.inCoordinates]
  simp only [coe_comp, Function.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt (F₁ →L[ℝ] ℝ) (fun y ↦ E₁ y →L[ℝ] ℝ) x₀) hx2,
    hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  simp only [coe_comp, Function.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt ℝ (Bundle.Trivial B ℝ) x₀) (by simp)]
  rfl

end General

section LocalFrame

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ y, AddCommGroup (V y)]
  [∀ y, Module ℝ (V y)] [∀ y, TopologicalSpace (V y)]
  [FiberBundle F V] [VectorBundle ℝ F V] {m : ℕ∞ω} [ContMDiffVectorBundle m F V IB]
  {ι : Type*}

/-- **The local frame of a trivialisation is the trivialisation's inverse on a basis**, on its
base set — the general-bundle form of `localFrame_eq_symmL`. -/
theorem localFrame_eq_symmL' (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ F) {x : B} (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrame b i x = e.symmL ℝ x (b i) := by
  simp [e.localFrame_apply_of_mem_baseSet b hx, Trivialization.basisAt,
    Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply, e.symmL_apply hx]

end LocalFrame

section EndBundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {n : ℕ∞ω}
  [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle n E (fun (x : M) ↦ TangentSpace I x) I]

set_option maxSynthPendingDepth 4

/-- **The Hilbert–Schmidt inner product on the fibre `End(T_xM)`.** -/
noncomputable def hsFibre (x : M) :
    (TangentSpace I x →L[ℝ] TangentSpace I x) →L[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x) →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  hsForm (stdOrthonormalBasis ℝ (TangentSpace I x))

omit [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle n E (fun (x : M) ↦ TangentSpace I x) I] in
/-- `hsFibre` may be computed in any orthonormal basis of the fibre. -/
theorem hsFibre_eq {x : M} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (A B : TangentSpace I x →L[ℝ] TangentSpace I x) :
    hsFibre (I := I) x A B = hsForm b A B := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  exact hsForm_congr _ b A B

omit [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle n E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **`hsFibre` over a local orthonormal frame of `TM`.** The Hilbert–Schmidt form of two
endomorphisms of a fibre is the sum of the inner products of their values on any frame that
is orthonormal there — frame independence, cashed in on the frames a manifold actually
supplies. -/
theorem hsFibre_eq_sum_frame {ιf : Type*} [Fintype ιf]
    {fr : ιf → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) {y : M} (hy : y ∈ u)
    (A B : TangentSpace I y →L[ℝ] TangentSpace I y) :
    hsFibre (I := I) y A B = ∑ i, ⟪A (fr i y), B (fr i y)⟫ := by
  obtain ⟨c, hc⟩ := CovariantDerivative.exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
  rw [hsFibre_eq c, hsForm_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hc i]

omit [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- The Hilbert–Schmidt form is symmetric. -/
theorem hsFibre_symm (x : M) (A B : TangentSpace I x →L[ℝ] TangentSpace I x) :
    hsFibre (I := I) x A B = hsFibre (I := I) x B A := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  rw [hsFibre_eq (stdOrthonormalBasis ℝ (TangentSpace I x)),
    hsFibre_eq (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact hsForm_symm _ A B

omit [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- The Hilbert–Schmidt form is positive definite. -/
theorem hsFibre_self_pos {x : M} {A : TangentSpace I x →L[ℝ] TangentSpace I x} (hA : A ≠ 0) :
    0 < hsFibre (I := I) x A A := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  rw [hsFibre_eq (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact hsForm_self_pos _ hA

omit [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- The unit set of the Hilbert–Schmidt form is bounded, so it defines the fibre's topology. -/
theorem isVonNBounded_hsFibre (x : M) :
    Bornology.IsVonNBounded ℝ
      {A : TangentSpace I x →L[ℝ] TangentSpace I x | hsFibre (I := I) x A A < 1} := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  have hset : {A : TangentSpace I x →L[ℝ] TangentSpace I x | hsFibre (I := I) x A A < 1}
      = {A | hsForm (stdOrthonormalBasis ℝ (TangentSpace I x)) A A < 1} := by
    ext A
    simp only [Set.mem_ofPred_eq, hsFibre_eq (stdOrthonormalBasis ℝ (TangentSpace I x))]
  rw [hset]
  exact isVonNBounded_hsForm_lt_one _

/-- **Smoothness of the Hilbert–Schmidt pairing** of two `C^n` sections of `End(TM)`. -/
theorem contMDiffAt_hsFibre_apply
    {A B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x₀ : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y (A y)) x₀)
    (hB : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y (B y)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y ↦ hsFibre (I := I) y (A y) (B y)) x₀ := by
  classical
  set e := trivializationAt E (fun y : M ↦ TangentSpace I y) x₀ with he
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  set bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbE
  set fr := bE.orthonormalFrame e with hfr
  have h1 : IsOrthonormalFrameOn I E 1 fr e.baseSet :=
    bE.orthonormalFrame_isOrthonormalFrameOn e
  have key : ∀ y ∈ e.baseSet,
      hsFibre (I := I) y (A y) (B y) = ∑ i, ⟪A y (fr i y), B y (fr i y)⟫ :=
    fun y hy ↦ hsFibre_eq_sum_frame h1 hy (A y) (B y)
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ ∑ i, ⟪A y (fr i y), B y (fr i y)⟫) x₀ := by
    refine ContMDiffAt.sum (fun i _ ↦ ?_)
    have hfri : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% (fr i)) x₀ :=
      contMDiffAt_orthonormalFrame_of_mem bE e i hx₀
    exact ContMDiffAt.inner_bundle' (hA.clm_bundle_apply hfri) (hB.clm_bundle_apply hfri)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy using key y hy

/-- **The Hilbert–Schmidt fibre metric on `End(TM)` is `C^n`.** -/
theorem contMDiff_hsFibre :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' ((E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] TangentSpace I y) →L[ℝ]
          (TangentSpace I y →L[ℝ] TangentSpace I y) →L[ℝ] ℝ) x (hsFibre (I := I) x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set eL := trivializationAt (E →L[ℝ] E)
    (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) x₀ with heL
  have hx₀ : x₀ ∈ eL.baseSet := mem_baseSet_trivializationAt _ _ _
  set bL : Module.Basis (Fin (Module.finrank ℝ (E →L[ℝ] E))) ℝ (E →L[ℝ] E) :=
    Module.finBasis ℝ (E →L[ℝ] E) with hbL
  have hsec : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y
        (eL.symmL ℝ y (bL i))) x₀ := by
    intro i
    refine (contMDiffAt_localFrame_of_mem (I := I) (n := n) eL bL i hx₀).congr_of_eventuallyEq ?_
    filter_upwards [eL.open_baseSet.mem_nhds hx₀] with y hy
    show TotalSpace.mk' (E →L[ℝ] E) y _ = TotalSpace.mk' (E →L[ℝ] E) y _
    rw [localFrame_eq_symmL' eL bL hy i]
  refine contMDiffAt_clm_of_basis bL (fun i ↦ ?_)
  refine contMDiffAt_clm_of_basis bL (fun j ↦ ?_)
  refine (contMDiffAt_hsFibre_apply (hsec i) (hsec j)).congr_of_eventuallyEq ?_
  filter_upwards [eL.open_baseSet.mem_nhds hx₀] with y hy
  exact inCoordinates_bilin x₀ y hy (hsFibre (I := I) y) (bL i) (bL j)

/-- **The Hilbert–Schmidt Riemannian metric on `End(TM)`.** -/
noncomputable def endMetric :
    Bundle.ContMDiffRiemannianMetric I n (E →L[ℝ] E)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) where
  inner := hsFibre (I := I)
  symm := hsFibre_symm
  pos _ _ hv := hsFibre_self_pos hv
  isVonNBounded := isVonNBounded_hsFibre
  contMDiff := contMDiff_hsFibre

end EndBundle

section Synonym

/-! ### `End(TM)` as a type synonym

The Hilbert–Schmidt metric cannot be attached to `fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y`
through Mathlib's `RiemannianBundle` mechanism: that fibre already carries the **operator norm**
at default instance priority, while the norm `RiemannianBundle` induces is scoped at priority
`80`, so `InnerProductSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x)` never resolves to the
Hilbert–Schmidt one. `TangentSpace` escapes this only because it is a non-reducible type synonym
with no competing head symbol — mathlib says so in as many words ("The definition of
`TangentSpace` is not reducible so that type class inference does not pick wrong instances").
So the fix is the same synonym one type former up. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

set_option maxSynthPendingDepth 4

/-- **The endomorphism bundle of `TM`, as a type synonym.** Not reducible, so that instance
search does not pick the operator norm on the fibre in place of the Hilbert–Schmidt metric —
exactly the reason `TangentSpace` is a synonym. -/
@[nolint unusedArguments]
def EndTangent (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (x : M) : Type _ :=
  TangentSpace I x →L[ℝ] TangentSpace I x

noncomputable instance (x : M) : AddCommGroup (EndTangent I x) :=
  inferInstanceAs (AddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x))

noncomputable instance (x : M) : Module ℝ (EndTangent I x) :=
  inferInstanceAs (Module ℝ (TangentSpace I x →L[ℝ] TangentSpace I x))

noncomputable instance (x : M) : TopologicalSpace (EndTangent I x) :=
  inferInstanceAs (TopologicalSpace (TangentSpace I x →L[ℝ] TangentSpace I x))

noncomputable instance (x : M) : IsTopologicalAddGroup (EndTangent I x) :=
  inferInstanceAs (IsTopologicalAddGroup (TangentSpace I x →L[ℝ] TangentSpace I x))

noncomputable instance (x : M) : ContinuousSMul ℝ (EndTangent I x) :=
  inferInstanceAs (ContinuousSMul ℝ (TangentSpace I x →L[ℝ] TangentSpace I x))

noncomputable instance : TopologicalSpace (TotalSpace (E →L[ℝ] E) (EndTangent I (M := M))) :=
  inferInstanceAs (TopologicalSpace
    (TotalSpace (E →L[ℝ] E) (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y)))

noncomputable instance : FiberBundle (E →L[ℝ] E) (EndTangent I (M := M)) :=
  inferInstanceAs (FiberBundle (E →L[ℝ] E)
    (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y))

noncomputable instance : VectorBundle ℝ (E →L[ℝ] E) (EndTangent I (M := M)) :=
  inferInstanceAs (VectorBundle ℝ (E →L[ℝ] E)
    (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y))

noncomputable instance {m : ℕ∞ω} [ContMDiffVectorBundle m E (fun (x : M) ↦ TangentSpace I x) I] :
    ContMDiffVectorBundle m (E →L[ℝ] E) (EndTangent I (M := M)) I :=
  inferInstanceAs (ContMDiffVectorBundle m (E →L[ℝ] E)
    (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) I)

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {n : ℕ∞ω}
  [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle n E (fun (x : M) ↦ TangentSpace I x) I]

variable (I n) in
/-- **The Hilbert–Schmidt metric on the endomorphism bundle**, transported to the synonym. The
transport is a definitional one: `EndTangent I` and `fun y ↦ TangentSpace I y →L[ℝ]
TangentSpace I y` are equal by `delta` and `eta`, and every fibre instance above is literally
the corresponding instance of the raw bundle. -/
noncomputable def endTangentMetric :
    Bundle.ContMDiffRiemannianMetric I n (E →L[ℝ] E) (EndTangent I (M := M)) :=
  endMetric

/-- Registering the Hilbert–Schmidt metric makes `End(TM)` a Riemannian bundle. -/
@[instance_reducible] noncomputable def endTangentRiemannianBundle :
    RiemannianBundle (EndTangent I (M := M)) :=
  ⟨(endTangentMetric I n (M := M)).toRiemannianMetric⟩

/-- **`End(TM)` is a `C^n` Riemannian bundle.** This is the falsification check for the whole
file: the instance is what `BundleBochner.lean` and `BundleMaximumPrinciple.lean` consume, and
it is unobtainable on the raw endomorphism bundle. -/
theorem isContMDiffRiemannianBundle_endTangent :
    letI : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := n)
    IsContMDiffRiemannianBundle I n (E →L[ℝ] E) (EndTangent I (M := M)) :=
  letI : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := n)
  inferInstance

end Synonym

end RicciFlowBlueprint
