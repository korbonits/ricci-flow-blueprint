/-
**Parallel transport on `End(TM)`.**

`ParallelTransportGlobal.lean` transports a vector; `ParallelFrame.lean` transports a whole
orthonormal basis. This transports an *endomorphism*: for every `A₀ ∈ End(T_{γt₀}M)` there is
a field along `γ` that is parallel for the induced connection `endCov` and equals `A₀` at `t₀`.

**Why an orthonormal frame makes this cheap.** Against a general transported frame, writing an
endomorphism in frame coordinates needs the inverse of the frame matrix, which then has to be
differentiated. Against an *orthonormal* one the coordinates are just
`mᵢⱼ = ⟪bᵢ, A₀(bⱼ)⟫`, and the transported field is the fixed combination
`A u = ∑ᵢⱼ mᵢⱼ ⟪frⱼ u, ·⟫ frᵢ u`
of rank-one operators built from the frame. No inversion appears anywhere.

**The index order is load-bearing, not cosmetic.** Written the other way round --- coordinates
`⟪A₀(bⱼ), bᵢ⟫`, outer sum `∑ᵢ ⟪A₀ v, bᵢ⟫ • bᵢ` --- the expansion is equal over `ℝ` to
`OrthonormalBasis.sum_repr'` but not *syntactically*, and unification then grinds through the
metric's construction: a `whnf` timeout at 200k heartbeats, corrected belief 5 met again one
type former down. With `⟪bᵢ, A₀(bⱼ)⟫` the expansion matches `sum_repr'` on the nose and the
file compiles in seconds.

**Parallelism costs no transport computation.** `endoAlong_apply_frame` says the value on
`frₖ` is a *constant* combination of the frame, hence parallel; the Leibniz rule of
`HomBundleAlongCurve.lean` then gives `(D/dt A)(frₖ u) = 0` for every `k`, and the frame is a
basis of the fibre. That file names the missing half of its own converse as "a family of
parallel sections spanning each fibre"; this is it, and the metric is what supplies it.

**The one genuinely new brick is the differentiability criterion.** `HomBundleSmooth.lean` has
the pointwise statement — a section of `Hom(W₁,W₂)` is `C^n` as soon as its values on the
source trivialisation's local frame are — and what a *constructed* morphism field **along a
curve** needs is the same statement with `ContMDiffAt` replaced by differentiability along the
curve. It transposes: the coordinate of a Hom section is literally the target trivialisation's
coordinate of `u ↦ A u (e₁.symmL (γ u) w)`, so no coordinate change survives there either.
-/
import RicciFlowBlueprint.ParallelFrame
import RicciFlowBlueprint.HomBundleAlongCurve
import RicciFlowBlueprint.HomBundleSmooth
import RicciFlowBlueprint.IveyParallel

open Bundle Filter Set ContinuousLinearMap CovariantDerivative
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

section ClmBasis

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {ι : Type*} [Fintype ι]

/-- A curve in `F →L[ℝ] G` (with `F` finite-dimensional) is differentiable at a time as soon as
its values on a basis of `F` are.  The `DifferentiableAt` transposition of
`contMDiffAt_clm_of_basis`, which is what a statement along a curve consumes. -/
theorem differentiableAt_clm_of_basis (b : Module.Basis ι ℝ F) {A : ℝ → F →L[ℝ] G} {t : ℝ}
    (h : ∀ i, DifferentiableAt ℝ (fun u ↦ A u (b i)) t) : DifferentiableAt ℝ A t := by
  have hA : A = fun u ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ F G
      (LinearMap.toContinuousLinearMap (b.coord i)) (A u (b i)) := by
    funext u
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simp [ContinuousLinearMap.smulRightL_apply_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Finsupp.single_eq_of_ne hij]
    · simp
  rw [hA]
  exact DifferentiableAt.fun_sum fun i _ ↦
    ((ContinuousLinearMap.smulRightL ℝ F G
      (LinearMap.toContinuousLinearMap (b.coord i))).differentiableAt).comp t (h i)

end ClmBasis

section Criterion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {W₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ W₁)]
  [∀ x : M, AddCommGroup (W₁ x)] [∀ x : M, Module ℝ (W₁ x)]
  [∀ x : M, TopologicalSpace (W₁ x)] [∀ x : M, IsTopologicalAddGroup (W₁ x)]
  [∀ x : M, ContinuousSMul ℝ (W₁ x)] [FiberBundle F₁ W₁] [VectorBundle ℝ F₁ W₁]
  [ContMDiffVectorBundle 1 F₁ W₁ I]
  {W₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ W₂)]
  [∀ x : M, AddCommGroup (W₂ x)] [∀ x : M, Module ℝ (W₂ x)]
  [∀ x : M, TopologicalSpace (W₂ x)] [∀ x : M, IsTopologicalAddGroup (W₂ x)]
  [∀ x : M, ContinuousSMul ℝ (W₂ x)] [FiberBundle F₂ W₂] [VectorBundle ℝ F₂ W₂]
  [ContMDiffVectorBundle 1 F₂ W₂ I]
  {ι : Type*} [Fintype ι] {γ : ℝ → M}

set_option maxSynthPendingDepth 4

omit [IsManifold I ω M] [∀ (x : M), IsTopologicalAddGroup (W₁ x)]
  [∀ (x : M), ContinuousSMul ℝ (W₁ x)] in
-- BENCH: hom-section-along-curve-criterion
/-- **A morphism field along a curve is differentiable as soon as its values on the source
trivialisation's local frame are.**

The along-curve transposition of `contMDiffAt_hom_section_of_symmL`, and what a *constructed*
morphism field along a curve needs — there is no global section to restrict, so
`MDiffAlongSectionAt.of_section` does not apply.

It is cheap for the same reason the pointwise version is: the Hom bundle's trivialisation
coordinate of `A u` is, applied to `w`, literally the target trivialisation's coordinate of
`u ↦ A u (e₁.symmL (γ u) w)`, so **no coordinate change survives**. The only additions are
`differentiableAt_clm_of_basis`, to go from the basis values to the whole coordinate, and one
`eventuallyEq` because the identity holds only where the curve is inside both base sets. -/
theorem mdiffAlongSectionAt_hom_of_symmL
    {A : Π u : ℝ, W₁ (γ u) →L[ℝ] W₂ (γ u)} {t : ℝ} (b : Module.Basis ι ℝ F₁)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (h : ∀ i, MDiffAlongSectionAt I F₂ W₂ γ
      (fun u ↦ A u ((trivializationAt F₁ W₁ (γ t)).symmL ℝ (γ u) (b i))) t) :
    MDiffAlongSectionAt I (F₁ →L[ℝ] F₂) (fun y ↦ W₁ y →L[ℝ] W₂ y) γ A t := by
  have h₂ : γ t ∈ (trivializationAt F₂ W₂ (γ t)).baseSet :=
    mem_baseSet_trivializationAt F₂ W₂ (γ t)
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ (trivializationAt F₂ W₂ (γ t)).baseSet :=
    hγ.continuousAt ((trivializationAt F₂ W₂ (γ t)).open_baseSet.mem_nhds h₂)
  rw [mdiffAlongSectionAt_iff_of_mem
    (e := trivializationAt (F₁ →L[ℝ] F₂) (fun y ↦ W₁ y →L[ℝ] W₂ y) (γ t)) hγ
    (mem_baseSet_trivializationAt _ _ _)]
  refine differentiableAt_clm_of_basis b fun i ↦ ?_
  have hi : DifferentiableAt ℝ
      (fun u ↦ (trivializationAt F₂ W₂ (γ t)
        ⟨γ u, A u ((trivializationAt F₁ W₁ (γ t)).symmL ℝ (γ u) (b i))⟩).2) t :=
    (mdiffAlongSectionAt_iff_of_mem hγ h₂).mp (h i)
  refine hi.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with u hu
  rw [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  simp only [coe_comp, Function.comp_apply]
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hu _

end Criterion

section Construction

open CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {γ : ℝ → M} {t₀ : ℝ} {ι : Type*} [Fintype ι]

set_option maxSynthPendingDepth 4

/-- Bilinearity in the right slot, stated over a variable inner product space.

`inner_sum` will not `rw` on a `Finset.sum` of `TangentSpace`-typed terms — it picks `E`'s own
`AddCommMonoid` — so the step is stated here and applied with `exact`, which unifies up to
defeq. The documented remedy. -/
theorem inner_sum_smul_right_aux {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {κ : Type*} [Fintype κ] (w : F) (c : κ → ℝ) (z : κ → F) :
    (⟪w, ∑ j, c j • z j⟫ : ℝ) = ∑ j, c j * ⟪w, z j⟫ := by
  rw [inner_sum]
  exact Finset.sum_congr rfl fun j _ ↦ real_inner_smul_right _ _ _

/-- **The transported endomorphism**, written in a parallel orthonormal frame.

The coordinates `mᵢⱼ = ⟪bᵢ, A₀(bⱼ)⟫` are *constants*, and the field is the fixed combination
`∑ᵢⱼ mᵢⱼ ⟪frⱼ u, ·⟫ frᵢ u` of rank-one operators built from the frame. **Orthonormality is
what removes the inversion**: against a general frame the coordinates of an endomorphism need
the inverse of the frame matrix, which would then have to be differentiated.

**The index order is not cosmetic.** Writing `⟪bᵢ, A₀(bⱼ)⟫` rather than `⟪A₀(bⱼ), bᵢ⟫` is what
makes the expansion match `OrthonormalBasis.sum_repr'` syntactically; with the slots swapped the
two are equal over `ℝ` but not syntactically, and unification grinds to a `whnf` timeout
through the metric. -/
noncomputable def endoAlong (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    (fr : ι → Π u : ℝ, TangentSpace I (γ u)) (u : ℝ) :
    TangentSpace I (γ u) →L[ℝ] TangentSpace I (γ u) :=
  ∑ i, ∑ j, (⟪b i, A₀ (b j)⟫ : ℝ) • (innerSL ℝ (fr j u)).smulRight (fr i u)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
theorem endoAlong_apply (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    (fr : ι → Π u : ℝ, TangentSpace I (γ u)) (u : ℝ) (v : TangentSpace I (γ u)) :
    endoAlong b A₀ fr u v
      = ∑ i, ∑ j, (⟪b i, A₀ (b j)⟫ : ℝ) • ((⟪fr j u, v⟫ : ℝ) • fr i u) := by
  simp [endoAlong]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **At the base time the field is `A₀`, pointwise.**  The inner sum is the orthonormal
expansion of `A₀ v`'s coordinates and the outer one is `sum_repr'`, so the whole computation is
that one lemma applied twice with nothing reindexed. -/
theorem endoAlong_apply_self (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)} (hfr : ∀ i, fr i t₀ = b i)
    (v : TangentSpace I (γ t₀)) : endoAlong b A₀ fr t₀ v = A₀ v := by
  rw [endoAlong_apply]
  simp only [hfr]
  have hv : ∀ i, (∑ j, (⟪b i, A₀ (b j)⟫ : ℝ) * ⟪b j, v⟫) = ⟪b i, A₀ v⟫ := by
    intro i
    have hexp : A₀ v = ∑ j, (⟪b j, v⟫ : ℝ) • A₀ (b j) := by
      conv_lhs => rw [← b.sum_repr' v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ map_smul _ _ _
    rw [hexp]
    have key := inner_sum_smul_right_aux (F := TangentSpace I (γ t₀)) (b i)
      (fun j ↦ (⟪b j, v⟫ : ℝ)) (fun j ↦ A₀ (b j))
    rw [key]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  calc (∑ i, ∑ j, (⟪b i, A₀ (b j)⟫ : ℝ) • ((⟪b j, v⟫ : ℝ) • b i))
      = ∑ i, (⟪b i, A₀ v⟫ : ℝ) • b i := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← hv i, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [smul_smul]
    _ = A₀ v := b.sum_repr' _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
theorem endoAlong_self (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)} (hfr : ∀ i, fr i t₀ = b i) :
    endoAlong b A₀ fr t₀ = A₀ :=
  ContinuousLinearMap.ext (endoAlong_apply_self b A₀ hfr)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- The same expansion with the two scalars merged, which is the shape the differentiability
argument consumes: a fixed frame section scaled by one function of the parameter. -/
theorem endoAlong_apply' (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    (fr : ι → Π u : ℝ, TangentSpace I (γ u)) (u : ℝ) (v : TangentSpace I (γ u)) :
    endoAlong b A₀ fr u v
      = ∑ i, ∑ j, ((⟪b i, A₀ (b j)⟫ : ℝ) * (⟪fr j u, v⟫ : ℝ)) • fr i u := by
  rw [endoAlong_apply]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ smul_smul _ _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **The value on the frame.** Orthonormality of `fr · u` collapses the inner sum, leaving a
combination of the frame with *constant* coefficients — which is exactly the hypothesis
`isParallelAlong_sum_smul` consumes. -/
theorem endoAlong_apply_frame (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)} {u : ℝ}
    (hon : Orthonormal ℝ fun i ↦ fr i u) (k : ι) :
    endoAlong b A₀ fr u (fr k u) = ∑ i, (⟪b i, A₀ (b k)⟫ : ℝ) • fr i u := by
  classical
  have hij := orthonormal_iff_ite.mp hon
  rw [endoAlong_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single k (fun j _ hjk ↦ by rw [hij j k]; simp [hjk])
    (fun h ↦ absurd (Finset.mem_univ k) h), hij k k]
  simp

end Construction

section Transport

/-! ### `End(TM)` parallel transport

The frame turned into a morphism field. `endoAlong` is parallel as a section of
`Hom(TM,TM)`, which is what the cross-fibre comparison needs: the tested endomorphism is
carried between fibres with its Hilbert–Schmidt norm and its spectrum intact, so
`IveyEndo.lean`'s `mem_iveyEndoSet_conj_iff` says the pinching set travels with it.

**Nothing is transported twice.** Parallelism is read off the Leibniz rule
`D/dt(Aσ) = (D/dt A)σ + A(D/dt σ)` of `HomBundleAlongCurve.lean`: both `fr k` and
`A(fr k)` are parallel — the latter because `endoAlong_apply_frame` writes it as a
*constant* combination of the frame — so `(D/dt A)(fr k u) = 0` for every `k`, and the
frame is a basis of the fibre. This is the "family of parallel sections spanning each
fibre" that file names as the missing half of its converse. -/

open CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} {ι : Type*} [Fintype ι]

set_option maxSynthPendingDepth 4

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- Differentiability along `γ` depends on the section only through its germ. Stated here
because `MDifferentiableAt.congr_of_eventuallyEq` wants the equality of the *total-space*
maps, and every use below has it fibrewise. -/
theorem mdiffAlongAt_congr {V V' : Π u : ℝ, TangentSpace I (γ u)} {t : ℝ}
    (h : MDiffAlongAt γ V t) (hev : V' =ᶠ[𝓝 t] V) : MDiffAlongAt γ V' t := by
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hev] with u hu
  show (⟨γ u, V' u⟩ : TangentBundle I M) = ⟨γ u, V u⟩
  rw [hu]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- The trivialisation's inverse frame is differentiable along the curve, for the trivial
reason: in *that* trivialisation's own coordinate it is the constant `v`. -/
theorem mdiffAlongAt_symmL
    {e : Trivialization E (TotalSpace.proj :
      TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)} [MemTrivializationAtlas e]
    {u : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ u) (hu : γ u ∈ e.baseSet) (v : E) :
    MDiffAlongAt γ (fun w ↦ e.symmL ℝ (γ w) v) u := by
  have hnhds : ∀ᶠ w in 𝓝 u, γ w ∈ e.baseSet := hγ.continuousAt (e.open_baseSet.mem_nhds hu)
  rw [mdiffAlongAt_iff_of_mem (e := e) hγ hu]
  refine (differentiableAt_const v).congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with w hw
  show (e ⟨γ w, e.symmL ℝ (γ w) v⟩).2 = v
  rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hw,
    e.continuousLinearMapAt_symmL (R := ℝ) hw]

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **`endoAlong` is differentiable along the curve, as a section of the Hom bundle.**

Through `mdiffAlongSectionAt_hom_of_symmL` the claim reduces to the values on the source
trivialisation's inverse frame; there `endoAlong_apply'` writes the section as a finite
combination of the frame with coefficients `⟪frⱼ, ·⟫`, whose differentiability is
`hasDerivAt_inner_along` — the one place metric compatibility is used. -/
theorem mdiffAlongSectionAt_endoAlong
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)} {u : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ u) (hfrd : ∀ i, MDiffAlongAt γ (fr i) u) :
    MDiffAlongSectionAt I (E →L[ℝ] E)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) γ (endoAlong b A₀ fr) u := by
  classical
  set e := trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ u) with he
  have hu : γ u ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ u)
  refine mdiffAlongSectionAt_hom_of_symmL (Module.finBasis ℝ E) hγ fun n ↦ ?_
  show MDiffAlongAt γ (fun w ↦ endoAlong b A₀ fr w
    (e.symmL ℝ (γ w) (Module.finBasis ℝ E n))) u
  have hW : MDiffAlongAt γ (fun w ↦ e.symmL ℝ (γ w) (Module.finBasis ℝ E n)) u :=
    mdiffAlongAt_symmL hγ hu _
  have hkey : (fun w ↦ endoAlong b A₀ fr w (e.symmL ℝ (γ w) (Module.finBasis ℝ E n)))
      = fun w ↦ ∑ i, ∑ j, ((⟪b i, A₀ (b j)⟫ : ℝ)
        * (⟪fr j w, e.symmL ℝ (γ w) (Module.finBasis ℝ E n)⟫ : ℝ)) • fr i w := by
    funext w; exact endoAlong_apply' b A₀ fr w _
  rw [hkey]
  refine MDiffAlongAt.sum hγ _ fun i _ ↦ MDiffAlongAt.sum hγ _ fun j _ ↦ ?_
  exact MDiffAlongAt.smul hγ ((differentiableAt_const _).mul
    (hasDerivAt_inner_along cov hmet hγ (hfrd j) hW).differentiableAt) (hfrd i)

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`endoAlong` carries each frame section to a parallel section**: by
`endoAlong_apply_frame` its value there is a *constant* combination of the frame. -/
theorem isParallelAlong_endoAlong_frame
    (hs : IsOpen s) (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)}
    (hfrd : ∀ i, ∀ w ∈ s, MDiffAlongAt γ (fr i) w)
    (hfrp : ∀ i, IsParallelAlong cov γ (fr i) s)
    (hon : ∀ w ∈ s, Orthonormal ℝ fun i ↦ fr i w) (k : ι) :
    IsParallelAlong cov γ (fun u ↦ endoAlong b A₀ fr u (fr k u)) s := by
  set c : ι → ℝ := fun i ↦ (⟪b i, A₀ (b k)⟫ : ℝ) with hc
  have hsum : IsParallelAlong cov γ (fun u ↦ ∑ i, c i • fr i u) s :=
    isParallelAlong_sum_smul cov hγ Finset.univ c (fun i _ ↦ hfrd i) (fun i _ ↦ hfrp i)
  have hsumd : ∀ w ∈ s, MDiffAlongAt γ (fun u ↦ ∑ i, c i • fr i u) w := fun w hw ↦
    MDiffAlongAt.sum (hγ w hw) _ fun i _ ↦
      MDiffAlongAt.smul (hγ w hw) (differentiableAt_const (c i)) (hfrd i w hw)
  have hev : ∀ w ∈ s, (fun v ↦ endoAlong b A₀ fr v (fr k v))
      =ᶠ[𝓝 w] fun v ↦ ∑ i, c i • fr i v := fun w hw ↦ by
    filter_upwards [hs.mem_nhds hw] with v hv using endoAlong_apply_frame b A₀ (hon v hv) k
  have hd : ∀ w ∈ s, MDiffAlongAt γ (fun u ↦ endoAlong b A₀ fr u (fr k u)) w := fun w hw ↦
    mdiffAlongAt_congr (hsumd w hw) (hev w hw)
  intro w hw
  rw [(isCovDerivAlong_covAlong cov γ).congr_of_eventuallyEq (hd w hw) (hsumd w hw)
    (hγ w hw) (hev w hw)]
  exact hsum w hw

omit [CompleteSpace E] [ContMDiffCovariantDerivative cov 1] in
/-- **`endoAlong` is a parallel section of the Hom bundle.**

`covAlongSection_hom_apply_eq_zero` gives `(D/dt A)(fr k u) = 0` for every `k`, and the frame
is an orthonormal basis of the fibre, so the operator itself vanishes. This is the converse
`HomBundleAlongCurve.lean` leaves open, with the spanning family supplied by the metric. -/
theorem isParallelAlongSection_endoAlong
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)}
    (hfrd : ∀ i, ∀ w ∈ s, MDiffAlongAt γ (fr i) w)
    (hfrp : ∀ i, IsParallelAlong cov γ (fr i) s)
    (hbu : ∀ w ∈ s, ∃ bw : OrthonormalBasis ι ℝ (TangentSpace I (γ w)), ∀ i, bw i = fr i w) :
    IsParallelAlongSection I (E →L[ℝ] E)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) (homCov cov cov) γ
      (endoAlong b A₀ fr) s := by
  have hon : ∀ w ∈ s, Orthonormal ℝ fun i ↦ fr i w := fun w hw ↦ by
    obtain ⟨bw, hbw⟩ := hbu w hw
    have : (fun i ↦ fr i w) = fun i ↦ bw i := funext fun i ↦ (hbw i).symm
    rw [this]; exact bw.orthonormal
  have hA : ∀ w ∈ s, MDiffAlongSectionAt I (E →L[ℝ] E)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) γ (endoAlong b A₀ fr) w :=
    fun w hw ↦ mdiffAlongSectionAt_endoAlong cov hmet b A₀ (hγ w hw) fun i ↦ hfrd i w hw
  have hAfr : ∀ k, IsParallelAlong cov γ (fun u ↦ endoAlong b A₀ fr u (fr k u)) s := fun k ↦
    isParallelAlong_endoAlong_frame cov hs hγ b A₀ hfrd hfrp hon k
  have hAfrd : ∀ k, ∀ w ∈ s, MDiffAlongAt γ (fun u ↦ endoAlong b A₀ fr u (fr k u)) w :=
    fun k w hw ↦ by
      have hbw : (fun v ↦ endoAlong b A₀ fr v (fr k v))
          =ᶠ[𝓝 w] fun v ↦ ∑ i, (⟪b i, A₀ (b k)⟫ : ℝ) • fr i v := by
        filter_upwards [hs.mem_nhds hw] with v hv using endoAlong_apply_frame b A₀ (hon v hv) k
      exact mdiffAlongAt_congr (MDiffAlongAt.sum (hγ w hw) _ fun i _ ↦
        MDiffAlongAt.smul (hγ w hw) (differentiableAt_const _) (hfrd i w hw)) hbw
  intro w hw
  obtain ⟨bw, hbw⟩ := hbu w hw
  have hzero : ∀ k, covAlongSection (homCov cov cov) γ (endoAlong b A₀ fr) w (fr k w) = 0 :=
    fun k ↦ covAlongSection_hom_apply_eq_zero cov cov (hγ w hw) (hA w hw) (hfrd k w hw)
      ((covAlongSection_eq_covAlong cov (hγ w hw) (hfrd k w hw)).trans (hfrp k w hw))
      ((covAlongSection_eq_covAlong cov (hγ w hw) (hAfrd k w hw)).trans (hAfr k w hw))
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : v = ∑ k, (⟪bw k, v⟫ : ℝ) • bw k := (bw.sum_repr' v).symm
  rw [hv, map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [map_smul, hbw k, hzero k, smul_zero]

/-- The conjugate of an endomorphism by a linear isometry, expanded in an orthonormal basis of
the source. **Stated over abstract spaces on purpose**: every step is `map_sum`/`map_smul` on a
`Finset.sum`, which will not `rw` on a `TangentSpace`-typed sum (it picks `E`'s own
`AddCommMonoid`), so the computation is done here and applied with `exact`. -/
theorem conj_expansion_aux {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis κ ℝ F) (A₀ : F →L[ℝ] F) (P : F ≃ₗᵢ[ℝ] G) (v : G) :
    P (A₀ (P.symm v)) = ∑ i, ∑ j, ((⟪b i, A₀ (b j)⟫ : ℝ) * (⟪P (b j), v⟫ : ℝ)) • P (b i) := by
  have hsym : P.symm v = ∑ j, (⟪P (b j), v⟫ : ℝ) • b j := by
    conv_lhs => rw [← b.sum_repr' (P.symm v)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← P.inner_map_map (b j) (P.symm v), P.apply_symm_apply]
  have h1 : A₀ (∑ j, (⟪P (b j), v⟫ : ℝ) • b j) = ∑ j, (⟪P (b j), v⟫ : ℝ) • A₀ (b j) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ ↦ map_smul _ _ _
  have h2 : P (∑ j, (⟪P (b j), v⟫ : ℝ) • A₀ (b j))
      = ∑ j, (⟪P (b j), v⟫ : ℝ) • P (A₀ (b j)) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ ↦ map_smul _ _ _
  have h3 : ∀ j, P (A₀ (b j)) = ∑ i, (⟪b i, A₀ (b j)⟫ : ℝ) • P (b i) := fun j ↦ by
    conv_lhs => rw [← b.sum_repr' (A₀ (b j))]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
  calc P (A₀ (P.symm v))
      = ∑ j, (⟪P (b j), v⟫ : ℝ) • P (A₀ (b j)) := by rw [hsym, h1, h2]
    _ = ∑ j, ∑ i, ((⟪b i, A₀ (b j)⟫ : ℝ) * (⟪P (b j), v⟫ : ℝ)) • P (b i) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [h3 j, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul, mul_comm]
    _ = ∑ i, ∑ j, ((⟪b i, A₀ (b j)⟫ : ℝ) * (⟪P (b j), v⟫ : ℝ)) • P (b i) := Finset.sum_comm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **The transported endomorphism IS conjugation by the transport isometry.**

This is the identification that ties this file to `IveyParallel.lean`: there the pinching set
is shown invariant under conjugation by *any* fibre isometry, hence under parallel transport,
and here the parallel `End(TM)` field is shown to be exactly that conjugate. Without it the
two results would be about different objects. -/
theorem endoAlong_eq_endoConj (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀))
    {fr : ι → Π u : ℝ, TangentSpace I (γ u)} {u : ℝ}
    (P : TangentSpace I (γ t₀) ≃ₗᵢ[ℝ] TangentSpace I (γ u)) (hP : ∀ i, P (b i) = fr i u) :
    endoAlong b A₀ fr u = endoConj P A₀ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [endoAlong_apply', endoConj_apply,
    conj_expansion_aux (F := TangentSpace I (γ t₀)) (G := TangentSpace I (γ u)) b A₀ P v]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hP i, hP j]

/-- **Parallel transport on `End(TM)`.** For every endomorphism of one fibre there is a
parallel morphism field along the curve through it.

This is the piece the cross-fibre half of the bundle maximum principle was missing: the
tested direction is an endomorphism of a *single* fibre, and comparing it with neighbouring
fibres asks for it to be carried along, isometrically for the Hilbert–Schmidt metric and
without moving its spectrum. -/
theorem exists_isParallelAlongSection_end
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    (ht₀ : t₀ ∈ s) [Nonempty ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀)) :
    ∃ A : Π u : ℝ, TangentSpace I (γ u) →L[ℝ] TangentSpace I (γ u),
      A t₀ = A₀ ∧
      (∀ u ∈ s, MDiffAlongSectionAt I (E →L[ℝ] E)
        (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) γ A u) ∧
      IsParallelAlongSection I (E →L[ℝ] E)
        (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) (homCov cov cov) γ A s := by
  obtain ⟨fr, hfr0, hfrd, hfrp, hbu⟩ :=
    exists_parallel_orthonormalBasis_along cov hmet hs hconn hγ hγv ht₀ b
  exact ⟨endoAlong b A₀ fr, endoAlong_self b A₀ hfr0,
    fun w hw ↦ mdiffAlongSectionAt_endoAlong cov hmet b A₀ (hγ w hw) fun i ↦ hfrd i w hw,
    isParallelAlongSection_endoAlong cov hmet hs hγ b A₀ hfrd hfrp hbu⟩

/-- **Hamilton's pinching set travels with the transported endomorphism.**

The composition the whole `End(TM)` line was for, and the falsification check on it: the
parallel field of `exists_isParallelAlongSection_end` lies in the pinching set at one time
exactly when it does at another. `IveyParallel.lean` proves the set invariant under
conjugation by an *abstract* fibre isometry; `endoAlong_eq_endoConj` says the parallel field
is exactly that conjugate, so the two statements are about the same object. -/
theorem exists_isParallelAlongSection_end_mem_iveyEndoSet
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    (ht₀ : t₀ ∈ s) {t : ℝ} (ht : t ∈ s) [Nonempty ι]
    [Nontrivial (TangentSpace I (γ t₀))] [FiniteDimensional ℝ (TangentSpace I (γ t₀))]
    [Nontrivial (TangentSpace I (γ t))] [FiniteDimensional ℝ (TangentSpace I (γ t))]
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀)))
    (A₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀)) :
    ∃ A : Π u : ℝ, TangentSpace I (γ u) →L[ℝ] TangentSpace I (γ u),
      A t₀ = A₀ ∧
      (∀ u ∈ s, MDiffAlongSectionAt I (E →L[ℝ] E)
        (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) γ A u) ∧
      IsParallelAlongSection I (E →L[ℝ] E)
        (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) (homCov cov cov) γ A s ∧
      (A t ∈ Pinching.iveyEndoSet (TangentSpace I (γ t))
        ↔ A₀ ∈ Pinching.iveyEndoSet (TangentSpace I (γ t₀))) := by
  obtain ⟨fr, hfr0, hfrd, hfrp, hbu⟩ :=
    exists_parallel_orthonormalBasis_along cov hmet hs hconn hγ hγv ht₀ b
  obtain ⟨P, hP⟩ := exists_parallelTransportIsometry_global cov hmet hs hconn hγ hγv ht₀ ht
  have hPb : ∀ i, P (b i) = fr i t := fun i ↦ by
    rw [← hfr0 i, ← hP (fr i) (hfrd i) (hfrp i)]
  refine ⟨endoAlong b A₀ fr, endoAlong_self b A₀ hfr0,
    fun w hw ↦ mdiffAlongSectionAt_endoAlong cov hmet b A₀ (hγ w hw) fun i ↦ hfrd i w hw,
    isParallelAlongSection_endoAlong cov hmet hs hγ b A₀ hfrd hfrp hbu, ?_⟩
  rw [endoAlong_eq_endoConj b A₀ P hPb]
  exact Pinching.mem_iveyEndoSet_conj_iff P A₀

end Transport

end RicciFlowBlueprint
