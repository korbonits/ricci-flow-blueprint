/-
**The induced connection on a Hom bundle is `C^k`.**
-/
import RicciFlowBlueprint.HomBundle
import RicciFlowBlueprint.BundleNormalSection

open Bundle Filter Manifold ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

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

section Criterion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {W₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ W₁)]
  [∀ x : M, AddCommGroup (W₁ x)] [∀ x : M, Module ℝ (W₁ x)]
  [∀ x : M, TopologicalSpace (W₁ x)] [FiberBundle F₁ W₁] [VectorBundle ℝ F₁ W₁]
  {W₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ W₂)]
  [∀ x : M, AddCommGroup (W₂ x)] [∀ x : M, Module ℝ (W₂ x)]
  [∀ x : M, TopologicalSpace (W₂ x)] [∀ x : M, IsTopologicalAddGroup (W₂ x)]
  [∀ x : M, ContinuousSMul ℝ (W₂ x)] [FiberBundle F₂ W₂] [VectorBundle ℝ F₂ W₂]
  {n : ℕ∞ω} {ι : Type*} [Fintype ι]

set_option maxSynthPendingDepth 4

omit [IsManifold I ω M] in
/-- **A section of `Hom(W₁,W₂)` is `C^n` as soon as its values on the source trivialisation's
local frame are.** The converse of `ContMDiffAt.clm_bundle_apply`, and the criterion a
*constructed* bundle morphism needs: `contMDiffAt_hom_bundle` reduces to the coordinate
representative, and that representative is the target trivialisation's coordinate of the
section `y ↦ A y (e₁.symmL y u)` — so there is no coordinate change to control. -/
theorem contMDiffAt_hom_section_of_symmL
    {A : Π y : M, W₁ y →L[ℝ] W₂ y} {x₀ : M} (b : Module.Basis ι ℝ F₁)
    (h : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) n
      (fun y ↦ TotalSpace.mk' F₂ y (A y ((trivializationAt F₁ W₁ x₀).symmL ℝ y (b i)))) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂)
        (E := fun z : M ↦ W₁ z →L[ℝ] W₂ z) y (A y)) x₀ := by
  set e₂ := trivializationAt F₂ W₂ x₀ with he₂
  have hx₀ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ W₂ x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  refine contMDiffAt_clm_of_basis b (fun i ↦ ?_)
  have hi := (contMDiffAt_totalSpace.mp (h i)).2
  refine hi.congr_of_eventuallyEq ?_
  filter_upwards [e₂.open_baseSet.mem_nhds hx₀] with y hy
  rw [ContinuousLinearMap.inCoordinates]
  simp only [coe_comp, Function.comp_apply]
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e₂ hy _

end Criterion

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x : M, AddCommGroup (V₁ x)] [∀ x : M, Module ℝ (V₁ x)]
  [∀ x : M, TopologicalSpace (V₁ x)] [∀ x : M, IsTopologicalAddGroup (V₁ x)]
  [∀ x : M, ContinuousSMul ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I] [ContMDiffVectorBundle 2 F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x : M, AddCommGroup (V₂ x)] [∀ x : M, Module ℝ (V₂ x)]
  [∀ x : M, TopologicalSpace (V₂ x)] [∀ x : M, IsTopologicalAddGroup (V₂ x)]
  [∀ x : M, ContinuousSMul ℝ (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)
  [ContMDiffCovariantDerivative cov₁ 1] [ContMDiffCovariantDerivative cov₂ 1]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]

set_option maxSynthPendingDepth 4

omit [CompleteSpace E] in
/-- **The induced connection on a Hom bundle is `C¹`.**

`homCov` was built as a `CovariantDerivative` but nothing said it was *smooth*, and
`laplacianSection` — hence the whole `∇²`/`Δ`/Bochner layer — needs exactly that. Two
applications of `contMDiffAt_hom_section_of_symmL`, one per `Hom`, reduce the claim to the
two terms of `∇A = ∇²(Aσ) − A(∇¹σ)` on a pair of local frames, and each is
`contMDiff_cov_apply_section` composed with `ContMDiff.clm_bundle_apply`. The frames are
globalised first, for `RicciSection.lean`'s reason: every smoothness lemma in the covariant
layer is stated for *globally* `C^k` sections, and smoothness is a germ property. -/
theorem contMDiffCovariantDerivative_homCov :
    ContMDiffCovariantDerivative (homCov cov₁ cov₂) 1 := by
  refine ⟨⟨fun {A} hA ↦ ?_⟩⟩
  rw [contMDiffOn_univ] at hA ⊢
  have hA2 : CMDiff 2 (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun z : M ↦ V₁ z →L[ℝ] V₂ z) y (A y)) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num] at hA
    exact hA
  intro x₀
  set bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbE
  refine contMDiffAt_hom_section_of_symmL (W₁ := fun z : M ↦ TangentSpace I z)
    (W₂ := fun z : M ↦ V₁ z →L[ℝ] V₂ z) bE (fun i ↦ ?_)
  set bF : Module.Basis (Fin (Module.finrank ℝ F₁)) ℝ F₁ := Module.finBasis ℝ F₁ with hbF
  refine contMDiffAt_hom_section_of_symmL (W₁ := V₁) (W₂ := V₂) bF (fun j ↦ ?_)
  set eT := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with heT
  set eV := trivializationAt F₁ V₁ x₀ with heV
  have hxT : x₀ ∈ eT.baseSet := mem_baseSet_trivializationAt E _ x₀
  have hxV : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F₁ V₁ x₀
  -- globalise the two local frames: every smoothness lemma below is a global statement
  obtain ⟨W, hW, hWeq⟩ : ∃ τ : Π y : M, TangentSpace I y,
      CMDiff 2 (T% τ) ∧ ∀ᶠ y in 𝓝 x₀, τ y = eT.symmL ℝ y (bE i) := by
    obtain ⟨τ, hτ, hτeq⟩ := exists_contMDiff_eventuallyEq_of_bundle (I := I) E
      (V := fun z : M ↦ TangentSpace I z) (n := 2) (eT.open_baseSet.mem_nhds hxT)
      (eT.contMDiffOn_localFrame_baseSet 2 bE i)
    refine ⟨τ, hτ, ?_⟩
    filter_upwards [hτeq, eT.open_baseSet.mem_nhds hxT] with y h1 h2
    rw [h1, localFrame_eq_symmL' eT bE h2 i]
  obtain ⟨S, hS, hSeq⟩ : ∃ τ : Π y : M, V₁ y,
      CMDiff 2 (T% τ) ∧ ∀ᶠ y in 𝓝 x₀, τ y = eV.symmL ℝ y (bF j) := by
    obtain ⟨τ, hτ, hτeq⟩ := exists_contMDiff_eventuallyEq_of_bundle (I := I) F₁
      (V := V₁) (n := 2) (eV.open_baseSet.mem_nhds hxV)
      (eV.contMDiffOn_localFrame_baseSet 2 bF j)
    refine ⟨τ, hτ, ?_⟩
    filter_upwards [hτeq, eV.open_baseSet.mem_nhds hxV] with y h1 h2
    rw [h1, localFrame_eq_symmL' eV bF h2 j]
  -- the two terms of `∇A` are separately `C¹`
  have hcast : ((1 : ℕ∞ω) + 1) = 2 := by norm_num
  have hAS : CMDiff 2 (T% (fun z : M ↦ A z (S z))) := hA2.clm_bundle_apply hS
  have h1 : CMDiff 1 (T% (fun y : M ↦ cov₂ (fun z ↦ A z (S z)) y (W y))) :=
    contMDiff_cov_apply_section cov₂ (hcast ▸ hAS) (hW.of_le (by norm_num))
  have h2 : CMDiff 1 (T% (fun y : M ↦ cov₁ S y (W y))) :=
    contMDiff_cov_apply_section cov₁ (hcast ▸ hS) (hW.of_le (by norm_num))
  have h3 : CMDiff 1 (T% (fun y : M ↦ A y (cov₁ S y (W y)))) :=
    (hA2.of_le (by norm_num)).clm_bundle_apply h2
  have hsub : CMDiff 1 (T% (fun y : M ↦
      cov₂ (fun z ↦ A z (S z)) y (W y) - A y (cov₁ S y (W y)))) :=
    h1.sub_section h3
  refine (hsub x₀).congr_of_eventuallyEq ?_
  filter_upwards [hWeq, hSeq] with y hy1 hy2
  show TotalSpace.mk' F₂ y _ = TotalSpace.mk' F₂ y _
  rw [← hy1, ← hy2,
    homCov_apply (isMDiffHomAt_of_section ((hA2 y).mdifferentiableAt (by norm_num)))
      ((hW y).mdifferentiableAt (by norm_num)) ((hS y).mdifferentiableAt (by norm_num))]
  rfl

omit [CompleteSpace E] in
/-- **The induced connection on `End(TM)` is `C¹`** — the instance
`BundleMaximumPrinciple.lean` needs to accept `End(TM)`. -/
instance contMDiffCovariantDerivative_endCov
    [ContMDiffVectorBundle 1 E (fun (y : M) ↦ TangentSpace I y) I]
    (cov : CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    [ContMDiffCovariantDerivative cov 1] :
    ContMDiffCovariantDerivative (endCov cov) 1 :=
  contMDiffCovariantDerivative_homCov cov cov

end CovariantDerivative
