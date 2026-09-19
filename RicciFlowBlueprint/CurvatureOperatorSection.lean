/-
**The dimension-three curvature operator as a `C²` section of `End(TM)`.**

`CurvatureOperatorThree.lean` builds `Rm₃ = scal · Id − 2 Ric♯` pointwise; this file makes it
a section, which is what a maximum principle can be run on. With
`contMDiff_curvatureOperator_endTangent` it is a `C²` section of the *synonym*
`EndTangent` — the bundle that carries the Hilbert–Schmidt metric and the induced
connection — so the object Hamilton–Ivey needs now exists with all its structure.

**Two bricks.**

* **`contMDiffAt_end_section_of_symmL`** — a section of `End(TM)` is `C^n` as soon as its
  values on the trivialisation's local frame are. This is the converse of
  `ContMDiffAt.clm_bundle_apply`, and it is what a *constructed* endomorphism field needs:
  `contMDiffAt_hom_bundle` reduces to the coordinate representative, and for a `Hom(V,V)`
  section that representative is literally the trivialisation coordinate of the section
  `y ↦ A y (e.symmL y u)`, so **there is no coordinate change to control** — one rewrite of
  `inCoordinates` and `continuousLinearMapAt_apply_of_mem`.
* **`contMDiffAt_ricciSharp_apply`** — `Ric♯` applied to a `C³` field is a `C²` section, and
  **the Riesz isomorphism is never differentiated**. A section of a Riemannian bundle is
  `C^n` as soon as its inner products with a local frame are
  (`contMDiffAt_section_of_inner_localFrame`), and those inner products *are* the Ricci form,
  whose smoothness is `RicciSection.lean`. So the sharp costs nothing.

Everything else is `ContMDiffAt.smul_section` / `.const_smul_section` / `.sub_section` on
`curvatureOperator_apply`.

Gotchas: `contMDiffAt_section_of_inner_localFrame` infers `E`'s own norm for the fibre unless
`(V := fun z : M ↦ TangentSpace I z)` is passed — the lean4#14949 family; the local frame is
only locally smooth, so it is globalised by `exists_contMDiff_eventuallyEq` and the germ
recovered by `congr_of_eventuallyEq`, as everywhere in this layer; and `T%` of a `Pi`-smul
needs a `show` before the rewrite lands.
-/
import RicciFlowBlueprint.RicciSection
import RicciFlowBlueprint.CurvatureOperatorThree

open Bundle Filter Manifold ContinuousLinearMap
open scoped Manifold ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace RicciFlowBlueprint

section Criterion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {n : ℕ∞ω} [ContMDiffVectorBundle n E (fun (x : M) ↦ TangentSpace I x) I]
  {ι : Type*} [Fintype ι]

set_option maxSynthPendingDepth 4

omit [ContMDiffVectorBundle n E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **A section of `End(TM)` is `C^n` as soon as its values on the trivialisation's local
frame are.** The converse of `ContMDiffAt.clm_bundle_apply`, and the criterion a *constructed*
endomorphism field needs: `contMDiffAt_hom_bundle` reduces to the coordinate representative,
and for a `Hom(V,V)` section that representative is the trivialisation coordinate of the
section `y ↦ A y (e.symmL y u)` — so there is no coordinate change to control. -/
theorem contMDiffAt_end_section_of_symmL
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x₀ : M} (b : Module.Basis ι ℝ E)
    (h : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y
        (A y ((trivializationAt E (fun z : M ↦ TangentSpace I z) x₀).symmL ℝ y (b i)))) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y (A y)) x₀ := by
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  refine contMDiffAt_clm_of_basis b (fun i ↦ ?_)
  have hi := (contMDiffAt_totalSpace.mp (h i)).2
  refine hi.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
  rw [ContinuousLinearMap.inCoordinates]
  simp only [coe_comp, Function.comp_apply]
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy _

end Criterion

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

set_option maxSynthPendingDepth 4

omit [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`Ric♯` applied to a `C³` field is a `C²` section.** The Riesz isomorphism is not
differentiated: a section of a Riemannian bundle is `C^n` as soon as its inner products with
a local frame are (`contMDiffAt_section_of_inner_localFrame`), and those inner products *are*
the Ricci form. -/
theorem contMDiffAt_ricciSharp_apply {X : Π y : M, TangentSpace I y} {x₀ : M}
    (hX : CMDiff 3 (T% X)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (fun y ↦ cov.ricciSharp y (X y))) x₀ := by
  classical
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  set bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbE
  refine contMDiffAt_section_of_inner_localFrame (n := 2)
    (V := fun z : M ↦ TangentSpace I z) bE (fun i ↦ ?_)
  obtain ⟨W, hW, hWeq⟩ : ∃ τ : Π y : M, TangentSpace I y,
      CMDiff 4 (T% τ) ∧ τ =ᶠ[𝓝 x₀] e.localFrame bE i :=
    exists_contMDiff_eventuallyEq (n := 4) (e.open_baseSet.mem_nhds hx₀)
      (e.contMDiffOn_localFrame_baseSet 4 bE i)
  have hmain : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ cov.ricciForm y (X y) (W y)) x₀ :=
    cov.contMDiffAt_ricciForm_apply_two hX hW
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hWeq] with y hy
  rw [cov.inner_ricciSharp, hy]

/-- **Hamilton's curvature operator is a `C²` section of `End(TM)`.** Everything it is built
from is now known smooth: the scalar curvature by `RicciSection.lean`, and `Ric♯` because the
Riesz isomorphism never has to be differentiated. -/
theorem contMDiffAt_curvatureOperator (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y
        (cov.curvatureOperator y)) x₀ := by
  classical
  set e := trivializationAt E (fun z : M ↦ TangentSpace I z) x₀ with he
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  set bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbE
  refine contMDiffAt_end_section_of_symmL (n := 2) bE (fun i ↦ ?_)
  obtain ⟨W, hW, hWeq⟩ : ∃ τ : Π y : M, TangentSpace I y,
      CMDiff 3 (T% τ) ∧ τ =ᶠ[𝓝 x₀] e.localFrame bE i :=
    exists_contMDiff_eventuallyEq (n := 3) (e.open_baseSet.mem_nhds hx₀)
      (e.contMDiffOn_localFrame_baseSet 3 bE i)
  have hW2 : CMDiffAt 2 (T% W) x₀ := (hW.of_le (by norm_num)) x₀
  have hsmul : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
      (T% (fun y ↦ cov.scalarCurvatureAt y • W y)) x₀ :=
    ContMDiffAt.smul_section (cov.contMDiffAt_scalarCurvatureAt_two x₀) hW2
  have hsharp : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
      (T% (fun y ↦ (2 : ℝ) • cov.ricciSharp y (W y))) x₀ :=
    ContMDiffAt.const_smul_section (a := (2 : ℝ)) (cov.contMDiffAt_ricciSharp_apply hW)
  have hsub : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
      (T% (fun y ↦ cov.scalarCurvatureAt y • W y - (2 : ℝ) • cov.ricciSharp y (W y))) x₀ :=
    ContMDiffAt.sub_section hsmul hsharp
  refine hsub.congr_of_eventuallyEq ?_
  filter_upwards [hWeq, e.open_baseSet.mem_nhds hx₀] with y hy hy'
  have hval : e.symmL ℝ y (bE i) = W y := by
    rw [hy, RicciFlowBlueprint.localFrame_eq_symmL' e bE hy' i]
  show TotalSpace.mk' E y _ = TotalSpace.mk' E y _
  rw [hval, cov.curvatureOperator_apply]

/-- Hamilton's curvature operator is a `C²` section of `End(TM)`. -/
theorem contMDiff_curvatureOperator :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y
        (cov.curvatureOperator y)) :=
  fun x₀ ↦ cov.contMDiffAt_curvatureOperator x₀

/-- **`Rm₃` is a `C²` section of the type synonym too**, by the same definitional transport
that carries the Hilbert–Schmidt metric across — which is what lets it be fed to the
general-bundle layer, where `EndTangent` is the bundle that has a metric. -/
theorem contMDiff_curvatureOperator_endTangent :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := RicciFlowBlueprint.EndTangent I (M := M)) y (cov.curvatureOperator y)) :=
  cov.contMDiff_curvatureOperator

end CovariantDerivative
