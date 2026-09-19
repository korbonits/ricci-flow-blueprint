/-
**The Ricci form and the scalar curvature are smooth.**

`RicciForm.lean` makes `Ric` a genuine bilinear form and `scal` a genuine metric trace on any
manifold, but says nothing about how they vary with the point. That gap is load-bearing:
`ScalarPreservation.lean` and `ScalarLowerBound.lean` both carry
`ContMDiffAt I 𝓘(ℝ,ℝ) 2 (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x` as an **explicit
hypothesis**, because nothing in the development proved it. This file proves it.

**The one real obstacle is locality, and the fix is to globalise the frame first.** `Ric` is a
trace, so it is computed by an orthonormal frame (`ricci_eq_sum_inner_frame`); but a frame is
local, while every smoothness lemma in the curvature tower (`contMDiff_curvature`,
`contMDiff_curvature_two`) is stated for **globally** `C^k` sections. So
`exists_orthonormal_frame_on_open` globalises the trivialisation's orthonormal frame one
section at a time — which gives agreement only *near* the point — and then intersects the
finitely many agreement sets and takes the interior, exactly as `exists_frame_on_open` does in
`CovariantAlongCurve.lean`. The globalised frame is orthonormal on a whole **open**
neighbourhood, so the frame sum computes `Ric` at every point of it, and a germ statement is
all that smoothness needs.

After that the proof is two lines: each summand `⟪R(Fr i, V)W, Fr i⟫` is smooth by
`contMDiff_curvature` and `ContMDiffAt.inner_bundle'`, and `scal` is the same sum with
`V = W = Fr i`.

**Levels.** The last slot is the expensive one at every level of this tower, so the `C¹`
statement runs `C²/C²/C³` and the `C²` statement `C³/C³/C⁴`, with the frame one level above
the fields it feeds. The two are twin proofs rather than one statement at a variable level,
for the reason recorded in `CurvatureDeriv.lean`: `ContMDiffAt.mlieBracket_vectorField` is
indexed by `ℕ∞` while `ContMDiff` is indexed by `ℕ∞ω`, and a variable level costs more cast
bookkeeping than the copy.

Gotchas: `Module.Basis.orthonormalFrame` applied to the tangent bundle infers
`Bundle.Trivial M E` for the bundle and then reports a *topology* mismatch on the total space
— the lean4#14949 family; pin the frame's type with an ascribed existential
(`∃ fr : Fin _ → Π y : M, TangentSpace I y, fr = bE.orthonormalFrame e`) and rewrite.
`exists_contMDiff_eventuallyEq` needs `[T2Space M]`. And `contMDiff_curvature` wants
`[ContMDiffCovariantDerivative cov 2]`, `contMDiff_curvature_two` wants `3` — one more than
the level of the curvature section they produce.
-/
import RicciFlowBlueprint.CurvatureDeriv
import RicciFlowBlueprint.EndBundleMetric
import RicciFlowBlueprint.RicciForm
import RicciFlowBlueprint.Scalar

open Bundle Filter Manifold
open scoped Manifold ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 4

/-- **A globally `C^n` frame, orthonormal on a whole neighbourhood.** The local orthonormal
frame of a trivialisation is globalised one section at a time, which gives agreement only
*near* the point; intersecting the finitely many agreement sets and taking the interior
recovers an open set, exactly as `exists_frame_on_open` does for a plain local frame. -/
theorem exists_orthonormal_frame_on_open {n : ℕ∞}
    [ContMDiffVectorBundle (n : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x) I]
    [IsContMDiffRiemannianBundle I (n : ℕ∞ω) E (fun (x : M) ↦ TangentSpace I x)]
    [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
    [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
    (y₀ : M) :
    ∃ (U : Set M) (Fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y),
      IsOpen U ∧ y₀ ∈ U ∧ (∀ i, CMDiff (n : ℕ∞ω) (T% (Fr i))) ∧
      ∀ y ∈ U, ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
        ∀ i, Fr i y = b i := by
  classical
  set e := trivializationAt E (fun y : M ↦ TangentSpace I y) y₀ with he
  have hy₀ : y₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ y₀
  set bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbE
  obtain ⟨fr, hfrdef⟩ : ∃ fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      fr = bE.orthonormalFrame e := ⟨_, rfl⟩
  have hs : IsOrthonormalFrameOn I E 1 fr e.baseSet := by
    rw [hfrdef]; exact Module.Basis.orthonormalFrame_isOrthonormalFrameOn (n := 1) bE e
  have hloc : ∀ i, ∃ τ : Π y : M, TangentSpace I y,
      CMDiff (n : ℕ∞ω) (T% τ) ∧ τ =ᶠ[𝓝 y₀] fr i := fun i ↦
    exists_contMDiff_eventuallyEq (n := n) (e.open_baseSet.mem_nhds hy₀)
      (hfrdef ▸ Module.Basis.contMDiffOn_orthonormalFrame_baseSet (n := (n : ℕ∞ω)) bE e i)
  choose Fr hFr hFreq using hloc
  refine ⟨interior {y | ∀ i, Fr i y = fr i y} ∩ e.baseSet, Fr,
    isOpen_interior.inter e.open_baseSet, ⟨?_, hy₀⟩, hFr, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    exact Filter.eventually_all.mpr hFreq
  · intro y hy
    obtain ⟨b, hb⟩ :=
      CovariantDerivative.exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy.2
    exact ⟨b, fun i ↦ by rw [(interior_subset hy.1) i, hb i]⟩

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

omit [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 3] in
/-- **The Ricci form is `C¹` against `C²`/`C³` fields.** The frame is globalised first, so
every hypothesis of `contMDiff_curvature` is a global one; the frame sum computes `Ric` only
on the neighbourhood where the globalised frame is still orthonormal, which is all a germ
statement needs. -/
theorem contMDiffAt_ricciForm_apply {V W : Π y : M, TangentSpace I y} {x₀ : M}
    (hV : CMDiff 2 (T% V)) (hW : CMDiff 3 (T% W)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun y ↦ cov.ricciForm y (V y) (W y)) x₀ := by
  obtain ⟨U, Fr, hU, hx₀, hFr, hb⟩ :=
    exists_orthonormal_frame_on_open (I := I) (n := 2) (M := M) x₀
  have hFr1 : ∀ i, CMDiff 1 (T% (Fr i)) := fun i ↦ (hFr i).of_le (by norm_num)
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ ∑ i, ⟪cov.curvature (Fr i) V W y, Fr i y⟫) x₀ := by
    refine ContMDiffAt.sum (fun i _ ↦ ?_)
    exact ContMDiffAt.inner_bundle' (cov.contMDiff_curvature (hFr i) hV hW x₀) (hFr1 i x₀)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀] with y hy
  obtain ⟨b, hbb⟩ := hb y hy
  rw [cov.ricciForm_apply, cov.ricciAt_eq hV (hW.of_le (by norm_num))]
  exact cov.ricci_eq_sum_inner_frame (hW.of_le (by norm_num)) b
    (fun i ↦ ((hFr i) y).mdifferentiableAt (by norm_num)) hbb

omit [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 3] in
/-- **The scalar curvature is `C¹`.** Its smoothness is currently an explicit hypothesis in
`ScalarPreservation.lean` and `ScalarLowerBound.lean`; this discharges it. -/
theorem contMDiffAt_scalarCurvatureAt (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun y ↦ cov.scalarCurvatureAt y) x₀ := by
  obtain ⟨U, Fr, hU, hx₀, hFr, hb⟩ :=
    exists_orthonormal_frame_on_open (I := I) (n := 3) (M := M) x₀
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ ∑ i, cov.ricciForm y (Fr i y) (Fr i y)) x₀ :=
    ContMDiffAt.sum fun i _ ↦
      cov.contMDiffAt_ricciForm_apply ((hFr i).of_le (by norm_num)) (hFr i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀] with y hy
  obtain ⟨b, hbb⟩ := hb y hy
  rw [cov.scalarCurvatureAt_eq_sum_basis b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [cov.ricciForm_apply, hbb i]

omit [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **The Ricci form is `C²` against `C³`/`C⁴` fields.** The twin of
`contMDiffAt_ricciForm_apply` one derivative up: the last slot is the expensive one at every
level of this tower, so `W` runs at `C⁴`. -/
theorem contMDiffAt_ricciForm_apply_two {V W : Π y : M, TangentSpace I y} {x₀ : M}
    (hV : CMDiff 3 (T% V)) (hW : CMDiff 4 (T% W)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ cov.ricciForm y (V y) (W y)) x₀ := by
  obtain ⟨U, Fr, hU, hx₀, hFr, hb⟩ :=
    exists_orthonormal_frame_on_open (I := I) (n := 3) (M := M) x₀
  have hFr2 : ∀ i, CMDiff 2 (T% (Fr i)) := fun i ↦ (hFr i).of_le (by norm_num)
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) 2
      (fun y ↦ ∑ i, ⟪cov.curvature (Fr i) V W y, Fr i y⟫) x₀ := by
    refine ContMDiffAt.sum (fun i _ ↦ ?_)
    exact ContMDiffAt.inner_bundle' (cov.contMDiff_curvature_two (hFr i) hV hW x₀) (hFr2 i x₀)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀] with y hy
  obtain ⟨b, hbb⟩ := hb y hy
  rw [cov.ricciForm_apply,
    cov.ricciAt_eq (hV.of_le (by norm_num)) (hW.of_le (by norm_num))]
  exact cov.ricci_eq_sum_inner_frame (hW.of_le (by norm_num)) b
    (fun i ↦ ((hFr i) y).mdifferentiableAt (by norm_num)) hbb

omit [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **The scalar curvature is `C²`** — the form `ScalarPreservation.lean` and
`ScalarLowerBound.lean` assume. -/
theorem contMDiffAt_scalarCurvatureAt_two (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ cov.scalarCurvatureAt y) x₀ := by
  obtain ⟨U, Fr, hU, hx₀, hb⟩ :
      ∃ (U : Set M) (Fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y),
        IsOpen U ∧ x₀ ∈ U ∧ (∀ i, CMDiff 4 (T% (Fr i))) ∧
          ∀ y ∈ U, ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
            ∀ i, Fr i y = b i := by
    obtain ⟨U, Fr, h⟩ := exists_orthonormal_frame_on_open (I := I) (n := 4) (M := M) x₀
    exact ⟨U, Fr, h⟩
  obtain ⟨hFr, hbas⟩ := hb
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) 2
      (fun y ↦ ∑ i, cov.ricciForm y (Fr i y) (Fr i y)) x₀ :=
    ContMDiffAt.sum fun i _ ↦
      cov.contMDiffAt_ricciForm_apply_two ((hFr i).of_le (by norm_num)) (hFr i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀] with y hy
  obtain ⟨b, hbb⟩ := hbas y hy
  rw [cov.scalarCurvatureAt_eq_sum_basis b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [cov.ricciForm_apply, hbb i]

omit [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 3] in
/-- The scalar curvature is `C¹` as a function on `M`. -/
theorem contMDiff_scalarCurvatureAt :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (fun y : M ↦ cov.scalarCurvatureAt y) :=
  fun x₀ ↦ cov.contMDiffAt_scalarCurvatureAt x₀

omit [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- The scalar curvature is `C²` as a function on `M`. -/
theorem contMDiff_scalarCurvatureAt_two :
    ContMDiff I 𝓘(ℝ, ℝ) 2 (fun y : M ↦ cov.scalarCurvatureAt y) :=
  fun x₀ ↦ cov.contMDiffAt_scalarCurvatureAt_two x₀

end CovariantDerivative
