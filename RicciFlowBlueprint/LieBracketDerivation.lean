/-
The Lie bracket acts as a derivation on functions.

This is the identity `[V, W] f = V (W f) - W (V f)`. It is missing from Mathlib
in both the vector-space and the manifold setting, and the manifold version is
the last obstruction to third-slot tensoriality of the curvature operator (see
`RicciFlowBlueprint.Curvature`), hence to defining Ricci curvature at all.

The vector-space case is the mathematical content: the two second-derivative
terms cancel by symmetry of the second derivative, and what survives is exactly
the bracket. The manifold case (`mlieBracket_apply_fun` below) transports this
through `extChartAt`: both sides of the identity are rewritten as chart-side
data on `range I` — `mvfderiv` at points near `x` becomes `fderivWithin` of
`f ∘ (extChartAt I x).symm` composed with the chart differential, vector fields
become their `mpullbackWithin` through the inverse chart — after which the
`Within` form of the vector-space identity (with second-derivative symmetry
supplied by `ContDiffWithinAt.isSymmSndFDerivWithinAt` on `range I`) closes the
goal.
-/
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Notation

open scoped Manifold

namespace VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- BENCH: lie-bracket-derivation
-- The Lie bracket acts as a derivation on functions: `[V,W] f = V (W f) - W (V f)`.
theorem lieBracket_apply_fun
    {f : E → F} {f' : E → E →L[𝕜] F} {f'' : E →L[𝕜] E →L[𝕜] F}
    {V W : E → E} {V' W' : E →L[𝕜] E} {x : E}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hf' : HasFDerivAt f' f'' x)
    (hV : HasFDerivAt V V' x) (hW : HasFDerivAt W W' x) :
    (fderiv 𝕜 (fun y ↦ f' y (W y)) x) (V x)
      - (fderiv 𝕜 (fun y ↦ f' y (V y)) x) (W x)
      = f' x (lieBracket 𝕜 V W x) := by
  have h1 : HasFDerivAt (fun y ↦ f' y (W y)) ((f' x).comp W' + f''.flip (W x)) x :=
    hf'.clm_apply hW
  have h2 : HasFDerivAt (fun y ↦ f' y (V y)) ((f' x).comp V' + f''.flip (V x)) x :=
    hf'.clm_apply hV
  have hsymm : f'' (V x) (W x) = f'' (W x) (V x) :=
    second_derivative_symmetric hf hf' (V x) (W x)
  rw [h1.fderiv, h2.fderiv, lieBracket_eq]
  dsimp only
  rw [hV.fderiv, hW.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub]
  rw [hsymm]
  abel

section ModelSpace

/-- On the model space, `mvfderiv` (the derivative of a map into a normed space,
which `d%` denotes) is just `fderiv`. The `fromTangentSpace` identification is
the identity. -/
theorem mvfderiv_eq_fderiv (g : E → F) (y : E) :
    mvfderiv 𝓘(𝕜, E) g y = fderiv 𝕜 g y := by
  simp [mvfderiv, mfderiv_eq_fderiv]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- On the model space the manifold bracket is the vector-space bracket. The
transparency option is needed because `TangentSpace 𝓘(𝕜,E) x` is defeq to `E`
for elaboration but not for instance search. -/
theorem mlieBracket_eq_lieBracket
    {V W : Π x : E, TangentSpace 𝓘(𝕜, E) x} {x : E} :
    mlieBracket 𝓘(𝕜, E) V W x = lieBracket 𝕜 V W x := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin,
    lieBracketWithin_univ]

/-- The same collapse for plain `E → E` vector fields. `HasFDerivAt` needs a
non-dependent codomain while `mlieBracketWithin` needs the dependent one; the
two are defeq, and term-mode application bridges them where `simp`/`rw` cannot. -/
theorem mlieBracket_eq_lieBracket' {V W : E → E} {x : E} :
    mlieBracket 𝓘(𝕜, E) V W x = lieBracket 𝕜 V W x :=
  mlieBracket_eq_lieBracket

/-- The model-space case of "the Lie bracket acts as a derivation on functions",
in manifold notation: `[V,W] f = V (W f) - W (V f)` with `mvfderiv` and
`mlieBracket` over `𝓘(𝕜, E)`.

Assembly note: the collapse lemmas must be applied at the *fully applied* level
(the whole `mvfderiv … y (v)` term), where the goal lives in `F` and no
`TangentSpace`-vs-`E` instance path survives. `simp only` does this and also
rewrites under the binder `fun y ↦ …`, where `rw` cannot reach; `hfd` is needed
in the same pass to turn the inner `fderiv 𝕜 f y` into `f' y` under that binder. -/
theorem mlieBracket_apply_fun_model
    {f : E → F} {f' : E → E →L[𝕜] F} {f'' : E →L[𝕜] E →L[𝕜] F}
    {V W : E → E} {V' W' : E →L[𝕜] E} {x : E}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hf' : HasFDerivAt f' f'' x)
    (hV : HasFDerivAt V V' x) (hW : HasFDerivAt W W' x) :
    (mvfderiv 𝓘(𝕜, E) (fun y ↦ mvfderiv 𝓘(𝕜, E) f y (W y)) x) (V x)
      - (mvfderiv 𝓘(𝕜, E) (fun y ↦ mvfderiv 𝓘(𝕜, E) f y (V y)) x) (W x)
      = (mvfderiv 𝓘(𝕜, E) f x) (mlieBracket 𝓘(𝕜, E) V W x) := by
  have key := lieBracket_apply_fun hf hf' hV hW
  have hfd : ∀ y, fderiv 𝕜 f y = f' y := fun y ↦ (hf y).fderiv
  simp only [mvfderiv_eq_fderiv, mlieBracket_eq_lieBracket', hfd]
  exact key

end ModelSpace

section VectorSpaceWithin

open Set

/-- The `Within` form of `lieBracket_apply_fun`, with the second-derivative
symmetry supplied by `ContDiffWithinAt.isSymmSndFDerivWithinAt` (hence the
closure-of-interior hypothesis). This is the version that survives transport
through `extChartAt`, where everything lives on `range I`. -/
theorem lieBracketWithin_apply_fun
    {g : E → F} {V W : E → E} {u : Set E} {z : E}
    (hg : ContDiffWithinAt 𝕜 2 g u z)
    (hV : DifferentiableWithinAt 𝕜 V u z) (hW : DifferentiableWithinAt 𝕜 W u z)
    (hu : UniqueDiffOn 𝕜 u) (hz : z ∈ closure (interior u)) (h'z : z ∈ u) :
    (fderivWithin 𝕜 (fun y ↦ fderivWithin 𝕜 g u y (W y)) u z) (V z)
      - (fderivWithin 𝕜 (fun y ↦ fderivWithin 𝕜 g u y (V y)) u z) (W z)
      = fderivWithin 𝕜 g u z (lieBracketWithin 𝕜 V W u z) := by
  have hg' : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 g u) u z :=
    (hg.fderivWithin_right (m := 1) hu (by norm_num) h'z).differentiableWithinAt one_ne_zero
  have hsymm : IsSymmSndFDerivWithinAt 𝕜 g u z :=
    hg.isSymmSndFDerivWithinAt (by simp) hu hz h'z
  rw [fderivWithin_clm_apply (hu z h'z) hg' hW, fderivWithin_clm_apply (hu z h'z) hg' hV,
    lieBracketWithin_eq]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub]
  rw [hsymm (V z) (W z)]
  abel

end VectorSpaceWithin

section Manifold

open Set

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] [CompleteSpace E]

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- Chain rule expressing `mvfderiv` of `h ∘ extChartAt I x` through `fderivWithin` on
`range I`. The subtlety is that `h` need only be differentiable *within* `range I` (at a
boundary point of the model there is nothing more), so the composition must be taken with
`mfderivWithin_comp` and the fact that `extChartAt` maps everything into `range I`. -/
lemma mvfderiv_comp_extChartAt_apply {h : E → F} {x y : M}
    (hy : y ∈ (extChartAt I x).source)
    (hh : DifferentiableWithinAt 𝕜 h (range I) (extChartAt I x y)) (v : TangentSpace I y) :
    mvfderiv I (h ∘ (extChartAt I x)) y v
      = fderivWithin 𝕜 h (range I) (extChartAt I x y)
          (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y v) := by
  have hy' : y ∈ (chartAt H x).source := by rwa [← extChartAt_source I x]
  have hφ : MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) y := mdifferentiableAt_extChartAt hy'
  have hh' : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) h (range I) (extChartAt I x y) :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.2 hh
  have hmaps : (univ : Set M) ⊆ (extChartAt I x) ⁻¹' (range I) := by
    intro z _
    exact ⟨chartAt H x z, rfl⟩
  have comp : mfderiv I 𝓘(𝕜, F) (h ∘ (extChartAt I x)) y
      = (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, F) h (range I) (extChartAt I x y)).comp
          (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) := by
    rw [← mfderivWithin_univ, ← mfderivWithin_univ (f := (extChartAt I x))]
    exact mfderivWithin_comp y hh' hφ.mdifferentiableWithinAt hmaps (uniqueMDiffWithinAt_univ _)
  simp only [mvfderiv, comp, mfderivWithin_eq_fderivWithin]
  rfl

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- `mvfderiv` at any point `y` of the chart source around `x`, computed in the chart at
`x` — not just at the centre `x` itself, which is what the definitional unfolding gives.
This uniformity in `y` is what lets the *outer* derivative in `mlieBracket_apply_fun` see
a single chart-side function. -/
lemma mvfderiv_apply_eq_fderivWithin {f : M → F} {x y : M}
    (hy : y ∈ (extChartAt I x).source) (hf : MDifferentiableAt I 𝓘(𝕜, F) f y)
    (v : TangentSpace I y) :
    mvfderiv I f y v
      = fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x y)
          (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y v) := by
  have hev : f =ᶠ[nhds y] (f ∘ (extChartAt I x).symm) ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds' hy] with z hz
    show f z = f ((extChartAt I x).symm ((extChartAt I x) z))
    rw [(extChartAt I x).left_inv hz]
  have hg : DifferentiableWithinAt 𝕜 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x y) := by
    apply mdifferentiableWithinAt_iff_differentiableWithinAt.1
    have h1 : MDifferentiableWithinAt 𝓘(𝕜, E) I (extChartAt I x).symm (range I)
        (extChartAt I x y) :=
      mdifferentiableWithinAt_extChartAt_symm ((extChartAt I x).map_source hy)
    have h2 : MDifferentiableAt I 𝓘(𝕜, F) f ((extChartAt I x).symm (extChartAt I x y)) := by
      rw [(extChartAt I x).left_inv hy]; exact hf
    exact MDifferentiableAt.comp_mdifferentiableWithinAt
      (f := ((extChartAt I x).symm : E → M)) (extChartAt I x y) h2 h1
  have : mvfderiv I f y = mvfderiv I ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) y := by
    simp only [mvfderiv, hev.mfderiv_eq]
    congr 1
  rw [this, mvfderiv_comp_extChartAt_apply hy hg v]

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- Near `x`, the pullback through `(extChartAt I x).symm` of a vector field, evaluated at
the chart image point, is the pushforward of the vector field through the chart. -/
lemma eventually_mpullbackWithin_extChartAt_symm_apply {V : Π x : M, TangentSpace I x} {x : M} :
    ∀ᶠ y in nhds x, mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) (extChartAt I x y)
      = mfderiv I 𝓘(𝕜, E) (extChartAt I x) y (V y) := by
  have h := eventuallyEq_mpullback_mpullbackWithin_extChartAt (I := I) (s := univ) (x := x) V
  rw [nhdsWithin_univ] at h
  filter_upwards [h, extChartAt_source_mem_nhds (I := I) x] with y hVy hy
  rw [hVy, mpullback_apply, (isInvertible_mfderiv_extChartAt hy).self_apply_inverse]

omit [IsRCLikeNormedField 𝕜] [IsManifold I 2 M] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- `mvfderiv` only depends on the local germ of the function. -/
lemma mvfderiv_congr_of_eventuallyEq {h₁ h₂ : M → F} {y : M} (h : h₁ =ᶠ[nhds y] h₂) :
    mvfderiv I h₁ y = mvfderiv I h₂ y := by
  simp only [mvfderiv, h.mfderiv_eq]
  congr 1

set_option backward.isDefEq.respectTransparency false in
-- BENCH: lie-bracket-derivation-manifold
/-- The Lie bracket of vector fields on a manifold acts as a derivation on functions:
`[V,W] f = V (W f) - W (V f)`, with `mvfderiv` as the action of vector fields on
`F`-valued functions.

Hypotheses: `f` must be `C²` at `x` (second-derivative symmetry is what makes the
second-order terms cancel, and `C²` at a point is what transports through the chart via
`ContDiffWithinAt.isSymmSndFDerivWithinAt`); the vector fields need only be
differentiable at `x`. -/
theorem mlieBracket_apply_fun {f : M → F} {V W : Π x : M, TangentSpace I x} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F) 2 f x)
    (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    (mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x) (V x)
      - (mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x) (W x)
      = (mvfderiv I f x) (mlieBracket I V W x) := by
  have hxu : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  -- the function, transferred to the chart
  have hg : ContDiffWithinAt 𝕜 2 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
    have h := (contMDiffAt_iff.1 hf).2
    simpa [extChartAt_model_space_eq_id] using h
  -- the vector fields, transferred to the chart
  have hV' : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)) (range I)
      (extChartAt I x x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
      (V := V) (s := univ) (x := x) hV.mdifferentiableWithinAt
    simpa using h
  have hW' : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)) (range I)
      (extChartAt I x x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
      (V := W) (s := univ) (x := x) hW.mdifferentiableWithinAt
    simpa using h
  -- differentiability of the chart-side directional-derivative functions
  have hg1 : DifferentiableWithinAt 𝕜
      (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I)) (range I) (extChartAt I x x) :=
    ((hg.fderivWithin_right (m := 1) I.uniqueDiffOn (by norm_num)
      hxu).differentiableWithinAt one_ne_zero)
  have hgW : DifferentiableWithinAt 𝕜
      (fun z ↦ fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) z
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I) z)) (range I)
      (extChartAt I x x) := hg1.clm_apply hW'
  have hgV : DifferentiableWithinAt 𝕜
      (fun z ↦ fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) z
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) z)) (range I)
      (extChartAt I x x) := hg1.clm_apply hV'
  -- eventual differentiability of `f`
  have hfev : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(𝕜, F) f y := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).1 hf] with y hy
    exact hy.mdifferentiableAt two_ne_zero
  -- the directional-derivative functions, transferred to the chart
  have hWev : (fun y ↦ mvfderiv I f y (W y)) =ᶠ[nhds x]
      (fun z ↦ fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) z
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I) z)) ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, hfev,
      eventually_mpullbackWithin_extChartAt_symm_apply (V := W) (x := x)] with y hy hfy hWy
    show mvfderiv I f y (W y) = _
    rw [mvfderiv_apply_eq_fderivWithin hy hfy (W y)]
    simp only [Function.comp_apply, hWy]
  have hVev : (fun y ↦ mvfderiv I f y (V y)) =ᶠ[nhds x]
      (fun z ↦ fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) z
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) z)) ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, hfev,
      eventually_mpullbackWithin_extChartAt_symm_apply (V := V) (x := x)] with y hy hfy hVy
    show mvfderiv I f y (V y) = _
    rw [mvfderiv_apply_eq_fderivWithin hy hfy (V y)]
    simp only [Function.comp_apply, hVy]
  -- the two second-derivative terms
  have hL1 : mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x)
      = fderivWithin 𝕜 (fun z ↦ fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) z
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I) z)) (range I)
          (extChartAt I x x)
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) (extChartAt I x x)) := by
    rw [mvfderiv_congr_of_eventuallyEq hWev,
      mvfderiv_comp_extChartAt_apply (mem_extChartAt_source x) hgW (V x)]
    congr 1
    exact (eventually_mpullbackWithin_extChartAt_symm_apply (V := V)
      (x := x)).self_of_nhds.symm
  have hL2 : mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (W x)
      = fderivWithin 𝕜 (fun z ↦ fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) z
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) z)) (range I)
          (extChartAt I x x)
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I) (extChartAt I x x)) := by
    rw [mvfderiv_congr_of_eventuallyEq hVev,
      mvfderiv_comp_extChartAt_apply (mem_extChartAt_source x) hgV (W x)]
    congr 1
    exact (eventually_mpullbackWithin_extChartAt_symm_apply (V := W)
      (x := x)).self_of_nhds.symm
  -- the bracket term: `mlieBracket` is *defined* as the pullback of the chart-side
  -- bracket, so applying the chart differential undoes the `.inverse`
  have hR : mvfderiv I f x (mlieBracket I V W x)
      = fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x)
          (lieBracketWithin 𝕜
            (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
            (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I))
            (range I) (extChartAt I x x)) := by
    rw [mvfderiv_apply_eq_fderivWithin (mem_extChartAt_source x)
      (hf.mdifferentiableAt two_ne_zero) (mlieBracket I V W x)]
    congr 1
    have hb : mlieBracket I V W x = (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x).inverse
        (show E from lieBracketWithin 𝕜
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I))
          (range I) (extChartAt I x x)) := by
      rw [← mlieBracketWithin_univ, mlieBracketWithin_apply, preimage_univ, univ_inter]
    rw [hb, (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).self_apply_inverse]
  rw [hL1, hL2, hR]
  exact lieBracketWithin_apply_fun hg hV' hW' I.uniqueDiffOn
    (I.range_subset_closure_interior hxu) hxu

end Manifold

end VectorField
