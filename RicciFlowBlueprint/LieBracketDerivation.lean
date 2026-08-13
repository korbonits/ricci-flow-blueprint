/-
The Lie bracket acts as a derivation on functions.

This is the identity `[V, W] f = V (W f) - W (V f)`. It is missing from Mathlib
in both the vector-space and the manifold setting, and the manifold version is
the last obstruction to third-slot tensoriality of the curvature operator (see
`RicciFlowBlueprint.Curvature`), hence to defining Ricci curvature at all.

What follows is the vector-space case, which is the mathematical content: the
two second-derivative terms cancel by symmetry of the second derivative, and
what survives is exactly the bracket. The manifold case additionally requires
transporting this through `extChartAt`, which is the remaining work.
-/
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

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

end VectorField
