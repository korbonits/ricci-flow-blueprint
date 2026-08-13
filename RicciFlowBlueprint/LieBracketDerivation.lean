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

/- ASSEMBLY BLOCKED. Combining the two collapse lemmas above into the
model-space derivation identity runs into a type-synonym conflict:
`HasFDerivAt V V' x` requires `V : E → E` (non-dependent codomain), while
`mlieBracketWithin` requires `V : Π x, TangentSpace 𝓘(𝕜,E) x`. The two are
defeq for elaboration but not for instance synthesis, and
`backward.isDefEq.respectTransparency false` does not help since it governs
defeq checking rather than instance search. Resolving this needs either a
non-dependent restatement of the bracket API on the model space, or an explicit
transport across the synonym. -/

end ModelSpace

end VectorField
