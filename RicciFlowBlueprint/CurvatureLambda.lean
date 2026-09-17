/-
**The curvature operator on `Λ²T_xM`.**

`CurvatureOperator.lean` supplies `curvatureTensorAt`, the Riemann tensor as a `4`-linear form
on tangent vectors with all four symmetries. This file factors it through the exterior square,
which is the form Hamilton's pinching argument and Uhlenbeck's trick are stated in.

**Mathlib supplies the target but not the constructor.**
`Analysis/InnerProductSpace/ExteriorPower.lean` puts an inner product on `⋀[ℝ]^n E` by the Gram
determinant and `OrthonormalBasis.exteriorPower` induces an orthonormal basis, so the exterior
square is a genuine inner product space with no work. `exteriorPower.alternatingMapLinearEquiv`
is the universal property. What is missing is a way to *build* a rank-2 alternating map from a
bilinear one — the algebraic multilinear API has no `curryLeft`/`uncurryLeft` — so
`altOfBilin` does it by hand, once, for reuse on both pairs of slots.
-/
import RicciFlowBlueprint.CurvatureOperator
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

section AltTwo

variable {V N : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup N] [Module ℝ N]

/-- **A bilinear alternating function of two vectors, as an `AlternatingMap` over `Fin 2`.**

Mathlib has no constructor for this, and it is needed twice — once for each pair of slots of
the Riemann tensor — so it is worth isolating. Everything is a two-case split on the `Fin 2`
index; the alternating condition only has to be checked on the diagonal because `i ≠ j` in
`Fin 2` forces `{i,j} = {0,1}`. -/
noncomputable def altOfBilin (B : V → V → N)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℝ) (x z), B (c • x) z = c • B x z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₂ : ∀ (c : ℝ) (x z), B x (c • z) = c • B x z)
    (halt : ∀ x, B x x = 0) : V [⋀^Fin 2]→ₗ[ℝ] N where
  toFun v := B (v 0) (v 1)
  map_update_add' m i x y := by
    fin_cases i
    · show B ((Function.update m 0 (x + y)) 0) ((Function.update m 0 (x + y)) 1) = _
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (1 : Fin 2) ≠ 0)]
      show B (x + y) (m 1) = B ((Function.update m 0 x) 0) ((Function.update m 0 x) 1)
        + B ((Function.update m 0 y) 0) ((Function.update m 0 y) 1)
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (1 : Fin 2) ≠ 0),
        Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (1 : Fin 2) ≠ 0)]
      exact hadd₁ x y (m 1)
    · show B ((Function.update m 1 (x + y)) 0) ((Function.update m 1 (x + y)) 1) = _
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (0 : Fin 2) ≠ 1)]
      show B (m 0) (x + y) = B ((Function.update m 1 x) 0) ((Function.update m 1 x) 1)
        + B ((Function.update m 1 y) 0) ((Function.update m 1 y) 1)
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (0 : Fin 2) ≠ 1),
        Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (0 : Fin 2) ≠ 1)]
      exact hadd₂ (m 0) x y
  map_update_smul' m i c x := by
    fin_cases i
    · show B ((Function.update m 0 (c • x)) 0) ((Function.update m 0 (c • x)) 1) = _
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (1 : Fin 2) ≠ 0)]
      show B (c • x) (m 1) = c • B ((Function.update m 0 x) 0) ((Function.update m 0 x) 1)
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (1 : Fin 2) ≠ 0)]
      exact hsmul₁ c x (m 1)
    · show B ((Function.update m 1 (c • x)) 0) ((Function.update m 1 (c • x)) 1) = _
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (0 : Fin 2) ≠ 1)]
      show B (m 0) (c • x) = c • B ((Function.update m 1 x) 0) ((Function.update m 1 x) 1)
      rw [Function.update_self, Function.update_of_ne (Fin.ne_of_val_ne (by norm_num) : (0 : Fin 2) ≠ 1)]
      exact hsmul₂ c (m 0) x
  map_eq_zero_of_eq' v i j hv hij := by
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    show B (v 0) (v 1) = 0
    rw [← h01]
    exact halt (v 0)

@[simp] theorem altOfBilin_apply (B : V → V → N) (hadd₁ hsmul₁ hadd₂ hsmul₂ halt) (v : Fin 2 → V) :
    altOfBilin B hadd₁ hsmul₁ hadd₂ hsmul₂ halt v = B (v 0) (v 1) := rfl

end AltTwo

section LambdaSquared

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The second factorisation through `Λ²`, for an abstract family of functionals.**

Given `Φ c d : ⋀²V →ₗ[ℝ] ℝ` bilinear and alternating in `(c,d)` — which is what the *first*
factorisation of a `(0,4)` tensor produces — this is the induced map
`⋀²V →ₗ[ℝ] (V [⋀^Fin 2]→ₗ[ℝ] ℝ)`.

**Linearity in the `Λ²` argument is carried by hand, not by the universal property.** That is
the point: `exteriorPower.alternatingMapLinearEquiv` is used only at codomain `ℝ`, never at a
`LinearMap`-valued codomain. -/
noncomputable def sndAux (Φ : V → V → (⋀[ℝ]^2 V →ₗ[ℝ] ℝ))
    (ha₁ : ∀ c c' d w, Φ (c + c') d w = Φ c d w + Φ c' d w)
    (hs₁ : ∀ (r : ℝ) c d w, Φ (r • c) d w = r • Φ c d w)
    (ha₂ : ∀ c d d' w, Φ c (d + d') w = Φ c d w + Φ c d' w)
    (hs₂ : ∀ (r : ℝ) c d w, Φ c (r • d) w = r • Φ c d w)
    (hz : ∀ c w, Φ c c w = 0) :
    ⋀[ℝ]^2 V →ₗ[ℝ] (V [⋀^Fin 2]→ₗ[ℝ] ℝ) where
  toFun w := altOfBilin (fun c d ↦ Φ c d w) (fun c c' d ↦ ha₁ c c' d w)
    (fun r c d ↦ hs₁ r c d w) (fun c d d' ↦ ha₂ c d d' w)
    (fun r c d ↦ hs₂ r c d w) (fun c ↦ hz c w)
  map_add' w w' := by ext v; show Φ (v 0) (v 1) (w + w') = _; rw [map_add]; rfl
  map_smul' r w := by ext v; show Φ (v 0) (v 1) (r • w) = _; rw [map_smul]; rfl

/-- **A bilinear form on `Λ²V` from a family of functionals alternating in two more slots.**
This is the object a `(0,4)` tensor with both antisymmetries factors through. -/
noncomputable def sndForm (Φ : V → V → (⋀[ℝ]^2 V →ₗ[ℝ] ℝ))
    (ha₁ : ∀ c c' d w, Φ (c + c') d w = Φ c d w + Φ c' d w)
    (hs₁ : ∀ (r : ℝ) c d w, Φ (r • c) d w = r • Φ c d w)
    (ha₂ : ∀ c d d' w, Φ c (d + d') w = Φ c d w + Φ c d' w)
    (hs₂ : ∀ (r : ℝ) c d w, Φ c (r • d) w = r • Φ c d w)
    (hz : ∀ c w, Φ c c w = 0) :
    ⋀[ℝ]^2 V →ₗ[ℝ] (⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :=
  (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := V) (N := ℝ)
    (n := 2)).toLinearMap ∘ₗ sndAux Φ ha₁ hs₁ ha₂ hs₂ hz

/-- **The characterisation**, and the reason this is landed rather than merely defined:
`sndForm Φ (w, c∧d) = Φ c d w`. Applying a map of type
`⋀²V →ₗ[ℝ] (⋀²V →ₗ[ℝ] ℝ)` is exactly what the previous attempt could not do; here it goes
through, because nothing in the term reduces past `Φ`. -/
theorem sndForm_apply (Φ : V → V → (⋀[ℝ]^2 V →ₗ[ℝ] ℝ))
    (ha₁ : ∀ c c' d w, Φ (c + c') d w = Φ c d w + Φ c' d w)
    (hs₁ : ∀ (r : ℝ) c d w, Φ (r • c) d w = r • Φ c d w)
    (ha₂ : ∀ c d d' w, Φ c (d + d') w = Φ c d w + Φ c d' w)
    (hs₂ : ∀ (r : ℝ) c d w, Φ c (r • d) w = r • Φ c d w)
    (hz : ∀ c w, Φ c c w = 0)
    (w : ⋀[ℝ]^2 V) (d : Fin 2 → V) :
    sndForm Φ ha₁ hs₁ ha₂ hs₂ hz w (exteriorPower.ιMulti ℝ 2 d) = Φ (d 0) (d 1) w := by
  show exteriorPower.alternatingMapLinearEquiv
      (sndAux Φ ha₁ hs₁ ha₂ hs₂ hz w) (exteriorPower.ιMulti ℝ 2 d) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end LambdaSquared

end RicciFlowBlueprint

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

open RicciFlowBlueprint

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- `Rm(a,a,c,d) = 0`, from antisymmetry in the first pair. -/
theorem curvatureTensorAt_self_fst_snd (a c d : TangentSpace I x) :
    cov.curvatureTensorAt a a c d = 0 := by
  have h := cov.curvatureTensorAt_antisymm_fst_snd (a := a) (b := a) (c := c) (d := d)
  linarith

/-- `Rm(a,b,c,c) = 0`, from antisymmetry in the second pair. -/
theorem curvatureTensorAt_self_thd_fth
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (a b c : TangentSpace I x) :
    cov.curvatureTensorAt a b c c = 0 := by
  have h := cov.curvatureTensorAt_antisymm_thd_fth (a := a) (b := b) (c := c) (d := c)
    hmetric htor
  linarith

/-! ### Factoring through `Λ²`

**Everything here is stated over `E`, never over `TangentSpace I x`.** The two are definitionally
equal and `curvatureTensorAt` is happy to take `E`-typed vectors (with `x` pinned explicitly,
since it is otherwise undetermined), but forming `⋀[ℝ]^2 (TangentSpace I x)` and then unifying
it against `⋀[ℝ]^2 E` sends `isDefEq` through the exterior algebra --- a quotient of a tensor
algebra --- and it does not come back, even at 4x heartbeats. This is the `E` vs `TangentSpace`
wall documented in `CLAUDE.md`, one type former up, and the same remedy applies: state the heavy
type over `E`. No metric is used in this section, so nothing is lost. -/

/-- The first pair of slots, factored: `(a,b) ↦ Rm(a,b,c,d)` as an alternating map. -/
noncomputable def curvatureAltFst (x : M) (c d : E) : E [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  altOfBilin (fun a b : E ↦ cov.curvatureTensorAt (x := x) a b c d)
    (fun a a' b ↦ cov.curvatureTensorAt_add_fst a a' b c d)
    (fun r a b ↦ cov.curvatureTensorAt_smul_fst a b c d r)
    (fun a b b' ↦ cov.curvatureTensorAt_add_snd b b' a c d)
    (fun r a b ↦ cov.curvatureTensorAt_smul_snd b a c d r)
    (fun a ↦ cov.curvatureTensorAt_self_fst_snd a c d)

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
@[simp] theorem curvatureAltFst_apply (x : M) (c d : E) (v : Fin 2 → E) :
    cov.curvatureAltFst x c d v = cov.curvatureTensorAt (x := x) (v 0) (v 1) c d := rfl

/-- The first pair factored through `Λ²`, as a linear functional. -/
noncomputable def curvatureFunctional (x : M) (c d : E) : ⋀[ℝ]^2 E →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv (cov.curvatureAltFst x c d)

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
theorem curvatureFunctional_apply_ιMulti (x : M) (c d : E) (v : Fin 2 → E) :
    cov.curvatureFunctional x c d (exteriorPower.ιMulti ℝ 2 v)
      = cov.curvatureTensorAt (x := x) (v 0) (v 1) c d :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-! The laws in the *second* pair of slots. Each is proved at the level of the alternating map,
where it is the corresponding slot law of `curvatureTensorAt` applied pointwise, and then
pushed through `alternatingMapLinearEquiv` --- a linear **equivalence**, so it carries `+` and
`•` across for free. No induction over `Λ²` is needed, and none is available: Mathlib has
`exteriorPower.ιMulti_span` but no span-induction eliminator. -/

theorem curvatureAltFst_add_thd (x : M) (c c' d : E) :
    cov.curvatureAltFst x (c + c') d = cov.curvatureAltFst x c d + cov.curvatureAltFst x c' d := by
  ext v
  show cov.curvatureTensorAt (x := x) (v 0) (v 1) (c + c') d
      = cov.curvatureTensorAt (x := x) (v 0) (v 1) c d
        + cov.curvatureTensorAt (x := x) (v 0) (v 1) c' d
  exact cov.curvatureTensorAt_add_thd c c' (v 0) (v 1) d

theorem curvatureAltFst_smul_thd (x : M) (r : ℝ) (c d : E) :
    cov.curvatureAltFst x (r • c) d = r • cov.curvatureAltFst x c d := by
  ext v
  show cov.curvatureTensorAt (x := x) (v 0) (v 1) (r • c) d
      = r • cov.curvatureTensorAt (x := x) (v 0) (v 1) c d
  exact cov.curvatureTensorAt_smul_thd c (v 0) (v 1) d r

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
theorem curvatureAltFst_add_fth (x : M) (c d d' : E) :
    cov.curvatureAltFst x c (d + d') = cov.curvatureAltFst x c d + cov.curvatureAltFst x c d' := by
  ext v
  show cov.curvatureTensorAt (x := x) (v 0) (v 1) c (d + d')
      = cov.curvatureTensorAt (x := x) (v 0) (v 1) c d
        + cov.curvatureTensorAt (x := x) (v 0) (v 1) c d'
  exact cov.curvatureTensorAt_add_fth d d' (v 0) (v 1) c

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
theorem curvatureAltFst_smul_fth (x : M) (r : ℝ) (c d : E) :
    cov.curvatureAltFst x c (r • d) = r • cov.curvatureAltFst x c d := by
  ext v
  show cov.curvatureTensorAt (x := x) (v 0) (v 1) c (r • d)
      = r • cov.curvatureTensorAt (x := x) (v 0) (v 1) c d
  exact cov.curvatureTensorAt_smul_fth d (v 0) (v 1) c r

theorem curvatureAltFst_self
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (x : M) (c : E) :
    cov.curvatureAltFst x c c = 0 := by
  ext v
  show cov.curvatureTensorAt (x := x) (v 0) (v 1) c c = 0
  exact cov.curvatureTensorAt_self_thd_fth hmetric htor (v 0) (v 1) c

/-! The same five laws at the level of the functional, as **named theorems**. Inlining their
proofs into `curvatureAltSnd` makes that term carry five tactic-generated proofs, and the
elaborator then chokes on any *use* of `curvatureForm`. Naming them keeps the term small. -/

theorem curvatureFunctional_add_thd (x : M) (c c' d : E) :
    cov.curvatureFunctional x (c + c') d
      = cov.curvatureFunctional x c d + cov.curvatureFunctional x c' d := by
  simp only [curvatureFunctional, cov.curvatureAltFst_add_thd, map_add]

theorem curvatureFunctional_smul_thd (x : M) (r : ℝ) (c d : E) :
    cov.curvatureFunctional x (r • c) d = r • cov.curvatureFunctional x c d := by
  simp only [curvatureFunctional, cov.curvatureAltFst_smul_thd, map_smul]

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
theorem curvatureFunctional_add_fth (x : M) (c d d' : E) :
    cov.curvatureFunctional x c (d + d')
      = cov.curvatureFunctional x c d + cov.curvatureFunctional x c d' := by
  simp only [curvatureFunctional, cov.curvatureAltFst_add_fth, map_add]

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
theorem curvatureFunctional_smul_fth (x : M) (r : ℝ) (c d : E) :
    cov.curvatureFunctional x c (r • d) = r • cov.curvatureFunctional x c d := by
  simp only [curvatureFunctional, cov.curvatureAltFst_smul_fth, map_smul]

theorem curvatureFunctional_self
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (x : M) (c : E) :
    cov.curvatureFunctional x c c = 0 := by
  simp only [curvatureFunctional, cov.curvatureAltFst_self hmetric htor, map_zero]

/-! ### Where this stops, and why --- diagnosis corrected 2026-09-16

An earlier version of this note recorded that the obstruction was **the nested codomain**
`⋀[ℝ]^2 E →ₗ[ℝ] (⋀[ℝ]^2 E →ₗ[ℝ] ℝ)`. That was wrong, and the correction is worth more than
the guess was:

* a map of **exactly** that type, taken as a variable, applies to two wedges by `rfl` under
  this file's full instance pile;
* Mathlib itself builds and applies one (`LinearMap.BilinForm.exteriorPower`, with a `simp`
  lemma evaluating it on two `ιMulti`s);
* and a map whose codomain is an `AlternatingMap` --- *not* nested --- fails in the same way,
  which rules the codomain out entirely.

**What the profiler says.** `set_option diagnostics true` on the smallest failing
application reports `isDefEq` unfolding `RiemannianBundle.g` 202472 times and
`RiemannianMetric.inner` 202476 times, through `innerSL`, `LinearMap.mkContinuousOfExistsBound`
and `mkContinuous₂`, with the `f a =?= f b` heuristic firing on `toFun` 286390 times. **The
cost is the Riemannian metric, not `Λ²`.** `curvatureTensorAt a b c d` is by definition
`⟪Rm(a,b)c, d⟫`, so every definitional comparison of a term built from it descends into the
metric's construction.

**The metric-free construction works.** `sndForm` above is the whole second factorisation, and
it defines, applies and is characterised (`sndForm_apply`) for an abstract `Φ`. So the
factorisation itself was never the problem either.

**What remains.** Instantiating at `Φ = curvatureFunctional x` puts the metric back inside the
term, and the application times out again --- unchanged by marking the inner definitions, the
outer definition, or `curvatureTensorAt` itself `irreducible` (all three were tried). So
`curvatureForm` is still deliberately absent.

**The lead for the next attempt**, and it is a different one from before: keep the metric out
of the *term*, not merely out of the construction. Build the `(0,4)` tensor once as a bundled
`E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ` so that `⟪·,·⟫` sits inside a single opaque continuous
linear map, and factor that. This is the same lesson `Divergence.lean` paid for with
`curvatureBilinFst` (declare at the `E` type, not the `TangentSpace` one) and `FlowKoszul.lean`
paid for with `→ₗ` in place of `→L`. -/

end CovariantDerivative
