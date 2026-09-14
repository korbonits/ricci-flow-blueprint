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

/-! ### Where this stops, and why

Everything above is the **first** pair of slots factored through `Λ²`, together with all ten
laws the *second* factorisation needs. The second factorisation itself is **not** here, and the
reason is worth recording precisely rather than retrying.

`curvatureAltSnd` would be an alternating map into `⋀[ℝ]^2 E →ₗ[ℝ] ℝ`, and `curvatureForm` its
factorisation, a bilinear form on `Λ²`. Both *define* without complaint. But **any application
of `curvatureForm` fails to elaborate** -- `isDefEq` runs into the exterior algebra (a quotient
of a tensor algebra) and does not return, at 4x heartbeats, with both wedges replaced by opaque
variables, with the proof fields extracted as named theorems, and with only one of the two
arguments applied.

**The culprit is the nested codomain, not `Λ²` itself.** `curvatureFunctional`, which is a
`LinearMap` out of `⋀[ℝ]^2 E` into `ℝ`, applies perfectly well -- that is what
`curvatureFunctional_apply_ιMulti` above is. It is specifically
`⋀[ℝ]^2 E →ₗ[ℝ] (⋀[ℝ]^2 E →ₗ[ℝ] ℝ)` that the elaborator cannot handle here.

A definition whose only characterisation cannot be stated is exactly the hazard this repo
guards against, so `curvatureForm` is deliberately absent rather than landed unusable. The
design lead for the next attempt: avoid the nested `LinearMap` codomain --- build the curvature
*operator* `Λ² → Λ²` directly through the inner product that
`Analysis/InnerProductSpace/ExteriorPower.lean` supplies, rather than a bilinear form, or go
through a bundled bilinear-map type, or define it on a basis via
`OrthonormalBasis.exteriorPower`. -/

end CovariantDerivative
