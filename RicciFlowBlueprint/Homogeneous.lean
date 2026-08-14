/-
Ricci flow on left-invariant metrics: the branch of the blueprint that closes
end to end today, with no `sorry` and no `proof_wanted`.

On a Lie group `G`, a left-invariant metric is exactly an inner product on the
Lie algebra `𝔤`, and for left-invariant vector fields every term of the Koszul
formula that differentiates a function vanishes (⟨Y,Z⟩ is constant), leaving

    2⟨∇ₓy, z⟩ = ⟨[x,y],z⟩ − ⟨[y,z],x⟩ + ⟨[z,x],y⟩,

which is *algebra*: the right-hand side is a bounded trilinear expression in
the bracket and the metric, and the left-hand side determines `∇ₓy` because
the metric is invertible as a map `𝔤 → 𝔤*`. So the Levi-Civita connection of a
left-invariant metric can be **defined outright** — no existence theorem, no
`CovariantDerivative`, no bundles — and `∂g/∂t = −2 Ric(g)` becomes an ODE on
the finite-dimensional space of bilinear forms on `𝔤`, where Mathlib's
Picard–Lindelöf applies. This file carries that out in full:

* `koszul` — the connection, defined by inverting the metric
  (`ContinuousLinearMap.inverse`, which is total, so the definition needs no
  hypotheses; every lemma assumes `g.IsInvertible`).
* `koszul_sub_koszul` / `apply_koszul_add_apply_koszul` — torsion-freeness and
  metric compatibility. Together with `eq_koszul_of_torsionFree_of_compat`
  (uniqueness) this is the fundamental theorem of Riemannian geometry in the
  left-invariant world — the statement that is `sorry`ed at manifold level in
  `LeviCivita.lean` is *proved* here.
* `curvature`, `ricciEndo`, `ricciBilin` — R(x,y) = [∇ₓ,∇_y] − ∇_{[x,y]} and
  Ric(x,y) = tr(w ↦ R(w,x)y), matching the trace convention of `Ricci.lean`.
* `contDiffAt_ricciField` — the analytic heart: `g ↦ −2 Ric(g)` is `C^n` at
  every invertible `g`. Ricci is a polynomial in `g` and `g⁻¹`; smoothness of
  operator inversion at invertible points is `contDiffAt_map_inverse`.
* `ricciFlow_exists` / `ricciFlow_unique` / `ricciFlow_leftInvariant` —
  short-time existence and uniqueness of the flow through every inner product,
  via Picard–Lindelöf (`Mathlib/Analysis/ODE/ExistUnique.lean`).
* `ofLieAlgebra` + `ricciFlow_lieAlgebra` — the bridge to honest `LieRing`
  Lie algebras (see design note below).

## Design notes

**The bracket is an explicit continuous bilinear map, not a `LieRing`
instance.** `LieRing 𝔤` extends `AddCommGroup 𝔤`, and so does
`NormedAddCommGroup 𝔤`; declaring both puts two unrelated `AddCommGroup`
structures on `𝔤` and nothing in Mathlib combines them (no file under
`Mathlib/Analysis` mentions `LieRing`). Since `HasDerivAt` needs a norm on the
space where the flow lives, the norm is non-negotiable, so the bracket is the
structure that moves out of the instance system: we work on a
finite-dimensional real normed space `E` with a bracket `β : E →L[ℝ] E →L[ℝ] E`
and hypothesis `∀ x, β x x = 0` where a proof needs it. Jacobi is never
consumed — torsion-freeness, compatibility, Levi-Civita uniqueness and the ODE
theory need only bilinearity and alternation. The transport section shows no
generality is lost: any finite-dimensional real Lie algebra `𝔩` induces
`ofLieAlgebra e` (alternating *and* Jacobi) along any linear equivalence
`e : 𝔩 ≃ₗ[ℝ] E`, and the abstract flow statement `ricciFlow_lieAlgebra`
follows. This mirrors the lesson of `Hamilton.lean`: quantities that vary
(there the metric, here also the bracket) must not be instance-carried.

**The metric is `g : E →L[ℝ] E →L[ℝ] ℝ`, i.e. literally a map into the
topological dual**, so "invert the metric" is `ContinuousLinearMap.inverse g`
with no `toDual` detour, `Nondegenerate` is `ContinuousLinearMap.IsInvertible`,
and the smoothness of `g ↦ g⁻¹` is exactly `contDiffAt_map_inverse`. Positive
definiteness (`IsInnerProduct`) enters only through
`IsInnerProduct.isInvertible`; symmetry of `g` is never needed (the identities
are stated with all metric slots explicit, so they hold verbatim for
asymmetric `g`, and specialize to the textbook statements when `g` is
symmetric).

**What "maximal solution" became.** Mathlib has local Picard–Lindelöf and
local uniqueness but no maximal-interval machinery, so the headline is
short-time existence plus germ uniqueness at every time, not a unique maximal
flow. Gluing local solutions into a maximal one is routine mathematics but new
Mathlib infrastructure, out of scope here.
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Trace

open Set Filter Topology ContinuousLinearMap

namespace RicciFlowBlueprint
namespace LeftInvariant

/-! ### A composition combinator

`(x, y) ↦ (F x).comp (G y)` as a bundled continuous bilinear map. All the
bundled-in-two-slots operators below (the Koszul right-hand side, the Ricci
endomorphism) are assembled from this and `ContinuousLinearMap.compL`, which
keeps every definition inside the continuous-linear-map algebra — that is what
makes the smoothness proof `contDiffAt_ricciField` a mechanical composition of
`ContDiff.clm_comp`s. -/

section CompBilin

variable {X Y A B C : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- `(x, y) ↦ (F x).comp (G y)`, bundled. -/
noncomputable def compBilin (F : X →L[ℝ] B →L[ℝ] C) (G : Y →L[ℝ] A →L[ℝ] B) :
    X →L[ℝ] Y →L[ℝ] A →L[ℝ] C :=
  ((compL ℝ Y (A →L[ℝ] B) (A →L[ℝ] C)).flip G).comp ((compL ℝ A B C).comp F)

@[simp]
theorem compBilin_apply (F : X →L[ℝ] B →L[ℝ] C) (G : Y →L[ℝ] A →L[ℝ] B) (x : X) (y : Y) :
    compBilin F G x y = (F x).comp (G y) := rfl

end CompBilin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The Koszul connection

Note: nothing in this section needs finite dimensionality — the Koszul connection,
torsion-freeness, compatibility and Levi-Civita uniqueness hold on any normed space
whose metric is invertible as a map to the topological dual. Finite dimensionality
enters with the trace (`traceCLM`), with `IsInnerProduct.isInvertible`, and with the
ODE theory. -/

section Koszul

variable (β : E →L[ℝ] E →L[ℝ] E) (g : E →L[ℝ] E →L[ℝ] ℝ)

/-- The right-hand side of the algebraic Koszul formula: `koszulRHS β g x y` is the
linear functional `z ↦ 2⁻¹ (g [x,y] z − g [y,z] x + g [z,x] y)` (third term recorded
as `− g [x,z] y`, which is equal once `β` is alternating — and is what makes the
definition bracket-hypothesis-free). -/
noncomputable def koszulRHS : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) •
    ((compL ℝ E E (E →L[ℝ] ℝ) g).comp β - compBilin g.flip β - (compBilin g.flip β).flip)

theorem koszulRHS_apply (x y z : E) :
    koszulRHS β g x y z = 2⁻¹ * (g (β x y) z - g (β y z) x - g (β x z) y) := by
  simp only [koszulRHS, smul_apply, sub_apply, coe_comp', Function.comp_apply, compL_apply,
    comp_apply, compBilin_apply, flip_apply, smul_eq_mul]
  ring

/-- The Levi-Civita connection of the left-invariant metric `g`, defined outright by
solving the Koszul formula: `∇ₓy = g⁻¹ (koszulRHS β g x y)`. Uses the total function
`ContinuousLinearMap.inverse`, so no hypothesis is needed here; every lemma about
`koszul` assumes `g.IsInvertible`. -/
noncomputable def koszul : E →L[ℝ] E →L[ℝ] E :=
  (compL ℝ E (E →L[ℝ] ℝ) E g.inverse).comp (koszulRHS β g)

theorem koszul_apply (x y : E) : koszul β g x y = g.inverse (koszulRHS β g x y) := rfl

variable {g}

/-- The defining property of the Koszul connection: `g (∇ₓ y) = koszulRHS β g x y`. -/
theorem apply_koszul (hg : g.IsInvertible) (x y : E) :
    g (koszul β g x y) = koszulRHS β g x y := by
  obtain ⟨A, rfl⟩ := hg
  simp [koszul_apply]

theorem apply_koszul_apply (hg : g.IsInvertible) (x y z : E) :
    g (koszul β g x y) z = koszulRHS β g x y z := by
  rw [apply_koszul β hg]

theorem injective_of_isInvertible {g : E →L[ℝ] E →L[ℝ] ℝ} (hg : g.IsInvertible) :
    Function.Injective g := by
  obtain ⟨A, rfl⟩ := hg
  simpa using A.injective

variable {β}

/-- An alternating bilinear map is skew. -/
theorem skew_of_alt (hβ : ∀ x, β x x = 0) (x y : E) : β y x = -β x y := by
  have h := hβ (x + y)
  simp only [map_add, add_apply, hβ x, hβ y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **The Koszul connection is torsion-free**: `∇ₓy − ∇_yx = [x, y]`.
For left-invariant fields the Lie bracket of vector fields is the Lie algebra
bracket, so this is `T(X,Y) = 0`. -/
-- BENCH: koszul-torsion-free
theorem koszul_sub_koszul (hβ : ∀ x, β x x = 0) (hg : g.IsInvertible) (x y : E) :
    koszul β g x y - koszul β g y x = β x y := by
  apply injective_of_isInvertible hg
  rw [map_sub, apply_koszul β hg, apply_koszul β hg]
  ext z
  have h1 : β y x = -β x y := skew_of_alt hβ x y
  simp only [sub_apply, koszulRHS_apply, h1, map_neg, neg_apply]
  ring

/-- **The Koszul connection is metric-compatible**: `g(∇ₓy, z) + g(∇ₓz, y) = 0`.
For left-invariant fields `X⟨Y,Z⟩ = 0`, so this is `∇g = 0`: each `∇ₓ` is
`g`-skew-adjoint. -/
-- BENCH: koszul-metric-compatible
theorem apply_koszul_add_apply_koszul (hβ : ∀ x, β x x = 0) (hg : g.IsInvertible) (x y z : E) :
    g (koszul β g x y) z + g (koszul β g x z) y = 0 := by
  rw [apply_koszul_apply β hg, apply_koszul_apply β hg, koszulRHS_apply, koszulRHS_apply]
  have h1 : β z y = -β y z := skew_of_alt hβ y z
  simp only [h1, map_neg, neg_apply]
  ring

/-- **Uniqueness of the Levi-Civita connection on left-invariant fields**: any bilinear
`D` that is torsion-free and metric-compatible equals `koszul β g`. Together with
`koszul_sub_koszul` and `apply_koszul_add_apply_koszul` this is the fundamental
theorem of Riemannian geometry in the left-invariant setting — the statement that is
blocked at manifold level in `LeviCivita.lean` (mathlib4 PR #36845), proved outright
here. -/
-- BENCH: levi-civita-left-invariant
theorem eq_koszul_of_torsionFree_of_compat (hβ : ∀ x, β x x = 0) (hg : g.IsInvertible)
    (D : E →L[ℝ] E →L[ℝ] E)
    (hD₁ : ∀ x y, D x y - D y x = β x y)
    (hD₂ : ∀ x y z, g (D x y) z + g (D x z) y = 0) :
    D = koszul β g := by
  ext y z
  apply injective_of_isInvertible hg
  ext x
  rw [apply_koszul_apply β hg, koszulRHS_apply]
  have t1 := congrArg (fun v => g v z) (hD₁ x y)
  have t2 := congrArg (fun v => g v y) (hD₁ x z)
  have t3 := congrArg (fun v => g v x) (hD₁ y z)
  simp only [map_sub, sub_apply] at t1 t2 t3
  have e1 := hD₂ x y z
  have e2 := hD₂ y z x
  have e3 := hD₂ z x y
  have s2 : g (β z x) y = -g (β x z) y := by
    rw [skew_of_alt hβ x z, map_neg, neg_apply]
  have s3 : g (β y x) z = -g (β x y) z := by
    rw [skew_of_alt hβ x y, map_neg, neg_apply]
  rw [s2, s3]
  linarith

end Koszul

/-! ### Curvature and Ricci -/

section Ricci

variable (β : E →L[ℝ] E →L[ℝ] E) (g : E →L[ℝ] E →L[ℝ] ℝ)

/-- The curvature operator of the Koszul connection,
`R(x,y) = ∇ₓ∇_y − ∇_y∇ₓ − ∇_{[x,y]}` (the sign convention of `Curvature.lean`). -/
noncomputable def curvature (x y : E) : E →L[ℝ] E :=
  (koszul β g x).comp (koszul β g y) - (koszul β g y).comp (koszul β g x) - koszul β g (β x y)

theorem curvature_apply (x y z : E) :
    curvature β g x y z =
      koszul β g x (koszul β g y z) - koszul β g y (koszul β g x z)
        - koszul β g (β x y) z := rfl

/-- The endomorphism `w ↦ R(w, x) y`, bundled as a continuous bilinear map in `(x, y)`
so that both the trace (`ricciBilin`) and the smoothness proof can consume it.
The third term is recorded as `+ ∇_{[x,w]} y`, which equals `− ∇_{[w,x]} y` once `β`
is alternating (`ricciEndo_apply_eq_curvature`). -/
noncomputable def ricciEndo : E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (compL ℝ E E (E →L[ℝ] E) (koszul β g).flip).comp (koszul β g)
    - compBilin (koszul β g) (koszul β g).flip
    + (compBilin (koszul β g).flip β).flip

theorem ricciEndo_apply (x y w : E) :
    ricciEndo β g x y w =
      koszul β g w (koszul β g x y) - koszul β g x (koszul β g w y)
        + koszul β g (β x w) y := rfl

/-- The endomorphism traced by `ricciBilin` is `w ↦ R(w, x) y`. -/
theorem ricciEndo_apply_eq_curvature (hβ : ∀ x, β x x = 0) (x y w : E) :
    ricciEndo β g x y w = curvature β g w x y := by
  rw [ricciEndo_apply, curvature_apply, skew_of_alt hβ x w, map_neg, neg_apply]
  abel

variable [FiniteDimensional ℝ E]

variable (E) in
/-- The trace of an endomorphism, as a continuous linear functional on `E →L[ℝ] E`
(finite dimension makes the algebraic trace continuous). -/
noncomputable def traceCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ E).comp (coeLM ℝ : (E →L[ℝ] E) →ₗ[ℝ] E →ₗ[ℝ] E))

@[simp]
theorem traceCLM_apply (f : E →L[ℝ] E) :
    traceCLM E f = LinearMap.trace ℝ E ↑f := by
  simp [traceCLM]

/-- The Ricci form of the left-invariant metric `g`:
`Ric(x, y) = tr (w ↦ R(w, x) y)`, the trace convention of `Ricci.lean`.
Unfolds via `ricciBilin_apply` and `ricciEndo_apply_eq_curvature`. -/
noncomputable def ricciBilin : E →L[ℝ] E →L[ℝ] ℝ :=
  (compL ℝ E (E →L[ℝ] E) ℝ (traceCLM E)).comp (ricciEndo β g)

theorem ricciBilin_apply (x y : E) :
    ricciBilin β g x y = LinearMap.trace ℝ E ↑(ricciEndo β g x y) := by
  simp [ricciBilin]

end Ricci

/-! ### Inner products -/

section InnerProduct

variable [FiniteDimensional ℝ E]

/-- An inner product on `E`, carried as an explicit bilinear form — the whole point of
the flow is that the metric varies, so it must not be instance-carried (see
`Hamilton.lean` for the manifold-level version of this lesson). Only `posDef` is
consumed (via `isInvertible`); `symm` makes the notion honest. -/
structure IsInnerProduct (g : E →L[ℝ] E →L[ℝ] ℝ) : Prop where
  symm : ∀ x y, g x y = g y x
  posDef : ∀ x, x ≠ 0 → 0 < g x x

/-- A positive-definite form is invertible as a map to the dual: injectivity is
positive-definiteness, surjectivity is dimension count. This is where finite
dimensionality is essential. -/
theorem IsInnerProduct.isInvertible {g : E →L[ℝ] E →L[ℝ] ℝ} (hg : IsInnerProduct g) :
    g.IsInvertible := by
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hpos := hg.posDef x hne
    rw [show g x = 0 from hx] at hpos
    simp at hpos
  have : FiniteDimensional ℝ (E →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finiteDimensional
  have hrank : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finrank_eq,
      Module.finrank_linearMap_self]
  refine ⟨((g : E →ₗ[ℝ] E →L[ℝ] ℝ).linearEquivOfInjective hinj hrank).toContinuousLinearEquiv,
    ?_⟩
  ext x
  simp [LinearMap.linearEquivOfInjective_apply]

end InnerProduct

/-! ### The Ricci flow vector field and its smoothness -/

section Flow

variable [FiniteDimensional ℝ E] (β : E →L[ℝ] E →L[ℝ] E)

/-- The Ricci flow vector field `g ↦ −2 Ric(g)` on the space of bilinear forms.
Total (junk where `g` is not invertible), smooth at every invertible `g`. -/
noncomputable def ricciField (g : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-2 : ℝ) • ricciBilin β g

/-- **Smoothness of the Ricci flow vector field at invertible metrics** — the analytic
content of the left-invariant branch. `Ric(g)` is a polynomial in `g` and `g⁻¹`;
inversion is `C^n` at invertible operators (`contDiffAt_map_inverse`), and everything
else is composition of bounded (bi)linear operations. -/
-- BENCH: ricci-field-smooth
theorem contDiffAt_ricciField {n : WithTop ℕ∞} {g₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hg₀ : g₀.IsInvertible) :
    ContDiffAt ℝ n (ricciField β) g₀ := by
  -- the polynomial part `g ↦ koszulRHS β g` is smooth everywhere
  have hflip : ContDiff ℝ n fun g : E →L[ℝ] E →L[ℝ] ℝ => g.flip := by
    exact (flipₗᵢ ℝ E E ℝ).contDiff
  have h₁ : ContDiff ℝ n fun g : E →L[ℝ] E →L[ℝ] ℝ =>
      (compL ℝ E E (E →L[ℝ] ℝ) g).comp β := by
    exact (compL ℝ E E (E →L[ℝ] ℝ)).contDiff.clm_comp contDiff_const
  have h₂ : ContDiff ℝ n fun g : E →L[ℝ] E →L[ℝ] ℝ => compBilin g.flip β := by
    exact contDiff_const.clm_comp (contDiff_const.clm_comp hflip)
  have h₃ : ContDiff ℝ n fun g : E →L[ℝ] E →L[ℝ] ℝ => (compBilin g.flip β).flip := by
    exact ContDiff.comp (by exact (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff) h₂
  have hRHS : ContDiff ℝ n fun g : E →L[ℝ] E →L[ℝ] ℝ => koszulRHS β g := by
    exact ((h₁.sub h₂).sub h₃).const_smul (2⁻¹ : ℝ)
  -- inversion is smooth at the invertible point `g₀`
  have hinv : ContDiffAt ℝ n ContinuousLinearMap.inverse g₀ := hg₀.contDiffAt_map_inverse
  have hkos : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ => koszul β g) g₀ := by
    exact ContDiffAt.clm_comp
      (ContDiffAt.comp g₀ (compL ℝ E (E →L[ℝ] ℝ) E).contDiff.contDiffAt hinv)
      hRHS.contDiffAt
  have hkosflip : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ => (koszul β g).flip) g₀ := by
    exact ContDiffAt.comp g₀ (by exact (flipₗᵢ ℝ E E E).contDiff.contDiffAt) hkos
  -- the three terms of the Ricci endomorphism
  have hA : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ =>
      (compL ℝ E E (E →L[ℝ] E) (koszul β g).flip).comp (koszul β g)) g₀ := by
    exact ContDiffAt.clm_comp
      (ContDiffAt.comp g₀ (compL ℝ E E (E →L[ℝ] E)).contDiff.contDiffAt hkosflip) hkos
  have hB : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ =>
      compBilin (koszul β g) (koszul β g).flip) g₀ := by
    exact ContDiffAt.clm_comp
      (ContDiffAt.comp g₀ (compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)).flip.contDiff.contDiffAt
        hkosflip)
      (contDiffAt_const.clm_comp hkos)
  have hC : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ =>
      (compBilin (koszul β g).flip β).flip) g₀ := by
    exact ContDiffAt.comp g₀ (by exact (flipₗᵢ ℝ E E (E →L[ℝ] E)).contDiff.contDiffAt)
      (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp hkosflip))
  have hEndo : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ => ricciEndo β g) g₀ :=
    (hA.sub hB).add hC
  have hRic : ContDiffAt ℝ n (fun g : E →L[ℝ] E →L[ℝ] ℝ => ricciBilin β g) g₀ :=
    contDiffAt_const.clm_comp hEndo
  exact hRic.const_smul (-2 : ℝ)

/-! ### Short-time existence and uniqueness -/

/-- **Short-time existence of the Ricci flow on left-invariant metrics**, by
Picard–Lindelöf: through every invertible `g₀` there is a local solution of
`∂g/∂t = −2 Ric(g)`. -/
-- BENCH: ricci-flow-left-invariant-exists
theorem ricciFlow_exists {g₀ : E →L[ℝ] E →L[ℝ] ℝ} (hg₀ : g₀.IsInvertible) (t₀ : ℝ) :
    ∃ γ : ℝ → E →L[ℝ] E →L[ℝ] ℝ, γ t₀ = g₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (ricciField β (γ t)) t :=
  (contDiffAt_ricciField β hg₀).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    t₀

/-- **Uniqueness of the Ricci flow on left-invariant metrics**: two local solutions
through the same invertible `g₀` agree near `t₀`. -/
-- BENCH: ricci-flow-left-invariant-unique
theorem ricciFlow_unique {g₀ : E →L[ℝ] E →L[ℝ] ℝ} (hg₀ : g₀.IsInvertible) {t₀ : ℝ}
    {γ₁ γ₂ : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    (h₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ₁ (ricciField β (γ₁ t)) t)
    (h₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ₂ (ricciField β (γ₂ t)) t)
    (hγ₁ : γ₁ t₀ = g₀) (hγ₂ : γ₂ t₀ = g₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  obtain ⟨K, s, hs, hK⟩ :=
    (contDiffAt_ricciField β (n := 1) hg₀).exists_lipschitzOnWith
  have m₁ : ∀ᶠ t in 𝓝 t₀, γ₁ t ∈ s :=
    h₁.self_of_nhds.continuousAt.preimage_mem_nhds (by rw [hγ₁]; exact hs)
  have m₂ : ∀ᶠ t in 𝓝 t₀, γ₂ t ∈ s :=
    h₂.self_of_nhds.continuousAt.preimage_mem_nhds (by rw [hγ₂]; exact hs)
  exact ODE_solution_unique_of_eventually (.of_forall fun _ => hK)
    (h₁.and m₁) (h₂.and m₂) (by rw [hγ₁, hγ₂])

/-- **The Ricci flow on left-invariant metrics** — the closed branch of the blueprint.
Through every inner product `g₀` on `E` there is a short-time solution of Hamilton's
equation `∂g/∂t = −2 Ric(g)`, unique among local solutions as a germ at `t₀`. -/
-- BENCH: ricci-flow-left-invariant
theorem ricciFlow_leftInvariant {g₀ : E →L[ℝ] E →L[ℝ] ℝ} (hg₀ : IsInnerProduct g₀)
    (t₀ : ℝ) :
    ∃ γ : ℝ → E →L[ℝ] E →L[ℝ] ℝ, γ t₀ = g₀ ∧
      (∀ᶠ t in 𝓝 t₀, HasDerivAt γ (ricciField β (γ t)) t) ∧
      ∀ γ' : ℝ → E →L[ℝ] E →L[ℝ] ℝ,
        (∀ᶠ t in 𝓝 t₀, HasDerivAt γ' (ricciField β (γ' t)) t) → γ' t₀ = g₀ →
          γ' =ᶠ[𝓝 t₀] γ := by
  obtain ⟨γ, hγ0, ε, hε, hγ⟩ := ricciFlow_exists β hg₀.isInvertible t₀
  have hev : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (ricciField β (γ t)) t := by
    filter_upwards [Ioo_mem_nhds (by linarith) (by linarith)] with t ht using hγ t ht
  exact ⟨γ, hγ0, hev, fun γ' h' h0 =>
    ricciFlow_unique β hg₀.isInvertible h' hev h0 hγ0⟩

end Flow

/-! ### Transport from honest Lie algebras

`LieRing 𝔩` and `NormedAddCommGroup 𝔩` cannot be combined on one type (both extend
`AddCommGroup`; nothing in Mathlib resolves the diamond), which is why the results
above carry the bracket explicitly. This section shows nothing was lost: any
finite-dimensional real Lie algebra transports its bracket onto a normed model along
any linear equivalence, alternation and Jacobi included, and the flow statement
follows for the transported structure. -/

section OfLieAlgebra

variable {𝔩 : Type*} [LieRing 𝔩] [LieAlgebra ℝ 𝔩]

/-- The bracket of a finite-dimensional real Lie algebra `𝔩`, transported to the
normed model `E` along a linear equivalence: `β x y = e ⁅e.symm x, e.symm y⁆`. -/
noncomputable def ofLieAlgebra (e : 𝔩 ≃ₗ[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] E →L[ℝ] E).toLinearMap.comp
      (LinearMap.mk₂ ℝ (fun x y => e ⁅e.symm x, e.symm y⁆)
        (fun x x' y => by simp [add_lie])
        (fun c x y => by simp [smul_lie])
        (fun x y y' => by simp [lie_add])
        (fun c x y => by simp [lie_smul])))

@[simp]
theorem ofLieAlgebra_apply (e : 𝔩 ≃ₗ[ℝ] E) (x y : E) :
    ofLieAlgebra e x y = e ⁅e.symm x, e.symm y⁆ := by
  simp [ofLieAlgebra]

theorem ofLieAlgebra_alt (e : 𝔩 ≃ₗ[ℝ] E) (x : E) : ofLieAlgebra e x x = 0 := by
  simp

/-- The transported bracket satisfies the (Leibniz form of the) Jacobi identity.
Recorded for honesty — no result in this file consumes it. -/
theorem ofLieAlgebra_jacobi (e : 𝔩 ≃ₗ[ℝ] E) (x y z : E) :
    ofLieAlgebra e x (ofLieAlgebra e y z) =
      ofLieAlgebra e (ofLieAlgebra e x y) z
        + ofLieAlgebra e y (ofLieAlgebra e x z) := by
  simp [leibniz_lie]

/-- **The Ricci flow exists on any finite-dimensional real Lie algebra**: the
abstract-Lie-algebra phrasing of `ricciFlow_leftInvariant`, along a choice of normed
model `e : 𝔩 ≃ₗ[ℝ] E`. -/
-- BENCH: ricci-flow-lie-algebra
theorem ricciFlow_lieAlgebra (e : 𝔩 ≃ₗ[ℝ] E) {g₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hg₀ : IsInnerProduct g₀) (t₀ : ℝ) :
    ∃ γ : ℝ → E →L[ℝ] E →L[ℝ] ℝ, γ t₀ = g₀ ∧
      (∀ᶠ t in 𝓝 t₀, HasDerivAt γ (ricciField (ofLieAlgebra e) (γ t)) t) ∧
      ∀ γ' : ℝ → E →L[ℝ] E →L[ℝ] ℝ,
        (∀ᶠ t in 𝓝 t₀, HasDerivAt γ' (ricciField (ofLieAlgebra e) (γ' t)) t) →
          γ' t₀ = g₀ → γ' =ᶠ[𝓝 t₀] γ :=
  ricciFlow_leftInvariant (ofLieAlgebra e) hg₀ t₀

end OfLieAlgebra

end LeftInvariant
end RicciFlowBlueprint
