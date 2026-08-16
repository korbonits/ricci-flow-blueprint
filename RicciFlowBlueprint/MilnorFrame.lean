/-
**Milnor's classification lemma** (J. Milnor, *Curvatures of left invariant
metrics on Lie groups*, Advances in Mathematics **21** (1976), Lemma 4.1):
every 3-dimensional **unimodular** metric Lie algebra admits a *Milnor frame* —
an orthonormal basis `b₀, b₁, b₂` and reals `λ₀, λ₁, λ₂` with

    [b₁,b₂] = λ₀ b₀,  [b₂,b₀] = λ₁ b₁,  [b₀,b₁] = λ₂ b₂.

This discharges the `IsMilnorFrame` hypothesis that `Milnor.lean` takes as an
assumption, closing the one soft spot of that file.

## Proof

Fix an orthonormal basis `e₀, e₁, e₂` and let `crossOB` be the coordinate cross
product it defines (`Λ²F ≅ F` in dimension 3). The alternating bracket factors
through it: `[x,y] = L (x × y)` for the linear map `L` with `L e₀ = [e₁,e₂]`,
`L e₁ = [e₂,e₀]`, `L e₂ = [e₀,e₁]` (`bracket_eq_crossL` — both sides are
bilinear and agree on basis pairs). The crux is that **unimodularity
(`IsUnimodular`: every `ad x` is trace-free) says exactly that `L` is
self-adjoint** (`isSymmetric_crossL`): the trace of `ad eᵢ` is the difference
of the two off-diagonal matrix entries `⟨L eₖ, eⱼ⟩ − ⟨L eⱼ, eₖ⟩`. The spectral
theorem (`LinearMap.IsSymmetric.eigenvectorBasis`) then produces an orthonormal
eigenbasis `b` of `L`; since `bᵢ × bⱼ` is orthogonal to `bᵢ` and `bⱼ` it is a
scalar multiple of the third basis vector, so `[bᵢ,bⱼ] = L (bᵢ × bⱼ)` is that
multiple of `μₖ bₖ` — a Milnor frame. Two economies: the Jacobi identity is
never consumed (Lemma 4.1 is a statement about alternating unimodular
brackets), and no orientation needs to be chosen — the eigenbasis need not be
re-oriented because the `λ`'s absorb the sign of `⟨bₖ, bᵢ × bⱼ⟩`.

## The bridge

The rest of the project deliberately keeps the metric out of the instance
system (`g : E →L[ℝ] E →L[ℝ] ℝ`, see the design notes of `Homogeneous.lean`),
while the spectral theorem needs an honest `InnerProductSpace` instance. This
lemma concerns a single fixed metric, so the abstract statement is proved on an
inner product space (`exists_orthonormalBasis_isMilnorFrame`) and transported:

* `IsInnerProduct.exists_orthonormal_basis` — Gram–Schmidt for the explicit
  form `g`: a `g`-orthonormal basis, from
  `LinearMap.BilinForm.exists_orthogonal_basis` plus normalization by
  `√(g v v)` (positive definiteness makes the diagonal positive).
* Such a basis gives a linear model `φ : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)`
  carrying `g` to the standard inner product; the bracket transports along `φ`
  (same device as `ofLieAlgebra` in `Homogeneous.lean`), alternation and
  unimodularity (`LinearMap.trace_conj'`) included, and the Milnor frame of
  the transported bracket pulls back.

The headline `exists_milnorFrame` produces, for any alternating unimodular
`β` and any `IsInnerProduct g` in dimension 3, a `g`-orthonormal basis `b` and
`l : Fin 3 → ℝ` with `IsMilnorFrame β b l` — exactly the hypotheses consumed
by `ricciBilin_milnorFrame` and `ricciField_milnorFrame_diag` in `Milnor.lean`.
`exists_milnorFrame_ricci_diagonal` records the combination: on a
3-dimensional unimodular metric Lie algebra, Ricci is diagonalizable in a
`g`-orthonormal frame with principal curvatures `rᵢ = 2 μⱼ μₖ`, with no frame
hypothesis left.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import RicciFlowBlueprint.Milnor

open Module ContinuousLinearMap

set_option maxSynthPendingDepth 3

namespace RicciFlowBlueprint
namespace LeftInvariant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bracket is **unimodular** when every `ad x = β x` is trace-free
(Milnor, §4). For a Lie group this is the left-invariance of right Haar
measure, stated algebraically. -/
def IsUnimodular (β : E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∀ x, LinearMap.trace ℝ E (β x : E →ₗ[ℝ] E) = 0

/-! ### The abstract classification, on an inner product space -/

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (β : F →L[ℝ] F →L[ℝ] F) (e : OrthonormalBasis (Fin 3) ℝ F)

/-- The coordinate cross product attached to an orthonormal basis `e` of a
3-dimensional inner product space: the usual `x × y` formula in
`e`-coordinates. This realizes `Λ²F ≅ F`; no orientation is chosen (a
different orthonormal basis gives ± this map, a sign the Milnor `λ`'s absorb). -/
private noncomputable def crossOB (x y : F) : F :=
  (e.repr x 1 * e.repr y 2 - e.repr x 2 * e.repr y 1) • e 0
    + (e.repr x 2 * e.repr y 0 - e.repr x 0 * e.repr y 2) • e 1
    + (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) • e 2

/-- The factor of the bracket through the cross product: the linear map with
`L e₀ = [e₁,e₂]`, `L e₁ = [e₂,e₀]`, `L e₂ = [e₀,e₁]`. -/
private noncomputable def crossL : F →ₗ[ℝ] F :=
  e.toBasis.constr ℝ ![β (e 1) (e 2), β (e 2) (e 0), β (e 0) (e 1)]

private theorem crossL_apply₀ : crossL β e (e 0) = β (e 1) (e 2) := by
  simpa [crossL, OrthonormalBasis.coe_toBasis] using
    e.toBasis.constr_basis ℝ ![β (e 1) (e 2), β (e 2) (e 0), β (e 0) (e 1)] 0

private theorem crossL_apply₁ : crossL β e (e 1) = β (e 2) (e 0) := by
  simpa [crossL, OrthonormalBasis.coe_toBasis] using
    e.toBasis.constr_basis ℝ ![β (e 1) (e 2), β (e 2) (e 0), β (e 0) (e 1)] 1

private theorem crossL_apply₂ : crossL β e (e 2) = β (e 0) (e 1) := by
  simpa [crossL, OrthonormalBasis.coe_toBasis] using
    e.toBasis.constr_basis ℝ ![β (e 1) (e 2), β (e 2) (e 0), β (e 0) (e 1)] 2

/-- Coordinates against an orthonormal basis are inner products, in the form
used below. -/
private theorem inner_basis (x : F) (i : Fin 3) : inner ℝ x (e i) = e.repr x i := by
  rw [real_inner_comm]
  exact (e.repr_apply_apply x i).symm

/-- The cross product is orthogonal to its first factor. -/
private theorem inner_crossOB_left (x y : F) : inner ℝ x (crossOB e x y) = 0 := by
  simp only [crossOB, inner_add_right, real_inner_smul_right, inner_basis]
  ring

/-- The cross product is orthogonal to its second factor. -/
private theorem inner_crossOB_right (x y : F) : inner ℝ y (crossOB e x y) = 0 := by
  simp only [crossOB, inner_add_right, real_inner_smul_right, inner_basis]
  ring

/-- **The bracket factors through the cross product**: `[x,y] = L (x × y)`.
Both sides are bilinear and agree on basis pairs (only alternation of `β` is
used). This is the isomorphism `Λ²F ≅ F` doing its work; dimension 3 is
essential. -/
private theorem bracket_eq_crossL (hβ : ∀ x, β x x = 0) (x y : F) :
    β x y = crossL β e (crossOB e x y) := by
  conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
  simp only [crossOB, map_sum, map_smulₛₗ, RingHom.id_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, Fin.sum_univ_three,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_add, map_smul, crossL_apply₀, crossL_apply₁, crossL_apply₂, hβ,
    skew_of_alt hβ (e 1) (e 2), skew_of_alt hβ (e 2) (e 0), skew_of_alt hβ (e 0) (e 1)]
  module

/-- **Unimodularity says exactly that `L` is self-adjoint** — the crux of
Milnor's Lemma 4.1. Tracing `ad eᵢ` in the orthonormal basis produces the
difference of the two `(j,k)` off-diagonal entries of `L`; unimodularity kills
all three differences, and the diagonal is symmetric for free. -/
private theorem isSymmetric_crossL (hβ : ∀ x, β x x = 0) (huni : IsUnimodular β) :
    (crossL β e).IsSymmetric := by
  -- the trace of `ad x` as an orthonormal-frame sum
  have htr : ∀ x : F, inner ℝ (e 0) (β x (e 0)) + inner ℝ (e 1) (β x (e 1))
      + inner ℝ (e 2) (β x (e 2)) = 0 := by
    intro x
    have h := huni x
    rw [trace_eq_sum_repr e.toBasis (β x), Fin.sum_univ_three] at h
    simpa only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      e.repr_apply_apply] using h
  -- the three off-diagonal symmetries, from unimodularity at `e₀, e₁, e₂`
  have h0 := htr (e 0)
  have h1 := htr (e 1)
  have h2 := htr (e 2)
  rw [show β (e 0) (e 2) = -β (e 2) (e 0) from skew_of_alt hβ (e 2) (e 0),
    ← crossL_apply₂ β e, ← crossL_apply₁ β e, hβ] at h0
  rw [show β (e 1) (e 0) = -β (e 0) (e 1) from skew_of_alt hβ (e 0) (e 1),
    ← crossL_apply₂ β e, ← crossL_apply₀ β e, hβ] at h1
  rw [show β (e 2) (e 1) = -β (e 1) (e 2) from skew_of_alt hβ (e 1) (e 2),
    ← crossL_apply₁ β e, ← crossL_apply₀ β e, hβ] at h2
  simp only [inner_zero_right, inner_neg_right, zero_add, add_zero] at h0 h1 h2
  -- symmetry of the matrix of `L`
  have hsym : ∀ i j : Fin 3,
      inner ℝ (crossL β e (e i)) (e j) = inner ℝ (e i) (crossL β e (e j)) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      first
        | exact real_inner_comm _ _
        | (rw [real_inner_comm]; linarith)
        | linarith
  -- bilinear expansion
  intro x y
  conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
  conv_rhs => rw [← e.sum_repr x, ← e.sum_repr y]
  simp only [Fin.sum_univ_three, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hsym]

variable {β}

/-- **Milnor's Lemma 4.1, abstract form**: a 3-dimensional real inner product
space with an alternating unimodular bracket admits an orthonormal Milnor
frame. The frame is an orthonormal eigenbasis of the self-adjoint factor `L`
of the bracket through the cross product; `λᵢ = ⟨bᵢ, bⱼ × bₖ⟩ μᵢ` where `μᵢ`
is the `i`-th eigenvalue. -/
-- BENCH: milnor-classification-abstract
theorem exists_orthonormalBasis_isMilnorFrame (hdim : finrank ℝ F = 3)
    (hβ : ∀ x, β x x = 0) (huni : IsUnimodular β) :
    ∃ (b : OrthonormalBasis (Fin 3) ℝ F) (l : Fin 3 → ℝ),
      IsMilnorFrame β b.toBasis l := by
  -- an auxiliary orthonormal basis, defining the cross product and `L`
  let e : OrthonormalBasis (Fin 3) ℝ F := (stdOrthonormalBasis ℝ F).reindex (finCongr hdim)
  have hL : (crossL β e).IsSymmetric := isSymmetric_crossL β e hβ huni
  -- the spectral theorem: an orthonormal eigenbasis of `L`
  let b : OrthonormalBasis (Fin 3) ℝ F := hL.eigenvectorBasis hdim
  let μ : Fin 3 → ℝ := hL.eigenvalues hdim
  have hbe : ∀ i, crossL β e (b i) = μ i • b i := fun i =>
    hL.apply_eigenvectorBasis hdim i
  -- `bᵢ × bⱼ` is orthogonal to `bᵢ` and `bⱼ`, hence a multiple of `bₖ`
  have hv12 : crossOB e (b 1) (b 2) = inner ℝ (b 0) (crossOB e (b 1) (b 2)) • b 0 := by
    have h := b.sum_repr' (crossOB e (b 1) (b 2))
    rw [Fin.sum_univ_three, inner_crossOB_left, inner_crossOB_right] at h
    simpa using h.symm
  have hv20 : crossOB e (b 2) (b 0) = inner ℝ (b 1) (crossOB e (b 2) (b 0)) • b 1 := by
    have h := b.sum_repr' (crossOB e (b 2) (b 0))
    rw [Fin.sum_univ_three, inner_crossOB_left, inner_crossOB_right] at h
    simpa using h.symm
  have hv01 : crossOB e (b 0) (b 1) = inner ℝ (b 2) (crossOB e (b 0) (b 1)) • b 2 := by
    have h := b.sum_repr' (crossOB e (b 0) (b 1))
    rw [Fin.sum_univ_three, inner_crossOB_left, inner_crossOB_right] at h
    simpa using h.symm
  refine ⟨b, ![inner ℝ (b 0) (crossOB e (b 1) (b 2)) * μ 0,
    inner ℝ (b 1) (crossOB e (b 2) (b 0)) * μ 1,
    inner ℝ (b 2) (crossOB e (b 0) (b 1)) * μ 2], ?_, ?_, ?_⟩
  · show β (b.toBasis 1) (b.toBasis 2) = _ • b.toBasis 0
    simp only [OrthonormalBasis.coe_toBasis, Matrix.cons_val_zero]
    conv_lhs => rw [bracket_eq_crossL β e hβ, hv12, map_smul, hbe 0, smul_smul]
  · show β (b.toBasis 2) (b.toBasis 0) = _ • b.toBasis 1
    simp only [OrthonormalBasis.coe_toBasis, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_zero]
    conv_lhs => rw [bracket_eq_crossL β e hβ, hv20, map_smul, hbe 1, smul_smul]
  · show β (b.toBasis 0) (b.toBasis 1) = _ • b.toBasis 2
    simp only [OrthonormalBasis.coe_toBasis, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    conv_lhs => rw [bracket_eq_crossL β e hβ, hv01, map_smul, hbe 2, smul_smul]

end InnerProductSpace

/-! ### The bridge to the explicit-metric setting of `Milnor.lean` -/

section Bridge

variable [FiniteDimensional ℝ E]
variable {β : E →L[ℝ] E →L[ℝ] E} {g : E →L[ℝ] E →L[ℝ] ℝ}

/-- **Gram–Schmidt for an explicit inner product**: every `IsInnerProduct g`
admits a `g`-orthonormal basis. From `LinearMap.BilinForm.exists_orthogonal_basis`
(diagonalization of symmetric bilinear forms) plus normalization by `√(g v v)`,
which positive definiteness makes possible. -/
theorem IsInnerProduct.exists_orthonormal_basis (hg : IsInnerProduct g) :
    ∃ w : Basis (Fin (finrank ℝ E)) ℝ E,
      ∀ i j, g (w i) (w j) = if i = j then 1 else 0 := by
  classical
  -- `g` as an algebraic bilinear form
  let B : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ (fun x y => g x y)
    (fun x x' y => by simp) (fun c x y => by simp)
    (fun x y y' => by simp) (fun c x y => by simp)
  have hBg : ∀ x y, B x y = g x y := fun x y => rfl
  have hB : B.IsSymm := ⟨fun x y => by simpa [hBg] using hg.symm x y⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hpos : ∀ i, 0 < g (v i) (v i) := fun i => hg.posDef (v i) (v.ne_zero i)
  have hsqrt : ∀ i, Real.sqrt (g (v i) (v i)) ≠ 0 :=
    fun i => Real.sqrt_ne_zero'.mpr (hpos i)
  -- normalize
  let c : Fin (finrank ℝ E) → ℝˣ := fun i =>
    Units.mk0 (Real.sqrt (g (v i) (v i)))⁻¹ (inv_ne_zero (hsqrt i))
  refine ⟨v.unitsSMul c, fun i j => ?_⟩
  rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
    map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    simp only [c, Units.val_mk0]
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (hpos i).le,
      inv_mul_cancel₀ (hpos i).ne']
  · rw [if_neg hij, show (g (v i)) (v j) = 0 from hv hij, mul_zero, mul_zero]

variable (β) in
/-- **Milnor's classification lemma (Lemma 4.1), bridged**: a 3-dimensional
space with an explicit inner product `g : E →L[ℝ] E →L[ℝ] ℝ` and an
alternating unimodular bracket admits a `g`-orthonormal Milnor frame. The
conclusion pairs `IsMilnorFrame` with exactly the orthonormality hypothesis
`hb` consumed by `ricciBilin_milnorFrame` and `ricci_heisenberg_mixed_sign`
in `Milnor.lean`, so the frame existence assumed there is now discharged. -/
-- BENCH: milnor-classification
theorem exists_milnorFrame (hg : IsInnerProduct g) (hdim : finrank ℝ E = 3)
    (hβ : ∀ x, β x x = 0) (huni : IsUnimodular β) :
    ∃ (b : Basis (Fin 3) ℝ E) (l : Fin 3 → ℝ),
      IsMilnorFrame β b l ∧ ∀ i j, g (b i) (b j) = if i = j then 1 else 0 := by
  classical
  -- a `g`-orthonormal basis, reindexed to `Fin 3`
  obtain ⟨w₀, hw₀⟩ := hg.exists_orthonormal_basis
  let w : Basis (Fin 3) ℝ E := w₀.reindex (finCongr hdim)
  have hw : ∀ i j, g (w i) (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [Basis.reindex_apply, Basis.reindex_apply, hw₀]
    simp [Equiv.symm_apply_eq]
  -- the coordinate model carrying `g` to the standard inner product
  let φ : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    w.equivFun.trans (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm
  have hφ_apply : ∀ (x : E) (i : Fin 3), φ x i = w.repr x i := fun x i => rfl
  have hginner : ∀ x y : E, inner ℝ (φ x) (φ y) = g x y := by
    intro x y
    rw [apply_apply_of_diag w (d := fun _ => 1) (by simpa using hw) x y]
    simp [PiLp.inner_apply, RCLike.inner_apply, hφ_apply, mul_comm]
  -- the transported bracket (same device as `ofLieAlgebra`)
  let β' : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
          (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) ≃ₗ[ℝ]
            EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).toLinearMap.comp
        (LinearMap.mk₂ ℝ (fun x y => φ (β (φ.symm x) (φ.symm y)))
          (fun x x' y => by simp)
          (fun c x y => by simp)
          (fun x y y' => by simp)
          (fun c x y => by simp)))
  have hβ'app : ∀ x y, β' x y = φ (β (φ.symm x) (φ.symm y)) := fun x y => by
    simp [β']
  have hβ' : ∀ x, β' x x = 0 := fun x => by simp [hβ'app, hβ]
  have huni' : IsUnimodular β' := by
    intro x
    have hconj : (β' x : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
        = φ.conj (β (φ.symm x) : E →ₗ[ℝ] E) := by
      ext y
      simp [hβ'app, LinearEquiv.conj_apply_apply]
    rw [hconj, LinearMap.trace_conj']
    exact huni _
  -- the abstract classification in the model
  obtain ⟨b', l, hf'⟩ := exists_orthonormalBasis_isMilnorFrame
    (F := EuclideanSpace ℝ (Fin 3)) finrank_euclideanSpace_fin hβ' huni'
  -- pull the frame back
  have hpull : ∀ x y : EuclideanSpace ℝ (Fin 3),
      β (φ.symm x) (φ.symm y) = φ.symm (β' x y) := by
    intro x y
    rw [hβ'app, LinearEquiv.symm_apply_apply]
  refine ⟨b'.toBasis.map φ.symm, l, ⟨?_, ?_, ?_⟩, fun i j => ?_⟩
  · rw [Basis.map_apply, Basis.map_apply, Basis.map_apply, OrthonormalBasis.coe_toBasis,
      hpull,
      show β' (b' 1) (b' 2) = l 0 • b' 0 by
        simpa [OrthonormalBasis.coe_toBasis] using hf'.bracket₁₂,
      map_smul]
  · rw [Basis.map_apply, Basis.map_apply, Basis.map_apply, OrthonormalBasis.coe_toBasis,
      hpull,
      show β' (b' 2) (b' 0) = l 1 • b' 1 by
        simpa [OrthonormalBasis.coe_toBasis] using hf'.bracket₂₀,
      map_smul]
  · rw [Basis.map_apply, Basis.map_apply, Basis.map_apply, OrthonormalBasis.coe_toBasis,
      hpull,
      show β' (b' 0) (b' 1) = l 2 • b' 2 by
        simpa [OrthonormalBasis.coe_toBasis] using hf'.bracket₀₁,
      map_smul]
  · rw [Basis.map_apply, Basis.map_apply, OrthonormalBasis.coe_toBasis, ← hginner,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact orthonormal_iff_ite.mp b'.orthonormal i j

variable (β) in
/-- **Ricci curvature of a 3-dimensional unimodular metric Lie algebra is
diagonalizable**, with principal Ricci curvatures `rᵢ = 2 μⱼ μₖ`,
`μᵢ = ½(λⱼ + λₖ − λᵢ)`: the combination of the classification lemma
(`exists_milnorFrame`) with Milnor's computation
(`ricciBilin_milnorFrame`) — no frame hypothesis remains. -/
-- BENCH: milnor-ricci-diagonalizable
theorem exists_milnorFrame_ricci_diagonal (hg : IsInnerProduct g)
    (hdim : finrank ℝ E = 3) (hβ : ∀ x, β x x = 0) (huni : IsUnimodular β) :
    ∃ (b : Basis (Fin 3) ℝ E) (l : Fin 3 → ℝ),
      IsMilnorFrame β b l ∧
      (∀ i j, g (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ i j, ricciBilin β g (b i) (b j) =
        if i = j then 2 * milnorMu l (i + 1) * milnorMu l (i + 2) else 0 := by
  obtain ⟨b, l, hf, hb⟩ := exists_milnorFrame β hg hdim hβ huni
  exact ⟨b, l, hf, hb, fun i j => ricciBilin_milnorFrame hβ hf hb i j⟩

end Bridge

end LeftInvariant
end RicciFlowBlueprint
