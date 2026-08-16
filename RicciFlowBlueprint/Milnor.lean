/-
Milnor's curvature formulas for left-invariant metrics, after
J. Milnor, *Curvatures of left invariant metrics on Lie groups*,
Advances in Mathematics **21** (1976), 293–329, in the algebraic setting of
`Homogeneous.lean` (bracket `β : E →L[ℝ] E →L[ℝ] E`, metric
`g : E →L[ℝ] E →L[ℝ] ℝ`).

## Contents

* **The structure-constant formulas** (any dimension). With
  `α i j k = ⟨[eᵢ,eⱼ], eₖ⟩` for an orthonormal basis `{eᵢ}`:
  - `apply_koszul_apply_milnor` — the connection, basis-free:
    `⟨∇ₓy, z⟩ = ½(⟨[x,y],z⟩ − ⟨[y,z],x⟩ + ⟨[z,x],y⟩)`; specialized to basis
    vectors this is Milnor's `⟨∇_{eᵢ}eⱼ, eₖ⟩ = ½(α i j k − α j k i + α k i j)`.
  - `koszul_orthonormal_expand` — the connection as an explicit combination of
    basis vectors with those coefficients.
  - `ricciBilin_eq_sum_curvature` — `Ric(x,y) = Σ_w ⟨R(e_w,x)y, e_w⟩`.
  - `ricciBilin_structureConstants` — Ricci fully expanded into structure
    constants: a double sum of products of `⟨∇··, ·⟩`- and `α`-terms, the
    computational backbone of Milnor's paper.
  - `scalar_eq_sum_ricciBilin` — `scal = Σᵢ Ric(eᵢ, eᵢ)`, the trace of
    `g⁻¹ ∘ Ric` (`scalar`, `Homogeneous.lean`) computed in an orthonormal frame.

* **The three-dimensional case** (`IsMilnorFrame`). A *Milnor frame* is an
  orthonormal (more generally `g`-diagonal) basis `b₀, b₁, b₂` with
  `[b₁,b₂] = λ₀ b₀`, `[b₂,b₀] = λ₁ b₁`, `[b₀,b₁] = λ₂ b₂`. Milnor's Lemma 4.1
  (every 3-dimensional unimodular metric Lie algebra admits such a frame) is
  **assumed, not proved**: the frame and the `λᵢ` enter as hypotheses.
  - `koszul_milnorFrame` — the full connection table `∇_{bᵢ}bⱼ`.
  - `ricciBilin_milnorFrame` — **Ricci is diagonal in a Milnor frame**, with
    eigenvalues `rᵢ = 2 μⱼ μₖ` where `μᵢ = ½(λⱼ + λₖ − λᵢ)` (`milnorMu`);
    equivalently `rᵢ = ½(λᵢ² − (λⱼ − λₖ)²)`.
  - `scalar_milnorFrame` — `scal = 2(μ₀μ₁ + μ₁μ₂ + μ₂μ₀)`, the sum of the
    principal Ricci curvatures.
  - `ricciBilin_milnorFrame_diag` / `ricciField_milnorFrame_diag` — the same
    computation for the diagonal metric `g(bᵢ,bⱼ) = δᵢⱼ dᵢ` (write
    `(A,B,C) = (d₀,d₁,d₂)`): Ricci is again diagonal, with
    `Ric(b₀,b₀) = 2 P₁ P₂ / (BC)` cyclically, where
    `Pᵢ = ½(dⱼλⱼ + dₖλₖ − dᵢλᵢ)` (`milnorP`). Hence Hamilton's equation
    `∂g/∂t = −2 Ric(g)` **preserves the diagonal ansatz** and reduces to the
    explicit ODE system

        A' = −4 P₁ P₂ / (BC),  B' = −4 P₂ P₀ / (CA),  C' = −4 P₀ P₁ / (AB),

    the classical Ricci-flow system on 3-dimensional unimodular Lie groups
    (cf. Isenberg–Jackson). `ricciField_milnorFrame_diag` states exactly this:
    the value of the Ricci flow vector field of `ricciFlow_leftInvariant` at a
    diagonal metric is diagonal with these entries.

* **A corollary in Milnor's §4** (`ricci_heisenberg_mixed_sign`): for the
  Heisenberg algebra (a Milnor frame with `λ₁ = λ₂ = 0 ≠ λ₀` — the non-abelian
  nilpotent case in dimension 3) the principal Ricci curvatures are
  `(λ₀²/2, −λ₀²/2, −λ₀²/2)`: there are directions of strictly positive and of
  strictly negative Ricci curvature, an instance of Milnor's Theorem 2.4.

## Conventions

Ours are those of `Homogeneous.lean`/`Ricci.lean`:
`R(x,y) = ∇ₓ∇_y − ∇_y∇ₓ − ∇_{[x,y]}` and `Ric(x,y) = tr(w ↦ R(w,x)y)`, so the
round metric has positive Ricci curvature. Milnor's paper uses the opposite
sign for the curvature transformation (`R_{xy} = ∇_{[x,y]} + [∇_y, ∇ₓ]`, his
§3) *and* contracts it with the opposite slot order, so his sectional and
Ricci *values* agree with ours; all formulas below match the numbers in his
paper (e.g. the Heisenberg principal Ricci curvatures `(λ²/2, −λ²/2, −λ²/2)`
of his §4).

No result here concludes anything about a Lie *group*: as in
`Homogeneous.lean` the development is purely algebraic.
-/
import Mathlib.Data.Fin.VecNotation
import RicciFlowBlueprint.Homogeneous

open Set Filter Topology Module ContinuousLinearMap

set_option maxSynthPendingDepth 3

namespace RicciFlowBlueprint
namespace LeftInvariant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {β : E →L[ℝ] E →L[ℝ] E} {g : E →L[ℝ] E →L[ℝ] ℝ}

/-! ### Bases: pairing, trace, diagonal metrics

Small general lemmas: vectors are determined by their `g`-pairings with a basis
(when `g` is invertible), the trace of an endomorphism is the sum of diagonal
coordinates in any basis, and a basis that diagonalizes `g` with positive
entries witnesses `IsInnerProduct g`. -/

section BasisLemmas

variable {ι : Type*} (b : Basis ι ℝ E)

/-- Two vectors with the same `g`-pairings against a basis are equal (for
invertible `g`). The workhorse for computing `koszul` from `koszulRHS`. -/
theorem eq_of_apply_basis (hg : g.IsInvertible) {v w : E}
    (h : ∀ k, g v (b k) = g w (b k)) : v = w :=
  injective_of_isInvertible hg (ContinuousLinearMap.coe_injective (b.ext fun k => h k))

variable [Fintype ι] [DecidableEq ι]

/-- The trace of a continuous endomorphism as the sum of its diagonal
coordinates in a basis. -/
theorem trace_eq_sum_repr (f : E →L[ℝ] E) :
    LinearMap.trace ℝ E ↑f = ∑ w, b.repr (f (b w)) w := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]

variable {d : ι → ℝ}

/-- Expansion of `g` in a `g`-diagonal basis: `g(x,y) = Σᵢ dᵢ xᵢ yᵢ`. -/
theorem apply_apply_of_diag (hdiag : ∀ i j, g (b i) (b j) = if i = j then d i else 0)
    (x y : E) : g x y = ∑ i, d i * (b.repr x i * b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hdiag, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A basis diagonalizing `g` with positive diagonal entries witnesses
`IsInnerProduct g` — in particular `g` is invertible, so `koszul β g` is the
honest Levi-Civita connection. -/
theorem isInnerProduct_of_diag (hdiag : ∀ i j, g (b i) (b j) = if i = j then d i else 0)
    (hd : ∀ i, 0 < d i) : IsInnerProduct g where
  symm x y := by
    rw [apply_apply_of_diag b hdiag, apply_apply_of_diag b hdiag]
    exact Finset.sum_congr rfl fun i _ => by ring
  posDef x hx := by
    rw [apply_apply_of_diag b hdiag]
    have hne : ∃ i, b.repr x i ≠ 0 := by
      by_contra hall
      exact hx (b.repr.map_eq_zero_iff.mp
        (Finsupp.ext fun i => not_not.mp (not_exists.mp hall i)))
    obtain ⟨i, hi⟩ := hne
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (mul_self_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hd i) (mul_self_pos.mpr hi)⟩

/-- An orthonormal basis witnesses `IsInnerProduct g`. -/
theorem isInnerProduct_of_orthonormal (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    IsInnerProduct g :=
  isInnerProduct_of_diag b (d := fun _ => 1) (by simpa using hb) fun _ => one_pos

/-- In an orthonormal basis, coordinates are `g`-pairings: `xᵢ = g(x, bᵢ)`.
(Only first-slot linearity of `g` is used; no symmetry needed.) -/
theorem repr_apply_orthonormal (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (x : E) (m : ι) : b.repr x m = g x (b m) := by
  have hx : g x (b m) = ∑ i, b.repr x i * g (b i) (b m) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum, sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_apply, smul_eq_mul]
  rw [hx]
  simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end BasisLemmas

/-! ### The structure-constant formulas (Milnor, any dimension)

For an orthonormal basis `{eᵢ}` write `α i j k = ⟨[eᵢ,eⱼ], eₖ⟩ = g (β (b i) (b j)) (b k)`.
The Koszul connection and the Ricci form are polynomial in the `α`'s. -/

section StructureConstants

variable {ι : Type*} (b : Basis ι ℝ E)

/-- **Milnor's formula for the Levi-Civita connection of a left-invariant
metric** (basis-free): `⟨∇ₓy, z⟩ = ½(⟨[x,y],z⟩ − ⟨[y,z],x⟩ + ⟨[z,x],y⟩)`.
At orthonormal basis vectors this is `⟨∇_{eᵢ}eⱼ, eₖ⟩ = ½(αᵢⱼₖ − αⱼₖᵢ + αₖᵢⱼ)`. -/
-- BENCH: milnor-connection-formula
theorem apply_koszul_apply_milnor (hβ : ∀ x, β x x = 0) (hg : g.IsInvertible) (x y z : E) :
    g (koszul β g x y) z = 2⁻¹ * (g (β x y) z - g (β y z) x + g (β z x) y) := by
  rw [apply_koszul_apply β hg, koszulRHS_apply, skew_of_alt hβ x z]
  simp only [map_neg, neg_apply]
  ring

variable [Fintype ι] [DecidableEq ι]

/-- The connection at basis vectors, expanded in the basis: for orthonormal
`{eᵢ}`, `∇_{eᵢ}eⱼ = Σₖ ½(α i j k − α j k i + α k i j) • eₖ`. -/
theorem koszul_orthonormal_expand (hβ : ∀ x, β x x = 0) (hg : g.IsInvertible)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) (i j : ι) :
    koszul β g (b i) (b j) =
      ∑ k, (2⁻¹ * (g (β (b i) (b j)) (b k) - g (β (b j) (b k)) (b i)
        + g (β (b k) (b i)) (b j))) • b k := by
  conv_lhs => rw [← b.sum_repr (koszul β g (b i) (b j))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_apply_orthonormal b hb, apply_koszul_apply_milnor hβ hg]

/-- Right-slot basis expansion of a Koszul pairing (orthonormal basis). -/
theorem apply_koszul_expand_right (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (a v : E) (k : ι) :
    g (koszul β g a v) (b k) = ∑ m, g v (b m) * g (koszul β g a (b m)) (b k) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, map_sum, sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, map_smul, smul_apply, smul_eq_mul, repr_apply_orthonormal b hb]

/-- Left-slot basis expansion of a Koszul pairing (orthonormal basis). -/
theorem apply_koszul_expand_left (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (u y : E) (k : ι) :
    g (koszul β g u y) (b k) = ∑ m, g u (b m) * g (koszul β g (b m) y) (b k) := by
  conv_lhs => rw [← b.sum_repr u]
  rw [map_sum, sum_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_apply, map_smul, smul_apply, smul_eq_mul,
    repr_apply_orthonormal b hb]

variable [FiniteDimensional ℝ E]

/-- **Ricci as an orthonormal-frame sum**: `Ric(x,y) = Σ_w ⟨R(e_w, x)y, e_w⟩`. -/
-- BENCH: milnor-ricci-frame-sum
theorem ricciBilin_eq_sum_curvature (hβ : ∀ x, β x x = 0)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) (x y : E) :
    ricciBilin β g x y = ∑ w, g (curvature β g (b w) x y) (b w) := by
  rw [ricciBilin_apply, trace_eq_sum_repr b]
  exact Finset.sum_congr rfl fun w _ => by
    rw [repr_apply_orthonormal b hb, ricciEndo_apply_eq_curvature β g hβ]

-- BENCH: scalar-frame-sum
/-- **Scalar curvature as an orthonormal-frame sum**: `scal = Σᵢ Ric(bᵢ, bᵢ)`. The
trace of `g⁻¹ ∘ Ric` computed in a `g`-orthonormal basis, where coordinates are
`g`-pairings and `g ∘ g⁻¹ = id`. -/
theorem scalar_eq_sum_ricciBilin (hg : g.IsInvertible)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    scalar β g = ∑ i, ricciBilin β g (b i) (b i) := by
  have haux : ∀ f : E →L[ℝ] ℝ, g (g.inverse f) = f := by
    obtain ⟨A, rfl⟩ := hg
    intro f
    simp
  rw [scalar, traceCLM_apply, trace_eq_sum_repr b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_apply_orthonormal b hb, ContinuousLinearMap.comp_apply, haux]

/-- **Ricci in structure constants** (Milnor's computational backbone): for an
orthonormal basis, with all pairings written out,

`Ric(x,y) = Σ_w Σ_m (⟨∇ₓy,eₘ⟩⟨∇_{e_w}eₘ,e_w⟩ − ⟨∇_{e_w}y,eₘ⟩⟨∇ₓeₘ,e_w⟩
             − ⟨[e_w,x],eₘ⟩⟨∇_{eₘ}y,e_w⟩)`.

At `x = eᵢ, y = eⱼ` every factor is a structure constant via
`apply_koszul_apply_milnor`: `⟨∇_{eᵢ}eⱼ,eₖ⟩ = ½(αᵢⱼₖ − αⱼₖᵢ + αₖᵢⱼ)`. -/
-- BENCH: milnor-ricci-structure-constants
theorem ricciBilin_structureConstants (hβ : ∀ x, β x x = 0)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) (x y : E) :
    ricciBilin β g x y = ∑ w, ∑ m,
      (g (koszul β g x y) (b m) * g (koszul β g (b w) (b m)) (b w)
        - g (koszul β g (b w) y) (b m) * g (koszul β g x (b m)) (b w)
        - g (β (b w) x) (b m) * g (koszul β g (b m) y) (b w)) := by
  rw [ricciBilin_apply, trace_eq_sum_repr b]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [repr_apply_orthonormal b hb, ricciEndo_apply, map_add, add_apply, map_sub, sub_apply,
    apply_koszul_expand_right b hb (b w) (koszul β g x y) w,
    apply_koszul_expand_right b hb x (koszul β g (b w) y) w,
    apply_koszul_expand_left b hb (β x (b w)) y w,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [skew_of_alt hβ (b w) x]
  simp only [map_neg, neg_apply]
  ring

end StructureConstants

/-! ### Dimension three: Milnor frames

Milnor's Lemma 4.1: every 3-dimensional *unimodular* metric Lie algebra has an
orthonormal basis `b₀, b₁, b₂` with `[b₁,b₂] = λ₀ b₀`, `[b₂,b₀] = λ₁ b₁`,
`[b₀,b₁] = λ₂ b₂`. Here the existence of the frame is a *hypothesis*
(`IsMilnorFrame` for the bracket relations, plus a diagonality hypothesis on
the metric); the classification is not formalized. -/

/-- A **Milnor frame** for the bracket `β`: a basis of a 3-dimensional space
satisfying the cyclic bracket relations `[b₁,b₂] = λ₀ b₀`, `[b₂,b₀] = λ₁ b₁`,
`[b₀,b₁] = λ₂ b₂`. Existence for unimodular brackets (Milnor, Lemma 4.1) is
assumed, not proved. -/
structure IsMilnorFrame (β : E →L[ℝ] E →L[ℝ] E) (b : Basis (Fin 3) ℝ E)
    (l : Fin 3 → ℝ) : Prop where
  bracket₁₂ : β (b 1) (b 2) = l 0 • b 0
  bracket₂₀ : β (b 2) (b 0) = l 1 • b 1
  bracket₀₁ : β (b 0) (b 1) = l 2 • b 2

namespace IsMilnorFrame

variable {b : Basis (Fin 3) ℝ E} {l : Fin 3 → ℝ}

theorem bracket₂₁ (hf : IsMilnorFrame β b l) (hβ : ∀ x, β x x = 0) :
    β (b 2) (b 1) = -(l 0 • b 0) := by
  rw [skew_of_alt hβ (b 1) (b 2), hf.bracket₁₂]

theorem bracket₀₂ (hf : IsMilnorFrame β b l) (hβ : ∀ x, β x x = 0) :
    β (b 0) (b 2) = -(l 1 • b 1) := by
  rw [skew_of_alt hβ (b 2) (b 0), hf.bracket₂₀]

theorem bracket₁₀ (hf : IsMilnorFrame β b l) (hβ : ∀ x, β x x = 0) :
    β (b 1) (b 0) = -(l 2 • b 2) := by
  rw [skew_of_alt hβ (b 0) (b 1), hf.bracket₀₁]

end IsMilnorFrame

/-- Milnor's `μᵢ = ½(λⱼ + λₖ − λᵢ)` (indices cyclic): the connection
coefficients of a Milnor frame, and the half-sums appearing in the principal
Ricci curvatures `rᵢ = 2 μⱼ μₖ`. -/
noncomputable def milnorMu (l : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(l 1 + l 2 - l 0) / 2, (l 2 + l 0 - l 1) / 2, (l 0 + l 1 - l 2) / 2]

/-- The weighted Milnor coefficients `Pᵢ = ½(dⱼλⱼ + dₖλₖ − dᵢλᵢ)` for the
diagonal metric `g(bᵢ,bⱼ) = δᵢⱼ dᵢ` on a Milnor frame; `milnorP l 1 = milnorMu l`. -/
noncomputable def milnorP (l d : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(d 1 * l 1 + d 2 * l 2 - d 0 * l 0) / 2,
    (d 2 * l 2 + d 0 * l 0 - d 1 * l 1) / 2,
    (d 0 * l 0 + d 1 * l 1 - d 2 * l 2) / 2]

@[simp]
theorem milnorP_one (l : Fin 3 → ℝ) : milnorP l (fun _ => 1) = milnorMu l := by
  funext i
  fin_cases i <;> simp [milnorP, milnorMu]

section MilnorFrame

variable [FiniteDimensional ℝ E] {b : Basis (Fin 3) ℝ E} {l d : Fin 3 → ℝ}

/-- **The Levi-Civita connection of a diagonal metric in a Milnor frame** —
the full table `∇_{bᵢ}bⱼ`. With `Pᵢ = milnorP l d i`:

`∇_{b₀}b₁ = (P₀/d₂) b₂`, `∇_{b₁}b₀ = −(P₁/d₂) b₂` (cyclically), `∇_{bᵢ}bᵢ = 0`.

For the orthonormal case (`d = 1`) this is Milnor's `∇_{bᵢ}bⱼ = ± μ bₖ` table. -/
-- BENCH: milnor-connection-table
theorem koszul_milnorFrame (hβ : ∀ x, β x x = 0) (hf : IsMilnorFrame β b l)
    (hdiag : ∀ i j, g (b i) (b j) = if i = j then d i else 0) (hd : ∀ i, 0 < d i) :
    ∀ i j, koszul β g (b i) (b j) =
      ![![0, (milnorP l d 0 / d 2) • b 2, -((milnorP l d 0 / d 1) • b 1)],
        ![-((milnorP l d 1 / d 2) • b 2), 0, (milnorP l d 1 / d 0) • b 0],
        ![(milnorP l d 2 / d 1) • b 1, -((milnorP l d 2 / d 0) • b 0), 0]] i j := by
  have hg : g.IsInvertible := (isInnerProduct_of_diag b hdiag hd).isInvertible
  have hd0 : d 0 ≠ 0 := (hd 0).ne'
  have hd1 : d 1 ≠ 0 := (hd 1).ne'
  have hd2 : d 2 ≠ 0 := (hd 2).ne'
  intro i j
  fin_cases i <;> fin_cases j <;>
    (refine eq_of_apply_basis b hg fun k => ?_;
     rw [apply_koszul_apply β hg, koszulRHS_apply];
     fin_cases k <;>
       simp [hβ, hf.bracket₁₂, hf.bracket₂₀, hf.bracket₀₁, hf.bracket₂₁ hβ, hf.bracket₀₂ hβ,
         hf.bracket₁₀ hβ, hdiag, milnorP, map_smul, map_neg, smul_apply, neg_apply,
         smul_eq_mul] <;>
       field_simp <;> ring)

/-- **Ricci of a diagonal metric in a Milnor frame is diagonal**, with
`Ric(bᵢ,bᵢ) = 2 Pⱼ Pₖ / (dⱼ dₖ)` (cyclic), `Pᵢ = ½(dⱼλⱼ + dₖλₖ − dᵢλᵢ)`.
Writing `(A,B,C) = (d₀,d₁,d₂)` this is Milnor's computation, generalized from
orthonormal to diagonal metrics — the form needed for the Ricci flow ODE. -/
-- BENCH: milnor-ricci-diagonal-metric
theorem ricciBilin_milnorFrame_diag (hβ : ∀ x, β x x = 0) (hf : IsMilnorFrame β b l)
    (hdiag : ∀ i j, g (b i) (b j) = if i = j then d i else 0) (hd : ∀ i, 0 < d i)
    (i j : Fin 3) :
    ricciBilin β g (b i) (b j) =
      if i = j then
        2 * milnorP l d (i + 1) * milnorP l d (i + 2) / (d (i + 1) * d (i + 2))
      else 0 := by
  have hkoz := koszul_milnorFrame hβ hf hdiag hd
  have hd0 : d 0 ≠ 0 := (hd 0).ne'
  have hd1 : d 1 ≠ 0 := (hd 1).ne'
  have hd2 : d 2 ≠ 0 := (hd 2).ne'
  rw [ricciBilin_apply, trace_eq_sum_repr b, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    (simp [ricciEndo_apply, hβ, hf.bracket₁₂, hf.bracket₂₀, hf.bracket₀₁, hf.bracket₂₁ hβ,
       hf.bracket₀₂ hβ, hf.bracket₁₀ hβ, hkoz, map_smul, map_neg, smul_apply, neg_apply,
       smul_eq_mul, map_add, Basis.repr_self, milnorP] <;>
     field_simp <;> ring)

/-- **Milnor's diagonalization theorem** (the headline of his §4 computation):
in an orthonormal Milnor frame, Ricci is diagonal with eigenvalues
`rᵢ = 2 μⱼ μₖ`, `μᵢ = ½(λⱼ + λₖ − λᵢ)` — equivalently
`rᵢ = ½(λᵢ² − (λⱼ − λₖ)²)`. -/
-- BENCH: milnor-ricci-diagonal
theorem ricciBilin_milnorFrame (hβ : ∀ x, β x x = 0) (hf : IsMilnorFrame β b l)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) (i j : Fin 3) :
    ricciBilin β g (b i) (b j) =
      if i = j then 2 * milnorMu l (i + 1) * milnorMu l (i + 2) else 0 := by
  have h := ricciBilin_milnorFrame_diag (d := fun _ => 1) hβ hf (by simpa using hb)
    (fun _ => one_pos) i j
  simpa using h

-- BENCH: milnor-scalar
/-- **Milnor's scalar curvature formula**: in an orthonormal Milnor frame,
`scal = 2(μ₀μ₁ + μ₁μ₂ + μ₂μ₀)` — the sum of the principal Ricci curvatures
`rᵢ = 2 μⱼ μₖ` of `ricciBilin_milnorFrame`. (Sanity check: the round `SU(2)` has
`λᵢ = 2`, so `μᵢ = 1` and `scal = 6`, the scalar curvature of the unit 3-sphere.) -/
theorem scalar_milnorFrame (hβ : ∀ x, β x x = 0) (hf : IsMilnorFrame β b l)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0) :
    scalar β g = 2 * (milnorMu l 0 * milnorMu l 1 + milnorMu l 1 * milnorMu l 2
      + milnorMu l 2 * milnorMu l 0) := by
  have hg : g.IsInvertible := (isInnerProduct_of_orthonormal b hb).isInvertible
  have h0 := ricciBilin_milnorFrame hβ hf hb 0 0
  have h1 := ricciBilin_milnorFrame hβ hf hb 1 1
  have h2 := ricciBilin_milnorFrame hβ hf hb 2 2
  norm_num [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at h0 h1 h2
  rw [scalar_eq_sum_ricciBilin b hg hb, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- **The Ricci flow of a left-invariant metric on a 3-dimensional unimodular
Lie algebra is an explicit ODE system**: at a diagonal metric
`g(bᵢ,bⱼ) = δᵢⱼ dᵢ` (write `(A,B,C) = (d₀,d₁,d₂)`), the Ricci flow vector
field `g ↦ −2 Ric(g)` of `ricciFlow_leftInvariant` is again diagonal, with
entries

`A' = −4 P₁ P₂ / (BC)`, `B' = −4 P₂ P₀ / (CA)`, `C' = −4 P₀ P₁ / (AB)`,

`Pᵢ = ½(dⱼλⱼ + dₖλₖ − dᵢλᵢ)`: the diagonal ansatz is invariant and Hamilton's
PDE reduces to this system in `(A,B,C)`. -/
-- BENCH: milnor-ricci-flow-ode
theorem ricciField_milnorFrame_diag (hβ : ∀ x, β x x = 0) (hf : IsMilnorFrame β b l)
    (hdiag : ∀ i j, g (b i) (b j) = if i = j then d i else 0) (hd : ∀ i, 0 < d i)
    (i j : Fin 3) :
    ricciField β g (b i) (b j) =
      if i = j then
        -4 * milnorP l d (i + 1) * milnorP l d (i + 2) / (d (i + 1) * d (i + 2))
      else 0 := by
  simp only [ricciField, smul_apply, smul_eq_mul,
    ricciBilin_milnorFrame_diag hβ hf hdiag hd i j]
  split_ifs <;> ring

/-- **Milnor's mixed-sign theorem, Heisenberg case**: for the 3-dimensional
Heisenberg algebra (Milnor frame with `λ₁ = λ₂ = 0`, `λ₀ ≠ 0` — non-abelian
and nilpotent), the principal Ricci curvatures are `(λ₀²/2, −λ₀²/2, −λ₀²/2)`:
Ricci is strictly positive in the center direction and strictly negative in
the two complementary directions. An instance of Milnor's Theorem 2.4 (a
non-abelian nilpotent metric Lie algebra has directions of both signs). -/
-- BENCH: milnor-heisenberg-mixed-sign
theorem ricci_heisenberg_mixed_sign (hβ : ∀ x, β x x = 0) (hf : IsMilnorFrame β b l)
    (hb : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (h1 : l 1 = 0) (h2 : l 2 = 0) (h0 : l 0 ≠ 0) :
    0 < ricciBilin β g (b 0) (b 0) ∧
      ricciBilin β g (b 1) (b 1) < 0 ∧ ricciBilin β g (b 2) (b 2) < 0 := by
  have hsq : 0 < l 0 * l 0 := mul_self_pos.mpr h0
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [ricciBilin_milnorFrame hβ hf hb];
     simp [milnorMu, h1, h2];
     nlinarith)

end MilnorFrame

end LeftInvariant
end RicciFlowBlueprint
