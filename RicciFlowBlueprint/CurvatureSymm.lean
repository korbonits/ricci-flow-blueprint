/-
**The algebraic symmetries of the Riemann tensor**, on a general manifold.

Writing `Rm(X,Y,Z,W) = ⟪R(X,Y)Z, W⟫` for a metric torsion-free connection, the
four classical symmetries are

  `Rm(X,Y,Z,W) = -Rm(Y,X,Z,W)`  (antisymmetry in the first pair),
  `Rm(X,Y,Z,W) = -Rm(X,Y,W,Z)`  (antisymmetry in the second pair),
  `Rm(X,Y,Z,W) + Rm(Y,Z,X,W) + Rm(Z,X,Y,W) = 0`  (first Bianchi), and
  `Rm(X,Y,Z,W) = Rm(Z,W,X,Y)`  (**pair symmetry**).

The first three are already here — `curvature_antisymm` (which needs nothing at
all), `inner_curvature_right_skew` (`Sectional.lean`, from metric compatibility)
and `bianchi_first` (from torsion-freeness). The fourth is not independent: it
follows from the other three by the classical octahedron argument, four copies
of the first Bianchi identity added together. In the six independent unknowns

  `p = Rm(X,Y,Z,W)`, `q = Rm(Z,W,X,Y)`, `r = Rm(Y,Z,X,W)`,
  `s = Rm(Z,X,Y,W)`, `t = Rm(W,Y,Z,X)`, `u = Rm(W,X,Z,Y)`,

the four Bianchi identities read `p + r + s = 0`, `t = q + r`, `q + u + s = 0`,
`t = u + p`, whose only consequence is `p = q`. That is the whole proof, and
`linarith` finds it once the atoms are linked by the two antisymmetries.

Pair symmetry is what makes the curvature an operator on `Λ²T_xM` — the form in
which Hamilton's pinching estimates and Uhlenbeck's trick are stated — and it is
what the second contraction of the second Bianchi identity needs.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.RicciSymm

open Bundle
open scoped Manifold ContDiff

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

section Symmetries

variable {X Y Z W : Π y : M, TangentSpace I y} {x : M}

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **First Bianchi, paired against a vector**: the identity is a vector identity, so the
fourth slot needs no regularity at all. -/
theorem inner_bianchi_first (htor : cov.torsion = 0)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (w : TangentSpace I x) :
    ⟪cov.curvature X Y Z x, w⟫ + ⟪cov.curvature Y Z X x, w⟫
      + ⟪cov.curvature Z X Y x, w⟫ = 0 := by
  have h := cov.bianchi_first (x := x) htor hX hY hZ
  have e : ⟪cov.curvature X Y Z x + cov.curvature Y Z X x + cov.curvature Z X Y x, w⟫
      = ⟪cov.curvature X Y Z x, w⟫ + ⟪cov.curvature Y Z X x, w⟫
        + ⟪cov.curvature Z X Y x, w⟫ := by
    rw [inner_add_left, inner_add_left]
  rw [← e, h, inner_zero_left]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [ContMDiffCovariantDerivative cov 1] in
/-- Antisymmetry in the first pair, at the level of the `(0,4)` tensor. -/
theorem inner_curvature_left_skew (w : TangentSpace I x) :
    ⟪cov.curvature X Y Z x, w⟫ = -⟪cov.curvature Y X Z x, w⟫ := by
  rw [cov.curvature_antisymm X Y Z x, inner_neg_left]

-- BENCH: curvature-pair-symm
/-- **Pair symmetry of the Riemann tensor**: `⟪R(X,Y)Z, W⟫ = ⟪R(Z,W)X, Y⟫`, for a metric
torsion-free connection on a general manifold. Four copies of the first Bianchi identity,
linked by the two antisymmetries. -/
theorem inner_curvature_pair_symm
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫ = ⟪cov.curvature Z W X x, Y x⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have mX : MDiffAt (T% X) x := (hX.mdifferentiable h2) x
  have mY : MDiffAt (T% Y) x := (hY.mdifferentiable h2) x
  have mZ : MDiffAt (T% Z) x := (hZ.mdifferentiable h2) x
  have mW : MDiffAt (T% W) x := (hW.mdifferentiable h2) x
  -- the four Bianchi identities
  have b1 := cov.inner_bianchi_first htor hX hY hZ (W x)
  have b2 := cov.inner_bianchi_first htor hY hZ hW (X x)
  have b3 := cov.inner_bianchi_first htor hZ hW hX (Y x)
  have b4 := cov.inner_bianchi_first htor hW hX hY (Z x)
  -- links, by antisymmetry in the second pair and (where needed) the first
  have l1 : ⟪cov.curvature Y Z X x, W x⟫ = -⟪cov.curvature Y Z W x, X x⟫ :=
    cov.inner_curvature_right_skew hmetric mY mZ hX hW
  have l2 : ⟪cov.curvature Z X Y x, W x⟫ = -⟪cov.curvature Z X W x, Y x⟫ :=
    cov.inner_curvature_right_skew hmetric mZ mX hY hW
  have l2' : ⟪cov.curvature Z X W x, Y x⟫ = -⟪cov.curvature X Z W x, Y x⟫ :=
    cov.inner_curvature_left_skew (Y x)
  have l3 : ⟪cov.curvature Z W Y x, X x⟫ = -⟪cov.curvature Z W X x, Y x⟫ :=
    cov.inner_curvature_right_skew hmetric mZ mW hY hX
  have l4 : ⟪cov.curvature W Y Z x, X x⟫ = -⟪cov.curvature W Y X x, Z x⟫ :=
    cov.inner_curvature_right_skew hmetric mW mY hZ hX
  have l4' : ⟪cov.curvature W Y X x, Z x⟫ = -⟪cov.curvature Y W X x, Z x⟫ :=
    cov.inner_curvature_left_skew (Z x)
  have l5 : ⟪cov.curvature W X Z x, Y x⟫ = -⟪cov.curvature W X Y x, Z x⟫ :=
    cov.inner_curvature_right_skew hmetric mW mX hZ hY
  have l6 : ⟪cov.curvature X Y W x, Z x⟫ = -⟪cov.curvature X Y Z x, W x⟫ :=
    cov.inner_curvature_right_skew hmetric mX mY hW hZ
  linarith

/-- Antisymmetry in the second pair, restated here for the record. -/
theorem inner_curvature_right_skew'
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫ = -⟪cov.curvature X Y W x, Z x⟫ :=
  cov.inner_curvature_right_skew hmetric hX hY hZ hW

end Symmetries

end CovariantDerivative
