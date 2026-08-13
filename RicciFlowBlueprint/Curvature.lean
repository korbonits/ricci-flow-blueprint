/-
Riemann curvature of a covariant derivative.

Upstream target: `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature.lean`.
A richer version — curvature packaged as a tensor, with first-two-slot
tensoriality — is drafted on the `riemann-curvature` branch of mathlib4; rebase
that before extending this file. What is here is the bare operator, enough to
state the identities the blueprint depends on.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorField.LieBracket

open Bundle VectorField
open scoped Manifold ContDiff

namespace VectorField

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ω M]
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- The cyclic (Jacobi) form of the Leibniz identity for the Lie bracket of vector fields:
`[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`.

Mathlib supplies only the Leibniz form `[U,[V,W]] = [[U,V],W] + [V,[U,W]]`; converting needs
antisymmetry in both slots. -/
lemma jacobi_mlieBracket_apply
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x)
    (hZX : MDiffAt (T% (mlieBracket I Z X)) x) :
    mlieBracket I X (mlieBracket I Y Z) x + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x = 0 := by
  have hm : minSmoothness ℝ 2 = 2 := by simp
  have cX : CMDiffAt (minSmoothness ℝ 2) (T% X) x := by rw [hm]; exact hX
  have cY : CMDiffAt (minSmoothness ℝ 2) (T% Y) x := by rw [hm]; exact hY
  have cZ : CMDiffAt (minSmoothness ℝ 2) (T% Z) x := by rw [hm]; exact hZ
  have L := leibniz_identity_mlieBracket_apply (I := I) (U := X) (V := Y) (W := Z) cX cY cZ
  -- `[[X,Y],Z] = -[Z,[X,Y]]`
  have e₁ : mlieBracket I (mlieBracket I X Y) Z x = - mlieBracket I Z (mlieBracket I X Y) x :=
    mlieBracket_swap_apply ..
  -- `[Y,[X,Z]] = -[Y,[Z,X]]`, via `[X,Z] = -[Z,X]` as sections
  have e₂ : mlieBracket I Y (mlieBracket I X Z) x = - mlieBracket I Y (mlieBracket I Z X) x := by
    have hswap : mlieBracket I X Z = (-1 : ℝ) • mlieBracket I Z X := by
      rw [mlieBracket_swap]; funext w; simp
    rw [hswap, mlieBracket_const_smul_right hZX]
    module
  rw [L, e₁, e₂]
  abel

end VectorField

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `cov` negates. -/
lemma neg_apply {τ : Π y : M, TangentSpace I y} {y : M} (hτ : MDiffAt (T% τ) y) :
    cov (-τ) y = -cov τ y := by
  have h : (-τ) = (-1 : ℝ) • τ := by funext z; simp
  rw [h, cov.isCovariantDerivativeOn.smul_const (-1 : ℝ) hτ]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `cov` is additive on differences of differentiable sections. -/
lemma sub_apply {σ τ : Π y : M, TangentSpace I y} {y : M}
    (hσ : MDiffAt (T% σ) y) (hτ : MDiffAt (T% τ) y) :
    cov (σ - τ) y = cov σ y - cov τ y := by
  have h : σ - τ = σ + (-τ) := by funext z; simp [sub_eq_add_neg]
  rw [h, cov.isCovariantDerivativeOn.add hσ (mdifferentiableAt_neg_section hτ),
    cov.neg_apply hτ]
  module



omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇_Y σ` is differentiable at `x` when `∇` is `C^1`, `σ` is `C^2` and `Y` is differentiable. -/
lemma mdiffAt_cov_apply [ContMDiffCovariantDerivative cov 1]
    {σ Y : Π y : M, TangentSpace I y} {x : M}
    (hσ : CMDiff 2 (T% σ)) (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (fun y ↦ cov σ y (Y y))) x := by
  -- the Hom-bundle section `y ↦ cov σ y`
  have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y : M ↦ (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) fun y ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)))
      Set.univ := by
    exact (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 1)).contMDiff (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hσ.contMDiffOn)
  have h1 : MDiffAt (fun y : M ↦ (TotalSpace.mk' (E →L[ℝ] E)
      (E := fun y : M ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)) y (cov σ y))) x := by
    have h := hcovσ x (Set.mem_univ x)
    rw [contMDiffWithinAt_univ] at h
    exact h.mdifferentiableAt one_ne_zero
  exact h1.clm_bundle_apply hY

/-- The curvature operator `R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.

Note the nonstandard argument order inherited from `CovariantDerivative`:
`cov σ x (X x)` is `(∇_X σ) x` on paper. -/
noncomputable def curvature (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov (fun y ↦ cov Z y (Y y)) x (X x) - cov (fun y ↦ cov Z y (X y)) x (Y x)
    - cov Z x (mlieBracket I X Y x)

-- BENCH: curvature-antisymm
-- The curvature operator is antisymmetric in its first two arguments:
-- R(X, Y)Z = -R(Y, X)Z.
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem curvature_antisymm (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    cov.curvature X Y Z x = - cov.curvature Y X Z x := by
  simp only [curvature, mlieBracket_swap_apply (I := I) (V := Y) (W := X), map_neg]
  abel

-- BENCH: bianchi-first
/-- First Bianchi identity, with the differentiability side conditions taken as explicit
hypotheses. -/
theorem bianchi_first_of_mdiff (hcov : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x)
    (hZY : MDiffAt (T% (fun y ↦ cov Y y (Z y))) x)
    (hZX : MDiffAt (T% (fun y ↦ cov X y (Z y))) x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x)
    (hXY : MDiffAt (T% (fun y ↦ cov Y y (X y))) x)
    (hYX : MDiffAt (T% (fun y ↦ cov X y (Y y))) x)
    :
    cov.curvature X Y Z x + cov.curvature Y Z X x + cov.curvature Z X Y x = 0 := by
  have h1 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hX' : MDiff (T% X) := hX.mdifferentiable h1
  have hY' : MDiff (T% Y) := hY.mdifferentiable h1
  have hZ' : MDiff (T% Z) := hZ.mdifferentiable h1
  -- Brackets of C² fields are C¹, hence differentiable.
  have hbYZ : MDiffAt (T% (mlieBracket I Y Z)) x :=
    ((hY x).mlieBracket_vectorField (n := 2) (m := 1) (hZ x) (by norm_num)).mdifferentiableAt one_ne_zero
  have hbZX : MDiffAt (T% (mlieBracket I Z X)) x :=
    ((hZ x).mlieBracket_vectorField (n := 2) (m := 1) (hX x) (by norm_num)).mdifferentiableAt one_ne_zero
  have hbXY : MDiffAt (T% (mlieBracket I X Y)) x :=
    ((hX x).mlieBracket_vectorField (n := 2) (m := 1) (hY x) (by norm_num)).mdifferentiableAt one_ne_zero
  have hjac := VectorField.jacobi_mlieBracket_apply (hX x) (hY x) (hZ x) hbZX
  have htf : ∀ {A B : Π y : M, TangentSpace I y} {y : M},
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      cov B y (A y) - cov A y (B y) = mlieBracket I A B y :=
    (torsion_eq_zero_iff cov).mp hcov
  -- Torsion-freeness as an identity of sections.
  have eYZ : (fun y ↦ cov Z y (Y y)) - (fun y ↦ cov Y y (Z y)) = mlieBracket I Y Z := by
    funext y; exact htf (hY' y) (hZ' y)
  have eZX : (fun y ↦ cov X y (Z y)) - (fun y ↦ cov Z y (X y)) = mlieBracket I Z X := by
    funext y; exact htf (hZ' y) (hX' y)
  have eXY : (fun y ↦ cov Y y (X y)) - (fun y ↦ cov X y (Y y)) = mlieBracket I X Y := by
    funext y; exact htf (hX' y) (hY' y)
  -- Group the cyclic sum by the direction slot.
  have gX : cov (fun y ↦ cov Z y (Y y)) x (X x) - cov (fun y ↦ cov Y y (Z y)) x (X x)
      = cov (mlieBracket I Y Z) x (X x) := by
    rw [← _root_.sub_apply, ← cov.sub_apply hYZ hZY, eYZ]
  have gY : cov (fun y ↦ cov X y (Z y)) x (Y x) - cov (fun y ↦ cov Z y (X y)) x (Y x)
      = cov (mlieBracket I Z X) x (Y x) := by
    rw [← _root_.sub_apply, ← cov.sub_apply hZX hXZ, eZX]
  have gZ : cov (fun y ↦ cov Y y (X y)) x (Z x) - cov (fun y ↦ cov X y (Y y)) x (Z x)
      = cov (mlieBracket I X Y) x (Z x) := by
    rw [← _root_.sub_apply, ← cov.sub_apply hXY hYX, eXY]
  -- Torsion-freeness again, now on the pairs (X, [Y,Z]) and cyclic.
  have tX := htf (hX' x) hbYZ
  have tY := htf (hY' x) hbZX
  have tZ := htf (hZ' x) hbXY
  simp only [curvature]
  linear_combination (norm := module) gX + gY + gZ + tX + tY + tZ + hjac


-- BENCH: bianchi-first-clean
-- First Bianchi identity for a `C^1` connection and `C^2` vector fields, with every
-- differentiability side condition discharged.
theorem bianchi_first [ContMDiffCovariantDerivative cov 1] (hcov : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    cov.curvature X Y Z x + cov.curvature Y Z X x + cov.curvature Z X Y x = 0 := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  exact cov.bianchi_first_of_mdiff hcov hX hY hZ
    (cov.mdiffAt_cov_apply hZ ((hY.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hY ((hZ.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hX ((hZ.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hZ ((hX.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hY ((hX.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hX ((hY.mdifferentiable h2) x))

-- (superseded) the clean form of `bianchi_first`, deriving the differentiability side
-- conditions from smoothness of `X`, `Y`, `Z` rather than assuming them. Needs
-- `[ContMDiffCovariantDerivative cov k]` (smoothness of `∇` is a typeclass, not
-- part of `CovariantDerivative`) plus a lemma applying a `C^k` Hom-bundle
-- section to a `C^k` section. Brackets come from
-- `ContDiff.mlieBracket_vectorField`, and Jacobi from
-- `leibniz_identity_mlieBracket_apply` combined with `mlieBracket_swap_apply`.
-- That is bookkeeping, not mathematics: the content is `bianchi_first_of_mdiff`.

omit [FiniteDimensional ℝ E] in
/-- `R(fX, Y)Z = f · R(X, Y)Z`: the curvature operator is `C^∞(M)`-linear in its
first slot. This is the content of first-slot tensoriality — the obstruction to
defining Ricci curvature. -/
theorem curvature_smul_left (f : M → ℝ) (X Y Z : Π y : M, TangentSpace I y) {x : M}
    (hf : MDiffAt f x)
    (hX : MDiffAt (T% X) x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x) :
    cov.curvature (f • X) Y Z x = f x • cov.curvature X Y Z x := by
  -- `∇_{f•X} Z = f • ∇_X Z`, pointwise by linearity of the direction slot.
  have hpi : ∀ y, (f • X) y = f y • X y := fun _ ↦ rfl
  have hsec : (fun y ↦ cov Z y ((f • X) y)) = f • (fun y ↦ cov Z y (X y)) := by
    funext y; simp [hpi]
  simp only [curvature]
  -- reshape the middle term into `cov (f • σ)` so Leibniz applies, then expand
  rw [hsec, cov.isCovariantDerivativeOn.leibniz hXZ hf, mlieBracket_smul_left hf hX]
  simp only [hpi, map_smul, map_add, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  module

omit [FiniteDimensional ℝ E] in
/-- `R(X, fY)Z = f · R(X, Y)Z`, immediately from antisymmetry and the first slot. -/
theorem curvature_smul_middle (f : M → ℝ) (X Y Z : Π y : M, TangentSpace I y) {x : M}
    (hf : MDiffAt f x)
    (hY : MDiffAt (T% Y) x)
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x) :
    cov.curvature X (f • Y) Z x = f x • cov.curvature X Y Z x := by
  rw [cov.curvature_antisymm X (f • Y) Z x,
    cov.curvature_smul_left f Y X Z hf hY hYZ,
    cov.curvature_antisymm Y X Z x]
  module

omit [FiniteDimensional ℝ E] in
/-- `R(X, Y)(fZ) = f · R(X, Y)Z`, assuming the bracket acts as a derivation on
functions. That identity — `[X,Y]f = X(Yf) - Y(Xf)` — is not in Mathlib; it
needs symmetry of the second derivative transported to manifolds. Everything
else in slot-3 tensoriality is discharged here. -/
theorem curvature_smul_right_of_derivation
    (f : M → ℝ) (X Y Z : Π y : M, TangentSpace I y) {x : M}
    (hf : MDiff f) (hZ : MDiff (T% Z))
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x)
    (hYf : MDiffAt (fun y ↦ d% f y (Y y)) x)
    (hXf : MDiffAt (fun y ↦ d% f y (X y)) x)
    (hfYZ : MDiffAt (T% (f • fun y ↦ cov Z y (Y y))) x)
    (hfXZ : MDiffAt (T% (f • fun y ↦ cov Z y (X y))) x)
    (hgYZ : MDiffAt (T% ((fun y ↦ d% f y (Y y)) • Z)) x)
    (hgXZ : MDiffAt (T% ((fun y ↦ d% f y (X y)) • Z)) x)
    -- the missing identity: the Lie bracket is a derivation on functions
    (hder : d% (fun y ↦ d% f y (Y y)) x (X x) - d% (fun y ↦ d% f y (X y)) x (Y x)
              = d% f x (mlieBracket I X Y x)) :
    cov.curvature X Y (f • Z) x = f x • cov.curvature X Y Z x := by
  have hsecY : (fun y ↦ cov (f • Z) y (Y y))
      = (f • fun y ↦ cov Z y (Y y)) + ((fun y ↦ d% f y (Y y)) • Z) := by
    funext y; simp [cov.isCovariantDerivativeOn.leibniz (hZ y) (hf y)]
  have hsecX : (fun y ↦ cov (f • Z) y (X y))
      = (f • fun y ↦ cov Z y (X y)) + ((fun y ↦ d% f y (X y)) • Z) := by
    funext y; simp [cov.isCovariantDerivativeOn.leibniz (hZ y) (hf y)]
  simp only [curvature, hsecY, hsecX,
    cov.isCovariantDerivativeOn.add hfYZ hgYZ,
    cov.isCovariantDerivativeOn.add hfXZ hgXZ,
    cov.isCovariantDerivativeOn.leibniz hYZ (hf x),
    cov.isCovariantDerivativeOn.leibniz hXZ (hf x),
    cov.isCovariantDerivativeOn.leibniz (hZ x) hYf,
    cov.isCovariantDerivativeOn.leibniz (hZ x) hXf,
    cov.isCovariantDerivativeOn.leibniz (hZ x) (hf x)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have key : (d% (fun y ↦ d% f y (Y y)) x (X x) - d% (fun y ↦ d% f y (X y)) x (Y x)) • Z x
      = (d% f x (mlieBracket I X Y x)) • Z x := by rw [hder]
  linear_combination (norm := module) key

-- Sectional curvature needs the metric, so it is stated alongside the
-- Levi-Civita connection once `sectionalCurvature` is ported from the
-- `riemann-curvature` branch.

end CovariantDerivative
