/-
The second Bianchi identity.

For a torsion-free connection on the tangent bundle,

  `(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0`,

where `(∇_X R)(Y,Z)W = ∇_X(R(Y,Z)W) − R(∇_X Y,Z)W − R(Y,∇_X Z)W − R(Y,Z)(∇_X W)`
(`covCurvature`). Expanding everything in terms of iterated covariant derivatives
of `W`, the third-order terms cancel in pairs, the terms with one bracket cancel
in pairs, torsion-freeness turns `∇_X Y − ∇_Y X` into `[X,Y]` wherever it
appears, and what is left is `∇_W` applied to the Jacobi sum of brackets, which
vanishes (`jacobi_mlieBracket_apply`). No metric is involved.

Differentiability: `W` is `C³`, `X`, `Y`, `Z` are `C²`, and the connection is
`C²` (a `C³` section has a `C²` covariant derivative), so that the sections
`∇_Y ∇_Z W` are differentiable and `∇_X` can be applied to them.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.Curvature

open Bundle VectorField
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇_Y σ` is `C^k` when `∇` is `C^k`, `σ` is `C^{k+1}` and `Y` is `C^k`. -/
lemma contMDiff_cov_apply {k : ℕ∞ω} [ContMDiffCovariantDerivative cov k]
    {σ Y : Π y : M, TangentSpace I y}
    (hσ : CMDiff (k + 1) (T% σ)) (hY : CMDiff k (T% Y)) :
    CMDiff k (T% (fun y ↦ cov σ y (Y y))) := by
  have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) k
      (fun y : M ↦ (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) fun y ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)))
      Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := k)).contMDiff hσ.contMDiffOn
  intro y
  have h1 : CMDiffAt k (fun y : M ↦ (TotalSpace.mk' (E →L[ℝ] E)
      (E := fun y : M ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)) y (cov σ y))) y := by
    have h := hcovσ y (Set.mem_univ y)
    rw [contMDiffWithinAt_univ] at h
    exact h
  exact h1.clm_bundle_apply (hY y)

omit [FiniteDimensional ℝ E] in
/-- The Lie bracket is additive on differences in its first slot. -/
lemma _root_.VectorField.mlieBracket_sub_left'
    {U U' W : Π y : M, TangentSpace I y} {x : M}
    (hU : MDiffAt (T% U) x) (hU' : MDiffAt (T% U') x) :
    mlieBracket I (U - U') W x = mlieBracket I U W x - mlieBracket I U' W x := by
  have e : U - U' = U + (fun _ : M ↦ (-1 : ℝ)) • U' := by
    funext y; simp [sub_eq_add_neg]
  have hneg : MDiffAt (T% ((fun _ : M ↦ (-1 : ℝ)) • U')) x := by
    have : (fun _ : M ↦ (-1 : ℝ)) • U' = -U' := by funext y; simp
    rw [this]
    exact mdifferentiableAt_neg_section hU'
  rw [e, mlieBracket_add_left hU hneg, mlieBracket_smul_left mdifferentiableAt_const hU',
    mvfderiv_const]
  simp [sub_eq_add_neg]

/-- **The covariant derivative of the curvature tensor**:
`(∇_X R)(Y,Z)W = ∇_X(R(Y,Z)W) − R(∇_X Y,Z)W − R(Y,∇_X Z)W − R(Y,Z)(∇_X W)`. -/
noncomputable def covCurvature (X Y Z W : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x :=
  cov (fun y ↦ cov.curvature Y Z W y) x (X x)
    - cov.curvature (fun y ↦ cov Y y (X y)) Z W x
    - cov.curvature Y (fun y ↦ cov Z y (X y)) W x
    - cov.curvature Y Z (fun y ↦ cov W y (X y)) x

-- BENCH: bianchi-second
/-- **The second Bianchi identity**: for a torsion-free connection,
`(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0`. -/
theorem bianchi_second [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
    (hcov : cov.torsion = 0)
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X Y Z W x + cov.covCurvature Y Z X W x + cov.covCurvature Z X Y W x
      = 0 := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have h3 : (3 : ℕ∞ω) ≠ 0 := by norm_num
  have hX' : MDiff (T% X) := hX.mdifferentiable h2
  have hY' : MDiff (T% Y) := hY.mdifferentiable h2
  have hZ' : MDiff (T% Z) := hZ.mdifferentiable h2
  have hW2 : CMDiff 2 (T% W) := hW.of_le (by norm_num)
  have hW3 : CMDiff ((2 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]; exact hW
  -- torsion-freeness
  have htf : ∀ {A B : Π y : M, TangentSpace I y} {y : M},
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      cov B y (A y) - cov A y (B y) = mlieBracket I A B y :=
    (torsion_eq_zero_iff cov).mp hcov
  have eXY : (fun y ↦ cov Y y (X y)) - (fun y ↦ cov X y (Y y)) = mlieBracket I X Y := by
    funext y; exact htf (hX' y) (hY' y)
  have eYZ : (fun y ↦ cov Z y (Y y)) - (fun y ↦ cov Y y (Z y)) = mlieBracket I Y Z := by
    funext y; exact htf (hY' y) (hZ' y)
  have eZX : (fun y ↦ cov X y (Z y)) - (fun y ↦ cov Z y (X y)) = mlieBracket I Z X := by
    funext y; exact htf (hZ' y) (hX' y)
  -- brackets of `C²` fields are differentiable
  have hbXY : MDiffAt (T% (mlieBracket I X Y)) x :=
    ((hX x).mlieBracket_vectorField (n := 2) (m := 1) (hY x) (by norm_num)).mdifferentiableAt
      one_ne_zero
  have hbYZ : MDiffAt (T% (mlieBracket I Y Z)) x :=
    ((hY x).mlieBracket_vectorField (n := 2) (m := 1) (hZ x) (by norm_num)).mdifferentiableAt
      one_ne_zero
  have hbZX : MDiffAt (T% (mlieBracket I Z X)) x :=
    ((hZ x).mlieBracket_vectorField (n := 2) (m := 1) (hX x) (by norm_num)).mdifferentiableAt
      one_ne_zero
  -- `∇_V W` is `C²`, so `∇_U ∇_V W` is differentiable
  have c : ∀ {V : Π y : M, TangentSpace I y}, CMDiff 2 (T% V) →
      CMDiff 2 (T% (fun y ↦ cov W y (V y))) := fun hV ↦ cov.contMDiff_cov_apply hW3 hV
  have d : ∀ {U V : Π y : M, TangentSpace I y}, MDiffAt (T% U) x → CMDiff 2 (T% V) →
      MDiffAt (T% (fun y ↦ cov (fun z ↦ cov W z (V z)) y (U y))) x :=
    fun hU hV ↦ cov.mdiffAt_cov_apply (c hV) hU
  -- `∇_{∇_U V} W` is differentiable
  have n : ∀ {U V : Π y : M, TangentSpace I y}, MDiffAt (T% U) x → CMDiff 2 (T% V) →
      MDiffAt (T% (fun y ↦ cov W y (cov V y (U y)))) x :=
    fun hU hV ↦ cov.mdiffAt_cov_apply hW2 (cov.mdiffAt_cov_apply hV hU)
  -- `∇_X (R(Y,Z)W)` split into its three terms
  have s : ∀ {U V T : Π y : M, TangentSpace I y}, MDiffAt (T% U) x → CMDiff 2 (T% V) →
      CMDiff 2 (T% T) → MDiffAt (T% (mlieBracket I V T)) x →
      cov (fun y ↦ cov.curvature V T W y) x (U x)
        = cov (fun y ↦ cov (fun z ↦ cov W z (T z)) y (V y)) x (U x)
          - cov (fun y ↦ cov (fun z ↦ cov W z (V z)) y (T y)) x (U x)
          - cov (fun y ↦ cov W y (mlieBracket I V T y)) x (U x) := by
    intro U V T hU hV hT hVT
    have e : (fun y ↦ cov.curvature V T W y)
        = (fun y ↦ cov (fun z ↦ cov W z (T z)) y (V y))
          - (fun y ↦ cov (fun z ↦ cov W z (V z)) y (T y))
          - (fun y ↦ cov W y (mlieBracket I V T y)) := by
      funext y; rfl
    rw [e, cov.sub_apply (mdifferentiableAt_sub_section
        (cov.mdiffAt_cov_apply (c hT) (hV.mdifferentiable h2 x))
        (cov.mdiffAt_cov_apply (c hV) (hT.mdifferentiable h2 x)))
      (cov.mdiffAt_cov_apply hW2 hVT),
      cov.sub_apply (cov.mdiffAt_cov_apply (c hT) (hV.mdifferentiable h2 x))
        (cov.mdiffAt_cov_apply (c hV) (hT.mdifferentiable h2 x))]
    rfl
  have sX := s (hX' x) hY hZ hbYZ
  have sY := s (hY' x) hZ hX hbZX
  have sZ := s (hZ' x) hX hY hbXY
  -- `∇_{∇_U V} ∇_T W − ∇_{∇_V U} ∇_T W = ∇_{[U,V]} ∇_T W`
  have m : ∀ {U V T : Π y : M, TangentSpace I y}, MDiffAt (T% U) x → MDiffAt (T% V) x →
      cov (fun y ↦ cov W y (T y)) x (cov V x (U x))
        - cov (fun y ↦ cov W y (T y)) x (cov U x (V x))
        = cov (fun y ↦ cov W y (T y)) x (mlieBracket I U V x) := by
    intro U V T hU hV
    rw [← map_sub, htf hU hV]
  have mXY := m (T := Z) (hX' x) (hY' x)
  have mYZ := m (T := X) (hY' x) (hZ' x)
  have mZX := m (T := Y) (hZ' x) (hX' x)
  -- `∇_T ∇_{∇_U V} W − ∇_T ∇_{∇_V U} W = ∇_T ∇_{[U,V]} W`
  have n' : ∀ {U V T : Π y : M, TangentSpace I y}, CMDiff 2 (T% U) → CMDiff 2 (T% V) →
      cov (fun y ↦ cov W y (cov V y (U y))) x (T x)
        - cov (fun y ↦ cov W y (cov U y (V y))) x (T x)
        = cov (fun y ↦ cov W y (mlieBracket I U V y)) x (T x) := by
    intro U V T hU hV
    have e : (fun y ↦ cov W y (cov V y (U y))) - (fun y ↦ cov W y (cov U y (V y)))
        = fun y ↦ cov W y (mlieBracket I U V y) := by
      funext y
      simp only [Pi.sub_apply]
      rw [← map_sub, htf (hU.mdifferentiable h2 y) (hV.mdifferentiable h2 y)]
    rw [← _root_.sub_apply,
      ← cov.sub_apply (n (hU.mdifferentiable h2 x) hV) (n (hV.mdifferentiable h2 x) hU), e]
  have nXY := n' (T := Z) hX hY
  have nYZ := n' (T := X) hY hZ
  have nZX := n' (T := Y) hZ hX
  -- `[∇_U V, T] + [T, ∇_V U] = [[U,V], T]`
  have b : ∀ {U V T : Π y : M, TangentSpace I y}, CMDiff 2 (T% U) → CMDiff 2 (T% V) →
      cov W x (mlieBracket I (fun y ↦ cov V y (U y)) T x)
        + cov W x (mlieBracket I T (fun y ↦ cov U y (V y)) x)
        = cov W x (mlieBracket I (mlieBracket I U V) T x) := by
    intro U V T hU hV
    have e : (fun y ↦ cov V y (U y)) - (fun y ↦ cov U y (V y)) = mlieBracket I U V := by
      funext y; exact htf (hU.mdifferentiable h2 y) (hV.mdifferentiable h2 y)
    rw [mlieBracket_swap_apply (V := T), map_neg, ← sub_eq_add_neg, ← map_sub,
      ← mlieBracket_sub_left' (cov.mdiffAt_cov_apply hV (hU.mdifferentiable h2 x))
        (cov.mdiffAt_cov_apply hU (hV.mdifferentiable h2 x)), e]
  have bXY := b (T := Z) hX hY
  have bYZ := b (T := X) hY hZ
  have bZX := b (T := Y) hZ hX
  -- Jacobi
  have hjac := VectorField.jacobi_mlieBracket_apply (hX x) (hY x) (hZ x) hbZX
  have hj : cov W x (mlieBracket I (mlieBracket I X Y) Z x)
      + cov W x (mlieBracket I (mlieBracket I Y Z) X x)
      + cov W x (mlieBracket I (mlieBracket I Z X) Y x) = 0 := by
    rw [mlieBracket_swap_apply (V := mlieBracket I X Y),
      mlieBracket_swap_apply (V := mlieBracket I Y Z),
      mlieBracket_swap_apply (V := mlieBracket I Z X), map_neg, map_neg, map_neg]
    have := congrArg (cov W x) hjac
    rw [map_add, map_add, map_zero] at this
    linear_combination (norm := module) -this
  simp only [covCurvature]
  rw [sX, sY, sZ]
  simp only [curvature]
  linear_combination (norm := module)
    -mXY - mYZ - mZX + nXY + nYZ + nZX + bXY + bYZ + bZX + hj
