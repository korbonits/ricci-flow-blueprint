/-
The first variation of the curvature.

Two connections `∇` and `∇'` on the tangent bundle differ by a tensor
`A(Y, Z) = ∇'_Y Z − ∇_Y Z` (Mathlib's `CovariantDerivative.difference`), and their
curvatures differ by

  `R'(X,Y)Z = R(X,Y)Z + (∇_X A)(Y,Z) − (∇_Y A)(X,Z) + A(X, A(Y,Z)) − A(Y, A(X,Z))`

when `∇` is torsion-free (`curvature_eq_add_covEnd`). Along a one-parameter family
`∇ᵗ` with `∇ᵗ = ∇ + Aᵗ`, `Aᵗ⁰ = 0` and `∂ₜ Aᵗ = Ȧ` at `t₀`, the quadratic terms
have zero derivative and

  `∂ₜ Rᵗ(X,Y)Z = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)`

(`hasDerivAt_curvatureE`). This is the first half of `lem:evolution-rm`: with
`Ȧ = ∂ₜ ∇` given by the first variation of the Levi-Civita connection
(`Variation.lean`), it is `∂ₜ Rm` in terms of `∇² h` for `h = ∂ₜ g`; the
second half, the rewriting of `∇²(Ric)` as `Δ Rm + Q(Rm)` through the second
Bianchi identity, is separate.

One hypothesis is again a commutation: `∂ₜ` and `∇_X` applied to the section
`y ↦ Aᵗ(Y,Z)(y)` commute at `x`. As in `Variation.lean` it is joint regularity
in `(t, x)`, taken in exactly the form used.

Time derivatives are stated on `E`, not on `TangentSpace I x` (which carries
no norm): `curvatureE`, `covE`, `covEndE`. The algebraic identity is stated on
the tangent spaces.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`,
and for a one-form `A x : T_xM →L T_xM →L T_xM`, `A x (σ x) (X x)` is
`A(X, σ)(x)` on paper.
-/
import RicciFlowBlueprint.Variation
import Mathlib.Analysis.Calculus.Deriv.Mul

open Bundle CovariantDerivative VectorField
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The **covariant derivative of an endomorphism-valued one-form** `A`, where
`A y (Z y) (Y y)` is `A(Y, Z)(y)` on paper:
`(∇_X A)(Y, Z) = ∇_X (A(Y, Z)) − A(∇_X Y, Z) − A(Y, ∇_X Z)`. -/
noncomputable def covEnd
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) : TangentSpace I x :=
  cov (fun y ↦ A y (Z y) (Y y)) x (X x)
    - A x (Z x) (cov Y x (X x)) - A x (cov Z x (X x)) (Y x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The section `y ↦ A(Y, Z)(y)` is differentiable at `x` when `A = ∇' − ∇` for two `C¹`
connections, `Z` is `C²` and `Y` is differentiable at `x`. -/
lemma mdiffAt_difference_apply
    (cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov' 1]
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ∀ (σ : Π y : M, TangentSpace I y) (y : M), MDiffAt (T% σ) y →
      ∀ v : TangentSpace I y, cov' σ y v = cov σ y v + A y (σ y) v)
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (fun y ↦ A y (Z y) (Y y))) x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hZm : MDiff (T% Z) := hZ.mdifferentiable h2
  have e : (fun y ↦ A y (Z y) (Y y)) =
      (fun y ↦ cov' Z y (Y y)) - (fun y ↦ cov Z y (Y y)) := by
    funext y
    simp only [Pi.sub_apply]
    rw [hA Z y (hZm y) (Y y)]
    abel
  have := mdifferentiableAt_sub_section (cov'.mdiffAt_cov_apply hZ hY)
    (cov.mdiffAt_cov_apply hZ hY)
  rw [← e] at this
  exact this

-- BENCH: curvature-difference
/-- **Curvature of a perturbed connection.** If `∇' = ∇ + A` on differentiable sections and
`∇` is torsion-free, then
`R'(X,Y)Z = R(X,Y)Z + (∇_X A)(Y,Z) − (∇_Y A)(X,Z) + A(X, A(Y,Z)) − A(Y, A(X,Z))`. -/
theorem curvature_eq_add_covEnd
    (cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov' 1]
    (hcov : cov.torsion = 0)
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ∀ (σ : Π y : M, TangentSpace I y) (y : M), MDiffAt (T% σ) y →
      ∀ v : TangentSpace I y, cov' σ y v = cov σ y v + A y (σ y) v)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov'.curvature X Y Z x = cov.curvature X Y Z x
      + cov.covEnd A X Y Z x - cov.covEnd A Y X Z x
      + A x (A x (Z x) (Y x)) (X x) - A x (A x (Z x) (X x)) (Y x) := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hZm : MDiff (T% Z) := hZ.mdifferentiable h2
  -- the inner derivatives of `∇'` split as `∇ + A`, as sections
  have eY : (fun y ↦ cov' Z y (Y y)) =
      (fun y ↦ cov Z y (Y y)) + (fun y ↦ A y (Z y) (Y y)) := by
    funext y; exact hA Z y (hZm y) (Y y)
  have eX : (fun y ↦ cov' Z y (X y)) =
      (fun y ↦ cov Z y (X y)) + (fun y ↦ A y (Z y) (X y)) := by
    funext y; exact hA Z y (hZm y) (X y)
  have hσY := cov.mdiffAt_cov_apply hZ hY
  have hσX := cov.mdiffAt_cov_apply hZ hX
  have hτY := cov.mdiffAt_difference_apply cov' hA hZ hY
  have hτX := cov.mdiffAt_difference_apply cov' hA hZ hX
  -- torsion-freeness of `∇`
  have hb := (torsion_eq_zero_iff cov).mp hcov hX hY
  -- expand the three terms of `R'`
  have t1 : cov' (fun y ↦ cov' Z y (Y y)) x (X x) =
      cov (fun y ↦ cov Z y (Y y)) x (X x) + A x (cov Z x (Y x)) (X x)
        + cov (fun y ↦ A y (Z y) (Y y)) x (X x) + A x (A x (Z x) (Y x)) (X x) := by
    rw [eY, cov'.isCovariantDerivativeOn.add hσY hτY, add_apply,
      hA _ x hσY (X x), hA _ x hτY (X x)]
    abel
  have t2 : cov' (fun y ↦ cov' Z y (X y)) x (Y x) =
      cov (fun y ↦ cov Z y (X y)) x (Y x) + A x (cov Z x (X x)) (Y x)
        + cov (fun y ↦ A y (Z y) (X y)) x (Y x) + A x (A x (Z x) (X x)) (Y x) := by
    rw [eX, cov'.isCovariantDerivativeOn.add hσX hτX, add_apply,
      hA _ x hσX (Y x), hA _ x hτX (Y x)]
    abel
  have t3 : cov' Z x (mlieBracket I X Y x) =
      cov Z x (mlieBracket I X Y x) + A x (Z x) (mlieBracket I X Y x) :=
    hA Z x (hZm x) _
  have t4 : A x (Z x) (cov Y x (X x) - cov X x (Y x)) =
      A x (Z x) (cov Y x (X x)) - A x (Z x) (cov X x (Y x)) := map_sub _ _ _
  rw [hb] at t4
  simp only [curvature, covEnd, t1, t2, t3]
  rw [t4]
  abel

end CovariantDerivative

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-- `(∇_v σ)(x)`, as a vector of `E = T_xM`. -/
noncomputable def covE (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (σ : Π y : M, TangentSpace I y) (x : M) (v : TangentSpace I x) : E :=
  cov σ x v

/-- `R(X,Y)Z` at `x`, as a vector of `E = T_xM`. -/
noncomputable def curvatureE (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (X Y Z : Π y : M, TangentSpace I y) (x : M) : E :=
  cov.curvature X Y Z x

/-- `(∇_X A)(Y, Z)` at `x` for a one-form `A` with values in `End E`, as a vector of
`E = T_xM`. -/
noncomputable def covEndE (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (A : M → E →L[ℝ] E →L[ℝ] E) (X Y Z : Π y : M, TangentSpace I y) (x : M) : E :=
  cov.covEnd A X Y Z x

section Variation

variable {cov : ℝ → CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
  {A : ℝ → M → E →L[ℝ] E →L[ℝ] E} {A' : M → E →L[ℝ] E →L[ℝ] E} {t₀ : ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The difference tensor vanishes at the base time. -/
theorem difference_self_eq_zero
    (hA : ∀ t (σ : Π y : M, TangentSpace I y) (y : M), MDiffAt (T% σ) y →
      ∀ v : TangentSpace I y, covE (cov t) σ y v = covE (cov t₀) σ y v + A t y (σ y) v)
    (y : M) : A t₀ y = 0 := by
  ext v w
  have hσ := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I y from v)
  have := hA t₀ _ y hσ w
  rw [FiberBundle.extend_apply_self] at this
  simp only [zero_apply]
  exact add_eq_left.mp this.symm

-- BENCH: variation-curvature
/-- **First variation of the curvature.** Along a family of `C¹` connections
`∇ᵗ = ∇ + Aᵗ` with `∇ = ∇ᵗ⁰` torsion-free and `∂ₜ Aᵗ = Ȧ` at `t₀`, if `∂ₜ` commutes with
`∇_X` and `∇_Y` on the sections `Aᵗ(Y,Z)` and `Aᵗ(X,Z)` at `x`, then
`∂ₜ Rᵗ(X,Y)Z = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)` at `t₀`. -/
theorem hasDerivAt_curvatureE
    (hcov : ∀ t, ContMDiffCovariantDerivative (cov t) 1)
    (htf : (cov t₀).torsion = 0)
    (hA : ∀ t (σ : Π y : M, TangentSpace I y) (y : M), MDiffAt (T% σ) y →
      ∀ v : TangentSpace I y, covE (cov t) σ y v = covE (cov t₀) σ y v + A t y (σ y) v)
    (hA' : ∀ y, HasDerivAt (fun t ↦ A t y) (A' y) t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXYZ : HasDerivAt (fun t ↦ covE (cov t₀) (fun y ↦ A t y (Z y) (Y y)) x (X x))
      (covE (cov t₀) (fun y ↦ A' y (Z y) (Y y)) x (X x)) t₀)
    (hYXZ : HasDerivAt (fun t ↦ covE (cov t₀) (fun y ↦ A t y (Z y) (X y)) x (Y x))
      (covE (cov t₀) (fun y ↦ A' y (Z y) (X y)) x (Y x)) t₀) :
    HasDerivAt (fun t ↦ curvatureE (cov t) X Y Z x)
      (covEndE (cov t₀) A' X Y Z x - covEndE (cov t₀) A' Y X Z x) t₀ := by
  have h0 : A t₀ x = 0 := difference_self_eq_zero hA x
  -- pointwise derivatives of the difference tensor
  have hAv : ∀ (v w : E), HasDerivAt (fun t ↦ A t x v w) (A' x v w) t₀ := by
    intro v w
    have := ((hA' x).clm_apply (hasDerivAt_const (F := E) t₀ v)).clm_apply
      (hasDerivAt_const (F := E) t₀ w)
    simp only [map_zero, add_zero] at this
    exact this
  -- `(∇_X Aᵗ)(Y,Z)` is differentiable, with derivative `(∇_X Ȧ)(Y,Z)`
  have d1 : HasDerivAt (fun t ↦ covEndE (cov t₀) (A t) X Y Z x)
      (covEndE (cov t₀) A' X Y Z x) t₀ :=
    (hXYZ.sub (hAv (Z x) (cov t₀ Y x (X x)))).sub (hAv (cov t₀ Z x (X x)) (Y x))
  have d2 : HasDerivAt (fun t ↦ covEndE (cov t₀) (A t) Y X Z x)
      (covEndE (cov t₀) A' Y X Z x) t₀ :=
    (hYXZ.sub (hAv (Z x) (cov t₀ X x (Y x)))).sub (hAv (cov t₀ Z x (Y x)) (X x))
  -- the quadratic terms have zero derivative at `t₀`, since `Aᵗ⁰ = 0`
  have q : ∀ (v w u : E), HasDerivAt (fun t ↦ A t x (A t x v w) u) 0 t₀ := by
    intro v w u
    have := ((hA' x).clm_apply (hAv v w)).clm_apply (hasDerivAt_const (F := E) t₀ u)
    simp only [h0, zero_apply, map_zero, add_zero] at this
    exact this
  -- the curvature of `∇ᵗ` through the difference tensor
  have hfun : (fun t ↦ curvatureE (cov t) X Y Z x) = fun t ↦
      curvatureE (cov t₀) X Y Z x
        + covEndE (cov t₀) (A t) X Y Z x - covEndE (cov t₀) (A t) Y X Z x
        + A t x (A t x (Z x) (Y x)) (X x) - A t x (A t x (Z x) (X x)) (Y x) := by
    funext t
    have := hcov t
    have := hcov t₀
    exact (cov t₀).curvature_eq_add_covEnd (cov t) htf (fun σ y hσ v ↦ hA t σ y hσ v) hZ hX hY
  rw [hfun]
  have := ((((hasDerivAt_const t₀ (curvatureE (cov t₀) X Y Z x)).add d1).sub d2).add
    (q (Z x) (Y x) (X x))).sub (q (Z x) (X x) (Y x))
  exact this.congr_deriv (by abel)

end Variation

section Coordinates

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
/-- A curve of continuous linear maps out of a finite-dimensional space is differentiable
as soon as it is differentiable when applied to every vector. -/
theorem exists_hasDerivAt_clm_of_apply {B : ℝ → E →L[ℝ] F} {t₀ : ℝ}
    (h : ∀ v, ∃ d, HasDerivAt (fun t ↦ B t v) d t₀) :
    ∃ B', HasDerivAt B B' t₀ := by
  classical
  choose d hd using h
  let b := Module.finBasis ℝ E
  have hB : B = fun t ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ E F
      (LinearMap.toContinuousLinearMap (b.coord i)) (B t (b i)) := by
    funext t
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simp [ContinuousLinearMap.smulRightL_apply_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Finsupp.single_eq_of_ne hij]
    · simp
  exact ⟨_, by
    rw [hB]
    exact HasDerivAt.fun_sum fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ E F
        (LinearMap.toContinuousLinearMap (b.coord i))).hasFDerivAt.comp_hasDerivAt t₀ (hd (b i))⟩

omit [CompleteSpace E] in
/-- A curve of continuous bilinear maps out of a finite-dimensional space is differentiable
as soon as it is differentiable when applied to every pair of vectors. -/
theorem exists_hasDerivAt_clm₂_of_apply {B : ℝ → E →L[ℝ] E →L[ℝ] F} {t₀ : ℝ}
    (h : ∀ v w, ∃ d, HasDerivAt (fun t ↦ B t v w) d t₀) :
    ∃ B', HasDerivAt B B' t₀ :=
  exists_hasDerivAt_clm_of_apply fun v ↦ exists_hasDerivAt_clm_of_apply (h v)

end Coordinates

section Difference

/-- The difference `∇ − ∇'` of two connections on the tangent bundle, as a one-form with
values in `End E` (Mathlib's `CovariantDerivative.difference`, on the model space):
`differenceE cov cov' y (σ y) v = (∇_v σ)(y) − (∇'_v σ)(y)` for `σ` differentiable at `y`. -/
noncomputable def differenceE (cov cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (y : M) : E →L[ℝ] E →L[ℝ] E :=
  cov.difference cov' y

omit [CompleteSpace E] in
theorem differenceE_apply (cov cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {σ : Π y : M, TangentSpace I y} {y : M} (hσ : MDiffAt (T% σ) y) (v : TangentSpace I y) :
    differenceE cov cov' y (σ y) v = covE cov σ y v - covE cov' σ y v := by
  have := IsCovariantDerivativeOn.difference_apply cov.isCovariantDerivativeOnUniv
    cov'.isCovariantDerivativeOnUniv (Set.mem_univ y) hσ
  change (cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv y (σ y)) v = _
  rw [this]
  rfl

omit [CompleteSpace E] in
/-- `∇ = ∇' + (∇ − ∇')` on differentiable sections: the hypothesis `hA` of
`hasDerivAt_curvatureE` for `A t = differenceE (cov t) (cov t₀)`. -/
theorem covE_eq_add_differenceE
    (cov cov' : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    {σ : Π y : M, TangentSpace I y} {y : M} (hσ : MDiffAt (T% σ) y) (v : TangentSpace I y) :
    covE cov σ y v = covE cov' σ y v + differenceE cov cov' y (σ y) v := by
  rw [differenceE_apply cov cov' hσ v]
  abel

end Difference

section Metric

/-! ### Along a family of metrics

The difference tensor of the Levi-Civita connections of `g t` and `g t₀` is differentiable in
`t`, with derivative `Ȧ = ∂ₜ ∇` characterised by the first variation formula of
`Variation.lean`; the first variation of the curvature then reads
`∂ₜ Rm(X,Y)Z = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)`. -/

set_option maxSynthPendingDepth 3

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

omit [CompleteSpace E] in
/-- The Levi-Civita connection of a `C²` metric is `C¹`, as a function of the metric. -/
theorem contMDiffCovariantDerivative_leviCivitaOfMetric_one
    (g₀ : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) :
    ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  exact instContMDiffCovariantDerivativeLeviCivitaConnectionOne

/-- **The commutation hypothesis** of the variation formulas: along the family `g t` with
`∂ₜ g = h`, the space derivatives `X(g_t(Y,Z))` are differentiable in `t` with derivative
`X(h(Y,Z))`, for all fields differentiable at the point. This is joint regularity of
`(t, x) ↦ g t x`, which the pointwise definition of the flow does not impose. -/
def CommutesWithMvfderiv (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (h : M → E →L[ℝ] E →L[ℝ] ℝ) (t₀ : ℝ) : Prop :=
  ∀ (X Y Z : Π y : M, TangentSpace I y) (y : M),
    MDiffAt (T% X) y → MDiffAt (T% Y) y → MDiffAt (T% Z) y →
    HasDerivAt (fun t ↦ mvfderiv I (fun y' ↦ (g t).inner y' (Y y') (Z y')) y (X y))
      (mvfderiv I (fun y' ↦ h y' (Y y') (Z y')) y (X y)) t₀

omit [CompleteSpace E] in
/-- The difference tensor of two Levi-Civita connections, on constant-in-trivialisation
fields: `A(v, w) = ∇ᵗ_v (extend w) − ∇ᵗ⁰_v (extend w)`. -/
theorem differenceE_leviCivitaOfMetric_apply (t : ℝ) (y : M) (v w : E) :
    differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y w v =
      leviCivitaOfMetricE (g t) (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) y
        - leviCivitaOfMetricE (g t₀) (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) y := by
  have hσ := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I y from w)
  have := differenceE_apply (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) hσ v
  rw [FiberBundle.extend_apply_self] at this
  rw [this]
  unfold leviCivitaOfMetricE covE
  rw [FiberBundle.extend_apply_self]

-- BENCH: variation-connection-tensor
/-- **`t ↦ ∇ᵗ − ∇ᵗ⁰` is differentiable** at each point, as a one-form with values in `End E`,
given `∂ₜ g = h` and the commutation hypothesis. -/
theorem exists_hasDerivAt_differenceE_leviCivitaOfMetric
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (y : M) :
    ∃ A', HasDerivAt
      (fun t ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y) A' t₀ := by
  apply exists_hasDerivAt_clm₂_of_apply
  intro w v
  have hX := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I y from v)
  have hY := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I y from w)
  obtain ⟨Γ', hΓ⟩ := exists_hasDerivAt_leviCivitaOfMetricE hg hX hY
    (fun Z hZ ↦ hcomm _ _ Z y hX hY hZ) (fun Z hZ ↦ hcomm _ Z _ y hY hZ hX)
    (fun Z hZ ↦ hcomm Z _ _ y hZ hX hY)
  have hfun : (fun t ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y w v) =
      fun t ↦ leviCivitaOfMetricE (g t) (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) y
        - leviCivitaOfMetricE (g t₀) (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) y := by
    funext t
    exact differenceE_leviCivitaOfMetric_apply t y v w
  exact ⟨_, by rw [hfun]; exact hΓ.sub_const _⟩

/-- The time derivative of the difference tensor of the Levi-Civita connections, `Ȧ = ∂ₜ ∇`. -/
noncomputable def derivDifferenceE
    (g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (t₀ : ℝ)
    (y : M) : E →L[ℝ] E →L[ℝ] E :=
  deriv (fun t ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y) t₀

theorem hasDerivAt_differenceE_leviCivitaOfMetric
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (y : M) :
    HasDerivAt (fun t ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y)
      (derivDifferenceE g t₀ y) t₀ :=
  (exists_hasDerivAt_differenceE_leviCivitaOfMetric hg hcomm y).choose_spec.differentiableAt.hasDerivAt

-- BENCH: variation-connection-tensor-inner
/-- **`∂ₜ ∇` as a tensor**: its value on `(v, w)` is characterised by
`g(Ȧ(v,w), Z) = ½ [(∇_v h)(w,Z) + (∇_w h)(Z,v) − (∇_Z h)(v,w)]`, with `∇ = ∇ᵗ⁰` and the
constant-in-trivialisation extensions of `v`, `w` as fields. -/
theorem inner_derivDifferenceE_eq
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (y : M) (v w : E)
    {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) y) :
    (g t₀).inner y (derivDifferenceE g t₀ y w v) (Z y) =
      ((leviCivitaOfMetric (g t₀)).covBilin h (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) Z y
        + (leviCivitaOfMetric (g t₀)).covBilin h (FiberBundle.extend E (show TangentSpace I y from w))
          Z (FiberBundle.extend E (show TangentSpace I y from v)) y
        - (leviCivitaOfMetric (g t₀)).covBilin h Z
          (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) y) / 2 := by
  have hA' := hasDerivAt_differenceE_leviCivitaOfMetric hg hcomm y
  have hX := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I y from v)
  have hY := FiberBundle.mdifferentiableAt_extend I E (show TangentSpace I y from w)
  have h1 : HasDerivAt
      (fun t ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y w v)
      (derivDifferenceE g t₀ y w v) t₀ := by
    have := (hA'.clm_apply (hasDerivAt_const (F := E) t₀ w)).clm_apply
      (hasDerivAt_const (F := E) t₀ v)
    simp only [map_zero, add_zero] at this
    exact this
  have hfun : (fun t ↦ leviCivitaOfMetricE (g t)
      (FiberBundle.extend E (show TangentSpace I y from v))
      (FiberBundle.extend E (show TangentSpace I y from w)) y) =
      fun t ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y w v
        + leviCivitaOfMetricE (g t₀) (FiberBundle.extend E (show TangentSpace I y from v))
          (FiberBundle.extend E (show TangentSpace I y from w)) y := by
    funext t
    rw [differenceE_leviCivitaOfMetric_apply]
    abel
  have hd : HasDerivAt (fun t ↦ leviCivitaOfMetricE (g t)
      (FiberBundle.extend E (show TangentSpace I y from v))
      (FiberBundle.extend E (show TangentSpace I y from w)) y)
      (derivDifferenceE g t₀ y w v) t₀ := by
    rw [hfun]
    exact h1.add_const _
  exact inner_deriv_leviCivitaOfMetric_eq hg hX hY hZ (hcomm _ _ Z y hX hY hZ)
    (hcomm _ Z _ y hY hZ hX) (hcomm Z _ _ y hZ hX hY) hd

-- BENCH: variation-curvature-metric
/-- **First variation of the curvature along a family of metrics.** With `∂ₜ g = h`, the
commutation hypothesis, and the commutation of `∂ₜ` with `∇_X`, `∇_Y` on the sections
`Aᵗ(Y,Z)`, `Aᵗ(X,Z)` (`Aᵗ = ∇ᵗ − ∇ᵗ⁰`), the curvature of `g t` at `x` is differentiable in
`t` with `∂ₜ Rm(X,Y)Z = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)`, where `Ȧ = ∂ₜ ∇` is the tensor of
`inner_derivDifferenceE_eq`. -/
theorem hasDerivAt_curvatureE_leviCivitaOfMetric
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiff 2 (T% Z)) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXYZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (Y y))
        x (X x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (Y y)) x (X x)) t₀)
    (hYXZ : HasDerivAt (fun t ↦ covE (leviCivitaOfMetric (g t₀))
        (fun y ↦ differenceE (leviCivitaOfMetric (g t)) (leviCivitaOfMetric (g t₀)) y (Z y) (X y))
        x (Y x))
      (covE (leviCivitaOfMetric (g t₀)) (fun y ↦ derivDifferenceE g t₀ y (Z y) (X y)) x (Y x)) t₀) :
    HasDerivAt (fun t ↦ curvatureE (leviCivitaOfMetric (g t)) X Y Z x)
      (covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀) X Y Z x
        - covEndE (leviCivitaOfMetric (g t₀)) (derivDifferenceE g t₀) Y X Z x) t₀ :=
  hasDerivAt_curvatureE (fun t ↦ contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t))
    (torsion_leviCivitaOfMetric_eq_zero (g t₀))
    (fun _ _ _ hσ v ↦ covE_eq_add_differenceE _ _ hσ v)
    (hasDerivAt_differenceE_leviCivitaOfMetric hg hcomm) hZ hX hY hXYZ hYXZ

end Metric

end RicciFlowBlueprint
