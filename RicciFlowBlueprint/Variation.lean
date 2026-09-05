/-
The first variation of the Levi-Civita connection.

Along a one-parameter family of metrics `g t` with `∂ₜ g = h`, the Levi-Civita
connections `∇ᵗ` satisfy

  `g(∂ₜ ∇_X Y, Z) = ½ [ (∇_X h)(Y,Z) + (∇_Y h)(Z,X) − (∇_Z h)(X,Y) ]`,

with `∇ = ∇ᵗ⁰` on the right. This is the formula every evolution equation of
Ricci flow starts from (`lem:evolution-rm`): with `h = −2 Ric` it gives `∂ₜ Γ`,
and differentiating once more gives `∂ₜ Rm`.

The route is the Koszul formula. `g(∇_X Y, Z)` is an explicit expression in the
metric alone, so its time derivative is the same expression in `h`, provided the
space derivatives `X(g(Y,Z))` commute with `∂ₜ`. That commutation is a joint
regularity statement about `(t, x) ↦ g t x`, which the pointwise-in-`t`
definition of the flow (`Flow.lean`) does not impose; here it is taken as a
hypothesis, in exactly the form used. The rest is algebra: the Koszul
combination of a symmetric bilinear form `h`, rewritten through a torsion-free
connection, is `(∇_X h)(Y,Z) + (∇_Y h)(Z,X) − (∇_Z h)(X,Y) + 2 h(∇_X Y, Z)`
(`koszul_bilin_eq`), and the last term is what the product rule
`∂ₜ [g(∇_X Y, Z)] = h(∇_X Y, Z) + g(∂ₜ ∇_X Y, Z)` absorbs.

Differentiability of `t ↦ ∇ᵗ_X Y (x)` itself is a hypothesis of the vector
form (`inner_deriv_leviCivitaOfMetric_eq`); it follows from that of `g` through
the musical isomorphism, and is not proved here. The scalar form
(`hasDerivAt_inner_leviCivitaOfMetric`) needs nothing of the kind.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.LeviCivitaSmooth
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

/-- The **covariant derivative of a bilinear form field**:
`(∇_X h)(Y, Z) = X(h(Y, Z)) - h(∇_X Y, Z) - h(Y, ∇_X Z)`. -/
noncomputable def covBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)
    - h x (cov Y x (X x)) (Z x) - h x (Y x) (cov Z x (X x))

-- BENCH: koszul-bilinear
/-- **The Koszul combination of a symmetric bilinear form**, through a torsion-free connection:
`X h(Y,Z) + Y h(Z,X) - Z h(X,Y) - h(Y,[X,Z]) - h(Z,[Y,X]) + h(X,[Z,Y])
  = (∇_X h)(Y,Z) + (∇_Y h)(Z,X) - (∇_Z h)(X,Y) + 2 h(∇_X Y, Z)`.
For `h = g` and `∇` metric-compatible the first three terms vanish and this is the Koszul
formula; for `h = ∂ₜ g` it is the first variation of the connection. -/
theorem koszul_bilin_eq (hcov : cov.torsion = 0)
    {h : M → E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ y v w, h y v w = h y w v)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x) + mvfderiv I (fun y ↦ h y (Z y) (X y)) x (Y x)
      - mvfderiv I (fun y ↦ h y (X y) (Y y)) x (Z x)
      - h x (Y x) (mlieBracket I X Z x) - h x (Z x) (mlieBracket I Y X x)
      + h x (X x) (mlieBracket I Z Y x)
    = cov.covBilin h X Y Z x + cov.covBilin h Y Z X x - cov.covBilin h Z X Y x
      + 2 * h x (cov Y x (X x)) (Z x) := by
  have hb : ∀ {U V : Π y : M, TangentSpace I y} {y : M}, MDiffAt (T% U) y → MDiffAt (T% V) y →
      cov V y (U y) - cov U y (V y) = mlieBracket I U V y := (torsion_eq_zero_iff cov).mp hcov
  rw [← hb hX hZ, ← hb hY hX, ← hb hZ hY]
  have e1 : h x (Y x) (cov Z x (X x) - cov X x (Z x)) =
      h x (Y x) (cov Z x (X x)) - h x (Y x) (cov X x (Z x)) := map_sub _ _ _
  have e2 : h x (Z x) (cov X x (Y x) - cov Y x (X x)) =
      h x (Z x) (cov X x (Y x)) - h x (Z x) (cov Y x (X x)) := map_sub _ _ _
  have e3 : h x (X x) (cov Y x (Z x) - cov Z x (Y x)) =
      h x (X x) (cov Y x (Z x)) - h x (X x) (cov Z x (Y x)) := map_sub _ _ _
  simp only [covBilin]
  linarith [e1, e2, e3, hsymm x (Y x) (cov X x (Z x)), hsymm x (Y x) (cov Z x (X x)),
    hsymm x (Z x) (cov Y x (X x)), hsymm x (Z x) (cov X x (Y x)),
    hsymm x (X x) (cov Z x (Y x)), hsymm x (X x) (cov Y x (Z x))]

end CovariantDerivative

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

set_option maxSynthPendingDepth 3

section Variation

/-- The **Levi-Civita connection of a metric**, as a function of the metric: Mathlib's
`leviCivitaConnection` under the `RiemannianBundle` instance of `g`. -/
noncomputable def leviCivitaOfMetric
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) :
    CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x) :=
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  leviCivitaConnection I M

theorem torsion_leviCivitaOfMetric_eq_zero
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) :
    (leviCivitaOfMetric g).torsion = 0 := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact torsion_leviCivitaConnection_eq_zero I

omit [CompleteSpace E] in
/-- **The Koszul formula** for `leviCivitaOfMetric g`, in terms of `g.inner`. -/
theorem inner_leviCivitaOfMetric_eq
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    g.inner x (leviCivitaOfMetric g Y x (X x)) (Z x) =
      (mvfderiv I (fun y ↦ g.inner y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ g.inner y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ g.inner y (X y) (Y y)) x (Z x)
        - g.inner x (Y x) (mlieBracket I X Z x) - g.inner x (Z x) (mlieBracket I Y X x)
        + g.inner x (X x) (mlieBracket I Z Y x)) / 2 := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (isLeviCivitaConnection_leviCivitaConnection I).apply_eq I hX hY hZ

/-- The metric `g` at `y`, as a bilinear form on the model space `E = T_yM`. Time derivatives
of a family of metrics are stated for this: `TangentSpace I y` carries no norm of its own (the
norm comes from a `RiemannianBundle` instance, i.e. from a metric), so `HasDerivAt` into
`T_yM →L T_yM →L ℝ` cannot be stated, while into `E →L E →L ℝ` it can, and in finite
dimensions the notion does not depend on the norm. -/
noncomputable def innerE (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  g.inner y

/-- `∇_X Y` at `x` for the Levi-Civita connection of `g`, as a vector of `E = T_xM`. -/
noncomputable def leviCivitaOfMetricE
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X Y : Π y : M, TangentSpace I y) (x : M) : E :=
  leviCivitaOfMetric g Y x (X x)

variable {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Pointwise time derivatives of the metric, from the derivative of `t ↦ g_t(y)` as a
bilinear map. -/
theorem hasDerivAt_inner_apply
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀) (y : M)
    (v w : TangentSpace I y) : HasDerivAt (fun t ↦ (g t).inner y v w) (h y v w) t₀ := by
  have := ((hg y).clm_apply (hasDerivAt_const (F := E) t₀ v)).clm_apply
    (hasDerivAt_const (F := E) t₀ w)
  simp only [map_zero, add_zero] at this
  exact this

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The time derivative of a family of symmetric bilinear forms is symmetric. -/
theorem symm_of_hasDerivAt_inner
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀) (y : M) (v w : E) :
    h y v w = h y w v := by
  refine (hasDerivAt_inner_apply hg y v w).unique ?_
  have : (fun t ↦ (g t).inner y v w) = fun t ↦ (g t).inner y w v := by
    funext t; exact (g t).symm y v w
  rw [this]; exact hasDerivAt_inner_apply hg y w v

omit [CompleteSpace E] in
-- BENCH: koszul-differentiated
/-- **The Koszul formula, differentiated in time.** Along a family of metrics `g t` with
`∂ₜ g = h`, and assuming the space derivatives `X(g(Y,Z))` commute with `∂ₜ` for the three
fields at hand, `t ↦ g_t(∇ᵗ_X Y, Z)` is differentiable with derivative the Koszul
combination of `h`. -/
theorem hasDerivAt_inner_leviCivitaOfMetric
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hXYZ : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (Y y) (Z y)) x (X x))
      (mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)) t₀)
    (hYZX : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (Z y) (X y)) x (Y x))
      (mvfderiv I (fun y ↦ h y (Z y) (X y)) x (Y x)) t₀)
    (hZXY : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (X y) (Y y)) x (Z x))
      (mvfderiv I (fun y ↦ h y (X y) (Y y)) x (Z x)) t₀) :
    HasDerivAt (fun t ↦ (g t).inner x (leviCivitaOfMetric (g t) Y x (X x)) (Z x))
      ((mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ h y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ h y (X y) (Y y)) x (Z x)
        - h x (Y x) (mlieBracket I X Z x) - h x (Z x) (mlieBracket I Y X x)
        + h x (X x) (mlieBracket I Z Y x)) / 2) t₀ := by
  have hfun : (fun t ↦ (g t).inner x (leviCivitaOfMetric (g t) Y x (X x)) (Z x)) =
      fun t ↦ (mvfderiv I (fun y ↦ (g t).inner y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ (g t).inner y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ (g t).inner y (X y) (Y y)) x (Z x)
        - (g t).inner x (Y x) (mlieBracket I X Z x) - (g t).inner x (Z x) (mlieBracket I Y X x)
        + (g t).inner x (X x) (mlieBracket I Z Y x)) / 2 := by
    funext t
    exact inner_leviCivitaOfMetric_eq (g t) hX hY hZ
  rw [hfun]
  exact (((((hXYZ.add hYZX).sub hZXY).sub (hasDerivAt_inner_apply hg x _ _)).sub
    (hasDerivAt_inner_apply hg x _ _)).add (hasDerivAt_inner_apply hg x _ _)).div_const 2

-- BENCH: variation-connection-scalar
/-- **First variation of the Levi-Civita connection, scalar form.** Under the hypotheses of
`hasDerivAt_inner_leviCivitaOfMetric`,
`∂ₜ [g_t(∇ᵗ_X Y, Z)] = ½ [(∇_X h)(Y,Z) + (∇_Y h)(Z,X) - (∇_Z h)(X,Y)] + h(∇_X Y, Z)`
with `∇ = ∇ᵗ⁰`. -/
theorem hasDerivAt_inner_leviCivitaOfMetric_covBilin
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hXYZ : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (Y y) (Z y)) x (X x))
      (mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)) t₀)
    (hYZX : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (Z y) (X y)) x (Y x))
      (mvfderiv I (fun y ↦ h y (Z y) (X y)) x (Y x)) t₀)
    (hZXY : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (X y) (Y y)) x (Z x))
      (mvfderiv I (fun y ↦ h y (X y) (Y y)) x (Z x)) t₀) :
    HasDerivAt (fun t ↦ (g t).inner x (leviCivitaOfMetric (g t) Y x (X x)) (Z x))
      (((leviCivitaOfMetric (g t₀)).covBilin h X Y Z x
        + (leviCivitaOfMetric (g t₀)).covBilin h Y Z X x
        - (leviCivitaOfMetric (g t₀)).covBilin h Z X Y x) / 2
        + h x (leviCivitaOfMetric (g t₀) Y x (X x)) (Z x)) t₀ := by
  have := hasDerivAt_inner_leviCivitaOfMetric hg hX hY hZ hXYZ hYZX hZXY
  convert this using 1
  rw [(leviCivitaOfMetric (g t₀)).koszul_bilin_eq (torsion_leviCivitaOfMetric_eq_zero _)
    (symm_of_hasDerivAt_inner hg) hX hY hZ]
  ring

-- BENCH: variation-connection
/-- **First variation of the Levi-Civita connection.** If `∂ₜ g = h` and `t ↦ ∇ᵗ_X Y (x)` is
differentiable at `t₀` with derivative `Γ'`, then
`g(Γ', Z) = ½ [(∇_X h)(Y,Z) + (∇_Y h)(Z,X) - (∇_Z h)(X,Y)]`, with `∇ = ∇ᵗ⁰`. -/
theorem inner_deriv_leviCivitaOfMetric_eq
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hXYZ : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (Y y) (Z y)) x (X x))
      (mvfderiv I (fun y ↦ h y (Y y) (Z y)) x (X x)) t₀)
    (hYZX : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (Z y) (X y)) x (Y x))
      (mvfderiv I (fun y ↦ h y (Z y) (X y)) x (Y x)) t₀)
    (hZXY : HasDerivAt (fun t ↦ mvfderiv I (fun y ↦ (g t).inner y (X y) (Y y)) x (Z x))
      (mvfderiv I (fun y ↦ h y (X y) (Y y)) x (Z x)) t₀)
    {Γ' : E} (hΓ : HasDerivAt (fun t ↦ leviCivitaOfMetricE (g t) X Y x) Γ' t₀) :
    (g t₀).inner x Γ' (Z x) =
      ((leviCivitaOfMetric (g t₀)).covBilin h X Y Z x
        + (leviCivitaOfMetric (g t₀)).covBilin h Y Z X x
        - (leviCivitaOfMetric (g t₀)).covBilin h Z X Y x) / 2 := by
  have h1 := hasDerivAt_inner_leviCivitaOfMetric_covBilin hg hX hY hZ hXYZ hYZX hZXY
  have h2 : HasDerivAt (fun t ↦ (g t).inner x (leviCivitaOfMetric (g t) Y x (X x)) (Z x))
      (h x (leviCivitaOfMetric (g t₀) Y x (X x)) (Z x) + (g t₀).inner x Γ' (Z x)) t₀ := by
    have := ((hg x).clm_apply hΓ).clm_apply (hasDerivAt_const (F := E) t₀ (Z x))
    simp only [map_zero, add_zero] at this
    exact this
  have := h1.unique h2
  linarith

end Variation

end RicciFlowBlueprint
