/-
Sections with prescribed value and **vanishing covariant derivative** at a point.

`GlobalExtension.lean` produces a global `C^k` section through any prescribed
`v ∈ T_xM`. That is enough for every *pointwise* statement in this repo, because
those only ever read the section's value. It is **not** enough for Hamilton's
maximum principle on a non-trivial bundle, and this file supplies what is.

**Why the principle needs more.** `TensorMaximumPrinciple.lean` and everything
built on it take `u : ℝ → M → V` with `V` a *fixed* inner product space — the
trivial bundle `M × V`. The touching-point hypothesis quantifies over a direction
`n ∈ V` and asks about the function `x ↦ ⟪n, u t x⟫`, which only makes sense
because `n` is the same vector at every point. On a genuine bundle the direction
lives in one fibre, `n ∈ V x₀`, and `⟪n, u t x⟫` is meaningless for `x ≠ x₀`.
Hamilton's fix is to spread `n` out into a section and compare against *that*; the
Laplacian of `x ↦ ⟪n(x), u(t,x)⟫` then picks up correction terms in `∇n` and `Δn`,
and the argument works exactly when both vanish at `x₀`.

**What is proved here is the first of the two**, `∇n(x₀) = 0`
(`exists_contMDiff_section_cov_eq_zero`). The textbook construction is parallel
transport along radial geodesics, which would put this behind the regularity of
`exp` — an open ODE-theory gap (see `CLAUDE.md`). It is not needed: one only wants
*first-order* agreement at a single point, and that is linear algebra. Take any
extension `Ñ`, let `A = ∇Ñ(x₀)`, and subtract `∑ᵢ fᵢ · Wᵢ` where the `Wᵢ` are
global sections through an orthonormal basis of `T_{x₀}M` and the `fᵢ` are
functions vanishing at `x₀` with `d fᵢ(x₀)` the matching component of `−A`.
Leibniz then reads `∇(fᵢ·Wᵢ)(x₀) = dfᵢ(x₀) ⊗ Wᵢ(x₀)`, since `fᵢ(x₀) = 0`.

**An orthonormal basis is what makes this cheap.** With a local *frame* one would
have to produce the components of `A` as continuous linear functionals by
inverting a basis; against an orthonormal basis they are `u ↦ ⟪bᵢ, A u⟫`, which is
`innerSL` composed with `A` and so a CLM by construction. No frame, no
trivialisation, no `exists_frame_on_open`: `exists_contMDiff_extension` applied to
each `bᵢ` is all the geometry required.

**Still missing for the maximum principle: `Δn(x₀) = 0`.** The same construction
with quadratic coefficients gives it — one needs a function with `f(x₀) = 0`,
`df(x₀) = 0` and prescribed `Δf(x₀)`, and then `Δ(f·W)(x₀) = Δf(x₀) · W(x₀)`
because the two first-order terms drop out. Only the *trace* of the second
derivative has to be prescribed, not the full Hessian, which is what keeps that
step small as well. It is not done here.
-/
import RicciFlowBlueprint.GlobalExtension
import RicciFlowBlueprint.CovariantAlongCurve
import RicciFlowBlueprint.TraceCov
import RicciFlowBlueprint.Hessian

open Bundle Filter CovariantDerivative
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ω M] [T2Space M] in
/-- **The chain rule through a continuous linear map**, for `mvfderiv`. Mathlib has the
composition lemmas for `mfderiv` but none in this shape; the `HasMFDerivAt` route avoids
unfolding `mvfderiv`'s `fromTangentSpace` by hand. -/
theorem mvfderiv_clm_comp {x : M} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : M → E) (ψ : E →L[ℝ] F) (hg : MDifferentiableAt I 𝓘(ℝ, E) g x) :
    mvfderiv I (fun y ↦ ψ (g y)) x = ψ ∘L mvfderiv I g x := by
  have hψ : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) (⇑ψ) (g x) ψ := ψ.hasFDerivAt.hasMFDerivAt
  have h1 : HasMFDerivAt I 𝓘(ℝ, F) (fun y ↦ ψ (g y)) x
      (ψ ∘L mfderiv I 𝓘(ℝ, E) g x) := hψ.comp x hg.hasMFDerivAt
  simp only [mvfderiv, h1.mfderiv]
  rfl

-- BENCH: prescribed-differential
/-- **A globally `C^k` function vanishing at `x` with prescribed differential there.**

The chart supplies the only thing needed: its differential at the base point is *invertible*
(`isInvertible_mfderiv_extChartAt`), so composing a linear functional with the inverse solves
for the required model-space covector. Multiplying by a bump (`exists_contMDiff_eventuallyEq_fun`)
globalises without touching the germ at `x`, hence without touching either conclusion. -/
theorem exists_contMDiff_fun_mvfderiv_eq {n : ℕ∞} {x : M} (φ : TangentSpace I x →L[ℝ] ℝ) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) (n : ℕ∞ω) f ∧ f x = 0 ∧ mvfderiv I f x = φ := by
  set c : E := extChartAt I x x with hc
  set g : M → E := fun y ↦ extChartAt I x y - c with hgdef
  set L : TangentSpace I x →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I x) x with hLdef
  have hL : L.IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (I := I) x)
  set ψ : E →L[ℝ] ℝ := φ ∘L L.inverse with hψdef
  have hchart : ContMDiffOn I 𝓘(ℝ, E) (n : ℕ∞ω) (extChartAt I x) (chartAt H x).source := by
    simpa using (contMDiffOn_extChartAt (I := I) (n := (n : ℕ∞ω)) (x := x))
  have hsrc : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have hg : ContMDiffOn I 𝓘(ℝ, E) (n : ℕ∞ω) g (chartAt H x).source :=
    hchart.sub contMDiffOn_const
  have hgd : MDifferentiableAt I 𝓘(ℝ, E) g x := by
    have : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
      (contMDiffAt_extChartAt (I := I) (n := (1 : ℕ∞ω)) (x := x)).mdifferentiableAt one_ne_zero
    exact this.sub mdifferentiableAt_const
  have hgderiv : mvfderiv I g x = L := by
    have hex : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
      (contMDiffAt_extChartAt (I := I) (n := (1 : ℕ∞ω)) (x := x)).mdifferentiableAt one_ne_zero
    rw [hgdef, mvfderiv_fun_sub hex mdifferentiableAt_const, mvfderiv_const, sub_zero]
    rfl
  obtain ⟨f, hf, hfeq⟩ :=
    exists_contMDiff_eventuallyEq_fun (n := n) (x := x) hsrc
      (f := fun y ↦ ψ (g y)) (ψ.contMDiff.comp_contMDiffOn hg)
  refine ⟨f, hf, ?_, ?_⟩
  · rw [hfeq.eq_of_nhds]
    show ψ (extChartAt I x x - c) = 0
    rw [hc, sub_self, map_zero]
  · rw [hfeq.mvfderiv_eq, mvfderiv_clm_comp g ψ hgd, hgderiv, hψdef,
      ContinuousLinearMap.comp_assoc, hL.inverse_comp_self, ContinuousLinearMap.comp_id]

section Section

variable
  [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

-- BENCH: normal-section
omit [CompleteSpace E] in
/-- **A globally `C^k` section through a prescribed vector whose covariant derivative
vanishes at that point**: for every `v ∈ T_xM` there is `N` with `N x = v` and `∇N(x) = 0`.

This is what a maximum principle on a non-trivial bundle needs in place of a constant
direction vector, and it is proved with **no parallel transport and no exponential map** —
only first-order agreement at one point is wanted, and that is linear algebra over an
orthonormal basis of the single fibre `T_xM`.

The `fᵢ` vanish at `x`, so Leibniz leaves only `dfᵢ(x) ⊗ Wᵢ(x)`, and the components of
`∇Ñ(x)` against an orthonormal basis are `u ↦ ⟪bᵢ, ∇Ñ(x) u⟫` — continuous and linear by
construction, which is the reason an orthonormal basis is used rather than a local frame. -/
theorem exists_contMDiff_section_cov_eq_zero {n : ℕ∞} (hn : n ≠ 0) {x : M}
    (v : TangentSpace I x) :
    ∃ N : Π y : M, TangentSpace I y,
      CMDiff (n : ℕ∞ω) (T% N) ∧ N x = v ∧ cov N x = 0 := by
  classical
  obtain ⟨Ñ, hÑ, hÑx⟩ := exists_contMDiff_extension (I := I) (n := n) v
  set b := stdOrthonormalBasis ℝ (TangentSpace I x) with hb
  set A : TangentSpace I x →L[ℝ] TangentSpace I x := cov Ñ x with hA
  have hW : ∀ i, ∃ W : Π y : M, TangentSpace I y, CMDiff (n : ℕ∞ω) (T% W) ∧ W x = b i :=
    fun i ↦ exists_contMDiff_extension (I := I) (n := n) (b i)
  choose W hWreg hWx using hW
  have hf : ∀ i, ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) (n : ℕ∞ω) f ∧ f x = 0 ∧
      mvfderiv I f x = -((innerSL ℝ (b i)).comp A) :=
    fun i ↦ exists_contMDiff_fun_mvfderiv_eq (n := n) _
  choose f hfreg hfx hfd using hf
  have hsum : CMDiff (n : ℕ∞ω) (T% (fun y ↦ ∑ i, f i y • W i y)) :=
    ContMDiff.sum_section fun i _ ↦ (hfreg i).smul_section (hWreg i)
  have hÑd : MDiffAt (T% Ñ) x := hÑ.mdifferentiableAt (by exact_mod_cast hn)
  have hsplit : (fun y ↦ Ñ y + ∑ i, f i y • W i y) = Ñ + (fun y ↦ ∑ i, f i y • W i y) := rfl
  refine ⟨fun y ↦ Ñ y + ∑ i, f i y • W i y, ?_, ?_, ?_⟩
  · rw [hsplit]; exact hÑ.add_section hsum
  · simp only [hfx, zero_smul, Finset.sum_const_zero, add_zero, hÑx]
  · rw [hsplit, cov.isCovariantDerivativeOn.add hÑd (hsum.mdifferentiableAt
      (by exact_mod_cast hn))]
    ext u
    have hsm := cov_sum_smul_section_apply cov Finset.univ
      (fun i _ ↦ (hfreg i).mdifferentiableAt (by exact_mod_cast hn))
      (fun i _ ↦ (hWreg i).mdifferentiableAt (by exact_mod_cast hn)) u
    show A u + cov (fun y ↦ ∑ i, f i y • W i y) x u = 0
    rw [hsm]
    have hterm : ∀ i, f i x • cov (W i) x u + mvfderiv I (f i) x u • W i x
        = -(⟪b i, A u⟫ • b i) := by
      intro i
      rw [hfx i, hWx i, zero_smul, zero_add, hfd i]
      simp
    simp only [hterm]
    have hneg : ∑ i, -(⟪b i, A u⟫ • b i) = -∑ i, ⟪b i, A u⟫ • b i := by simp
    rw [hneg, b.sum_repr' (A u)]
    abel

omit [CompleteSpace E] in
/-- The `C²` case, matching `exists_contMDiff_two_extension`. -/
theorem exists_contMDiff_two_section_cov_eq_zero {x : M} (v : TangentSpace I x) :
    ∃ N : Π y : M, TangentSpace I y, CMDiff 2 (T% N) ∧ N x = v ∧ cov N x = 0 := by
  simpa using exists_contMDiff_section_cov_eq_zero cov (n := 2) two_ne_zero v

end Section

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-! ### Towards `ΔN(x) = 0`

The two second-order bricks. Together they say that adding `(a/2)·g² • W` to a section changes
neither its value nor its covariant derivative at a zero `x` of `g`, and changes its Laplacian
there by exactly `a·(∑ⱼ dg(bⱼ)²)·W(x)`. With `dg = ⟪bᵢ, ·⟫` that factor is `1`, so the
Laplacian can be corrected component by component just as the first derivative was above.

What is left to assemble the full statement is bookkeeping rather than analysis: additivity of
`∇²` in its section slot, the finite-sum version of it, and the identification of `laplacian`
with the frame sum `∑ⱼ ∇²_{bⱼ,bⱼ}`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- **The Hessian of `f • W` at a point where `f` and `df` both vanish is `(∇²f) • W`.**
Leibniz produces three corrections beyond the leading term and every one of them carries a
factor `f x` or `df x`, so all three die. This is what lets a *second*-order correction be
added to a section without disturbing a first-order condition already arranged at the same
point: `∇(f • W)(x) = 0` too, for the same reason. -/
theorem hessian_smul_of_vanishing {f : M → ℝ} {W X Y : Π y : M, TangentSpace I y} {x : M}
    (hfx : f x = 0) (hdf : mvfderiv I f x = 0)
    (hf : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) f y) (hW : ∀ y, MDiffAt (T% W) y)
    (hcw : MDiffAt (T% (fun y ↦ cov W y (Y y))) x)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ mvfderiv I f y (Y y)) x) :
    cov.hessian X Y (f • W) x = cov.hessianFun f X Y x • W x := by
  have h2 : cov (f • W) x = 0 := by
    rw [cov.isCovariantDerivativeOn.leibniz (hW x) (hf x), hfx, hdf, zero_smul,
      ContinuousLinearMap.zero_smulRight, add_zero]
  have hsplit : (fun y ↦ cov (f • W) y (Y y))
      = f • (fun y ↦ cov W y (Y y)) + (fun y ↦ mvfderiv I f y (Y y)) • W := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (hW y) (hf y)]
    show f y • cov W y (Y y) + (mvfderiv I f y).smulRight (W y) (Y y)
      = f y • cov W y (Y y) + mvfderiv I f y (Y y) • W y
    rw [ContinuousLinearMap.smulRight_apply]
  show cov (fun y ↦ cov (f • W) y (Y y)) x (X x) - cov (f • W) x (cov Y x (X x)) = _
  rw [h2, hsplit]
  have hd1 : MDiffAt (T% (f • (fun y ↦ cov W y (Y y)))) x := (hf x).smul_section hcw
  have hd2 : MDiffAt (T% ((fun y ↦ mvfderiv I f y (Y y)) • W)) x := hu.smul_section (hW x)
  rw [cov.isCovariantDerivativeOn.add hd1 hd2,
    cov.isCovariantDerivativeOn.leibniz hcw (hf x),
    cov.isCovariantDerivativeOn.leibniz (hW x) hu]
  simp only [ContinuousLinearMap.smulRight_apply, hfx, hdf, zero_smul,
    zero_apply, zero_add, add_zero, ContinuousLinearMap.zero_smulRight, sub_zero]
  rw [hessianFun, hdf]
  simp



omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇²(½a·g²) = a · dg ⊗ dg` at a zero of `g`.** A half-square is the cheapest function with
prescribed value `0`, prescribed differential `0` and a *prescribed second* derivative: both
first-order conditions hold automatically because every term of `d(g²) = 2g·dg` carries a
factor `g`, and the second derivative is the rank-one form `dg ⊗ dg` scaled by `a`. Tracing it
against an orthonormal basis and taking `dg = ⟪bᵢ, ·⟫` gives `Δ = a`, since
`∑ⱼ ⟪bᵢ, bⱼ⟫² = 1` — which is why no chart-side second-derivative transport is needed anywhere
in this construction. -/
theorem hessianFun_half_sq {g : M → ℝ} {X Y : Π y : M, TangentSpace I y} {x : M} (a : ℝ)
    (hgx : g x = 0) (hg : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) g y)
    (hgd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ mvfderiv I g y (Y y)) x) :
    cov.hessianFun (fun y ↦ a / 2 * (g y * g y)) X Y x
      = a * (mvfderiv I g x (X x)) * (mvfderiv I g x (Y x)) := by
  have hfd : ∀ y, mvfderiv I (fun y ↦ a / 2 * (g y * g y)) y = (a * g y) • mvfderiv I g y := by
    intro y
    have hsqd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z ↦ g z * g z) y := (hg y).mul (hg y)
    have hsq : mvfderiv I (fun z ↦ g z * g z) y = (2 * g y) • mvfderiv I g y := by
      rw [mvfderiv_fun_mul (hg y) (hg y)]; module
    rw [mvfderiv_fun_mul mdifferentiableAt_const hsqd, mvfderiv_const, smul_zero, add_zero, hsq]
    module
  have hval : ∀ y, mvfderiv I (fun y ↦ a / 2 * (g y * g y)) y (Y y)
      = (a * g y) * (mvfderiv I g y (Y y)) := by
    intro y; rw [hfd y]; rfl
  have hmul : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ a * g y) x :=
    (mdifferentiableAt_const (c := a)).mul (hg x)
  rw [hessianFun, hfd x, hgx, mul_zero, zero_smul]
  have hfun : (fun y ↦ mvfderiv I (fun y ↦ a / 2 * (g y * g y)) y (Y y))
      = (fun y ↦ (a * g y) * (mvfderiv I g y (Y y))) := by funext y; exact hval y
  have hdmul : mvfderiv I (fun y ↦ a * g y) x = a • mvfderiv I g x := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const (hg x), mvfderiv_const, smul_zero, add_zero]
  rw [hfun, mvfderiv_fun_mul hmul hgd, hgx, mul_zero, hdmul]
  simp only [smul_apply, zero_smul, zero_add, zero_apply, sub_zero, smul_eq_mul]
  ring

end CovariantDerivative
