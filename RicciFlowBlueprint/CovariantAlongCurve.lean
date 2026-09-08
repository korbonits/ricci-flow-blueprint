/-
The covariant derivative along a curve.

Mathlib's `CovariantDerivative` acts on **global sections over `M`**:
`(Π x : M, V x) → (Π x : M, T_xM →L[ℝ] V x)`. A curve's velocity is not such a section — it
lives only along the curve — so `∇_{γ'} γ' = 0` cannot even be *stated* with it. The missing
primitive is the pullback connection on `γ*TM`, written `D/dt`, and everything in comparison
geometry rests on it: geodesics, parallel transport, the Jacobi equation, and the first and
second variation of length (and, later, of Perelman's `L`-length).

This file defines it the way Mathlib defines the ambient one: a **predicate**
`IsCovDerivAlong` cutting out the operators that deserve the name, with existence and
uniqueness proved separately. The three axioms are the usual ones — additive, Leibniz over a
scalar function of `t`, and agreement with `cov` on the restriction of a global section.

A section along `γ` is a lift of `γ` to `TM`, so its regularity is ordinary
`MDifferentiableAt` into the total space; no new bundle structure is needed.
-/
import RicciFlowBlueprint.Curvature
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Bundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-- The **velocity** of a curve, `γ'(t) ∈ T_{γ(t)}M`. -/
noncomputable def velocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) I γ t (show TangentSpace 𝓘(ℝ, ℝ) t from (1 : ℝ))

/-- **A section of `TM` along `γ` is differentiable at `t`** when its lift to the total space
is. This is the `T%` idiom of the ambient theory, with the base `M` replaced by the parameter
interval. -/
def MDiffAlongAt (γ : ℝ → M) (V : Π t : ℝ, TangentSpace I (γ t)) (t : ℝ) : Prop :=
  MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
    (fun u ↦ (⟨γ u, V u⟩ : TangentBundle I M)) t

/-- **The covariant derivative along a curve**, as a predicate. `D` differentiates sections of
`TM` along `γ`; the three axioms say it is additive, satisfies the Leibniz rule over scalar
functions of the parameter, and restricts `cov` correctly:
`D (W ∘ γ) t = (∇_{γ'(t)} W)(γ t)` for a global section `W`.

The last axiom is what ties `D` to the ambient connection, and — with the other two — pins it
down: near any `t` a section along `γ` is a combination of restrictions of a local frame. -/
structure IsCovDerivAlong
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (γ : ℝ → M)
    (D : (Π t : ℝ, TangentSpace I (γ t)) → (Π t : ℝ, TangentSpace I (γ t)))
    (s : Set ℝ := Set.univ) : Prop where
  add {V W : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}
    (hV : MDiffAlongAt γ V t) (hW : MDiffAlongAt γ W t) (ht : t ∈ s := by trivial) :
    D (V + W) t = D V t + D W t
  leibniz {V : Π t : ℝ, TangentSpace I (γ t)} {f : ℝ → ℝ} {t : ℝ}
    (hV : MDiffAlongAt γ V t) (hf : DifferentiableAt ℝ f t) (ht : t ∈ s := by trivial) :
    D (f • V) t = f t • D V t + deriv f t • V t
  restrict {W : Π x : M, TangentSpace I x} {t : ℝ}
    (hW : MDiffAt (T% W) (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (ht : t ∈ s := by trivial) :
    D (fun u ↦ W (γ u)) t = cov W (γ t) (velocity γ t)

/-- The zero section along a differentiable curve is differentiable. -/
theorem MDiffAlongAt.zero_section {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDiffAlongAt γ (0 : Π t : ℝ, TangentSpace I (γ t)) t :=
  ((contMDiff_zeroSection (n := 1) ℝ (fun (x : M) ↦ TangentSpace I x)).mdifferentiable
    (by norm_num) (γ t)).comp t hγ

variable {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)} {γ : ℝ → M}
  {D : (Π t : ℝ, TangentSpace I (γ t)) → (Π t : ℝ, TangentSpace I (γ t))} {s : Set ℝ}

/-- `D` kills the zero section: Leibniz with the zero coefficient. -/
theorem IsCovDerivAlong.zero (h : IsCovDerivAlong cov γ D s) {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s) :
    D 0 t = 0 := by
  have hz : ((fun _ : ℝ ↦ (0 : ℝ)) • (0 : Π t : ℝ, TangentSpace I (γ t)))
      = (0 : Π t : ℝ, TangentSpace I (γ t)) := by
    funext u; simp
  have hL := h.leibniz (f := fun _ : ℝ ↦ (0 : ℝ))
    (MDiffAlongAt.zero_section hγ) (differentiableAt_const (0 : ℝ)) ht
  rw [hz] at hL
  simpa using hL

-- BENCH: cov-along-curve-local
/-- **`D` is local**: it depends on a section only through its germ. Not an axiom — the usual
bump-function argument. If `V = W` near `t`, take a smooth `f` equal to `1` near `t` and
supported where they agree; then `f • V = f • W` *globally*, while Leibniz evaluates both sides
at `t` to `D V t` and `D W t`, because `f t = 1` and `deriv f t = 0`. -/
theorem IsCovDerivAlong.congr_of_eventuallyEq (h : IsCovDerivAlong cov γ D s)
    {V W : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}
    (hV : MDiffAlongAt γ V t) (hW : MDiffAlongAt γ W t) (ht : t ∈ s)
    (hVW : V =ᶠ[𝓝 t] W) :
    D V t = D W t := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hVW
  -- a bump: `1` on `closedBall t (ε/3)`, supported in `ball t (ε/2)`
  set b : ContDiffBump t := ⟨ε / 3, ε / 2, by positivity, by linarith⟩ with hb
  have hbc : ∀ u, (b : ℝ → ℝ) u = b u := fun _ ↦ rfl
  have hf1 : b t = 1 := b.one_of_mem_closedBall (by simp [Metric.mem_closedBall]; positivity)
  have hfnear : (fun u ↦ b u) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds t (by positivity : (0 : ℝ) < ε / 3)] with u hu
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
  have hfd : DifferentiableAt ℝ (fun u ↦ b u) t :=
    (b.contDiff (n := 1)).differentiable (by norm_num) t
  have hderiv : deriv (fun u ↦ b u) t = 0 := by
    rw [hfnear.deriv_eq, deriv_const]
  -- the two smeared sections agree globally
  have hsm : ((fun u ↦ b u) • V) = ((fun u ↦ b u) • W) := by
    funext u
    by_cases hu : b u = 0
    · simp [hu]
    · have humem : u ∈ Metric.ball t ε := by
        have hu2 : u ∈ Metric.ball t (ε / 2) := by
          rw [← b.support_eq]; exact Function.mem_support.mpr hu
        exact Metric.ball_subset_ball (by linarith) hu2
      show b u • V u = b u • W u
      rw [hball u humem]
  have eV := h.leibniz hV hfd ht
  have eW := h.leibniz hW hfd ht
  rw [hsm] at eV
  rw [eV] at eW
  rw [hf1, hderiv] at eW
  simpa using eW

end CovariantDerivative
