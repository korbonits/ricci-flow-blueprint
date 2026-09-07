/-
Hamilton's curvature ODE in dimension three, and its invariant sets.

Under Ricci flow the curvature operator evolves by `∂ₜ Rm = Δ Rm + Rm² + Rm^#`
(Hamilton 1982, §7–8; in an evolving orthonormal frame, Uhlenbeck's trick). In
dimension three the curvature operator is determined by its three eigenvalues
`λ ≥ μ ≥ ν` — twice the sectional curvatures, so that the scalar curvature is the
trace `R = λ + μ + ν` and the Ricci eigenvalues are `(μ + ν)/2, (λ + ν)/2, (λ + μ)/2`
(Cao--Zhu §2.4) — and the reaction
term `Rm² + Rm^#` is diagonal in the same eigenframe with entries

    λ² + μν,   μ² + λν,   ν² + λμ.

Hamilton's tensor maximum principle says that a closed convex set of curvature
operators preserved by the ODE `Ṙm = Rm² + Rm^#` is preserved by the PDE. So the
pinching estimates of Hamilton's paper reduce to statements about the ODE

    λ̇ = λ² + μν,   μ̇ = μ² + λν,   ν̇ = ν² + λμ,

and those are what this file proves — with no manifold in sight:

* `ordering_preserved` — `λ ≥ μ ≥ ν` is preserved;
* `ricci_pos_preserved` — positive Ricci curvature (`μ + ν > 0`) is preserved;
* `bound_preserved` — `λ ≤ C(μ + ν)` is preserved for `C ≥ 1/2`;
* `pinching_antitone` — given the above, `(λ - ν) (μ + ν)^{δ - 1}` is
  nonincreasing for `0 < δ ≤ 1/(2C + 1)`: the curvature pinches toward
  constant sectional curvature as it blows up (Hamilton 1982, Theorem 10.1;
  Chow–Knopf, Lemma 6.30 ff.).

The proofs are linear Grönwall comparisons: each quantity `f` satisfies
`f' = a f + (a term of known sign)` for a continuous `a`, so `f e^{-∫a}` is
monotone. The maximum-principle transfer from the ODE to the flow is the part
Mathlib does not have (`thm:max-tensor` in the blueprint).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set

namespace RicciFlowBlueprint
namespace Pinching

section Gronwall

variable {f f' a : ℝ → ℝ} {T : ℝ}

/-- **Linear Grönwall comparison.** If `f' ≤ a f` on `[0, T]` with `a` continuous there and
`f 0 ≤ 0`, then `f ≤ 0` on `[0, T]`. Proof: `f e^{-∫a}` is nonincreasing. -/
theorem nonpos_of_deriv_le_mul (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (ha : ContinuousOn a (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, f' t ≤ a t * f t) (h0 : f 0 ≤ 0) :
    ∀ t ∈ Icc 0 T, f t ≤ 0 := by
  -- extend `a` continuously to all of `ℝ` by projecting onto `[0, T]`
  set a' : ℝ → ℝ := fun u ↦ a (projIcc 0 T hT u) with ha'
  have ha'c : Continuous a' :=
    ha.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun u ↦ (projIcc 0 T hT u).2
  have ha'eq : ∀ u ∈ Icc 0 T, a' u = a u := fun u hu ↦ by
    simp [a', projIcc_of_mem hT hu]
  set A : ℝ → ℝ := fun u ↦ ∫ s in (0:ℝ)..u, a' s with hA
  have hAd : ∀ u, HasDerivAt A (a' u) u := fun u ↦
    intervalIntegral.integral_hasDerivAt_right (ha'c.intervalIntegrable _ _)
      (ha'c.stronglyMeasurableAtFilter _ _) ha'c.continuousAt
  have hA0 : A 0 = 0 := by simp [A]
  set g : ℝ → ℝ := fun u ↦ f u * Real.exp (-A u) with hg
  have hgd : ∀ u ∈ Icc 0 T, HasDerivAt g ((f' u - a' u * f u) * Real.exp (-A u)) u := by
    intro u hu
    exact ((hf u hu).mul ((hAd u).neg.exp)).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact fun u hu ↦ (hgd u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hgd u (Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu' := Ioo_subset_Icc_self hu
      rw [(hgd u hu').deriv, ha'eq u hu']
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle u hu']) (Real.exp_pos _).le
  intro t ht
  have h1 : g t ≤ g 0 := hanti ⟨le_rfl, hT⟩ ht ht.1
  have h2 : g 0 = f 0 := by simp [g, hA0]
  have h3 : g t = f t * Real.exp (-A t) := rfl
  rw [h2] at h1
  rw [h3] at h1
  have := Real.exp_pos (-A t)
  nlinarith

/-- If `a f ≤ f'` on `[0, T]` with `a` continuous there and `0 ≤ f 0`, then `0 ≤ f` on `[0, T]`. -/
theorem nonneg_of_mul_le_deriv (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (ha : ContinuousOn a (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, a t * f t ≤ f' t) (h0 : 0 ≤ f 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t := by
  have := nonpos_of_deriv_le_mul (f := fun t ↦ -f t) (f' := fun t ↦ -f' t) hT
    (fun t ht ↦ (hf t ht).neg) ha (fun t ht ↦ by show -f' t ≤ a t * -f t; linarith [hle t ht]) (by simpa using h0)
  intro t ht
  linarith [this t ht]

/-- If `a f ≤ f'` on `[0, T]` with `a` continuous there and `0 < f 0`, then `0 < f` on `[0, T]`. -/
theorem pos_of_mul_le_deriv (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (ha : ContinuousOn a (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, a t * f t ≤ f' t) (h0 : 0 < f 0) :
    ∀ t ∈ Icc 0 T, 0 < f t := by
  -- apply the nonneg version to `f - f 0 · e^{∫a}`… simpler: `f e^{-∫a}` is nondecreasing
  set a' : ℝ → ℝ := fun u ↦ a (projIcc 0 T hT u) with ha'
  have ha'c : Continuous a' :=
    ha.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun u ↦ (projIcc 0 T hT u).2
  have ha'eq : ∀ u ∈ Icc 0 T, a' u = a u := fun u hu ↦ by
    simp [a', projIcc_of_mem hT hu]
  set A : ℝ → ℝ := fun u ↦ ∫ s in (0:ℝ)..u, a' s with hA
  have hAd : ∀ u, HasDerivAt A (a' u) u := fun u ↦
    intervalIntegral.integral_hasDerivAt_right (ha'c.intervalIntegrable _ _)
      (ha'c.stronglyMeasurableAtFilter _ _) ha'c.continuousAt
  have hA0 : A 0 = 0 := by simp [A]
  set g : ℝ → ℝ := fun u ↦ f u * Real.exp (-A u) with hg
  have hgd : ∀ u ∈ Icc 0 T, HasDerivAt g ((f' u - a' u * f u) * Real.exp (-A u)) u := by
    intro u hu
    exact ((hf u hu).mul ((hAd u).neg.exp)).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hmono : MonotoneOn g (Icc 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) ?_ ?_ ?_
    · exact fun u hu ↦ (hgd u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hgd u (Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu' := Ioo_subset_Icc_self hu
      rw [(hgd u hu').deriv, ha'eq u hu']
      exact mul_nonneg (by linarith [hle u hu']) (Real.exp_pos _).le
  intro t ht
  have h1 : g 0 ≤ g t := hmono ⟨le_rfl, hT⟩ ht ht.1
  have h2 : g 0 = f 0 := by simp [g, hA0]
  have h3 : g t = f t * Real.exp (-A t) := rfl
  rw [h2, h3] at h1
  have := Real.exp_pos (-A t)
  nlinarith

end Gronwall

section CurvatureODE

/-- **Hamilton's curvature ODE in dimension three.** `l m n` are the eigenvalues `λ ≥ μ ≥ ν`
of the curvature operator along a solution of `Ṙm = Rm² + Rm^#`, on the time interval
`[0, T]`: `λ̇ = λ² + μν`, `μ̇ = μ² + λν`, `ν̇ = ν² + λμ`. -/
structure IsCurvatureODE (l m n : ℝ → ℝ) (T : ℝ) : Prop where
  hl : ∀ t ∈ Icc 0 T, HasDerivAt l (l t ^ 2 + m t * n t) t
  hm : ∀ t ∈ Icc 0 T, HasDerivAt m (m t ^ 2 + l t * n t) t
  hn : ∀ t ∈ Icc 0 T, HasDerivAt n (n t ^ 2 + l t * m t) t

variable {l m n : ℝ → ℝ} {T : ℝ}

theorem IsCurvatureODE.continuousOn_l (h : IsCurvatureODE l m n T) : ContinuousOn l (Icc 0 T) :=
  fun t ht ↦ (h.hl t ht).continuousAt.continuousWithinAt

theorem IsCurvatureODE.continuousOn_m (h : IsCurvatureODE l m n T) : ContinuousOn m (Icc 0 T) :=
  fun t ht ↦ (h.hm t ht).continuousAt.continuousWithinAt

theorem IsCurvatureODE.continuousOn_n (h : IsCurvatureODE l m n T) : ContinuousOn n (Icc 0 T) :=
  fun t ht ↦ (h.hn t ht).continuousAt.continuousWithinAt

-- BENCH: pinching-ordering
/-- **The ordering `λ ≥ μ` is preserved**: `(μ - λ)˙ = (μ - λ)(λ + μ - ν)`. -/
theorem IsCurvatureODE.le_preserved_lm (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (h0 : m 0 ≤ l 0) : ∀ t ∈ Icc 0 T, m t ≤ l t := by
  have := nonpos_of_deriv_le_mul (f := fun t ↦ m t - l t)
    (f' := fun t ↦ (m t ^ 2 + l t * n t) - (l t ^ 2 + m t * n t))
    (a := fun t ↦ l t + m t - n t) hT
    (fun t ht ↦ (h.hm t ht).sub (h.hl t ht))
    ((h.continuousOn_l.add h.continuousOn_m).sub h.continuousOn_n)
    (fun t _ ↦ le_of_eq (by ring)) (by simpa using h0)
  intro t ht
  linarith [this t ht]

/-- **The ordering `μ ≥ ν` is preserved**: `(ν - μ)˙ = (ν - μ)(μ + ν - λ)`. -/
theorem IsCurvatureODE.le_preserved_mn (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (h0 : n 0 ≤ m 0) : ∀ t ∈ Icc 0 T, n t ≤ m t := by
  have := nonpos_of_deriv_le_mul (f := fun t ↦ n t - m t)
    (f' := fun t ↦ (n t ^ 2 + l t * m t) - (m t ^ 2 + l t * n t))
    (a := fun t ↦ m t + n t - l t) hT
    (fun t ht ↦ (h.hn t ht).sub (h.hm t ht))
    ((h.continuousOn_m.add h.continuousOn_n).sub h.continuousOn_l)
    (fun t _ ↦ le_of_eq (by ring)) (by simpa using h0)
  intro t ht
  linarith [this t ht]

-- BENCH: pinching-ricci-pos
/-- **Positive Ricci curvature is preserved.** The smallest Ricci eigenvalue is `(μ + ν)/2`, and
`(μ + ν)˙ = μ² + ν² + λ(μ + ν) ≥ λ(μ + ν)`. -/
theorem IsCurvatureODE.ricci_pos_preserved (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (h0 : 0 < m 0 + n 0) : ∀ t ∈ Icc 0 T, 0 < m t + n t :=
  pos_of_mul_le_deriv (f := fun t ↦ m t + n t)
    (f' := fun t ↦ (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)) (a := l) hT
    (fun t ht ↦ (h.hm t ht).add (h.hn t ht)) h.continuousOn_l
    (fun t _ ↦ by
      show l t * (m t + n t) ≤ (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)
      nlinarith [sq_nonneg (m t), sq_nonneg (n t)])
    h0

-- BENCH: pinching-bound
/-- **The bound `λ ≤ C(μ + ν)` is preserved** for `C ≥ 1/2`:
`(λ - C(μ + ν))˙ = λ(λ - C(μ + ν)) + (μν - C(μ² + ν²))`, and `μν ≤ (μ² + ν²)/2`. -/
theorem IsCurvatureODE.bound_preserved (h : IsCurvatureODE l m n T) (hT : 0 ≤ T) {C : ℝ}
    (hC : 1 / 2 ≤ C) (h0 : l 0 ≤ C * (m 0 + n 0)) :
    ∀ t ∈ Icc 0 T, l t ≤ C * (m t + n t) := by
  have := nonpos_of_deriv_le_mul (f := fun t ↦ l t - C * (m t + n t))
    (f' := fun t ↦ (l t ^ 2 + m t * n t) - C * ((m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)))
    (a := l) hT
    (fun t ht ↦ (h.hl t ht).sub (((h.hm t ht).add (h.hn t ht)).const_mul C))
    h.continuousOn_l
    (fun t _ ↦ by
      show (l t ^ 2 + m t * n t) - C * ((m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)) ≤
        l t * (l t - C * (m t + n t))
      nlinarith [sq_nonneg (m t - n t),
        mul_nonneg (sub_nonneg.2 hC) (add_nonneg (sq_nonneg (m t)) (sq_nonneg (n t)))])
    (by simpa using h0)
  intro t ht
  linarith [this t ht]

-- BENCH: pinching-improves
/-- **Hamilton's pinching estimate for the ODE** (Hamilton 1982, Theorem 10.1). If at time `0`
the eigenvalues are ordered, `μ + ν > 0`, and `λ ≤ C(μ + ν)`, then for
`0 ≤ δ` with `δ(2C + 1) ≤ 1` the ratio `(λ - ν) / (μ + ν)^{1 - δ}` is nonincreasing:
the traceless part of the curvature is controlled by a *smaller power* of the scalar curvature,
so the curvature pinches toward constant sectional curvature wherever it blows up. -/
theorem IsCurvatureODE.pinching_antitone (h : IsCurvatureODE l m n T) (hT : 0 ≤ T) {C δ : ℝ}
    (hC : 1 / 2 ≤ C) (hδ : 0 ≤ δ) (hδC : δ * (2 * C + 1) ≤ 1)
    (h0lm : m 0 ≤ l 0) (h0mn : n 0 ≤ m 0) (h0B : 0 < m 0 + n 0) (h0C : l 0 ≤ C * (m 0 + n 0)) :
    AntitoneOn (fun t ↦ (l t - n t) * (m t + n t) ^ (δ - 1)) (Icc 0 T) := by
  have hlm := h.le_preserved_lm hT h0lm
  have hmn := h.le_preserved_mn hT h0mn
  have hB := h.ricci_pos_preserved hT h0B
  have hbd := h.bound_preserved hT hC h0C
  -- the derivative of the ratio
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t ↦ (l t - n t) * (m t + n t) ^ (δ - 1))
      ((m t + n t) ^ (δ - 2) *
        (((l t ^ 2 + m t * n t) - (n t ^ 2 + l t * m t)) * (m t + n t) +
          (δ - 1) * (l t - n t) * ((m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)))) t := by
    intro t ht
    have hBt : m t + n t ≠ 0 := (hB t ht).ne'
    have h1 := ((h.hl t ht).sub (h.hn t ht)).mul
      (((h.hm t ht).add (h.hn t ht)).rpow_const (p := δ - 1) (Or.inl hBt))
    refine h1.congr_deriv ?_
    have e1 : (m t + n t) ^ (δ - 1) = (m t + n t) ^ (δ - 2) * (m t + n t) := by
      rw [show δ - 1 = (δ - 2) + 1 by ring, Real.rpow_add_one hBt]
    have e2 : (δ - 1) - 1 = δ - 2 := by ring
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [e1, e2]
    ring
  -- the derivative is nonpositive
  have hneg : ∀ t ∈ Icc 0 T, (m t + n t) ^ (δ - 2) *
        (((l t ^ 2 + m t * n t) - (n t ^ 2 + l t * m t)) * (m t + n t) +
          (δ - 1) * (l t - n t) * ((m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t))) ≤ 0 := by
    intro t ht
    have hBt := hB t ht
    have hA : 0 ≤ l t - n t := by linarith [hlm t ht, hmn t ht]
    have hl := hbd t ht
    refine mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hBt.le _) ?_
    -- the bracket is `A * (δ λ B + (ν - μ) B - (1 - δ)(μ² + ν²))`
    have key : ((l t ^ 2 + m t * n t) - (n t ^ 2 + l t * m t)) * (m t + n t) +
        (δ - 1) * (l t - n t) * ((m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)) =
        (l t - n t) * (δ * l t * (m t + n t) + (n t - m t) * (m t + n t)
          - (1 - δ) * (m t ^ 2 + n t ^ 2)) := by ring
    rw [key]
    refine mul_nonpos_of_nonneg_of_nonpos hA ?_
    have hsq : (m t + n t) ^ 2 / 2 ≤ m t ^ 2 + n t ^ 2 := by nlinarith [sq_nonneg (m t - n t)]
    have h1 : δ * l t * (m t + n t) ≤ δ * C * (m t + n t) ^ 2 := by
      have : l t * (m t + n t) ≤ C * (m t + n t) * (m t + n t) :=
        mul_le_mul_of_nonneg_right hl hBt.le
      nlinarith [mul_le_mul_of_nonneg_left this hδ]
    have h2 : (n t - m t) * (m t + n t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [hmn t ht]) hBt.le
    have h3 : (1 - δ) * ((m t + n t) ^ 2 / 2) ≤ (1 - δ) * (m t ^ 2 + n t ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by nlinarith)
    have h4 : δ * C * (m t + n t) ^ 2 - (1 - δ) * ((m t + n t) ^ 2 / 2) ≤ 0 := by
      have : δ * C - (1 - δ) / 2 ≤ 0 := by linarith
      nlinarith [sq_nonneg (m t + n t)]
    linarith
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
  · exact fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hd t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t (Ioo_subset_Icc_self ht)).deriv]
    exact hneg t (Ioo_subset_Icc_self ht)

/-! ### The Hamilton--Ivey pinching estimate

Hamilton 1995 §4 / Ivey 1993; the presentation is Cao--Zhu, *Hamilton--Perelman's proof*,
Theorem 2.4.1. In the normalisation of `IsCurvatureODE` the scalar curvature is the trace
`R = λ + μ + ν`, and the estimate says: if `ν ≥ -1` everywhere at `t = 0`, then

    R ≥ (-ν) (log(-ν) - 3)   wherever `ν < 0`.

Negative curvature is dominated by the scalar curvature at a rate that degenerates only
logarithmically, so every blow-up limit of a three-dimensional flow has `ν ≥ 0`. That is the
standing hypothesis on a `κ`-solution, and nothing else supplies it.

Hamilton's proof runs the tensor maximum principle on the closed convex set

    K : λ + μ + ν ≥ -3   and   ν + f⁻¹(λ + μ + ν) ≥ 0,   f(x) = x (log x - 3) on `[e², ∞)`,

so the whole content at the ODE level is that `K` is preserved. The first inequality is
`le_scal` below: `R` is nondecreasing, full stop. The second is checked on the boundary,
where the defining relation eliminates the logarithm and leaves a polynomial inequality in
nonnegative reals — `hamiltonIvey_boundary_of_nonneg` and `hamiltonIvey_boundary_of_neg`,
Cao--Zhu's Case (i) and Case (ii).

Still to come: `f⁻¹` and its concavity, hence convexity of `K`; the assembly of the two
boundary cases into invariance of `K` under the ODE; and the time-dependent form of
`thm:max-tensor` needed for Hamilton's later improvement `R ≥ (-ν)(log(-ν) + log(1+t) - 3)`.
-/

/-- The trace of the curvature operator is the scalar curvature, and it evolves by
`Ṙ = λ² + μ² + ν² + λμ + λν + μν = ½[(λ+μ)² + (λ+ν)² + (μ+ν)²]`. -/
theorem IsCurvatureODE.hasDerivAt_scal (h : IsCurvatureODE l m n T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun t ↦ l t + m t + n t)
      (((l t + m t) ^ 2 + (l t + n t) ^ 2 + (m t + n t) ^ 2) / 2) t := by
  have key := ((h.hl t ht).add (h.hm t ht)).add (h.hn t ht)
  have hrw : ((l t + m t) ^ 2 + (l t + n t) ^ 2 + (m t + n t) ^ 2) / 2
      = (l t ^ 2 + m t * n t) + (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t) := by ring
  rw [hrw]
  exact key

-- BENCH: pinching-scal-monotone
/-- **A lower bound on the scalar curvature is preserved.** `Ṙ = ½[(λ+μ)² + (λ+ν)² + (μ+ν)²] ≥ 0`,
so `R` is nondecreasing along the curvature ODE. This is the first of the two inequalities
cutting out Hamilton's pinching set `K`, with `c = -3`. -/
theorem IsCurvatureODE.le_scal (h : IsCurvatureODE l m n T) (hT : 0 ≤ T) {c : ℝ}
    (h0 : c ≤ l 0 + m 0 + n 0) : ∀ t ∈ Icc 0 T, c ≤ l t + m t + n t := by
  have key := nonpos_of_deriv_le_mul (f := fun t ↦ c - (l t + m t + n t))
    (f' := fun t ↦ -(((l t + m t) ^ 2 + (l t + n t) ^ 2 + (m t + n t) ^ 2) / 2))
    (a := fun _ ↦ 0) hT
    (fun t ht ↦ (h.hasDerivAt_scal ht).const_sub c)
    continuousOn_const
    (fun t _ ↦ by
      have hS : (0:ℝ) ≤ ((l t + m t) ^ 2 + (l t + n t) ^ 2 + (m t + n t) ^ 2) / 2 := by positivity
      show -(((l t + m t) ^ 2 + (l t + n t) ^ 2 + (m t + n t) ^ 2) / 2)
        ≤ 0 * (c - (l t + m t + n t))
      linarith)
    (by simpa using h0)
  intro t ht
  linarith [key t ht]

-- BENCH: pinching-ivey-boundary
/-- **Hamilton--Ivey, boundary case `μ ≥ 0`** (Cao--Zhu, Theorem 2.4.1, Case (i)).

On the boundary of the pinching set the defining relation is `λ + μ = (-ν)(log(-ν) - 2)`;
writing `N = -ν` and `L = log N`, that is the hypothesis `hb`. What has to be checked is
`λ̇ + μ̇ ≥ (L - 1) (-ν)˙`, and substituting `hb` clears the logarithm: after multiplying
through by `N > 0` the claim is

    N(λ² + μ²) + N³ + λμ(λ + μ + N) ≥ 0,

every term of which is a product of nonnegatives. -/
theorem hamiltonIvey_boundary_of_nonneg {l m N L : ℝ}
    (hm : 0 ≤ m) (hml : m ≤ l) (hN : 0 < N) (hb : l + m = N * (L - 2)) :
    (L - 1) * (-(N ^ 2 + l * m)) ≤ (l ^ 2 - m * N) + (m ^ 2 - l * N) := by
  have hl : 0 ≤ l := hm.trans hml
  have hNL : N * (L - 1) = l + m + N := by linear_combination -hb
  refine le_of_mul_le_mul_left ?_ hN
  have hrw : N * ((L - 1) * (-(N ^ 2 + l * m))) = (N * (L - 1)) * (-(N ^ 2 + l * m)) := by ring
  rw [hrw, hNL]
  nlinarith [mul_nonneg hN.le (add_nonneg (sq_nonneg l) (sq_nonneg m)),
    mul_nonneg (mul_nonneg hl hm) (by linarith : (0:ℝ) ≤ l + m + N),
    pow_pos hN 3]

/-- **Hamilton--Ivey, boundary case `μ < 0`** (Cao--Zhu, Theorem 2.4.1, Case (ii)).

With `P = -μ > 0` and `N = -ν`, the ordering `ν ≤ μ` reads `P ≤ N`, and the boundary relation
is `λ = P + N(L - 2)`. The inequality to check is `λ̇ ≥ (-μ)˙ + (L - 1)(-ν)˙`, and after
substituting and multiplying by `N > 0` it becomes

    (λ² - λP + P²)(N - P) + P³ + N³ ≥ 0,

with `λ² - λP + P² = (λ - P/2)² + 3P²/4 ≥ 0` and `N - P ≥ 0`. (On the boundary one also has
`λ ≥ 0`, as Cao--Zhu note, but the inequality does not need it.) -/
theorem hamiltonIvey_boundary_of_neg {l P N L : ℝ}
    (hP : 0 < P) (hPN : P ≤ N) (hb : l = P + N * (L - 2)) :
    (l * N - P ^ 2) + (L - 1) * (l * P - N ^ 2) ≤ l ^ 2 + P * N := by
  have hN : 0 < N := hP.trans_le hPN
  have hNL : N * (L - 1) = l - P + N := by linear_combination -hb
  refine le_of_mul_le_mul_left ?_ hN
  have hrw : N * ((l * N - P ^ 2) + (L - 1) * (l * P - N ^ 2))
      = N * (l * N - P ^ 2) + (N * (L - 1)) * (l * P - N ^ 2) := by ring
  rw [hrw, hNL]
  nlinarith [mul_nonneg (by nlinarith [sq_nonneg (2 * l - P), sq_nonneg P] :
      (0:ℝ) ≤ l ^ 2 - l * P + P ^ 2) (by linarith : (0:ℝ) ≤ N - P),
    pow_pos hP 3, pow_pos hN 3]

/-! #### Hamilton's pinching function and his pinching set

`f(x) = x(log x - 3)` is increasing and convex on `[e², ∞)` (where `f'(x) = log x - 2 ≥ 0`),
with `f(e²) = -e²`, so it is a bijection onto `[-e², ∞)`. Hamilton's set is

    K : λ + μ + ν ≥ -3   and   ν + f⁻¹(λ + μ + ν) ≥ 0.

Since `f⁻¹` takes values in `[e², ∞)`, the second condition holds automatically when
`-ν ≤ e²` and is `f(-ν) ≤ λ + μ + ν` otherwise — which is how `IsIveyPinched` states it,
with no inverse function. (`f⁻¹` is still wanted for the *convexity* of `K`, which is what
the tensor maximum principle consumes; it is not needed for anything below.) -/

/-- **Hamilton's pinching function** `f(x) = x (log x - 3)`. -/
noncomputable def iveyF (x : ℝ) : ℝ := x * (Real.log x - 3)

@[simp] theorem iveyF_one : iveyF 1 = -3 := by simp [iveyF]

/-- `f'(x) = log x - 2`, so `f` decreases on `(0, e²)` and increases on `(e², ∞)`. -/
theorem hasDerivAt_iveyF {x : ℝ} (hx : 0 < x) : HasDerivAt iveyF (Real.log x - 2) x := by
  have h : HasDerivAt (fun y : ℝ ↦ y * (Real.log y - 3))
      (1 * (Real.log x - 3) + x * x⁻¹) x :=
    (hasDerivAt_id' (x := x)).mul ((Real.hasDerivAt_log hx.ne').sub_const 3)
  have heq : 1 * (Real.log x - 3) + x * x⁻¹ = Real.log x - 2 := by
    rw [mul_inv_cancel₀ hx.ne']; ring
  rw [heq] at h
  exact h

/-- `f` is antitone on `[1, e²]`, where `f' = log x - 2 ≤ 0`, so `f ≤ f(1) = -3` there.
This is what makes the first inequality of `K` do the work in the middle range. -/
theorem iveyF_le_neg_three {N : ℝ} (h1 : 1 ≤ N) (h2 : N ≤ Real.exp 2) : iveyF N ≤ -3 := by
  have h1e : (1:ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hanti : AntitoneOn iveyF (Icc 1 (Real.exp 2)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x ↦ Real.log x - 2)
      (convex_Icc _ _)
      (fun x hx ↦
        (hasDerivAt_iveyF (lt_of_lt_of_le zero_lt_one hx.1)).continuousAt.continuousWithinAt)
      (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [interior_Icc] at hx
      exact (hasDerivAt_iveyF (lt_trans zero_lt_one hx.1)).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx.1
      have : Real.log x ≤ 2 := (Real.log_le_iff_le_exp hx0).2 hx.2.le
      linarith
  simpa using hanti ⟨le_refl 1, h1e⟩ ⟨h1, h2⟩ h1

/-- **Hamilton's pinching set**, stated without the inverse function (see the discussion above):
`λ+μ+ν ≥ -3`, and either `-ν ≤ e²` or `f(-ν) ≤ λ+μ+ν`. -/
def IsIveyPinched (l m n : ℝ) : Prop :=
  -3 ≤ l + m + n ∧ (-n ≤ Real.exp 2 ∨ iveyF (-n) ≤ l + m + n)

/-- **The normalisation `ν ≥ -1` puts an ordered triple in `K`.** Both conditions are immediate:
`λ+μ+ν ≥ 3ν ≥ -3` by the ordering, and `-ν ≤ 1 ≤ e²`. This is the entry point of Hamilton's
argument — the hypothesis at `t = 0`, which for a closed manifold is arranged by scaling. -/
theorem isIveyPinched_of_neg_one_le {l m n : ℝ} (hml : m ≤ l) (hnm : n ≤ m) (hn : -1 ≤ n) :
    IsIveyPinched l m n :=
  ⟨by linarith, Or.inl (le_trans (by linarith) (Real.one_le_exp (by norm_num)))⟩

-- BENCH: pinching-ivey-unpack
/-- **The pinching set encodes the Hamilton--Ivey estimate.** For an ordered triple in `K` with
`ν < 0`, `R = λ+μ+ν ≥ (-ν)(log(-ν) - 3)`.

Three ranges of `N = -ν`. If `N > e²` this is the second condition of `K` verbatim. If `N ≤ 1`
then `log N ≤ 0`, so `f(N) ≤ -3N`, and the ordering `λ ≥ μ ≥ ν` gives `λ+μ+ν ≥ 3ν = -3N`. If
`1 ≤ N ≤ e²` then `f(N) ≤ f(1) = -3` by `iveyF_le_neg_three`, and the *first* condition of `K`
finishes it. The middle range is why `K` carries the seemingly unrelated bound
`λ+μ+ν ≥ -3` at all. -/
theorem le_of_isIveyPinched {l m n : ℝ} (hml : m ≤ l) (hnm : n ≤ m)
    (h : IsIveyPinched l m n) (hneg : n < 0) :
    iveyF (-n) ≤ l + m + n := by
  obtain ⟨hR, hcase⟩ := h
  rcases hcase with hsmall | hdone
  · have hN0 : (0:ℝ) < -n := by linarith
    rcases le_total (-n) 1 with h1 | h1
    · have hlog : Real.log (-n) ≤ 0 := Real.log_nonpos hN0.le h1
      have hord : -3 * (-n) ≤ l + m + n := by linarith
      have hf : iveyF (-n) ≤ -3 * (-n) :=
        calc iveyF (-n) = (-n) * (Real.log (-n) - 3) := rfl
          _ ≤ (-n) * (0 - 3) := by
              nlinarith [mul_nonneg hN0.le (neg_nonneg.2 hlog)]
          _ = -3 * (-n) := by ring
      linarith
    · exact le_trans (iveyF_le_neg_three h1 hsmall) hR
  · exact hdone

/-! #### Invariance of `K`: the two boundary cases are one Grönwall

Cao--Zhu check the boundary in two cases according to the sign of `μ`, but the two are the
same inequality: `hamiltonIvey_boundary_of_neg`'s hypothesis `λ = P + N(L-2)` with `P = -μ`
is `λ + μ = N(L-2)`, the hypothesis of the other. Eliminating `L` from either leaves the
*same* polynomial, `iveyE`, and it is nonnegative under the ordering alone — no boundary
relation, no logarithm.

That turns Hamilton's boundary argument into a linear Grönwall comparison. Writing
`Ψ = R - f(-ν)` for the defect and `N = -ν > 0`,

    Ψ' = iveyE / N - Ψ · (N² + λμ) / N,

identically, so `iveyE ≥ 0` gives `Ψ' ≥ a Ψ` with `a = -(N² + λμ)/N` continuous wherever
`ν < 0`, and `nonneg_of_mul_le_deriv` applies. -/

/-- The polynomial left after eliminating the logarithm from Hamilton's boundary condition:
`N(λ²+μ²) + N³ + λμ(λ+μ+N)`, with `N = -ν`. -/
def iveyE (l m N : ℝ) : ℝ := N * (l ^ 2 + m ^ 2) + N ^ 3 + l * m * (l + m + N)

-- BENCH: pinching-ivey-E
/-- **`iveyE ≥ 0` under the ordering alone.** This is Cao--Zhu's Case (i) and Case (ii)
unified: `hamiltonIvey_boundary_of_nonneg` and `hamiltonIvey_boundary_of_neg` are the two
halves of this proof, dressed in the boundary relation that eliminates the logarithm.

If `μ ≥ 0` then `λ ≥ μ ≥ 0` and every term is a product of nonnegatives. If `μ < 0` use

    N(λ²+μ²) + N³ + λμ(λ+μ+N) = (λ² + λμ + μ²)(N + μ) + N³ - μ³,

where `λ² + λμ + μ² = (λ + μ/2)² + ¾μ² ≥ 0`, `N + μ ≥ 0` is the ordering `ν ≤ μ`, and
`N³ - μ³ > 0` because `μ < 0 < N`. -/
theorem iveyE_nonneg {l m N : ℝ} (hml : m ≤ l) (hmN : -N ≤ m) (hN : 0 < N) :
    0 ≤ iveyE l m N := by
  unfold iveyE
  rcases le_total 0 m with hm | hm
  · have hl : 0 ≤ l := hm.trans hml
    have h1 : 0 ≤ N * (l ^ 2 + m ^ 2) := by positivity
    have h2 : 0 ≤ l * m * (l + m + N) := by positivity
    nlinarith [pow_pos hN 3]
  · have hq : 0 ≤ l ^ 2 + l * m + m ^ 2 := by nlinarith [sq_nonneg (2 * l + m), sq_nonneg m]
    have hNm : 0 ≤ N + m := by linarith
    have hm3 : m ^ 3 ≤ 0 := by
      nlinarith [mul_nonneg (sq_nonneg m) (neg_nonneg.2 hm)]
    have hcube : 0 ≤ N ^ 3 - m ^ 3 := by nlinarith [pow_pos hN 3]
    nlinarith [mul_nonneg hq hNm]

/-- The **defect** `Ψ = R - f(-ν)`. Hamilton's second condition, for an ordered triple, is
exactly `Ψ ≥ 0` (`le_of_isIveyPinched` in one direction, the definition in the other). -/
noncomputable def iveyPsi (l m n : ℝ) : ℝ := l + m + n - iveyF (-n)

/-- `Ψ' = λ̇ + μ̇ + ν̇ + (log(-ν) - 2) ν̇` along the curvature ODE, by the chain rule through
`hasDerivAt_iveyF`. -/
theorem IsCurvatureODE.hasDerivAt_iveyPsi (h : IsCurvatureODE l m n T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hn : n t < 0) :
    HasDerivAt (fun s ↦ iveyPsi (l s) (m s) (n s))
      ((l t ^ 2 + m t * n t) + (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)
        + (Real.log (-n t) - 2) * (n t ^ 2 + l t * m t)) t := by
  have hN : (0:ℝ) < -n t := by linarith
  have hu : HasDerivAt (fun s ↦ -n s) (-(n t ^ 2 + l t * m t)) t := (h.hn t ht).neg
  have hcomp := (hasDerivAt_iveyF hN).comp t hu
  rw [Function.comp_def] at hcomp
  have hsum := (((h.hl t ht).add (h.hm t ht)).add (h.hn t ht)).sub hcomp
  have heq : (l t ^ 2 + m t * n t) + (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)
      - (Real.log (-n t) - 2) * -(n t ^ 2 + l t * m t)
      = (l t ^ 2 + m t * n t) + (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)
        + (Real.log (-n t) - 2) * (n t ^ 2 + l t * m t) := by ring
  rw [heq] at hsum
  exact hsum

-- BENCH: pinching-ivey-invariant
/-- **The defect is nonnegative for as long as `ν < 0`** — the middle of Hamilton's argument.

The identity behind it is
\[ \Psi' \;=\; \frac{\texttt{iveyE}(\lambda,\mu,N)}{N} \;-\; \Psi\,\frac{N^2+\lambda\mu}{N},
   \qquad N = -\nu, \]
which holds with no hypotheses beyond `ν < 0` (`field_simp; ring`, the `log N` terms
cancelling). So `iveyE_nonneg` gives `a Ψ ≤ Ψ'` for the continuous
`a = -(N^2+\lambda\mu)/N`, and `nonneg_of_mul_le_deriv` finishes it. Cao--Zhu's boundary
argument is this Grönwall comparison restricted to `Ψ = 0`. -/
theorem IsCurvatureODE.iveyPsi_nonneg (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (hml : ∀ t ∈ Icc 0 T, m t ≤ l t) (hnm : ∀ t ∈ Icc 0 T, n t ≤ m t)
    (hneg : ∀ t ∈ Icc 0 T, n t < 0)
    (h0 : 0 ≤ iveyPsi (l 0) (m 0) (n 0)) :
    ∀ t ∈ Icc 0 T, 0 ≤ iveyPsi (l t) (m t) (n t) := by
  refine nonneg_of_mul_le_deriv (f := fun t ↦ iveyPsi (l t) (m t) (n t))
    (f' := fun t ↦ (l t ^ 2 + m t * n t) + (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)
      + (Real.log (-n t) - 2) * (n t ^ 2 + l t * m t))
    (a := fun t ↦ -(n t ^ 2 + l t * m t) / (-n t)) hT
    (fun t ht ↦ h.hasDerivAt_iveyPsi ht (hneg t ht)) ?_ (fun t ht ↦ ?_) h0
  · exact ((((h.continuousOn_n.pow 2).add (h.continuousOn_l.mul h.continuousOn_m)).neg).div
      h.continuousOn_n.neg (fun t ht ↦ by have := hneg t ht; intro hc; simp at hc; linarith))
  · have hN : (0:ℝ) < -n t := by linarith [hneg t ht]
    have hne : (-n t) ≠ 0 := ne_of_gt hN
    have hn0 : n t ≠ 0 := ne_of_lt (hneg t ht)
    have key : ((l t ^ 2 + m t * n t) + (m t ^ 2 + l t * n t) + (n t ^ 2 + l t * m t)
        + (Real.log (-n t) - 2) * (n t ^ 2 + l t * m t))
        - (-(n t ^ 2 + l t * m t) / (-n t)) * iveyPsi (l t) (m t) (n t)
        = iveyE (l t) (m t) (-n t) / (-n t) := by
      unfold iveyPsi iveyF iveyE
      set L := Real.log (-n t) with hL
      field_simp
      ring
    have hE : 0 ≤ iveyE (l t) (m t) (-n t) / (-n t) :=
      div_nonneg (iveyE_nonneg (hml t ht) (by linarith [hnm t ht]) hN) hN.le
    linarith

/-- **Non-negative curvature is preserved.** `ν̇ = ν² + λμ`, and the ordering gives
`λν ≤ ν² + λμ` — for `λ ≥ 0` because `μ ≥ ν`, and for `λ < 0` because then `ν ≤ μ ≤ λ < 0`, so
`(-λ)(μ-ν) ≤ (-ν)(-ν) = ν²`. Hence `ν̇ ≥ λ ν` and `nonneg_of_mul_le_deriv` applies. -/
theorem IsCurvatureODE.nonneg_preserved (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (h0lm : m 0 ≤ l 0) (h0mn : n 0 ≤ m 0) (h0 : 0 ≤ n 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ n t := by
  have hlm := h.le_preserved_lm hT h0lm
  have hmn := h.le_preserved_mn hT h0mn
  refine nonneg_of_mul_le_deriv (f := n) (f' := fun t ↦ n t ^ 2 + l t * m t) (a := l) hT
    (fun t ht ↦ h.hn t ht) h.continuousOn_l (fun t ht ↦ ?_) h0
  have h1 := hlm t ht
  have h2 := hmn t ht
  show l t * n t ≤ n t ^ 2 + l t * m t
  rcases le_total 0 (l t) with hl | hl
  · nlinarith [mul_nonneg hl (sub_nonneg.2 h2)]
  · nlinarith [mul_le_mul (by linarith : -l t ≤ -n t) (by linarith : m t - n t ≤ -n t)
      (by linarith) (by linarith)]

/-- **Time translation.** The curvature ODE restarted at `s`. Needed to run
`nonneg_preserved` from an interior time. -/
theorem IsCurvatureODE.shift (h : IsCurvatureODE l m n T) {s : ℝ} (hs0 : 0 ≤ s) :
    IsCurvatureODE (fun u ↦ l (s + u)) (fun u ↦ m (s + u)) (fun u ↦ n (s + u)) (T - s) where
  hl u hu := (h.hl (s + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add s u
  hm u hu := (h.hm (s + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add s u
  hn u hu := (h.hn (s + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add s u

/-- **Restriction to a shorter interval.** -/
theorem IsCurvatureODE.restrict (h : IsCurvatureODE l m n T) {S : ℝ} (hS : S ≤ T) :
    IsCurvatureODE l m n S where
  hl s hs := h.hl s ⟨hs.1, le_trans hs.2 hS⟩
  hm s hs := h.hm s ⟨hs.1, le_trans hs.2 hS⟩
  hn s hs := h.hn s ⟨hs.1, le_trans hs.2 hS⟩

/-- **`ν < 0` propagates backwards.** If `ν` is negative at `t`, it was negative on all of
`[0,t]`: otherwise `nonneg_preserved`, applied to the ODE restarted where `ν ≥ 0`, would make
`ν(t) ≥ 0`. -/
theorem IsCurvatureODE.neg_of_neg (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (h0lm : m 0 ≤ l 0) (h0mn : n 0 ≤ m 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hnt : n t < 0) : ∀ s ∈ Icc 0 t, n s < 0 := by
  have hlm := h.le_preserved_lm hT h0lm
  have hmn := h.le_preserved_mn hT h0mn
  intro s hs
  by_contra hcon
  have hc : 0 ≤ n s := not_lt.1 hcon
  have hsT : s ≤ T := le_trans hs.2 ht.2
  have hsmem : s ∈ Icc 0 T := ⟨hs.1, hsT⟩
  have hkey := (h.shift hs.1).nonneg_preserved (by linarith) (by simpa using hlm s hsmem)
    (by simpa using hmn s hsmem) (by simpa using hc) (t - s)
    ⟨by linarith [hs.2], by linarith [ht.2]⟩
  simp only [add_sub_cancel] at hkey
  linarith

-- BENCH: pinching-ivey-ode
/-- **The Hamilton--Ivey estimate at the level of the ODE** (Hamilton 1995 §4, Ivey 1993;
Cao--Zhu Theorem 2.4.1). For an ordered solution of the curvature ODE normalised by
`ν(0) ≥ -1`, at every time at which `ν < 0`,
\[ \lambda + \mu + \nu \ \ge\ (-\nu)\bigl(\log(-\nu) - 3\bigr) . \]

The three parts: `isIveyPinched_of_neg_one_le` puts the initial data in Hamilton's set `K`;
`iveyPsi_nonneg` carries the defect `Ψ = R - f(-ν)` forward, by the Grönwall comparison that
`iveyE_nonneg` powers; `le_of_isIveyPinched` reads the estimate back off `K`. `neg_of_neg`
supplies the hypothesis `iveyPsi_nonneg` needs, that `ν < 0` on the whole of `[0,t]` —
non-negative curvature is preserved, so a later negative `ν` was negative all along.

This is the ODE half. Transporting it to the flow is `thm:max-tensor` applied to `K`, which
additionally wants `K` convex — and that is the one place `f⁻¹` is needed. -/
theorem IsCurvatureODE.hamiltonIvey (h : IsCurvatureODE l m n T) (hT : 0 ≤ T)
    (h0lm : m 0 ≤ l 0) (h0mn : n 0 ≤ m 0) (h0n : -1 ≤ n 0) :
    ∀ t ∈ Icc 0 T, n t < 0 → iveyF (-n t) ≤ l t + m t + n t := by
  intro t ht hnt
  have ht0 : (0:ℝ) ≤ t := ht.1
  have hneg := h.neg_of_neg hT h0lm h0mn ht hnt
  have hres := h.restrict ht.2
  have hlm := hres.le_preserved_lm ht0 h0lm
  have hmn := hres.le_preserved_mn ht0 h0mn
  have hstart : 0 ≤ iveyPsi (l 0) (m 0) (n 0) :=
    sub_nonneg.2 (le_of_isIveyPinched h0lm h0mn
      (isIveyPinched_of_neg_one_le h0lm h0mn h0n) (hneg 0 ⟨le_refl 0, ht0⟩))
  have hmid := hres.iveyPsi_nonneg ht0 hlm hmn hneg hstart t ⟨ht0, le_refl t⟩
  unfold iveyPsi at hmid
  linarith

end CurvatureODE

end Pinching
end RicciFlowBlueprint
