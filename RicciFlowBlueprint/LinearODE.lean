/-
**Linear ODEs: the Picard–Dyson iterates.**

The equation `Φ'(t) = A(t) ∘ Φ(t)`, `Φ(0) = 1`, for a continuous family of bounded operators
`A : ℝ → (F →L[ℝ] F)`. This is the ODE **Uhlenbeck's trick** needs: the trivialising family
solves `∂ₜι = Ric ∘ ι`, which is linear in `ι`.

**Why this is built here rather than taken from Mathlib.** `Analysis/ODE/PicardLindelof.lean`
does prove existence on a whole interval (`IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard`),
but gated on its field `mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`, where `L` bounds
the vector field on a ball of radius `a` about `x₀`. For a *linear* field `f t x = A t x` with
`‖A t‖ ≤ C` the best available bound is `L = C(‖x₀‖ + a)`, so on `[0,T]` the condition reads
`C(‖x₀‖ + a) T ≤ a - r` --- which for `r = 0` needs `a(1 - CT) ≥ C‖x₀‖T`, i.e. **`C·T < 1`**.
Past that one has to continue the solution across a chain of short intervals, and Mathlib has no
maximal-solution or continuation theory (see CLAUDE.md's gap list).

**The Dyson series does not need continuation.** The iterates `Iₙ` satisfy
`‖Iₙ(t)‖ ≤ (C|t|)ⁿ / n!`, and the factorial beats the power at every `t`, so the series converges
on the whole line with no smallness hypothesis at all. That is the classical reason linear ODEs
are globally solvable, and it is what this file sets up.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.ODE.ExistUnique

open intervalIntegral Set

namespace RicciFlowBlueprint

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The Picard iterates for `Φ' = A(t) ∘ Φ` with `Φ(0) = 1`: `I₀ = 1` and
`Iₙ₊₁(t) = ∫₀ᵗ A(s) ∘ Iₙ(s) ds`. The integral is junk where the integrand fails to be
integrable, which the continuity lemmas below rule out. -/
noncomputable def dysonIter (A : ℝ → (F →L[ℝ] F)) : ℕ → ℝ → (F →L[ℝ] F)
  | 0, _ => 1
  | n + 1, t => ∫ s in (0 : ℝ)..t, (A s).comp (dysonIter A n s)

omit [CompleteSpace F] in
@[simp] theorem dysonIter_zero (A : ℝ → (F →L[ℝ] F)) (t : ℝ) : dysonIter A 0 t = 1 := rfl

omit [CompleteSpace F] in
theorem dysonIter_succ (A : ℝ → (F →L[ℝ] F)) (n : ℕ) (t : ℝ) :
    dysonIter A (n + 1) t = ∫ s in (0 : ℝ)..t, (A s).comp (dysonIter A n s) := rfl

omit [CompleteSpace F] in
@[simp] theorem dysonIter_succ_zero (A : ℝ → (F →L[ℝ] F)) (n : ℕ) :
    dysonIter A (n + 1) 0 = 0 := by
  rw [dysonIter_succ, intervalIntegral.integral_same]

omit [CompleteSpace F] in
/-- **Every iterate is continuous.** Induction: `I₀` is constant, and an integral with a
continuous integrand is continuous in its endpoint. -/
theorem continuous_dysonIter {A : ℝ → (F →L[ℝ] F)} (hA : Continuous A) (n : ℕ) :
    Continuous (dysonIter A n) := by
  induction n with
  | zero =>
    show Continuous fun _ : ℝ ↦ (1 : F →L[ℝ] F)
    exact continuous_const
  | succ n ih =>
    have hcont : Continuous fun s ↦ (A s).comp (dysonIter A n s) :=
      (ContinuousLinearMap.compL ℝ F F F).continuous₂.comp₂ hA ih
    have := intervalIntegral.continuous_primitive
      (μ := MeasureTheory.volume) (f := fun s ↦ (A s).comp (dysonIter A n s))
      (fun a b ↦ (hcont.intervalIntegrable a b)) 0
    have heq : dysonIter A (n + 1)
        = fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, (A x).comp (dysonIter A n x) := rfl
    rw [heq]
    exact this
omit [CompleteSpace F] in
/-- **The factorial bound** `‖Iₙ(t)‖ ≤ (C t)ⁿ / n!`, for `‖A s‖ ≤ C` and `t ≥ 0`.

This is the whole reason a linear ODE is solvable on *any* interval with no smallness
hypothesis: the factorial beats the power at every `t`, so the series `∑ₙ Iₙ(t)` converges
however large `C·t` is. A cruder bound `‖Iₙ(t)‖ ≤ (Ct)ⁿ` --- what one gets by estimating the
integrand by its value at the endpoint --- would be useless past `C·t = 1`, which is exactly
the regime where Mathlib's `IsPicardLindelof.mul_max_le` also gives out. The factorial comes
from integrating `sⁿ` rather than bounding it. -/
theorem norm_dysonIter_le_of_nonneg {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖dysonIter A n t‖ ≤ (C * t) ^ n / n.factorial := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  induction n generalizing t with
  | zero =>
    have : ‖(1 : F →L[ℝ] F)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa using this
  | succ n ih =>
    have hcont : Continuous fun s ↦ (A s).comp (dysonIter A n s) :=
      (ContinuousLinearMap.compL ℝ F F F).continuous₂.comp₂ hA (continuous_dysonIter hA n)
    have hbdd : Continuous fun s : ℝ ↦ C ^ (n + 1) / n.factorial * s ^ n :=
      continuous_const.mul (continuous_pow n)
    rw [dysonIter_succ]
    calc ‖∫ s in (0 : ℝ)..t, (A s).comp (dysonIter A n s)‖
        ≤ ∫ s in (0 : ℝ)..t, ‖(A s).comp (dysonIter A n s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, C ^ (n + 1) / n.factorial * s ^ n := by
          refine intervalIntegral.integral_mono_on ht
            (hcont.norm.intervalIntegrable 0 t) (hbdd.intervalIntegrable 0 t) fun s hs ↦ ?_
          have hs0 : 0 ≤ s := hs.1
          have h1 : ‖(A s).comp (dysonIter A n s)‖ ≤ ‖A s‖ * ‖dysonIter A n s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          have h2 : ‖A s‖ * ‖dysonIter A n s‖ ≤ C * ((C * s) ^ n / n.factorial) := by
            refine mul_le_mul (hC s) (ih hs0) (norm_nonneg _) hC0
          refine h1.trans (h2.trans (le_of_eq ?_))
          rw [mul_pow]
          field_simp
          ring
      _ = (C * t) ^ (n + 1) / (n + 1).factorial := by
          rw [intervalIntegral.integral_const_mul, integral_pow]
          rw [Nat.factorial_succ, mul_pow]
          field_simp
          push_cast
          ring

omit [CompleteSpace F] in
/-- **The factorial bound at any sign of `t`**: `‖Iₙ(t)‖ ≤ (C|t|)ⁿ / n!`.

The two-sided form is what the termwise differentiation of the series needs --- `HasDerivAt` at
`t = 0` looks at a two-sided neighbourhood, so a bound on `[0,∞)` alone will not do. The
negative branch is the positive one run backwards: `∫₀ᵗ = −∫ₜ⁰`, and on `[t,0]` one has
`|s| = −s`, so the model integral is `∫ₜ⁰ (−s)ⁿ ds = ∫₀^{−t} sⁿ ds` by `integral_comp_neg`. -/
theorem norm_dysonIter_le {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (n : ℕ) (t : ℝ) :
    ‖dysonIter A n t‖ ≤ (C * |t|) ^ n / n.factorial := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  induction n generalizing t with
  | zero =>
    have : ‖(1 : F →L[ℝ] F)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa using this
  | succ n ih =>
    have hcont : Continuous fun s ↦ (A s).comp (dysonIter A n s) :=
      (ContinuousLinearMap.compL ℝ F F F).continuous₂.comp₂ hA (continuous_dysonIter hA n)
    -- the pointwise bound on the integrand, valid at every `s`
    have hpt : ∀ s : ℝ, ‖(A s).comp (dysonIter A n s)‖ ≤ C ^ (n + 1) / n.factorial * |s| ^ n := by
      intro s
      have h1 : ‖(A s).comp (dysonIter A n s)‖ ≤ ‖A s‖ * ‖dysonIter A n s‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      have h2 : ‖A s‖ * ‖dysonIter A n s‖ ≤ C * ((C * |s|) ^ n / n.factorial) :=
        mul_le_mul (hC s) (ih s) (norm_nonneg _) hC0
      refine h1.trans (h2.trans (le_of_eq ?_))
      rw [mul_pow]; field_simp; ring
    rw [dysonIter_succ]
    rcases le_total 0 t with ht | ht
    · have habs : ∀ s ∈ Set.uIcc (0 : ℝ) t, |s| = s := by
        intro s hs
        rw [Set.uIcc_of_le ht] at hs
        exact abs_of_nonneg hs.1
      calc ‖∫ s in (0 : ℝ)..t, (A s).comp (dysonIter A n s)‖
          ≤ ∫ s in (0 : ℝ)..t, ‖(A s).comp (dysonIter A n s)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht
        _ ≤ ∫ s in (0 : ℝ)..t, C ^ (n + 1) / n.factorial * s ^ n := by
            refine intervalIntegral.integral_mono_on ht
              (hcont.norm.intervalIntegrable 0 t)
              ((continuous_const.mul (continuous_pow n)).intervalIntegrable 0 t) fun s hs ↦ ?_
            have := hpt s
            rwa [abs_of_nonneg hs.1] at this
        _ = (C * |t|) ^ (n + 1) / (n + 1).factorial := by
            rw [intervalIntegral.integral_const_mul, integral_pow, abs_of_nonneg ht,
              Nat.factorial_succ, mul_pow]
            field_simp
            push_cast
            ring
    · have hneg : ∫ s in (0 : ℝ)..t, (A s).comp (dysonIter A n s)
          = -∫ s in t..(0 : ℝ), (A s).comp (dysonIter A n s) :=
        intervalIntegral.integral_symm _ _
      rw [hneg, norm_neg]
      calc ‖∫ s in t..(0 : ℝ), (A s).comp (dysonIter A n s)‖
          ≤ ∫ s in t..(0 : ℝ), ‖(A s).comp (dysonIter A n s)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht
        _ ≤ ∫ s in t..(0 : ℝ), C ^ (n + 1) / n.factorial * (-s) ^ n := by
            refine intervalIntegral.integral_mono_on ht
              (hcont.norm.intervalIntegrable t 0)
              ((continuous_const.mul ((continuous_neg).pow n)).intervalIntegrable t 0) fun s hs ↦ ?_
            have := hpt s
            rwa [abs_of_nonpos hs.2] at this
        _ = (C * |t|) ^ (n + 1) / (n + 1).factorial := by
            rw [intervalIntegral.integral_const_mul]
            rw [show (∫ s in t..(0 : ℝ), (-s) ^ n) = ∫ s in (0 : ℝ)..(-t), s ^ n by
              rw [intervalIntegral.integral_comp_neg (fun s ↦ s ^ n)]; norm_num]
            rw [integral_pow, abs_of_nonpos ht, Nat.factorial_succ, mul_pow]
            field_simp
            push_cast
            ring

/-- **The series converges at every `t`**, with no smallness hypothesis: the factorial bound
dominates it by `∑ₙ (C|t|)ⁿ/n!`, which is `Real.summable_pow_div_factorial`. -/
theorem summable_dysonIter {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) : Summable (fun n ↦ dysonIter A n t) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial (C * |t|))
    (fun n ↦ norm_dysonIter_le hA hC n t)

/-- **The fundamental solution** `Φ(t) = ∑ₙ Iₙ(t)` of `Φ' = A(t) ∘ Φ`, `Φ(0) = 1`. -/
noncomputable def dysonSum (A : ℝ → (F →L[ℝ] F)) (t : ℝ) : F →L[ℝ] F := ∑' n, dysonIter A n t

omit [CompleteSpace F] in
/-- `Φ(0) = 1`: every iterate past the zeroth starts at `0`. -/
@[simp] theorem dysonSum_zero (A : ℝ → (F →L[ℝ] F)) : dysonSum A 0 = 1 := by
  rw [dysonSum, tsum_eq_single 0 (fun n hn ↦ ?_)]
  · exact dysonIter_zero A 0
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact dysonIter_succ_zero A m

/-- Each iterate past the zeroth is differentiable, with `Iₙ₊₁' = A(t) ∘ Iₙ(t)` --- the
fundamental theorem of calculus for a continuous integrand. -/
theorem hasDerivAt_dysonIter_succ {A : ℝ → (F →L[ℝ] F)} (hA : Continuous A) (n : ℕ) (t : ℝ) :
    HasDerivAt (dysonIter A (n + 1)) ((A t).comp (dysonIter A n t)) t := by
  have hcont : Continuous fun s ↦ (A s).comp (dysonIter A n s) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous₂.comp₂ hA (continuous_dysonIter hA n)
  have h := (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have heq : dysonIter A (n + 1)
      = fun u : ℝ ↦ ∫ x in (0 : ℝ)..u, (A x).comp (dysonIter A n x) := rfl
  rw [heq]
  exact h

-- BENCH: dyson-fundamental-solution
/-- **`Φ' = A(t) ∘ Φ`** --- the fundamental solution solves the equation, at every `t`, with no
smallness hypothesis anywhere.

**The series is differentiated termwise, not swapped with an integral.** Mathlib's
`hasDerivAt_tsum_of_isPreconnected` asks for a summable bound on the derivatives, uniform on an
open preconnected set; here the derivatives are `A(y) ∘ Iₙ(y)`, bounded by `C(CR)ⁿ/n!` on
`(-R, R)`, and that is summable by the factorial. Swapping `∑` with `∫₀ᵗ` instead would have
meant dominated convergence and `ENNReal` bookkeeping for no gain.

**The index is shifted before applying it**: the derivative of `Iₙ₊₁` is `A ∘ Iₙ`, so summing
over `Iₙ₊₁` rather than `Iₙ` is what makes the bound's index match the term's. The zeroth
iterate is then the constant `1`, which contributes nothing to the derivative. -/
theorem hasDerivAt_dysonSum {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) :
    HasDerivAt (dysonSum A) ((A t).comp (dysonSum A t)) t := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set R : ℝ := |t| + 1 with hR
  have hRpos : 0 < R := by positivity
  have htR : t ∈ Set.Ioo (-R) R := by
    constructor
    · have := abs_nonneg t; have := neg_abs_le t; simp only [hR]; linarith
    · have := le_abs_self t; simp only [hR]; linarith
  have h0R : (0 : ℝ) ∈ Set.Ioo (-R) R := ⟨by linarith, hRpos⟩
  -- the uniform summable bound on the derivatives
  have hu : Summable fun n : ℕ ↦ C * ((C * R) ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial (C * R)).mul_left C
  -- each shifted term is differentiable, with the matching bound
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      HasDerivAt (fun z ↦ dysonIter A (n + 1) z) ((A y).comp (dysonIter A n y)) y :=
    fun n y _ ↦ hasDerivAt_dysonIter_succ hA n y
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      ‖(A y).comp (dysonIter A n y)‖ ≤ C * ((C * R) ^ n / n.factorial) := by
    intro n y hy
    have hyR : |y| ≤ R := by
      rw [abs_le]; exact ⟨hy.1.le, hy.2.le⟩
    have h1 : ‖(A y).comp (dysonIter A n y)‖ ≤ ‖A y‖ * ‖dysonIter A n y‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : ‖A y‖ * ‖dysonIter A n y‖ ≤ C * ((C * |y|) ^ n / n.factorial) :=
      mul_le_mul (hC y) (norm_dysonIter_le hA hC n y) (norm_nonneg _) hC0
    refine h1.trans (h2.trans ?_)
    have h3 : (C * |y|) ^ n ≤ (C * R) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg y]) n
    have h4 : (0 : ℝ) < n.factorial := by positivity
    exact mul_le_mul_of_nonneg_left (by gcongr) hC0
  have hg0 : Summable fun n : ℕ ↦ dysonIter A (n + 1) (0 : ℝ) := by
    simp
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (isPreconnected_Ioo) hg hg' h0R hg0 htR
  -- reassemble `Φ = 1 + ∑ₙ Iₙ₊₁` and identify the derivative
  have hsplit : dysonSum A = fun z ↦ (1 : F →L[ℝ] F) + ∑' n, dysonIter A (n + 1) z := by
    funext z
    rw [dysonSum, ← (summable_dysonIter hA hC z).sum_add_tsum_nat_add 1]
    simp
  have hval : ∑' n, (A t).comp (dysonIter A n t) = (A t).comp (dysonSum A t) := by
    rw [dysonSum]
    exact ((ContinuousLinearMap.compL ℝ F F F) (A t)).map_tsum (summable_dysonIter hA hC t) |>.symm
  rw [← hval, hsplit]
  exact key.const_add _

omit [CompleteSpace F] in
/-- **No blow-up**: `‖Φ(t)‖ ≤ exp(C|t|)`.  Summing the factorial bound is summing the exponential
series, `NormedSpace.exp_eq_tsum_div` at `Real.exp`. -/
theorem norm_dysonSum_le {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) : ‖dysonSum A t‖ ≤ Real.exp (C * |t|) := by
  have hfac : Summable fun n : ℕ ↦ (C * |t|) ^ n / n.factorial :=
    Real.summable_pow_div_factorial (C * |t|)
  have hnorm : Summable fun n : ℕ ↦ ‖dysonIter A n t‖ :=
    hfac.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_dysonIter_le hA hC n t)
  calc ‖dysonSum A t‖ ≤ ∑' n : ℕ, ‖dysonIter A n t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (C * |t|) ^ n / n.factorial :=
        hnorm.tsum_le_tsum (fun n ↦ norm_dysonIter_le hA hC n t) hfac
    _ = Real.exp (C * |t|) := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The vector solution `x(t) = Φ(t)v` of `ẋ = A(t)x`, `x(0) = v`. -/
theorem hasDerivAt_dysonSum_apply {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (v : F) (t : ℝ) :
    HasDerivAt (fun s ↦ dysonSum A s v) (A t (dysonSum A t v)) t := by
  simpa using (hasDerivAt_dysonSum hA hC t).clm_apply (hasDerivAt_const t v)

-- BENCH: linear-ode-uniqueness
omit [CompleteSpace F] in
/-- **Global uniqueness for a linear ODE.**  Two solutions of `ẋ = A(t)x` defined on all of `ℝ`
and agreeing at **any one** time are equal --- the base time is arbitrary, which is what makes
the propagator invertible below.

Mathlib's `ODE_solution_unique_univ` applies verbatim; the only thing to supply is a Lipschitz
constant **uniform in `t`**, which a bounded `A` gives (`‖A t‖₊ ≤ C.toNNReal`).  No smallness
hypothesis and no continuation argument: a linear field is globally Lipschitz, so the
whole-line statement is available directly. -/
theorem eq_of_hasDerivAt_linear {A : ℝ → (F →L[ℝ] F)} {C t₀ : ℝ} (hC : ∀ s, ‖A s‖ ≤ C)
    {f g : ℝ → F} (hf : ∀ t, HasDerivAt f (A t (f t)) t) (hg : ∀ t, HasDerivAt g (A t (g t)) t)
    (h0 : f t₀ = g t₀) : f = g := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hlip : ∀ t : ℝ, LipschitzOnWith C.toNNReal (fun x ↦ A t x) (Set.univ : Set F) := by
    intro t
    refine ((A t).lipschitzWith.weaken ?_).lipschitzOnWith
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC0]
    exact hC t
  exact ODE_solution_unique_univ (t₀ := t₀) hlip (fun t ↦ ⟨hf t, trivial⟩)
    (fun t ↦ ⟨hg t, trivial⟩) h0

/-- **The fundamental solution is the only one**: every global solution of `ẋ = A(t)x` is
`x(t) = Φ(t)x(0)`.  With `hasDerivAt_dysonSum` this is existence-and-uniqueness on the whole
line for a linear equation --- what mathlib's local theory does not give. -/
theorem eq_dysonSum_apply {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) {f : ℝ → F} (hf : ∀ t, HasDerivAt f (A t (f t)) t) (t : ℝ) :
    f t = dysonSum A t (f 0) :=
  congrFun (eq_of_hasDerivAt_linear (t₀ := 0) hC hf
    (fun s ↦ hasDerivAt_dysonSum_apply hA hC (f 0) s) (by simp)) t

/-- **The propagator based at `t₀`**: `U(t, t₀)`, the fundamental solution normalised at `t₀`
rather than at `0`.  It is the Dyson sum of the time-shifted family. -/
noncomputable def dysonFrom (A : ℝ → (F →L[ℝ] F)) (t₀ t : ℝ) : F →L[ℝ] F :=
  dysonSum (fun r ↦ A (r + t₀)) (t - t₀)

omit [CompleteSpace F] in
@[simp] theorem dysonFrom_self (A : ℝ → (F →L[ℝ] F)) (t₀ : ℝ) : dysonFrom A t₀ t₀ = 1 := by
  rw [dysonFrom, sub_self, dysonSum_zero]

/-- `t ↦ U(t,t₀)v` solves `ẋ = A(t)x` with `x(t₀) = v`. -/
theorem hasDerivAt_dysonFrom_apply {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t₀ : ℝ) (v : F) (t : ℝ) :
    HasDerivAt (fun s ↦ dysonFrom A t₀ s v) (A t (dysonFrom A t₀ t v)) t := by
  have hA' : Continuous fun r ↦ A (r + t₀) := hA.comp (continuous_id.add continuous_const)
  have hC' : ∀ r, ‖A (r + t₀)‖ ≤ C := fun r ↦ hC _
  have hout := hasDerivAt_dysonSum_apply hA' hC' v (t - t₀)
  have key := hout.comp_sub_const t t₀
  rw [sub_add_cancel] at key
  exact key

-- BENCH: linear-ode-propagator-invertible
/-- **The fundamental solution is invertible at every time.**

Both halves come from uniqueness alone, with no second series and no adjoint.
*Injective*: if `Φ(t)v = 0` then `s ↦ Φ(s)v` and the zero solution agree at `t`, hence
everywhere, so `v = 0` --- this is **backward uniqueness**, and it is exactly what the
arbitrary base time in `eq_of_hasDerivAt_linear` buys.
*Surjective*: `s ↦ U(s,t)w` is a global solution taking the value `w` at `t`, so it is
`Φ(s)` applied to its own value at `0`, and `w` is in the range. -/
theorem bijective_dysonSum {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) : Function.Bijective (dysonSum A t) := by
  constructor
  · intro v w hvw
    -- reduce to injectivity at `0` by linearity
    have hz : dysonSum A t (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hsol : ∀ s, HasDerivAt (fun r ↦ dysonSum A r (v - w)) (A s (dysonSum A s (v - w))) s :=
      fun s ↦ hasDerivAt_dysonSum_apply hA hC _ s
    have hzero : ∀ s : ℝ, HasDerivAt (fun _ : ℝ ↦ (0 : F)) (A s ((fun _ : ℝ ↦ (0 : F)) s)) s := by
      intro s
      simpa using (hasDerivAt_const s (0 : F))
    have := eq_of_hasDerivAt_linear (t₀ := t) hC hsol hzero (by simpa using hz)
    have h0 := congrFun this 0
    simp only [dysonSum_zero] at h0
    have : v - w = 0 := by simpa using h0
    exact sub_eq_zero.mp this
  · intro w
    refine ⟨dysonFrom A t 0 w, ?_⟩
    have hsol : ∀ s, HasDerivAt (fun r ↦ dysonFrom A t r w) (A s (dysonFrom A t s w)) s :=
      fun s ↦ hasDerivAt_dysonFrom_apply hA hC t w s
    have hsol' : ∀ s, HasDerivAt (fun r ↦ dysonSum A r (dysonFrom A t 0 w))
        (A s (dysonSum A s (dysonFrom A t 0 w))) s :=
      fun s ↦ hasDerivAt_dysonSum_apply hA hC _ s
    have := eq_of_hasDerivAt_linear (t₀ := 0) hC hsol hsol' (by simp)
    have ht := congrFun this t
    simpa using ht.symm

/-- **`Φ(t)` as a linear homeomorphism.**  Bijectivity plus the open mapping theorem. -/
noncomputable def dysonEquiv {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) : F ≃L[ℝ] F :=
  ContinuousLinearEquiv.ofBijective (dysonSum A t)
    (LinearMap.ker_eq_bot.mpr (bijective_dysonSum hA hC t).1)
    (LinearMap.range_eq_top.mpr (bijective_dysonSum hA hC t).2)

@[simp] theorem dysonEquiv_apply {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
    (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) (v : F) : dysonEquiv hA hC t v = dysonSum A t v := rfl

end RicciFlowBlueprint
