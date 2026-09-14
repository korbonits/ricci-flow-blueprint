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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

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
/-- **The two-sided integral estimate**: a continuous integrand bounded by `K|s|ⁿ` has its
primitive at `0` bounded by `K|t|ⁿ⁺¹/(n+1)`.

This is the only place the sign of `t` is ever split, and both the iterate bound and the
parameter-derivative bound are one line on top of it. The negative branch is the positive one
run backwards: `∫₀ᵗ = −∫ₜ⁰`, and on `[t,0]` one has `|s| = −s`, so the model integral is
`∫ₜ⁰ (−s)ⁿ ds = ∫₀^{−t} sⁿ ds` by `integral_comp_neg`. The two-sided form is what termwise
differentiation of the series needs: `HasDerivAt` at `t = 0` looks at a two-sided
neighbourhood, so a bound on `[0,∞)` alone will not do. -/
theorem norm_integral_le_of_norm_le_pow {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → G} (hg : Continuous g) {K : ℝ} {n : ℕ} (h : ∀ s, ‖g s‖ ≤ K * |s| ^ n) (t : ℝ) :
    ‖∫ s in (0 : ℝ)..t, g s‖ ≤ K * |t| ^ (n + 1) / (n + 1) := by
  have hK : 0 ≤ K := by have := h 1; simp at this; exact le_trans (norm_nonneg _) this
  rcases le_total 0 t with ht | ht
  · calc ‖∫ s in (0 : ℝ)..t, g s‖
        ≤ ∫ s in (0 : ℝ)..t, ‖g s‖ := intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, K * s ^ n := by
          refine intervalIntegral.integral_mono_on ht (hg.norm.intervalIntegrable 0 t)
            ((continuous_const.mul (continuous_pow n)).intervalIntegrable 0 t) fun s hs ↦ ?_
          have := h s
          rwa [abs_of_nonneg hs.1] at this
      _ = K * |t| ^ (n + 1) / (n + 1) := by
          rw [intervalIntegral.integral_const_mul, integral_pow, abs_of_nonneg ht]
          ring
  · have hneg : ∫ s in (0 : ℝ)..t, g s = -∫ s in t..(0 : ℝ), g s :=
      intervalIntegral.integral_symm _ _
    rw [hneg, norm_neg]
    calc ‖∫ s in t..(0 : ℝ), g s‖
        ≤ ∫ s in t..(0 : ℝ), ‖g s‖ := intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in t..(0 : ℝ), K * (-s) ^ n := by
          refine intervalIntegral.integral_mono_on ht (hg.norm.intervalIntegrable t 0)
            ((continuous_const.mul (continuous_neg.pow n)).intervalIntegrable t 0) fun s hs ↦ ?_
          have := h s
          rwa [abs_of_nonpos hs.2] at this
      _ = K * |t| ^ (n + 1) / (n + 1) := by
          rw [intervalIntegral.integral_const_mul,
            show (∫ s in t..(0 : ℝ), (-s) ^ n) = ∫ s in (0 : ℝ)..(-t), s ^ n by
              rw [intervalIntegral.integral_comp_neg (fun s ↦ s ^ n)]; norm_num,
            integral_pow, abs_of_nonpos ht]
          ring

omit [CompleteSpace F] in
/-- **The factorial bound** `‖Iₙ(t)‖ ≤ (C|t|)ⁿ / n!`.

This is the whole reason a linear ODE is solvable on *any* interval with no smallness
hypothesis: the factorial beats the power at every `t`, so the series `∑ₙ Iₙ(t)` converges
however large `C·t` is. A cruder bound `‖Iₙ(t)‖ ≤ (Ct)ⁿ` --- what one gets by estimating the
integrand by its value at the endpoint --- would be useless past `C·t = 1`, which is exactly
the regime where Mathlib's `IsPicardLindelof.mul_max_le` also gives out. The factorial comes
from integrating `sⁿ` rather than bounding it. -/
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
    have hpt : ∀ s : ℝ, ‖(A s).comp (dysonIter A n s)‖ ≤ C ^ (n + 1) / n.factorial * |s| ^ n := by
      intro s
      have h1 : ‖(A s).comp (dysonIter A n s)‖ ≤ ‖A s‖ * ‖dysonIter A n s‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      have h2 : ‖A s‖ * ‖dysonIter A n s‖ ≤ C * ((C * |s|) ^ n / n.factorial) :=
        mul_le_mul (hC s) (ih s) (norm_nonneg _) hC0
      refine h1.trans (h2.trans (le_of_eq ?_))
      rw [mul_pow]; field_simp; ring
    rw [dysonIter_succ]
    refine (norm_integral_le_of_norm_le_pow hcont hpt t).trans (le_of_eq ?_)
    rw [Nat.factorial_succ, mul_pow]
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

/-! ### Dependence on a parameter

`Φ` depends on the family `A`, and the family may itself depend on a parameter.  Uhlenbeck's
trick needs the solution of `∂ₜι = Ric_{g_t}(x)∘ι` to be a *differentiable section*, i.e. `C^k`
in the base point `x`; the regularity of `exp` and the Jacobi equation need the same thing for
the initial condition.  Mathlib has neither (its local flow is built by `choose` behind a
`dite`, so as constructed it is not even continuous in the initial point).

**The Dyson series gives it directly**, because each iterate is an integral of a product and
differentiating under the integral sign is all that is needed.  The derivatives obey the same
recursion with a Leibniz term, and their bound is the factorial bound with one extra power of
`|t|` and a factor `n` --- which is still summable, to `C'|t|e^{C|t|}`. -/

section Parameter

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

set_option maxSynthPendingDepth 3

/-- The derivative in the parameter of the `n`-th Picard--Dyson iterate, defined by the
recursion obtained from `dysonIter`'s by differentiating under the integral sign:
`J₀ = 0` and `Jₙ₊₁(x,t) = ∫₀ᵗ A(x,s)∘Jₙ(x,s) + (A'(x,s)·)∘Iₙ(x,s) ds`.

**The two terms are in Mathlib's order, not the natural one.**  `HasFDerivAt.clm_comp` states
the product rule for `y ↦ (c y).comp (d y)` as `compL (c x) ∘ d' + (compL.flip (d x)) ∘ c'`;
writing the recursion the other way round would cost an `add_comm` at every step of the
induction, and matching it makes the differentiation step `clm_comp` verbatim. -/
noncomputable def dysonIterDeriv (A : H → ℝ → (F →L[ℝ] F))
    (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))) : ℕ → H → ℝ → (H →L[ℝ] (F →L[ℝ] F))
  | 0, _, _ => 0
  | n + 1, x, t => ∫ s in (0 : ℝ)..t,
      (((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s))

omit [CompleteSpace F] in
@[simp] theorem dysonIterDeriv_zero (A : H → ℝ → (F →L[ℝ] F))
    (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))) (x : H) (t : ℝ) : dysonIterDeriv A A' 0 x t = 0 := rfl

omit [CompleteSpace F] in
theorem dysonIterDeriv_succ (A : H → ℝ → (F →L[ℝ] F))
    (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))) (n : ℕ) (x : H) (t : ℝ) :
    dysonIterDeriv A A' (n + 1) x t = ∫ s in (0 : ℝ)..t,
      (((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s)) := rfl

omit [CompleteSpace F] in
/-- The integrand of that recursion, at a fixed parameter, is continuous in `t`. -/
theorem continuous_dysonIterDeriv_integrand {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} (hA : ∀ x, Continuous (A x))
    (hA' : ∀ x, Continuous (A' x)) (n : ℕ) (x : H)
    (ih : Continuous (dysonIterDeriv A A' n x)) :
    Continuous fun s ↦
      (((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s)) := by
  have h1 : Continuous fun s ↦
      ((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s) :=
    (ContinuousLinearMap.compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F)).continuous₂.comp₂
      ((ContinuousLinearMap.compL ℝ F F F).continuous.comp (hA x)) ih
  have h2 : Continuous fun s ↦
      ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s) :=
    (ContinuousLinearMap.compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F)).continuous₂.comp₂
      ((ContinuousLinearMap.compL ℝ F F F).flip.continuous.comp
        (continuous_dysonIter (hA x) n)) (hA' x)
  exact h1.add h2

omit [CompleteSpace F] in
/-- Every `Jₙ` is continuous in `t`. -/
theorem continuous_dysonIterDeriv {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} (hA : ∀ x, Continuous (A x))
    (hA' : ∀ x, Continuous (A' x)) (n : ℕ) (x : H) :
    Continuous (dysonIterDeriv A A' n x) := by
  induction n with
  | zero =>
    show Continuous fun _ : ℝ ↦ (0 : H →L[ℝ] (F →L[ℝ] F))
    exact continuous_const
  | succ n ih =>
    have hcont := continuous_dysonIterDeriv_integrand hA hA' n x ih
    have := intervalIntegral.continuous_primitive (μ := MeasureTheory.volume)
      (f := fun s ↦
        (((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s)))
      (fun a b ↦ hcont.intervalIntegrable a b) 0
    have heq : dysonIterDeriv A A' (n + 1) x = fun b : ℝ ↦ ∫ s in (0 : ℝ)..b,
        (((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s)) := rfl
    rw [heq]
    exact this

omit [CompleteSpace F] in
/-- `‖h ↦ B ∘ (L h)‖ ≤ ‖B‖‖L‖`, proved from the definition rather than through the operator
norm of `compL`. -/
theorem norm_compL_comp_le (B : F →L[ℝ] F) (L : H →L[ℝ] (F →L[ℝ] F)) :
    ‖((ContinuousLinearMap.compL ℝ F F F) B).comp L‖ ≤ ‖B‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  calc ‖(((ContinuousLinearMap.compL ℝ F F F) B).comp L) h‖
      = ‖B.comp (L h)‖ := rfl
    _ ≤ ‖B‖ * ‖L h‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖ * (‖L‖ * ‖h‖) := by gcongr; exact L.le_opNorm h
    _ = ‖B‖ * ‖L‖ * ‖h‖ := by ring

omit [CompleteSpace F] in
/-- `‖h ↦ (L h) ∘ B‖ ≤ ‖L‖‖B‖`. -/
theorem norm_compL_flip_comp_le (B : F →L[ℝ] F) (L : H →L[ℝ] (F →L[ℝ] F)) :
    ‖((ContinuousLinearMap.compL ℝ F F F).flip B).comp L‖ ≤ ‖L‖ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  calc ‖(((ContinuousLinearMap.compL ℝ F F F).flip B).comp L) h‖
      = ‖(L h).comp B‖ := rfl
    _ ≤ ‖L h‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * ‖h‖ * ‖B‖ := by gcongr; exact L.le_opNorm h
    _ = ‖L‖ * ‖B‖ * ‖h‖ := by ring

/-- The bound on `‖Jₙ(x,t)‖`, as a function of `n` and `t` alone.  It has to be uniform in the
parameter to serve as the dominating function when differentiating under the integral sign,
and stated at every `n` (not only at `n+1`) to be usable as that function. -/
noncomputable def dysonDerivBound (C C' : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, t => C' * |t| * (C * |t|) ^ n / n.factorial

theorem continuous_dysonDerivBound (C C' : ℝ) (n : ℕ) : Continuous (dysonDerivBound C C' n) := by
  cases n with
  | zero => exact continuous_const
  | succ n =>
    show Continuous fun t ↦ C' * |t| * (C * |t|) ^ n / n.factorial
    fun_prop

/-- The bound is summable at every `t`, for the same reason the iterate bound is --- it is the
exponential series with one power of `|t|` in front, summing to `C'|t|e^{C|t|}`. -/
theorem summable_dysonDerivBound (C C' : ℝ) (t : ℝ) :
    Summable fun n ↦ dysonDerivBound C C' n t := by
  have h1 : Summable fun n : ℕ ↦ C' * |t| * ((C * |t|) ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial (C * |t|)).mul_left (C' * |t|)
  have h2 : (fun n : ℕ ↦ dysonDerivBound C C' (n + 1) t)
      = fun n : ℕ ↦ C' * |t| * ((C * |t|) ^ n / n.factorial) := by
    funext n
    show C' * |t| * (C * |t|) ^ n / n.factorial = _
    ring
  exact (summable_nat_add_iff 1).mp (by rw [h2]; exact h1)

/-- The bound is monotone in `|t|`, which is what lets a bound on an interval `(-R,R)` be taken
at the endpoint --- the uniform bound termwise differentiation in `t` asks for. -/
theorem dysonDerivBound_le_of_abs_le {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (n : ℕ) {s r : ℝ}
    (h : |s| ≤ |r|) : dysonDerivBound C C' n s ≤ dysonDerivBound C C' n r := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    show C' * |s| * (C * |s|) ^ n / n.factorial ≤ C' * |r| * (C * |r|) ^ n / n.factorial
    have h1 : (C * |s|) ^ n ≤ (C * |r|) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg s]) n
    have h2 : C' * |s| ≤ C' * |r| := by nlinarith [abs_nonneg s]
    have hfac : (0 : ℝ) < n.factorial := by positivity
    gcongr

omit [CompleteSpace F] in
/-- **The factorial bound for the parameter derivatives**: `‖Jₙ₊₁(x,t)‖ ≤ C'|t|(C|t|)ⁿ/n!`.

One extra power of `|t|` against `norm_dysonIter_le`, and one factor of `C` traded for `C'` ---
the Leibniz term contributes `A'` exactly once along the recursion.  The bound is still
summable, to `C'|t|e^{C|t|}`, and that is what makes the *derivative* series converge and so
lets the sum be differentiated termwise.

The induction closes with equality, not slack: the two contributions at step `n+1` are
`C'Cⁿ⁺¹|t|ⁿ⁺²/(n+2)!` and `C'Cⁿ⁺¹|t|ⁿ⁺²/((n+2)·n!)`, and `1/(n+2)! + 1/((n+2)n!) = 1/(n+1)!`
exactly. -/
theorem norm_dysonIterDeriv_succ_le {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (n : ℕ) (x : H) (t : ℝ) :
    ‖dysonIterDeriv A A' (n + 1) x t‖ ≤ C' * |t| * (C * |t|) ^ n / n.factorial := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x 0)
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) (hC' x 0)
  induction n generalizing t with
  | zero =>
    have hcont := continuous_dysonIterDeriv_integrand hA hA' 0 x
      (continuous_dysonIterDeriv hA hA' 0 x)
    have hpt : ∀ s : ℝ,
        ‖(((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' 0 x s)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) 0 s)).comp
              (A' x s))‖ ≤ C' * |s| ^ 0 := by
      intro s
      have hz : dysonIterDeriv A A' 0 x s = 0 := rfl
      rw [hz, ContinuousLinearMap.comp_zero, zero_add]
      refine (norm_compL_flip_comp_le _ _).trans ?_
      have h1 : ‖dysonIter (A x) 0 s‖ ≤ 1 := by
        have : ‖(1 : F →L[ℝ] F)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        simpa [dysonIter_zero] using this
      calc ‖A' x s‖ * ‖dysonIter (A x) 0 s‖ ≤ C' * 1 :=
            mul_le_mul (hC' x s) h1 (norm_nonneg _) hC'0
        _ = C' * |s| ^ 0 := by simp
    rw [dysonIterDeriv_succ]
    refine (norm_integral_le_of_norm_le_pow hcont hpt t).trans (le_of_eq ?_)
    simp
  | succ n ih =>
    have hcont := continuous_dysonIterDeriv_integrand hA hA' (n + 1) x
      (continuous_dysonIterDeriv hA hA' (n + 1) x)
    have hpt : ∀ s : ℝ,
        ‖(((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' (n + 1) x s)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) (n + 1) s)).comp
              (A' x s))‖
        ≤ C' * C ^ (n + 1) * (n + 2) / (n + 1).factorial * |s| ^ (n + 1) := by
      intro s
      have hI : ‖dysonIter (A x) (n + 1) s‖ ≤ (C * |s|) ^ (n + 1) / (n + 1).factorial :=
        norm_dysonIter_le (hA x) (fun r ↦ hC x r) (n + 1) s
      have hJ : ‖dysonIterDeriv A A' (n + 1) x s‖ ≤ C' * |s| * (C * |s|) ^ n / n.factorial :=
        ih s
      have hfac : (0 : ℝ) < n.factorial := by positivity
      have hfac1 : (0 : ℝ) < (n + 1).factorial := by positivity
      refine (norm_add_le _ _).trans ?_
      have e1 : ‖((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp
          (dysonIterDeriv A A' (n + 1) x s)‖
          ≤ C * (C' * |s| * (C * |s|) ^ n / n.factorial) :=
        (norm_compL_comp_le _ _).trans (mul_le_mul (hC x s) hJ (norm_nonneg _) hC0)
      have e2 : ‖((ContinuousLinearMap.compL ℝ F F F).flip
          (dysonIter (A x) (n + 1) s)).comp (A' x s)‖
          ≤ C' * ((C * |s|) ^ (n + 1) / (n + 1).factorial) :=
        (norm_compL_flip_comp_le _ _).trans (mul_le_mul (hC' x s) hI (norm_nonneg _) hC'0)
      refine (add_le_add e1 e2).trans (le_of_eq ?_)
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [dysonIterDeriv_succ]
    refine (norm_integral_le_of_norm_le_pow hcont hpt t).trans (le_of_eq ?_)
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

omit [CompleteSpace F] in
/-- The same bound at every `n`, against `dysonDerivBound`. -/
theorem norm_dysonIterDeriv_le {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (n : ℕ) (x : H) (t : ℝ) :
    ‖dysonIterDeriv A A' n x t‖ ≤ dysonDerivBound C C' n t := by
  cases n with
  | zero => simp [dysonDerivBound]
  | succ n => exact norm_dysonIterDeriv_succ_le hA hA' hC hC' n x t

-- BENCH: dyson-parameter-derivative
omit [CompleteSpace F] in
/-- **Each iterate is differentiable in the parameter**, with derivative `Jₙ`.

The induction is one application of Mathlib's differentiation under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) per step, and the differentiability
hypothesis it asks for at each `s` is exactly `HasFDerivAt.clm_comp` of the inductive
hypothesis against `hderiv` --- which is why `dysonIterDeriv` is written in Mathlib's term
order.

The dominating function is `bnd`, and it has to be uniform in the parameter: that is what the
global bounds `hC`, `hC'` are for.  They are also what lets the set be all of `H`, so no
neighbourhood bookkeeping appears. -/
theorem hasFDerivAt_dysonIter {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C')
    (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x)
    (n : ℕ) (x : H) (t : ℝ) :
    HasFDerivAt (fun y ↦ dysonIter (A y) n t) (dysonIterDeriv A A' n x t) x := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x 0)
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) (hC' x 0)
  induction n generalizing x t with
  | zero =>
    show HasFDerivAt (fun _ : H ↦ (1 : F →L[ℝ] F)) 0 x
    exact hasFDerivAt_const _ _
  | succ n ih =>
    have hFcont : ∀ y : H, Continuous fun s ↦ (A y s).comp (dysonIter (A y) n s) := fun y ↦
      (ContinuousLinearMap.compL ℝ F F F).continuous₂.comp₂ (hA y) (continuous_dysonIter (hA y) n)
    have hF'cont : ∀ y : H, Continuous fun s ↦
        (((ContinuousLinearMap.compL ℝ F F F) (A y s)).comp (dysonIterDeriv A A' n y s)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A y) n s)).comp (A' y s)) :=
      fun y ↦ continuous_dysonIterDeriv_integrand hA hA' n y (continuous_dysonIterDeriv hA hA' n y)
    have hbndcont : Continuous fun s : ℝ ↦
        C * dysonDerivBound C C' n s + C' * ((C * |s|) ^ n / n.factorial) := by
      refine (continuous_const.mul (continuous_dysonDerivBound C C' n)).add ?_
      fun_prop
    have hbound : ∀ (y : H) (r : ℝ),
        ‖(((ContinuousLinearMap.compL ℝ F F F) (A y r)).comp (dysonIterDeriv A A' n y r)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A y) n r)).comp (A' y r))‖
        ≤ C * dysonDerivBound C C' n r + C' * ((C * |r|) ^ n / n.factorial) := by
      intro y r
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (norm_compL_comp_le _ _).trans
          (mul_le_mul (hC y r) (norm_dysonIterDeriv_le hA hA' hC hC' n y r) (norm_nonneg _) hC0)
      · exact (norm_compL_flip_comp_le _ _).trans
          (mul_le_mul (hC' y r) (norm_dysonIter_le (hA y) (fun q ↦ hC y q) n r)
            (norm_nonneg _) hC'0)
    exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := MeasureTheory.volume) (a := 0) (b := t) (s := Set.univ) (x₀ := x)
      (F := fun y s ↦ (A y s).comp (dysonIter (A y) n s))
      (F' := fun y s ↦
        (((ContinuousLinearMap.compL ℝ F F F) (A y s)).comp (dysonIterDeriv A A' n y s)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A y) n s)).comp (A' y s)))
      (bound := fun s ↦ C * dysonDerivBound C C' n s + C' * ((C * |s|) ^ n / n.factorial))
      Filter.univ_mem
      (Filter.Eventually.of_forall fun y ↦ (hFcont y).aestronglyMeasurable)
      ((hFcont x).intervalIntegrable 0 t)
      (hF'cont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r _ y _ ↦ hbound y r)
      (hbndcont.intervalIntegrable 0 t)
      (Filter.Eventually.of_forall fun r _ y _ ↦ (hderiv y r).clm_comp (ih y r))

omit [CompleteSpace F] in
@[simp] theorem dysonIterDeriv_succ_zero (A : H → ℝ → (F →L[ℝ] F))
    (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))) (n : ℕ) (x : H) :
    dysonIterDeriv A A' (n + 1) x 0 = 0 := by
  rw [dysonIterDeriv_succ, intervalIntegral.integral_same]

/-- The derivative series converges at every `t`. -/
theorem summable_dysonIterDeriv {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (x : H) (t : ℝ) :
    Summable fun n ↦ dysonIterDeriv A A' n x t :=
  Summable.of_norm_bounded (summable_dysonDerivBound C C' t)
    (fun n ↦ norm_dysonIterDeriv_le hA hA' hC hC' n x t)

/-- The sum of the differentiated iterates --- the parameter derivative of `Φ`. -/
noncomputable def dysonDerivSum (A : H → ℝ → (F →L[ℝ] F))
    (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))) (x : H) (t : ℝ) : H →L[ℝ] (F →L[ℝ] F) :=
  ∑' n, dysonIterDeriv A A' n x t

omit [CompleteSpace F] in
@[simp] theorem dysonDerivSum_zero (A : H → ℝ → (F →L[ℝ] F))
    (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))) (x : H) : dysonDerivSum A A' x 0 = 0 := by
  have hz : (fun n ↦ dysonIterDeriv A A' n x 0) = fun _ ↦ 0 := by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact dysonIterDeriv_succ_zero A A' n x
  rw [dysonDerivSum, hz, tsum_zero]

-- BENCH: dyson-sum-parameter-derivative
/-- **The fundamental solution is differentiable in the parameter**, with derivative `∑ₙ Jₙ`.

This is what Mathlib does not have in any form --- its local flow is built by `choose` behind a
`dite`, so as constructed it is not even continuous in the initial point --- and what both open
lines of the roadmap are gated on: Uhlenbeck's trivialising family has to be a *differentiable
section*, and the regularity of `exp` runs through the variational equation, which is linear.

Nothing is needed beyond the two series: the iterates are differentiable by
`hasFDerivAt_dysonIter`, their derivatives are dominated by `dysonDerivBound C C' n t`
uniformly in the parameter, and that is summable (to `C'|t|e^{C|t|}`) for the same reason the
solution series is --- the factorial. `hasFDerivAt_tsum` then differentiates termwise. -/
theorem hasFDerivAt_dysonSum {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C')
    (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x)
    (t : ℝ) (x : H) :
    HasFDerivAt (fun y ↦ dysonSum (A y) t) (dysonDerivSum A A' x t) x := by
  exact hasFDerivAt_tsum (summable_dysonDerivBound C C' t)
    (fun n y ↦ hasFDerivAt_dysonIter hA hA' hC hC' hderiv n y t)
    (fun n y ↦ norm_dysonIterDeriv_le hA hA' hC hC' n y t)
    (summable_dysonIter (hA x) (fun r ↦ hC x r) t) x

/-- `Φ` is differentiable in the parameter, and in particular continuous in it. -/
theorem differentiable_dysonSum {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C')
    (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x) (t : ℝ) :
    Differentiable ℝ fun y ↦ dysonSum (A y) t :=
  fun x ↦ (hasFDerivAt_dysonSum hA hA' hC hC' hderiv t x).differentiableAt

/-- Each `Jₙ₊₁` solves its own equation in `t` --- the fundamental theorem of calculus for a
continuous integrand, exactly as for the iterates themselves. -/
theorem hasDerivAt_dysonIterDeriv_succ {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} (hA : ∀ x, Continuous (A x))
    (hA' : ∀ x, Continuous (A' x)) (n : ℕ) (x : H) (t : ℝ) :
    HasDerivAt (dysonIterDeriv A A' (n + 1) x)
      (((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp (dysonIterDeriv A A' n x t)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n t)).comp (A' x t)) t := by
  have hcont := continuous_dysonIterDeriv_integrand hA hA' n x
    (continuous_dysonIterDeriv hA hA' n x)
  have h := (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have heq : dysonIterDeriv A A' (n + 1) x = fun u : ℝ ↦ ∫ s in (0 : ℝ)..u,
      (((ContinuousLinearMap.compL ℝ F F F) (A x s)).comp (dysonIterDeriv A A' n x s)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n s)).comp (A' x s)) := rfl
  rw [heq]
  exact h

-- BENCH: dyson-variational-equation
/-- **The variational equation**: `∂ₜ(D_xΦ) = (D_xA·)∘Φ + A∘(D_xΦ)`.

The parameter derivative solves the *inhomogeneous* linear equation obtained by
differentiating `∂ₜΦ = AΦ` in the parameter --- which is the classical statement that
differentiation in the parameter and in time commute for this equation, proved here rather
than assumed.

**This is what makes the route to `C^k` a checked claim rather than an aspiration.** With it,
the pair `(Φ, D_xΦ)` solves the *linear* block-triangular system
`∂ₜ(u,v) = (A u, (A'·)u + A v)` on `(F →L F) × (H →L (F →L F))`, whose operator is bounded,
continuous in `t`, and one derivative less regular in the parameter than `A`. So `C^k`
dependence follows from the `C¹` theorem applied to the augmented system, by induction on `k`,
with no second-order differentiation under the integral sign anywhere.

Same termwise argument as `hasDerivAt_dysonSum`, one level up: the derivatives of the terms
are `A∘Jₙ + (A'·)∘Iₙ`, dominated on `(-R,R)` by `C·dysonDerivBound C C' n R + C'(CR)ⁿ/n!`
uniformly, which is summable. -/
theorem hasDerivAt_dysonDerivSum {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (x : H) (t : ℝ) :
    HasDerivAt (dysonDerivSum A A' x)
      (((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp (dysonDerivSum A A' x t)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonSum (A x) t)).comp (A' x t)) t := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x 0)
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) (hC' x 0)
  set R : ℝ := |t| + 1 with hR
  have hRpos : 0 < R := by positivity
  have htR : t ∈ Set.Ioo (-R) R := by
    constructor
    · have := neg_abs_le t; simp only [hR]; linarith
    · have := le_abs_self t; simp only [hR]; linarith
  have h0R : (0 : ℝ) ∈ Set.Ioo (-R) R := ⟨by linarith, hRpos⟩
  have hu : Summable fun n : ℕ ↦
      C * dysonDerivBound C C' n R + C' * ((C * R) ^ n / n.factorial) :=
    ((summable_dysonDerivBound C C' R).mul_left C).add
      ((Real.summable_pow_div_factorial (C * R)).mul_left C')
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      HasDerivAt (fun z ↦ dysonIterDeriv A A' (n + 1) x z)
        (((ContinuousLinearMap.compL ℝ F F F) (A x y)).comp (dysonIterDeriv A A' n x y)
          + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n y)).comp (A' x y)) y :=
    fun n y _ ↦ hasDerivAt_dysonIterDeriv_succ hA hA' n x y
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      ‖(((ContinuousLinearMap.compL ℝ F F F) (A x y)).comp (dysonIterDeriv A A' n x y)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n y)).comp (A' x y))‖
      ≤ C * dysonDerivBound C C' n R + C' * ((C * R) ^ n / n.factorial) := by
    intro n y hy
    have hyR : |y| ≤ R := by rw [abs_le]; exact ⟨hy.1.le, hy.2.le⟩
    have habsR : |y| ≤ |R| := by rwa [abs_of_pos hRpos]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_compL_comp_le _ _).trans (mul_le_mul (hC x y)
        ((norm_dysonIterDeriv_le hA hA' hC hC' n x y).trans
          (dysonDerivBound_le_of_abs_le hC0 hC'0 n habsR)) (norm_nonneg _) hC0)
    · refine (norm_compL_flip_comp_le _ _).trans
        (mul_le_mul (hC' x y) ?_ (norm_nonneg _) hC'0)
      refine (norm_dysonIter_le (hA x) (fun q ↦ hC x q) n y).trans ?_
      have h1 : (C * |y|) ^ n ≤ (C * R) ^ n :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg y]) n
      have h2 : (0 : ℝ) < n.factorial := by positivity
      gcongr
  have hg0 : Summable fun n : ℕ ↦ dysonIterDeriv A A' (n + 1) x 0 := by simp
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' h0R hg0 htR
  -- reassemble `D_xΦ = ∑ₙ Jₙ₊₁` (the zeroth term is `0`) and identify the derivative
  have hsplit : dysonDerivSum A A' x = fun z ↦ ∑' n, dysonIterDeriv A A' (n + 1) x z := by
    funext z
    rw [dysonDerivSum, ← (summable_dysonIterDeriv hA hA' hC hC' x z).sum_add_tsum_nat_add 1]
    simp
  -- the two pieces of the derivative are the images of the two series under fixed maps
  have hval : ∑' n, (((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp
        (dysonIterDeriv A A' n x t)
      + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonIter (A x) n t)).comp (A' x t))
      = ((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp (dysonDerivSum A A' x t)
        + ((ContinuousLinearMap.compL ℝ F F F).flip (dysonSum (A x) t)).comp (A' x t) := by
    have hsJ := summable_dysonIterDeriv hA hA' hC hC' x t
    have hsI := summable_dysonIter (hA x) (fun q ↦ hC x q) t
    have h1 : ∑' n, ((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp
        (dysonIterDeriv A A' n x t)
        = ((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp (dysonDerivSum A A' x t) :=
      (((ContinuousLinearMap.compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F))
        ((ContinuousLinearMap.compL ℝ F F F) (A x t))).map_tsum hsJ).symm
    have h2 : ∑' n, ((ContinuousLinearMap.compL ℝ F F F).flip
        (dysonIter (A x) n t)).comp (A' x t)
        = ((ContinuousLinearMap.compL ℝ F F F).flip (dysonSum (A x) t)).comp (A' x t) :=
      ((((ContinuousLinearMap.compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F)).flip (A' x t)).comp
        (ContinuousLinearMap.compL ℝ F F F).flip).map_tsum hsI).symm
    have hs1 : Summable fun n ↦ ((ContinuousLinearMap.compL ℝ F F F) (A x t)).comp
        (dysonIterDeriv A A' n x t) :=
      (((ContinuousLinearMap.compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F))
        ((ContinuousLinearMap.compL ℝ F F F) (A x t))).hasSum hsJ.hasSum).summable
    have hs2 : Summable fun n ↦ ((ContinuousLinearMap.compL ℝ F F F).flip
        (dysonIter (A x) n t)).comp (A' x t) :=
      ((((ContinuousLinearMap.compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F)).flip (A' x t)).comp
        (ContinuousLinearMap.compL ℝ F F F).flip).hasSum hsI.hasSum).summable
    rw [hs1.tsum_add hs2, h1, h2]
  rw [← hval, hsplit]
  exact key

end Parameter

end RicciFlowBlueprint
