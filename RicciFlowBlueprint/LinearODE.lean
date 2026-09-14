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
theorem norm_dysonIter_le {A : ℝ → (F →L[ℝ] F)} {C : ℝ} (hA : Continuous A)
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

end RicciFlowBlueprint
