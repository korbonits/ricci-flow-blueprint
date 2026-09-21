/-
**The Hilbert–Schmidt inner product on `End(W)`**, the fibre metric `End(TM)` needs.

`HomBundle.lean` gives `End(TM)` a connection. To run a maximum principle on a section of it
the *fibres* must also carry an inner product, and Mathlib supplies none: there is no
`InnerProductSpace` instance on `→L`, and the only `IsContMDiffRiemannianBundle` instances in
Mathlib are for the trivial bundle and for lowering the smoothness index. So the
Hilbert–Schmidt form has to be built.

This file is the **pointwise algebra**: the form itself, its symmetry, its definiteness, and
the norm bound that makes its unit set bounded. Everything is stated for a bare
finite-dimensional inner product space `W`, so nothing here knows about manifolds.

Built through `ContinuousLinearMap.bilinearComp`, so bilinearity and continuity hold **by
construction** — no `mk₂`, no boundedness estimate. Frame independence is then free, because
`(v,w) ↦ ⟪A v, B w⟫` is a genuine continuous bilinear form and
`OrthonormalBasis.sum_apply_self_eq` traces it.
-/
import RicciFlowBlueprint.HomBundle

open scoped RealInnerProductSpace

namespace RicciFlowBlueprint

section Pointwise

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The Hilbert–Schmidt form** `⟨A,B⟩ = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` on `End(W)`, as a continuous
bilinear form. `bilinearComp` supplies bilinearity and continuity, so there is nothing to
prove about either. -/
noncomputable def hsForm (b : OrthonormalBasis ι ℝ W) :
    (W →L[ℝ] W) →L[ℝ] (W →L[ℝ] W) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ).bilinearComp (ContinuousLinearMap.apply ℝ W (b i))
    (ContinuousLinearMap.apply ℝ W (b i))

omit [FiniteDimensional ℝ W] in
theorem hsForm_apply (b : OrthonormalBasis ι ℝ W) (A B : W →L[ℝ] W) :
    hsForm b A B = ∑ i, ⟪A (b i), B (b i)⟫ := by
  simp only [hsForm, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply]

omit [FiniteDimensional ℝ W] in
/-- **Frame independence.** `(v,w) ↦ ⟪A v, B w⟫` is a continuous bilinear form, so its trace
over an orthonormal basis does not depend on the basis. -/
theorem hsForm_congr (b : OrthonormalBasis ι ℝ W) (c : OrthonormalBasis κ ℝ W)
    (A B : W →L[ℝ] W) : hsForm b A B = hsForm c A B := by
  rw [hsForm_apply, hsForm_apply]
  exact OrthonormalBasis.sum_apply_self_eq b c ((((innerSL ℝ).comp A).flip.comp B).flip)

omit [FiniteDimensional ℝ W] in
theorem hsForm_symm (b : OrthonormalBasis ι ℝ W) (A B : W →L[ℝ] W) :
    hsForm b A B = hsForm b B A := by
  rw [hsForm_apply, hsForm_apply]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

omit [FiniteDimensional ℝ W] in
theorem hsForm_self_nonneg (b : OrthonormalBasis ι ℝ W) (A : W →L[ℝ] W) :
    0 ≤ hsForm b A A := by
  rw [hsForm_apply]
  exact Finset.sum_nonneg fun i _ ↦ real_inner_self_nonneg

omit [FiniteDimensional ℝ W] in
/-- Each `‖A eᵢ‖²` is one summand of a sum of nonnegative terms. -/
theorem sq_norm_apply_le_hsForm (b : OrthonormalBasis ι ℝ W) (A : W →L[ℝ] W) (i : ι) :
    ‖A (b i)‖ ^ 2 ≤ hsForm b A A := by
  have hsum : hsForm b A A = ∑ j, ‖A (b j)‖ ^ 2 := by
    rw [hsForm_apply]
    exact Finset.sum_congr rfl fun j _ ↦ real_inner_self_eq_norm_sq _
  rw [hsum]
  exact Finset.single_le_sum (f := fun j ↦ ‖A (b j)‖ ^ 2) (fun j _ ↦ sq_nonneg _)
    (Finset.mem_univ i)

omit [FiniteDimensional ℝ W] in
/-- `‖A‖ ≤ ∑ᵢ ‖A eᵢ‖`: expand `v` in the basis and use `|⟪eᵢ,v⟫| ≤ ‖v‖`. -/
theorem opNorm_le_sum_norm_apply (b : OrthonormalBasis ι ℝ W) (A : W →L[ℝ] W) :
    ‖A‖ ≤ ∑ i, ‖A (b i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ ↦ norm_nonneg _) ?_
  intro v
  have hv : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have hAv : A v = ∑ i, b.repr v i • A (b i) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
  calc ‖A v‖ = ‖∑ i, b.repr v i • A (b i)‖ := by rw [hAv]
    _ ≤ ∑ i, ‖b.repr v i • A (b i)‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr v i| * ‖A (b i)‖ := by
        exact Finset.sum_congr rfl fun i _ ↦ by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖A (b i)‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hb1 : |b.repr v i| ≤ ‖v‖ := by
          rw [b.repr_apply_apply]
          calc |⟪b i, v⟫| ≤ ‖b i‖ * ‖v‖ := abs_real_inner_le_norm _ _
            _ = ‖v‖ := by rw [b.norm_eq_one i, one_mul]
        nlinarith [norm_nonneg (A (b i)), abs_nonneg (b.repr v i)]
    _ = (∑ i, ‖A (b i)‖) * ‖v‖ := (Finset.sum_mul _ _ _).symm

omit [FiniteDimensional ℝ W] in
/-- **The unit set of the Hilbert–Schmidt form is bounded**, which is the
`isVonNBounded` field of a `RiemannianMetric`. Each `‖A eᵢ‖ < 1` there, so
`‖A‖ < Fintype.card ι` by the bound above. -/
theorem isVonNBounded_hsForm_lt_one (b : OrthonormalBasis ι ℝ W) :
    Bornology.IsVonNBounded ℝ {A : W →L[ℝ] W | hsForm b A A < 1} := by
  refine (NormedSpace.isVonNBounded_iff ℝ).2 ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Fintype.card ι, fun A hA ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hA
  have hnorm : ∀ i, ‖A (b i)‖ ≤ 1 := by
    intro i
    have h := sq_norm_apply_le_hsForm b A i
    nlinarith [norm_nonneg (A (b i)), h, hA]
  have hsum : ∑ i, ‖A (b i)‖ ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i, ‖A (b i)‖ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hnorm i
      _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_trans (opNorm_le_sum_norm_apply b A) hsum

omit [FiniteDimensional ℝ W] in
/-- **Definiteness**: `⟨A,A⟩ = 0` forces `A = 0`, since every `A eᵢ` vanishes. -/
theorem hsForm_self_eq_zero (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W}
    (h : hsForm b A A = 0) : A = 0 := by
  have hzero : ∀ i, A (b i) = 0 := by
    intro i
    have h1 := sq_norm_apply_le_hsForm b A i
    rw [h] at h1
    have : ‖A (b i)‖ = 0 := by nlinarith [norm_nonneg (A (b i))]
    exact norm_eq_zero.mp this
  have hle : ‖A‖ ≤ 0 := by
    refine le_trans (opNorm_le_sum_norm_apply b A) ?_
    simp [hzero]
  exact norm_le_zero_iff.mp hle

omit [FiniteDimensional ℝ W] in
theorem hsForm_self_pos (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W} (hA : A ≠ 0) :
    0 < hsForm b A A :=
  lt_of_le_of_ne (hsForm_self_nonneg b A) fun h ↦ hA (hsForm_self_eq_zero b h.symm)

end Pointwise

end RicciFlowBlueprint
