/-
**Hamilton's sharp lower bound on the scalar curvature under the Ricci flow.**

`ScalarPreservation.lean` proves that a lower bound `R ≥ C` is preserved, using only that the
reaction term `2|Ric|²` is nonnegative. Keeping the reaction term instead of discarding it
gives the sharp estimate: by Cauchy--Schwarz `2|Ric|² ≥ (2/n)R²`, so `R` obeys
`∂ₜ R ≥ Δ R + (2/n)R²`, whose ODE `φ' = (2/n)φ²` pushes a negative bound up to zero like
`C/(1 - (2/n)Ct)`.

**The obstruction is that `r ↦ (2/n)r²` is not Lipschitz**, while the maximum principle asks
for a Lipschitz reaction. The fix costs nothing: truncate it to `reactionTrunc`, which is
Lipschitz, still bounded above by `(2/n)r²` *everywhere* (so the hypothesis at spatial minima
is unaffected), and still exactly `(2/n)r²` along the comparison solution, because the
truncation level is chosen to be `-C` and the comparison solution never leaves `[C, 0)`.

**So no bound on `R` is assumed.** An earlier plan truncated at a bound for `R` itself, read
off compactness; that is unnecessary, since `(max (-A) (min r A))² ≤ r²` for every `r`.
-/
import RicciFlowBlueprint.ScalarPreservation

open Set Bundle CovariantDerivative
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

/-! ### The comparison ODE

Everything in this section is about real functions; no geometry appears. -/

/-- The reaction term `r ↦ (2/n) r²` truncated at level `A`. Lipschitz, unlike the square
itself, and bounded above by `(2/n) r²` for **every** `r`, which is what lets it be substituted
into the maximum principle's hypothesis at a spatial minimum without assuming anything about
the range of `R`. -/
noncomputable def reactionTrunc (n A r : ℝ) : ℝ := (2 / n) * (max (-A) (min r A)) ^ 2

theorem reactionTrunc_eq_of_mem {n A r : ℝ} (hl : -A ≤ r) (hr : r ≤ A) :
    reactionTrunc n A r = (2 / n) * r ^ 2 := by
  rw [reactionTrunc, min_eq_left hr, max_eq_right hl]

/-- The truncation never leaves `[-A, A]`. -/
theorem abs_clamp_le {A r : ℝ} (hA : 0 ≤ A) : |max (-A) (min r A)| ≤ A := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- **Truncation only moves `|r|` down.** This is what makes the truncated reaction term a
lower bound for the true one at *every* value, so that no bound on `R` has to be assumed. -/
theorem abs_clamp_le_abs {A r : ℝ} (hA : 0 ≤ A) : |max (-A) (min r A)| ≤ |r| := by
  rw [abs_le]
  constructor
  · exact le_trans (le_min (neg_abs_le r) (by linarith [abs_nonneg r])) (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg r]) ((min_le_left _ _).trans (le_abs_self r))

/-- `reactionTrunc n A r ≤ (2/n) r²` for **every** `r`. -/
theorem reactionTrunc_le {n A r : ℝ} (hn : 0 < n) (hA : 0 ≤ A) :
    reactionTrunc n A r ≤ (2 / n) * r ^ 2 := by
  have h1 := abs_clamp_le_abs (A := A) (r := r) hA
  have h2 : |max (-A) (min r A)| ^ 2 ≤ |r| ^ 2 := by
    nlinarith [abs_nonneg (max (-A) (min r A))]
  have h : (max (-A) (min r A)) ^ 2 ≤ r ^ 2 := by simpa [sq_abs] using h2
  have hpos : (0 : ℝ) < 2 / n := by positivity
  exact mul_le_mul_of_nonneg_left h hpos.le

/-- **The truncated reaction term is Lipschitz**, with constant `(4/n)A` --- which is the whole
reason for truncating. The square itself is not, and `MaximumPrinciple.le_of_deriv_ge_at_min`
asks for a Lipschitz reaction. -/
theorem lipschitzWith_reactionTrunc {n A : ℝ} (hn : 0 < n) (hA : 0 ≤ A) :
    LipschitzWith (((4 / n) * A).toNNReal) (reactionTrunc n A) := by
  have hclampL : LipschitzWith 1 (fun r : ℝ ↦ max (-A) (min r A)) :=
    (LipschitzWith.id.min_const A).const_max (-A)
  refine LipschitzWith.of_dist_le_mul fun r s ↦ ?_
  have hcl : |max (-A) (min r A) - max (-A) (min s A)| ≤ |r - s| := by
    have := hclampL.dist_le_mul r s
    simpa [Real.dist_eq] using this
  have hbr := abs_clamp_le (A := A) (r := r) hA
  have hbs := abs_clamp_le (A := A) (r := s) hA
  have hpos : (0 : ℝ) < 2 / n := by positivity
  have hK : ((((4 / n) * A).toNNReal) : ℝ) = (4 / n) * A :=
    Real.coe_toNNReal _ (by positivity)
  have hsum : |max (-A) (min r A) + max (-A) (min s A)| ≤ 2 * A := by
    rw [abs_le] at hbr hbs ⊢
    exact ⟨by linarith [hbr.1, hbs.1], by linarith [hbr.2, hbs.2]⟩
  have hmain : |max (-A) (min r A) - max (-A) (min s A)|
        * |max (-A) (min r A) + max (-A) (min s A)| ≤ (2 * A) * |r - s| := by
    have := mul_le_mul hcl hsum (abs_nonneg _) (abs_nonneg _)
    linarith [this]
  rw [Real.dist_eq, Real.dist_eq, hK, reactionTrunc, reactionTrunc]
  have hfac : (2 / n) * (max (-A) (min r A)) ^ 2 - (2 / n) * (max (-A) (min s A)) ^ 2
      = (2 / n) * ((max (-A) (min r A) - max (-A) (min s A))
          * (max (-A) (min r A) + max (-A) (min s A))) := by ring
  rw [hfac, abs_mul, abs_of_pos hpos, abs_mul]
  calc (2 / n) * (|max (-A) (min r A) - max (-A) (min s A)|
          * |max (-A) (min r A) + max (-A) (min s A)|)
      ≤ (2 / n) * ((2 * A) * |r - s|) := mul_le_mul_of_nonneg_left hmain hpos.le
    _ = (4 / n) * A * |r - s| := by ring

/-! ### The comparison solution

`φ(t) = C/(1 - (2/n)Ct)` solves `φ' = (2/n)φ²` with `φ(0) = C`, and for `C < 0` it increases
from `C` towards `0` --- so it never leaves `[C, 0]`, and the truncation at level `-C` is
invisible to it. -/

/-- Hamilton's comparison solution `C/(1 - (2/n)Ct)`. -/
noncomputable def hamiltonComparison (n C t : ℝ) : ℝ := C / (1 - (2 / n) * C * t)

theorem hamiltonComparison_zero (n C : ℝ) : hamiltonComparison n C 0 = C := by
  simp [hamiltonComparison]

/-- The denominator is at least `1` for `t ≥ 0` and `C < 0`, so nothing degenerates. -/
theorem one_le_hamiltonDenom {n C t : ℝ} (hn : 0 < n) (hC : C < 0) (ht : 0 ≤ t) :
    1 ≤ 1 - (2 / n) * C * t := by
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt (by positivity : (0 : ℝ) < 2 / n))
    (by linarith : (0 : ℝ) ≤ -C)) ht]

/-- The comparison solution stays in `[C, 0]`. -/
theorem hamiltonComparison_mem {n C t : ℝ} (hn : 0 < n) (hC : C < 0) (ht : 0 ≤ t) :
    C ≤ hamiltonComparison n C t ∧ hamiltonComparison n C t ≤ 0 := by
  have hd := one_le_hamiltonDenom hn hC ht
  have hd0 : (0 : ℝ) < 1 - (2 / n) * C * t := by linarith
  constructor
  · rw [hamiltonComparison, le_div_iff₀ hd0]
    nlinarith
  · rw [hamiltonComparison, div_nonpos_iff]
    exact Or.inr ⟨hC.le, hd0.le⟩

/-- **The comparison solution solves the truncated ODE.** The truncation at level `-C` is
invisible to it, because it never leaves `[C, 0]`. -/
theorem hasDerivAt_hamiltonComparison {n C t : ℝ} (hn : 0 < n) (hC : C < 0) (ht : 0 ≤ t) :
    HasDerivAt (hamiltonComparison n C)
      (reactionTrunc n (-C) (hamiltonComparison n C t)) t := by
  have hd := one_le_hamiltonDenom hn hC ht
  have hd0 : (1 : ℝ) - (2 / n) * C * t ≠ 0 := by linarith
  have hD : HasDerivAt (fun u : ℝ ↦ 1 - (2 / n) * C * u) (-((2 / n) * C * 1)) t :=
    ((hasDerivAt_id t).const_mul ((2 / n) * C)).const_sub 1
  have hq := (hasDerivAt_const t C).div hD hd0
  have hmem := hamiltonComparison_mem hn hC ht
  rw [reactionTrunc_eq_of_mem (by linarith [hmem.1]) (by linarith [hmem.2])]
  refine hq.congr_deriv ?_
  rw [hamiltonComparison]
  field_simp
  ring

/-! ### The estimate on the manifold -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [CompactSpace M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] [I.Boundaryless] [CompactSpace M] in
-- BENCH: scal-sq-le-ricci-sq
/-- **`R² ≤ n |Ric|²_g`** --- Cauchy–Schwarz for the metric trace
(`sq_metricTraceE_le_card_mul`) at `B = Ric`, with `Ric` symmetric and `n = dim M`. -/
theorem sq_scalarCurvatureOfMetricAt_le
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M) :
    (scalarCurvatureOfMetricAt g x) ^ 2
      ≤ (Module.finrank ℝ E : ℝ)
          * metricTraceE g x (ricciFormOfMetric g x ∘L sharpE g x (ricciFormOfMetric g x)) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [scalarCurvatureOfMetricAt_eq_metricTraceE g x]
  have h := sq_metricTraceE_le_card_mul (I := I) (M := M) g x (ricciFormOfMetric g x)
    (ricciFormOfMetric_symm g x) (stdOrthonormalBasis ℝ (TangentSpace I x))
  have hfr : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  simpa [hfr] using h

-- BENCH: hamilton-scalar-lower-bound
/-- **Hamilton's lower bound on the scalar curvature under the Ricci flow.** If `R ≥ C` at
time `0` with `C < 0`, then

  `R(t, ·) ≥ C / (1 - (2/n) C t)`   for every `t ∈ [0, T]`,

which increases from `C` towards `0`. This is `ScalarPreservation.lean`'s statement with the
reaction term kept rather than discarded: Cauchy–Schwarz turns `2|Ric|²` into `≥ (2/n)R²`, and
the comparison ODE `φ' = (2/n)φ²` is what pushes the bound up.

**No bound on `R` is assumed**, even though the maximum principle needs a Lipschitz reaction
and `r ↦ (2/n)r²` is not one. The truncation `reactionTrunc n (-C)` is Lipschitz, lies below
`(2/n)r²` at *every* `r` (so the hypothesis at spatial minima survives), and agrees with it
along the comparison solution, which never leaves `[C, 0]`.

As with `ScalarPreservation.lean`, the Laplacian and the norm move with `t` and the maximum
principle does not mind: the `letI` for the metric lives inside the proof, one time at a
time. -/
theorem scalarCurvatureOfMetricAt_ge_hamiltonComparison
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
    {R' : ℝ → M → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hC : C < 0)
    (hn : 0 < (Module.finrank ℝ E : ℝ))
    (hcont : Continuous fun p : ℝ × M ↦ scalarCurvatureOfMetricAt (g p.1) p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivAt (fun s ↦ scalarCurvatureOfMetricAt (g s) x) (R' t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x,
      ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x)
    (heq : ∀ t ∈ Icc 0 T, ∀ x,
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      R' t x = (leviCivitaOfMetric (g t)).laplacianFun
          (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x
        + 2 * metricTraceE (g t) x
            (ricciFormOfMetric (g t) x ∘L sharpE (g t) x (ricciFormOfMetric (g t) x)))
    (h0 : ∀ x, C ≤ scalarCurvatureOfMetricAt (g 0) x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      hamiltonComparison (Module.finrank ℝ E) C t ≤ scalarCurvatureOfMetricAt (g t) x := by
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hndef
  have hCA : (0 : ℝ) ≤ -C := by linarith
  refine MaximumPrinciple.le_of_deriv_ge_at_min (F := reactionTrunc n (-C))
    (φ := hamiltonComparison n C) hT hcont hut
    (lipschitzWith_reactionTrunc hn hCA) ?_
    (fun t ht ↦ hasDerivAt_hamiltonComparison hn hC ht.1)
    (fun x ↦ by rw [hamiltonComparison_zero]; exact h0 x)
  intro t ht x₀ hmin
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  have hlap : 0 ≤ (leviCivitaOfMetric (g t)).laplacianFun
      (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x₀ :=
    laplacianFun_nonneg_of_isLocalMin _ (hreg t ht x₀) (Filter.Eventually.of_forall hmin)
  have hcs := sq_scalarCurvatureOfMetricAt_le (g t) x₀
  have htr := reactionTrunc_le (n := n) (A := -C)
    (r := scalarCurvatureOfMetricAt (g t) x₀) hn hCA
  -- `(2/n) R² ≤ 2 |Ric|²` is Cauchy–Schwarz rescaled
  have h1 : (2 / n) * (scalarCurvatureOfMetricAt (g t) x₀) ^ 2
      ≤ (2 / n) * (n * metricTraceE (g t) x₀
          (ricciFormOfMetric (g t) x₀ ∘L sharpE (g t) x₀ (ricciFormOfMetric (g t) x₀))) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  have h2 : (2 / n) * (n * metricTraceE (g t) x₀
        (ricciFormOfMetric (g t) x₀ ∘L sharpE (g t) x₀ (ricciFormOfMetric (g t) x₀)))
      = 2 * metricTraceE (g t) x₀
          (ricciFormOfMetric (g t) x₀ ∘L sharpE (g t) x₀ (ricciFormOfMetric (g t) x₀)) := by
    field_simp
  rw [heq t ht x₀]
  linarith

-- BENCH: hamilton-scalar-lower-bound-flow
/-- **Hamilton's lower bound**, with the evolution equation as the single hypothesis --- and
that hypothesis is exactly `ScalarFlow.lean`'s conclusion, via
`hasDerivAt_scalarFlowRHS_of_hasDerivAt_scalarCurvatureAt`. -/
theorem scalarCurvatureOfMetricAt_ge_hamiltonComparison_of_scalarFlowRHS
    {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
    {T C : ℝ} (hT : 0 ≤ T) (hC : C < 0)
    (hn : 0 < (Module.finrank ℝ E : ℝ))
    (hcont : Continuous fun p : ℝ × M ↦ scalarCurvatureOfMetricAt (g p.1) p.2)
    (hev : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivAt (fun s ↦ scalarCurvatureOfMetricAt (g s) x) (scalarFlowRHS g t x) t)
    (hreg : ∀ t ∈ Icc 0 T, ∀ x,
      ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ scalarCurvatureOfMetricAt (g t) y) x)
    (h0 : ∀ x, C ≤ scalarCurvatureOfMetricAt (g 0) x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      hamiltonComparison (Module.finrank ℝ E) C t ≤ scalarCurvatureOfMetricAt (g t) x :=
  scalarCurvatureOfMetricAt_ge_hamiltonComparison hT hC hn hcont hev hreg
    (fun _ _ _ ↦ rfl) h0

end RicciFlowBlueprint
