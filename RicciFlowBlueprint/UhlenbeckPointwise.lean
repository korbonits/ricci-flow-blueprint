/-
**Uhlenbeck's trick, pointwise.**

Under the Ricci flow `∂ₜg = −2 Ric` the fibre metric on every tensor bundle moves, and the
maximum principle wants it fixed. Uhlenbeck's device is an isometry `ι_t : (V, g₀) → (TM, g_t)`
solving `∂ₜι = Ric♯ ∘ ι`, `ι₀ = id`; pulling curvature back along it puts the evolution on a
bundle whose metric does not move.

**The ODE is pointwise in `x`, and that is what makes it cheap.** `T_xM` does not depend on
`t` --- only its inner product does --- so for each fixed point the equation is a *linear* ODE
in the fixed Banach space `End(T_xM)`, and `LinearODE.lean`'s Dyson series solves it on the
whole interval with no smallness hypothesis and no continuation. **No dependence on the
parameter `x` is needed for the maximum principle**: the touching-point step runs at one time
and uses only the smoothness of the curvature itself, and the time-derivative step runs in the
single fibre over the touching point. So the geometric half of Uhlenbeck's trick that
`LinearODESmooth.lean`'s header left open --- chart-and-bundle transfer of `C^k` parameter
dependence --- is not on the critical path for the pinching estimate.

**Everything here is at one point and stated in `E`**, with the metrics carried as values
`G t : E →L E →L ℝ` (the repo's convention for a varying metric) and the Ricci form as
`B t`. The abstraction is the one the flow supplies at a point: `HasDerivAt G (−2 • B t) t`,
`A t` the `G t`-sharp of `B t`, both forms symmetric. The isometry is then one derivative:
`∂ₜ G(ιv, ιw) = −2B(ιv,ιw) + G(Aιv, ιw) + G(ιv, Aιw) = −2B + B + B = 0`.
-/
import RicciFlowBlueprint.LinearODE

open Set ContinuousLinearMap
open scoped Topology

namespace RicciFlowBlueprint

namespace Uhlenbeck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G B : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {A : ℝ → E →L[ℝ] E} {C T : ℝ}

/-- **The derivative of the pulled-back metric vanishes.** The three terms are the metric's own
derivative `−2B` and the two ODE terms, each of which is `B` by the sharp relation and the
symmetry of `G` and `B`. -/
theorem hasDerivAt_metric_dysonSum (hAc : Continuous A) (hC : ∀ s, ‖A s‖ ≤ C) {t : ℝ}
    (hG : HasDerivAt G ((-2 : ℝ) • B t) t)
    (hGA : ∀ v w, G t (A t v) w = B t v w)
    (hGsymm : ∀ v w, G t v w = G t w v) (hBsymm : ∀ v w, B t v w = B t w v)
    (v w : E) :
    HasDerivAt (fun s ↦ G s (dysonSum A s v) (dysonSum A s w)) 0 t := by
  have hv := hasDerivAt_dysonSum_apply hAc hC v t
  have hw := hasDerivAt_dysonSum_apply hAc hC w t
  have h := (hG.clm_apply hv).clm_apply hw
  refine h.congr_deriv ?_
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hGA, hGsymm (dysonSum A t v) (A t (dysonSum A t w)), hGA,
    hBsymm (dysonSum A t w)]
  ring

/-- **Uhlenbeck's map is an isometry `(E, G 0) → (E, G t)`** on the interval where the flow
equation holds. -/
theorem metric_dysonSum_eq (hAc : Continuous A) (hC : ∀ s, ‖A s‖ ≤ C)
    (hG : ∀ t ∈ Icc 0 T, HasDerivAt G ((-2 : ℝ) • B t) t)
    (hGA : ∀ t ∈ Icc 0 T, ∀ v w, G t (A t v) w = B t v w)
    (hGsymm : ∀ t ∈ Icc 0 T, ∀ v w, G t v w = G t w v)
    (hBsymm : ∀ t ∈ Icc 0 T, ∀ v w, B t v w = B t w v)
    (v w : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    G t (dysonSum A t v) (dysonSum A t w) = G 0 v w := by
  have key : ∀ r ∈ Icc 0 T,
      HasDerivAt (fun s ↦ G s (dysonSum A s v) (dysonSum A s w)) 0 r := fun r hr ↦
    hasDerivAt_metric_dysonSum hAc hC (hG r hr) (hGA r hr) (hGsymm r hr) (hBsymm r hr) v w
  have h := constant_of_has_deriv_right_zero
    (f := fun s ↦ G s (dysonSum A s v) (dysonSum A s w))
    (fun r hr ↦ (key r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (key r (Ico_subset_Icc_self hr)).hasDerivWithinAt) t ht
  simpa using h

/-- **The inverse pulls `G t` back to `G 0`.** The form the conjugation argument uses: for an
endomorphism `R` of `(E, G t)`, `ι⁻¹ R ι` is the same operator seen in `(E, G 0)`. -/
theorem metric_dysonEquiv_symm_eq (hAc : Continuous A) (hC : ∀ s, ‖A s‖ ≤ C)
    (hG : ∀ t ∈ Icc 0 T, HasDerivAt G ((-2 : ℝ) • B t) t)
    (hGA : ∀ t ∈ Icc 0 T, ∀ v w, G t (A t v) w = B t v w)
    (hGsymm : ∀ t ∈ Icc 0 T, ∀ v w, G t v w = G t w v)
    (hBsymm : ∀ t ∈ Icc 0 T, ∀ v w, B t v w = B t w v)
    (v w : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    G 0 ((dysonEquiv hAc hC t).symm v) ((dysonEquiv hAc hC t).symm w) = G t v w := by
  have h := metric_dysonSum_eq hAc hC hG hGA hGsymm hBsymm
    ((dysonEquiv hAc hC t).symm v) ((dysonEquiv hAc hC t).symm w) ht
  rw [← h]
  have hv : dysonSum A t ((dysonEquiv hAc hC t).symm v) = v := by
    rw [← dysonEquiv_apply hAc hC t]; exact (dysonEquiv hAc hC t).apply_symm_apply v
  have hw : dysonSum A t ((dysonEquiv hAc hC t).symm w) = w := by
    rw [← dysonEquiv_apply hAc hC t]; exact (dysonEquiv hAc hC t).apply_symm_apply w
  rw [hv, hw]

section Inverse

/-- **The derivative of the inverse of an invertible family of operators**:
`∂ₜ Φ⁻¹ = −Φ⁻¹ Φ' Φ⁻¹`. Differentiability is `contDiffAt_map_inverse`; the value is read off
by differentiating `Φ ∘ Φ⁻¹ = 1`, the pattern of `MetricTrace.lean`'s
`hasDerivAt_inverse_innerE` with the codomain `E` rather than `E →L ℝ`. -/
theorem hasDerivAt_inverse_of_isInvertible {Φ : ℝ → E →L[ℝ] E} {Φ' : E →L[ℝ] E} {t : ℝ}
    (hΦ : HasDerivAt Φ Φ' t) (hinv : ∀ s, (Φ s).IsInvertible) :
    HasDerivAt (fun s ↦ (Φ s).inverse) (-((Φ t).inverse ∘L Φ' ∘L (Φ t).inverse)) t := by
  obtain ⟨e, he⟩ := hinv t
  have hdiff : HasFDerivAt ContinuousLinearMap.inverse
      (fderiv ℝ ContinuousLinearMap.inverse (Φ t)) (Φ t) := by
    have h := (contDiffAt_map_inverse (n := 1) e).differentiableAt (by norm_num)
    rw [he] at h
    exact h.hasFDerivAt
  have hD : HasDerivAt (fun s ↦ (Φ s).inverse)
      (fderiv ℝ ContinuousLinearMap.inverse (Φ t) Φ') t :=
    HasFDerivAt.comp_hasDerivAt (f := Φ) (x := t) hdiff hΦ
  set D := fderiv ℝ ContinuousLinearMap.inverse (Φ t) Φ' with hDdef
  have hid : HasDerivAt (fun s ↦ Φ s ∘L (Φ s).inverse)
      (Φ' ∘L (Φ t).inverse + Φ t ∘L D) t := hΦ.clm_comp hD
  have hconst : (fun s ↦ Φ s ∘L (Φ s).inverse) = fun _ ↦ ContinuousLinearMap.id ℝ E := by
    funext s; exact (hinv s).self_comp_inverse
  rw [hconst] at hid
  have h0 := hid.unique (hasDerivAt_const t _)
  have h1 := congrArg (fun L ↦ (Φ t).inverse ∘L L) h0
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_zero] at h1
  have h2 : (Φ t).inverse ∘L (Φ t ∘L D) = D := by
    rw [← ContinuousLinearMap.comp_assoc, (hinv t).inverse_comp_self,
      ContinuousLinearMap.id_comp]
  rw [h2] at h1
  have hDeq : D = -((Φ t).inverse ∘L Φ' ∘L (Φ t).inverse) := eq_neg_of_add_eq_zero_right h1
  rw [← hDeq]
  exact hD

end Inverse

/-- Uhlenbeck's map is invertible at every time --- the Dyson propagator is. -/
theorem isInvertible_dysonSum (hAc : Continuous A) (hC : ∀ s, ‖A s‖ ≤ C) (t : ℝ) :
    (dysonSum A t).IsInvertible :=
  ⟨dysonEquiv hAc hC t, by ext v; simp⟩

/-- **The conjugated operator evolves by the conjugated derivative plus a commutator**:
`∂ₜ(ι⁻¹ R ι) = ι⁻¹ (Ṙ + R A − A R) ι`. The commutator is what Uhlenbeck's frame costs in
general; for the dimension-three curvature operator `R = scal·1 − 2 Ric♯` it vanishes, since
`A = Ric♯`. -/
theorem hasDerivAt_conj (hAc : Continuous A) (hC : ∀ s, ‖A s‖ ≤ C)
    {R : ℝ → E →L[ℝ] E} {R' : E →L[ℝ] E} {t : ℝ} (hR : HasDerivAt R R' t) :
    HasDerivAt (fun s ↦ (dysonSum A s).inverse ∘L R s ∘L dysonSum A s)
      ((dysonSum A t).inverse ∘L (R' + R t ∘L A t - A t ∘L R t) ∘L dysonSum A t) t := by
  have hι := hasDerivAt_dysonSum hAc hC t
  have hιinv := hasDerivAt_inverse_of_isInvertible hι (isInvertible_dysonSum hAc hC)
  have h := hιinv.clm_comp (hR.clm_comp hι)
  refine h.congr_deriv ?_
  have hid' : ∀ u, dysonSum A t ((dysonSum A t).inverse u) = u := fun u ↦ by
    have := congrArg (fun L ↦ L u) (isInvertible_dysonSum hAc hC t).self_comp_inverse
    simpa using this
  ext v
  simp only [add_apply, neg_apply, comp_apply, sub_apply, hid', map_add, map_sub]
  abel

/-- **Self-adjointness transfers along Uhlenbeck's map**: if `R` is `G t`-symmetric then
`ι⁻¹ R ι` is `G 0`-symmetric. The whole point of the frame: the pulled-back curvature lives in
a space whose inner product does not move. -/
theorem metric_conj_symm (hAc : Continuous A) (hC : ∀ s, ‖A s‖ ≤ C)
    (hG : ∀ t ∈ Icc 0 T, HasDerivAt G ((-2 : ℝ) • B t) t)
    (hGA : ∀ t ∈ Icc 0 T, ∀ v w, G t (A t v) w = B t v w)
    (hGsymm : ∀ t ∈ Icc 0 T, ∀ v w, G t v w = G t w v)
    (hBsymm : ∀ t ∈ Icc 0 T, ∀ v w, B t v w = B t w v)
    {t : ℝ} (ht : t ∈ Icc 0 T) {R : E →L[ℝ] E} (hR : ∀ v w, G t (R v) w = G t v (R w))
    (v w : E) :
    G 0 (((dysonSum A t).inverse ∘L R ∘L dysonSum A t) v) w
      = G 0 v (((dysonSum A t).inverse ∘L R ∘L dysonSum A t) w) := by
  have hinv : (dysonSum A t).inverse = ((dysonEquiv hAc hC t).symm : E →L[ℝ] E) := by
    rw [show dysonSum A t = ((dysonEquiv hAc hC t : E ≃L[ℝ] E) : E →L[ℝ] E) by ext; simp,
      ContinuousLinearMap.inverse_equiv]
  have hback : ∀ a b, G 0 ((dysonEquiv hAc hC t).symm a) ((dysonEquiv hAc hC t).symm b)
      = G t a b := fun a b ↦ metric_dysonEquiv_symm_eq hAc hC hG hGA hGsymm hBsymm a b ht
  have hself : ∀ u, (dysonEquiv hAc hC t).symm (dysonSum A t u) = u := fun u ↦ by
    rw [← dysonEquiv_apply hAc hC t]; exact (dysonEquiv hAc hC t).symm_apply_apply u
  simp only [ContinuousLinearMap.comp_apply, hinv, ContinuousLinearEquiv.coe_coe]
  calc G 0 ((dysonEquiv hAc hC t).symm (R (dysonSum A t v))) w
      = G 0 ((dysonEquiv hAc hC t).symm (R (dysonSum A t v)))
          ((dysonEquiv hAc hC t).symm (dysonSum A t w)) := by rw [hself]
    _ = G t (R (dysonSum A t v)) (dysonSum A t w) := hback _ _
    _ = G t (dysonSum A t v) (R (dysonSum A t w)) := hR _ _
    _ = G 0 ((dysonEquiv hAc hC t).symm (dysonSum A t v))
          ((dysonEquiv hAc hC t).symm (R (dysonSum A t w))) := (hback _ _).symm
    _ = G 0 v ((dysonEquiv hAc hC t).symm (R (dysonSum A t w))) := by rw [hself]

end Uhlenbeck

end RicciFlowBlueprint
