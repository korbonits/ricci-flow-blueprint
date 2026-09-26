/-
**Hamilton–Ivey pinching is preserved by the Ricci flow on a closed three-manifold.**

The assembly. The maximum principle runs on `u(t,x) = mat_{e(t,x)} Rm₃(g_t)(x)`, the matrix of
the curvature operator in the Uhlenbeck frame `e(t,x) = ι(t,x) e₀(x)`: a point of the fixed
Euclidean space `Mat3`, so no bundle metric is ever an instance while another is in scope.

* `∂ₜu = mat(∂ₜRm₃)`, the Uhlenbeck commutator vanishing (`hasDerivAt_metric_dysonSum_conj`);
* `∂ₜRm₃ = ΔRm₃ + Q(Rm₃)` (`exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt`) and
  `mat(Q(Rm₃)) = Q_mat(u)` (`toMat_hamiltonReaction`);
* at a spatial maximum of the distance to `K_mat`, `⟪u − p, mat ΔRm₃⟫ ≤ 0`
  (`inner_toMat_laplacian_curvatureOperator_nonpos`), the frame being invisible;
* `Q_mat` satisfies Nagumo's condition on `K_mat` and is Lipschitz on balls, `0 ∈ K_mat`.

This file first packages the touching step **at one time**, for any family of orthonormal
frames, under the single `letI` of `g_t`.
-/
import RicciFlowBlueprint.CurvatureOperatorEvolution
import RicciFlowBlueprint.IveyTouching
import RicciFlowBlueprint.FibrewiseMaximumPrinciple
import RicciFlowBlueprint.ScalarPreservation

open Bundle Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace RicciFlowBlueprint

open CovariantDerivative Pinching ContinuousLinearMap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 4

/-- **The matrix of `Rm₃` in a family of vectors**, for a metric carried as a value. -/
noncomputable def curvatureMat (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) (b : Fin 3 → E) : Mat3 :=
  WithLp.toLp 2 fun ij ↦ innerE g x (curvatureOperatorE g x (b ij.1)) (b ij.2)

/-- `Rm₃` for a metric carried as a value is the curvature operator of its Levi-Civita
connection. -/
theorem curvatureOperatorE_apply_eq
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M) (v : E) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one g
    curvatureOperatorE g x v = (leviCivitaOfMetric g).curvatureOperator x v := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g
  have h := sharpE_apply_eq_sharp (g := fun _ ↦ g) (t₀ := 0) x (ricciFormOfMetric g x) v
  show scalarCurvatureOfMetricAt g x • v - (2 : ℝ) • sharpE g x (ricciFormOfMetric g x) v = _
  rw [h]
  rfl

variable
  {g : ℝ → ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)}
  {h : M → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- **A bounded time derivative makes a curve Lipschitz on `[0,T]`.** -/
theorem norm_sub_le_of_hasDerivAt_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u ut : ℝ → F} {T C : ℝ} (hut : ∀ t ∈ Icc 0 T, HasDerivAt u (ut t) t)
    (hb : ∀ t ∈ Icc 0 T, ‖ut t‖ ≤ C) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ‖u t - u s‖ ≤ C * |t - s| := by
  have key : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → ‖u t - u s‖ ≤ C * |t - s| := by
    intro s hs t ht hst
    have hsub : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs.1 ht.2
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := u) (f' := ut) (C := C)
      (fun r hr ↦ (hut r (hsub hr)).hasDerivWithinAt)
      (fun r hr ↦ hb r (hsub (Ico_subset_Icc_self hr))) t ⟨hst, le_rfl⟩
    rwa [abs_of_nonneg (sub_nonneg.2 hst)]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [norm_sub_rev, abs_sub_comm]
    exact key t ht s hs hts

/-- **Continuity in `x` at each time plus a Lipschitz bound in `t` uniform in `x` gives joint
continuity on `[0,T] × M`.** -/
theorem continuousOn_of_continuous_of_lipschitz_time {M : Type*} [TopologicalSpace M]
    {F : ℝ → M → ℝ} {T B : ℝ} (hx : ∀ t ∈ Icc 0 T, Continuous (F t))
    (ht : ∀ x, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |F t x - F s x| ≤ B * |t - s|) :
    ContinuousOn (fun p : ℝ × M ↦ F p.1 p.2) (Icc 0 T ×ˢ univ) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, -⟩
  have h1 : Filter.Tendsto (fun p : ℝ × M ↦ F t₀ p.2) (𝓝[Icc 0 T ×ˢ univ] (t₀, x₀))
      (𝓝 (F t₀ x₀)) :=
    ((hx t₀ ht₀).continuousAt.comp continuous_snd.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun p : ℝ × M ↦ F p.1 p.2 - F t₀ p.2)
      (𝓝[Icc 0 T ×ˢ univ] (t₀, x₀)) (𝓝 0) := by
    have hc : Filter.Tendsto (fun p : ℝ × M ↦ B * |p.1 - t₀|) (𝓝[Icc 0 T ×ˢ univ] (t₀, x₀))
        (𝓝 0) := by
      have hcont : Continuous (fun p : ℝ × M ↦ B * |p.1 - t₀|) :=
        continuous_const.mul ((continuous_fst.sub continuous_const).abs)
      have h := (hcont.tendsto (t₀, x₀)).mono_left (nhdsWithin_le_nhds (s := Icc 0 T ×ˢ univ))
      simpa using h
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [Real.norm_eq_abs]
    exact ht p.2 t₀ ht₀ p.1 hp.1
  have hsum := h1.add h2
  rw [add_zero] at hsum
  exact hsum.congr fun p ↦ by ring

/-- A matrix-valued function is differentiable when its entries are. -/
theorem hasDerivAt_toLp_mat {φ : ℝ → Fin 3 × Fin 3 → ℝ} {φ' : Fin 3 × Fin 3 → ℝ} {t : ℝ}
    (h : ∀ ij, HasDerivAt (fun s ↦ φ s ij) (φ' ij) t) :
    HasDerivAt (fun s ↦ (WithLp.toLp 2 (φ s) : Mat3)) (WithLp.toLp 2 φ') t :=
  (PiLp.hasFDerivAt_toLp 2 (φ t)).comp_hasDerivAt t (hasDerivAt_pi.2 h)

/-- A `g`-orthonormal frame of `T_xM`, chosen. -/
noncomputable def orthoFrame (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) : Fin 3 → E :=
  Classical.epsilon fun fr : Fin 3 → E ↦
    ∀ i j, innerE g x (fr i) (fr j) = if i = j then (1 : ℝ) else 0

omit [CompleteSpace E] [T2Space M] in
theorem orthoFrame_spec (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) (hdim : finrank ℝ E = 3) (i j : Fin 3) :
    innerE g x (orthoFrame g x i) (orthoFrame g x j) = if i = j then 1 else 0 := by
  refine Classical.epsilon_spec (p := fun fr : Fin 3 → E ↦
    ∀ i j, innerE g x (fr i) (fr j) = if i = j then (1 : ℝ) else 0) ?_ i j
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hd : finrank ℝ (TangentSpace I x) = 3 := hdim
  let b := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hd)
  exact ⟨fun i ↦ b i, fun i j ↦ orthonormal_iff_ite.mp b.orthonormal i j⟩

/-- **The distance of `Rm₃` to the pinching set**, in Hilbert--Schmidt norm, read in any
orthonormal frame (`infDist_curvatureMat_congr`). -/
noncomputable def pinchDist (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) : ℝ :=
  infDist (curvatureMat g x (orthoFrame g x)) pinchedMat

/-- **The Hilbert--Schmidt norm of `Rm₃`**, read in any orthonormal frame. -/
noncomputable def curvNorm (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (x : M) : ℝ :=
  ‖curvatureMat g x (orthoFrame g x)‖

section Frames

variable (g₀ : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x)) (x : M)

/-- **An orthonormal frame is an orthonormal basis, and the matrix of `Rm₃` in it is `toMat`.** -/
theorem exists_curvatureMat_eq_toMat (hdim : finrank ℝ E = 3) (fr : Fin 3 → E)
    (hfr : ∀ i j, innerE g₀ x (fr i) (fr j) = if i = j then 1 else 0) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
    ∃ e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x), (∀ i, e i = fr i) ∧
      curvatureMat g₀ x fr = toMat e ((leviCivitaOfMetric g₀).curvatureOperator x) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → TangentSpace I x, v = fun i ↦ fr i := ⟨_, rfl⟩
  have hon : Orthonormal ℝ v :=
    orthonormal_iff_ite.mpr fun i j ↦ by rw [hv]; exact hfr i j
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp only [Fintype.card_fin]; exact hdim.symm)]
  have he : ∀ i, OrthonormalBasis.mk hon hsp i = fr i := fun i ↦ by
    rw [congrFun (OrthonormalBasis.coe_mk hon hsp) i, hv]
  refine ⟨OrthonormalBasis.mk hon hsp, he, ?_⟩
  ext ij
  rw [toMat_apply, he, he]
  show innerE g₀ x (curvatureOperatorE g₀ x (fr ij.1)) (fr ij.2) = _
  rw [curvatureOperatorE_apply_eq]
  rfl

variable [∀ x : M, Nontrivial (TangentSpace I x)]

/-- **The distance of `Rm₃` to the pinching set does not depend on the orthonormal frame.** -/
theorem infDist_curvatureMat_congr (hdim : finrank ℝ E = 3) {fr fr' : Fin 3 → E}
    (hfr : ∀ i j, innerE g₀ x (fr i) (fr j) = if i = j then 1 else 0)
    (hfr' : ∀ i j, innerE g₀ x (fr' i) (fr' j) = if i = j then 1 else 0) :
    infDist (curvatureMat g₀ x fr) pinchedMat = infDist (curvatureMat g₀ x fr') pinchedMat := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
  let _ : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨e, -, he⟩ := exists_curvatureMat_eq_toMat g₀ x hdim fr hfr
  obtain ⟨e', -, he'⟩ := exists_curvatureMat_eq_toMat g₀ x hdim fr' hfr'
  rw [he, he']
  exact (infDist_toMat_pinchedMat (fun _ _ _ ↦ rfl) e _).trans
    (infDist_toMat_pinchedMat (fun _ _ _ ↦ rfl) e' _).symm

omit [∀ x : M, Nontrivial (TangentSpace I x)] in
/-- **The Hilbert--Schmidt norm of `Rm₃` does not depend on the orthonormal frame.** -/
theorem norm_curvatureMat_congr (hdim : finrank ℝ E = 3) {fr fr' : Fin 3 → E}
    (hfr : ∀ i j, innerE g₀ x (fr i) (fr j) = if i = j then 1 else 0)
    (hfr' : ∀ i j, innerE g₀ x (fr' i) (fr' j) = if i = j then 1 else 0) :
    ‖curvatureMat g₀ x fr‖ = ‖curvatureMat g₀ x fr'‖ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
  let _ : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
  obtain ⟨e, -, he⟩ := exists_curvatureMat_eq_toMat g₀ x hdim fr hfr
  obtain ⟨e', -, he'⟩ := exists_curvatureMat_eq_toMat g₀ x hdim fr' hfr'
  rw [he, he']
  exact (norm_toMat_endTangent (fun _ _ _ ↦ rfl) e _).trans
    (norm_toMat_endTangent (fun _ _ _ ↦ rfl) e' _).symm

/-- **The matrix of `Rm₃` is pinched iff `Rm₃` is**: self-adjointness is automatic. -/
theorem curvatureMat_mem_pinchedMat_iff (hdim : finrank ℝ E = 3) {fr : Fin 3 → E}
    (hfr : ∀ i j, innerE g₀ x (fr i) (fr j) = if i = j then 1 else 0) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
    letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
      contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
    letI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    curvatureMat g₀ x fr ∈ pinchedMat ↔
      (leviCivitaOfMetric g₀).curvatureOperator x ∈ iveyEndoSet (TangentSpace I x) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
  let _ : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨e, -, he⟩ := exists_curvatureMat_eq_toMat g₀ x hdim fr hfr
  rw [he, toMat_mem_pinchedMat_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (leviCivitaOfMetric g₀).isSymmetric_curvatureOperator
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M))
    (torsion_leviCivitaOfMetric_eq_zero g₀) x⟩⟩

end Frames

variable [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]

-- BENCH: pinch-dist-continuous
/-- **At a fixed time the pinching distance and the norm of `Rm₃` are continuous on `M`.**
Near any point they are read in a smooth local orthonormal frame, where the matrix entries are
inner products of smooth sections --- `Rm₃` applied to a frame vector, paired with a frame
vector --- and the frame is invisible (`infDist_curvatureMat_congr`, `norm_curvatureMat_congr`). -/
theorem continuous_pinchDist_curvNorm [∀ x : M, Nontrivial (TangentSpace I x)]
    (hdim : finrank ℝ E = 3)
    (g₀ : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (hrb3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hrb4 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 2)
    (hlc3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 3) :
    Continuous (fun x ↦ pinchDist g₀ x) ∧ Continuous (fun x ↦ curvNorm g₀ x) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
  let _ : IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x) := hrb4
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one g₀
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 2 := hlc2
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric g₀) 3 := hlc3
  -- continuity at each point, through a local orthonormal frame
  have key : ∀ x₀ : M, ∃ m : M → Mat3, ContinuousAt m x₀ ∧
      ∀ᶠ y in 𝓝 x₀, pinchDist g₀ y = infDist (m y) pinchedMat ∧ curvNorm g₀ y = ‖m y‖ := by
    intro x₀
    obtain ⟨U, Fr, hU, hxU, hFr, hon⟩ := exists_orthonormal_frame_on_open (I := I) (n := 2) x₀
    set fr : M → Fin 3 → E := fun y i ↦ Fr (Fin.cast hdim.symm i) y with hfrdef
    have hfro : ∀ y ∈ U, ∀ i j,
        innerE g₀ y (fr y i) (fr y j) = if i = j then 1 else 0 := by
      intro y hy i j
      obtain ⟨b, hb⟩ := hon y hy
      have h := orthonormal_iff_ite.mp b.orthonormal (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
      rw [← hb, ← hb] at h
      simp only [Fin.cast_inj] at h
      exact h
    refine ⟨fun y ↦ curvatureMat g₀ y (fr y), ?_, ?_⟩
    · refine (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.2 fun ij ↦ ?_)
      have hsec : MDiffAt (T% (fun y ↦ (leviCivitaOfMetric g₀).curvatureOperator y
          (Fr (Fin.cast hdim.symm ij.1) y))) x₀ :=
        (ContMDiffAt.clm_bundle_apply ((leviCivitaOfMetric g₀).contMDiff_curvatureOperator x₀)
          (hFr _ x₀)).mdifferentiableAt (by norm_num)
      have hfrm : MDiffAt (T% (Fr (Fin.cast hdim.symm ij.2))) x₀ :=
        (hFr _ x₀).mdifferentiableAt (by norm_num)
      refine (MDifferentiableAt.inner_bundle' hsec hfrm).continuousAt.congr ?_
      refine Filter.Eventually.of_forall fun y ↦ ?_
      show _ = innerE g₀ y (curvatureOperatorE g₀ y (fr y ij.1)) (fr y ij.2)
      rw [curvatureOperatorE_apply_eq]
      rfl
    · filter_upwards [hU.mem_nhds hxU] with y hy
      exact ⟨infDist_curvatureMat_congr g₀ y hdim (orthoFrame_spec g₀ y hdim) (hfro y hy),
        norm_curvatureMat_congr g₀ y hdim (orthoFrame_spec g₀ y hdim) (hfro y hy)⟩
  choose m hm hmeq using key
  refine ⟨continuous_iff_continuousAt.2 fun x₀ ↦ ?_, continuous_iff_continuousAt.2 fun x₀ ↦ ?_⟩
  · have h1 : ContinuousAt (fun y ↦ infDist (m x₀ y) pinchedMat) x₀ :=
      (continuous_infDist_pt pinchedMat).continuousAt.comp (hm x₀)
    refine h1.congr ?_
    filter_upwards [hmeq x₀] with y hy
    exact hy.1.symm
  · have h1 : ContinuousAt (fun y ↦ ‖m x₀ y‖) x₀ := continuous_norm.continuousAt.comp (hm x₀)
    refine h1.congr ?_
    filter_upwards [hmeq x₀] with y hy
    exact hy.2.symm

-- BENCH: hamilton-ivey-touching-time
/-- **The touching step of Hamilton–Ivey at one time, for any family of orthonormal frames.**
If `D x` is the time derivative of `Rm₃` at `x`, then at a spatial maximum of the distance from
`u x = mat_{fr x} Rm₃` to `K_mat`, the outward normal pairs with `mat_{fr x} D` no more than with
Hamilton's reaction. -/
theorem inner_curvatureMat_deriv_le_reaction [I.Boundaryless] (hdim : finrank ℝ E = 3)
    (hg : ∀ y, HasDerivAt (fun t ↦ innerE (g t) y) (h y) t₀)
    (hcomm : CommutesWithMvfderiv g h t₀) (hcov : CommutesWithCov g t₀)
    (hbil : ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) h y)
    (hAt : ∀ x, CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t₀) x)
    (hflow : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsRicciFlowAt I M g t₀)
    (hrb3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hrb4 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2)
    (hlc3 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3)
    (hRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z (U z) (V z)) y)
    (hRic2 : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ Z P : Π y : M, TangentSpace I y, CMDiff 4 (T% Z) → CMDiff 4 (T% P) →
        ContMDiffAt I 𝓘(ℝ, ℝ) 2
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y (Z y) (P y)) x)
    (hdRic : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
        CMDiff 2 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t₀)).ricciForm z) P Q R y) x)
    (hcovR : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
        CMDiff 3 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t₀)).covRicci P Q R y) x)
    (hcb : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, ∀ Y Z : Π y : M, TangentSpace I y, CMDiff 4 (T% Y) → CMDiff 4 (T% Z) →
        (leviCivitaOfMetric (g t₀)).IsMDiffCovBilinAt
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) Y Z x)
    (hscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ y, MDiffAt (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y)
    (hdscal : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, CovariantDerivative.IsMDiffOneFormAt (I := I)
        (fun y ↦ (mvfderiv I (fun z ↦ (leviCivitaOfMetric (g t₀)).scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
      ∀ x, CovariantDerivative.IsMDiffOneFormAt (I := I)
        ((leviCivitaOfMetric (g t₀)).divBilinOneForm
          (fun y ↦ (leviCivitaOfMetric (g t₀)).ricciForm y) (fun y U V _ _ ↦ hRic U V y)) x)
    (fr : M → Fin 3 → E)
    (hfr : ∀ x i j, innerE (g t₀) x (fr x i) (fr x j) = if i = j then 1 else 0)
    {D : M → E →L[ℝ] E} (hD : ∀ x, HasDerivAt (fun t ↦ curvatureOperatorE (g t) x) (D x) t₀)
    {x₀ : M} {p : Mat3} (hp : p ∈ pinchedMat)
    (hpmin : ‖curvatureMat (g t₀) x₀ (fr x₀) - p‖
      = infDist (curvatureMat (g t₀) x₀ (fr x₀)) pinchedMat)
    (hhalf : ∀ q ∈ pinchedMat, ⟪curvatureMat (g t₀) x₀ (fr x₀) - p, q - p⟫ ≤ 0)
    (hmax : ∀ x, infDist (curvatureMat (g t₀) x (fr x)) pinchedMat
      ≤ infDist (curvatureMat (g t₀) x₀ (fr x₀)) pinchedMat) :
    ⟪curvatureMat (g t₀) x₀ (fr x₀) - p,
        WithLp.toLp 2 fun ij ↦ innerE (g t₀) x₀ (D x₀ (fr x₀ ij.1)) (fr x₀ ij.2)⟫
      ≤ ⟪curvatureMat (g t₀) x₀ (fr x₀) - p, reactionMat (curvatureMat (g t₀) x₀ (fr x₀))⟫ := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t₀).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x) := hrb3
  let _ : IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x) := hrb4
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 :=
    contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 2 := hlc2
  let _ : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 3 := hlc3
  let _ : RiemannianBundle (EndTangent I (M := M)) := endTangentRiemannianBundle (n := 1)
  let _ : IsContMDiffRiemannianBundle I 1 (E →L[ℝ] E) (EndTangent I (M := M)) :=
    isContMDiffRiemannianBundle_endTangent (n := 1)
  have hfd : ∀ x : M, FiniteDimensional ℝ (TangentSpace I x) := fun _ ↦
    inferInstanceAs (FiniteDimensional ℝ E)
  have hnt : ∀ x : M, Nontrivial (TangentSpace I x) := fun x ↦
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := TangentSpace I x)
      (show 0 < finrank ℝ (TangentSpace I x) by
        rw [show finrank ℝ (TangentSpace I x) = 3 from hdim]; norm_num)
  have hinner : ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q :=
    fun _ _ _ ↦ rfl
  -- the frames are orthonormal bases
  have hbasis : ∀ x : M, ∃ e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x), ∀ i, e i = fr x i := by
    intro x
    obtain ⟨v, hv⟩ : ∃ v : Fin 3 → TangentSpace I x, v = fun i ↦ fr x i := ⟨_, rfl⟩
    have hon : Orthonormal ℝ v :=
      orthonormal_iff_ite.mpr fun i j ↦ by rw [hv]; exact hfr x i j
    have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
      rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank'
        (by simp only [Fintype.card_fin]; exact hdim.symm)]
    refine ⟨OrthonormalBasis.mk hon hsp, fun i ↦ ?_⟩
    rw [congrFun (OrthonormalBasis.coe_mk hon hsp) i, hv]
  choose e he using hbasis
  have hu : ∀ x, curvatureMat (g t₀) x (fr x)
      = toMat (e x) ((leviCivitaOfMetric (g t₀)).curvatureOperator x) := by
    intro x
    ext ij
    rw [toMat_apply, he, he]
    show innerE (g t₀) x (curvatureOperatorE (g t₀) x (fr x ij.1)) (fr x ij.2) = _
    rw [curvatureOperatorE_apply_eq]
    rfl
  -- the evolution equation at the touching point
  obtain ⟨D', hD', hid⟩ := exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt hdim hg hcomm
    hcov hbil (hAt x₀) hflow hrb3 hrb4 hlc2 hlc3 hRic (hRic2 x₀) (hdRic x₀) (hcovR x₀) (hcb x₀)
    hscal (hdscal x₀) (hw x₀)
  have hDD : D x₀ = D' := (hD x₀).unique hD'
  set Lap := (endCov (leviCivitaOfMetric (g t₀))).laplacianSection (leviCivitaOfMetric (g t₀))
    ((leviCivitaOfMetric (g t₀)).contMDiff_curvatureOperator) x₀ with hLap
  have hut : (WithLp.toLp 2 fun ij ↦ innerE (g t₀) x₀ (D x₀ (fr x₀ ij.1)) (fr x₀ ij.2) : Mat3)
      = toMat (e x₀) Lap
        + reactionMat (curvatureMat (g t₀) x₀ (fr x₀)) := by
    rw [hu, ← toMat_hamiltonReaction, ← map_add]
    ext ij
    rw [toMat_apply, he, he]
    show innerE (g t₀) x₀ (D x₀ (fr x₀ ij.1)) (fr x₀ ij.2) = _
    rw [hDD]
    exact hid _ _
  have htouch := inner_toMat_laplacian_curvatureOperator_nonpos (leviCivitaOfMetric (g t₀))
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)) hinner e
    (fun x ↦ by rw [← hu, ← hu]; exact hmax x) hp (by rw [← hu]; exact hpmin)
    (by rw [← hu]; exact hhalf)
  rw [← hu] at htouch
  have h2 : ⟪curvatureMat (g t₀) x₀ (fr x₀) - p, toMat (e x₀) Lap⟫ ≤ 0 := htouch
  rw [hut, inner_add_right]
  linarith


-- BENCH: hamilton-ivey-three
/-- **Hamilton–Ivey pinching is preserved by the Ricci flow on a closed three-manifold.**

For a Ricci flow `g_t`, `t ∈ [0,T]`, on a compact boundaryless three-manifold, regular enough for
the evolution equations of `scal` and `Ric` to hold (the hypotheses of
`exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt` at every time), and with the time
derivative of `Rm₃` bounded on `[0,T] × M`: if the curvature operator is in Hamilton's pinching
set at `t = 0`, it is at every `t ∈ [0,T]`.

**The one joint-in-`(t,x)` input is the bound on `∂ₜRm₃`** (`hDbound`) --- the metric is a
family `g : ℝ → ContMDiffRiemannianMetric`, which encodes no joint regularity at all, so some
such input is unavoidable. From it the proof *derives* what the maximum principle consumes:
continuity of the pinching distance on `[0,T] × M` (continuous in `x` at each time, by
`continuous_pinchDist_curvNorm`, and Lipschitz in `t` uniformly in `x`) and a bound on `Rm₃`
(compactness at `t = 0`, then Lipschitz in `t`). -/
theorem curvatureOperator_mem_iveyEndoSet_of_isRicciFlow [CompactSpace M] [I.Boundaryless]
    (hdim : finrank ℝ E = 3) [∀ x : M, Nontrivial (TangentSpace I x)] {T : ℝ}
    {h : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ t ∈ Icc 0 T, ∀ y, HasDerivAt (fun s ↦ innerE (g s) y) (h t y) t)
    (hcomm : ∀ t ∈ Icc 0 T, CommutesWithMvfderiv g (h t) t)
    (hcov : ∀ t ∈ Icc 0 T, CommutesWithCov g t)
    (hbil : ∀ t ∈ Icc 0 T, ∀ y : M, CovariantDerivative.IsMDiffBilinAt (I := I) (h t) y)
    (hAt : ∀ t ∈ Icc 0 T, ∀ x,
      CovariantDerivative.IsMDiffTwoTensorAt (I := I) (derivDifferenceTensor g t) x)
    (hflow : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      IsRicciFlowAt I M g t)
    (hrb3 : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x))
    (hrb4 : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x))
    (hlc2 : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 2)
    (hlc3 : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 3)
    (hRic : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ (U V : Π y : M, TangentSpace I y) (y : M),
        MDiffAt (fun z ↦ (leviCivitaOfMetric (g t)).ricciForm z (U z) (V z)) y)
    (hRic2 : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ x, ∀ Z P : Π y : M, TangentSpace I y, CMDiff 4 (T% Z) → CMDiff 4 (T% P) →
        ContMDiffAt I 𝓘(ℝ, ℝ) 2
          (fun y ↦ (leviCivitaOfMetric (g t)).ricciForm y (Z y) (P y)) x)
    (hdRic : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ x, ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
        CMDiff 2 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t)).covBilin
          (fun z ↦ (leviCivitaOfMetric (g t)).ricciForm z) P Q R y) x)
    (hcovR : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ x, ∀ P Q R : Π y : M, TangentSpace I y, CMDiff 2 (T% P) → CMDiff 3 (T% Q) →
        CMDiff 3 (T% R) → MDiffAt (fun y ↦ (leviCivitaOfMetric (g t)).covRicci P Q R y) x)
    (hcb : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ x, ∀ Y Z : Π y : M, TangentSpace I y, CMDiff 4 (T% Y) → CMDiff 4 (T% Z) →
        (leviCivitaOfMetric (g t)).IsMDiffCovBilinAt
          (fun y ↦ (leviCivitaOfMetric (g t)).ricciForm y) Y Z x)
    (hscal : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ y, MDiffAt (fun z ↦ (leviCivitaOfMetric (g t)).scalarCurvatureAt z) y)
    (hdscal : ∀ t ∈ Icc 0 T, letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ x, CovariantDerivative.IsMDiffOneFormAt (I := I)
        (fun y ↦ (mvfderiv I (fun z ↦ (leviCivitaOfMetric (g t)).scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : ∀ t (ht : t ∈ Icc 0 T), letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      ∀ x, CovariantDerivative.IsMDiffOneFormAt (I := I)
        ((leviCivitaOfMetric (g t)).divBilinOneForm
          (fun y ↦ (leviCivitaOfMetric (g t)).ricciForm y) (fun y U V _ _ ↦ hRic t ht U V y)) x)
    (hDbound : ∃ C, ∀ t ∈ Icc 0 T, ∀ x : M, ∀ v w : E,
      innerE (g t) x v v = 1 → innerE (g t) x w w = 1 →
      |innerE (g t) x (deriv (fun s ↦ curvatureOperatorE (g s) x) t v) w| ≤ C)
    (h0 : ∀ x : M,
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g 0).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g 0)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g 0)
      letI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
      (leviCivitaOfMetric (g 0)).curvatureOperator x ∈ iveyEndoSet (TangentSpace I x)) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      letI : CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaOfMetric (g t)) 1 :=
        contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t)
      letI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
      (leviCivitaOfMetric (g t)).curvatureOperator x ∈ iveyEndoSet (TangentSpace I x) := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht
    exact absurd (ht.1.trans ht.2) (not_le.2 hT)
  -- the Uhlenbeck coefficient `Ric♯`, extended off `[0,T]` by clamping
  set fA : M → ℝ → E →L[ℝ] E := fun x s ↦ sharpE (g s) x (ricciFormOfMetric (g s) x) with hfA
  have hfAd : ∀ x, ∀ t ∈ Icc 0 T, HasDerivAt (fA x) _ t := fun x t ht ↦
    hasDerivAt_sharpE (hg t ht x) (hasDerivAt_ricciFormOfMetric (hg t ht) (hcomm t ht) (hcov t ht) x)
  have hfAc : ∀ x, ContinuousOn (fA x) (Icc 0 T) := fun x t ht ↦
    (hfAd x t ht).continuousAt.continuousWithinAt
  set A : M → ℝ → E →L[ℝ] E := fun x s ↦ fA x (projIcc 0 T hT s) with hAdef
  have hAc : ∀ x, Continuous (A x) := fun x ↦
    (hfAc x).comp_continuous (continuous_subtype_val.comp (continuous_projIcc (h := hT)))
      fun s ↦ Subtype.mem (projIcc 0 T hT s)
  have hAb : ∀ x, ∃ C, ∀ s, ‖A x s‖ ≤ C := fun x ↦ by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hfAc x)
    exact ⟨C, fun s ↦ hC _ (Subtype.mem (projIcc 0 T hT s))⟩
  choose C hC using hAb
  have hAeq : ∀ x, ∀ t ∈ Icc 0 T, A x t = fA x t := fun x t ht ↦ by
    simp only [hAdef, projIcc_of_mem hT ht]
  -- the metric, its derivative, and the sharp relation
  have hG : ∀ x, ∀ t ∈ Icc 0 T, HasDerivAt (fun s ↦ innerE (g s) x)
      ((-2 : ℝ) • ricciFormOfMetric (g t) x) t := fun x t ht ↦ by
    rw [← innerE_deriv_eq_of_isRicciFlowAt' (hg t ht) x (hflow t ht)]; exact hg t ht x
  have hGA : ∀ x, ∀ t ∈ Icc 0 T, ∀ v w,
      innerE (g t) x (A x t v) w = ricciFormOfMetric (g t) x v w := fun x t ht v w ↦ by
    rw [hAeq x t ht]; exact innerE_sharpE (g t) x _ v w
  have hGsymm : ∀ x t, ∀ v w, innerE (g t) x v w = innerE (g t) x w v :=
    fun x t v w ↦ (g t).symm x v w
  have hBsymm : ∀ x t, ∀ v w, ricciFormOfMetric (g t) x v w = ricciFormOfMetric (g t) x w v :=
    fun x t v w ↦ ricciFormOfMetric_symm (g t) x v w
  -- the Uhlenbeck frame, orthonormal for `g_t`
  set e₀ : M → Fin 3 → E := fun x ↦ orthoFrame (g 0) x with he₀
  set fr : ℝ → M → Fin 3 → E := fun t x i ↦ dysonSum (A x) t (e₀ x i) with hfrdef
  have hfr : ∀ t ∈ Icc 0 T, ∀ x i j,
      innerE (g t) x (fr t x i) (fr t x j) = if i = j then 1 else 0 := fun t ht x i j ↦ by
    rw [show innerE (g t) x (fr t x i) (fr t x j)
        = innerE (g 0) x (e₀ x i) (e₀ x j) from
      Uhlenbeck.metric_dysonSum_eq (G := fun s ↦ innerE (g s) x) (B := fun s ↦ ricciFormOfMetric (g s) x)
        (hAc x) (hC x) (hG x) (hGA x) (fun t _ ↦ hGsymm x t) (fun t _ ↦ hBsymm x t) _ _ ht]
    exact orthoFrame_spec (g 0) x hdim i j
  -- the time derivative of `Rm₃`
  have hDex : ∀ t ∈ Icc 0 T, ∀ x,
      ∃ D : E →L[ℝ] E, HasDerivAt (fun s ↦ curvatureOperatorE (g s) x) D t := fun t ht x ↦ by
    obtain ⟨D, hD, -⟩ := exists_hasDerivAt_curvatureOperatorE_eq_of_isRicciFlowAt hdim
      (hg t ht) (hcomm t ht) (hcov t ht) (hbil t ht) (hAt t ht x) (hflow t ht) (hrb3 t ht)
      (hrb4 t ht) (hlc2 t ht) (hlc3 t ht) (hRic t ht) (hRic2 t ht x) (hdRic t ht x)
      (hcovR t ht x) (hcb t ht x) (hscal t ht) (hdscal t ht x) (hw t ht x)
    exact ⟨D, hD⟩
  set D : ℝ → M → E →L[ℝ] E := fun t x ↦ deriv (fun s ↦ curvatureOperatorE (g s) x) t with hDdef
  have hD : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivAt (fun s ↦ curvatureOperatorE (g s) x) (D t x) t := fun t ht x ↦
    (hDex t ht x).choose_spec.differentiableAt.hasDerivAt
  -- the matrix in the Uhlenbeck frame and its time derivative
  set u : ℝ → M → Mat3 := fun t x ↦ curvatureMat (g t) x (fr t x) with hudef
  set ut : ℝ → M → Mat3 := fun t x ↦
    WithLp.toLp 2 fun ij ↦ innerE (g t) x (D t x (fr t x ij.1)) (fr t x ij.2) with hutdef
  have hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t := fun t ht x ↦ by
    have hRA : curvatureOperatorE (g t) x ∘L A x t = A x t ∘L curvatureOperatorE (g t) x := by
      rw [hAeq x t ht]; exact curvatureOperatorE_comm (g t) x
    refine hasDerivAt_toLp_mat fun ij ↦ ?_
    exact Uhlenbeck.hasDerivAt_metric_dysonSum_conj (G := fun s ↦ innerE (g s) x)
      (B := fun s ↦ ricciFormOfMetric (g s) x) (hAc x) (hC x) (hG x t ht) (hGA x t ht)
      (hGsymm x t) (hBsymm x t) (hD t ht x) hRA (e₀ x ij.1) (e₀ x ij.2)
  -- the fibrewise maximum principle in the fixed space `Mat3`
  -- the time derivative of `u` is bounded: its entries pair `∂ₜRm₃` against unit vectors
  obtain ⟨C, hCb⟩ := hDbound
  set Cp := max C 0 with hCp
  have hutb : ∀ t ∈ Icc 0 T, ∀ x, ‖ut t x‖ ≤ 3 * Cp := fun t ht x ↦ by
    have hunit : ∀ i, innerE (g t) x (fr t x i) (fr t x i) = 1 := fun i ↦ by
      rw [hfr t ht x i i]; simp
    have hent : ∀ ij : Fin 3 × Fin 3,
        ‖innerE (g t) x (D t x (fr t x ij.1)) (fr t x ij.2)‖ ^ 2 ≤ Cp ^ 2 := fun ij ↦ by
      have h := hCb t ht x _ _ (hunit ij.1) (hunit ij.2)
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h.trans (le_max_left _ _)) 2
    have hsum : ∑ ij : Fin 3 × Fin 3,
        ‖innerE (g t) x (D t x (fr t x ij.1)) (fr t x ij.2)‖ ^ 2 ≤ (3 * Cp) ^ 2 := by
      refine (Finset.sum_le_sum fun ij _ ↦ hent ij).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring
    rw [hutdef, EuclideanSpace.norm_eq]
    exact (Real.sqrt_le_sqrt hsum).trans
      (le_of_eq (Real.sqrt_sq (by positivity)))
  have hlip : ∀ x, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ‖u t x - u s x‖ ≤ 3 * Cp * |t - s| :=
    fun x ↦ norm_sub_le_of_hasDerivAt_Icc (fun t ht ↦ hut t ht x) (fun t ht ↦ hutb t ht x)
  -- at each time the distance and the norm are continuous in space
  have hcont : ∀ t ∈ Icc 0 T,
      Continuous (fun x ↦ pinchDist (g t) x) ∧ Continuous (fun x ↦ curvNorm (g t) x) :=
    fun t ht ↦ continuous_pinchDist_curvNorm hdim (g t) (hrb3 t ht) (hrb4 t ht) (hlc2 t ht)
      (hlc3 t ht)
  have hdc' : ContinuousOn (fun p : ℝ × M ↦ infDist (u p.1 p.2) pinchedMat) (Icc 0 T ×ˢ univ) := by
    refine continuousOn_of_continuous_of_lipschitz_time
      (F := fun t x ↦ infDist (u t x) pinchedMat) (B := 3 * Cp) (fun t ht ↦ ?_) ?_
    · refine (hcont t ht).1.congr fun x ↦ ?_
      exact (infDist_curvatureMat_congr (g t) x hdim (hfr t ht x)
        (orthoFrame_spec (g t) x hdim)).symm
    · intro x s hs t ht
      have h := (lipschitz_infDist_pt pinchedMat).dist_le_mul (u t x) (u s x)
      rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm] at h
      exact h.trans (hlip x s hs t ht)
  -- and `Rm₃` stays bounded: bounded at `t = 0` by compactness, Lipschitz in `t`
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨C0, hC0⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont 0 h0T).2.continuousOn
  set Bd := C0 + 3 * Cp * T with hBddef
  obtain ⟨Lc, hLc⟩ := exists_lipschitzOnWith_reactionMat (2 * Bd)
  have hu : ∀ t ∈ Icc 0 T, ∀ x, ‖u t x‖ ≤ Bd := fun t ht x ↦ by
    have h0 : ‖u 0 x‖ = curvNorm (g 0) x :=
      norm_curvatureMat_congr (g 0) x hdim (hfr 0 h0T x) (orthoFrame_spec (g 0) x hdim)
    have hc0 : curvNorm (g 0) x ≤ C0 := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hC0 x (mem_univ x))
    have hl := hlip x 0 h0T t ht
    rw [sub_zero, abs_of_nonneg ht.1] at hl
    have hCp0 : 0 ≤ Cp := le_max_right _ _
    calc ‖u t x‖ ≤ ‖u 0 x‖ + ‖u t x - u 0 x‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ C0 + 3 * Cp * T := by
        rw [h0]; nlinarith [ht.2]
  have hmax : ∀ t ∈ Icc 0 T, ∀ x₀ : M, ∀ p ∈ pinchedMat,
      ‖u t x₀ - p‖ = infDist (u t x₀) pinchedMat →
      (∀ q ∈ pinchedMat, (⟪u t x₀ - p, q - p⟫ : ℝ) ≤ 0) →
      (∀ x, infDist (u t x) pinchedMat ≤ infDist (u t x₀) pinchedMat) →
      (⟪u t x₀ - p, ut t x₀⟫ : ℝ) ≤ ⟪u t x₀ - p, reactionMat (u t x₀)⟫ :=
    fun t ht x₀ p hp hpmin hhalf hmaxm ↦
      inner_curvatureMat_deriv_le_reaction hdim (hg t ht) (hcomm t ht) (hcov t ht) (hbil t ht)
        (hAt t ht) (hflow t ht) (hrb3 t ht) (hrb4 t ht) (hlc2 t ht) (hlc3 t ht) (hRic t ht)
        (hRic2 t ht) (hdRic t ht) (hcovR t ht) (hcb t ht) (hscal t ht) (hdscal t ht) (hw t ht)
        (fr t) (hfr t ht) (hD t ht) hp hpmin hhalf hmaxm
  have hfr0 : ∀ x, fr 0 x = e₀ x := fun x ↦ by
    funext i; simp only [hfrdef, dysonSum_zero, one_apply_eq_self]
  have h0' : ∀ x, u 0 x ∈ pinchedMat := fun x ↦ by
    rw [hudef]
    simp only [hfr0]
    exact (curvatureMat_mem_pinchedMat_iff (g 0) x hdim (orthoFrame_spec (g 0) x hdim)).mpr
      (h0 x)
  have key := MaximumPrinciple.mem_of_infDist_max_local (V := fun _ : M ↦ Mat3) (u := u) (ut := ut)
    (F := fun _ ↦ reactionMat) (K := fun _ ↦ pinchedMat) (L := Lc) (T := T) (B := Bd)
    (fun _ ↦ isClosed_pinchedMat) (fun _ ↦ convex_pinchedMat) (fun _ ↦ zero_mem_pinchedMat)
    hdc' hut hu (fun _ ↦ hLc) hmax (fun _ _ hp _ hn ↦ inner_reactionMat_nonpos hp hn) h0'
  intro t ht x
  exact (curvatureMat_mem_pinchedMat_iff (g t) x hdim (hfr t ht x)).mp (key t ht x)

end RicciFlowBlueprint
