/-
**Every parallel `End(TM)` field is conjugation by transport, so the pinching set is a parallel
family.**

`EndTransport.lean` *builds* a parallel endomorphism field through each endomorphism and shows
the one it builds is conjugation by the `TM` transport isometry. The bundle maximum principle
asks more: `IsParallelSet` quantifies over **every** parallel field. The gap is uniqueness of
parallel sections of `End(TM)`, and it is closed without any uniqueness theorem on the Hom
bundle: a parallel `N` carries parallel vector fields to parallel vector fields
(`isParallelAlongSection_hom`), and on `TM` those are determined by their initial values
(`exists_parallelTransportIsometry_global`). So `N t v = P (N t₀ (P⁻¹ v))` for every `v`.
-/
import RicciFlowBlueprint.IveyMatrixModel
import RicciFlowBlueprint.EndTransport
import RicciFlowBlueprint.EndMetricCompat
import RicciFlowBlueprint.BundleDistanceMax

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

open CovariantDerivative Pinching

section Conj

variable {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W']

theorem endoConj_symm_endoConj (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    endoConj S.symm (endoConj S A) = A := by
  ext v; simp

/-- `toMat e` is onto: every matrix is the matrix of the conjugate of its operator on `ℝ³`. -/
theorem toMat_surjective (e : OrthonormalBasis (Fin 3) ℝ W) :
    Function.Surjective (toMat e) := by
  intro m
  refine ⟨endoConj e.repr.symm (fromMat m), ?_⟩
  have h := endoConj_symm_endoConj e.repr.symm (fromMat m)
  rw [LinearIsometryEquiv.symm_symm] at h
  rw [toMat_eq_std, h, toMat_fromMat]

variable [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] [Nontrivial W] [Nontrivial W']

/-- The self-adjoint pinching set is natural under isometries. -/
theorem mem_symmIvey_conj_iff (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    endoConj S A ∈ symmIvey W' ↔ A ∈ symmIvey W := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨(mem_iveyEndoSet_conj_iff S A).mp h1, ?_⟩,
    fun ⟨h1, h2⟩ ↦ ⟨(mem_iveyEndoSet_conj_iff S A).mpr h1, isSymmetric_endoConj S h2⟩⟩
  have := isSymmetric_endoConj S.symm h2
  rwa [endoConj_symm_endoConj] at this

end Conj

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

-- BENCH: parallel-end-conj
/-- **A parallel endomorphism field is conjugation by the transport isometry**, whichever
parallel field it is. -/
theorem parallel_end_eq_endoConj
    {γ : ℝ → M} {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ s)
    {P : TangentSpace I (γ t₀) ≃ₗᵢ[ℝ] TangentSpace I (γ t)}
    (hP : ∀ V : Π u : ℝ, TangentSpace I (γ u), (∀ u ∈ s, MDiffAlongAt γ V u) →
      IsParallelAlong cov γ V s → V t = P (V t₀))
    {N : Π u : ℝ, TangentSpace I (γ u) →L[ℝ] TangentSpace I (γ u)}
    (hNd : ∀ u ∈ s, MDiffAlongSectionAt I (E →L[ℝ] E)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) γ N u)
    (hNp : IsParallelAlongSection I (E →L[ℝ] E)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) (homCov cov cov) γ N s) :
    N t = endoConj P (N t₀) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  obtain ⟨V, hV0, hVd, hVp⟩ := exists_isParallelAlong_global cov hs hconn hγ hγv ht₀ (P.symm v)
  have hVt : V t = v := by rw [hP V hVd hVp, hV0, P.apply_symm_apply]
  have hVs : IsParallelAlongSection I E (fun y : M ↦ TangentSpace I y) cov γ V s :=
    (isParallelAlongSection_iff_isParallelAlong cov hγ hVd).mpr hVp
  have hWp := isParallelAlongSection_hom cov cov hγ hNd (fun u hu ↦ hVd u hu) hNp hVs
  have hWd : ∀ u ∈ s, MDiffAlongAt γ (fun u ↦ N u (V u)) u := fun u hu ↦
    MDifferentiableAt.clm_bundle_apply (hNd u hu) (hVd u hu)
  have hW := hP (fun u ↦ N u (V u)) hWd
    ((isParallelAlongSection_iff_isParallelAlong cov hγ hWd).mp hWp)
  rw [endoConj_apply, ← hV0, ← hW, hVt]

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- BENCH: is-parallel-set-ivey
/-- **The self-adjoint pinching set is a parallel family in `End(TM)`**, in the sense the bundle
maximum principle consumes: membership is preserved along every parallel endomorphism field. -/
theorem isParallelSet_symmIvey (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    [∀ x : M, Nontrivial (TangentSpace I x)] [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] :
    IsParallelSet I (E →L[ℝ] E) (EndTangent I (M := M)) (endTangentCov cov)
      (fun x ↦ {A : EndTangent I x |
        (A : TangentSpace I x →L[ℝ] TangentSpace I x) ∈ symmIvey (TangentSpace I x)}) := by
  intro γ s hs hconn hγ hγv N hNd hNp t₀ ht₀ t ht
  obtain ⟨P, hP⟩ := exists_parallelTransportIsometry_global cov hmet hs hconn hγ hγv ht₀ ht
  have h := parallel_end_eq_endoConj cov hs hconn hγ hγv ht₀ hP
    (N := fun u ↦ (N u : TangentSpace I (γ u) →L[ℝ] TangentSpace I (γ u))) hNd hNp
  show (N t : TangentSpace I (γ t) →L[ℝ] TangentSpace I (γ t)) ∈ symmIvey _ ↔
    (N t₀ : TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t₀)) ∈ symmIvey _
  rw [h]
  exact mem_symmIvey_conj_iff P _

/-- **`End(TM)` admits parallel transport**, in the total-space form the geodesic argument
consumes: `EndTransport.lean`'s construction, through any endomorphism of any fibre. -/
theorem hasParallelTransport_endTangent
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    [∀ x : M, Nontrivial (TangentSpace I x)] :
    HasParallelTransport I (E →L[ℝ] E) (EndTangent I (M := M)) (endTangentCov cov) := by
  intro γ s hs hconn hγ hγv t₀ ht₀ x n hx
  subst hx
  have : FiniteDimensional ℝ (TangentSpace I (γ t₀)) := inferInstanceAs (FiniteDimensional ℝ E)
  have : Nonempty (Fin (Module.finrank ℝ (TangentSpace I (γ t₀)))) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨A, hA0, hAd, hAp⟩ := exists_isParallelAlongSection_end cov hmet hs hconn hγ hγv ht₀
    (stdOrthonormalBasis ℝ (TangentSpace I (γ t₀))) n
  exact ⟨A, by rw [hA0], hAd, hAp⟩

end RicciFlowBlueprint
