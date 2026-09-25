/-
**The touching-point step of Hamilton–Ivey, read in matrices.**

The fibrewise maximum principle runs on `u x = mat_{e x}(Rm₃ x)` in the fixed space `Mat3`, the
bases `e x` chosen arbitrarily, point by point. Its touching-point hypothesis asks, at a spatial
maximum of `dist(u, K_mat)` and for the nearest point `p`, that `⟪u − p, mat(ΔRm₃)⟫ ≤ 0`.
`BundleDistanceMax.lean` proves exactly that on `End(TM)` with the Hilbert--Schmidt metric; what
is added here is the dictionary. `mat_e` is an isometry from the HS fibre **onto** `Mat3` carrying
the self-adjoint pinching set onto `K_mat`, so distances to the set, nearest points, half-spaces
and pairings all transfer, and a maximum of the matrix distance is a maximum of the bundle one.
The choice of `e x` is invisible, which is why it needs no continuity.
-/
import RicciFlowBlueprint.IveyParallelEnd
import RicciFlowBlueprint.CurvatureOperatorMaxPrinciple

open Bundle Metric
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

open CovariantDerivative Pinching

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 4

variable (x) in
/-- The self-adjoint pinching set in the fibre of `End(TM)` over `x`. -/
def pinchedEnd (x : M) [Nontrivial (TangentSpace I x)] [FiniteDimensional ℝ (TangentSpace I x)] :
    Set (EndTangent I x) :=
  {A : EndTangent I x | (A : TangentSpace I x →L[ℝ] TangentSpace I x) ∈ symmIvey (TangentSpace I x)}

theorem image_toMat_pinchedEnd {x : M} [Nontrivial (TangentSpace I x)]
    [FiniteDimensional ℝ (TangentSpace I x)] (e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x)) :
    (fun A : EndTangent I x ↦ toMat e A) '' pinchedEnd x = pinchedMat := by
  ext m
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (toMat_mem_pinchedMat_iff e _).mpr hA
  · intro hm
    obtain ⟨A, rfl⟩ := toMat_surjective e m
    exact ⟨A, (toMat_mem_pinchedMat_iff e A).mp hm, rfl⟩

section Dictionary

variable [FiniteDimensional ℝ E] [IsManifold I ω M] [RiemannianBundle (EndTangent I (M := M))]
  (hinner : ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q)
  {x : M} (e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x))

include hinner in
/-- The matrix map is isometric for the Hilbert--Schmidt fibre metric. -/
theorem inner_toMat_endTangent (A B : EndTangent I x) :
    ⟪toMat e A, toMat e B⟫ = ⟪A, B⟫ := by
  refine (inner_toMat e A B).trans ?_
  rw [hinner]
  exact (hsFibre_eq e A B).symm

include hinner in
theorem norm_toMat_endTangent (A : EndTangent I x) : ‖toMat e A‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_toMat_endTangent hinner]

include hinner in
theorem isometry_toMat_endTangent :
    Isometry (fun A : EndTangent I x ↦ toMat e A) := by
  refine Isometry.of_dist_eq fun A B ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ← norm_toMat_endTangent hinner e (A - B)]
  exact congrArg norm (map_sub (toMat e) A B).symm

include hinner in
/-- **Distance to the pinching set is frame-independent**: the matrix distance is the
Hilbert--Schmidt distance in the fibre. -/
theorem infDist_toMat_pinchedMat [Nontrivial (TangentSpace I x)]
    [FiniteDimensional ℝ (TangentSpace I x)] (A : EndTangent I x) :
    infDist (toMat e A) pinchedMat = infDist A (pinchedEnd x) := by
  rw [← image_toMat_pinchedEnd e]
  exact infDist_image (isometry_toMat_endTangent hinner e)

end Dictionary

section Touching

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] [T2Space M]
  [I.Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 4 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 3 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffVectorBundle 4 E (fun (x : M) ↦ TangentSpace I x) I]
  [RiemannianBundle (EndTangent I (M := M))]
  [IsContMDiffRiemannianBundle I 1 (E →L[ℝ] E) (EndTangent I (M := M))]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]
  [∀ x : M, Nontrivial (TangentSpace I x)] [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

-- BENCH: ivey-touching-matrix
/-- **The touching-point step in matrices.** With the bases `e x` chosen arbitrarily, at a
spatial maximum of `x ↦ dist(mat_{e x} Rm₃(x), K_mat)` and for a nearest point `p` with its
supporting half-space, `⟪mat Rm₃ − p, mat ΔRm₃⟫ ≤ 0`. -/
theorem inner_toMat_laplacian_curvatureOperator_nonpos
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hinner : ∀ (y : M) (P Q : EndTangent I y), ⟪P, Q⟫ = hsFibre (I := I) y P Q)
    (e : ∀ x : M, OrthonormalBasis (Fin 3) ℝ (TangentSpace I x)) {x₀ : M}
    (hmax : ∀ x, infDist (toMat (e x) (cov.curvatureOperator x)) pinchedMat
      ≤ infDist (toMat (e x₀) (cov.curvatureOperator x₀)) pinchedMat)
    {p : Mat3} (hp : p ∈ pinchedMat)
    (hpmin : ‖toMat (e x₀) (cov.curvatureOperator x₀) - p‖
      = infDist (toMat (e x₀) (cov.curvatureOperator x₀)) pinchedMat)
    (hhalf : ∀ q ∈ pinchedMat, ⟪toMat (e x₀) (cov.curvatureOperator x₀) - p, q - p⟫ ≤ 0) :
    ⟪toMat (e x₀) (cov.curvatureOperator x₀) - p,
      toMat (e x₀) (CovariantDerivative.laplacianSection (endTangentCov cov) cov
        (cov.contMDiff_curvatureOperator_endTangent) x₀)⟫ ≤ 0 := by
  obtain ⟨P₀, rfl⟩ := toMat_surjective (e x₀) p
  obtain ⟨P, hP⟩ : ∃ P : EndTangent I x₀, P = P₀ := ⟨P₀, rfl⟩
  subst hP
  set R : Π y : M, EndTangent I y := fun y ↦ cov.curvatureOperator y with hR
  have hPK : P ∈ pinchedEnd x₀ := (toMat_mem_pinchedMat_iff _ _).mp hp
  have hsub : toMat (e x₀) (cov.curvatureOperator x₀) - toMat (e x₀) P
      = toMat (e x₀) (R x₀ - P) := (map_sub (toMat (e x₀)) _ _).symm
  have hmaxf : ∀ x, infDist (R x) (pinchedEnd x) ≤ infDist (R x₀) (pinchedEnd x₀) := fun x ↦ by
    rw [← infDist_toMat_pinchedMat hinner (e x), ← infDist_toMat_pinchedMat hinner (e x₀)]
    exact hmax x
  have hpmin' : ‖R x₀ - P‖ = infDist (R x₀) (pinchedEnd x₀) := by
    rw [← infDist_toMat_pinchedMat hinner (e x₀), ← norm_toMat_endTangent hinner (e x₀), ← hsub]
    exact hpmin
  have hhalf' : ∀ q ∈ pinchedEnd x₀,
      (⟪R x₀ - P, q - P⟫ : ℝ) ≤ 0 := by
    intro q hq
    have h := hhalf (toMat (e x₀) q) ((toMat_mem_pinchedMat_iff _ _).mpr hq)
    have hq' : toMat (e x₀) q - toMat (e x₀) P = toMat (e x₀) (q - P) := (map_sub _ _ _).symm
    rw [hsub, hq', inner_toMat_endTangent hinner] at h
    exact h
  have hK0 : ∀ x : M, (pinchedEnd (I := I) x).Nonempty := fun x ↦ ⟨0, zero_mem_symmIvey⟩
  have h := inner_laplacianSection_nonpos_of_infDist_le (endTangentCov cov) cov
    (isMetricCompatible_endTangentCov cov hmet hinner) (hasParallelTransport_endTangent cov hmet)
    hK0 (isParallelSet_symmIvey cov hmet) (cov.contMDiff_curvatureOperator_endTangent) hmaxf
    hpmin' hhalf' (stdOrthonormalBasis ℝ (TangentSpace I x₀))
  rw [hsub, inner_toMat_endTangent hinner]
  exact h

end Touching

end RicciFlowBlueprint
