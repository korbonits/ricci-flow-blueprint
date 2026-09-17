/-
**Parallel transport is an isometry**, for a metric connection.

`ParallelTransport.lean` builds transport as a continuous linear *equivalence* of fibres and
says explicitly that it is not an isometry until `cov` is assumed metric — the fibres need no
norm for `≃L[ℝ]` to elaborate, and none appears there. This file assumes metric compatibility
and upgrades the equivalence to a `≃ₗᵢ[ℝ]`.

**Mathlib names this as future work**: the header of
`VectorBundle/CovariantDerivative/Metric.lean` lists "when Mathlib has a notion of parallel
transport, prove the equivalence of `IsMetricCompatible` with the characterisation that
parallel transport be an isometry". One direction of that is proved here.

**What it costs is one Leibniz rule.** `hasDerivAt_inner_along` says
`d/dt ⟪V,W⟫ = ⟪D/dt V, W⟫ + ⟪V, D/dt W⟫`, and everything else is immediate: along a parallel
pair the derivative vanishes, so the pairing is constant, so norms are preserved, so the
transport map is an isometry. The Leibniz rule itself is the frame-expansion argument of
`CovariantAlongCurve.lean` used once more — expand both sections in (possibly *different*)
local frames, differentiate the resulting double sum of products, and read the frame
pairings' derivatives off metric compatibility. The two frames need not be the same one, and
neither needs to be orthonormal or parallel: every term matches on the nose.

**Why this is wanted.** A maximum principle on a non-trivial bundle compares
`dist(u(t,x), K_x)` between *different* fibres, and there is nothing to compare unless the
identification between them preserves the metric. `BundleMaximumPrinciple.lean` closes the
touching-point half of that argument; this is the first brick of the cross-fibre half.
-/
import RicciFlowBlueprint.ParallelTransport
import RicciFlowBlueprint.Bochner

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

section Algebra

/-! ### Two algebraic identities, stated over a bare inner product space

Both are pure bilinearity, and both are stated here rather than inline for the documented
reason: a `Finset.sum` over `Π t, T_{γ t}M` picks an `AddCommMonoid` only *defeq* to the one
the fibre's own instances produce, so `rw` with `sum_inner` fails on a goal that prints
correctly. Stated over a variable `F` and applied with `exact`, the same steps go through up
to definitional equality. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Bilinearity against two frames: `⟪∑ᵢ fᵢ Aᵢ, ∑ⱼ gⱼ Bⱼ⟫ = ∑ᵢⱼ fᵢ gⱼ ⟪Aᵢ,Bⱼ⟫`. -/
theorem inner_sum_smul_sum (f : ι → ℝ) (g : κ → ℝ) (A : ι → F) (B : κ → F) :
    ⟪∑ i, f i • A i, ∑ j, g j • B j⟫ = ∑ i, ∑ j, f i * g j * ⟪A i, B j⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [real_inner_smul_right]
  ring

/-- The shape the Leibniz rule produces: the two pairings of a differentiated frame expansion
against an undifferentiated one, added, reorganised as one double sum whose summand is the
product rule. -/
theorem inner_expansion_add (f f' : ι → ℝ) (g g' : κ → ℝ)
    (A a : ι → F) (B b : κ → F) :
    ⟪∑ i, (f i • a i + f' i • A i), ∑ j, g j • B j⟫
      + ⟪∑ i, f i • A i, ∑ j, (g j • b j + g' j • B j)⟫
      = ∑ i, ∑ j, (f' i * g j * ⟪A i, B j⟫ + f i * g' j * ⟪A i, B j⟫
          + f i * g j * (⟪a i, B j⟫ + ⟪A i, b j⟫)) := by
  rw [sum_inner, sum_inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_sum, inner_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

end Algebra

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  {γ : ℝ → M} {V V' : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}

section Leibniz

omit [T2Space M] in
/-- Metric compatibility at a bare tangent vector rather than along a vector field. Mathlib's
`IsMetricCompatible.mvfderiv_inner_eq` quantifies over a field `X` but uses only `X x`, so a
`FiberBundle.extend` of the vector discharges it. -/
theorem mvfderiv_inner_eq_apply
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {σ τ : Π y : M, TangentSpace I y} {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ⟪σ y, τ y⟫) x v = ⟪cov σ x v, τ x⟫ + ⟪σ x, cov τ x v⟫ := by
  have h := hmet.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y)
    (FiberBundle.extend E v) hσ hτ
  simp only [FiberBundle.extend_apply_self] at h
  exact h

-- BENCH: transport-leibniz
/-- **The Leibniz rule for `D/dt` against the metric**:
`d/dt ⟪V,W⟫ = ⟪D/dt V, W⟫ + ⟪V, D/dt W⟫` for a metric connection.

Both sections are expanded in local frames by `exists_frame_expansion` — **not necessarily
the same frame**, and neither orthonormal nor parallel. The pairing becomes a double sum
`∑ᵢⱼ fᵢ gⱼ ⟪Aᵢ∘γ, Bⱼ∘γ⟫`; the product rule contributes the `fᵢ'` and `gⱼ'` terms, which are
exactly the coordinate parts of `D/dt V` and `D/dt W`, and metric compatibility contributes
the derivative of each frame pairing, which is exactly the connection parts. Nothing is left
over, which is why no hypothesis on the frames is needed. -/
theorem hasDerivAt_inner_along
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t)
    (hV' : MDiffAlongAt γ V' t) :
    HasDerivAt (fun u ↦ ⟪V u, V' u⟫)
      (⟪covAlong cov γ V t, V' t⟫ + ⟪V t, covAlong cov γ V' t⟫) t := by
  classical
  obtain ⟨ι, _, A, f, hA, hf, hVexp⟩ := exists_frame_expansion hγ hV
  obtain ⟨κ, _, B, g, hB, hg, hV'exp⟩ := exists_frame_expansion hγ hV'
  have hAm : ∀ i, MDiffAt (T% (A i)) (γ t) := fun i ↦ (hA i).mdifferentiable one_ne_zero (γ t)
  have hBm : ∀ j, MDiffAt (T% (B j)) (γ t) := fun j ↦ (hB j).mdifferentiable one_ne_zero (γ t)
  -- the derivative of a frame pairing, by metric compatibility
  have hpd : ∀ i j, HasDerivAt (fun u ↦ (⟪A i (γ u), B j (γ u)⟫ : ℝ))
      (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
        + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫) t := by
    intro i j
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ ⟪A i y, B j y⟫) (γ t) :=
      (hAm i).inner_bundle' (hBm j)
    have hdiff : DifferentiableAt ℝ (fun u ↦ (⟪A i (γ u), B j (γ u)⟫ : ℝ)) t := by
      rw [← mdifferentiableAt_iff_differentiableAt]
      exact hmd.comp t hγ
    have hval : deriv (fun u ↦ (⟪A i (γ u), B j (γ u)⟫ : ℝ)) t
        = ⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
          + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫ := by
      rw [deriv_comp_curve hmd hγ, mvfderiv_inner_eq_apply cov hmet (hAm i) (hBm j)]
    exact hval ▸ hdiff.hasDerivAt
  -- the pairing, expanded
  have hexp : (fun u ↦ (⟪V u, V' u⟫ : ℝ)) =ᶠ[𝓝 t]
      fun u ↦ ∑ i, ∑ j, f i u * g j u * ⟪A i (γ u), B j (γ u)⟫ := by
    filter_upwards [hVexp, hV'exp] with u hu hu'
    rw [hu, hu']
    exact inner_sum_smul_sum (F := TangentSpace I (γ u)) _ _ _ _
  have hd : HasDerivAt (fun u ↦ ∑ i, ∑ j, f i u * g j u * ⟪A i (γ u), B j (γ u)⟫)
      (∑ i, ∑ j, (deriv (f i) t * g j t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * deriv (g j) t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
          + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫))) t := by
    refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ ?_
    have h := ((hf i).hasDerivAt.mul (hg j).hasDerivAt).mul (hpd i j)
    have e : (deriv (f i) t * g j t + f i t * deriv (g j) t) * ⟪A i (γ t), B j (γ t)⟫
          + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
            + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫)
        = deriv (f i) t * g j t * ⟪A i (γ t), B j (γ t)⟫
          + f i t * deriv (g j) t * ⟪A i (γ t), B j (γ t)⟫
          + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
            + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫) := by ring
    exact e ▸ h
  have hmain := hd.congr_of_eventuallyEq hexp
  have hVc : covAlong cov γ V t
      = ∑ i, (f i t • cov (A i) (γ t) (velocity γ t) + deriv (f i) t • A i (γ t)) :=
    (isCovDerivAlong_covAlong cov γ).eq_sum_of_expansion hγ hV hγ hA hf hVexp
  have hV'c : covAlong cov γ V' t
      = ∑ j, (g j t • cov (B j) (γ t) (velocity γ t) + deriv (g j) t • B j (γ t)) :=
    (isCovDerivAlong_covAlong cov γ).eq_sum_of_expansion hγ hV' hγ hB hg hV'exp
  have hVt : V t = ∑ i, f i t • A i (γ t) := hVexp.eq_of_nhds
  have hV't : V' t = ∑ j, g j t • B j (γ t) := hV'exp.eq_of_nhds
  have hvalue : ⟪covAlong cov γ V t, V' t⟫ + ⟪V t, covAlong cov γ V' t⟫
      = ∑ i, ∑ j, (deriv (f i) t * g j t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * deriv (g j) t * ⟪A i (γ t), B j (γ t)⟫
        + f i t * g j t * (⟪cov (A i) (γ t) (velocity γ t), B j (γ t)⟫
          + ⟪A i (γ t), cov (B j) (γ t) (velocity γ t)⟫)) := by
    rw [hVc, hV'c, hVt, hV't]
    exact inner_expansion_add (F := TangentSpace I (γ t)) (fun i ↦ f i t)
      (fun i ↦ deriv (f i) t) (fun j ↦ g j t) (fun j ↦ deriv (g j) t)
      (fun i ↦ A i (γ t)) (fun i ↦ cov (A i) (γ t) (velocity γ t))
      (fun j ↦ B j (γ t)) (fun j ↦ cov (B j) (γ t) (velocity γ t))
  rw [hvalue]
  exact hmain

end Leibniz

section Constant

variable {a c : ℝ}

-- BENCH: transport-inner-const
/-- **A metric connection transports parallel sections with their pairing intact**: for `V`
and `V'` parallel along `γ` on `[a,c]`, `⟪V,V'⟫` is constant there.

The Leibniz rule makes the derivative `⟪0,V'⟫ + ⟪V,0⟫`; the rest is
`constant_of_has_deriv_right_zero`. -/
theorem inner_eq_of_isParallelAlong
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hγ : ∀ u ∈ Icc a c, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hV : ∀ u ∈ Icc a c, MDiffAlongAt γ V u) (hV' : ∀ u ∈ Icc a c, MDiffAlongAt γ V' u)
    (hPV : IsParallelAlong cov γ V (Icc a c)) (hPV' : IsParallelAlong cov γ V' (Icc a c))
    {u : ℝ} (hu : u ∈ Icc a c) :
    ⟪V u, V' u⟫ = ⟪V a, V' a⟫ := by
  have key : ∀ r ∈ Icc a c, HasDerivAt (fun y ↦ (⟪V y, V' y⟫ : ℝ)) 0 r := by
    intro r hr
    have h := hasDerivAt_inner_along cov hmet (hγ r hr) (hV r hr) (hV' r hr)
    rwa [hPV r hr, hPV' r hr, inner_zero_left, inner_zero_right, add_zero] at h
  exact constant_of_has_deriv_right_zero
    (fun r hr ↦ (key r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (key r (Ico_subset_Icc_self hr)).hasDerivWithinAt) u hu

/-- **Parallel transport preserves lengths.** -/
theorem norm_eq_of_isParallelAlong
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hγ : ∀ u ∈ Icc a c, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hV : ∀ u ∈ Icc a c, MDiffAlongAt γ V u)
    (hPV : IsParallelAlong cov γ V (Icc a c))
    {u : ℝ} (hu : u ∈ Icc a c) :
    ‖V u‖ = ‖V a‖ := by
  have h := inner_eq_of_isParallelAlong cov hmet hγ hV hV hPV hPV hu
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (V u), norm_nonneg (V a)]

end Constant

section Isometry

variable [CompleteSpace E]

set_option maxSynthPendingDepth 3

variable [ContMDiffCovariantDerivative cov 1]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
  [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
  {W : ι → Π y : M, TangentSpace I y} {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
  (hW : ∀ i, CMDiff 2 (T% (W i))) (hWU : ∀ i, ∀ y ∈ U, W i y = e.localFrame b i y)
  {s : Set ℝ} (hs : IsOpen s)
  (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
  (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
  (hγU : ∀ u ∈ s, γ u ∈ U)
  {a c : ℝ} (hac : a ≤ c) (hsub : Icc a c ⊆ s)

include hU hUe hW hWU hs hγ hγv hγU hac hsub in
-- BENCH: transport-isometry
/-- **Parallel transport is a linear ISOMETRY of the fibres**, for a metric connection.

`exists_parallelTransportEquiv` gives the continuous linear equivalence with no metric
anywhere; the only thing added here is that it preserves norms, which is
`norm_eq_of_isParallelAlong` applied to the parallel section through each vector —
`exists_isParallelAlong` being what supplies that section. -/
theorem exists_parallelTransportIsometry
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a c) {t : ℝ} (ht : t ∈ Icc a c) :
    ∃ P : TangentSpace I (γ t₀) ≃ₗᵢ[ℝ] TangentSpace I (γ t),
      ∀ V : Π u : ℝ, TangentSpace I (γ u), (∀ u ∈ Icc a c, MDiffAlongAt γ V u) →
        IsParallelAlong cov γ V (Icc a c) → V t = P (V t₀) := by
  obtain ⟨P, hP⟩ := exists_parallelTransportEquiv cov b hU hUe hW hWU hγ hγv hγU hac hsub ht₀ ht
  have ht₀' : t₀ ∈ Icc a c := Ioo_subset_Icc_self ht₀
  have hγ' : ∀ u ∈ Icc a c, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u := fun u hu ↦ hγ u (hsub hu)
  have hnorm : ∀ v : TangentSpace I (γ t₀), ‖P v‖ = ‖v‖ := by
    intro v
    obtain ⟨V, hVt₀, hVd, hVp⟩ :=
      exists_isParallelAlong cov b hU hUe hW hWU hs hγ hγv hγU hac hsub ht₀' v
    have h1 : ‖V t‖ = ‖V a‖ := norm_eq_of_isParallelAlong cov hmet hγ' hVd hVp ht
    have h2 : ‖V t₀‖ = ‖V a‖ := norm_eq_of_isParallelAlong cov hmet hγ' hVd hVp ht₀'
    rw [← hVt₀, ← hP V hVd hVp, h1, ← h2]
  exact ⟨{ P.toLinearEquiv with norm_map' := hnorm }, fun V hVd hVp ↦ hP V hVd hVp⟩

end Isometry

end CovariantDerivative
