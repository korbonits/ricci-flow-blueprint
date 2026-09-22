/-
**The covariant derivative along a curve, for a section of a general vector bundle.**

`CovariantAlongCurve.lean` builds `D/dt` for a section of `TM`, which is what geodesics and
`TM`-parallel transport need. The cross-fibre half of the maximum principle needs it one
level up: the tested object is a section of a tensor bundle --- in dimension three, of
`End(TM)` --- and the direction it is tested against has to be carried between *fibres of
that bundle*, not of `TM`.

**Nothing in the construction is about the tangent bundle.** The *direction* stays there ---
`velocity γ t` is a tangent vector and `cov σ y` is a map out of `T_yM` --- but the section
being differentiated, and the fibres it takes values in, are arbitrary. So this file is the
port `BundleHessian.lean` was, with the same discipline: **no fibre norm is bound**, only
mathlib's standard general-bundle binders, and the tangent-bundle statements come back by
`rfl` (`mdiffAlongSectionAt_eq_mdiffAlongAt`, `isCovDerivAlongSection_eq_isCovDerivAlong`).

One thing does change shape. `Π t, V (γ t)` is a *dependent* Pi, so `Filter.EventuallyEq`
does not typecheck on it and every germ hypothesis is a bare `∀ᶠ u in 𝓝 t, σ u = τ u` ---
the same adjustment `GlobalExtension.lean` documents, for the same reason.

Argument order follows `CovariantDerivative`: `cov σ y (X y)` is `(∇_X σ) y` on paper.
-/
import RicciFlowBlueprint.CovariantAlongCurve

open Bundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]

variable (I F V) in
/-- **A section of `V` along `γ` is differentiable at `t`** when its lift to the total space
is. The general-bundle form of `MDiffAlongAt`; the model fibre has to be named, `T% σ` being
unable to infer it for a bundle other than `TM`. -/
def MDiffAlongSectionAt (γ : ℝ → M) (σ : Π t : ℝ, V (γ t)) (t : ℝ) : Prop :=
  MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
    (fun u ↦ (⟨γ u, σ u⟩ : TotalSpace F V)) t

/-- **The covariant derivative along a curve, on a general bundle**, as a predicate. The three
axioms are the ones `IsCovDerivAlong` carries: additive, Leibniz over a scalar function of the
parameter, and agreement with `cov` on the restriction of a global section. Only the *last*
mentions the tangent bundle, and only through the direction `γ'(t)`. -/
structure IsCovDerivAlongSection
    (cov : CovariantDerivative I F V) (γ : ℝ → M)
    (D : (Π t : ℝ, V (γ t)) → (Π t : ℝ, V (γ t)))
    (s : Set ℝ := Set.univ) : Prop where
  add {σ τ : Π t : ℝ, V (γ t)} {t : ℝ}
    (hσ : MDiffAlongSectionAt I F V γ σ t) (hτ : MDiffAlongSectionAt I F V γ τ t)
    (ht : t ∈ s := by trivial) :
    D (σ + τ) t = D σ t + D τ t
  leibniz {σ : Π t : ℝ, V (γ t)} {f : ℝ → ℝ} {t : ℝ}
    (hσ : MDiffAlongSectionAt I F V γ σ t) (hf : DifferentiableAt ℝ f t)
    (ht : t ∈ s := by trivial) :
    D (f • σ) t = f t • D σ t + deriv f t • σ t
  restrict {W : Π y : M, V y} {t : ℝ}
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun y ↦ (⟨y, W y⟩ : TotalSpace F V)) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s := by trivial) :
    D (fun u ↦ W (γ u)) t = cov W (γ t) (velocity γ t)

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [ContMDiffVectorBundle 1 F V I] in
/-- The zero section along a differentiable curve is differentiable. -/
theorem MDiffAlongSectionAt.zero_section {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDiffAlongSectionAt I F V γ (0 : Π t : ℝ, V (γ t)) t :=
  ((contMDiff_zeroSection (n := 1) ℝ V).mdifferentiable (by norm_num) (γ t)).comp t hγ

variable {cov : CovariantDerivative I F V} {γ : ℝ → M}
  {D D' : (Π t : ℝ, V (γ t)) → (Π t : ℝ, V (γ t))} {s : Set ℝ}

omit [IsManifold I ω M] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] in
/-- The predicate is monotone in the parameter set. -/
theorem IsCovDerivAlongSection.mono {s' : Set ℝ} (h : IsCovDerivAlongSection cov γ D s')
    (hss' : s ⊆ s') : IsCovDerivAlongSection cov γ D s where
  add hσ hτ ht := h.add hσ hτ (hss' ht)
  leibniz hσ hf ht := h.leibniz hσ hf (hss' ht)
  restrict hW hγ ht := h.restrict hW hγ (hss' ht)

omit [IsManifold I ω M] [ContMDiffVectorBundle 1 F V I] in
/-- `D` kills the zero section: Leibniz with the zero coefficient. -/
theorem IsCovDerivAlongSection.zero (h : IsCovDerivAlongSection cov γ D s) {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s) :
    D 0 t = 0 := by
  have hz : ((fun _ : ℝ ↦ (0 : ℝ)) • (0 : Π t : ℝ, V (γ t)))
      = (0 : Π t : ℝ, V (γ t)) := by
    funext u; simp
  have hL := h.leibniz (f := fun _ : ℝ ↦ (0 : ℝ))
    (MDiffAlongSectionAt.zero_section hγ) (differentiableAt_const (0 : ℝ)) ht
  rw [hz] at hL
  simpa using hL

omit [IsManifold I ω M] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] in
-- BENCH: bundle-cov-along-curve-local
/-- **`D` is local**: it depends on a section only through its germ. Not an axiom --- the same
bump-function argument as on `TM`, and it does not notice the change of bundle: `f • σ = f • τ`
*globally* for a bump `f` supported where they agree, while Leibniz evaluates both sides at `t`
because `f t = 1` and `deriv f t = 0`. -/
theorem IsCovDerivAlongSection.congr_of_eventuallyEq (h : IsCovDerivAlongSection cov γ D s)
    {σ τ : Π t : ℝ, V (γ t)} {t : ℝ}
    (hσ : MDiffAlongSectionAt I F V γ σ t) (hτ : MDiffAlongSectionAt I F V γ τ t) (ht : t ∈ s)
    (hστ : ∀ᶠ u in 𝓝 t, σ u = τ u) :
    D σ t = D τ t := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hστ
  set b : ContDiffBump t := ⟨ε / 3, ε / 2, by positivity, by linarith⟩ with hb
  have hf1 : b t = 1 := b.one_of_mem_closedBall (by simp [Metric.mem_closedBall]; positivity)
  have hfnear : (fun u ↦ b u) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds t (by positivity : (0 : ℝ) < ε / 3)] with u hu
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
  have hfd : DifferentiableAt ℝ (fun u ↦ b u) t :=
    (b.contDiff (n := 1)).differentiable (by norm_num) t
  have hderiv : deriv (fun u ↦ b u) t = 0 := by
    rw [hfnear.deriv_eq, deriv_const]
  have hsm : ((fun u ↦ b u) • σ) = ((fun u ↦ b u) • τ) := by
    funext u
    by_cases hu : b u = 0
    · simp [hu]
    · have humem : u ∈ Metric.ball t ε := by
        have hu2 : u ∈ Metric.ball t (ε / 2) := by
          rw [← b.support_eq]; exact Function.mem_support.mpr hu
        exact Metric.ball_subset_ball (by linarith) hu2
      show b u • σ u = b u • τ u
      rw [hball u humem]
  have eσ := h.leibniz hσ hfd ht
  have eτ := h.leibniz hτ hfd ht
  rw [hsm] at eσ
  rw [eσ] at eτ
  rw [hf1, hderiv] at eτ
  simpa using eτ


section Frame

/-! ### Local frames along a curve

Uniqueness of `D/dt` rests on the same fact as on `TM`: near `t` a section of `V` along `γ`
is a finite combination `σ = ∑ᵢ fᵢ · (Wᵢ ∘ γ)` of restrictions of *global* sections of `V`,
with `fᵢ` differentiable. The frame is mathlib's `Trivialization.localFrame` for the bundle at
hand; the coefficients are read off the same trivialisation, which is what makes them
differentiable; and the frame is globalised by `exists_contMDiff_eventuallyEq_of_bundle`.
-/

variable {σ τ : Π t : ℝ, V (γ t)} {t : ℝ}

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] in
/-- **Differentiability along `γ` is differentiability of the fibre coordinate** in any
trivialisation of `V` around `γ t`. -/
theorem mdiffAlongSectionAt_iff_of_mem
    {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (he : γ t ∈ e.baseSet) :
    MDiffAlongSectionAt I F V γ σ t ↔ DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, σ u⟩).2) t := by
  rw [MDiffAlongSectionAt, e.mdifferentiableAt_totalSpace_iff I _ (e.mem_source.mpr he),
    ← mdifferentiableAt_iff_differentiableAt]
  exact and_iff_right hγ

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] in
omit [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module ℝ (V x)] in
/-- The restriction of a globally `C¹` section to a differentiable curve is differentiable
along it. -/
theorem MDiffAlongSectionAt.of_section {W : Π y : M, V y}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y ↦ (⟨y, W y⟩ : TotalSpace F V)))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDiffAlongSectionAt I F V γ (fun u ↦ W (γ u)) t :=
  (hW.mdifferentiable (by norm_num) (γ t)).comp t hγ

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] in
/-- Sections along `γ` add. -/
theorem MDiffAlongSectionAt.add (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hσ : MDiffAlongSectionAt I F V γ σ t) (hτ : MDiffAlongSectionAt I F V γ τ t) :
    MDiffAlongSectionAt I F V γ (σ + τ) t := by
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hmem)
  rw [mdiffAlongSectionAt_iff_of_mem hγ hmem] at hσ hτ ⊢
  refine (hσ.add hτ).congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with u hu
  show (e ⟨γ u, σ u + τ u⟩).2 = (e ⟨γ u, σ u⟩).2 + (e ⟨γ u, τ u⟩).2
  exact map_add (e.continuousLinearEquivAt ℝ (γ u) hu) (σ u) (τ u)

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] in
/-- Sections along `γ` scale by differentiable functions of the parameter. -/
theorem MDiffAlongSectionAt.smul {f : ℝ → ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hf : DifferentiableAt ℝ f t) (hσ : MDiffAlongSectionAt I F V γ σ t) :
    MDiffAlongSectionAt I F V γ (f • σ) t := by
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hmem)
  rw [mdiffAlongSectionAt_iff_of_mem hγ hmem] at hσ ⊢
  refine (hf.smul hσ).congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with u hu
  show (e ⟨γ u, f u • σ u⟩).2 = f u • (e ⟨γ u, σ u⟩).2
  exact map_smul (e.continuousLinearEquivAt ℝ (γ u) hu) (f u) (σ u)

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] in
/-- Finite sums of sections along `γ`, taken **fibrewise**: `Finset.sum` over the Pi type
`Π t, V (γ t)` picks an `AddCommMonoid` only defeq to the one `Fintype.sum_apply` produces,
and no `rw` crosses that gap. -/
theorem MDiffAlongSectionAt.sum {ι : Type*} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (a : Finset ι) {σs : ι → Π t : ℝ, V (γ t)}
    (hσ : ∀ i ∈ a, MDiffAlongSectionAt I F V γ (σs i) t) :
    MDiffAlongSectionAt I F V γ (fun u ↦ ∑ i ∈ a, σs i u) t := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (fun u ↦ ∑ i ∈ (∅ : Finset ι), σs i u) = (0 : Π t : ℝ, V (γ t)) := by
      funext u; exact Finset.sum_empty
    rw [h0]
    exact MDiffAlongSectionAt.zero_section hγ
  | insert c a hc ih =>
    have hstep : (fun u ↦ ∑ i ∈ insert c a, σs i u)
        = σs c + fun u ↦ ∑ i ∈ a, σs i u := by
      funext u
      show ∑ i ∈ insert c a, σs i u = σs c u + ∑ i ∈ a, σs i u
      exact Finset.sum_insert hc
    rw [hstep]
    exact (hσ c (Finset.mem_insert_self c a)).add hγ
      (ih fun i hi ↦ hσ i (Finset.mem_insert_of_mem hi))


variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M]

omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
-- BENCH: bundle-cov-along-curve-frame-expansion
/-- **A section of `V` along `γ` is, near `t`, a finite combination of restrictions of globally
`C¹` sections of `V`, with differentiable coefficients.** This is what pins `D/dt` down.

Everything is read off one trivialisation of `V` around `γ t`; the conclusion is a bare
`∀ᶠ`, `Π t, V (γ t)` being a dependent Pi. -/
theorem exists_frame_expansion_section (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hσ : MDiffAlongSectionAt I F V γ σ t) :
    ∃ (ι : Type) (_ : Fintype ι) (W : ι → Π y : M, V y) (f : ι → ℝ → ℝ),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y ↦ (⟨y, W i y⟩ : TotalSpace F V))) ∧
      (∀ i, DifferentiableAt ℝ (f i) t) ∧
      ∀ᶠ u in 𝓝 t, σ u = ∑ i, f i u • W i (γ u) := by
  classical
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  set b := Module.finBasis ℝ F with hb
  have hcoord : DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, σ u⟩).2) t :=
    (mdiffAlongSectionAt_iff_of_mem hγ hmem).mp hσ
  have hloc : ∀ i, ∃ ρ : Π y : M, V y,
      ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y ↦ (⟨y, ρ y⟩ : TotalSpace F V)) ∧
        ∀ᶠ y in 𝓝 (γ t), ρ y = e.localFrame b i y := fun i ↦
    RicciFlowBlueprint.exists_contMDiff_eventuallyEq_of_bundle (I := I) F (V := V) (n := 1)
      (e.open_baseSet.mem_nhds hmem) (e.contMDiffOn_localFrame_baseSet 1 b i)
  choose W hW hWeq using hloc
  refine ⟨_, inferInstance, W, fun i u ↦ b.repr (e ⟨γ u, σ u⟩).2 i, hW, fun i ↦ ?_, ?_⟩
  · exact (((b.coord i).toContinuousLinearMap).differentiableAt).comp t hcoord
  have hrepr : ∀ (y : M) (hy : y ∈ e.baseSet) (v : V y) (i),
      (e.basisAt b hy).repr v i = b.repr (e ⟨y, v⟩).2 i := by
    intro y hy v i
    simp [Trivialization.basisAt]
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hmem)
  have hall : ∀ᶠ u in 𝓝 t, ∀ i, W i (γ u) = e.localFrame b i (γ u) :=
    Filter.eventually_all.mpr fun i ↦ hγ.continuousAt.eventually (hWeq i)
  filter_upwards [hnhds, hall] with u hu hWu
  refine ((e.basisAt b hu).sum_repr (σ u)).symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  show (e.basisAt b hu).repr (σ u) i • (e.basisAt b hu) i
      = b.repr (e ⟨γ u, σ u⟩).2 i • W i (γ u)
  rw [hrepr (γ u) hu (σ u) i, hWu i, e.localFrame_apply_of_mem_baseSet b hu]


omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ω M] in
-- BENCH: bundle-cov-along-curve-sum
/-- `D` is additive over finite sums, by induction from the `add` axiom. -/
theorem IsCovDerivAlongSection.sum (h : IsCovDerivAlongSection cov γ D s)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s) {ι : Type*} (a : Finset ι)
    {σs : ι → Π t : ℝ, V (γ t)} (hσ : ∀ i ∈ a, MDiffAlongSectionAt I F V γ (σs i) t) :
    D (fun u ↦ ∑ i ∈ a, σs i u) t = ∑ i ∈ a, D (σs i) t := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (fun u ↦ ∑ i ∈ (∅ : Finset ι), σs i u) = (0 : Π t : ℝ, V (γ t)) := by
      funext u; exact Finset.sum_empty
    rw [h0, Finset.sum_empty]
    exact h.zero hγ ht
  | insert c a hc ih =>
    have hstep : (fun u ↦ ∑ i ∈ insert c a, σs i u)
        = σs c + fun u ↦ ∑ i ∈ a, σs i u := by
      funext u
      show ∑ i ∈ insert c a, σs i u = σs c u + ∑ i ∈ a, σs i u
      exact Finset.sum_insert hc
    rw [hstep, h.add (hσ c (Finset.mem_insert_self c a))
      (MDiffAlongSectionAt.sum hγ a fun i hi ↦ hσ i (Finset.mem_insert_of_mem hi)) ht,
      ih fun i hi ↦ hσ i (Finset.mem_insert_of_mem hi), Finset.sum_insert hc]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ω M] in
-- BENCH: bundle-cov-along-curve-expansion-value
/-- **`D/dt` is computed by any local expansion.** If `σ = ∑ᵢ fᵢ · (Wᵢ ∘ γ)` near `t` with
`Wᵢ` global `C¹` sections of `V` and `fᵢ` differentiable, then
`D σ t = ∑ᵢ (fᵢ(t)·∇_{γ'}Wᵢ + fᵢ'(t)·Wᵢ(γ t))`, an expression in which `D` no longer occurs. -/
theorem IsCovDerivAlongSection.eq_sum_of_expansion (h : IsCovDerivAlongSection cov γ D s)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hσ : MDiffAlongSectionAt I F V γ σ t) (ht : t ∈ s)
    {ι : Type*} [Fintype ι] {W : ι → Π y : M, V y} {f : ι → ℝ → ℝ}
    (hW : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y ↦ (⟨y, W i y⟩ : TotalSpace F V)))
    (hf : ∀ i, DifferentiableAt ℝ (f i) t)
    (hexp : ∀ᶠ u in 𝓝 t, σ u = ∑ i, f i u • W i (γ u)) :
    D σ t = ∑ i, (f i t • cov (W i) (γ t) (velocity γ t) + deriv (f i) t • W i (γ t)) := by
  classical
  set σs : ι → Π u : ℝ, V (γ u) := fun i ↦ (f i) • fun u ↦ W i (γ u) with hσs
  have hexp' : ∀ᶠ u in 𝓝 t, σ u = ∑ i ∈ Finset.univ, σs i u := hexp
  have hWγ : ∀ i, MDiffAlongSectionAt I F V γ (fun u ↦ W i (γ u)) t := fun i ↦
    MDiffAlongSectionAt.of_section (hW i) hγ
  have hterm : ∀ i, MDiffAlongSectionAt I F V γ (σs i) t := fun i ↦ (hWγ i).smul hγ (hf i)
  have hsum : MDiffAlongSectionAt I F V γ (fun u ↦ ∑ i ∈ Finset.univ, σs i u) t :=
    MDiffAlongSectionAt.sum hγ Finset.univ fun i _ ↦ hterm i
  rw [h.congr_of_eventuallyEq hσ hsum ht hexp', h.sum hγ ht Finset.univ fun i _ ↦ hterm i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hσs, h.leibniz (hWγ i) (hf i) ht,
    h.restrict ((hW i).mdifferentiable (by norm_num) (γ t)) hγ ht]

-- BENCH: bundle-cov-along-curve-unique
/-- **`D/dt` is determined by the ambient connection**, on any bundle. Two operators
satisfying the three axioms agree on every section differentiable along `γ`: both are
computed by the frame expansion, which mentions neither. -/
theorem IsCovDerivAlongSection.eq_of_isCovDerivAlongSection
    (h : IsCovDerivAlongSection cov γ D s) (h' : IsCovDerivAlongSection cov γ D' s)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hσ : MDiffAlongSectionAt I F V γ σ t) (ht : t ∈ s) :
    D σ t = D' σ t := by
  obtain ⟨ι, _, W, f, hW, hf, hexp⟩ := exists_frame_expansion_section hγ hσ
  rw [h.eq_sum_of_expansion hγ hσ ht hW hf hexp, h'.eq_sum_of_expansion hγ hσ ht hW hf hexp]

end Frame


section Tangent

/-! ### The tangent-bundle case

The falsification check: at `V = TM` the general definitions **are** the ones
`CovariantAlongCurve.lean` works with, and the bridges are `rfl`. Without this the general
statements would be unfalsified --- they would typecheck without anything saying they mean
what they are supposed to mean. -/

variable (I) in
theorem mdiffAlongSectionAt_eq_mdiffAlongAt (γ : ℝ → M)
    (σ : Π t : ℝ, TangentSpace I (γ t)) (t : ℝ) :
    MDiffAlongSectionAt I E (fun y : M ↦ TangentSpace I y) γ σ t = MDiffAlongAt γ σ t := rfl

variable (I) in
/-- The two predicates have the **same three fields**, each stated at a type the other bridge
says is the same: the axioms of `IsCovDerivAlong` are exactly what `IsCovDerivAlongSection`
asks at `V = TM`, so the equivalence destructures and reassembles with nothing in between.
(A bare `rfl` is unavailable only because the two are distinct structures, not because
anything differs.) -/
theorem isCovDerivAlongSection_iff_isCovDerivAlong
    (cov : CovariantDerivative I E (fun y : M ↦ TangentSpace I y)) (γ : ℝ → M)
    (D : (Π t : ℝ, TangentSpace I (γ t)) → (Π t : ℝ, TangentSpace I (γ t))) (s : Set ℝ) :
    IsCovDerivAlongSection cov γ D s ↔ IsCovDerivAlong cov γ D s :=
  ⟨fun h ↦ ⟨fun hσ hτ ht ↦ h.add hσ hτ ht, fun hσ hf ht ↦ h.leibniz hσ hf ht,
      fun hW hγ ht ↦ h.restrict hW hγ ht⟩,
    fun h ↦ ⟨fun hσ hτ ht ↦ h.add hσ hτ ht, fun hσ hf ht ↦ h.leibniz hσ hf ht,
      fun hW hγ ht ↦ h.restrict hW hγ ht⟩⟩

end Tangent

end CovariantDerivative
