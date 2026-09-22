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
import RicciFlowBlueprint.BundleNormalSection

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
    (hW : MDiffAt (T% W) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s := by trivial) :
    D (fun u ↦ W (γ u)) t = cov W (γ t) (velocity γ t)

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle 1 F V I] in
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

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
/-- **Differentiability along `γ` is differentiability of the fibre coordinate** in any
trivialisation of `V` around `γ t`. -/
theorem mdiffAlongSectionAt_iff_of_mem
    {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (he : γ t ∈ e.baseSet) :
    MDiffAlongSectionAt I F V γ σ t ↔ DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, σ u⟩).2) t := by
  rw [MDiffAlongSectionAt, e.mdifferentiableAt_totalSpace_iff I _ (e.mem_source.mpr he),
    ← mdifferentiableAt_iff_differentiableAt]
  exact and_iff_right hγ

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] [∀ x : M, AddCommGroup (V x)]
  [∀ x : M, Module ℝ (V x)] in
/-- The restriction of a globally `C¹` section to a differentiable curve is differentiable
along it. -/
theorem MDiffAlongSectionAt.of_section {W : Π y : M, V y}
    (hW : CMDiff (1 : ℕ∞ω) (T% W))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDiffAlongSectionAt I F V γ (fun u ↦ W (γ u)) t :=
  (hW.mdifferentiable (by norm_num) (γ t)).comp t hγ

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
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

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
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

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
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
      (∀ i, CMDiff (1 : ℕ∞ω) (T% (W i))) ∧
      (∀ i, DifferentiableAt ℝ (f i) t) ∧
      ∀ᶠ u in 𝓝 t, σ u = ∑ i, f i u • W i (γ u) := by
  classical
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  set b := Module.finBasis ℝ F with hb
  have hcoord : DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, σ u⟩).2) t :=
    (mdiffAlongSectionAt_iff_of_mem hγ hmem).mp hσ
  have hloc : ∀ i, ∃ ρ : Π y : M, V y,
      CMDiff (1 : ℕ∞ω) (T% ρ) ∧
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
    (hW : ∀ i, CMDiff (1 : ℕ∞ω) (T% (W i)))
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


section Existence

/-! ### Existence

`D/dt` is built in the trivialisation of `V` at `γ t`: differentiate the fibre coordinates of
`σ` and add the connection's own contribution on the frame. Additivity and the Leibniz rule are
then the corresponding facts about `deriv`; the third axiom is the only one with content, and
it is `cov`'s Leibniz rule applied to the local-frame expansion of a global section.

Existence is what stops `IsParallelAlongSection` being vacuous: quantified over operators
satisfying the axioms, a vanishing condition on an *empty* class of operators is trivially
true, and that is the repository's worst class of error. -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M]

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] in
/-- The fibre basis a trivialisation of `V` induces is the model basis read through it. -/
theorem repr_basisAt_eq_section
    {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ F) {y : M} (hy : y ∈ e.baseSet) (v : V y) (i : ι) :
    (e.basisAt b hy).repr v i = b.repr (e ⟨y, v⟩).2 i := by
  simp [Trivialization.basisAt]

omit [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] in
/-- **The local frame reconstructs a fibre vector** from its coordinates. -/
theorem sum_repr_smul_localFrame_section
    {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F) {y : M} (hy : y ∈ e.baseSet) (v : V y) :
    ∑ i, b.repr (e ⟨y, v⟩).2 i • e.localFrame b i y = v := by
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) ((e.basisAt b hy).sum_repr v)
  rw [e.localFrame_apply_of_mem_baseSet b hy, ← repr_basisAt_eq_section b hy v i]

variable (I F V) in
/-- **The canonical frame of `V` at `x`**: a globally `C¹` section agreeing near `x` with the
`i`-th vector of the local frame of the preferred trivialisation. Only the germ at `x`
matters, because that is all `cov` sees. -/
noncomputable def canonFrameSection (x : M) (i : Fin (Module.finrank ℝ F)) : Π y : M, V y :=
  (RicciFlowBlueprint.exists_contMDiff_eventuallyEq_of_bundle (I := I) F (V := V) (n := 1)
    ((trivializationAt F V x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F V x))
    ((trivializationAt F V x).contMDiffOn_localFrame_baseSet 1 (Module.finBasis ℝ F) i)).choose

variable (I F V) in
omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
theorem contMDiff_canonFrameSection (x : M) (i : Fin (Module.finrank ℝ F)) :
    CMDiff (1 : ℕ∞ω) (T% (canonFrameSection I F V x i)) :=
  (RicciFlowBlueprint.exists_contMDiff_eventuallyEq_of_bundle (I := I) F (V := V) (n := 1)
    ((trivializationAt F V x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F V x))
    ((trivializationAt F V x).contMDiffOn_localFrame_baseSet
      1 (Module.finBasis ℝ F) i)).choose_spec.1

variable (I F V) in
omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
theorem canonFrameSection_eventuallyEq (x : M) (i : Fin (Module.finrank ℝ F)) :
    ∀ᶠ y in 𝓝 x, canonFrameSection I F V x i y
      = (trivializationAt F V x).localFrame (Module.finBasis ℝ F) i y :=
  (RicciFlowBlueprint.exists_contMDiff_eventuallyEq_of_bundle (I := I) F (V := V) (n := 1)
    ((trivializationAt F V x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F V x))
    ((trivializationAt F V x).contMDiffOn_localFrame_baseSet
      1 (Module.finBasis ℝ F) i)).choose_spec.2

variable (I F V) in
omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
theorem canonFrameSection_apply_self (x : M) (i : Fin (Module.finrank ℝ F)) :
    canonFrameSection I F V x i x
      = (trivializationAt F V x).basisAt (Module.finBasis ℝ F)
          (FiberBundle.mem_baseSet_trivializationAt F V x) i := by
  rw [(canonFrameSection_eventuallyEq I F V x i).self_of_nhds]
  exact (trivializationAt F V x).localFrame_apply_of_mem_baseSet
    (Module.finBasis ℝ F) (FiberBundle.mem_baseSet_trivializationAt F V x)

variable (F V) in
/-- **The fibre coordinates of a section of `V` along `γ`** in the trivialisation at `x`. -/
noncomputable def coeffAlongSection (γ : ℝ → M) (σ : Π t : ℝ, V (γ t)) (x : M)
    (i : Fin (Module.finrank ℝ F)) (u : ℝ) : ℝ :=
  (Module.finBasis ℝ F).repr ((trivializationAt F V x) ⟨γ u, σ u⟩).2 i

/-- **The covariant derivative of a section of `V` along `γ`.** Differentiate the fibre
coordinates in the trivialisation at `γ t` and add the connection's contribution on the
frame. -/
noncomputable def covAlongSection (cov : CovariantDerivative I F V) (γ : ℝ → M)
    (σ : Π t : ℝ, V (γ t)) (t : ℝ) : V (γ t) :=
  ∑ i, (deriv (coeffAlongSection F V γ σ (γ t) i) t • canonFrameSection I F V (γ t) i (γ t)
    + coeffAlongSection F V γ σ (γ t) i t
        • cov (canonFrameSection I F V (γ t) i) (γ t) (velocity γ t))

omit [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)] in
/-- The coordinates reconstruct the section at the base point of the trivialisation. -/
theorem sum_coeffAlongSection_smul_canonFrameSection (γ : ℝ → M) (σ : Π t : ℝ, V (γ t)) (t : ℝ) :
    ∑ i, coeffAlongSection F V γ σ (γ t) i t • canonFrameSection I F V (γ t) i (γ t) = σ t := by
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    ((e.basisAt (Module.finBasis ℝ F) hmem).sum_repr (σ t))
  rw [canonFrameSection_apply_self I F V (γ t) i, coeffAlongSection,
    ← repr_basisAt_eq_section (Module.finBasis ℝ F) hmem (σ t) i]

variable {γ : ℝ → M} {σ τ : Π t : ℝ, V (γ t)} {t : ℝ}

omit [T2Space M] [IsManifold I ω M] [∀ x : M, IsTopologicalAddGroup (V x)]
  [∀ x : M, ContinuousSMul ℝ (V x)] [FiniteDimensional ℝ E] in
/-- The coordinates of a section along `γ` are differentiable exactly when it is. -/
theorem differentiableAt_coeffAlongSection (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hσ : MDiffAlongSectionAt I F V γ σ t) (i : Fin (Module.finrank ℝ F)) :
    DifferentiableAt ℝ (coeffAlongSection F V γ σ (γ t) i) t := by
  have hc : DifferentiableAt ℝ
      (fun u ↦ ((trivializationAt F V (γ t)) ⟨γ u, σ u⟩).2) t :=
    (mdiffAlongSectionAt_iff_of_mem hγ (FiberBundle.mem_baseSet_trivializationAt F V (γ t))).mp hσ
  exact (((Module.finBasis ℝ F).coord i).toContinuousLinearMap.differentiableAt).comp t hc

omit [ContMDiffVectorBundle 1 F V I] [T2Space M] [IsManifold I ω M]
  [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ E] in
/-- The coordinates are additive in the section, near `t`. -/
theorem coeffAlongSection_add_eventuallyEq (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (i : Fin (Module.finrank ℝ F)) :
    coeffAlongSection F V γ (σ + τ) (γ t) i
      =ᶠ[𝓝 t] coeffAlongSection F V γ σ (γ t) i + coeffAlongSection F V γ τ (γ t) i := by
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  filter_upwards [hγ.continuousAt (e.open_baseSet.mem_nhds hmem)] with u hu
  show (Module.finBasis ℝ F).repr (e ⟨γ u, σ u + τ u⟩).2 i
      = (Module.finBasis ℝ F).repr (e ⟨γ u, σ u⟩).2 i
        + (Module.finBasis ℝ F).repr (e ⟨γ u, τ u⟩).2 i
  have hlin : (e ⟨γ u, σ u + τ u⟩).2 = (e ⟨γ u, σ u⟩).2 + (e ⟨γ u, τ u⟩).2 :=
    map_add (e.continuousLinearEquivAt ℝ (γ u) hu) (σ u) (τ u)
  rw [hlin, map_add]
  rfl

omit [ContMDiffVectorBundle 1 F V I] [T2Space M] [IsManifold I ω M]
  [∀ x : M, IsTopologicalAddGroup (V x)] [∀ x : M, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ E] in
/-- The coordinates scale in the section, near `t`. -/
theorem coeffAlongSection_smul_eventuallyEq (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (f : ℝ → ℝ)
    (i : Fin (Module.finrank ℝ F)) :
    coeffAlongSection F V γ (f • σ) (γ t) i
      =ᶠ[𝓝 t] f * coeffAlongSection F V γ σ (γ t) i := by
  set e := trivializationAt F V (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  filter_upwards [hγ.continuousAt (e.open_baseSet.mem_nhds hmem)] with u hu
  show (Module.finBasis ℝ F).repr (e ⟨γ u, f u • σ u⟩).2 i
      = f u * (Module.finBasis ℝ F).repr (e ⟨γ u, σ u⟩).2 i
  have hlin : (e ⟨γ u, f u • σ u⟩).2 = f u • (e ⟨γ u, σ u⟩).2 :=
    map_smul (e.continuousLinearEquivAt ℝ (γ u) hu) (f u) (σ u)
  rw [hlin, map_smul]
  rfl

-- BENCH: bundle-cov-along-curve-exists
/-- **`covAlongSection` satisfies the axioms**, on the set where `γ` is differentiable. With
`eq_of_isCovDerivAlongSection` this makes it *the* covariant derivative of a section of `V`
along `γ`. -/
theorem isCovDerivAlongSection_covAlongSection (cov : CovariantDerivative I F V) (γ : ℝ → M) :
    IsCovDerivAlongSection cov γ (covAlongSection cov γ)
      {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t} where
  add {σ τ t} hσ hτ ht := by
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := ht
    have hdσ := differentiableAt_coeffAlongSection hγ hσ
    have hdτ := differentiableAt_coeffAlongSection hγ hτ
    simp only [covAlongSection, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(coeffAlongSection_add_eventuallyEq hγ i).deriv_eq,
      deriv_add (hdσ i) (hdτ i), (coeffAlongSection_add_eventuallyEq hγ i).eq_of_nhds]
    show (deriv (coeffAlongSection F V γ σ (γ t) i) t
            + deriv (coeffAlongSection F V γ τ (γ t) i) t)
          • canonFrameSection I F V (γ t) i (γ t)
        + (coeffAlongSection F V γ σ (γ t) i t + coeffAlongSection F V γ τ (γ t) i t)
          • cov (canonFrameSection I F V (γ t) i) (γ t) (velocity γ t) = _
    rw [add_smul, add_smul]
    abel
  leibniz {σ f t} hσ hf ht := by
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := ht
    have hdσ := differentiableAt_coeffAlongSection hγ hσ
    rw [← sum_coeffAlongSection_smul_canonFrameSection (I := I) (F := F) (V := V) γ σ t]
    simp only [covAlongSection, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(coeffAlongSection_smul_eventuallyEq hγ f i).deriv_eq,
      deriv_mul hf (hdσ i), (coeffAlongSection_smul_eventuallyEq hγ f i).eq_of_nhds]
    show (deriv f t * coeffAlongSection F V γ σ (γ t) i t
            + f t * deriv (coeffAlongSection F V γ σ (γ t) i) t)
          • canonFrameSection I F V (γ t) i (γ t)
        + (f t * coeffAlongSection F V γ σ (γ t) i t)
          • cov (canonFrameSection I F V (γ t) i) (γ t) (velocity γ t) = _
    show _ = f t • (deriv (coeffAlongSection F V γ σ (γ t) i) t
          • canonFrameSection I F V (γ t) i (γ t)
        + coeffAlongSection F V γ σ (γ t) i t
          • cov (canonFrameSection I F V (γ t) i) (γ t) (velocity γ t))
        + deriv f t • coeffAlongSection F V γ σ (γ t) i t
          • canonFrameSection I F V (γ t) i (γ t)
    rw [smul_add, add_smul, smul_smul, smul_smul, smul_smul]
    abel
  restrict {Z t} hZ hγ ht := by
    set e := trivializationAt F V (γ t) with he
    set b := Module.finBasis ℝ F with hb
    have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
    set a : Fin (Module.finrank ℝ F) → M → ℝ := fun i y ↦ b.repr (e ⟨y, Z y⟩).2 i with ha
    have hco : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ (e ⟨y, Z y⟩).2) (γ t) :=
      ((e.mdifferentiableAt_totalSpace_iff I (T% Z) (e.mem_source.mpr hmem)).mp hZ).2
    have hac : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (a i) (γ t) := fun i ↦
      ((((b.coord i).toContinuousLinearMap.contMDiff (n := 1)).mdifferentiable
        (by norm_num) _).comp (γ t) hco)
    have hcanon : ∀ i, MDiffAt (T% (canonFrameSection I F V (γ t) i)) (γ t) := fun i ↦
      (contMDiff_canonFrameSection I F V (γ t) i).mdifferentiable (by norm_num) (γ t)
    have hZexp : ∀ᶠ y in 𝓝 (γ t), Z y = ∑ i, a i y • canonFrameSection I F V (γ t) i y := by
      filter_upwards [e.open_baseSet.mem_nhds hmem,
        Filter.eventually_all.mpr fun i ↦ canonFrameSection_eventuallyEq I F V (γ t) i]
        with y hy hfr
      rw [← sum_repr_smul_localFrame_section b hy (Z y)]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hfr i]
    have hsum : MDiffAt (T% (fun y ↦ ∑ i, a i y • canonFrameSection I F V (γ t) i y)) (γ t) :=
      MDifferentiableAt.sum_section fun i _ ↦ (hac i).smul_section (hcanon i)
    have hcovZ : cov Z (γ t) (velocity γ t)
        = ∑ i, (a i (γ t) • cov (canonFrameSection I F V (γ t) i) (γ t) (velocity γ t)
            + mvfderiv I (a i) (γ t) (velocity γ t) • canonFrameSection I F V (γ t) i (γ t)) := by
      rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq hZ hsum Filter.univ_mem hZexp]
      exact RicciFlowBlueprint.cov_sum_smul_section_apply_of_bundle cov Finset.univ (fun i _ ↦ hac i)
        (fun i _ ↦ hcanon i) _
    have hcoeff : ∀ i, coeffAlongSection F V γ (fun u ↦ Z (γ u)) (γ t) i = fun u ↦ a i (γ u) :=
      fun _ ↦ rfl
    simp only [covAlongSection, hcoeff]
    rw [hcovZ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [deriv_comp_curve (hac i) hγ]
    abel

-- BENCH: bundle-cov-along-curve-exists-unique
/-- **The covariant derivative of a section of `V` along a curve exists**, on the set where
`γ` is differentiable; by `eq_of_isCovDerivAlongSection` it is unique there. -/
theorem exists_isCovDerivAlongSection (cov : CovariantDerivative I F V) (γ : ℝ → M) :
    ∃ D : (Π t : ℝ, V (γ t)) → Π t : ℝ, V (γ t),
      IsCovDerivAlongSection cov γ D {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t} :=
  ⟨covAlongSection cov γ, isCovDerivAlongSection_covAlongSection cov γ⟩

/-- Any operator satisfying the axioms **is** `covAlongSection` on sections differentiable
along `γ`. -/
theorem eq_covAlongSection {cov : CovariantDerivative I F V}
    {D : (Π t : ℝ, V (γ t)) → Π t : ℝ, V (γ t)} {s : Set ℝ}
    (h : IsCovDerivAlongSection cov γ D s) (hs : s ⊆ {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t})
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hσ : MDiffAlongSectionAt I F V γ σ t) (ht : t ∈ s) :
    D σ t = covAlongSection cov γ σ t :=
  h.eq_of_isCovDerivAlongSection ((isCovDerivAlongSection_covAlongSection cov γ).mono hs)
    hγ hσ ht

variable (I F V) in
/-- **A parallel section of `V` along `γ`**, `D/dt σ = 0` on `s`. Defined off
`covAlongSection`; `isParallelAlongSection_iff_forall` shows this is the same as vanishing
under *every* operator satisfying the axioms. -/
def IsParallelAlongSection (cov : CovariantDerivative I F V) (γ : ℝ → M)
    (σ : Π t : ℝ, V (γ t)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, covAlongSection cov γ σ t = 0

/-- **The quantified form is not vacuous.** Forward is uniqueness, backward is existence ---
and it is the backward direction that has content: without
`isCovDerivAlongSection_covAlongSection` the right-hand side would quantify over a class of
operators nothing is known to inhabit, and would be trivially true. -/
theorem isParallelAlongSection_iff_forall {cov : CovariantDerivative I F V}
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hσ : ∀ t ∈ s, MDiffAlongSectionAt I F V γ σ t) :
    IsParallelAlongSection I F V cov γ σ s
      ↔ ∀ D : (Π t : ℝ, V (γ t)) → Π t : ℝ, V (γ t),
          IsCovDerivAlongSection cov γ D s → ∀ t ∈ s, D σ t = 0 := by
  refine ⟨fun h D hD t ht ↦ ?_, fun h t ht ↦ ?_⟩
  · rw [hD.eq_of_isCovDerivAlongSection
      ((isCovDerivAlongSection_covAlongSection cov γ).mono hγ) (hγ t ht) (hσ t ht) ht]
    exact h t ht
  · exact h _ ((isCovDerivAlongSection_covAlongSection cov γ).mono hγ) t ht

end Existence

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


variable [FiniteDimensional ℝ E] [T2Space M]

/-- **`covAlongSection` at `V = TM` is `covAlong`.** Not asserted by construction: both
satisfy the three axioms, and uniqueness identifies them. This is what checks that the
general construction computes the tangent-bundle operator and not merely something of the
same type. -/
theorem covAlongSection_eq_covAlong
    (cov : CovariantDerivative I E (fun y : M ↦ TangentSpace I y)) {γ : ℝ → M}
    {σ : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hσ : MDiffAlongAt γ σ t) :
    covAlongSection cov γ σ t = covAlong cov γ σ t :=
  (eq_covAlongSection
    ((isCovDerivAlongSection_iff_isCovDerivAlong I cov γ (covAlong cov γ) _).mpr
      (isCovDerivAlong_covAlong cov γ)) subset_rfl hγ hσ hγ).symm

/-- **The two notions of a parallel section agree** at `V = TM`. -/
theorem isParallelAlongSection_iff_isParallelAlong
    (cov : CovariantDerivative I E (fun y : M ↦ TangentSpace I y)) {γ : ℝ → M}
    {σ : Π t : ℝ, TangentSpace I (γ t)} {s : Set ℝ}
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hσ : ∀ t ∈ s, MDiffAlongAt γ σ t) :
    IsParallelAlongSection I E (fun y : M ↦ TangentSpace I y) cov γ σ s
      ↔ IsParallelAlong cov γ σ s := by
  constructor <;> intro h t ht
  · rw [← covAlongSection_eq_covAlong cov (hγ t ht) (hσ t ht)]; exact h t ht
  · rw [covAlongSection_eq_covAlong cov (hγ t ht) (hσ t ht)]; exact h t ht

end Tangent

end CovariantDerivative
