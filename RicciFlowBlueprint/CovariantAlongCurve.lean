/-
The covariant derivative along a curve.

Mathlib's `CovariantDerivative` acts on **global sections over `M`**:
`(Π x : M, V x) → (Π x : M, T_xM →L[ℝ] V x)`. A curve's velocity is not such a section — it
lives only along the curve — so `∇_{γ'} γ' = 0` cannot even be *stated* with it. The missing
primitive is the pullback connection on `γ*TM`, written `D/dt`, and everything in comparison
geometry rests on it: geodesics, parallel transport, the Jacobi equation, and the first and
second variation of length (and, later, of Perelman's `L`-length).

This file defines it the way Mathlib defines the ambient one: a **predicate**
`IsCovDerivAlong` cutting out the operators that deserve the name, with existence and
uniqueness proved separately. The three axioms are the usual ones — additive, Leibniz over a
scalar function of `t`, and agreement with `cov` on the restriction of a global section.

A section along `γ` is a lift of `γ` to `TM`, so its regularity is ordinary
`MDifferentiableAt` into the total space; no new bundle structure is needed.
-/
import RicciFlowBlueprint.Curvature
import RicciFlowBlueprint.GlobalExtension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Bundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-- The **velocity** of a curve, `γ'(t) ∈ T_{γ(t)}M`. -/
noncomputable def velocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) I γ t (show TangentSpace 𝓘(ℝ, ℝ) t from (1 : ℝ))

/-- **A section of `TM` along `γ` is differentiable at `t`** when its lift to the total space
is. This is the `T%` idiom of the ambient theory, with the base `M` replaced by the parameter
interval. -/
def MDiffAlongAt (γ : ℝ → M) (V : Π t : ℝ, TangentSpace I (γ t)) (t : ℝ) : Prop :=
  MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
    (fun u ↦ (⟨γ u, V u⟩ : TangentBundle I M)) t

/-- **The covariant derivative along a curve**, as a predicate. `D` differentiates sections of
`TM` along `γ`; the three axioms say it is additive, satisfies the Leibniz rule over scalar
functions of the parameter, and restricts `cov` correctly:
`D (W ∘ γ) t = (∇_{γ'(t)} W)(γ t)` for a global section `W`.

The last axiom is what ties `D` to the ambient connection, and — with the other two — pins it
down: near any `t` a section along `γ` is a combination of restrictions of a local frame. -/
structure IsCovDerivAlong
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (γ : ℝ → M)
    (D : (Π t : ℝ, TangentSpace I (γ t)) → (Π t : ℝ, TangentSpace I (γ t)))
    (s : Set ℝ := Set.univ) : Prop where
  add {V W : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}
    (hV : MDiffAlongAt γ V t) (hW : MDiffAlongAt γ W t) (ht : t ∈ s := by trivial) :
    D (V + W) t = D V t + D W t
  leibniz {V : Π t : ℝ, TangentSpace I (γ t)} {f : ℝ → ℝ} {t : ℝ}
    (hV : MDiffAlongAt γ V t) (hf : DifferentiableAt ℝ f t) (ht : t ∈ s := by trivial) :
    D (f • V) t = f t • D V t + deriv f t • V t
  restrict {W : Π x : M, TangentSpace I x} {t : ℝ}
    (hW : MDiffAt (T% W) (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (ht : t ∈ s := by trivial) :
    D (fun u ↦ W (γ u)) t = cov W (γ t) (velocity γ t)

/-- The zero section along a differentiable curve is differentiable. -/
theorem MDiffAlongAt.zero_section {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDiffAlongAt γ (0 : Π t : ℝ, TangentSpace I (γ t)) t :=
  ((contMDiff_zeroSection (n := 1) ℝ (fun (x : M) ↦ TangentSpace I x)).mdifferentiable
    (by norm_num) (γ t)).comp t hγ

variable {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)} {γ : ℝ → M}
  {D : (Π t : ℝ, TangentSpace I (γ t)) → (Π t : ℝ, TangentSpace I (γ t))} {s : Set ℝ}

/-- The predicate is monotone in the parameter set. -/
theorem IsCovDerivAlong.mono {s' : Set ℝ} (h : IsCovDerivAlong cov γ D s') (hss' : s ⊆ s') :
    IsCovDerivAlong cov γ D s where
  add hV hW ht := h.add hV hW (hss' ht)
  leibniz hV hf ht := h.leibniz hV hf (hss' ht)
  restrict hW hγ ht := h.restrict hW hγ (hss' ht)

/-- `D` kills the zero section: Leibniz with the zero coefficient. -/
theorem IsCovDerivAlong.zero (h : IsCovDerivAlong cov γ D s) {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s) :
    D 0 t = 0 := by
  have hz : ((fun _ : ℝ ↦ (0 : ℝ)) • (0 : Π t : ℝ, TangentSpace I (γ t)))
      = (0 : Π t : ℝ, TangentSpace I (γ t)) := by
    funext u; simp
  have hL := h.leibniz (f := fun _ : ℝ ↦ (0 : ℝ))
    (MDiffAlongAt.zero_section hγ) (differentiableAt_const (0 : ℝ)) ht
  rw [hz] at hL
  simpa using hL

-- BENCH: cov-along-curve-local
/-- **`D` is local**: it depends on a section only through its germ. Not an axiom — the usual
bump-function argument. If `V = W` near `t`, take a smooth `f` equal to `1` near `t` and
supported where they agree; then `f • V = f • W` *globally*, while Leibniz evaluates both sides
at `t` to `D V t` and `D W t`, because `f t = 1` and `deriv f t = 0`. -/
theorem IsCovDerivAlong.congr_of_eventuallyEq (h : IsCovDerivAlong cov γ D s)
    {V W : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}
    (hV : MDiffAlongAt γ V t) (hW : MDiffAlongAt γ W t) (ht : t ∈ s)
    (hVW : V =ᶠ[𝓝 t] W) :
    D V t = D W t := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hVW
  -- a bump: `1` on `closedBall t (ε/3)`, supported in `ball t (ε/2)`
  set b : ContDiffBump t := ⟨ε / 3, ε / 2, by positivity, by linarith⟩ with hb
  have hbc : ∀ u, (b : ℝ → ℝ) u = b u := fun _ ↦ rfl
  have hf1 : b t = 1 := b.one_of_mem_closedBall (by simp [Metric.mem_closedBall]; positivity)
  have hfnear : (fun u ↦ b u) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds t (by positivity : (0 : ℝ) < ε / 3)] with u hu
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
  have hfd : DifferentiableAt ℝ (fun u ↦ b u) t :=
    (b.contDiff (n := 1)).differentiable (by norm_num) t
  have hderiv : deriv (fun u ↦ b u) t = 0 := by
    rw [hfnear.deriv_eq, deriv_const]
  -- the two smeared sections agree globally
  have hsm : ((fun u ↦ b u) • V) = ((fun u ↦ b u) • W) := by
    funext u
    by_cases hu : b u = 0
    · simp [hu]
    · have humem : u ∈ Metric.ball t ε := by
        have hu2 : u ∈ Metric.ball t (ε / 2) := by
          rw [← b.support_eq]; exact Function.mem_support.mpr hu
        exact Metric.ball_subset_ball (by linarith) hu2
      show b u • V u = b u • W u
      rw [hball u humem]
  have eV := h.leibniz hV hfd ht
  have eW := h.leibniz hW hfd ht
  rw [hsm] at eV
  rw [eV] at eW
  rw [hf1, hderiv] at eW
  simpa using eW


section Frame

/-! ### Local frames along a curve

Uniqueness of `D/dt` rests on one fact: near `t` a section along `γ` is a finite combination
`V = ∑ᵢ fᵢ · (Wᵢ ∘ γ)` of restrictions of *global* sections, with `fᵢ` differentiable. Locality
plus the three axioms then compute `D V t` with no reference to `D`.

The local frame is Mathlib's `Trivialization.localFrame`; the coefficients are read off the
same trivialisation, which is also what makes them differentiable; and the frame is made
global by the bump argument of `GlobalExtension.lean`.
-/

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable {V W : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}

/-- **Differentiability along `γ` is differentiability of the fibre coordinate** in any
trivialisation around `γ t`. This is `Trivialization.mdifferentiableAt_totalSpace_iff` with the
base component discharged by the curve's own differentiability. -/
theorem mdiffAlongAt_iff_of_mem
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (he : γ t ∈ e.baseSet) :
    MDiffAlongAt γ V t ↔ DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, V u⟩).2) t := by
  rw [MDiffAlongAt, e.mdifferentiableAt_totalSpace_iff I _ (e.mem_source.mpr he),
    ← mdifferentiableAt_iff_differentiableAt]
  exact and_iff_right hγ

omit [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- The restriction of a globally `C¹` section to a differentiable curve is differentiable
along it. -/
theorem MDiffAlongAt.of_section {W : Π y : M, TangentSpace I y} (hW : CMDiff 1 (T% W))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDiffAlongAt γ (fun u ↦ W (γ u)) t :=
  (hW.mdifferentiable (by norm_num) (γ t)).comp t hγ

/-- Sections along `γ` add. -/
theorem MDiffAlongAt.add (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : MDiffAlongAt γ V t) (hW : MDiffAlongAt γ W t) :
    MDiffAlongAt γ (V + W) t := by
  set e := trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hmem)
  rw [mdiffAlongAt_iff_of_mem hγ hmem] at hV hW ⊢
  refine (hV.add hW).congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with u hu
  show (e ⟨γ u, V u + W u⟩).2 = (e ⟨γ u, V u⟩).2 + (e ⟨γ u, W u⟩).2
  exact map_add (e.continuousLinearEquivAt ℝ (γ u) hu) (V u) (W u)

/-- Sections along `γ` scale by differentiable functions of the parameter. -/
theorem MDiffAlongAt.smul {f : ℝ → ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hf : DifferentiableAt ℝ f t) (hV : MDiffAlongAt γ V t) :
    MDiffAlongAt γ (f • V) t := by
  set e := trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hmem)
  rw [mdiffAlongAt_iff_of_mem hγ hmem] at hV ⊢
  refine (hf.smul hV).congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with u hu
  show (e ⟨γ u, f u • V u⟩).2 = f u • (e ⟨γ u, V u⟩).2
  exact map_smul (e.continuousLinearEquivAt ℝ (γ u) hu) (f u) (V u)

/-- Finite sums of sections along `γ`. The sum is taken **fibrewise**, not in the Pi type:
the `AddCommMonoid` instance `Finset.sum` would pick on `Π t, T_{γ t}M` is only defeq to the
one `Fintype.sum_apply` produces, and no `rw` crosses that gap. -/
theorem MDiffAlongAt.sum {ι : Type*} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (a : Finset ι) {Vs : ι → Π t : ℝ, TangentSpace I (γ t)}
    (hV : ∀ i ∈ a, MDiffAlongAt γ (Vs i) t) :
    MDiffAlongAt γ (fun u ↦ ∑ i ∈ a, Vs i u) t := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (fun u ↦ ∑ i ∈ (∅ : Finset ι), Vs i u)
        = (0 : Π t : ℝ, TangentSpace I (γ t)) := by
      funext u; exact Finset.sum_empty
    rw [h0]
    exact MDiffAlongAt.zero_section hγ
  | insert c a hc ih =>
    have hstep : (fun u ↦ ∑ i ∈ insert c a, Vs i u)
        = Vs c + fun u ↦ ∑ i ∈ a, Vs i u := by
      funext u
      show ∑ i ∈ insert c a, Vs i u = Vs c u + ∑ i ∈ a, Vs i u
      exact Finset.sum_insert hc
    rw [hstep]
    exact (hV c (Finset.mem_insert_self c a)).add hγ
      (ih fun i hi ↦ hV i (Finset.mem_insert_of_mem hi))


variable [FiniteDimensional ℝ E] [T2Space M]

-- BENCH: cov-along-curve-frame-expansion
/-- **A section along `γ` is, near `t`, a finite combination of restrictions of globally `C¹`
sections, with differentiable coefficients.** This is what pins `D/dt` down.

Everything is read off one trivialisation around `γ t`: the frame is Mathlib's
`Trivialization.localFrame` for a basis of the model fibre, made global by the bump argument of
`GlobalExtension.lean`; the coefficients are the fibre coordinates of `V`, differentiable
because differentiability along `γ` *is* differentiability of those coordinates. -/
theorem exists_frame_expansion (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t) :
    ∃ (ι : Type) (_ : Fintype ι) (W : ι → Π y : M, TangentSpace I y) (f : ι → ℝ → ℝ),
      (∀ i, CMDiff 1 (T% (W i))) ∧ (∀ i, DifferentiableAt ℝ (f i) t) ∧
      V =ᶠ[𝓝 t] fun u ↦ ∑ i, f i u • W i (γ u) := by
  classical
  set e := trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
  set b := Module.finBasis ℝ E with hb
  -- the fibre coordinates of `V` in `e`
  have hcoord : DifferentiableAt ℝ (fun u ↦ (e ⟨γ u, V u⟩).2) t :=
    (mdiffAlongAt_iff_of_mem hγ hmem).mp hV
  -- the local frame, made global
  have hloc : ∀ i, ∃ τ : Π y : M, TangentSpace I y,
      CMDiff (1 : ℕ∞ω) (T% τ) ∧ τ =ᶠ[𝓝 (γ t)] e.localFrame b i := fun i ↦
    RicciFlowBlueprint.exists_contMDiff_eventuallyEq (n := 1) (e.open_baseSet.mem_nhds hmem)
      (e.contMDiffOn_localFrame_baseSet 1 b i)
  choose W hW hWeq using hloc
  refine ⟨_, inferInstance, W, fun i u ↦ b.repr (e ⟨γ u, V u⟩).2 i, hW, fun i ↦ ?_, ?_⟩
  · exact (((b.coord i).toContinuousLinearMap).differentiableAt).comp t hcoord
  -- the expansion holds wherever the frame is defined and equal to its globalisation
  have hrepr : ∀ (y : M) (hy : y ∈ e.baseSet) (v : TangentSpace I y) (i),
      (e.basisAt b hy).repr v i = b.repr (e ⟨y, v⟩).2 i := by
    intro y hy v i
    simp [Trivialization.basisAt]
  have hnhds : ∀ᶠ u in 𝓝 t, γ u ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hmem)
  have hall : ∀ᶠ u in 𝓝 t, ∀ i, W i (γ u) = e.localFrame b i (γ u) :=
    Filter.eventually_all.mpr fun i ↦ hγ.continuousAt.eventually (hWeq i)
  filter_upwards [hnhds, hall] with u hu hWu
  refine ((e.basisAt b hu).sum_repr (V u)).symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  show (e.basisAt b hu).repr (V u) i • (e.basisAt b hu) i
      = b.repr (e ⟨γ u, V u⟩).2 i • W i (γ u)
  rw [hrepr (γ u) hu (V u) i, hWu i, e.localFrame_apply_of_mem_baseSet b hu]


omit [FiniteDimensional ℝ E] [T2Space M] in
-- BENCH: cov-along-curve-sum
/-- `D` is additive over finite sums, by induction from the `add` axiom. -/
theorem IsCovDerivAlong.sum (h : IsCovDerivAlong cov γ D s)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : t ∈ s) {ι : Type*} (a : Finset ι)
    {Vs : ι → Π t : ℝ, TangentSpace I (γ t)} (hV : ∀ i ∈ a, MDiffAlongAt γ (Vs i) t) :
    D (fun u ↦ ∑ i ∈ a, Vs i u) t = ∑ i ∈ a, D (Vs i) t := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (fun u ↦ ∑ i ∈ (∅ : Finset ι), Vs i u)
        = (0 : Π t : ℝ, TangentSpace I (γ t)) := by
      funext u; exact Finset.sum_empty
    rw [h0, Finset.sum_empty]
    exact h.zero hγ ht
  | insert c a hc ih =>
    have hstep : (fun u ↦ ∑ i ∈ insert c a, Vs i u)
        = Vs c + fun u ↦ ∑ i ∈ a, Vs i u := by
      funext u
      show ∑ i ∈ insert c a, Vs i u = Vs c u + ∑ i ∈ a, Vs i u
      exact Finset.sum_insert hc
    rw [hstep, h.add (hV c (Finset.mem_insert_self c a))
      (MDiffAlongAt.sum hγ a fun i hi ↦ hV i (Finset.mem_insert_of_mem hi)) ht,
      ih fun i hi ↦ hV i (Finset.mem_insert_of_mem hi), Finset.sum_insert hc]

omit [FiniteDimensional ℝ E] [T2Space M] in
-- BENCH: cov-along-curve-expansion-value
/-- **`D/dt` is computed by any local expansion.** If `V = ∑ᵢ fᵢ · (Wᵢ ∘ γ)` near `t` with `Wᵢ`
global `C¹` sections and `fᵢ` differentiable, then
`D V t = ∑ᵢ (fᵢ(t)·∇_{γ'}Wᵢ + fᵢ'(t)·Wᵢ(γ t))`, an expression in which `D` no longer occurs.

Locality replaces `V` by the sum, additivity splits it, Leibniz evaluates each term, and
`restrict` turns `D(Wᵢ ∘ γ)` into `∇_{γ'}Wᵢ`. Uniqueness is the immediate corollary; the
lemma itself is what computes `D/dt` in a chart. -/
theorem IsCovDerivAlong.eq_sum_of_expansion (h : IsCovDerivAlong cov γ D s)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t) (ht : t ∈ s)
    {ι : Type*} [Fintype ι] {W : ι → Π y : M, TangentSpace I y} {f : ι → ℝ → ℝ}
    (hW : ∀ i, CMDiff 1 (T% (W i))) (hf : ∀ i, DifferentiableAt ℝ (f i) t)
    (hexp : V =ᶠ[𝓝 t] fun u ↦ ∑ i, f i u • W i (γ u)) :
    D V t = ∑ i, (f i t • cov (W i) (γ t) (velocity γ t) + deriv (f i) t • W i (γ t)) := by
  classical
  set Vs : ι → Π u : ℝ, TangentSpace I (γ u) := fun i ↦ (f i) • fun u ↦ W i (γ u) with hVs
  have hexp' : V =ᶠ[𝓝 t] fun u ↦ ∑ i ∈ Finset.univ, Vs i u := hexp
  have hWγ : ∀ i, MDiffAlongAt γ (fun u ↦ W i (γ u)) t := fun i ↦
    MDiffAlongAt.of_section (hW i) hγ
  have hterm : ∀ i, MDiffAlongAt γ (Vs i) t := fun i ↦ (hWγ i).smul hγ (hf i)
  have hsum : MDiffAlongAt γ (fun u ↦ ∑ i ∈ Finset.univ, Vs i u) t :=
    MDiffAlongAt.sum hγ Finset.univ fun i _ ↦ hterm i
  rw [h.congr_of_eventuallyEq hV hsum ht hexp', h.sum hγ ht Finset.univ fun i _ ↦ hterm i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hVs, h.leibniz (hWγ i) (hf i) ht,
    h.restrict ((hW i).mdifferentiable (by norm_num) (γ t)) hγ ht]

-- BENCH: cov-along-curve-unique
/-- **`D/dt` is determined by the ambient connection.** Two operators satisfying the three
axioms agree on every section differentiable along `γ`: both are computed by the frame
expansion of `exists_frame_expansion`, which mentions neither. -/
theorem IsCovDerivAlong.eq_of_isCovDerivAlong (h : IsCovDerivAlong cov γ D s)
    (h' : IsCovDerivAlong cov γ D' s) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : MDiffAlongAt γ V t) (ht : t ∈ s) :
    D V t = D' V t := by
  obtain ⟨ι, _, W, f, hW, hf, hexp⟩ := exists_frame_expansion hγ hV
  rw [h.eq_sum_of_expansion hγ hV ht hW hf hexp, h'.eq_sum_of_expansion hγ hV ht hW hf hexp]

end Frame

section Existence

/-! ### Existence

`D/dt` is built in the trivialisation at `γ t`: differentiate the fibre coordinates of `V` and
add the connection's own contribution on the frame. Additivity and the Leibniz rule are then
the corresponding facts about `deriv`; the third axiom is the only one with content, and it is
`cov`'s Leibniz rule applied to the local-frame expansion of a global section.

Uniqueness (`eq_of_isCovDerivAlong`) makes this construction a definition of *the* covariant
derivative along a curve rather than one of many. It is also what makes the geodesic equation
`∇_{γ'}γ' = 0` a statement with content: quantified over operators satisfying the axioms, it
would otherwise be vacuously true.
-/

variable [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M]


omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- The fibre basis a trivialisation induces is the model basis read through it. -/
theorem repr_basisAt_eq
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} (b : Module.Basis ι ℝ E) {y : M} (hy : y ∈ e.baseSet)
    (v : TangentSpace I y) (i : ι) :
    (e.basisAt b hy).repr v i = b.repr (e ⟨y, v⟩).2 i := by
  simp [Trivialization.basisAt]


omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- **The local frame reconstructs a fibre vector** from its coordinates. -/
theorem sum_repr_smul_localFrame
    {e : Trivialization E (TotalSpace.proj : TotalSpace E (fun (x : M) ↦ TangentSpace I x) → M)}
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) {y : M}
    (hy : y ∈ e.baseSet) (v : TangentSpace I y) :
    ∑ i, b.repr (e ⟨y, v⟩).2 i • e.localFrame b i y = v := by
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) ((e.basisAt b hy).sum_repr v)
  rw [e.localFrame_apply_of_mem_baseSet b hy, ← repr_basisAt_eq b hy v i]

variable (I) in
/-- **The canonical frame at `x`**: a globally `C¹` section agreeing near `x` with the `i`-th
vector of the local frame induced by the preferred trivialisation and `Module.finBasis`. The
globalisation is the bump argument of `GlobalExtension.lean`; only the germ at `x` matters,
because that is all `cov` sees. -/
noncomputable def canonFrame (x : M) (i : Fin (Module.finrank ℝ E)) :
    Π y : M, TangentSpace I y :=
  (RicciFlowBlueprint.exists_contMDiff_eventuallyEq (I := I) (n := 1)
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E _ x))
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).contMDiffOn_localFrame_baseSet
      1 (Module.finBasis ℝ E) i)).choose

variable (I) in
theorem contMDiff_canonFrame (x : M) (i : Fin (Module.finrank ℝ E)) :
    CMDiff (1 : ℕ∞ω) (T% (canonFrame I x i)) :=
  (RicciFlowBlueprint.exists_contMDiff_eventuallyEq (I := I) (n := 1)
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E _ x))
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).contMDiffOn_localFrame_baseSet
      1 (Module.finBasis ℝ E) i)).choose_spec.1

variable (I) in
theorem canonFrame_eventuallyEq (x : M) (i : Fin (Module.finrank ℝ E)) :
    canonFrame I x i =ᶠ[𝓝 x]
      (trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).localFrame
        (Module.finBasis ℝ E) i :=
  (RicciFlowBlueprint.exists_contMDiff_eventuallyEq (I := I) (n := 1)
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E _ x))
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).contMDiffOn_localFrame_baseSet
      1 (Module.finBasis ℝ E) i)).choose_spec.2

variable (I) in
theorem canonFrame_apply_self (x : M) (i : Fin (Module.finrank ℝ E)) :
    canonFrame I x i x
      = (trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).basisAt (Module.finBasis ℝ E)
          (FiberBundle.mem_baseSet_trivializationAt E _ x) i := by
  rw [(canonFrame_eventuallyEq I x i).eq_of_nhds]
  exact (trivializationAt E (fun (y : M) ↦ TangentSpace I y) x).localFrame_apply_of_mem_baseSet
    (Module.finBasis ℝ E) (FiberBundle.mem_baseSet_trivializationAt E _ x)

/-- **The fibre coordinates of a section along `γ`** in the trivialisation at `x`. -/
noncomputable def coeffAlong (γ : ℝ → M) (V : Π t : ℝ, TangentSpace I (γ t)) (x : M)
    (i : Fin (Module.finrank ℝ E)) (u : ℝ) : ℝ :=
  (Module.finBasis ℝ E).repr
    ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) x) ⟨γ u, V u⟩).2 i

/-- **The covariant derivative along `γ`.** Differentiate the fibre coordinates of `V` in the
trivialisation at `γ t` and add the connection's contribution on the frame. -/
noncomputable def covAlong (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (γ : ℝ → M) (V : Π t : ℝ, TangentSpace I (γ t)) (t : ℝ) : TangentSpace I (γ t) :=
  ∑ i, (deriv (coeffAlong γ V (γ t) i) t • canonFrame I (γ t) i (γ t)
    + coeffAlong γ V (γ t) i t • cov (canonFrame I (γ t) i) (γ t) (velocity γ t))


omit [IsManifold I ω M] [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- **The chain rule along a curve** for a scalar function of the manifold. -/
theorem deriv_comp_curve {f : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    deriv (fun u ↦ f (γ u)) t = mvfderiv I f (γ t) (velocity γ t) := by
  have h := mvfderiv_comp_apply (g := f) (f := γ) t hf hγ
    (show TangentSpace 𝓘(ℝ, ℝ) t from (1 : ℝ))
  rw [velocity]
  rw [← h]
  simp only [mvfderiv, mfderiv_eq_fderiv]
  rfl


omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- A finite combination of sections with differentiable coefficients is differentiable. -/
theorem mdiffAt_sum_smul_section {ι : Type*} (a : Finset ι)
    {c : ι → M → ℝ} {W : ι → Π y : M, TangentSpace I y} {x : M}
    (hc : ∀ i ∈ a, MDifferentiableAt I 𝓘(ℝ, ℝ) (c i) x)
    (hW : ∀ i ∈ a, MDiffAt (T% (W i)) x) :
    MDiffAt (T% (fun y ↦ ∑ i ∈ a, c i y • W i y)) x := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (T% fun y ↦ ∑ i ∈ (∅ : Finset ι), c i y • W i y)
        = (T% (0 : Π y : M, TangentSpace I y)) := by
      funext y
      show (⟨y, ∑ i ∈ (∅ : Finset ι), c i y • W i y⟩ :
        TotalSpace E fun y : M ↦ TangentSpace I y) = ⟨y, 0⟩
      rw [Finset.sum_empty]
    rw [h0]
    exact mdifferentiableAt_zeroSection _ _
  | insert j a hj ih =>
    have hstep : (T% fun y ↦ ∑ i ∈ insert j a, c i y • W i y)
        = (T% ((c j • W j) + fun y ↦ ∑ i ∈ a, c i y • W i y)) := by
      funext y
      show (⟨y, ∑ i ∈ insert j a, c i y • W i y⟩ :
        TotalSpace E fun y : M ↦ TangentSpace I y) = ⟨y, c j y • W j y + ∑ i ∈ a, c i y • W i y⟩
      rw [Finset.sum_insert hj]
    rw [hstep]
    exact mdifferentiableAt_add_section
      ((hc j (Finset.mem_insert_self j a)).smul_section (hW j (Finset.mem_insert_self j a)))
      (ih (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hW i (Finset.mem_insert_of_mem hi))

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- **Leibniz over a finite combination of sections**, applied to a tangent vector. -/
theorem cov_sum_smul_section_apply
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) {ι : Type*} (a : Finset ι)
    {c : ι → M → ℝ} {W : ι → Π y : M, TangentSpace I y} {x : M}
    (hc : ∀ i ∈ a, MDifferentiableAt I 𝓘(ℝ, ℝ) (c i) x)
    (hW : ∀ i ∈ a, MDiffAt (T% (W i)) x) (v : TangentSpace I x) :
    cov (fun y ↦ ∑ i ∈ a, c i y • W i y) x v
      = ∑ i ∈ a, (c i x • cov (W i) x v + mvfderiv I (c i) x v • W i x) := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (fun y ↦ ∑ i ∈ (∅ : Finset ι), c i y • W i y)
        = (0 : Π y : M, TangentSpace I y) := by funext y; exact Finset.sum_empty
    rw [h0, Finset.sum_empty, cov.zero]
    rfl
  | insert j a hj ih =>
    have hjm := Finset.mem_insert_self j a
    have hstep : (fun y ↦ ∑ i ∈ insert j a, c i y • W i y)
        = (c j • W j) + fun y ↦ ∑ i ∈ a, c i y • W i y := by
      funext y
      show ∑ i ∈ insert j a, c i y • W i y = c j y • W j y + ∑ i ∈ a, c i y • W i y
      exact Finset.sum_insert hj
    have hrest := mdiffAt_sum_smul_section a (c := c) (W := W)
      (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hW i (Finset.mem_insert_of_mem hi))
    rw [hstep, cov.isCovariantDerivativeOn.add
        ((hc j hjm).smul_section (hW j hjm)) hrest,
      cov.isCovariantDerivativeOn.leibniz (hW j hjm) (hc j hjm), Finset.sum_insert hj,
      ← ih (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hW i (Finset.mem_insert_of_mem hi)]
    rfl

/-- The coordinates reconstruct the section at the base point of the trivialisation. -/
theorem sum_coeffAlong_smul_canonFrame (γ : ℝ → M) (V : Π t : ℝ, TangentSpace I (γ t)) (t : ℝ) :
    ∑ i, coeffAlong γ V (γ t) i t • canonFrame I (γ t) i (γ t) = V t := by
  set e := trivializationAt E (fun (y : M) ↦ TangentSpace I y) (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) ((e.basisAt (Module.finBasis ℝ E) hmem).sum_repr (V t))
  rw [canonFrame_apply_self I (γ t) i, coeffAlong,
    ← repr_basisAt_eq (Module.finBasis ℝ E) hmem (V t) i]


variable {γ : ℝ → M} {V W : Π t : ℝ, TangentSpace I (γ t)} {t : ℝ}

omit [T2Space M] in
/-- The coordinates of a section along `γ` are differentiable exactly when it is. -/
theorem differentiableAt_coeffAlong (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : MDiffAlongAt γ V t) (i : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (coeffAlong γ V (γ t) i) t := by
  have hc : DifferentiableAt ℝ (fun u ↦
      ((trivializationAt E (fun (y : M) ↦ TangentSpace I y) (γ t)) ⟨γ u, V u⟩).2) t :=
    (mdiffAlongAt_iff_of_mem hγ (FiberBundle.mem_baseSet_trivializationAt E _ (γ t))).mp hV
  exact (((Module.finBasis ℝ E).coord i).toContinuousLinearMap.differentiableAt).comp t hc

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
/-- The coordinates are additive in the section, near `t`. -/
theorem coeffAlong_add_eventuallyEq (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (i : Fin (Module.finrank ℝ E)) :
    coeffAlong γ (V + W) (γ t) i
      =ᶠ[𝓝 t] coeffAlong γ V (γ t) i + coeffAlong γ W (γ t) i := by
  set e := trivializationAt E (fun (y : M) ↦ TangentSpace I y) (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
  filter_upwards [hγ.continuousAt (e.open_baseSet.mem_nhds hmem)] with u hu
  show (Module.finBasis ℝ E).repr (e ⟨γ u, V u + W u⟩).2 i
      = (Module.finBasis ℝ E).repr (e ⟨γ u, V u⟩).2 i
        + (Module.finBasis ℝ E).repr (e ⟨γ u, W u⟩).2 i
  have hlin : (e ⟨γ u, V u + W u⟩).2 = (e ⟨γ u, V u⟩).2 + (e ⟨γ u, W u⟩).2 :=
    map_add (e.continuousLinearEquivAt ℝ (γ u) hu) (V u) (W u)
  rw [hlin, map_add]
  rfl

omit [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [T2Space M] in
/-- The coordinates scale in the section, near `t`. -/
theorem coeffAlong_smul_eventuallyEq (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (f : ℝ → ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    coeffAlong γ (f • V) (γ t) i =ᶠ[𝓝 t] f * coeffAlong γ V (γ t) i := by
  set e := trivializationAt E (fun (y : M) ↦ TangentSpace I y) (γ t) with he
  have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
  filter_upwards [hγ.continuousAt (e.open_baseSet.mem_nhds hmem)] with u hu
  show (Module.finBasis ℝ E).repr (e ⟨γ u, f u • V u⟩).2 i
      = f u * (Module.finBasis ℝ E).repr (e ⟨γ u, V u⟩).2 i
  have hlin : (e ⟨γ u, f u • V u⟩).2 = f u • (e ⟨γ u, V u⟩).2 :=
    map_smul (e.continuousLinearEquivAt ℝ (γ u) hu) (f u) (V u)
  rw [hlin, map_smul]
  rfl

-- BENCH: cov-along-curve-exists
/-- **`covAlong` satisfies the axioms**, on the set where `γ` is differentiable. With
`eq_of_isCovDerivAlong` this makes it *the* covariant derivative along `γ`. -/
theorem isCovDerivAlong_covAlong
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (γ : ℝ → M) :
    IsCovDerivAlong cov γ (covAlong cov γ) {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t} where
  add {V W t} hV hW ht := by
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := ht
    have hdV := differentiableAt_coeffAlong hγ hV
    have hdW := differentiableAt_coeffAlong hγ hW
    simp only [covAlong, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(coeffAlong_add_eventuallyEq hγ i).deriv_eq,
      deriv_add (hdV i) (hdW i), (coeffAlong_add_eventuallyEq hγ i).eq_of_nhds]
    show (deriv (coeffAlong γ V (γ t) i) t + deriv (coeffAlong γ W (γ t) i) t)
          • canonFrame I (γ t) i (γ t)
        + (coeffAlong γ V (γ t) i t + coeffAlong γ W (γ t) i t)
          • cov (canonFrame I (γ t) i) (γ t) (velocity γ t) = _
    rw [add_smul, add_smul]
    abel
  leibniz {V f t} hV hf ht := by
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := ht
    have hdV := differentiableAt_coeffAlong hγ hV
    rw [← sum_coeffAlong_smul_canonFrame γ V t]
    simp only [covAlong, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(coeffAlong_smul_eventuallyEq hγ f i).deriv_eq,
      deriv_mul hf (hdV i), (coeffAlong_smul_eventuallyEq hγ f i).eq_of_nhds]
    show (deriv f t * coeffAlong γ V (γ t) i t + f t * deriv (coeffAlong γ V (γ t) i) t)
          • canonFrame I (γ t) i (γ t)
        + (f t * coeffAlong γ V (γ t) i t)
          • cov (canonFrame I (γ t) i) (γ t) (velocity γ t) = _
    show _ = f t • (deriv (coeffAlong γ V (γ t) i) t • canonFrame I (γ t) i (γ t)
        + coeffAlong γ V (γ t) i t • cov (canonFrame I (γ t) i) (γ t) (velocity γ t))
        + deriv f t • coeffAlong γ V (γ t) i t • canonFrame I (γ t) i (γ t)
    rw [smul_add, add_smul, smul_smul, smul_smul, smul_smul]
    abel
  restrict {Z t} hZ hγ ht := by
    set e := trivializationAt E (fun (y : M) ↦ TangentSpace I y) (γ t) with he
    set b := Module.finBasis ℝ E with hb
    have hmem : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ t)
    set a : Fin (Module.finrank ℝ E) → M → ℝ := fun i y ↦ b.repr (e ⟨y, Z y⟩).2 i with ha
    have hco : MDifferentiableAt I 𝓘(ℝ, E) (fun y ↦ (e ⟨y, Z y⟩).2) (γ t) :=
      ((e.mdifferentiableAt_totalSpace_iff I (T% Z) (e.mem_source.mpr hmem)).mp hZ).2
    have hac : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (a i) (γ t) := fun i ↦
      ((((b.coord i).toContinuousLinearMap.contMDiff (n := 1)).mdifferentiable
        (by norm_num) _).comp (γ t) hco)
    have hcanon : ∀ i, MDiffAt (T% (canonFrame I (γ t) i)) (γ t) := fun i ↦
      (contMDiff_canonFrame I (γ t) i).mdifferentiable (by norm_num) (γ t)
    have hZexp : ∀ᶠ y in 𝓝 (γ t), Z y = ∑ i, a i y • canonFrame I (γ t) i y := by
      filter_upwards [e.open_baseSet.mem_nhds hmem,
        Filter.eventually_all.mpr fun i ↦ canonFrame_eventuallyEq I (γ t) i] with y hy hfr
      rw [← sum_repr_smul_localFrame b hy (Z y)]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hfr i]
    have hcovZ : cov Z (γ t) (velocity γ t)
        = ∑ i, (a i (γ t) • cov (canonFrame I (γ t) i) (γ t) (velocity γ t)
            + mvfderiv I (a i) (γ t) (velocity γ t) • canonFrame I (γ t) i (γ t)) := by
      rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq hZ
        (mdiffAt_sum_smul_section Finset.univ (fun i _ ↦ hac i) fun i _ ↦ hcanon i)
        Filter.univ_mem hZexp]
      exact cov_sum_smul_section_apply cov Finset.univ (fun i _ ↦ hac i)
        (fun i _ ↦ hcanon i) _
    have hcoeff : ∀ i, coeffAlong γ (fun u ↦ Z (γ u)) (γ t) i = fun u ↦ a i (γ u) :=
      fun _ ↦ rfl
    simp only [covAlong, hcoeff]
    rw [hcovZ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [deriv_comp_curve (hac i) hγ]
    abel


-- BENCH: cov-along-curve-exists-unique
/-- **The covariant derivative along a curve exists**, on the set where `γ` is differentiable.
With `eq_of_isCovDerivAlong` it is unique there, so `D/dt` is well defined. -/
theorem exists_isCovDerivAlong
    (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)) (γ : ℝ → M) :
    ∃ D : (Π t : ℝ, TangentSpace I (γ t)) → Π t : ℝ, TangentSpace I (γ t),
      IsCovDerivAlong cov γ D {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t} :=
  ⟨covAlong cov γ, isCovDerivAlong_covAlong cov γ⟩

/-- Any operator satisfying the axioms **is** `covAlong` on sections differentiable along `γ`. -/
theorem eq_covAlong {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
    {D : (Π t : ℝ, TangentSpace I (γ t)) → Π t : ℝ, TangentSpace I (γ t)} {s : Set ℝ}
    (h : IsCovDerivAlong cov γ D s) (hs : s ⊆ {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t})
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hV : MDiffAlongAt γ V t) (ht : t ∈ s) :
    D V t = covAlong cov γ V t :=
  h.eq_of_isCovDerivAlong
    (((isCovDerivAlong_covAlong cov γ).mono hs)) hγ hV ht


/-! ### Parallel sections and geodesics -/

/-- **A section is parallel along `γ`** when its covariant derivative along `γ` vanishes. -/
def IsParallelAlong (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (γ : ℝ → M) (V : Π t : ℝ, TangentSpace I (γ t)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, covAlong cov γ V t = 0

/-- **A curve is a geodesic** when its velocity is parallel along it: `∇_{γ'}γ' = 0`. -/
def IsGeodesicOn (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
    (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsParallelAlong cov γ (velocity (I := I) γ) s

-- BENCH: cov-along-curve-parallel-iff
/-- **Being parallel does not depend on the construction.** Every operator satisfying the three
axioms sees the same parallel sections, and — because `covAlong` is one of them — the
quantified form is not vacuous. This is what gives the geodesic equation content. -/
theorem isParallelAlong_iff_forall {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)}
    {s : Set ℝ} (hs : s ⊆ {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t})
    (hV : ∀ t ∈ s, MDiffAlongAt γ V t) :
    IsParallelAlong cov γ V s ↔
      ∀ D : (Π t : ℝ, TangentSpace I (γ t)) → Π t : ℝ, TangentSpace I (γ t),
        IsCovDerivAlong cov γ D s → ∀ t ∈ s, D V t = 0 := by
  constructor
  · intro h D hD t ht
    rw [eq_covAlong hD hs (hs ht) (hV t ht) ht]
    exact h t ht
  · intro h t ht
    exact h (covAlong cov γ) ((isCovDerivAlong_covAlong cov γ).mono hs) t ht

/-- **The geodesic equation does not depend on the construction.** -/
theorem isGeodesicOn_iff_forall
    {cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x)} {s : Set ℝ}
    (hs : s ⊆ {t | MDifferentiableAt 𝓘(ℝ, ℝ) I γ t})
    (hv : ∀ t ∈ s, MDiffAlongAt γ (velocity (I := I) γ) t) :
    IsGeodesicOn cov γ s ↔
      ∀ D : (Π t : ℝ, TangentSpace I (γ t)) → Π t : ℝ, TangentSpace I (γ t),
        IsCovDerivAlong cov γ D s → ∀ t ∈ s, D (velocity (I := I) γ) t = 0 :=
  isParallelAlong_iff_forall hs hv

end Existence


end CovariantDerivative
