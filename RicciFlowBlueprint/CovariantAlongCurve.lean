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

-- BENCH: cov-along-curve-unique
/-- **`D/dt` is determined by the ambient connection.** Two operators satisfying the three
axioms agree on every section differentiable along `γ`.

This is the frame expansion cashed in: near `t`, `V = ∑ᵢ fᵢ · (Wᵢ ∘ γ)` with `Wᵢ` global and
`fᵢ` differentiable, so locality replaces `V` by that sum, additivity splits it, Leibniz
evaluates each term, and `restrict` turns `D(Wᵢ ∘ γ)` into `∇_{γ'}Wᵢ` — an expression in which
`D` no longer occurs. -/
theorem IsCovDerivAlong.eq_of_isCovDerivAlong (h : IsCovDerivAlong cov γ D s)
    (h' : IsCovDerivAlong cov γ D' s) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : MDiffAlongAt γ V t) (ht : t ∈ s) :
    D V t = D' V t := by
  classical
  obtain ⟨ι, _, W, f, hW, hf, hexp⟩ := exists_frame_expansion hγ hV
  set Vs : ι → Π u : ℝ, TangentSpace I (γ u) := fun i ↦ (f i) • fun u ↦ W i (γ u) with hVs
  have hexp' : V =ᶠ[𝓝 t] fun u ↦ ∑ i ∈ Finset.univ, Vs i u := hexp
  have hWγ : ∀ i, MDiffAlongAt γ (fun u ↦ W i (γ u)) t := fun i ↦
    MDiffAlongAt.of_section (hW i) hγ
  have hterm : ∀ i, MDiffAlongAt γ (Vs i) t := fun i ↦ (hWγ i).smul hγ (hf i)
  have hsum : MDiffAlongAt γ (fun u ↦ ∑ i ∈ Finset.univ, Vs i u) t :=
    MDiffAlongAt.sum hγ Finset.univ fun i _ ↦ hterm i
  have key : ∀ (Dd : (Π t : ℝ, TangentSpace I (γ t)) → Π t : ℝ, TangentSpace I (γ t)),
      IsCovDerivAlong cov γ Dd s → Dd V t
        = ∑ i, (f i t • cov (W i) (γ t) (velocity γ t) + deriv (f i) t • W i (γ t)) := by
    intro Dd hd
    rw [hd.congr_of_eventuallyEq hV hsum ht hexp', hd.sum hγ ht Finset.univ fun i _ ↦ hterm i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hVs, hd.leibniz (hWγ i) (hf i) ht,
      hd.restrict ((hW i).mdifferentiable (by norm_num) (γ t)) hγ ht]
  rw [key D h, key D' h']

end Frame

end CovariantDerivative
