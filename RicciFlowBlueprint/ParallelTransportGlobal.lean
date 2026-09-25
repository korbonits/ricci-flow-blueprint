/-
**Parallel transport along an arbitrary curve**, with no chart hypotheses.

`ParallelTransport.lean` builds transport in a *trivialisation*: its statements carry a
trivialisation `e`, a basis `b`, a frame `W`, an open `U ⊆ e.baseSet`, and — the binding
constraint — `hγU : ∀ u ∈ s, γ u ∈ U`, so the curve may never leave one chart. That is
enough to prove the ODE facts and nothing more; as a tool for anything downstream it is not
usable, since a curve on a manifold does not stay in a chart.

**What is already global, and what is not.** `TransportIsometry.lean`'s
`inner_eq_of_isParallelAlong` and `norm_eq_of_isParallelAlong` carry *no* frame hypotheses at
all — they need only that `γ` and the sections are differentiable and the sections parallel.
So the *isometry* half of parallel transport is global already. What is chart-local is
exactly two things: **existence** of the parallel section, and **uniqueness**. This file
removes the chart from those two, and the transport map and its isometry then follow from
what is already proved.

**The mechanism is connectedness, not subdivision.** One does not have to chain finitely many
local transports and check the chaining is independent of the choices. For uniqueness: the
agreement set of two parallel sections is open *and has open complement*, because the
chart-local uniqueness statement propagates agreement — and disagreement — across a whole
subinterval at once. On a preconnected `s` that settles it, with no choice of subdivision to
be well-defined against.
-/
import RicciFlowBlueprint.TransportIsometry
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  {γ : ℝ → M} {V V' : Π t : ℝ, TangentSpace I (γ t)} {s : Set ℝ}

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] in
/-- **A chart to work in, around one time.** For any `u` in the open set where `γ` is
differentiable there is a closed interval `[a',c']` containing `u` in its interior, inside
`s`, along which the curve stays in a single trivialisation carrying a `C²` frame — i.e. all
the data `ParallelTransport.lean`'s statements ask for, supplied rather than assumed.

The frame comes from `exists_frame_on_open` at `γ u`; the interval comes from continuity of
`γ`, which turns the frame's open `U` into a neighbourhood of `u` in `ℝ`. -/
theorem exists_chart_interval (hs : IsOpen s)
    (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w) {u : ℝ} (hu : u ∈ s) :
    ∃ (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) (U : Set M) (a' c' : ℝ),
      IsOpen U ∧ U ⊆ (trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ u)).baseSet ∧
      (∀ i, CMDiff 2 (T% (W i))) ∧
      (∀ i, ∀ y ∈ U, W i y
        = (trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ u)).localFrame
            (Module.finBasis ℝ E) i y) ∧
      u ∈ Ioo a' c' ∧ Icc a' c' ⊆ s ∧ (∀ w ∈ Icc a' c', γ w ∈ U) := by
  classical
  set e := trivializationAt E (fun (x : M) ↦ TangentSpace I x) (γ u) with he
  have hmem : γ u ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (γ u)
  obtain ⟨U, W, hUopen, hUmem, hUe, hW, hWU⟩ :=
    exists_frame_on_open (n := 2) (e := e) (Module.finBasis ℝ E) hmem
  -- `γ ⁻¹' U ∩ s` is a neighbourhood of `u` in `ℝ`
  have hpre : γ ⁻¹' U ∩ s ∈ 𝓝 u :=
    Filter.inter_mem ((hγ u hu).continuousAt.preimage_mem_nhds (hUopen.mem_nhds hUmem))
      (hs.mem_nhds hu)
  obtain ⟨a₁, c₁, hu₁, hsub₁⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
  -- shrink to a closed interval still inside the open one
  obtain ⟨a', ha'⟩ := exists_between hu₁.1
  obtain ⟨c', hc'⟩ := exists_between hu₁.2
  refine ⟨W, U, a', c', hUopen, hUe, hW, hWU, ⟨ha'.2, hc'.1⟩, ?_, ?_⟩
  · exact fun w hw ↦ (hsub₁ ⟨lt_of_lt_of_le ha'.1 hw.1, lt_of_le_of_lt hw.2 hc'.2⟩).2
  · exact fun w hw ↦ (hsub₁ ⟨lt_of_lt_of_le ha'.1 hw.1, lt_of_le_of_lt hw.2 hc'.2⟩).1

/-- **Parallel sections agreeing at one point agree everywhere**, on a preconnected open set,
with no chart hypotheses.

The agreement set `A` is open and its complement is open, both for the same reason: the
chart-local `eqOn_of_isParallelAlong` propagates agreement across a whole subinterval at
once, so knowing the two sections agree *anywhere* in a chart interval forces agreement
throughout it — and hence disagreement anywhere in it forces disagreement throughout. On a
preconnected `s` with `A` nonempty that gives `A = s`. -/
theorem eqOn_of_isParallelAlong_global (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (hγv : ∀ w ∈ s, MDiffAlongAt γ (velocity (I := I) γ) w)
    (hV : ∀ w ∈ s, MDiffAlongAt γ V w) (hV' : ∀ w ∈ s, MDiffAlongAt γ V' w)
    (hPV : IsParallelAlong cov γ V s) (hPV' : IsParallelAlong cov γ V' s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (hinit : V t₀ = V' t₀) :
    ∀ u ∈ s, V u = V' u := by
  classical
  -- On a chart interval, agreement at one interior point spreads to the whole interval.
  have key : ∀ u ∈ s, ∃ a' c' : ℝ, u ∈ Ioo a' c' ∧ Icc a' c' ⊆ s ∧
      ∀ p ∈ Ioo a' c', V p = V' p → ∀ w ∈ Icc a' c', V w = V' w := by
    intro u hu
    obtain ⟨W, U, a', c', hUopen, hUe, hW, hWU, huIoo, hIccs, hγU⟩ :=
      exists_chart_interval hs hγ hu
    have hac : a' ≤ c' := le_of_lt (huIoo.1.trans huIoo.2)
    refine ⟨a', c', huIoo, hIccs, fun p hp hpeq w hw ↦ ?_⟩
    exact eqOn_of_isParallelAlong cov (Module.finBasis ℝ E) hUopen hUe hW hWU
      (fun x hx ↦ hγ x (hIccs hx)) (fun x hx ↦ hγv x (hIccs hx)) (fun x hx ↦ hγU x hx) hac
      (subset_refl _) hp (fun x hx ↦ hV x (hIccs hx)) (fun x hx ↦ hV' x (hIccs hx))
      (fun x hx ↦ hPV x (hIccs hx)) (fun x hx ↦ hPV' x (hIccs hx)) hpeq w hw
  set A := {u ∈ s | V u = V' u} with hA
  have hAopen : ∀ u ∈ A, ∃ J, IsOpen J ∧ u ∈ J ∧ J ∩ s ⊆ A := by
    intro u hu
    obtain ⟨a', c', huIoo, hIccs, hspread⟩ := key u hu.1
    exact ⟨Ioo a' c', isOpen_Ioo, huIoo,
      fun w hw ↦ ⟨hw.2, hspread u huIoo hu.2 w (Ioo_subset_Icc_self hw.1)⟩⟩
  have hAcompl : ∀ u ∈ s \ A, ∃ J, IsOpen J ∧ u ∈ J ∧ J ∩ s ⊆ s \ A := by
    intro u hu
    obtain ⟨a', c', huIoo, hIccs, hspread⟩ := key u hu.1
    refine ⟨Ioo a' c', isOpen_Ioo, huIoo, fun w hw ↦ ⟨hw.2, fun hwA ↦ ?_⟩⟩
    exact hu.2 ⟨hu.1, hspread w hw.1 hwA.2 u (Ioo_subset_Icc_self huIoo)⟩
  -- `s` is covered by two opens, one inside `A` and one inside its complement
  choose! Ja hJaopen hJamem hJasub using hAopen
  choose! Jb hJbopen hJbmem hJbsub using hAcompl
  by_contra hne
  push Not at hne
  obtain ⟨u, hus, huneq⟩ := hne
  have huA : u ∈ s \ A := ⟨hus, fun h ↦ huneq h.2⟩
  have ht₀A : t₀ ∈ A := ⟨ht₀, hinit⟩
  have hcover : s ⊆ (⋃ p ∈ A, Ja p) ∪ ⋃ p ∈ s \ A, Jb p := by
    intro w hw
    by_cases hwA : w ∈ A
    · exact Or.inl (Set.mem_biUnion hwA (hJamem w hwA))
    · exact Or.inr (Set.mem_biUnion ⟨hw, hwA⟩ (hJbmem w ⟨hw, hwA⟩))
  obtain ⟨w, hws, hw₁, hw₂⟩ :=
    hconn _ _ (isOpen_biUnion fun p hp ↦ hJaopen p hp)
      (isOpen_biUnion fun p hp ↦ hJbopen p hp) hcover
      ⟨t₀, ht₀, Set.mem_biUnion ht₀A (hJamem t₀ ht₀A)⟩
      ⟨u, hus, Set.mem_biUnion huA (hJbmem u huA)⟩
  simp only [Set.mem_iUnion] at hw₁ hw₂
  obtain ⟨p, hp, hwp⟩ := hw₁
  obtain ⟨q, hq, hwq⟩ := hw₂
  exact (hJbsub q hq ⟨hwq, hws⟩).2 (hJasub p hp ⟨hwp, hws⟩)

/-- **Two parallel sections glue.** On overlapping open sets with preconnected intersection,
parallel sections agreeing at one point of the overlap assemble into a parallel section on the
union, restricting to each.

**This is what global uniqueness buys.** Gluing by `if u ∈ J₁ then V₁ u else V₂ u` is only
sound because the two agree on the *whole* overlap, not merely at the one point where they
were matched — otherwise the glued function would jump at the boundary of `J₁` and be
differentiable nowhere near it. Uniqueness upgrades the pointwise match to agreement on the
overlap, after which the glued section is *locally equal* to one of the two everywhere, and
differentiability and parallelism are both local. -/
theorem exists_glue_isParallelAlong {J₁ J₂ : Set ℝ}
    (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂) (hI : IsPreconnected (J₁ ∩ J₂))
    (hγ : ∀ w ∈ J₁ ∪ J₂, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (hγv : ∀ w ∈ J₁ ∪ J₂, MDiffAlongAt γ (velocity (I := I) γ) w)
    {V₁ V₂ : Π u : ℝ, TangentSpace I (γ u)}
    (hV₁ : ∀ w ∈ J₁, MDiffAlongAt γ V₁ w) (hV₂ : ∀ w ∈ J₂, MDiffAlongAt γ V₂ w)
    (hP₁ : IsParallelAlong cov γ V₁ J₁) (hP₂ : IsParallelAlong cov γ V₂ J₂)
    {p : ℝ} (hp : p ∈ J₁ ∩ J₂) (heq : V₁ p = V₂ p) :
    ∃ V : Π u : ℝ, TangentSpace I (γ u),
      (∀ w ∈ J₁, V w = V₁ w) ∧ (∀ w ∈ J₂, V w = V₂ w) ∧
      (∀ w ∈ J₁ ∪ J₂, MDiffAlongAt γ V w) ∧ IsParallelAlong cov γ V (J₁ ∪ J₂) := by
  classical
  have hagree : ∀ w ∈ J₁ ∩ J₂, V₁ w = V₂ w :=
    eqOn_of_isParallelAlong_global cov (hJ₁.inter hJ₂) hI
      (fun w hw ↦ hγ w (Or.inl hw.1)) (fun w hw ↦ hγv w (Or.inl hw.1))
      (fun w hw ↦ hV₁ w hw.1) (fun w hw ↦ hV₂ w hw.2)
      (fun w hw ↦ hP₁ w hw.1) (fun w hw ↦ hP₂ w hw.2) hp heq
  set V : Π u : ℝ, TangentSpace I (γ u) := fun u ↦ if u ∈ J₁ then V₁ u else V₂ u with hVdef
  have hVJ₁ : ∀ w ∈ J₁, V w = V₁ w := fun w hw ↦ by simp only [hVdef, hw, ↓reduceIte]
  have hVJ₂ : ∀ w ∈ J₂, V w = V₂ w := by
    intro w hw
    by_cases h : w ∈ J₁
    · rw [hVJ₁ w h]; exact hagree w ⟨h, hw⟩
    · simp only [hVdef, h, ↓reduceIte]
  -- near any point of `J₁` the glued section *is* `V₁`, and likewise for `J₂`
  have hev₁ : ∀ w ∈ J₁, (fun u ↦ (⟨γ u, V u⟩ : TangentBundle I M))
      =ᶠ[𝓝 w] fun u ↦ (⟨γ u, V₁ u⟩ : TangentBundle I M) := fun w hw ↦
    Filter.eventually_of_mem (hJ₁.mem_nhds hw) fun y hy ↦ by
      show (⟨γ y, V y⟩ : TangentBundle I M) = ⟨γ y, V₁ y⟩
      rw [hVJ₁ y hy]
  have hev₂ : ∀ w ∈ J₂, (fun u ↦ (⟨γ u, V u⟩ : TangentBundle I M))
      =ᶠ[𝓝 w] fun u ↦ (⟨γ u, V₂ u⟩ : TangentBundle I M) := fun w hw ↦
    Filter.eventually_of_mem (hJ₂.mem_nhds hw) fun y hy ↦ by
      show (⟨γ y, V y⟩ : TangentBundle I M) = ⟨γ y, V₂ y⟩
      rw [hVJ₂ y hy]
  have hVsec₁ : ∀ w ∈ J₁, V =ᶠ[𝓝 w] V₁ := fun w hw ↦
    Filter.eventually_of_mem (hJ₁.mem_nhds hw) fun y hy ↦ hVJ₁ y hy
  have hVsec₂ : ∀ w ∈ J₂, V =ᶠ[𝓝 w] V₂ := fun w hw ↦
    Filter.eventually_of_mem (hJ₂.mem_nhds hw) fun y hy ↦ hVJ₂ y hy
  have hVd : ∀ w ∈ J₁ ∪ J₂, MDiffAlongAt γ V w := by
    rintro w (hw | hw)
    · exact (hV₁ w hw).congr_of_eventuallyEq (hev₁ w hw)
    · exact (hV₂ w hw).congr_of_eventuallyEq (hev₂ w hw)
  refine ⟨V, hVJ₁, hVJ₂, hVd, ?_⟩
  rintro w (hw | hw)
  · rw [(isCovDerivAlong_covAlong cov γ).congr_of_eventuallyEq (hVd w (Or.inl hw))
      (hV₁ w hw) (hγ w (Or.inl hw)) (hVsec₁ w hw)]
    exact hP₁ w hw
  · rw [(isCovDerivAlong_covAlong cov γ).congr_of_eventuallyEq (hVd w (Or.inr hw))
      (hV₂ w hw) (hγ w (Or.inr hw)) (hVsec₂ w hw)]
    exact hP₂ w hw

/-- **A transport interval.** Around any time there is an open preconnected interval inside
`s` supporting parallel transport *from any of its points*, with any prescribed value there.

Quantifying over the base point rather than fixing it at the centre is what makes this usable
twice over: the reachability argument below needs to start a local section at whatever point
it already knows about, not at the point the chart was built around. It costs nothing —
`exists_isParallelAlong` already allows any base point in its interval.

`exists_isParallelAlong` delivers a section on a *closed* interval and demands the curve stay
in the chart on all of the ambient open set; both are arranged by shrinking twice — once to a
closed interval inside the chart, once to an open one inside that. Open is what gluing
consumes. -/
theorem exists_transport_interval (hs : IsOpen s)
    (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (hγv : ∀ w ∈ s, MDiffAlongAt γ (velocity (I := I) γ) w)
    {u : ℝ} (hu : u ∈ s) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ u ∈ J ∧ J ⊆ s ∧
      ∀ p ∈ J, ∀ x : TangentSpace I (γ p),
        ∃ V : Π w : ℝ, TangentSpace I (γ w), V p = x ∧
          (∀ w ∈ J, MDiffAlongAt γ V w) ∧ IsParallelAlong cov γ V J := by
  obtain ⟨W, U, a', c', hUopen, hUe, hW, hWU, huIoo, hIccs, hγU⟩ :=
    exists_chart_interval hs hγ hu
  obtain ⟨a'', ha''⟩ := exists_between huIoo.1
  obtain ⟨c'', hc''⟩ := exists_between huIoo.2
  have hsubIcc : Icc a'' c'' ⊆ Ioo a' c' := fun w hw ↦
    ⟨lt_of_lt_of_le ha''.1 hw.1, lt_of_le_of_lt hw.2 hc''.2⟩
  have hIoo_s : Ioo a' c' ⊆ s := fun w hw ↦ hIccs (Ioo_subset_Icc_self hw)
  have hac'' : a'' ≤ c'' := le_of_lt (ha''.2.trans hc''.1)
  refine ⟨Ioo a'' c'', isOpen_Ioo, isPreconnected_Ioo, ⟨ha''.2, hc''.1⟩,
    fun w hw ↦ hIoo_s (hsubIcc (Ioo_subset_Icc_self hw)), fun p hp x ↦ ?_⟩
  obtain ⟨V, hVp, hVd, hVP⟩ :=
    exists_isParallelAlong cov (Module.finBasis ℝ E) hUopen hUe hW hWU isOpen_Ioo
      (fun w hw ↦ hγ w (hIoo_s hw)) (fun w hw ↦ hγv w (hIoo_s hw))
      (fun w hw ↦ hγU w (Ioo_subset_Icc_self hw)) hac'' hsubIcc
      (Ioo_subset_Icc_self hp) x
  exact ⟨V, hVp, fun w hw ↦ hVd w (Ioo_subset_Icc_self hw),
    fun w hw ↦ hVP w (Ioo_subset_Icc_self hw)⟩

/-- **Parallel transport exists along any curve**, on a preconnected open set, with no chart
hypotheses: through every `v ∈ T_{γ(t₀)}\M` there is a section parallel along `γ` on all of
`s`.

**Two connectedness arguments, and no subdivision.** First, the set of times *reachable* from
`t₀` — joined to it by a connected open set carrying a parallel section through `v` — is open
and has open complement, because a transport interval meeting it is swallowed by it: glue the
reaching section to a local one started at the meeting point. So every time is reachable.
Second, the reaching sections are assembled into one global section pointwise, `V r` being the
value at `r` of *its own* witness. That is well defined because any two witnesses agree at
`t₀` and so, by `eqOn_of_isParallelAlong_global` on their preconnected intersection, agree
throughout it — which also makes `V` locally equal to a witness, hence differentiable and
parallel.

Nothing here chooses a subdivision, so nothing has to be proved independent of one. -/
theorem exists_isParallelAlong_global (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (hγv : ∀ w ∈ s, MDiffAlongAt γ (velocity (I := I) γ) w)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (v : TangentSpace I (γ t₀)) :
    ∃ V : Π u : ℝ, TangentSpace I (γ u), V t₀ = v ∧
      (∀ u ∈ s, MDiffAlongAt γ V u) ∧ IsParallelAlong cov γ V s := by
  classical
  have hord : ∀ {A B : Set ℝ}, IsPreconnected A → IsPreconnected B → IsPreconnected (A ∩ B) := by
    intro A B hA hB
    rw [isPreconnected_iff_ordConnected] at hA hB ⊢
    exact hA.inter hB
  set Reach : Set ℝ := {r | ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ t₀ ∈ J ∧ r ∈ J ∧ J ⊆ s ∧
    ∃ V : Π w : ℝ, TangentSpace I (γ w), V t₀ = v ∧
      (∀ w ∈ J, MDiffAlongAt γ V w) ∧ IsParallelAlong cov γ V J} with hReachDef
  -- a transport interval that meets `Reach` is contained in it
  have spread : ∀ J' : Set ℝ, IsOpen J' → IsPreconnected J' → J' ⊆ s →
      (∀ p ∈ J', ∀ x : TangentSpace I (γ p), ∃ V' : Π w : ℝ, TangentSpace I (γ w), V' p = x ∧
        (∀ w ∈ J', MDiffAlongAt γ V' w) ∧ IsParallelAlong cov γ V' J') →
      ∀ p ∈ J', p ∈ Reach → J' ⊆ Reach := by
    intro J' hJ'o hJ'c hJ's htr p hpJ' hpR q hqJ'
    obtain ⟨J, hJo, hJc, ht₀J, hpJ, hJs, V, hVt₀, hVd, hVP⟩ := hpR
    obtain ⟨V', hV'p, hV'd, hV'P⟩ := htr p hpJ' (V p)
    have hun : ∀ w ∈ J ∪ J', w ∈ s := by
      rintro w (h | h); exacts [hJs h, hJ's h]
    obtain ⟨Vg, hgJ, hgJ', hgd, hgP⟩ :=
      exists_glue_isParallelAlong cov hJo hJ'o (hord hJc hJ'c)
        (fun w hw ↦ hγ w (hun w hw)) (fun w hw ↦ hγv w (hun w hw))
        hVd hV'd hVP hV'P ⟨hpJ, hpJ'⟩ hV'p.symm
    exact ⟨J ∪ J', hJo.union hJ'o, hJc.union p hpJ hpJ' hJ'c, Or.inl ht₀J, Or.inr hqJ',
      hun, Vg, by rw [hgJ t₀ ht₀J]; exact hVt₀, hgd, hgP⟩
  have hloc : ∀ r ∈ s, ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ r ∈ J ∧ J ⊆ s ∧
      ∀ p ∈ J, ∀ x : TangentSpace I (γ p), ∃ V' : Π w : ℝ, TangentSpace I (γ w), V' p = x ∧
        (∀ w ∈ J, MDiffAlongAt γ V' w) ∧ IsParallelAlong cov γ V' J :=
    fun r hr ↦ exists_transport_interval cov hs hγ hγv hr
  choose! J' hJ'o hJ'c hJ'mem hJ's hJ'tr using hloc
  have ht₀R : t₀ ∈ Reach := by
    obtain ⟨V, hVt₀, hVd, hVP⟩ :=
      hJ'tr t₀ ht₀ t₀ (hJ'mem t₀ ht₀) v
    exact ⟨J' t₀, hJ'o t₀ ht₀, hJ'c t₀ ht₀, hJ'mem t₀ ht₀, hJ'mem t₀ ht₀, hJ's t₀ ht₀,
      V, hVt₀, hVd, hVP⟩
  -- every time is reachable
  have hall : ∀ r ∈ s, r ∈ Reach := by
    by_contra hne
    push Not at hne
    obtain ⟨q, hqs, hqR⟩ := hne
    obtain ⟨w, hws, hw₁, hw₂⟩ :=
      hconn _ _ (isOpen_biUnion fun p hp ↦ hJ'o p hp.1) (isOpen_biUnion fun p hp ↦ hJ'o p hp.1)
        (fun r hr ↦ by
          by_cases hrR : r ∈ Reach
          · exact Or.inl (Set.mem_biUnion (show r ∈ {z | z ∈ s ∧ z ∈ Reach} from ⟨hr, hrR⟩)
              (hJ'mem r hr))
          · exact Or.inr (Set.mem_biUnion (show r ∈ {z | z ∈ s ∧ z ∉ Reach} from ⟨hr, hrR⟩)
              (hJ'mem r hr)))
        ⟨t₀, ht₀, Set.mem_biUnion (show t₀ ∈ {z | z ∈ s ∧ z ∈ Reach} from ⟨ht₀, ht₀R⟩)
          (hJ'mem t₀ ht₀)⟩
        ⟨q, hqs, Set.mem_biUnion (show q ∈ {z | z ∈ s ∧ z ∉ Reach} from ⟨hqs, hqR⟩)
          (hJ'mem q hqs)⟩
    simp only [Set.mem_iUnion] at hw₁ hw₂
    obtain ⟨p, hp, hwp⟩ := hw₁
    obtain ⟨p', hp', hwp'⟩ := hw₂
    -- `w` is reachable from the first family, so the second family's interval is too
    have hwR : w ∈ Reach :=
      spread (J' p) (hJ'o p hp.1) (hJ'c p hp.1) (hJ's p hp.1) (hJ'tr p hp.1) p
        (hJ'mem p hp.1) hp.2 hwp
    exact hp'.2 (spread (J' p') (hJ'o p' hp'.1) (hJ'c p' hp'.1) (hJ's p' hp'.1)
      (hJ'tr p' hp'.1) w hwp' hwR (hJ'mem p' hp'.1))
  -- assemble the witnesses into one section
  have hreach : ∀ r ∈ s, ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ t₀ ∈ J ∧ r ∈ J ∧ J ⊆ s ∧
      ∃ V : Π w : ℝ, TangentSpace I (γ w), V t₀ = v ∧
        (∀ w ∈ J, MDiffAlongAt γ V w) ∧ IsParallelAlong cov γ V J := hall
  choose! Jr hJro hJrc ht₀Jr hrJr hJrs Vr hVrt₀ hVrd hVrP using hreach
  have hkey : ∀ r ∈ s, ∀ w ∈ Jr r, Vr w w = Vr r w := by
    intro r hr w hw
    have hws : w ∈ s := hJrs r hr hw
    have h := eqOn_of_isParallelAlong_global cov ((hJro r hr).inter (hJro w hws))
      (hord (hJrc r hr) (hJrc w hws))
      (fun z hz ↦ hγ z (hJrs r hr hz.1)) (fun z hz ↦ hγv z (hJrs r hr hz.1))
      (fun z hz ↦ hVrd r hr z hz.1) (fun z hz ↦ hVrd w hws z hz.2)
      (fun z hz ↦ hVrP r hr z hz.1) (fun z hz ↦ hVrP w hws z hz.2)
      ⟨ht₀Jr r hr, ht₀Jr w hws⟩ (by rw [hVrt₀ r hr, hVrt₀ w hws])
    exact (h w ⟨hw, hrJr w hws⟩).symm
  have hev : ∀ r ∈ s, (fun u ↦ (⟨γ u, Vr u u⟩ : TangentBundle I M))
      =ᶠ[𝓝 r] fun u ↦ (⟨γ u, Vr r u⟩ : TangentBundle I M) := by
    refine fun r hr ↦ Filter.eventually_of_mem ((hJro r hr).mem_nhds (hrJr r hr)) fun w hw ↦ ?_
    show (⟨γ w, Vr w w⟩ : TangentBundle I M) = ⟨γ w, Vr r w⟩
    rw [hkey r hr w hw]
  have hevs : ∀ r ∈ s, (fun u ↦ Vr u u) =ᶠ[𝓝 r] Vr r := fun r hr ↦
    Filter.eventually_of_mem ((hJro r hr).mem_nhds (hrJr r hr)) fun w hw ↦ hkey r hr w hw
  have hVd : ∀ r ∈ s, MDiffAlongAt γ (fun u ↦ Vr u u) r := fun r hr ↦
    (hVrd r hr r (hrJr r hr)).congr_of_eventuallyEq (hev r hr)
  refine ⟨fun u ↦ Vr u u, hVrt₀ t₀ ht₀, hVd, fun r hr ↦ ?_⟩
  rw [(isCovDerivAlong_covAlong cov γ).congr_of_eventuallyEq (hVd r hr)
    (hVrd r hr r (hrJr r hr)) (hγ r hr) (hevs r hr)]
  exact hVrP r hr r (hrJr r hr)

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- Parallel sections add. -/
theorem isParallelAlong_add (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    {V₁ V₂ : Π u : ℝ, TangentSpace I (γ u)}
    (hV₁ : ∀ w ∈ s, MDiffAlongAt γ V₁ w) (hV₂ : ∀ w ∈ s, MDiffAlongAt γ V₂ w)
    (hP₁ : IsParallelAlong cov γ V₁ s) (hP₂ : IsParallelAlong cov γ V₂ s) :
    IsParallelAlong cov γ (V₁ + V₂) s := fun u hu ↦ by
  rw [(isCovDerivAlong_covAlong cov γ).add (hV₁ u hu) (hV₂ u hu) (hγ u hu), hP₁ u hu, hP₂ u hu,
    add_zero]

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- Parallel sections scale. The Leibniz term dies because the scalar is constant. -/
theorem isParallelAlong_const_smul (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    {V₁ : Π u : ℝ, TangentSpace I (γ u)} (r : ℝ)
    (hV₁ : ∀ w ∈ s, MDiffAlongAt γ V₁ w) (hP₁ : IsParallelAlong cov γ V₁ s) :
    IsParallelAlong cov γ ((fun _ : ℝ ↦ r) • V₁) s := fun u hu ↦ by
  rw [(isCovDerivAlong_covAlong cov γ).leibniz (hV₁ u hu) (differentiableAt_const r) (hγ u hu),
    hP₁ u hu, deriv_const]
  simp

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **A finite sum of parallel sections is parallel.** No induction is needed here: `D/dt` is
already known additive over finite sums (`IsCovDerivAlong.sum`), so this is one rewrite. -/
theorem isParallelAlong_sum (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    {κ : Type*} (a : Finset κ) {Vs : κ → Π u : ℝ, TangentSpace I (γ u)}
    (hV : ∀ i ∈ a, ∀ w ∈ s, MDiffAlongAt γ (Vs i) w)
    (hP : ∀ i ∈ a, IsParallelAlong cov γ (Vs i) s) :
    IsParallelAlong cov γ (fun u ↦ ∑ i ∈ a, Vs i u) s := fun u hu ↦ by
  rw [(isCovDerivAlong_covAlong cov γ).sum (hγ u hu) (hγ u hu) a fun i hi ↦ hV i hi u hu]
  exact Finset.sum_eq_zero fun i hi ↦ hP i hi u hu

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **A constant-coefficient combination of parallel sections is parallel.** This is the form a
parallel *frame* is consumed in: a vector with fixed coordinates in a parallel frame is
itself parallel. -/
theorem isParallelAlong_sum_smul (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    {κ : Type*} (a : Finset κ) (c : κ → ℝ) {Vs : κ → Π u : ℝ, TangentSpace I (γ u)}
    (hV : ∀ i ∈ a, ∀ w ∈ s, MDiffAlongAt γ (Vs i) w)
    (hP : ∀ i ∈ a, IsParallelAlong cov γ (Vs i) s) :
    IsParallelAlong cov γ (fun u ↦ ∑ i ∈ a, c i • Vs i u) s :=
  isParallelAlong_sum cov (Vs := fun i u ↦ c i • Vs i u) hγ a
    (fun i hi w hw ↦ MDiffAlongAt.smul (hγ w hw) (differentiableAt_const (c i)) (hV i hi w hw))
    (fun i hi ↦ isParallelAlong_const_smul cov hγ (c i) (hV i hi) (hP i hi))

section Isometry

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

/-- **Parallel transport along an arbitrary curve, as a linear isometry of fibres.**

This is the usable form. `ParallelTransport.lean`'s isometry carries a trivialisation, a
basis, a frame, an open set inside the base set and the hypothesis that the curve never
leaves it; here the only hypotheses are that the connection is metric and that `γ` is
differentiable on a preconnected open `s`.

Everything is assembled from parts already proved: existence and uniqueness with no chart
(above), linearity from the two axioms of `D/dt` (addition, and the Leibniz rule with a
constant scalar, whose derivative term vanishes), and the norm identity from
`norm_eq_of_isParallelAlong`, which never needed a chart to begin with. Invertibility is
transport in the other direction, and the two compose to the identity by uniqueness. -/
theorem exists_parallelTransportIsometry_global
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ w)
    (hγv : ∀ w ∈ s, MDiffAlongAt γ (velocity (I := I) γ) w)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {t : ℝ} (ht : t ∈ s) :
    ∃ P : TangentSpace I (γ t₀) ≃ₗᵢ[ℝ] TangentSpace I (γ t),
      ∀ V : Π u : ℝ, TangentSpace I (γ u), (∀ u ∈ s, MDiffAlongAt γ V u) →
        IsParallelAlong cov γ V s → V t = P (V t₀) := by
  classical
  have hex : ∀ {p : ℝ}, p ∈ s → ∀ x : TangentSpace I (γ p),
      ∃ V : Π u : ℝ, TangentSpace I (γ u), V p = x ∧
        (∀ u ∈ s, MDiffAlongAt γ V u) ∧ IsParallelAlong cov γ V s :=
    fun hp x ↦ exists_isParallelAlong_global cov hs hconn hγ hγv hp x
  -- two parallel sections agreeing at one of the two times agree at the other
  have key : ∀ {p q : ℝ}, p ∈ s → q ∈ s → ∀ V₁ V₂ : Π u : ℝ, TangentSpace I (γ u),
      (∀ u ∈ s, MDiffAlongAt γ V₁ u) → IsParallelAlong cov γ V₁ s →
      (∀ u ∈ s, MDiffAlongAt γ V₂ u) → IsParallelAlong cov γ V₂ s →
      V₁ p = V₂ p → V₁ q = V₂ q := fun hp hq V₁ V₂ h₁d h₁P h₂d h₂P h ↦
    eqOn_of_isParallelAlong_global cov hs hconn hγ hγv h₁d h₂d h₁P h₂P hp h _ hq
  -- transport from `p` to `q`, characterised by computing every parallel section
  have transp : ∀ {p q : ℝ}, p ∈ s → q ∈ s →
      ∃ F : TangentSpace I (γ p) → TangentSpace I (γ q),
        ∀ V : Π u : ℝ, TangentSpace I (γ u), (∀ u ∈ s, MDiffAlongAt γ V u) →
          IsParallelAlong cov γ V s → V q = F (V p) := by
    intro p q hp hq
    refine ⟨fun x ↦ (Classical.choose (hex hp x)) q, fun V hVd hVP ↦ ?_⟩
    obtain ⟨h0, hd, hP⟩ := Classical.choose_spec (hex hp (V p))
    exact key hp hq V _ hVd hVP hd hP h0.symm
  obtain ⟨F, hF⟩ := transp ht₀ ht
  obtain ⟨G, hG⟩ := transp ht ht₀
  -- the section realising `F x`
  have hsec : ∀ x : TangentSpace I (γ t₀), ∃ V : Π u : ℝ, TangentSpace I (γ u), V t₀ = x ∧
      (∀ u ∈ s, MDiffAlongAt γ V u) ∧ IsParallelAlong cov γ V s ∧ V t = F x := by
    intro x
    obtain ⟨V, h0, hd, hP⟩ := hex ht₀ x
    exact ⟨V, h0, hd, hP, by rw [hF V hd hP, h0]⟩
  have hsec' : ∀ y : TangentSpace I (γ t), ∃ V : Π u : ℝ, TangentSpace I (γ u), V t = y ∧
      (∀ u ∈ s, MDiffAlongAt γ V u) ∧ IsParallelAlong cov γ V s ∧ V t₀ = G y := by
    intro y
    obtain ⟨V, h0, hd, hP⟩ := hex ht y
    exact ⟨V, h0, hd, hP, by rw [hG V hd hP, h0]⟩
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    obtain ⟨V₁, h10, h1d, h1P, h1t⟩ := hsec x
    obtain ⟨V₂, h20, h2d, h2P, h2t⟩ := hsec y
    have hsumd : ∀ u ∈ s, MDiffAlongAt γ (V₁ + V₂) u := fun u hu ↦
      MDiffAlongAt.add (hγ u hu) (h1d u hu) (h2d u hu)
    have hsumP := isParallelAlong_add cov hγ h1d h2d h1P h2P
    have h := hF (V₁ + V₂) hsumd hsumP
    have e₀ : (V₁ + V₂) t₀ = x + y := by show V₁ t₀ + V₂ t₀ = x + y; rw [h10, h20]
    have e₁ : (V₁ + V₂) t = F x + F y := by show V₁ t + V₂ t = F x + F y; rw [h1t, h2t]
    rw [e₀] at h
    rw [← h, e₁]
  have hsmul : ∀ (r : ℝ) x, F (r • x) = r • F x := by
    intro r x
    obtain ⟨V₁, h10, h1d, h1P, h1t⟩ := hsec x
    have hrd : ∀ u ∈ s, MDiffAlongAt γ ((fun _ : ℝ ↦ r) • V₁) u := fun u hu ↦
      MDiffAlongAt.smul (hγ u hu) (differentiableAt_const r) (h1d u hu)
    have hrP := isParallelAlong_const_smul cov hγ r h1d h1P
    have h := hF ((fun _ : ℝ ↦ r) • V₁) hrd hrP
    have e₀ : ((fun _ : ℝ ↦ r) • V₁) t₀ = r • x := by show r • V₁ t₀ = r • x; rw [h10]
    have e₁ : ((fun _ : ℝ ↦ r) • V₁) t = r • F x := by show r • V₁ t = r • F x; rw [h1t]
    rw [e₀] at h
    rw [← h, e₁]
  have hGF : ∀ x, G (F x) = x := by
    intro x
    obtain ⟨V, h0, hd, hP, hVt⟩ := hsec x
    rw [← hVt, ← hG V hd hP, h0]
  have hFG : ∀ y, F (G y) = y := by
    intro y
    obtain ⟨V, h0, hd, hP, hVt₀⟩ := hsec' y
    rw [← hVt₀, ← hF V hd hP, h0]
  have hnorm : ∀ x, ‖F x‖ = ‖x‖ := by
    intro x
    obtain ⟨V, h0, hd, hP, hVt⟩ := hsec x
    have hI : Icc (t₀ ⊓ t) (t₀ ⊔ t) ⊆ s :=
      (isPreconnected_iff_ordConnected.mp hconn).uIcc_subset ht₀ ht
    have hmem₀ : t₀ ∈ Icc (t₀ ⊓ t) (t₀ ⊔ t) := ⟨inf_le_left, le_sup_left⟩
    have hmemt : t ∈ Icc (t₀ ⊓ t) (t₀ ⊔ t) := ⟨inf_le_right, le_sup_right⟩
    have h₁ := norm_eq_of_isParallelAlong cov hmet (fun u hu ↦ hγ u (hI hu))
      (fun u hu ↦ hd u (hI hu)) (fun u hu ↦ hP u (hI hu)) hmemt
    have h₂ := norm_eq_of_isParallelAlong cov hmet (fun u hu ↦ hγ u (hI hu))
      (fun u hu ↦ hd u (hI hu)) (fun u hu ↦ hP u (hI hu)) hmem₀
    rw [← hVt, h₁, ← h₂, h0]
  exact ⟨{ toFun := F, map_add' := hadd, map_smul' := hsmul, invFun := G,
           left_inv := hGF, right_inv := hFG, norm_map' := hnorm }, hF⟩

end Isometry
