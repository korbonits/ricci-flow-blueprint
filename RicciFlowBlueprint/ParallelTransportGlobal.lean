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
import RicciFlowBlueprint.ParallelTransport

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
