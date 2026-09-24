/-
**A parallel orthonormal frame along a curve.**

`ParallelTransportGlobal.lean` transports one vector; this transports a whole orthonormal
basis and checks that it stays orthonormal, so that every fibre along the curve acquires an
orthonormal basis depending on nothing but the basis chosen at the start.

**Why this is the next brick on the cross-fibre maximum principle, and why it is cheap.**
`BundleMaximumPrinciple.lean` does the *touching-point* half: at a spatial maximum of
`⟪N,u⟫` with `N` a normal section, `⟪n, Δu x⟫ ≤ 0`. What is left is the cross-fibre
comparison, where the first-touching-time argument compares `dist(u(t,x), K_x)` between
*different* fibres. Hamilton's device is to carry the tested direction along the curve by
parallel transport, so that `|N|` and the support function of `K` are constant and a maximum
of the distance is a maximum of `⟪N,u⟫`.

A parallel *orthonormal frame* is what makes that comparison a statement about a **fixed**
inner product space: it trivialises `TM` isometrically along the curve, hence trivialises
`End(TM)` isometrically for the Hilbert–Schmidt metric, and `IveyEndo.lean`'s
`mem_iveyEndoSet_conj_iff` says the pinching set is carried across. So the bundle-valued
comparison reduces along each curve to the trivial-bundle case
`TensorMaximumPrinciple.lean` already handles.

**Nothing new is transported.** The frame is `exists_isParallelAlong_global` applied once per
basis vector, and the orthonormality is `TransportIsometry.lean`'s constancy of the pairing,
which carries no frame hypotheses and so was global already. The one adjustment is that the
constancy is stated there on a closed interval based at its left endpoint, and here it is
wanted on a preconnected open set based at an arbitrary time — which is two cases of
order-connectedness, not a new argument.
-/
import RicciFlowBlueprint.ParallelTransportGlobal

open Bundle Filter Set RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ}

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **Constancy of the pairing of two parallel sections, on a preconnected open set and based
at an arbitrary time.**

`TransportIsometry.lean` proves this on a closed interval, based at its *left endpoint*. The
adjustment is two cases of order-connectedness — in `ℝ` a preconnected set is order-connected,
so the closed interval between the two times lies in `s` — and no part of the argument
changes. -/
theorem inner_eq_of_isParallelAlong_global
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    {V V' : Π u : ℝ, TangentSpace I (γ u)}
    (hV : ∀ u ∈ s, MDiffAlongAt γ V u) (hV' : ∀ u ∈ s, MDiffAlongAt γ V' u)
    (hPV : IsParallelAlong cov γ V s) (hPV' : IsParallelAlong cov γ V' s)
    {t₀ u : ℝ} (ht₀ : t₀ ∈ s) (hu : u ∈ s) :
    ⟪V u, V' u⟫ = ⟪V t₀, V' t₀⟫ := by
  rw [isPreconnected_iff_ordConnected] at hconn
  rcases le_total t₀ u with h | h
  · have hsub : Icc t₀ u ⊆ s := hconn.out ht₀ hu
    exact inner_eq_of_isParallelAlong cov hmet (fun w hw ↦ hγ w (hsub hw))
      (fun w hw ↦ hV w (hsub hw)) (fun w hw ↦ hV' w (hsub hw))
      (fun w hw ↦ hPV w (hsub hw)) (fun w hw ↦ hPV' w (hsub hw)) (right_mem_Icc.mpr h)
  · have hsub : Icc u t₀ ⊆ s := hconn.out hu ht₀
    exact (inner_eq_of_isParallelAlong cov hmet (fun w hw ↦ hγ w (hsub hw))
      (fun w hw ↦ hV w (hsub hw)) (fun w hw ↦ hV' w (hsub hw))
      (fun w hw ↦ hPV w (hsub hw)) (fun w hw ↦ hPV' w (hsub hw)) (right_mem_Icc.mpr h)).symm

-- BENCH: parallel-orthonormal-frame
/-- **A parallel orthonormal frame along a curve.**

Transport an orthonormal basis of one fibre along `γ`; the result is orthonormal in every
fibre, because the pairing of two parallel sections is constant.

The whole content is that the *same* constancy statement serves for both the diagonal and the
off-diagonal pairings, so orthonormality is preserved as one condition rather than a norm
statement and an angle statement proved separately. -/
theorem exists_parallel_orthonormal_frame_along
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀))) :
    ∃ fr : ι → Π u : ℝ, TangentSpace I (γ u),
      (∀ i, fr i t₀ = b i) ∧
      (∀ i, ∀ u ∈ s, MDiffAlongAt γ (fr i) u) ∧
      (∀ i, IsParallelAlong cov γ (fr i) s) ∧
      (∀ u ∈ s, Orthonormal ℝ fun i ↦ fr i u) := by
  classical
  choose fr hfr0 hfrd hfrp using fun i ↦
    exists_isParallelAlong_global cov hs hconn hγ hγv ht₀ (b i)
  refine ⟨fr, hfr0, hfrd, hfrp, fun u hu ↦ ?_⟩
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_eq_of_isParallelAlong_global cov hmet hconn hγ (hfrd i) (hfrd j) (hfrp i) (hfrp j)
    ht₀ hu, hfr0 i, hfr0 j]
  exact orthonormal_iff_ite.mp b.orthonormal i j

/-- **Every fibre along the curve acquires an orthonormal basis**, transported from the one
chosen at `t₀`.

An orthonormal family of the right cardinality in a finite-dimensional space is a basis, and
the cardinality is right because `b` is one at `t₀` and `finrank` does not vary. -/
theorem exists_parallel_orthonormalBasis_along
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀))) :
    ∃ fr : ι → Π u : ℝ, TangentSpace I (γ u),
      (∀ i, fr i t₀ = b i) ∧
      (∀ i, ∀ u ∈ s, MDiffAlongAt γ (fr i) u) ∧
      (∀ i, IsParallelAlong cov γ (fr i) s) ∧
      ∀ u ∈ s, ∃ bu : OrthonormalBasis ι ℝ (TangentSpace I (γ u)), ∀ i, bu i = fr i u := by
  obtain ⟨fr, hfr0, hfrd, hfrp, hfron⟩ :=
    exists_parallel_orthonormal_frame_along cov hmet hs hconn hγ hγv ht₀ b
  refine ⟨fr, hfr0, hfrd, hfrp, fun u hu ↦ ?_⟩
  have hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ u)) :=
    (Module.finrank_eq_card_basis b.toBasis).symm
  set bas := basisOfOrthonormalOfCardEqFinrank (hfron u hu) hcard with hbas
  have hcoe : ⇑bas = fun i ↦ fr i u := coe_basisOfOrthonormalOfCardEqFinrank _ _
  refine ⟨bas.toOrthonormalBasis (by rw [hcoe]; exact hfron u hu), fun i ↦ ?_⟩
  rw [Module.Basis.coe_toOrthonormalBasis, hcoe]

omit [CompleteSpace E] [ContMDiffVectorBundle 2 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **The coordinates of a parallel section in a parallel frame are constant.**

This is what the frame is for. Along the curve the section and the frame move together, so in
frame coordinates a parallel section is a fixed vector of `ℝ^n` --- which is the sense in which
the frame trivialises the bundle isometrically. -/
theorem inner_eq_of_isParallelAlong_frame
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    {V fr : Π u : ℝ, TangentSpace I (γ u)}
    (hV : ∀ u ∈ s, MDiffAlongAt γ V u) (hfr : ∀ u ∈ s, MDiffAlongAt γ fr u)
    (hPV : IsParallelAlong cov γ V s) (hPfr : IsParallelAlong cov γ fr s)
    {t₀ u : ℝ} (ht₀ : t₀ ∈ s) (hu : u ∈ s) :
    ⟪V u, fr u⟫ = ⟪V t₀, fr t₀⟫ :=
  inner_eq_of_isParallelAlong_global cov hmet hconn hγ hV hfr hPV hPfr ht₀ hu

-- BENCH: parallel-transport-frame
/-- **Parallel transport is the map carrying the frame to the frame.**

`exists_parallelTransportIsometry_global` produces the isometry abstractly, as whatever sends
each parallel section's value at `t₀` to its value at `u`. Pairing it with the frame says what
it *does*: it takes the chosen orthonormal basis of the starting fibre to the transported
orthonormal basis of the target fibre. That is the form a coordinate computation consumes, and
the form in which the transport is visibly a change of orthonormal basis rather than an
abstract isometry. -/
theorem exists_parallelTransportIsometry_frame
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hγv : ∀ u ∈ s, MDiffAlongAt γ (velocity (I := I) γ) u)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {u : ℝ} (hu : u ∈ s) {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I (γ t₀))) :
    ∃ (fr : ι → Π w : ℝ, TangentSpace I (γ w))
      (P : TangentSpace I (γ t₀) ≃ₗᵢ[ℝ] TangentSpace I (γ u)),
      (∀ i, fr i t₀ = b i) ∧
      (∀ i, ∀ w ∈ s, MDiffAlongAt γ (fr i) w) ∧
      (∀ i, IsParallelAlong cov γ (fr i) s) ∧
      (∃ bu : OrthonormalBasis ι ℝ (TangentSpace I (γ u)), ∀ i, bu i = fr i u) ∧
      (∀ i, P (b i) = fr i u) ∧
      ∀ V : Π w : ℝ, TangentSpace I (γ w), (∀ w ∈ s, MDiffAlongAt γ V w) →
        IsParallelAlong cov γ V s → V u = P (V t₀) := by
  obtain ⟨fr, hfr0, hfrd, hfrp, hbu⟩ :=
    exists_parallel_orthonormalBasis_along cov hmet hs hconn hγ hγv ht₀ b
  obtain ⟨P, hP⟩ := exists_parallelTransportIsometry_global cov hmet hs hconn hγ hγv ht₀ hu
  refine ⟨fr, P, hfr0, hfrd, hfrp, hbu u hu, fun i ↦ ?_, hP⟩
  rw [← hfr0 i, ← hP (fr i) (hfrd i) (hfrp i)]

end CovariantDerivative
