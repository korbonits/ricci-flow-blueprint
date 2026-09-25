/-
**Hamilton's reaction preserves the pinching set, from every point of it.**

`Pinching.lean`'s `hamiltonIvey` and `IveyConvex.lean`'s `IsCurvatureODE.isIveyPinched` prove
invariance of `K` from the *normalised* initial data `ν ≥ −1`. That is the right statement for
the final theorem --- the hypothesis at `t = 0` --- but the maximum principle consumes something
stronger: the reaction must point into `K` (Nagumo's condition) at **every** boundary point,
and a boundary point need not satisfy `ν ≥ −1`.

**The Grönwall argument already gives it.** `hamiltonIvey` used `ν ≥ −1` for exactly one thing:
to put the initial triple in `K`, whence `Ψ(0) = R − f(−ν) ≥ 0` by `le_of_isIveyPinched`. Taking
membership in `K` as the hypothesis instead, every other step is unchanged
(`IsCurvatureODE.isIveyPinched_of_isIveyPinched`).

**Local existence** is Picard--Lindelöf for the polynomial field
`(λ,μ,ν) ↦ (λ²+μν, μ²+λν, ν²+λμ)` on `ℝ × ℝ × ℝ` (`exists_isCurvatureODE`), in the form
mathlib states for a `C¹` field, so no Lipschitz estimate is done here.
-/
import RicciFlowBlueprint.IveyConvex
import Mathlib.Analysis.ODE.ExistUnique

open Set
open scoped Topology

namespace RicciFlowBlueprint

namespace Pinching

variable {l m n : ℝ → ℝ} {T : ℝ}

-- BENCH: ivey-invariance-general
/-- **`K` is invariant under the curvature ODE from every ordered point of it**, not only from
the normalised data `ν ≥ −1`. -/
theorem IsCurvatureODE.isIveyPinched_of_isIveyPinched (h : IsCurvatureODE l m n T)
    (hT : 0 ≤ T) (h0lm : m 0 ≤ l 0) (h0mn : n 0 ≤ m 0)
    (h0 : IsIveyPinched (l 0) (m 0) (n 0)) :
    ∀ t ∈ Icc 0 T, IsIveyPinched (l t) (m t) (n t) := by
  intro t ht
  have hR : (-3 : ℝ) ≤ l t + m t + n t := h.le_scal hT h0.1 t ht
  refine ⟨hR, ?_⟩
  rcases lt_or_ge (n t) 0 with hnt | hpos
  · right
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have hneg := h.neg_of_neg hT h0lm h0mn ht hnt
    have hres := h.restrict ht.2
    have hlm := hres.le_preserved_lm ht0 h0lm
    have hmn := hres.le_preserved_mn ht0 h0mn
    have hstart : 0 ≤ iveyPsi (l 0) (m 0) (n 0) :=
      sub_nonneg.2 (le_of_isIveyPinched h0lm h0mn h0 (hneg 0 ⟨le_refl 0, ht0⟩))
    have hmid := hres.iveyPsi_nonneg ht0 hlm hmn hneg hstart t ⟨ht0, le_refl t⟩
    unfold iveyPsi at hmid
    linarith
  · left
    linarith [Real.exp_pos (2 : ℝ)]

/-- The curvature ODE's vector field on `ℝ × ℝ × ℝ`. -/
def curvatureField (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 ^ 2 + p.2.1 * p.2.2, p.2.1 ^ 2 + p.1 * p.2.2, p.2.2 ^ 2 + p.1 * p.2.1)

theorem contDiff_curvatureField : ContDiff ℝ 1 curvatureField := by
  unfold curvatureField
  fun_prop

-- BENCH: curvature-ode-exists
/-- **The curvature ODE has a local solution from every initial triple.** -/
theorem exists_isCurvatureODE (l₀ m₀ n₀ : ℝ) :
    ∃ T > (0 : ℝ), ∃ l m n : ℝ → ℝ, l 0 = l₀ ∧ m 0 = m₀ ∧ n 0 = n₀ ∧
      IsCurvatureODE l m n T := by
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (contDiff_curvatureField.contDiffAt (x := (l₀, m₀, n₀))) 0
  have hsub : Icc (0 : ℝ) (ε / 2) ⊆ Ioo (0 - ε) (0 + ε) := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : ∀ t ∈ Icc (0 : ℝ) (ε / 2), HasDerivAt α (curvatureField (α t)) t :=
    fun t ht ↦ hα t (hsub ht)
  have h1 : ∀ t ∈ Icc (0 : ℝ) (ε / 2),
      HasDerivAt (fun s ↦ (α s).1) (curvatureField (α t)).1 t := fun t ht ↦
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t (hc t ht)
  have h2 : ∀ t ∈ Icc (0 : ℝ) (ε / 2),
      HasDerivAt (fun s ↦ (α s).2.1) (curvatureField (α t)).2.1 t := fun t ht ↦
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
      ).hasFDerivAt.comp_hasDerivAt t (hc t ht)
  have h3 : ∀ t ∈ Icc (0 : ℝ) (ε / 2),
      HasDerivAt (fun s ↦ (α s).2.2) (curvatureField (α t)).2.2 t := fun t ht ↦
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
      ).hasFDerivAt.comp_hasDerivAt t (hc t ht)
  refine ⟨ε / 2, by positivity, fun s ↦ (α s).1, fun s ↦ (α s).2.1, fun s ↦ (α s).2.2,
    by simp [hα0], by simp [hα0], by simp [hα0], ⟨h1, h2, h3⟩⟩

end Pinching

end RicciFlowBlueprint
