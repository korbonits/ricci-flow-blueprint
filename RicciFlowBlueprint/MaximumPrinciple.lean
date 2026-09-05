/-
The scalar maximum principle on a compact space, abstractly.

On a closed manifold, a solution of `∂ₜu = Δu + ⟨X, ∇u⟩ + F(u)` is bounded below by
the solution of `φ' = F(φ)` with `φ(0) ≤ min u(0, ·)`. The only place the
Laplacian enters is the observation that at a spatial minimum `x₀` of `u(t, ·)`
one has `∇u = 0` and `Δu ≥ 0`, hence `∂ₜu(t, x₀) ≥ F(u(t, x₀))`. So we state the
principle with exactly that as the hypothesis (`hmin`), on an arbitrary compact
space: no Laplacian, no manifold. Once the Laplacian on a Riemannian manifold
exists in Mathlib, the classical statement is this theorem plus the
second-derivative test at a minimum.

The proof is the classical one. Perturb the comparison function to
`ψ_ε(t) = φ(t) - ε e^{(2K+1)t}`, which is a strict subsolution:
`ψ_ε' < F(ψ_ε)` by the Lipschitz bound on `F`. If `u ≥ ψ_ε` failed, the set of
times where it fails is closed (compactness of `M`), so there is a first time
`t₀ > 0` and a point `x₀` with `u(t₀, x₀) = ψ_ε(t₀)`; then `x₀` is a spatial
minimum, the left derivative of `u(·, x₀) - ψ_ε` at `t₀` is `≤ 0`, but the
differential inequality makes it `> 0`. Let `ε → 0`.

This is `thm:max-scalar` in the blueprint, with the manifold abstracted away;
`thm:max-tensor` (Hamilton's tensor maximum principle) has the same skeleton,
with the convex set in place of the half-line `[φ(t), ∞)`.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact

open Set Filter Topology

namespace RicciFlowBlueprint
namespace MaximumPrinciple

/-- If `g > 0` on `[0, t₀)`, `g t₀ = 0`, and `g` has left derivative `g'` at `t₀ > 0`, then
`g' ≤ 0`. -/
theorem deriv_nonpos_of_pos_left {g : ℝ → ℝ} {g' t₀ : ℝ}
    (hg : HasDerivWithinAt g g' (Iio t₀) t₀)
    (hpos : ∀ t ∈ Ico 0 t₀, 0 < g t) (h0 : g t₀ = 0) (ht₀ : 0 < t₀) : g' ≤ 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Iio t₀) (x := t₀) (by simp)] at hg
  refine le_of_tendsto hg ?_
  filter_upwards [mem_of_superset (Ioo_mem_nhdsLT ht₀) Ioo_subset_Ico_self] with t ht
  rw [slope_def_field, h0, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hpos t ht).le (by linarith [ht.2])

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]

/-- For `f` continuous on `ℝ × M` with `M` compact, the set of times `t ∈ [0, T]` at which
`f (t, ·) ≤ 0` somewhere is closed: it is the projection of a compact set. -/
theorem isClosed_touching {f : ℝ × M → ℝ} (hf : Continuous f) (T : ℝ) :
    IsClosed {t ∈ Icc (0:ℝ) T | ∃ x, f (t, x) ≤ 0} := by
  have hK : IsCompact {p : ℝ × M | p.1 ∈ Icc 0 T ∧ f p ≤ 0} := by
    refine ((isCompact_Icc (a := (0:ℝ)) (b := T)).prod isCompact_univ).of_isClosed_subset ?_ ?_
    · exact (isClosed_Icc.preimage continuous_fst).inter (isClosed_le hf continuous_const)
    · intro p hp
      exact ⟨hp.1, mem_univ _⟩
  have : {t ∈ Icc (0:ℝ) T | ∃ x, f (t, x) ≤ 0} =
      Prod.fst '' {p : ℝ × M | p.1 ∈ Icc 0 T ∧ f p ≤ 0} := by
    ext t
    constructor
    · rintro ⟨ht, x, hx⟩
      exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    · rintro ⟨⟨t', x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨ht, x, hx⟩
  rw [this]
  exact (hK.image continuous_fst).isClosed

-- BENCH: max-principle-scalar
/-- **The scalar maximum principle, abstractly.** Let `M` be compact, `u : ℝ → M → ℝ` jointly
continuous with time derivative `ut` on `[0, T]`, and `F` Lipschitz. Suppose that at every
spatial minimum `x₀` of `u t` one has `F (u t x₀) ≤ ut t x₀` (on a manifold this is
`∂ₜu = Δu + ⟨X, ∇u⟩ + F(u)` together with `Δu ≥ 0`, `∇u = 0` at a minimum). If `φ` solves
`φ' = F(φ)` on `[0, T]` and `φ 0 ≤ u 0` everywhere, then `φ t ≤ u t x` for all `t ∈ [0, T]`
and all `x`. -/
theorem le_of_deriv_ge_at_min {u ut : ℝ → M → ℝ} {F φ : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hF : LipschitzWith K F)
    (hmin : ∀ t ∈ Icc 0 T, ∀ x₀, (∀ x, u t x₀ ≤ u t x) → F (u t x₀) ≤ ut t x₀)
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (F (φ t)) t)
    (h0 : ∀ x, φ 0 ≤ u 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x, φ t ≤ u t x := by
  set c : ℝ := 2 * K + 1 with hc
  have hcpos : 0 < c := by positivity
  have hφc : ContinuousOn φ (Icc 0 T) := fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt
  -- the perturbed comparison function is a strict subsolution and stays strictly below `u`
  have key : ∀ ε > 0, ∀ t ∈ Icc 0 T, ∀ x, φ t - ε * Real.exp (c * t) < u t x := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    set ψ : ℝ → ℝ := fun t ↦ φ t - ε * Real.exp (c * t) with hψ
    -- a globally continuous copy of `ψ`, agreeing with it on `[0, T]`
    set ψ' : ℝ → ℝ := fun t ↦ φ (projIcc 0 T hT t) - ε * Real.exp (c * t) with hψ'
    have hψ'c : Continuous ψ' :=
      (hφc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun t ↦ (projIcc 0 T hT t).2).sub (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    have hψ'eq : ∀ t ∈ Icc 0 T, ψ' t = ψ t := fun t ht ↦ by
      simp [ψ', ψ, projIcc_of_mem hT ht]
    -- the touching set and the first touching time
    set S : Set ℝ := {t ∈ Icc (0:ℝ) T | ∃ x, u t x - ψ' t ≤ 0} with hS
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, x, hx⟩ := hcon
      exact ⟨t, ht, x, by rw [hψ'eq t ht]; simp only [ψ]; linarith⟩
    have hScl : IsClosed S :=
      isClosed_touching (f := fun p : ℝ × M ↦ u p.1 p.2 - ψ' p.1)
        (hu.sub (hψ'c.comp continuous_fst)) T
    have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
    set t₀ := sInf S with ht₀
    have ht₀S : t₀ ∈ S := hScl.csInf_mem hSne hSbdd
    obtain ⟨ht₀I, x₀, hx₀⟩ := ht₀S
    rw [hψ'eq t₀ ht₀I] at hx₀
    have hx₀' : u t₀ x₀ ≤ ψ t₀ := by linarith
    have hnot : ∀ t ∈ Ico 0 t₀, ∀ x, ψ t < u t x := by
      intro t ht x
      by_contra h
      push Not at h
      have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans ht₀I.2⟩, x, by
        rw [hψ'eq t ⟨ht.1, ht.2.le.trans ht₀I.2⟩]; linarith⟩
      exact absurd (csInf_le hSbdd htS) (not_le.2 ht.2)
    have ht₀pos : 0 < t₀ := by
      rcases ht₀I.1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hx₀'
        have := h0 x₀
        have : 0 < ε * Real.exp (c * 0) := by positivity
        simp only [ψ] at hx₀'
        linarith
    -- `x₀` is a spatial minimum at time `t₀`, and `u t₀ x₀ = ψ t₀`
    have hglob : ∀ x, ψ t₀ ≤ u t₀ x := by
      intro x
      have hcont : ContinuousWithinAt (fun t ↦ u t x - ψ' t) (Iio t₀) t₀ :=
        ((hu.comp (continuous_id.prodMk continuous_const)).sub hψ'c).continuousAt.continuousWithinAt
      have : ∀ᶠ t in 𝓝[<] t₀, 0 ≤ u t x - ψ' t := by
        filter_upwards [mem_of_superset (Ioo_mem_nhdsLT ht₀pos) Ioo_subset_Ico_self] with t ht
        rw [hψ'eq t ⟨ht.1, ht.2.le.trans ht₀I.2⟩]
        linarith [hnot t ht x]
      have hlim := ge_of_tendsto (hcont.tendsto) this
      rw [hψ'eq t₀ ht₀I] at hlim
      linarith
    have hmin₀ : ∀ x, u t₀ x₀ ≤ u t₀ x := fun x ↦ hx₀'.trans (hglob x)
    have heq : u t₀ x₀ = ψ t₀ := le_antisymm hx₀' (hglob x₀)
    -- the left derivative of `u (·, x₀) - ψ` at `t₀` is `≤ 0` ...
    have hψd : HasDerivAt ψ (F (φ t₀) - ε * (c * Real.exp (c * t₀))) t₀ := by
      have := (hφ t₀ ht₀I).sub (((hasDerivAt_id t₀).const_mul c).exp.const_mul ε)
      refine this.congr_deriv ?_
      simp only [id, mul_one]
      ring
    have hgd : HasDerivWithinAt (fun t ↦ u t x₀ - ψ t)
        (ut t₀ x₀ - (F (φ t₀) - ε * (c * Real.exp (c * t₀)))) (Iio t₀) t₀ :=
      ((hut t₀ ht₀I x₀).sub hψd).hasDerivWithinAt
    have hle : ut t₀ x₀ - (F (φ t₀) - ε * (c * Real.exp (c * t₀))) ≤ 0 :=
      deriv_nonpos_of_pos_left hgd (fun t ht ↦ by linarith [hnot t ht x₀]) (by simp [heq])
        ht₀pos
    -- ... but the differential inequality at the minimum makes it `> 0`
    have h1 : F (u t₀ x₀) ≤ ut t₀ x₀ := hmin t₀ ht₀I x₀ hmin₀
    rw [heq] at h1
    set E := ε * Real.exp (c * t₀) with hE
    have hEpos : 0 < E := by positivity
    have h2 : F (φ t₀) - K * E ≤ F (ψ t₀) := by
      have := hF.dist_le_mul (φ t₀) (ψ t₀)
      rw [Real.dist_eq, Real.dist_eq] at this
      have hd : |φ t₀ - ψ t₀| = E := by
        simp only [ψ, sub_sub_cancel]
        exact abs_of_pos hEpos
      rw [hd] at this
      linarith [(abs_le.mp this).2]
    have h3 : ε * (c * Real.exp (c * t₀)) = 2 * (K * E) + E := by
      simp only [hE, hc]
      ring
    rw [h3] at hle
    linarith [mul_nonneg (NNReal.coe_nonneg K) hEpos.le]
  -- let `ε → 0`
  intro t ht x
  refine le_of_forall_pos_lt_add fun η hη ↦ ?_
  have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
  have := key (η / Real.exp (c * t)) (by positivity) t ht x
  rw [div_mul_cancel₀ η hexp.ne'] at this
  linarith

/-- **The scalar maximum principle, upper bound.** The mirror image: if at every spatial
maximum `x₀` of `u t` one has `ut t x₀ ≤ F (u t x₀)`, `φ' = F(φ)`, and `u 0 ≤ φ 0`
everywhere, then `u t x ≤ φ t`. -/
theorem le_of_deriv_le_at_max {u ut : ℝ → M → ℝ} {F φ : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hF : LipschitzWith K F)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x₀, (∀ x, u t x ≤ u t x₀) → ut t x₀ ≤ F (u t x₀))
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (F (φ t)) t)
    (h0 : ∀ x, u 0 x ≤ φ 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ φ t := by
  have hF' : LipschitzWith K (fun y ↦ -F (-y)) := by
    intro a b
    have := hF (-a) (-b)
    simpa [edist_neg_neg] using this
  have := le_of_deriv_ge_at_min (u := fun t x ↦ -u t x) (ut := fun t x ↦ -ut t x)
    (F := fun y ↦ -F (-y)) (φ := fun t ↦ -φ t) hT (hu.neg)
    (fun t ht x ↦ (hut t ht x).neg) hF'
    (fun t ht x₀ hx₀ ↦ by
      have := hmax t ht x₀ fun x ↦ by linarith [hx₀ x]
      simp only [neg_neg]
      linarith)
    (fun t ht ↦ ((hφ t ht).neg).congr_deriv (by simp))
    (fun x ↦ by linarith [h0 x])
  intro t ht x
  linarith [this t ht x]

end MaximumPrinciple
end RicciFlowBlueprint
