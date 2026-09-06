/-
Hamilton's tensor maximum principle, abstractly.

Let `K` be a closed convex subset of a real inner product space `V`, and
`u : [0,T] × M → V` a solution of `∂ₜu = Δu + F(u)` on a closed manifold. If
`K` is preserved by the ODE `v' = F(v)` and `u(0, ·) ∈ K`, then `u(t, ·) ∈ K`
for all `t`. This is the workhorse of curvature-positivity arguments: Hamilton
1982 applies it (through the invariant sets of `Pinching.lean`) to the
curvature operator in dimension three.

As in `MaximumPrinciple.lean`, the Laplacian enters at one point only: at a
spatial maximum `x₀` of `x ↦ ⟪n, u(t,x)⟫` one has `Δ⟪n, u⟫ ≤ 0`, hence
`⟪n, ∂ₜu⟫ ≤ ⟪n, F(u)⟫` at `(t, x₀)`. We take exactly that as the hypothesis
(`hmax`), for every direction `n`. Invariance of `K` under the ODE enters
through its Nagumo form: `⟪n, F(p)⟫ ≤ 0` for every `p ∈ K` and every outward
normal `n` at `p` (`hK`). The lemma `subtangential_of_invariant` derives this
from invariance along a solution curve; it is the easy direction of Nagumo's
theorem.

The proof is the scalar one with the convex set in place of a half-line.
Perturb: the claim is `dist(u(t,x), K) < ε e^{(2L+1)t}`. If it fails, take
the first time `t₀` and a point `x₀` where it does; let `p` be the nearest
point of `K` to `u₀ = u(t₀,x₀)` and `n = u₀ − p`. Since `K` lies in the
half-space `⟪n, · − p⟫ ≤ 0`, the function `⟪n, u(t,·) − p⟫` is bounded by
`‖n‖ · dist(u(t,·), K)`, so `x₀` is a spatial maximum of it at time `t₀`, and
`t ↦ ⟪n, u(t,x₀) − p⟫ − ‖n‖ ε e^{(2L+1)t}` is negative before `t₀` and zero
at `t₀`, whence its left derivative is `≥ 0`. The two inequalities give
`(2L+1)‖n‖² ≤ ⟪n, F(u₀)⟫ ≤ ⟪n, F(p)⟫ + L‖n‖² ≤ L‖n‖²`, absurd. Let `ε → 0`.

No manifold, no Laplacian, no tensor: `V` is any real inner product space and
`M` any compact space.
-/
import RicciFlowBlueprint.MaximumPrinciple
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Filter Topology Metric
open scoped RealInnerProductSpace

namespace RicciFlowBlueprint
namespace MaximumPrinciple

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The easy direction of Nagumo's theorem.** If from every `p ∈ K` there is a solution
curve of `v' = F(v)` (a right derivative at `0` suffices) that stays in `K` for small positive
times, then `F(p)` points into `K`: `⟪n, F p⟫ ≤ 0` for every outward normal `n` at `p`. -/
theorem subtangential_of_invariant {K : Set V} {F : V → V}
    (hinv : ∀ p ∈ K, ∃ γ : ℝ → V, γ 0 = p ∧ HasDerivWithinAt γ (F p) (Ioi 0) 0 ∧
      ∀ᶠ s in 𝓝[>] (0:ℝ), γ s ∈ K)
    (p : V) (hp : p ∈ K) (n : V) (hn : ∀ q ∈ K, ⟪n, q - p⟫ ≤ 0) : ⟪n, F p⟫ ≤ 0 := by
  obtain ⟨γ, hγ0, hγd, hγK⟩ := hinv p hp
  have hd : HasDerivWithinAt (fun s ↦ ⟪n, γ s⟫) ⟪n, F p⟫ (Ioi 0) 0 := by
    have := (hasDerivWithinAt_const (0:ℝ) (Ioi 0) n).inner ℝ hγd
    simpa using this
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hd
  refine le_of_tendsto hd ?_
  filter_upwards [hγK, self_mem_nhdsWithin] with s hs hs0
  rw [slope_def_field, hγ0, ← inner_sub_right, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (hn _ hs) (le_of_lt hs0)

/-- The nearest point `p` of a closed convex `K` to `u₀`, with `n = u₀ - p`: `K` lies in the
half-space `⟪n, · - p⟫ ≤ 0`. -/
theorem exists_nearest_point [CompleteSpace V] {K : Set V} (hK : IsClosed K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (u₀ : V) :
    ∃ p ∈ K, ‖u₀ - p‖ = infDist u₀ K ∧ ∀ q ∈ K, ⟪u₀ - p, q - p⟫ ≤ 0 := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hK.isComplete hKc u₀
  refine ⟨p, hp, ?_, (norm_eq_iInf_iff_real_inner_le_zero hKc hp).mp hmin⟩
  rw [hmin, infDist_eq_iInf]
  simp only [dist_eq_norm]

/-- The supporting half-space bounds the distance from below: if `K ⊆ {⟪n, · - p⟫ ≤ 0}`
then `⟪n, v - p⟫ ≤ ‖n‖ * infDist v K` for every `v`. -/
theorem inner_sub_le_norm_mul_infDist {K : Set V} (hKne : K.Nonempty) {p n : V}
    (hn : ∀ q ∈ K, ⟪n, q - p⟫ ≤ 0) (v : V) : ⟪n, v - p⟫ ≤ ‖n‖ * infDist v K := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  rw [← div_le_iff₀' hpos, le_infDist hKne]
  intro q hq
  rw [div_le_iff₀' hpos, dist_eq_norm]
  have : ⟪n, v - p⟫ = ⟪n, v - q⟫ + ⟪n, q - p⟫ := by
    rw [← inner_add_right]; congr 1; abel
  rw [this]
  linarith [real_inner_le_norm n (v - q), hn q hq]

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]

-- BENCH: max-principle-tensor
/-- **Hamilton's tensor maximum principle, abstractly.** Let `M` be compact, `V` a complete
real inner product space, `K ⊆ V` closed, convex and nonempty, `u : ℝ → M → V` jointly
continuous with time derivative `ut` on `[0, T]`, and `F` Lipschitz. Suppose

* (`hmax`) at every spatial maximum `x₀` of `x ↦ ⟪n, u t x⟫` one has
  `⟪n, ut t x₀⟫ ≤ ⟪n, F (u t x₀)⟫` — on a manifold this is `∂ₜu = Δu + F(u)` together with
  `Δ⟪n, u⟫ ≤ 0` at a maximum;
* (`hK`) `K` is preserved by the ODE `v' = F(v)`, in Nagumo's form: `⟪n, F p⟫ ≤ 0` for every
  `p ∈ K` and every outward normal `n` at `p` (`subtangential_of_invariant` derives this
  from invariance along solution curves).

If `u 0 x ∈ K` for all `x`, then `u t x ∈ K` for all `t ∈ [0, T]` and all `x`. -/
theorem mem_of_deriv_le_at_max [CompleteSpace V] {u ut : ℝ → M → V} {F : V → V}
    {K : Set V} {L : NNReal} {T : ℝ}
    (hKcl : IsClosed K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    (hu : Continuous fun p : ℝ × M ↦ u p.1 p.2)
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hF : LipschitzWith L F)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x₀, ∀ n : V, (∀ x, ⟪n, u t x⟫ ≤ ⟪n, u t x₀⟫) →
      ⟪n, ut t x₀⟫ ≤ ⟪n, F (u t x₀)⟫)
    (hK : ∀ p ∈ K, ∀ n : V, (∀ q ∈ K, ⟪n, q - p⟫ ≤ 0) → ⟪n, F p⟫ ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K := by
  set c : ℝ := 2 * L + 1 with hc
  have hcpos : 0 < c := by positivity
  have hdc : Continuous fun p : ℝ × M ↦ infDist (u p.1 p.2) K :=
    (continuous_infDist_pt K).comp hu
  -- the distance to `K` stays strictly below `ε e^{ct}`
  have key : ∀ ε > 0, ∀ t ∈ Icc 0 T, ∀ x, infDist (u t x) K < ε * Real.exp (c * t) := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    -- the touching set and the first touching time
    set S : Set ℝ := {t ∈ Icc (0:ℝ) T | ∃ x, ε * Real.exp (c * t) - infDist (u t x) K ≤ 0}
      with hS
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, x, hx⟩ := hcon
      exact ⟨t, ht, x, by linarith⟩
    have hScl : IsClosed S :=
      isClosed_touching (f := fun p : ℝ × M ↦ ε * Real.exp (c * p.1) - infDist (u p.1 p.2) K)
        ((continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_fst))).sub hdc) T
    have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
    set t₀ := sInf S with ht₀
    have ht₀S : t₀ ∈ S := hScl.csInf_mem hSne hSbdd
    obtain ⟨ht₀I, x₀, hx₀⟩ := ht₀S
    set E := ε * Real.exp (c * t₀) with hE
    have hEpos : 0 < E := by positivity
    have hx₀' : E ≤ infDist (u t₀ x₀) K := by linarith
    have hnot : ∀ t ∈ Ico 0 t₀, ∀ x, infDist (u t x) K < ε * Real.exp (c * t) := by
      intro t ht x
      by_contra h
      push Not at h
      have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans ht₀I.2⟩, x, by linarith⟩
      exact absurd (csInf_le hSbdd htS) (not_le.2 ht.2)
    have ht₀pos : 0 < t₀ := by
      rcases ht₀I.1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hx₀'
        rw [infDist_zero_of_mem (h0 x₀)] at hx₀'
        have : 0 < ε * Real.exp (c * 0) := by positivity
        rw [hE, ← h] at hx₀'
        linarith
    -- at time `t₀` the distance is `≤ E` everywhere, `= E` at `x₀`
    have hglob : ∀ x, infDist (u t₀ x) K ≤ E := by
      intro x
      have hcont : ContinuousWithinAt
          (fun t ↦ ε * Real.exp (c * t) - infDist (u t x) K) (Iio t₀) t₀ :=
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
          continuous_id))).sub (hdc.comp (continuous_id.prodMk continuous_const)))
          |>.continuousAt.continuousWithinAt
      have : ∀ᶠ t in 𝓝[<] t₀, 0 ≤ ε * Real.exp (c * t) - infDist (u t x) K := by
        filter_upwards [mem_of_superset (Ioo_mem_nhdsLT ht₀pos) Ioo_subset_Ico_self] with t ht
        linarith [hnot t ht x]
      have hlim := ge_of_tendsto hcont.tendsto this
      linarith
    have heq : infDist (u t₀ x₀) K = E := le_antisymm (hglob x₀) hx₀'
    -- the nearest point of `K` and the outward normal
    obtain ⟨p, hp, hnorm, hn⟩ := exists_nearest_point hKcl hKc hKne (u t₀ x₀)
    set n := u t₀ x₀ - p with hn_def
    have hnE : ‖n‖ = E := by rw [hn_def, hnorm, heq]
    have hbound : ∀ t x, ⟪n, u t x⟫ ≤ ⟪n, p⟫ + E * infDist (u t x) K := by
      intro t x
      have := inner_sub_le_norm_mul_infDist hKne hn (u t x)
      rw [inner_sub_right, hnE] at this
      linarith
    have hat : ⟪n, u t₀ x₀⟫ = ⟪n, p⟫ + E * E := by
      have : ⟪n, u t₀ x₀ - p⟫ = E * E := by
        rw [hn_def, real_inner_self_eq_norm_sq, ← hn_def, hnE]; ring
      rw [inner_sub_right] at this
      linarith
    -- `x₀` is a spatial maximum of `⟪n, u t₀ ·⟫`
    have hmax₀ : ∀ x, ⟪n, u t₀ x⟫ ≤ ⟪n, u t₀ x₀⟫ := by
      intro x
      rw [hat]
      have := hbound t₀ x
      have := hglob x
      nlinarith
    have h1 : ⟪n, ut t₀ x₀⟫ ≤ ⟪n, F (u t₀ x₀)⟫ := hmax t₀ ht₀I x₀ n hmax₀
    -- the left derivative of `t ↦ ⟪n, p⟫ + E ε e^{ct} - ⟪n, u t x₀⟫` at `t₀` is `≤ 0`
    have hgd : HasDerivWithinAt (fun t ↦ ⟪n, p⟫ + E * (ε * Real.exp (c * t)) - ⟪n, u t x₀⟫)
        (E * (ε * (c * Real.exp (c * t₀))) - ⟪n, ut t₀ x₀⟫) (Iio t₀) t₀ := by
      have hexp : HasDerivAt (fun t ↦ ⟪n, p⟫ + E * (ε * Real.exp (c * t)))
          (E * (ε * (c * Real.exp (c * t₀)))) t₀ := by
        have := ((((hasDerivAt_id t₀).const_mul c).exp.const_mul ε).const_mul E).const_add
          ⟪n, p⟫
        refine this.congr_deriv ?_
        simp only [id, mul_one]
        ring
      have hin : HasDerivAt (fun t ↦ ⟪n, u t x₀⟫) ⟪n, ut t₀ x₀⟫ t₀ := by
        have := (hasDerivAt_const t₀ n).inner ℝ (hut t₀ ht₀I x₀)
        simpa using this
      exact (hexp.sub hin).hasDerivWithinAt
    have hle : E * (ε * (c * Real.exp (c * t₀))) - ⟪n, ut t₀ x₀⟫ ≤ 0 := by
      refine deriv_nonpos_of_pos_left hgd ?_ ?_ ht₀pos
      · intro t ht
        have := hbound t x₀
        have := hnot t ht x₀
        nlinarith
      · rw [hat]; ring
    -- Lipschitz and subtangentiality
    have h2 : ⟪n, F (u t₀ x₀)⟫ ≤ ⟪n, F p⟫ + E * (L * E) := by
      have hd := hF.dist_le_mul (u t₀ x₀) p
      rw [dist_eq_norm, dist_eq_norm, ← hn_def, hnE] at hd
      have := real_inner_le_norm n (F (u t₀ x₀) - F p)
      rw [inner_sub_right, hnE] at this
      nlinarith [hEpos]
    have h3 : ⟪n, F p⟫ ≤ 0 := hK p hp n hn
    have h4 : E * (ε * (c * Real.exp (c * t₀))) = c * (E * E) := by rw [hE]; ring
    rw [h4] at hle
    have h5 : c * (E * E) ≤ L * (E * E) := by nlinarith
    have h6 : 0 < E * E := by positivity
    have := le_of_mul_le_mul_right h5 h6
    rw [hc] at this
    linarith [NNReal.coe_nonneg L]
  -- let `ε → 0`
  intro t ht x
  rw [← hKcl.closure_eq, mem_closure_iff_infDist_zero hKne]
  refine le_antisymm ?_ infDist_nonneg
  refine le_of_forall_pos_lt_add fun η hη ↦ ?_
  have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
  have := key (η / Real.exp (c * t)) (by positivity) t ht x
  rw [div_mul_cancel₀ η hexp.ne'] at this
  linarith

end MaximumPrinciple
end RicciFlowBlueprint
