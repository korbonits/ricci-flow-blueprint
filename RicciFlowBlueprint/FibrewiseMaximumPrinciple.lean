/-
**Hamilton's tensor maximum principle for a FAMILY of fibres.**

`TensorMaximumPrinciple.lean` works in one fixed inner product space `V`, so its touching-point
hypothesis can be stated as "`x₀` is a spatial maximum of `⟪n, u t x⟫`" --- which only parses
because `n` is the same vector at every point. On a bundle the tested direction lives in one
fibre and the comparison between points has to be made through the *distance* to a family of
sets instead.

**The change is smaller than it looks, and it makes the proof shorter.** The first-touching-
time argument never compares `u t x` with `u t x₀` directly; it compares
`dist(u t x, K x)` with `dist(u t x₀, K x₀)`, which is a comparison of *real numbers*. Where
the fixed-space version has to turn the distance maximum into a pairing maximum (the lemmas
`hbound`, `hat`, `hmax₀` there), here the pairing maximum is the *hypothesis*, in the form
`BundleDistanceMax.lean` supplies it, and those steps disappear. Everything else --- the
`ε e^{ct}` perturbation, the closed touching set, the first touching time, the left
derivative, Lipschitz comparison and subtangentiality --- happens in the single fibre over
`x₀` and is the fixed-space argument verbatim.

**There is no geometry in this file.** `M` is a compact topological space and the fibres are
an arbitrary family of complete real inner product spaces: no manifold, no bundle, no
connection. What connects it to geometry is the hypothesis `hmax`, which on a Riemannian
bundle is `∂ₜu = Δu + F(u)` together with `⟪n, Δu(x₀)⟫ ≤ 0` at a maximum of the distance ---
and that is exactly `BundleDistanceMax.lean`'s conclusion.
-/
import RicciFlowBlueprint.TensorMaximumPrinciple

open Filter Set Metric
open scoped Topology RealInnerProductSpace NNReal

namespace RicciFlowBlueprint

namespace MaximumPrinciple

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, CompleteSpace (V x)]

/-- **The fibrewise principle with the Lipschitz comparison asked only where it is used**: between
`u t x₀` and its nearest point in `K x₀`, at a point of maximal distance. Both the global and the
local-on-balls forms below are one line from this. -/
theorem mem_of_infDist_max_of_le {u ut : ℝ → Π x : M, V x} {F : Π x : M, V x → V x}
    {K : Π x : M, Set (V x)} {L : ℝ≥0} {T : ℝ}
    (hKcl : ∀ x, IsClosed (K x)) (hKc : ∀ x, Convex ℝ (K x)) (hKne : ∀ x, (K x).Nonempty)
    (hdc : Continuous fun p : ℝ × M ↦ infDist (u p.1 p.2) (K p.2))
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hF : ∀ t ∈ Icc 0 T, ∀ x₀ : M, ∀ p ∈ K x₀,
      ‖u t x₀ - p‖ = infDist (u t x₀) (K x₀) →
      ‖F x₀ (u t x₀) - F x₀ p‖ ≤ L * ‖u t x₀ - p‖)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x₀ : M, ∀ p ∈ K x₀,
      ‖u t x₀ - p‖ = infDist (u t x₀) (K x₀) →
      (∀ q ∈ K x₀, (⟪u t x₀ - p, q - p⟫ : ℝ) ≤ 0) →
      (∀ x, infDist (u t x) (K x) ≤ infDist (u t x₀) (K x₀)) →
      (⟪u t x₀ - p, ut t x₀⟫ : ℝ) ≤ ⟪u t x₀ - p, F x₀ (u t x₀)⟫)
    (hKinv : ∀ x : M, ∀ p ∈ K x, ∀ n : V x,
      (∀ q ∈ K x, (⟪n, q - p⟫ : ℝ) ≤ 0) → (⟪n, F x p⟫ : ℝ) ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K x) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K x := by
  set c : ℝ := 2 * L + 1 with hc
  have hcpos : 0 < c := by positivity
  have key : ∀ ε > 0, ∀ t ∈ Icc 0 T, ∀ x, infDist (u t x) (K x) < ε * Real.exp (c * t) := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    set S : Set ℝ :=
      {t ∈ Icc (0:ℝ) T | ∃ x, ε * Real.exp (c * t) - infDist (u t x) (K x) ≤ 0} with hS
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, x, hx⟩ := hcon
      exact ⟨t, ht, x, by linarith⟩
    have hScl : IsClosed S :=
      isClosed_touching
        (f := fun p : ℝ × M ↦ ε * Real.exp (c * p.1) - infDist (u p.1 p.2) (K p.2))
        ((continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_fst))).sub hdc) T
    have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
    set t₀ := sInf S with ht₀
    have ht₀S : t₀ ∈ S := hScl.csInf_mem hSne hSbdd
    obtain ⟨ht₀I, x₀, hx₀⟩ := ht₀S
    set E := ε * Real.exp (c * t₀) with hE
    have hEpos : 0 < E := by positivity
    have hx₀' : E ≤ infDist (u t₀ x₀) (K x₀) := by linarith
    have hnot : ∀ t ∈ Ico 0 t₀, ∀ x, infDist (u t x) (K x) < ε * Real.exp (c * t) := by
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
        rw [hE, ← h] at hx₀'
        have : 0 < ε * Real.exp (c * 0) := by positivity
        linarith
    have hglob : ∀ x, infDist (u t₀ x) (K x) ≤ E := by
      intro x
      have hcont : ContinuousWithinAt
          (fun t ↦ ε * Real.exp (c * t) - infDist (u t x) (K x)) (Iio t₀) t₀ :=
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
          continuous_id))).sub (hdc.comp (continuous_id.prodMk continuous_const)))
          |>.continuousAt.continuousWithinAt
      have hev : ∀ᶠ t in 𝓝[<] t₀, 0 ≤ ε * Real.exp (c * t) - infDist (u t x) (K x) := by
        filter_upwards [mem_of_superset (Ioo_mem_nhdsLT ht₀pos) Ioo_subset_Ico_self] with t ht
        linarith [hnot t ht x]
      have hlim := ge_of_tendsto hcont.tendsto hev
      linarith
    have heq : infDist (u t₀ x₀) (K x₀) = E := le_antisymm (hglob x₀) hx₀'
    obtain ⟨p, hp, hnorm, hn⟩ :=
      exists_nearest_point (V := V x₀) (hKcl x₀) (hKc x₀) (hKne x₀) (u t₀ x₀)
    set n := u t₀ x₀ - p with hn_def
    have hnE : ‖n‖ = E := by rw [hn_def, hnorm, heq]
    have hbound : ∀ t, (⟪n, u t x₀⟫ : ℝ) ≤ ⟪n, p⟫ + E * infDist (u t x₀) (K x₀) := by
      intro t
      have h := inner_sub_le_norm_mul_infDist (V := V x₀) (hKne x₀) hn (u t x₀)
      rw [inner_sub_right, hnE] at h
      linarith
    have hat : (⟪n, u t₀ x₀⟫ : ℝ) = ⟪n, p⟫ + E * E := by
      have h : (⟪n, u t₀ x₀ - p⟫ : ℝ) = E * E := by
        rw [hn_def, real_inner_self_eq_norm_sq, ← hn_def, hnE]; ring
      rw [inner_sub_right] at h
      linarith
    have h1 : (⟪n, ut t₀ x₀⟫ : ℝ) ≤ ⟪n, F x₀ (u t₀ x₀)⟫ :=
      hmax t₀ ht₀I x₀ p hp hnorm hn (fun x ↦ (hglob x).trans_eq heq.symm)
    have hgd : HasDerivWithinAt (fun t ↦ ⟪n, p⟫ + E * (ε * Real.exp (c * t)) - ⟪n, u t x₀⟫)
        (E * (ε * (c * Real.exp (c * t₀))) - ⟪n, ut t₀ x₀⟫) (Iio t₀) t₀ := by
      have hexp : HasDerivAt (fun t ↦ ⟪n, p⟫ + E * (ε * Real.exp (c * t)))
          (E * (ε * (c * Real.exp (c * t₀)))) t₀ := by
        have h := ((((hasDerivAt_id t₀).const_mul c).exp.const_mul ε).const_mul E).const_add
          (⟪n, p⟫ : ℝ)
        refine h.congr_deriv ?_
        simp only [id, mul_one]
        ring
      have hin : HasDerivAt (fun t ↦ (⟪n, u t x₀⟫ : ℝ)) ⟪n, ut t₀ x₀⟫ t₀ := by
        have h := (hasDerivAt_const t₀ n).inner ℝ (hut t₀ ht₀I x₀)
        simpa using h
      exact (hexp.sub hin).hasDerivWithinAt
    have hle : E * (ε * (c * Real.exp (c * t₀))) - ⟪n, ut t₀ x₀⟫ ≤ 0 := by
      refine deriv_nonpos_of_pos_left hgd ?_ ?_ ht₀pos
      · intro t ht
        have hb := hbound t
        have hs := hnot t ht x₀
        nlinarith
      · rw [hat]; ring
    have h2 : (⟪n, F x₀ (u t₀ x₀)⟫ : ℝ) ≤ ⟪n, F x₀ p⟫ + E * (L * E) := by
      have hd := hF t₀ ht₀I x₀ p hp hnorm
      rw [← hn_def, hnE] at hd
      have h := real_inner_le_norm n (F x₀ (u t₀ x₀) - F x₀ p)
      rw [inner_sub_right, hnE] at h
      nlinarith [hEpos]
    have h3 : (⟪n, F x₀ p⟫ : ℝ) ≤ 0 := hKinv x₀ p hp n hn
    have h4 : E * (ε * (c * Real.exp (c * t₀))) = c * (E * E) := by rw [hE]; ring
    rw [h4] at hle
    have h5 : c * (E * E) ≤ L * (E * E) := by nlinarith
    have h6 : 0 < E * E := by positivity
    have h7 := le_of_mul_le_mul_right h5 h6
    rw [hc] at h7
    linarith [NNReal.coe_nonneg L]
  intro t ht x
  rw [← (hKcl x).closure_eq, mem_closure_iff_infDist_zero (hKne x)]
  refine le_antisymm ?_ infDist_nonneg
  refine le_of_forall_pos_lt_add fun η hη ↦ ?_
  have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
  have h := key (η / Real.exp (c * t)) (by positivity) t ht x
  rw [div_mul_cancel₀ η hexp.ne'] at h
  linarith


-- BENCH: max-principle-fibrewise
/-- **The tensor maximum principle on a family of fibres.**

`K x ⊆ V x` closed, convex and nonempty in each fibre, `u : ℝ → Π x, V x` with a time
derivative `ut` on `[0,T]`, the distance to the family jointly continuous, and `F x` Lipschitz
with a constant uniform in `x`. Suppose

* (`hmax`) wherever `x ↦ dist(u t x, K x)` is maximal, the outward normal `n = u t x₀ − p` at
  the nearest point --- which comes with the supporting half-space property, so a consumer
  need not re-derive it --- satisfies `⟪n, ∂ₜu⟫ ≤ ⟪n, F (u)⟫`;
* (`hKinv`) each `K x` is preserved by the ODE `v' = F x v`, in Nagumo's form.

If `u 0 x ∈ K x` for all `x`, then `u t x ∈ K x` for all `t ∈ [0,T]`.

**Joint continuity of the distance is a hypothesis and has to be**: `u` is a section of a
family, so there is no continuity statement about `u` itself to derive it from --- that is
precisely the cross-fibre content, and on a bundle it comes from a local trivialisation. -/
theorem mem_of_infDist_max {u ut : ℝ → Π x : M, V x} {F : Π x : M, V x → V x}
    {K : Π x : M, Set (V x)} {L : ℝ≥0} {T : ℝ}
    (hKcl : ∀ x, IsClosed (K x)) (hKc : ∀ x, Convex ℝ (K x)) (hKne : ∀ x, (K x).Nonempty)
    (hdc : Continuous fun p : ℝ × M ↦ infDist (u p.1 p.2) (K p.2))
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hF : ∀ x, LipschitzWith L (F x))
    (hmax : ∀ t ∈ Icc 0 T, ∀ x₀ : M, ∀ p ∈ K x₀,
      ‖u t x₀ - p‖ = infDist (u t x₀) (K x₀) →
      (∀ q ∈ K x₀, (⟪u t x₀ - p, q - p⟫ : ℝ) ≤ 0) →
      (∀ x, infDist (u t x) (K x) ≤ infDist (u t x₀) (K x₀)) →
      (⟪u t x₀ - p, ut t x₀⟫ : ℝ) ≤ ⟪u t x₀ - p, F x₀ (u t x₀)⟫)
    (hKinv : ∀ x : M, ∀ p ∈ K x, ∀ n : V x,
      (∀ q ∈ K x, (⟪n, q - p⟫ : ℝ) ≤ 0) → (⟪n, F x p⟫ : ℝ) ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K x) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K x :=
  mem_of_infDist_max_of_le hKcl hKc hKne hdc hut
    (fun _ _ x₀ p _ _ ↦ by
      simpa only [dist_eq_norm] using (hF x₀).dist_le_mul _ p) hmax hKinv h0

-- BENCH: max-principle-fibrewise-local
/-- **The fibrewise principle with a LOCALLY Lipschitz reaction.** When `0 ∈ K x` and `u` stays
in the ball of radius `B`, a nearest point `p` satisfies `‖p‖ ≤ 2B`: `‖u − p‖ = dist(u,K) ≤ ‖u‖`.
So a Lipschitz bound for `F x` on the ball of radius `2B` is all the comparison ever uses, and a
polynomial reaction --- Hamilton's --- needs **no truncation**. -/
theorem mem_of_infDist_max_local {u ut : ℝ → Π x : M, V x} {F : Π x : M, V x → V x}
    {K : Π x : M, Set (V x)} {L : ℝ≥0} {T B : ℝ}
    (hKcl : ∀ x, IsClosed (K x)) (hKc : ∀ x, Convex ℝ (K x)) (hK0 : ∀ x, (0 : V x) ∈ K x)
    (hdc : Continuous fun p : ℝ × M ↦ infDist (u p.1 p.2) (K p.2))
    (hut : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s ↦ u s x) (ut t x) t)
    (hu : ∀ t ∈ Icc 0 T, ∀ x, ‖u t x‖ ≤ B)
    (hF : ∀ x, LipschitzOnWith L (F x) (closedBall 0 (2 * B)))
    (hmax : ∀ t ∈ Icc 0 T, ∀ x₀ : M, ∀ p ∈ K x₀,
      ‖u t x₀ - p‖ = infDist (u t x₀) (K x₀) →
      (∀ q ∈ K x₀, (⟪u t x₀ - p, q - p⟫ : ℝ) ≤ 0) →
      (∀ x, infDist (u t x) (K x) ≤ infDist (u t x₀) (K x₀)) →
      (⟪u t x₀ - p, ut t x₀⟫ : ℝ) ≤ ⟪u t x₀ - p, F x₀ (u t x₀)⟫)
    (hKinv : ∀ x : M, ∀ p ∈ K x, ∀ n : V x,
      (∀ q ∈ K x, (⟪n, q - p⟫ : ℝ) ≤ 0) → (⟪n, F x p⟫ : ℝ) ≤ 0)
    (h0 : ∀ x, u 0 x ∈ K x) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ∈ K x := by
  refine mem_of_infDist_max_of_le (L := L) hKcl hKc (fun x ↦ ⟨0, hK0 x⟩) hdc hut
    (fun t ht x₀ p _ hnorm ↦ ?_) hmax hKinv h0
  have hub := hu t ht x₀
  have hd0 : ‖u t x₀ - p‖ ≤ ‖u t x₀‖ := by
    rw [hnorm]
    simpa only [dist_zero_right] using infDist_le_dist_of_mem (x := u t x₀) (hK0 x₀)
  have hp : ‖p‖ ≤ 2 * B := by
    have : ‖p‖ ≤ ‖u t x₀‖ + ‖u t x₀ - p‖ := by
      calc ‖p‖ = ‖u t x₀ - (u t x₀ - p)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u t x₀‖ + ‖u t x₀ - p‖ := norm_sub_le _ _
    linarith
  have hu2 : ‖u t x₀‖ ≤ 2 * B := by linarith [norm_nonneg (u t x₀)]
  have h := (hF x₀).dist_le_mul (u t x₀) (by simpa using hu2) p (by simpa using hp)
  simpa only [dist_eq_norm] using h

end MaximumPrinciple

end RicciFlowBlueprint
