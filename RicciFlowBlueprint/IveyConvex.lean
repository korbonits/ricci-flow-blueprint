/-
**Convexity of Hamilton's pinching set** — the input `thm:max-tensor` needs in order to
carry the Hamilton–Ivey estimate from the ODE (`Pinching.lean`) to the PDE.

`Pinching.lean` states the set without an inverse function:

  `IsIveyPinched λ μ ν ↔ -3 ≤ λ+μ+ν ∧ (-ν ≤ e² ∨ f(-ν) ≤ λ+μ+ν)`,  `f(x) = x(log x - 3)`.

That disjunction is not obviously convex, and the literature restores convexity by writing
the second condition as `-ν ≤ f⁻¹(λ+μ+ν)` and invoking concavity of `f⁻¹`. **No inverse
function is needed.** The disjunction collapses to a single inequality against

  `G(ν) = f(max(-ν, e²))`,

because `f` is increasing on `[e², ∞)`: when `-ν ≤ e²` we have `G(ν) = f(e²) = -e² ≤ -3`,
which the first condition already gives, and otherwise `G(ν) = f(-ν)`. And `G` is convex on
all of `ℝ` — it is `f`, convex and increasing on `[e², ∞)`, composed with the convex
`ν ↦ max(-ν, e²)`, which lands there. So the pinching set is cut out by three half-spaces
and one convex inequality.

Building `f⁻¹` and proving it concave, which `CLAUDE.md` recorded as the remaining obstacle
(a) for Hamilton–Ivey, is therefore unnecessary.
-/
import RicciFlowBlueprint.Pinching
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set

namespace RicciFlowBlueprint
namespace Pinching

section IveyF

/-- `3 ≤ e²`, which is what makes the first condition of `K` dominate the second in the
middle range. -/
theorem three_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
  have := Real.add_one_le_exp (2 : ℝ)
  linarith

@[simp] theorem iveyF_exp_two : iveyF (Real.exp 2) = -Real.exp 2 := by
  rw [iveyF, Real.log_exp]
  ring

/-- `f` is monotone on `[e², ∞)`, where `f' = log x - 2 ≥ 0`. -/
theorem monotoneOn_iveyF : MonotoneOn iveyF (Ici (Real.exp 2)) := by
  have hpos : ∀ x ∈ Ici (Real.exp 2), (0:ℝ) < x := fun x hx ↦
    lt_of_lt_of_le (Real.exp_pos 2) hx
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x ↦ Real.log x - 2)
    (convex_Ici _)
    (fun x hx ↦ (hasDerivAt_iveyF (hpos x hx)).continuousAt.continuousWithinAt)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Ici] at hx
    exact (hasDerivAt_iveyF (lt_trans (Real.exp_pos 2) hx)).hasDerivWithinAt
  · rw [interior_Ici] at hx
    have : (2:ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 2]
      exact Real.log_le_log (Real.exp_pos 2) hx.le
    linarith

/-- `f` is convex on `[e², ∞)`: its derivative `log x - 2` is monotone. -/
theorem convexOn_iveyF : ConvexOn ℝ (Ici (Real.exp 2)) iveyF := by
  have hpos : ∀ x ∈ Ici (Real.exp 2), (0:ℝ) < x := fun x hx ↦
    lt_of_lt_of_le (Real.exp_pos 2) hx
  have hderiv : ∀ x ∈ interior (Ici (Real.exp 2)), deriv iveyF x = Real.log x - 2 := by
    intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivAt_iveyF (lt_trans (Real.exp_pos 2) hx)).deriv
  refine MonotoneOn.convexOn_of_deriv (convex_Ici _)
    (fun x hx ↦ (hasDerivAt_iveyF (hpos x hx)).continuousAt.continuousWithinAt)
    (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)
  · rw [interior_Ici] at hx
    exact ((hasDerivAt_iveyF (lt_trans (Real.exp_pos 2) hx)).differentiableAt).differentiableWithinAt
  · rw [hderiv x hx, hderiv y hy]
    rw [interior_Ici] at hx
    have hx0 : (0:ℝ) < x := lt_trans (Real.exp_pos 2) hx
    have : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    linarith

end IveyF

section IveyG

/-- `G(ν) = f(max(-ν, e²))`, the single convex function cutting out the second condition of
Hamilton's set. -/
noncomputable def iveyG (n : ℝ) : ℝ := iveyF (max (-n) (Real.exp 2))

theorem iveyG_of_le {n : ℝ} (h : -n ≤ Real.exp 2) : iveyG n = -Real.exp 2 := by
  rw [iveyG, max_eq_right h, iveyF_exp_two]

theorem iveyG_of_ge {n : ℝ} (h : Real.exp 2 ≤ -n) : iveyG n = iveyF (-n) := by
  rw [iveyG, max_eq_left h]

/-- `ν ↦ max(-ν, e²)` maps `ℝ` onto `[e², ∞)`. -/
theorem image_max_neg_exp_two :
    (fun n : ℝ ↦ max (-n) (Real.exp 2)) '' univ = Ici (Real.exp 2) := by
  ext y
  constructor
  · rintro ⟨n, -, rfl⟩
    show Real.exp 2 ≤ max (-n) (Real.exp 2)
    exact le_max_right _ _
  · intro hy
    refine ⟨-y, mem_univ _, ?_⟩
    show max (- -y) (Real.exp 2) = y
    rw [neg_neg, max_eq_left hy]

/-- `ν ↦ max(-ν, e²)` is convex. -/
theorem convexOn_max_neg_exp_two :
    ConvexOn ℝ (univ : Set ℝ) (fun n : ℝ ↦ max (-n) (Real.exp 2)) := by
  have hneg : ConvexOn ℝ (univ : Set ℝ) (fun n : ℝ ↦ -n) :=
    ⟨convex_univ, fun x _ y _ a b _ _ _ ↦ le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  have hconst : ConvexOn ℝ (univ : Set ℝ) (fun _ : ℝ ↦ Real.exp 2) :=
    convexOn_const _ convex_univ
  exact hneg.sup hconst

-- BENCH: ivey-g-convex
/-- **`G` is convex on all of `ℝ`.** -/
theorem convexOn_iveyG : ConvexOn ℝ (univ : Set ℝ) iveyG := by
  have h := ConvexOn.comp (f := fun n : ℝ ↦ max (-n) (Real.exp 2)) (g := iveyF) (s := univ)
    (by rw [image_max_neg_exp_two]; exact convexOn_iveyF)
    convexOn_max_neg_exp_two
    (by rw [image_max_neg_exp_two]; exact monotoneOn_iveyF)
  exact h

theorem continuous_iveyG : Continuous iveyG := by
  have hmax : Continuous (fun n : ℝ ↦ max (-n) (Real.exp 2)) :=
    continuous_neg.max continuous_const
  have hpos : ∀ n : ℝ, (0:ℝ) < max (-n) (Real.exp 2) :=
    fun n ↦ lt_of_lt_of_le (Real.exp_pos 2) (le_max_right _ _)
  refine Continuous.congr (f := fun n ↦ (max (-n) (Real.exp 2))
    * (Real.log (max (-n) (Real.exp 2)) - 3)) ?_ (fun n ↦ rfl)
  exact hmax.mul ((Real.continuousOn_log.comp_continuous hmax
    (fun n ↦ (hpos n).ne')).sub continuous_const)

-- BENCH: ivey-pinched-iff-g
/-- **The disjunction in `IsIveyPinched` is a single inequality against `G`.** -/
theorem isIveyPinched_iff_iveyG (l m n : ℝ) :
    IsIveyPinched l m n ↔ (-3 ≤ l + m + n ∧ iveyG n ≤ l + m + n) := by
  have he : (3:ℝ) ≤ Real.exp 2 := three_le_exp_two
  constructor
  · rintro ⟨hR, hcase⟩
    refine ⟨hR, ?_⟩
    rcases le_or_gt (-n) (Real.exp 2) with hsmall | hbig
    · rw [iveyG_of_le hsmall]; linarith
    · rw [iveyG_of_ge hbig.le]
      rcases hcase with hc | hc
      · linarith
      · exact hc
  · rintro ⟨hR, hG⟩
    refine ⟨hR, ?_⟩
    rcases le_or_gt (-n) (Real.exp 2) with hsmall | hbig
    · exact Or.inl hsmall
    · exact Or.inr (by rwa [iveyG_of_ge hbig.le] at hG)

end IveyG

section PinchedSet

/-- **Hamilton's pinching set**, as a subset of `ℝ³` in the form the tensor maximum
principle consumes: the ordered triples `ν ≤ μ ≤ λ` with `λ+μ+ν ≥ -3` and
`G(ν) ≤ λ+μ+ν`. -/
def iveyPinchedSet : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 2 ≤ v 1 ∧ v 1 ≤ v 0 ∧ -3 ≤ v 0 + v 1 + v 2 ∧ iveyG (v 2) ≤ v 0 + v 1 + v 2}

theorem mem_iveyPinchedSet_iff (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ iveyPinchedSet ↔
      v 2 ≤ v 1 ∧ v 1 ≤ v 0 ∧ IsIveyPinched (v 0) (v 1) (v 2) := by
  rw [iveyPinchedSet, Set.mem_ofPred_eq, isIveyPinched_iff_iveyG]

-- BENCH: ivey-set-convex
/-- **The pinching set is convex** — three half-spaces and one convex inequality. -/
theorem convex_iveyPinchedSet : Convex ℝ iveyPinchedSet := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  have hco : ∀ i : Fin 3, (a • u + b • v) i = a * u i + b * v i := by
    intro i; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hco, hco]; nlinarith
  · rw [hco, hco]; nlinarith
  · rw [hco, hco, hco]; nlinarith
  · rw [hco 0, hco 1, hco 2]
    have hG := convexOn_iveyG.2 (mem_univ (u 2)) (mem_univ (v 2)) ha hb hab
    simp only [smul_eq_mul] at hG
    calc iveyG (a * u 2 + b * v 2) ≤ a * iveyG (u 2) + b * iveyG (v 2) := hG
      _ ≤ a * (u 0 + u 1 + u 2) + b * (v 0 + v 1 + v 2) := by nlinarith
      _ = a * u 0 + b * v 0 + (a * u 1 + b * v 1) + (a * u 2 + b * v 2) := by ring

-- BENCH: ivey-set-closed
/-- **The pinching set is closed.** -/
theorem isClosed_iveyPinchedSet : IsClosed iveyPinchedSet := by
  have hp : ∀ i : Fin 3, Continuous fun v : EuclideanSpace ℝ (Fin 3) ↦ v i :=
    fun i ↦ (EuclideanSpace.proj i).continuous
  have h1 : IsClosed {v : EuclideanSpace ℝ (Fin 3) | v 2 ≤ v 1} :=
    isClosed_le (hp 2) (hp 1)
  have h2 : IsClosed {v : EuclideanSpace ℝ (Fin 3) | v 1 ≤ v 0} :=
    isClosed_le (hp 1) (hp 0)
  have h3 : IsClosed {v : EuclideanSpace ℝ (Fin 3) | -3 ≤ v 0 + v 1 + v 2} :=
    isClosed_le continuous_const (((hp 0).add (hp 1)).add (hp 2))
  have h4 : IsClosed {v : EuclideanSpace ℝ (Fin 3) | iveyG (v 2) ≤ v 0 + v 1 + v 2} :=
    isClosed_le (continuous_iveyG.comp (hp 2)) (((hp 0).add (hp 1)).add (hp 2))
  exact (h1.inter (h2.inter (h3.inter h4)))

end PinchedSet

end Pinching
end RicciFlowBlueprint
