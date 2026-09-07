/-
Global `C^k` extension of a tangent vector.

`FiberBundle.extend E v` is a section through `v ∈ T_xM`, but it is only `C^k`
near `x` (`exists_contMDiffOn_extend`), so it cannot be fed to any predicate that
demands a globally regular field. Multiplying by a smooth bump function supported
in that neighbourhood repairs this:

  `exists_contMDiff_extension : ∃ X, CMDiff k (T% X) ∧ X x = v`.

This is the lemma the working notes have carried as an open gap since the start
("no global `C²` extension of a tangent vector"). Its consequence for the
*statements* of `Hamilton.lean` is the point: predicates that quantify over
globally `C²` vector fields are otherwise contentless unless such fields are
known to exist, and nothing in `ChartedSpace + IsManifold + CompactSpace`
supplies them. With this lemma, "for every `C²` field `X` with `X x ≠ 0`" and
"for every nonzero `v ∈ T_xM`" become interchangeable
(`forall_contMDiff_iff_forall_tangent`), which is how Chow–Liao–Qin state the
same hypothesis (arXiv 2608.21502, `positiveRicciMetric`); see
`notes/hamilton-statement-comparison.md`.

`[T2Space M]` is required and is not decoration: `SmoothBumpFunction.contMDiff`
needs it. It is exactly the hypothesis whose absence made the old statements
vacuously satisfiable.
-/
import RicciFlowBlueprint.Ricci
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M]

-- BENCH: global-extension-of-local
/-- **A section that is `C^k` near a point agrees near that point with a globally `C^k`
section.** Multiply by a bump function that is `1` near `x` and supported where the section
is regular. This is the general local-to-global step; `exists_contMDiff_extension` is the
case of `FiberBundle.extend`. -/
theorem exists_contMDiff_eventuallyEq {n : ℕ∞} {x : M} {u : Set M} (hu : u ∈ 𝓝 x)
    {σ : Π y : M, TangentSpace I y} (hσ : CMDiff[u] (n : ℕ∞ω) (T% σ)) :
    ∃ τ : Π y : M, TangentSpace I y, CMDiff (n : ℕ∞ω) (T% τ) ∧ τ =ᶠ[𝓝 x] σ := by
  obtain ⟨f, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (interior_mem_nhds.mpr hu)).ex_mem
  refine ⟨fun y ↦ f y • σ y, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport
      ((f.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn) isOpen_interior hf
      (hσ.mono interior_subset)
  · filter_upwards [f.eventuallyEq_one] with y hy
    show f y • σ y = σ y
    rw [hy, Pi.one_apply, one_smul]

-- BENCH: global-extension
/-- **Every tangent vector is the value of a globally `C^k` vector field.** -/
theorem exists_contMDiff_extension {n : ℕ∞} {x : M} (v : TangentSpace I x) :
    ∃ X : Π y : M, TangentSpace I y, CMDiff (n : ℕ∞ω) (T% X) ∧ X x = v := by
  obtain ⟨s, hs, hext⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := (n : ℕ∞ω)) I E
      (V := fun y : M ↦ TangentSpace I y) v
  obtain ⟨X, hX, hXeq⟩ := exists_contMDiff_eventuallyEq hs hext
  refine ⟨X, hX, ?_⟩
  rw [hXeq.eq_of_nhds, FiberBundle.extend_apply_self]

/-- The `C²` case, which is what the curvature predicates use. -/
theorem exists_contMDiff_two_extension {x : M} (v : TangentSpace I x) :
    ∃ X : Π y : M, TangentSpace I y, CMDiff 2 (T% X) ∧ X x = v := by
  simpa using exists_contMDiff_extension (n := 2) v

-- BENCH: pointwise-iff
/-- **Quantifying over globally `C²` fields is the same as quantifying over tangent
vectors.** This is what makes the `Hamilton.lean` predicates say what they are meant to
say: without it, `∀ X, CMDiff 2 (T% X) → P x (X x)` could hold merely because no such
`X` exists. -/
theorem forall_contMDiff_iff_forall_tangent {x : M} (P : TangentSpace I x → Prop) :
    (∀ X : Π y : M, TangentSpace I y, CMDiff 2 (T% X) → P (X x)) ↔ ∀ v, P v := by
  constructor
  · intro h v
    obtain ⟨X, hX, hXv⟩ := exists_contMDiff_two_extension v
    exact hXv ▸ h X hX
  · exact fun h X _ ↦ h (X x)

end RicciFlowBlueprint
