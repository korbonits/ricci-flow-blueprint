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

Everything here is proved for an **arbitrary `C^k` vector bundle** (`section Bundle`), the
tangent-bundle statements being corollaries. Nothing in the bump-function argument is about
`TangentSpace`: mathlib's `FiberBundle.exists_contMDiffOn_extend` and
`ContMDiffOn.smul_section_of_tsupport` are already general. This is the form Hamilton's
pinching estimate needs — the curvature operator is a section of `Sym²(Λ²TM)`, not a vector
field, so a maximum principle for it cannot quantify over a constant direction vector and
must spread one into a section of the bundle instead.
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

section Bundle

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ y : M, AddCommGroup (V y)] [∀ y : M, Module ℝ (V y)]
  [∀ y : M, TopologicalSpace (V y)] [FiberBundle F V] [VectorBundle ℝ F V]

-- BENCH: global-extension-of-local-bundle
/-- **A section of a vector bundle that is `C^k` near a point agrees near that point with a
globally `C^k` section.** Multiply by a bump function that is `1` near `x` and supported where
the section is regular.

Nothing in the argument is about the tangent bundle: `SmoothBumpFunction` lives on the base and
`ContMDiffOn.smul_section_of_tsupport` is stated for an arbitrary vector bundle. This is the
form Hamilton's pinching needs, the curvature operator being a section of `Sym²(Λ²TM)` rather
than a vector field.

The conclusion is `∀ᶠ y in 𝓝 x, τ y = σ y` rather than `τ =ᶠ[𝓝 x] σ`: `Filter.EventuallyEq`
wants a non-dependent codomain, and `Π y, V y` is only non-dependent for the tangent bundle,
where `V y` reduces to `E`. -/
theorem exists_contMDiff_eventuallyEq_of_bundle {n : ℕ∞} {x : M} {u : Set M} (hu : u ∈ 𝓝 x)
    {σ : Π y : M, V y} (hσ : CMDiff[u] (n : ℕ∞ω) (T% σ)) :
    ∃ τ : Π y : M, V y, CMDiff (n : ℕ∞ω) (T% τ) ∧ ∀ᶠ y in 𝓝 x, τ y = σ y := by
  obtain ⟨f, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (interior_mem_nhds.mpr hu)).ex_mem
  refine ⟨fun y ↦ f y • σ y, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport
      ((f.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn) isOpen_interior hf
      (hσ.mono interior_subset)
  · filter_upwards [f.eventuallyEq_one] with y hy
    show f y • σ y = σ y
    rw [hy, Pi.one_apply, one_smul]

-- BENCH: global-extension-bundle
/-- **Every vector in a fibre is the value of a globally `C^k` section.** The general-bundle
form of `exists_contMDiff_extension`. -/
theorem exists_contMDiff_extension_of_bundle {n : ℕ∞} [ContMDiffVectorBundle (n : ℕ∞ω) F V I]
    {x : M} (v : V x) :
    ∃ σ : Π y : M, V y, CMDiff (n : ℕ∞ω) (T% σ) ∧ σ x = v := by
  obtain ⟨s, hs, hext⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := (n : ℕ∞ω)) I F (V := V) v
  obtain ⟨σ, hσ, hσeq⟩ := exists_contMDiff_eventuallyEq_of_bundle (I := I) F hs hext
  exact ⟨σ, hσ, by rw [hσeq.self_of_nhds, FiberBundle.extend_apply_self]⟩

-- BENCH: pointwise-iff-bundle
/-- **Quantifying over globally `C^k` sections is the same as quantifying over fibre
vectors.** This is what makes a predicate on sections of `V` say what it is meant to say;
`forall_contMDiff_iff_forall_tangent` is the tangent-bundle case at `k = 2`. -/
theorem forall_contMDiff_iff_forall_fiber {n : ℕ∞} [ContMDiffVectorBundle (n : ℕ∞ω) F V I]
    {x : M} (P : V x → Prop) :
    (∀ σ : Π y : M, V y, CMDiff (n : ℕ∞ω) (T% σ) → P (σ x)) ↔ ∀ v, P v := by
  refine ⟨fun h v ↦ ?_, fun h σ _ ↦ h (σ x)⟩
  obtain ⟨σ, hσ, hσv⟩ := exists_contMDiff_extension_of_bundle (I := I) F (n := n) v
  exact hσv ▸ h σ hσ

end Bundle

-- BENCH: global-extension-of-local
/-- **A section that is `C^k` near a point agrees near that point with a globally `C^k`
section.** Multiply by a bump function that is `1` near `x` and supported where the section
is regular. This is the general local-to-global step; `exists_contMDiff_extension` is the
case of `FiberBundle.extend`. The tangent-bundle case of
`exists_contMDiff_eventuallyEq_of_bundle`, stated separately because `Filter.EventuallyEq`
elaborates here (`TangentSpace I y` reduces to `E`) and is what the callers use. -/
theorem exists_contMDiff_eventuallyEq {n : ℕ∞} {x : M} {u : Set M} (hu : u ∈ 𝓝 x)
    {σ : Π y : M, TangentSpace I y} (hσ : CMDiff[u] (n : ℕ∞ω) (T% σ)) :
    ∃ τ : Π y : M, TangentSpace I y, CMDiff (n : ℕ∞ω) (T% τ) ∧ τ =ᶠ[𝓝 x] σ :=
  exists_contMDiff_eventuallyEq_of_bundle (I := I) E (V := fun y : M ↦ TangentSpace I y) hu hσ

-- BENCH: global-extension-fun
/-- **The scalar analogue**: a function that is `C^k` near `x` agrees near `x` with a globally
`C^k` function. Needed to globalise local frame coefficients. -/
theorem exists_contMDiff_eventuallyEq_fun {n : ℕ∞} {x : M} {u : Set M} (hu : u ∈ 𝓝 x)
    {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) (n : ℕ∞ω) f u) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) (n : ℕ∞ω) g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨φ, hφ⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (interior_mem_nhds.mpr hu)).ex_mem
  have hφs : CMDiff (n : ℕ∞ω) (φ : M → ℝ) := φ.contMDiff.of_le (by exact_mod_cast le_top)
  refine ⟨(φ : M → ℝ) • f, ?_, ?_⟩
  · refine contMDiff_of_contMDiffOn_union_of_isOpen
      (s := interior u) (t := (tsupport (φ : M → ℝ))ᶜ) ?_ ?_ ?_ isOpen_interior
      (isOpen_compl_iff.mpr (isClosed_tsupport _))
    · exact hφs.contMDiffOn.smul (hf.mono interior_subset)
    · refine ContMDiffOn.congr (contMDiffOn_const (c := (0 : ℝ))) fun y hy ↦ ?_
      show φ y • f y = (0 : ℝ)
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    · rw [Set.eq_univ_iff_forall]
      intro y
      by_cases hy : y ∈ interior u
      · exact Or.inl hy
      · exact Or.inr fun hc ↦ hy (hφ hc)
  · filter_upwards [φ.eventuallyEq_one] with y hy
    show φ y • f y = f y
    rw [hy, Pi.one_apply, one_smul]

-- BENCH: global-extension
/-- **Every tangent vector is the value of a globally `C^k` vector field.** -/
theorem exists_contMDiff_extension {n : ℕ∞} {x : M} (v : TangentSpace I x) :
    ∃ X : Π y : M, TangentSpace I y, CMDiff (n : ℕ∞ω) (T% X) ∧ X x = v :=
  exists_contMDiff_extension_of_bundle (I := I) E (V := fun y : M ↦ TangentSpace I y) v

/-- The `C²` case, which is what the curvature predicates use. -/
theorem exists_contMDiff_two_extension {x : M} (v : TangentSpace I x) :
    ∃ X : Π y : M, TangentSpace I y, CMDiff 2 (T% X) ∧ X x = v := by
  simpa using exists_contMDiff_extension (n := 2) v

/-- The `C³` case, which is what the second derivative of the curvature uses. -/
theorem exists_contMDiff_three_extension {x : M} (v : TangentSpace I x) :
    ∃ X : Π y : M, TangentSpace I y, CMDiff 3 (T% X) ∧ X x = v := by
  simpa using exists_contMDiff_extension (n := 3) v

-- BENCH: pointwise-iff
/-- **Quantifying over globally `C²` fields is the same as quantifying over tangent
vectors.** This is what makes the `Hamilton.lean` predicates say what they are meant to
say: without it, `∀ X, CMDiff 2 (T% X) → P x (X x)` could hold merely because no such
`X` exists. -/
theorem forall_contMDiff_iff_forall_tangent {x : M} (P : TangentSpace I x → Prop) :
    (∀ X : Π y : M, TangentSpace I y, CMDiff 2 (T% X) → P (X x)) ↔ ∀ v, P v := by
  refine ⟨fun h v ↦ ?_, fun h X _ ↦ h (X x)⟩
  obtain ⟨X, hX, hXv⟩ := exists_contMDiff_two_extension v
  exact hXv ▸ h X hX

end RicciFlowBlueprint
