/-
**The Leibniz rule for `D/dt` on a Hom bundle**, and parallel morphism fields.

`BundleCovariantAlongCurve.lean` builds `D/dt` for a section of an arbitrary bundle. A
morphism field `A : Π y, V₁ y →L[ℝ] V₂ y` is such a section, of `Hom(V₁,V₂)`, and it acts on
sections of `V₁`. The rule relating the three derivatives is

  `D/dt (A σ) = (D/dt A)(σ) + A (D/dt σ)`,

and it is proved here. **No metric is used anywhere** --- unlike `TransportIsometry.lean`'s
pairing rule, where metric compatibility is what differentiates `⟪Aᵢ,Bⱼ⟫`; here the
derivative of `Bᵢ(Wⱼ)` along the curve **is** the definition of `∇A` rearranged.

**Why it is wanted.** The cross-fibre half of the maximum principle carries the tested
direction between fibres of the bundle the tested object is a section of. In dimension three
that bundle is `End(TM)`, and `IveyParallel.lean` shows Hamilton's pinching set is preserved
by *every* fibre isometry, hence by parallel transport of `TM`. What was missing is the
statement that conjugating by transport of `TM` **is** parallel transport of `End(TM)` ---
and that is this rule, cashed in: a morphism field is parallel exactly when it carries
parallel sections to parallel sections (`isParallelAlongSection_hom_iff`).

Both sections are expanded in local frames --- not the same frame, and neither parallel ---
exactly as `hasDerivAt_inner_along` does, with the product rule contributing the coordinate
parts of the two `D/dt`s and `covHom` the connection parts. Nothing is left over, which is
why the frames carry no hypotheses.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.BundleCovariantAlongCurve
import RicciFlowBlueprint.HomBundle

open Bundle Filter Module
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

section Algebra

/-! ### Two algebraic identities

Both are stated over bare **topological modules**, not normed spaces: a fibre `V₂ x` has no
norm here, and asking for one would break the tangent-bundle specialisation (corrected
belief 4). Neither is about manifolds at all. -/

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℝ W₁] [TopologicalSpace W₁]
  [AddCommGroup W₂] [Module ℝ W₂] [TopologicalSpace W₂] [IsTopologicalAddGroup W₂]
  [ContinuousSMul ℝ W₂] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A finite combination of continuous linear maps applied to a finite combination of
vectors. -/
theorem clm_sum_smul_apply_sum (c : ι → ℝ) (L : ι → W₁ →L[ℝ] W₂) (d : κ → ℝ) (w : κ → W₁) :
    (∑ i, c i • L i) (∑ j, d j • w j)
      = ∑ p : ι × κ, (c p.1 * d p.2) • (L p.1) (w p.2) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_apply, smul_apply, map_sum, map_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by module


/-- The identity the Leibniz rule reduces to once both sides are expanded in frames. -/
theorem clm_expansion_add (a a' : ι → ℝ) (b b' : κ → ℝ) (Bv DB : ι → W₁ →L[ℝ] W₂)
    (Wv DW : κ → W₁) :
    (∑ i, (a i • DB i + a' i • Bv i)) (∑ j, b j • Wv j)
        + (∑ i, a i • Bv i) (∑ j, (b j • DW j + b' j • Wv j))
      = ∑ p : ι × κ, ((a p.1 * b p.2) • ((DB p.1) (Wv p.2) + (Bv p.1) (DW p.2))
          + (a' p.1 * b p.2 + a p.1 * b' p.2) • (Bv p.1) (Wv p.2)) := by
  have e₁ : (∑ i, (a i • DB i + a' i • Bv i)) (∑ j, b j • Wv j)
      = ∑ p : ι × κ, ((a p.1 * b p.2) • (DB p.1) (Wv p.2)
          + (a' p.1 * b p.2) • (Bv p.1) (Wv p.2)) := by
    rw [Fintype.sum_prod_type]
    simp only [sum_apply, add_apply, smul_apply, map_sum, map_smul, Finset.smul_sum,
      mul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by module
  have e₂ : (∑ i, a i • Bv i) (∑ j, (b j • DW j + b' j • Wv j))
      = ∑ p : ι × κ, ((a p.1 * b p.2) • (Bv p.1) (DW p.2)
          + (a p.1 * b' p.2) • (Bv p.1) (Wv p.2)) := by
    rw [Fintype.sum_prod_type]
    simp only [sum_apply, smul_apply, map_sum, map_add, map_smul, Finset.smul_sum,
      mul_smul, ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by module
  rw [e₁, e₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [add_smul, smul_add]
  abel

end Algebra

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x : M, AddCommGroup (V₁ x)] [∀ x : M, Module ℝ (V₁ x)]
  [∀ x : M, TopologicalSpace (V₁ x)] [∀ x : M, IsTopologicalAddGroup (V₁ x)]
  [∀ x : M, ContinuousSMul ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x : M, AddCommGroup (V₂ x)] [∀ x : M, Module ℝ (V₂ x)]
  [∀ x : M, TopologicalSpace (V₂ x)] [∀ x : M, IsTopologicalAddGroup (V₂ x)]
  [∀ x : M, ContinuousSMul ℝ (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 1 F₂ V₂ I]
  (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)

set_option maxSynthPendingDepth 3

variable {γ : ℝ → M} {t : ℝ}

omit [CompleteSpace E] [T2Space M] [FiniteDimensional ℝ F₂]
  [ContMDiffVectorBundle 1 F₂ V₂ I] in
/-- `∇A` at a bare tangent vector rather than along a vector field: `homCov_apply` quantifies
over a field `X` but uses only `X x`, so a `FiberBundle.extend` of the vector discharges it.
This is `mvfderiv_inner_eq_apply`'s manoeuvre one bundle up. -/
theorem homCov_apply_vector {A : Π y : M, V₁ y →L[ℝ] V₂ y} {σ : Π y : M, V₁ y} {x : M}
    (hA : IsMDiffHomAt (I := I) F₁ F₂ A x) (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    homCov cov₁ cov₂ A x v (σ x)
      = cov₂ (fun y ↦ A y (σ y)) x v - A x (cov₁ σ x v) := by
  have h := homCov_apply (cov₁ := cov₁) (cov₂ := cov₂) hA
    (X := FiberBundle.extend E v) (FiberBundle.mdifferentiableAt_extend I E v) hσ
  simp only [FiberBundle.extend_apply_self, covHom] at h
  exact h

omit [CompleteSpace E] in
-- BENCH: hom-bundle-leibniz-along
/-- **The Leibniz rule for `D/dt` on a Hom bundle**:
`D/dt (A σ) = (D/dt A)(σ) + A (D/dt σ)`.

Expand `A` and `σ` in local frames --- not the same frame, and neither parallel. The product
`A σ` is then a combination of the *global* sections `y ↦ Bᵢ y (Wⱼ y)` of `V₂` with
coefficients `fᵢ gⱼ`, so `D/dt` of it is computed by `eq_sum_of_expansion`; the product rule
supplies the `fᵢ'` and `gⱼ'` terms, which are exactly the coordinate parts of the two
derivatives on the right, and `covHom` --- the definition of `∇A` rearranged --- supplies
`∇_{γ'}(BᵢWⱼ) = (∇_{γ'}Bᵢ)(Wⱼ) + Bᵢ(∇_{γ'}Wⱼ)`, which is exactly the connection parts.
Nothing is left over, which is why the frames carry no hypotheses. -/
theorem covAlongSection_hom_apply
    {A : Π u : ℝ, V₁ (γ u) →L[ℝ] V₂ (γ u)} {σ : Π u : ℝ, V₁ (γ u)}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hA : MDiffAlongSectionAt I (F₁ →L[ℝ] F₂) (fun y : M ↦ V₁ y →L[ℝ] V₂ y) γ A t)
    (hσ : MDiffAlongSectionAt I F₁ V₁ γ σ t) :
    covAlongSection cov₂ γ (fun u ↦ A u (σ u)) t
      = covAlongSection (homCov cov₁ cov₂) γ A t (σ t)
        + A t (covAlongSection cov₁ γ σ t) := by
  classical
  obtain ⟨ι, _, B, f, hB, hf, hAexp⟩ := exists_frame_expansion_section hγ hA
  obtain ⟨κ, _, W, g, hW, hg, hσexp⟩ := exists_frame_expansion_section hγ hσ
  have hBm : ∀ i, IsMDiffHomAt (I := I) F₁ F₂ (B i) (γ t) := fun i ↦
    isMDiffHomAt_of_section ((hB i).mdifferentiable one_ne_zero (γ t))
  have hWm : ∀ j, MDiffAt (T% (W j)) (γ t) := fun j ↦
    (hW j).mdifferentiable one_ne_zero (γ t)
  -- the product frame, a global `C¹` section of `V₂`
  have hprod : ∀ p : ι × κ,
      CMDiff (1 : ℕ∞ω) (T% (fun y : M ↦ B p.1 y (W p.2 y))) := fun p ↦
    ContMDiff.clm_bundle_apply (hB p.1) (hW p.2)
  have hcoeff : ∀ p : ι × κ, DifferentiableAt ℝ (fun u ↦ f p.1 u * g p.2 u) t := fun p ↦
    (hf p.1).mul (hg p.2)
  -- the product, expanded
  have hexp : ∀ᶠ u in 𝓝 t, (fun u ↦ A u (σ u)) u
      = ∑ p : ι × κ, (f p.1 u * g p.2 u) • (B p.1 (γ u)) (W p.2 (γ u)) := by
    filter_upwards [hAexp, hσexp] with u hu hu'
    show A u (σ u) = _
    rw [hu, hu']
    exact clm_sum_smul_apply_sum _ _ _ _
  have hprodm : MDiffAlongSectionAt I F₂ V₂ γ (fun u ↦ A u (σ u)) t := by
    have h1 : MDiffAlongSectionAt I (F₁ →L[ℝ] F₂) (fun y : M ↦ V₁ y →L[ℝ] V₂ y) γ A t := hA
    exact MDifferentiableAt.clm_bundle_apply h1 hσ
  -- the three derivatives
  have hL := (isCovDerivAlongSection_covAlongSection cov₂ γ).eq_sum_of_expansion
    hγ hprodm hγ hprod hcoeff hexp
  have hDA := (isCovDerivAlongSection_covAlongSection (homCov cov₁ cov₂) γ).eq_sum_of_expansion
    hγ hA hγ hB hf hAexp
  have hDσ := (isCovDerivAlongSection_covAlongSection cov₁ γ).eq_sum_of_expansion
    hγ hσ hγ hW hg hσexp
  have hAt : A t = ∑ i, f i t • B i (γ t) := hAexp.self_of_nhds
  have hσt : σ t = ∑ j, g j t • W j (γ t) := hσexp.self_of_nhds
  -- the connection part of the product frame is the definition of `∇A` rearranged
  have hconn : ∀ p : ι × κ,
      cov₂ (fun y ↦ B p.1 y (W p.2 y)) (γ t) (velocity γ t)
        = homCov cov₁ cov₂ (B p.1) (γ t) (velocity γ t) (W p.2 (γ t))
          + B p.1 (γ t) (cov₁ (W p.2) (γ t) (velocity γ t)) := by
    intro p
    rw [homCov_apply_vector cov₁ cov₂ (hBm p.1) (hWm p.2)]
    abel
  have hderiv : ∀ p : ι × κ, deriv (fun u ↦ f p.1 u * g p.2 u) t
      = deriv (f p.1) t * g p.2 t + f p.1 t * deriv (g p.2) t := fun p ↦
    deriv_mul (hf p.1) (hg p.2)
  rw [hL, hDA, hDσ, hAt, hσt,
    clm_expansion_add (fun i ↦ f i t) (fun i ↦ deriv (f i) t) (fun j ↦ g j t)
      (fun j ↦ deriv (g j) t)
      (fun i ↦ B i (γ t)) (fun i ↦ homCov cov₁ cov₂ (B i) (γ t) (velocity γ t))
      (fun j ↦ W j (γ t)) (fun j ↦ cov₁ (W j) (γ t) (velocity γ t))]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [hconn p, hderiv p]


section Parallel

/-! ### Parallel morphism fields

The rule cashed in. A parallel morphism field carries parallel sections to parallel
sections, and --- the half the converse needs --- a morphism field whose action on one
parallel section is parallel has `D/dt A` killing that section.

The **full** converse, that a morphism field killing every parallel section is itself
parallel, needs a family of parallel sections spanning each fibre. On `TM` that is
`ParallelTransportGlobal.lean`'s transport applied to a basis, and it is the next piece;
it is stated there rather than here because it wants a metric, and nothing in this file
does. -/

variable {A : Π u : ℝ, V₁ (γ u) →L[ℝ] V₂ (γ u)} {σ : Π u : ℝ, V₁ (γ u)} {s : Set ℝ}

omit [CompleteSpace E] in
/-- **A parallel morphism field carries parallel sections to parallel sections.** -/
theorem isParallelAlongSection_hom
    (hγ : ∀ u ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ u)
    (hA : ∀ u ∈ s, MDiffAlongSectionAt I (F₁ →L[ℝ] F₂) (fun y : M ↦ V₁ y →L[ℝ] V₂ y) γ A u)
    (hσ : ∀ u ∈ s, MDiffAlongSectionAt I F₁ V₁ γ σ u)
    (hpA : IsParallelAlongSection I (F₁ →L[ℝ] F₂) (fun y : M ↦ V₁ y →L[ℝ] V₂ y)
      (homCov cov₁ cov₂) γ A s)
    (hpσ : IsParallelAlongSection I F₁ V₁ cov₁ γ σ s) :
    IsParallelAlongSection I F₂ V₂ cov₂ γ (fun u ↦ A u (σ u)) s := by
  intro u hu
  rw [covAlongSection_hom_apply cov₁ cov₂ (hγ u hu) (hA u hu) (hσ u hu), hpA u hu, hpσ u hu]
  simp

omit [CompleteSpace E] in
/-- **The converse, one section at a time.** If `σ` and `A σ` are both parallel at `t`, then
`D/dt A` kills `σ t`. Quantified over enough parallel sections to span the fibre this says
`A` is parallel; supplying them is what a metric buys. -/
theorem covAlongSection_hom_apply_eq_zero
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hA : MDiffAlongSectionAt I (F₁ →L[ℝ] F₂) (fun y : M ↦ V₁ y →L[ℝ] V₂ y) γ A t)
    (hσ : MDiffAlongSectionAt I F₁ V₁ γ σ t)
    (hpσ : covAlongSection cov₁ γ σ t = 0)
    (hpAσ : covAlongSection cov₂ γ (fun u ↦ A u (σ u)) t = 0) :
    covAlongSection (homCov cov₁ cov₂) γ A t (σ t) = 0 := by
  have h := covAlongSection_hom_apply cov₁ cov₂ hγ hA hσ
  rw [hpAσ, hpσ, map_zero, add_zero] at h
  exact h.symm

end Parallel

end CovariantDerivative
