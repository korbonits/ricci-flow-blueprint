/-
**Hamilton's reaction on endomorphisms, and Nagumo's condition for it on the pinching set.**

In dimension three the reaction term of `∂ₜRm₃` is `Q(R) = R² + R^#`, with `R^#` the adjugate;
by Cayley--Hamilton `R^# = R² − (tr R)R + σ₂(R)·1`, so

`Q(R) = 2R² − (tr R)·R + σ₂(R)·1`,   `σ₂(R) = ((tr R)² − tr R²)/2`,

a polynomial in `R` (`hamiltonReaction`). On an eigenvector with eigenvalue `λᵢ` it acts by
`λᵢ² + λⱼλₖ` --- Hamilton's ODE, `Pinching.lean`'s `IsCurvatureODE`
(`hamiltonReaction_apply_basis`, checked against `RicciReactionThree.lean`'s geometry
symbolically).

**Nagumo's condition** (`hsForm_hamiltonReaction_nonpos`): at a self-adjoint operator `p` in the
pinching set, `Q(p)` points into the self-adjoint part of the set, measured in the
Hilbert--Schmidt form. The proof is `TensorMaximumPrinciple.lean`'s `subtangential_of_invariant`
with an explicit curve: diagonalise `p`, run Hamilton's ODE on its eigenvalues
(`exists_isCurvatureODE`), and put the solution back on the same eigenbasis. The curve starts at
`p`, leaves it with velocity `Q(p)`, and stays in the set because the ODE preserves both the
ordering of the eigenvalues and the pinching condition from *every* pinched start
(`IsCurvatureODE.isIveyPinched_of_isIveyPinched`).

**The Hilbert--Schmidt form is carried as a value** (`hsForm c`), never as an instance on
`W →L W` --- that space already has the operator norm, and corrected belief 6 says the two cannot
coexist as instances. The consumer, the maximum principle on `EndTangent`, reaches it through
`hsFibre`.
-/
import RicciFlowBlueprint.IveyReaction
import RicciFlowBlueprint.IveyEndo
import RicciFlowBlueprint.EndMetric
import RicciFlowBlueprint.TensorMaximumPrinciple

open Set Filter Module ContinuousLinearMap
open scoped RealInnerProductSpace Topology

namespace RicciFlowBlueprint

namespace Pinching

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The rank-one operator `w ↦ ⟪v, w⟫ v`. -/
noncomputable def rankOne (v : W) : W →L[ℝ] W := (innerSL ℝ v).smulRight v

omit [FiniteDimensional ℝ W] in
@[simp] theorem rankOne_apply (v w : W) : rankOne v w = ⟪v, w⟫ • v := by
  simp [rankOne]

omit [FiniteDimensional ℝ W] in
/-- Two operators agreeing on an orthonormal basis are equal. -/
theorem clm_ext_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ W)
    {A B : W →L[ℝ] W} (h : ∀ i, A (b i) = B (b i)) : A = B := by
  apply ContinuousLinearMap.coe_injective
  exact b.toBasis.ext fun i ↦ by simpa using h i

/-- **Hamilton's reaction on an endomorphism**: `Q(R) = 2R² − (tr R)·R + σ₂(R)·1`. -/
noncomputable def hamiltonReaction (A : W →L[ℝ] W) : W →L[ℝ] W :=
  (2 : ℝ) • (A ∘L A) - traceEndo W A • A
    + ((traceEndo W A ^ 2 - traceEndo W (A ∘L A)) / 2) • ContinuousLinearMap.id ℝ W

/-- The trace of an operator diagonal in an orthonormal basis is the sum of its entries. -/
theorem traceEndo_of_diag {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ W)
    {A : W →L[ℝ] W} {e : ι → ℝ} (hA : ∀ i, A (b i) = e i • (b i : W)) :
    traceEndo W A = ∑ i, e i := by
  rw [traceEndo_apply, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change ⟪b i, A (b i)⟫ = e i
  rw [hA i, real_inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
  ring

-- BENCH: hamilton-reaction-basis
/-- **On an eigenvector, Hamilton's reaction is Hamilton's ODE**: with eigenvalues `λ, μ, ν`
on an orthonormal basis, `Q(R)e₀ = (λ² + μν)e₀`, and cyclically. -/
theorem hamiltonReaction_apply_basis (b : OrthonormalBasis (Fin 3) ℝ W) {A : W →L[ℝ] W}
    {e : Fin 3 → ℝ} (hA : ∀ i, A (b i) = e i • (b i : W)) :
    hamiltonReaction A (b 0) = (e 0 ^ 2 + e 1 * e 2) • (b 0 : W) ∧
    hamiltonReaction A (b 1) = (e 1 ^ 2 + e 0 * e 2) • (b 1 : W) ∧
    hamiltonReaction A (b 2) = (e 2 ^ 2 + e 0 * e 1) • (b 2 : W) := by
  have hAA : ∀ i, (A ∘L A) (b i) = (e i ^ 2) • (b i : W) := fun i ↦ by
    rw [ContinuousLinearMap.comp_apply, hA i, map_smul, hA i, smul_smul, sq]
  have htr := traceEndo_of_diag b hA
  have htr2 := traceEndo_of_diag b hAA
  simp only [Fin.sum_univ_three] at htr htr2
  have key : ∀ i, hamiltonReaction A (b i)
      = (2 * e i ^ 2 - (e 0 + e 1 + e 2) * e i
          + ((e 0 + e 1 + e 2) ^ 2 - (e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2)) / 2) • (b i : W) := by
    intro i
    simp only [hamiltonReaction, add_apply, sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, hAA i, hA i, htr, htr2, smul_smul]
    rw [← sub_smul, ← add_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [key 0]; congr 1; ring
  · rw [key 1]; congr 1; ring
  · rw [key 2]; congr 1; ring

omit [FiniteDimensional ℝ W] in
/-- A rank-one operator `⟪v,·⟫v` is symmetric. -/
theorem inner_rankOne_comm (v x y : W) : ⟪rankOne v x, y⟫ = ⟪x, rankOne v y⟫ := by
  simp only [rankOne_apply, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x v]
  ring

variable [Nontrivial W]

-- BENCH: hamilton-reaction-nagumo
/-- **Nagumo's condition for Hamilton's reaction on the pinching set.** At a self-adjoint `p`
in the pinching set, for every Hilbert--Schmidt outward normal `n` of the self-adjoint part of
the set, `⟨n, Q(p)⟩ ≤ 0`.

The curve: diagonalise `p` (mathlib's eigenvalues come sorted), run Hamilton's ODE on the
eigenvalues, and put the solution back on the same eigenbasis. It starts at `p`, has velocity
`Q(p)` because on each eigenvector `Q` acts by the ODE's right-hand side, and stays in the set
because the ODE preserves the ordering and the pinching condition from every pinched start. -/
theorem hsForm_hamiltonReaction_nonpos (hdim : finrank ℝ W = 3)
    {κ : Type*} [Fintype κ] (c : OrthonormalBasis κ ℝ W)
    {p : W →L[ℝ] W} (hp : p ∈ iveyEndoSet W) (hsym : (p : W →ₗ[ℝ] W).IsSymmetric)
    {nn : W →L[ℝ] W}
    (hn : ∀ q ∈ iveyEndoSet W, (q : W →ₗ[ℝ] W).IsSymmetric → hsForm c nn (q - p) ≤ 0) :
    hsForm c nn (hamiltonReaction p) ≤ 0 := by
  classical
  set b := hsym.eigenvectorBasis hdim with hbdef
  set e := hsym.eigenvalues hdim with hedef
  have he : Antitone e := hsym.eigenvalues_antitone hdim
  have hpb : ∀ i, p (b i) = e i • (b i : W) := fun i ↦ hsym.apply_eigenvectorBasis hdim i
  have hpin : IsIveyPinched (e 0) (e 1) (e 2) :=
    (mem_iveyEndoSet_iff_isIveyPinched_antitone b hpb he).mp hp
  have h10 : e 1 ≤ e 0 := he (by decide)
  have h21 : e 2 ≤ e 1 := he (by decide)
  obtain ⟨T, hT, l, m, n, hl0, hm0, hn0, hode⟩ := exists_isCurvatureODE (e 0) (e 1) (e 2)
  have hT0 : (0 : ℝ) ≤ T := hT.le
  -- the curve through `p`
  set γ : ℝ → W →L[ℝ] W := fun s ↦
    l s • rankOne (b 0 : W) + m s • rankOne (b 1 : W) + n s • rankOne (b 2 : W) with hγdef
  have hbb : ∀ i j, rankOne (b i : W) (b j) = if i = j then (b i : W) else 0 := by
    intro i j
    rw [rankOne_apply, orthonormal_iff_ite.mp b.orthonormal i j]
    split_ifs <;> simp
  have hγb : ∀ s, γ s (b 0) = l s • (b 0 : W) ∧ γ s (b 1) = m s • (b 1 : W)
      ∧ γ s (b 2) = n s • (b 2 : W) := by
    intro s
    simp only [hγdef, add_apply, smul_apply, hbb]
    refine ⟨?_, ?_, ?_⟩ <;> simp
  -- it starts at `p`
  have hγ0 : γ 0 = p := by
    refine clm_ext_orthonormalBasis b fun i ↦ ?_
    fin_cases i
    · show γ 0 (b 0) = p (b 0)
      rw [(hγb 0).1, hpb, hl0]
    · show γ 0 (b 1) = p (b 1)
      rw [(hγb 0).2.1, hpb, hm0]
    · show γ 0 (b 2) = p (b 2)
      rw [(hγb 0).2.2, hpb, hn0]
  -- it leaves with velocity `Q(p)`
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0⟩
  have hγd : HasDerivAt γ ((l 0 ^ 2 + m 0 * n 0) • rankOne (b 0 : W)
      + (m 0 ^ 2 + l 0 * n 0) • rankOne (b 1 : W)
      + (n 0 ^ 2 + l 0 * m 0) • rankOne (b 2 : W)) 0 :=
    (((hode.hl 0 hmem0).smul_const (rankOne (b 0 : W))).add
      ((hode.hm 0 hmem0).smul_const (rankOne (b 1 : W)))).add
      ((hode.hn 0 hmem0).smul_const (rankOne (b 2 : W)))
  have hQ := hamiltonReaction_apply_basis b hpb
  have hvel : (l 0 ^ 2 + m 0 * n 0) • rankOne (b 0 : W)
      + (m 0 ^ 2 + l 0 * n 0) • rankOne (b 1 : W)
      + (n 0 ^ 2 + l 0 * m 0) • rankOne (b 2 : W) = hamiltonReaction p := by
    refine clm_ext_orthonormalBasis b fun i ↦ ?_
    simp only [add_apply, smul_apply, hbb]
    fin_cases i
    · simp [hQ.1, hl0, hm0, hn0]
    · simp [hQ.2.1, hl0, hm0, hn0]
    · simp [hQ.2.2, hl0, hm0, hn0]
  rw [hvel] at hγd
  -- it stays in the set
  have hin : ∀ s ∈ Icc 0 T, γ s ∈ iveyEndoSet W := by
    intro s hs
    have hlm := hode.le_preserved_lm hT0 (by rw [hl0, hm0]; exact h10) s hs
    have hmn := hode.le_preserved_mn hT0 (by rw [hm0, hn0]; exact h21) s hs
    have hpin' := hode.isIveyPinched_of_isIveyPinched hT0 (by rw [hl0, hm0]; exact h10)
      (by rw [hm0, hn0]; exact h21) (by rw [hl0, hm0, hn0]; exact hpin) s hs
    exact (mem_iveyEndoSet_iff_isIveyPinched b (hγb s).1 (hγb s).2.1 (hγb s).2.2 hmn hlm).mpr
      hpin'
  have hsymγ : ∀ s, ((γ s : W →L[ℝ] W) : W →ₗ[ℝ] W).IsSymmetric := by
    intro s x y
    simp only [hγdef, ContinuousLinearMap.coe_coe, add_apply, smul_apply, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_rankOne_comm]
  -- the slope argument of `subtangential_of_invariant`, in the Hilbert--Schmidt form
  have hd : HasDerivWithinAt (fun s ↦ hsForm c nn (γ s)) (hsForm c nn (hamiltonReaction p))
      (Ioi 0) 0 :=
    ((hsForm c nn).hasFDerivAt.comp_hasDerivAt 0 hγd).hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hd
  refine le_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsGT hT] with s hs
  rw [slope_def_field, hγ0, ← map_sub, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (hn (γ s) (hin s ⟨hs.1.le, hs.2.le⟩) (hsymγ s))
    hs.1.le

end Pinching

end RicciFlowBlueprint
