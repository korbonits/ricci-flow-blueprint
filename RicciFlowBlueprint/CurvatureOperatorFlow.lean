/-
**`∂ₜRm₃ = ΔRm₃ + Q(Rm₃)`: the evolution of the dimension-three curvature operator.**

Every term is already on the table. `UhlenbeckFlow.lean` gives
`∂ₜRm₃ = (∂ₜscal)·1 − 2(2 Ric♯² + (∂ₜRic)♯)`, the moving index raising included;
`ScalarFlow.lean` gives `∂ₜscal = Δscal + 2|Ric|²`; `RicciEvolution.lean` with
`RicciReactionThree.lean` gives `∂ₜRic = Δ_g Ric + [k=l](2∑ᵢKᵢₖrᵢ − 2rₖ²)` in a Ricci eigenbasis;
and `CurvatureOperatorLaplacian.lean` gives `⟪ΔRm₃ v,w⟫ = (Δscal)⟪v,w⟫ − 2(Δ_g Ric)(v,w)`.

**This file first does the algebra, with no geometry in it.** In a Ricci eigenbasis the
Laplacian terms cancel exactly (`Δscal` against `Δscal`, `−2Δ_g Ric` against `−2Δ_g Ric`) and
what is left is diagonal: `2|Ric|² − 4rₖ² − 2(2∑ᵢKᵢₖrᵢ − 2rₖ²) = 2|Ric|² − 4∑ᵢKᵢₖrᵢ`. With
`λₖ = R − 2rₖ` the eigenvalues of `Rm₃` (twice the sectional curvature of the plane opposite
`bₖ`), that is `λₖ² + λᵢλⱼ` --- Hamilton's ODE, the eigenvalue of `Q(Rm₃)` on `bₖ`
(`hamiltonReaction_apply_basis`). The check at `k = 0` with `p = K₁₂`, `q = K₀₂`, `s = K₀₁`:
`2[(s+q)² + (s+p)² + (q+p)²] − 4[s(s+p) + q(q+p)] = 4p² + 4qs = λ₀² + λ₁λ₂`.
-/
import RicciFlowBlueprint.IveyReactionEndo

open ContinuousLinearMap
open scoped RealInnerProductSpace

namespace RicciFlowBlueprint

namespace Pinching

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

-- BENCH: curvature-operator-flow-algebra
/-- **The algebra of `∂ₜRm₃ = ΔRm₃ + Q(Rm₃)`**, in a Ricci eigenbasis `b`, with the sectional
curvatures `K` (symmetric, zero on the diagonal) and the Ricci eigenvalues `rₖ = ∑ₙ Kₖₙ`.

* `hD`: `D = s'·1 − 2(2S² + P)`, the time derivative as `UhlenbeckFlow.lean` delivers it;
* `hs'`: `s' = Δscal + 2|Ric|²`;
* `hP`: `(∂ₜRic)(bₖ,bₗ) = (Δ_g Ric)ₖₗ + [k=l](2∑ᵢKᵢₖrᵢ − 2rₖ²)`;
* `hL`: `(ΔRm₃)ₖₗ = Δscal·δₖₗ − 2(Δ_g Ric)ₖₗ`.

Then `D = L + Q((∑ r)·1 − 2S)`, and `(∑ r)·1 − 2S` is `Rm₃`. -/
theorem eq_add_hamiltonReaction_of_eigenbasis (b : OrthonormalBasis (Fin 3) ℝ W)
    (K : Fin 3 → Fin 3 → ℝ) (hK : ∀ i j, K i j = K j i) (hK0 : ∀ i, K i i = 0)
    {S P D L : W →L[ℝ] W} (hS : ∀ k, S (b k) = (∑ n, K k n) • (b k : W))
    {s' ds : ℝ} (Λ : Fin 3 → Fin 3 → ℝ)
    (hD : D = s' • ContinuousLinearMap.id ℝ W - (2 : ℝ) • ((2 : ℝ) • (S ∘L S) + P))
    (hs' : s' = ds + 2 * ∑ i, (∑ n, K i n) ^ 2)
    (hP : ∀ k l, ⟪P (b k), b l⟫ = Λ k l
      + if k = l then 2 * ∑ i, K i k * ∑ n, K i n - 2 * (∑ n, K k n) ^ 2 else 0)
    (hL : ∀ k l, ⟪L (b k), b l⟫ = (if k = l then ds else 0) - 2 * Λ k l) :
    D = L + hamiltonReaction ((∑ i, ∑ n, K i n) • ContinuousLinearMap.id ℝ W - (2 : ℝ) • S) := by
  classical
  set Rm := (∑ i, ∑ n, K i n) • ContinuousLinearMap.id ℝ W - (2 : ℝ) • S with hRm
  have hRmb : ∀ k, Rm (b k) = ((∑ i, ∑ n, K i n) - 2 * ∑ n, K k n) • (b k : W) := fun k ↦ by
    rw [hRm, sub_apply, smul_apply, smul_apply, id_apply, hS k, smul_smul, ← sub_smul]
  obtain ⟨h0, h1, h2⟩ := hamiltonReaction_apply_basis b hRmb
  have hon : ∀ k l, ⟪(b k : W), b l⟫ = if k = l then 1 else 0 :=
    fun k l ↦ orthonormal_iff_ite.mp b.orthonormal k l
  have hSS : ∀ k l, ⟪(S ∘L S) (b k), b l⟫ = (∑ n, K k n) ^ 2 * (if k = l then 1 else 0) :=
    fun k l ↦ by
      rw [comp_apply, hS k, map_smul, hS k, smul_smul, real_inner_smul_left, hon, sq]
  refine clm_ext_orthonormalBasis b fun k ↦ ?_
  refine InnerProductSpace.ext_inner_right_basis b.toBasis fun l ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, add_apply, inner_add_left]
  have hDk : ⟪D (b k), b l⟫ = s' * (if k = l then 1 else 0)
      - 2 * (2 * ((∑ n, K k n) ^ 2 * (if k = l then 1 else 0)) + ⟪P (b k), b l⟫) := by
    rw [hD, sub_apply, smul_apply, id_apply, smul_apply, add_apply, smul_apply,
      inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_add_left,
      real_inner_smul_left, hon, hSS]
  rw [hDk, hP, hL, hs']
  have s10 := hK 1 0
  have s20 := hK 2 0
  have s21 := hK 2 1
  have z0 := hK0 0
  have z1 := hK0 1
  have z2 := hK0 2
  fin_cases k <;> fin_cases l <;>
    simp [h0, h1, h2, real_inner_smul_left, hon, Fin.sum_univ_three, s10, s20, s21, z0, z1,
      z2] <;> ring

end Pinching

end RicciFlowBlueprint
