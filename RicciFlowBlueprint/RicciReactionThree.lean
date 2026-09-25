/-
**The reaction term of `∂ₜRic` in dimension three.**

`RicciEvolution.lean` gives `∂ₜRic(Y,Z) = (Δ_g Ric)(Y,Z) + T₁ + T₂ + T₃ + T₄`, the four
terms being two traced curvature commutators and two `Ric`-against-`Rm` contractions --- all
quadratic in the curvature, all stated on fields. This file evaluates their sum on a Ricci
eigenbasis in dimension three:

`T₁ + T₂ + T₃ + T₄ (eₖ, eₗ) = [k = l]·(2∑ᵢ Kᵢₖ rᵢ − 2rₖ²)`,

with `Kᵢⱼ` the sectional curvature of `eᵢ∧eⱼ` and `rᵢ = ∑ₙ Kᵢₙ` the Ricci eigenvalue --- the
Lichnerowicz reaction `2 Rm∗Ric − 2 Ric²`, diagonal in the eigenbasis. Combined with the moving
index raising (`UhlenbeckFlow.lean`) this is what makes the reaction of `∂ₜRm₃` Hamilton's
`λ² + μν` (checked symbolically before it was formalised).

**Two ingredients, both proved elsewhere and combined here.** The commutators are evaluated at
a point by `CurvatureCommutatorPointwise.lean`, the contractions by expanding the curvature
vector in the basis (`ricciForm_curvature_left`/`_right`); then every component of `Rm` is read
off `CurvatureThreeTable.lean` and every component of `Ric` off the eigenbasis. What is left is
a finite sum over `Fin 3`, closed by `simp` and `ring` --- the table's sectional curvatures are
carried through an opaque `secAt` so that the table's right-hand side is not itself rewritten.
-/
import RicciFlowBlueprint.CurvatureThreeTable
import RicciFlowBlueprint.CurvatureCommutatorPointwise

open Bundle Filter RicciFlowBlueprint
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  {x : M}

set_option maxSynthPendingDepth 3

section Contraction

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))

/-- **`Ric` against a curvature vector, first slot**:
`Ric(R(X,Y)Z, w) = ∑ₘ Rm(X,Y,Z,eₘ) Ric(eₘ, w)`. -/
theorem ricciForm_curvature_left {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (w : TangentSpace I x) :
    cov.ricciForm x (cov.curvature X Y Z x) w
      = ∑ m, cov.curvatureTensorAt (X x) (Y x) (Z x) (b m) * cov.ricciAt x (b m) w := by
  rw [cov.ricciForm_apply]
  conv_lhs => rw [← sum_inner_smul_eq b (cov.curvature X Y Z x)]
  rw [sum_smul_of_additive (fun v ↦ cov.ricciAt x v w)
    (fun p q ↦ cov.ricciAt_add_left p q w) (fun r p ↦ cov.ricciAt_smul_left r p w)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [real_inner_comm, cov.curvatureTensorAt_apply_field hX hY hZ]

/-- **`Ric` against a curvature vector, second slot.** -/
theorem ricciForm_curvature_right {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (w : TangentSpace I x) :
    cov.ricciForm x w (cov.curvature X Y Z x)
      = ∑ m, cov.curvatureTensorAt (X x) (Y x) (Z x) (b m) * cov.ricciAt x w (b m) := by
  rw [cov.ricciForm_apply]
  conv_lhs => rw [← sum_inner_smul_eq b (cov.curvature X Y Z x)]
  rw [sum_smul_of_additive (fun v ↦ cov.ricciAt x w v)
    (fun p q ↦ cov.ricciAt_add_right w p q) (fun r p ↦ cov.ricciAt_smul_right r w p)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [real_inner_comm, cov.curvatureTensorAt_apply_field hX hY hZ]

end Contraction

section Three

variable (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
  (htor : cov.torsion = 0) (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x))

/-- The sectional curvature of the plane `bᵢ ∧ bⱼ`, kept opaque so that the component table
can be used as a rewrite rule without rewriting its own right-hand side. -/
noncomputable def secAt (i j : Fin 3) : ℝ := cov.curvatureTensorAt (b i) (b j) (b j) (b i)

include hmetric htor in
theorem secAt_comm (i j : Fin 3) : cov.secAt b i j = cov.secAt b j i :=
  cov.curvatureTensorAt_sec_comm hmetric htor _ _

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] [CompleteSpace E] in
theorem secAt_self (i : Fin 3) : cov.secAt b i i = 0 :=
  cov.curvatureTensorAt_self_fst (b i)

variable (hric : ∀ i j, i ≠ j → cov.ricciAt x (b i) (b j) = 0)

include hmetric htor hric in
/-- The component table, with the sectional curvatures opaque. -/
theorem curvatureTensorAt_eq_secAt (i j k l : Fin 3) :
    cov.curvatureTensorAt (b i) (b j) (b k) (b l)
      = (if i = l ∧ j = k then cov.secAt b i j else 0)
        - (if i = k ∧ j = l then cov.secAt b i j else 0) :=
  cov.curvatureTensorAt_three_table hmetric htor b hric i j k l

include hmetric htor hric in
/-- **Ricci in its eigenbasis**: `Ric(bₚ, b_q) = [p = q] ∑ₙ K_{pn}`. -/
theorem ricciAt_eq_secAt (p q : Fin 3) :
    cov.ricciAt x (b p) (b q) = if p = q then ∑ n, cov.secAt b p n else 0 := by
  rcases eq_or_ne p q with h | h
  · subst h
    simp only [↓reduceIte]
    rw [cov.ricciAt_diag_eq_sum_sec hmetric htor b]
    rfl
  · simp only [h, ↓reduceIte]
    exact hric p q h

variable [ContMDiffCovariantDerivative cov 2] [ContMDiffCovariantDerivative cov 3]

include hmetric htor hric in
-- BENCH: ricci-reaction-three
/-- **The reaction term of `∂ₜRic` in dimension three**, on a Ricci eigenbasis:
the two traced curvature commutators and the two `Ric`-against-`Rm` contractions of
`RicciEvolution.lean` sum to `[k = l]·(2∑ᵢ Kᵢₖ rᵢ − 2rₖ²)` --- the Lichnerowicz reaction
`2 Rm∗Ric − 2 Ric²`, diagonal. -/
theorem ricciReaction_three {fr : Fin 3 → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 4 (T% (fr i))) (hfrx : ∀ i, fr i x = b i) (k l : Fin 3) :
    (∑ j, ∑ i, (⟪cov.curvatureCommutator (fr i) (fr j) (fr k) (fr i) (fr l) x, fr j x⟫ : ℝ))
      + (∑ j, ∑ i, (⟪cov.curvatureCommutator (fr i) (fr k) (fr i) (fr j) (fr l) x,
          fr j x⟫ : ℝ))
      + ∑ j, cov.ricciForm x (cov.curvature (fr j) (fr k) (fr l) x) (fr j x)
      + ∑ j, cov.ricciForm x (fr l x) (cov.curvature (fr j) (fr k) (fr j) x)
    = if k = l then
        2 * ∑ i, cov.secAt b i k * ∑ n, cov.secAt b i n - 2 * (∑ n, cov.secAt b k n) ^ 2
      else 0 := by
  have h2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  simp only [cov.inner_curvatureCommutator_eq_sum b (hfr _) (hfr _) (hfr _) (hfr _) (hfr _),
    cov.ricciForm_curvature_left b (h2 _) (h2 _) (h2 _),
    cov.ricciForm_curvature_right b (h2 _) (h2 _) (h2 _), hfrx,
    cov.curvatureTensorAt_eq_secAt hmetric htor b hric,
    cov.ricciAt_eq_secAt hmetric htor b hric]
  have s10 := cov.secAt_comm hmetric htor b 1 0
  have s20 := cov.secAt_comm hmetric htor b 2 0
  have s21 := cov.secAt_comm hmetric htor b 2 1
  have s0 := cov.secAt_self b 0
  have s1 := cov.secAt_self b 1
  have s2 := cov.secAt_self b 2
  fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_three, s10, s20, s21, s0, s1, s2] <;> ring

end Three

end CovariantDerivative
