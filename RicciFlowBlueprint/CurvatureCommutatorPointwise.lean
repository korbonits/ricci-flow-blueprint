/-
**The curvature commutator at a point.**

`BianchiDeriv.lean`'s `curvatureCommutator X Y A B C` is the right-hand side of the Ricci
identity for `Rm`, and it is what the quadratic terms of `∂ₜRm` and `∂ₜRic` are made of
(`CurvatureFlow.lean`, `RicciEvolution.lean`). It is stated on *fields*, with the curvature
applied to curvature *sections* --- which is what the Ricci identity produces, and is useless
for any algebra at a point. This file evaluates it at a point in an orthonormal basis:

`⟪C(X,Y;A,B,C), w⟫ = ∑ₘ [Rm(X,Y,eₘ,w)Rm(A,B,C,eₘ) − Rm(X,Y,A,eₘ)Rm(eₘ,B,C,w)
                         − Rm(X,Y,B,eₘ)Rm(A,eₘ,C,w) − Rm(X,Y,C,eₘ)Rm(A,B,eₘ,w)]`,

a polynomial in the components of the `(0,4)` tensor. Every term is the same manoeuvre:
evaluate the outer curvature on the inner curvature *section* by `curvatureTensorAt_apply_field`
(which needs that section `C²`, whence `contMDiff_curvature_two` and `C⁴` fields), then expand
the inner value in the basis and pull the sum out of the slot it occupies.

**No vector sum is ever rewritten.** `b.sum_repr'` produces one, and the linear functional of
the relevant slot is pushed through it by `sum_smul_of_additive`, stated over a bare module
and applied with `exact` --- the documented remedy for `Finset.sum` over a `TangentSpace`.
-/
import RicciFlowBlueprint.CurvatureOperator
import RicciFlowBlueprint.BianchiDeriv

open Bundle Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

/-- A real-valued additive, homogeneous function commutes with a finite linear combination. -/
theorem sum_smul_of_additive {W : Type*} [AddCommGroup W] [Module ℝ W] {κ : Type*}
    [Fintype κ] (f : W → ℝ) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hsmul : ∀ (r : ℝ) a, f (r • a) = r * f a) (c : κ → ℝ) (e : κ → W) :
    f (∑ m, c m • e m) = ∑ m, c m * f (e m) := by
  let L : W →ₗ[ℝ] ℝ :=
    { toFun := f, map_add' := hadd, map_smul' := fun r a ↦ by simp [hsmul] }
  have hL : f (∑ m, c m • e m) = L (∑ m, c m • e m) := rfl
  rw [hL, map_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by simp [L]

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

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
  {x : M} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))

set_option maxSynthPendingDepth 3

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ω M] [T2Space M]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- The basis expansion of a tangent vector, with coefficients written as pairings. -/
theorem sum_inner_smul_eq (z : TangentSpace I x) : ∑ m, (⟪b m, z⟫ : ℝ) • b m = z :=
  b.sum_repr' z

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **Slot one, expanded**: `Rm(z, v, w, u) = ∑ₘ ⟪eₘ, z⟫ Rm(eₘ, v, w, u)`. -/
theorem curvatureTensorAt_expand_fst (z v w u : TangentSpace I x) :
    cov.curvatureTensorAt z v w u = ∑ m, (⟪b m, z⟫ : ℝ) * cov.curvatureTensorAt (b m) v w u := by
  conv_lhs => rw [← sum_inner_smul_eq b z]
  exact sum_smul_of_additive (fun z ↦ cov.curvatureTensorAt z v w u)
    (fun p q ↦ cov.curvatureTensorAt_add_fst p q v w u)
    (fun r p ↦ cov.curvatureTensorAt_smul_fst p v w u r) _ _

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- **Slot two, expanded.** -/
theorem curvatureTensorAt_expand_snd (a z w u : TangentSpace I x) :
    cov.curvatureTensorAt a z w u = ∑ m, (⟪b m, z⟫ : ℝ) * cov.curvatureTensorAt a (b m) w u := by
  conv_lhs => rw [← sum_inner_smul_eq b z]
  exact sum_smul_of_additive (fun z ↦ cov.curvatureTensorAt a z w u)
    (fun p q ↦ cov.curvatureTensorAt_add_snd p q a w u)
    (fun r p ↦ cov.curvatureTensorAt_smul_snd p a w u r) _ _

omit [CompleteSpace E] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **Slot three, expanded.** -/
theorem curvatureTensorAt_expand_thd (a c z u : TangentSpace I x) :
    cov.curvatureTensorAt a c z u = ∑ m, (⟪b m, z⟫ : ℝ) * cov.curvatureTensorAt a c (b m) u := by
  conv_lhs => rw [← sum_inner_smul_eq b z]
  exact sum_smul_of_additive (fun z ↦ cov.curvatureTensorAt a c z u)
    (fun p q ↦ cov.curvatureTensorAt_add_thd p q a c u)
    (fun r p ↦ cov.curvatureTensorAt_smul_thd p a c u r) _ _

variable [ContMDiffCovariantDerivative cov 2] [ContMDiffCovariantDerivative cov 3]

-- BENCH: curvature-commutator-pointwise
/-- **The curvature commutator at a point, in an orthonormal basis.** A polynomial in the
components of the `(0,4)` tensor: the outer curvature is evaluated on the inner curvature
*section* (which is `C²` because the fields are `C⁴`), and the inner value is expanded in the
basis in whichever slot it occupies. -/
theorem inner_curvatureCommutator_eq_sum {X Y A B C : Π y : M, TangentSpace I y}
    (hX : CMDiff 4 (T% X)) (hY : CMDiff 4 (T% Y)) (hA : CMDiff 4 (T% A))
    (hB : CMDiff 4 (T% B)) (hC : CMDiff 4 (T% C)) (w : TangentSpace I x) :
    (⟪cov.curvatureCommutator X Y A B C x, w⟫ : ℝ) =
      ∑ m, (cov.curvatureTensorAt (X x) (Y x) (b m) w
              * cov.curvatureTensorAt (A x) (B x) (C x) (b m)
        - cov.curvatureTensorAt (X x) (Y x) (A x) (b m)
              * cov.curvatureTensorAt (b m) (B x) (C x) w
        - cov.curvatureTensorAt (X x) (Y x) (B x) (b m)
              * cov.curvatureTensorAt (A x) (b m) (C x) w
        - cov.curvatureTensorAt (X x) (Y x) (C x) (b m)
              * cov.curvatureTensorAt (A x) (B x) (b m) w) := by
  have h2 : ∀ {Z : Π y : M, TangentSpace I y}, CMDiff 4 (T% Z) → CMDiff 2 (T% Z) :=
    fun h ↦ h.of_le (by norm_num)
  have h3 : ∀ {Z : Π y : M, TangentSpace I y}, CMDiff 4 (T% Z) → CMDiff 3 (T% Z) :=
    fun h ↦ h.of_le (by norm_num)
  have hW₁ : CMDiff 2 (T% (fun y ↦ cov.curvature A B C y)) :=
    cov.contMDiff_curvature_two (h3 hA) (h3 hB) hC
  have hW₂ : CMDiff 2 (T% (fun y ↦ cov.curvature X Y A y)) :=
    cov.contMDiff_curvature_two (h3 hX) (h3 hY) hA
  have hW₃ : CMDiff 2 (T% (fun y ↦ cov.curvature X Y B y)) :=
    cov.contMDiff_curvature_two (h3 hX) (h3 hY) hB
  have hW₄ : CMDiff 2 (T% (fun y ↦ cov.curvature X Y C y)) :=
    cov.contMDiff_curvature_two (h3 hX) (h3 hY) hC
  -- the inner values, as components
  have hin : ∀ {P Q R : Π y : M, TangentSpace I y}, CMDiff 2 (T% P) → CMDiff 2 (T% Q) →
      CMDiff 2 (T% R) → ∀ m, (⟪b m, cov.curvature P Q R x⟫ : ℝ)
        = cov.curvatureTensorAt (P x) (Q x) (R x) (b m) := fun hP hQ hR m ↦ by
    rw [real_inner_comm, cov.curvatureTensorAt_apply_field hP hQ hR]
  have t1 : (⟪cov.curvature X Y (fun y ↦ cov.curvature A B C y) x, w⟫ : ℝ)
      = ∑ m, cov.curvatureTensorAt (X x) (Y x) (b m) w
          * cov.curvatureTensorAt (A x) (B x) (C x) (b m) := by
    rw [← cov.curvatureTensorAt_apply_field (h2 hX) (h2 hY) hW₁ w,
      cov.curvatureTensorAt_expand_thd b]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [hin (h2 hA) (h2 hB) (h2 hC) m, mul_comm]
  have t2 : (⟪cov.curvature (fun y ↦ cov.curvature X Y A y) B C x, w⟫ : ℝ)
      = ∑ m, cov.curvatureTensorAt (X x) (Y x) (A x) (b m)
          * cov.curvatureTensorAt (b m) (B x) (C x) w := by
    rw [← cov.curvatureTensorAt_apply_field hW₂ (h2 hB) (h2 hC) w,
      cov.curvatureTensorAt_expand_fst b]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [hin (h2 hX) (h2 hY) (h2 hA) m]
  have t3 : (⟪cov.curvature A (fun y ↦ cov.curvature X Y B y) C x, w⟫ : ℝ)
      = ∑ m, cov.curvatureTensorAt (X x) (Y x) (B x) (b m)
          * cov.curvatureTensorAt (A x) (b m) (C x) w := by
    rw [← cov.curvatureTensorAt_apply_field (h2 hA) hW₃ (h2 hC) w,
      cov.curvatureTensorAt_expand_snd b]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [hin (h2 hX) (h2 hY) (h2 hB) m]
  have t4 : (⟪cov.curvature A B (fun y ↦ cov.curvature X Y C y) x, w⟫ : ℝ)
      = ∑ m, cov.curvatureTensorAt (X x) (Y x) (C x) (b m)
          * cov.curvatureTensorAt (A x) (B x) (b m) w := by
    rw [← cov.curvatureTensorAt_apply_field (h2 hA) (h2 hB) hW₄ w,
      cov.curvatureTensorAt_expand_thd b]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [hin (h2 hX) (h2 hY) (h2 hC) m]
  unfold curvatureCommutator
  rw [inner_sub_left, inner_sub_left, inner_sub_left, t1, t2, t3, t4,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

end CovariantDerivative
