/-
The Ricci identity for a bilinear form field.

`Hessian.lean` has the Ricci identity for *sections*, `∇²_{X,Y}Z − ∇²_{Y,X}Z = R(X,Y)Z`, and
`hessianFun_symm` says a *function* has a symmetric Hessian — no curvature term, a function
having no slots for it to act on. A bilinear form has two slots, so it picks up one term per
slot:

  `(∇²_{W,X}h)(Y,Z) − (∇²_{X,W}h)(Y,Z) = −h(R(W,X)Y, Z) − h(Y, R(W,X)Z)`.

This is the commutation rule the curvature evolution equation needs: with `h = −2Ric`, turning
`∇²Ric` into `Δ Rm` plus quadratic curvature terms is exactly a matter of moving derivatives
past each other.

The whole content is the expansion `cov2Bilin_eq_hessianFun`: `∇²h` is the Hessian of the
*scalar* `h(Y,Z)` plus terms that are either `∇h` in a slot, or `h` applied to second
derivatives of the fields. Antisymmetrising kills the Hessian (it is symmetric), cancels the
cross terms, and leaves exactly the curvature.
-/
import RicciFlowBlueprint.BilinLaplacian
import RicciFlowBlueprint.Bianchi
import RicciFlowBlueprint.Hessian

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

variable [ContMDiffCovariantDerivative cov 1] {h : M → E →L[ℝ] E →L[ℝ] ℝ} {x : M}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
-- BENCH: bilin-ricci-expand
/-- **`∇²h` expanded against the Hessian of the scalar `h(Y,Z)`.** Every term other than the
leading Hessian is either `∇h` in one slot, or `h` applied to a second derivative of one of the
fields; the first derivative of the scalar cancels between the leading term and the
`∇_{∇_W X}` correction. -/
theorem cov2Bilin_eq_hessianFun (hb : IsMDiffBilinAt (I := I) h x)
    {W X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff 1 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hcb : MDiffAt (fun y ↦ cov.covBilin h X Y Z y) x) :
    cov.cov2Bilin h W X Y Z x
      = cov.hessianFun (fun y ↦ h y (Y y) (Z y)) W X x
        + h x (cov Y x (cov X x (W x))) (Z x)
        + h x (Y x) (cov Z x (cov X x (W x)))
        - cov.covBilin h W (fun y ↦ cov Y y (X y)) Z x
        - h x (cov (fun y ↦ cov Y y (X y)) x (W x)) (Z x)
        - h x (cov Y x (X x)) (cov Z x (W x))
        - cov.covBilin h W Y (fun y ↦ cov Z y (X y)) x
        - h x (cov Y x (W x)) (cov Z x (X x))
        - h x (Y x) (cov (fun y ↦ cov Z y (X y)) x (W x))
        - cov.covBilin h X (fun y ↦ cov Y y (W y)) Z x
        - cov.covBilin h X Y (fun y ↦ cov Z y (W y)) x := by
  have hne : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h21 : ((1 : ℕ∞ω) + 1) = 2 := by norm_num
  have hY1 : CMDiff 1 (T% Y) := hY.of_le (by norm_num)
  have hZ1 : CMDiff 1 (T% Z) := hZ.of_le (by norm_num)
  have hDY : CMDiff 1 (T% (fun y ↦ cov Y y (X y))) :=
    cov.contMDiff_cov_apply (by rw [h21]; exact hY) hX
  have hDZ : CMDiff 1 (T% (fun y ↦ cov Z y (X y))) :=
    cov.contMDiff_cov_apply (by rw [h21]; exact hZ) hX
  have hA : MDiffAt (fun y ↦ h y (cov Y y (X y)) (Z y)) x :=
    hb _ _ (hDY.mdifferentiable hne x) (hZ1.mdifferentiable hne x)
  have hB : MDiffAt (fun y ↦ h y (Y y) (cov Z y (X y))) x :=
    hb _ _ (hY1.mdifferentiable hne x) (hDZ.mdifferentiable hne x)
  have hfirst : MDiffAt (fun y ↦ mvfderiv I (fun z ↦ h z (Y z) (Z z)) y (X y)) x := by
    have hrw : (fun y ↦ mvfderiv I (fun z ↦ h z (Y z) (Z z)) y (X y))
        = fun y ↦ (cov.covBilin h X Y Z y + h y (cov Y y (X y)) (Z y))
          + h y (Y y) (cov Z y (X y)) := by
      funext y; simp only [covBilin]; ring
    rw [hrw]
    have hadd : MDiffAt (fun y ↦ cov.covBilin h X Y Z y + h y (cov Y y (X y)) (Z y)) x :=
      hcb.add hA
    exact hadd.add hB
  have hsub1 : MDiffAt (fun y ↦ mvfderiv I (fun z ↦ h z (Y z) (Z z)) y (X y)
      - h y (cov Y y (X y)) (Z y)) x := hfirst.sub hA
  have hsub : mvfderiv I (fun y ↦ cov.covBilin h X Y Z y) x (W x)
      = mvfderiv I (fun y ↦ mvfderiv I (fun z ↦ h z (Y z) (Z z)) y (X y)) x (W x)
        - mvfderiv I (fun y ↦ h y (cov Y y (X y)) (Z y)) x (W x)
        - mvfderiv I (fun y ↦ h y (Y y) (cov Z y (X y))) x (W x) := by
    have hfun : (fun y ↦ cov.covBilin h X Y Z y)
        = fun y ↦ (mvfderiv I (fun z ↦ h z (Y z) (Z z)) y (X y)
          - h y (cov Y y (X y)) (Z y)) - h y (Y y) (cov Z y (X y)) := rfl
    rw [hfun, mvfderiv_fun_sub hsub1 hB, mvfderiv_fun_sub hfirst hA]
    rfl
  rw [cov2Bilin, hsub]
  simp only [covBilin, hessianFun]
  ring

-- BENCH: bilin-ricci
/-- **The Ricci identity for a bilinear form field.** Commuting the two derivatives of `∇²h`
costs one curvature term per slot of `h`:

`(∇²_{W,X}h)(Y,Z) − (∇²_{X,W}h)(Y,Z) = −h(R(W,X)Y, Z) − h(Y, R(W,X)Z)`.

Everything is already in `cov2Bilin_eq_hessianFun`. Antisymmetrising, the leading Hessian of the
scalar `h(Y,Z)` cancels because a *function* has a symmetric Hessian (`hessianFun_symm`, which
is where torsion-freeness is used the first time); the `∇h` terms and the cross terms
`h(∇_X Y, ∇_W Z)` cancel outright; and what is left is
`h(∇_{[W,X]}Y − ∇_W∇_X Y + ∇_X∇_W Y, Z)`, which is `−h(R(W,X)Y, Z)` by the definition of the
curvature — torsion-freeness used the second time, to turn `∇_W X − ∇_X W` into `[W,X]`. -/
theorem cov2Bilin_sub_swap (hcov : cov.torsion = 0) (hb : IsMDiffBilinAt (I := I) h x)
    {W X Y Z : Π y : M, TangentSpace I y}
    (hW : CMDiff 1 (T% W)) (hX : CMDiff 1 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hf2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ h y (Y y) (Z y)) x)
    (hcb₁ : MDiffAt (fun y ↦ cov.covBilin h X Y Z y) x)
    (hcb₂ : MDiffAt (fun y ↦ cov.covBilin h W Y Z y) x) :
    cov.cov2Bilin h W X Y Z x - cov.cov2Bilin h X W Y Z x
      = -h x (cov.curvature W X Y x) (Z x) - h x (Y x) (cov.curvature W X Z x) := by
  have hne : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hWd : MDiffAt (T% W) x := hW.mdifferentiable hne x
  have hXd : MDiffAt (T% X) x := hX.mdifferentiable hne x
  -- torsion-freeness, in the two places it is used
  have htor : cov X x (W x) - cov W x (X x) = mlieBracket I W X x :=
    (torsion_eq_zero_iff cov).mp hcov hWd hXd
  have hkey : ∀ σ : Π y : M, TangentSpace I y,
      cov σ x (cov X x (W x)) - cov σ x (cov W x (X x)) = cov σ x (mlieBracket I W X x) := by
    intro σ
    rw [← map_sub, htor]
  -- `h x` is linear in each slot
  have hh1 : ∀ a b c : E, h x (a - b) c = h x a c - h x b c := fun a b c ↦ by
    rw [map_sub]; rfl
  have hh2 : ∀ a b c : E, h x a (b - c) = h x a b - h x a c := fun a b c ↦ map_sub _ _ _
  -- the curvature, distributed through `h`; the three-term forms are stated at the model type,
  -- because a `TangentSpace`-typed `-` will not match an `E`-typed `map_sub`
  have hh1' : ∀ a b c d : E, h x (a - b - c) d = h x a d - h x b d - h x c d := by
    intro a b c d; rw [hh1, hh1]
  have hh2' : ∀ a b c d : E, h x a (b - c - d) = h x a b - h x a c - h x a d := by
    intro a b c d; rw [hh2, hh2]
  have e1 : h x (cov.curvature W X Y x) (Z x)
      = h x (cov (fun y ↦ cov Y y (X y)) x (W x)) (Z x)
        - h x (cov (fun y ↦ cov Y y (W y)) x (X x)) (Z x)
        - h x (cov Y x (mlieBracket I W X x)) (Z x) := by
    rw [curvature]; exact hh1' _ _ _ _
  have e2 : h x (Y x) (cov.curvature W X Z x)
      = h x (Y x) (cov (fun y ↦ cov Z y (X y)) x (W x))
        - h x (Y x) (cov (fun y ↦ cov Z y (W y)) x (X x))
        - h x (Y x) (cov Z x (mlieBracket I W X x)) := by
    rw [curvature]; exact hh2' _ _ _ _
  -- the two slots, with everything stated at the model type and applied by defeq
  have hsub1 : ∀ a b c d : E, a - b = c → h x a d - h x b d = h x c d := by
    intro a b c d hab; rw [← hh1, hab]
  have hsub2 : ∀ a b c d : E, a - b = c → h x d a - h x d b = h x d c := by
    intro a b c d hab; rw [← hh2, hab]
  have key1 : h x (cov Y x (cov X x (W x))) (Z x) - h x (cov Y x (cov W x (X x))) (Z x)
      = h x (cov Y x (mlieBracket I W X x)) (Z x) := hsub1 _ _ _ _ (hkey Y)
  have key2 : h x (Y x) (cov Z x (cov X x (W x))) - h x (Y x) (cov Z x (cov W x (X x)))
      = h x (Y x) (cov Z x (mlieBracket I W X x)) := hsub2 _ _ _ _ (hkey Z)
  rw [cov.cov2Bilin_eq_hessianFun hb hX hY hZ hcb₁, cov.cov2Bilin_eq_hessianFun hb hW hY hZ hcb₂,
    cov.hessianFun_symm hcov hf2 hWd hXd]
  linarith [e1, e2, key1, key2]


end CovariantDerivative
