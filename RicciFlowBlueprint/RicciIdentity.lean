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
import RicciFlowBlueprint.CurvatureLaplacian
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


/-! ### The same, one level up: `∇²Rm`

`Rm` has three input slots and a vector output, so commuting the derivatives of `∇²Rm` costs
four curvature terms — one per input slot, and one for the output, the last being the only
place a section's Hessian differs from a function's.

The structure of the proof is identical to the bilinear case: expand `∇²Rm` against the
Hessian of the *section* `Rm(A,B)C`, then antisymmetrise.
-/

section Curvature

variable [ContMDiffCovariantDerivative cov 2]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ContMDiffCovariantDerivative cov 1]
  [ContMDiffCovariantDerivative cov 2] in
-- BENCH: cov2-curvature-expand
/-- **`∇²Rm` expanded against the Hessian of the section `Rm(A,B)C`.** Exactly as for a bilinear
form: every term other than the leading Hessian is either `∇Rm` in one slot, or `Rm` with a
second derivative of one of the fields in one slot; and the first derivative of the section
cancels between the leading term and the `∇_{∇_X Y}` correction.

The four hypotheses are the differentiability of the four sections that `∇Rm` is built from —
exactly what `contMDiff_covCurvature` establishes when the fields are regular enough. -/
theorem cov2Curvature_eq_hessian {X Y A B C : Π y : M, TangentSpace I y} {x : M}
    (ha : MDiffAt (T% (fun u ↦ cov (fun y ↦ cov.curvature A B C y) u (Y u))) x)
    (hb : MDiffAt (T% (fun u ↦ cov.curvature (fun z ↦ cov A z (Y z)) B C u)) x)
    (hc : MDiffAt (T% (fun u ↦ cov.curvature A (fun z ↦ cov B z (Y z)) C u)) x)
    (hd : MDiffAt (T% (fun u ↦ cov.curvature A B (fun z ↦ cov C z (Y z)) u)) x) :
    cov.cov2Curvature X Y A B C x
      = cov.hessian X Y (fun y ↦ cov.curvature A B C y) x
        + cov.curvature (fun z ↦ cov A z (cov Y z (X z))) B C x
        + cov.curvature A (fun z ↦ cov B z (cov Y z (X z))) C x
        + cov.curvature A B (fun z ↦ cov C z (cov Y z (X z))) x
        - cov.covCurvature X (fun z ↦ cov A z (Y z)) B C x
        - cov.curvature (fun z ↦ cov (fun w ↦ cov A w (Y w)) z (X z)) B C x
        - cov.curvature (fun z ↦ cov A z (Y z)) (fun z ↦ cov B z (X z)) C x
        - cov.curvature (fun z ↦ cov A z (Y z)) B (fun z ↦ cov C z (X z)) x
        - cov.covCurvature X A (fun z ↦ cov B z (Y z)) C x
        - cov.curvature (fun z ↦ cov A z (X z)) (fun z ↦ cov B z (Y z)) C x
        - cov.curvature A (fun z ↦ cov (fun w ↦ cov B w (Y w)) z (X z)) C x
        - cov.curvature A (fun z ↦ cov B z (Y z)) (fun z ↦ cov C z (X z)) x
        - cov.covCurvature X A B (fun z ↦ cov C z (Y z)) x
        - cov.curvature (fun z ↦ cov A z (X z)) B (fun z ↦ cov C z (Y z)) x
        - cov.curvature A (fun z ↦ cov B z (X z)) (fun z ↦ cov C z (Y z)) x
        - cov.curvature A B (fun z ↦ cov (fun w ↦ cov C w (Y w)) z (X z)) x
        - cov.covCurvature Y (fun z ↦ cov A z (X z)) B C x
        - cov.covCurvature Y A (fun z ↦ cov B z (X z)) C x
        - cov.covCurvature Y A B (fun z ↦ cov C z (X z)) x := by
  have hsplit : cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
      = cov (fun u ↦ cov (fun y ↦ cov.curvature A B C y) u (Y u)) x (X x)
        - cov (fun u ↦ cov.curvature (fun z ↦ cov A z (Y z)) B C u) x (X x)
        - cov (fun u ↦ cov.curvature A (fun z ↦ cov B z (Y z)) C u) x (X x)
        - cov (fun u ↦ cov.curvature A B (fun z ↦ cov C z (Y z)) u) x (X x) := by
    have hfun : (fun u ↦ cov.covCurvature Y A B C u)
        = ((((fun u ↦ cov (fun y ↦ cov.curvature A B C y) u (Y u))
            - (fun u ↦ cov.curvature (fun z ↦ cov A z (Y z)) B C u))
            - (fun u ↦ cov.curvature A (fun z ↦ cov B z (Y z)) C u))
            - (fun u ↦ cov.curvature A B (fun z ↦ cov C z (Y z)) u)) := rfl
    have hab := mdifferentiableAt_sub_section ha hb
    have habc := mdifferentiableAt_sub_section hab hc
    rw [hfun, cov.sub_apply habc hd, cov.sub_apply hab hc, cov.sub_apply ha hb]
    rfl
  rw [cov2Curvature, hsplit]
  simp only [hessian, covCurvature]
  abel

omit [ContMDiffCovariantDerivative cov 2] in
/-- **The four second-derivative terms in `Rm`'s first slot combine into the curvature.**
`∇_{∇_X Y}A − ∇_X∇_Y A − ∇_{∇_Y X}A + ∇_Y∇_X A` is `−R(X,Y)A` at `x` — torsion-freeness turning
`∇_X Y − ∇_Y X` into `[X,Y]` — and `Rm(·,B)C` is additive and pointwise in that slot, so the
four terms collapse.

Note the route: additivity (`curvature_add_left`) plus pointwiseness
(`TensorialAt.pointwise`), *not* the continuous linear map `TensorialAt.mkHom` produces.
Rewriting with `mkHom_apply` here sends the unifier through the trivialisations behind
`FiberBundle.extend` and does not return — the same `whnf` timeout `OneForm.lean` documents. -/
theorem curvature_fst_second_deriv_comm (hcov : cov.torsion = 0)
    {X Y A B C : Π y : M, TangentSpace I y} {x : M} (hC2 : CMDiff 2 (T% C))
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP₁ : MDiffAt (T% (fun z ↦ cov A z (cov Y z (X z)))) x)
    (hP₂ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov A w (Y w)) z (X z))) x)
    (hP₃ : MDiffAt (T% (fun z ↦ cov A z (cov X z (Y z)))) x)
    (hP₄ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov A w (X w)) z (Y z))) x)
    (hR : MDiffAt (T% (fun y ↦ cov.curvature X Y A y)) x) :
    cov.curvature (fun z ↦ cov A z (cov Y z (X z))) B C x
        - cov.curvature (fun z ↦ cov (fun w ↦ cov A w (Y w)) z (X z)) B C x
        - cov.curvature (fun z ↦ cov A z (cov X z (Y z))) B C x
        + cov.curvature (fun z ↦ cov (fun w ↦ cov A w (X w)) z (Y z)) B C x
      = -cov.curvature (fun y ↦ cov.curvature X Y A y) B C x := by
  have htor : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    (torsion_eq_zero_iff cov).mp hcov hX hY
  have hkey : cov A x (cov Y x (X x)) - cov A x (cov X x (Y x))
      = cov A x (mlieBracket I X Y x) := by rw [← map_sub, htor]
  have h₁₄ := mdifferentiableAt_add_section hP₁ hP₄
  have h₁₄R := mdifferentiableAt_add_section h₁₄ hR
  have h₂₃ := mdifferentiableAt_add_section hP₂ hP₃
  have hL := cov.tensorialAt_curvature_fst (V := B) (Z := C) hC2 x
  have hval : ((fun z ↦ cov A z (cov Y z (X z)))
      + (fun z ↦ cov (fun w ↦ cov A w (X w)) z (Y z))
      + (fun y ↦ cov.curvature X Y A y)) x
      = ((fun z ↦ cov (fun w ↦ cov A w (Y w)) z (X z))
        + (fun z ↦ cov A z (cov X z (Y z)))) x := by
    show cov A x (cov Y x (X x)) + cov (fun w ↦ cov A w (X w)) x (Y x)
        + cov.curvature X Y A x
      = cov (fun w ↦ cov A w (Y w)) x (X x) + cov A x (cov X x (Y x))
    rw [curvature, ← hkey]
    abel
  have key := hL.pointwise h₁₄R h₂₃ hval
  rw [cov.curvature_add_left hC2 h₁₄ hR, cov.curvature_add_left hC2 hP₁ hP₄,
    cov.curvature_add_left hC2 hP₂ hP₃] at key
  linear_combination (norm := module) key

omit [ContMDiffCovariantDerivative cov 2] in
/-- **The same in `Rm`'s second slot**, by the middle-slot tensoriality that antisymmetry
supplies. -/
theorem curvature_snd_second_deriv_comm (hcov : cov.torsion = 0)
    {X Y A B C : Π y : M, TangentSpace I y} {x : M} (hC2 : CMDiff 2 (T% C))
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP₁ : MDiffAt (T% (fun z ↦ cov B z (cov Y z (X z)))) x)
    (hP₂ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov B w (Y w)) z (X z))) x)
    (hP₃ : MDiffAt (T% (fun z ↦ cov B z (cov X z (Y z)))) x)
    (hP₄ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov B w (X w)) z (Y z))) x)
    (hR : MDiffAt (T% (fun y ↦ cov.curvature X Y B y)) x) :
    cov.curvature A (fun z ↦ cov B z (cov Y z (X z))) C x
        - cov.curvature A (fun z ↦ cov (fun w ↦ cov B w (Y w)) z (X z)) C x
        - cov.curvature A (fun z ↦ cov B z (cov X z (Y z))) C x
        + cov.curvature A (fun z ↦ cov (fun w ↦ cov B w (X w)) z (Y z)) C x
      = -cov.curvature A (fun y ↦ cov.curvature X Y B y) C x := by
  have htor : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    (torsion_eq_zero_iff cov).mp hcov hX hY
  have hkey : cov B x (cov Y x (X x)) - cov B x (cov X x (Y x))
      = cov B x (mlieBracket I X Y x) := by rw [← map_sub, htor]
  have h₁₄ := mdifferentiableAt_add_section hP₁ hP₄
  have h₁₄R := mdifferentiableAt_add_section h₁₄ hR
  have h₂₃ := mdifferentiableAt_add_section hP₂ hP₃
  have hL := cov.tensorialAt_curvature_snd (V := A) (Z := C) hC2 x
  have hval : ((fun z ↦ cov B z (cov Y z (X z)))
      + (fun z ↦ cov (fun w ↦ cov B w (X w)) z (Y z))
      + (fun y ↦ cov.curvature X Y B y)) x
      = ((fun z ↦ cov (fun w ↦ cov B w (Y w)) z (X z))
        + (fun z ↦ cov B z (cov X z (Y z)))) x := by
    show cov B x (cov Y x (X x)) + cov (fun w ↦ cov B w (X w)) x (Y x)
        + cov.curvature X Y B x
      = cov (fun w ↦ cov B w (Y w)) x (X x) + cov B x (cov X x (Y x))
    rw [curvature, ← hkey]
    abel
  have key := hL.pointwise h₁₄R h₂₃ hval
  rw [cov.curvature_add_middle hC2 h₁₄ hR, cov.curvature_add_middle hC2 hP₁ hP₄,
    cov.curvature_add_middle hC2 hP₂ hP₃] at key
  linear_combination (norm := module) key

section Third

variable [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]

omit [ContMDiffCovariantDerivative cov 2] in
/-- **The same in `Rm`'s third slot.** This one is the expensive slot, as everywhere in the
tower: `curvature_add_right` and `curvature_congr_third` want their sections globally `C²`,
where the first two slots need only differentiability at the point. That is why `RicciSymm.lean`
had to build `curvatureEndoAt` by hand rather than off a `TensorialAt`. -/
theorem curvature_thd_second_deriv_comm (hcov : cov.torsion = 0)
    {X Y A B C : Π y : M, TangentSpace I y} {x : M}
    (hA2 : CMDiffAt 2 (T% A) x) (hB2 : CMDiffAt 2 (T% B) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP₁ : CMDiff 2 (T% (fun z ↦ cov C z (cov Y z (X z)))))
    (hP₂ : CMDiff 2 (T% (fun z ↦ cov (fun w ↦ cov C w (Y w)) z (X z))))
    (hP₃ : CMDiff 2 (T% (fun z ↦ cov C z (cov X z (Y z)))))
    (hP₄ : CMDiff 2 (T% (fun z ↦ cov (fun w ↦ cov C w (X w)) z (Y z))))
    (hR : CMDiff 2 (T% (fun y ↦ cov.curvature X Y C y))) :
    cov.curvature A B (fun z ↦ cov C z (cov Y z (X z))) x
        - cov.curvature A B (fun z ↦ cov (fun w ↦ cov C w (Y w)) z (X z)) x
        - cov.curvature A B (fun z ↦ cov C z (cov X z (Y z))) x
        + cov.curvature A B (fun z ↦ cov (fun w ↦ cov C w (X w)) z (Y z)) x
      = -cov.curvature A B (fun y ↦ cov.curvature X Y C y) x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hA : MDiffAt (T% A) x := hA2.mdifferentiableAt h2
  have hB : MDiffAt (T% B) x := hB2.mdifferentiableAt h2
  have htor : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    (torsion_eq_zero_iff cov).mp hcov hX hY
  have hkey : cov C x (cov Y x (X x)) - cov C x (cov X x (Y x))
      = cov C x (mlieBracket I X Y x) := by rw [← map_sub, htor]
  have h₁₄ := hP₁.add_section hP₄
  have h₁₄R := h₁₄.add_section hR
  have h₂₃ := hP₂.add_section hP₃
  have hval : ((fun z ↦ cov C z (cov Y z (X z)))
      + (fun z ↦ cov (fun w ↦ cov C w (X w)) z (Y z))
      + (fun y ↦ cov.curvature X Y C y)) x
      = ((fun z ↦ cov (fun w ↦ cov C w (Y w)) z (X z))
        + (fun z ↦ cov C z (cov X z (Y z)))) x := by
    show cov C x (cov Y x (X x)) + cov (fun w ↦ cov C w (X w)) x (Y x)
        + cov.curvature X Y C x
      = cov (fun w ↦ cov C w (Y w)) x (X x) + cov C x (cov X x (Y x))
    rw [curvature, ← hkey]
    abel
  have key := cov.curvature_congr_third hA2 hB2 h₁₄R h₂₃ hval
  rw [cov.curvature_add_right h₁₄ hR hA hB, cov.curvature_add_right hP₁ hP₄ hA hB,
    cov.curvature_add_right hP₂ hP₃ hA hB] at key
  linear_combination (norm := module) key

omit [ContMDiffCovariantDerivative cov 2] in
-- BENCH: curvature-ricci-identity
/-- **The Ricci identity for the curvature tensor.** Commuting the two derivatives of `∇²Rm`
costs one curvature term per slot of `Rm` — three for the inputs, and one for the vector
output:

`(∇²_{X,Y}Rm)(A,B)C − (∇²_{Y,X}Rm)(A,B)C
   = R(X,Y)(Rm(A,B)C) − Rm(R(X,Y)A,B)C − Rm(A,R(X,Y)B)C − Rm(A,B)(R(X,Y)C)`.

Everything is `cov2Curvature_eq_hessian` twice plus four facts. The output term is
`hessian_sub_hessian_swap` — the Ricci identity for sections, which is where a section's
Hessian differs from a function's and so where the bilinear case had nothing. The three input
terms are the slot lemmas above. Every remaining term of the two expansions cancels in pairs:
the `∇Rm` terms because each appears in both orders, and the cross terms
`Rm(∇_Y A, ∇_X B)C` because swapping `X` and `Y` maps the pair to itself. -/
theorem cov2Curvature_sub_swap (hcov : cov.torsion = 0)
    {X Y A B C : Π y : M, TangentSpace I y} {x : M}
    (hC2 : CMDiff 2 (T% C)) (hA2 : CMDiffAt 2 (T% A) x) (hB2 : CMDiffAt 2 (T% B) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    -- the expansion, in the order `(X, Y)`
    (ha : MDiffAt (T% (fun u ↦ cov (fun y ↦ cov.curvature A B C y) u (Y u))) x)
    (hb : MDiffAt (T% (fun u ↦ cov.curvature (fun z ↦ cov A z (Y z)) B C u)) x)
    (hc : MDiffAt (T% (fun u ↦ cov.curvature A (fun z ↦ cov B z (Y z)) C u)) x)
    (hd : MDiffAt (T% (fun u ↦ cov.curvature A B (fun z ↦ cov C z (Y z)) u)) x)
    -- and in the order `(Y, X)`
    (ha' : MDiffAt (T% (fun u ↦ cov (fun y ↦ cov.curvature A B C y) u (X u))) x)
    (hb' : MDiffAt (T% (fun u ↦ cov.curvature (fun z ↦ cov A z (X z)) B C u)) x)
    (hc' : MDiffAt (T% (fun u ↦ cov.curvature A (fun z ↦ cov B z (X z)) C u)) x)
    (hd' : MDiffAt (T% (fun u ↦ cov.curvature A B (fun z ↦ cov C z (X z)) u)) x)
    -- the second derivatives of `A`, and `R(X,Y)A`
    (hA₁ : MDiffAt (T% (fun z ↦ cov A z (cov Y z (X z)))) x)
    (hA₂ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov A w (Y w)) z (X z))) x)
    (hA₃ : MDiffAt (T% (fun z ↦ cov A z (cov X z (Y z)))) x)
    (hA₄ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov A w (X w)) z (Y z))) x)
    (hRA : MDiffAt (T% (fun y ↦ cov.curvature X Y A y)) x)
    -- of `B`
    (hB₁ : MDiffAt (T% (fun z ↦ cov B z (cov Y z (X z)))) x)
    (hB₂ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov B w (Y w)) z (X z))) x)
    (hB₃ : MDiffAt (T% (fun z ↦ cov B z (cov X z (Y z)))) x)
    (hB₄ : MDiffAt (T% (fun z ↦ cov (fun w ↦ cov B w (X w)) z (Y z))) x)
    (hRB : MDiffAt (T% (fun y ↦ cov.curvature X Y B y)) x)
    -- and of `C`, where the third slot asks for global `C²`
    (hC₁ : CMDiff 2 (T% (fun z ↦ cov C z (cov Y z (X z)))))
    (hC₂ : CMDiff 2 (T% (fun z ↦ cov (fun w ↦ cov C w (Y w)) z (X z))))
    (hC₃ : CMDiff 2 (T% (fun z ↦ cov C z (cov X z (Y z)))))
    (hC₄ : CMDiff 2 (T% (fun z ↦ cov (fun w ↦ cov C w (X w)) z (Y z))))
    (hRC : CMDiff 2 (T% (fun y ↦ cov.curvature X Y C y))) :
    cov.cov2Curvature X Y A B C x - cov.cov2Curvature Y X A B C x
      = cov.curvature X Y (fun y ↦ cov.curvature A B C y) x
        - cov.curvature (fun y ↦ cov.curvature X Y A y) B C x
        - cov.curvature A (fun y ↦ cov.curvature X Y B y) C x
        - cov.curvature A B (fun y ↦ cov.curvature X Y C y) x := by
  rw [cov.cov2Curvature_eq_hessian ha hb hc hd, cov.cov2Curvature_eq_hessian ha' hb' hc' hd']
  have hh := cov.hessian_sub_hessian_swap hcov (Z := fun y ↦ cov.curvature A B C y) hX hY
  have kA := cov.curvature_fst_second_deriv_comm (B := B) hcov hC2 hX hY hA₁ hA₂ hA₃ hA₄ hRA
  have kB := cov.curvature_snd_second_deriv_comm (A := A) hcov hC2 hX hY hB₁ hB₂ hB₃ hB₄ hRB
  have kC := cov.curvature_thd_second_deriv_comm hcov hA2 hB2 hX hY hC₁ hC₂ hC₃ hC₄ hRC
  linear_combination (norm := module) hh + kA + kB + kC

end Third

end Curvature

end CovariantDerivative
