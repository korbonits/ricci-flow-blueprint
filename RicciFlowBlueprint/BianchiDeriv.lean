/-
**The differentiated second Bianchi identity.**

The second Bianchi identity is a cyclic identity in the *direction* slot of `∇Rm` and the
first two slots of `Rm`, with `Rm`'s last slot a spectator:

  `(∇_X Rm)(Y,Z)W + (∇_Y Rm)(Z,X)W + (∇_Z Rm)(X,Y)W = 0`.

Differentiating it once more gives the same cyclic identity for `∇²Rm`:

  `(∇²_{X,Y}Rm)(A,B)C + (∇²_{X,A}Rm)(B,Y)C + (∇²_{X,B}Rm)(Y,A)C = 0`,

and this is what the trace step of `∂ₜRm = ΔRm + Q` consumes: summing it over `Y = eᵢ`
with `X = eᵢ` turns `Δ Rm` into two traces of `∇²Rm` with the derivative slots in the
*wrong* order, which the Ricci identity for the curvature tensor then reorders at the cost
of terms quadratic in `Rm`.

**Nothing is differentiated twice by hand.** `∇²Rm` is `∇Rm` differentiated once with one
correction per slot, so the cyclic sum splits into a leading term and four correction
groups, and *every one of the five vanishes by the undifferentiated identity*:

* the leading terms combine, by additivity of `∇` on sections, into `∇` of the section
  `u ↦ (∇_Y Rm)(A,B)C u + (∇_A Rm)(B,Y)C u + (∇_B Rm)(Y,A)C u`, which is the zero section
  by `bianchi_second` at every point, and `∇` of the zero section is zero;
* the four correction groups are the cyclic sum with one field replaced by its derivative
  — `∇_X Y`, `∇_X A`, `∇_X B`, `∇_X C` — so each is `bianchi_second` again.

So the proof is five applications of `bianchi_second` and one `IsCovariantDerivativeOn.zero`.
The regrouping is what carries the content: the corrections do *not* cancel in pairs, they
cancel three at a time, one group per differentiated field.

Regularity is one derivative above `bianchi_second` throughout, and the last slot stays the
expensive one: `C` is asked for four derivatives so that `∇_X C` still has the three that
`bianchi_second` wants of its spectator slot.

**No metric is needed**, exactly as for `bianchi_second` itself: the three Riemannian
instances of the ambient section are `omit`ted. That is worth knowing before the trace
step, which is where a metric first becomes unavoidable.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.RicciIdentity

open Bundle Filter Module VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]
  [ContMDiffCovariantDerivative cov 3]

variable {X Y A B C : Π y : M, TangentSpace I y} {x : M}

omit [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) ↦ TangentSpace I x)] in
-- BENCH: bianchi-second-deriv
/-- **The differentiated second Bianchi identity.**

`(∇²_{X,Y}Rm)(A,B)C + (∇²_{X,A}Rm)(B,Y)C + (∇²_{X,B}Rm)(Y,A)C = 0`, the cyclic identity of
`bianchi_second` one derivative up.

The five terms of `cov2Curvature` split the cyclic sum into a leading part and four
correction groups. The leading parts combine into `∇_X` of the section that
`bianchi_second` says is zero. Each correction group is the cyclic sum with one field
replaced by its covariant derivative, so is `bianchi_second` again — the corrections cancel
three at a time, one group per differentiated field, not in pairs. -/
theorem cov2Curvature_cyclic_eq_zero (hcov : cov.torsion = 0)
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y)) (hA : CMDiff 3 (T% A))
    (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X Y A B C x + cov.cov2Curvature X A B Y C x
      + cov.cov2Curvature X B Y A C x = 0 := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  -- Lower-regularity copies of the hypotheses.
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  -- The covariant derivatives that appear in the corrections, at the levels
  -- `bianchi_second` asks of each slot.
  have hDY : CMDiff 2 (T% (fun u ↦ cov Y u (X u))) := cov.contMDiff_cov_apply hY hX2
  have hDA : CMDiff 2 (T% (fun u ↦ cov A u (X u))) := cov.contMDiff_cov_apply hA hX2
  have hDB : CMDiff 2 (T% (fun u ↦ cov B u (X u))) := cov.contMDiff_cov_apply hB hX2
  have hDC : CMDiff 3 (T% (fun u ↦ cov C u (X u))) := cov.contMDiff_cov_apply hC hX
  -- The three `∇Rm` sections whose cyclic sum vanishes.
  have hs1 : CMDiff 1 (T% (fun u ↦ cov.covCurvature Y A B C u)) :=
    cov.contMDiff_covCurvature hY hA hB hC
  have hs2 : CMDiff 1 (T% (fun u ↦ cov.covCurvature A B Y C u)) :=
    cov.contMDiff_covCurvature hA hB hY hC
  have hs3 : CMDiff 1 (T% (fun u ↦ cov.covCurvature B Y A C u)) :=
    cov.contMDiff_covCurvature hB hY hA hC
  -- The leading terms: `∇_X` of a section that is identically zero.
  have hzero : (fun u ↦ cov.covCurvature Y A B C u + cov.covCurvature A B Y C u
      + cov.covCurvature B Y A C u) = (0 : Π y : M, TangentSpace I y) := by
    funext u
    exact cov.bianchi_second hcov hY2 hA2 hB2 hC3
  have hsum : cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
      + cov (fun u ↦ cov.covCurvature A B Y C u) x (X x)
      + cov (fun u ↦ cov.covCurvature B Y A C u) x (X x) = 0 := by
    -- Additivity of `∇`, stated in applied form: `rw` will not match the Pi-typed `+`
    -- that `IsCovariantDerivativeOn.add` produces against a lambda-typed one.
    have hadd1 : cov (fun u ↦ cov.covCurvature Y A B C u
          + cov.covCurvature A B Y C u) x (X x)
        = cov (fun u ↦ cov.covCurvature Y A B C u) x (X x)
          + cov (fun u ↦ cov.covCurvature A B Y C u) x (X x) :=
      congrArg (fun L ↦ L (X x)) (cov.isCovariantDerivativeOn.add
        ((hs1.mdifferentiable h1) x) ((hs2.mdifferentiable h1) x))
    have hadd2 : cov (fun u ↦ (cov.covCurvature Y A B C u + cov.covCurvature A B Y C u)
          + cov.covCurvature B Y A C u) x (X x)
        = cov (fun u ↦ cov.covCurvature Y A B C u + cov.covCurvature A B Y C u) x (X x)
          + cov (fun u ↦ cov.covCurvature B Y A C u) x (X x) :=
      congrArg (fun L ↦ L (X x)) (cov.isCovariantDerivativeOn.add
        (((hs1.add_section hs2).mdifferentiable h1) x) ((hs3.mdifferentiable h1) x))
    have hval : cov (fun u ↦ (cov.covCurvature Y A B C u + cov.covCurvature A B Y C u)
        + cov.covCurvature B Y A C u) x (X x) = 0 := by
      have hz : cov (0 : Π y : M, TangentSpace I y) x = 0 :=
        cov.isCovariantDerivativeOn.zero
      rw [hzero, hz]
      exact zero_apply _
    rw [← hval, hadd2, hadd1]
  -- The four correction groups, one per differentiated field.
  have kY := cov.bianchi_second hcov (x := x) hDY hA2 hB2 hC3
  have kA := cov.bianchi_second hcov (x := x) hY2 hDA hB2 hC3
  have kB := cov.bianchi_second hcov (x := x) hY2 hA2 hDB hC3
  have kC := cov.bianchi_second hcov (x := x) hY2 hA2 hB2 hDC
  unfold cov2Curvature
  linear_combination (norm := module) hsum - kY - kA - kB - kC

/-- **The commutator defect of the curvature tensor**: the right-hand side of the Ricci
identity for `Rm`, one curvature term per slot — three inputs and the vector output.

This is where the quadratic terms of `∂ₜRm = ΔRm + Q` come from. They are not bolted on at
the end: they are exactly what reordering the two derivative slots of `∇²Rm` costs. -/
noncomputable def curvatureCommutator (X Y A B C : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x :=
  cov.curvature X Y (fun y ↦ cov.curvature A B C y) x
    - cov.curvature (fun y ↦ cov.curvature X Y A y) B C x
    - cov.curvature A (fun y ↦ cov.curvature X Y B y) C x
    - cov.curvature A B (fun y ↦ cov.curvature X Y C y) x

-- BENCH: cov2-curvature-sub-swap-contmdiff
/-- **The Ricci identity for the curvature tensor, with its regularity hypotheses derived.**

`cov2Curvature_sub_swap` asks for twenty-five separate differentiability facts — one for
each term of the two expansions and each second derivative of each field. Every one of them
follows from uniform `C³` fields with `C` at `C⁴`, which is the regularity the trace step
already carries, so this wrapper is what makes the identity usable inside a frame sum.

The levels are forced by the third slot, as everywhere in this tower: `hC₂` needs
`∇_Y C` at `C³`, hence `C` at `C⁴`, because `curvature_smul_third` wants a `C²`
coefficient. -/
theorem cov2Curvature_sub_swap' (hcov : cov.torsion = 0)
    (hX : CMDiff 3 (T% X)) (hY : CMDiff 3 (T% Y))
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C)) :
    cov.cov2Curvature X Y A B C x - cov.cov2Curvature Y X A B C x
      = cov.curvatureCommutator X Y A B C x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hX2 : CMDiff 2 (T% X) := hX.of_le (by norm_num)
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC2 : CMDiff 2 (T% C) := hC.of_le (by norm_num)
  have hC3 : CMDiff 3 (T% C) := hC.of_le (by norm_num)
  have hXm : MDiffAt (T% X) x := (hX.mdifferentiable (by norm_num)) x
  have hYm : MDiffAt (T% Y) x := (hY.mdifferentiable (by norm_num)) x
  -- The first covariant derivatives that the expansions differentiate again.
  have hAY : CMDiff 2 (T% (fun z ↦ cov A z (Y z))) := cov.contMDiff_cov_apply hA hY2
  have hAX : CMDiff 2 (T% (fun z ↦ cov A z (X z))) := cov.contMDiff_cov_apply hA hX2
  have hBY : CMDiff 2 (T% (fun z ↦ cov B z (Y z))) := cov.contMDiff_cov_apply hB hY2
  have hBX : CMDiff 2 (T% (fun z ↦ cov B z (X z))) := cov.contMDiff_cov_apply hB hX2
  have hCY : CMDiff 3 (T% (fun z ↦ cov C z (Y z))) := cov.contMDiff_cov_apply hC hY
  have hCX : CMDiff 3 (T% (fun z ↦ cov C z (X z))) := cov.contMDiff_cov_apply hC hX
  have hYX : CMDiff 2 (T% (fun z ↦ cov Y z (X z))) := cov.contMDiff_cov_apply hY hX2
  have hXY : CMDiff 2 (T% (fun z ↦ cov X z (Y z))) := cov.contMDiff_cov_apply hX hY2
  exact cov.cov2Curvature_sub_swap hcov hC2 (hA2 x) (hB2 x) hXm hYm
    (cov.mdiffAt_cov_apply (cov.contMDiff_curvature_two hA hB hC) hYm)
    ((cov.contMDiff_curvature hAY hB2 hC3).mdifferentiable h1 x)
    ((cov.contMDiff_curvature hA2 hBY hC3).mdifferentiable h1 x)
    ((cov.contMDiff_curvature hA2 hB2 hCY).mdifferentiable h1 x)
    (cov.mdiffAt_cov_apply (cov.contMDiff_curvature_two hA hB hC) hXm)
    ((cov.contMDiff_curvature hAX hB2 hC3).mdifferentiable h1 x)
    ((cov.contMDiff_curvature hA2 hBX hC3).mdifferentiable h1 x)
    ((cov.contMDiff_curvature hA2 hB2 hCX).mdifferentiable h1 x)
    (cov.mdiffAt_cov_apply hA2 ((hYX.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hAY hXm)
    (cov.mdiffAt_cov_apply hA2 ((hXY.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hAX hYm)
    ((cov.contMDiff_curvature hX2 hY2 hA).mdifferentiable h1 x)
    (cov.mdiffAt_cov_apply hB2 ((hYX.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hBY hXm)
    (cov.mdiffAt_cov_apply hB2 ((hXY.mdifferentiable h2) x))
    (cov.mdiffAt_cov_apply hBX hYm)
    ((cov.contMDiff_curvature hX2 hY2 hB).mdifferentiable h1 x)
    (cov.contMDiff_cov_apply hC3 hYX)
    (cov.contMDiff_cov_apply hCY hX2)
    (cov.contMDiff_cov_apply hC3 hXY)
    (cov.contMDiff_cov_apply hCX hY2)
    (cov.contMDiff_curvature_two hX hY hC)

-- BENCH: curvature-laplacian-trace
/-- **`Δ Rm` as two traces of `∇²Rm` with the derivative slots in the wrong order.**

Summing `cov2Curvature_cyclic_eq_zero` over `X = Y = eᵢ` puts the first term of the cyclic
sum on the diagonal, where it *is* `Δ Rm` (`curvatureLaplacian_eq_sum_frame`), and leaves
the other two:

  `Δ Rm(A,B)C = −∑ᵢ (∇²_{eᵢ,A}Rm)(B,eᵢ)C − ∑ᵢ (∇²_{eᵢ,B}Rm)(eᵢ,A)C`.

This is the shape the evolution equation needs, and it is also why the Ricci identity for
the curvature tensor is required: in both surviving sums the *traced* index `eᵢ` sits in the
outer derivative slot, while the divergence lemmas of `Divergence.lean` trace the slot that
`∇Rm` is pointwise in. Reordering the two derivative slots by `cov2Curvature_sub_swap` is
what produces the terms quadratic in `Rm`.

The metric enters here and only here — the identity being summed carries none. -/
theorem curvatureLaplacian_eq_neg_sum (hcov : cov.torsion = 0)
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hb : ∀ i, fr i x = b i) :
    cov.curvatureLaplacian A B C x
      = -∑ i, cov.cov2Curvature (fr i) A B (fr i) C x
        - ∑ i, cov.cov2Curvature (fr i) B (fr i) A C x := by
  have hcyc : ∀ i : ι, cov.cov2Curvature (fr i) (fr i) A B C x
      + cov.cov2Curvature (fr i) A B (fr i) C x
      + cov.cov2Curvature (fr i) B (fr i) A C x = 0 :=
    fun i ↦ cov.cov2Curvature_cyclic_eq_zero hcov (hfr i) (hfr i) hA hB hC
  have hsum : ∑ i, (cov.cov2Curvature (fr i) (fr i) A B C x
      + cov.cov2Curvature (fr i) A B (fr i) C x
      + cov.cov2Curvature (fr i) B (fr i) A C x) = 0 := by
    simp only [hcyc, Finset.sum_const_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  rw [cov.curvatureLaplacian_eq_sum_frame hA hB hC hfr b hb]
  linear_combination (norm := module) hsum

-- BENCH: curvature-laplacian-swapped
/-- **`Δ Rm` with the derivative slots in the right order, and the quadratic terms exposed.**

Applying the Ricci identity for `Rm` to each summand of `curvatureLaplacian_eq_neg_sum`
moves the traced index out of the outer derivative slot and into the inner one, at the cost
of one commutator per summand:

  `Δ Rm(A,B)C = −∑ᵢ (∇²_{A,eᵢ}Rm)(B,eᵢ)C − ∑ᵢ (∇²_{B,eᵢ}Rm)(eᵢ,A)C
      − ∑ᵢ [∇²,∇²](eᵢ,A;B,eᵢ)C − ∑ᵢ [∇²,∇²](eᵢ,B;eᵢ,A)C`.

**This is `∂ₜRm = ΔRm + Q` in outline.** The first two sums are `∇` of a divergence of `Rm`
and so become second derivatives of `Ric` by the contracted second Bianchi identity; the
last two are `Q`, and they are quadratic in `Rm` because `curvatureCommutator` is `Rm`
applied to `Rm`. Nothing else will appear. -/
theorem curvatureLaplacian_eq_swapped (hcov : cov.torsion = 0)
    (hA : CMDiff 3 (T% A)) (hB : CMDiff 3 (T% B)) (hC : CMDiff 4 (T% C))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hb : ∀ i, fr i x = b i) :
    cov.curvatureLaplacian A B C x
      = -∑ i, cov.cov2Curvature A (fr i) B (fr i) C x
        - ∑ i, cov.cov2Curvature B (fr i) (fr i) A C x
        - ∑ i, cov.curvatureCommutator (fr i) A B (fr i) C x
        - ∑ i, cov.curvatureCommutator (fr i) B (fr i) A C x := by
  have e2 : ∑ i, cov.cov2Curvature (fr i) A B (fr i) C x
      = ∑ i, cov.cov2Curvature A (fr i) B (fr i) C x
        + ∑ i, cov.curvatureCommutator (fr i) A B (fr i) C x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hsw := cov.cov2Curvature_sub_swap' (x := x) hcov (hfr i) hA hB (hfr i) hC
    linear_combination (norm := module) hsw
  have e3 : ∑ i, cov.cov2Curvature (fr i) B (fr i) A C x
      = ∑ i, cov.cov2Curvature B (fr i) (fr i) A C x
        + ∑ i, cov.curvatureCommutator (fr i) B (fr i) A C x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hsw := cov.cov2Curvature_sub_swap' (x := x) hcov (hfr i) hB (hfr i) hA hC
    linear_combination (norm := module) hsw
  rw [cov.curvatureLaplacian_eq_neg_sum hcov hA hB hC hfr b hb, e2, e3]
  module

omit [ContMDiffCovariantDerivative cov 3] in
-- BENCH: sum-inner-covcurvature-snd
/-- **The divergence of `Rm` in its second slot, in terms of `∇Ric`.**

`∑ᵢ ⟪(∇_{eᵢ}Rm)(B,eᵢ)C, D⟫ = (∇_C Ric)(D,B) − (∇_D Ric)(C,B)`.

`Divergence.lean` traces the derivative index against `Rm`'s *output*; the trace step of the
evolution equation produces it against `Rm`'s *second input*. Pair symmetry of `∇Rm`
(`inner_covCurvature_pair_symm`) exchanges the two — it moves the pair `(B,eᵢ)` past `(C,D)`
and so puts `eᵢ` back in the output slot, where `divCurvature` lives. The contracted second
Bianchi identity then evaluates it.

This is the undifferentiated form of what the two surviving sums of
`curvatureLaplacian_eq_swapped` become once `∇_A` is moved outside the trace. -/
theorem sum_inner_covCurvature_snd_eq
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    {B C D : Π y : M, TangentSpace I y} {x : M}
    (hB : CMDiff 3 (T% B)) (hC : CMDiff 3 (T% C)) (hD : CMDiff 3 (T% D))
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (v : OrthonormalBasis ι ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = v i) :
    ∑ i, ⟪cov.covCurvature (fr i) B (fr i) C x, D x⟫
      = cov.covRicci C D B x - cov.covRicci D C B x := by
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC2 : CMDiff 2 (T% C) := hC.of_le (by norm_num)
  have hD2 : CMDiff 2 (T% D) := hD.of_le (by norm_num)
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  rw [← cov.divCurvature_eq_covRicci_sub htor hmet hC2 hD2 hB hs hu hx hfr2,
    cov.divCurvature_eq_sum_frame hC2 hD2 hB hfr2 v hbv]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact cov.inner_covCurvature_pair_symm hmet htor (hfr2 i) hB (hfr i) hC hD

end CovariantDerivative
