/-
**Constant sectional curvature determines the curvature tensor.**

If every sectional curvature at `x` equals `k`, then

  `⟪R(X,Y)Z, W⟫ = k (⟪Y,Z⟫⟪X,W⟫ − ⟪X,Z⟫⟪Y,W⟫)`

for all four arguments — the curvature is `k` times the constant-curvature model
`½ g ⊙ g`. This is the classical algebraic lemma, and it is exactly the bridge
between the two ways Hamilton's theorem gets stated: `Hamilton.lean`'s
`AdmitsConstPositiveSecMetric` fixes the sectional curvatures, whereas
Chow–Liao–Qin's `admitsConstantPositiveSectionalCurvature` fixes the full
`(0,4)` tensor. With this lemma the two are the same hypothesis, so the
divergence recorded in `notes/hamilton-statement-comparison.md` closes.

The proof is polarisation, twice. Let

  `T(A,B,C,D) = ⟪R(A,B)C, D⟫ − k (⟪B,C⟫⟪A,D⟫ − ⟪A,C⟫⟪B,D⟫)`

(`curvatureDefect`). `T` inherits every symmetry of the curvature — the model
term has them too — and the hypothesis says `T(A,B,B,A) = 0`. Polarising the
first and fourth slots gives `T(A,B,B,C) = 0`, polarising the second and third
gives antisymmetry in slots 2 and 3, and a tensor antisymmetric in *three*
consecutive slots is killed by the first Bianchi identity: `3T = 0`.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureSymm

open Bundle
open scoped Manifold ContDiff

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]

set_option maxSynthPendingDepth 3

section Defect

variable {k : ℝ} {A A' B B' C C' D D' : Π y : M, TangentSpace I y} {x : M}

/-- The difference between the curvature `(0,4)` tensor and `k` times the
constant-curvature model. -/
noncomputable def curvatureDefect (k : ℝ) (A B C D : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  ⟪cov.curvature A B C x, D x⟫
    - k * (⟪B x, C x⟫ * ⟪A x, D x⟫ - ⟪A x, C x⟫ * ⟪B x, D x⟫)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [ContMDiffCovariantDerivative cov 1] in
theorem curvatureDefect_anti12 :
    cov.curvatureDefect k A B C D x = -cov.curvatureDefect k B A C D x := by
  simp only [curvatureDefect, cov.curvature_antisymm A B C x, inner_neg_left]
  ring

theorem curvatureDefect_anti34
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x)
    (hC : CMDiff 2 (T% C)) (hD : CMDiff 2 (T% D)) :
    cov.curvatureDefect k A B C D x = -cov.curvatureDefect k A B D C x := by
  have h := cov.inner_curvature_right_skew hmetric hA hB hC hD
  simp only [curvatureDefect]
  linarith

theorem curvatureDefect_pair
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    (hA : CMDiff 2 (T% A)) (hB : CMDiff 2 (T% B))
    (hC : CMDiff 2 (T% C)) (hD : CMDiff 2 (T% D)) :
    cov.curvatureDefect k A B C D x = cov.curvatureDefect k C D A B x := by
  have h := cov.inner_curvature_pair_symm (x := x) hmetric htor hA hB hC hD
  have e1 : ⟪D x, A x⟫ = ⟪A x, D x⟫ := real_inner_comm _ _
  have e2 : ⟪C x, B x⟫ = ⟪B x, C x⟫ := real_inner_comm _ _
  have e3 : ⟪C x, A x⟫ = ⟪A x, C x⟫ := real_inner_comm _ _
  have e4 : ⟪D x, B x⟫ = ⟪B x, D x⟫ := real_inner_comm _ _
  simp only [curvatureDefect]
  rw [h, e1, e2, e3, e4]
  ring

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
theorem curvatureDefect_bianchi (htor : cov.torsion = 0)
    (hA : CMDiff 2 (T% A)) (hB : CMDiff 2 (T% B)) (hC : CMDiff 2 (T% C))
    (D : Π y : M, TangentSpace I y) :
    cov.curvatureDefect k A B C D x + cov.curvatureDefect k B C A D x
      + cov.curvatureDefect k C A B D x = 0 := by
  have h := cov.inner_bianchi_first htor hA hB hC (D x)
  have e1 : ⟪C x, B x⟫ = ⟪B x, C x⟫ := real_inner_comm _ _
  have e2 : ⟪C x, A x⟫ = ⟪A x, C x⟫ := real_inner_comm _ _
  have e3 : ⟪B x, A x⟫ = ⟪A x, B x⟫ := real_inner_comm _ _
  simp only [curvatureDefect]
  rw [e1, e2, e3]
  linarith

omit [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
theorem curvatureDefect_add_fst (hC : CMDiff 2 (T% C))
    (hA : MDiffAt (T% A) x) (hA' : MDiffAt (T% A') x) :
    cov.curvatureDefect k (A + A') B C D x
      = cov.curvatureDefect k A B C D x + cov.curvatureDefect k A' B C D x := by
  simp only [curvatureDefect, Pi.add_apply, cov.curvature_add_left hC hA hA', inner_add_left]
  ring

omit [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
theorem curvatureDefect_add_snd (hC : CMDiff 2 (T% C))
    (hB : MDiffAt (T% B) x) (hB' : MDiffAt (T% B') x) :
    cov.curvatureDefect k A (B + B') C D x
      = cov.curvatureDefect k A B C D x + cov.curvatureDefect k A B' C D x := by
  simp only [curvatureDefect, Pi.add_apply, cov.curvature_add_middle hC hB hB', inner_add_left]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
theorem curvatureDefect_add_thd (hC : CMDiff 2 (T% C)) (hC' : CMDiff 2 (T% C'))
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
    cov.curvatureDefect k A B (C + C') D x
      = cov.curvatureDefect k A B C D x + cov.curvatureDefect k A B C' D x := by
  simp only [curvatureDefect, Pi.add_apply, cov.curvature_add_right hC hC' hA hB,
    inner_add_left, inner_add_right]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [ContMDiffCovariantDerivative cov 1] in
theorem curvatureDefect_add_fth :
    cov.curvatureDefect k A B C (D + D') x
      = cov.curvatureDefect k A B C D x + cov.curvatureDefect k A B C D' x := by
  simp only [curvatureDefect, Pi.add_apply, inner_add_right]
  ring

end Defect

section ConstantCurvature

variable {k : ℝ} {X Y Z W : Π y : M, TangentSpace I y} {x : M}

-- BENCH: const-sec-determines-curvature
/-- **Constant sectional curvature determines the whole curvature tensor.** -/
theorem inner_curvature_eq_of_const_sec
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    (hsec : ∀ A B : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      ⟪cov.curvature A B B x, A x⟫
        = k * (⟪B x, B x⟫ * ⟪A x, A x⟫ - ⟪A x, B x⟫ * ⟪B x, A x⟫))
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫
      = k * (⟪Y x, Z x⟫ * ⟪X x, W x⟫ - ⟪X x, Z x⟫ * ⟪Y x, W x⟫) := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have md : ∀ {U : Π y : M, TangentSpace I y}, CMDiff 2 (T% U) → MDiffAt (T% U) x :=
    fun hU ↦ (hU.mdifferentiable h2) x
  -- the hypothesis, in terms of the defect
  have d0 : ∀ A B : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      cov.curvatureDefect k A B B A x = 0 := by
    intro A B hA hB
    simp only [curvatureDefect]
    rw [hsec A B hA hB]
    ring
  -- first polarisation: the defect kills any `(A, B, B, C)`
  have d1 : ∀ A B C : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      CMDiff 2 (T% C) → cov.curvatureDefect k A B B C x = 0 := by
    intro A B C hA hB hC
    have hAC : CMDiff 2 (T% (A + C)) := hA.add_section hC
    have e := d0 (A + C) B hAC hB
    rw [cov.curvatureDefect_add_fst hB (md hA) (md hC),
      cov.curvatureDefect_add_fth, cov.curvatureDefect_add_fth] at e
    -- `T(C,B,B,A) = T(A,B,B,C)` by pair symmetry and the two antisymmetries
    have p : cov.curvatureDefect k C B B A x = cov.curvatureDefect k A B B C x := by
      rw [cov.curvatureDefect_pair hmetric htor hC hB hB hA,
        cov.curvatureDefect_anti34 hmetric (md hB) (md hA) hC hB,
        cov.curvatureDefect_anti12 (k := k) (A := B) (B := A) (C := B) (D := C)]
      ring
    have e0 := d0 A B hA hB
    have e1 := d0 C B hC hB
    linarith
  -- second polarisation: antisymmetry in the middle two slots
  have d2 : ∀ A B C D : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      CMDiff 2 (T% C) → CMDiff 2 (T% D) →
      cov.curvatureDefect k A B C D x + cov.curvatureDefect k A C B D x = 0 := by
    intro A B C D hA hB hC hD
    have hBC : CMDiff 2 (T% (B + C)) := hB.add_section hC
    have e := d1 A (B + C) D hA hBC hD
    rw [cov.curvatureDefect_add_snd hBC (md hB) (md hC)] at e
    rw [cov.curvatureDefect_add_thd hB hC (md hA) (md hB),
      cov.curvatureDefect_add_thd hB hC (md hA) (md hC)] at e
    have e1 := d1 A B D hA hB hD
    have e2 := d1 A C D hA hC hD
    linarith
  -- three consecutive antisymmetries plus first Bianchi force the defect to vanish
  have d3 : cov.curvatureDefect k X Y Z W x = 0 := by
    have hb := cov.curvatureDefect_bianchi (k := k) (x := x) htor hX hY hZ W
    have s1 := d2 Y Z X W hY hZ hX hW
    have s2 := d2 Z X Y W hZ hX hY hW
    have a1 : cov.curvatureDefect k Y X Z W x = -cov.curvatureDefect k X Y Z W x :=
      cov.curvatureDefect_anti12
    have a2 : cov.curvatureDefect k Z Y X W x = -cov.curvatureDefect k Y Z X W x :=
      cov.curvatureDefect_anti12
    have a3 : cov.curvatureDefect k X Z Y W x = -cov.curvatureDefect k Z X Y W x :=
      cov.curvatureDefect_anti12
    linarith
  simp only [curvatureDefect] at d3
  linarith

-- BENCH: const-sec-determines-curvature-norm
/-- **Constant sectional curvature determines the curvature tensor**, with the hypothesis in
the form `Hamilton.lean`'s `hasConstSecLC_iff_mul` produces:
`⟪R(X,Y)Y,X⟫ = k(‖X‖²‖Y‖² − ⟪X,Y⟫²)`.

This is the bridge between the two ways the conclusion of Hamilton's theorem gets stated —
`AdmitsConstPositiveSecMetric` fixes the sectional curvatures, Chow–Liao–Qin's
`admitsConstantPositiveSectionalCurvature` fixes the full `(0,4)` tensor — and it says they
are the same hypothesis. -/
theorem inner_curvature_eq_of_const_sec_norm
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    (hsec : ∀ A B : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      ⟪cov.curvature A B B x, A x⟫
        = k * (‖A x‖ ^ 2 * ‖B x‖ ^ 2 - ⟪A x, B x⟫ ^ 2))
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫
      = k * (⟪Y x, Z x⟫ * ⟪X x, W x⟫ - ⟪X x, Z x⟫ * ⟪Y x, W x⟫) := by
  refine cov.inner_curvature_eq_of_const_sec hmetric htor (fun A B hA hB ↦ ?_) hX hY hZ hW
  have e1 : ⟪A x, A x⟫ = ‖A x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have e2 : ⟪B x, B x⟫ = ‖B x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have e3 : ⟪B x, A x⟫ = ⟪A x, B x⟫ := real_inner_comm _ _
  rw [hsec A B hA hB, e1, e2, e3]
  ring

end ConstantCurvature

section RicciScalar

variable [T2Space M]
variable {k : ℝ} {X Y : Π y : M, TangentSpace I y} {x : M}

-- BENCH: ricci-of-const-sec
/-- **Ricci of a constant-curvature metric is `(n-1)k` times the metric.** -/
theorem ricci_eq_of_const_sec
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    (hsec : ∀ A B : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      ⟪cov.curvature A B B x, A x⟫
        = k * (⟪B x, B x⟫ * ⟪A x, A x⟫ - ⟪A x, B x⟫ * ⟪B x, A x⟫))
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.ricci X Y x = ((Fintype.card ι : ℝ) - 1) * k * ⟪X x, Y x⟫ := by
  classical
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have md : ∀ {U : Π y : M, TangentSpace I y}, CMDiff 2 (T% U) → MDiffAt (T% U) x :=
    fun hU ↦ (hU.mdifferentiable h2) x
  -- the trace, over `b`, of the first-slot endomorphism, tested on global `C²` extensions
  have key : cov.ricci X Y x
      = ∑ i, ⟪b i, cov.curvature (extendTwo (I := I) (b i)) X Y x⟫ := by
    rw [cov.ricci_eq_trace hY x, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    conv_lhs => rw [← extendTwo_apply_self (I := I) (b i)]
    exact cov.mkHom_curvature_fst_apply hY (md (contMDiff_extendTwo (b i)))
  -- each term, by the constant-curvature formula
  have term : ∀ i, ⟪b i, cov.curvature (extendTwo (I := I) (b i)) X Y x⟫
      = k * (⟪X x, Y x⟫ - ⟪X x, b i⟫ * ⟪b i, Y x⟫) := by
    intro i
    have hEic : CMDiff 2 (T% (extendTwo (I := I) (b i))) := contMDiff_extendTwo (b i)
    have hEiv : extendTwo (I := I) (b i) x = b i := extendTwo_apply_self (b i)
    have e := cov.inner_curvature_eq_of_const_sec hmetric htor hsec hEic hX hY hEic
    rw [hEiv] at e
    have hbb : (⟪b i, b i⟫ : ℝ) = 1 := by simp
    have ecomm : ⟪b i, cov.curvature (extendTwo (I := I) (b i)) X Y x⟫
        = ⟪cov.curvature (extendTwo (I := I) (b i)) X Y x, b i⟫ := real_inner_comm _ _
    rw [ecomm, e, hbb]
    ring
  rw [key, Finset.sum_congr rfl fun i _ ↦ term i, ← Finset.mul_sum,
    Finset.sum_sub_distrib, b.sum_inner_mul_inner, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

-- BENCH: scalar-of-const-sec
/-- **Scalar curvature of a constant-curvature metric is `n(n-1)k`.** -/
theorem scalarCurvatureAt_eq_of_const_sec
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    (hsec : ∀ A B : Π y : M, TangentSpace I y, CMDiff 2 (T% A) → CMDiff 2 (T% B) →
      ⟪cov.curvature A B B x, A x⟫
        = k * (⟪B x, B x⟫ * ⟪A x, A x⟫ - ⟪A x, B x⟫ * ⟪B x, A x⟫))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.scalarCurvatureAt x = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * k := by
  classical
  rw [cov.scalarCurvatureAt_eq_sum_basis b]
  have term : ∀ i, cov.ricciAt x (b i) (b i) = ((Fintype.card ι : ℝ) - 1) * k := by
    intro i
    have hEic : CMDiff 2 (T% (extendTwo (I := I) (b i))) := contMDiff_extendTwo (b i)
    have hEiv : extendTwo (I := I) (b i) x = b i := extendTwo_apply_self (b i)
    have e := cov.ricci_eq_of_const_sec hmetric htor hsec hEic hEic b
    rw [hEiv] at e
    have hbb : (⟪b i, b i⟫ : ℝ) = 1 := by simp
    rw [← hEiv, cov.ricciAt_eq hEic hEic, e, hbb]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ term i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end RicciScalar

end CovariantDerivative
