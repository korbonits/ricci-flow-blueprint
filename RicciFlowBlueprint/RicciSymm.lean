/-
**Ricci is symmetric** on a general Riemannian manifold.

`Ricci.lean` proved the trace of the first Bianchi identity,

  `Ric(X,Y) − Ric(Y,X) = − tr (v ↦ R(X,Y)v)`,

under two hypotheses it could not then discharge: that global `C²` fields hit
every tangent vector (`hsur`), and that the endomorphism `v ↦ R(X,Y)v` exists at
all (`hL`) — the curvature's third slot was not known to be pointwise. Both are
now theorems: `GlobalExtension.lean` supplies the fields and
`CurvaturePointwise.lean` the pointwise dependence, so `curvatureEndoAt` is an
unconditional linear endomorphism of `T_xM`.

Its trace vanishes for a *metric* connection because `R(X,Y)` is skew-adjoint
(`inner_curvature_self_right`), and the trace over an orthonormal basis is
`∑ᵢ ⟪eᵢ, R(X,Y)eᵢ⟫`. Hence `Ric(X,Y) = Ric(Y,X)`, with no hypothesis beyond
metric compatibility and torsion-freeness — i.e. for the Levi-Civita connection.

Note what is *not* true: torsion-freeness alone does not give symmetry. The
antisymmetric part of Ricci is exactly that trace, and it vanishes because the
connection is metric, not because it is torsion-free. See `CLAUDE.md`,
corrected belief #2.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.RicciForm

open Bundle Filter
open scoped Manifold ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

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

open RicciFlowBlueprint

set_option maxSynthPendingDepth 3

section Endo

variable {X Y : Π y : M, TangentSpace I y} {x : M}

private theorem two_ne_zero'' : (2 : ℕ∞ω) ≠ 0 := by norm_num

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [ContMDiffCovariantDerivative cov 1] in
/-- A named global `C²` extension of a tangent vector. Naming it matters: the anonymous
`Exists.choose` of two different vectors prints identically, so `rw` cannot target one. -/
noncomputable def extendTwo (v : TangentSpace I x) : Π y : M, TangentSpace I y :=
  (exists_contMDiff_two_extension v).choose

omit [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [ContMDiffCovariantDerivative cov 1] in
theorem contMDiff_extendTwo (v : TangentSpace I x) : CMDiff 2 (T% (extendTwo (I := I) v)) :=
  (exists_contMDiff_two_extension v).choose_spec.1

omit [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [ContMDiffCovariantDerivative cov 1] in
@[simp] theorem extendTwo_apply_self (v : TangentSpace I x) : extendTwo (I := I) v x = v :=
  (exists_contMDiff_two_extension v).choose_spec.2

omit [CompleteSpace E] in
-- BENCH: curvature-endo-at
/-- **`R(X,Y)` as a linear endomorphism of `T_xM`**, on a general manifold: the
hypothesis `hL` of `ricci_sub_ricci_swap`, now constructed. Well-definedness is
`curvature_congr_third`; linearity is `curvature_add_right` and
`curvature_smul_const_right` on global `C²` extensions. -/
noncomputable def curvatureEndoAt (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := cov.curvature X Y (extendTwo (I := I) v) x
  map_add' v w := by
    have hval : extendTwo (I := I) (v + w) x
        = (extendTwo (I := I) v + extendTwo (I := I) w) x := by
      simp only [Pi.add_apply, extendTwo_apply_self]
    rw [cov.curvature_congr_third hX hY (contMDiff_extendTwo (v + w))
        ((contMDiff_extendTwo v).add_section (contMDiff_extendTwo w)) hval,
      cov.curvature_add_right (contMDiff_extendTwo v) (contMDiff_extendTwo w)
        (hX.mdifferentiableAt two_ne_zero'') (hY.mdifferentiableAt two_ne_zero'')]
  map_smul' c v := by
    have hval : extendTwo (I := I) (c • v) x = (c • extendTwo (I := I) v) x := by
      simp only [Pi.smul_apply, extendTwo_apply_self]
    rw [RingHom.id_apply,
      cov.curvature_congr_third hX hY (contMDiff_extendTwo (c • v))
        (contMDiff_extendTwo v).const_smul_section hval,
      cov.curvature_smul_const_right c (contMDiff_extendTwo v)
        (hX.mdifferentiableAt two_ne_zero'') (hY.mdifferentiableAt two_ne_zero'')]

omit [CompleteSpace E] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- `curvatureEndoAt` computes `R(X,Y)` on any globally `C²` field. -/
theorem curvatureEndoAt_apply (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    {W : Π y : M, TangentSpace I y} (hW : CMDiff 2 (T% W)) :
    cov.curvatureEndoAt hX hY (W x) = cov.curvature X Y W x :=
  cov.curvature_congr_third hX hY (contMDiff_extendTwo (W x)) hW (extendTwo_apply_self (W x))

-- BENCH: trace-curvature-endo-zero
/-- **The curvature endomorphism of a metric connection is traceless**, because it is
skew-adjoint. -/
theorem trace_curvatureEndoAt_eq_zero
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) :
    LinearMap.trace ℝ (TangentSpace I x) (cov.curvatureEndoAt hX hY) = 0 := by
  have : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TangentSpace I x))]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  set v := stdOrthonormalBasis ℝ (TangentSpace I x) i with hv
  have h0 : ⟪cov.curvature X Y (extendTwo (I := I) v) x, extendTwo (I := I) v x⟫ = 0 :=
    cov.inner_curvature_self_right hmetric (hX.mdifferentiableAt two_ne_zero'')
      (hY.mdifferentiableAt two_ne_zero'') (contMDiff_extendTwo v)
  rw [extendTwo_apply_self] at h0
  have hL : cov.curvatureEndoAt hX hY v = cov.curvature X Y (extendTwo (I := I) v) x := rfl
  have e : ⟪v, cov.curvature X Y (extendTwo (I := I) v) x⟫
      = ⟪cov.curvature X Y (extendTwo (I := I) v) x, v⟫ := real_inner_comm _ _
  rw [hL, e]
  exact h0

end Endo

section Symm

variable {X Y : Π y : M, TangentSpace I y} {x : M}

-- BENCH: ricci-symm-manifold
/-- **Ricci is symmetric** for a metric torsion-free connection on a general manifold —
in particular for the Levi-Civita connection. The antisymmetric part is the trace of the
curvature endomorphism (`ricci_sub_ricci_swap`), and that vanishes by skew-adjointness. -/
theorem ricci_symm (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) :
    cov.ricci X Y x = cov.ricci Y X x := by
  have hsw := cov.ricci_sub_ricci_swap htor hX hY
    (fun v ↦ ⟨extendTwo (I := I) v, contMDiff_extendTwo v, extendTwo_apply_self v⟩)
    (L := cov.curvatureEndoAt (hX x) (hY x))
    (fun W hW ↦ cov.curvatureEndoAt_apply (hX x) (hY x) hW)
  rw [cov.trace_curvatureEndoAt_eq_zero hmetric (hX x) (hY x)] at hsw
  linarith

/-- **The Ricci form is symmetric.** -/
theorem ricciAt_symm (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (v w : TangentSpace I x) :
    cov.ricciAt x v w = cov.ricciAt x w v := by
  obtain ⟨V, hV, hVv⟩ := exists_contMDiff_two_extension v
  obtain ⟨W, hW, hWw⟩ := exists_contMDiff_two_extension w
  rw [← hVv, ← hWw, cov.ricciAt_eq hV hW, cov.ricciAt_eq hW hV]
  exact cov.ricci_symm hmetric htor hV hW

theorem ricciForm_symm (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) (v w : TangentSpace I x) :
    cov.ricciForm x v w = cov.ricciForm x w v :=
  cov.ricciAt_symm hmetric htor v w

end Symm

end CovariantDerivative
