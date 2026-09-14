/-
**The Riemann tensor as a pointwise `(0,4)` form**, on a general manifold.

`CurvatureSymm.lean` proves pair symmetry and says what it is *for*: it is what makes `R` an
operator on `Λ²T_xM`, the form Hamilton's pinching argument and Uhlenbeck's trick need. This
file supplies the object that claim is about.

**What was missing was a genuinely pointwise `(0,4)` tensor.** The repo had the curvature
packaged in *pieces* — `curvatureEndoAt` fixes the two field slots `X,Y` and varies a tangent
vector in the third; `curvatureBilinFst` fixes the fields `Z,W` and varies the first — but
nothing took four tangent vectors. The alternating-map factorisation through `Λ²` needs all
four at once.

**Three slots cost an extension, the fourth is free.** `curvatureTensorAt` evaluates the
curvature on global `C²` extensions of the first three vectors and pairs against the fourth
directly, so slot 4 needs no regularity at all — the identity there is a vector identity, as
`inner_bianchi_first` already observed. Slots 1 and 2 are `tensorialAt_curvature_fst`/`_snd`
cashed in through `TensorialAt.pointwise`; slot 3 is `curvature_congr_third` with
`curvature_add_right`/`curvature_smul_const_right`, exactly the `curvatureEndoAt` pattern one
slot wider.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.CurvatureSymm

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

variable {x : M}

private theorem two_ne_zero₄ : (2 : ℕ∞ω) ≠ 0 := by norm_num

-- BENCH: curvature-tensor-at
/-- **The Riemann tensor at a point**, `Rm_x(v₁,v₂,v₃,v₄) = ⟪R(v₁,v₂)v₃, v₄⟫`, as a function of
four tangent vectors.

The first three are globalised by `extendTwo`; the fourth is used as it is, since the pairing
is against a vector and needs no field. -/
noncomputable def curvatureTensorAt (v₁ v₂ v₃ v₄ : TangentSpace I x) : ℝ :=
  ⟪cov.curvature (extendTwo (I := I) v₁) (extendTwo (I := I) v₂)
    (extendTwo (I := I) v₃) x, v₄⟫

/-- `curvatureTensorAt` computes `⟪R(X,Y)Z, W⟫` on any globally `C²` fields. -/
theorem curvatureTensorAt_apply_field {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (w : TangentSpace I x) :
    cov.curvatureTensorAt (X x) (Y x) (Z x) w = ⟪cov.curvature X Y Z x, w⟫ := by
  have hmX : MDiffAt (T% X) x := (hX.mdifferentiable two_ne_zero₄) x
  have hmY : MDiffAt (T% Y) x := (hY.mdifferentiable two_ne_zero₄) x
  have hme₁ : MDiffAt (T% (extendTwo (I := I) (X x))) x :=
    ((contMDiff_extendTwo (X x)).mdifferentiable two_ne_zero₄) x
  have hme₂ : MDiffAt (T% (extendTwo (I := I) (Y x))) x :=
    ((contMDiff_extendTwo (Y x)).mdifferentiable two_ne_zero₄) x
  -- slot 3 first: replace the extension of `Z x` by `Z` itself
  have h3 : cov.curvature (extendTwo (I := I) (X x)) (extendTwo (I := I) (Y x))
      (extendTwo (I := I) (Z x)) x
      = cov.curvature (extendTwo (I := I) (X x)) (extendTwo (I := I) (Y x)) Z x :=
    cov.curvature_congr_third ((contMDiff_extendTwo (X x)).contMDiffAt)
      ((contMDiff_extendTwo (Y x)).contMDiffAt) (contMDiff_extendTwo (Z x)) hZ
      (extendTwo_apply_self (Z x))
  -- then slot 1 and slot 2, by pointwiseness
  have h1 : cov.curvature (extendTwo (I := I) (X x)) (extendTwo (I := I) (Y x)) Z x
      = cov.curvature X (extendTwo (I := I) (Y x)) Z x :=
    (cov.tensorialAt_curvature_fst (V := extendTwo (I := I) (Y x)) hZ x).pointwise
      hme₁ hmX (extendTwo_apply_self (X x))
  have h2 : cov.curvature X (extendTwo (I := I) (Y x)) Z x = cov.curvature X Y Z x :=
    (cov.tensorialAt_curvature_snd (V := X) hZ x).pointwise hme₂ hmY
      (extendTwo_apply_self (Y x))
  rw [curvatureTensorAt, h3, h1, h2]

section Multilinear

variable (v w a b c d : TangentSpace I x)

omit [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
private theorem mdiffAt_ext (u : TangentSpace I x) :
    MDiffAt (T% (extendTwo (I := I) u)) x :=
  ((contMDiff_extendTwo u).mdifferentiable two_ne_zero₄) x

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- Additivity in the first slot. -/
theorem curvatureTensorAt_add_fst :
    cov.curvatureTensorAt (v + w) b c d
      = cov.curvatureTensorAt v b c d + cov.curvatureTensorAt w b c d := by
  have hsum : MDiffAt (T% (extendTwo (I := I) v + extendTwo (I := I) w)) x :=
    (((contMDiff_extendTwo v).add_section (contMDiff_extendTwo w)).mdifferentiable
      two_ne_zero₄) x
  have hval : extendTwo (I := I) (v + w) x
      = (extendTwo (I := I) v + extendTwo (I := I) w) x := by
    simp only [Pi.add_apply, extendTwo_apply_self]
  have hT := cov.tensorialAt_curvature_fst (V := extendTwo (I := I) b)
    (contMDiff_extendTwo c) x
  simp only [curvatureTensorAt]
  rw [hT.pointwise (mdiffAt_ext (v + w)) hsum hval,
    hT.add (mdiffAt_ext v) (mdiffAt_ext w), inner_add_left]

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- Homogeneity in the first slot. -/
theorem curvatureTensorAt_smul_fst (r : ℝ) :
    cov.curvatureTensorAt (r • v) b c d = r * cov.curvatureTensorAt v b c d := by
  have hsmul : MDiffAt (T% ((fun _ : M ↦ r) • extendTwo (I := I) v)) x := by
    have h : MDiffAt (T% (r • extendTwo (I := I) v)) x :=
      (((contMDiff_extendTwo v).const_smul_section (a := r)).mdifferentiable two_ne_zero₄) x
    exact h
  have hval : extendTwo (I := I) (r • v) x
      = ((fun _ : M ↦ r) • extendTwo (I := I) v) x := by
    show extendTwo (I := I) (r • v) x = r • extendTwo (I := I) v x
    rw [extendTwo_apply_self, extendTwo_apply_self]
  have hT := cov.tensorialAt_curvature_fst (V := extendTwo (I := I) b)
    (contMDiff_extendTwo c) x
  simp only [curvatureTensorAt]
  rw [hT.pointwise (mdiffAt_ext (r • v)) hsmul hval,
    hT.smul mdifferentiableAt_const (mdiffAt_ext v), real_inner_smul_left]

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- Additivity in the second slot. -/
theorem curvatureTensorAt_add_snd :
    cov.curvatureTensorAt a (v + w) c d
      = cov.curvatureTensorAt a v c d + cov.curvatureTensorAt a w c d := by
  have hsum : MDiffAt (T% (extendTwo (I := I) v + extendTwo (I := I) w)) x :=
    (((contMDiff_extendTwo v).add_section (contMDiff_extendTwo w)).mdifferentiable
      two_ne_zero₄) x
  have hval : extendTwo (I := I) (v + w) x
      = (extendTwo (I := I) v + extendTwo (I := I) w) x := by
    simp only [Pi.add_apply, extendTwo_apply_self]
  have hT := cov.tensorialAt_curvature_snd (V := extendTwo (I := I) a)
    (contMDiff_extendTwo c) x
  simp only [curvatureTensorAt]
  rw [hT.pointwise (mdiffAt_ext (v + w)) hsum hval,
    hT.add (mdiffAt_ext v) (mdiffAt_ext w), inner_add_left]

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] in
/-- Homogeneity in the second slot. -/
theorem curvatureTensorAt_smul_snd (r : ℝ) :
    cov.curvatureTensorAt a (r • v) c d = r * cov.curvatureTensorAt a v c d := by
  have hsmul : MDiffAt (T% ((fun _ : M ↦ r) • extendTwo (I := I) v)) x := by
    have h : MDiffAt (T% (r • extendTwo (I := I) v)) x :=
      (((contMDiff_extendTwo v).const_smul_section (a := r)).mdifferentiable two_ne_zero₄) x
    exact h
  have hval : extendTwo (I := I) (r • v) x
      = ((fun _ : M ↦ r) • extendTwo (I := I) v) x := by
    show extendTwo (I := I) (r • v) x = r • extendTwo (I := I) v x
    rw [extendTwo_apply_self, extendTwo_apply_self]
  have hT := cov.tensorialAt_curvature_snd (V := extendTwo (I := I) a)
    (contMDiff_extendTwo c) x
  simp only [curvatureTensorAt]
  rw [hT.pointwise (mdiffAt_ext (r • v)) hsmul hval,
    hT.smul mdifferentiableAt_const (mdiffAt_ext v), real_inner_smul_left]

omit [CompleteSpace E] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- Additivity in the third slot. -/
theorem curvatureTensorAt_add_thd :
    cov.curvatureTensorAt a b (v + w) d
      = cov.curvatureTensorAt a b v d + cov.curvatureTensorAt a b w d := by
  have hval : extendTwo (I := I) (v + w) x
      = (extendTwo (I := I) v + extendTwo (I := I) w) x := by
    simp only [Pi.add_apply, extendTwo_apply_self]
  simp only [curvatureTensorAt]
  rw [cov.curvature_congr_third ((contMDiff_extendTwo a).contMDiffAt)
      ((contMDiff_extendTwo b).contMDiffAt) (contMDiff_extendTwo (v + w))
      ((contMDiff_extendTwo v).add_section (contMDiff_extendTwo w)) hval,
    cov.curvature_add_right (contMDiff_extendTwo v) (contMDiff_extendTwo w)
      (mdiffAt_ext a) (mdiffAt_ext b), inner_add_left]

omit [CompleteSpace E] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- Homogeneity in the third slot. -/
theorem curvatureTensorAt_smul_thd (r : ℝ) :
    cov.curvatureTensorAt a b (r • v) d = r * cov.curvatureTensorAt a b v d := by
  have hval : extendTwo (I := I) (r • v) x
      = (r • extendTwo (I := I) v) x := by
    simp only [Pi.smul_apply, extendTwo_apply_self]
  simp only [curvatureTensorAt]
  rw [cov.curvature_congr_third ((contMDiff_extendTwo a).contMDiffAt)
      ((contMDiff_extendTwo b).contMDiffAt) (contMDiff_extendTwo (r • v))
      (contMDiff_extendTwo v).const_smul_section hval,
    cov.curvature_smul_const_right r (contMDiff_extendTwo v)
      (mdiffAt_ext a) (mdiffAt_ext b), real_inner_smul_left]

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- Additivity in the fourth slot --- free, the pairing being against a vector. -/
theorem curvatureTensorAt_add_fth :
    cov.curvatureTensorAt a b c (v + w)
      = cov.curvatureTensorAt a b c v + cov.curvatureTensorAt a b c w :=
  inner_add_right _ _ _

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- Homogeneity in the fourth slot --- free. -/
theorem curvatureTensorAt_smul_fth (r : ℝ) :
    cov.curvatureTensorAt a b c (r • v) = r * cov.curvatureTensorAt a b c v :=
  real_inner_smul_right _ _ _

end Multilinear

section Symmetries

variable {a b c d : TangentSpace I x}

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [ContMDiffCovariantDerivative cov 1] in
/-- **Antisymmetry in the first pair.** -/
theorem curvatureTensorAt_antisymm_fst_snd :
    cov.curvatureTensorAt a b c d = -cov.curvatureTensorAt b a c d := by
  simp only [curvatureTensorAt]
  exact cov.inner_curvature_left_skew d

-- BENCH: curvature-tensor-at-pair-symm
/-- **Pair symmetry**, pointwise: `Rm(a,b,c,d) = Rm(c,d,a,b)`.

This is `inner_curvature_pair_symm` read on the four `extendTwo` extensions; the fourth slot
takes the vector directly, so only three extensions ever appear on either side. -/
theorem curvatureTensorAt_pair_symm
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) :
    cov.curvatureTensorAt a b c d = cov.curvatureTensorAt c d a b := by
  have h := cov.inner_curvature_pair_symm (x := x) hmetric htor
    (contMDiff_extendTwo a) (contMDiff_extendTwo b) (contMDiff_extendTwo c)
    (contMDiff_extendTwo d)
  rw [extendTwo_apply_self, extendTwo_apply_self] at h
  exact h

/-- **Antisymmetry in the second pair**, from pair symmetry and antisymmetry in the first. -/
theorem curvatureTensorAt_antisymm_thd_fth
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0) :
    cov.curvatureTensorAt a b c d = -cov.curvatureTensorAt a b d c := by
  rw [cov.curvatureTensorAt_pair_symm hmetric htor,
    cov.curvatureTensorAt_antisymm_fst_snd (a := c) (b := d),
    cov.curvatureTensorAt_pair_symm (a := d) (b := c) hmetric htor]

omit [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] in
/-- **The first Bianchi identity**, pointwise. -/
theorem curvatureTensorAt_bianchi (htor : cov.torsion = 0) :
    cov.curvatureTensorAt a b c d + cov.curvatureTensorAt b c a d
      + cov.curvatureTensorAt c a b d = 0 := by
  simp only [curvatureTensorAt]
  exact cov.inner_bianchi_first htor (contMDiff_extendTwo a) (contMDiff_extendTwo b)
    (contMDiff_extendTwo c) d

end Symmetries

end CovariantDerivative
