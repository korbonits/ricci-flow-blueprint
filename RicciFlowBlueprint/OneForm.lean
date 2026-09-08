/-
The covariant derivative and divergence of a one-form.

`(∇_X ω)(Y) = X(ω(Y)) − ω(∇_X Y)` has **two** terms, against `covBilin`'s three and
`covCurvature`'s four, so both of its slots are free of any frame argument: the direction is a
continuous linear map by construction, and the `Y` slot is the plain Leibniz cancellation on
`MDifferentiableAt` fields. `TensorialAt.mkHom₂` therefore applies directly and `∇ω` is a
bilinear form on `T_xM`; its metric trace is the divergence `div ω = ∑ᵢ (∇_{eᵢ}ω)(eᵢ)`.

For `ω = df` these are `Hessian.lean`'s `hessianFun` and `laplacianFun`. The point of the
general case is `div div h`: the double divergence of a bilinear form, which pairs slots 1&3
and 2&4 of `∇²h`, factors as `div` of the one-form `Z ↦ ∑ᵢ (∇_{eᵢ}h)(eᵢ,Z)` and so needs no
four-linear packaging of `∇²h` at all.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.BilinLaplacian

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- The **covariant derivative of a one-form field**: `(∇_X ω)(Y) = X(ω(Y)) − ω(∇_X Y)`. -/
noncomputable def covOneForm (w : M → E →L[ℝ] ℝ) (X Y : Π y : M, TangentSpace I y) (x : M) :
    ℝ :=
  mvfderiv I (fun y ↦ w y (Y y)) x (X x) - w x (cov Y x (X x))

variable {w : M → E →L[ℝ] ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇ω` is linear in the direction, with no hypotheses: both terms are continuous linear maps
applied to `X x`. -/
theorem covOneForm_smul_dir {f : M → ℝ} {X Y : Π y : M, TangentSpace I y} {x : M} :
    cov.covOneForm w (f • X) Y x = f x * cov.covOneForm w X Y x := by
  have key : ∀ (c : ℝ) (v : E), (w x) (c • v) = c * (w x) v := by
    intro c v; rw [map_smul]; rfl
  have hfx : (f • X) x = f x • X x := rfl
  have hd : mvfderiv I (fun y ↦ w y (Y y)) x (f x • X x)
      = f x * mvfderiv I (fun y ↦ w y (Y y)) x (X x) := by rw [map_smul]; rfl
  have e₁ : (w x) (cov Y x (f x • X x)) = f x * (w x) (cov Y x (X x)) := by
    rw [show cov Y x (f x • X x) = f x • cov Y x (X x) from map_smul _ _ _]
    exact key (f x) _
  simp only [covOneForm, hfx]
  rw [hd, e₁]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇ω` is additive in the direction. -/
theorem covOneForm_add_dir {X X' Y : Π y : M, TangentSpace I y} {x : M} :
    cov.covOneForm w (X + X') Y x = cov.covOneForm w X Y x + cov.covOneForm w X' Y x := by
  have key : ∀ v v' : E, (w x) (v + v') = (w x) v + (w x) v' := fun v v' ↦ map_add _ _ _
  have hd : mvfderiv I (fun y ↦ w y (Y y)) x ((X + X') x)
      = mvfderiv I (fun y ↦ w y (Y y)) x (X x)
        + mvfderiv I (fun y ↦ w y (Y y)) x (X' x) := map_add _ _ _
  have e₁ : (w x) (cov Y x ((X + X') x))
      = (w x) (cov Y x (X x)) + (w x) (cov Y x (X' x)) := by
    rw [show cov Y x ((X + X') x) = cov Y x (X x) + cov Y x (X' x) from map_add _ _ _]
    exact key _ _
  simp only [covOneForm]
  rw [hd, e₁]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇ω` is pointwise in the direction.** -/
theorem covOneForm_congr_dir {X X' Y : Π y : M, TangentSpace I y} {x : M} (hXX' : X x = X' x) :
    cov.covOneForm w X Y x = cov.covOneForm w X' Y x := by
  simp only [covOneForm, hXX']

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇ω` is linear in its second slot: the Leibniz term of `X(f·ω(Y))` is cancelled by the
Leibniz term of `∇_X(f • Y)`. Only `MDifferentiableAt` of the fields is used. -/
theorem covOneForm_smul_snd {f : M → ℝ} {X Y : Π y : M, TangentSpace I y} {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hw : MDiffAt (fun y ↦ w y (Y y)) x) :
    cov.covOneForm w X (f • Y) x = f x * cov.covOneForm w X Y x := by
  have key : ∀ (z : M) (c : ℝ) (v : E), (w z) (c • v) = c * (w z) v := by
    intro z c v; rw [map_smul]; rfl
  have key₂ : ∀ (c d : ℝ) (v v' : E), (w x) (c • v + d • v') = c * (w x) v + d * (w x) v' := by
    intro c d v v'
    rw [map_add, map_smul, map_smul]; rfl
  have hprod : (fun y ↦ w y ((f • Y) y)) = fun y ↦ f y * w y (Y y) := by
    funext y
    exact key y (f y) (Y y)
  have hcov : cov (f • Y) x (X x)
      = f x • cov Y x (X x) + mvfderiv I f x (X x) • Y x := by
    rw [cov.isCovariantDerivativeOn.leibniz hY hf]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have e₁ : (w x) (cov (f • Y) x (X x))
      = f x * (w x) (cov Y x (X x)) + mvfderiv I f x (X x) * (w x) (Y x) := by
    rw [hcov]
    exact key₂ (f x) (mvfderiv I f x (X x)) (cov Y x (X x)) (Y x)
  simp only [covOneForm, hprod]
  rw [mvfderiv_fun_mul hf hw, e₁]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- `∇ω` is additive in its second slot. -/
theorem covOneForm_add_snd {X Y Y' : Π y : M, TangentSpace I y} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hw : MDiffAt (fun y ↦ w y (Y y)) x) (hw' : MDiffAt (fun y ↦ w y (Y' y)) x) :
    cov.covOneForm w X (Y + Y') x = cov.covOneForm w X Y x + cov.covOneForm w X Y' x := by
  have key : ∀ (z : M) (v v' : E), (w z) (v + v') = (w z) v + (w z) v' :=
    fun z v v' ↦ map_add _ _ _
  have hsum : (fun y ↦ w y ((Y + Y') y)) = fun y ↦ w y (Y y) + w y (Y' y) := by
    funext y
    exact key y (Y y) (Y' y)
  have e₁ : (w x) (cov (Y + Y') x (X x))
      = (w x) (cov Y x (X x)) + (w x) (cov Y' x (X x)) := by
    rw [cov.isCovariantDerivativeOn.add hY hY']
    exact key x (cov Y x (X x)) (cov Y' x (X x))
  simp only [covOneForm, hsum]
  rw [mvfderiv_fun_add hw hw', e₁]
  simp only [add_apply]
  ring

/-- **`ω` is differentiable against differentiable fields at `x`.** -/
def IsMDiffOneFormAt (w : M → E →L[ℝ] ℝ) (x : M) : Prop :=
  ∀ U : Π y : M, TangentSpace I y, MDiffAt (T% U) x → MDiffAt (fun y ↦ w y (U y)) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem tensorialAt_covOneForm_dir (Y : Π y : M, TangentSpace I y) (x : M) :
    TensorialAt I E (fun X ↦ cov.covOneForm w X Y x) x where
  smul _ _ := cov.covOneForm_smul_dir
  add _ _ := cov.covOneForm_add_dir

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem tensorialAt_covOneForm_snd (hw : IsMDiffOneFormAt (I := I) w x)
    (X : Π y : M, TangentSpace I y) :
    TensorialAt I E (fun Y ↦ cov.covOneForm w X Y x) x where
  smul hf hY := cov.covOneForm_smul_snd hf hY (hw _ hY)
  add hY hY' := cov.covOneForm_add_snd hY hY' (hw _ hY) (hw _ hY')

/-- **`∇ω` as a continuous bilinear form on `T_xM`.** No frame argument is needed anywhere:
`∇ω` has two terms, so both slots are `TensorialAt` on merely differentiable fields. -/
noncomputable def covOneFormAt (hw : IsMDiffOneFormAt (I := I) w x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Y ↦ cov.covOneForm w X Y x) x
    (fun _ _ ↦ cov.tensorialAt_covOneForm_dir _ x)
    (fun X _ ↦ cov.tensorialAt_covOneForm_snd hw X)

omit [CompleteSpace E] in
theorem covOneFormAt_apply (hw : IsMDiffOneFormAt (I := I) w x)
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.covOneFormAt hw (X x) (Y x) = cov.covOneForm w X Y x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

section Divergence

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **The divergence of a one-form**, `div ω = ∑ᵢ (∇_{eᵢ}ω)(eᵢ)`: the metric trace of `∇ω`.
For `ω = df` this is `laplacianFun f`. -/
noncomputable def divOneForm (w : M → E →L[ℝ] ℝ) (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.covOneForm w (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
    (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) x

omit [CompleteSpace E] in
/-- **`div ω` is frame-independent**: it is the trace of a bilinear form. -/
theorem divOneForm_eq_sum_basis (hw : IsMDiffOneFormAt (I := I) w x)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.divOneForm w x = ∑ i, cov.covOneFormAt hw (b i) (b i) := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  have hstd : cov.divOneForm w x
      = ∑ i, cov.covOneFormAt hw (stdOrthonormalBasis ℝ (TangentSpace I x) i)
          (stdOrthonormalBasis ℝ (TangentSpace I x) i) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hext := FiberBundle.mdifferentiableAt_extend I E
      (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    have hself : (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i) : Π y : M,
        TangentSpace I y) x = stdOrthonormalBasis ℝ (TangentSpace I x) i :=
      FiberBundle.extend_apply_self ..
    have happ := cov.covOneFormAt_apply hw hext hext
    rw [hself] at happ
    exact happ.symm
  rw [hstd]
  exact OrthonormalBasis.sum_apply_self_eq _ b (cov.covOneFormAt hw)

omit [CompleteSpace E] in
/-- **`div ω` read off any frame orthonormal at `x`.** -/
theorem divOneForm_eq_sum_frame (hw : IsMDiffOneFormAt (I := I) w x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, MDiffAt (T% (fr i)) x) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hb : ∀ i, fr i x = b i) :
    cov.divOneForm w x = ∑ i, cov.covOneForm w (fr i) (fr i) x := by
  rw [cov.divOneForm_eq_sum_basis hw b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hb i, cov.covOneFormAt_apply hw (hfr i) (hfr i)]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- **The Hessian of a function is `∇` of its differential**: `∇²f(X,Y) = (∇_X \mathrm{d}f)(Y)`.
The two definitions are the same expression, so this is `rfl`; the point is that `covOneFormAt`
then packages `∇²f` as a bilinear form with **no frame argument**, which is what the Hessian on
its own has no cheap route to. -/
theorem hessianFun_eq_covOneForm (f : M → ℝ) (X Y : Π y : M, TangentSpace I y) (x : M) :
    cov.hessianFun f X Y x
      = cov.covOneForm (fun y ↦ (mvfderiv I f y : TangentSpace I y →L[ℝ] ℝ)) X Y x := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- `∇ω` is linear in `ω` under a constant rescaling. -/
theorem covOneForm_smul_form (c : ℝ) (v : M → E →L[ℝ] ℝ)
    {X Y : Π y : M, TangentSpace I y} {x : M} (hv : MDiffAt (fun y ↦ v y (Y y)) x) :
    cov.covOneForm (fun y ↦ (c • v y : E →L[ℝ] ℝ)) X Y x = c * cov.covOneForm v X Y x := by
  have hfun : (fun y ↦ (c • v y : E →L[ℝ] ℝ) (Y y)) = fun y ↦ c * v y (Y y) := by
    funext y; rfl
  have hd : mvfderiv I (fun y ↦ c * v y (Y y)) x (X x)
      = c * mvfderiv I (fun y ↦ v y (Y y)) x (X x) := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const hv, mvfderiv_const]
    simp
  have hval : (c • v x : E →L[ℝ] ℝ) (cov Y x (X x)) = c * v x (cov Y x (X x)) := rfl
  simp only [covOneForm, hfun]
  rw [hd, hval]
  show _ = c * (mvfderiv I (fun y ↦ v y (Y y)) x (X x) - v x (cov Y x (X x)))
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- **`∇ω` only depends on the germ of `ω`.** -/
theorem covOneForm_congr_of_eventuallyEq {v v' : M → E →L[ℝ] ℝ}
    {X Y : Π y : M, TangentSpace I y} {x : M} (hvv' : v =ᶠ[𝓝 x] v') :
    cov.covOneForm v X Y x = cov.covOneForm v' X Y x := by
  have hfun : (fun y ↦ v y (Y y)) =ᶠ[𝓝 x] fun y ↦ v' y (Y y) := by
    filter_upwards [hvv'] with y hy
    rw [hy]
  simp only [covOneForm, hfun.mvfderiv_eq, hvv'.eq_of_nhds]

end Divergence

section OneFormTrace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] in
/-- `div` is linear in `ω` under a constant rescaling. -/
theorem divOneForm_smul (c : ℝ) (v : M → E →L[ℝ] ℝ) {x : M}
    (hv : IsMDiffOneFormAt (I := I) v x) :
    cov.divOneForm (fun y ↦ (c • v y : E →L[ℝ] ℝ)) x = c * cov.divOneForm v x := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  rw [divOneForm, divOneForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    cov.covOneForm_smul_form c v (hv _ (FiberBundle.mdifferentiableAt_extend ..))

omit [CompleteSpace E] in
/-- **`div ω` only depends on the germ of `ω`.** -/
theorem divOneForm_congr {v v' : M → E →L[ℝ] ℝ} {x : M} (hvv' : v =ᶠ[𝓝 x] v') :
    cov.divOneForm v x = cov.divOneForm v' x := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  exact Finset.sum_congr rfl fun i _ ↦ cov.covOneForm_congr_of_eventuallyEq hvv'

end OneFormTrace


section FunctionTrace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] in
/-- **The Laplacian of a function is the divergence of its differential.** -/
theorem laplacianFun_eq_divOneForm (f : M → ℝ) (x : M) :
    cov.laplacianFun f x
      = cov.divOneForm (fun y ↦ (mvfderiv I f y : TangentSpace I y →L[ℝ] ℝ)) x := rfl

omit [CompleteSpace E] in
/-- **`Δf` read off any frame orthonormal at `x`**, and hence frame-independent. Free from
`divOneForm_eq_sum_frame`: no packaging of the Hessian is needed, because `∇²f` *is* `∇` of the
one-form `df`, and `∇ω` has only two terms. -/
theorem laplacianFun_eq_sum_frame {f : M → ℝ} {x : M}
    (hf : IsMDiffOneFormAt (I := I) (fun y ↦ (mvfderiv I f y : TangentSpace I y →L[ℝ] ℝ)) x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, MDiffAt (T% (fr i)) x) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hb : ∀ i, fr i x = b i) :
    cov.laplacianFun f x = ∑ i, cov.hessianFun f (fr i) (fr i) x := by
  rw [cov.laplacianFun_eq_divOneForm f x, cov.divOneForm_eq_sum_frame hf hfr b hb]
  exact Finset.sum_congr rfl fun i _ ↦ (cov.hessianFun_eq_covOneForm f (fr i) (fr i) x).symm

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]
  [ContMDiffCovariantDerivative cov 1]

variable {h : M → E →L[ℝ] E →L[ℝ] ℝ}

omit [CompleteSpace E] in
-- BENCH: laplacian-metric-trace
/-- **`Δ(tr_g h) = tr_g(Δ_g h)`.** The metric trace commutes with the Laplacian, which is the
last identification the evolution of the scalar curvature needs: it turns the second of the two
canonical double traces of `∇²h` into the Laplacian of a function. Both sides are read off the
same frame --- the left by `laplacianFun_eq_sum_frame`, which is free because `∇²f` is `∇` of
the one-form `df`, and the right by `laplacianBilin_eq_sum_frame` --- and then it is
`hessianFun_traceBilin_eq` termwise plus one `Finset.sum_comm`. -/
theorem laplacianFun_traceBilin_eq
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hb : ∀ y : M, IsMDiffBilinAt (I := I) h y) {x : M}
    (hf : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I (traceBilin (I := I) h) y : TangentSpace I y →L[ℝ] ℝ)) x)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (b : OrthonormalBasis iota ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i)
    (hfr2 : ∀ i, CMDiff 2 (T% (fr i)))
    (hh : ∀ y ∈ u, ∀ i, MDiffAt (fun y' ↦ h y' (fr i y') (fr i y')) y)
    (hd : ∀ i j, MDiffAt (fun y ↦ cov.covBilin h (fr i) (fr j) (fr j) y) x)
    (hcb : ∀ j, cov.IsMDiffCovBilinAt h (fr j) (fr j) x) :
    cov.laplacianFun (traceBilin (I := I) h) x
      = ∑ j, cov.laplacianBilin h (fr j) (fr j) x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr2 i).mdifferentiable h2 x
  have step : ∀ i, cov.hessianFun (traceBilin (I := I) h) (fr i) (fr i) x
      = ∑ j, cov.cov2Bilin h (fr i) (fr i) (fr j) (fr j) x := fun i ↦
    cov.hessianFun_traceBilin_eq hcov hb (hfr1 i) (hfr2 i) hs hu hx hfr2 hh (hd i)
  rw [cov.laplacianFun_eq_sum_frame hf hfr1 b hbv,
    Finset.sum_congr rfl fun i _ ↦ step i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦
    (cov.laplacianBilin_eq_sum_frame (hb x) (hcb j) (hfr2 j) (hfr2 j) hfr2 b hbv).symm

end FunctionTrace


section BilinDivergence

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- A finite sum of tensorial scalar operations is tensorial. -/
theorem tensorialAt_sum {ι : Type*} {s : Finset ι}
    {Φ : ι → (Π y : M, TangentSpace I y) → ℝ} {x : M}
    (hΦ : ∀ i ∈ s, TensorialAt I E (Φ i) x) :
    TensorialAt I E (fun σ ↦ ∑ i ∈ s, Φ i σ) x where
  smul hf hσ := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i hi ↦ (hΦ i hi).smul hf hσ
  add hσ hσ' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi ↦ (hΦ i hi).add hσ hσ'

variable {h : M → E →L[ℝ] E →L[ℝ] ℝ}

/-- `∇h` traced in its **first two** slots, as a bilinear form on `T_xM` for a fixed third
field. The direction slot is tensorial with no hypotheses; the second needs `IsMDiffBilinAt`
and differentiability of `Z`. -/
noncomputable def covBilinFstSnd (hb : IsMDiffBilinAt (I := I) h x)
    {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Y ↦ cov.covBilin h X Y Z x) x
    (fun _ _ ↦ cov.tensorialAt_covBilin_dir _ Z x)
    (fun X _ ↦ cov.tensorialAt_covBilin_snd hb X hZ)

omit [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
theorem covBilinFstSnd_apply (hb : IsMDiffBilinAt (I := I) h x)
    {X Y Z : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    cov.covBilinFstSnd hb hZ (X x) (Y x) = cov.covBilin h X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

/-- **The divergence of a bilinear form field**, `(div h)(Z) = ∑ᵢ (∇_{eᵢ}h)(eᵢ, Z)`: the trace
of the `(0,3)`-tensor `∇h` in its first two slots. -/
noncomputable def divBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ) (Z : Π y : M, TangentSpace I y)
    (x : M) : ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  ∑ i, cov.covBilin h (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i))
    (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i)) Z x

omit [CompleteSpace E] in
/-- **`div h` is frame-independent**: it is the trace of a bilinear form. -/
theorem divBilin_eq_sum_basis (hb : IsMDiffBilinAt (I := I) h x)
    {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.divBilin h Z x = ∑ i, cov.covBilinFstSnd hb hZ (b i) (b i) := by
  have hfin : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  have hstd : cov.divBilin h Z x
      = ∑ i, cov.covBilinFstSnd hb hZ (stdOrthonormalBasis ℝ (TangentSpace I x) i)
          (stdOrthonormalBasis ℝ (TangentSpace I x) i) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hext := FiberBundle.mdifferentiableAt_extend I E
      (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    have hself : (FiberBundle.extend E (stdOrthonormalBasis ℝ (TangentSpace I x) i) : Π y : M,
        TangentSpace I y) x = stdOrthonormalBasis ℝ (TangentSpace I x) i :=
      FiberBundle.extend_apply_self ..
    have happ := cov.covBilinFstSnd_apply hb hext hext hZ
    rw [hself] at happ
    exact happ.symm
  rw [hstd]
  exact OrthonormalBasis.sum_apply_self_eq _ b (cov.covBilinFstSnd hb hZ)

omit [CompleteSpace E] in
/-- **`div h` read off any frame orthonormal at `x`.** -/
theorem divBilin_eq_sum_frame (hb : IsMDiffBilinAt (I := I) h x)
    {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x)
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (hfr : ∀ i, MDiffAt (T% (fr i)) x) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (hbv : ∀ i, fr i x = b i) :
    cov.divBilin h Z x = ∑ i, cov.covBilin h (fr i) (fr i) Z x := by
  rw [cov.divBilin_eq_sum_basis hb hZ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hbv i, cov.covBilinFstSnd_apply hb (hfr i) (hfr i) hZ]

omit [CompleteSpace E] in
/-- `div h` is tensorial in its remaining slot: a finite sum of the third-slot tensorialities
of `∇h`. -/
theorem tensorialAt_divBilin (hb : IsMDiffBilinAt (I := I) h x) :
    TensorialAt I E (fun Z ↦ cov.divBilin h Z x) x := by
  have : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E _ x
  exact tensorialAt_sum fun i _ ↦ cov.tensorialAt_covBilin_thd hb _
    (FiberBundle.mdifferentiableAt_extend I E (stdOrthonormalBasis ℝ (TangentSpace I x) i))

/-- **`div h` as a one-form on `T_xM`.** -/
noncomputable def divBilinForm (hb : IsMDiffBilinAt (I := I) h x) : E →L[ℝ] ℝ :=
  (TensorialAt.mkHom (fun Z ↦ cov.divBilin h Z x) x (cov.tensorialAt_divBilin hb) :
    TangentSpace I x →L[ℝ] ℝ)

omit [CompleteSpace E] in
theorem divBilinForm_apply (hb : IsMDiffBilinAt (I := I) h x)
    {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
    cov.divBilinForm hb (Z x) = cov.divBilin h Z x :=
  TensorialAt.mkHom_apply _ hZ

/-- **`h` is differentiable against differentiable fields everywhere.** The global form of
`IsMDiffBilinAt`, needed to make `div h` a one-form *field* rather than a covector at one
point --- which is what `div div h` differentiates. Implied by `h` being `C¹`. -/
def IsMDiffBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ x : M, IsMDiffBilinAt (I := I) h x

/-- **`div h` as a one-form field.** -/
noncomputable def divBilinOneForm (h : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : IsMDiffBilin (I := I) h) : M → E →L[ℝ] ℝ :=
  fun y ↦ cov.divBilinForm (hb y)

omit [CompleteSpace E] in
theorem divBilinOneForm_eq (hb : IsMDiffBilin (I := I) h) (y : M) :
    cov.divBilinOneForm h hb y = cov.divBilinForm (hb y) := rfl

/-- **`div div h`**, the double divergence of a bilinear form field: the divergence of the
one-form `div h`. This is the trace of `∇²h` pairing slots 1&3 and 2&4, obtained without any
four-linear packaging of `∇²h` --- `div h` is the 1&2 trace of the `(0,3)`-tensor `∇h`, and
`div` of a one-form needs no frame argument at all. -/
noncomputable def divDivBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ) (hb : IsMDiffBilin (I := I) h)
    (x : M) : ℝ :=
  cov.divOneForm (cov.divBilinOneForm h hb) x

/-- The bilinear form `(v,w) ↦ (∇_v h)(w, Z)` at each point, as a field: what `div h` is the
frame sum of, and what `TraceCov.lean`'s trace lemma differentiates. -/
noncomputable def divBilinAux (h : M → E →L[ℝ] E →L[ℝ] ℝ) (hb : IsMDiffBilin (I := I) h)
    {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z)) : M → E →L[ℝ] E →L[ℝ] ℝ :=
  fun y ↦ (cov.covBilinFstSnd (hb y) (hZ.mdifferentiable (by norm_num) y) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)

section DivCommutes

variable [ContMDiffCovariantDerivative cov 1]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

omit [CompleteSpace E] in
-- BENCH: divergence-commutes-with-cov
/-- **The divergence commutes with `∇`**: `(∇_W (div h))(Z) = ∑ᵢ (∇²_{W,eᵢ}h)(eᵢ, Z)`.
This is what identifies the iterated `div div h` with the double trace of `∇²h` that the
evolution of the scalar curvature produces. The proof is `TraceCov.lean`'s trace lemma applied
to `(v,w) ↦ (∇_v h)(w,Z)`: differentiating the frame sum produces `∇²h` plus exactly the term
`(div h)(∇_W Z)` that `∇_W` of a one-form subtracts, so the two cancel. -/
theorem covOneForm_divBilinOneForm_eq_sum
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hb : IsMDiffBilin (I := I) h) {Z W : Π y : M, TangentSpace I y}
    (hZ : CMDiff 2 (T% Z)) (hW : MDiffAt (T% W) x)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr2 : ∀ i, CMDiff 2 (T% (fr i)))
    (hB : ∀ i, MDiffAt (fun y ↦ cov.covBilin h (fr i) (fr i) Z y) x) :
    cov.covOneForm (cov.divBilinOneForm h hb) W Z x
      = ∑ i, cov.cov2Bilin h W (fr i) (fr i) Z x := by
  classical
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hZ1 : ∀ y, MDiffAt (T% Z) y := fun y ↦ hZ.mdifferentiable h2 y
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr2 i).mdifferentiable h2 x
  have hDfr : ∀ i, MDiffAt (T% (fun y ↦ cov (fr i) y (W y))) x := fun i ↦
    cov.mdiffAt_cov_apply (hfr2 i) hW
  have hDZ : MDiffAt (T% (fun y ↦ cov Z y (W y))) x := cov.mdiffAt_cov_apply hZ hW
  set B := cov.divBilinAux h hb hZ with hBdef
  obtain ⟨b, hbv⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  -- `B` computes `∇h` on the frame, pointwise over `u`
  have hBapp : ∀ y ∈ u, ∀ i, B y (fr i y) (fr i y) = cov.covBilin h (fr i) (fr i) Z y := by
    intro y hy i
    have hfy : MDiffAt (T% (fr i)) y :=
      (hs.toIsLocalFrameOn.contMDiffAt hu hy i).mdifferentiableAt one_ne_zero
    exact cov.covBilinFstSnd_apply (hb y) hfy hfy (hZ1 y)
  -- the one-form `div h` is the frame sum near `x`
  have hgerm : (fun y ↦ cov.divBilinOneForm h hb y (Z y))
      =ᶠ[𝓝 x] fun y ↦ ∑ i, B y (fr i y) (fr i y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    obtain ⟨c, hcv⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
    have hfy : ∀ i, MDiffAt (T% (fr i)) y := fun i ↦
      (hs.toIsLocalFrameOn.contMDiffAt hu hy i).mdifferentiableAt one_ne_zero
    rw [cov.divBilinOneForm_eq hb y]
    calc cov.divBilinForm (hb y) (Z y)
        = cov.divBilin h Z y := cov.divBilinForm_apply (hb y) (hZ1 y)
      _ = ∑ i, cov.covBilin h (fr i) (fr i) Z y :=
          cov.divBilin_eq_sum_frame (hb y) (hZ1 y) hfy c fun i ↦ (hcv i).symm
      _ = ∑ i, B y (fr i y) (fr i y) :=
          Finset.sum_congr rfl fun i _ ↦ (hBapp y hy i).symm
  have hBd : ∀ i, MDiffAt (fun y ↦ B y (fr i y) (fr i y)) x := by
    intro i
    refine (hB i).congr_of_eventuallyEq ?_
    filter_upwards [hu.mem_nhds hx] with y hy
    exact hBapp y hy i
  -- the leading term, by the trace lemma
  have hlead : mvfderiv I (fun y ↦ cov.divBilinOneForm h hb y (Z y)) x (W x)
      = ∑ i, cov.covBilin B W (fr i) (fr i) x := by
    rw [hgerm.mvfderiv_eq]
    exact cov.mvfderiv_sum_eq_sum_covBilin_of_frame hcov hs hu hx hBd
  -- each summand is `∇²h` plus the term that `∇_W` of a one-form subtracts
  have hexpand : ∀ i, cov.covBilin B W (fr i) (fr i) x
      = cov.cov2Bilin h W (fr i) (fr i) Z x
        + cov.covBilin h (fr i) (fr i) (fun y ↦ cov Z y (W y)) x := by
    intro i
    have hmg : (fun y ↦ B y (fr i y) (fr i y))
        =ᶠ[𝓝 x] fun y ↦ cov.covBilin h (fr i) (fr i) Z y := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact hBapp y hy i
    have hm' : mvfderiv I (fun y ↦ B y (fr i y) (fr i y)) x (W x)
        = mvfderiv I (fun y ↦ cov.covBilin h (fr i) (fr i) Z y) x (W x) := by
      rw [hmg.mvfderiv_eq]
    have e1 : B x (cov (fr i) x (W x)) (fr i x)
        = cov.covBilin h (fun y ↦ cov (fr i) y (W y)) (fr i) Z x :=
      cov.covBilinFstSnd_apply (hb x) (hDfr i) (hfr1 i) (hZ1 x)
    have e2 : B x (fr i x) (cov (fr i) x (W x))
        = cov.covBilin h (fr i) (fun y ↦ cov (fr i) y (W y)) Z x :=
      cov.covBilinFstSnd_apply (hb x) (hfr1 i) (hDfr i) (hZ1 x)
    have hcB : cov.covBilin B W (fr i) (fr i) x
        = mvfderiv I (fun y ↦ B y (fr i y) (fr i y)) x (W x)
          - B x (cov (fr i) x (W x)) (fr i x) - B x (fr i x) (cov (fr i) x (W x)) := rfl
    have hc2 : cov.cov2Bilin h W (fr i) (fr i) Z x
        = mvfderiv I (fun y ↦ cov.covBilin h (fr i) (fr i) Z y) x (W x)
          - cov.covBilin h (fun y ↦ cov (fr i) y (W y)) (fr i) Z x
          - cov.covBilin h (fr i) (fun y ↦ cov (fr i) y (W y)) Z x
          - cov.covBilin h (fr i) (fr i) (fun y ↦ cov Z y (W y)) x := rfl
    rw [hcB, hc2, hm', e1, e2]
    ring
  -- The subtracted term of `∇_W ω` is the frame sum of the same quantity. The value is passed
  -- explicitly: matching `divBilinForm_apply` against a beta-redex sends the unifier through
  -- `mkHom` into the trivialisations behind `FiberBundle.extend`, and it does not come back.
  have key : ∀ (v : TangentSpace I x) (V : Π y : M, TangentSpace I y), MDiffAt (T% V) x →
      V x = v → cov.divBilinForm (hb x) v = ∑ i, cov.covBilin h (fr i) (fr i) V x := by
    intro v V hVd hVv
    rw [← hVv, cov.divBilinForm_apply (hb x) hVd]
    exact cov.divBilin_eq_sum_frame (hb x) hVd hfr1 b fun i ↦ (hbv i).symm
  have hsub : cov.divBilinOneForm h hb x (cov Z x (W x))
      = ∑ i, cov.covBilin h (fr i) (fr i) (fun y ↦ cov Z y (W y)) x := by
    rw [cov.divBilinOneForm_eq hb x]
    exact key (cov Z x (W x)) (fun y ↦ cov Z y (W y)) hDZ rfl
  simp only [covOneForm]
  rw [hlead, hsub, Finset.sum_congr rfl fun i _ ↦ hexpand i, Finset.sum_add_distrib]
  ring

omit [CompleteSpace E] in
-- BENCH: div-div-bilin-double-trace
/-- **`div div h` is the double trace of `∇²h`**:
`div div h = ∑_{j,i} (∇²_{eⱼ,eᵢ}h)(eᵢ, eⱼ)`. This is the form the evolution of the scalar
curvature produces, and it is reached without ever packaging `∇²h` as a four-linear map: the
outer trace is `div` of a one-form and the inner one is the previous lemma. -/
theorem divDivBilin_eq_sum
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hb : IsMDiffBilin (I := I) h)
    (hw : IsMDiffOneFormAt (I := I) (cov.divBilinOneForm h hb) x)
    {iota : Type*} [Fintype iota] {fr : iota → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr2 : ∀ i, CMDiff 2 (T% (fr i)))
    (hB : ∀ j i, MDiffAt (fun y ↦ cov.covBilin h (fr i) (fr i) (fr j) y) x)
    (b : OrthonormalBasis iota ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i) :
    cov.divDivBilin h hb x
      = ∑ j, ∑ i, cov.cov2Bilin h (fr j) (fr i) (fr i) (fr j) x := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr2 i).mdifferentiable h2 x
  rw [divDivBilin, cov.divOneForm_eq_sum_frame hw hfr1 b hbv]
  exact Finset.sum_congr rfl fun j _ ↦
    cov.covOneForm_divBilinOneForm_eq_sum hcov hb (hfr2 j) (hfr1 j) hs hu hx hfr2 (hB j)

end DivCommutes

end BilinDivergence

end CovariantDerivative
