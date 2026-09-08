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
import RicciFlowBlueprint.BilinDeriv

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

end Divergence

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

/-- **`div div h`**, the double divergence of a bilinear form field: the divergence of the
one-form `div h`. This is the trace of `∇²h` pairing slots 1&3 and 2&4, obtained without any
four-linear packaging of `∇²h` --- `div h` is the 1&2 trace of the `(0,3)`-tensor `∇h`, and
`div` of a one-form needs no frame argument at all. -/
noncomputable def divDivBilin (h : M → E →L[ℝ] E →L[ℝ] ℝ) (hb : IsMDiffBilin (I := I) h)
    (x : M) : ℝ :=
  cov.divOneForm (cov.divBilinOneForm h hb) x

end BilinDivergence

end CovariantDerivative
