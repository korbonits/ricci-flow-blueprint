/-
**Normal sections of a general vector bundle.**

`NormalSection.lean` builds, for every `v ∈ T_xM`, a global `C²` vector field `N` with
`N x = v`, `∇N(x) = 0` and `ΔN(x) = 0`. Hamilton's maximum principle needs the same thing
for a section of `Sym²(Λ²TM)`, so this file redoes it one bundle up.

The construction is unchanged and still uses **no parallel transport and no exponential
map**: only first- and second-order agreement at a single point is wanted, and that is
linear algebra over an orthonormal basis of the single fibre `V x`.

**One thing does change, and it is the only interesting difference.** In the tangent case
the family `Wᵢ` of correction sections and the frame the Laplacian is traced over are the
*same* family, so the second-order step reads `∑ⱼ⟪bᵢ,bⱼ⟫² = 1` off orthonormality. Here they
live in different bundles: the corrections `Wᵢ` run through an orthonormal basis of `V x`,
while the trace runs over an orthonormal basis of `T_xM`. What replaces the identity is the
observation that a *single* function `g` suffices — `∇²(½a·g²)(x)(X,Y) = a·dg(X)·dg(Y)`, so
tracing gives `a·∑ⱼ dg(Eⱼ)²`, which is `a` as soon as `dg(x)` is a unit covector. Taking
`dg(x) = ⟪E_{j₀},·⟫` for any one frame vector does it, and the whole correction needs one `g`
rather than a family.

That leaves an edge case the tangent version never had: when `T_xM` is zero there is no unit
covector. But then `Δ` is an empty sum, so `ΔN₁(x) = 0` already and nothing has to be
corrected — which is how the case is discharged.
-/
import RicciFlowBlueprint.BundleHessian
import RicciFlowBlueprint.NormalSection

open Bundle Filter CovariantDerivative
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, NormedAddCommGroup (V x)] [∀ x : M, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : CovariantDerivative I F V)

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ω M] [FiniteDimensional ℝ F] in
/-- `∇` over a finite sum `∑ᵢ cᵢ • Wᵢ` of sections of `V`. The general-bundle form of
`cov_sum_smul_section_apply`; the induction is mathlib's Leibniz rule at every step. -/
theorem cov_sum_smul_section_apply_of_bundle {ι : Type*} (a : Finset ι)
    {c : ι → M → ℝ} {W : ι → Π y : M, V y} {x : M}
    (hc : ∀ i ∈ a, MDifferentiableAt I 𝓘(ℝ, ℝ) (c i) x)
    (hW : ∀ i ∈ a, MDiffAt (T% (W i)) x) (v : TangentSpace I x) :
    cov (fun y ↦ ∑ i ∈ a, c i y • W i y) x v
      = ∑ i ∈ a, (c i x • cov (W i) x v + mvfderiv I (c i) x v • W i x) := by
  classical
  induction a using Finset.induction with
  | empty =>
    have h0 : (fun y ↦ ∑ i ∈ (∅ : Finset ι), c i y • W i y) = (0 : Π y : M, V y) := by
      funext y; exact Finset.sum_empty
    rw [h0, Finset.sum_empty, cov.zero]
    rfl
  | insert j a hj ih =>
    have hjm := Finset.mem_insert_self j a
    have hstep : (fun y ↦ ∑ i ∈ insert j a, c i y • W i y)
        = (c j • W j) + fun y ↦ ∑ i ∈ a, c i y • W i y := by
      funext y
      show ∑ i ∈ insert j a, c i y • W i y = c j y • W j y + ∑ i ∈ a, c i y • W i y
      exact Finset.sum_insert hj
    have hrest : MDiffAt (T% (fun y ↦ ∑ i ∈ a, c i y • W i y)) x :=
      MDifferentiableAt.sum_section fun i hi ↦
        (hc i (Finset.mem_insert_of_mem hi)).smul_section (hW i (Finset.mem_insert_of_mem hi))
    rw [hstep, cov.isCovariantDerivativeOn.add
        ((hc j hjm).smul_section (hW j hjm)) hrest,
      cov.isCovariantDerivativeOn.leibniz (hW j hjm) (hc j hjm), Finset.sum_insert hj,
      ← ih (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hW i (Finset.mem_insert_of_mem hi)]
    rfl

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ω M] [FiniteDimensional ℝ F] in
/-- `∇` over a finite sum of sections of `V`. -/
theorem cov_sum_section_apply_of_bundle {ι : Type*} (a : Finset ι) {Zs : ι → Π y : M, V y}
    {y : M} (h : ∀ i ∈ a, MDiffAt (T% (Zs i)) y) (v : TangentSpace I y) :
    cov (fun z ↦ ∑ i ∈ a, Zs i z) y v = ∑ i ∈ a, cov (Zs i) y v := by
  have hc : ∀ i ∈ a, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M ↦ (1 : ℝ)) y :=
    fun _ _ ↦ mdifferentiableAt_const
  have := cov_sum_smul_section_apply_of_bundle cov a (c := fun _ _ ↦ (1 : ℝ)) hc h v
  have hd : mvfderiv I (fun _ : M ↦ (1 : ℝ)) y = 0 := mvfderiv_const 1
  simpa [hd] using this

-- BENCH: bundle-normal-section-first
/-- **A globally `C^k` section of `V` through a prescribed `v ∈ V x` with `∇N(x) = 0`.**
The first-order half, verbatim from the tangent case with the orthonormal basis taken in the
fibre `V x` instead of `T_xM`. -/
theorem exists_contMDiff_section_cov_eq_zero_of_bundle {n : ℕ∞}
    [ContMDiffVectorBundle (n : ℕ∞ω) F V I] (hn : n ≠ 0) {x : M} (v : V x) :
    ∃ N : Π y : M, V y, CMDiff (n : ℕ∞ω) (T% N) ∧ N x = v ∧ cov N x = 0 := by
  classical
  have : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨Ñ, hÑ, hÑx⟩ := exists_contMDiff_extension_of_bundle (I := I) (n := n) F v
  set b := stdOrthonormalBasis ℝ (V x) with hb
  set A : TangentSpace I x →L[ℝ] V x := cov Ñ x with hA
  have hW : ∀ i, ∃ W : Π y : M, V y, CMDiff (n : ℕ∞ω) (T% W) ∧ W x = b i :=
    fun i ↦ exists_contMDiff_extension_of_bundle (I := I) (n := n) F (b i)
  choose W hWreg hWx using hW
  have hf : ∀ i, ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) (n : ℕ∞ω) f ∧ f x = 0 ∧
      mvfderiv I f x = -((innerSL ℝ (b i)).comp A) :=
    fun i ↦ exists_contMDiff_fun_mvfderiv_eq (n := n) _
  choose f hfreg hfx hfd using hf
  have hsum : CMDiff (n : ℕ∞ω) (T% (fun y ↦ ∑ i, f i y • W i y)) :=
    ContMDiff.sum_section fun i _ ↦ (hfreg i).smul_section (hWreg i)
  have hÑd : MDiffAt (T% Ñ) x := hÑ.mdifferentiableAt (by exact_mod_cast hn)
  have hsplit : (fun y ↦ Ñ y + ∑ i, f i y • W i y) = Ñ + (fun y ↦ ∑ i, f i y • W i y) := rfl
  refine ⟨fun y ↦ Ñ y + ∑ i, f i y • W i y, ?_, ?_, ?_⟩
  · rw [hsplit]; exact hÑ.add_section hsum
  · simp only [hfx, zero_smul, Finset.sum_const_zero, add_zero, hÑx]
  · rw [hsplit, cov.isCovariantDerivativeOn.add hÑd (hsum.mdifferentiableAt
      (by exact_mod_cast hn))]
    ext u
    have hsm := cov_sum_smul_section_apply_of_bundle cov Finset.univ
      (fun i _ ↦ (hfreg i).mdifferentiableAt (by exact_mod_cast hn))
      (fun i _ ↦ (hWreg i).mdifferentiableAt (by exact_mod_cast hn)) u
    show A u + cov (fun y ↦ ∑ i, f i y • W i y) x u = 0
    rw [hsm]
    have hterm : ∀ i, f i x • cov (W i) x u + mvfderiv I (f i) x u • W i x
        = -(⟪b i, A u⟫ • b i) := by
      intro i
      rw [hfx i, hWx i, zero_smul, zero_add, hfd i]
      simp
    simp only [hterm]
    have hneg : ∑ i, -(⟪b i, A u⟫ • b i) = -∑ i, ⟪b i, A u⟫ • b i := by simp
    rw [hneg, b.sum_repr' (A u)]
    abel

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, NormedAddCommGroup (V x)] [∀ x : M, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I F V)
  (covT : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ F] in
/-- `∇_Y σ` is globally `C^k` for a `C^k` connection, a `C^{k+1}` section of `V` and a `C^k`
vector field. The general-bundle form of `contMDiff_cov_apply`. -/
lemma contMDiff_cov_apply_section {k : ℕ∞ω} [ContMDiffCovariantDerivative cov k]
    {σ : Π y : M, V y} {Y : Π y : M, TangentSpace I y}
    (hσ : CMDiff (k + 1) (T% σ)) (hY : CMDiff k (T% Y)) :
    CMDiff k (T% (fun y ↦ cov σ y (Y y))) := by
  have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) k
      (fun y : M ↦ (⟨y, cov σ y⟩ :
        TotalSpace (E →L[ℝ] F) fun y ↦ (TangentSpace I y →L[ℝ] V y))) Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := k)).contMDiff hσ.contMDiffOn
  intro y
  have h1 : CMDiffAt k (fun y : M ↦ (TotalSpace.mk' (E →L[ℝ] F)
      (E := fun y : M ↦ (TangentSpace I y →L[ℝ] V y)) y (cov σ y))) y := by
    have h := hcovσ y (Set.mem_univ y)
    rw [contMDiffWithinAt_univ] at h
    exact h
  exact h1.clm_bundle_apply (hY y)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ F] in
/-- **`∇²(f • W) = (∇²f) • W` at a point where `f` and `df` both vanish**, for a section `W`
of `V`. Leibniz produces three corrections beyond the leading term and each carries a factor
`f x` or `df x`. By the same token `∇(f • W)(x) = 0`, which is what lets a second-order
correction be added without disturbing a first-order condition already arranged. -/
theorem hessianSection_smul_of_vanishing {f : M → ℝ} {W : Π y : M, V y}
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hfx : f x = 0) (hdf : mvfderiv I f x = 0)
    (hf : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) f y) (hW : ∀ y, MDiffAt (T% W) y)
    (hcw : MDiffAt (T% (fun y ↦ cov W y (Y y))) x)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ mvfderiv I f y (Y y)) x) :
    cov.hessianSection covT X Y (f • W) x = covT.hessianFun f X Y x • W x := by
  have h2 : cov (f • W) x = 0 := by
    rw [cov.isCovariantDerivativeOn.leibniz (hW x) (hf x), hfx, hdf, zero_smul,
      ContinuousLinearMap.zero_smulRight, add_zero]
  have hsplit : (fun y ↦ cov (f • W) y (Y y))
      = f • (fun y ↦ cov W y (Y y)) + (fun y ↦ mvfderiv I f y (Y y)) • W := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (hW y) (hf y)]
    show f y • cov W y (Y y) + (mvfderiv I f y).smulRight (W y) (Y y)
      = f y • cov W y (Y y) + mvfderiv I f y (Y y) • W y
    rw [ContinuousLinearMap.smulRight_apply]
  show cov (fun y ↦ cov (f • W) y (Y y)) x (X x) - cov (f • W) x (covT Y x (X x)) = _
  rw [h2, hsplit]
  have hd1 : MDiffAt (T% (f • (fun y ↦ cov W y (Y y)))) x := (hf x).smul_section hcw
  have hd2 : MDiffAt (T% ((fun y ↦ mvfderiv I f y (Y y)) • W)) x := hu.smul_section (hW x)
  rw [cov.isCovariantDerivativeOn.add hd1 hd2,
    cov.isCovariantDerivativeOn.leibniz hcw (hf x),
    cov.isCovariantDerivativeOn.leibniz (hW x) hu]
  simp only [ContinuousLinearMap.smulRight_apply, hfx, hdf, zero_smul,
    zero_apply, zero_add, add_zero, ContinuousLinearMap.zero_smulRight, sub_zero]
  rw [hessianFun, hdf]
  simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [VectorBundle ℝ F V] in
/-- **`∇²` is additive in its section slot**, two-term case, for sections of `V`. -/
theorem hessianSection_add {Z Z' : Π y : M, V y} {X Y : Π y : M, TangentSpace I y} {x : M}
    (hZ : ∀ y, MDiffAt (T% Z) y) (hZ' : ∀ y, MDiffAt (T% Z') y)
    (h1 : MDiffAt (T% (fun z ↦ cov Z z (Y z))) x)
    (h2 : MDiffAt (T% (fun z ↦ cov Z' z (Y z))) x) :
    cov.hessianSection covT X Y (fun y ↦ Z y + Z' y) x
      = cov.hessianSection covT X Y Z x + cov.hessianSection covT X Y Z' x := by
  have hadd : (fun y : M ↦ Z y + Z' y) = Z + Z' := rfl
  have hσ : (fun y ↦ cov (fun z ↦ Z z + Z' z) y (Y y))
      = (fun z ↦ cov Z z (Y z)) + (fun z ↦ cov Z' z (Y z)) := by
    funext y
    rw [hadd, cov.isCovariantDerivativeOn.add (hZ y) (hZ' y)]
    rfl
  show cov (fun y ↦ cov (fun z ↦ Z z + Z' z) y (Y y)) x (X x)
      - cov (fun z ↦ Z z + Z' z) x (covT Y x (X x)) = _
  rw [hσ, cov.isCovariantDerivativeOn.add h1 h2, hadd,
    cov.isCovariantDerivativeOn.add (hZ x) (hZ' x)]
  simp only [_root_.add_apply, hessianSection]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ F] in
/-- **`∇²` is additive over a finite sum of sections of `V`.** -/
theorem hessianSection_sum {ι : Type*} (a : Finset ι) {Zs : ι → Π y : M, V y}
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hZ : ∀ i ∈ a, ∀ y, MDiffAt (T% (Zs i)) y)
    (hcz : ∀ i ∈ a, MDiffAt (T% (fun z ↦ cov (Zs i) z (Y z))) x) :
    cov.hessianSection covT X Y (fun y ↦ ∑ i ∈ a, Zs i y) x
      = ∑ i ∈ a, cov.hessianSection covT X Y (Zs i) x := by
  have hσ : (fun y ↦ cov (fun z ↦ ∑ i ∈ a, Zs i z) y (Y y))
      = fun y ↦ ∑ i ∈ a, cov (Zs i) y (Y y) := by
    funext y
    exact cov_sum_section_apply_of_bundle cov a (fun i hi ↦ hZ i hi y) (Y y)
  show cov (fun y ↦ cov (fun z ↦ ∑ i ∈ a, Zs i z) y (Y y)) x (X x)
      - cov (fun z ↦ ∑ i ∈ a, Zs i z) x (covT Y x (X x)) = _
  rw [hσ, cov_sum_section_apply_of_bundle cov a hcz (X x),
    cov_sum_section_apply_of_bundle cov a (fun i hi ↦ hZ i hi x) (covT Y x (X x)),
    ← Finset.sum_sub_distrib]
  rfl

variable [ContMDiffCovariantDerivative cov 1] [ContMDiffVectorBundle 2 F V I]

omit [CompleteSpace E] in
-- BENCH: bundle-normal-section
/-- **A global `C²` section of `V` through a prescribed `v ∈ V x` with `∇N(x) = 0` AND
`ΔN(x) = 0`** — the primitive Hamilton's maximum principle needs on a non-trivial bundle.

Two stages that do not interact. `exists_contMDiff_section_cov_eq_zero_of_bundle` supplies
`N₁`; the correction `∑ᵢ (aᵢ/2)·g² · Wᵢ` is then added with `aᵢ = −⟪bᵢ, ΔN₁(x)⟫`, the `Wᵢ`
running through an orthonormal basis of the fibre `V x`. Each summand vanishes to second
order at `x`, so it disturbs neither the value nor the covariant derivative already
arranged, while contributing `a ·dg⊗dg · Wᵢ(x)` to the Hessian.

**One function `g` suffices, not a family** — this is where the general-bundle case is
*simpler* than the tangent one. There the correction sections and the frame the trace runs
over are the same family, and the collapse `∑ⱼ⟪bᵢ,bⱼ⟫² = 1` is orthonormality of that one
basis. Here the two live in different bundles, and what replaces it is that tracing
`a·dg⊗dg` gives `a·∑ⱼ dg(Eⱼ)²`, which is `a` as soon as `dg(x)` is a *unit covector* on
`T_xM` — so a single `g` with `dg(x) = ⟪E_{j₀},·⟫` corrects every component at once.

The degenerate case is `T_xM = 0`, where no unit covector exists; there `Δ` is an empty sum,
`ΔN₁(x) = 0` already, and `N₁` itself is the answer. -/
theorem exists_contMDiff_section_normal_of_bundle {x : M} (v : V x) :
    ∃ (N : Π y : M, V y) (hN : CMDiff 2 (T% N)),
      N x = v ∧ cov N x = 0 ∧ cov.laplacianSection covT hN x = 0 := by
  classical
  have hfinV : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  have hfinT : FiniteDimensional ℝ (TangentSpace I x) := VectorBundle.finiteDimensional ℝ E _ x
  obtain ⟨N₁, hN₁, hN₁x, hN₁c⟩ :=
    exists_contMDiff_section_cov_eq_zero_of_bundle cov (n := 2) two_ne_zero v
  set Efr := stdOrthonormalBasis ℝ (TangentSpace I x) with hEfr
  rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) with hemp | hne
  · -- `T_xM = 0`: the trace defining `Δ` is an empty sum
    have := hemp
    refine ⟨N₁, hN₁, hN₁x, hN₁c, ?_⟩
    rw [cov.laplacianSection_eq_sum covT hN₁ Efr]
    simp
  obtain ⟨j₀⟩ := hne
  set e : TangentSpace I x := Efr j₀ with he
  set b := stdOrthonormalBasis ℝ (V x) with hb
  set w := cov.laplacianSection covT hN₁ x with hw
  have hWex : ∀ i, ∃ W : Π y : M, V y, CMDiff 2 (T% W) ∧ W x = b i :=
    fun i ↦ exists_contMDiff_extension_of_bundle (I := I) (n := 2) F (b i)
  choose W hWreg hWx using hWex
  have hEex : ∀ j, ∃ Z : Π y : M, TangentSpace I y, CMDiff 2 (T% Z) ∧ Z x = Efr j :=
    fun j ↦ RicciFlowBlueprint.exists_contMDiff_two_extension (Efr j)
  choose Efield hEreg hEx using hEex
  obtain ⟨g, hgreg, hgx, hgd⟩ :=
    RicciFlowBlueprint.exists_contMDiff_fun_mvfderiv_eq (n := 2) (innerSL ℝ e)
  set a : _ → ℝ := fun i ↦ -⟪b i, w⟫ with ha
  set f : _ → M → ℝ := fun i y ↦ a i / 2 * (g y * g y) with hf
  have hfreg : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) 2 (f i) := by
    intro i
    have hq : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 (fun r : ℝ ↦ a i / 2 * (r * r)) :=
      (contDiff_const.mul (contDiff_id.mul contDiff_id)).contMDiff.of_le le_top
    exact hq.comp hgreg
  have hfx : ∀ i, f i x = 0 := by intro i; simp [hf, hgx]
  have hgmd : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) g y := fun y ↦ hgreg.mdifferentiableAt two_ne_zero
  have hfd : ∀ i, mvfderiv I (f i) x = 0 := by
    intro i
    rw [hf]
    simp only
    rw [mvfderiv_half_sq (a i) (hgmd x), hgx, mul_zero, zero_smul]
  set S : Π y : M, V y := fun y ↦ ∑ i, f i y • W i y with hS
  have hSreg : CMDiff 2 (T% S) := ContMDiff.sum_section fun i _ ↦ (hfreg i).smul_section (hWreg i)
  have hN : CMDiff 2 (T% (fun y ↦ N₁ y + S y)) := hN₁.add_section hSreg
  have hfmd : ∀ i, ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) y :=
    fun i y ↦ (hfreg i).mdifferentiableAt two_ne_zero
  have hWmd : ∀ i, ∀ y, MDiffAt (T% (W i)) y := fun i y ↦ (hWreg i).mdifferentiableAt two_ne_zero
  have hW1 : ∀ i, CMDiff 1 (T% (W i)) := fun i ↦ (hWreg i).of_le (by norm_num)
  have hE1 : ∀ j, CMDiff 1 (T% (Efield j)) := fun j ↦ (hEreg j).of_le (by norm_num)
  have hSx : S x = 0 := by rw [hS]; simp [hfx]
  have hcovS : cov S x = 0 := by
    ext u
    have hsm := cov_sum_smul_section_apply_of_bundle cov Finset.univ
      (fun i _ ↦ hfmd i x) (fun i _ ↦ hWmd i x) u
    show cov (fun y ↦ ∑ i, f i y • W i y) x u = 0
    rw [hsm]
    simp [hfx, hfd]
  refine ⟨fun y ↦ N₁ y + S y, hN, ?_, ?_, ?_⟩
  · show N₁ x + S x = v
    rw [hSx, add_zero, hN₁x]
  · show cov (N₁ + S) x = 0
    rw [(cov.isCovariantDerivativeOn (s := Set.univ)).add (hN₁.mdifferentiableAt two_ne_zero)
      (hSreg.mdifferentiableAt two_ne_zero) (Set.mem_univ x), hN₁c, hcovS, add_zero]
  · have hfr : ∀ j, MDiffAt (T% (Efield j)) x :=
      fun j ↦ (hEreg j).mdifferentiableAt two_ne_zero
    have hterm : ∀ i j, cov.hessianSection covT (Efield j) (Efield j)
        (fun y ↦ f i y • W i y) x = (a i * ⟪e, Efr j⟫ * ⟪e, Efr j⟫) • b i := by
      intro i j
      have hcw : MDiffAt (T% (fun z ↦ cov (W i) z (Efield j z))) x :=
        (cov.contMDiff_cov_apply_section (k := 1) (hWreg i)
          (hE1 j)).mdifferentiableAt one_ne_zero
      have hu : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ mvfderiv I (f i) y (Efield j y)) x :=
        (contMDiffAt_mvfderiv_apply (n := 2) (m := 1) ((hfreg i) x) ((hE1 j) x)
          (by norm_num)).mdifferentiableAt one_ne_zero
      have hgu : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ mvfderiv I g y (Efield j y)) x :=
        (contMDiffAt_mvfderiv_apply (n := 2) (m := 1) (hgreg x) ((hE1 j) x)
          (by norm_num)).mdifferentiableAt one_ne_zero
      show cov.hessianSection covT (Efield j) (Efield j) (f i • W i) x = _
      rw [cov.hessianSection_smul_of_vanishing covT (hfx i) (hfd i) (hfmd i) (hWmd i) hcw hu]
      rw [show covT.hessianFun (f i) (Efield j) (Efield j) x
          = covT.hessianFun (fun y ↦ a i / 2 * (g y * g y)) (Efield j) (Efield j) x from rfl,
        covT.hessianFun_half_sq (a i) hgx hgmd hgu, hgd, hEx j, hWx i]
      rfl
    have hsplit : ∀ j, cov.hessianSection covT (Efield j) (Efield j)
        (fun y ↦ N₁ y + S y) x
        = cov.hessianSection covT (Efield j) (Efield j) N₁ x
          + ∑ i, (a i * ⟪e, Efr j⟫ * ⟪e, Efr j⟫) • b i := by
      intro j
      have hc1 : MDiffAt (T% (fun z ↦ cov N₁ z (Efield j z))) x :=
        (cov.contMDiff_cov_apply_section (k := 1) hN₁ (hE1 j)).mdifferentiableAt one_ne_zero
      have hc2 : MDiffAt (T% (fun z ↦ cov S z (Efield j z))) x :=
        (cov.contMDiff_cov_apply_section (k := 1) hSreg (hE1 j)).mdifferentiableAt one_ne_zero
      rw [cov.hessianSection_add covT (fun _ ↦ hN₁.mdifferentiableAt two_ne_zero)
        (fun _ ↦ hSreg.mdifferentiableAt two_ne_zero) hc1 hc2]
      congr 1
      have hZs : ∀ i ∈ (Finset.univ : Finset _), ∀ y,
          MDiffAt (T% (fun z ↦ f i z • W i z)) y :=
        fun i _ _ ↦ ((hfreg i).smul_section (hWreg i)).mdifferentiableAt two_ne_zero
      have hcz : ∀ i ∈ (Finset.univ : Finset _),
          MDiffAt (T% (fun z ↦ cov (fun y ↦ f i y • W i y) z (Efield j z))) x :=
        fun i _ ↦ (cov.contMDiff_cov_apply_section (k := 1)
          ((hfreg i).smul_section (hWreg i)) (hE1 j)).mdifferentiableAt one_ne_zero
      show cov.hessianSection covT (Efield j) (Efield j) (fun y ↦ ∑ i, f i y • W i y) x = _
      rw [cov.hessianSection_sum covT Finset.univ hZs hcz]
      exact Finset.sum_congr rfl fun i _ ↦ hterm i j
    rw [cov.laplacianSection_eq_sum_frame covT hN hfr Efr hEx,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) ↦ hsplit j), Finset.sum_add_distrib,
      ← cov.laplacianSection_eq_sum_frame covT hN₁ hfr Efr hEx, ← hw]
    have hinner : ∀ j, (⟪e, Efr j⟫ : ℝ) = if j₀ = j then 1 else 0 := fun j ↦
      orthonormal_iff_ite.mp Efr.orthonormal j₀ j
    have hdiag : ∑ j, ∑ i, (a i * ⟪e, Efr j⟫ * ⟪e, Efr j⟫) • b i = ∑ i, a i • b i := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_smul]
      congr 1
      simp [hinner]
    rw [hdiag, ha]
    simp only [neg_smul, Finset.sum_neg_distrib]
    rw [b.sum_repr' w, add_neg_cancel]

end CovariantDerivative
