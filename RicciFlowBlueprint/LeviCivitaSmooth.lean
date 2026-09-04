/-
Smoothness of the Levi-Civita connection.

Mathlib constructs `leviCivitaConnection I M` but (as of September 2026) does not
prove it is `C^n`. This file supplies that: if the manifold is `C^{n+2}` and the
metric is `C^{n+1}`, the Levi-Civita connection is a `C^n` covariant derivative.

## Strategy

`ContMDiffCovariantDerivative cov n` asks that for every `C^{n+1}` section `Y`,
`x ↦ ∇Y(x) ∈ Hom(T_xM, T_xM)` is a `C^n` section of the endomorphism bundle. In a
local trivialisation `e` of `TM` with frame `sᵢ = e.localFrame b i`:

1. a map into `E →L[ℝ] F` is `C^n` iff its values on a basis are
   (`contMDiffAt_clm_of_basis`);
2. a section `w` of a Riemannian bundle is `C^n` at `x₀` if the scalar functions
   `⟪w, sⱼ⟫` are — the coordinate metric `h x u v = ⟪e.symm x u, e.symm x v⟫` is a
   smooth invertible map into `E →L E →L ℝ`, and `w` in coordinates is `h⁻¹` applied
   to `(⟪w, sⱼ⟫)ⱼ` (`contMDiffAt_section_of_inner_localFrame`);
3. `⟪∇_{sᵢ} Y, sⱼ⟫` is the Koszul expression, whose terms are derivatives of
   inner products and inner products with brackets, all `C^n`
   (`contMDiffAt_koszul`);
4. assemble.
-/
import RicciFlowBlueprint.LeviCivita
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Hom

open Bundle CovariantDerivative Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

section ClmOfBasis

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- A map into `F →L[ℝ] G` (with `F` finite-dimensional) is `C^n` at a point as soon as
its values on a basis of `F` are. -/
theorem contMDiffAt_clm_of_basis [FiniteDimensional ℝ F] (b : Module.Basis ι ℝ F)
    {A : M → F →L[ℝ] G} {x₀ : M}
    (h : ∀ i, ContMDiffAt I 𝓘(ℝ, G) n (fun x ↦ A x (b i)) x₀) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] G) n A x₀ := by
  have hA : A = fun x ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ F G
      (LinearMap.toContinuousLinearMap (b.coord i)) (A x (b i)) := by
    funext x
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simp [ContinuousLinearMap.smulRightL_apply_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Finsupp.single_eq_of_ne hij]
    · simp
  rw [hA]
  apply contMDiffAt_finsetSum
  intro i _
  exact contMDiffAt_const.clm_apply (h i)

end ClmOfBasis

section InnerFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsContMDiffRiemannianBundle I n F V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ F] in
/-- **Smoothness of a section from its inner products with a local frame.** On a
Riemannian bundle with `C^n` metric, a section `w` is `C^n` at `x₀` as soon as the scalar
functions `x ↦ ⟪w x, sⱼ x⟫` are, where `sⱼ` is the local frame induced by the
trivialisation at `x₀` and a basis of the model fibre.

Proof: in the trivialisation, `w` has coordinate vector `c` with `G c = (⟪w, sⱼ⟫)ⱼ` for the
Gram operator `G` of the frame; `G` is smooth and invertible on the base set, and
`ContinuousLinearMap.inverse` is smooth at invertible points (`contDiffAt_map_inverse`). -/
theorem contMDiffAt_section_of_inner_localFrame (b : Module.Basis ι ℝ F) {x₀ : M}
    {w : Π x, V x}
    (h : ∀ i, ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun x ↦ ⟪w x, (trivializationAt F V x₀).localFrame b i x⟫) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (w x)) x₀ := by
  set e := trivializationAt F V x₀ with he
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  set s : ι → Π x, V x := e.localFrame b with hs_def
  have hs : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (s i x)) x₀ :=
    fun i ↦ contMDiffAt_localFrame_of_mem n e b i hx₀
  have hs_eq : ∀ i, ∀ x ∈ e.baseSet, s i x = e.symmL ℝ x (b i) := by
    intro i x hx
    simp [s, e.localFrame_apply_of_mem_baseSet b hx, Trivialization.basisAt,
      Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply, e.symmL_apply hx]
  -- the Gram operator of the frame, acting on coefficient vectors
  let G : M → (ι → ℝ) →L[ℝ] (ι → ℝ) := fun x ↦
    ContinuousLinearMap.pi fun j ↦ ∑ i, ⟪s i x, s j x⟫ • ContinuousLinearMap.proj i
  have hG_apply : ∀ x c j, G x c j = ∑ i, c i * ⟪s i x, s j x⟫ := by
    intro x c j
    simp [G, mul_comm]
  have hG : ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) n G x₀ := by
    apply contMDiffAt_clm_of_basis (Pi.basisFun ℝ ι)
    intro i
    rw [contMDiffAt_pi_space]
    intro j
    have : (fun x ↦ G x (Pi.basisFun ℝ ι i) j) = fun x ↦ ⟪s i x, s j x⟫ := by
      funext x
      simp [hG_apply, Pi.basisFun_apply, Pi.single_apply]
    rw [this]
    exact (hs i).inner_bundle (hs j)
  -- the vector of inner products
  let k : M → ι → ℝ := fun x j ↦ ⟪w x, s j x⟫
  have hk : ContMDiffAt I 𝓘(ℝ, ι → ℝ) n k x₀ := by
    rw [contMDiffAt_pi_space]
    exact h
  -- the Gram operator is invertible on the base set
  have hinv : ∀ x ∈ e.baseSet, (G x).IsInvertible := by
    intro x hx
    have hinj : Function.Injective (G x) := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have h0 : ⟪∑ i, c i • s i x, ∑ i, c i • s i x⟫ = 0 := by
        calc ⟪∑ i, c i • s i x, ∑ j, c j • s j x⟫ = ∑ j, c j * G x c j := by
              simp only [hG_apply, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
                Finset.mul_sum, RCLike.conj_to_real]
          _ = 0 := by simp [hc]
      have h1 : ∑ i, c i • s i x = 0 := inner_self_eq_zero.mp h0
      have h2 : ∑ i, c i • s i x = e.symmL ℝ x (∑ i, c i • b i) := by
        simp [map_sum, map_smul, hs_eq _ x hx]
      have h3 : ∑ i, c i • b i = 0 := by
        have := congrArg (e.continuousLinearMapAt ℝ x) (h2.symm.trans h1)
        simpa [e.continuousLinearMapAt_symmL hx] using this
      funext i
      exact Fintype.linearIndependent_iff.mp b.linearIndependent c h3 i
    have hsurj : Function.Surjective (G x) :=
      (LinearMap.injective_iff_surjective (f := (G x : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))).mp hinj
    exact ⟨(LinearEquiv.ofBijective (G x : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv, by ext; rfl⟩
  -- on the base set, the coordinates of `w` are `G⁻¹` of the inner-product vector
  have key : ∀ x ∈ e.baseSet,
      (e ⟨x, w x⟩).2 = b.equivFunL.symm ((G x).inverse (k x)) := by
    intro x hx
    have hW : e.symmL ℝ x ((e ⟨x, w x⟩).2) = w x := by
      rw [← e.continuousLinearMapAt_apply_of_mem ℝ hx]
      exact e.symmL_continuousLinearMapAt hx (w x)
    have hsum : ∑ i, b.equivFun (e ⟨x, w x⟩).2 i • s i x = w x := by
      calc ∑ i, b.equivFun (e ⟨x, w x⟩).2 i • s i x
          = ∑ i, b.equivFun (e ⟨x, w x⟩).2 i • e.symmL ℝ x (b i) := by
            simp only [hs_eq _ x hx]
        _ = e.symmL ℝ x (∑ i, b.equivFun (e ⟨x, w x⟩).2 i • b i) := by
            simp only [map_sum, map_smul]
        _ = w x := by rw [b.sum_equivFun, hW]
    have hGk : G x (b.equivFun (e ⟨x, w x⟩).2) = k x := by
      funext j
      rw [hG_apply]
      calc ∑ i, b.equivFun (e ⟨x, w x⟩).2 i * ⟪s i x, s j x⟫
          = ⟪∑ i, b.equivFun (e ⟨x, w x⟩).2 i • s i x, s j x⟫ := by
            simp [sum_inner, inner_smul_left]
        _ = ⟪w x, s j x⟫ := by rw [hsum]
    rw [← hGk, (hinv x hx).inverse_apply_eq.mpr rfl]
    simp
  rw [contMDiffAt_section]
  have hsm : ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ b.equivFunL.symm ((G x).inverse (k x))) x₀ := by
    have hi : ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) n (fun x ↦ (G x).inverse) x₀ := by
      obtain ⟨Eq, hEq⟩ := hinv x₀ hx₀
      have h' : ContDiffAt ℝ n ContinuousLinearMap.inverse (G x₀) := by
        rw [← hEq]
        exact contDiffAt_map_inverse Eq
      exact h'.comp_contMDiffAt hG
    exact ((b.equivFunL.symm : (ι → ℝ) →L[ℝ] F).contMDiff.contMDiffAt).comp x₀
      (hi.clm_apply hk)
  exact hsm.congr_of_eventuallyEq
    (by filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx using key x hx)

end InnerFrame

section DerivAlong

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {m n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I n M]

omit [IsManifold I n M] in
/-- The derivative of a `C^n` real function along a `C^m` vector field is `C^m`, for
`m + 1 ≤ n`. -/
theorem contMDiffAt_mvfderiv_apply {f : M → ℝ} {X : Π x : M, TangentSpace I x} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) n f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) m (fun x ↦ TotalSpace.mk' E x (X x)) x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(ℝ, ℝ) m (fun x ↦ mvfderiv I f x (X x)) x₀ := by
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I (M := M)) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hg₂ : ContMDiffAt I 𝓘(ℝ, E) m
      (fun x ↦ ((trivializationAt E (TangentSpace I (M := M)) x₀) ⟨x, X x⟩).2) x₀ :=
    (contMDiffAt_section x₀).mp hX
  have hf' : ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) n
      (Function.uncurry fun (_ : M) (y : M) ↦ f y) (id x₀, id x₀) :=
    hf.comp (x₀, x₀) contMDiffAt_snd
  have key := ContMDiffAt.mfderiv_apply (I := I) (I' := 𝓘(ℝ, ℝ)) (fun (_ : M) (y : M) ↦ f y)
    id id (fun x ↦ ((trivializationAt E (TangentSpace I (M := M)) x₀) ⟨x, X x⟩).2)
    hf' contMDiffAt_id contMDiffAt_id hg₂ hmn
  apply key.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I (M := M)) x₀).open_baseSet.mem_nhds hx₀]
    with x hx
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  change (d% f x) (X x) = (mfderiv I 𝓘(ℝ, ℝ) f x)
    ((trivializationAt E (TangentSpace I (M := M)) x₀).symmL ℝ x
      (((trivializationAt E (TangentSpace I (M := M)) x₀) ⟨x, X x⟩).2))
  rw [← (trivializationAt E (TangentSpace I (M := M)) x₀).continuousLinearMapAt_apply_of_mem ℝ hx,
    (trivializationAt E (TangentSpace I (M := M)) x₀).symmL_continuousLinearMapAt hx]
  rfl

end DerivAlong

section Main

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {k : ℕ∞}

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- The local frame of a trivialisation, on its base set, is the trivialisation's inverse
applied to the basis vectors. -/
lemma localFrame_eq_symmL {x₀ x : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hx : x ∈ (trivializationAt E (TangentSpace I (M := M)) x₀).baseSet) (i) :
    (trivializationAt E (TangentSpace I (M := M)) x₀).localFrame b i x =
      (trivializationAt E (TangentSpace I (M := M)) x₀).symmL ℝ x (b i) := by
  simp [(trivializationAt E (TangentSpace I (M := M)) x₀).localFrame_apply_of_mem_baseSet b hx,
    Trivialization.basisAt, Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply,
    (trivializationAt E (TangentSpace I (M := M)) x₀).symmL_apply hx]

/- Workaround for https://github.com/leanprover/lean4/issues/14949 (unification sees through the
type synonym `TangentSpace`): restate `ContMDiffAt.inner_bundle` for the tangent bundle, as
mathlib's `LeviCivita.lean` does for `MDifferentiable.inner_bundle`. -/
omit [FiniteDimensional ℝ E] in
lemma _root_.ContMDiffAt.inner_bundle' {n : ℕ∞ω}
    [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun x ↦ TotalSpace.mk' E x (X x)) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun x ↦ TotalSpace.mk' E x (Y x)) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun x ↦ ⟪X x, Y x⟫) x :=
  ContMDiffAt.inner_bundle hX hY

/-- The **Koszul expression** is `C^k` when the metric is `C^{k+1}` and the three fields are
`C^{k+1}` at the point. -/
theorem contMDiffAt_koszul
    [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace I x)]
    {X Y Z : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (k + 1) (fun x ↦ TotalSpace.mk' E x (X x)) x₀)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (k + 1) (fun x ↦ TotalSpace.mk' E x (Y x)) x₀)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (k + 1) (fun x ↦ TotalSpace.mk' E x (Z x)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦
      (mvfderiv I (fun y ↦ ⟪Y y, Z y⟫) x (X x) + mvfderiv I (fun y ↦ ⟪Z y, X y⟫) x (Y x)
        - mvfderiv I (fun y ↦ ⟪X y, Y y⟫) x (Z x)
        - ⟪Y x, VectorField.mlieBracket I X Z x⟫
        - ⟪Z x, VectorField.mlieBracket I Y X x⟫
        + ⟪X x, VectorField.mlieBracket I Z Y x⟫) / 2) x₀ := by
  have : IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k + 1) (by simp)
  have hk1 : (k : ℕ∞ω) + 1 ≤ k + 1 := le_rfl
  have hbr : ∀ {U V : Π x : M, TangentSpace I x},
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (k + 1) (fun x ↦ TotalSpace.mk' E x (U x)) x₀ →
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (k + 1) (fun x ↦ TotalSpace.mk' E x (V x)) x₀ →
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) k
        (fun x ↦ TotalSpace.mk' E x (VectorField.mlieBracket I U V x)) x₀ := by
    intro U V hU hV
    have hU' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((k + 1 : ℕ∞) : ℕ∞ω)
        (fun x ↦ TotalSpace.mk' E x (U x)) x₀ := by push_cast; exact hU
    have hV' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((k + 1 : ℕ∞) : ℕ∞ω)
        (fun x ↦ TotalSpace.mk' E x (V x)) x₀ := by push_cast; exact hV
    exact hU'.mlieBracket_vectorField hV' (by simp)
  have hXk := hX.of_le (by simp : (k : ℕ∞ω) ≤ k + 1)
  have hYk := hY.of_le (by simp : (k : ℕ∞ω) ≤ k + 1)
  have hZk := hZ.of_le (by simp : (k : ℕ∞ω) ≤ k + 1)
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦ mvfderiv I (fun y ↦ ⟪Y y, Z y⟫) x (X x)) x₀ :=
    contMDiffAt_mvfderiv_apply (hY.inner_bundle' hZ) hXk hk1
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦ mvfderiv I (fun y ↦ ⟪Z y, X y⟫) x (Y x)) x₀ :=
    contMDiffAt_mvfderiv_apply (hZ.inner_bundle' hX) hYk hk1
  have h3 : ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦ mvfderiv I (fun y ↦ ⟪X y, Y y⟫) x (Z x)) x₀ :=
    contMDiffAt_mvfderiv_apply (hX.inner_bundle' hY) hZk hk1
  have h4 : ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦ ⟪Y x, VectorField.mlieBracket I X Z x⟫) x₀ :=
    hYk.inner_bundle' (hbr hX hZ)
  have h5 : ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦ ⟪Z x, VectorField.mlieBracket I Y X x⟫) x₀ :=
    hZk.inner_bundle' (hbr hY hX)
  have h6 : ContMDiffAt I 𝓘(ℝ, ℝ) k (fun x ↦ ⟪X x, VectorField.mlieBracket I Z Y x⟫) x₀ :=
    hXk.inner_bundle' (hbr hZ hY)
  simp only [div_eq_mul_inv]
  exact (contDiffAt_id.mul contDiffAt_const).comp_contMDiffAt
    (((((h1.add h2).sub h3).sub h4).sub h5).add h6)

-- BENCH: levi-civita-smooth
/-- **Smoothness of the Levi-Civita connection.** On a `C^ω` manifold with a `C^{k+1}` Riemannian
metric, Mathlib's `leviCivitaConnection` is a `C^k` covariant derivative. This is the result
Mathlib's `LeviCivita.lean` defers to "future PRs"; it is what makes `Ric` of the canonical
connection a genuine function of the metric (`ricci` is junk on connections not known to be
`C¹`). -/
theorem contMDiffCovariantDerivative_leviCivitaConnection
    [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace I x)] :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) k := by
  have : IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k + 1) (by simp)
  refine ⟨⟨fun {Y} hY ↦ ?_⟩⟩
  rw [contMDiffOn_univ] at hY ⊢
  intro x₀
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I (M := M)) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, b = Module.finBasis ℝ E :=
    ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x,
      s = (trivializationAt E (TangentSpace I (M := M)) x₀).localFrame b := ⟨_, rfl⟩
  have hs : ∀ i, ∀ x ∈ (trivializationAt E (TangentSpace I (M := M)) x₀).baseSet,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (k + 1) (fun y ↦ TotalSpace.mk' E y (s i y)) x := by
    intro i x hx
    rw [hs_def]
    exact contMDiffAt_localFrame_of_mem (k + 1) _ b i hx
  have hne : ((k : ℕ∞ω) + 1) ≠ 0 := by simp
  -- Step 3: `⟪∇_{sᵢ} Y, sⱼ⟫` is `C^k` at `x₀`, by the Koszul formula
  have hinner : ∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) k
      (fun x ↦ ⟪leviCivitaConnection I M Y x (s i x), s j x⟫) x₀ := by
    intro i j
    have hK := contMDiffAt_koszul (hs i x₀ hx₀) (hY x₀) (hs j x₀ hx₀)
    apply hK.congr_of_eventuallyEq
    filter_upwards [(trivializationAt E (TangentSpace I (M := M)) x₀).open_baseSet.mem_nhds hx₀]
      with x hx
    exact leviCivitaConnection_apply_inner I ((hs i x hx).mdifferentiableAt hne)
      ((hY x).mdifferentiableAt hne) ((hs j x hx).mdifferentiableAt hne)
  -- Step 2: the sections `∇_{sᵢ} Y` are `C^k` at `x₀`
  subst hs_def
  have hw : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) k
      (fun x ↦ TotalSpace.mk' E x (leviCivitaConnection I M Y x
        ((trivializationAt E (TangentSpace I (M := M)) x₀).localFrame b i x))) x₀ := by
    intro i
    exact contMDiffAt_section_of_inner_localFrame (V := fun x : M ↦ TangentSpace I x) b
      (fun j ↦ hinner i j)
  -- Step 1: the endomorphism-bundle section, in coordinates
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  simp only [ContinuousLinearMap.inCoordinates]
  apply contMDiffAt_clm_of_basis b
  intro i
  apply ((contMDiffAt_section x₀).mp (hw i)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I (M := M)) x₀).open_baseSet.mem_nhds hx₀]
    with x hx
  simp only [ContinuousLinearMap.comp_apply]
  rw [(trivializationAt E (TangentSpace I (M := M)) x₀).continuousLinearMapAt_apply_of_mem ℝ hx,
    localFrame_eq_symmL b hx i]

/-- The case used by `Flow.lean` and `Hamilton.lean`: with a `C²` metric the Levi-Civita
connection is `C¹`, so its `ricci` is not junk. Registered as an instance. -/
instance instContMDiffCovariantDerivativeLeviCivitaConnectionOne
    [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)] :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 := by
  have : IsContMDiffRiemannianBundle I (((1 : ℕ∞) : ℕ∞ω) + 1) E (fun (x : M) ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  simpa using contMDiffCovariantDerivative_leviCivitaConnection (I := I) (M := M) (k := 1)

end Main

section RicciOfMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

-- BENCH: ricci-of-metric
/-- **The Ricci curvature of a metric.** For a `C²` Riemannian metric `g`, `Ric(g)` is the Ricci
curvature of its Levi-Civita connection. This is a genuine function of `g` and not junk: the
Levi-Civita connection is `C¹` (`contMDiffCovariantDerivative_leviCivitaConnection`), which is
what `ricci` needs to be the trace of a tensor. -/
noncomputable def ricciOfMetric
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X Y : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (leviCivitaConnection I M).ricci X Y x

/-- The sectional curvature of a `C²` metric, via its Levi-Civita connection. -/
noncomputable def sectionalCurvatureOfMetric
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X Y : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  sectionalCurvature (leviCivitaConnection I M) X Y x

end RicciOfMetric

end RicciFlowBlueprint
