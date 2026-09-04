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

end RicciFlowBlueprint
