/-
**Hamilton's pinching set, its reaction and Nagumo's condition, in a fixed matrix space.**

The final assembly runs the fibrewise maximum principle on the matrix of `Rm₃` in the Uhlenbeck
frame, which lives in the **fixed** space `Mat3 = EuclideanSpace ℝ (Fin 3 × Fin 3)`. That space
is chosen so that no metric on a bundle is ever an instance while another is in scope: its inner
product is the Euclidean one, which on matrices of operators in an orthonormal basis *is* the
Hilbert--Schmidt form (`inner_toMat`, Parseval). Everything the principle asks of the target set
and the reaction is transported here once:

* `toMat e A = (⟪A eᵢ, eⱼ⟫)ᵢⱼ`, linear, with `⟪toMat A, toMat B⟫ = hsForm e A B`;
* `pinchedMat` = the matrices of self-adjoint pinched operators on `ℝ³`, closed, convex,
  containing `0`, and `toMat e A ∈ pinchedMat ↔ A` is self-adjoint and pinched **in any
  orthonormal basis of any three-dimensional `W`** --- the frame change is an isometry and the
  set is natural (`mem_iveyEndoSet_conj_iff`);
* `reactionMat` = Hamilton's reaction read in matrices, with
  `toMat e (Q A) = reactionMat (toMat e A)`;
* Nagumo's condition for `reactionMat` on `pinchedMat`, from `IveyReactionEndo.lean`.
-/
import RicciFlowBlueprint.IveyReactionEndo

open Set Filter Module ContinuousLinearMap
open scoped RealInnerProductSpace Topology

namespace RicciFlowBlueprint

namespace Pinching

/-- The model space for `3 × 3` matrices: Euclidean, so its inner product is Frobenius. -/
abbrev Mat3 := EuclideanSpace ℝ (Fin 3 × Fin 3)

/-- Three-space, with its standard orthonormal basis. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **The matrix of an endomorphism in an orthonormal basis**: entry `(i,j)` is `⟪A eᵢ, eⱼ⟫`. -/
noncomputable def toMat (e : OrthonormalBasis (Fin 3) ℝ W) : (W →L[ℝ] W) →ₗ[ℝ] Mat3 where
  toFun A := WithLp.toLp 2 (fun ij ↦ ⟪A (e ij.1), e ij.2⟫)
  map_add' A B := by
    ext ij
    simp [inner_add_left]
  map_smul' c A := by
    ext ij
    simp [real_inner_smul_left]

omit [FiniteDimensional ℝ W] in
@[simp] theorem toMat_apply (e : OrthonormalBasis (Fin 3) ℝ W) (A : W →L[ℝ] W)
    (ij : Fin 3 × Fin 3) : toMat e A ij = ⟪A (e ij.1), e ij.2⟫ := rfl

omit [FiniteDimensional ℝ W] in
-- BENCH: to-mat-inner
/-- **The Euclidean inner product of matrices is the Hilbert--Schmidt form** (Parseval). -/
theorem inner_toMat (e : OrthonormalBasis (Fin 3) ℝ W) (A B : W →L[ℝ] W) :
    ⟪toMat e A, toMat e B⟫ = hsForm e A B := by
  rw [hsForm_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← e.sum_inner_mul_inner (A (e i)) (B (e i))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [toMat_apply, RCLike.inner_apply, conj_trivial]
  rw [real_inner_comm (e j) (B (e i))]
  ring

omit [FiniteDimensional ℝ W] in
/-- `toMat` is injective: the Hilbert--Schmidt form is definite. -/
theorem toMat_injective (e : OrthonormalBasis (Fin 3) ℝ W) : Function.Injective (toMat e) := by
  intro A B h
  apply clm_ext_orthonormalBasis e
  intro i
  rw [← e.sum_repr' (A (e i)), ← e.sum_repr' (B (e i))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hij := congrArg (fun M : Mat3 ↦ M (i, j)) h
  simp only [toMat_apply] at hij
  rw [real_inner_comm, hij, real_inner_comm]

section Conj

variable {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
/-- **The matrix does not see an isometric change of space**: the matrix of `S A S⁻¹` in the
image basis is the matrix of `A`. -/
theorem toMat_endoConj (S : W ≃ₗᵢ[ℝ] W') (e : OrthonormalBasis (Fin 3) ℝ W)
    (c : OrthonormalBasis (Fin 3) ℝ W') (hc : ∀ i, c i = S (e i)) (A : W →L[ℝ] W) :
    toMat c (endoConj S A) = toMat e A := by
  ext ij
  simp only [toMat_apply, endoConj_apply, hc, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.inner_map_map]

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
/-- Self-adjointness is preserved by an isometric change of space. -/
theorem isSymmetric_endoConj (S : W ≃ₗᵢ[ℝ] W') {A : W →L[ℝ] W}
    (hA : (A : W →ₗ[ℝ] W).IsSymmetric) : ((endoConj S A : W' →L[ℝ] W') : W' →ₗ[ℝ] W').IsSymmetric := by
  intro v w
  simp only [ContinuousLinearMap.coe_coe, endoConj_apply]
  have h := hA (S.symm v) (S.symm w)
  simp only [ContinuousLinearMap.coe_coe] at h
  calc ⟪S (A (S.symm v)), w⟫ = ⟪S (A (S.symm v)), S (S.symm w)⟫ := by rw [S.apply_symm_apply]
    _ = ⟪A (S.symm v), S.symm w⟫ := S.inner_map_map _ _
    _ = ⟪S.symm v, A (S.symm w)⟫ := h
    _ = ⟪S (S.symm v), S (A (S.symm w))⟫ := (S.inner_map_map _ _).symm
    _ = ⟪v, S (A (S.symm w))⟫ := by rw [S.apply_symm_apply]

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
theorem endoConj_comp (S : W ≃ₗᵢ[ℝ] W') (A B : W →L[ℝ] W) :
    endoConj S (A ∘L B) = endoConj S A ∘L endoConj S B := by
  ext v; simp

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
theorem endoConj_id (S : W ≃ₗᵢ[ℝ] W') :
    endoConj S (ContinuousLinearMap.id ℝ W) = ContinuousLinearMap.id ℝ W' := by
  ext v; simp

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
theorem endoConj_add (S : W ≃ₗᵢ[ℝ] W') (A B : W →L[ℝ] W) :
    endoConj S (A + B) = endoConj S A + endoConj S B := by
  ext v; simp

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
theorem endoConj_sub (S : W ≃ₗᵢ[ℝ] W') (A B : W →L[ℝ] W) :
    endoConj S (A - B) = endoConj S A - endoConj S B := by
  ext v; simp

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W'] in
theorem endoConj_smul (S : W ≃ₗᵢ[ℝ] W') (r : ℝ) (A : W →L[ℝ] W) :
    endoConj S (r • A) = r • endoConj S A := by
  ext v; simp

/-- **Hamilton's reaction is natural**: `Q(S A S⁻¹) = S Q(A) S⁻¹`, being a polynomial in `A`
with conjugation-invariant coefficients. -/
theorem hamiltonReaction_endoConj (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    hamiltonReaction (endoConj S A) = endoConj S (hamiltonReaction A) := by
  unfold hamiltonReaction
  rw [endoConj_add, endoConj_sub, endoConj_smul, endoConj_smul, endoConj_smul, endoConj_comp,
    endoConj_id, ← endoConj_comp, traceEndo_conj, traceEndo_conj]

end Conj

section Model

/-- The standard orthonormal basis of `ℝ³`. -/
noncomputable abbrev std : OrthonormalBasis (Fin 3) ℝ R3 := EuclideanSpace.basisFun (Fin 3) ℝ

omit [FiniteDimensional ℝ W] in
/-- An orthonormal basis of `W` is the image of the standard one under its coordinate map. -/
theorem std_eq_repr (e : OrthonormalBasis (Fin 3) ℝ W) (i : Fin 3) : std i = e.repr (e i) := by
  classical
  rw [e.repr_self, EuclideanSpace.basisFun_apply]

omit [FiniteDimensional ℝ W] in
/-- **The matrix in any orthonormal basis is the matrix, in the standard basis of `ℝ³`, of the
conjugate by the coordinate isometry.** -/
theorem toMat_eq_std (e : OrthonormalBasis (Fin 3) ℝ W) (A : W →L[ℝ] W) :
    toMat e A = toMat std (endoConj e.repr A) :=
  (toMat_endoConj e.repr e std (std_eq_repr e) A).symm

variable (W) in
/-- The self-adjoint part of the endomorphism pinching set. -/
def symmIvey [Nontrivial W] : Set (W →L[ℝ] W) :=
  {A | A ∈ iveyEndoSet W ∧ (A : W →ₗ[ℝ] W).IsSymmetric}

/-- **The pinching set in the matrix model**: matrices of self-adjoint pinched operators. -/
def pinchedMat : Set Mat3 := toMat std '' symmIvey R3

variable [Nontrivial W]

-- BENCH: pinched-mat-iff
/-- **Membership of a matrix in the model set is membership of the operator in the pinching
set**, in any orthonormal basis of any three-dimensional `W`: the change of space is an isometry
and the set is natural. -/
theorem toMat_mem_pinchedMat_iff (e : OrthonormalBasis (Fin 3) ℝ W) (A : W →L[ℝ] W) :
    toMat e A ∈ pinchedMat ↔ A ∈ symmIvey W := by
  rw [toMat_eq_std]
  constructor
  · rintro ⟨B, ⟨hB, hBs⟩, hBA⟩
    have hEq : B = endoConj e.repr A := toMat_injective std hBA
    subst hEq
    refine ⟨(mem_iveyEndoSet_conj_iff e.repr A).mp hB, ?_⟩
    have h := isSymmetric_endoConj e.repr.symm hBs
    have hback : endoConj e.repr.symm (endoConj e.repr A) = A := by ext v; simp
    rwa [hback] at h
  · rintro ⟨hA, hAs⟩
    exact ⟨endoConj e.repr A, ⟨(mem_iveyEndoSet_conj_iff e.repr A).mpr hA,
      isSymmetric_endoConj e.repr hAs⟩, rfl⟩

omit [FiniteDimensional ℝ W] [Nontrivial W] in
theorem convex_isSymmetric : Convex ℝ {A : W →L[ℝ] W | (A : W →ₗ[ℝ] W).IsSymmetric} := by
  intro A hA B hB a b _ _ _ v w
  have h1 := hA v w
  have h2 := hB v w
  simp only [ContinuousLinearMap.coe_coe] at h1 h2 ⊢
  simp only [add_apply, smul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, h1, h2]

omit [FiniteDimensional ℝ W] [Nontrivial W] in
theorem isClosed_isSymmetric : IsClosed {A : W →L[ℝ] W | (A : W →ₗ[ℝ] W).IsSymmetric} := by
  have : {A : W →L[ℝ] W | (A : W →ₗ[ℝ] W).IsSymmetric}
      = ⋂ v : W, ⋂ w : W, {A : W →L[ℝ] W | ⟪A v, w⟫ = ⟪v, A w⟫} := by
    ext A; simp [LinearMap.IsSymmetric]
  rw [this]
  refine isClosed_iInter fun v ↦ isClosed_iInter fun w ↦ isClosed_eq ?_ ?_
  · exact ((ContinuousLinearMap.apply ℝ W v).continuous).inner continuous_const
  · exact continuous_const.inner (ContinuousLinearMap.apply ℝ W w).continuous

theorem convex_pinchedMat : Convex ℝ pinchedMat :=
  ((convex_iveyEndoSet (W := R3)).inter convex_isSymmetric).linear_image (toMat std)

theorem isClosed_pinchedMat : IsClosed pinchedMat := by
  have hemb := LinearMap.isClosedEmbedding_of_injective (f := toMat std)
    (LinearMap.ker_eq_bot.mpr (toMat_injective std))
  exact hemb.isClosedMap _ ((isClosed_iveyEndoSet (W := R3)).inter isClosed_isSymmetric)

/-- **`0` is pinched**: `tr 0 = 0 ≥ −3` and `G(λ_min 0) = G(0) = −e² ≤ 0`. -/
theorem zero_mem_symmIvey : (0 : W →L[ℝ] W) ∈ symmIvey W := by
  refine ⟨?_, fun v w ↦ by simp⟩
  have hsph : ∃ v : W, ‖v‖ = 1 := by
    obtain ⟨v, hv⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℝ) (E := W) zero_le_one
    exact ⟨v, mem_sphere_zero_iff_norm.mp hv⟩
  obtain ⟨v, hv⟩ := hsph
  have hmin : lambdaMin (0 : W →L[ℝ] W) = 0 := le_antisymm
    (by simpa using lambdaMin_le (0 : W →L[ℝ] W) hv)
    (le_lambdaMin fun w _ ↦ by simp)
  have htr : traceEndo W (0 : W →L[ℝ] W) = 0 := map_zero _
  refine ⟨by rw [htr]; norm_num, ?_⟩
  rw [htr, hmin, iveyG_of_le (by simp; positivity)]
  linarith [Real.exp_pos 2]

theorem zero_mem_pinchedMat : (0 : Mat3) ∈ pinchedMat :=
  ⟨0, zero_mem_symmIvey, map_zero _⟩

/-- **The operator of a matrix** on `ℝ³`: `std i ↦ ∑ⱼ Mᵢⱼ std j`. -/
noncomputable def fromMat (M : Mat3) : R3 →L[ℝ] R3 :=
  ∑ i, ∑ j, M (i, j) • (innerSL ℝ (std i)).smulRight (std j)

theorem toMat_fromMat (M : Mat3) : toMat std (fromMat M) = M := by
  classical
  ext ⟨k, l⟩
  simp only [toMat_apply, fromMat, sum_apply, smul_apply, smulRight_apply, innerSL_apply_apply,
    sum_inner, real_inner_smul_left]
  have hon := orthonormal_iff_ite.mp (std).orthonormal
  simp only [hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem fromMat_toMat (A : R3 →L[ℝ] R3) : fromMat (toMat std A) = A :=
  toMat_injective std (toMat_fromMat _)

/-- **Hamilton's reaction on matrices.** -/
noncomputable def reactionMat (M : Mat3) : Mat3 := toMat std (hamiltonReaction (fromMat M))

-- BENCH: reaction-mat
omit [Nontrivial W] in
/-- **The matrix of the reaction is the reaction of the matrix**, in any orthonormal basis of
any three-dimensional `W`. -/
theorem toMat_hamiltonReaction (e : OrthonormalBasis (Fin 3) ℝ W) (A : W →L[ℝ] W) :
    toMat e (hamiltonReaction A) = reactionMat (toMat e A) := by
  rw [toMat_eq_std, toMat_eq_std e A, reactionMat, fromMat_toMat, hamiltonReaction_endoConj]

-- BENCH: reaction-mat-nagumo
/-- **Nagumo's condition in the matrix model**: at a pinched matrix, the reaction points into
the set against every outward normal. -/
theorem inner_reactionMat_nonpos {p : Mat3} (hp : p ∈ pinchedMat) {n : Mat3}
    (hn : ∀ q ∈ pinchedMat, ⟪n, q - p⟫ ≤ 0) : ⟪n, reactionMat p⟫ ≤ 0 := by
  obtain ⟨P, ⟨hP, hPs⟩, rfl⟩ := hp
  have hdim : finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  rw [reactionMat, fromMat_toMat, ← toMat_fromMat n, inner_toMat]
  refine hsForm_hamiltonReaction_nonpos hdim std hP hPs fun Q hQ hQs ↦ ?_
  have h := hn (toMat std Q) ⟨Q, ⟨hQ, hQs⟩, rfl⟩
  rwa [← map_sub, ← toMat_fromMat n, inner_toMat] at h

omit [Nontrivial W] in
/-- Hamilton's reaction is a polynomial in the operator, hence smooth. -/
theorem contDiff_hamiltonReaction : ContDiff ℝ ⊤ (hamiltonReaction (W := W)) := by
  have hc : ContDiff ℝ ⊤ fun A : W →L[ℝ] W ↦ A ∘L A := contDiff_id.clm_comp contDiff_id
  have ht := (traceEndo W).contDiff (n := ⊤)
  have h2 : ContDiff ℝ ⊤ fun A : W →L[ℝ] W ↦ (2 : ℝ) • (A ∘L A) := hc.const_smul (2 : ℝ)
  have h3 : ContDiff ℝ ⊤ fun A : W →L[ℝ] W ↦ traceEndo W A • A := ht.smul contDiff_id
  have h4 : ContDiff ℝ ⊤ fun A : W →L[ℝ] W ↦
      ((traceEndo W A ^ 2 - traceEndo W (A ∘L A)) / 2) • ContinuousLinearMap.id ℝ W :=
    (((ht.pow 2).sub (ht.comp hc)).div_const 2).smul contDiff_const
  unfold hamiltonReaction
  exact (h2.sub h3).add h4

theorem contDiff_fromMat : ContDiff ℝ ⊤ fromMat := by
  unfold fromMat
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ ?_
  exact (EuclideanSpace.proj (i, j) : Mat3 →L[ℝ] ℝ).contDiff.smul contDiff_const

theorem contDiff_reactionMat : ContDiff ℝ ⊤ reactionMat :=
  (LinearMap.toContinuousLinearMap (toMat std)).contDiff.comp
    (contDiff_hamiltonReaction.comp contDiff_fromMat)

-- BENCH: reaction-mat-lipschitz
/-- **The reaction is Lipschitz on every ball** — the only regularity the maximum principle
asks of it, since the matrix of `Rm₃` stays in a bounded set on a compact time interval. -/
theorem exists_lipschitzOnWith_reactionMat (R : ℝ) :
    ∃ K, LipschitzOnWith K reactionMat (Metric.closedBall 0 R) :=
  contDiff_reactionMat.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall _ _)
    (isCompact_closedBall _ _)

end Model

end Pinching

end RicciFlowBlueprint
