/-
**Hamilton's pinching set as a convex set of endomorphisms.**

`IveyConvex.lean` proves the set closed and convex as a subset of `ℝ³`, in the eigenvalue
coordinates `λ ≥ μ ≥ ν`. But the tensor maximum principle is applied to a *section of a
bundle*, and in dimension three that bundle is `End(TM)` (`CurvatureOperatorThree.lean`) —
so what has to be closed and convex is a set of **endomorphisms of a fibre**, with no
eigenvalue coordinates anywhere. This file is that transfer, which `CLAUDE.md` recorded as
the one piece of the step still to build.

**The ordering conditions disappear.** In `ℝ³` the set carries `ν ≤ μ ≤ λ`, which is not a
property of an operator at all — it is a choice of labelling for its eigenvalues. On
endomorphisms the same set is cut out by two conditions only:

  `-3 ≤ tr A`  and  `G(λ_min A) ≤ tr A`.

**Convexity comes from two facts about `λ_min` and one about `G`.** The trace is linear;
`λ_min` is concave, being an infimum of linear functionals `A ↦ ⟪Av,v⟫`; and `G` is convex
*and antitone*, so `G ∘ λ_min` is convex. Nothing here is about dimension three, and
nothing is about the curvature.

**`λ_min` is defined as a Rayleigh infimum, not as an eigenvalue**, and that is what makes
the whole file cheap: concavity and the Lipschitz bound `|λ_min A − λ_min B| ≤ ‖A − B‖` are
two lines each from `le_ciInf`/`ciInf_le`, where the spectral definition would need the
eigenvalues to depend continuously on `A`. The spectral reading is recovered only where it
is needed, in the bridge back to `IveyConvex.lean`.

**The bridge is the falsification check.** For an operator diagonal in an orthonormal basis
with entries `ν ≤ μ ≤ λ`, membership here is `IsIveyPinched λ μ ν` — so the two sets are the
same set, and `IveyConvex.lean`'s ODE-side results transfer. Both halves of that need one
identity, `⟪Av,v⟫ = ∑ᵢ eᵢ⟪bᵢ,v⟫²`, and Parseval is *not* imported for the normalisation:
applying the same identity at `A = id` gives `∑ᵢ⟪bᵢ,v⟫² = ⟪v,v⟫`.
-/
import RicciFlowBlueprint.IveyConvex
import Mathlib.Analysis.InnerProductSpace.Trace

open Set Metric
open scoped RealInnerProductSpace

namespace RicciFlowBlueprint

section LambdaMin

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Nontrivial W]

/-- **The bottom of the Rayleigh quotient**, `λ_min A = inf {⟪Av,v⟫ : ‖v‖ = 1}`.

For a self-adjoint operator on a finite-dimensional space this is the least eigenvalue
(`lambdaMin_eq_of_diagonal`), but the definition asks for no self-adjointness and no
spectral theory: it is an infimum of *linear* functionals of `A`, which is what makes it
concave and `1`-Lipschitz. -/
noncomputable def lambdaMin (A : W →L[ℝ] W) : ℝ := ⨅ v : sphere (0 : W) 1, ⟪A v, (v : W)⟫

omit [Nontrivial W] in
theorem bddBelow_inner_sphere (A : W →L[ℝ] W) :
    BddBelow (Set.range fun v : sphere (0 : W) 1 ↦ ⟪A v, (v : W)⟫) := by
  refine ⟨-‖A‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  have hv : ‖(v : W)‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have h1 : |⟪A (v : W), (v : W)⟫| ≤ ‖A (v : W)‖ * ‖(v : W)‖ := abs_real_inner_le_norm _ _
  have h2 : ‖A (v : W)‖ ≤ ‖A‖ * ‖(v : W)‖ := A.le_opNorm _
  rw [hv, mul_one] at h1 h2
  have := abs_le.mp h1
  linarith [this.1]

omit [Nontrivial W] in
/-- `λ_min` is a lower bound for every unit Rayleigh value. -/
theorem lambdaMin_le (A : W →L[ℝ] W) {v : W} (hv : ‖v‖ = 1) : lambdaMin A ≤ ⟪A v, v⟫ :=
  ciInf_le (bddBelow_inner_sphere A) (⟨v, mem_sphere_zero_iff_norm.mpr hv⟩ : sphere (0 : W) 1)

/-- …and the greatest one. -/
theorem le_lambdaMin {A : W →L[ℝ] W} {c : ℝ} (h : ∀ v : W, ‖v‖ = 1 → c ≤ ⟪A v, v⟫) :
    c ≤ lambdaMin A := by
  have : Nonempty (sphere (0 : W) 1) := NormedSpace.sphere_nonempty_rclike (𝕜 := ℝ) zero_le_one
  exact le_ciInf fun v ↦ h v (mem_sphere_zero_iff_norm.mp v.2)

/-- **`λ_min` is concave.** An infimum of linear functionals of `A`. -/
theorem lambdaMin_concave (A B : W →L[ℝ] W) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * lambdaMin A + b * lambdaMin B ≤ lambdaMin (a • A + b • B) := by
  refine le_lambdaMin fun v hv ↦ ?_
  have e : ⟪(a • A + b • B) v, v⟫ = a * ⟪A v, v⟫ + b * ⟪B v, v⟫ := by
    show ⟪a • A v + b • B v, v⟫ = _
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [e]
  have h1 := lambdaMin_le A hv
  have h2 := lambdaMin_le B hv
  nlinarith

/-- **`λ_min` is `1`-Lipschitz**, one half of the estimate. -/
theorem lambdaMin_le_add_norm (A B : W →L[ℝ] W) : lambdaMin A ≤ lambdaMin B + ‖A - B‖ := by
  have key : lambdaMin A - ‖A - B‖ ≤ lambdaMin B := by
    refine le_lambdaMin fun v hv ↦ ?_
    have hsplit : ⟪A v, v⟫ = ⟪B v, v⟫ + ⟪(A - B) v, v⟫ := by
      show _ = ⟪B v, v⟫ + ⟪A v - B v, v⟫
      rw [inner_sub_left]
      ring
    have hb : ⟪(A - B) v, v⟫ ≤ ‖A - B‖ := by
      have h1 : |⟪(A - B) v, v⟫| ≤ ‖(A - B) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      have h2 : ‖(A - B) v‖ ≤ ‖A - B‖ * ‖v‖ := (A - B).le_opNorm _
      rw [hv, mul_one] at h1 h2
      have := abs_le.mp h1
      linarith [this.2]
    have := lambdaMin_le A hv
    linarith
  linarith

theorem lipschitzWith_lambdaMin :
    LipschitzWith 1 (lambdaMin : (W →L[ℝ] W) → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun A B ↦ ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, abs_le]
  constructor
  · have := lambdaMin_le_add_norm B A
    rw [show ‖B - A‖ = ‖A - B‖ from norm_sub_rev B A] at this
    linarith
  · linarith [lambdaMin_le_add_norm A B]

theorem continuous_lambdaMin : Continuous (lambdaMin : (W →L[ℝ] W) → ℝ) :=
  lipschitzWith_lambdaMin.continuous

end LambdaMin

section Diagonal

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {ι : Type*} [Fintype ι]

/-- **The Rayleigh quotient of a diagonal operator**: `⟪Av,v⟫ = ∑ᵢ eᵢ⟪bᵢ,v⟫²`.

Stated for an operator diagonalised by an orthonormal basis. Applying it at `A = id`,
`e = 1` gives `∑ᵢ⟪bᵢ,v⟫² = ⟪v,v⟫`, so Parseval is never needed separately. -/
theorem inner_apply_self_eq_sum (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W} {e : ι → ℝ}
    (hA : ∀ i, A (b i) = e i • (b i : W)) (v : W) :
    ⟪A v, v⟫ = ∑ i, e i * ⟪(b i : W), v⟫ ^ 2 := by
  have hv : v = ∑ i, ⟪(b i : W), v⟫ • (b i : W) := (b.sum_repr' v).symm
  calc ⟪A v, v⟫
      = ⟪A (∑ i, ⟪(b i : W), v⟫ • (b i : W)), v⟫ := by rw [← hv]
    _ = ⟪∑ i, ⟪(b i : W), v⟫ • A (b i), v⟫ := by
        rw [map_sum]
        exact congrArg (fun w ↦ ⟪w, v⟫) (Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _)
    _ = ∑ i, ⟪(b i : W), v⟫ * ⟪A (b i), v⟫ := by
        rw [sum_inner]
        exact Finset.sum_congr rfl fun i _ ↦ real_inner_smul_left _ _ _
    _ = ∑ i, e i * ⟪(b i : W), v⟫ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hA i, real_inner_smul_left]
        ring

/-- `∑ᵢ⟪bᵢ,v⟫² = ⟪v,v⟫`, the previous identity at the identity operator. -/
theorem sum_sq_inner_eq (b : OrthonormalBasis ι ℝ W) (v : W) :
    ∑ i, ⟪(b i : W), v⟫ ^ 2 = ⟪v, v⟫ := by
  have h := inner_apply_self_eq_sum b (A := ContinuousLinearMap.id ℝ W) (e := fun _ ↦ (1 : ℝ))
    (fun i ↦ by simp) v
  simp only [ContinuousLinearMap.id_apply, one_mul] at h
  exact h.symm

variable [Nontrivial W]

/-- **A lower bound on the diagonal entries is a lower bound on `λ_min`.** -/
theorem le_lambdaMin_of_diagonal (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W} {e : ι → ℝ}
    (hA : ∀ i, A (b i) = e i • (b i : W)) {c : ℝ} (hc : ∀ i, c ≤ e i) :
    c ≤ lambdaMin A := by
  refine le_lambdaMin fun v hv ↦ ?_
  have hnorm : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hsum := inner_apply_self_eq_sum b hA v
  have hone := sum_sq_inner_eq b v
  have hstep : ∑ i, c * ⟪(b i : W), v⟫ ^ 2 ≤ ∑ i, e i * ⟪(b i : W), v⟫ ^ 2 :=
    Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)
  rw [← Finset.mul_sum, hone, hnorm, mul_one] at hstep
  rw [hsum]
  exact hstep

omit [Nontrivial W] in
/-- **Each diagonal entry is an upper bound for `λ_min`.** -/
theorem lambdaMin_le_of_diagonal (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W} {e : ι → ℝ}
    (hA : ∀ i, A (b i) = e i • (b i : W)) (i : ι) : lambdaMin A ≤ e i := by
  have hb : ‖(b i : W)‖ = 1 := b.norm_eq_one i
  have h := lambdaMin_le A hb
  rwa [hA i, real_inner_smul_left, real_inner_self_eq_norm_sq, hb, one_pow, mul_one] at h

/-- **`λ_min` of a diagonal operator is its least entry.** -/
theorem lambdaMin_eq_of_diagonal (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W} {e : ι → ℝ}
    (hA : ∀ i, A (b i) = e i • (b i : W)) {i₀ : ι} (hi₀ : ∀ i, e i₀ ≤ e i) :
    lambdaMin A = e i₀ :=
  le_antisymm (lambdaMin_le_of_diagonal b hA i₀) (le_lambdaMin_of_diagonal b hA hi₀)

omit [Nontrivial W] in
/-- **The trace of a diagonal operator is the sum of its entries.** -/
theorem trace_eq_sum_of_diagonal (b : OrthonormalBasis ι ℝ W) {A : W →L[ℝ] W} {e : ι → ℝ}
    (hA : ∀ i, A (b i) = e i • (b i : W)) :
    LinearMap.trace ℝ W (A : W →ₗ[ℝ] W) = ∑ i, e i := by
  rw [LinearMap.trace_eq_sum_inner (A : W →ₗ[ℝ] W) b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hb : ‖(b i : W)‖ = 1 := b.norm_eq_one i
  show ⟪(b i : W), A (b i)⟫ = e i
  rw [hA i, real_inner_smul_right, real_inner_self_eq_norm_sq, hb, one_pow, mul_one]

end Diagonal

section Conj

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']

/-- **Conjugation of an endomorphism by a linear isometry equivalence**, `A ↦ S A S⁻¹`. -/
noncomputable def endoConj (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) : W' →L[ℝ] W' :=
  S.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp S.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem endoConj_apply (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) (v : W') :
    endoConj S A v = S (A (S.symm v)) := rfl

/-- **`λ_min` is conjugation-invariant.** An isometry carries unit vectors to unit vectors
and preserves the pairing, so the two Rayleigh ranges are the same set. -/
theorem lambdaMin_conj [Nontrivial W] [Nontrivial W'] (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    lambdaMin (endoConj S A) = lambdaMin A := by
  refine le_antisymm (le_lambdaMin fun v hv ↦ ?_) (le_lambdaMin fun w hw ↦ ?_)
  · have hSv : ‖S v‖ = 1 := by rw [S.norm_map]; exact hv
    have h := lambdaMin_le (endoConj S A) hSv
    rwa [endoConj_apply, S.symm_apply_apply, S.inner_map_map] at h
  · have hSw : ‖S.symm w‖ = 1 := by rw [S.symm.norm_map]; exact hw
    have key : ∀ a b : W, ⟪a, b⟫ = ⟪S a, S b⟫ := fun a b ↦ (S.inner_map_map a b).symm
    have e : ⟪endoConj S A w, w⟫ = ⟪A (S.symm w), S.symm w⟫ := by
      rw [key (A (S.symm w)) (S.symm w), S.apply_symm_apply]
      rfl
    rw [e]
    exact lambdaMin_le A hSw

end Conj


namespace Pinching

/-- **`G` is antitone.** `ν ↦ max(-ν, e²)` is antitone and lands in `[e², ∞)`, where `f`
increases. This is what turns concavity of `λ_min` into convexity of `G ∘ λ_min`. -/
theorem antitone_iveyG : Antitone iveyG := by
  intro x y hxy
  show iveyF (max (-y) (Real.exp 2)) ≤ iveyF (max (-x) (Real.exp 2))
  exact monotoneOn_iveyF (Set.mem_Ici.mpr (le_max_right _ _))
    (Set.mem_Ici.mpr (le_max_right _ _)) (max_le_max (neg_le_neg hxy) le_rfl)

section Set

variable (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Nontrivial W]
  [FiniteDimensional ℝ W]

/-- The trace as a continuous linear functional on `End(W)`. -/
noncomputable def traceEndo : (W →L[ℝ] W) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ W).comp (ContinuousLinearMap.coeLM ℝ))

variable {W}

omit [Nontrivial W] in
@[simp] theorem traceEndo_apply (A : W →L[ℝ] W) :
    traceEndo W A = LinearMap.trace ℝ W (A : W →ₗ[ℝ] W) := rfl

variable (W)

/-- **Hamilton's pinching set on endomorphisms of a fibre.** The eigenvalue ordering of the
`ℝ³` version is absent: it is a labelling of eigenvalues, not a property of an operator. -/
def iveyEndoSet : Set (W →L[ℝ] W) :=
  {A | -3 ≤ traceEndo W A ∧ iveyG (lambdaMin A) ≤ traceEndo W A}

variable {W}

omit [Nontrivial W] in
theorem mem_iveyEndoSet_iff (A : W →L[ℝ] W) :
    A ∈ iveyEndoSet W ↔ -3 ≤ traceEndo W A ∧ iveyG (lambdaMin A) ≤ traceEndo W A :=
  Iff.rfl

-- BENCH: ivey-endo-convex
/-- **The endomorphism pinching set is convex.** The trace is linear, `λ_min` is concave,
and `G` is convex and antitone — so `G ∘ λ_min` is convex, and both conditions are convex
inequalities. -/
theorem convex_iveyEndoSet : Convex ℝ (iveyEndoSet W) := by
  rintro A ⟨hA1, hA2⟩ B ⟨hB1, hB2⟩ a b ha hb hab
  have htr : traceEndo W (a • A + b • B) = a * traceEndo W A + b * traceEndo W B := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [htr]; nlinarith
  · rw [htr]
    have hconc := lambdaMin_concave A B ha hb
    have hanti := antitone_iveyG hconc
    have hconv := convexOn_iveyG.2 (mem_univ (lambdaMin A)) (mem_univ (lambdaMin B)) ha hb hab
    simp only [smul_eq_mul] at hconv
    have hA : a * iveyG (lambdaMin A) ≤ a * traceEndo W A :=
      mul_le_mul_of_nonneg_left hA2 ha
    have hB : b * iveyG (lambdaMin B) ≤ b * traceEndo W B :=
      mul_le_mul_of_nonneg_left hB2 hb
    linarith

/-- **The endomorphism pinching set is closed**, `λ_min` being `1`-Lipschitz and `G`
continuous. -/
theorem isClosed_iveyEndoSet : IsClosed (iveyEndoSet W) := by
  have h1 : IsClosed {A : W →L[ℝ] W | -3 ≤ traceEndo W A} :=
    isClosed_le continuous_const (traceEndo W).continuous
  have h2 : IsClosed {A : W →L[ℝ] W | iveyG (lambdaMin A) ≤ traceEndo W A} :=
    isClosed_le (continuous_iveyG.comp continuous_lambdaMin) (traceEndo W).continuous
  exact h1.inter h2

-- BENCH: ivey-endo-bridge
/-- **The bridge, and the falsification check**: on an operator diagonalised by an
orthonormal basis of a three-dimensional fibre, with entries ordered `ν ≤ μ ≤ λ`, membership
of the endomorphism set is exactly `IsIveyPinched λ μ ν`.

So `iveyEndoSet` is `IveyConvex.lean`'s set, read on operators rather than on eigenvalue
triples, and everything `Pinching.lean` proves about the ODE transfers. Without this the
convexity above would be convexity of an unidentified set. -/
theorem mem_iveyEndoSet_iff_isIveyPinched (b : OrthonormalBasis (Fin 3) ℝ W)
    {A : W →L[ℝ] W} {l m n : ℝ}
    (h0 : A (b 0) = l • (b 0 : W)) (h1 : A (b 1) = m • (b 1 : W))
    (h2 : A (b 2) = n • (b 2 : W)) (hnm : n ≤ m) (hml : m ≤ l) :
    A ∈ iveyEndoSet W ↔ IsIveyPinched l m n := by
  have hA : ∀ i : Fin 3, A (b i) = ![l, m, n] i • (b i : W) := by
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  have hmin : ∀ i : Fin 3, ![l, m, n] 2 ≤ ![l, m, n] i := by
    intro i
    fin_cases i <;> simp <;> linarith
  have hlam : lambdaMin A = n := by
    have h := lambdaMin_eq_of_diagonal b hA hmin
    simpa using h
  have htr : traceEndo W A = l + m + n := by
    rw [traceEndo_apply, trace_eq_sum_of_diagonal b hA, Fin.sum_univ_three]
    simp
  rw [mem_iveyEndoSet_iff, hlam, htr, isIveyPinched_iff_iveyG]

/-- The bridge with the entries given as an **antitone** family, which is the form the
spectral theorem hands over: mathlib's `LinearMap.IsSymmetric.eigenvalues` is already sorted
in decreasing order, so no reindexing is needed anywhere. -/
theorem mem_iveyEndoSet_iff_isIveyPinched_antitone (b : OrthonormalBasis (Fin 3) ℝ W)
    {A : W →L[ℝ] W} {e : Fin 3 → ℝ} (hA : ∀ i, A (b i) = e i • (b i : W)) (he : Antitone e) :
    A ∈ iveyEndoSet W ↔ IsIveyPinched (e 0) (e 1) (e 2) :=
  mem_iveyEndoSet_iff_isIveyPinched b (hA 0) (hA 1) (hA 2)
    (he (by decide)) (he (by decide))

section Naturality

variable {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [Nontrivial W']
  [FiniteDimensional ℝ W']

omit [Nontrivial W] [Nontrivial W'] in
/-- **The trace is conjugation-invariant**, Mathlib's `LinearMap.trace_conj'` through the
coercion. -/
theorem traceEndo_conj (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    traceEndo W' (endoConj S A) = traceEndo W A := by
  rw [traceEndo_apply, traceEndo_apply]
  have he : ((endoConj S A : W' →L[ℝ] W') : W' →ₗ[ℝ] W')
      = S.toLinearEquiv.conj (A : W →ₗ[ℝ] W) := by
    ext v
    rfl
  rw [he, LinearMap.trace_conj']

-- BENCH: ivey-endo-natural
/-- **The pinching set is invariant under every fibre isometry.**

Both conditions cutting it out — the trace and `λ_min` — are conjugation-invariant, so
`iveyEndoSet` is *natural*: it is attached to an inner product space with no further choice.

**This is what makes `x ↦ iveyEndoSet (V x)` a parallel subbundle, with no transport
computation.** The cross-fibre half of the maximum principle compares `dist(u(t,x), K_x)`
between different fibres, and Hamilton's argument asks for `K` to be preserved by parallel
transport. Here that is not a hypothesis to be checked against a connection: transport is an
isometry (`TransportIsometry.lean`), and *every* isometry preserves this set. -/
theorem mem_iveyEndoSet_conj_iff (S : W ≃ₗᵢ[ℝ] W') (A : W →L[ℝ] W) :
    endoConj S A ∈ iveyEndoSet W' ↔ A ∈ iveyEndoSet W := by
  rw [mem_iveyEndoSet_iff, mem_iveyEndoSet_iff, lambdaMin_conj, traceEndo_conj]

end Naturality

end Set

end Pinching

end RicciFlowBlueprint
