/-
**The metric trace commutes with the covariant derivative**: `X(tr_g B) = tr_g(∇_X B)`.

This is the gate for every Laplacian identity in this project — the contracted
second Bianchi identity, `∂ₜ scal = Δ scal + 2|Ric|²`, and `∂ₜ Rm = Δ Rm + Q`
(`lem:evolution-rm`, `lem:pinching`). Written out with the trace expanded over a
local orthonormal frame `e₁, …, eₙ` it says

  `X (∑ᵢ B(eᵢ, eᵢ)) = ∑ᵢ (∇_X B)(eᵢ, eᵢ)`,

and the whole content is that the `2n²` correction terms cancel. No *parallel*
frame is needed, which is the point: writing `∇_X eᵢ = ∑ⱼ aᵢⱼ eⱼ`, metric
compatibility forces `a` to be antisymmetric (`inner_cov_antisymm`, because
`⟪eᵢ, eⱼ⟫` is locally constant), the corrections are
`∑ᵢⱼ aᵢⱼ [B(eⱼ,eᵢ) + B(eᵢ,eⱼ)]`, and an antisymmetric matrix against a symmetric
one is `0` (`sum_bilin_of_antisymm`). Note `B` itself need not be symmetric.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`, and
`cov.covBilin B X Y Z x` is `(∇_X B)(Y, Z)` at `x` (`Variation.lean`).
-/
import RicciFlowBlueprint.MetricTrace
import RicciFlowBlueprint.OrthonormalFrame
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace RicciFlowBlueprint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

section MVFDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [IsManifold I ω M] in
/-- `mvfderiv` only depends on the germ of the function. -/
theorem _root_.Filter.EventuallyEq.mvfderiv_eq {f g : M → F} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  unfold mvfderiv
  rw [h.mfderiv_eq, h.eq_of_nhds]
  ext v
  rfl

omit [IsManifold I ω M] in
/-- **A finite sum is differentiable.** Mathlib's `MDifferentiableAt.sum` is stated for
an index type in `Type`; this is the `Type*` version. -/
theorem mdifferentiableAt_fun_sum {ι : Type*} {t : Finset ι} {f : ι → M → F} {x : M}
    (hf : ∀ i ∈ t, MDiffAt (f i) x) : MDiffAt (fun y ↦ ∑ i ∈ t, f i y) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (mdifferentiableAt_const : MDiffAt (fun _ : M ↦ (0 : F)) x)
  | insert a s ha ih =>
    have hrw : (fun y ↦ ∑ i ∈ insert a s, f i y) = (fun y ↦ f a y + ∑ i ∈ s, f i y) := by
      funext y; rw [Finset.sum_insert ha]
    rw [hrw]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

omit [IsManifold I ω M] in
/-- **`mvfderiv` of a finite sum.** -/
theorem mvfderiv_fun_sum {ι : Type*} {t : Finset ι} {f : ι → M → F} {x : M}
    (hf : ∀ i ∈ t, MDiffAt (f i) x) :
    mvfderiv I (fun y ↦ ∑ i ∈ t, f i y) x = ∑ i ∈ t, mvfderiv I (f i) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mvfderiv_const (I := I) (M := M) (0 : F)
  | insert a s ha ih =>
    have hfa : MDiffAt (f a) x := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, MDiffAt (f i) x := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hsum : MDiffAt (fun y ↦ ∑ i ∈ s, f i y) x := mdifferentiableAt_fun_sum hfs
    have hrw : (fun y ↦ ∑ i ∈ insert a s, f i y)
        = (fun y ↦ f a y + ∑ i ∈ s, f i y) := by
      funext y; rw [Finset.sum_insert ha]
    rw [hrw, mvfderiv_fun_add hfa hsum, Finset.sum_insert ha, ih hfs]

end MVFDeriv

end RicciFlowBlueprint

namespace CovariantDerivative

open RicciFlowBlueprint

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

set_option maxSynthPendingDepth 3

section Algebra

omit [FiniteDimensional ℝ E] [IsManifold I ω M] in
/-- **Antisymmetric against symmetric is zero.** If `D i` has antisymmetric coefficients
against an orthonormal basis `b`, then `∑ᵢ [B(Dᵢ, bᵢ) + B(bᵢ, Dᵢ)] = 0`, for any bilinear
form `B` — symmetry of `B` is not needed. -/
theorem sum_bilin_of_antisymm {x : M} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (D : ι → TangentSpace I x) (hD : ∀ i j, ⟪D i, b j⟫ = -⟪D j, b i⟫) :
    ∑ i, (B (D i) (b i) + B (b i) (D i)) = 0 := by
  classical
  -- the coefficient matrix, made opaque so that rewriting `D i` cannot reach it
  obtain ⟨a, hexp, hanti⟩ : ∃ a : ι → ι → ℝ,
      (∀ i, (D i : E) = ∑ j, a i j • (b j : E)) ∧ (∀ i j, a i j = -a j i) := by
    refine ⟨fun i j ↦ ⟪b j, D i⟫, fun i ↦ (b.sum_repr' (D i)).symm, fun i j ↦ ?_⟩
    show ⟪b j, D i⟫ = -⟪b i, D j⟫
    have e1 : ⟪b j, D i⟫ = ⟪D i, b j⟫ := real_inner_comm _ _
    have e2 : ⟪b i, D j⟫ = ⟪D j, b i⟫ := real_inner_comm _ _
    rw [e1, e2]
    exact hD i j
  -- expansions of a bilinear form in the two slots, stated for plain vectors of `E`
  have key₁ : ∀ (c : ι → ℝ) (e : ι → E) (w : E),
      B (∑ j, c j • e j) w = ∑ j, c j * B (e j) w := by
    intro c e w
    rw [map_sum, FunLike.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have key₂ : ∀ (c : ι → ℝ) (e : ι → E) (w : E),
      B w (∑ j, c j • e j) = ∑ j, c j * B w (e j) := by
    intro c e w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
  have step : ∀ i, B (D i) (b i) + B (b i) (D i)
      = ∑ j, a i j * (B (b j) (b i) + B (b i) (b j)) := by
    intro i
    have e1 : B (D i) (b i) = ∑ j, a i j * B (b j) (b i) := by
      rw [hexp i]; exact key₁ (a i) (fun j ↦ b j) (b i)
    have e2 : B (b i) (D i) = ∑ j, a i j * B (b i) (b j) := by
      rw [hexp i]; exact key₂ (a i) (fun j ↦ b j) (b i)
    rw [e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ step i]
  -- the double sum is its own negative
  have hS : ∑ i, ∑ j, a i j * (B (b j) (b i) + B (b i) (b j))
      = -∑ i, ∑ j, a i j * (B (b j) (b i) + B (b i) (b j)) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hanti j i]; ring
  linarith [hS]

end Algebra

section Frame

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

/-- **The connection coefficients of an orthonormal frame are antisymmetric.** For a
metric connection and a frame whose inner products are locally constant,
`⟪∇_X eᵢ, eⱼ⟫ = -⟪∇_X eⱼ, eᵢ⟫`. -/
theorem inner_cov_antisymm (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {ι : Type*} {fr : ι → Π y : M, TangentSpace I y} {X : Π y : M, TangentSpace I y} {x : M}
    (hfr : ∀ i, MDiffAt (T% (fr i)) x)
    (hconst : ∀ i j, (fun y ↦ ⟪fr i y, fr j y⟫) =ᶠ[𝓝 x] fun _ ↦ ⟪fr i x, fr j x⟫)
    (i j : ι) :
    ⟪cov (fr i) x (X x), fr j x⟫ = -⟪cov (fr j) x (X x), fr i x⟫ := by
  have h := hcov.mvfderiv_inner_eq (V := fun y : M ↦ TangentSpace I y) X (hfr i) (hfr j)
  have hz : mvfderiv I (fun y ↦ ⟪fr i y, fr j y⟫) x = 0 := by
    rw [(hconst i j).mvfderiv_eq]
    exact mvfderiv_const _
  rw [hz] at h
  simp only [_root_.zero_apply] at h
  have e : ⟪fr i x, cov (fr j) x (X x)⟫ = ⟪cov (fr j) x (X x), fr i x⟫ := real_inner_comm _ _
  rw [e] at h
  linarith [h]

-- BENCH: metric-trace-commutes
/-- **The metric trace commutes with the covariant derivative.** For a metric connection
and a local orthonormal frame `fr` of `TM` near `x`,

  `X (∑ᵢ B(frᵢ, frᵢ)) = ∑ᵢ (∇_X B)(frᵢ, frᵢ)`.

The frame need not be parallel: the `2n²` correction terms cancel because the connection
coefficients of an orthonormal frame are antisymmetric while `B(eⱼ,eᵢ) + B(eᵢ,eⱼ)` is
symmetric. `B` itself need not be symmetric. -/
theorem mvfderiv_sum_eq_sum_covBilin
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {B : M → E →L[ℝ] E →L[ℝ] ℝ} {X : Π y : M, TangentSpace I y} {x : M}
    {ι : Type*} [Fintype ι] {fr : ι → Π y : M, TangentSpace I y}
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (hb : ∀ i, fr i x = b i)
    (hfr : ∀ i, MDiffAt (T% (fr i)) x)
    (hconst : ∀ i j, (fun y ↦ ⟪fr i y, fr j y⟫) =ᶠ[𝓝 x] fun _ ↦ ⟪fr i x, fr j x⟫)
    (hB : ∀ i, MDiffAt (fun y ↦ B y (fr i y) (fr i y)) x) :
    mvfderiv I (fun y ↦ ∑ i, B y (fr i y) (fr i y)) x (X x)
      = ∑ i, cov.covBilin B X (fr i) (fr i) x := by
  -- the corrections cancel
  have key : ∑ i, (B x (cov (fr i) x (X x)) (fr i x)
      + B x (fr i x) (cov (fr i) x (X x))) = 0 := by
    have hD : ∀ i j, ⟪cov (fr i) x (X x), b j⟫ = -⟪cov (fr j) x (X x), b i⟫ := by
      intro i j
      rw [← hb i, ← hb j]
      exact cov.inner_cov_antisymm hcov hfr hconst i j
    have h0 := sum_bilin_of_antisymm b (B x) (fun i ↦ cov (fr i) x (X x)) hD
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hb i]
  have expand : ∑ i, cov.covBilin B X (fr i) (fr i) x
      = (∑ i, mvfderiv I (fun y ↦ B y (fr i y) (fr i y)) x (X x))
        - ∑ i, (B x (cov (fr i) x (X x)) (fr i x)
            + B x (fr i x) (cov (fr i) x (X x))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [covBilin]; ring
  rw [expand, key, sub_zero, mvfderiv_fun_sum (fun i _ ↦ hB i),
    _root_.sum_apply]

end Frame

section OfFrame

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I] [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] in
/-- **A local orthonormal frame is an orthonormal basis of each fibre over its base set.** -/
theorem exists_orthonormalBasis_of_isOrthonormalFrameOn
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) {y : M} (hy : y ∈ u) :
    ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y), ∀ i, b i = fr i y := by
  classical
  let bas : Module.Basis ι ℝ (TangentSpace I y) :=
    Module.Basis.mk (hs.linearIndependent hy) (hs.generating hy)
  have hcoe : ⇑bas = fun i ↦ fr i y := Module.Basis.coe_mk _ _
  have hon : Orthonormal ℝ ⇑bas := by rw [hcoe]; exact hs.orthonormal hy
  refine ⟨bas.toOrthonormalBasis hon, fun i ↦ ?_⟩
  have h1 := congrFun (Module.Basis.coe_toOrthonormalBasis bas hon) i
  rw [show (bas.toOrthonormalBasis hon) i = (bas.toOrthonormalBasis hon : ι → _) i from rfl, h1,
    hcoe]

-- BENCH: metric-trace-commutes-frame
/-- **The metric trace commutes with the covariant derivative**, with the frame packaged:
over the base set of a `C¹` orthonormal frame,
`X (∑ᵢ B(frᵢ, frᵢ)) = ∑ᵢ (∇_X B)(frᵢ, frᵢ)`. -/
theorem mvfderiv_sum_eq_sum_covBilin_of_frame
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {B : M → E →L[ℝ] E →L[ℝ] ℝ} {X : Π y : M, TangentSpace I y}
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M} {x : M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hB : ∀ i, MDiffAt (fun y ↦ B y (fr i y) (fr i y)) x) :
    mvfderiv I (fun y ↦ ∑ i, B y (fr i y) (fr i y)) x (X x)
      = ∑ i, cov.covBilin B X (fr i) (fr i) x := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hx
  refine cov.mvfderiv_sum_eq_sum_covBilin hcov b (fun i ↦ (hb i).symm)
    (fun i ↦ (hs.toIsLocalFrameOn.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero)
    (fun i j ↦ ?_) hB
  filter_upwards [hu.mem_nhds hx] with y hy
  rw [orthonormal_iff_ite.mp (hs.orthonormal hy) i j,
    orthonormal_iff_ite.mp (hs.orthonormal hx) i j]

end OfFrame

end CovariantDerivative
