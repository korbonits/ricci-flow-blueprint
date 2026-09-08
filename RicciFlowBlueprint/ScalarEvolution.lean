/-
`div div Ric = ½ Δ scal`, and the scalar curvature under the flow.

The second contraction of the second Bianchi identity says `2 div Ric = d scal`
(`Divergence.lean`). Taking the divergence once more turns it into
`div div Ric = ½ Δ scal` — an identity between the two objects that
`sum_inner_covTwoTensor_eq` produces, and the last thing standing between
`tr_g(∂ₜ Ric) = div div h − tr_g(Δ_g h)` and `∂ₜ scal = Δ scal + 2|Ric|²`.

Everything here is geometry for a fixed metric connection, so it is stated in a section
with an ambient `RiemannianBundle` binder; only the final specialisation to `∂ₜ g = −2 Ric`
has to work under the `letI` that a varying metric forces.

Argument order follows `CovariantDerivative`: `cov σ x (X x)` is `(∇_X σ) x`.
-/
import RicciFlowBlueprint.OneForm
import RicciFlowBlueprint.Divergence

open Bundle Filter VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  [VectorBundle ℝ E (fun (x : M) ↦ TangentSpace I x)] [T2Space M]

variable (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov 2]

variable {ι : Type*} [Fintype ι]

-- BENCH: div-ricci-as-one-form
/-- **`div Ric = ½ d scal` as one-forms.** The second contraction of the second Bianchi
identity, read as an identity of one-forms rather than a frame sum: `divBilin` is the 1&2 trace
of `∇Ric`, which `covBilin_ricciForm_eq_covRicci` turns into the sum of `covRicci` that
`two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt` evaluates. -/
theorem divBilin_ricciForm_eq (htor : cov.torsion = 0)
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {Y : Π y : M, TangentSpace I y} {x : M} (hY : CMDiff 3 (T% Y))
    (hb : IsMDiffBilinAt (I := I) (fun y ↦ cov.ricciForm y) x)
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i) :
    cov.divBilin (fun y ↦ cov.ricciForm y) Y x
      = (1 / 2 : ℝ) * mvfderiv I (fun y ↦ cov.scalarCurvatureAt y) x (Y x) := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hY2 : CMDiff 2 (T% Y) := hY.of_le (by norm_num)
  have hfr1 : ∀ i, MDiffAt (T% (fr i)) x := fun i ↦ (hfr i).mdifferentiable (by norm_num) x
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  rw [cov.divBilin_eq_sum_frame hb (hY2.mdifferentiable (by norm_num) x) hfr1 b hbv]
  have hterm : ∀ i, cov.covBilin (fun y ↦ cov.ricciForm y) (fr i) (fr i) Y x
      = cov.covRicci (fr i) (fr i) Y x := fun i ↦
    cov.covBilin_ricciForm_eq_covRicci (hfr2 i) (hfr i) hY
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
  have hsecond := cov.two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt htor hmet hY hs hu hx hfr
  linarith [hsecond]

/-- **`div Ric = ½ d scal` as an identity of one-forms**, at every point of the frame's base
set. Same content as `divBilin_ricciForm_eq`, packaged so that its divergence can be taken. -/
theorem divBilinForm_ricciForm_eq (htor : cov.torsion = 0)
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hbg : IsMDiffBilin (I := I) (fun y ↦ cov.ricciForm y))
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) {y : M} (hy : y ∈ u) :
    cov.divBilinForm (hbg y)
      = ((1 / 2 : ℝ) • (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y :
          TangentSpace I y →L[ℝ] ℝ) : E →L[ℝ] ℝ) := by
  obtain ⟨b, hbv⟩ := exists_orthonormalBasis_of_isOrthonormalFrameOn hs hy
  ext v
  obtain ⟨V, hV, hVv⟩ :=
    RicciFlowBlueprint.exists_contMDiff_extension (n := 3) (x := y)
      (show TangentSpace I y from v)
  have hV1 : MDiffAt (T% V) y := hV.mdifferentiable (by norm_num) y
  have hstep : cov.divBilinForm (hbg y) (V y) = cov.divBilin (fun z ↦ cov.ricciForm z) V y :=
    cov.divBilinForm_apply (hbg y) hV1
  rw [← hVv, hstep,
    cov.divBilin_ricciForm_eq htor hmet hV (hbg y) hs hu hy hfr b fun i ↦ (hbv i).symm]
  rfl

-- BENCH: div-div-ricci
/-- **`div div Ric = ½ Δ scal`.** The second contraction of the second Bianchi identity, with
the divergence taken once more: `div Ric` is the one-form `½ d scal`, and the divergence of
`df` is `Δf` (`laplacianFun_eq_divOneForm`, a `rfl`). This is the identity that turns
`tr_g(∂ₜ Ric) = div div h − tr_g(Δ_g h)` into a statement about `Δ scal`. -/
theorem divDivBilin_ricciForm_eq (htor : cov.torsion = 0)
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hbg : IsMDiffBilin (I := I) (fun y ↦ cov.ricciForm y)) {x : M}
    (hscal : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y :
        TangentSpace I y →L[ℝ] ℝ)) x)
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    cov.divDivBilin (fun y ↦ cov.ricciForm y) hbg x
      = (1 / 2 : ℝ) * cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x := by
  -- name the one-form `d scal` at the `E` type, so the `•` below is `E`'s and not
  -- `TangentSpace`'s — otherwise `divOneForm_smul` does not match
  obtain ⟨v, hv⟩ : ∃ v : M → E →L[ℝ] ℝ, v = fun y ↦
      (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y : TangentSpace I y →L[ℝ] ℝ) := ⟨_, rfl⟩
  have hscal' : IsMDiffOneFormAt (I := I) v x := by rw [hv]; exact hscal
  have hgerm : cov.divBilinOneForm (fun y ↦ cov.ricciForm y) hbg
      =ᶠ[𝓝 x] fun y ↦ ((1 / 2 : ℝ) • v y : E →L[ℝ] ℝ) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    rw [hv]
    exact cov.divBilinForm_ricciForm_eq htor hmet hbg hs hu hfr hy
  rw [divDivBilin, cov.divOneForm_congr hgerm, cov.divOneForm_smul _ v hscal',
    cov.laplacianFun_eq_divOneForm, hv]

-- BENCH: trace-ricci-variation-is-laplacian-scal
/-- **`tr_g(∂ₜ Ric) = Δ scal` under the Ricci flow.** The two canonical double traces of
`∇²h` that `sum_inner_covTwoTensor_eq` produces, evaluated at `h = −2 Ric`: the first is
`div div h = −2 · ½ Δ scal = −Δ scal`, the second `tr_g(Δ_g h) = Δ(tr_g h) = −2 Δ scal`, and
`−Δ scal − (−2 Δ scal) = Δ scal`. Only `∇²h`'s linearity in `h` is needed to get there —
everything downstream is already proved for `Ric` itself. -/
theorem sum_cov2Bilin_neg_two_ricciForm_eq (htor : cov.torsion = 0)
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (hbg : IsMDiffBilin (I := I) (fun y ↦ cov.ricciForm y)) {x : M}
    (hscal : IsMDiffOneFormAt (I := I)
      (fun y ↦ (mvfderiv I (fun z ↦ cov.scalarCurvatureAt z) y :
        TangentSpace I y →L[ℝ] ℝ)) x)
    (hw : IsMDiffOneFormAt (I := I)
      (cov.divBilinOneForm (fun y ↦ cov.ricciForm y) hbg) x)
    {fr : ι → Π y : M, TangentSpace I y} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u) (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (hbv : ∀ i, fr i x = b i)
    (hh : ∀ (U V : Π y : M, TangentSpace I y) (y : M),
      MDiffAt (fun z ↦ cov.ricciForm z (U z) (V z)) y)
    (hd : ∀ a c d, MDiffAt
      (fun y ↦ cov.covBilin (fun z ↦ cov.ricciForm z) (fr a) (fr c) (fr d) y) x)
    (hcb : ∀ j, cov.IsMDiffCovBilinAt (fun y ↦ cov.ricciForm y) (fr j) (fr j) x) :
    (∑ i, ∑ j, cov.cov2Bilin (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ))
        (fr i) (fr j) (fr j) (fr i) x)
      - ∑ i, ∑ j, cov.cov2Bilin (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ))
        (fr i) (fr i) (fr j) (fr j) x
      = cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x := by
  have hfr2 : ∀ i, CMDiff 2 (T% (fr i)) := fun i ↦ (hfr i).of_le (by norm_num)
  -- pull the constant out of both double sums
  have hpull : ∀ (a c d e : ι),
      cov.cov2Bilin (fun y ↦ ((-2 : ℝ) • cov.ricciForm y : E →L[ℝ] E →L[ℝ] ℝ))
          (fr a) (fr c) (fr d) (fr e) x
        = (-2 : ℝ) * cov.cov2Bilin (fun y ↦ cov.ricciForm y) (fr a) (fr c) (fr d) (fr e) x :=
    fun a c d e ↦ cov.cov2Bilin_smul_form _ _ hh (hd c d e)
  -- the first double trace is `div div Ric = ½ Δ scal`
  have hfirst : (∑ i, ∑ j, cov.cov2Bilin (fun y ↦ cov.ricciForm y)
      (fr i) (fr j) (fr j) (fr i) x)
      = (1 / 2 : ℝ) * cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x := by
    rw [← cov.divDivBilin_eq_sum hmet hbg hw hs hu hx hfr2 (fun j i ↦ hd i i j) b hbv]
    exact cov.divDivBilin_ricciForm_eq htor hmet hbg hscal hs hu hx hfr
  -- the second is `tr_g(Δ_g Ric) = Δ(tr_g Ric) = Δ scal`
  have hsecond : (∑ i, ∑ j, cov.cov2Bilin (fun y ↦ cov.ricciForm y)
      (fr i) (fr i) (fr j) (fr j) x)
      = cov.laplacianFun (fun z ↦ cov.scalarCurvatureAt z) x := by
    have htrace : cov.laplacianFun (traceBilin (I := I) (fun y ↦ cov.ricciForm y)) x
        = ∑ j, cov.laplacianBilin (fun y ↦ cov.ricciForm y) (fr j) (fr j) x :=
      cov.laplacianFun_traceBilin_eq hmet hbg hscal hs hu hx b hbv hfr2
        (fun y _ i ↦ hh (fr i) (fr i) y) (fun i j ↦ hd i j j) hcb
    rw [Finset.sum_comm]
    have hlap : ∀ j, cov.laplacianBilin (fun y ↦ cov.ricciForm y) (fr j) (fr j) x
        = ∑ i, cov.cov2Bilin (fun y ↦ cov.ricciForm y) (fr i) (fr i) (fr j) (fr j) x :=
      fun j ↦ cov.laplacianBilin_eq_sum_frame (hbg x) (hcb j) (hfr2 j) (hfr2 j) hfr2 b hbv
    rw [← Finset.sum_congr rfl fun j _ ↦ hlap j, ← htrace]
    -- `traceBilin ricciForm` *is* `scalarCurvatureAt`: the same frame sum, by definition
    rfl
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hpull i j j i,
    Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hpull i i j j]
  simp only [← Finset.mul_sum]
  rw [hfirst, hsecond]
  ring

end CovariantDerivative
