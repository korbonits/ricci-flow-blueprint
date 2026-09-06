# Ricci flow blueprint — working notes

A `leanblueprint` for Ricci flow. Live: https://korbonits.github.io/ricci-flow-blueprint/
Milestone: Hamilton 1982. Terminal node: Perelman's spherical space form theorem.

## State (2026-09-06)

`lake build` clean, **no `sorry`**, axiom-free — `#print axioms` shows only
`[propext, Classical.choice, Quot.sound]`. Tracks mathlib `master` (pinned rev
in `lake-manifest.json`) on Lean `v4.34.0-rc2`, because mathlib4 #36845
(Levi-Civita) merged after the last release and `LeviCivita.lean` builds on it.

| File | Contents |
| --- | --- |
| `Curvature.lean` | `curvature`, `curvature_antisymm`, `bianchi_first`, `curvature_smul_*` and `curvature_add_*` (tensoriality, all three slots), `tensorialAt_curvature_fst/snd`, `neg_apply`, `sub_apply`, `mdiffAt_cov_apply` |
| `LieBracketDerivation.lean` | `lieBracket_apply_fun`, `mlieBracket_apply_fun` (any manifold, corners allowed), `jacobi_mlieBracket_apply`, model-space collapses |
| `Ricci.lean` | `ricci` — **defined**; `ricci_sub_ricci_swap` |
| `Sectional.lean` | `sectionalCurvature`, `sectionalCurvature_basis_change` |
| `LeviCivita.lean` | `exists_leviCivita`, `leviCivita_unique` (on differentiable sections — the `∃!` form was never provable), `curvature_eq_of_isLeviCivita`, `ricci_eq_of_isLeviCivita`, `sectionalCurvature_eq_of_isLeviCivita` |
| `LeviCivitaSmooth.lean` | `contMDiffCovariantDerivative_leviCivitaConnection` — **Levi-Civita is `C^k` for a `C^{k+1}` metric** (Mathlib leaves this to "future PRs"); criteria `contMDiffAt_clm_of_basis`, `contMDiffAt_section_of_inner_localFrame`, `contMDiffAt_mvfderiv_apply`, `contMDiffAt_koszul`; instance for `k = 1`; `ricciOfMetric`, `sectionalCurvatureOfMetric` |
| `Flow.lean` | `IsRicciFlowAt/On`, `isRicciFlowAt_const_iff`, `isRicciFlowAt_iff_of_isLeviCivita`, `isRicciFlowOn_iff_ricciOfMetric` — **the flow is `∂g/∂t = -2 Ric(g t)` with `Ric` a function of `g`**; `ricciFlow_shortTime_existence` (`proof_wanted`); the analytic-frontier survey lives in its header |
| `Hamilton.lean` | `hamilton_1982` — **stated**, `proof_wanted`, no sorry, no axiom. Predicates require a `C¹` witness and `C²` test fields (corrected 2026-09-04: the old `HasConstSecLC` quantified over arbitrary fields, i.e. over junk). `admitsPositiveRicciMetric_iff` / `admitsConstPositiveSecMetric_iff` restate them via `ricciOfMetric` / `sectionalCurvatureOfMetric` |
| `Pinching.lean` | **branch closed**: Hamilton's curvature ODE in dimension 3 — ordering, positive Ricci, `λ ≤ C(μ+ν)` preserved; `pinching_antitone` (Hamilton Thm 10.1, ODE half). Linear Grönwall helpers `nonpos_of_deriv_le_mul` etc. No manifold |
| `Hessian.lean` | `hessian` (∇²), `hessian_sub_hessian_swap` (Ricci identity), tensoriality + `hessianAt`, `hessianFun` + `hessianFun_symm`, `laplacian` + `laplacian_eq_sum` (basis-independent metric trace, `OrthonormalBasis.sum_apply_self_eq`) |
| `SecondDerivativeTest.lean` | **proved**: `deriv2_nonneg_of_isLocalMin`, `fderiv2_nonneg_of_isLocalMin`, `fderiv_fderiv_apply_nonneg_of_isLocalMin` (chart-side core), `hessianFun_nonneg_of_isLocalMin` and `laplacianFun_nonneg_of_isLocalMin` on a **boundaryless manifold** (transport through `extChartAt`, same pattern as `mlieBracket_apply_fun`), plus the `*_model` versions. The connection term `(∇_X X) f` dies at a critical point, so any `cov` works |
| `MaximumPrinciple.lean` | **proved**: the scalar maximum principle on a compact space with the differential inequality assumed at spatial minima (`le_of_deriv_ge_at_min`, `le_of_deriv_le_at_max`). ε-perturbation `φ − ε e^{(2K+1)t}` + first touching time. No Laplacian |
| `TensorMaximumPrinciple.lean` | **proved**: Hamilton's tensor maximum principle abstractly (`mem_of_deriv_le_at_max`): `K` closed convex in a complete real inner product space, hypothesis `⟪n, ∂ₜu⟫ ≤ ⟪n, F(u)⟫` at spatial maxima of `⟪n,u⟫`, ODE-invariance in Nagumo form `⟪n, F p⟫ ≤ 0` for outward normals (`subtangential_of_invariant` derives it). Nearest point via `exists_norm_eq_iInf_of_complete_convex` + `norm_eq_iInf_iff_real_inner_le_zero`; distance via `Metric.infDist`, `le_infDist`. Same skeleton as the scalar one |
| `ManifoldMaximumPrinciple.lean` | **proved**: both principles on a closed Riemannian manifold (`le_of_laplacian`, `le_of_laplacian'`, `mem_of_laplacian`) for `∂ₜu = Δu + F(u)`, `u(t,·)` `C²`: the abstract theorems with the touching-point hypothesis discharged by `laplacianFun_nonneg_of_isLocalMin`. Tensor case is the trivial bundle, equation componentwise `⟪n, ∂ₜu⟫ = Δ⟪n,u⟫ + ⟪n, F u⟫`; a max of `⟪n,u⟫` is a min of `⟪-n,u⟫`, so no linearity lemma is needed. `hessianFun_neg`, `laplacianFun_neg` added to `Hessian.lean` |
| `Variation.lean` | **proved**: `covBilin` (∇ of a bilinear form field), `koszul_bilin_eq` (Koszul combination of a symmetric `h` through a torsion-free `∇` is `∇h`-terms `+ 2h(∇_X Y,Z)`), `leviCivitaOfMetric`, `inner_leviCivitaOfMetric_eq` (Koszul in `g.inner`), `hasDerivAt_inner_leviCivitaOfMetric` (Koszul differentiated in `t`), `inner_deriv_leviCivitaOfMetric_eq` (**first variation of ∇**). Hypotheses: `∂ₜ` commutes with `X(g(Y,Z))` for the fields at hand; differentiability of `t ↦ ∇ᵗ_X Y` (vector form only) |
| `CurvatureVariation.lean` | **proved**: `covEnd` (∇ of an `End`-valued one-form), `curvature_eq_add_covEnd` (curvature of `∇ + A`, `∇` torsion-free — algebraic), `hasDerivAt_curvatureE` (`∂ₜ Rᵗ = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)` along `∇ᵗ = ∇ + Aᵗ`), `exists_hasDerivAt_clm_of_apply` (coordinatewise ⇒ CLM-valued derivative), `differenceE` (Mathlib's `difference` on `E`), `derivDifferenceE` (`Ȧ = ∂ₜ∇` as `deriv`, no existential), `inner_derivDifferenceE_eq`, `hasDerivAt_curvatureE_leviCivitaOfMetric` (**first variation of Rm along metrics**). Hypotheses: `CommutesWithMvfderiv` (the `Variation.lean` commutation, all fields) and `∂ₜ`/`∇_X` commuting on `Aᵗ(Y,Z)` |
| `Bianchi.lean` | **proved**: `contMDiff_cov_apply` (`C^k` connection, `C^{k+1}` section, `C^k` field ⇒ `C^k` covariant derivative), `mlieBracket_sub_left'`, `covCurvature` (`(∇_X R)(Y,Z)W`), `bianchi_second` (**second Bianchi**, `C²` connection, `C²` fields, `C³` argument; no metric). The proof is the first-Bianchi pattern: split the sections, rewrite `∇_X Y − ∇_Y X` as `[X,Y]` in both the direction slot and as sections, `linear_combination (norm := module)` with Jacobi |
| `MetricTrace.lean` | **proved**: `sharpE` (`g♯⁻¹ ∘ B♭`), `metricTraceE` (`tr(g♯⁻¹ B♭)`), `metricTraceE_eq_sum` (= `∑ᵢ B(eᵢ,eᵢ)` over any `g`-orthonormal basis, via `LinearMap.trace_eq_sum_inner`), `sharpE_apply_eq_sum`, `metricTraceE_comp_sharpE_eq_sum` (`⟨h,B⟩_g`), `hasDerivAt_inverse_innerE` (`∂ₜ g⁻¹ = −g⁻¹ h g⁻¹`, from `contDiffAt_map_inverse` plus differentiating `g ∘ g⁻¹ = id`), `hasDerivAt_metricTraceE` (**`∂ₜ tr_{g_t} B_t = tr Ḃ − ⟨h,B⟩`**). All at a point on `E`. `metricTraceE_innerE_comp`, `ricci_eq_metricTraceE` bridge to `ricci` |
| `RicciVariation.lean` | **proved**: `CommutesWithCov` (∂ₜ/∇_X commute on the difference-tensor sections, all fields), `curvatureEndoE` (`v ↦ R(v,X)Y` via `mkHom`, typed on `E` by ascription — an expected type `E →L E` on a bare `mkHom` leaves `?V x =?= E` unsolved), `hasDerivAt_ricciOfMetric` (**∂ₜ Ric = tr ∂ₜ[v ↦ R(v,X)Y]**, any manifold). Model space: `constField`, `ricci_add_right_const`/`ricci_smul_right_const` (second slot on constant fields), `ricciE` (Ricci form as `E →L E →L ℝ` via `LinearMap.mk₂`), `scalarCurvatureOfMetric'` (= `Scalar.lean`'s), `hasDerivAt_scalarCurvatureOfMetric'` (`∂ₜ R = tr_g Ṙic − ⟨h,Ric⟩`), `innerE_deriv_eq_of_isRicciFlowAt` (`h = −2 Ric` from the flow by uniqueness), `hasDerivAt_scalarCurvatureOfMetric'_of_isRicciFlowAt` (**∂ₜ R = tr_g Ṙic + 2\|Ric\|²**). Never `local notation` over a section variable: hygiene hides `E` and everything downstream is silently auto-bound |
| `Homogeneous.lean` | **branch closed**: `koszul`, torsion/compat, Levi-Civita uniqueness, `contDiffAt_ricciField`, `ricciFlow_leftInvariant` |
| `Milnor.lean` | **branch closed**: Koszul formula, Ricci in structure constants, diagonal Ricci `rᵢ = 2μⱼμₖ`, Heisenberg, Isenberg–Jackson ODE |

## Four corrected beliefs — do not re-derive these wrong

0. **Levi-Civita uniqueness is NOT `∃!`.** A `CovariantDerivative` is
   unconstrained on sections not differentiable at the point (every law and
   predicate quantifies over differentiable sections), so two Levi-Civita
   connections can differ there. Mathlib's `IsLeviCivitaConnection.uniqueness`
   is pointwise on differentiable sections, and that is all curvature needs.

1. **`mkHom₃` was never needed and would not have worked.** The trace is in the
   first slot only, so one-slot `TensorialAt.mkHom` suffices. A `mkHom₃` copied
   from `mkHom₂` quantifies over merely-`MDiffAt` sections, whereas first-slot
   tensoriality of `R` needs the third-slot field to be `C²`.
2. **Ricci is NOT symmetric for a general torsion-free connection.** Tracing
   first Bianchi gives `Ric(X,Y) − Ric(Y,X) = −tr R(X,Y)`; that vanishes for a
   *metric* connection, where `R(X,Y)` is skew-adjoint. Symmetry is the
   corollary, not the theorem.
3. **The tangent-bundle "diamond" is not a diamond.** The fibre instances are
   definitionally equal (`rfl` succeeds for `AddCommGroup` and
   `TopologicalSpace`; `#synth` picks `instAddCommGroupTangentSpace`). What
   fails is elaboration over defeq terms — see below.

## Stating anything where the metric VARIES

Two conditions are **jointly necessary** for `cov.IsMetricCompatible` to elaborate:

1. the `RiemannianBundle` instance must be an ambient **binder**
   (`variable [RiemannianBundle …]`), not introduced by `letI`/`haveI` in a term;
2. `cov` must be bound by an **existential** — not an explicit parameter, not a
   structure field, and not a parameter in *hypothesis* position.

So: elaborate the predicate ONCE in a section satisfying both, then only *apply*
that constant under `letI := ⟨g.toRiemannianMetric⟩`. See `Hamilton.lean`'s header
(`HasPositiveRicciLC` → `AdmitsPositiveRicciMetric`) and `Flow.lean`.
**Corollary:** converse lemmas must be iffs between existentials. Ten variants
were tested to establish this. It is a workaround, not a fix — open Zulip question.

## Roadmap (revised 2026-09-06)

The dated diary that used to sit here is condensed; the Lean-level lessons it
carried are now in "Lean gotchas". Chronology, for the record: mathlib bump and
Levi-Civita (09-04), its smoothness and the textbook flow equation (09-04), the
curvature ODE invariants and both abstract maximum principles (09-05/06), the
second-derivative test (model space, then manifold), the variations of the
connection, curvature, metric trace, Ricci and scalar curvature (09-05/06),
second Bianchi (09-05), the principles on a manifold and CI hardening (09-06).

**Where Hamilton 1982 stands.** The theorem is stated honestly
(`hamilton_1982`, `proof_wanted`). Its proof splits into a curvature-pinching
half and an analytic half.

Pinching half, in order of what is done:
1. Curvature ODE and its invariant sets (`Pinching.lean`) — done.
2. Tensor maximum principle — done abstractly and on a closed manifold for a
   fixed fibre (`TensorMaximumPrinciple.lean`, `ManifoldMaximumPrinciple.lean`).
3. Evolution equation `∂ₜ Rm = Δ Rm + Q(Rm)` (`lem:evolution-rm`) — the
   inputs are done (`∂ₜ Rm` in terms of `∇²h`, second Bianchi, the metric
   trace and its variation, `∂ₜ Ric`, `∂ₜ R = tr_g Ṙic + 2|Ric|²`); the
   rewrite to `Δ Rm + Q` is not.
4. Transfer of the invariant sets to the flow (`lem:pinching`) — not started;
   needs 3, the bundle version of 2 with an evolving fibre metric (Uhlenbeck's
   trick), convexity of eigenvalue-defined sets (variational
   characterisation of eigenvalues), and Nagumo's condition lifted from the
   eigenvalue ODE to the operator ODE by equivariance.

Analytic half: short-time existence, Shi's estimates, long-time existence,
convergence of the normalised flow. Parabolic theory Mathlib does not have.
Nothing here is started; see "Where the real gaps are".

**Next, in order.**
1. The manifold trace lemma `X(tr_g B) = tr_g(∇_X B)` for a metric
   connection. Needs a local frame of sections and the inverse Gram matrix
   (`extend` is orthonormal only at `x`; differentiate `y ↦ ∑ᵢⱼ Gⁱʲ(y)
   B(Eᵢ,Eⱼ)(y)` at `x`, where `G(x) = I` and `∂G = ⟨∇Eᵢ,Eⱼ⟩ + ⟨Eᵢ,∇Eⱼ⟩` by
   compatibility, and the frame terms cancel). This is the gate for
   everything with a Laplacian in it.
2. Contracted second Bianchi, `tr_g Ṙic = ΔR` under the flow, hence
   `∂ₜ R = ΔR + 2|Ric|²` — the scalar case of `lem:evolution-rm` — and with
   the scalar maximum principle, Hamilton's `R_min` is nondecreasing: the
   first flow *estimate* in the project.
3. `∂ₜ Rm = Δ Rm + Q` (Uhlenbeck's trick, `Q = Rm² + Rm#` in dimension three).
4. Item 4 of the pinching half above.

**Upstream candidates** (Mathlib-general, no dependence on the curvature
stack unless noted): `VectorField.lieBracket_apply_fun`; `neg_apply`,
`sub_apply`, `mdiffAt_cov_apply`, `contMDiff_cov_apply` (`C^k` connection ⇒
`C^k` covariant derivative); `mlieBracket_sub_left'`;
`exists_hasDerivAt_clm_of_apply` (coordinatewise ⇒ CLM-valued derivative);
`hasDerivAt_inverse_innerE`'s pattern (derivative of `inverse` from
`contDiffAt_map_inverse` plus `f ∘ f⁻¹ = id`); `hessianFun_neg`; and the
big one, smoothness of `leviCivitaConnection` (`LeviCivitaSmooth.lean`,
which Mathlib's `LeviCivita.lean` lists as future work — weaken
`IsManifold I ω M` to `C^{k+2}` first). Post the Zulip question
(`#mathlib4`, "RiemannianBundle: metrics as instances vs values", tag
`sgouezel`) before upstreaming anything that quantifies over metrics.
Small PRs first; budget the time for conventions, not mathematics.

**Not yet:** upstreaming curvature/Ricci/sectional (wait for the Zulip
answer), anything parabolic, any writing-up.

## Where the real gaps are

- **Levi-Civita existence is NOT needed to define the flow** — the per-slice
  `∀ t, ∃ cov` is equivalent to the textbook equation, now as a theorem
  (`isRicciFlowOn_iff_ricciOfMetric`, using smoothness of the connection from
  `LeviCivitaSmooth.lean`). Both formulations are kept; the existential one is
  what elaborates under `letI`.
- **Three distinct parabolic theories** are on the road, not one: Ricci flow,
  harmonic map flow (uniqueness of the standard solution), curve-shrinking flow
  (finite extinction).
- **Second independent analytic gap:** Cheeger–Gromov compactness. Mathlib has
  Gromov–Hausdorff for compact metric spaces; pointed smooth convergence of
  manifolds under curvature bounds does not exist. First bites above Hamilton.
- Mathlib has **no maximal-solution ODE theory** — hence germ uniqueness in
  `Homogeneous.lean`.
- **No global `C²` extension of a tangent vector** (bump function times
  `FiberBundle.extend`, or any section through a given `v ∈ T_xM` that is
  `C²` everywhere). `ricci`'s second slot needs one, so Ricci is not a
  pointwise bilinear form on a general manifold, and the scalar curvature
  (`Scalar.lean`) and `∂ₜ R` (`RicciVariation.lean`) are on the model space
  only. First bites when the trace lemma (Next 1) is applied to `Ric`.
- **The metric trace does not yet commute with `∇`** on the manifold
  (Next 1). Every Laplacian identity — contracted Bianchi, `ΔR`, `Δ Rm` —
  waits on it.

## Lean gotchas

- Use `[IsManifold I ω M]`. Instance search will not see through
  `minSmoothness ℝ n = n`; `ω` synthesises `3`, `(2:ℕ∞)+1` and `minSmoothness ℝ 2`.
- Metric reaches `TM` via `[RiemannianBundle (fun x ↦ TangentSpace I x)]`, never a
  raw `[∀ x, InnerProductSpace ℝ (TangentSpace I x)]`.
- **lean4#14949 (unification sees through `TangentSpace`)**: applying a lemma
  stated for a general bundle `V` to `TangentSpace I` can infer the wrong
  fibre instances (`fun _ ↦ NormedAddCommGroup E`). Pass
  `(V := fun x : M ↦ TangentSpace I x)` explicitly, or restate the lemma for
  the tangent bundle (`ContMDiffAt.inner_bundle'` in `LeviCivitaSmooth.lean`,
  as mathlib does in `LeviCivita.lean`).
- `omit [..] in` goes *before* the docstring, not between docstring and
  `theorem`. `set x := e with h` then `rw [← h]` fails when `e` sits under
  dependent types (trivialisations); write the term out instead.
- `ContMDiffAt.div_const`/`.mul` on `ℝ` want a Lie-group instance ℝ lacks;
  use `(contDiffAt_id.mul contDiffAt_const).comp_contMDiffAt`.
- ODE comparison: `HasDerivAt.neg` produces `(-A) u`, and `.add`/`.sub` produce
  `(m + n) t` — `simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]` before
  `ring`. `ContinuousOn a (Icc 0 T)` does not give `ContinuousAt` at the
  endpoints; extend by `projIcc` to get a `Continuous` integrand for
  `intervalIntegral.integral_hasDerivAt_right`.
- `Basis` is `Module.Basis`; `Fintype.linearIndependent_iff` gives coefficients
  from `∑ c i • b i = 0`.
- Mathlib's `IsLeviCivitaConnection` spells compatibility as
  `cov.IsMetricCompatible (M := M) (V := TangentSpace I)` with `cov` an explicit
  variable — the named arguments are what lets it elaborate outside an
  existential. Prefer `cov.IsLeviCivitaConnection` in hypothesis position;
  `isLeviCivitaConnection_iff` converts to the `∧` form used in the existentials.
- Building mathlib `master` from source with no cache takes hours on 4 cores;
  `lake exe cache get` needs `mathlib4.lakecache.org`.
- `HAdd (TangentSpace I x) E` never synthesises: keep algebraic identities on
  tangent spaces (`A : Π y, T_yM →L T_yM →L T_yM`) and analytic statements on
  `E` (`covE`, `curvatureE`, `covEndE`), and bridge with `exact` by defeq.
- `simp only` zeta-reduces a `show T from v` ascription and then
  `rw [extend_apply_self]` fails (`?v : E` vs `T_yM` at instances
  transparency) — use `unfold`. Same family: `LinearMap.trace ℝ E` and
  `LinearMap.trace ℝ (TangentSpace I x)` are defeq but `rw` will not cross;
  `change` to the `TangentSpace` form before `trace_eq_sum_inner`, and state
  sum-expansion facts for plain `E`-vectors (`key : ∀ c e w, …`) then `exact`
  them at `b i`.
- A bare `TensorialAt.mkHom …` elaborated against an expected type `E →L E`
  leaves `?V x =?= E` unsolved; ascribe `(… : TangentSpace I x →L[ℝ]
  TangentSpace I x)` first, then use it at type `E →L E`.
- **Never `local notation` over a section variable.** Hygiene hides `E`, the
  next `variable (g : … E …)` silently fails, and everything downstream is
  auto-bound with stuck `IsManifold ?I ω ?M` instances. Write the lambda out.
- The `RiemannianBundle` instance for a metric `g` is introduced by
  `letI : RiemannianBundle … := ⟨g.toRiemannianMetric⟩` in defs and
  `let _ : … := …` in proofs (the `haveI`/`letI` linter); a hypothesis that
  needs it is written `(h : letI := …; P)`, as `IsRicciFlowOn` does.
- **`TangentSpace I x` has no norm of its own** — the norm comes from a
  `RiemannianBundle` instance, i.e. from a metric. `HasDerivAt` into
  `TangentSpace I x` or `TangentSpace I x →L[ℝ] …` fails to elaborate with
  `failed to synthesize NormedAddCommGroup (TangentSpace I x)`. Type such data
  on `E` via a wrapper def whose signature says `E` (`innerE`,
  `leviCivitaOfMetricE` in `Variation.lean`); a type ascription `(v : E)` does
  **not** change the inferred type. Pass `hasDerivAt_const (F := E)`. Then
  `map_sub`/`map_zero` will not fire on a `TangentSpace`-typed `a - b` fed to an
  `E`-typed CLM: state the equation as a `have … := map_sub _ _ _` and rewrite.
- `set_option maxSynthPendingDepth 3` for nested CLM spaces
  (`E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ`), or norm instances silently fail to synthesise and
  `simp` lemmas quietly no-op.
- `[LieRing 𝔤]` **cannot** carry a norm — `LieRing` and `NormedAddCommGroup` both
  extend `AddCommGroup`, an unresolved diamond with no mathlib precedent. Carry the
  bracket as an explicit `β : E →L[ℝ] E →L[ℝ] E` and transport.
- Carry a varying metric as a map into the dual (`g : E →L[ℝ] E →L[ℝ] ℝ`); then
  nondegeneracy is `ContinuousLinearMap.IsInvertible` and smoothness is
  `contDiffAt_map_inverse`, with no coordinates.
- Argument order is nonstandard: `cov σ x (X x)` is `(∇_X σ) x` on paper.
- `torsion_eq_zero_iff` takes `cov` explicitly. `ContMDiffAt.mdifferentiableAt`
  wants `n ≠ 0`, not `1 ≤ n`.
- "Prints identically but won't unify" is usually a substitution made mentally
  under a binder, not a diamond. `simp only` with collapse lemmas *and* pointwise
  `∀ y` facts in one set; `rw` cannot reach under a binder.

## Blueprint / CI gotchas

- **CI (`.github/workflows/blueprint.yml`) runs three jobs.** `lean`: mathlib cache
  (a miss fails, never builds from source), `lake build` with warnings as errors,
  then `scripts/check_axioms.py` (`#print axioms` on every `\lean{}` name in the
  blueprint; only `propext`, `Classical.choice`, `Quot.sound` allowed; no `axiom`
  declarations). `blueprint`: **on PRs too** — `leanblueprint pdf` with the log
  checked for `^!` and `Missing character`, then `web` and `checkdecls`; uploads
  the site only on `main`. `deploy`: Pages, `main` only. TeX is a pinned TinyTeX
  bundle (`TINYTEX_URL`, xelatex + latexmk included, ~200 MB, verified locally),
  not `texlive-full`.
- The axiom script is the local pre-PR check too: `python3 scripts/check_axioms.py`
  after `lake build` (~3 min, mostly loading oleans).
- **PDF builds locally**: basictex + `sudo /Library/TeX/texbin/tlmgr install latexmk`.
  The config uses **xelatex** (`$pdflatex = 'xelatex -synctex=1'`), not pdflatex.
  Fallback without latexmk: `xelatex` twice from `blueprint/src`.
- **Grep the log for `Missing character`, not just errors.** A literal `₃` inside
  `\texttt{}` has no glyph in `lmmono10-regular` and was silently dropped from the
  PDF for several commits. Use `$_3$`.
- Every macro must be declared in `macros/common.tex` — an undefined `\Z` broke CI.
  And never write a bare `\lean` in prose; it takes an argument.
- `checkdecls` verifies every `\lean{}` name. `proof_wanted` produces a **private**
  declaration that it cannot resolve — name such statements in prose instead.
- `latexmkrc` lists `print.tex` only; `print.tex` must not load `blueprint.sty`.
- CI uses `concurrency: pages` with `cancel-in-progress` — **pushing while a run is
  in flight cancels it.** Batch pushes. This cancelled three runs on 2026-08-13.
- `gh run watch` exits 1 on transient API errors and its shell exit code does not
  reflect the CI conclusion. Poll `gh run view --json status,conclusion` in a loop.
- **Never `git add -A` while a subagent is writing** — it swept 500 lines of
  in-progress work into an unrelated commit (`d43dd54`). Stage explicit paths.
