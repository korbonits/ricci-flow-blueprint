# Ricci flow blueprint — working notes

A `leanblueprint` for Ricci flow. Live: https://korbonits.github.io/ricci-flow-blueprint/
Milestone: Hamilton 1982. Terminal node: Perelman's spherical space form theorem.

## State (2026-09-04)

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
| `MaximumPrinciple.lean` | **proved**: the scalar maximum principle on a compact space with the differential inequality assumed at spatial minima (`le_of_deriv_ge_at_min`, `le_of_deriv_le_at_max`). ε-perturbation `φ − ε e^{(2K+1)t}` + first touching time. No Laplacian |
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

## Roadmap (from 2026-09-04)

**Done since 2026-08-14:** Milnor's classification lemma; scalar curvature;
#36845 merged upstream and adopted here (`LeviCivita.lean` rewritten, `sorry`
gone, bridges to `Flow.lean`/`Hamilton.lean` proved); `RicciFlow.lean` folded
into `Flow.lean`.

**Done 2026-09-04, later the same day:** smoothness of `leviCivitaConnection`
(`LeviCivitaSmooth.lean`, `C^ω` manifold, `C^{k+1}` metric ⇒ `C^k` connection),
hence `ricciOfMetric` and the textbook flow equation
`isRicciFlowOn_iff_ricciOfMetric`. This was the gate for DeTurck and the
curvature evolution equations. **Upstream candidate**: Mathlib's
`LeviCivita.lean` lists smoothness as future work; the three criteria in
`LeviCivitaSmooth.lean` are Mathlib-general (any bundle for the frame
criterion) except the main theorem's `IsManifold I ω M`, which a Mathlib
version should weaken to `C^{k+2}`. Offer on Zulip before opening the PR.

**Done 2026-09-05:** Hamilton's curvature ODE and its invariant sets
(`Pinching.lean`): the algebraic heart of Hamilton 1982. What transfers it
to the flow is the tensor maximum principle (`thm:max-tensor`), which needs
the evolution equation and hence the Laplacian on tensors.

**Done 2026-09-05, later:** the scalar maximum principle, abstractly
(`MaximumPrinciple.lean`). The tensor version has the same skeleton; what it
needs is the evolution equation for the differential inequality at a touching
point.

**Next — curvature evolution.** With `Ric(g)` a function of `g`, the next
PDE-free target is the evolution of `Ric`/`scal` under the flow, i.e. the
first variation of curvature (`lem:evolution-rm`). It needs the second
covariant derivative and the Laplacian on tensors; neither exists in Mathlib.

**Day 1 — unblock (~45 min).** Post the Zulip question in `#mathlib4`, topic
`RiemannianBundle: metrics as instances vs values`; tag `sgouezel`. It gates
upstreaming the curvature stack.

**Day 2 — first upstream PR (~2–3 hrs).** `VectorField.lieBracket_apply_fun` →
`Mathlib/Analysis/Calculus/VectorField.lean`, beside `lieBracket_smul_*`. No
dependency on the curvature stack. Budget the time for mathlib conventions, not
mathematics.

**Day 5 — second and third PRs (~2 hrs).** `neg_apply`/`sub_apply`, then
`mdiffAt_cov_apply`. Three small merged PRs beat one large one in review.

**Not yet:** upstreaming curvature/Ricci/sectional (wait for the Zulip
answer), anything parabolic, any writing-up.
**If a day is lost, drop in this order:** third PR, second PR. Keep Day 1 and
the smoothness item.

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
