# Ricci flow blueprint — working notes

A `leanblueprint` for Hamilton's 1982 theorem. Live:
https://korbonits.github.io/ricci-flow-blueprint/

Companion (private): `~/code/mathai-2026-paper` — the MATH-AI submission whose
benchmark tasks are the `-- BENCH:` statements here. **Deadline 2026-09-25.**
Read its `CLAUDE.md` for the overall plan; this file is the Lean side.

## State

`lake build` is clean. Only remaining `sorry` is `exists_unique_leviCivita`,
superseded upstream. Proved here, all axiom-free:

- `CovariantDerivative.curvature`, `curvature_antisymm`
- `CovariantDerivative.bianchi_first` — first Bianchi identity, clean form
  (`C^1` connection, `C^2` fields, all side conditions discharged), and
  `bianchi_first_of_mdiff` with explicit hypotheses
- `neg_apply`, `sub_apply`, `mdiffAt_cov_apply`, `VectorField.jacobi_mlieBracket_apply`

## Next: upstream the four lemmas

These have **no Mathlib equivalent** and are independent of Ricci flow, so they
are far easier to land than anything blueprint-specific. Best next contribution:

| Lemma | Why Mathlib wants it |
| --- | --- |
| `neg_apply`, `sub_apply` | `IsCovariantDerivativeOn` ships only `add` and `leibniz`; subtraction has to route through `smul_const (-1)` |
| `jacobi_mlieBracket_apply` | Mathlib has only the Leibniz form `[U,[V,W]] = [[U,V],W] + [V,[U,W]]`; the cyclic form needs antisymmetry in *both* slots |
| `mdiffAt_cov_apply` | first consumer of `ContMDiffCovariantDerivative` **anywhere** — the class had none |

Also: **PR #36845** (Levi-Civita, `grunweg`, reviewed by `sgouezel`) is
`awaiting-author` since 2026-07-28 with only cosmetic items left — doc-comment
length, lemma naming order, hoisting `[FiniteDimensional ℝ E]` into a `variable`
line. Adoptable, and the route into `t-differential-geometry`.

## Blocked, and why

- **Ricci / scalar curvature cannot be *defined*** — the trace needs `curvature` to
  descend from vector *fields* to vectors in its first slot. Blocked upstream on
  `TensorialAt` giving only first-order (`MDiffAt`) hypotheses and the absence of
  `mkHom₃`. That wall is one level earlier than the missing PDE. This is
  `grunweg`'s active area (see `plan.mde` in PR #36128) — **ask, don't build**.
- **Short-time existence** needs parabolic PDE on bundle sections. Mathlib's entire
  PDE surface is `Analysis/Distribution/Sobolev.lean` + `SobolevInequality.lean`.
- The principal-bundle route to curvature (connection 1-form, `F = dω + ½[ω,ω]`)
  is gated on differential forms on manifolds. Different Bianchi, different gap —
  our affine-connection route needs no forms, which is why it closed.
- **Beachhead with no PDE:** Ricci flow on left-invariant metrics on a Lie group is
  an ODE on a finite-dimensional space. Mathlib has Picard–Lindelöf. Still prose.

## Lean gotchas learned the hard way

- Use `[IsManifold I ω M]`. Instance search will **not** see through
  `minSmoothness ℝ n = n` even though it reduces over ℝ; `ω` synthesises
  `3`, `(2:ℕ∞)+1` and `minSmoothness ℝ 2` directly and dissolves the index arithmetic.
- The metric must reach `TM` via `[RiemannianBundle (fun x ↦ TangentSpace I x)]`,
  never a raw `[∀ x, InnerProductSpace ℝ (TangentSpace I x)]` — the fibers already
  carry a topology and the raw binder makes a diamond.
- Argument order is nonstandard: `cov σ x (X x)` is `(∇_X σ) x` on paper.
- `torsion_eq_zero_iff` takes `cov` **explicitly**: `(torsion_eq_zero_iff cov).mp`.
- `ContMDiffAt.mdifferentiableAt` wants `n ≠ 0`, not `1 ≤ n`.
- Bind a `have` of a ∀-statement with an explicit type or the implicits get
  eagerly instantiated.

## Blueprint/CI gotchas

- `blueprint/src/latexmkrc` must list **`print.tex` only**. `web.tex` is plasTeX's
  job and uses `\home`/`\github` from the plugin, not from `blueprint.sty`.
- `print.tex` must **not** load `blueprint.sty` — it is a plasTeX-side stub that
  no-ops `\graphcolor`. Print gets `\lean`/`\leanok`/`\uses` dummies from
  `macros/print.tex` instead.
- plasTeX writes to `blueprint/web`; the workflow uploads that path.
- `checkdecls` is a lake dependency and verifies every `\lean{}` name exists.
- CI uses `concurrency: pages` with `cancel-in-progress` — **pushing while a run is
  in flight cancels it.** Let runs finish.
- `gh run watch | tail` swallows the exit status. Capture it separately.
