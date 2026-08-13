# Ricci flow blueprint — working notes

A `leanblueprint` for Hamilton's 1982 theorem. Live:
https://korbonits.github.io/ricci-flow-blueprint/

Companion (private): `~/code/mathai-2026-paper` — the MATH-AI submission whose
benchmark tasks are the `-- BENCH:` statements here. **Deadline 2026-09-25.**
Read its `CLAUDE.md` for the overall plan; this file is the Lean side.

## State (2026-08-13)

`lake build` clean. Only `sorry` is `exists_unique_leviCivita` (superseded by
upstream PR #36845). Everything below is axiom-free — `#print axioms` shows only
`[propext, Classical.choice, Quot.sound]` — and none of it exists in Mathlib.

**Curvature.lean**
- `CovariantDerivative.curvature`, `curvature_antisymm`
- `bianchi_first_of_mdiff`, `bianchi_first` — first Bianchi identity, clean form
- `neg_apply`, `sub_apply` — subtraction for covariant derivatives
- `mdiffAt_cov_apply` — first consumer of `ContMDiffCovariantDerivative` anywhere
- `curvature_smul_left`, `curvature_smul_middle` — tensoriality slots 1, 2
- `curvature_smul_right_of_derivation` — slot 3, modulo hypothesis `hder`

**LieBracketDerivation.lean**
- `lieBracket_apply_fun` — `[V,W]f = V(Wf) − W(Vf)`, vector spaces
- `mvfderiv_eq_fderiv`, `mlieBracket_eq_lieBracket(')` — model-space collapses
- `mlieBracket_apply_fun_model` — derivation identity, manifold notation on `E`

## Where the blocker actually is

The README's old "blocked on parabolic PDE" is true but is the **second**
obstruction. Ricci curvature cannot be *defined*:

    Ricci definable
      ← curvature tensoriality slots 1–3   1,2 proved; 3 modulo `hder`
      ← [X,Y]f = X(Yf) − Y(Xf) on manifolds
           ├ vector-space case              proved
           ├ model-space case               proved
           └ chart transport to general M   ← the only remaining gap

Discharging `hder` in `curvature_smul_right_of_derivation` completes slot 3 and
unblocks defining Ricci.

## IN FLIGHT

A Fable subagent is attempting the chart transport (model space → general
manifold) and, if it succeeds, discharging `hder`. It may edit
`LieBracketDerivation.lean` and `Curvature.lean`. **Do not edit those two files
until it reports.** Template it was pointed at: mathlib's
`leibniz_identity_mlieBracketWithin_apply` (~127 lines) and
`mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt`. Note there is no
manifold-level second-derivative symmetry in mathlib — that may be the real
deliverable.

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
