# Ricci flow blueprint

A [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) for
formalizing Ricci flow in Lean 4 with Mathlib. The first milestone is Hamilton's
1982 theorem — *a closed 3-manifold admitting a metric of strictly positive
Ricci curvature admits a metric of constant positive sectional curvature*. The
terminal node is Perelman's spherical space form theorem, which contains the
Poincaré conjecture as the case `Γ = 1`.

**Rendered blueprint: https://korbonits.github.io/ricci-flow-blueprint/**

## What is and isn't here

The obstacle is usually said to be analysis, and eventually it is — but not
first. As of August 2026, Riemannian **curvature did not exist in Mathlib at
all**: the library has manifolds, vector bundles, and covariant derivatives, but
no Riemann tensor, no Ricci, and zero occurrences of the string `sectional`. So
a project planning around the parabolic PDE gap stalls long before reaching it.

That gap is real and is marked explicitly: short-time existence needs
quasilinear parabolic systems on sections of vector bundles, hence Sobolev
spaces of bundle sections and elliptic regularity, none of which Mathlib has.
Reading Morgan–Tian's structure also shows the road needs **three** distinct
parabolic theories, not one — Ricci flow, harmonic map flow (for uniqueness of
the standard solution), and curve-shrinking flow (for finite extinction) — plus
a second independent gap in Cheeger–Gromov compactness.

Two branches are nevertheless **closed end to end**, both PDE-free: Ricci flow
on left-invariant metrics, which is an ODE, and Milnor's curvature formulas.

## Status

### Curvature (`Curvature.lean`, `Ricci.lean`, `Sectional.lean`)

| Node | Status |
| --- | --- |
| `CovariantDerivative.curvature`, `curvature_antisymm` | defined, proved |
| `bianchi_first` | **proved** — first Bianchi, all side conditions discharged |
| `curvature_smul_*`, `curvature_add_*` | **proved** — tensoriality, all three slots |
| `tensorialAt_curvature_fst/snd` | **proved** — curvature descends to a pointwise tensor |
| `CovariantDerivative.ricci` | **defined** — trace of `Z ↦ R(Z,X)Y`, via one-slot `mkHom` |
| `ricci_sub_ricci_swap` | **proved** — `Ric(X,Y) − Ric(Y,X) = −tr R(X,Y)` |
| `sectionalCurvature`, `_basis_change` | **defined** — with invariance under change of basis |
| Scalar curvature | not attempted — needs the metric trace |
| `exists_unique_leviCivita` | the only `sorry`; superseded by mathlib4 [#36845](https://github.com/leanprover-community/mathlib4/pull/36845) |

Note `Ric` is **not** symmetric for a general torsion-free connection; the
identity above is the trace of first Bianchi, and symmetry is the corollary when
`tr R(X,Y) = 0`, which holds for a metric connection.

### Ricci flow (`Flow.lean`, `Hamilton.lean`)

| Node | Status |
| --- | --- |
| `IsRicciFlowOn` | **defined** — `∂g/∂t = −2Ric(g)`, per time slice, on an interval |
| `isRicciFlowAt_const_iff` | **proved** — stationary iff Ricci-flat; the definition has content |
| `ricciFlow_shortTime_existence` | **stated** (`proof_wanted`) — blocked on parabolic PDE |
| `hamilton_1982` | **stated** (`proof_wanted`) — no `sorry`, no added axiom |
| Hamilton 1982, proved | years away |
| Perelman's spherical space form theorem | terminal node |

### Left-invariant metrics — **closed** (`Homogeneous.lean`)

| Node | Status |
| --- | --- |
| `koszul` + torsion-free + metric-compatible | **proved** — Levi-Civita defined algebraically |
| `eq_koszul_of_torsionFree_of_compat` | **proved** — Levi-Civita *uniqueness*, left-invariant case |
| `contDiffAt_ricciField` | **proved** — `g ↦ −2Ric(g)` is `C^n` at nondegenerate `g` |
| `ricciFlow_leftInvariant` | **proved** — short-time existence + germ uniqueness |

Mathlib has no maximal-solution theory, so uniqueness is stated as a germ at
`t₀` rather than on a maximal interval.

### Milnor's formulas — **closed** (`Milnor.lean`)

| Node | Status |
| --- | --- |
| `apply_koszul_apply_milnor` | **proved** — the Koszul formula |
| `ricciBilin_structureConstants` | **proved** — Ricci in structure constants, any dimension |
| `ricciBilin_milnorFrame` | **proved** — Ricci diagonal, `rᵢ = 2μⱼμₖ`, `μᵢ = ½(λⱼ+λₖ−λᵢ)` |
| `ricci_heisenberg_mixed_sign` | **proved** — Heisenberg has mixed Ricci signs (Milnor Thm 2.4) |
| `ricciField_milnorFrame_diag` | **proved** — the Isenberg–Jackson ODE system, explicitly |

Two caveats: the Milnor frame's *existence* is a hypothesis (Milnor's
classification lemma is not formalized — in progress on `wip/milnor-frame`), and
the ODE is stated as the field's value at diagonal metrics rather than proving
solutions stay diagonal.

Milnor flips both the curvature sign and the contraction slot relative to our
conventions, so the numerical values agree — the two flips cancel. Stated
explicitly in `Milnor.lean` rather than left to luck.

## Upstreamable

These have no Mathlib equivalent and do not depend on the curvature stack:

- `VectorField.lieBracket_apply_fun` / `mlieBracket_apply_fun` — `[V,W]f = V(Wf) − W(Vf)`,
  on a vector space and on any manifold with corners
- `VectorField.jacobi_mlieBracket_apply` — the cyclic Jacobi identity
  (Mathlib has only the Leibniz form)
- `CovariantDerivative.neg_apply` / `sub_apply` — subtraction for covariant derivatives
  (`IsCovariantDerivativeOn` ships only `add` and `leibniz`)
- `CovariantDerivative.mdiffAt_cov_apply` — differentiability of `∇_Y σ`
- `VectorField.mvfderiv_eq_fderiv` — collapse to `fderiv` on the model space

## A note on stating theorems about varying metrics

Anything where the metric **varies** — "M admits a metric such that …", or a
flow `g(t)` — needs care. Two conditions are jointly necessary for
`cov.IsMetricCompatible` to elaborate: the `RiemannianBundle` instance must be
an ambient *binder*, and `cov` must be bound by an *existential*. So predicates
are elaborated once in that context, and varying-metric definitions merely apply
those constants under `letI`. See the header of `Hamilton.lean`. The underlying
fibre instances are definitionally equal, so this is an elaboration workaround
rather than a soundness issue.

## Build

    lake exe cache get
    lake build
    leanblueprint pdf && leanblueprint web

The PDF build uses **xelatex**, not pdflatex. Check the log for
`Missing character` as well as errors — a literal `₃` inside `\texttt{}` was
silently dropped for several commits.

Statements marked `-- BENCH: <id>` are the headline results.
