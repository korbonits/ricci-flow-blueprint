# Ricci flow blueprint

A [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) for
formalizing Hamilton's 1982 theorem — *a closed 3-manifold with positive Ricci
curvature admits a metric of constant positive sectional curvature* — in Lean 4
with Mathlib.

Rendered blueprint: TODO (GitHub Pages)

## What is and isn't here

The obstacle is not differential geometry, it's analysis. Mathlib has no
parabolic PDE theory, no elliptic regularity, and no Sobolev spaces of bundle
sections, so short-time existence of the flow — via DeTurck's trick or
Nash–Moser — has no foundation to build on. The blueprint marks that region
explicitly rather than pretending it's a few lemmas away.

The near-term goal is therefore the *perfectoid-shaped* one: state the flow and
its short-time existence precisely, with an honest dependency graph underneath,
and close one branch end to end.

| Node | Status |
| --- | --- |
| `CovariantDerivative.curvature` | **defined** |
| `curvature_antisymm` | **proved** |
| `neg_apply`, `sub_apply`, `mdiffAt_cov_apply` | **proved** — upstreamable, no Mathlib equivalent |
| `bianchi_first` | **proved** — first Bianchi, all side conditions discharged |
| `curvature_smul_left/middle/right` | **proved** — tensoriality, all three slots, unconditional |
| `VectorField.lieBracket_apply_fun` | **proved** — `[V,W]f = V(Wf) − W(Vf)`, vector spaces |
| `VectorField.mlieBracket_apply_fun` | **proved** — the same on any manifold, corners allowed |
| Ricci and scalar curvature | mathematics done; needs tensor packaging (`TensorialAt`/`mkHom₃`) |
| `exists_unique_leviCivita` | upstream: mathlib4 [#36845](https://github.com/leanprover-community/mathlib4/pull/36845) |
| Ricci flow on left-invariant metrics (an ODE) | prose — the beachhead, no PDE required |
| Short-time existence on a closed manifold | blocked: parabolic PDE |
| Hamilton 1982 | terminal node |

`lake build` is clean; the only remaining `sorry` is `exists_unique_leviCivita`,
which is superseded by the upstream PR above.

Four lemmas here have no Mathlib equivalent and are candidates for upstreaming:
`neg_apply`/`sub_apply` (subtraction for covariant derivatives),
`jacobi_mlieBracket_apply` (the cyclic Jacobi identity), and `mdiffAt_cov_apply`
(differentiability of `∇_Y σ`).

Mathlib already carries the terminal statement of the road this is on:
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`.

## Contributing

Statements marked `-- BENCH: <id>` are also benchmark tasks for the companion
MATH-AI paper; keep the marker when you fill in a proof. Only real statements
carry the marker — a placeholder `True` would silently inflate pass rates.

    lake exe cache get
    lake build
    leanblueprint pdf && leanblueprint web
