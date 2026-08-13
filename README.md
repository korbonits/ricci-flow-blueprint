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

| Branch | Status |
| --- | --- |
| Curvature tensor, sectional curvature | drafted, upstreaming |
| Levi-Civita existence + uniqueness (Koszul) | statement only |
| Ricci and scalar curvature | statement only |
| Ricci flow on left-invariant metrics (an ODE) | the beachhead — no PDE required |
| Short-time existence on a closed manifold | blocked on parabolic PDE |
| Hamilton 1982 | terminal node |

Mathlib already carries the terminal statement of the road this is on:
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`.

## Contributing

Statements marked `-- BENCH: <id>` are also benchmark tasks for the companion
MATH-AI paper; keep the marker when you fill in a proof.

    lake exe cache get
    lake build
    leanblueprint pdf && leanblueprint web
