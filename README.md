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
| `curvature_add_left/middle/right` | **proved** — additivity, the other half of tensoriality |
| `tensorialAt_curvature_fst/snd` | **proved** — curvature descends to a pointwise tensor |
| `CovariantDerivative.ricci` | **defined** — trace of `Z ↦ R(Z,X)Y`, via one-slot `mkHom` |
| `ricci_sub_ricci_swap` | **proved** — `Ric(X,Y) − Ric(Y,X) = −tr R(X,Y)`, the trace of first Bianchi |
| Sectional curvature | undefined — absent from mathlib entirely (zero occurrences of `sectional`) |
| Scalar curvature | needs the metric trace; not attempted |
| `exists_unique_leviCivita` | upstream: mathlib4 [#36845](https://github.com/leanprover-community/mathlib4/pull/36845) |
| `IsRicciFlowOn` | **defined** — `∂g/∂t = −2Ric(g)`, per time slice, on an interval |
| `isRicciFlowAt_const_iff` | **proved** — stationary iff Ricci-flat; the definition has content |
| `ricciFlow_shortTime_existence` | **stated** — `proof_wanted`; blocked on parabolic PDE |
| `LeftInvariant.koszul` + torsion/compat | **proved** — Levi-Civita defined algebraically |
| `eq_koszul_of_torsionFree_of_compat` | **proved** — Levi-Civita *uniqueness*, left-invariant case |
| `contDiffAt_ricciField` | **proved** — `g ↦ −2Ric(g)` is `C^n` at nondegenerate `g` |
| `ricciFlow_leftInvariant` | **proved** — short-time existence + germ uniqueness. **Branch closed end to end** |
| Short-time existence on a closed manifold | blocked: parabolic PDE |
| `sectionalCurvature` + `_basis_change` | **defined** — with invariance under change of basis of the 2-plane |
| `hamilton_1982` | **stated** — `proof_wanted`, no sorry, no added axiom |
| Hamilton 1982 (proof) | years away: parabolic PDE, tensor maximum principle, pinching, Shi, convergence |
| Perelman's spherical space form theorem | terminal node |

`lake build` is clean; the only remaining `sorry` is `exists_unique_leviCivita`,
which is superseded by the upstream PR above.

Four lemmas here have no Mathlib equivalent and are candidates for upstreaming:
`neg_apply`/`sub_apply` (subtraction for covariant derivatives),
`jacobi_mlieBracket_apply` (the cyclic Jacobi identity), and `mdiffAt_cov_apply`
(differentiability of `∇_Y σ`).

Mathlib already carries the terminal statement of the road this is on:
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`.

## Contributing

Statements marked `-- BENCH: <id>` are the headline results — the ones worth
citing from the blueprint. Keep the marker when you fill in a proof. Only real
statements carry one; a placeholder `True` does not.

    lake exe cache get
    lake build
    leanblueprint pdf && leanblueprint web
