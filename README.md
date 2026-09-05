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
no Riemann tensor, no Ricci, no scalar curvature, and zero occurrences of the
string `sectional`. The vocabulary — Riemann, Ricci, sectional, scalar — is now
complete here. So
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
| `scalarCurvature` | **defined** — on the model space, hypothesis-free |
| `scalarCurvatureWith` + `_congr` | **proved** — frame-relative on a general manifold, frame-independent |
| `ricci_eq_sum_inner_curvature` | **proved** — Ricci as an orthonormal-frame sum, general manifold |
| `exists_leviCivita`, `leviCivita_unique` | **proved** — from Mathlib's `leviCivitaConnection` ([#36845](https://github.com/leanprover-community/mathlib4/pull/36845), merged); uniqueness holds on differentiable sections, which is the correct statement — the old `∃!` was not provable |
| `ricci_eq_of_isLeviCivita`, `sectionalCurvature_eq_of_isLeviCivita` | **proved** — every `C¹` Levi-Civita connection gives the same `Ric` and `K` on `C²` fields, so the existentials in `Hamilton.lean`/`Flow.lean` are statements about the metric |

Note `Ric` is **not** symmetric for a general torsion-free connection; the
identity above is the trace of first Bianchi, and symmetry is the corollary when
`tr R(X,Y) = 0`, which holds for a metric connection.

**No `sorry` remains.**

### Smoothness of Levi-Civita, and `Ric` as a function of the metric (`LeviCivitaSmooth.lean`)

| Node | Status |
| --- | --- |
| `contMDiffCovariantDerivative_leviCivitaConnection` | **proved** — on a `C^ω` manifold with a `C^{k+1}` metric, Mathlib's `leviCivitaConnection` is `C^k`; the result Mathlib's `LeviCivita.lean` defers to "future PRs" |
| `contMDiffAt_section_of_inner_localFrame` | **proved** — a section of a Riemannian bundle is `C^n` if its inner products with a local frame are (Gram inversion, no orthonormal frames) |
| `contMDiffAt_mvfderiv_apply` | **proved** — the derivative of a `C^{n+1}` function along a `C^n` field is `C^n` |
| `ricciOfMetric`, `sectionalCurvatureOfMetric` | **defined** — `Ric(g)`, `K(g)` via the Levi-Civita connection; not junk, since it is `C¹` |
| `isRicciFlowOn_iff_ricciOfMetric` | **proved** — the flow is `∂g/∂t = -2 Ric(g t)`, no connection quantified over |
| `admitsPositiveRicciMetric_iff`, `admitsConstPositiveSecMetric_iff` | **proved** — Hamilton's hypothesis and conclusion in terms of `Ric(g)` and `K(g)` |

### Ricci flow (`Flow.lean`, `Hamilton.lean`)

| Node | Status |
| --- | --- |
| `IsRicciFlowOn` | **defined** — `∂g/∂t = −2Ric(g)`, per time slice, on an interval |
| `isRicciFlowAt_const_iff` | **proved** — stationary iff Ricci-flat; the definition has content |
| `isRicciFlowAt_iff_of_isLeviCivita` | **proved** — the existential can be discharged by *any* `C¹` Levi-Civita connection: the textbook equation with `Ric` computed by a specified connection |
| `isRicciFlowAt_iff_leviCivita` | **proved** — with the canonical connection, which is `C¹` by `LeviCivitaSmooth.lean` |
| `ricciFlow_shortTime_existence` | **stated** (`proof_wanted`) — blocked on parabolic PDE |
| `hamilton_1982` | **stated** (`proof_wanted`) — no `sorry`, no added axiom |
| Hamilton 1982, proved | years away |
| Perelman's spherical space form theorem | terminal node |

### Hamilton's curvature ODE — **closed** (`Pinching.lean`)

The reaction ODE of the curvature evolution in dimension three,
`λ̇ = λ² + μν, μ̇ = μ² + λν, ν̇ = ν² + λμ`, with no manifold in sight. The tensor
maximum principle transfers these to the flow; that transfer is the missing part.

| Node | Status |
| --- | --- |
| `le_preserved_lm`, `le_preserved_mn` | **proved** — the ordering `λ ≥ μ ≥ ν` is preserved |
| `ricci_pos_preserved` | **proved** — positive Ricci curvature (`μ + ν > 0`) is preserved |
| `bound_preserved` | **proved** — `λ ≤ C(μ + ν)` is preserved for `C ≥ 1/2` |
| `pinching_antitone` | **proved** — `(λ − ν)(μ + ν)^{δ−1}` is nonincreasing for `δ(2C+1) ≤ 1`: Hamilton 1982, Theorem 10.1, the ODE half |
| `nonpos_of_deriv_le_mul` | **proved** — linear Grönwall comparison, `f' ≤ a f`, `f 0 ≤ 0` ⇒ `f ≤ 0` |

### Second covariant derivative and Laplacian (`Hessian.lean`)

| Node | Status |
| --- | --- |
| `hessian`, `hessianAt` | **defined** — `∇²_{X,Y} Z`, tensorial in both slots, hence a bilinear map at each point |
| `hessian_sub_hessian_swap` | **proved** — the Ricci identity `∇²_{X,Y} Z − ∇²_{Y,X} Z = R(X,Y) Z` for torsion-free connections |
| `hessianFun`, `hessianFun_symm` | **proved** — the Hessian of a `C²` function is symmetric for torsion-free connections |
| `laplacian`, `laplacian_eq_sum` | **defined** — the metric trace of the Hessian, basis-independent |
| `laplacianFun` | **defined** — the Laplacian of a function |
| `deriv2_nonneg_of_isLocalMin`, `fderiv2_nonneg_of_isLocalMin` | **proved** — the second-derivative test on the line and in a normed space (`SecondDerivativeTest.lean`) |
| `hessianFun_nonneg_of_isLocalMin_model`, `laplacianFun_nonneg_of_isLocalMin_model` | **proved** — `∇²f(X,X) ≥ 0` and `Δf ≥ 0` at a local minimum, model space, any connection: the hypothesis the abstract maximum principle asks for |

### The scalar maximum principle — **proved, abstractly** (`MaximumPrinciple.lean`)

| Node | Status |
| --- | --- |
| `le_of_deriv_ge_at_min` | **proved** — on a compact space, if `F(u) ≤ ∂ₜu` at every spatial minimum and `φ' = F(φ)`, `φ 0 ≤ u 0`, then `φ ≤ u`. The Laplacian's only role in the classical proof is to supply the hypothesis at a minimum |
| `le_of_deriv_le_at_max` | **proved** — the mirrored upper bound |

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
| `scalar` + `contDiffAt_scalar` | **proved** — Lie-algebra scalar curvature, smooth in `g` |
| `exists_milnorFrame_scalar` | **proved** — `scal = 2(μ₀μ₁ + μ₁μ₂ + μ₂μ₀)`, no frame hypothesis |

| `exists_milnorFrame` | **proved** — Milnor's classification lemma (Lemma 4.1) |
| `exists_milnorFrame_ricci_diagonal` | **proved** — Ricci diagonal, *no frame hypothesis* |

One caveat remains: the ODE is stated as the field's value at diagonal metrics
rather than proving solutions stay diagonal.

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

The project tracks mathlib `master` (pinned in `lake-manifest.json`) on Lean
`v4.34.0-rc2`, since the Levi-Civita connection is not yet in a mathlib
release.
    leanblueprint pdf && leanblueprint web

The PDF build uses **xelatex**, not pdflatex. Check the log for
`Missing character` as well as errors — a literal `₃` inside `\texttt{}` was
silently dropped for several commits.

Statements marked `-- BENCH: <id>` are the headline results.
