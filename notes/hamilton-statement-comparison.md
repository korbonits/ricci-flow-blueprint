# Hamilton 1982: our formal statement vs. Chow–Liao–Qin (arXiv 2608.21502)

Findings only; nothing fixed.

Their paper: Bennett Chow, Yuan Liao, Ziyang Qin, "A Lean Formalization of
Hamilton's Three-Manifold Theorem", arXiv:2608.21502v1 [math.DG], 21 Aug 2026.
Repository <https://github.com/qinz1yang/differential-geometry>, release 0.1.0,
commit `8bd406e35`, tag `arxiv-v1-preview`, Lean 4 v4.29.0 / mathlib v4.29.0.
(Read from a local copy of the PDF; arxiv.org is blocked by this session's
egress policy.)

Predicate bodies below marked *(paper prose)* are given in the paper as
mathematics, not as displayed Lean; only the signatures are quoted verbatim.
Ours are quoted from source at `71e3e32`.

## The headline

**They prove it; we state it.** `hamilton_positive_ricci` is a closed proof with
`#print axioms` reporting exactly `[propext, Classical.choice, Quot.sound]`.
Ours is `proof_wanted`.

**And their statement is better in two specific, fixable ways** that are
independent of having a proof — both concerning what the curvature is tested
against. Those are items 1 and 2 below, and item 1 is the one I would act on.

## Side by side

| Aspect | Ours | Theirs |
| --- | --- | --- |
| Endpoint | `proof_wanted hamilton_1982` | `theorem hamilton_positive_ricci`, proved |
| Manifold regularity | `IsManifold I ω M` (**analytic**) | `IsManifold I ∞ M` (**smooth**) |
| Closed | `[CompactSpace M]` + `[I.Boundaryless]` | inside `isClosedThreeManifold` |
| Connected | **absent** | **present**, inside `isClosedThreeManifold` |
| Hausdorff | **absent, and not derivable** (verified: `infer_instance` fails for `T2Space M`, `SecondCountableTopology M`, `Nonempty M` under our exact hypotheses) | `[T2Space M]` ambient on the short-time theorem; the paper does not display it for the Hamilton endpoint, so not determined here |
| Dimension | `Module.finrank ℝ E = 3` as an explicit hypothesis | `finrank ℝ E = 3` inside `isClosedThreeManifold` |
| Metric | `ContMDiffRiemannianMetric I 2` (**`C²`**), existential in both hypothesis and conclusion | `SmoothRiemannianMetric I M` (**smooth**), existential in both |
| Levi-Civita | **existentially quantified**: `∃ cov, ContMDiffCovariantDerivative cov 1 ∧ cov.IsMetricCompatible ∧ cov.torsion = 0 ∧ …`; proved equal to mathlib's canonical `leviCivitaConnection` via `hasPositiveRicciLC_iff` | **constructed**: `def LeviCivita (g) := leviCivitaConnectionOfMetric g`, project-local via Koszul; torsion-freeness, compatibility and smoothness proved separately |
| Connection regularity | `C¹`, demanded inside the existential | smoothness proved, not assumed (`…_contMDiffCovariantDerivativeLocally`) |
| **Curvature tested against** | **globally `C²` vector fields**: `∀ X, CMDiff 2 (T% X) → X x ≠ 0 → …` | **tangent vectors pointwise**: `∀ x, ∀ v ∈ Tₓ M, v ≠ 0 → 0 < metricRicciAt g x (v,v)` *(paper prose)* |
| Ricci object | `cov.ricci X Y x : ℝ`, with an `else 0` junk branch when the first slot is not tensorial | `metricRicciAt g x : Tensor0SSpace 2 I x`, a genuine pointwise tensor in a tensor bundle |
| Constant positive sec | quotient: `sectionalCurvature cov X Y x = k`, where `sectionalCurvature = ⟪R X Y Y, X⟫ / (‖X‖²‖Y‖² − ⟪X,Y⟫²)`, guarded by a nondegeneracy hypothesis | **multiplied out**: `∃ c > 0, ∀ x X Y, metricRm04StdAt g x X Y Y X = c (g(X,X)g(Y,Y) − g(X,Y)²)` *(paper prose)*; no nondegeneracy hypothesis needed |
| Conclusion | metric existence only (`AdmitsConstPositiveSecMetric`) | **both**: `admitsConstantPositiveSectionalCurvature ∧ isSphericalSpaceForm` |
| Diffeomorphism | absent | `SphericalSpaceFormQuotientModel`: `RoundQuotientData` for the unit round `S³` (finite group `Γ`, orthogonal action on `ℝ⁴`, smooth projection whose fibers are the `Γ`-orbits, smooth local sections) plus `equiv : M ≃ₘ⟨I,…⟩ data.Q`. Bridged by `constant_positive_sectional_curvature_iff_spherical_space_form` |

Their endpoint, verbatim:

```lean
theorem hamilton_positive_ricci
    (hM : isClosedThreeManifold (I := I) (M := M))
    (hpos : admitsPositiveRicci (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) ∧
      isSphericalSpaceForm (I := I) (M := M)
```

## Divergences, classified

(a) cosmetic — (b) real difference in strength — (c) junk-value or vacuity hazard

| # | Divergence | Class |
| --- | --- | --- |
| 1 | **Test class: global `C²` fields (ours) vs. tangent vectors (theirs).** Ours quantifies over globally `C²` sections. Producing one with a prescribed nonzero value at `x` needs a bump function times `FiberBundle.extend`, hence partitions of unity, hence Hausdorff + paracompactness — none of which our hypotheses supply or imply. Two consequences. (i) On pathological `M` with no such fields, both `HasPositiveRicciLC` and `HasConstSecLC` are **vacuously true**, and since the conclusion may reuse the hypothesis's metric with `k = 1`, `hamilton_1982` becomes **trivially provable and asserts nothing**. (ii) Even on well-behaved `M`, our hypothesis is equivalent to the intended "`Ric(v,v) > 0` for every nonzero tangent vector" only *via* the bump-function bridge, which we have not proved. Their pointwise formulation has neither problem: it is meaningful with no ambient hypotheses at all, because `metricRicciAt g x` is a genuine tensor at `x`. **This is the substantive finding.** | **(c)** |
| 2 | **Sectional curvature: quotient (ours) vs. multiplied-out identity (theirs).** `sectionalCurvature` divides by the Gram determinant, so degenerate pairs silently yield `0`; we guard with a nondegeneracy hypothesis on the quantified pair. Their `Rm04(X,Y,Y,X) = c(g(X,X)g(Y,Y) − g(X,Y)²)` needs no guard at all — on a degenerate pair it reads `0 = c·0`, automatically true — so there is no division and no junk branch to reason about. Strictly the better encoding. | **(c)** for ours; theirs immune |
| 3 | **Connectedness: absent (ours) vs. present (theirs).** Ours happens to survive the omission because our conclusion is metric existence with a single constant: a compact manifold has finitely many components, so apply Hamilton componentwise and rescale each metric to `k = 1` (`g ↦ λg` scales sectional curvature by `1/λ`). So ours is a mild *strengthening* needing a rescaling step Hamilton does not. But this is luck, not design: with their `isSphericalSpaceForm` conclusion the omission would make the statement **false**. Their short-time theorem deliberately omits connectedness and the paper says so explicitly ("Connectedness is absent, as it should be"), which is the right discipline. | **(b)** |
| 4 | **Conclusion strength.** Ours stops at metric existence. Theirs adds the spherical-space-form conclusion with an explicit quotient model and a genuine diffeomorphism, bridged in both directions. Ours is strictly weaker than the classical statement; the missing bridge is Killing–Hopf, which mathlib does not have and which they built. | **(b)** |
| 5 | **Manifold regularity: `ω` (ours) vs. `∞` (theirs).** Analytic is a stronger hypothesis on `M`, so ours is a formally weaker theorem. Mathematically not a real restriction in dimension 3 (Whitney), but that bridge is not in mathlib either. We chose `ω` because instance search resolves it to every lower regularity; the cost is a narrower statement. | **(b)** |
| 6 | **Metric/connection regularity: `C²`/`C¹` (ours) vs. smooth (theirs).** Mixed direction. In the hypothesis, a `C²` metric makes our antecedent easier to satisfy (stronger); in the conclusion, producing only a `C²` metric is weaker. Ours is deliberate — `C²` is the minimum at which `ricciOfMetric` is well-posed — but it means our hypothesis and conclusion are not the same class of object as theirs. | **(b)** |
| 7 | **Connection quantified (ours) vs. constructed (theirs).** Different route, same content: we prove the existential equals the canonical connection, they prove the constructed connection is the unique torsion-free compatible one. Notably **their `LeviCivita_unique` is pointwise on sections differentiable at the comparison point**, with the paper's justification matching our corrected belief #0 almost word for word: a bundled `CovariantDerivative` is unconstrained on nondifferentiable inputs, so the pointwise form is the strongest appropriate statement. Independent confirmation that `∃!` was the wrong shape. | **(a)** |
| 8 | **Ricci as `ℝ`-valued function of two fields (ours) vs. a tensor-bundle section (theirs).** They built `Tensor0SSpace`/`TensorRSSpace` (continuous multilinear forms, and CLMs between them) so that `metricRicciAt g x` lives in a fiber over `x`. We use raw sections plus a tensoriality criterion with a junk branch. Their infrastructure is the **root cause** of divergences 1 and 2 being in their favour: once Ricci is a pointwise tensor, quantifying over tangent vectors is the natural thing to write. | **(b)**, structural |
| 9 | **Gram determinant `≠ 0` vs `> 0`** in our nondegeneracy guard. Equivalent by Cauchy–Schwarz. | **(a)** |

## Junk-value audit

The two we already fixed, confirmed still fixed:

- `sectionalCurvature` against arbitrary fields — `curvature X Y Y x` runs through
  `[X,Y]` and `∇_X ∇_Y Y`, junk on fields not differentiable at `x`. Guarded now
  by `CMDiff 2` on both fields.
- `ricci` with no regularity on the connection — returns `0` unless the first slot
  is tensorial, which needs `cov` `C¹` and the third-slot field `C²`. Guarded now
  by `ContMDiffCovariantDerivative cov 1` inside the existential.

Still open on our side, and both are places where theirs is immune:

- **The division in `sectionalCurvature`** (item 2). Guarded by a hypothesis on the
  quantified pair rather than by the definition, so any future lemma that drops the
  nondegeneracy hypothesis silently asserts things about `0`.
- **The vacuity of quantifying over global `C²` fields** (item 1).

Neither of these is a junk value on *their* side, because neither `metricRicciAt`
nor the multiplied-out curvature identity has a degenerate branch to fall into.

## What I would take from their design

1. Make Ricci and the curvature identity **pointwise in tangent vectors**. This is
   the one change that removes a real hazard rather than tidying. It requires the
   pointwise tensor we do not have — our own notes already record "no global `C²`
   extension of a tangent vector" as an open gap, and item 1 is the same gap seen
   from the statement side rather than the proof side.
2. **Write the sectional-curvature condition multiplied out.** Cheap, immediate,
   removes a division and a hypothesis.
3. Consider whether `ω` is worth its narrowing, and whether `T2Space` should be
   ambient regardless of item 1.

## Provenance note

They construct the Levi-Civita connection project-locally on mathlib v4.29.0; we
use mathlib's `leviCivitaConnection` (#36845), which landed after that release and
is why we track master on v4.34.0-rc2. So the two projects duplicate that layer
for a defensible reason on each side.

Their claimed axiom hygiene matches ours in kind: theorem-specific `#print axioms`
reporting only the three standard constants, with the paper careful to say this is
not the same as the repository being placeholder-free, and not to be paraphrased as
"axiom-free". That is the same standard `scripts/check_axioms.py` enforces here.
