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
| `Hamilton.lean` | `hasConstSecLC_tensor`/`_ricci`/`_scalar` — **constant sectional curvature delivers the full `(0,4)` tensor, `Ric = (n−1)k g` and `scal = n(n−1)k`** at the canonical Levi-Civita connection (`ConstantCurvature.lean` instantiated through `hasConstSecLC_iff_mul`); `hamilton_1982` — **stated**, `proof_wanted`, no sorry, no axiom. Predicates require a `C¹` witness and `C²` test fields (corrected 2026-09-04: the old `HasConstSecLC` quantified over arbitrary fields, i.e. over junk). `admitsPositiveRicciMetric_iff` / `admitsConstPositiveSecMetric_iff` restate them via `ricciOfMetric` / `sectionalCurvatureOfMetric` |
| `Pinching.lean` | Hamilton's curvature ODE in dimension 3 — ordering, positive Ricci, `λ ≤ C(μ+ν)` preserved; `pinching_antitone` (Hamilton Thm 10.1, ODE half). Linear Grönwall helpers `nonpos_of_deriv_le_mul` etc. No manifold. **Reopened for Hamilton–Ivey**: `iveyF` (= `x(log x - 3)`), `hasDerivAt_iveyF`, `iveyF_le_neg_three`, `IsIveyPinched` (Hamilton's set with no `f⁻¹`), `isIveyPinched_of_neg_one_le`, `le_of_isIveyPinched`, `iveyE`/`iveyE_nonneg` (the unified boundary polynomial), `iveyPsi`/`iveyPsi_nonneg` (the Grönwall), `nonneg_preserved`, `shift`, `restrict`, `neg_of_neg`, and **`hamiltonIvey`** (the ODE half, complete); `hasDerivAt_scal`, `le_scal` (`Ṙ = ½[(λ+μ)²+(λ+ν)²+(μ+ν)²] ≥ 0`, so any lower bound on `R` is preserved — the first inequality of Hamilton's set `K`), `hamiltonIvey_boundary_of_nonneg`/`_of_neg` (the boundary check with the log eliminated; pure polynomial, Cao–Zhu Cases (i)/(ii)). **Normalisation**: `λ,μ,ν` are *twice* the sectional curvatures, `R = λ+μ+ν`, Ricci eigenvalues `(μ+ν)/2` etc. — the header said `μ+ν`, off by 2; every proved statement is a sign or ratio claim so none moved |
| `GramSchmidtOrtho.lean`, `OrthonormalFrame.lean` | **Not ours.** Ported from unmerged mathlib PR #26221 (grunweg), Apache-2.0, see `NOTICE.md`. Gives `Module.Basis.orthonormalFrame` and `contMDiffAt_orthonormalFrame_of_mem`: a `C^k` **orthonormal** local frame of a Riemannian bundle, by pointwise Gram–Schmidt on `Trivialization.localFrame`. Mathlib has `IsLocalFrameOn` but no orthonormal version; it names the planned file in `LocalFrame.lean`'s header. **Delete when #26221 lands.** Upstream's one `sorry` (`contMDiffOn_iff_coeff'`, marked unused) was dropped |
| `GlobalExtension.lean` | **proved**: `exists_contMDiff_extension` (a global `C^k` section through any prescribed `v ∈ T_xM`, via `FiberBundle.exists_contMDiffOn_extend` plus a bump), `exists_contMDiff_two_extension`, and `forall_contMDiff_iff_forall_tangent` — quantifying over globally `C²` fields **is** quantifying over tangent vectors. This is what makes the `Hamilton.lean` predicates non-vacuous |
| `CurvaturePointwise.lean` | **proved**: `curvature_smul_third`, `curvature_sum_smul_third`, `curvature_congr_third`, `curvature_pointwise_third` (curvature depends on the third slot only through its value at the point), `ricci_congr_of_eq`, **`ricciAt`** (Ricci as a genuine function of two tangent vectors) + `ricciAt_eq`, `sectionalCurvature_congr'`, `inner_curvature_eq_zero_of_dep` |
| `Hessian.lean` | `hessian` (∇²), `hessian_sub_hessian_swap` (Ricci identity), tensoriality + `hessianAt`, `hessianFun` + `hessianFun_symm`, `laplacian` + `laplacian_eq_sum` + `laplacian_eq_sum_frame` (basis-independent metric trace, `OrthonormalBasis.sum_apply_self_eq` — which traces bilinear maps into **any** normed space, so the vector-valued trace needs no pairing against a covector, unlike `scal`). **This file already is `∇²` on sections and the rough Laplacian** — `hessian X Y Z x` is `∇²_{X,Y}Z`, `hessian_sub_hessian_swap` is the Ricci identity, and `hessianAt` is the bilinear map via `TensorialAt.mkHom₂`, which applies because `hessian_smul_right` needs only `MDiffAt`. Do not rebuild it: no frame-and-globalise argument is needed here, unlike the third slot of `curvature` |
| `SecondDerivativeTest.lean` | **proved**: `deriv2_nonneg_of_isLocalMin`, `fderiv2_nonneg_of_isLocalMin`, `fderiv_fderiv_apply_nonneg_of_isLocalMin` (chart-side core), `hessianFun_nonneg_of_isLocalMin` and `laplacianFun_nonneg_of_isLocalMin` on a **boundaryless manifold** (transport through `extChartAt`, same pattern as `mlieBracket_apply_fun`), plus the `*_model` versions. The connection term `(∇_X X) f` dies at a critical point, so any `cov` works |
| `MaximumPrinciple.lean` | **proved**: the scalar maximum principle on a compact space with the differential inequality assumed at spatial minima (`le_of_deriv_ge_at_min`, `le_of_deriv_le_at_max`). ε-perturbation `φ − ε e^{(2K+1)t}` + first touching time. No Laplacian |
| `TensorMaximumPrinciple.lean` | **proved**: Hamilton's tensor maximum principle abstractly (`mem_of_deriv_le_at_max`): `K` closed convex in a complete real inner product space, hypothesis `⟪n, ∂ₜu⟫ ≤ ⟪n, F(u)⟫` at spatial maxima of `⟪n,u⟫`, ODE-invariance in Nagumo form `⟪n, F p⟫ ≤ 0` for outward normals (`subtangential_of_invariant` derives it). Nearest point via `exists_norm_eq_iInf_of_complete_convex` + `norm_eq_iInf_iff_real_inner_le_zero`; distance via `Metric.infDist`, `le_infDist`. Same skeleton as the scalar one |
| `ManifoldMaximumPrinciple.lean` | **proved**: both principles on a closed Riemannian manifold (`le_of_laplacian`, `le_of_laplacian'`, `mem_of_laplacian`) for `∂ₜu = Δu + F(u)`, `u(t,·)` `C²`: the abstract theorems with the touching-point hypothesis discharged by `laplacianFun_nonneg_of_isLocalMin`. Tensor case is the trivial bundle, equation componentwise `⟪n, ∂ₜu⟫ = Δ⟪n,u⟫ + ⟪n, F u⟫`; a max of `⟪n,u⟫` is a min of `⟪-n,u⟫`, so no linearity lemma is needed. `hessianFun_neg`, `laplacianFun_neg` added to `Hessian.lean` |
| `Variation.lean` | **proved**: `covBilin` (∇ of a bilinear form field), `koszul_bilin_eq` (Koszul combination of a symmetric `h` through a torsion-free `∇` is `∇h`-terms `+ 2h(∇_X Y,Z)`), `leviCivitaOfMetric`, `inner_leviCivitaOfMetric_eq` (Koszul in `g.inner`), `hasDerivAt_inner_leviCivitaOfMetric` (Koszul differentiated in `t`), `inner_deriv_leviCivitaOfMetric_eq` (**first variation of ∇**). Hypotheses: `∂ₜ` commutes with `X(g(Y,Z))` for the fields at hand; differentiability of `t ↦ ∇ᵗ_X Y` (vector form only) |
| `CurvatureVariation.lean` | **proved**: `covEnd` (∇ of an `End`-valued one-form), `curvature_eq_add_covEnd` (curvature of `∇ + A`, `∇` torsion-free — algebraic), `hasDerivAt_curvatureE` (`∂ₜ Rᵗ = (∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)` along `∇ᵗ = ∇ + Aᵗ`), `exists_hasDerivAt_clm_of_apply` (coordinatewise ⇒ CLM-valued derivative), `differenceE` (Mathlib's `difference` on `E`), `derivDifferenceE` (`Ȧ = ∂ₜ∇` as `deriv`, no existential), `inner_derivDifferenceE_eq`, `hasDerivAt_curvatureE_leviCivitaOfMetric` (**first variation of Rm along metrics**). Hypotheses: `CommutesWithMvfderiv` (the `Variation.lean` commutation, all fields) and `∂ₜ`/`∇_X` commuting on `Aᵗ(Y,Z)` |
| `Bianchi.lean` | **proved**: `contMDiff_cov_apply` (`C^k` connection, `C^{k+1}` section, `C^k` field ⇒ `C^k` covariant derivative), `mlieBracket_sub_left'`, `covCurvature` (`(∇_X R)(Y,Z)W`), `bianchi_second` (**second Bianchi**, `C²` connection, `C²` fields, `C³` argument; no metric). The proof is the first-Bianchi pattern: split the sections, rewrite `∇_X Y − ∇_Y X` as `[X,Y]` in both the direction slot and as sections, `linear_combination (norm := module)` with Jacobi |
| `CurvatureDeriv.lean` | **proved**: **`∇R` is tensorial in all four slots.** *Direction* (`covCurvature_smul_dir`, `_add_dir`, with `cov_smul_dir`): each of the four terms picks up one `f x`, since `∇_{f•X} = f∇_X` and `R` is already tensorial in the slot it lands in (the third via `curvature_smul_third`). *`Y`* (`covCurvature_smul_snd`, `_add_snd`): a cancellation, not a rescaling — `∇_X(f•R(Y,Z)W)` gives a Leibniz term that `R(∇_X(f•Y),Z)W` cancels; applying Leibniz needs `y ↦ R(Y,Z)W y` to be a *differentiable section*, which is **`contMDiff_curvature`** (also here: a `C³` triple has a `C¹` curvature section, two `contMDiff_cov_apply` plus mathlib's `ContMDiffAt.mlieBracket_vectorField`). *`Z`* (`_smul_thd`, `_add_thd`): free from `Y` by **`covCurvature_antisymm`**. *`W`* (`covCurvature_smul_fth`, `_add_fth`): the same cancellation with the other pairing — `R(Y,Z)(f•W) = f·R(Y,Z)W` as *sections*, so `∇_X` contributes `(Xf)·R(Y,Z)W` and `∇_X(f•W) = f∇_X W + (Xf)W` contributes the match. **`f` must be `C³` here**, not `C²`: the second Leibniz term is `R(Y,Z)((Xf)•W)` and third-slot tensoriality wants its coefficient `C²`. Needed `curvature_smul_third'` (in `CurvaturePointwise.lean`) — the third-slot linearity asking of slots 1–2 only the `C¹` its proof uses, since the fields there are `∇_X Y`, `∇_X Z`. With all four slots, `div Rm(Y,Z,W) = ∑ᵢ ⟪(∇_{eᵢ}R)(Y,Z)W, eᵢ⟫` is well defined and frame-independent. **`∇Rm` is also pointwise in all four slots** (`covCurvature_congr_snd`/`_thd`/`_fth`, with `_congr_dir` in `Divergence.lean`) — so `∇Rm` is a genuine tensor. Slots 2 and 4 are the `CurvaturePointwise` frame-and-globalise argument one level up; locality is cheap because every term but the leading one is `Rm` in a tensorial slot, so only `∇_X(Rm(Y,Z)W)` needs the germ. Slot 3 is free from slot 2 by `covCurvature_antisymm`. **Slot 4 runs one derivative higher**: `covCurvature_smul_fth` wants a `C³` coefficient, so the frame and the coefficients are globalised at `C³` and the frame comes from `IsOrthonormalFrameOn … 3` (needing `IsContMDiffRiemannianBundle I 3`). Towards `Δ Rm`: `contMDiff_curvature_two` (`C⁴` fields ⟹ `C²` curvature section) and `contMDiff_covCurvature` (`C³`/`C⁴` fields ⟹ `C¹` `∇Rm` section). Levels there are hard-coded: `ContMDiffAt.mlieBracket_vectorField` indexes by `ℕ∞` while `ContMDiff` indexes by `ℕ∞ω`, and a variable level costs more cast bookkeeping than the twin proof. Note `T%` wraps the section, so `rw` cannot see through `curvature`'s definition — use `show`; and a Pi-`add`/`smul` residue after `simp only [add_apply]` is closed by `rfl`, not by `Pi.add_apply` |
| `Bochner.lean` | **proved**: **the Bochner identity** `Δ⟪σ,τ⟫ = ⟪Δσ,τ⟫ + ⟪σ,Δτ⟫ + 2∑ᵢ⟪∇_{eᵢ}σ,∇_{eᵢ}τ⟫` for a metric connection. `hessianFun_inner_eq` is the pointwise Hessian form — metric compatibility twice, and the Hessian's correction `−(∇_XY)⟪σ,τ⟫` expands (again by compatibility) into exactly the two corrections that turn the iterated derivatives into `∇²σ`, `∇²τ`. The trace is over the frame `laplacian`/`laplacianFun` are *already* defined on (canonical extensions of `stdOrthonormalBasis`), so no frame-independence is needed as input; the factor `2` is the two cross terms coinciding at `X = Y`. `laplacianFun_inner_self_eq` (`Δ|σ|² = 2⟪Δσ,σ⟫ + 2∑|∇_{eᵢ}σ|²`) and `two_mul_inner_laplacian_le` (`Δ|σ|² ≥ 2⟪Δσ,σ⟫`, the form `thm:max-scalar` consumes). **`sum_inner_cov_congr`** — the gradient term is frame-independent *on its own*, with no metric compatibility and no Bochner: `(v,w) ↦ ⟪∇_vσ,∇_wτ⟫` is a continuous bilinear form because `cov σ x` is a CLM, so `sum_apply_self_eq` applies. Also `MDifferentiableAt.inner_bundle'` (lean4#14949 wrapper, upstream candidate). Hypotheses are weak: `σ,τ` `C²`, and the direction fields need nothing (`X`) or `MDiffAt` (`Y`) |
| `CurvatureLaplacian.lean` | **proved**: **`Δ Rm` exists.** `cov2Curvature` = `∇²Rm`, with **one correction per slot of `∇Rm` — five terms**. `cov2Curvature_congr_dir` (pointwise in the outer direction) needs **no frame argument**: it is the four-slot pointwise lemma of `CurvatureDeriv.lean` cashed in — every term is a CLM at `X x` or `∇Rm` in a pointwise slot applied to a field whose value at `x` is determined by `X x`. The inner slot is the usual Leibniz cancellation (`_smul_snd`/`_add_snd`, coefficient `C³` so that `(Xf)` is `C²`) plus `cov2Curvature_congr_snd`, the frame-and-globalise argument at `C³`. Then `cov2CurvatureAt` (on `exists_contMDiff_three_extension`, new in `GlobalExtension.lean`), `cov2CurvatureBilin` as a `T_xM →L T_xM →L T_xM`, and `curvatureLaplacian` as its trace with `_eq_sum_basis`/`_eq_sum_frame` — frame-independence free by `sum_apply_self_eq`, vector-valued with no pairing. Regularity: `X,Y,A,B` `C³`, `C` `C⁴`. **The last slot is the expensive one at every level of the tower**: `C` needs four derivatives because `covCurvature_congr_fth` needs `C³` coefficients because `curvature_smul_third` needs `C²`. `Δ Rm` is the right-hand side of `∂ₜRm = ΔRm + Q`; the geometry side is done, `∂ₜRm` is still model-space |
| `Divergence.lean` | **proved**: **`div Rm` exists.** `covCurvature_congr_dir` — `(∇_X Rm)(Y,Z)W` at `x` depends only on `X x`, and this needs **no new frame argument**: each of the four terms is separately pointwise in `X` (the first is a CLM at `X x`; the middle two are `Rm` in a tensorial slot via mathlib's `TensorialAt.pointwise` on `tensorialAt_curvature_fst`/`_snd`; the last is `curvature_congr_third`). With direction-slot linearity that gives `covCurvatureAt` (on `exists_contMDiff_two_extension`, as `ricciAt` is) and the endomorphism `covCurvatureEndo`; `divCurvature` is its **endomorphism** trace — no metric, unlike `scal`, which is a *metric* trace of a bilinear form. So `divCurvature_eq_sum_basis` (frame-independence) is just `LinearMap.trace_eq_sum_inner`, and `divCurvature_eq_sum_frame` reads it off any `C²` frame orthonormal at `x`. Also **`divCurvature_eq_sub_sum`** — the **traced second Bianchi identity**: `div Rm(Y,Z,W) = ∑ᵢ⟪(∇_Y Rm)(eᵢ,Z)W,eᵢ⟫ − ∑ᵢ⟪(∇_Z Rm)(eᵢ,Y)W,eᵢ⟫`, by pairing `bianchi_second` with `eᵢ` and turning the middle term round with `covCurvature_antisymm`. No derivative of the frame appears — the identity is pointwise in `eᵢ` and only summed. Note `omit [CompleteSpace E]` fails on it (`bianchi_second` references the instance). **`sum_inner_covCurvature_eq`** closes the gap that left: `∑ᵢ⟪(∇_X Rm)(eᵢ,Z)W,eᵢ⟫ = (∇_X Ric)(Z,W)` (`covRicci`), the first-slot trace commuting with `∇`. Same mechanism as `TraceCov.lean` — the frame is not parallel, so `⟪∇_X eᵢ, eⱼ⟫` appears and `inner_cov_antisymm` + `sum_bilin_of_antisymm` kill it — but the bilinear form has to be *produced*: `curvatureBilinFst = (innerSL ℝ).comp (mkHom …)`, available only because `Rm` is tensorial in its first slot. Hence **`divCurvature_eq_covRicci_sub`**: `div Rm(Y,Z,W) = (∇_Y Ric)(Z,W) − (∇_Z Ric)(Y,W)`, the **contracted second Bianchi identity, first contraction**. Both connection hypotheses are used and for different things — torsion-freeness for `bianchi_second`, metric compatibility for the trace. **`two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt`** is the **second contraction**, `2 div Ric = d scal`: sum the first contraction over `Z = W = eⱼ`; on the right `TraceCov` gives `Y(scal)` and `covRicci_symm` (from `ricci_symm`) gives `div Ric(Y)`, on the left pair symmetry of `∇Rm` plus `sum_inner_covCurvature_eq` gives `div Ric(Y)` again. **Pair symmetry of `∇Rm` is not inherited for free**: `inner_curvature_pair_symm` is about the `(0,4)` tensor, while `covCurvature` is an operator on fields. `inner_covCurvature_expand` bridges them — for a *metric* connection `∇_X` moves onto the pairing, so `⟪(∇_X Rm)(A,B)C,D⟫` is `X⟪Rm(A,B)C,D⟫` minus **five** corrections, one per slot plus the metric one `⟪Rm(A,B)C,∇_X D⟫` — and the two sides' corrections are the same five numbers reordered. Frame must be `C³` there so `∇_X eᵢ` is `C²`. **Typing gotcha, load-bearing**: `sum_bilin_of_antisymm` wants `B : E →L[ℝ] E →L[ℝ] ℝ`, so `curvatureBilinFst` must be *declared* at that type (body ascribed through `TangentSpace I x →L …`) — declared at the `TangentSpace` type it is defeq but every later `rw` fails with "did not find the pattern" on a goal that prints identically. Also `innerSL_apply_apply`, not `innerSL_apply`; and `mkHom_apply` is reached by `show`, not `simp only`. Gotchas: `open scoped Classical in` for the `dite`, and it goes **before** the docstring like `omit`; `simp only [d, h, and_self, ↓reduceDIte]` then `rfl` (naming `LinearMap.coe_mk` trips the unused-simp-arg linter, which is a CI error) |
| `MetricTrace.lean` | **proved**: `sharpE` (`g♯⁻¹ ∘ B♭`), `metricTraceE` (`tr(g♯⁻¹ B♭)`), `metricTraceE_eq_sum` (= `∑ᵢ B(eᵢ,eᵢ)` over any `g`-orthonormal basis, via `LinearMap.trace_eq_sum_inner`), `sharpE_apply_eq_sum`, `metricTraceE_comp_sharpE_eq_sum` (`⟨h,B⟩_g`), `hasDerivAt_inverse_innerE` (`∂ₜ g⁻¹ = −g⁻¹ h g⁻¹`, from `contDiffAt_map_inverse` plus differentiating `g ∘ g⁻¹ = id`), `hasDerivAt_metricTraceE` (**`∂ₜ tr_{g_t} B_t = tr Ḃ − ⟨h,B⟩`**). All at a point on `E`. `metricTraceE_innerE_comp`, `ricci_eq_metricTraceE` bridge to `ricci`. **Two inequalities for the pairing** (2026-09-11): `metricTraceE_comp_sharpE_self_nonneg` (`⟨B,B⟩_g ≥ 0` for symmetric `B` — a sum of squares over any `g`-orthonormal basis) and `sq_metricTraceE_le_card_mul` (**`(tr_g B)² ≤ n·⟨B,B⟩_g`**, Cauchy–Schwarz: Chebyshev `sq_sum_le_card_mul_sum_sq` on the diagonal, then the off-diagonal squares are discarded by `Finset.single_le_sum`). At `B = Ric` these are `|Ric|² ≥ 0` and `R² ≤ n|Ric|²`, the two facts the scalar-curvature estimates run on. Needs `import Mathlib.Algebra.Order.Chebyshev` — it is not transitively available, and the lemma is in the **root** namespace, not `Finset` |
| `RicciForm.lean` | **proved**: **Ricci as an honest bilinear form and the scalar curvature on a general manifold**. `ricciAt_add_left`/`_smul_left`/`_add_right`/`_smul_right` (each field-level law applied to global `C²` extensions), `ricciForm x : E →L[ℝ] E →L[ℝ] ℝ` (`LinearMap.mk₂` + `toContinuousLinearMap` twice), `ricciForm_apply_field`; `scalarCurvatureAt` and `scalarCurvatureAt_eq_sum_basis` — **frame-independence is free** once `Ric` is bilinear (`OrthonormalBasis.sum_apply_self_eq`), so `scalarCurvatureWith_congr'` discharges the `h3` that `Scalar.lean` had to assume; `mvfderiv_scalarCurvatureAt_eq_sum_covBilin` = **`X(scal) = tr_g(∇_X Ric)`**, the trace lemma applied to `ricciForm` |
| `RicciSymm.lean` | **proved**: **Ricci is symmetric on a general manifold** for a metric torsion-free connection, with no hypotheses. `extendTwo`/`contMDiff_extendTwo`/`extendTwo_apply_self` (a *named* global `C²` extension — the anonymous `Exists.choose` of two vectors prints identically and `rw` cannot target one), `curvatureEndoAt` (the `hL` of `ricci_sub_ricci_swap`, now constructed: well-definedness from `curvature_congr_third`, linearity from `curvature_add_right`/`curvature_smul_const_right`), `trace_curvatureEndoAt_eq_zero` (skew-adjointness, via `LinearMap.trace_eq_sum_inner`), `ricci_symm`, `ricciAt_symm`, `ricciForm_symm`. Both hypotheses of `ricci_sub_ricci_swap` are now theorems |
| `CurvatureSymm.lean` | **proved**: **pair symmetry of the Riemann tensor** on a general manifold, `⟪R(X,Y)Z,W⟫ = ⟪R(Z,W)X,Y⟫` (`inner_curvature_pair_symm`) — the octahedron argument, four copies of first Bianchi linked by the two antisymmetries, closed by `linarith` in the six unknowns. `inner_bianchi_first` (first Bianchi paired against a vector; the fourth slot needs *no* regularity, the identity being a vector identity), `inner_curvature_left_skew`. This is what makes `R` an operator on `Λ²T_xM` — the form Hamilton's pinching and Uhlenbeck's trick need — and what the second contraction of second Bianchi will use |
| `ConstantCurvature.lean` | **proved**: **constant sectional curvature determines the whole `(0,4)` tensor** — `⟪R(X,Y)Z,W⟫ = k(⟪Y,Z⟫⟪X,W⟫ − ⟪X,Z⟫⟪Y,W⟫)` (`inner_curvature_eq_of_const_sec`, and `_norm` for the `‖·‖` form `hasConstSecLC_iff_mul` produces). `curvatureDefect` = `Rm − k·(model)`, with its four symmetries and four additivity laws; polarising slots 1&4 gives `T(A,B,B,C) = 0`, polarising 2&3 gives antisymmetry there, and a tensor antisymmetric in three consecutive slots is killed by first Bianchi (`3T = 0`). **Not a parity fix — a strengthening.** Their `admitsConstantPositiveSectionalCurvature` is the multiplied-out *sectional* identity `Rm(X,Y,Y,X) = c(g(X,X)g(Y,Y) − g(X,Y)²)`, which `hasConstSecLC_iff_mul` already matched; divergence 2 in `notes/hamilton-statement-comparison.md` was closed before this. What this adds is that the sectional identity determines the *whole* `(0,4)` tensor, so everything downstream of constant curvature can use `Rm` directly. Corollaries by tracing once and twice: `ricci_eq_of_const_sec` (`Ric = (n−1)k g`) and `scalarCurvatureAt_eq_of_const_sec` (`scal = n(n−1)k`), both over an arbitrary orthonormal basis with `n = Fintype.card ι`, so no `finrank` identification is needed |
| `IveyConvex.lean` | **proved**: **Hamilton's pinching set is closed and convex** — the input `thm:max-tensor` needs to carry Hamilton–Ivey from the ODE to the flow, and roadmap blocker (a). **`f⁻¹` is not needed and was never needed**: the disjunction in `IsIveyPinched` collapses to one inequality against `iveyG n = iveyF (max (-n) (e²))` (`isIveyPinched_iff_iveyG`), because `f` increases on `[e²,∞)` so the `-ν ≤ e²` branch gives `G = f(e²) = -e² ≤ -3`, which the *first* condition already supplies. `monotoneOn_iveyF`, `convexOn_iveyF` (via `MonotoneOn.convexOn_of_deriv` — `f' = log x − 2` is monotone), `convexOn_max_neg_exp_two`, `image_max_neg_exp_two`, `convexOn_iveyG` (`ConvexOn.comp`), `continuous_iveyG`; `iveyPinchedSet : Set (EuclideanSpace ℝ (Fin 3))` with `convex_iveyPinchedSet` and `isClosed_iveyPinchedSet` |
| `BilinDeriv.lean` | **proved**: **`∇h` is a tensor** for a bilinear form field `h`. Slot laws `covBilin_smul_dir`/`_add_dir`/`_congr_dir`, `_smul_snd`/`_add_snd`, `_smul_thd`/`_add_thd`; `tensorialAt_covBilin_dir`/`_snd`/`_thd`; `covBilinDir` (the direction as a linear form, by `mkHom`) and `covBilinForm` (`∇_X h` as a bilinear form, by `mkHom₂`) with `covBilinForm_apply`; `sum_covBilin_congr` (the metric trace of `∇_X h` is frame-independent *on its own*, by `sum_apply_self_eq`). **All three slots are cheap, unlike `∇Rm`'s four.** The direction slot needs *nothing*: `mvfderiv I f x` and `cov Y x` are already CLMs out of `T_xM`, so linearity and pointwiseness hold by construction. Slots `Y`/`Z` are the plain Leibniz cancellation on `MDiffAt` fields (the `hessian_smul_right` pattern), so no frame-and-globalise. One hypothesis is carried, `IsMDiffBilinAt h x` (`y ↦ h y (U y) (V y)` differentiable for differentiable `U`,`V`) — what makes Leibniz available. **Gotchas, all the `E` vs `TangentSpace` family**: `map_add`/`map_smul` will not `rw` when the `+`/`•` is `TangentSpace`-typed and the CLM is `E`-typed — state the fact at the `E` type (`key : ∀ c d v v' w : E, h x (c•v + d•v') w = …`) and close with `exact`, which is up to defeq. `(f • X) x` is not reduced by `Pi.smul_apply` on a dependent Pi — `have hfx : (f • X) x = f x • X x := rfl` then `simp only [hfx]`. And a hand-built `∘L` between `T_xM →L T_xM` and `E →L ℝ` will not unfold under `simp`; get the direction CLM from `TensorialAt.mkHom` instead |
| `BilinLaplacian.lean` | **proved**: **`∇²h` and `Δ_g h` for a bilinear form field.** `cov2Bilin` = `(∇²_{W,X}h)(Y,Z)`, with **one correction per slot of `∇h` — three terms**, against `cov2Curvature`'s five. The two derivative slots split the same way they do for `∇²Rm`: the **outer** direction `W` needs **no frame argument** (`cov2Bilin_congr_dir`, `_smul_dir`, `_add_dir`) — it is `BilinDeriv.lean` cashed in, every term being a CLM at `W x` or `∇h` in a slot it is already pointwise in; the **inner** direction `X` is the Leibniz cancellation (`_smul_snd`/`_add_snd`) plus `cov2Bilin_congr_snd`, the frame-and-globalise argument — but **at `C¹`**, not `∇²Rm`'s `C³`, because `cov2Bilin_smul_snd` asks its coefficient for one derivative. **The inner cancellation is cheap**: every step but the leading one uses only the *direction* slot of `∇h`, which carries no hypotheses. Then `cov2BilinAt` (on `exists_contMDiff_two_extension`), `cov2BilinForm` as a `T_xM →L T_xM →L ℝ`, and `laplacianBilin` as its trace with `_eq_sum_basis`/`_eq_sum_frame` — frame-independence free by `sum_apply_self_eq`. **`traceBilin`** (`tr_g h` as a function on `M`, frame-independent since `h y` is already a CLM) and **`hessianFun_traceBilin_eq`**: `∇²(tr_g h)(X,Y) = ∑ᵢ (∇²_{X,Y}h)(eᵢ,eᵢ)` — **the trace commutes with `∇²` too**, by the same mechanism as the divergence one level up: differentiating the frame sum twice gives `∇²h` **plus** exactly the `tr_g(∇_{∇_XY}h)` that the Hessian's connection correction subtracts. Same beta-redex hazard as `OneForm.lean`'s, same fix. One hypothesis beyond `IsMDiffBilinAt`: `IsMDiffCovBilinAt` (`y ↦ (∇_V h)(Y,Z)` differentiable for `C¹` `V`) — merely-`MDiffAt` `V` cannot supply it, since the leading term of `∇h` differentiates `h(Y,Z)` in the direction `V` and so sees the germ of `V`. That is exactly why the inner slot needs the frame argument and the outer one does not |
| `OneForm.lean` | **proved**: **`∇ω`, `div ω`, `div h` and `div div h`.** `covOneForm` (`(∇_X ω)(Y) = X(ω(Y)) − ω(∇_X Y)`) has **two** terms, against `covBilin`'s three and `covCurvature`'s four, so **both slots are free of any frame argument** — direction by construction, `Y` by the plain Leibniz cancellation on `MDiffAt` fields — and `mkHom₂` gives `covOneFormAt` directly; `divOneForm` is the trace, frame-independent by `sum_apply_self_eq`. For `ω = df` these are `Hessian.lean`'s `hessianFun`/`laplacianFun`. **The payoff is that `div div h` needs no four-linear packaging of `∇²h`**: it factors as `div(div h)`, and `div h` (`(div h)(Z) = ∑ᵢ (∇_{eᵢ}h)(eᵢ,Z)`) is the 1&2 trace of the `(0,3)`-tensor `∇h` — one `mkHom₂` over (direction, slot 2), `covBilinFstSnd` — which is tensorial in its remaining slot as a finite sum (`tensorialAt_sum`, a small general helper) and so an honest one-form field (`divBilinForm`, `divBilinOneForm`). `IsMDiffBilin` is the global form of `IsMDiffBilinAt`, needed because `div div h` differentiates `div h` as a *field*. **`hessianFun_eq_covOneForm` / `laplacianFun_eq_divOneForm` are `rfl`** — `∇²f(X,Y)` and `(∇_X df)(Y)` are literally the same expression — and that is load-bearing, not a remark: it **hands the Hessian its bilinear packaging for free**. `∇²f` on its own has no cheap route to one (a `TensorialAt` instance would need `y ↦ df_y(Y y)` differentiable for merely-`MDiffAt` `Y`, the same obstruction as `IsMDiffCovBilinAt`), but `∇ω` has two terms and needs no frame argument, so `laplacianFun_eq_sum_frame` falls out of `divOneForm_eq_sum_frame`. Hence **`laplacianFun_traceBilin_eq`**: `Δ(tr_g h) = tr_g(Δ_g h)`, the last identification the flow needs — both sides off the same frame, terms matched by `hessianFun_traceBilin_eq`, plus one `Finset.sum_comm`. Gotcha: `omit` needs the binder spelled out — `omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]`, not `fun x ↦ …`, or the omit silently fails and instance search sticks on `ChartedSpace H ?m`. **`covOneForm_divBilinOneForm_eq_sum`** — **the divergence commutes with `∇`**: `(∇_W(div h))(Z) = ∑ᵢ (∇²_{W,eᵢ}h)(eᵢ,Z)`, hence **`divDivBilin_eq_sum`**, `div div h = ∑_{j,i}(∇²_{eⱼ,eᵢ}h)(eᵢ,eⱼ)` — the iterated definition equals the double trace the flow produces. It is `TraceCov`'s lemma on `(v,w) ↦ (∇_v h)(w,Z)`: differentiating the frame sum gives `∇²h` **plus** exactly the `(div h)(∇_W Z)` that `∇_W` of a one-form subtracts, so no curvature term survives. **Gotcha, expensive**: matching `divBilinForm_apply` against a beta-redex (`(fun y ↦ cov Z y (W y)) x` vs `cov Z x (W x)`) sends the unifier through `mkHom` into the trivialisations behind `FiberBundle.extend` and it never returns — a `whnf` timeout that more heartbeats do not fix. Pass the value explicitly: `∀ v V, MDiffAt V x → V x = v → …`, applied with `rfl` |
| `KoszulSecondDeriv.lean` | **proved**: **differentiating the Koszul combination gives the same combination one level up, with no curvature terms.** `covTwoTensor` (`∇` of a `(1,2)`-tensor), `IsKoszulOf` (the characterisation `⟪A(P,Q),R⟫ = ½[(∇_Ph)(Q,R) + (∇_Qh)(R,P) − (∇_Rh)(P,Q)]` on `C¹` fields, which is what `inner_derivDifferenceE_eq` supplies for `A = ∂ₜ∇`), and **`inner_covTwoTensor_eq`**: `⟪(∇_U A)(P,Q),R⟫ = ½[(∇²_{U,P}h)(Q,R) + (∇²_{U,Q}h)(R,P) − (∇²_{U,R}h)(P,Q)]` for a metric connection. Metric compatibility moves `∇_U` onto the pairing; differentiating the germ identity gives the three `∇²h` terms **plus nine corrections**, which regroup three-by-three (one group per differentiated field) into exactly the three Koszul combinations that `∇_U A` and the pairing subtract — the regrouping is linear, so it is `linarith` once the four expansions are in hand. **This is what turns `∂ₜRm` into a statement about `∇²h` alone.** **`sum_inner_covTwoTensor_eq`** traces it twice: for symmetric `h`, `∑_{i,j}⟪Rm_A(eᵢ,eⱼ)eⱼ,eᵢ⟫ = div div h − tr_g(Δ_g h)` where `Rm_A(X,Y)Z = (∇_XA)(Y,Z) − (∇_YA)(X,Z)` is what `∂ₜRm` equals — **no curvature terms at any stage**; `sum_inner_covTwoTensor_eq_divDiv` names the two sums. **Symmetry of `h` is what collapses six double sums to two**: `cov2Bilin_symm` (from `covBilin_symm`, both in `BilinLaplacian.lean`) identifies `(∇²_{U,a}h)(b,c)` with `(∇²_{U,a}h)(c,b)`, merging the first two terms of each Koszul combination; the rest is one `Finset.sum_comm`. **`∇A` is also pointwise in both slots a traced vector can land in**: the *direction* is free (`covTwoTensor_congr_dir` — every term is a CLM at `U x`), and the tensor's *first argument* is the Leibniz cancellation, so `TensorialAt` applies and `covTwoTensor_congr_snd` needs no frame argument. One hypothesis, `IsMDiffTwoTensorAt` (`y ↦ A y (P y)(Q y)` differentiable for differentiable `P`,`Q`) — for `A = ∂ₜ∇` a regularity hypothesis on the first variation, carried alongside the commutation ones. Gotchas: `MDifferentiableAt.add` produces a *Pi*-add type, so `mvfderiv_fun_sub` picks the wrong higher-order unifier — ascribe `have hadd : MDiffAt (fun y ↦ a y + b y) x := hd₁.add hd₂` first; there is no `mvfderiv_fun_div_const`, so state the germ identity as `… = fun y ↦ 2 * ⟪…⟫` and use `mvfderiv_fun_mul mdifferentiableAt_const` with `mvfderiv_const` killing the other term |
| `FlowKoszul.lean` | **proved**: **`∂ₜRm` is the `Rm_A` of `KoszulSecondDeriv.lean`.** Two conventions had to be lined up: `covEnd` (which the curvature variation is phrased in) takes a `(1,2)`-tensor **argument first, direction second** — matching `differenceE` — while `covTwoTensor` takes the **direction first**, so the two agree on *flipped* tensors term for term (`covEnd_eq_covTwoTensor_flip`, a `rfl`). `derivDifferenceTensor` is that flip of `∂ₜ∇`; **`isKoszulOf_derivDifference`** says it is Koszul for `h = ∂ₜg` — `inner_derivDifferenceE_eq` states this on `FiberBundle.extend` fields and the `covBilin` congr lemmas transfer it to arbitrary `C¹` fields; **`hasDerivAt_curvatureE_covTwoTensor`** delivers `∂ₜRm` as `Rm_A` (also a `rfl` once the flip is right). **`derivCurvatureEndoE_apply_field`** moves `∂ₜ[v ↦ Rm(v,X)Y]` off the `extend` field the variation formula produces and onto an arbitrary differentiable field, which is what lets the double trace be read off a frame. **`metricTraceE_derivRicciFormOfMetric_eq`** then reads both traces off one frame — outer by `metricTraceE_eq_sum`, inner by `LinearMap.trace_eq_sum_inner` — and **`metricTraceE_derivRicciFormOfMetric_eq_sub`** combines with the double-trace theorem to give **`tr_g(∂ₜRic) = div div h − tr_g(Δ_g h)`** for the actual flow, with no curvature terms. **Two typing walls here, both with the same fix**: ascribing an `E →L[ℝ] E` to `T_xM →L[ℝ] T_xM` grinds `isDefEq` forever (a `whnf` timeout unaffected by 5× heartbeats) — ascribe to **`→ₗ[ℝ]`** instead and `change` the trace, exactly as `metricTraceE_eq_sum` does; and `⟪·,·⟫` will not elaborate on an `E`-typed value, so state the summand as an equation between *tangent vectors* (no inner product) and rewrite with it. Also: `isMetricCompatible_leviCivitaOfMetric` **cannot be stated** as a standalone lemma (CLAUDE.md's `IsMetricCompatible` rule — no ambient `RiemannianBundle` binder here); pass mathlib's `isMetricCompatible_leviCivitaConnection I (M := M)` directly at the application site, where the expected type is already fixed. **The `letI RiemannianBundle` hazard is real but survivable here**: the conclusion is written `letI : RiemannianBundle … := ⟨(g t₀).toRiemannianMetric⟩` before the `IsKoszulOf`, re-introduced in the proof by `let _ : … := …`, and `⟪·,·⟫` is then defeq to `(g t₀).inner y`. Gotcha: `.flip` on a `T_yM →L T_yM →L T_yM` needs a norm on `T_yM`, which only a `RiemannianBundle` supplies — so state the bridge with `A : M → E →L E →L E` and ascribe the flip to the `TangentSpace` type, as `covEndE` does |
| `ScalarEvolution.lean` | **proved**: **`div div Ric = ½ Δ scal`** — the second contraction of the second Bianchi identity with the divergence taken once more. `divBilin_ricciForm_eq` reads `2 div Ric = d scal` as an identity of **one-forms** rather than a frame sum: `divBilin` is the 1&2 trace of `∇Ric`, `covBilin_ricciForm_eq_covRicci` turns each term into `covRicci`, and `two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt` evaluates the sum. `divBilinForm_ricciForm_eq` upgrades that to a CLM identity on the frame's whole base set (so the germ is available), and **`divDivBilin_ricciForm_eq`** takes the divergence again, using `divOneForm_congr` (germ-locality) and `divOneForm_smul` (linearity in `ω`) plus `laplacianFun_eq_divOneForm`. Everything is stated for a fixed metric connection with an **ambient `RiemannianBundle` binder** — the `letI` hazard only bites at the final specialisation. Gotcha: writing `(c • (mvfderiv … : T_yM →L ℝ) : E →L ℝ)` gives the *TangentSpace* scalar action, so `divOneForm_smul` will not match; `obtain ⟨v, hv⟩ : ∃ v : M → E →L[ℝ] ℝ, v = … := ⟨_, rfl⟩` first and write `c • v y`, which is `E`'s. **`sum_cov2Bilin_neg_two_ricciForm_eq`**: at `h = −2Ric` the two canonical double traces are `div div h = −2·½Δscal = −Δscal` and `tr_g(Δ_g h) = Δ(tr_g h) = −2Δscal`, so their difference is **`Δ scal`** — i.e. `tr_g(∂ₜRic) = Δ scal` under the flow. Getting there needs **only** linearity of `∇²h` in `h` (`cov2Bilin_smul_form`, from `covBilin_smul_form` in `BilinDeriv.lean`): everything downstream is already proved for `Ric` itself, and `traceBilin ricciForm = scalarCurvatureAt` is `rfl` — the same frame sum by definition |
| `ScalarFlow.lean` | **proved**: **`∂ₜ scal = Δ scal + 2\|Ric\|²` on a general manifold** — the first evolution equation of the flow formalised here in full, and the close of roadmap item 2. `metricTraceE_derivRicciFormOfMetric_eq_laplacian` joins the two halves: `FlowKoszul.lean` gives `tr_g(∂ₜRic) = div div h − tr_g(Δ_g h)` (no curvature terms — they cancel at the Koszul step, before any Bianchi identity), `innerE_deriv_eq_of_isRicciFlowAt'` supplies `h = −2 Ric` as a *function* equality (`funext`), and `ScalarEvolution.lean`'s `sum_cov2Bilin_neg_two_ricciForm_eq` evaluates the difference to `Δ scal`. **`hasDerivAt_scalarCurvatureOfMetricAt_eq_laplacian_add`** then composes with `hasDerivAt_scalarCurvatureOfMetricAt_of_isRicciFlowAt`. **Every hypothesis is written under a two-step `letI`**: `RiemannianBundle … := ⟨(g t₀).toRiemannianMetric⟩` *and* `ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1 := contMDiffCovariantDerivative_leviCivitaOfMetric_one (g t₀)` — `ricciForm`, `scalarCurvatureAt`, `divBilinOneForm` and `IsMDiffCovBilinAt` all need the *instance*, not just the metric, and a hypothesis-position `letI` supplies only what it names. `ContMDiffCovariantDerivative … 2` is carried as an **explicit hypothesis** (`hlc2`): a `C²` metric gives only a `C¹` connection, so it is not derivable here, and `ScalarEvolution.lean`'s section requires it. `hsymm` and the `∇h`-differentiability hypothesis are derived from the `Ric` ones by `ricciForm_symm` and `covBilin_smul_form`; there is no `MDifferentiableAt.const_mul`, use `mdifferentiableAt_const.mul` |
| `CovariantAlongCurve.lean` | **proved**: **`D/dt`, the covariant derivative along a curve**, as a predicate — the first brick of the self-built comparison-geometry substrate. Mathlib's `CovariantDerivative` acts on **global sections over `M`**, so `∇_{γ'}γ' = 0` cannot even be *stated*; the missing primitive is the pullback connection on `γ*TM`. `velocity` (`γ'(t)` via `mfderiv` at `1 : TangentSpace 𝓘(ℝ,ℝ) t`), `MDiffAlongAt` (a section along `γ` is a lift of `γ` to `TM`, so regularity is ordinary `MDifferentiableAt` into the total space — **no new bundle structure needed**), and `IsCovDerivAlong` with the three axioms: additive, Leibniz over `f : ℝ → ℝ`, and `D(W ∘ γ) t = cov W (γ t) (velocity γ t)`. Then `MDiffAlongAt.zero_section`, `IsCovDerivAlong.zero`, and **`congr_of_eventuallyEq`** — `D` is **local**, not by fiat: a `ContDiffBump` equal to `1` near `t` and supported where the sections agree makes `f • V = f • W` *globally*, while Leibniz evaluates both sides at `t` (`f t = 1`, `deriv f t = 0`). Gotchas: the bump's support lemma is `ContDiffBump.support_eq` (there is no `support_subset_ball`), and `import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct` is what supplies `HasContDiffBump ℝ`; `contMDiff_zeroSection` needs `(n := 1)` or the level stays a metavariable. **Uniqueness is proved** (`IsCovDerivAlong.eq_of_isCovDerivAlong`), on top of **`exists_frame_expansion`**: near `t` a section along `γ` is `∑ᵢ fᵢ·(Wᵢ∘γ)` with `Wᵢ` *global* `C¹` and `fᵢ` differentiable, so locality + `add` + `leibniz` + `restrict` compute `D V t` with no `D` left in it. Everything is read off **one trivialisation** around `γ t`: the frame is mathlib's `Trivialization.localFrame` for `Module.finBasis`, globalised by `exists_contMDiff_eventuallyEq`; the coefficients are `b.repr (e ⟨γ u, V u⟩).2 i`, differentiable because **`mdiffAlongAt_iff_of_mem`** says differentiability along `γ` *is* differentiability of those coordinates (`Trivialization.mdifferentiableAt_totalSpace_iff`, base component discharged by `hγ`). Same criterion gives `MDiffAlongAt.add`/`.smul`/`.sum`, a trivialisation being fibrewise linear (`continuousLinearEquivAt`, and the `map_add`/`map_smul` go through by **defeq with `exact`** — `simp only [← continuousLinearEquivAt_apply]` makes no progress, the lemma being a function equality). **Take finite sums fibrewise, not in the Pi type**: `Finset.sum` over `Π t, T_{γ t}M` picks an `AddCommMonoid` only *defeq* to the one `Fintype.sum_apply` produces, so `rw` fails on goals that print identically and even `Eq.trans` will not unify — state every sum as `fun u ↦ ∑ i ∈ a, Vs i u` and step the induction with `funext` + `Finset.sum_insert`. **Existence is proved too** (`isCovDerivAlong_covAlong`, `exists_isCovDerivAlong`, `eq_covAlong`) — which is what stops `∇_{γ'}γ' = 0` being *vacuously* true, the repo's worst class of error. `covAlong` is the classical formula in the trivialisation at `γ t`: `∑ᵢ (cᵢ'(t)·Wᵢ(γt) + cᵢ(t)·∇_{γ'}Wᵢ)` with `Wᵢ = canonFrame` (the globalised local frame) and `cᵢ = coeffAlong`. **`add` and `leibniz` are facts about `deriv`** — the coordinates are additive and scale, a trivialisation being fibrewise linear — and `leibniz`'s second term is `f'(t)·∑ᵢcᵢ(t)Wᵢ(γt) = f'(t)·V t` (`sum_coeffAlong_smul_canonFrame`). **`restrict` is the only one with content**: it is `cov`'s own Leibniz rule on `W = ∑ᵢ aᵢ Wᵢ`, transported by mathlib's `IsCovariantDerivativeOn.congr_of_eventuallyEq` (germ-locality of `∇`, already in mathlib — do not reprove it), plus `cov_sum_smul_section_apply` and the chain rule `deriv (a∘γ) t = mvfderiv a (γt) (γ' t)` (`deriv_comp_curve`, from `mvfderiv_comp_apply`; the residual goal closes by `simp only [mvfderiv, mfderiv_eq_fderiv]; rfl`, `fromTangentSpace` being the identity). **`rw` cannot see through `T%`** — it beta-reduces to `fun y ↦ ⟨y, σ y⟩` — so state section rewrites as `T% σ = T% τ` proved by `funext` + `show ⟨y,_⟩ = ⟨y,_⟩`. `W`'s frame coefficients need only `MDifferentiableAt`, so take them as `b.repr (e ⟨y, W y⟩).2 i` off `mdifferentiableAt_totalSpace_iff` rather than via `contMDiffAt_localFrameCoeff`, which wants `C¹`. **`IsParallelAlong`/`IsGeodesicOn`** are defined off `covAlong`, with `isParallelAlong_iff_forall`/`isGeodesicOn_iff_forall` proving them equivalent to vanishing under *every* operator satisfying the axioms — forward by uniqueness, backward by existence; without the latter the quantified form is vacuous. The reusable tool is **`IsCovDerivAlong.eq_sum_of_expansion`** (extracted from the uniqueness proof): `D/dt` is computed by *any* local expansion `V = ∑ᵢ fᵢ(Wᵢ∘γ)`, which is what will read the coordinate ODE off the coordinate frame. `velocity γ` as a *section* needs `velocity (I := I) γ` or instance search sticks on `ChartedSpace ?H M`. **The coordinate form is proved**: `covAlong_eq_sum_of_frame` says `D/dt` may be read in *any* trivialisation around `γ t` (not just the preferred one it is defined through), and `repr_covAlong_eq` is `(D/dt V)ᵏ = (cᵏ)' + ∑ᵢ cⁱ Γᵏᵢ` with `Γᵏᵢ = (∇_{γ'}Wᵢ)ᵏ`. Gotchas there: `b.repr` of a `Finset.sum` needs **`Finset.sum_apply'`** (the Finsupp one) after the two `map_sum`, or the outer `simp only` sees `(∑ …) k` and makes no progress; and `if_pos` is deprecated (a CI error) — use `simp only [Finset.mem_univ, ↓reduceIte]`. **`exists_frame_on_open` is the piece an ODE needs**: globalising the local frame one point at a time gives agreement only *near* that point (`=ᶠ[𝓝 y₀]`), useless along an arc; intersect the finitely many agreement sets, take `interior`, and intersect with `e.baseSet` — `mem_interior_iff_mem_nhds` plus `Filter.eventually_all` does it in four lines, with no change to `GlobalExtension.lean`. `covAlong_eq_sum_of_frame_on` reads the formula off that `U`, and `christoffel`/`repr_covAlong_eq_christoffel` package the correction as `Γ(y)(v)(c) = ∑ᵢ cⁱ ∇_v Wᵢ`, giving `D/dt V = c' + Γ(γt)(γ')(c t)`. **`Γ` is as regular as the connection**: `christoffelCoord` is the classical `Γᵢⱼ(y)` (`e`-coordinates of `∇_{Wⱼ}Wᵢ`), `christoffel_eq_sum` is bilinearity in the two slots, and `contMDiffAt_christoffelCoord` is `contMDiff_cov_apply` (from `Bianchi.lean` — hence the import) followed by mathlib's `contMDiffAt_section_iff`: a `C^k` connection and a `C^{k+1}` frame give `C^k` symbols. **That lemma is the first in the file to use any regularity of `cov` at all**; everything before it holds for a bare `CovariantDerivative`. What is left before `exp` is identifying the tangent-bundle trivialisation with the chart it comes from, which puts the geodesic equation on an open subset of `E` where Picard–Lindelöf applies |
| `Exponential.lean` | **proved**: **affine reparametrisation of geodesics**, the invariance `exp` is built on. `velocity_comp_mul` is the chain rule `velocity (γ ∘ (·*a)) t = a • velocity γ (t*a)` — via `HasMFDerivAt.comp` on `mfderiv_eq_smulRight_velocity`; state the `HasMFDerivAt` of `s ↦ s*a` by `hasMFDerivAt_iff_hasFDerivAt.mpr` (a `rw` fails on the `TangentSpace` instances) and get the `HasFDerivAt` in the `smulRight 1 a` form from `hasDerivAt_iff_hasFDerivAt.mp`, not from `HasDerivAt.hasFDerivAt` (which produces `toSpanSingleton ℝ (1*a)`); the declaration still needs `set_option backward.isDefEq.respectTransparency false in`. **The geodesic statement is nearly free** (`covAlong_velocity_comp_mul_eq_zero`, `_'`, `isGeodesicOn_comp_mul`): in the chart `p'' = −Γ̃(p)(p')(p')`, reparametrising multiplies the left by `a²`, and `Γ̃` is **bilinear by construction**, so `map_smul` twice on the right matches. **No case split on `a = 0`** — both sides vanish, so the constant curve is a geodesic with no separate argument about `D/dt` of the zero section. **Boundarylessness is not needed** here (unlike existence and uniqueness): the argument reads the equation in a chart but never differentiates the inverse chart. The enabling bridge is `covAlong_velocity_eq_zero_iff_chart` in `GeodesicODE.lean`, which restates the equation against `christoffelChart` (a function of the chart coordinate) rather than `christoffel` (a function of the base point) — the form every in-chart computation wants. **Uniqueness on a whole preconnected open set** (`forall_totalSpace_eq_of_isGeodesicOn`, `eqOn_of_isGeodesicOn`): the clopen argument on the agreement set in `TM`. Open is `eventuallyEq_of_isGeodesic'` — agreeing *near* a point makes the curves the same function there, so the velocities agree by `Filter.EventuallyEq.mfderiv_eq`, whose `tangentSpaceCast` is literally the identity and dies by `rfl`. **Closed is where mathlib is missing a piece: there is no `T2Space` instance on the total space of a bundle**, so the diagonal of `TM × TM` is unavailable; take closedness in two Hausdorff pieces instead — the base in `M`, the fibre coordinate `(e ⟨c u, c'(u)⟩).2` in `E` — and reassemble by `e.toPartialHomeomorph.injOn`. The fibre coordinate is continuous at the point exactly because `mdiffAlongAt_iff_of_mem` turns differentiability *along* the curve into differentiability of that coordinate. Extracted tool: **`eq_of_mem_closure_of_continuousAt`** — two maps agreeing on `A` and continuous *at* a point of `closure A` agree there; the usual `IsClosed {f = g}` argument with continuity assumed only where needed. Upstream candidate. **`exp` is built** — the first object of the comparison-geometry substrate. `IsGeodesicRun cov c s x v` packages exactly what uniqueness asks (open preconnected `s ∋ 0`, `c` and its velocity differentiable along it, the equation, and the initial data as **one** equation in `TM`); `exists_isGeodesicRun` is `exists_isGeodesicOn'` (whose conclusion was strengthened to hand back the differentiability it already proves); `IsGeodesicRun.eq_of_mem` is interval uniqueness on `s₁ ∩ s₂`, **preconnected because in `ℝ` preconnected = order-connected and that survives intersection** (`isPreconnected_iff_ordConnected`, `Set.OrdConnected.inter`); `IsGeodesicRun.comp_mul` reparametrises a run, needing `mdiffAlongAt_velocity_comp_mul` (the reparametrised velocity is differentiable along the curve — its coordinate is `a • v(u·a)`). Then **`expMap`** by choice on runs reaching time `1`, with **`expMap_eq`** (*any* such run computes it — that **is** well-definedness), **`expMap_smul_eq`** (`exp_x(a v) = γ_v(a)`, reparametrisation cashed in, which is what makes `exp` a map near the origin rather than one value) and **`expMap_zero`** free from it. Gotchas: **`dif_pos` is deprecated** (a CI error) — use `rw [expMap]; split` with `next hP =>`, not a `simp` on the condition; the `init` field's goal does not beta-reduce, so `simp only [zero_mul]` makes no progress — `show` the reduced form first; and scaling the fibre of a total-space equality is `congrArg (fun q ↦ ⟨q.proj, a • q.2⟩)`, which avoids ever projecting the dependent second component |
| `GeodesicODE.lean` | **proved**: **the tangent-bundle trivialisation *is* the chart** — the identification that turns `∇_{γ'}γ' = 0` into an ODE. `trivializationAt_snd_eq_tangentCoordChange` is a **`rfl`**: mathlib's `TangentBundle.trivializationAt_apply` already unfolds `(e_{x₀}⟨y,v⟩).2` to the `fderivWithin` that `tangentCoordChange` is. `hasDerivAt_extChartAt_comp` then gives `p'(t) = tangentCoordChange I (γt) x₀ (γt) (γ'(t))` for `p u = extChartAt I x₀ (γ u)`, so **`deriv_extChartAt_comp_eq_trivializationAt`**: the chart position's derivative *is* the velocity's fibre coordinate, and `coeffAlong_velocity_eq` says `coeffAlong` for `V = γ'` is `p'` in the model basis — so `D/dt V = c' + Γ(γ)(γ')(c)` at `V = γ'` is an equation in `p'` and `p''`. **The chart-side manoeuvre is mathlib's own**, from `IntegralCurve/Basic.lean`: compose the curve's `HasMFDerivAt` with the chart's, then `mfderiv_chartAt_eq_tangentCoordChange`. The only adjustment is dropping the integral-curve hypothesis, for which `mfderiv_eq_smulRight_velocity` (a curve's differential is the `smulRight` of its velocity) holds with **no** hypothesis — a CLM out of `ℝ` is determined at `1`, so both sides are junk together. **Gotcha, load-bearing**: `rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]` fails on the `TangentSpace` instances unless the declaration carries **`set_option backward.isDefEq.respectTransparency false in`** — mathlib guards its own copy the same way. Also `ContinuousLinearMap.one_apply` is deprecated (→ `one_apply_eq_self`), and `(1 : ℝ →L[ℝ] ℝ).smulRight v` *prints* as `toSpanSingleton ℝ v`, so `rw` with `smulRight_apply` misses; finish with `rfl`. **The ODE is assembled**: `trivializationAt_covAlong_eq` pushes `covAlong_eq_sum_of_frame` through the trivialisation to give `(D/dt V)ᵉ = q' + Γ(γ)(γ')(q)` with `q u = (e⟨γu,Vu⟩).2` — **a vector equation in `E` with no basis in the statement**, the basis eliminated by `sum_deriv_repr_smul` (the coefficients of `q'` *are* the derivatives of the coefficients of `q`). At `V = γ'` the identification turns `q` into `p'`, giving **`covAlong_velocity_eq_zero_iff`**: `∇_{γ'}γ' = 0 ↔ p'' = −Γ(γt)(γ')(p')`. The *iff* is free because a trivialisation is a linear **equivalence** on each fibre, so vanishing may be tested in coordinates (`continuousLinearEquivAt.map_eq_zero_iff`). Gotchas: `∀ᶠ u in 𝓝 t, f u = g u` is `Filter.Eventually`, **not** `EventuallyEq` — `.deriv_eq` needs the type stated as `f =ᶠ[𝓝 t] g`; and `.self_of_nhds` leaves a beta-redex that `rw` cannot match, use `.eq_of_nhds` bound to a `have` with the reduced statement. **`Γ` is packaged for Picard–Lindelöf**: `christoffelB y : E →L[ℝ] E →L[ℝ] E`, built from the scalar symbols by two `ContinuousLinearMap.smulRightL`s so linearity and continuity in both slots hold **by construction** — no `mk₂`, no bilinearity proof. `christoffel_eq_christoffelB` bridges, and `contMDiffAt_christoffelB` carries `contMDiffAt_christoffelCoord` across two fixed CLMs. Gotchas: the `simps` lemma is `smulRightL_apply_apply` (not `_apply`); `ContinuousLinearMap.sum_apply`/`.smul_apply`/`if_pos` are all deprecated (→ `sum_apply`, `smul_apply`); `LinearMap.coe_toContinuousLinearMap'` is the applied form; **`ContMDiff` unfolds to `∀ x, ContMDiffAt`**, so `hL.comp_contMDiffAt` resolves to `Function.comp_contMDiffAt` and fails — use `ContMDiffAt.comp y (hL _) h`; and the nested-CLM section needs `set_option maxSynthPendingDepth 3`. **Geodesics exist** (`exists_isGeodesicOn`, `exists_isGeodesicOn'`). `christoffelChart` is `Γ̃ = christoffelB ∘ (extChartAt I x₀).symm`, and `contDiffAt_christoffelChart` is **where `[I.Boundaryless]` enters and the only place it does**: the inverse chart is smooth on `range I`, which is everything only when `range I = univ`, so the composite is `ContMDiffAt` and hence ordinary `ContDiffAt` — for a model with corners the chart target is not open in `E` and `ContDiffAt` is the wrong predicate. `geodesicField z = (z.2, −Γ̃(z.1)(z.2)(z.2))` is the first-order system, `C^k` by `ContDiffAt.clm_apply` twice, and `exists_solution_geodesicField` is mathlib's `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀` — **no Lipschitz estimate is done here**, `IsPicardLindelof.of_contDiffAt_one` does it. The transport back sets `c = (extChartAt I x₀).symm ∘ p` and shrinks the interval so that `p` stays in the (open, by boundarylessness) chart target and `c` in the frame's `U`; then every manifold-side hypothesis of `covAlong_velocity_eq_zero_iff` is read off the solution — `c` differentiable because the inverse chart is, and `MDiffAlongAt c (velocity c)` because `mdiffAlongAt_iff_of_mem` turns it into differentiability of the fibre coordinate, which **is** `(z ·).2`. **The initial condition is one equation in the total space** (`⟨c 0, velocity c 0⟩ = ⟨x₀, v₀⟩`), which packages `c 0 = x₀` and `c'(0) = v₀` with no dependent-type cast; it follows from `e.toPartialHomeomorph.injOn` plus `e.coe_fst`. Gotchas: mathlib has **no** `HasDerivAt.fst`/`.snd` — use `(ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt`; `DifferentiableAt.congr_of_eventuallyEq` takes the equality in the **goal's** direction, not `.symm`; and after `e.toPartialHomeomorph.injOn` the goal prints with `↑e.toPartialHomeomorph`, so `e.coe_fst` will not `rw` until a `show` restates it at `⇑e`. `exists_frame_on_open` was generalised from `C¹` to any `n : ℕ∞` (one extra `ContMDiffVectorBundle n` binder) so that `exists_isGeodesicOn'` needs no frame data. **Geodesics are unique** (`eventuallyEq_of_isGeodesic`, `eventuallyEq_of_isGeodesic'`): the same identification run backwards — `hasDerivAt_geodesicField_of_isGeodesic` says a geodesic *solves* the system in the chart — plus mathlib's `ODE_solution_unique_of_eventually`, with the Lipschitz constant from `ContDiffAt.exists_lipschitzOnWith`. **The hypotheses are the ones the equation already needs**: ODE uniqueness wants `p'` *differentiable*, not merely `p''` to have a value, and the chart coordinate of the velocity **is** `p'`, so `MDiffAlongAt c (velocity c)` — already required for `D/dt γ'` to mean anything — is exactly that. No extra regularity. Gotchas: `congrArg TotalSpace.proj hinit` extracts the base equality from a total-space initial condition, but `simp only [hinit]` alone will not close `z₁ t₀ = z₂ t₀` (it rewrites the fibre term and leaves the base), so split with `Prod.ext` and a `show`; and the `∀ᶠ`-hypotheses have to be *nested* (`eventually_eventually_nhds.mpr`) before `filter_upwards`, since the per-point lemma itself takes `∀ᶠ` hypotheses |
| `RicciIdentity.lean` | **proved**: **the Ricci identity for a bilinear form field** — `(∇²_{W,X}h)(Y,Z) − (∇²_{X,W}h)(Y,Z) = −h(R(W,X)Y,Z) − h(Y,R(W,X)Z)` (`cov2Bilin_sub_swap`). Commuting the two derivatives costs **one curvature term per slot of `h`**: none for a function (`hessianFun_symm`), one for a section (`hessian_sub_hessian_swap`), two here. This is the commutation rule roadmap item 3 needs — with `h = −2Ric`, turning `∇²Ric` into `Δ Rm + Q` is a matter of moving derivatives past each other. **All the content is in one expansion**, `cov2Bilin_eq_hessianFun`: `∇²h` is the Hessian of the *scalar* `h(Y,Z)` plus terms that are either `∇h` in one slot or `h` applied to a second derivative of a field — and **the first derivative of the scalar cancels** between the leading term and the `∇_{∇_W X}` correction, which is why no first-order term survives. Antisymmetrising then kills the Hessian (a function's is symmetric — torsion-freeness, first use), cancels the `∇h` and cross terms outright, and leaves `h(∇_{[W,X]}Y − ∇_W∇_X Y + ∇_X∇_W Y, Z)` = `−h(R(W,X)Y,Z)` (torsion-freeness, second use). **Gotchas, all the `E` vs `TangentSpace` family and worth reading before the next file of this kind**: `rw` with an `E`-stated `map_sub` will not match a `TangentSpace`-typed `-`, **and a type ascription `(v : E)` does not fix it** — the ascribed term still carries the `TangentSpace` instance and prints identically. The fix that works is to state the whole step over `E`-typed *variables* — `∀ a b c d : E, a - b = c → h x a d - h x b d = h x c d` — prove it there by `rw`, and apply it with `exact`/`_`, which unifies up to defeq. Also: `mvfderiv_fun_sub` returns an equation of *CLMs*, so the applied form needs a trailing `rfl` (`simp only [sub_apply]` fails on the same transparency issue); and `omit [CompleteSpace E]` fails on anything mentioning `curvature`, which references the instance. **And the same identity one level up is proved too** — **the Ricci identity for the curvature tensor** (`cov2Curvature_sub_swap`): `(∇²_{X,Y}Rm)(A,B)C − (∇²_{Y,X}Rm)(A,B)C = R(X,Y)(Rm(A,B)C) − Rm(R(X,Y)A,B)C − Rm(A,R(X,Y)B)C − Rm(A,B)(R(X,Y)C)`, **one curvature term per slot — three inputs and the vector output**. This is what lets the *differentiated* second Bianchi identity be antisymmetrised. The expansion `cov2Curvature_eq_hessian` is the bilinear one one level up (`∇²Rm` against `hessian` of the *section* `Rm(A,B)C`, same first-derivative cancellation) and needs **no regularity of the connection at all**: the only splitting is `∇` over a difference of sections, which is an axiom, where the bilinear case had to differentiate a scalar. Antisymmetrising, the `∇Rm` terms cancel because each appears in both orders and the cross terms `Rm(∇_YA,∇_XB)C` because the swap maps the pair to itself; the output term is `hessian_sub_hessian_swap`, and the three input terms are one lemma each (`curvature_fst/snd/thd_second_deriv_comm`). **The third slot is the expensive one, as everywhere in this tower**: slots 1–2 combine their four second-derivative terms with additivity plus `TensorialAt.pointwise` on `tensorialAt_curvature_fst`/`_snd`, but slot 3 needs `curvature_add_right` and `curvature_congr_third`, which want `C²` sections and — because that lemma argues through an orthonormal frame — a **metric**, so it lives in its own section with `[T2Space M] [RiemannianBundle …] [IsContMDiffRiemannianBundle I 2 …]`. **Do not reach for `mkHom` here**: `rw [← TensorialAt.mkHom_apply …]` sends the unifier through `FiberBundle.extend` and does not return (the documented `whnf` timeout); additivity + `pointwise` + `linear_combination (norm := module)` does the same job in under a minute |
| `BianchiDeriv.lean` | **proved**: **the differentiated second Bianchi identity** — `(∇²_{X,Y}Rm)(A,B)C + (∇²_{X,A}Rm)(B,Y)C + (∇²_{X,B}Rm)(Y,A)C = 0` (`cov2Curvature_cyclic_eq_zero`), the cyclic identity of `bianchi_second` one derivative up. **Nothing is differentiated twice by hand**: `∇²Rm` is `∇Rm` differentiated once with one correction per slot, so the cyclic sum splits into a leading part and four correction groups, and **all five vanish by the *undifferentiated* identity** — the leading parts combine (additivity of `∇` on sections) into `∇_X` of the section `bianchi_second` says is zero, and each correction group is the cyclic sum with one field replaced by its covariant derivative. So the proof is five `bianchi_second` and one `∇0 = 0`. **The corrections cancel three at a time, not in pairs** — one group per differentiated field. **No metric**: all three Riemannian instances are `omit`ted, exactly as for `bianchi_second`; the trace step is where a metric first becomes unavoidable. Regularity one derivative above `bianchi_second`, last slot still the expensive one (`C` at `C⁴` so `∇_X C` keeps the `C³` the spectator slot wants). **Gotchas**: `IsCovariantDerivativeOn.add` produces a *Pi*-typed `+`, so `rw` will not match it against a lambda-typed one — state the additivity steps in **applied** form (`congrArg (fun L ↦ L (X x))`) and let defeq do the rest; `bianchi_second`'s `x` is implicit and undetermined in a bare `have`, so pass `(x := x)`; `simp only [cov2Curvature]` makes no progress, use `unfold`; and `ContinuousLinearMap.zero_apply` is deprecated (a CI error) → bare `zero_apply` . **The trace is taken too** (`curvatureLaplacian_eq_neg_sum`): summing over `X = Y = eᵢ` puts the first cyclic term on the diagonal, where it *is* `Δ Rm` (`curvatureLaplacian_eq_sum_frame`), leaving `Δ Rm(A,B)C = −∑ᵢ(∇²_{eᵢ,A}Rm)(B,eᵢ)C − ∑ᵢ(∇²_{eᵢ,B}Rm)(eᵢ,A)C`. **This is where the metric enters and the only place so far.** It is also what forces the Ricci identity for `Rm`: in both surviving sums the traced index sits in the **outer derivative slot**, whereas `Divergence.lean` traces the slot `∇Rm` is pointwise in — so the two derivative slots must be swapped by `cov2Curvature_sub_swap`, and *that* swap is what produces the quadratic terms . **The reordering is done too** (`curvatureLaplacian_eq_swapped`), with the quadratic terms named: `curvatureCommutator X Y A B C` is the RHS of the Ricci identity for `Rm`, and `Δ Rm(A,B)C = −∑ᵢ(∇²_{A,eᵢ}Rm)(B,eᵢ)C − ∑ᵢ(∇²_{B,eᵢ}Rm)(eᵢ,A)C − ∑ᵢ C(eᵢ,A;B,eᵢ) − ∑ᵢ C(eᵢ,B;eᵢ,A)`. **This is `∂ₜRm = ΔRm + Q` in outline**: the first two sums are `∇` of a divergence of `Rm` and become `∇²Ric` by the contracted second Bianchi identity; the last two **are** `Q`, quadratic because `curvatureCommutator` is `Rm` applied to `Rm`. **`Q` is not bolted on at the end — it is exactly what reordering the derivative slots costs.** `cov2Curvature_sub_swap'` is the usable form of the Ricci identity: all **twenty-five** differentiability hypotheses of `cov2Curvature_sub_swap` follow from uniform `C³` fields with `C` at `C⁴`, which is what the trace already carries — without it the identity cannot be applied inside a frame sum. Note `BianchiDeriv.lean` imports `RicciIdentity.lean` for this, and `IsContMDiffRiemannianBundle I 2` does synthesise from `I 3` . **Step (iii) is CLOSED** (`inner_curvatureLaplacian_eq`): `⟪Δ Rm(A,B)C, D⟫ = −(∇_A div Rm)(C,D,B) + (∇_B div Rm)(C,D,A) − Q`, with `Q` the two commutator sums and `covDivCurvature` naming `∇_A` of the `(0,3)`-tensor `div Rm(C,D,B) = (∇_C Ric)(D,B) − (∇_D Ric)(C,B)`. **Every term is accounted for**: two second derivatives of `Ric`, two quadratic in `Rm`. The chain is `sum_inner_covCurvature_snd_eq` (pair symmetry puts the traced index back in the output slot, where `divCurvature` lives — needs only a `C²` connection) → `sum_inner_covCurvature_frame_deriv_eq_zero` (the two frame-derivative terms cancel; **pair symmetry again**, putting both into `covCurvatureBilinDir` = `innerSL ∘ covCurvatureEndo`, so `sum_bilin_of_antisymm` applies verbatim — its statement is *already* the symmetrised form) → `sum_inner_cov2Curvature_snd_eq_mvfderiv` (`∇_A` outside the trace, **no curvature term survives**) → `sum_inner_cov2Curvature_snd_eq_covRicci` (the leading term needs the identity as a *function* on the frame's domain, so an `OrthonormalBasis` at each `y` plus `EventuallyEq.mvfderiv_eq`) → **`cov2Curvature_antisymm`** (`∇²Rm` inherits `Rm`'s antisymmetry; each of the five terms flips, and the two corrections in `∇_X A`/`∇_X B` **swap with each other**) → the capstone. Regularity peaks at `C⁴` for all four fields and the frame — pair symmetry wants `C³` in the slot `∇_A eᵢ` occupies. **Gotchas**: `MDifferentiableAt.inner_bundle'` needs its explicit name, dot notation resolving through `ChartedSpace.LiftPropWithinAt`; `mvfderiv_fun_sum` lives in `RicciFlowBlueprint`, not `CovariantDerivative`; and in `cov2Curvature_antisymm` a `show _ = -(…)` leaves the **LHS folded**, so `module` sees `1 = 0` — `unfold cov2Curvature` both sides instead |
| `CurvatureFlow.lean` | **proved**: **the first variation of `Rm` with the commutator pair collapsed** — step (iv) started. `inner_curvatureOfTwoTensor_eq` (in `KoszulSecondDeriv.lean`) pairs `∂ₜRm(X,Y)Z = (∇_XA)(Y,Z) − (∇_YA)(X,Z)` against `W` and applies `inner_covTwoTensor_eq` twice, giving **three antisymmetrised pairs of `∇²h`**; `inner_curvatureOfTwoTensor_eq_curvature` evaluates the first. **The three pairs are not alike, and the whole evolution equation is that asymmetry.** Only the first is antisymmetrised in `∇²h`'s two *derivative* slots, so only it is a commutator: `cov2Bilin_sub_swap` collapses it and it **loses its derivatives entirely**, becoming `h` applied to `Rm` — under the flow (`h = −2Ric`) exactly the terms quadratic in the curvature, i.e. `Q`. The other two antisymmetrise a derivative slot against an *argument* slot, so no commutation rule applies; they keep their derivatives and are what `BianchiDeriv.lean`'s trace step turns into `Δ Rm`. Two uniform hypotheses (`∇h` and `A` differentiable on `C²` fields) replace six pointwise ones. **Gotcha, new and nasty**: inserting a declaration between an `omit [..] in` and the docstring it guards **silently reattaches the omit to the new declaration** — the old one then trips the unused-section-variable linter, which is a CI error. Put a new declaration *before* the `omit`, with its own. **Gotcha**: a hypothesis mentioning `x` placed *before* `{x : M}` in the binder list auto-binds a **fresh** `x`, and the error is an `x` vs `x✝` mismatch far away in the proof — declare `{x : M}` first . **AND ROADMAP ITEM 3 IS CLOSED** (`inner_derivCurvature_eq_curvatureLaplacian_add`): `⟪∂ₜRm(X,Y)Z,W⟫ = ⟪Δ Rm(X,Y)Z,W⟫ + Q₁ + Q₂ + Ric(R(X,Y)Z,W) + Ric(Z,R(X,Y)W)`. **Every term on the right is either `Δ Rm` or quadratic in the curvature, and the two sources of quadratic terms are different**: `Q₁+Q₂` is what reordering the derivative slots of `∇²Rm` cost (the trace step), the two `Ric`-against-`Rm` terms are what commuting the derivative slots of `∇²h` cost (the first variation). Neither is bolted on; **each is a commutator defect**. The join needs one bridge, `covDivCurvature_eq_cov2Bilin`: the trace step speaks `covRicci` and the flow side `cov2Bilin ricciForm`, and the three corrections regroup **not termwise** but one group per differentiated slot. **Then four `∇²Ric` terms cancel in pairs by symmetry of `Ric` alone** — the flow side gives `(∇²_{X,W}Ric)(Y,Z)` where the trace step gives `(∇²_{X,W}Ric)(Z,Y)`; `cov2Bilin_symm` from `ricciForm_symm`, free. **What this is and is not**: it is the identity for the Koszul tensor `A` of `h = −2Ric`. Hooking it to an actual `IsRicciFlowAt` is one further specialisation — `isKoszulOf_derivDifference` plus `innerE_deriv_eq_of_isRicciFlowAt'`, under the two-step `letI`, exactly as `ScalarFlow.lean` did for the scalar equation. **Gotcha**: `ricciForm_symm` takes `hmet`/`htor` and is stated at a point, so `cov2Bilin_symm`'s `∀ y v w` form needs `fun y v w ↦ cov.ricciForm_symm (x := y) hmet htor v w`; and neither bare `smul_apply` nor `ContinuousLinearMap.smul_apply` fires on `((-2 • ricciForm x) v) w` — state the two instances as concrete `rfl` equations |
| `CurvatureEvolution.lean` | **proved**: **`∂ₜRm = Δ Rm + Q` for an actual Ricci flow** — the close of roadmap item 3. `CurvatureFlow.lean` proves the identity for *any* `(1,2)`-tensor `A` Koszul for `h = −2Ric`; here `A = ∂ₜ∇` and `h = ∂ₜg`, so both hypotheses become theorems — `isKoszulOf_derivDifference` (`∂ₜ∇` is Koszul for `∂ₜg`) and `innerE_deriv_eq_of_isRicciFlowAt'` (`∂ₜg = −2Ric`), which also *derives* the `hb`/`hf2`/`hd` differentiability hypotheses from Ricci-side ones by `covBilin_smul_form`. `inner_derivCurvature_eq_curvatureLaplacian_add_of_isRicciFlowAt` is the identity; `hasDerivAt_inner_curvatureE_eq_curvatureLaplacian_add_of_isRicciFlowAt` composes it with `hasDerivAt_curvatureE_covTwoTensor` into a genuine **`HasDerivAt` in `t`**. **The pairing is against the metric frozen at `t₀`** (`innerE (g t₀) x`), so the left-hand side is `∂ₜ` of the `(1,3)`-tensor and no `∂ₜg` term of its own appears — and typing it that way is also what keeps `⟪·,·⟫` off an `E`-valued argument. **Three levels are carried as explicit hypotheses under the `letI`** — `IsContMDiffRiemannianBundle I 3`, `ContMDiffCovariantDerivative … 2` and `… 3` — because `g : ℝ → ContMDiffRiemannianMetric I 2` gives only `I 2` and a `C¹` connection, the same reason `ScalarFlow.lean` carries `hlc2`. **Gotchas**: `ContDiffAt.comp_contMDiffAt` takes its point *implicitly* (passing `x` is an application type mismatch), and `fun y ↦ c * f y` is `(contDiffAt_const.mul contDiffAt_id).comp_contMDiffAt hf` — `ContMDiffAt.mul` on `ℝ` still wants the Lie-group instance it lacks; and pushing the CLM through the `TangentSpace`-typed difference `D₁ − D₂` needs the `map_sub` *stated* at the goal's exact form and closed by `exact map_sub _ _ _`, since `rw [map_sub]` will not match it |
| `ScalarPreservation.lean` | **proved**: **a lower bound on the scalar curvature is preserved by the Ricci flow** (`scalarCurvatureOfMetricAt_ge_of_hasDerivAt`, and `_of_hasDerivAt_scalarFlowRHS` taking the evolution equation as its single hypothesis) — **the first inequality of Hamilton's pinching set `K`, on the manifold**. **It needs no Uhlenbeck trick, and isolating it is what shows where the trick is actually forced**: the tensor principle is applied to a section of a bundle whose *fibre metric* moves with `t`, which is what has to be trivialised; the scalar equation has no fibre, so the only thing moving is `Δ` — and the maximum principle never looks at `Δ` except to ask `Δu ≥ 0` at a spatial minimum, which `laplacianFun_nonneg_of_isLocalMin` gives for **each metric separately**. So `le_of_deriv_ge_at_min` (metric-free) is applied directly and the `letI` lives only inside the proof, one time at a time — **do not reach for `le_of_laplacian`, which fixes one `cov` for all `t` and cannot state this**. The reaction term is nonnegative by `metricTraceE_comp_sharpE_self_nonneg` (in `MetricTrace.lean`): `⟨B,B⟩_g` is a sum of squares over any `g`-orthonormal basis once `B` is symmetric, and `ricciFormOfMetric_symm` supplies that from `RicciSymm.lean`. So `F = 0` and the comparison function is the constant. **Non-vacuity is checked, not asserted**: `hasDerivAt_scalarFlowRHS_of_hasDerivAt_scalarCurvatureAt` proves `scalarFlowRHS` defeq to `ScalarFlow.lean`'s conclusion **by `:= h`** — the two differ only by the `letI`, and a bridge proved by `:= h` is the cheapest way to make such a claim a checked one |
| `TraceCov.lean` | **proved**: **the metric trace commutes with `∇`** (roadmap Next 1, the gate for every Laplacian identity). `mvfderiv_sum_eq_sum_covBilin`: for a metric connection, a bilinear form field `B` and a local orthonormal frame, `X(∑ᵢ B(eᵢ,eᵢ)) = ∑ᵢ (∇_X B)(eᵢ,eᵢ)`; `_of_frame` is the same with the hypotheses read off an `IsOrthonormalFrameOn`. `B` need not be symmetric and the frame need not be parallel: `inner_cov_antisymm` (metric compatibility + locally constant `⟪eᵢ,eⱼ⟫` ⟹ the coefficients `aᵢⱼ = ⟪∇_X eᵢ, eⱼ⟫` are antisymmetric) and `sum_bilin_of_antisymm` (antisymmetric against symmetric is `0`, by `Finset.sum_comm`). `exists_orthonormalBasis_of_isOrthonormalFrameOn` turns a frame into an `OrthonormalBasis` of each fibre. Two Mathlib gaps filled on the way: `Filter.EventuallyEq.mvfderiv_eq` and `mvfderiv_fun_sum`/`mdifferentiableAt_fun_sum` |
| `RicciVariation.lean` | **proved**: `CommutesWithCov` (∂ₜ/∇_X commute on the difference-tensor sections, all fields), `curvatureEndoE` (`v ↦ R(v,X)Y` via `mkHom`, typed on `E` by ascription — an expected type `E →L E` on a bare `mkHom` leaves `?V x =?= E` unsolved), `hasDerivAt_ricciOfMetric` (**∂ₜ Ric = tr ∂ₜ[v ↦ R(v,X)Y]**, any manifold). **`section FlowMetric` — the whole scalar line on a general `M`** (was model-space-only): `ricciFormOfMetric` (`ricciForm` for `leviCivitaConnection`, on global `C²` extensions rather than `constField`) and `ricciFormOfMetric_apply_field`; `innerE_deriv_eq_of_isRicciFlowAt'` (`∂ₜg = −2 Ric`); `scalarCurvatureOfMetricAt` + `scalarCurvatureOfMetricAt_eq_metricTraceE` (`scal = tr_g Ric`); `hasDerivAt_ricciFormOfMetric_apply`/`derivRicciFormOfMetric`/`hasDerivAt_ricciFormOfMetric` (∂ₜ of the Ricci form, coordinatewise then as a CLM via `exists_hasDerivAt_clm₂_of_apply`); `hasDerivAt_scalarCurvatureOfMetricAt` (`∂ₜ R = tr_g Ṙic − ⟨h,Ric⟩`) and `hasDerivAt_scalarCurvatureOfMetricAt_of_isRicciFlowAt` (**∂ₜ R = tr_g Ṙic + 2\|Ric\|²**). `section ModelSpace` keeps the same theorems where `Scalar.lean` first phrased them, needing no extension lemma: `constField`, `ricci_add_right_const`/`ricci_smul_right_const`, `ricciE`, `scalarCurvatureOfMetric'`, `hasDerivAt_scalarCurvatureOfMetric'`, `innerE_deriv_eq_of_isRicciFlowAt`, `hasDerivAt_scalarCurvatureOfMetric'_of_isRicciFlowAt`. Gotcha: after `ext v w` on an `E →L E →L ℝ` the variables are `E`-typed, so `exists_contMDiff_two_extension` needs `(x := x) (show TangentSpace I x from v)` or its `M` is a metavariable. Never `local notation` over a section variable: hygiene hides `E` and everything downstream is silently auto-bound |
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
   corollary, not the theorem — and it is now proved unconditionally on a
   general manifold (`RicciSymm.lean`), both hypotheses of
   `ricci_sub_ricci_swap` having become theorems.
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

## Roadmap (revised 2026-09-07)

**Statement audit against Chow–Liao–Qin**: `notes/hamilton-statement-comparison.md`
(nine divergences, classified). The two class-(c) hazards — vacuity of the test
class, and the junk branch in the sectional quotient — are **closed** (PRs #16–#19).
What remains are class-(b) genuine differences: connectedness absent, conclusion
stops at metric existence (no Killing–Hopf), `ω` vs `∞`, `C²` vs smooth, and
Ricci as a raw section rather than a tensor-bundle element.

The dated diary that used to sit here is condensed; the Lean-level lessons it
carried are now in "Lean gotchas". Chronology, for the record: mathlib bump and
Levi-Civita (09-04), its smoothness and the textbook flow equation (09-04), the
curvature ODE invariants and both abstract maximum principles (09-05/06), the
second-derivative test (model space, then manifold), the variations of the
connection, curvature, metric trace, Ricci and scalar curvature (09-05/06),
second Bianchi (09-05), the principles on a manifold and CI hardening (09-06).

**Scooped, 2026-08-21.** Chow–Liao–Qin, `arXiv:2608.21502`, "A Lean
Formalization of Hamilton's Three-Manifold Theorem". Repo
`github.com/qinz1yang/differential-geometry`, tag `arxiv-v1-preview`,
Apache-2.0, **1.9M lines of Lean, zero `sorry`, zero project axioms** (audited
locally 2026-09-06). Top-level `hamilton_positive_ricci` takes exactly
`isClosedThreeManifold` + `admitsPositiveRicci` and concludes
`admitsConstantPositiveSectionalCurvature ∧ isSphericalSpaceForm`; the
definitions are honest. They also have short-time existence (DeTurck +
spectral/Galerkin), forward uniqueness, maximal continuation, Shi, Uhlenbeck,
both maximum principles, F- and W-entropy with the cutoff argument, Perelman
κ-noncollapsing, and Cheeger–Gromov–Hamilton compactness. **Both analytic gaps
this project had flagged as blocking are closed in the literature.**

Do not race them on parabolic PDE. They have a 266:1 line advantage and Bennett
Chow. Race where their library is empty.

**What their repo does NOT contain** (grepped, 2026-09-06): `Real.log` anywhere
in `Preservation/` — so **no Hamilton–Ivey**; no reduced volume, no `L`-length,
no `L`-geodesics; no κ-*solutions* (their `kappa` is all noncollapsing) and no
canonical *neighborhoods* (their `canonical` is all Moser-iteration constants);
no surgery, no solitons, no finite extinction, no harmonic map flow, no
curve-shrinking flow, no cut locus, no Toponogov. They do have `Geometry/
Exponential`, `Comparison/Volume`, `Comparison/Variation`, Jacobi fields,
Bishop, index form, injectivity radius — the substrate `L`-geometry needs, and
which this repo has none of.

**Also found: the blueprint chart was missing Hamilton–Ivey entirely.** It is
the fifth correction to the chart and a load-bearing one: without it no blow-up
limit is ever known to have non-negative curvature, so `def:kappa-solution`'s
standing hypothesis is never verified for anything that actually arises.
Now `thm:hamilton-ivey` at the head of `chap:kappa`, with a
`State of the art, September 2026` section in the Overview.

**Next, in order.**
1. **Hamilton–Ivey** — **the ODE half is done** (`IsCurvatureODE.hamiltonIvey`,
   no auxiliary hypotheses: ordering + `ν(0) ≥ -1` ⟹ `R ≥ (-ν)(log(-ν) - 3)`
   wherever `ν < 0`). Source is Cao–Zhu Thm 2.4.1, whose LaTeX is on arXiv
   (`math/0612069`, grep `Hamilton-Ivey Curvature Pinching`).
   **The key simplification, which the literature does not state:** Cao–Zhu's
   two boundary cases are *the same inequality* — case (ii)'s hypothesis
   `λ = -μ + N(L-2)` is case (i)'s `λ+μ = N(L-2)` — and eliminating `L` leaves
   the same polynomial `iveyE = N(λ²+μ²) + N³ + λμ(λ+μ+N)`, nonnegative under
   the ordering alone (`iveyE_nonneg`; two sign cases, the `μ<0` one via
   `iveyE = (λ²+λμ+μ²)(N+μ) + N³ - μ³`). So the boundary argument becomes a
   linear Grönwall: with `Ψ = R - f(-ν)` and `N = -ν`,
   `Ψ' = iveyE/N - Ψ(N²+λμ)/N` identically (`field_simp; ring`, the `log N`
   terms cancel), so `nonneg_of_mul_le_deriv` applies directly
   (`iveyPsi_nonneg`). `hamiltonIvey_boundary_of_nonneg`/`_of_neg` are the
   literature's form and are now redundant; kept for the correspondence.
   `ν < 0` on all of `[0,t]` is free: `nonneg_preserved` (`ν̇ ≥ λν` under the
   ordering) plus `shift`/`restrict` (time translation of `IsCurvatureODE`)
   give `neg_of_neg`.
   **Left:** ~~(a) `f⁻¹` on `[-e²,∞)` and its concavity~~ — **closed, and it was
   never needed**: `IveyConvex.lean` shows the disjunction cutting out `K` is a
   single inequality against `iveyG n = f(max(-n, e²))`, which is convex because
   `f` is convex and increasing on `[e²,∞)` and `n ↦ max(-n,e²)` is convex and
   lands there. `K` is closed and convex (`convex_iveyPinchedSet`,
   `isClosed_iveyPinchedSet`), which is exactly what `thm:max-tensor` consumes.
   Invariance of `K` under the ODE is also packaged in that language
   (`IsCurvatureODE.isIveyPinched`, `IsCurvatureODE.mem_iveyPinchedSet`), so
   **both** things `thm:max-tensor` asks about `K` are proved.
   **Item 3 below is now closed**, so the equation the principle is applied to
   exists. **And the first of `K`'s inequalities is already proved on the
   manifold** (`ScalarPreservation.lean`): a lower bound on `R` is preserved,
   with **no Uhlenbeck trick** — the scalar equation has no fibre, so a moving
   `Δ` costs nothing (see that file's row). What the trick is actually needed
   for is the *tensor* inequalities, where the bundle's fibre metric moves. (b) the time-dependent `K_t` form of
   `thm:max-tensor` is needed only for Hamilton 1999's `log(1+t)` improvement,
   not for the basic estimate; an earlier version of this list said otherwise.
   Watch out: `Real.log (-n) = Real.log n` is a simp lemma
   (`Real.log_neg_eq_log`), so `simpa [iveyF]` rewrites under you — use a
   `calc` with `rfl`, or `set L := Real.log (-n t)` before `field_simp`.
2. ~~**The manifold trace lemma** `X(tr_g B) = tr_g(∇_X B)`~~ — **done**,
   `TraceCov.lean`, exactly along the sketch that used to sit here (no parallel
   frame; antisymmetric coefficients against a symmetric bracket). **Next on
   this line:** the *contraction* itself. `div Rm` now **exists** and the
   **first contraction is proved** (`Divergence.lean`,
   `divCurvature_eq_covRicci_sub`) **and so is the second**
   (`two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt`: `2 div Ric = d scal`).
   **Roadmap item 2 is closed.** What is left on this line is
   `tr_g Ṙic = Δ scal` under the flow, and hence `∂ₜ scal = Δ scal + 2|Ric|²`.
   `RicciVariation.lean` now has `∂ₜ R = tr_g Ṙic + 2|Ric|²` **on a general
   manifold** (`hasDerivAt_scalarCurvatureOfMetricAt_of_isRicciFlowAt`), so
   `tr_g Ṙic = Δ R` was the only missing piece, on no restricted `M` — and it
   is now proved (`ScalarFlow.lean`), so the whole line is closed.
   **The derivation, and why it is a `∇²h` problem.** With
   `⟪Ȧ(X,Y),Z⟫ = ½[(∇_Xh)(Y,Z) + (∇_Yh)(Z,X) − (∇_Zh)(X,Y)]`
   (`inner_derivDifferenceE_eq`) and `∂ₜRm(X,Y)Z = (∇_XȦ)(Y,Z) − (∇_YȦ)(X,Z)`,
   tracing twice gives, with **no** curvature terms,
   `tr_g ∂ₜRic = div div h − Δ(tr_g h)`: the first trace contributes
   `div div h − ½Δ tr h`, the second `½Δ tr h`. Under the flow `h = −2Ric`, so
   `tr h = −2R` and `div div h = −2 div div Ric = −ΔR` by the second contraction
   (`2 div Ric = d scal`), giving `2ΔR − ΔR = ΔR`. **So everything needed is
   `∇²h` for a bilinear form `h` and its two traces** — `∇h` is done
   (`BilinDeriv.lean`), so are `∇²h` and `Δ_g h` (`BilinLaplacian.lean`), and so
   is `div div h` (`OneForm.lean`) — which turned out **not** to need the
   four-linear packaging of `∇²h` at all: it factors as `div(div h)`, `div h`
   being the 1&2 trace of `∇h` and `div` of a one-form needing no frame argument.
   The two forms of `div div h` are also identified: `divDivBilin_eq_sum` says
   the iterated divergence **is** the double trace `∑_{j,i}(∇²_{eⱼ,eᵢ}h)(eᵢ,eⱼ)`
   that the flow produces, by "the divergence commutes with `∇`".
   **The geometric half of the identity is now proved too**:
   `KoszulSecondDeriv.lean`'s `inner_covTwoTensor_eq` says that differentiating
   the Koszul combination gives the same combination with `∇h` replaced by
   `∇²h` and **no curvature terms**, so `∂ₜRm` becomes a statement about `∇²h`
   alone. **The double trace is proved too** (`sum_inner_covTwoTensor_eq`): for
   symmetric `h`, `∑_{i,j}⟪Rm_A(eᵢ,eⱼ)eⱼ,eᵢ⟫ = div div h − tr_g(Δ_g h)`, with
   no curvature terms anywhere. **So the whole geometric side is done.** What
   is left is the *analytic* plumbing: instantiate `IsKoszulOf` at `A = ∂ₜ∇`
   ~~from `inner_derivDifferenceE_eq`~~ — **done** (`FlowKoszul.lean`:
   `isKoszulOf_derivDifference`, and `hasDerivAt_curvatureE_covTwoTensor`
   delivering `∂ₜRm` as `Rm_A`). What is left is to identify `∑_{i,j}⟪Rm_A…⟫`
   with `tr_g(∂ₜRic)` — **done** (`metricTraceE_derivRicciFormOfMetric_eq_sub`:
   `tr_g(∂ₜRic) = div div h − tr_g(Δ_g h)` for the actual flow) — and
   ~~`tr_g(Δ_g h) = Δ(tr_g h)`~~ — **done** (`laplacianFun_traceBilin_eq`).
   That needed no new packaging of `hessianFun`: `∇²f` **is** `∇` of the
   one-form `df` (`hessianFun_eq_covOneForm`, `rfl`), so `OneForm.lean`'s
   frame-argument-free `covOneFormAt` already is the packaging. And
   **`div div Ric = ½ Δ scal` is done too** (`ScalarEvolution.lean`). What is
   the specialisation `h = −2Ric` is **done** too
   (`sum_cov2Bilin_neg_two_ricciForm_eq`): `tr_g(∂ₜRic) = Δ scal`. **Roadmap
   item 2 is fully closed.** Composing it with
   `hasDerivAt_scalarCurvatureOfMetricAt_of_isRicciFlowAt` gives
   **`∂ₜ scal = Δ scal + 2|Ric|²`** on a general manifold — **done**
   (`ScalarFlow.lean`: `metricTraceE_derivRicciFormOfMetric_eq_laplacian`, then
   `hasDerivAt_scalarCurvatureOfMetricAt_eq_laplacian_add`). **This is the first
   evolution equation of the flow formalised here in full.** The composition was
   bookkeeping, but not free: every hypothesis has to be written under a
   *two-step* `letI` (the `RiemannianBundle` **and**
   `ContMDiffCovariantDerivative (leviCivitaOfMetric (g t₀)) 1`), because
   `ricciForm`/`scalarCurvatureAt`/`divBilinOneForm` need the instance and a
   hypothesis-position `letI` supplies only what it names; and level `2` of that
   instance is carried as an explicit hypothesis, a `C²` metric giving only a
   `C¹` connection.
3. **`∂ₜ Rm = Δ Rm + Q`** — **CLOSED** (`CurvatureFlow.lean`,
   `inner_derivCurvature_eq_curvatureLaplacian_add`):
   `⟪∂ₜRm(X,Y)Z,W⟫ = ⟪Δ Rm(X,Y)Z,W⟫ + Q₁ + Q₂ + Ric(R(X,Y)Z,W) + Ric(Z,R(X,Y)W)`,
   for the Koszul tensor of `h = −2Ric`. **Every term on the right is either
   `Δ Rm` or quadratic in the curvature.** The two sources of quadratic terms are
   different and both are commutator defects: `Q₁+Q₂` from reordering the
   derivative slots of `∇²Rm`, the `Ric`-against-`Rm` terms from commuting those
   of `∇²h`. **The flow specialisation is done too** (`CurvatureEvolution.lean`,
   `inner_derivCurvature_eq_curvatureLaplacian_add_of_isRicciFlowAt` and its
   `HasDerivAt` form): `isKoszulOf_derivDifference` +
   `innerE_deriv_eq_of_isRicciFlowAt'` under the two-step `letI`, the same
   bookkeeping `ScalarFlow.lean` did for the scalar equation, plus three level
   hypotheses (`IsContMDiffRiemannianBundle I 3` and the connection at `2` and
   `3`) that a `C²` metric cannot supply. **So the line is closed end to end, and
   what is left on the Hamilton–Ivey road is item (4)'s Uhlenbeck trick, not the
   equation.** The record of how it was built follows.
   It was the single gate for both (1) and (2), with **both sides existing on a
   general manifold** and **both commutation bricks in** (`RicciIdentity.lean`). **What the remaining work
   decomposes into**, in order: (i) ~~the Ricci identity for `∇²h`~~ — **done**;
   (ii) ~~the same for `∇²Rm`~~ — **done** (`cov2Curvature_sub_swap`: one
   curvature term per slot, three inputs and the vector output), which is what
   lets the *differentiated* second Bianchi identity be antisymmetrised;
   (iii) the trace of that against the metric, turning `∇²Ric` into `ΔRm` plus
   quadratic terms; (iv) the substitution `h = −2Ric` into
   `inner_covTwoTensor_eq` and the bookkeeping to land on `Q`. **Step (iii) is
   the bulk and is started**: its first brick, the **differentiated second
   Bianchi identity**, is proved (`BianchiDeriv.lean`,
   `cov2Curvature_cyclic_eq_zero`) and — like `bianchi_second` itself — **needs
   no metric**. **The shape of what remains**: summing that identity over
   `Y = eᵢ` with `X = eᵢ` gives `Δ Rm(A,B)C` as minus two traces of `∇²Rm`
   whose derivative slots are in the *wrong* order; `cov2Curvature_sub_swap`
   reorders them at the cost of terms quadratic in `Rm`; and the reordered
   traces are `∇` of a divergence, which `divCurvature_eq_covRicci_sub` turns
   into `∇²Ric`. So the remaining work is the frame bookkeeping, and it runs on
   the same orthonormal-frame machinery `TraceCov.lean` and `Divergence.lean`
   use. The metric enters here and only here.
   *Geometry side*: `Δ Rm` is built (`CurvatureLaplacian.lean`), on top of
   `∇Rm` being tensorial **and pointwise** in all four slots
   (`CurvatureDeriv.lean`, `Divergence.lean`) — so `∇Rm` and `∇²Rm` are genuine
   tensors, not operators on fields.
   *Analytic side*: **`∂ₜ Rm` is NOT model-space-only.** Do not re-scope this
   wrongly: `hasDerivAt_curvatureE_leviCivitaOfMetric` (`CurvatureVariation.lean`,
   `section Metric`) is stated for a general `M`, as is `hasDerivAt_ricciOfMetric`
   (`RicciVariation.lean`, `section Ricci`). What *is* model-space-only is the
   **scalar** curvature variation, and that is model-space-only **no longer**:
   `RicciVariation.lean`'s `section FlowMetric` has `ricciFormOfMetric`,
   `scalarCurvatureOfMetricAt` and `∂ₜ R = tr_g Ṙic + 2|Ric|²` on a general
   `M`. `section ModelSpace` keeps the `constField` phrasing as the same
   theorems where `Scalar.lean` first stated them.
   **So what is left here is not a port but an identification.** `∂ₜ Rm` is
   currently delivered as `(∇_X Ȧ)(Y,Z) − (∇_Y Ȧ)(X,Z)` with `Ȧ = ∂ₜ∇` the
   derivative of the difference tensor; under the flow (`h = −2 Ric`) that has
   to be shown equal to `Δ Rm + Q(Rm)`. That is the standard several-page
   computation, and it is the real remaining work on this line.
4. **Perelman's `L`-geometry** (`def:reduced-volume`,
   `thm:reduced-volume-monotone`). The deepest genuinely-open node and the one
   everything downstream of `chap:kappa` consumes. Pure comparison geometry +
   ODE, no parabolic theory — but it needs an exponential-map / Jacobi-field /
   second-variation substrate this repo does not have and theirs does.
   **Decided 2026-09-08: build it ourselves.** The reason is not licensing
   (theirs is Apache-2.0 and `NOTICE.md` already sets the vendoring precedent)
   and not pride — it is that **`L`-geometry does not consume Riemannian
   comparison geometry off the shelf; it redoes it.** `L`-geodesics,
   `L`-Jacobi fields, the `L`-index form and the `L`-exponential map are their
   own objects with their own ODEs and their own second-variation formula.
   Bishop, Toponogov and the injectivity radius — the parts of their
   `Comparison/` that look most valuable — are largely *not* what
   `thm:reduced-volume-monotone` needs. So the reusable surface is much
   narrower than 1.9M lines suggests, while the costs (their mathlib pin
   against our post-#36845 requirement, their build time, their breakage) are
   not. **Build narrowly**: the exponential map, the Jacobi equation as an ODE,
   and enough second-variation scaffolding to imitate on the `L`-side. If a
   specific file turns out to be worth taking, vendor it narrowly with
   attribution as `GramSchmidtOrtho.lean` does — do not take a dependency.
   **Survey, 2026-09-08 — the first brick is NOT `exp`.** Mathlib
   `Geometry/Manifold/` has no geodesics, no pullback connection, no
   Christoffel symbols and no covariant derivative along a curve;
   `CovariantDerivative.toFun` acts only on **global sections over `M`**
   (`(Π x : M, V x) → (Π x : M, T_xM →L V x)`), and its whole API — including
   `IsCovariantDerivativeOn`'s two axioms `add`/`leibniz` — is phrased there.
   It does have Picard–Lindelöf (`Analysis/ODE/`). So the missing primitive is
   **`D/dt` along a curve**, the pullback connection on `γ*TM`: without it one
   cannot even *state* `∇_{γ'}γ' = 0`, parallel transport, the Jacobi equation,
   or the first/second variation of length — let alone their `L`-analogues.
   **Design**: mirror mathlib's own `IsCovariantDerivativeOn` →
   `CovariantDerivative` split. A predicate `IsCovDerivAlong cov γ D` with
   three axioms — additive; Leibniz over `f : ℝ → ℝ` with `deriv f`; and
   agreement with `cov` on restrictions of global sections,
   `D (W ∘ γ) t = cov W (γ t) (γ' t)` — then uniqueness, then existence via
   charts (the difference tensor against a chart-flat connection is the
   Christoffel tensor, and `Variation.lean`'s `differenceE` already builds
   exactly that comparison). A section along `γ` is a lift of `γ` to `TM`, so
   its regularity is ordinary `MDifferentiableAt` into the total space — no
   new bundle structure needed. **Do not do this model-space-first**: the repo
   paid for that once with `∂ₜ scal`, which sat `M = E`-only and then cost a
   full port.
   **Started 2026-09-08** (`CovariantAlongCurve.lean`): `velocity`,
   `MDiffAlongAt`, the predicate `IsCovDerivAlong` with those three axioms,
   `zero`, and **locality** (`congr_of_eventuallyEq`) — `D` depends on a section
   only through its germ, by the bump argument, not by fiat — **and uniqueness**
   (`eq_of_isCovDerivAlong`), via `exists_frame_expansion`. **No metric was
   needed**: an earlier plan reached for `OrthonormalFrame.lean` and
   coefficients `⟪V u, Eᵢ(γ u)⟫`, but a plain trivialisation gives the frame
   (`Trivialization.localFrame`) *and* the coefficients (`b.repr (e ⟨γ u,V u⟩).2`)
   *and* their differentiability, all from the same total-space criterion.
   **Existence is proved too** (`isCovDerivAlong_covAlong`), and it needed **no
   Christoffel symbols and no chart-flat connection**: the classical
   trivialisation formula `∑ᵢ(cᵢ'Wᵢ + cᵢ∇_{γ'}Wᵢ)` is enough, because `cov`'s
   own Leibniz rule on the local frame expansion `W = ∑ᵢaᵢWᵢ` *is* the
   `restrict` axiom. An earlier plan here called for `Variation.lean`'s
   `differenceE` against a chart-flat connection; that was more machinery than
   the job takes. **Geodesics are stated** (`IsGeodesicOn`) and, crucially,
   *non-vacuously*: `isGeodesicOn_iff_forall` says `∇_{γ'}γ' = 0` is equivalent
   to vanishing under every operator satisfying the axioms, forward by
   uniqueness and **backward by existence** — without the latter the quantified
   form is vacuously true, the repo's worst class of error. **`Γ` is built and
   is `C^k`** (`christoffelCoord`, `contMDiffAt_christoffelCoord`), so the
   coordinate equation `D/dt V = c' + Γ(γ)(γ')(c)` is available with the
   regularity Picard–Lindelöf wants.
   **That identification is now done** (`GeodesicODE.lean`): the tangent-bundle
   trivialisation *is* the chart (a `rfl`), and with `p t := extChartAt I x₀ (γ t)`
   the coordinate of `γ'(t)` is `p'(t)`
   (`deriv_extChartAt_comp_eq_trivializationAt`, `coeffAlong_velocity_eq`). The
   chart-side manoeuvre was mathlib's own, from `IntegralCurve/Basic.lean` —
   look there first for anything of this shape, it saved most of the work.
   **The equation is assembled too** (`covAlong_velocity_eq_zero_iff`):
   `∇_{γ'}γ' = 0 ↔ p'' = −Γ(γt)(γ')(p')`, an ODE on an open subset of `E`. The
   vector form `trivializationAt_covAlong_eq` was the right level to work at —
   going componentwise through `b.repr` first was a detour; `sum_deriv_repr_smul`
   eliminates the basis in one line.
   **Picard–Lindelöf is started.** The entry point is mathlib's
   `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` — a `C¹`
   vector field on a normed space admits an integral curve — so **no Lipschitz
   estimate has to be done by hand**; `IsPicardLindelof.of_contDiffAt_one` does
   it. `Γ` is packaged as the bilinear `christoffelB` with its regularity
   (`contMDiffAt_christoffelB`).
   **The chart transport is done and so is Picard–Lindelöf**
   (`christoffelChart`, `contDiffAt_christoffelChart`, `geodesicField`,
   `exists_solution_geodesicField`), and **geodesics exist**:
   `exists_isGeodesicOn` and, with the frame supplied by `exists_frame_on_open`
   (now stated at any regularity, not only `C¹`), the frame-free
   `exists_isGeodesicOn'` — through every point in every direction there is a
   geodesic on an interval about `0`, with the initial condition stated as one
   equation in `TM` so that no dependent-type cast appears. **`[I.Boundaryless]`
   enters exactly once**, in `contDiffAt_christoffelChart`: the chart target has
   to be open in `E` for `ContDiffAt` to be the right predicate. **No Lipschitz
   estimate is done by hand** — `IsPicardLindelof.of_contDiffAt_one` does it.
   **Uniqueness is proved too** (`eventuallyEq_of_isGeodesic`,
   `eventuallyEq_of_isGeodesic'`), on `hasDerivAt_geodesicField_of_isGeodesic`
   (a geodesic *solves* the system in the chart) plus
   `ODE_solution_unique_of_eventually` — and it needs **no hypotheses beyond
   the ones the geodesic equation already carries**, because ODE uniqueness
   wants `p'` differentiable and the chart coordinate of the velocity *is*
   `p'`. **Affine reparametrisation is proved too** (`Exponential.lean`:
   `velocity_comp_mul`, `covAlong_velocity_comp_mul_eq_zero`,
   `isGeodesicOn_comp_mul`) and cost almost nothing — in the chart the equation
   is `p'' = −Γ̃(p)(p')(p')`, reparametrising multiplies the left by `a²`, and
   `Γ̃` is bilinear by construction; **no case split on `a = 0`** and **no
   boundarylessness**. **Interval uniqueness is proved too**
   (`forall_totalSpace_eq_of_isGeodesicOn`, `eqOn_of_isGeodesicOn`) — the clopen
   argument, with closedness taken in two Hausdorff pieces because mathlib has
   no `T2Space` on a bundle's total space. **And `exp` is built**
   (`IsGeodesicRun`, `expMap`, `expMap_eq`, `expMap_smul_eq`, `expMap_zero`) —
   the first object of the comparison-geometry substrate, well defined rather
   than chosen, with homogeneity `exp_x(a v) = γ_v(a)` from reparametrisation.
   **Left on this line**: regularity of `exp` — and this is **not** a
   manifold-side computation. Mathlib has **no smooth dependence of ODE
   solutions on initial conditions** (checked 2026-09-09; its local flow is
   built by `choose` behind a `dite` and is not even continuous as constructed),
   only Lipschitz and continuous dependence. So `d exp_0 = id`, parallel
   transport and Jacobi fields all sit behind a genuine ODE-theory gap; see
   "Where the real gaps are".


**Upstream candidates** (Mathlib-general, no dependence on the curvature
stack unless noted): `VectorField.lieBracket_apply_fun`; `neg_apply`,
`sub_apply`, `mdiffAt_cov_apply`, `contMDiff_cov_apply` (`C^k` connection ⇒
`C^k` covariant derivative); `mlieBracket_sub_left'`;
`exists_hasDerivAt_clm_of_apply` (coordinatewise ⇒ CLM-valued derivative);
`Filter.EventuallyEq.mvfderiv_eq`, `mvfderiv_fun_sum` and
`mdifferentiableAt_fun_sum` (Mathlib has `mvfderiv_fun_add` but no germ-congruence
and no finite-sum rule; its `MDifferentiableAt.sum` is stated for `ι : Type`, not
`Type*`);
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

Read this list as *gaps in Mathlib and in this repo*. Since 2026-08-21 the
parabolic and Cheeger–Gromov entries are no longer gaps **in the literature** —
Chow–Liao–Qin closed both — but nothing of theirs is in Mathlib, and nothing of
theirs is imported here.

- **Levi-Civita existence is NOT needed to define the flow** — the per-slice
  `∀ t, ∃ cov` is equivalent to the textbook equation, now as a theorem
  (`isRicciFlowOn_iff_ricciOfMetric`, using smoothness of the connection from
  `LeviCivitaSmooth.lean`). Both formulations are kept; the existential one is
  what elaborates under `letI`.
- **Three distinct parabolic theories** are on the road, not one: Ricci flow,
  harmonic map flow (uniqueness of the standard solution), curve-shrinking flow
  (finite extinction). Chow–Liao–Qin have the first; the other two are open
  everywhere.
- **Second independent analytic gap:** Cheeger–Gromov compactness. Mathlib has
  Gromov–Hausdorff for compact metric spaces; pointed smooth convergence of
  manifolds under curvature bounds does not exist. Chow–Liao–Qin built it
  (`Geometry/Compactness/CheegerGromov`), so it is done but not upstreamed.
- **No comparison-geometry substrate here at all** — no exponential map, no
  Jacobi fields, no second variation, no index form, no injectivity radius, no
  cut locus. Perelman's `L`-geometry (Next 4) cannot start without it. This is
  the deciding fact in build-versus-import.
- Mathlib has **no maximal-solution ODE theory** — hence germ uniqueness in
  `Homogeneous.lean`.
- **Uhlenbeck's trick is gated by the SAME mathlib gap as the `L`-geometry line.**
  Checked 2026-09-11, `Analysis/ODE/`: there are six files and **no linear-ODE
  theory at all**, no global existence, and no dependence-on-parameters theorem.
  Every existence result in `ExistUnique.lean` is *local* (on a closed ball, on a
  small interval); the rest is uniqueness. Uhlenbeck's trick needs
  `∂ₜι(t,x) = Ric_{g_t}(x) ∘ ι(t,x)` solved on all of `[0,T]` **and** `C^k` in
  `x`, since the pulled-back curvature has to be a differentiable section.
  *Continuous* dependence on `x` is in fact reachable without new theory — fold
  the parameter into the state as a coordinate with `ẋ = 0` and use
  `..._lipschitzOnWith` / `..._continuousOn`, which are dependence on the
  **initial condition** — but `C^k` dependence is not, and `C^k` is what the
  trick needs. So roadmap items 1 and 4 have one common gate, and it is an
  ODE-theory contribution, not a geometry one.
  **The alternative worth costing before attempting it**: Hamilton 1982 §9
  applies the tensor maximum principle on a bundle whose fibre metric *moves*,
  with the metric's time derivative appearing explicitly. That avoids the trick
  entirely at the cost of generalising `TensorMaximumPrinciple.lean`. The scalar
  analogue of that trade is already settled in this repo's favour —
  `ScalarPreservation.lean` shows a moving `Δ` costs nothing when the principle
  only inspects the operator at an extremum.
- **Mathlib has no *smooth dependence* of ODE solutions on initial conditions.**
  Checked 2026-09-09, `Analysis/ODE/ExistUnique.lean`: the local flow
  `ContDiffAt.exists_eventually_eq_hasDerivAt` is built by `choose` behind a
  `dite`, so as constructed it is not even continuous in the initial point; what
  *is* available is Lipschitz and continuous dependence
  (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`,
  `..._continuousOn`). **This is now the gate on the `L`-geometry line**:
  `expMap` is built and well defined (`Exponential.lean`), but nothing yet says
  it is continuous, let alone `C^k`, and `d exp_0 = id` and Jacobi fields both
  need that. Closing it is a mathlib-level contribution — the variational
  equation, or a Banach fixed point in a `C^k` space — not a manifold-side
  computation, and it should be scoped as such before being attempted.
- ~~No global `C²` extension of a tangent vector.~~ **Closed 2026-09-07**
  (`GlobalExtension.lean`, PR #16). It was the worst hazard in the repo, not
  merely a gap: `Hamilton.lean`'s predicates quantify over globally `C²`
  fields, so on an `M` carrying no such nonvanishing field they were
  *vacuously true* and `hamilton_1982` was trivially provable and asserted
  nothing. `forall_contMDiff_iff_forall_tangent` is the bridge; the
  predicates are now also stated pointwise
  (`hasPositiveRicciLC_iff_tangent`, `hasConstSecLC_iff_mul`).
- ~~Ricci is not a pointwise bilinear form; the scalar curvature is
  model-space only.~~ Closed the same day by `RicciForm.lean`, on top of the
  extension and of `CurvaturePointwise.lean`'s pointwise third slot: `Ric` is
  a continuous bilinear form (`ricciForm`) and `scal` a genuine metric trace
  (`scalarCurvatureAt`) on any manifold, with frame-independence free.
  ~~**Still model-space only:** `∂ₜ R`.~~ **Closed 2026-09-08**
  (`RicciVariation.lean`, `section FlowMetric`): `ricciFormOfMetric`,
  `innerE_deriv_eq_of_isRicciFlowAt'` (`∂ₜg = −2 Ric`),
  `scalarCurvatureOfMetricAt` (= `tr_g` of the Ricci form),
  `hasDerivAt_ricciFormOfMetric`, and `∂ₜ R = tr_g Ṙic − ⟨h,Ric⟩` with its flow
  corollary `∂ₜ R = tr_g Ṙic + 2|Ric|²`, all on a general manifold. The
  `constField` versions in `section ModelSpace` are kept as the same theorems
  where they were first phrased.
- ~~The metric trace does not yet commute with `∇` on the manifold.~~ Closed
  2026-09-07 by `TraceCov.lean` (PR #20), and the *contraction* is closed too:
  **both** contractions of the second Bianchi identity are proved
  (`Divergence.lean`), so `div Rm(Y,Z,W) = (∇_Y Ric)(Z,W) − (∇_Z Ric)(Y,W)` and
  `2 div Ric = d scal`.
- ~~`∇Rm` is only an operator on fields, and there is no `Δ Rm`.~~ **Closed
  2026-09-08.** `∇Rm` is tensorial and pointwise in all four slots
  (`CurvatureDeriv.lean`, `Divergence.lean`), `∇²Rm` likewise in both derivative
  slots, and `Δ Rm` is the trace of the resulting bilinear map
  (`CurvatureLaplacian.lean`). The Bochner identity for the rough Laplacian is
  proved too (`Bochner.lean`). **What is left on the evolution line is the
  identification `∂ₜ Rm = Δ Rm + Q`** — a computation, not a port; see Next 3.

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
- `real_inner_comm x y` orients the *other* way than reading suggests: `rw` with
  it hunts for the pattern you were trying to produce. State the swap as a
  `have e : ⟪a, b⟫ = ⟪b, a⟫ := real_inner_comm _ _` and rewrite with `e`.
- `refine ⟨fun i j ↦ e, …⟩` leaves the later goals beta-unreduced, so `rw`
  fails on `(fun i j => e) i j`; put a `show` first.
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
