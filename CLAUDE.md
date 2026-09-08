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
| `Divergence.lean` | **proved**: **`div Rm` exists.** `covCurvature_congr_dir` — `(∇_X Rm)(Y,Z)W` at `x` depends only on `X x`, and this needs **no new frame argument**: each of the four terms is separately pointwise in `X` (the first is a CLM at `X x`; the middle two are `Rm` in a tensorial slot via mathlib's `TensorialAt.pointwise` on `tensorialAt_curvature_fst`/`_snd`; the last is `curvature_congr_third`). With direction-slot linearity that gives `covCurvatureAt` (on `exists_contMDiff_two_extension`, as `ricciAt` is) and the endomorphism `covCurvatureEndo`; `divCurvature` is its **endomorphism** trace — no metric, unlike `scal`, which is a *metric* trace of a bilinear form. So `divCurvature_eq_sum_basis` (frame-independence) is just `LinearMap.trace_eq_sum_inner`, and `divCurvature_eq_sum_frame` reads it off any `C²` frame orthonormal at `x`. Also **`divCurvature_eq_sub_sum`** — the **traced second Bianchi identity**: `div Rm(Y,Z,W) = ∑ᵢ⟪(∇_Y Rm)(eᵢ,Z)W,eᵢ⟫ − ∑ᵢ⟪(∇_Z Rm)(eᵢ,Y)W,eᵢ⟫`, by pairing `bianchi_second` with `eᵢ` and turning the middle term round with `covCurvature_antisymm`. No derivative of the frame appears — the identity is pointwise in `eᵢ` and only summed. Note `omit [CompleteSpace E]` fails on it (`bianchi_second` references the instance). **`sum_inner_covCurvature_eq`** closes the gap that left: `∑ᵢ⟪(∇_X Rm)(eᵢ,Z)W,eᵢ⟫ = (∇_X Ric)(Z,W)` (`covRicci`), the first-slot trace commuting with `∇`. Same mechanism as `TraceCov.lean` — the frame is not parallel, so `⟪∇_X eᵢ, eⱼ⟫` appears and `inner_cov_antisymm` + `sum_bilin_of_antisymm` kill it — but the bilinear form has to be *produced*: `curvatureBilinFst = (innerSL ℝ).comp (mkHom …)`, available only because `Rm` is tensorial in its first slot. Hence **`divCurvature_eq_covRicci_sub`**: `div Rm(Y,Z,W) = (∇_Y Ric)(Z,W) − (∇_Z Ric)(Y,W)`, the **contracted second Bianchi identity, first contraction**. Both connection hypotheses are used and for different things — torsion-freeness for `bianchi_second`, metric compatibility for the trace. **`two_mul_sum_covRicci_eq_mvfderiv_scalarCurvatureAt`** is the **second contraction**, `2 div Ric = d scal`: sum the first contraction over `Z = W = eⱼ`; on the right `TraceCov` gives `Y(scal)` and `covRicci_symm` (from `ricci_symm`) gives `div Ric(Y)`, on the left pair symmetry of `∇Rm` plus `sum_inner_covCurvature_eq` gives `div Ric(Y)` again. **Pair symmetry of `∇Rm` is not inherited for free**: `inner_curvature_pair_symm` is about the `(0,4)` tensor, while `covCurvature` is an operator on fields. `inner_covCurvature_expand` bridges them — for a *metric* connection `∇_X` moves onto the pairing, so `⟪(∇_X Rm)(A,B)C,D⟫` is `X⟪Rm(A,B)C,D⟫` minus **five** corrections, one per slot plus the metric one `⟪Rm(A,B)C,∇_X D⟫` — and the two sides' corrections are the same five numbers reordered. Frame must be `C³` there so `∇_X eᵢ` is `C²`. **Typing gotcha, load-bearing**: `sum_bilin_of_antisymm` wants `B : E →L[ℝ] E →L[ℝ] ℝ`, so `curvatureBilinFst` must be *declared* at that type (body ascribed through `TangentSpace I x →L …`) — declared at the `TangentSpace` type it is defeq but every later `rw` fails with "did not find the pattern" on a goal that prints identically. Also `innerSL_apply_apply`, not `innerSL_apply`; and `mkHom_apply` is reached by `show`, not `simp only`. Gotchas: `open scoped Classical in` for the `dite`, and it goes **before** the docstring like `omit`; `simp only [d, h, and_self, ↓reduceDIte]` then `rfl` (naming `LinearMap.coe_mk` trips the unused-simp-arg linter, which is a CI error) |
| `MetricTrace.lean` | **proved**: `sharpE` (`g♯⁻¹ ∘ B♭`), `metricTraceE` (`tr(g♯⁻¹ B♭)`), `metricTraceE_eq_sum` (= `∑ᵢ B(eᵢ,eᵢ)` over any `g`-orthonormal basis, via `LinearMap.trace_eq_sum_inner`), `sharpE_apply_eq_sum`, `metricTraceE_comp_sharpE_eq_sum` (`⟨h,B⟩_g`), `hasDerivAt_inverse_innerE` (`∂ₜ g⁻¹ = −g⁻¹ h g⁻¹`, from `contDiffAt_map_inverse` plus differentiating `g ∘ g⁻¹ = id`), `hasDerivAt_metricTraceE` (**`∂ₜ tr_{g_t} B_t = tr Ḃ − ⟨h,B⟩`**). All at a point on `E`. `metricTraceE_innerE_comp`, `ricci_eq_metricTraceE` bridge to `ricci` |
| `RicciForm.lean` | **proved**: **Ricci as an honest bilinear form and the scalar curvature on a general manifold**. `ricciAt_add_left`/`_smul_left`/`_add_right`/`_smul_right` (each field-level law applied to global `C²` extensions), `ricciForm x : E →L[ℝ] E →L[ℝ] ℝ` (`LinearMap.mk₂` + `toContinuousLinearMap` twice), `ricciForm_apply_field`; `scalarCurvatureAt` and `scalarCurvatureAt_eq_sum_basis` — **frame-independence is free** once `Ric` is bilinear (`OrthonormalBasis.sum_apply_self_eq`), so `scalarCurvatureWith_congr'` discharges the `h3` that `Scalar.lean` had to assume; `mvfderiv_scalarCurvatureAt_eq_sum_covBilin` = **`X(scal) = tr_g(∇_X Ric)`**, the trace lemma applied to `ricciForm` |
| `RicciSymm.lean` | **proved**: **Ricci is symmetric on a general manifold** for a metric torsion-free connection, with no hypotheses. `extendTwo`/`contMDiff_extendTwo`/`extendTwo_apply_self` (a *named* global `C²` extension — the anonymous `Exists.choose` of two vectors prints identically and `rw` cannot target one), `curvatureEndoAt` (the `hL` of `ricci_sub_ricci_swap`, now constructed: well-definedness from `curvature_congr_third`, linearity from `curvature_add_right`/`curvature_smul_const_right`), `trace_curvatureEndoAt_eq_zero` (skew-adjointness, via `LinearMap.trace_eq_sum_inner`), `ricci_symm`, `ricciAt_symm`, `ricciForm_symm`. Both hypotheses of `ricci_sub_ricci_swap` are now theorems |
| `CurvatureSymm.lean` | **proved**: **pair symmetry of the Riemann tensor** on a general manifold, `⟪R(X,Y)Z,W⟫ = ⟪R(Z,W)X,Y⟫` (`inner_curvature_pair_symm`) — the octahedron argument, four copies of first Bianchi linked by the two antisymmetries, closed by `linarith` in the six unknowns. `inner_bianchi_first` (first Bianchi paired against a vector; the fourth slot needs *no* regularity, the identity being a vector identity), `inner_curvature_left_skew`. This is what makes `R` an operator on `Λ²T_xM` — the form Hamilton's pinching and Uhlenbeck's trick need — and what the second contraction of second Bianchi will use |
| `ConstantCurvature.lean` | **proved**: **constant sectional curvature determines the whole `(0,4)` tensor** — `⟪R(X,Y)Z,W⟫ = k(⟪Y,Z⟫⟪X,W⟫ − ⟪X,Z⟫⟪Y,W⟫)` (`inner_curvature_eq_of_const_sec`, and `_norm` for the `‖·‖` form `hasConstSecLC_iff_mul` produces). `curvatureDefect` = `Rm − k·(model)`, with its four symmetries and four additivity laws; polarising slots 1&4 gives `T(A,B,B,C) = 0`, polarising 2&3 gives antisymmetry there, and a tensor antisymmetric in three consecutive slots is killed by first Bianchi (`3T = 0`). **Not a parity fix — a strengthening.** Their `admitsConstantPositiveSectionalCurvature` is the multiplied-out *sectional* identity `Rm(X,Y,Y,X) = c(g(X,X)g(Y,Y) − g(X,Y)²)`, which `hasConstSecLC_iff_mul` already matched; divergence 2 in `notes/hamilton-statement-comparison.md` was closed before this. What this adds is that the sectional identity determines the *whole* `(0,4)` tensor, so everything downstream of constant curvature can use `Rm` directly. Corollaries by tracing once and twice: `ricci_eq_of_const_sec` (`Ric = (n−1)k g`) and `scalarCurvatureAt_eq_of_const_sec` (`scal = n(n−1)k`), both over an arbitrary orthonormal basis with `n = Fintype.card ι`, so no `finrank` identification is needed |
| `IveyConvex.lean` | **proved**: **Hamilton's pinching set is closed and convex** — the input `thm:max-tensor` needs to carry Hamilton–Ivey from the ODE to the flow, and roadmap blocker (a). **`f⁻¹` is not needed and was never needed**: the disjunction in `IsIveyPinched` collapses to one inequality against `iveyG n = iveyF (max (-n) (e²))` (`isIveyPinched_iff_iveyG`), because `f` increases on `[e²,∞)` so the `-ν ≤ e²` branch gives `G = f(e²) = -e² ≤ -3`, which the *first* condition already supplies. `monotoneOn_iveyF`, `convexOn_iveyF` (via `MonotoneOn.convexOn_of_deriv` — `f' = log x − 2` is monotone), `convexOn_max_neg_exp_two`, `image_max_neg_exp_two`, `convexOn_iveyG` (`ConvexOn.comp`), `continuous_iveyG`; `iveyPinchedSet : Set (EuclideanSpace ℝ (Fin 3))` with `convex_iveyPinchedSet` and `isClosed_iveyPinchedSet` |
| `TraceCov.lean` | **proved**: **the metric trace commutes with `∇`** (roadmap Next 1, the gate for every Laplacian identity). `mvfderiv_sum_eq_sum_covBilin`: for a metric connection, a bilinear form field `B` and a local orthonormal frame, `X(∑ᵢ B(eᵢ,eᵢ)) = ∑ᵢ (∇_X B)(eᵢ,eᵢ)`; `_of_frame` is the same with the hypotheses read off an `IsOrthonormalFrameOn`. `B` need not be symmetric and the frame need not be parallel: `inner_cov_antisymm` (metric compatibility + locally constant `⟪eᵢ,eⱼ⟫` ⟹ the coefficients `aᵢⱼ = ⟪∇_X eᵢ, eⱼ⟫` are antisymmetric) and `sum_bilin_of_antisymm` (antisymmetric against symmetric is `0`, by `Finset.sum_comm`). `exists_orthonormalBasis_of_isOrthonormalFrameOn` turns a frame into an `OrthonormalBasis` of each fibre. Two Mathlib gaps filled on the way: `Filter.EventuallyEq.mvfderiv_eq` and `mvfderiv_fun_sum`/`mdifferentiableAt_fun_sum` |
| `RicciVariation.lean` | **proved**: `CommutesWithCov` (∂ₜ/∇_X commute on the difference-tensor sections, all fields), `curvatureEndoE` (`v ↦ R(v,X)Y` via `mkHom`, typed on `E` by ascription — an expected type `E →L E` on a bare `mkHom` leaves `?V x =?= E` unsolved), `hasDerivAt_ricciOfMetric` (**∂ₜ Ric = tr ∂ₜ[v ↦ R(v,X)Y]**, any manifold). Model space: `constField`, `ricci_add_right_const`/`ricci_smul_right_const` (second slot on constant fields), `ricciE` (Ricci form as `E →L E →L ℝ` via `LinearMap.mk₂`), `scalarCurvatureOfMetric'` (= `Scalar.lean`'s), `hasDerivAt_scalarCurvatureOfMetric'` (`∂ₜ R = tr_g Ṙic − ⟨h,Ric⟩`), `innerE_deriv_eq_of_isRicciFlowAt` (`h = −2 Ric` from the flow by uniqueness), `hasDerivAt_scalarCurvatureOfMetric'_of_isRicciFlowAt` (**∂ₜ R = tr_g Ṙic + 2\|Ric\|²**). Never `local notation` over a section variable: hygiene hides `E` and everything downstream is silently auto-bound |
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
   **What is actually left is item 3 below** — `∂ₜ Rm = Δ Rm + Q`, the equation
   the principle is applied to. (b) the time-dependent `K_t` form of
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
   `tr_g Ṙic = Δ scal` under the flow, and hence `∂ₜ scal = Δ scal + 2|Ric|²`;
   `RicciVariation.lean` already has `∂ₜ R = tr_g Ṙic + 2|Ric|²`, so only
   `tr_g Ṙic = Δ R` is missing.
3. **`∂ₜ Rm = Δ Rm + Q`** (Uhlenbeck's trick) — **now the single gate**, for
   both (1) and (2): the Hamilton–Ivey transport needs the flow written in the
   form `thm:max-tensor` consumes, and `∂ₜ scal = Δ scal + 2|Ric|²` needs the
   contraction of the same identity. Everything else either side of it is done.
   The prerequisite `∇Rm` **as a tensor** is largely built: `CurvatureDeriv.lean`
   has `C^∞(M)`-linearity in **all four slots**, plus pointwise dependence on
   the direction slot, which together give `div Rm` (`Divergence.lean`). Left
   on that line: pointwise dependence in the *other three* slots, which is what
   would make `∇Rm` a section of a tensor bundle rather than an operator on
   fields. `div Rm` does not need it.
4. **Perelman's `L`-geometry** (`def:reduced-volume`,
   `thm:reduced-volume-monotone`). The deepest genuinely-open node and the one
   everything downstream of `chap:kappa` consumes. Pure comparison geometry +
   ODE, no parabolic theory — but it needs an exponential-map / Jacobi-field /
   second-variation substrate this repo does not have and theirs does.
   Decide before starting whether to build it or to build on their library.


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
  **Still model-space only:** `∂ₜ R` (`RicciVariation.lean`), stated through
  `ricciE`/`scalarCurvatureOfMetric'` and not yet ported to
  `ricciForm`/`scalarCurvatureAt`.
- ~~The metric trace does not yet commute with `∇` on the manifold.~~ Closed
  2026-09-07 by `TraceCov.lean` (PR #20). What still waits is the
  *contraction*: rewriting the traced second Bianchi identity as `ΔR`, and
  the analogous step for `Δ Rm`.

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
