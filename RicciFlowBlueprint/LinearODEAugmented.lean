/-
**The augmented system, and second-order dependence on a parameter.**

`LinearODE.lean` proves that the fundamental solution `Φ(x,t)` of `Φ' = A(x,t) ∘ Φ` is once
differentiable in the parameter `x`, with derivative `D_xΦ = ∑ₙ Jₙ` solving the *variational
equation* `∂ₜ(D_xΦ) = (D_xA ·) ∘ Φ + A ∘ (D_xΦ)`.  That file's own docstring says what the next
step is: the pair `(Φ, D_xΦ)` solves a **linear** system, so `C^k` should follow from the `C¹`
theorem applied to that system, with no second-order differentiation under the integral sign.

This file does it.  The system is
`∂ₜ(u, v) = (A ∘ u, A ∘ v + (·∘u) ∘ A')`
on `G := (F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))`, block-triangular: the first component is the
original equation and does not see `v`.  Its coefficient `augOp` is again a bounded operator
family, continuous in `t`, and — this is the point — it is a fixed **continuous linear** function
`augCLM` of the pair `(A, A')`.  So differentiating it in the parameter is the chain rule through
a CLM, and `LinearODE.lean`'s `C¹` theorem applies to it verbatim.

Two things are proved:

* `dysonSum_augOp_apply_one_zero` — the identification. `Φ_aug(x,t)(1,0) = (Φ(x,t), D_xΦ(x,t))`,
  by uniqueness for the augmented equation: both sides solve it and agree at `t = 0`.  This is
  the whole content; everything else is bookkeeping.
* `hasFDerivAt_dysonDerivSum` — `D_xΦ` is itself differentiable in `x`, i.e. **`Φ` is twice
  differentiable in the parameter**, which is the `k = 2` case the roadmap is gated on.

**The induction to general `k` is in `LinearODESmooth.lean`**, which iterates exactly this
construction. The one obstruction worth recording is a Lean one, not a mathematical one: the
induction replaces `F` by `G` at each step, and `G` lives in universe `max u_F u_H`, so a naive
induction would have to produce statements in a *growing* universe, which `Nat.rec` cannot do.
Constraining `F` and `H` to one universe (`max u u = u`) fixes it and costs nothing at the
application site.
-/
import RicciFlowBlueprint.LinearODE

namespace RicciFlowBlueprint

open ContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

set_option maxSynthPendingDepth 3

section Aug

/-- The coefficient of the augmented system at a fixed pair `(a, a')`:
`(u, v) ↦ (a ∘ u, a ∘ v + (· ∘ u) ∘ a')`.

Built from `compL`, `prod`, `fst` and `snd`, so linearity and continuity in `(u,v)` hold **by
construction** — the `christoffelB` lesson, and the reason there is no `mk₂` and no boundedness
estimate here. The order of the two summands in the second component is Mathlib's, matching
`hasDerivAt_dysonDerivSum` verbatim. -/
noncomputable def augField (a : F →L[ℝ] F) (a' : H →L[ℝ] (F →L[ℝ] F)) :
    ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ] ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) :=
  ((compL ℝ F F F a).comp (fst ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F)))).prod
    ((compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F) (compL ℝ F F F a)).comp
        (snd ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F)))
      + (((compL ℝ H (F →L[ℝ] F) (F →L[ℝ] F)).flip a').comp ((compL ℝ F F F).flip)).comp
        (fst ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F))))

omit [CompleteSpace F] in
@[simp] theorem augField_apply (a : F →L[ℝ] F) (a' : H →L[ℝ] (F →L[ℝ] F))
    (z : (F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) :
    augField a a' z = (a.comp z.1, (compL ℝ F F F a).comp z.2 + ((compL ℝ F F F).flip z.1).comp a')
    := rfl

omit [CompleteSpace F] in
/-- `‖augField a a'‖ ≤ ‖a‖ + ‖a'‖`.  The two summands of the second component are exactly the
two shapes `LinearODE.lean` already estimates for the iterate recursion, so the bound is those
two lemmas plus `‖z.1‖, ‖z.2‖ ≤ ‖z‖`. -/
theorem norm_augField_le (a : F →L[ℝ] F) (a' : H →L[ℝ] (F →L[ℝ] F)) :
    ‖augField a a'‖ ≤ ‖a‖ + ‖a'‖ := by
  refine opNorm_le_bound _ (by positivity) fun z ↦ ?_
  have h1 : ‖z.1‖ ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : ‖z.2‖ ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  rw [augField_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · have := opNorm_comp_le a z.1
    nlinarith [norm_nonneg a, norm_nonneg a', norm_nonneg z.1]
  · refine (norm_add_le _ _).trans ?_
    have hb1 := norm_compL_comp_le (H := H) a z.2
    have hb2 := norm_compL_flip_comp_le (H := H) z.1 a'
    nlinarith [norm_nonneg a, norm_nonneg a', norm_nonneg z.1, norm_nonneg z.2]

/-- **The coefficient of the augmented system is a continuous LINEAR function of the pair
`(A, A')`.**

This is the design point of the file.  Differentiating `augOp` in the parameter is then the
chain rule through a fixed CLM — one line — rather than a product rule reproved by hand, and
that is what makes `LinearODE.lean`'s `C¹` theorem apply to the augmented system without any
new differentiation-under-the-integral argument. -/
noncomputable def augCLM :
    ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ]
      (((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ] ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))) :=
  LinearMap.mkContinuous
    { toFun := fun w ↦ augField w.1 w.2
      map_add' := by
        intro w w'
        refine ContinuousLinearMap.ext fun z ↦ Prod.ext ?_ ?_
        · simp [augField_apply, add_comp]
        · simp only [augField_apply, add_apply, Prod.fst_add, Prod.snd_add, map_add, add_comp,
            comp_add]
          abel
      map_smul' := by
        intro c w
        refine ContinuousLinearMap.ext fun z ↦ Prod.ext ?_ ?_
        · simp [augField_apply, smul_comp]
        · simp only [augField_apply, smul_apply, Prod.smul_fst, Prod.smul_snd, map_smul,
            smul_comp, comp_smul, RingHom.id_apply]
          rw [smul_add] }
    2 (by
      intro w
      refine (norm_augField_le w.1 w.2).trans ?_
      have h1 : ‖w.1‖ ≤ ‖w‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      have h2 : ‖w.2‖ ≤ ‖w‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      linarith)

omit [CompleteSpace F] in
@[simp] theorem augCLM_apply (a : F →L[ℝ] F) (a' : H →L[ℝ] (F →L[ℝ] F)) :
    augCLM (a, a') = augField a a' := rfl

omit [CompleteSpace F] in
theorem norm_augCLM_le : ‖(augCLM : ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ] _)‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

end Aug

section Identification

variable {A : H → ℝ → (F →L[ℝ] F)} {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} {C C' : ℝ}

/-- The coefficient of the augmented system along the parameter `x`. -/
noncomputable def augOp (A : H → ℝ → (F →L[ℝ] F)) (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F)))
    (x : H) (s : ℝ) :
    ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ] ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) :=
  augField (A x s) (A' x s)

omit [CompleteSpace F] in
theorem augOp_apply (x : H) (s : ℝ) (z : (F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) :
    augOp A A' x s z =
      ((A x s).comp z.1,
        (compL ℝ F F F (A x s)).comp z.2 + ((compL ℝ F F F).flip z.1).comp (A' x s)) := rfl

omit [CompleteSpace F] in
/-- Continuity in `t` is the chain rule for continuity through `augCLM` --- nothing to prove. -/
theorem continuous_augOp {x : H} (hA : Continuous (A x)) (hA' : Continuous (A' x)) :
    Continuous (augOp A A' x) :=
  augCLM.continuous.comp (hA.prodMk hA')

omit [CompleteSpace F] in
theorem norm_augOp_le {x : H} (hC : ∀ s, ‖A x s‖ ≤ C) (hC' : ∀ s, ‖A' x s‖ ≤ C') (s : ℝ) :
    ‖augOp A A' x s‖ ≤ C + C' :=
  (norm_augField_le _ _).trans (add_le_add (hC s) (hC' s))

-- BENCH: dyson-augmented-identification
/-- **The identification.**  The fundamental solution of the augmented system, applied to the
initial datum `(1, 0)`, is the pair `(Φ, D_xΦ)`.

This is the whole content of the file; everything else is bookkeeping.  Both sides solve
`ẇ = augOp(x,t) w` --- the left by `hasDerivAt_dysonSum_apply`, the right by
`hasDerivAt_dysonSum` and `hasDerivAt_dysonDerivSum` paired, whose two values are *literally*
the two components of `augField` --- and both are `(1, 0)` at `t = 0`.  Uniqueness for a linear
equation with bounded coefficient (`eq_of_hasDerivAt_linear`) does the rest.

The point is that the right-hand side is thereby exhibited as a Dyson sum **in its own right**,
so every theorem `LinearODE.lean` proves about Dyson sums now applies to `D_xΦ` as well. -/
theorem dysonSum_augOp_apply (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (x : H) (t : ℝ) :
    dysonSum (augOp A A' x) t ((1 : F →L[ℝ] F), (0 : H →L[ℝ] (F →L[ℝ] F)))
      = (dysonSum (A x) t, dysonDerivSum A A' x t) := by
  have hcont : Continuous (augOp A A' x) := continuous_augOp (hA x) (hA' x)
  have hbd : ∀ s, ‖augOp A A' x s‖ ≤ C + C' :=
    fun s ↦ norm_augOp_le (fun r ↦ hC x r) (fun r ↦ hC' x r) s
  have hg : ∀ u : ℝ, HasDerivAt (fun r ↦ (dysonSum (A x) r, dysonDerivSum A A' x r))
      (augOp A A' x u (dysonSum (A x) u, dysonDerivSum A A' x u)) u := fun u ↦
    (hasDerivAt_dysonSum (hA x) (fun r ↦ hC x r) u).prodMk
      (hasDerivAt_dysonDerivSum hA hA' hC hC' x u)
  have hf : ∀ u : ℝ,
      HasDerivAt (fun r ↦ dysonSum (augOp A A' x) r
        ((1 : F →L[ℝ] F), (0 : H →L[ℝ] (F →L[ℝ] F))))
        (augOp A A' x u (dysonSum (augOp A A' x) u
          ((1 : F →L[ℝ] F), (0 : H →L[ℝ] (F →L[ℝ] F))))) u :=
    fun u ↦ hasDerivAt_dysonSum_apply hcont hbd _ u
  exact congrFun (eq_of_hasDerivAt_linear (t₀ := 0) hbd hf hg (by simp)) t

end Identification

section Second

variable {A : H → ℝ → (F →L[ℝ] F)} {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))}
  {A'' : H → ℝ → (H →L[ℝ] (H →L[ℝ] (F →L[ℝ] F)))} {C C' C'' : ℝ}

omit [CompleteSpace F] in
/-- `p.prod q` as a sum of two fixed CLMs applied to `p` and `q` --- which is what makes it
visibly continuous in the pair. -/
theorem prod_eq_inl_comp_add_inr_comp (p : H →L[ℝ] (F →L[ℝ] F))
    (q : H →L[ℝ] (H →L[ℝ] (F →L[ℝ] F))) :
    p.prod q = (inl ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F))).comp p
      + (inr ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F))).comp q := by
  ext h <;> simp

/-- The parameter derivative of the augmented coefficient.  Because `augOp` is `augCLM` applied
to `(A, A')`, this is the chain rule through a CLM and nothing else. -/
noncomputable def augOpDeriv (A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F)))
    (A'' : H → ℝ → (H →L[ℝ] (H →L[ℝ] (F →L[ℝ] F)))) (x : H) (s : ℝ) :
    H →L[ℝ]
      (((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ] ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))) :=
  augCLM.comp ((A' x s).prod (A'' x s))

omit [CompleteSpace F] in
theorem hasFDerivAt_augOp (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x)
    (hderiv2 : ∀ x s, HasFDerivAt (fun y ↦ A' y s) (A'' x s) x) (x : H) (s : ℝ) :
    HasFDerivAt (fun y ↦ augOp A A' y s) (augOpDeriv A' A'' x s) x := by
  have h := (augCLM (F := F) (H := H)).hasFDerivAt.comp x
    ((hderiv x s).prodMk (hderiv2 x s))
  exact h

omit [CompleteSpace F] in
/-- Continuity of `s ↦ (p s).prod (q s)`, through the `inl`/`inr` decomposition.  Mathlib bundles
`prod` as a linear isometry only in shapes that do not fit here, and the decomposition costs two
lines. -/
theorem continuous_prod_clm {X : Type*} [TopologicalSpace X]
    {p : X → (H →L[ℝ] (F →L[ℝ] F))} {q : X → (H →L[ℝ] (H →L[ℝ] (F →L[ℝ] F)))}
    (hp : Continuous p) (hq : Continuous q) :
    Continuous fun s ↦ (p s).prod (q s) := by
  have h1 : Continuous fun s ↦
      (compL ℝ H (F →L[ℝ] F) ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
        (inl ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F)))) (p s) :=
    (compL ℝ H (F →L[ℝ] F) ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
      (inl ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F)))).continuous.comp hp
  have h2 : Continuous fun s ↦
      (compL ℝ H (H →L[ℝ] (F →L[ℝ] F)) ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
        (inr ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F)))) (q s) :=
    (compL ℝ H (H →L[ℝ] (F →L[ℝ] F)) ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
      (inr ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F)))).continuous.comp hq
  refine (h1.add h2).congr fun s ↦ ?_
  rw [prod_eq_inl_comp_add_inr_comp]
  rfl

omit [CompleteSpace F] in
theorem continuous_augOpDeriv {x : H} (hA' : Continuous (A' x)) (hA'' : Continuous (A'' x)) :
    Continuous (augOpDeriv A' A'' x) := by
  have h : Continuous fun s ↦
      (compL ℝ H ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
        (((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ]
          ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))) augCLM) ((A' x s).prod (A'' x s)) :=
    (compL ℝ H ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
      (((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ]
        ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))) augCLM).continuous.comp
      (continuous_prod_clm hA' hA'')
  exact h

omit [CompleteSpace F] in
theorem norm_augOpDeriv_le (x : H) (hC' : ∀ s, ‖A' x s‖ ≤ C') (hC'' : ∀ s, ‖A'' x s‖ ≤ C'')
    (s : ℝ) : ‖augOpDeriv A' A'' x s‖ ≤ 2 * (C' + C'') := by
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) (hC' 0)
  have hC''0 : 0 ≤ C'' := le_trans (norm_nonneg _) (hC'' 0)
  refine (opNorm_comp_le _ _).trans ?_
  have h1 : ‖(A' x s).prod (A'' x s)‖ ≤ C' + C'' := by
    refine opNorm_le_bound _ (by linarith) fun h ↦ ?_
    rw [prod_apply, Prod.norm_def]
    refine max_le ?_ ?_
    · exact ((A' x s).le_opNorm h).trans
        (by nlinarith [norm_nonneg h, hC' s, norm_nonneg (A' x s)])
    · exact ((A'' x s).le_opNorm h).trans
        (by nlinarith [norm_nonneg h, hC'' s, norm_nonneg (A'' x s)])
  exact mul_le_mul norm_augCLM_le h1 (norm_nonneg _) (by norm_num)

/-- Read `D_xΦ` off a solution operator of the augmented system: evaluate at the initial datum
`(1, 0)` and take the second component.  A CLM, so it commutes with differentiation for free. -/
noncomputable def augRead :
    ((((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F))) →L[ℝ]
        ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))) →L[ℝ] (H →L[ℝ] (F →L[ℝ] F))) :=
  (snd ℝ (F →L[ℝ] F) (H →L[ℝ] (F →L[ℝ] F))).comp
    (ContinuousLinearMap.apply ℝ ((F →L[ℝ] F) × (H →L[ℝ] (F →L[ℝ] F)))
      ((1 : F →L[ℝ] F), (0 : H →L[ℝ] (F →L[ℝ] F))))

-- BENCH: dyson-second-parameter-derivative
/-- **`D_xΦ` is itself differentiable in the parameter** --- i.e. `Φ` is twice differentiable in
the parameter, which is the `k = 2` case the roadmap is gated on.

No new analysis: the identification exhibits `D_xΦ` as a fixed CLM applied to the Dyson sum of
the augmented system, and that Dyson sum is differentiable in the parameter by
`LinearODE.lean`'s `C¹` theorem, whose hypotheses the augmented coefficient satisfies because it
is `augCLM` applied to `(A, A')`. -/
theorem hasFDerivAt_dysonDerivSum
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x)) (hA'' : ∀ x, Continuous (A'' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (hC'' : ∀ x s, ‖A'' x s‖ ≤ C'')
    (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x)
    (hderiv2 : ∀ x s, HasFDerivAt (fun y ↦ A' y s) (A'' x s) x) (t : ℝ) (x : H) :
    HasFDerivAt (fun y ↦ dysonDerivSum A A' y t)
      (augRead.comp (dysonDerivSum (augOp A A') (augOpDeriv A' A'') x t)) x := by
  have hbig := hasFDerivAt_dysonSum (A := augOp A A') (A' := augOpDeriv A' A'')
    (C := C + C') (C' := 2 * (C' + C''))
    (fun y ↦ continuous_augOp (hA y) (hA' y))
    (fun y ↦ continuous_augOpDeriv (hA' y) (hA'' y))
    (fun y s ↦ norm_augOp_le (fun r ↦ hC y r) (fun r ↦ hC' y r) s)
    (fun y s ↦ norm_augOpDeriv_le y (fun r ↦ hC' y r) (fun r ↦ hC'' y r) s)
    (fun y s ↦ hasFDerivAt_augOp hderiv hderiv2 y s) t x
  have hcomp := augRead.hasFDerivAt.comp x hbig
  have heq : ∀ y : H, dysonDerivSum A A' y t = augRead (dysonSum (augOp A A' y) t) := by
    intro y
    show dysonDerivSum A A' y t
      = (dysonSum (augOp A A' y) t ((1 : F →L[ℝ] F), (0 : H →L[ℝ] (F →L[ℝ] F)))).2
    rw [dysonSum_augOp_apply hA hA' hC hC' y t]
  simp only [heq]
  exact hcomp

theorem differentiable_dysonDerivSum
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x)) (hA'' : ∀ x, Continuous (A'' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (hC'' : ∀ x s, ‖A'' x s‖ ≤ C'')
    (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x)
    (hderiv2 : ∀ x s, HasFDerivAt (fun y ↦ A' y s) (A'' x s) x) (t : ℝ) :
    Differentiable ℝ fun y ↦ dysonDerivSum A A' y t := fun x ↦
  (hasFDerivAt_dysonDerivSum hA hA' hA'' hC hC' hC'' hderiv hderiv2 t x).differentiableAt

-- BENCH: dyson-sum-c-one
/-- **`Φ` is `C¹` in the parameter**, not merely differentiable.

`LinearODE.lean` gives differentiability and says nothing about how `D_xΦ` varies; the
continuity that `C¹` asks for comes free from the *second* derivative existing, since a
differentiable map is continuous.  This is the first statement in the repo that puts the
fundamental solution in a `ContDiff` class at all. -/
theorem contDiff_one_dysonSum
    (hA : ∀ x, Continuous (A x)) (hA' : ∀ x, Continuous (A' x)) (hA'' : ∀ x, Continuous (A'' x))
    (hC : ∀ x s, ‖A x s‖ ≤ C) (hC' : ∀ x s, ‖A' x s‖ ≤ C') (hC'' : ∀ x s, ‖A'' x s‖ ≤ C'')
    (hderiv : ∀ x s, HasFDerivAt (fun y ↦ A y s) (A' x s) x)
    (hderiv2 : ∀ x s, HasFDerivAt (fun y ↦ A' y s) (A'' x s) x) (t : ℝ) :
    ContDiff ℝ 1 fun y ↦ dysonSum (A y) t := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨differentiable_dysonSum hA hA' hC hC' hderiv t, ?_⟩
  have hfd : (fderiv ℝ fun y ↦ dysonSum (A y) t) = fun y ↦ dysonDerivSum A A' y t := by
    funext y
    exact (hasFDerivAt_dysonSum hA hA' hC hC' hderiv t y).fderiv
  rw [hfd]
  exact (differentiable_dysonDerivSum hA hA' hA'' hC hC' hC'' hderiv hderiv2 t).continuous

end Second

end RicciFlowBlueprint
