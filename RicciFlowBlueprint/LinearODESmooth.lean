/-
**`C^k` dependence of a linear ODE on a parameter, for every `k`.**

`LinearODEAugmented.lean` builds the augmented system and gets `k = 2` out of it, and records
that the induction to general `k` is blocked by a **Lean** obstruction rather than a
mathematical one: iterating replaces `F` by `G = (F →L F) × (H →L (F →L F))`, which lives in
universe `max u_F u_H`, so a naive induction would ask `Nat.rec` for statements in a *growing*
universe.

This file carries out the induction, by the fix named there: **put `F` and `H` in one
universe**, where `max u u = u` and the state space of the augmented system stays put.  The
constraint costs nothing at the application site — one always applies this to a concrete pair
of spaces — and nothing else about the argument changes.

The second ingredient is a hypothesis class that is *itself* recursive, `IsBddFamily`:
`f` is a bounded `C^{k+1}` family when it is continuous and bounded in `t` and has a parameter
derivative family that is a bounded `C^k` family.  Two facts about it carry the whole file:
it is stable under **post-composition with a fixed continuous linear map**, and under
**pairing** — and the induction step for each of those is the *same lemma at a different
continuous linear map*, because the derivative family of `L ∘ f` is `(compL L) ∘ f'`.  With
those, the augmented coefficient is a bounded `C^k` family for free, since it is `augCLM`
applied to the pair `(A, A')`.

So the induction step is: `Φ` is `C^{k+1}` iff it is differentiable with `C^k` derivative;
its derivative *is* a Dyson sum of the augmented system read through a fixed continuous linear
map (`LinearODEAugmented.lean`'s identification); and that Dyson sum is `C^k` by the induction
hypothesis.  No new analysis appears at any level.
-/
import RicciFlowBlueprint.LinearODEAugmented

universe u

namespace RicciFlowBlueprint

open ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

set_option maxSynthPendingDepth 3

section BddFamily

/-- Continuous in `t` and bounded, both uniformly in the parameter: the level-`0` hypothesis,
and exactly what `LinearODE.lean`'s theorems ask of a coefficient family. -/
structure IsBddCts {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : H → ℝ → W) : Prop where
  /-- Continuity in the time variable, at each parameter. -/
  cts : ∀ x, Continuous (f x)
  /-- A bound uniform in both variables. -/
  bdd : ∃ C : ℝ, ∀ x s, ‖f x s‖ ≤ C

/-- **A bounded `C^k` family.**  Recursive in `k`, and — this is the point — recursive in a way
that changes the *codomain* at each step, from `W` to `H →L[ℝ] W`.  That is why the whole file
needs `W` to range over one universe: the recursion would otherwise climb. -/
def IsBddFamily : (k : ℕ) → {W : Type u} → [NormedAddCommGroup W] → [NormedSpace ℝ W] →
    (H → ℝ → W) → Prop
  | 0, _, _, _, f => IsBddCts f
  | k + 1, W, _, _, f => IsBddCts f ∧
      ∃ f' : H → ℝ → (H →L[ℝ] W), (∀ x s, HasFDerivAt (fun y ↦ f y s) (f' x s) x) ∧
        IsBddFamily k f'

variable {W W' W₁ W₂ : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

theorem IsBddFamily.isBddCts {k : ℕ} {f : H → ℝ → W} (hf : IsBddFamily k f) : IsBddCts f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- One level down.  The only place the recursion is peeled without also using the derivative
family. -/
theorem IsBddFamily.le_succ : ∀ (k : ℕ) {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : H → ℝ → W}, IsBddFamily (k + 1) f → IsBddFamily k f := by
  intro k
  induction k with
  | zero => intro W _ _ f hf; exact hf.1
  | succ k ih =>
      intro W _ _ f hf
      obtain ⟨h0, f', hd, hf'⟩ := hf
      exact ⟨h0, f', hd, ih hf'⟩

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem IsBddCts.comp_clm (L : W →L[ℝ] W') {f : H → ℝ → W} (hf : IsBddCts f) :
    IsBddCts fun x s ↦ L (f x s) where
  cts := fun x ↦ L.continuous.comp (hf.cts x)
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    exact ⟨‖L‖ * C, fun x s ↦ (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hC x s) (norm_nonneg L))⟩

/-- **Stability under post-composition with a fixed continuous linear map.**

The induction step is the *same lemma at a different map*: the parameter derivative family of
`L ∘ f` is `(compL L) ∘ f'`, so one level down the statement to prove is this one with `L`
replaced by `compL ℝ H W W' L`. Nothing is differentiated by hand. -/
theorem IsBddFamily.comp_clm : ∀ (k : ℕ) {W W' : Type u} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W'] (L : W →L[ℝ] W')
    {f : H → ℝ → W}, IsBddFamily k f → IsBddFamily k fun x s ↦ L (f x s) := by
  intro k
  induction k with
  | zero => intro W W' _ _ _ _ L f hf; exact IsBddCts.comp_clm L hf
  | succ k ih =>
      intro W W' _ _ _ _ L f hf
      obtain ⟨h0, f', hd, hf'⟩ := hf
      exact ⟨h0.comp_clm L, fun x s ↦ L.comp (f' x s),
        fun x s ↦ L.hasFDerivAt.comp x (hd x s), ih (compL ℝ H W W' L) hf'⟩

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem IsBddCts.prodMk {f : H → ℝ → W₁} {g : H → ℝ → W₂} (hf : IsBddCts f)
    (hg : IsBddCts g) : IsBddCts fun x s ↦ (f x s, g x s) where
  cts := fun x ↦ (hf.cts x).prodMk (hg.cts x)
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    obtain ⟨D, hD⟩ := hg.bdd
    refine ⟨max C D, fun x s ↦ ?_⟩
    rw [Prod.norm_def]
    exact max_le_max (hC x s) (hD x s)

/-- Pairing of two continuous linear maps out of `H`, bundled as a continuous linear map of the
pair.  Mathlib bundles `prod` only in shapes that do not fit here; the `inl`/`inr`
decomposition makes linearity and continuity hold by construction. -/
noncomputable def prodCLM (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (W₁ W₂ : Type u) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂]
    [NormedSpace ℝ W₂] : ((H →L[ℝ] W₁) × (H →L[ℝ] W₂)) →L[ℝ] (H →L[ℝ] (W₁ × W₂)) :=
  (compL ℝ H W₁ (W₁ × W₂) (inl ℝ W₁ W₂)).comp (fst ℝ (H →L[ℝ] W₁) (H →L[ℝ] W₂))
    + (compL ℝ H W₂ (W₁ × W₂) (inr ℝ W₁ W₂)).comp (snd ℝ (H →L[ℝ] W₁) (H →L[ℝ] W₂))

@[simp] theorem prodCLM_apply (z : (H →L[ℝ] W₁) × (H →L[ℝ] W₂)) :
    prodCLM H W₁ W₂ z = z.1.prod z.2 := by
  ext h <;> simp [prodCLM]

/-- **Stability under pairing.**  The induction step needs the previous lemma: the derivative
family of the pair is `(f' x s).prod (g' x s)`, which is the *pair* of derivative families
pushed through the fixed map `prodCLM`. -/
theorem IsBddFamily.prodMk : ∀ (k : ℕ) {W₁ W₂ : Type u} [NormedAddCommGroup W₁]
    [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] {f : H → ℝ → W₁}
    {g : H → ℝ → W₂}, IsBddFamily k f → IsBddFamily k g →
    IsBddFamily k fun x s ↦ (f x s, g x s) := by
  intro k
  induction k with
  | zero => intro W₁ W₂ _ _ _ _ f g hf hg; exact IsBddCts.prodMk hf hg
  | succ k ih =>
      intro W₁ W₂ _ _ _ _ f g hf hg
      obtain ⟨h0, f', hdf, hf'⟩ := hf
      obtain ⟨g0, g', hdg, hg'⟩ := hg
      refine ⟨h0.prodMk g0, fun x s ↦ (f' x s).prod (g' x s),
        fun x s ↦ (hdf x s).prodMk (hdg x s), ?_⟩
      have h := IsBddFamily.comp_clm k (prodCLM H W₁ W₂) (ih hf' hg')
      have key : (fun x s ↦ prodCLM H W₁ W₂ (f' x s, g' x s))
          = fun x s ↦ (f' x s).prod (g' x s) := by
        funext x s
        rw [prodCLM_apply]
      rwa [key] at h

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem IsBddCts.bilin {V₁ V₂ V₃ : Type u} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (B : V₁ →L[ℝ] V₂ →L[ℝ] V₃) {f : H → ℝ → V₁} {g : H → ℝ → V₂} (hf : IsBddCts f)
    (hg : IsBddCts g) : IsBddCts fun x s ↦ B (f x s) (g x s) where
  cts := fun x ↦ (B.continuous.comp (hf.cts x)).clm_apply (hg.cts x)
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    obtain ⟨D, hD⟩ := hg.bdd
    refine ⟨‖B‖ * C * D, fun x s ↦ ?_⟩
    have h1 := B.le_opNorm₂ (f x s) (g x s)
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x s)
    have hstep1 : ‖B‖ * ‖f x s‖ * ‖g x s‖ ≤ ‖B‖ * C * ‖g x s‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hC x s) (norm_nonneg B)) (norm_nonneg _)
    have hstep2 : ‖B‖ * C * ‖g x s‖ ≤ ‖B‖ * C * D :=
      mul_le_mul_of_nonneg_left (hD x s) (mul_nonneg (norm_nonneg B) hC0)
    linarith

/-- Addition: `comp_clm` at the addition map, applied to the pair.  Nothing new. -/
theorem IsBddFamily.add (k : ℕ) {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : H → ℝ → W} (hf : IsBddFamily k f) (hg : IsBddFamily k g) :
    IsBddFamily k fun x s ↦ f x s + g x s :=
  IsBddFamily.comp_clm k (fst ℝ W W + snd ℝ W W) (IsBddFamily.prodMk k hf hg)

/-- **Stability under a bounded bilinear map** --- the Leibniz induction, and the only place in
the file where a product rule appears at all.

The derivative family of `B(f,g)` is `B.precompR (f, g') + B.precompL (f', g)`, and each summand
is *this same lemma one level down at a different bilinear map* --- so, exactly as for
`comp_clm`, nothing is differentiated by hand at any level.  The two factors of a summand sit at
different levels, which is what `le_succ` is for. -/
theorem IsBddFamily.bilin : ∀ (k : ℕ) {V₁ V₂ V₃ : Type u} [NormedAddCommGroup V₁]
    [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (B : V₁ →L[ℝ] V₂ →L[ℝ] V₃) {f : H → ℝ → V₁} {g : H → ℝ → V₂},
    IsBddFamily k f → IsBddFamily k g → IsBddFamily k fun x s ↦ B (f x s) (g x s) := by
  intro k
  induction k with
  | zero =>
      intro V₁ V₂ V₃ _ _ _ _ _ _ B f g hf hg
      exact IsBddCts.bilin B hf hg
  | succ k ih =>
      intro V₁ V₂ V₃ _ _ _ _ _ _ B f g hf hg
      have hfk : IsBddFamily k f := IsBddFamily.le_succ k hf
      have hgk : IsBddFamily k g := IsBddFamily.le_succ k hg
      obtain ⟨h0, f', hdf, hf'⟩ := hf
      obtain ⟨g0, g', hdg, hg'⟩ := hg
      refine ⟨IsBddCts.bilin B h0 g0,
        fun x s ↦ (B (f x s)).comp (g' x s) + (B.comp (f' x s)).flip (g x s),
        fun x s ↦ (B.hasFDerivAt.comp x (hdf x s)).clm_apply (hdg x s), ?_⟩
      have hres := IsBddFamily.add k (ih (B.precompR H) hfk hg') (ih (B.precompL H) hf' hgk)
      have heq : (fun x s ↦ B.precompR H (f x s) (g' x s) + B.precompL H (f' x s) (g x s))
          = fun x s ↦ (B (f x s)).comp (g' x s) + (B.comp (f' x s)).flip (g x s) := by
        funext x s
        ext h'
        simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL]
      rwa [heq] at hres

/-- **Instantiation, and the falsification check for `bilin`**: composition of two operator
families.  This is the shape the augmented field itself is built from, and unlike a *scalar*
family it is expressible here --- see the universe note below.

**A scalar family is NOT expressible at a general universe**, and the reason is worth recording
rather than rediscovering: `IsBddFamily` recurses `W ↦ (H →L[ℝ] W)`, which is stable only if `W`
and `H` share a universe, and `ℝ : Type 0`.  Nothing is lost: multiplication by a bump `χ` is
`fun x s ↦ (χ x • 1) (A x s)`, whose left factor is valued in `(W →L[ℝ] W) : Type u`, so the
scalar never has to carry a family of its own. -/
theorem IsBddFamily.comp_op (k : ℕ) {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : H → ℝ → (W →L[ℝ] W)} (hf : IsBddFamily k f) (hg : IsBddFamily k g) :
    IsBddFamily k fun x s ↦ (f x s).comp (g x s) :=
  IsBddFamily.bilin k (compL ℝ W W W) hf hg

/-- **A `C^k` map with bounded iterated derivatives is a bounded `C^k` family**, constant in
`t`.  This is what connects `IsBddFamily` to Mathlib's `ContDiff`, and so what makes the class
checkable in practice rather than only closed under operations.

The induction is the definition of `ContDiff` unwound one step at a time: the derivative family
is `fderiv ℝ g`, which is `C^{k-1}` by `contDiff_succ_iff_fderiv`, and whose iterated
derivatives are those of `g` shifted by one (`norm_iteratedFDeriv_fderiv`). -/
theorem isBddFamily_of_contDiff : ∀ (k : ℕ) {W : Type u} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (g : H → W), ContDiff ℝ k g →
    (∀ j ≤ k, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C) →
    IsBddFamily k fun (x : H) (_ : ℝ) ↦ g x := by
  intro k
  induction k with
  | zero =>
      intro W _ _ g _ hb
      obtain ⟨C, hC⟩ := hb 0 le_rfl
      exact ⟨fun _ ↦ continuous_const, C, fun x _ ↦ by
        have h := hC x; rwa [norm_iteratedFDeriv_zero] at h⟩
  | succ k ih =>
      intro W _ _ g hg hb
      obtain ⟨C, hC⟩ := hb 0 (Nat.zero_le _)
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast] at hg
      obtain ⟨hdiff, -, hfd⟩ := contDiff_succ_iff_fderiv.1 hg
      refine ⟨⟨fun _ ↦ continuous_const, C, fun x _ ↦ by
          have h := hC x; rwa [norm_iteratedFDeriv_zero] at h⟩,
        fun x _ ↦ fderiv ℝ g x, fun x _ ↦ (hdiff x).hasFDerivAt, ?_⟩
      refine ih (fderiv ℝ g) hfd ?_
      intro j hj
      obtain ⟨D, hD⟩ := hb (j + 1) (by omega)
      exact ⟨D, fun x ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hD x⟩


/-- **A compactly supported `C^k` map is a bounded `C^k` family**: its iterated derivatives are
continuous with compact support, hence bounded.  This is what makes a bump function usable as an
`IsBddFamily`, and so what a chart-local argument needs. -/
theorem isBddFamily_of_hasCompactSupport (k : ℕ) {W : Type u} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (g : H → W) (hg : ContDiff ℝ k g) (hsupp : HasCompactSupport g) :
    IsBddFamily k fun (x : H) (_ : ℝ) ↦ g x := by
  refine isBddFamily_of_contDiff k g hg fun j hj ↦ ?_
  exact (hsupp.iteratedFDeriv j).exists_bound_of_continuous
    (hg.continuous_iteratedFDeriv (by exact_mod_cast hj))

end BddFamily

section Smooth

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The augmented coefficient is a bounded `C^k` family as soon as `A` and its derivative family
are --- because it is `augCLM` applied to the pair, and `IsBddFamily` is stable under both. -/
theorem isBddFamily_augOp (k : ℕ) {A : H → ℝ → (F →L[ℝ] F)}
    {A' : H → ℝ → (H →L[ℝ] (F →L[ℝ] F))} (hA : IsBddFamily k A) (hA' : IsBddFamily k A') :
    IsBddFamily k (augOp A A') :=
  IsBddFamily.comp_clm k augCLM (IsBddFamily.prodMk k hA hA')

-- BENCH: dyson-sum-contdiff
/-- **`Φ(·,t)` is `C^k` in the parameter, for every `k`** --- the induction
`LinearODEAugmented.lean` left open, carried out.

The step is: `Φ` is `C^{k+1}` iff differentiable with `C^k` derivative; `D_xΦ` *is* the Dyson
sum of the augmented system read through the fixed continuous linear map `augRead`; and that
Dyson sum is `C^k` by the induction hypothesis applied at `F := G`, its coefficient being a
bounded `C^k` family by `isBddFamily_augOp`. **No new analysis at any level** --- every
derivative in sight comes from the one `C¹` theorem of `LinearODE.lean`.

The induction runs with `F` and `H` in a single universe, which is what keeps `G` in place; the
statement is universe-monomorphic for that reason and for no other. -/
theorem contDiff_dysonSum : ∀ (k : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (A : H → ℝ → (F →L[ℝ] F)), IsBddFamily (k + 1) A → ∀ t : ℝ,
    ContDiff ℝ k fun y ↦ dysonSum (A y) t := by
  intro k
  induction k with
  | zero =>
      intro F _ _ _ A hA t
      obtain ⟨h0, A', hdA, hA'⟩ := hA
      obtain ⟨C, hC⟩ := h0.bdd
      obtain ⟨C', hC'⟩ := hA'.isBddCts.bdd
      rw [Nat.cast_zero, contDiff_zero]
      exact (differentiable_dysonSum h0.cts hA'.isBddCts.cts hC hC' hdA t).continuous
  | succ k ih =>
      intro F _ _ _ A hA t
      have hAlow : IsBddFamily (k + 1) A := IsBddFamily.le_succ (k + 1) hA
      obtain ⟨h0, A', hdA, hA'⟩ := hA
      obtain ⟨C, hC⟩ := h0.bdd
      obtain ⟨C', hC'⟩ := hA'.isBddCts.bdd
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast, contDiff_succ_iff_fderiv]
      refine ⟨differentiable_dysonSum h0.cts hA'.isBddCts.cts hC hC' hdA t,
        fun h ↦ absurd h (by simp), ?_⟩
      have hfd : (fderiv ℝ fun y ↦ dysonSum (A y) t) = fun y ↦ dysonDerivSum A A' y t := by
        funext y
        exact (hasFDerivAt_dysonSum h0.cts hA'.isBddCts.cts hC hC' hdA t y).fderiv
      have hid : (fun y ↦ dysonDerivSum A A' y t)
          = ⇑augRead ∘ fun y ↦ dysonSum (augOp A A' y) t := by
        funext y
        show dysonDerivSum A A' y t
          = (dysonSum (augOp A A' y) t ((1 : F →L[ℝ] F), (0 : H →L[ℝ] (F →L[ℝ] F)))).2
        rw [dysonSum_augOp_apply h0.cts hA'.isBddCts.cts hC hC' y t]
      rw [hfd, hid]
      exact augRead.contDiff.comp
        (ih (augOp A A') (isBddFamily_augOp (k + 1) hAlow hA') t)

omit [CompleteSpace F] in
/-- **Non-vacuity.**  A family that does not depend on the parameter is a bounded `C^k` family
for every `k`, its derivative families all zero.  Without a witness like this, the theorem above
could be quantifying over an empty hypothesis class at large `k` and asserting nothing. -/
theorem isBddFamily_const : ∀ (k : ℕ) {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : ℝ → W), Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) →
    IsBddFamily k fun (_ : H) s ↦ g s := by
  intro k
  induction k with
  | zero =>
      intro W _ _ g hg hb
      obtain ⟨C, hC⟩ := hb
      exact ⟨fun _ ↦ hg, C, fun _ s ↦ hC s⟩
  | succ k ih =>
      intro W _ _ g hg hb
      obtain ⟨C, hC⟩ := hb
      refine ⟨⟨fun _ ↦ hg, C, fun _ s ↦ hC s⟩, fun _ _ ↦ 0,
        fun x s ↦ hasFDerivAt_const _ _, ?_⟩
      exact ih (fun _ ↦ (0 : H →L[ℝ] W)) continuous_const ⟨0, fun s ↦ by simp⟩

/-- **Agreement check.**  At `k = 1` the general theorem reproduces
`contDiff_one_dysonSum`, whose explicit hypothesis block is exactly `IsBddFamily 2` spelled
out.  The two developments reach the same conclusion from the same data. -/
theorem contDiff_one_dysonSum_of_isBddFamily {A : H → ℝ → (F →L[ℝ] F)}
    (hA : IsBddFamily 2 A) (t : ℝ) : ContDiff ℝ 1 fun y ↦ dysonSum (A y) t := by
  simpa using contDiff_dysonSum 1 A hA t

/-- **The conclusion localizes.**

`Φ(·,t)` depends on the parameter only through `A(x,·)`, so two families agreeing pointwise on a
set give the same `Φ` there.  This is the statement a chart-local argument consumes: the
hypotheses above are global in the parameter and a chart is not, so one supplies a globally
bounded `B` agreeing with `A` where it matters --- a bump product, with
`isBddFamily_of_hasCompactSupport` for the bump --- and reads off `C^k` there.

**What is still missing on this line, stated precisely.** Building that `B` for a genuinely
`t`-dependent `A` needs a `C^k` hypothesis on `A` that is *uniform in `t`*, and the cleanest
form of that hypothesis is not settled here. So the remaining ODE-side gap is a hypothesis
shape, not a theorem --- much smaller than the "no `C^k` parameter theory at all" this line
started from, but not nothing. -/
theorem contDiffOn_dysonSum (k : ℕ) {U : Set H} {A B : H → ℝ → (F →L[ℝ] F)}
    (hB : IsBddFamily (k + 1) B) (hAB : ∀ x ∈ U, A x = B x) (t : ℝ) :
    ContDiffOn ℝ k (fun y ↦ dysonSum (A y) t) U :=
  (contDiff_dysonSum k B hB t).contDiffOn.congr fun y hy ↦ by rw [hAB y hy]

end Smooth

end RicciFlowBlueprint
