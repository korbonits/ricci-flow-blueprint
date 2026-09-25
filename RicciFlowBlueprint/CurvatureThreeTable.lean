/-
**The Riemann tensor in dimension three, in a Ricci eigenbasis: every component.**

`CurvatureThree.lean` reads two facts off the trace identity `Ric(v,w) = ∑ᵢ Rm(eᵢ,v,w,eᵢ)`:
the diagonal of the curvature operator, and one off-diagonal component vanishing when the
matching Ricci component does. This file finishes the job: in an orthonormal basis that
diagonalises `Ric`, **all 81 components** are

`Rm(eᵢ,eⱼ,eₖ,eₗ) = K_{ij}·[i=l ∧ j=k] − K_{ij}·[i=k ∧ j=l]`,

with `K_{ij} = Rm(eᵢ,eⱼ,eⱼ,eᵢ)` the sectional curvature of the plane `eᵢ∧eⱼ`. So the tensor
is determined by three numbers, and every quadratic expression in it --- the reaction terms of
`∂ₜRic` --- becomes a polynomial in the three sectional curvatures.

**Still no Weyl tensor.** The literature gets this from `Rm = Ric ⊙ g − (scal/4) g ⊙ g`; the
argument here is combinatorial. A component with `i = j` or `k = l` vanishes by antisymmetry;
if `{i,j} = {k,l}` it is `±K_{ij}`; and otherwise the two index pairs share exactly one index
(there are only three indices), which antisymmetry moves to the canonical shape
`Rm(e_c,e_a,e_{a'},e_c)` --- and that is `Ric(e_a,e_{a'}) = 0`, the trace identity having a
single surviving summand.
-/
import RicciFlowBlueprint.CurvatureThree

open Bundle Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [T2Space M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) ↦ TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  {x : M}
  (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
  (htor : cov.torsion = 0) (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x))

set_option maxSynthPendingDepth 3

/-- In `Fin 3`, an index different from `c` is one of the two others. -/
theorem fin3_eq_or_eq {c a a' k : Fin 3} (hca : c ≠ a) (hca' : c ≠ a') (haa' : a ≠ a')
    (hkc : k ≠ c) : k = a ∨ k = a' := by
  have h1 := Fin.val_ne_of_ne hca
  have h2 := Fin.val_ne_of_ne hca'
  have h3 := Fin.val_ne_of_ne haa'
  have h4 := Fin.val_ne_of_ne hkc
  have := k.isLt; have := c.isLt; have := a.isLt; have := a'.isLt
  rcases (show k.val = a.val ∨ k.val = a'.val by omega) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

include hmetric htor in
/-- **The canonical off-diagonal zero**: for distinct `c, a, a'`,
`Rm(e_c, e_a, e_{a'}, e_c) = Ric(e_a, e_{a'})`, the trace identity having one surviving
summand. -/
theorem curvatureTensorAt_shared_eq_ricciAt {c a a' : Fin 3} (hca : c ≠ a) (hca' : c ≠ a')
    (haa' : a ≠ a') :
    cov.curvatureTensorAt (b c) (b a) (b a') (b c) = cov.ricciAt x (b a) (b a') := by
  rw [cov.ricciAt_eq_sum_curvatureTensorAt b, Finset.sum_eq_single c ?_ (by simp)]
  intro k _ hkc
  rcases fin3_eq_or_eq hca hca' haa' hkc with h | h
  · rw [h]; exact cov.curvatureTensorAt_self_fst (b a)
  · rw [h]; exact cov.curvatureTensorAt_self_thd hmetric htor (b a')

variable (hric : ∀ i j, i ≠ j → cov.ricciAt x (b i) (b j) = 0)

include hmetric htor hric in
-- BENCH: curvature-three-table
/-- **The full component table in a Ricci eigenbasis**:
`Rm(eᵢ,eⱼ,eₖ,eₗ) = K_{ij}[i=l ∧ j=k] − K_{ij}[i=k ∧ j=l]`, `K_{ij} = Rm(eᵢ,eⱼ,eⱼ,eᵢ)`. -/
theorem curvatureTensorAt_three_table (i j k l : Fin 3) :
    cov.curvatureTensorAt (b i) (b j) (b k) (b l)
      = (if i = l ∧ j = k then cov.curvatureTensorAt (b i) (b j) (b j) (b i) else 0)
        - (if i = k ∧ j = l then cov.curvatureTensorAt (b i) (b j) (b j) (b i) else 0) := by
  have a12 : ∀ p q r s : Fin 3, cov.curvatureTensorAt (b p) (b q) (b r) (b s)
      = -cov.curvatureTensorAt (b q) (b p) (b r) (b s) := fun _ _ _ _ ↦
    cov.curvatureTensorAt_antisymm_fst_snd
  have a34 : ∀ p q r s : Fin 3, cov.curvatureTensorAt (b p) (b q) (b r) (b s)
      = -cov.curvatureTensorAt (b p) (b q) (b s) (b r) := fun _ _ _ _ ↦
    cov.curvatureTensorAt_antisymm_thd_fth hmetric htor
  have zero : ∀ c a a' : Fin 3, c ≠ a → c ≠ a' → a ≠ a' →
      cov.curvatureTensorAt (b c) (b a) (b a') (b c) = 0 := fun c a a' h1 h2 h3 ↦ by
    rw [curvatureTensorAt_shared_eq_ricciAt cov hmetric htor b h1 h2 h3, hric a a' h3]
  rcases eq_or_ne i j with hij | hij
  · subst hij
    rw [cov.curvatureTensorAt_self_fst (b i), cov.curvatureTensorAt_self_fst (b i)]
    simp
  rcases eq_or_ne k l with hkl | hkl
  · subst hkl
    rw [cov.curvatureTensorAt_self_thd hmetric htor (b k)]
    by_cases h : i = k ∧ j = k
    · exact absurd (h.1.trans h.2.symm) hij
    · simp [h]
  -- both pairs genuine: compare them
  by_cases hA : i = l ∧ j = k
  · obtain ⟨rfl, rfl⟩ := hA
    have hB : ¬ (i = j ∧ j = i) := fun h ↦ hij h.1
    simp [hB]
  by_cases hB : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := hB
    have hA' : ¬ (i = j ∧ j = i) := fun h ↦ hij h.1
    simp only [hA', and_self, ↓reduceIte, zero_sub]
    rw [a34]
  simp only [hA, hB, ↓reduceIte, sub_zero]
  -- exactly one shared index
  rcases eq_or_ne i k with hik | hik
  · subst hik
    have hjl : j ≠ l := fun h ↦ hB ⟨rfl, h⟩
    rw [a34, zero i j l hij hkl hjl, neg_zero]
  rcases eq_or_ne i l with hil | hil
  · subst hil
    have hjk : j ≠ k := fun h ↦ hA ⟨rfl, h⟩
    exact zero i j k hij hkl.symm hjk
  rcases eq_or_ne j k with hjk | hjk
  · subst hjk
    rw [a12, a34, zero j i l hij.symm hkl hil, neg_zero, neg_zero]
  rcases eq_or_ne j l with hjl | hjl
  · subst hjl
    rw [a12, zero j i k hij.symm hkl.symm hik, neg_zero]
  -- four distinct indices in `Fin 3`: impossible
  exfalso
  have h1 := Fin.val_ne_of_ne hij; have h2 := Fin.val_ne_of_ne hkl
  have h3 := Fin.val_ne_of_ne hik; have h4 := Fin.val_ne_of_ne hil
  have h5 := Fin.val_ne_of_ne hjk; have h6 := Fin.val_ne_of_ne hjl
  have := i.isLt; have := j.isLt; have := k.isLt; have := l.isLt
  omega

end CovariantDerivative
