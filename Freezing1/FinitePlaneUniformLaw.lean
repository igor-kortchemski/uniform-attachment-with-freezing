module

public import Freezing1.FinitePlaneAtomMass
public import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning the actual plane limit law on a finite vertex count

All finite plane trees with exactly $m$ vertices form the finite class
`FinitePlaneClass m`. The actual plane limit law gives every member the same
mass $(1-p)^m p^{m-1}$, so conditioning it on the class is the uniform
law on all of them. No Catalan enumeration is needed.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- All finite plane trees with exactly `m` vertices, as a subset of the Polish space of plane trees. -/
def finitePlaneSet (m : ℕ) : Set Tree := {T | FiniteVertices T ∧ finiteVertexCount T = m}

theorem finitePlaneSet_eq_range (m : ℕ) :
    finitePlaneSet m = Set.range (Subtype.val : FinitePlaneClass m → Tree) := by
  ext T
  constructor
  · intro hT
    exact ⟨⟨T, hT⟩, rfl⟩
  · rintro ⟨T, rfl⟩
    exact T.property

theorem finitePlaneSet_finite (m : ℕ) : (finitePlaneSet m).Finite := by
  have : Finite {T : Tree // FiniteVertices T ∧ finiteVertexCount T = m} :=
    inferInstanceAs (Finite (FinitePlaneClass m))
  rw [finitePlaneSet_eq_range]
  exact Set.finite_range _

theorem measurableSet_finitePlaneSet (m : ℕ) : MeasurableSet (finitePlaneSet m) :=
  (finitePlaneSet_finite m).measurableSet

/-- The uniform probability law on all finite plane trees with `m` vertices. -/
noncomputable def finitePlaneUniform (m : ℕ) : Measure Tree :=
  (Fintype.card (FinitePlaneClass m) : ℝ≥0∞)⁻¹ • ∑ T : FinitePlaneClass m, Measure.dirac T.val

theorem finitePlaneUniform_apply (m : ℕ) {S : Set Tree} (hS : MeasurableSet S) :
    finitePlaneUniform m S =
      (Fintype.card (FinitePlaneClass m) : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun T : FinitePlaneClass m => T.val ∈ S).card : ℝ≥0∞) := by
  rw [finitePlaneUniform, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  simp only [Measure.dirac_apply' _ hS, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

theorem finitePlaneUniform_isProbability {m : ℕ} (hm : 1 ≤ m) :
    IsProbabilityMeasure (finitePlaneUniform m) := by
  have : Nonempty (FinitePlaneClass m) := finitePlaneClass_nonempty hm
  constructor
  rw [finitePlaneUniform_apply m MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  rw [Finset.card_univ]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

end Freezing1.PlaneTree

namespace Freezing1.ForwardAnnealed

open MeasureTheory ProbabilityTheory PlaneTree
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem measure_finitePlaneSet_inter {m : ℕ} (μ : Measure Tree) {c : ℝ≥0∞}
    (hat : ∀ T : FinitePlaneClass m, μ {T.val} = c) (S : Set Tree) :
    μ (finitePlaneSet m ∩ S) =
      ((Finset.univ.filter fun T : FinitePlaneClass m => T.val ∈ S).card : ℝ≥0∞) * c := by
  set F : Finset Tree := (Finset.univ.filter fun T : FinitePlaneClass m => T.val ∈ S).image
    Subtype.val with hF
  have hset : finitePlaneSet m ∩ S = (F : Set Tree) := by
    ext T
    simp only [finitePlaneSet_eq_range, Set.mem_inter_iff, Set.mem_range, Finset.coe_image,
      Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq, hF]
    constructor
    · rintro ⟨⟨U, rfl⟩, hS⟩
      exact ⟨U, hS, rfl⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨⟨U, rfl⟩, hU⟩
  rw [hset, ← sum_measure_singleton, hF, Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  simp only [hat, Finset.sum_const, nsmul_eq_mul]

theorem cond_finitePlaneSet_eq_uniform {m : ℕ} (hm : 1 ≤ m) (μ : Measure Tree) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (hat : ∀ T : FinitePlaneClass m, μ {T.val} = c) :
    μ[|finitePlaneSet m] = finitePlaneUniform m := by
  have : Nonempty (FinitePlaneClass m) := finitePlaneClass_nonempty hm
  have hcard0 : (Fintype.card (FinitePlaneClass m) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have htotal : μ (finitePlaneSet m) = (Fintype.card (FinitePlaneClass m) : ℝ≥0∞) * c := by
    have := measure_finitePlaneSet_inter μ hat Set.univ
    simpa only [Set.inter_univ, Finset.mem_univ, Set.mem_univ, Finset.filter_true,
      Finset.card_univ] using this
  ext S hS
  rw [cond_apply (measurableSet_finitePlaneSet m), finitePlaneUniform_apply m hS,
    measure_finitePlaneSet_inter μ hat S, htotal,
    ENNReal.mul_inv (Or.inl hcard0) (Or.inl (by simp)), mul_assoc]
  congr 1
  rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, mul_one]

end Freezing1.ForwardAnnealed
