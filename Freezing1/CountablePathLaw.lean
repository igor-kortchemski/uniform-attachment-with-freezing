module

public import Freezing1.InterleavedChainCylinders
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Data.List.OfFn

/-!
# Complete path laws determined by finite words

This is only a measure-extensionality statement. It supplies the final
passage from actual joint cylinder probabilities to a whole-path law.
-/

@[expose] public section

namespace Freezing1.CountablePathLaw

open MeasureTheory
open scoped Classical

variable {E : Type*} [MeasurableSpace E]

/-- Equality of all initial finite-dimensional distributions determines a
finite measure on the countable path product. -/
theorem eq_of_prefix_map_eq (μ ν : Measure (ℕ → E)) [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (Preorder.frestrictLe n) = ν.map (Preorder.frestrictLe n)) : μ = ν := by
  let P := fun I : Finset ℕ => μ.map I.restrict
  have : ∀ I : Finset ℕ, IsFiniteMeasure (P I) := fun _ => inferInstance
  have hμ : IsProjectiveLimit μ P := fun _ => rfl
  apply hμ.unique
  intro I
  let n := I.sup id
  let f : ((i : Finset.Iic n) → E) → ((i : I) → E) := fun q i =>
    q ⟨i.val, Finset.mem_Iic.mpr (Finset.le_sup (f := id) i.property)⟩
  have hh := congrArg (fun ρ : Measure ((i : Finset.Iic n) → E) => ρ.map f) (h n)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh.symm

variable [MeasurableSingletonClass E] [Countable E]

/-- A word beginning at time zero. -/
def initialWord (H : ℕ → E) (r : ℕ) : List E := List.ofFn (fun i : Fin r => H i.val)

theorem measurable_initialWord (r : ℕ) : Measurable (fun H : ℕ → E => initialWord H r) :=
  (measurable_of_countable (List.ofFn : (Fin r → E) → List E)).comp (by fun_prop)

/-- All pairs of initial-word probabilities determine a measure on a pair
of complete countable-state trajectories. -/
theorem pair_eq_of_word_probabilities
    (μ ν : Measure ((ℕ → E) × (ℕ → E))) [IsFiniteMeasure μ]
    (h : ∀ u v : List E,
      μ {p | initialWord p.1 u.length = u ∧ initialWord p.2 v.length = v} =
      ν {p | initialWord p.1 u.length = u ∧ initialWord p.2 v.length = v}) : μ = ν := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow E E ℕ
  have he : μ.map e.symm = ν.map e.symm := by
    apply eq_of_prefix_map_eq
    intro n
    apply Measure.ext_of_singleton
    intro z
    rw [Measure.map_map (by fun_prop) e.symm.measurable,
      Measure.map_map (by fun_prop) e.symm.measurable,
      Measure.map_apply (by fun_prop) (measurableSet_singleton z),
      Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
    let u := List.ofFn (fun i : Fin (n + 1) => (z ⟨i.val, Finset.mem_Iic.mpr (by omega)⟩).1)
    let v := List.ofFn (fun i : Fin (n + 1) => (z ⟨i.val, Finset.mem_Iic.mpr (by omega)⟩).2)
    have hevent : (Preorder.frestrictLe n ∘ e.symm) ⁻¹' {z} =
        {p | initialWord p.1 u.length = u ∧ initialWord p.2 v.length = v} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_def,
        Set.mem_ofPred_eq, initialWord, u, v, List.length_ofFn, List.ofFn_inj]
      constructor
      · intro hp
        constructor <;> funext i
        · exact congrArg Prod.fst (congrFun hp ⟨i.val, Finset.mem_Iic.mpr (by omega)⟩)
        · exact congrArg Prod.snd (congrFun hp ⟨i.val, Finset.mem_Iic.mpr (by omega)⟩)
      · rintro ⟨hp, hq⟩
        funext i
        apply Prod.ext
        · exact congrFun hp ⟨i.val, by have := Finset.mem_Iic.mp i.property; omega⟩
        · exact congrFun hq ⟨i.val, by have := Finset.mem_Iic.mp i.property; omega⟩
    rw [hevent]
    exact h u v
  have hh := congrArg (fun ρ => ρ.map e) he
  simpa only [Measure.map_map e.measurable e.symm.measurable,
    e.self_comp_symm, Measure.map_id] using hh

end Freezing1.CountablePathLaw
