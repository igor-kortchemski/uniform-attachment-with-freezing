module

public import Freezing1.ForwardLaw

/-! The all-positive specialization is the random recursive tree on n+1 vertices.
The comparison law uses fresh uniform parents in {0,...,n}, independently of
the current tree, rather than a choice from a random active set. -/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical ENNReal

namespace RecursiveTree

noncomputable def uniformParentLaw (n : ℕ) : Measure ℕ :=
  Measure.uniformOfFinset (Finset.range (n + 1))

instance uniformParentLaw_probability (n : ℕ) : IsProbabilityMeasure (uniformParentLaw n) := by
  constructor
  simp only [uniformParentLaw, Measure.uniformOfFinset_apply, Set.mem_univ,
    Finset.filter_true, Finset.card_range]
  exact ENNReal.div_self (by positivity) (by simp)

/-- Start from vertex zero and attach vertex n+1 to a fresh uniform member
of {0,...,n}. The parent distribution does not depend on the current tree. -/
noncomputable def law : ℕ → Measure Forward.State
  | 0 => Measure.dirac Forward.initial
  | n + 1 => (law n).bind fun s =>
      (uniformParentLaw n).map (fun v => Forward.attach s (n + 1) v)

instance law_probability (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ n ih =>
    apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
    exact Filter.Eventually.of_forall fun _ =>
      Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
        |>.mpr inferInstance

end RecursiveTree

namespace Forward

theorem treeLaw_allAttachment_vertex_sets (n : ℕ) :
    ∀ᵐ s ∂treeLaw (fun _ => true) n,
      s.active = Finset.range (n + 1) ∧ s.vertices = Finset.range (n + 1) := by
  apply treeLaw_ae_induction (fun _ => true)
    (fun n s => s.active = Finset.range (n + 1) ∧ s.vertices = Finset.range (n + 1))
  · simp [initial]
  · intro k s hs he
    have hz : 0 ∈ s.active := by rw [hs.1]; simp
    simp [he] at hz
  · intro k s hs v hv
    simp only [step, ite_eq_left hv, ↓reduceIte]
    change insert (k + 1) s.active = Finset.range (k + 1 + 1) ∧
      insert (k + 1) s.vertices = Finset.range (k + 1 + 1)
    rw [hs.1, hs.2, Finset.range_add_one (n := k + 1)]
    exact ⟨rfl, rfl⟩

/-- The full labelled forward tree law, including parent/depth fields, is
the independently specified random recursive parent-choice law. -/
theorem treeLaw_allAttachment_eq_recursive (n : ℕ) :
    treeLaw (fun _ => true) n = RecursiveTree.law n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [treeLaw, RecursiveTree.law, ← ih]
    apply Measure.bind_congr_right
    filter_upwards [treeLaw_allAttachment_vertex_sets n] with s hs
    have hne : s.active.Nonempty := ⟨0, by rw [hs.1]; simp⟩
    rw [transitionLaw, ite_eq_left hne, hs.1]
    change (Measure.uniformOfFinset (Finset.range (n + 1))).map _ =
      (Measure.uniformOfFinset (Finset.range (n + 1))).map _
    apply Measure.map_congr
    have hae : ∀ᵐ v ∂Measure.uniformOfFinset (Finset.range (n + 1)),
        v ∈ Finset.range (n + 1) := by
      rw [ae_iff]
      simp [Measure.uniformOfFinset_apply]
    filter_upwards [hae] with v hv
    have hva : v ∈ s.active := by rwa [hs.1]
    simp [step, hva]

end Forward

namespace RecursiveTree

/-- The new parent's law is exactly uniform on all earlier vertex labels. -/
theorem newest_parent_law (n : ℕ) :
    (law (n + 1)).map (fun s => s.parent (n + 1)) = uniformParentLaw n := by
  rw [law, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable]
  have he (s : Forward.State) :
      ((uniformParentLaw n).map (fun v => Forward.attach s (n + 1) v)).map
        (fun t => t.parent (n + 1)) = uniformParentLaw n := by
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    simp only [Function.comp_def, Forward.attach, Function.update_self]
    rw [show (fun x : ℕ => x) = id from rfl, Measure.map_id]
  simp only [he, Measure.bind_const, measure_univ, one_smul]

end RecursiveTree
end Freezing1
