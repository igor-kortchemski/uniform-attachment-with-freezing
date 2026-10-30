module

public import Freezing1.CanonicalUniformSampling
public import Freezing1.ForwardHistoryExistence

/-! Reverse birth is a freezing index. Its capture event implies actual prefix membership. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Birth in Algorithm2 dominates the actual chronological infection label.
These two clocks are not identified. -/
theorem reverse_birth_captures_forward_vertex {x : SignSequence} {n m : ℕ}
    {F : ReverseStamped.Forest} (ht : ReverseStamped.TimesValidAt x n 0 F)
    (ho : ReverseStamped.TimestampOrder F) {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices)
    (hb : birthTime n v ≤ m) :
    F.edgeTime v ∈ (Forward.truncateAt (CanonicalTree.reverseState F) m).vertices := by
  have htime : F.edgeTime v ≤ m := by
    cases v with
    | inl j =>
      have hnm : n ≤ m := hb
      by_cases hz : F.edgeTime (.inl j) = 0
      · omega
      · exact (ht.range _ hv hz).2.1.trans hnm
    | inr j =>
      have hf := ho.frozen_incoming j hv
      change j ≤ m at hb
      omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hv, htime⟩

/-- Uniform reverse-birth capture is a lower bound for actual chronological
prefix membership, on the exact canonical vertex correspondence. -/
theorem reverse_birth_probability_le_forward_capture {x : SignSequence} {n m : ℕ}
    {F : ReverseStamped.Forest} (ht : ReverseStamped.TimesValidAt x n 0 F)
    (ho : ReverseStamped.TimestampOrder F)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    (Measure.uniformOfFinset F.forest.vertices).real {v | birthTime n v ≤ m} ≤
      (Measure.uniformOfFinset (CanonicalTree.reverseState F).vertices).real
        {t | t ∈ (Forward.truncateAt (CanonicalTree.reverseState F) m).vertices} := by
  have : IsFiniteMeasure (Measure.uniformOfFinset F.forest.vertices) := by
    constructor
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    by_cases hz : F.forest.vertices.card = 0
    · simp only [hz, Nat.cast_zero, ENNReal.zero_div, ENNReal.zero_lt_top]
    · rw [ENNReal.div_self (by exact_mod_cast hz) (by simp)]
      exact ENNReal.one_lt_top
  rw [← CanonicalTree.uniform_reverse_coordinates hinj,
    map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)]
  apply ENNReal.toReal_mono
    (by exact measure_ne_top (Measure.uniformOfFinset F.forest.vertices) _)
  apply measure_mono_ae
  have hae : ∀ᵐ v ∂Measure.uniformOfFinset F.forest.vertices, v ∈ F.forest.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  filter_upwards [hae] with v hv hb
  exact reverse_birth_captures_forward_vertex ht ho hv hb

end Freezing1.SIR
