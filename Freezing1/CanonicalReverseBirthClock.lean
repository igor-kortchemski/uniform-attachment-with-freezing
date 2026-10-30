module

public import Freezing1.CanonicalUniformSampling
public import Freezing1.ForwardAbsorption

/-! The reverse birth clock on actual forward vertices is the freezing label minus one.
Its uniform law is transported by the canonical bijection; infection time is a different clock. -/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical ENNReal

namespace Forward

/-- Active vertices are born at the current reverse horizon. Frozen vertices
are born one step before their displayed freezing label. -/
def reverseBirthClock (n : ℕ) (s : State) (v : ℕ) : ℕ :=
  (s.frozenAt v).getD (n + 1) - 1

noncomputable def uniformReverseBirthLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).bind fun s =>
    (Measure.uniformOfFinset s.vertices).map (reverseBirthClock n s)

end Forward

namespace CanonicalTree

theorem reverseState_reverseBirthClock {F : ReverseStamped.Forest} (n : ℕ)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) :
    Forward.reverseBirthClock n (reverseState F) (F.edgeTime v) = birthTime n v := by
  unfold Forward.reverseBirthClock
  rw [(reverseState_vertex_data hinj hv).2.2]
  cases v <;> simp [reverseLabel, birthTime]

theorem uniform_reverse_birthClock {F : ReverseStamped.Forest} (n : ℕ)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    (Measure.uniformOfFinset (reverseState F).vertices).map
        (Forward.reverseBirthClock n (reverseState F)) =
      (Measure.uniformOfFinset F.forest.vertices).map (birthTime n) := by
  rw [← uniform_reverse_coordinates hinj, Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  have hae : ∀ᵐ v ∂Measure.uniformOfFinset F.forest.vertices, v ∈ F.forest.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  filter_upwards [hae] with v hv
  exact reverseState_reverseBirthClock n hinj hv

/-- The actual forward tree and the actual reverse label model give exactly
the same entire uniform birth-clock law, including the extinction endpoint. -/
theorem forward_uniformReverseBirthLaw_eq_reverse (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    Forward.uniformReverseBirthLaw x n = (uniformVertex x n).map (birthTime n) := by
  unfold Forward.uniformReverseBirthLaw
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn, reverseStateLaw,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  trans (ReverseStamped.treeLaw x n).bind fun F =>
    (Measure.uniformOfFinset F.forest.vertices).map (birthTime n)
  · apply Measure.bind_congr_right
    filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn] with F hF
    exact uniform_reverse_birthClock n hF.1
  · trans (Reverse.treeLaw x n).bind fun F =>
      (Measure.uniformOfFinset F.vertices).map (birthTime n)
    · rw [← ReverseStamped.map_treeLaw x n,
        Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    · calc
        _ = (Reverse.uniformVertexLaw x n).map (birthTime n) :=
          (Measure.map_bind (m := Reverse.treeLaw x n)
            (f := fun F => Measure.uniformOfFinset F.vertices) (g := birthTime n)
            measurable_from_top.aemeasurable (measurable_of_countable _).aemeasurable).symm
        _ = _ := by rw [Reverse.uniformVertexLaw_eq x n hn]

/-- The terminal forward tree can be observed after absorption without changing
the freezing-clock law. The clock horizon remains the true extinction index. -/
theorem forward_terminal_reverseBirthLaw {x : SignSequence} {n : ℕ}
    (ht : extinctionTime x = n) (k : ℕ) :
    (Forward.treeLaw x (n + k)).bind (fun s =>
      (Measure.uniformOfFinset s.vertices).map (Forward.reverseBirthClock n s)) =
        (uniformVertex x n).map (birthTime n) := by
  rw [Forward.treeLaw_constant_after_extinction ht k]
  exact forward_uniformReverseBirthLaw_eq_reverse x n ht.symm.le

end CanonicalTree
end Freezing1
