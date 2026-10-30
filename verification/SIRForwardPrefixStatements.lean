module

public import Freezing1.SIRPhysicalForwardPrefixBridge

/-! Independent statement probes for root-authored A66 prefix adapters. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

example {k : ℕ} (w : Fin k → Bool) :
    ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
      (Preorder.frestrictLe k)).map (ForwardAnnealed.planePrefix k) = planePrefixWordLaw w :=
  originalForwardPrefix_map_tree w

example (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree))) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map
            (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))) :=
  treeFullLaw_countsPrefix_original_treePrefix_word_mixture rate n k

/-- The two prefix coordinates describe the same active population. This
makes the extinction index a function of the same jointly identified data. -/
theorem mixed_counts_match_tree_active (rate : ℝ≥0) (n k : ℕ) :
    ∀ᵐ z ∂(signWordLaw rate n k).bind (fun w =>
      ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
        (Preorder.frestrictLe k)).map
          (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))),
      ∀ i : Finset.Iic k, (z.1 i).infectious = (z.2 i).active.card := by
  rw [← treeFullLaw_countsPrefix_original_treePrefix_word_mixture rate n k]
  have hm : Measurable (fun H : ℕ → TreeState =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree))) :=
    (measurable_of_countable (fun P : Prefix (E := TreeState) k =>
      ((fun i => (P i).counts), (fun i => (P i).tree)))).comp
        (Preorder.measurable_frestrictLe k)
  apply (ae_map_iff hm.aemeasurable (Set.to_countable _).measurableSet).mpr
  exact Filter.Eventually.of_forall fun _ _ => rfl

/-- Every index read from the count prefix observes its tree at that same
index. In particular this applies to the first zero index at horizon 2n+1. -/
theorem bounded_count_index_observation (rate : ℝ≥0) (n k : ℕ)
    (a : Prefix (E := Counts) k → Finset.Iic k) :
    ((treeFullLaw rate n).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree)))).map
          (fun z => (z.1 (a z.1), z.2 (a z.1))) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map (fun P =>
            (countsPrefixWord n w (a (countsPrefixWord n w)),
              ForwardAnnealed.planePrefix k P (a (countsPrefixWord n w))))) := by
  rw [treeFullLaw_countsPrefix_original_treePrefix_word_mixture,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall fun w => by
    have hF : Measurable (fun z : Prefix (E := Counts) k × Prefix (E := PlaneForward.State) k =>
        (z.1 (a z.1), z.2 (a z.1))) := measurable_of_countable _
    have hP : Measurable (fun P : Prefix (E := Forward.State) k =>
        (countsPrefixWord n w, ForwardAnnealed.planePrefix k P)) :=
      measurable_const.prodMk (ForwardAnnealed.measurable_planePrefix k)
    exact Measure.map_map hF hP

example {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (rate : ℝ≥0) (hr : 0 < rate)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) rate)
    (k : ℕ) :
    (physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree))) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map
            (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))) :=
  PoissonSIRData.countsPrefix_original_treePrefix_word_mixture
    ⟨hX, hindep, hrecovery, hcontact⟩ hr k

#print axioms conditionalTreePrefixWordLaw_map_tree
#print axioms originalForwardPrefix_map_tree
#print axioms treeFullLaw_original_treePrefix_word_mixture
#print axioms treeFullLaw_countsPrefix_original_treePrefix_word_mixture
#print axioms PoissonSIRData.countsPrefix_original_treePrefix_word_mixture
#print axioms mixed_counts_match_tree_active
#print axioms bounded_count_index_observation

end Freezing1.SIR
