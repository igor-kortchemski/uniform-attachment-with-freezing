module

public import Freezing1.InterleavedWordExtraction

/-!
# From extracted clocks to the actual global clock

No divergence of the selection count is required. If one side is selected
only finitely often, the source extraction repeats its last selected time;
the actual coordinate stays there too. Thus convergence along the exact
extracted path transfers to global time, including absorbing coordinates.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Classical

variable {E : Type*}

theorem coordinate_eq_extracted_selectionCount (H : ℕ → State E)
    (h : ∀ n, MovesOnlySelected (H n) (H (n + 1))) (side : Bool) (n : ℕ) :
    coordinate (H n) side =
      extracted H side (selectionCount (fun i => (H i).2.2) side n) := by
  have hh := observedCoordinate_last H h side n
  rw [observedCoordinate_eq_collect, getLastD_collect] at hh
  simpa only [coordinate, extracted] using hh.symm

/-- Once the kth selection time is in the past, the global coordinate is
an extracted state of rank at least k. Fallback is handled exactly. -/
theorem coordinate_eq_extracted_tail (H : ℕ → State E)
    (h : ∀ n, MovesOnlySelected (H n) (H (n + 1))) (side : Bool) {k n : ℕ}
    (ht : selectedTime (fun i => (H i).2.2) side k ≤ n) :
    ∃ j, k ≤ j ∧ coordinate (H n) side = extracted H side j := by
  let marks : ℕ → Bool := fun i => (H i).2.2
  let c := selectionCount marks side n
  by_cases hk : k ≤ c
  · exact ⟨c, hk, coordinate_eq_extracted_selectionCount H h side n⟩
  · have hb : ∀ m, selectionCount marks side m ≤ c :=
      (count_ge_or_globally_bounded marks side ht).resolve_left hk
    have hrank := selectedTime_rank marks side (k := c) (N := n) le_rfl
    have hnext : nextTime marks side (selectedTime marks side c) = selectedTime marks side c :=
      nextTime_of_count_bounded marks side _ (fun m => by rw [hrank.2]; exact hb m)
    have htime : selectedTime marks side k = selectedTime marks side c :=
      selectedTime_stable marks side rfl hnext (by omega)
    refine ⟨k, le_rfl, ?_⟩
    rw [coordinate_eq_extracted_selectionCount H h side n]
    change extracted H side c = extracted H side k
    exact congrArg (fun t => coordinate (H t) side) htime.symm

theorem tendsto_coordinate_of_extracted {Y : Type*} [TopologicalSpace Y]
    (H : ℕ → State E) (h : ∀ n, MovesOnlySelected (H n) (H (n + 1)))
    (side : Bool) (f : E → Y) {L : Y}
    (hc : Tendsto (fun k => f (extracted H side k)) atTop (𝓝 L)) :
    Tendsto (fun n => f (coordinate (H n) side)) atTop (𝓝 L) := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hc.eventually hU)
  apply eventually_atTop.mpr
  refine ⟨selectedTime (fun i => (H i).2.2) side k, ?_⟩
  intro n hn
  obtain ⟨j, hj, he⟩ := coordinate_eq_extracted_tail H h side hn
  change f (coordinate (H n) side) ∈ U
  rw [he]
  exact hk j hj

variable [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Applied to the actual interleaved path law, coordinate stasis follows
from the kernel. Fairness is not needed for this transfer. -/
theorem ae_tendsto_coordinate_of_extracted {Y : Type*} [TopologicalSpace Y]
    (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval) (s : State E)
    (side : Bool) (f : E → Y) (L : (ℕ → State E) → Y)
    (hc : ∀ᵐ H ∂fullLaw α κ s,
      Tendsto (fun k => f (extracted H side k)) atTop (𝓝 (L H))) :
    ∀ᵐ H ∂fullLaw α κ s,
      Tendsto (fun n => f (coordinate (H n) side)) atTop (𝓝 (L H)) := by
  filter_upwards [hc, fullLaw_movesOnlySelected α κ s] with H hH hm
  exact tendsto_coordinate_of_extracted H hm side f hH

end Freezing1.InterleavedChain
