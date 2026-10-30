module

public import Freezing1.PlaneGraftTransition
public import Freezing1.PlaneStateUpdates
public import Freezing1.CountablePathLaw
public import Freezing1.CountableMarkovShift
public import Freezing1.CountableMarkovObservations

/-!
# Grafting the entire interleaved history

Every finite history law is transported through the actual transition
kernel. The first coordinate remains a valid rooted state along the source
history, which discharges the root condition in kernel commutation.
-/

@[expose] public section

namespace Freezing1.CountableMarkovChain

open MeasureTheory ProbabilityTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]

private def transportPrefix (f : A → B) (n : ℕ) (H : Prefix (E := A) n) :
    Prefix (E := B) n := fun i => f (H i)

omit [MeasurableSingletonClass B] [Countable B] in
private theorem measurable_transportPrefix (f : A → B) (n : ℕ) :
    Measurable (transportPrefix f n) :=
  Measurable.of_eval fun i => (measurable_of_countable f).comp (measurable_pi_apply i)

theorem map_fullLaw_of_ae_intertwining (α : Kernel A A) [IsMarkovKernel α]
    (β : Kernel B B) [IsMarkovKernel β] (f : A → B) (x : A)
    (h : ∀ n, ∀ᵐ H ∂fullLaw α x, (α (H n)).map f = β (f (H n))) :
    (fullLaw α x).map (fun H n => f (H n)) = fullLaw β (f x) := by
  have hprefix : ∀ n, ((fullLaw α x).map (Preorder.frestrictLe n)).map
      (transportPrefix f n) = (fullLaw β (f x)).map (Preorder.frestrictLe n) := by
    intro n
    rw [map_prefix, map_prefix]
    induction n with
    | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_transportPrefix f 0),
        Kernel.partialTraj_self, Kernel.id_apply]
      rfl
    | succ n ih =>
      rw [partialTraj_successor α (Nat.zero_le n),
        partialTraj_successor β (Nat.zero_le n), Measure.map_bind
          (measurable_appended_transition α n).aemeasurable
          (measurable_transportPrefix f (n + 1)).aemeasurable,
        ← ih, Measure.bind_map (measurable_transportPrefix f n).aemeasurable
          (measurable_appended_transition β n).aemeasurable]
      have hint : ∀ᵐ H ∂Kernel.partialTraj (X := fun _ => A) (historyKernel α)
          0 n (fun _ => x),
          (α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map f =
            β (f (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) := by
        rw [← map_prefix]
        apply (ae_map_iff (Preorder.measurable_frestrictLe n).aemeasurable
          (Set.to_countable _).measurableSet).mpr
        exact h n
      apply Measure.bind_congr_right
      filter_upwards [hint] with H hH
      rw [Measure.map_map (measurable_transportPrefix f (n + 1))
        (measurable_prefixAppend_right H)]
      have hfun : transportPrefix f (n + 1) ∘ prefixAppend H =
          prefixAppend (transportPrefix f n H) ∘ f := by
        funext z i
        by_cases hi : i.val ≤ n
        · simp only [transportPrefix, Function.comp_def, prefixAppend, dite_eq_left hi]
        · simp only [transportPrefix, Function.comp_def, prefixAppend, dite_eq_right hi]
      rw [hfun, ← Measure.map_map (measurable_prefixAppend_right (transportPrefix f n H))
        (measurable_of_countable f), hH]
      rfl
  apply CountablePathLaw.eq_of_prefix_map_eq
  intro n
  rw [Measure.map_map (Preorder.measurable_frestrictLe n) (by fun_prop),
    ← hprefix n, Measure.map_map (measurable_transportPrefix f n)
      (Preorder.measurable_frestrictLe n)]
  rfl

end Freezing1.CountableMarkovChain

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped Classical

private theorem transition_valid (p : unitInterval) {s : State} (hs : Valid s) :
    ∀ᵐ r ∂transition p s, Valid r := by
  apply transition_ae
  · intro _
    exact hs
  · intro sign u _
    exact hs.step sign u

theorem interleaved_fullLaw_valid (p : unitInterval) :
    ∀ᵐ H ∂InterleavedChain.fullLaw (transition p) selectionParameter
      (initial, initial, true), ∀ n, Valid (H n).1 ∧ Valid (H n).2.1 := by
  let P : InterleavedChain.State State → Prop := fun s => Valid s.1 ∧ Valid s.2.1
  have hstep : ∀ s, ∀ᵐ t ∂InterleavedChain.transition (transition p) selectionParameter s,
      P s → P t := by
    intro s
    by_cases hs : P s
    · change ∀ᵐ t ∂unitInterval.toNNReal (selectionParameter (s.1, s.2.1)) •
          ((transition p s.1).map (fun z => (z, s.2.1, true))) +
        unitInterval.toNNReal (unitInterval.symm (selectionParameter (s.1, s.2.1))) •
          ((transition p s.2.1).map (fun z => (s.1, z, false))), P s → P t
      rw [ae_add_measure_iff]
      constructor
      · apply Measure.ae_smul_measure
        apply (ae_map_iff (measurable_of_countable _).aemeasurable
          (Set.to_countable _).measurableSet).mpr
        filter_upwards [transition_valid p hs.1] with z hz
        exact fun _ => ⟨hz, hs.2⟩
      · apply Measure.ae_smul_measure
        apply (ae_map_iff (measurable_of_countable _).aemeasurable
          (Set.to_countable _).measurableSet).mpr
        filter_upwards [transition_valid p hs.2] with z hz
        exact fun _ => ⟨hs.1, hz⟩
    · exact Filter.Eventually.of_forall fun _ h => (hs h).elim
  filter_upwards [CountableMarkovChain.fullLaw_initial
    (InterleavedChain.transition (transition p) selectionParameter) (initial, initial, true),
    CountableMarkovChain.fullLaw_steps
      (InterleavedChain.transition (transition p) selectionParameter) (initial, initial, true)
      (fun s t => P s → P t) hstep] with H h0 hs
  intro n
  induction n with
  | zero => simpa only [h0, P] using And.intro initial_valid initial_valid
  | succ n ih => exact hs n ih

theorem map_interleaved_fullLaw_graft (p : unitInterval) :
    (InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
      (fun H n => graft (H n).1 (H n).2.1) = fullLaw p (graft initial initial) := by
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
    (InterleavedChain.transition (transition p) selectionParameter) (transition p)
    (fun s => graft s.1 s.2.1) (initial, initial, true)
  intro n
  filter_upwards [interleaved_fullLaw_valid p] with H hH
  exact map_interleaved_transition_graft p (hH n).1.root_mem (H n).2.1 (H n).2.2

end Freezing1.PlaneForward
