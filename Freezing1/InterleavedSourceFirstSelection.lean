module

public import Freezing1.InterleavedChainLaw

/-!
# The actual first selected transition in the alternating-chain argument

The probability of the first selected value factors into the probability
of any selection and the original transition mass. This includes starvation
and absorbing states, and does not assume independence of extracted chains.
The proof uses only finite completion harmonicity and bounded convergence.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain Filter Set
open scoped ENNReal Topology Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

def everSelected (side : Bool) : Set (ℕ → State E) :=
  {H | ∃ n : ℕ, 0 < n ∧ (H n).2.2 = side}

def firstSelectionValue (side : Bool) (z : E) : Set (ℕ → State E) :=
  {H | H ∈ everSelected side ∧ extracted H side 1 = z}

omit [MeasurableSingletonClass E] [Countable E] in
theorem measurableSet_everSelected (side : Bool) :
    MeasurableSet (everSelected (E := E) side) := by
  apply Measurable.setOf
  apply Measurable.exists
  intro n
  exact measurable_const.and (((measurable_pi_apply n).snd.snd).eq measurable_const)

theorem measurableSet_firstSelectionValue (side : Bool) (z : E) :
    MeasurableSet (firstSelectionValue side z) :=
  (measurableSet_everSelected side).inter
    (((measurable_pi_apply 1).comp (measurable_extracted side)).eq measurable_const).setOf

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem firstSelectionValue_iff (H : ℕ → State E) (side : Bool) (z : E) :
    H ∈ firstSelectionValue side z ↔
      ∃ n : ℕ, 0 < n ∧ (H n).2.2 = side ∧
        (∀ m, 0 < m → m < n → (H m).2.2 ≠ side) ∧ coordinate (H n) side = z := by
  constructor
  · rintro ⟨hsel, hz⟩
    obtain ⟨hn, hm, hbefore⟩ := nextTime_of_exists (fun n => (H n).2.2) side 0 hsel
    refine ⟨nextTime (fun n => (H n).2.2) side 0, hn, hm, hbefore, ?_⟩
    exact hz
  · rintro ⟨n, hn, hm, hbefore, hz⟩
    have hsel : H ∈ everSelected side := ⟨n, hn, hm⟩
    obtain ⟨ht, hmark, _⟩ := nextTime_of_exists (fun n => (H n).2.2) side 0 hsel
    have hle : nextTime (fun n => (H n).2.2) side 0 ≤ n :=
      Nat.find_min' (nextCandidate_exists _ _ _) (Or.inl ⟨hn, hm⟩)
    have he : nextTime (fun n => (H n).2.2) side 0 = n :=
      le_antisymm hle (le_of_not_gt (fun hh => hbefore _ ht hh hmark))
    refine ⟨hsel, ?_⟩
    change coordinate (H (nextTime (fun n => (H n).2.2) side 0)) side = z
    rwa [he]

omit [MeasurableSingletonClass E] [Countable E] in
theorem completion_observed_singleton_of_count_pos (α : Kernel E E)
    (H : ℕ → State E) (side : Bool) (y z : E) (N : ℕ)
    (hN : 0 < selectionCount (fun n => (H n).2.2) side N) :
    completion α y (observedCoordinate H side N) [z] =
      if extracted H side 1 = z then 1 else 0 := by
  rw [observedCoordinate_eq_collect, collect_eq_ofFn]
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [hr, List.ofFn_succ]
  cases side <;> simp [completion, coordinate, extracted]

omit [MeasurableSingletonClass E] [Countable E] in
theorem completion_observed_singleton_eventually (α : Kernel E E)
    (H : ℕ → State E) (side : Bool) (y z : E) :
    ∀ᶠ N in atTop, completion α y (observedCoordinate H side N) [z] =
      if H ∈ everSelected side then (if extracted H side 1 = z then 1 else 0)
      else α y {z} := by
  by_cases hs : H ∈ everSelected side
  · obtain ⟨n, hn, hm⟩ := hs
    have hs : H ∈ everSelected side := ⟨n, hn, hm⟩
    have hcount := selectionCount_strict_of_marked (fun k => (H k).2.2) side hn hm
    rw [selectionCount_zero] at hcount
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [ite_eq_left hs]
    exact completion_observed_singleton_of_count_pos α H side y z N
      (hcount.trans_le (selectionCount_mono _ _ hN))
  · have hm (n : ℕ) : (H (n + 1)).2.2 ≠ side :=
      fun hh => hs ⟨n + 1, by omega, hh⟩
    have ho (N : ℕ) : observedCoordinate H side N = [] := by
      rw [observedCoordinate_eq_collect]
      induction N with
      | zero => rfl
      | succ N ih => simp only [collect, ite_eq_right (hm N), ih]
    exact Eventually.of_forall (fun N => by
      rw [ho N, ite_eq_right hs]
      simp [completion, wordProbability])

theorem lintegral_completion_observed_singleton (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (x y z : E) (i side : Bool) (N : ℕ) :
    ∫⁻ H, completion α (coordinate (x, y, i) side) (observedCoordinate H side N) [z]
      ∂InterleavedChain.fullLaw α κ (x, y, i) = α (coordinate (x, y, i) side) {z} := by
  cases side with
  | false =>
    simpa only [pairCompletion, completion_nil_target, one_mul, wordProbability,
      mul_one, coordinate, observedCoordinate, Bool.false_eq_true, ite_false] using
      lintegral_pairCompletion_observations α κ x y i [] [z] N
  | true =>
    simpa only [pairCompletion, completion_nil_target, mul_one, wordProbability,
      coordinate, observedCoordinate, ite_true] using
      lintegral_pairCompletion_observations α κ x y i [z] [] N

end Freezing1.InterleavedChain
