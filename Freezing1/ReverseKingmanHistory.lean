module

public import Freezing1.ReverseKingman

/-!
# The entire all-positive reverse history is Kingman's jump chain

Forgetting every forest except its component partition, the actual joint
history of the all-positive reverse construction (current forest together with
all earlier forests) has exactly the law of the Kingman jump chain recorded
with its past, started from the discrete partition of the $n+1$ original
labels. The projection is of the genuine joint law, not of one-step marginals.
-/

@[expose] public section

namespace Freezing1.Kingman

open MeasureTheory
open scoped ENNReal Classical

/-- A recorded history of partitions: the current one and all earlier ones. -/
structure BlockHistory (V : Type*) where
  current : Blocks V
  past : List (Blocks V)

instance {V : Type*} : MeasurableSpace (BlockHistory V) := ⊤
instance {V : Type*} : DiscreteMeasurableSpace (BlockHistory V) := ⟨fun _ => trivial⟩

def BlockHistory.push {V : Type*} (G : BlockHistory V) (P : Blocks V) : BlockHistory V :=
  ⟨P, G.current :: G.past⟩

/-- The recorded Kingman jump chain after `k` jumps from `P₀`, with its past. -/
noncomputable def kingmanLawAfter {V : Type*} [DecidableEq V] (P₀ : Blocks V) :
    ℕ → Measure (BlockHistory V)
  | 0 => Measure.dirac ⟨P₀, []⟩
  | k + 1 => (kingmanLawAfter P₀ k).bind fun G => (mergeLaw G.current).map G.push

instance kingmanLawAfter_probability {V : Type*} [DecidableEq V] (P₀ : Blocks V) (k : ℕ) :
    IsProbabilityMeasure (kingmanLawAfter P₀ k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall fun G =>
        (Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable).mpr inferInstance)

/-- The component-partition record of an actual reverse history. -/
def blockHistory (H : ReverseHistory.History) : BlockHistory (ℕ ⊕ ℕ) :=
  ⟨Blocks.ofForest H.current, H.past.map Blocks.ofForest⟩

theorem blockHistory_push (H : ReverseHistory.History) (F : Reverse.Forest) :
    blockHistory (ReverseHistory.push H F) =
      (blockHistory H).push (Blocks.ofForest F) := rfl

/-- The all-positive schedule. -/
abbrev allPositive : SignSequence := fun _ => true

theorem activeCount_allPositive (n : ℕ) : activeCount allPositive n = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [activeCount_succ, ih]; simp

theorem extinctionTime_allPositive : extinctionTime allPositive = ⊤ :=
  (extinctionTime_eq_top_iff allPositive).mpr fun i => by
    rw [activeCount_allPositive]; positivity

theorem transitionLaw_allPositive (i : ℕ) (F : Reverse.Forest) :
    Reverse.transitionLaw allPositive i F = F.joinLaw := by
  simp [Reverse.transitionLaw]

/-- One actual reverse step of the all-positive history projects to one Kingman jump. -/
theorem map_transitionLaw_blockHistory (n k : ℕ) (hk : k < n) (H : ReverseHistory.History)
    (hvalid : Reverse.ValidAt allPositive n (n - k) H.current) :
    (ReverseHistory.transitionLaw allPositive (n - (k + 1)) H).map blockHistory =
      (mergeLaw (Blocks.ofForest H.current)).map (blockHistory H).push := by
  have hroots : 2 ≤ H.current.roots.card := by
    rw [hvalid.roots_card, activeCount_allPositive]
    omega
  rw [ReverseHistory.transitionLaw, Measure.map_map measurable_from_top measurable_from_top,
    transitionLaw_allPositive, ← joinLaw_map_blocks H.current hroots,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

/-- The entire joint law of the first `k` actual reverse steps, projected to component
partitions, is the recorded Kingman jump chain from the discrete partition of the `n+1` labels. -/
theorem map_blockHistory_lawAfter (n : ℕ) :
    ∀ k, k ≤ n → (ReverseHistory.lawAfter allPositive n k).map blockHistory =
      kingmanLawAfter (Blocks.discrete ((Finset.range (n + 1)).disjSum ∅)) k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [ReverseHistory.lawAfter, Measure.map_dirac' measurable_from_top, kingmanLawAfter]
    congr 1
    simp only [blockHistory, ReverseHistory.initial, Reverse.initial, List.map_nil,
      ofForest_isolated, activeCount_allPositive]
    simp
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hvalid := ReverseHistory.lawAfter_current_valid allPositive n k
      (by rw [extinctionTime_allPositive]; exact le_top) hkn.le
    rw [ReverseHistory.lawAfter, ite_eq_left hkn,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      kingmanLawAfter, ← ih hkn.le,
      Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [hvalid] with H hH
    exact map_transitionLaw_blockHistory n k hkn H hH

/-- Along the whole recorded Kingman chain every state is a genuine partition of the same set,
each jump removes exactly one block, and the recorded past has one entry per jump. -/
theorem ae_kingmanLawAfter_partition {V : Type*} [DecidableEq V] {s : Finset V} {P₀ : Blocks V}
    (hP₀ : P₀.IsPartitionOf s) :
    ∀ k, k < P₀.family.card →
      ∀ᵐ G ∂kingmanLawAfter P₀ k, G.current.IsPartitionOf s ∧
        G.current.family.card + k = P₀.family.card ∧ G.past.length = k := by
  intro k
  induction k with
  | zero =>
    intro _
    apply (ae_dirac_iff (by trivial)).mpr
    exact ⟨hP₀, by simp, rfl⟩
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [kingmanLawAfter, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _G, (1 : ℝ≥0∞) ∂kingmanLawAfter P₀ k := by
        apply lintegral_congr_ae
        filter_upwards [ih'] with G hG
        obtain ⟨hGp, hGc, hGl⟩ := hG
        have h2 : 2 ≤ G.current.family.card := by omega
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        rw [ae_map_iff measurable_from_top.aemeasurable (by trivial)]
        filter_upwards [mergeLaw_ae_partition hGp h2] with Q hQ
        refine ⟨hQ.1, ?_, ?_⟩
        · change Q.family.card + (k + 1) = _
          omega
        · change (G.current :: G.past).length = k + 1
          simp [hGl]
      _ = 1 := by simp

end Freezing1.Kingman
