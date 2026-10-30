module

import Freezing1.ReverseKingmanHistory

open MeasureTheory
open Freezing1 Freezing1.Kingman
open scoped Classical ENNReal

/-! Authored exact-type reconstruction for A07: the all-positive reverse forest and
Kingman's jump chain on set partitions (no holding times). -/

-- The Kingman jump: every unordered pair of distinct blocks of a partition with m blocks
-- is merged with probability 1 / choose(m, 2).
example {V : Type*} [DecidableEq V] {s : Finset V} {P : Blocks V} (hP : P.IsPartitionOf s)
    {A B : Finset V} (hA : A ∈ P.family) (hB : B ∈ P.family) (hAB : A ≠ B) :
    mergeLaw P {P.merge A B} = ((P.family.card.choose 2 : ℕ) : ℝ≥0∞)⁻¹ :=
  mergeLaw_unordered hP hA hB hAB

-- The jump chain stays on partitions of the same set and loses exactly one block per jump.
example {V : Type*} [DecidableEq V] {s : Finset V} {P : Blocks V} (hP : P.IsPartitionOf s)
    (h2 : 2 ≤ P.family.card) :
    ∀ᵐ Q ∂mergeLaw P, Q.IsPartitionOf s ∧ Q.family.card + 1 = P.family.card :=
  mergeLaw_ae_partition hP h2

-- The component family of every actual rooted forest is a genuine partition of its vertices.
example {V : Type*} [DecidableEq V] (F : RootedForest V) :
    (Blocks.ofForest F).IsPartitionOf F.vertices :=
  ofForest_isPartitionOf F

-- One actual uniform ordered-root join of a forest projects to one Kingman merge.
example {V : Type*} [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] (F : RootedForest V) (hF : 2 ≤ F.roots.card) :
    F.joinLaw.map Blocks.ofForest = mergeLaw (Blocks.ofForest F) :=
  joinLaw_map_blocks F hF

-- Entire joint history of the first k steps of the all-positive reverse construction.
example (n k : ℕ) (hk : k ≤ n) :
    (ReverseHistory.lawAfter (fun _ => true) n k).map blockHistory =
      kingmanLawAfter (Blocks.discrete ((Finset.range (n + 1)).disjSum ∅)) k :=
  map_blockHistory_lawAfter n k hk

-- The start is the discrete partition of the n+1 original labels.
example (n : ℕ) :
    (Blocks.discrete ((Finset.range (n + 1)).disjSum (∅ : Finset ℕ))).family.card = n + 1 := by
  rw [Blocks.discrete_card, Finset.card_disjSum]; simp

-- After n jumps there is exactly one block, and the recorded past has n entries.
example (n : ℕ) :
    ∀ᵐ G ∂kingmanLawAfter (Blocks.discrete ((Finset.range (n + 1)).disjSum (∅ : Finset ℕ))) n,
      G.current.family.card = 1 ∧ G.past.length = n := by
  have hP := Blocks.discrete_isPartitionOf ((Finset.range (n + 1)).disjSum (∅ : Finset ℕ))
  have hc : (Blocks.discrete ((Finset.range (n + 1)).disjSum (∅ : Finset ℕ))).family.card
      = n + 1 := by
    rw [Blocks.discrete_card, Finset.card_disjSum]; simp
  filter_upwards [ae_kingmanLawAfter_partition hP n (by omega)] with G hG
  exact ⟨by omega, hG.2.2⟩

#print axioms Freezing1.Kingman.mergeLaw_unordered
#print axioms Freezing1.Kingman.mergeLaw_ae_partition
#print axioms Freezing1.Kingman.ofForest_isPartitionOf
#print axioms Freezing1.Kingman.joinLaw_map_blocks
#print axioms Freezing1.Kingman.map_blockHistory_lawAfter
#print axioms Freezing1.Kingman.ae_kingmanLawAfter_partition
