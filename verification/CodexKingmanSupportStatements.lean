module

import Freezing1.ReverseKingmanHistory
import Freezing1.ForwardStateDecodingUnique

open Freezing1 MeasureTheory
open scoped Classical ENNReal

noncomputable section

example {V : Type*} [DecidableEq V] (base : Finset V) (P : Kingman.Blocks V)
    (h : P.IsPartitionOf base) (A B : Finset V)
    (hA : A ∈ P.family) (hB : B ∈ P.family) (hne : A ≠ B) :
    Kingman.mergeLaw P {P.merge A B} =
      ((P.family.card.choose 2 : ℕ) : ℝ≥0∞)⁻¹ :=
  Kingman.mergeLaw_unordered h hA hB hne

example (F : RootedForest (ℕ ⊕ ℕ)) (h : 2 ≤ F.roots.card) :
    F.joinLaw.map Kingman.Blocks.ofForest = Kingman.mergeLaw (Kingman.Blocks.ofForest F) :=
  Kingman.joinLaw_map_blocks F h

-- The endpoint includes the complete recorded past, so this checks the joint
-- law of every partition in the finite coalescent history.
example (n : ℕ) :
    (ReverseHistory.fullLaw (fun _ => true) n).map
        (fun H => (⟨Kingman.Blocks.ofForest H.current,
          H.past.map Kingman.Blocks.ofForest⟩ : Kingman.BlockHistory (ℕ ⊕ ℕ))) =
      Kingman.kingmanLawAfter
        (Kingman.Blocks.discrete ((Finset.range (n + 1)).disjSum ∅)) n :=
  Kingman.map_blockHistory_lawAfter n n le_rfl

example (N : ℕ) (s : Forward.State) :
    (∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ (Forward.treeLaw x N) {s} ≠ 0) ↔
      ∃ q : BinaryBijection.UnorderedIncreasingClass s.active.card s.vertices.card
        (Finset.Icc 1 N), q.val.IsEncoding s :=
  Forward.exists_support_iff_exists_class

-- No state or legal history is assumed for the intrinsic source object.
example (k n : ℕ)
    (q : BinaryBijection.UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃ s : Forward.State, q.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k :=
  BinaryBijection.UnorderedIncreasingClass.exists_forward_support q

example (k n N : ℕ) :
    BinaryBijection.UnorderedIncreasingClass k n (Finset.Icc 1 N) ≃
      {s : Forward.State // Forward.IncreasingLabelled N s ∧
        s.active.card = k ∧ s.vertices.card = n} :=
  Forward.intrinsicClassEquiv k n N

example (N : ℕ) (s : Forward.State) (h : Forward.IncreasingLabelled N s) :
    ∃! q : BinaryBijection.UnorderedIncreasingClass s.active.card s.vertices.card
      (Finset.Icc 1 N), q.val.IsEncoding s := h.existsUnique_class

example (x : SignSequence) (N : ℕ) (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂Forward.treeLaw x N,
      ∃! q : BinaryBijection.UnorderedIncreasingClass s.active.card s.vertices.card
        (Finset.Icc 1 N), q.val.IsEncoding s :=
  Forward.treeLaw_ae_existsUnique_class x N hN

#print axioms Freezing1.Kingman.mergeLaw_unordered
#print axioms Freezing1.Kingman.joinLaw_map_blocks
#print axioms Freezing1.Kingman.map_blockHistory_lawAfter
#print axioms Freezing1.Forward.increasingLabelled_iff_exists_support
#print axioms Freezing1.BinaryBijection.UnorderedIncreasingClass.exists_forward_support
#print axioms Freezing1.Forward.exists_support_iff_exists_class
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.unorderedEq_of_encoding
#print axioms Freezing1.Forward.intrinsicClassEquiv
#print axioms Freezing1.Forward.treeLaw_ae_existsUnique_class
