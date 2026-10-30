module

import Freezing1.RecursiveTreeLaw

open MeasureTheory
open Freezing1
open scoped Classical ENNReal

-- Independently reconstructed full-state equality, rather than a shape-only comparison.
example (n : ℕ) :
    Forward.treeLaw (fun _ => true) n = RecursiveTree.law n :=
  Forward.treeLaw_allAttachment_eq_recursive n

-- Both actual vertex sets are the complete deterministic chronological label set.
example (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw (fun _ => true) n,
      s.active.card = n + 1 ∧ s.vertices.card = n + 1 := by
  filter_upwards [Forward.treeLaw_allAttachment_vertex_sets n] with s hs
  simp only [hs.1, hs.2, Finset.card_range, and_self]

-- A fresh state-independent uniform parent is a true product with the old full state.
example (n : ℕ) :
    RecursiveTree.law (n + 1) =
      ((RecursiveTree.law n).prod (RecursiveTree.uniformParentLaw n)).map
        (fun z => Forward.attach z.1 (n + 1) z.2) := by
  have hm : Measurable (fun z : Forward.State × ℕ => Forward.attach z.1 (n + 1) z.2) :=
    measurable_from_prod_countable_left fun _ => measurable_from_top
  rw [RecursiveTree.law, Measure.prod_eq_of_sfinite,
    Measure.map_bind measurable_from_top.aemeasurable hm.aemeasurable]
  congr 1
  funext s
  rw [Measure.map_map hm (measurable_of_countable _)]
  rfl

-- The printed n-vertex count is false already after the first attachment.
example : (Forward.treeLaw (fun _ => true) 1) {s | s.vertices.card = 2} = 1 := by
  apply (ae_iff_prob_eq_one measurable_from_top).mp
  filter_upwards [Forward.treeLaw_allAttachment_vertex_sets 1] with s hs
  simp only [hs.2, Finset.card_range]

-- The actual newest parent has the prescribed deterministic uniform marginal.
example (n : ℕ) :
    (Forward.treeLaw (fun _ => true) (n + 1)).map
      (fun s => s.parent (n + 1)) =
      Measure.uniformOfFinset (Finset.range (n + 1)) := by
  rw [Forward.treeLaw_allAttachment_eq_recursive, RecursiveTree.newest_parent_law]
  rfl

#print axioms RecursiveTree.uniformParentLaw
#print axioms RecursiveTree.law
#print axioms RecursiveTree.law_probability
#print axioms Forward.treeLaw_allAttachment_vertex_sets
#print axioms Forward.treeLaw_allAttachment_eq_recursive
#print axioms RecursiveTree.newest_parent_law
