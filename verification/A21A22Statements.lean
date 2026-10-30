module

import Freezing1.ForwardFreezingDegrees
import Freezing1.ForwardSelectionSourceChecks

/-!
Author-created expanded statement and axiom probe for source A21/A22.
Independent source review is recorded separately by the integrating agent.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (H : History)
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) :
    (∃ T : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T)) ↔
      ∀ r b, r ∈ (H b).vertices →
        ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r :=
  exists_local_limit_iff_all_degrees_stabilize hv hl

example (x : SignSequence) (hτ : extinctionTime x = ⊤) (r : ℕ)
    (F : Finset ℕ) (hF : ∀ i ∈ F, r < i ∧ x i = true) (ε : ℕ → Bool) :
    (fullLaw x) (survivesForever r r ∩
      {H | ∀ i ∈ F, ((H i).parent i = r ↔ ε i = true)}) =
      (fullLaw x) (survivesForever r r) *
        ∏ i ∈ F, ENNReal.ofReal
          (if ε i then 1 / (activeCount x (i - 1) : ℝ)
            else 1 - 1 / (activeCount x (i - 1) : ℝ)) := by
  calc
    _ = (fullLaw x) (survivesForever r r) *
        ∏ i ∈ F, ENNReal.ofReal (attachmentPatternFactor x F ε i) :=
      fullLaw_survival_attachmentPattern x hτ r hF ε
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp only [attachmentPatternFactor, hi, ↓reduceIte]

example (x : SignSequence) (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) :
    iIndepSet (postBirthAttachment x r) ((fullLaw x)[|survivesForever r r]) :=
  conditional_postBirthAttachment_iIndepSet x hτ r hp

example (x : SignSequence) (hτ : extinctionTime x = ⊤) (r : ℕ) :
    ∀ᵐ H ∂(fullLaw x).restrict (survivesForever r r),
      Tendsto (fun n => ((H n).vertices.filter fun v => (H n).graph.Adj r v).card)
        atTop atTop :=
  restrict_survival_vertexDegree_tendsto_atTop x hτ r

example (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x,
      (∃ T : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T)) ↔
      (∀ r b, r ∈ (H b).vertices →
        ∃ a j, ∀ n ≥ a, (H n).frozenAt r = some j) :=
  fullLaw_local_limit_iff_all_eventually_frozen_all_schedules x

example : (treeLaw selectionIndexSchedule 2).real {s | 0 ∈ s.active} ≠
    ∏ i ∈ Finset.Ioc 0 2,
      (if selectionIndexSchedule i then (1 : ℝ) else 1 - 1 / activeCount selectionIndexSchedule i) :=
  selectionIndexSchedule_refutes_printed_product

example : (fullLaw selectionIndexSchedule).real (survivesForever 0 0) = 1 / 2 :=
  selectionIndexSchedule_actual_never_frozen_probability

example : ∀ p ∈ (attach initial 1 0).active,
    vertexDegree (attach (attach initial 1 0) 2 p) 2 =
      vertexDegree (attach initial 1 0) 2 + 1 ∧
    (1 : ℝ) ≠ 1 / ((attach initial 1 0).active.card : ℝ) :=
  birth_step_not_selection_of_newborn

#print axioms exists_local_limit_iff_all_degrees_stabilize
#print axioms fullLaw_local_limit_iff_all_degrees_stabilize
#print axioms degree_constant_after_freezing
#print axioms old_record_eventually_constant
#print axioms fullLaw_survival_attachmentPattern
#print axioms conditional_postBirthAttachment_iIndepSet
#print axioms conditional_infinitely_many_attachments
#print axioms conditional_vertexDegree_tendsto_atTop
#print axioms restrict_survival_vertexDegree_tendsto_atTop
#print axioms fullLaw_degrees_stabilize_iff_all_eventually_frozen
#print axioms fullLaw_local_limit_iff_all_eventually_frozen_all_schedules
#print axioms selectionIndexSchedule_refutes_printed_product
#print axioms selectionIndexSchedule_actual_never_frozen_probability
#print axioms birth_step_not_selection_of_newborn
