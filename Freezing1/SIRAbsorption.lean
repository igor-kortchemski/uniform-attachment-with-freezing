module

public import Freezing1.SIRTreeLaw
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Finite extinction of the genuine embedded infection-tree chain

The full count-path identity supplies extinction by event 2n+1, and the
actual tree kernel then holds the entire state. The terminal tree law is
therefore evaluated at a proved deterministic terminal horizon.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

theorem treeKernel_absorbed (rate : ℝ≥0) {z : TreeState} (hz : z.tree.active = ∅) :
    treeKernel rate z = Measure.dirac z := by
  change (bernoulliMeasure true false (infectionProbability rate z.susceptible)).bind
    (signedTreeLaw z) = _
  have he : signedTreeLaw z = fun _ => Measure.dirac z := by
    funext sign
    exact signedTreeLaw_absorbed hz sign
  rw [he, Measure.bind_const, measure_univ, one_smul]

theorem treeFullLaw_held (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n, ∀ k,
      (H k).tree.active = ∅ → H (k + 1) = H k := by
  apply CountableMarkovChain.fullLaw_steps (treeKernel rate) (initialTreeState n)
    (fun z w => z.tree.active = ∅ → w = z)
  intro z
  by_cases hz : z.tree.active = ∅
  · rw [treeKernel_absorbed rate hz]
    simp
  · exact Filter.Eventually.of_forall fun w hh => (hz hh).elim

theorem treeFullLaw_absorbed_by (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n,
      (H (2 * n + 1)).tree.active = ∅ ∧
        ∀ k ≥ 2 * n + 1, H k = H (2 * n + 1) := by
  have hcounts : ∀ᵐ C ∂countsFullLaw rate n,
      (C (2 * n + 1)).infectious = 0 :=
    (countsFullLaw_absorbed_by rate n).mono fun _ h => h.1
  rw [← map_treeFullLaw_counts rate n] at hcounts
  have hmap : Measurable (fun H : ℕ → TreeState => fun k => (H k).counts) :=
    Measurable.of_eval fun k => (measurable_of_countable TreeState.counts).comp
      (measurable_pi_apply k)
  have hc := ae_of_ae_map hmap.aemeasurable hcounts
  filter_upwards [hc, treeFullLaw_held rate n] with H hz hh
  have he : (H (2 * n + 1)).tree.active = ∅ := Finset.card_eq_zero.mp hz
  refine ⟨he, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [hh k (by rw [ih]; exact he), ih]

/-- The terminal law of the actual embedded infection-tree model. -/
noncomputable def embeddedTerminalTreeLaw (rate : ℝ≥0) (n : ℕ) :
    ProbabilityMeasure PlaneTree.Tree :=
  ProbabilityMeasure.map
    (⟨treeFullLaw rate n, inferInstance⟩ : ProbabilityMeasure (ℕ → TreeState))
    (fun H : ℕ → TreeState => PlaneForward.shape (H (2 * n + 1)).tree)

theorem treeFullLaw_terminal_population (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n,
      (H (2 * n + 1)).susceptible + (H (2 * n + 1)).tree.vertices.card = n + 1 ∧
      (H (2 * n + 1)).tree.active = ∅ := by
  filter_upwards [treeFullLaw_valid rate n, treeFullLaw_absorbed_by rate n]
    with H hv ha
  exact ⟨(hv _).2, ha.1⟩

end Freezing1.SIR
