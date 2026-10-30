module

import Freezing1.SIRCaptureCoefficientObserved
import Freezing1.SIRCaptureCoefficientNative
import Freezing1.SIRCaptureCoefficientObservedPairs

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Freezing1.SIR

example (lam : ℝ) (hlam : 1 < lam) :
    2 * (1 - 1 / lam) < fluidExtinctionTime lam :=
  twice_survival_lt_fluidExtinctionTime hlam

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < fluidExtinctionTime lam) :
    ∀ᶠ n in atTop, (∫ H, reverseMissingFraction n
      ⌊(n : ℝ) * (fluidExtinctionTime lam - ε)⌋₊ H ∂countsFullLaw (rate n) n) < ε :=
  countsFullLaw_reverseMissing_same_epsilon rate lam hlam hr hε hεT

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < fluidExtinctionTime lam) :
    ∀ᶠ n in atTop, 1 - ε ≤
      ((signWordLaw (rate n) n (2 * n + 1)).bind fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).bind fun s =>
          (Measure.uniformOfFinset s.vertices).map (fun v =>
            (s.frozenAt v).getD (captureWordExtinction n w + 1) - 1)).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - ε)} :=
  actualTerminalReverseBirthLaw_same_epsilon rate lam hlam hr hε hεT

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < fluidExtinctionTime lam) :
    ∀ᶠ n in atTop, 1 - ε ≤
      ((treeFullLaw (rate n) n).bind fun H =>
        if (H (2 * n + 1)).tree.vertices.Nonempty then
          (Measure.uniformOfFinset (H (2 * n + 1)).tree.vertices).map
            (fun v => decide (v ∈ (H ⌊(n : ℝ) * (fluidExtinctionTime lam - ε)⌋₊).tree.vertices))
        else Measure.dirac false).real {true} :=
  actualPrefixCaptureLaw_same_epsilon rate lam hlam hr hε hεT

example (r : ℝ≥0) (n k : ℕ) :
    (actualPrefixCapturePairLaw r n k).map Prod.fst = actualPrefixCaptureLaw r n k ∧
      (actualPrefixCapturePairLaw r n k).map Prod.snd = actualPrefixCaptureLaw r n k :=
  ⟨actualPrefixCapturePairLaw_map_fst r n k, actualPrefixCapturePairLaw_map_snd r n k⟩

example (before last : TreeState) (h : last.tree.vertices.Nonempty) :
    (prefixCaptureKernel before last).prod (prefixCaptureKernel before last) =
      ((Measure.uniformOfFinset last.tree.vertices).prod
        (Measure.uniformOfFinset last.tree.vertices)).map
          (fun z => (decide (z.1 ∈ before.tree.vertices), decide (z.2 ∈ before.tree.vertices))) :=
  prefixCaptureKernel_prod_actual h

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (h : (1 : ℝ) < lam)
    (hr : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / n)) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < fluidExtinctionTime lam) :
    ∀ᶠ n in atTop,
      1 - ε ≤ (actualTerminalReverseBirthPairLaw (rate n) n).real
        {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - ε)} ∧
      (actualTerminalReverseBirthPairLaw (rate n) n).real
        {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - ε)} =
      (actualTerminalReverseBirthPairLaw (rate n) n).real
        {z | (z.2 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - ε)} :=
  source_same_epsilon_two_reverse_births rate lam h hr hε hεT

#print axioms twice_survival_lt_fluidExtinctionTime
#print axioms exists_same_epsilon_capture_parameters
#print axioms countsFullLaw_alive_small_terminal_tendsto
#print axioms countsFullLaw_reverseMissing_same_epsilon
#print axioms captureWord_reverse_birth_failure
#print axioms terminalReverseBirthLaw_same_epsilon
#print axioms actualTerminalReverseBirthLaw_eq
#print axioms actualTerminalVertexBirthLaw_order
#print axioms actualPrefixCaptureLaw_true_eq
#print axioms actualPrefixCaptureLaw_same_epsilon
#print axioms prefixCaptureKernel_prod_actual
#print axioms actualPrefixCapturePairLaw_same_epsilon
#print axioms actualTerminalReverseBirthPairLaw_map_fst
#print axioms actualTerminalReverseBirthPairLaw_map_snd
#print axioms source_same_epsilon_two_reverse_births

end Freezing1.SIR
