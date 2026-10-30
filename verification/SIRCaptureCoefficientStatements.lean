module

import Freezing1.SIRCaptureCoefficientSource
import Freezing1.SIRCaptureCoefficientBirthBridge
import Freezing1.SIRCaptureCoefficientObservedPairs

open Filter MeasureTheory ProbabilityTheory
open Freezing1 Freezing1.SIR
open scoped Classical NNReal ENNReal Topology

set_option backward.isDefEq.respectTransparency false

-- Authored source reconstruction: the strict unconditional margin is proved.
example {lam : ℝ} (hlam : 1 < lam) :
    2 * (1 - 1 / lam) < fluidExtinctionTime lam :=
  twice_survival_lt_fluidExtinctionTime hlam

-- Exact source reverse clock, on the actual terminal forward tree and adaptive words.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (eps : ℝ) (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ ((signWordLaw (rate n) n (2 * n + 1)).bind fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).bind fun s =>
          (Measure.uniformOfFinset s.vertices).map
            (fun v => (s.frozenAt v).getD (captureWordExtinction n w + 1) - 1)).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} :=
  source_same_epsilon_reverse_birth_capture rate lam hlam hratio heps hepsT

-- Native actual SIR history: true membership in the earlier vertex set.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (eps : ℝ) (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ ((treeFullLaw (rate n) n).bind fun H =>
        if (H (2 * n + 1)).tree.vertices.Nonempty then
          (Measure.uniformOfFinset (H (2 * n + 1)).tree.vertices).map
            (fun v => decide (v ∈ (H ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊).tree.vertices))
        else Measure.dirac false).real {true} :=
  source_same_epsilon_forward_capture rate lam hlam hratio heps hepsT

-- Both conditional uniform samples have the same marginal and same epsilon bound.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (eps : ℝ) (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      let k := ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊
      let μ := (treeFullLaw (rate n) n).bind fun H =>
        (prefixCaptureKernel (H k) (H (2 * n + 1))).prod
          (prefixCaptureKernel (H k) (H (2 * n + 1)))
      1 - eps ≤ μ.real {z | z.1 = true} ∧ μ.real {z | z.1 = true} = μ.real {z | z.2 = true} :=
  source_same_epsilon_two_uniform_captures rate lam hlam hratio heps hepsT

-- Literal displayed two reverse-birth probabilities, conditional products on one tree.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (eps : ℝ) (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      let μ := (signWordLaw (rate n) n (2 * n + 1)).bind fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).bind fun s =>
          let ν := (Measure.uniformOfFinset s.vertices).map
            (fun v => (s.frozenAt v).getD (captureWordExtinction n w + 1) - 1)
          ν.prod ν
      1 - eps ≤ μ.real {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} ∧
        μ.real {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} =
          μ.real {z | (z.2 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} :=
  source_same_epsilon_two_reverse_births rate lam hlam hratio heps hepsT

-- All finite cutoffs, including cutoffs after extinction, use the actual recovered fraction.
example (n : ℕ) (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w) (k : ℕ) :
    (uniformVertex (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w)).real
        {v | k ≤ birthTime (captureWordExtinction n w) v} =
      ((captureVertexCount n (wordCountsAt n w (2 * n + 1)) -
        captureRecoveredCount n (wordCountsAt n w k) : ℕ) : ℝ) /
        captureVertexCount n (wordCountsAt n w (2 * n + 1)) :=
  captureWord_reverse_birth_failure n w hw k

-- Independently reconstructed root-authored clock bridge, including active/frozen vertices.
example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (Forward.treeLaw x n).bind (fun s => (Measure.uniformOfFinset s.vertices).map
        (fun v => (s.frozenAt v).getD (n + 1) - 1)) =
      (uniformVertex x n).map (birthTime n) :=
  CanonicalTree.forward_uniformReverseBirthLaw_eq_reverse x n hn

-- The clock comparison is an inequality on the same vertex, not an assumed identification.
example {x : SignSequence} {n m : ℕ} {F : ReverseStamped.Forest}
    (ht : ReverseStamped.TimesValidAt x n 0 F) (ho : ReverseStamped.TimestampOrder F)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) (hb : birthTime n v ≤ m) :
    F.edgeTime v ∈ (Forward.truncateAt (CanonicalTree.reverseState F) m).vertices :=
  reverse_birth_captures_forward_vertex ht ho hv hb

#print axioms fluidProfile_at_extinction_lt_inverse
#print axioms twice_survival_lt_fluidExtinctionTime
#print axioms exists_same_epsilon_capture_parameters
#print axioms countsFullLaw_alive_small_terminal_tendsto
#print axioms countsFullLaw_reverseMissing_same_epsilon
#print axioms captureWordExtinction_spec
#print axioms captureWord_reverse_birth_failure
#print axioms signWordLaw_reverseMissing_integral_eq
#print axioms terminalReverseBirthLaw_same_epsilon
#print axioms actualTerminalReverseBirthLaw_eq
#print axioms actualTerminalReverseBirthLaw_same_epsilon
#print axioms actualTerminalVertexBirthLaw_order
#print axioms actualTerminalVertexBirthLaw_forward_capture_same_epsilon
#print axioms prefixCaptureKernel_prod_actual
#print axioms actualPrefixCaptureLaw_true_eq
#print axioms actualPrefixCaptureLaw_same_epsilon
#print axioms actualPrefixCapturePairLaw_true_marginals
#print axioms actualPrefixCapturePairLaw_same_epsilon
#print axioms source_same_epsilon_reverse_birth_capture
#print axioms source_same_epsilon_forward_capture
#print axioms source_same_epsilon_two_uniform_captures
#print axioms reverse_birth_captures_forward_vertex
#print axioms reverse_birth_probability_le_forward_capture
#print axioms CanonicalTree.reverseState_reverseBirthClock
#print axioms CanonicalTree.forward_uniformReverseBirthLaw_eq_reverse
#print axioms CanonicalTree.forward_terminal_reverseBirthLaw
#print axioms wordObservedBirthPairKernel_probability
#print axioms actualTerminalReverseBirthPairLaw_map_fst
#print axioms actualTerminalReverseBirthPairLaw_map_snd
#print axioms actualTerminalReverseBirthPairLaw_same_epsilon
#print axioms source_same_epsilon_two_reverse_births
