module

public import Freezing1.Extinction
public import Freezing1.BirthTime
public import Freezing1.HeightScale
public import Freezing1.RateFunction

/-!
# Verified paper results and explicit model boundaries

This is the reader-facing interface for the currently proved supporting results.
The Introduction's probability limit theorems remain open. In particular,
`uniform_birthTime_lt_of_le_extinctionTime` is a law on the deterministic labels;
the forest construction and its characterization of birth time remain separate
obligations. No unproved paper statement is introduced as a Lean axiom.
-/

@[expose] public section

namespace Freezing1

/-- Lemma `lemme minoration h_n^+`, with the paper's exact stopping condition. -/
theorem heightScale_lower_bound {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) :
    Real.log ((n : ℝ) / 4) ≤ heightScale x n := by
  exact log_quarter_le_heightScale hn ((lt_extinctionTime_iff x n).mp hτ)

/-- Lemma `lem:bunif` on its deterministic vertex-label space, including
the endpoint `n = τ`. The labels use the exact paper birth-time shift. -/
theorem uniform_birthTime_lt_of_le_extinctionTime {x : SignSequence} {m n : ℕ}
    (_hm : 1 ≤ m) (hmn : m ≤ n) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ((uniformVertex x n) {v | birthTime n v < m}).toReal =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  exact uniform_birthTime_lt (activeCount_nonneg_of_le_extinctionTime hτ) hmn

end Freezing1
