module

public import Freezing1.SIRCaptureCoefficientObserved
public import Freezing1.SIRCaptureCoefficientNative
public import Freezing1.MainSIREmbedded

/-! Source-ratio interfaces for the literal same-epsilon SIR capture estimate. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory
open scoped Classical NNReal Topology

theorem source_same_epsilon_reverse_birth_capture (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualTerminalReverseBirthLaw (rate n) n).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} :=
  actualTerminalReverseBirthLaw_same_epsilon rate lam hlam
    (scaled_rate_of_source_ratio rate lam
      (by exact_mod_cast (lt_trans zero_lt_one hlam)) hratio) heps hepsT

theorem source_same_epsilon_forward_capture (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualPrefixCaptureLaw (rate n) n
        ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊).real {true} :=
  actualPrefixCaptureLaw_same_epsilon rate lam hlam
    (scaled_rate_of_source_ratio rate lam
      (by exact_mod_cast (lt_trans zero_lt_one hlam)) hratio) heps hepsT

theorem source_same_epsilon_two_uniform_captures (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      let k := ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊
      1 - eps ≤ (actualPrefixCapturePairLaw (rate n) n k).real {z | z.1 = true} ∧
        (actualPrefixCapturePairLaw (rate n) n k).real {z | z.1 = true} =
          (actualPrefixCapturePairLaw (rate n) n k).real {z | z.2 = true} :=
  actualPrefixCapturePairLaw_same_epsilon rate lam hlam
    (scaled_rate_of_source_ratio rate lam
      (by exact_mod_cast (lt_trans zero_lt_one hlam)) hratio) heps hepsT

end Freezing1.SIR
