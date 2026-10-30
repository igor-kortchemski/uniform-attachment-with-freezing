module

public import Freezing1.MainLinearBlockConcentration

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical Topology

/- Literal quantifier order and constants of Forestier. The count is unfolded
   on the actual reverse history; identification with forward timestamp cuts
   is deliberately a separate statement. Global assumptions unused by this
   local bound are retained here for the complete source-specialized probe. -/
example (x : ℕ → Freezing1.SignSequence) (A : ℕ → ℝ)
    (c : Freezing1.LinearRegimeParameter)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (_hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < Freezing1.extinctionTime (x n))
    (hnear : Freezing1.NearOriginLimsup x A (c : ℝ))
    (_hbulk : Freezing1.BulkLiminf x) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
        (Freezing1.ReverseHistory.fullLaw (x n) n).real
          {H | (((Freezing1.ReverseHistory.stage H (C ^ (k + 1))).roots.filter
            fun v => (((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
              (Freezing1.linearHeightFactor c - η) <
                ((Freezing1.ReverseHistory.stage H (C ^ k)).depth v : ℝ)).card : ℝ) ≤
                  4 * ((C ^ k : ℕ) : ℝ)} ≤ L / ((C ^ k : ℕ) : ℝ) := by
  obtain ⟨C, hC, L, hL, ε, hε, hε1, he⟩ :=
    Freezing1.linear_geometricBlock_fewTallRoots_probability x A c hA hAinf hτ hnear hη hη1
  refine ⟨C, by omega, L, hL, ε, hε, hε1, ?_⟩
  simpa only [Freezing1.ReverseHistory.blockTallRootCount] using he

#print axioms Freezing1.uniform_geometricBlock_variance_le
#print axioms Freezing1.probability_below_four_le_of_mean_variance
#print axioms Freezing1.exists_geometricBlock_fewTallRoots_probability
#print axioms Freezing1.linear_geometricBlock_fewTallRoots_probability
