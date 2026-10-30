module

public import Freezing1.CountableMarkovObservations

/-!
# Nonnegative accumulated costs controlled by a true kernel potential

The one-step estimate is required along the actual full path law. No
independence or conditional expectation identity is postulated.
-/

@[expose] public section

namespace Freezing1.CountableMarkovChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E A : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

theorem lintegral_accumulate_of_superharmonic (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (a : A) (update : A → E → A) (f : A → E → ℝ≥0∞)
    (h : ∀ n, ∀ᵐ H ∂fullLaw α x,
      (∫⁻ z, f (update (accumulate a update H n) z) z ∂α (H n)) ≤
        f (accumulate a update H n) (H n)) (n : ℕ) :
    (∫⁻ H, f (accumulate a update H n) (H n) ∂fullLaw α x) ≤ f a x := by
  induction n with
  | zero =>
    calc
      _ = ∫⁻ _ : ℕ → E, f a x ∂fullLaw α x := by
        apply lintegral_congr_ae
        filter_upwards [fullLaw_initial α x] with H hH
        simp [hH]
      _ = _ := by simp
      _ ≤ _ := le_rfl
  | succ n ih =>
    rw [lintegral_accumulate_succ]
    exact (lintegral_mono_ae (h n)).trans ih

end Freezing1.CountableMarkovChain
