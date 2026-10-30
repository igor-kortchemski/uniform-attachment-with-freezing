module

public import Freezing1.ForwardComponentPopulation
public import Freezing1.ForwardHistorySupport
public import Freezing1.SignedUrnContinuation

/-!
# Actual forward continuation and the component urn

The continuation is defined by the original tree transition kernels. Its
component-population pushforward is the iterated signed urn, conditional on
any genuine phase state. The comparison holds up to the extinction endpoint;
strict positivity is needed only at times when a further choice is made.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

noncomputable def continuationLaw (x : SignSequence) : ℕ → ℕ → State → Measure State
  | _, 0, s => Measure.dirac s
  | b, k + 1, s => (transitionLaw s (b + 1) (x (b + 1))).bind
      (continuationLaw x (b + 1) k)

instance continuationLaw_probability (x : SignSequence) (b k : ℕ) (s : State) :
    IsProbabilityMeasure (continuationLaw x b k s) := by
  induction k generalizing b s with
  | zero => change IsProbabilityMeasure (Measure.dirac s); infer_instance
  | succ k ih =>
    change IsProbabilityMeasure ((transitionLaw _ _ _).bind _)
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall fun t => ih (b + 1) t)

/-- This continuation is the actual future law obtained by splitting the
original forward recursion at the chosen time. -/
theorem treeLaw_add_eq_bind_continuation (x : SignSequence) (b k : ℕ) :
    treeLaw x (b + k) = (treeLaw x b).bind (continuationLaw x b k) := by
  induction k generalizing b with
  | zero => simpa only [Nat.add_zero, continuationLaw] using (Measure.bind_dirac (m := treeLaw x b)).symm
  | succ k ih =>
    rw [show b + (k + 1) = (b + 1) + k by omega, ih, treeLaw,
      Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    rfl

/-- Conditional on the actual current tree, every component population has
exactly the prescribed signed urn continuation law. -/
theorem continuationLaw_componentPopulation {x : SignSequence} {b k a : ℕ} {s : State}
    (hd : PhaseData x b s) (ha : a ≤ b)
    (hτ : ((b + k : ℕ) : ℕ∞) ≤ extinctionTime x) (r : ℕ) :
    (continuationLaw x b k s).map (fun t => componentPopulation t a r) =
      SignedUrn.continuationLaw (activeCount x) b k (componentPopulation s a r) := by
  induction k generalizing b s with
  | zero => simp [continuationLaw, SignedUrn.continuationLaw]
  | succ k ih =>
    have hbτ : (b : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show b < b + (k + 1) by omega)) hτ
    have hpos := ((lt_extinctionTime_iff x b).mp hbτ) b le_rfl
    have hne : s.active.Nonempty := by
      apply Finset.card_pos.mp
      have hc := hd.count
      omega
    have hnext := transitionLaw_phaseData hd hne
    have hend : (((b + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hτ
    rw [continuationLaw, Measure.map_bind measurable_from_top.aemeasurable (by fun_prop)]
    calc
      _ = (transitionLaw s (b + 1) (x (b + 1))).bind
          (fun t => SignedUrn.continuationLaw (activeCount x) (b + 1) k
            (componentPopulation t a r)) := by
        apply Measure.bind_congr_right
        filter_upwards [hnext] with t ht
        exact ih ht (ha.trans (Nat.le_succ b)) hend
      _ = ((transitionLaw s (b + 1) (x (b + 1))).map
          (fun t => componentPopulation t a r)).bind
          (SignedUrn.continuationLaw (activeCount x) (b + 1) k) := by
        rw [Measure.bind_map measurable_from_top.aemeasurable
          (measurable_of_countable _).aemeasurable]
      _ = _ := by
        rw [transitionLaw_componentPopulation hd.valid ha r _ hne, hd.count,
          SignedUrn.continuationLaw, activeCount_succ]
        congr 2
        omega

/-- A particular vertex active at the cut starts its component urn with one
ball; the conditional law is independent of all other details of that tree. -/
theorem continuationLaw_componentPopulation_of_root {x : SignSequence} {a k : ℕ} {s : State}
    (hd : PhaseData x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    {r : ℕ} (hr : r ∈ s.active) :
    (continuationLaw x a k s).map (fun t => componentPopulation t a r) =
      SignedUrn.continuationLaw (activeCount x) a k 1 := by
  rw [continuationLaw_componentPopulation hd le_rfl hτ,
    componentPopulation_at_cut hd.valid hr]

end Freezing1.Forward
