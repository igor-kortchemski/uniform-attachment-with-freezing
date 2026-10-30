module

public import Freezing1.ForwardBlockStatistics
public import Freezing1.ForwardPrefixEvents
public import Freezing1.ForwardCutTruncation
public import Mathlib.Probability.Independence.Basic

/-!
# The actual pair of block counts is independent of the earlier tree

The complete earlier state and the pair consisting of the tall-root count
and the distinguished-root component maximum satisfy the exact event
factorization under the actual terminal tree law. This proves the source's
independence assertion for `(N,M)`; it makes no assertion about conditioning
on the full unlabelled forest for the separate matching identities.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem continuationLaw_prefix_blockStatistics_event
    {x : SignSequence} {a k : ℕ} {s : State}
    (hs : HasHistory x a s) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ)
    (A : Set State) (B : Set (ℕ × ℕ)) (hB : MeasurableSet B) :
    (continuationLaw x a k s) {q | truncateAt q a ∈ A ∧
      (blockTallCount q a (a + k) t, componentMaximum q a) ∈ B} =
      if s ∈ A then TaggedPopulation.blockStatisticsLaw x a k (activeCount x a).toNat t B
      else 0 := by
  have hmap := congrArg (fun μ : Measure (ℕ × ℕ) => μ B)
    (continuationLaw_blockStatistics hs hn t)
  rw [Measure.map_apply measurable_from_top hB] at hmap
  change (continuationLaw x a k s) {q |
    (blockTallCount q a (a + k) t, componentMaximum q a) ∈ B} = _ at hmap
  calc
    _ = (continuationLaw x a k s) {q | s ∈ A ∧
        (blockTallCount q a (a + k) t, componentMaximum q a) ∈ B} := by
      apply measure_congr
      filter_upwards [continuationLaw_truncate_self hs hn] with q hq
      simp only [hq]
    _ = _ := by
      by_cases hA : s ∈ A
      · simpa only [hA, true_and, ite_true] using hmap
      · simp only [hA, false_and, Set.ofPred_false, measure_empty, ite_false]

theorem treeLaw_prefix_blockStatistics_event_at_endpoint (x : SignSequence)
    {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ)
    (A : Set State) (hA : MeasurableSet A) (B : Set (ℕ × ℕ)) (hB : MeasurableSet B) :
    (treeLaw x b) {q | truncateAt q a ∈ A ∧
        (blockTallCount q a b t, componentMaximum q a) ∈ B} =
      (treeLaw x a) A * TaggedPopulation.blockStatisticsLaw x a (b - a)
        (activeCount x a).toNat t B := by
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have hτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  have ha : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have htree : treeLaw x b = (treeLaw x a).bind (continuationLaw x a (b - a)) := by
    calc
      _ = treeLaw x (a + (b - a)) := congrArg (treeLaw x) he.symm
      _ = _ := treeLaw_add_eq_bind_continuation x a (b - a)
  rw [htree, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ s, A.indicator (fun _ => TaggedPopulation.blockStatisticsLaw x a (b - a)
        (activeCount x a).toNat t B) s ∂treeLaw x a := by
      apply lintegral_congr_ae
      filter_upwards [treeLaw_hasHistory x a ha] with s hs
      simpa only [he, Set.indicator_apply] using
        continuationLaw_prefix_blockStatistics_event hs hτ t A B hB
    _ = TaggedPopulation.blockStatisticsLaw x a (b - a) (activeCount x a).toNat t B *
        (treeLaw x a) A := lintegral_indicator_const hA _
    _ = _ := mul_comm _ _

theorem treeLaw_prefix_blockStatistics_event (x : SignSequence)
    {n a b : ℕ} (hn : (n : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b) (hb : b ≤ n) (t : ℝ)
    (A : Set State) (hA : MeasurableSet A) (B : Set (ℕ × ℕ)) (hB : MeasurableSet B) :
    (treeLaw x n) {q | truncateAt q a ∈ A ∧
        (blockTallCount q a b t, componentMaximum (truncateAt q b) a) ∈ B} =
      (treeLaw x a) A * TaggedPopulation.blockStatisticsLaw x a (b - a)
        (activeCount x a).toNat t B := by
  have hbτ : (b : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hb : (b : ℕ∞) ≤ n).trans hn
  calc
    _ = (treeLaw x n) {q | truncateAt q a ∈ A ∧
        (blockTallCount (truncateAt q b) a b t, componentMaximum (truncateAt q b) a) ∈ B} := by
      apply measure_congr
      filter_upwards [treeLaw_phaseData x n hn] with q hq
      rw [blockTallCount_truncateAt hq.valid a b t]
    _ = (treeLaw x b) {q | truncateAt q a ∈ A ∧
        (blockTallCount q a b t, componentMaximum q a) ∈ B} :=
      treeLaw_two_prefix_event x hn hab hb
        (fun s q => s ∈ A ∧ (blockTallCount q a b t, componentMaximum q a) ∈ B)
    _ = _ := treeLaw_prefix_blockStatistics_event_at_endpoint x hab hbτ t A hA B hB

/-- Source A51, on the actual forward probability space. The maximum is
stopped at the upper block endpoint, including every distinguished root. -/
theorem indepFun_prefix_blockStatistics (x : SignSequence) {n a b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b) (hb : b ≤ n) (t : ℝ) :
    IndepFun (fun q => truncateAt q a)
      (fun q => (blockTallCount q a b t, componentMaximum (truncateAt q b) a))
      (treeLaw x n) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hA hB
  have hpair := treeLaw_prefix_blockStatistics_event x hn hab hb t A hA B hB
  have hsecond := treeLaw_prefix_blockStatistics_event x hn hab hb t Set.univ
    MeasurableSet.univ B hB
  simp only [Set.mem_univ, true_and, measure_univ, one_mul] at hsecond
  have hfirst := treeLaw_prefix_event x hn (hab.trans hb) (fun s => s ∈ A)
  change (treeLaw x n) {q | truncateAt q a ∈ A} = (treeLaw x a) A at hfirst
  change (treeLaw x n) {q | truncateAt q a ∈ A ∧
      (blockTallCount q a b t, componentMaximum (truncateAt q b) a) ∈ B} =
    (treeLaw x n) {q | truncateAt q a ∈ A} * (treeLaw x n)
      {q | (blockTallCount q a b t, componentMaximum (truncateAt q b) a) ∈ B}
  rw [hpair, hfirst, hsecond]

end Freezing1.Forward
