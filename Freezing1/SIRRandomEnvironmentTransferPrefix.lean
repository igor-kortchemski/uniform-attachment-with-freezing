module

public import Freezing1.SIRRandomEnvironmentTransferCounts

/-!
# Prefixes of the actual adaptive terminal environment

Sampling a complete terminal word and retaining its earlier signs gives
the previously constructed adaptive prefix law. Original fixed-schedule
forward laws consequently have the correct earlier marginal under terminal
word weights, without inferring joint laws from marginal equalities.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem signWordLaw_map_init (rate : ℝ≥0) (n k : ℕ) :
    (signWordLaw rate n (k + 1)).map
      (fun w : Fin (k + 1) → Bool => (Fin.init w : Fin k → Bool)) = signWordLaw rate n k := by
  rw [signWordLaw, Measure.map_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  calc
    _ = (signWordLaw rate n k).bind Measure.dirac := by
      congr 1
      funext w
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      change (bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible)).map
        (fun b : Bool => (Fin.init (Fin.snoc w b : Fin (k + 1) → Bool) : Fin k → Bool)) = Measure.dirac w
      have he : (fun b : Bool => (Fin.init (Fin.snoc w b : Fin (k + 1) → Bool) : Fin k → Bool)) =
          (fun _ : Bool => w) := by
        funext b
        simp only [Fin.init_snoc]
      rw [he, Measure.map_const]
      simp
    _ = _ := Measure.bind_dirac

def takeSigns {K : ℕ} (w : Fin K → Bool) {k : ℕ} (hk : k ≤ K) : Fin k → Bool :=
  fun i => w (Fin.castLE hk i)

theorem takeSigns_self {k : ℕ} (w : Fin k → Bool) : takeSigns w le_rfl = w := by
  funext i
  rfl

theorem takeSigns_init {K k : ℕ} (w : Fin (K + 1) → Bool) (hk : k ≤ K) :
    takeSigns (Fin.init w) hk = takeSigns w (hk.trans (Nat.le_succ K)) := by
  funext i
  rfl

theorem signWordLaw_map_takeSigns (rate : ℝ≥0) (n K k : ℕ) (hk : k ≤ K) :
    (signWordLaw rate n K).map (fun w => takeSigns w hk) = signWordLaw rate n k := by
  induction K generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    have heq : (fun w : Fin 0 → Bool => takeSigns w hk) = id := by
      funext w
      exact takeSigns_self w
    rw [heq, Measure.map_id]
  | succ K ih =>
    by_cases he : k = K + 1
    · subst k
      have heq : (fun w : Fin (K + 1) → Bool => takeSigns w hk) = id := by
        funext w
        exact takeSigns_self w
      rw [heq, Measure.map_id]
    · have hk' : k ≤ K := by omega
      calc
        _ = ((signWordLaw rate n (K + 1)).map
            (fun w : Fin (K + 1) → Bool => (Fin.init w : Fin K → Bool))).map
            (fun w => takeSigns w hk') := by
          rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
          congr 1
        _ = (signWordLaw rate n K).map (fun w => takeSigns w hk') := by
          rw [signWordLaw_map_init]
        _ = _ := ih k hk'

theorem takeSigns_schedule_agree {K k : ℕ} (w : Fin K → Bool) (hk : k ≤ K) :
    SchedulesAgreeThrough (ForwardAnnealed.wordSchedule w)
      (ForwardAnnealed.wordSchedule (takeSigns w hk)) k := by
  intro i hi hik
  have hiK : 1 ≤ i ∧ i ≤ K := ⟨hi, hik.trans hk⟩
  have hik' : 1 ≤ i ∧ i ≤ k := ⟨hi, hik⟩
  simp only [ForwardAnnealed.wordSchedule, dite_eq_left hiK, dite_eq_left hik', takeSigns]
  rfl

/-- The earlier original tree law under complete adaptive word weights is
exactly its adaptive-prefix mixture. -/
theorem original_tree_mixture_of_longer_word (rate : ℝ≥0) (n K k : ℕ) (hk : k ≤ K) :
    (signWordLaw rate n K).bind (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) k) =
      (signWordLaw rate n k).bind (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) k) := by
  rw [← signWordLaw_map_takeSigns rate n K k hk,
    Measure.bind_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall fun w =>
    Forward.treeLaw_eq_of_schedule_prefix (takeSigns_schedule_agree w hk)

end Freezing1.SIR
