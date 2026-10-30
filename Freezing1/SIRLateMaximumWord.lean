module

public import Freezing1.SIRRandomEnvironmentTransferCounts
public import Freezing1.SIRLateAttachmentSum
public import Freezing1.HeightScale

/-!
# Stopping and late height charges for actual feasible SIR words

All finite count-prefix coordinates are retained. The first extinct count
is identified with the unstopped word's first zero; no post-extinction walk
terms are used as height charges.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def wordCountsAt (n : ℕ) {N : ℕ} (w : Fin N → Bool) (i : ℕ) : Counts :=
  if hi : i ≤ N then countsPrefixWord n w ⟨i, Finset.mem_Iic.mpr hi⟩ else countsRunWord n w

theorem wordCountsAt_last (n : ℕ) {N : ℕ} (w : Fin N → Bool) :
    wordCountsAt n w N = countsRunWord n w := by
  simp only [wordCountsAt, dite_eq_left le_rfl, countsPrefixWord_last]

theorem wordCountsAt_init (n : ℕ) {N : ℕ} (w : Fin (N + 1) → Bool) {i : ℕ} (hi : i ≤ N) :
    wordCountsAt n w i = wordCountsAt n (Fin.init w) i := by
  simp only [wordCountsAt, dite_eq_left (hi.trans (Nat.le_succ N)),
    countsPrefixWord, CountableMarkovChain.prefixAppend, dite_eq_left hi]

theorem wordCountsAt_zero (n : ℕ) {N : ℕ} (w : Fin N → Bool) :
    wordCountsAt n w 0 = initialCounts n := by
  induction N with
  | zero => simp [wordCountsAt, countsPrefixWord]
  | succ N ih => rw [wordCountsAt_init n w (Nat.zero_le N)]; exact ih (Fin.init w)

theorem wordCountsAt_succ (n : ℕ) {N : ℕ} (w : Fin N → Bool) {i : ℕ} (hi : i < N) :
    wordCountsAt n w (i + 1) = countsStep (wordCountsAt n w i)
      (ForwardAnnealed.wordSchedule w (i + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hiN : i = N
    · subst i
      rw [wordCountsAt_last, wordCountsAt_init n w le_rfl, wordCountsAt_last,
        wordSchedule_last]
      rfl
    · have hi' : i < N := by omega
      rw [wordCountsAt_init n w (by omega : i + 1 ≤ N),
        wordCountsAt_init n w hi'.le,
        (wordSchedule_agree_init w) (i + 1) (by omega) (by omega)]
      exact ih (Fin.init w) hi'

theorem wordCountsAt_feasible_sign (n : ℕ) {N : ℕ} (w : Fin N → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i < N) :
    (wordCountsAt n w i).susceptible = 0 → ForwardAnnealed.wordSchedule w (i + 1) = false := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hiN : i = N
    · subst i
      rw [wordCountsAt_init n w le_rfl, wordCountsAt_last, wordSchedule_last]
      exact hw.2
    · have hi' : i < N := by omega
      rw [wordCountsAt_init n w hi'.le,
        (wordSchedule_agree_init w) (i + 1) (by omega) (by omega)]
      exact ih (Fin.init w) hw.1 hi'

theorem wordCountsAt_legal (n : ℕ) {N : ℕ} (w : Fin N → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i < N) :
    (wordCountsAt n w i).LegalNext (wordCountsAt n w (i + 1)) := by
  rw [wordCountsAt_succ n w hi]
  exact countsStep_legal_of_feasible _ _ (wordCountsAt_feasible_sign n w hw hi)

theorem wordCountsAt_eq_activeCount_before (n : ℕ) {N : ℕ} (w : Fin N → Bool)
    (hw : SignWordFeasible n w) {k : ℕ} (hk : k ≤ N)
    (hp : ∀ i < k, 0 < (wordCountsAt n w i).infectious) :
    ((wordCountsAt n w k).infectious : ℤ) = activeCount (ForwardAnnealed.wordSchedule w) k := by
  induction k with
  | zero => simp [wordCountsAt_zero, initialCounts]
  | succ k ih =>
    have hprev := hp k (by omega)
    have hrec := wordCountsAt_succ n w (by omega : k < N)
    have hi := ih (by omega) (fun i hi => hp i (by omega))
    rw [activeCount_succ, ← hi, hrec]
    cases hx : ForwardAnnealed.wordSchedule w (k + 1)
    · simp [countsStep, hprev.ne', recoverCounts,
        Nat.cast_sub (show 1 ≤ (wordCountsAt n w k).infectious by omega)]
      omega
    · have hu : (wordCountsAt n w k).susceptible ≠ 0 := by
        intro hu
        have hh := wordCountsAt_feasible_sign n w hw (by omega : k < N) hu
        simp [hx] at hh
      simp [countsStep, hprev.ne', hu, infectCounts]

/-- A feasible terminal word has the same first zero as its original
integer sign schedule, including the zero endpoint. -/
theorem terminal_word_first_extinction (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) :
    ∃ T : ℕ, T ≤ 2 * n + 1 ∧ extinctionTime (ForwardAnnealed.wordSchedule w) = T ∧
      (wordCountsAt n w T).infectious = 0 ∧
      ∀ i < T, 0 < (wordCountsAt n w i).infectious := by
  have hz : (wordCountsAt n w (2 * n + 1)).infectious = 0 := by
    rw [wordCountsAt_last]
    exact countsRunWord_feasible_terminal n w hw
  let hex : ∃ i, (wordCountsAt n w i).infectious = 0 := ⟨2 * n + 1, hz⟩
  let T := Nat.find hex
  have hT : T ≤ 2 * n + 1 := Nat.find_min' hex hz
  have hzero : (wordCountsAt n w T).infectious = 0 := Nat.find_spec hex
  have hpos : ∀ i < T, 0 < (wordCountsAt n w i).infectious := by
    intro i hi
    have hh := Nat.find_min hex hi
    omega
  have he := wordCountsAt_eq_activeCount_before n w hw hT hpos
  have hwalkzero : activeCount (ForwardAnnealed.wordSchedule w) T = 0 := by rw [← he, hzero]; rfl
  have hactual : ∃ i, activeCount (ForwardAnnealed.wordSchedule w) i = 0 := ⟨T, hwalkzero⟩
  have hfirst : Nat.find hactual = T := by
    apply (Nat.find_eq_iff hactual).mpr
    refine ⟨hwalkzero, ?_⟩
    intro i hi
    have he := wordCountsAt_eq_activeCount_before n w hw (hi.le.trans hT)
      (fun j hj => hpos j (hj.trans hi))
    have hp := hpos i hi
    rw [← he]
    omega
  refine ⟨T, hT, ?_, hzero, hpos⟩
  simp only [extinctionTime, dite_eq_left hactual, hfirst]

/-- Every pre-extinction source attachment reciprocal is dominated by the
actual susceptible-consuming pre-birth charge at that event. -/
theorem word_attachment_reciprocal_le_birthCharge (n : ℕ) {N : ℕ} (w : Fin N → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i < N)
    (hp : ∀ j ≤ i, 0 < (wordCountsAt n w j).infectious) :
    (if ForwardAnnealed.wordSchedule w (i + 1) then
      1 / (activeCount (ForwardAnnealed.wordSchedule w) (i + 1) : ℝ) else 0) ≤
      birthCharge (wordCountsAt n w i) (wordCountsAt n w (i + 1)) := by
  cases hx : ForwardAnnealed.wordSchedule w (i + 1)
  · simp only [Bool.false_eq_true, ite_false]
    exact birthCharge_nonneg _ _
  · simp only [ite_true]
    have hprev := hp i le_rfl
    have hu : (wordCountsAt n w i).susceptible ≠ 0 := by
      intro hu
      have hh := wordCountsAt_feasible_sign n w hw hi hu
      simp [hx] at hh
    have hrec := wordCountsAt_succ n w hi
    rw [hx] at hrec
    have hcount := wordCountsAt_eq_activeCount_before n w hw (by omega : i + 1 ≤ N)
      (fun j hj => hp j (by omega))
    have hcountR : ((wordCountsAt n w (i + 1)).infectious : ℝ) =
        (activeCount (ForwardAnnealed.wordSchedule w) (i + 1) : ℝ) := by exact_mod_cast hcount
    rw [← hcountR]
    have hlegal := wordCountsAt_legal n w hw hi
    have hd : (wordCountsAt n w (i + 1)).susceptible < (wordCountsAt n w i).susceptible := by
      rw [hrec]
      simp only [countsStep, ite_eq_right hprev.ne', ite_true, ite_eq_right hu, infectCounts]
      omega
    have hh := hlegal.post_birth_reciprocal_le
    simpa only [ite_eq_left hd] using hh

noncomputable def wordLateBirthCharge (n : ℕ) (w : Fin (2 * n + 1) → Bool) : ℝ :=
  birthHistoryCharge (CountableMarkovChain.shift n (wordCountsAt n w)) (n + 1)

theorem heightScale_add_word (x : SignSequence) (a b : ℕ) :
    heightScale x (a + b) = heightScale x a +
      ∑ j ∈ Finset.range b, if x (a + j + 1) then 1 / (activeCount x (a + j + 1) : ℝ) else 0 := by
  unfold heightScale
  rw [Finset.sum_range_add]

theorem birthHistoryCharge_mono (H : ℕ → Counts) : Monotone (birthHistoryCharge H) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [birthHistoryCharge, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (birthCharge_nonneg _ _)

/-- Only height-scale terms up to first extinction are used. Their true
transition index is `j -> j+1`, and the pre-birth charge dominates them. -/
theorem terminal_word_late_heightScale_le_charge (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) {T : ℕ} (hT : T ≤ 2 * n + 1) (hnT : n ≤ T)
    (hpos : ∀ i < T, 0 < (wordCountsAt n w i).infectious) :
    heightScale (ForwardAnnealed.wordSchedule w) T - heightScale (ForwardAnnealed.wordSchedule w) n ≤
      wordLateBirthCharge n w := by
  have he := heightScale_add_word (ForwardAnnealed.wordSchedule w) n (T - n)
  rw [show n + (T - n) = T by omega] at he
  have hsum : (∑ j ∈ Finset.range (T - n),
      if ForwardAnnealed.wordSchedule w (n + j + 1) then
        1 / (activeCount (ForwardAnnealed.wordSchedule w) (n + j + 1) : ℝ) else 0) ≤
      birthHistoryCharge (CountableMarkovChain.shift n (wordCountsAt n w)) (T - n) := by
    unfold birthHistoryCharge
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hh := word_attachment_reciprocal_le_birthCharge n w hw
      (by omega : n + j < 2 * n + 1) (fun i hi => hpos i (by omega))
    simpa only [CountableMarkovChain.shift, Nat.add_assoc] using hh
  have hm := birthHistoryCharge_mono (CountableMarkovChain.shift n (wordCountsAt n w))
    (by omega : T - n ≤ n + 1)
  change _ ≤ wordLateBirthCharge n w at hm
  linarith

theorem signWordLaw_wordLateBirthCharge_event_eq (rate : ℝ≥0) (n : ℕ) (L : ℝ) :
    signWordLaw rate n (2 * n + 1) {w | L ≤ wordLateBirthCharge n w} =
      countsFullLaw rate n {H | L ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1)} := by
  let extend : CountableMarkovChain.Prefix (E := Counts) (2 * n + 1) → (ℕ → Counts) := fun P k =>
    if hk : k ≤ 2 * n + 1 then P ⟨k, Finset.mem_Iic.mpr hk⟩ else initialCounts 0
  let score : CountableMarkovChain.Prefix (E := Counts) (2 * n + 1) → ℝ := fun P =>
    birthHistoryCharge (CountableMarkovChain.shift n (extend P)) (n + 1)
  have hwscore (w : Fin (2 * n + 1) → Bool) : score (countsPrefixWord n w) = wordLateBirthCharge n w := by
    unfold score wordLateBirthCharge birthHistoryCharge
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [CountableMarkovChain.shift, extend, wordCountsAt,
      dite_eq_left (by omega : n + i ≤ 2 * n + 1), dite_eq_left (by omega : n + (i + 1) ≤ 2 * n + 1)]
  have hHscore (H : ℕ → Counts) : score (Preorder.frestrictLe (2 * n + 1) H) =
      birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1) := by
    unfold score birthHistoryCharge
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [CountableMarkovChain.shift, extend,
      dite_eq_left (by omega : n + i ≤ 2 * n + 1), dite_eq_left (by omega : n + (i + 1) ≤ 2 * n + 1),
      Preorder.frestrictLe]
    rfl
  have hh := signWordLaw_countsPrefix_event_eq rate n (2 * n + 1) {P | L ≤ score P}
  simpa only [mem_ofPred_eq, hwscore, hHscore] using hh

theorem signWordLaw_wordLateBirthCharge_over_log_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (signWordLaw (rate n) n (2 * n + 1)).real
      {w | eta * Real.log n ≤ wordLateBirthCharge n w}) atTop (nhds 0) := by
  simpa only [Measure.real, signWordLaw_wordLateBirthCharge_event_eq] using
    countsFullLaw_post_population_birth_charge_over_log_tendsto_zero rate hstrong heta

end Freezing1.SIR
