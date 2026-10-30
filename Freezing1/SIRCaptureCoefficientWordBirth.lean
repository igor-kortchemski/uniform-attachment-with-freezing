module

public import Freezing1.SIRCaptureCoefficientCounts
public import Freezing1.SIRLateMaximumWord
public import Freezing1.SIRCountsExtinctionIndex
public import Freezing1.BirthTime

/-! Exact recovery-label birth counts in the actual adaptive epidemic words. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def captureWordExtinction (n : ℕ) (w : Fin (2 * n + 1) → Bool) : ℕ :=
  boundedExtinctionIndex n (wordCountsAt n w)

theorem wordCountsAt_after_last (n : ℕ) {K : ℕ} (w : Fin K → Bool)
    {i : ℕ} (hi : K ≤ i) : wordCountsAt n w i = countsRunWord n w := by
  by_cases he : i = K
  · rw [he, wordCountsAt_last]
  · unfold wordCountsAt
    rw [dite_eq_right (by omega : ¬ i ≤ K)]

theorem captureWord_legal (n : ℕ) (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w) :
    ∀ i, (wordCountsAt n w i).LegalNext (wordCountsAt n w (i + 1)) := by
  intro i
  by_cases hi : i < 2 * n + 1
  · exact wordCountsAt_legal n w hw hi
  · rw [wordCountsAt_after_last n w (by omega), wordCountsAt_after_last n w (by omega)]
    exact Or.inl ⟨countsRunWord_feasible_terminal n w hw, rfl⟩

theorem captureWordExtinction_spec (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) :
    captureWordExtinction n w ≤ 2 * n + 1 ∧
      extinctionTime (ForwardAnnealed.wordSchedule w) = captureWordExtinction n w ∧
      (wordCountsAt n w (captureWordExtinction n w)).infectious = 0 ∧
      ∀ i < captureWordExtinction n w, 0 < (wordCountsAt n w i).infectious := by
  have hzero : (wordCountsAt n w (2 * n + 1)).infectious = 0 := by
    rw [wordCountsAt_last]
    exact countsRunWord_feasible_terminal n w hw
  have hz := boundedExtinctionIndex_zero n (wordCountsAt n w) hzero
  have hp : ∀ i < boundedExtinctionIndex n (wordCountsAt n w),
      0 < (wordCountsAt n w i).infectious :=
    fun _ hi => boundedExtinctionIndex_pos_before n (wordCountsAt n w) hi
  change (wordCountsAt n w (captureWordExtinction n w)).infectious = 0 at hz
  change ∀ i < captureWordExtinction n w, 0 < (wordCountsAt n w i).infectious at hp
  obtain ⟨T, hT, he, hTzero, hTpos⟩ := terminal_word_first_extinction n w hw
  have hTeq : T = captureWordExtinction n w := by
    apply le_antisymm
    · by_contra hnot
      have hh := hTpos (captureWordExtinction n w) (by omega)
      rw [hz] at hh
      omega
    · by_contra hnot
      have hh := hp T (by omega)
      rw [hTzero] at hh
      omega
  exact ⟨boundedExtinctionIndex_le n _, by simpa only [hTeq] using he, hz, fun i hi => hp i hi⟩

theorem wordCountsAt_susceptible_plus_before (n : ℕ) {K : ℕ} (w : Fin K → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i ≤ K)
    (hp : ∀ j < i, 0 < (wordCountsAt n w j).infectious) :
    (wordCountsAt n w i).susceptible + plusCount (ForwardAnnealed.wordSchedule w) i = n := by
  induction i with
  | zero => simp only [wordCountsAt_zero, initialCounts, plusCount_zero, Nat.add_zero]
  | succ i ih =>
    have hprev := hp i (by omega)
    have h := ih (by omega) (fun j hj => hp j (by omega))
    rw [wordCountsAt_succ n w (by omega), plusCount_succ]
    cases hx : ForwardAnnealed.wordSchedule w (i + 1)
    · simp [countsStep, hprev.ne', recoverCounts]
      exact h
    · have hu : (wordCountsAt n w i).susceptible ≠ 0 := by
        intro hu
        have hh := wordCountsAt_feasible_sign n w hw (by omega) hu
        rw [hx] at hh
        contradiction
      simp [countsStep, hprev.ne', hu, infectCounts]
      omega

theorem captureWord_recovered_eq_minus (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i ≤ captureWordExtinction n w) :
    captureRecoveredCount n (wordCountsAt n w i) = minusCount (ForwardAnnealed.wordSchedule w) i := by
  have hs := captureWordExtinction_spec n w hw
  have hiK := hi.trans hs.1
  have hp : ∀ j < i, 0 < (wordCountsAt n w j).infectious := fun j hj => hs.2.2.2 j (hj.trans_le hi)
  have hU := wordCountsAt_susceptible_plus_before n w hw hiK hp
  have hI := wordCountsAt_eq_activeCount_before n w hw hiK hp
  have hwcount := activeCount_eq_counts (ForwardAnnealed.wordSchedule w) i
  unfold captureRecoveredCount captureVertexCount
  omega

theorem captureWord_terminal_vertex_count (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) :
    captureVertexCount n (wordCountsAt n w (2 * n + 1)) =
      plusCount (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w) + 1 := by
  have hs := captureWordExtinction_spec n w hw
  have hU := wordCountsAt_susceptible_plus_before n w hw hs.1 hs.2.2.2
  have hheld := legalHistory_absorbed_persists (captureWord_legal n w hw) hs.2.2.1 (2 * n + 1) hs.1
  rw [hheld]
  unfold captureVertexCount
  omega

/-- Source Lemma `bunif`, specialized at the actual random extinction
index, counts recovered vertices rather than all forward-prefix vertices. -/
theorem captureWord_reverse_birth_failure (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) (k : ℕ) :
    (uniformVertex (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w)).real
        {v | k ≤ birthTime (captureWordExtinction n w) v} =
      reverseMissingFraction n k (wordCountsAt n w) := by
  have hs := captureWordExtinction_spec n w hw
  have hl := captureWord_legal n w hw
  have h0 := wordCountsAt_zero n w
  have hwalk : activeCount (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w) = 0 := by
    have h := wordCountsAt_eq_activeCount_before n w hw hs.1 hs.2.2.2
    rw [hs.2.2.1, Nat.cast_zero] at h
    exact h.symm
  have hnonneg : 0 ≤ activeCount (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w) := by
    rw [hwalk]
  have : IsProbabilityMeasure (uniformVertex (ForwardAnnealed.wordSchedule w)
      (captureWordExtinction n w)) := uniformVertex_isProbabilityMeasure hnonneg
  by_cases hk : k ≤ captureWordExtinction n w
  · have hc := uniform_birthTime_lt_counts hnonneg hk
    have hR := captureWord_recovered_eq_minus n w hw hk
    have hN := captureWord_terminal_vertex_count n w hw
    have hNR : (captureVertexCount n (wordCountsAt n w (2 * n + 1)) : ℝ) =
        (plusCount (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w) : ℝ) + 1 := by
      exact_mod_cast hN
    change (uniformVertex (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w)).real
      {v | birthTime (captureWordExtinction n w) v < k} = _ at hc
    rw [← hR, ← hNR] at hc
    have he : {v : ℕ ⊕ ℕ | k ≤ birthTime (captureWordExtinction n w) v} =
        {v | birthTime (captureWordExtinction n w) v < k}ᶜ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [he, probReal_compl_eq_one_sub ((Set.to_countable _).measurableSet), hc]
    have hRN : captureRecoveredCount n (wordCountsAt n w k) ≤
        captureVertexCount n (wordCountsAt n w (2 * n + 1)) :=
      (Nat.sub_le _ _).trans (captureVertexCount_mono (n := n) hl (hk.trans hs.1))
    have hNpos : 0 < captureVertexCount n (wordCountsAt n w (2 * n + 1)) := by
      have hu := (legalHistory_susceptible_bounds h0 hl (2 * n + 1)).2
      unfold captureVertexCount
      omega
    unfold reverseMissingFraction uncapturedFraction
    rw [Nat.cast_sub hRN]
    have hNreal : (captureVertexCount n (wordCountsAt n w (2 * n + 1)) : ℝ) ≠ 0 := by
      exact_mod_cast hNpos.ne'
    field_simp
  · have hfilter : (vertexLabels (ForwardAnnealed.wordSchedule w)
        (captureWordExtinction n w)).filter
        (fun v => k ≤ birthTime (captureWordExtinction n w) v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hv, hbirth⟩ := Finset.mem_filter.mp hv
      have hb : birthTime (captureWordExtinction n w) v ≤ captureWordExtinction n w := by
        cases v with
        | inl j => exact le_rfl
        | inr j =>
          exact (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hv)).1).le
      omega
    have hsource : (uniformVertex (ForwardAnnealed.wordSchedule w)
        (captureWordExtinction n w)).real {v | k ≤ birthTime (captureWordExtinction n w) v} = 0 := by
      unfold uniformVertex Measure.real
      rw [Measure.uniformOfFinset_apply]
      simp only [Set.mem_ofPred_eq, hfilter, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div,
        ENNReal.toReal_zero]
    rw [hsource]
    have hkheld := legalHistory_absorbed_persists hl hs.2.2.1 k (by omega)
    have hNheld := legalHistory_absorbed_persists hl hs.2.2.1 (2 * n + 1) hs.1
    simp only [reverseMissingFraction, hkheld, hNheld, captureRecoveredCount, hs.2.2.1,
      Nat.sub_zero, uncapturedFraction, Nat.sub_self, Nat.cast_zero, zero_div]

theorem signWordLaw_reverseMissing_integral_eq (r : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    (∫ w, reverseMissingFraction n k (wordCountsAt n w) ∂signWordLaw r n (2 * n + 1)) =
      ∫ H, reverseMissingFraction n k H ∂countsFullLaw r n := by
  let score : CountableMarkovChain.Prefix (E := Counts) (2 * n + 1) → ℝ := fun P =>
    uncapturedFraction (captureVertexCount n (P ⟨2 * n + 1, Finset.mem_Iic.mpr le_rfl⟩))
      (captureRecoveredCount n (P ⟨k, Finset.mem_Iic.mpr hk⟩))
  have hword (w : Fin (2 * n + 1) → Bool) : score (countsPrefixWord n w) =
      reverseMissingFraction n k (wordCountsAt n w) := by
    simp only [score, reverseMissingFraction, wordCountsAt, dite_eq_left hk, dite_eq_left le_rfl]
  have hhist (H : ℕ → Counts) : score (Preorder.frestrictLe (2 * n + 1) H) =
      reverseMissingFraction n k H := rfl
  calc
    _ = ∫ P, score P ∂(signWordLaw r n (2 * n + 1)).map (countsPrefixWord n) := by
      rw [integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable score).aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall fun w => (hword w).symm)
    _ = _ := by
      rw [signWordLaw_map_countsPrefixWord,
        integral_map (Preorder.measurable_frestrictLe _).aemeasurable
          (measurable_of_countable score).aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall hhist)

end Freezing1.SIR
