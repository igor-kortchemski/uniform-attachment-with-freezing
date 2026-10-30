module

public import Freezing1.ReverseHistoryBlocks

/-!
# Expected number of tall component roots in an actual reverse block

The roots at phase b are random. Whole-history independence supplies the
weighted factorization for each deterministic label, after which finite
indicator summation gives the exact population-times-tail expectation.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

/-- The actual number of phase-b component roots whose height at phase a
exceeds the requested threshold. Their height at phase b is zero. -/
noncomputable def blockTallRootCount (a b : ℕ) (threshold : ℝ) (H : History) : ℕ :=
  ((stage H b).roots.filter fun v => threshold < ((stage H a).depth v : ℝ)).card

theorem mem_vertexLabels_of_mem_phaseLabels {x : SignSequence} {n b : ℕ} {v : ℕ ⊕ ℕ}
    (hv : v ∈ Reverse.phaseLabels x n b) : v ∈ vertexLabels x n := by
  cases v <;> simp_all [Reverse.phaseLabels, vertexLabels, frozenIndices]

theorem fullLaw_stage_valid (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {b : ℕ} (hb : b ≤ n) :
    ∀ᵐ H ∂fullLaw x n, Reverse.ValidAt x n b (stage H b) := by
  apply ae_of_ae_map (f := fun H => stage H b)
    (p := fun F => Reverse.ValidAt x n b F) measurable_from_top.aemeasurable
  rw [map_fullLaw_phase x n b hb]
  simpa only [Nat.sub_sub_self hb] using Reverse.lawAfter_valid x n (n - b) hn (by omega)

theorem history_indicator_integrable (μ : Measure History) [IsProbabilityMeasure μ]
    (P : History → Prop) [DecidablePred P] :
    Integrable (fun H => if P H then (1 : ℝ) else 0) μ := by
  apply (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun H => by split_ifs <;> norm_num

theorem integral_history_indicator (μ : Measure History) (P : History → Prop) [DecidablePred P] :
    (∫ H, (if P H then (1 : ℝ) else 0) ∂μ) = μ.real {H | P H} := by
  have he : (fun H => if P H then (1 : ℝ) else 0) =
      {H | P H}.indicator (fun _ => (1 : ℝ)) := by
    funext H
    by_cases hH : P H <;> simp [hH]
  rw [he, integral_indicator_const (1 : ℝ) (by trivial)]
  simp only [smul_eq_mul, mul_one]

/-- Finite indicator representation of the actual root count. -/
theorem blockTallRootCount_eq_sum {x : SignSequence} {n a b : ℕ} {H : History}
    (hH : Reverse.ValidAt x n b (stage H b)) (threshold : ℝ) :
    (blockTallRootCount a b threshold H : ℝ) =
      ∑ v ∈ Reverse.phaseLabels x n b,
        if v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ) then 1 else 0 := by
  have hf : (Reverse.phaseLabels x n b).filter
      (fun v => v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)) =
      (stage H b).roots.filter (fun v => threshold < ((stage H a).depth v : ℝ)) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hr, ht⟩
      exact ⟨hr, ht⟩
    · rintro ⟨hr, ht⟩
      exact ⟨hH.vertices_eq ▸ (RootedForest.mem_roots.mp hr).1, hr, ht⟩
  rw [Finset.sum_boole, hf]
  rfl

/-- Root membership sums to the deterministic number of components. -/
theorem sum_root_indicators_eq_population {x : SignSequence} {n b : ℕ} {H : History}
    (hH : Reverse.ValidAt x n b (stage H b))
    (hb : 0 ≤ activeCount x b) :
    (∑ v ∈ Reverse.phaseLabels x n b, if v ∈ (stage H b).roots then (1 : ℝ) else 0) =
      (activeCount x b : ℝ) := by
  rw [Finset.sum_boole]
  have hf : (Reverse.phaseLabels x n b).filter (fun v => v ∈ (stage H b).roots) =
      (stage H b).roots := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hH.vertices_eq ▸ (RootedForest.mem_roots.mp h).1, h⟩⟩
  rw [hf, hH.roots_card]
  exact_mod_cast Int.toNat_of_nonneg hb

/-- Summing the random root-membership probabilities recovers S_b. -/
theorem sum_root_probabilities (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {b : ℕ} (hb : b ≤ n) :
    (∑ v ∈ Reverse.phaseLabels x n b,
      (fullLaw x n).real {H | v ∈ (stage H b).roots}) = (activeCount x b : ℝ) := by
  have hbτ : (b : ℕ∞) ≤ extinctionTime x := le_trans (by exact_mod_cast hb) hn
  calc
    _ = ∫ H, ∑ v ∈ Reverse.phaseLabels x n b,
        if v ∈ (stage H b).roots then (1 : ℝ) else 0 ∂fullLaw x n := by
      rw [integral_finsetSum (Reverse.phaseLabels x n b)
        (f := fun v H => if v ∈ (stage H b).roots then (1 : ℝ) else 0)
        (fun v _ => history_indicator_integrable (fullLaw x n) (fun H => v ∈ (stage H b).roots))]
      simp_rw [integral_history_indicator]
    _ = ∫ _H, (activeCount x b : ℝ) ∂fullLaw x n := by
      apply integral_congr_ae
      filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
      exact sum_root_indicators_eq_population hH (activeCount_nonneg_of_le_extinctionTime hbτ)
    _ = _ := by simp

/-- At a root, a block-height event equals the corresponding difference event. -/
theorem root_height_event_eq_difference_event (v : ℕ ⊕ ℕ) (a b : ℕ) (threshold : ℝ) :
    {H : History | v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)} =
      {H | v ∈ (stage H b).roots ∧
        threshold < (((stage H a).depth v - (stage H b).depth v : ℕ) : ℝ)} := by
  ext H
  simp only [Set.mem_ofPred_eq]
  by_cases hr : v ∈ (stage H b).roots
  · have hz : (stage H b).depth v = 0 :=
      ((stage H b).depth_eq_zero_iff (RootedForest.mem_roots.mp hr).1).mpr
        (RootedForest.mem_roots.mp hr).2
    simp only [hr, hz, Nat.sub_zero]
  · simp only [hr, false_and]

/-- The actual count is integrable because it is almost surely a finite
sum of indicators over a deterministic carrier. -/
theorem blockTallRootCount_integrable (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a : ℕ) {b : ℕ} (hb : b ≤ n)
    (threshold : ℝ) :
    Integrable (fun H => (blockTallRootCount a b threshold H : ℝ)) (fullLaw x n) := by
  have hs : Integrable (fun H => ∑ v ∈ Reverse.phaseLabels x n b,
      if v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)
        then (1 : ℝ) else 0) (fullLaw x n) :=
    integrable_finsetSum _ (fun _ _ => history_indicator_integrable _ _)
  apply hs.congr
  filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
  exact (blockTallRootCount_eq_sum hH threshold).symm

/-- Exact first moment of the actual tall-root count, including frozen roots
and the extinction endpoint. This is the probability bridge needed for L12. -/
theorem integral_blockTallRootCount (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n)
    (threshold : ℝ) :
    (∫ H, (blockTallRootCount a b threshold H : ℝ) ∂fullLaw x n) =
      (activeCount x b : ℝ) *
      (bernoulliPartialSumLaw
        (fun i : Fin b => Reverse.attachmentParameter x n hn ⟨i.val, i.isLt.trans_le hb⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val)).real
        {k : ℕ | threshold < (k : ℝ)} := by
  let L := Reverse.phaseLabels x n b
  let ν := bernoulliPartialSumLaw
    (fun i : Fin b => Reverse.attachmentParameter x n hn ⟨i.val, i.isLt.trans_le hb⟩)
    (Finset.univ.filter fun i : Fin b => a ≤ i.val)
  let A : Set ℕ := {k | threshold < (k : ℝ)}
  have hfactor (v : ℕ ⊕ ℕ) (hv : v ∈ L) :
      (fullLaw x n).real {H | v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)} =
        (fullLaw x n).real {H | v ∈ (stage H b).roots} * ν.real A := by
    have hvn := mem_vertexLabels_of_mem_phaseLabels hv
    have hvb := (Reverse.mem_phaseLabels_iff_birthTime hb hvn).mp hv
    rw [root_height_event_eq_difference_event]
    exact depth_difference_event_and_root x n hn hvn hab hvb A
  calc
    _ = ∫ H, ∑ v ∈ L,
        if v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)
          then (1 : ℝ) else 0 ∂fullLaw x n := by
      apply integral_congr_ae
      filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
      exact blockTallRootCount_eq_sum hH threshold
    _ = ∑ v ∈ L, (fullLaw x n).real
        {H | v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)} := by
      rw [integral_finsetSum L
        (f := fun v H => if v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)
          then (1 : ℝ) else 0)
        (fun v _ => history_indicator_integrable (fullLaw x n)
          (fun H => v ∈ (stage H b).roots ∧ threshold < ((stage H a).depth v : ℝ)))]
      simp_rw [integral_history_indicator]
    _ = ∑ v ∈ L, (fullLaw x n).real {H | v ∈ (stage H b).roots} * ν.real A :=
      Finset.sum_congr rfl hfactor
    _ = (∑ v ∈ L, (fullLaw x n).real {H | v ∈ (stage H b).roots}) * ν.real A :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [sum_root_probabilities x n hn hb]

end Freezing1.ReverseHistory
