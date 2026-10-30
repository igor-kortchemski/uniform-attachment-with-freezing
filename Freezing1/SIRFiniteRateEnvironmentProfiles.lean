module

public import Freezing1.SIRFiniteRateNearBulk
public import Freezing1.SIRRandomEnvironmentTransferNearBulk
public import Freezing1.SIRRandomEnvironmentTransferSampling

/-!
# Actual adaptive finite-rate environments satisfy each finite constraint

Near-origin and bulk errors are controlled on one common early-survival
gate. The finite family is chosen before the gate size, preserving the
two-stage quantifier order needed in the finite-parameter regime.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

def CountsNearBulkGood (cutoff : ℕ → ℕ) (c : ℝ) (window floor : ℕ → ℝ)
    (m : ℕ) (C : ℕ → Counts) (J : ℕ) : Prop :=
  (∀ j ≤ J, ∀ i : ℕ, cutoff m ≤ i → i ≤ m → (i : ℝ) ≤ window j * m →
    |((C i).infectious : ℝ) / i - c| ≤ 1 / ((j : ℝ) + 1)) ∧
  (∀ j ≤ J, ∀ i : ℕ, (m : ℝ) / ((j : ℝ) + 2) ≤ i → i ≤ m →
    floor j ≤ ((C i).infectious : ℝ) / m)

theorem feasible_alive_wordCountsAt (n : ℕ) {K : ℕ} (w : Fin K → Bool)
    (hw : SignWordFeasible n w) {m : ℕ} (hm : m ≤ K)
    (halive : 0 < (wordCountsAt n w m).infectious) :
    PositiveThrough (ForwardAnnealed.wordSchedule w) m ∧
      ∀ i ≤ m, ((wordCountsAt n w i).infectious : ℤ) =
        activeCount (ForwardAnnealed.wordSchedule w) i := by
  have hpref := feasible_alive_countsPrefix n (takeSigns w hm) (feasible_takeSigns n w hw hm)
    (by simpa only [countsRunWord_takeSigns] using halive)
  have hagree := takeSigns_schedule_agree w hm
  constructor
  · intro i hi
    rw [activeCount_eq_of_schedulesAgreeThrough (hagree.mono hi)]
    exact hpref.1 i hi
  · intro i hi
    have hcounts := hpref.2 ⟨i, Finset.mem_Iic.mpr hi⟩
    have he : takeSigns (takeSigns w hm) hi = takeSigns w (hi.trans hm) := by
      funext j
      rfl
    have hp : countsPrefixWord n (takeSigns w hm) ⟨i, Finset.mem_Iic.mpr hi⟩ =
        wordCountsAt n w i := by
      have hh := countsRunWord_takeSigns n (takeSigns w hm) hi
      rw [he, countsRunWord_takeSigns] at hh
      change wordCountsAt n w i =
        (if h : i ≤ m then countsPrefixWord n (takeSigns w hm) ⟨i, Finset.mem_Iic.mpr h⟩
          else countsRunWord n (takeSigns w hm)) at hh
      simpa only [dite_eq_left hi] using hh.symm
    rw [hp, ← activeCount_eq_of_schedulesAgreeThrough (hagree.mono hi)] at hcounts
    exact hcounts

theorem CountsNearBulkGood.to_word {n K m J : ℕ} (cutoff : ℕ → ℕ)
    {c : ℝ} (window floor : ℕ → ℝ) (hwindow : ∀ j, window j < 1)
    (w : Fin K → Bool) (hw : SignWordFeasible n w) (hm : m ≤ K)
    (halive : 0 < (wordCountsAt n w m).infectious)
    (hgood : CountsNearBulkGood cutoff c window floor m (wordCountsAt n w) J) :
    NearBulkGood cutoff c window floor m (ForwardAnnealed.wordSchedule w) J := by
  have hc := (feasible_alive_wordCountsAt n w hw hm halive).2
  constructor
  · intro j hj i hi hitime
    have him : i ≤ m := by
      have hh := mul_le_mul_of_nonneg_right (hwindow j).le (Nat.cast_nonneg (α := ℝ) m)
      have hh' : (i : ℝ) ≤ m := hitime.trans (by simpa only [one_mul] using hh)
      exact_mod_cast hh'
    have he : ((wordCountsAt n w i).infectious : ℝ) =
        (activeCount (ForwardAnnealed.wordSchedule w) i : ℝ) := by exact_mod_cast hc i him
    rw [← he]
    exact hgood.1 j hj i hi him hitime
  · intro j hj i hi him
    have he : ((wordCountsAt n w i).infectious : ℝ) =
        (activeCount (ForwardAnnealed.wordSchedule w) i : ℝ) := by exact_mod_cast hc i him
    rw [← he]
    exact hgood.2 j hj i hi him

theorem measurableSet_countsNearBulkGood (cutoff : ℕ → ℕ) (c : ℝ)
    (window floor : ℕ → ℝ) (m J : ℕ) :
    MeasurableSet {C : ℕ → Counts | CountsNearBulkGood cutoff c window floor m C J} := by
  unfold CountsNearBulkGood
  measurability

theorem countsFullLaw_finite_constraints_failure_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam)
    (window : ℕ → ℝ)
    (hnear : ∀ j, Tendsto (fun n => countsFullLaw (rate n) n
      {C | ∃ i ≥ cutoff ⌊t * (n : ℝ)⌋₊, (i : ℝ) ≤ window j * ⌊t * (n : ℝ)⌋₊ ∧
        0 < (C i).infectious ∧ 1 / ((j : ℝ) + 1) ≤
          |((C i).infectious : ℝ) / i - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
      atTop (nhds 0))
    (J : ℕ) {delta : ℝ} (hd : 0 < delta)
    (hdsmall : delta < infectiousProfile lam t / (8 * ((J : ℝ) + 2))) :
    Tendsto (fun n => countsFullLaw (rate n) n
      {C | 0 < (C ⌊delta * (n : ℝ)⌋₊).infectious ∧
        0 < (C ⌊t * (n : ℝ)⌋₊).infectious ∧
        ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
          window (finiteRateBulkFloor lam t) ⌊t * (n : ℝ)⌋₊ C J}) atTop (nhds 0) := by
  let A : ℕ → ℕ → Set (ℕ → Counts) := fun n j =>
    {C | ∃ i ≥ cutoff ⌊t * (n : ℝ)⌋₊, (i : ℝ) ≤ window j * ⌊t * (n : ℝ)⌋₊ ∧
      0 < (C i).infectious ∧ 1 / ((j : ℝ) + 1) ≤
        |((C i).infectious : ℝ) / i - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|}
  let B : ℕ → ℕ → Set (ℕ → Counts) := fun n j =>
    {C | 0 < (C ⌊delta * (n : ℝ)⌋₊).infectious ∧ ∃ i : ℕ,
      (⌊t * (n : ℝ)⌋₊ : ℝ) / ((j : ℝ) + 2) ≤ i ∧ i ≤ ⌊t * (n : ℝ)⌋₊ ∧
      ((C i).infectious : ℝ) / ⌊t * (n : ℝ)⌋₊ < finiteRateBulkFloor lam t j}
  have hB (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      Tendsto (fun n => countsFullLaw (rate n) n (B n j)) atTop (nhds 0) := by
    apply countsFullLaw_finiteRate_bulk_failure_tendsto rate hlam hrate ht htt j hd
    apply hdsmall.trans_le
    apply div_le_div_of_nonneg_left (infectiousProfile_pos_before hlam ht htt).le (by positivity)
    have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hj' 2) (by norm_num)
  have hsum := tendsto_finsetSum (Finset.range (J + 1))
    (fun j hj => (hnear j).add (hB j hj))
  simp only [add_zero, Finset.sum_const_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  calc
    _ ≤ countsFullLaw (rate n) n (⋃ j ∈ Finset.range (J + 1), A n j ∪ B n j) := by
      apply measure_mono_ae
      filter_upwards [countsFullLaw_legal (rate n) n] with C hlegal
      rintro ⟨hgate, halive, hbad⟩
      by_contra hnot
      apply hbad
      constructor
      · intro j hj i hcut him hitime
        by_contra hfail
        apply hnot
        apply mem_iUnion.mpr
        refine ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), Or.inl ?_⟩⟩
        exact ⟨i, hcut, hitime, StoppedCoupling.legalHistory_positive_before hlegal halive i him,
          (lt_of_not_ge hfail).le⟩
      · intro j hj i hi him
        by_contra hfail
        apply hnot
        apply mem_iUnion.mpr
        refine ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), Or.inr ?_⟩⟩
        exact ⟨hgate, i, hi, him, lt_of_not_ge hfail⟩
    _ ≤ ∑ j ∈ Finset.range (J + 1), countsFullLaw (rate n) n (A n j ∪ B n j) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (J + 1),
        (countsFullLaw (rate n) n (A n j) + countsFullLaw (rate n) n (B n j)) :=
      Finset.sum_le_sum fun _ _ => measure_union_le _ _

end Freezing1.SIR
