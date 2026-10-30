module

public import Freezing1.ForwardHistorySupport
public import Freezing1.HistoryProbability

/-!
# Exact masses on the actual forward support

The genuine uniform active-choice kernel assigns one reciprocal population
factor to each legal output. Unique predecessor reconstruction evaluates the
Markov bind, and actual history existence supplies the support condition.
This proves the forward product formula on its corrected reachable support;
it does not adopt the source's false shape-only support assertion.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal BigOperators

noncomputable def pointStepMass (x : SignSequence) (n : ℕ) : ℝ≥0∞ :=
  ((activeCount x n).toNat : ℝ≥0∞)⁻¹

set_option backward.isDefEq.respectTransparency false in
/-- Each legal active choice has exactly one preimage in the finite uniform kernel. -/
theorem transitionLaw_step_singleton {n : ℕ} {s : State} (hs : ValidAt n s)
    (hd : CanonicalDefaults s) (hl : LabelsValidAt n s) (sign : Bool)
    {v : ℕ} (hv : v ∈ s.active) :
    (transitionLaw s (n + 1) sign) {step s (n + 1) sign v} = (s.active.card : ℝ≥0∞)⁻¹ := by
  rw [transitionLaw_apply s (n + 1) sign ⟨v, hv⟩]
  have hf : s.active.filter (fun w => step s (n + 1) sign w ∈
      ({step s (n + 1) sign v} : Set State)) = {v} := by
    ext w
    simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, he⟩
      exact step_injective_on hs hd hl sign hw hv he
    · rintro rfl
      exact ⟨hv, rfl⟩
  rw [hf]
  simp

theorem transitionLaw_legalStep_mass {x : SignSequence} {n : ℕ} {s H : State}
    (hd : PhaseData x n s) (hs : LegalStep x n s H) :
    (transitionLaw s (n + 1) (x (n + 1))) {H} = pointStepMass x n := by
  obtain ⟨v, hv, rfl⟩ := hs
  rw [transitionLaw_step_singleton hd.valid hd.defaults hd.labels _ hv]
  unfold pointStepMass
  have hc : s.active.card = (activeCount x n).toNat := by
    simpa only [Int.toNat_natCast] using congrArg Int.toNat hd.count
  rw [hc]

theorem transitionLaw_singleton_zero {x : SignSequence} {n : ℕ} {s H : State}
    (hne : s.active.Nonempty) (hs : ¬ LegalStep x n s H) :
    (transitionLaw s (n + 1) (x (n + 1))) {H} = 0 := by
  apply measure_mono_null (t := {G | ¬ LegalStep x n s G}) _
    (ae_iff.mp (transitionLaw_ae_legalStep x n s hne))
  intro G hG
  change ¬ LegalStep x n s G
  simpa only [Set.mem_singleton_iff.mp hG] using hs

/-- The actual bind at a legal output has exactly one contributing predecessor. -/
theorem treeLaw_singleton_succ {x : SignSequence} {n : ℕ} {s H : State}
    (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x)
    (hd : PhaseData x n s) (hs : LegalStep x n s H) :
    (treeLaw x (n + 1)) {H} = pointStepMass x n * (treeLaw x n) {s} := by
  have hnτ : (n : ℕ∞) < extinctionTime x :=
    lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
  rw [treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ r, ({s} : Set State).indicator (fun _ => pointStepMass x n) r ∂treeLaw x n := by
      apply lintegral_congr_ae
      filter_upwards [treeLaw_phaseData x n hnτ.le, treeLaw_active_nonempty x n hnτ]
        with r hdr hne
      by_cases he : r = s
      · subst r
        simp only [Set.indicator_of_mem (show s ∈ ({s} : Set State) from rfl)]
        exact transitionLaw_legalStep_mass hd hs
      · have hnot : ¬ LegalStep x n r H := by
          intro hr
          exact he (legalStep_predecessor_eq hdr.valid hd.valid hdr.defaults hd.defaults hd.labels hr hs)
        rw [transitionLaw_singleton_zero hne hnot]
        simp [he]
    _ = _ := lintegral_indicator_const (by trivial) _

/-- Exact partial-history mass under the actual forward construction. -/
theorem treeLaw_singleton_of_history_at {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (F : ℕ → State) (hinit : F 0 = initial)
    (hd : ∀ i ≤ n, PhaseData x i (F i))
    (hs : ∀ i < n, LegalStep x i (F i) (F (i + 1))) (k : ℕ) (hk : k ≤ n) :
    (treeLaw x k) {F k} = ∏ i ∈ Finset.range k, pointStepMass x i := by
  induction k with
  | zero => simp [treeLaw, hinit]
  | succ k ih =>
    have hkτ : ((k + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast hk) hn
    rw [treeLaw_singleton_succ hkτ (hd k (by omega)) (hs k (by omega)), ih (by omega),
      Finset.prod_range_succ, mul_comm]

theorem pointStepMass_toReal {x : SignSequence} {i : ℕ}
    (hi : (i : ℕ∞) ≤ extinctionTime x) :
    (pointStepMass x i).toReal = (activeCount x i : ℝ)⁻¹ := by
  simp only [pointStepMass, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hi)

/-- The actual terminal point probability of a legal history is exactly L04's
product, with the required corrected reachability hypothesis made explicit. -/
theorem treeLaw_real_singleton_of_history {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (F : ℕ → State) (hinit : F 0 = initial)
    (hd : ∀ i ≤ n, PhaseData x i (F i))
    (hs : ∀ i < n, LegalStep x i (F i) (F (i + 1))) :
    (treeLaw x n).real {F n} = forwardHistoryWeight x n := by
  rw [Measure.real, treeLaw_singleton_of_history_at hn F hinit hd hs n le_rfl, ENNReal.toReal_prod]
  unfold forwardHistoryWeight
  apply Finset.prod_congr rfl
  intro i hi
  exact pointStepMass_toReal (le_trans (show (i : ℕ∞) ≤ n by
    exact_mod_cast (Finset.mem_range.mp hi).le) hn)

theorem treeLaw_real_singleton_of_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {H : State} (hH : HasHistory x n H) :
    (treeLaw x n).real {H} = forwardHistoryWeight x n := by
  obtain ⟨F, hcur, hinit, hd, hs⟩ := hH
  simpa only [hcur] using treeLaw_real_singleton_of_history hn F hinit hd hs

/-- Every actual terminal outcome has the source forward product mass almost surely. -/
theorem treeLaw_real_singleton_ae (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂treeLaw x n, (treeLaw x n).real {H} = forwardHistoryWeight x n := by
  filter_upwards [treeLaw_hasHistory x n hn] with H hH
  exact treeLaw_real_singleton_of_hasHistory x n hn hH

/-- Correct forward support: a positive atom is equivalent to a legal history. -/
theorem treeLaw_singleton_ne_zero_iff_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (H : State) :
    (treeLaw x n) {H} ≠ 0 ↔ HasHistory x n H := by
  constructor
  · intro hmass
    by_contra hhist
    apply hmass
    apply measure_mono_null (t := {G | ¬ HasHistory x n G}) _
      (ae_iff.mp (treeLaw_hasHistory x n hn))
    intro G hG
    change ¬ HasHistory x n G
    simpa only [Set.mem_singleton_iff.mp hG] using hhist
  · intro hhist hzero
    have hm := treeLaw_real_singleton_of_hasHistory x n hn hhist
    rw [Measure.real, hzero, ENNReal.toReal_zero] at hm
    exact (ne_of_gt (forwardHistoryWeight_pos x n hn)) hm.symm

end Freezing1.Forward
