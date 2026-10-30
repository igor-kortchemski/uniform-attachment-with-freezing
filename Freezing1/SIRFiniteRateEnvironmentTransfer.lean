module

public import Freezing1.SIRFiniteRateEnvironmentProfiles
public import Freezing1.MainSIRUniformSamplesStrong

/-!
# Averaging deterministic geometry over finite-rate adaptive words

Only finitely many near-origin and bulk constraints are selected for each
probability budget. The common survival gate is then chosen sufficiently
early. This order does not impose a deterministic profile as a hypothesis
on the random SIR environment.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment CountableMarkovChain
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

def cappedCountsPrefix {K : ℕ} (q : Prefix (E := Counts) K) (i : ℕ) : Counts :=
  q ⟨min i K, Finset.mem_Iic.mpr (min_le_right _ _)⟩

theorem cappedCountsPrefix_at {K : ℕ} (q : Prefix (E := Counts) K) {i : ℕ} (hi : i ≤ K) :
    cappedCountsPrefix q i = q ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp only [cappedCountsPrefix, min_eq_left hi]

theorem cappedCountsPrefix_countsPrefixWord (n : ℕ) {K : ℕ} (w : Fin K → Bool) :
    cappedCountsPrefix (countsPrefixWord n w) = wordCountsAt n w := by
  funext i
  by_cases hi : i ≤ K
  · simp only [cappedCountsPrefix_at _ hi, wordCountsAt, dite_eq_left hi]
  · have hKi : K ≤ i := by omega
    simp only [cappedCountsPrefix, min_eq_right hKi, countsPrefixWord_last,
      wordCountsAt, dite_eq_right hi]

/-- A complete count-history event determined through `K` has its genuine
stopped SIR law under the actual adaptive word measure. -/
theorem signWordLaw_wordCountsAt_event_eq (rate : ℝ≥0) (n K : ℕ) (A : Set (ℕ → Counts))
    (hprefix : ∀ C D : ℕ → Counts, (∀ i ≤ K, C i = D i) → (C ∈ A ↔ D ∈ A)) :
    signWordLaw rate n K {w | wordCountsAt n w ∈ A} = countsFullLaw rate n A := by
  have hh := signWordLaw_countsPrefix_event_eq rate n K {q | cappedCountsPrefix q ∈ A}
  have he : {H : ℕ → Counts | cappedCountsPrefix (Preorder.frestrictLe K H) ∈ A} = A := by
    ext H
    apply hprefix
    intro i hi
    exact cappedCountsPrefix_at _ hi
  simpa only [mem_ofPred_eq, cappedCountsPrefix_countsPrefixWord, he] using hh

theorem CountsNearBulkGood.congr {cutoff : ℕ → ℕ} {c : ℝ} {window floor : ℕ → ℝ}
    {m J : ℕ} {C D : ℕ → Counts} (he : ∀ i ≤ m, C i = D i) :
    CountsNearBulkGood cutoff c window floor m C J ↔ CountsNearBulkGood cutoff c window floor m D J := by
  unfold CountsNearBulkGood
  constructor <;> rintro ⟨hnear, hbulk⟩ <;> constructor
  · intro j hj i hi him hitime
    rw [← he i him]
    exact hnear j hj i hi him hitime
  · intro j hj i hi him
    rw [← he i him]
    exact hbulk j hj i hi him
  · intro j hj i hi him hitime
    rw [he i him]
    exact hnear j hj i hi him hitime
  · intro j hj i hi him
    rw [he i him]
    exact hbulk j hj i hi him

theorem signWordLaw_gated_finite_bad_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam)
    (window : ℕ → ℝ)
    (hnear : ∀ j, Tendsto (fun n => countsFullLaw (rate n) n
      {C | ∃ i ≥ cutoff ⌊t * (n : ℝ)⌋₊, (i : ℝ) ≤ window j * ⌊t * (n : ℝ)⌋₊ ∧
        0 < (C i).infectious ∧ 1 / ((j : ℝ) + 1) ≤
          |((C i).infectious : ℝ) / i - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
      atTop (nhds 0))
    (J : ℕ) {delta : ℝ} (hd : 0 < delta) (hdt : delta ≤ t)
    (hdsmall : delta < infectiousProfile lam t / (8 * ((J : ℝ) + 2))) :
    Tendsto (fun n => signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊
      {w | ¬SignWordFeasible n w ∨
        (0 < (wordCountsAt n w ⌊delta * (n : ℝ)⌋₊).infectious ∧
          ((countsRunWord n w).infectious = 0 ∨
            ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
              window (finiteRateBulkFloor lam t) ⌊t * (n : ℝ)⌋₊ (wordCountsAt n w) J))})
      atTop (nhds 0) := by
  have hp := infectiousProfile_pos_before hlam ht htt
  have hden : 0 < (J : ℝ) + 2 := by positivity
  have hsmall0 : delta < infectiousProfile lam t / 8 := by
    apply hdsmall.trans_le
    apply div_le_div_of_nonneg_left hp.le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hext := countsFullLaw_gated_prefix_extinct_tendsto rate hlam hrate ht htt hd hsmall0
  have hgood := countsFullLaw_finite_constraints_failure_tendsto rate lam hlam hrate
    cutoff ht htt window hnear J hd hdsmall
  have hsum := hext.add hgood
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  let m : ℕ := ⌊t * (n : ℝ)⌋₊
  let a : ℕ := ⌊delta * (n : ℝ)⌋₊
  have ham : a ≤ m := Nat.floor_mono (mul_le_mul_of_nonneg_right hdt (Nat.cast_nonneg n))
  have hzero : signWordLaw (rate n) n m {w | ¬SignWordFeasible n w} = 0 :=
    ae_iff.mp (signWordLaw_feasible (rate n) n m)
  have heq : signWordLaw (rate n) n m
      {w | 0 < (wordCountsAt n w a).infectious ∧
        ((countsRunWord n w).infectious = 0 ∨
          ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
            window (finiteRateBulkFloor lam t) m (wordCountsAt n w) J)} =
      countsFullLaw (rate n) n
        {C | 0 < (C a).infectious ∧ ((C m).infectious = 0 ∨
          ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
            window (finiteRateBulkFloor lam t) m C J)} := by
    simp_rw [← wordCountsAt_last n]
    apply signWordLaw_wordCountsAt_event_eq (rate n) n m
      {C | 0 < (C a).infectious ∧ ((C m).infectious = 0 ∨
        ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
          window (finiteRateBulkFloor lam t) m C J)}
    intro C D hCD
    simp only [mem_ofPred_eq]
    rw [hCD a ham, hCD m le_rfl, CountsNearBulkGood.congr hCD]
  calc
    _ ≤ signWordLaw (rate n) n m {w | ¬SignWordFeasible n w} +
        signWordLaw (rate n) n m {w | 0 < (wordCountsAt n w a).infectious ∧
          ((countsRunWord n w).infectious = 0 ∨
            ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
              window (finiteRateBulkFloor lam t) m (wordCountsAt n w) J)} := measure_union_le _ _
    _ = countsFullLaw (rate n) n {C | 0 < (C a).infectious ∧
        ((C m).infectious = 0 ∨ ¬CountsNearBulkGood cutoff
          (((lam : ℝ) - 1) / ((lam : ℝ) + 1)) window (finiteRateBulkFloor lam t) m C J)} := by
      rw [hzero, zero_add, heq]
    _ ≤ _ := by
      simp only [mul_comm (n : ℝ) t]
      change countsFullLaw (rate n) n
        {C | 0 < (C a).infectious ∧ ((C m).infectious = 0 ∨
          ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
            window (finiteRateBulkFloor lam t) m C J)} ≤
        countsFullLaw (rate n) n {C | 0 < (C a).infectious ∧ (C m).infectious = 0} +
        countsFullLaw (rate n) n {C | 0 < (C a).infectious ∧ 0 < (C m).infectious ∧
          ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
            window (finiteRateBulkFloor lam t) m C J}
      apply (measure_mono (t :=
        {C | 0 < (C a).infectious ∧ (C m).infectious = 0} ∪
        {C | 0 < (C a).infectious ∧ 0 < (C m).infectious ∧ ¬CountsNearBulkGood cutoff
          (((lam : ℝ) - 1) / ((lam : ℝ) + 1)) window (finiteRateBulkFloor lam t) m C J}) ?_).trans
        (measure_union_le _ _)
      rintro C ⟨hg, hz | hb⟩
      · exact Or.inl ⟨hg, hz⟩
      · by_cases hz : (C m).infectious = 0
        · exact Or.inl ⟨hg, hz⟩
        · exact Or.inr ⟨hg, by omega, hb⟩

/-- Finite-rate random-environment transfer with the source's two-stage
order: choose finitely many deterministic constraints, then choose the
early survival gate. -/
theorem finiteRate_average_score_two_stage (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam)
    (score : ℕ → SignSequence → ℝ≥0∞) (hscore : ∀ m x, score m x ≤ 1)
    (huniform : ∀ window floor : ℕ → ℝ,
      (∀ j, 0 < window j ∧ window j < 1) →
      (∀ j, 0 < floor j ∧ floor j ≤ (((lam : ℝ) - 1) / ((lam : ℝ) + 1)) / ((j : ℝ) + 2)) →
      ∀ eta > 0, ∃ J N : ℕ, ∀ m ≥ N, ∀ x, PositiveThrough x m →
        NearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1)) window floor m x J →
          (score m x).toReal < eta)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioc (0 : ℝ) delta0,
      ∀ᶠ n in atTop, (∫⁻ w,
        if 0 < (wordCountsAt n w ⌊delta * (n : ℝ)⌋₊).infectious then
          score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) else 0
        ∂signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊) < ENNReal.ofReal eps := by
  obtain ⟨window, hwindow, hnear⟩ := exists_finiteRate_near_windows rate lam hrate cutoff hcutoff ht
  obtain ⟨J, N, hN⟩ := huniform window (finiteRateBulkFloor lam t) hwindow
    (fun j => ⟨finiteRateBulkFloor_pos hlam ht htt j, finiteRateBulkFloor_le_slope lam t j⟩)
    (eps / 3) (by positivity)
  let delta0 : ℝ := min (t / 2) (infectiousProfile lam t / (16 * ((J : ℝ) + 2)))
  have hd0 : 0 < delta0 := by
    apply lt_min (half_pos ht)
    exact div_pos (infectiousProfile_pos_before hlam ht htt) (by positivity)
  refine ⟨delta0, hd0, ?_⟩
  intro delta hd
  have hdt : delta ≤ t := (hd.2.trans (min_le_left _ _)).trans (by linarith)
  have hsmall : delta < infectiousProfile lam t / (8 * ((J : ℝ) + 2)) := by
    have hh := hd.2.trans (min_le_right _ _)
    have hp := infectiousProfile_pos_before hlam ht htt
    have he : infectiousProfile lam t / (16 * ((J : ℝ) + 2)) <
        infectiousProfile lam t / (8 * ((J : ℝ) + 2)) := by
      apply div_lt_div_of_pos_left hp (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) J]
    exact hh.trans_lt he
  let B : (n : ℕ) → Set (Fin ⌊t * (n : ℝ)⌋₊ → Bool) := fun n =>
    {w | ¬SignWordFeasible n w ∨
      (0 < (wordCountsAt n w ⌊delta * (n : ℝ)⌋₊).infectious ∧
        ((countsRunWord n w).infectious = 0 ∨
          ¬CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
            window (finiteRateBulkFloor lam t) ⌊t * (n : ℝ)⌋₊ (wordCountsAt n w) J))}
  have hbad := signWordLaw_gated_finite_bad_tendsto rate lam hlam hrate cutoff ht htt
    window hnear J hd.1 hdt hsmall
  have hthird : (0 : ℝ≥0∞) < ENNReal.ofReal (eps / 3) := ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [(finiteRate_horizon_tendsto ht).eventually (eventually_ge_atTop N),
    (ENNReal.tendsto_nhds_zero.mp hbad) (ENNReal.ofReal (eps / 3)) hthird] with n hn hbn
  have hbound := lintegral_le_small_add_bad (signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊)
    (fun w => if 0 < (wordCountsAt n w ⌊delta * (n : ℝ)⌋₊).infectious then
      score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) else 0)
    (fun w => by split_ifs; exact hscore _ _; exact bot_le)
    (B n) (Set.to_countable _).measurableSet (ENNReal.ofReal (eps / 3)) (fun w hw => by
      split_ifs with hgate
      · have hf : SignWordFeasible n w := by by_contra h; exact hw (Or.inl h)
        have ha : 0 < (countsRunWord n w).infectious := by
          by_contra h
          exact hw (Or.inr ⟨hgate, Or.inl (by omega)⟩)
        have hg : CountsNearBulkGood cutoff (((lam : ℝ) - 1) / ((lam : ℝ) + 1))
            window (finiteRateBulkFloor lam t) ⌊t * (n : ℝ)⌋₊ (wordCountsAt n w) J := by
          by_contra h
          exact hw (Or.inr ⟨hgate, Or.inr h⟩)
        have hpos := (feasible_alive_countsPrefix n w hf ha).1
        have hword := hg.to_word cutoff window (finiteRateBulkFloor lam t)
          (fun j => (hwindow j).2) w hf le_rfl (by simpa only [wordCountsAt_last] using ha)
        have hs := hN _ hn _ hpos hword
        have hfin : score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) ≠ ∞ :=
          ne_top_of_le_ne_top (by norm_num) (hscore _ _)
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_le_ofReal hs.le
      · exact bot_le)
  calc
    _ ≤ ENNReal.ofReal (eps / 3) + signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊ (B n) := hbound
    _ ≤ ENNReal.ofReal (eps / 3) + ENNReal.ofReal (eps / 3) := add_le_add (le_refl _) hbn
    _ = ENNReal.ofReal (eps / 3 + eps / 3) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff heps).mpr (by linarith)

end Freezing1.SIR
