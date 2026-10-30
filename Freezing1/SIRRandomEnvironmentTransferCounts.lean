module

public import Freezing1.SIRFixedWordBridge
public import Freezing1.SIRStartup
public import Freezing1.BalancedSchedule

/-!
# Full count histories of the actual adaptive word environment

Uniform-in-time environment estimates are transported through an exact
finite-prefix law. Equality of individual-time tree marginals alone is not
used to infer a path property.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter CountableMarkovChain
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

def countsPrefixWord (n : ℕ) : {k : ℕ} → (Fin k → Bool) → Prefix (E := Counts) k
  | 0, _ => fun _ => initialCounts n
  | _k + 1, w => prefixAppend (countsPrefixWord n (Fin.init w)) (countsRunWord n w)

theorem countsPrefixWord_snoc (n : ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    countsPrefixWord n (Fin.snoc w b) =
      prefixAppend (countsPrefixWord n w) (countsStep (countsRunWord n w) b) := by
  simp only [countsPrefixWord, Fin.init_snoc, countsRunWord_snoc]

theorem countsPrefixWord_last (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    countsPrefixWord n w ⟨k, Finset.mem_Iic.mpr le_rfl⟩ = countsRunWord n w := by
  cases k with
  | zero => rfl
  | succ k => simp [countsPrefixWord, prefixAppend]

/-- The complete count prefix, not only its endpoint, has the genuine SIR
Markov path law under the actual adaptive sign-word measure. -/
theorem signWordLaw_map_countsPrefixWord (rate : ℝ≥0) (n k : ℕ) :
    (signWordLaw rate n k).map (countsPrefixWord n) =
      (countsFullLaw rate n).map (Preorder.frestrictLe k) := by
  rw [countsFullLaw, CountableMarkovChain.map_prefix]
  induction k with
  | zero =>
    rw [signWordLaw, Measure.map_dirac' (measurable_of_countable _),
      Kernel.partialTraj_self, Kernel.id_apply]
    rfl
  | succ k ih =>
    rw [signWordLaw, Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable,
      partialTraj_successor (countsKernel rate) (Nat.zero_le k), ← ih,
      Measure.bind_map (measurable_of_countable _).aemeasurable
        (measurable_appended_transition (countsKernel rate) k).aemeasurable]
    congr 1
    funext w
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      countsPrefixWord_last]
    change (bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible)).map
      (countsPrefixWord n ∘ Fin.snoc w) =
      ((bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible)).map
        (countsStep (countsRunWord n w))).map (prefixAppend (countsPrefixWord n w))
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext b
    exact countsPrefixWord_snoc n w b

theorem activeCount_eq_of_schedulesAgreeThrough {x y : SignSequence} {k : ℕ}
    (h : SchedulesAgreeThrough x y k) : activeCount x k = activeCount y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [activeCount_succ, activeCount_succ, ih (h.mono (Nat.le_succ k)),
      h (k + 1) (by omega) le_rfl]

theorem wordSchedule_agree_init {k : ℕ} (w : Fin (k + 1) → Bool) :
    SchedulesAgreeThrough (ForwardAnnealed.wordSchedule w)
      (ForwardAnnealed.wordSchedule (Fin.init w)) k := by
  have hh := ForwardAnnealed.wordSchedule_snoc_prefix (Fin.init w) (w (Fin.last k))
  simpa only [Fin.snoc_init_self] using hh

theorem wordSchedule_last {k : ℕ} (w : Fin (k + 1) → Bool) :
    ForwardAnnealed.wordSchedule w (k + 1) = w (Fin.last k) := by
  conv_lhs => rw [← Fin.snoc_init_self w]
  exact ForwardAnnealed.wordSchedule_snoc_last _ _

/-- On a feasible word alive at its horizon, every prefix count is the
source's unstopped integer walk, and the walk stays positive throughout. -/
theorem feasible_alive_countsPrefix (n : ℕ) {k : ℕ} (w : Fin k → Bool)
    (hw : SignWordFeasible n w) (halive : 0 < (countsRunWord n w).infectious) :
    PositiveThrough (ForwardAnnealed.wordSchedule w) k ∧
      ∀ i : Finset.Iic k, ((countsPrefixWord n w i).infectious : ℤ) =
        activeCount (ForwardAnnealed.wordSchedule w) i.val := by
  induction k with
  | zero =>
    constructor
    · intro i hi
      have : i = 0 := by omega
      subst i
      simp
    · intro i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.property; omega
      simp [countsPrefixWord, initialCounts, hi]
  | succ k ih =>
    have hlegal := countsStep_legal_of_feasible (countsRunWord n (Fin.init w))
      (w (Fin.last k)) hw.2
    have hprev : 0 < (countsRunWord n (Fin.init w)).infectious :=
      hlegal.infectious_pos_previous halive
    obtain ⟨hpositive, hcounts⟩ := ih (Fin.init w) hw.1 hprev
    have hprefix := wordSchedule_agree_init w
    have hcountk : ((countsRunWord n (Fin.init w)).infectious : ℤ) =
        activeCount (ForwardAnnealed.wordSchedule w) k := by
      rw [activeCount_eq_of_schedulesAgreeThrough hprefix]
      simpa only [countsPrefixWord_last] using hcounts ⟨k, Finset.mem_Iic.mpr le_rfl⟩
    have hend : ((countsRunWord n w).infectious : ℤ) =
        activeCount (ForwardAnnealed.wordSchedule w) (k + 1) := by
      rw [activeCount_succ, wordSchedule_last, ← hcountk]
      change ((countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))).infectious : ℤ) = _
      cases hb : w (Fin.last k) with
      | false =>
        simp [countsStep, hprev.ne', recoverCounts, Nat.cast_sub (show 1 ≤
          (countsRunWord n (Fin.init w)).infectious by omega)]
        omega
      | true =>
        have hu : (countsRunWord n (Fin.init w)).susceptible ≠ 0 := by
          intro hz
          have hh := hw.2 hz
          simp [hb] at hh
        simp [countsStep, hprev.ne', hu, infectCounts]
    constructor
    · intro i hi
      by_cases hik : i ≤ k
      · rw [activeCount_eq_of_schedulesAgreeThrough (hprefix.mono hik)]
        exact hpositive i hik
      · have he : i = k + 1 := by omega
        rw [he, ← hend]
        exact_mod_cast halive
    · intro i
      by_cases hik : i.val ≤ k
      · have hh := hcounts ⟨i.val, Finset.mem_Iic.mpr hik⟩
        rw [← activeCount_eq_of_schedulesAgreeThrough (hprefix.mono hik)] at hh
        simpa only [countsPrefixWord, prefixAppend, dite_eq_left hik] using hh
      · have he : i = ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
          apply Subtype.ext
          change i.val = k + 1
          have := Finset.mem_Iic.mp i.property
          omega
        rw [he, countsPrefixWord_last]
        exact hend

def RegularWord (n : ℕ) {k : ℕ} (w : Fin k → Bool) : Prop :=
  SignWordFeasible n w ∧ 0 < (countsRunWord n w).infectious

theorem signWordLaw_countsPrefix_event_eq (rate : ℝ≥0) (n k : ℕ)
    (A : Set (Prefix (E := Counts) k)) :
    signWordLaw rate n k {w | countsPrefixWord n w ∈ A} =
      countsFullLaw rate n {H | Preorder.frestrictLe k H ∈ A} := by
  have hh := congrArg (fun μ : Measure (Prefix (E := Counts) k) => μ A)
    (signWordLaw_map_countsPrefixWord rate n k)
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet] at hh
  exact hh

theorem signWordLaw_map_countsRunWord (rate : ℝ≥0) (n k : ℕ) :
    (signWordLaw rate n k).map (countsRunWord n) =
      (countsFullLaw rate n).map (fun H => H k) := by
  let last : Prefix (E := Counts) k → Counts := fun q => q ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  calc
    _ = ((signWordLaw rate n k).map (countsPrefixWord n)).map last := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      congr 1
      funext w
      exact (countsPrefixWord_last n w).symm
    _ = ((countsFullLaw rate n).map (Preorder.frestrictLe k)).map last := by
      rw [signWordLaw_map_countsPrefixWord]
    _ = _ := by
      rw [Measure.map_map (measurable_of_countable _) (by fun_prop)]
      rfl

theorem signWordLaw_not_regular_le_absorption (rate : ℝ≥0) (n k : ℕ) :
    signWordLaw rate n k {w | ¬RegularWord n w} ≤
      countsFullLaw rate n {H | (H k).infectious = 0} := by
  have heq : signWordLaw rate n k {w | (countsRunWord n w).infectious = 0} =
      countsFullLaw rate n {H | (H k).infectious = 0} := by
    have hh := congrArg (fun μ : Measure Counts => μ {c | c.infectious = 0})
      (signWordLaw_map_countsRunWord rate n k)
    rw [Measure.map_apply (measurable_of_countable _) (by trivial),
      Measure.map_apply (by fun_prop) (by trivial)] at hh
    exact hh
  rw [← heq]
  apply measure_mono_ae
  filter_upwards [signWordLaw_feasible rate n k] with w hw hnot
  have hh : ¬0 < (countsRunWord n w).infectious := fun hi => hnot ⟨hw, hi⟩
  omega

theorem signWordLaw_regular_profile_error_le (rate : ℝ≥0) (n L : ℕ) (eps : ℝ) :
    signWordLaw rate n n {w | RegularWord n w ∧ ∃ i ≥ L, i ≤ n ∧
      eps ≤ |(activeCount (ForwardAnnealed.wordSchedule w) i : ℝ) / i - 1|} ≤
    countsFullLaw rate n {H | ∃ i ≥ L, i ≤ n ∧ eps ≤ |((H i).infectious : ℝ) / i - 1|} := by
  let A : Set (Prefix (E := Counts) n) := {q | ∃ i : Finset.Iic n, L ≤ i.val ∧
    eps ≤ |((q i).infectious : ℝ) / i.val - 1|}
  calc
    _ ≤ signWordLaw rate n n {w | countsPrefixWord n w ∈ A} := by
      apply measure_mono
      rintro w ⟨hw, i, hi, hin, hbad⟩
      refine ⟨⟨i, Finset.mem_Iic.mpr hin⟩, hi, ?_⟩
      have hh := (feasible_alive_countsPrefix n w hw.1 hw.2).2 ⟨i, Finset.mem_Iic.mpr hin⟩
      have hhR : ((countsPrefixWord n w ⟨i, Finset.mem_Iic.mpr hin⟩).infectious : ℝ) =
          (activeCount (ForwardAnnealed.wordSchedule w) i : ℝ) := by exact_mod_cast hh
      rw [hhR]
      exact hbad
    _ = countsFullLaw rate n {H | Preorder.frestrictLe n H ∈ A} :=
      signWordLaw_countsPrefix_event_eq rate n n A
    _ ≤ _ := by
      apply measure_mono
      rintro H ⟨i, hi, hbad⟩
      exact ⟨i.val, hi, Finset.mem_Iic.mp i.property, hbad⟩

theorem signWordLaw_not_regular_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) :
    Tendsto (fun n => signWordLaw (rate n) n n {w | ¬RegularWord n w}) atTop (nhds 0) := by
  have hgrid : Tendsto (fun n => countsFullLaw (rate n) n
      {H | ∃ k ≤ 2 * n, (1 / 2 : ℝ) * n ≤
        |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|}) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
      (countsFullLaw_triangle_tendsto_zero rate hstrong (by norm_num : (0 : ℝ) < 1 / 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgrid (fun _ => bot_le)
  intro n
  apply (signWordLaw_not_regular_le_absorption (rate n) n n).trans
  apply measure_mono
  intro H hz
  refine ⟨n, by omega, ?_⟩
  have hmin : min n (2 * n - n) = n := by omega
  rw [hz, hmin]
  simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem signWordLaw_strong_regular_profile_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => signWordLaw (rate n) n n
      {w | RegularWord n w ∧ ∃ i ≥ cutoff n, i ≤ n ∧
        eps ≤ |(activeCount (ForwardAnnealed.wordSchedule w) i : ℝ) / i - 1|})
      atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (countsFullLaw_strong_relative_until_n_tendsto rate hstrong cutoff hcutoff heps)
    (fun _ => bot_le) (fun n => signWordLaw_regular_profile_error_le (rate n) n (cutoff n) eps)

end Freezing1.SIR
