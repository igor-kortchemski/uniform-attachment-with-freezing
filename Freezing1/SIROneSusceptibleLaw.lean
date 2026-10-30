module

public import Freezing1.SIRCountLaw
public import Freezing1.CountableMarkovAvoidance

/-!
# The genuine SIR future with one susceptible individual

The complete stopped-kernel law is derived from its actual first-step
recursion. Its first infection time has a constructed truncated geometric
law; no finite-word probabilities are assumed as hypotheses.
-/

@[expose] public section

namespace Freezing1.SIR.OneSusceptible

open MeasureTheory ProbabilityTheory CountableMarkovChain Filter Set
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

abbrev History := ℕ → Counts

def prepend (c : Counts) (H : History) : History := fun k => k.casesOn c H

theorem measurable_prepend (c : Counts) : Measurable (prepend c) := by
  apply Measurable.of_eval
  intro k
  cases k <;> dsimp [prepend] <;> fun_prop

noncomputable def historyLaw (rate : ℝ≥0) (c : Counts) : Measure History :=
  CountableMarkovChain.fullLaw (countsKernel rate) c

instance historyLaw_probability (rate : ℝ≥0) (c : Counts) :
    IsProbabilityMeasure (historyLaw rate c) := by unfold historyLaw; infer_instance

noncomputable def law (rate : ℝ≥0) (m : ℕ) : Measure History := historyLaw rate ⟨1, m⟩

instance law_probability (rate : ℝ≥0) (m : ℕ) : IsProbabilityMeasure (law rate m) := by
  unfold law
  infer_instance

theorem historyLaw_legal (rate : ℝ≥0) (c : Counts) :
    ∀ᵐ H ∂historyLaw rate c, ∀ k, (H k).LegalNext (H (k + 1)) :=
  CountableMarkovChain.fullLaw_steps (countsKernel rate) c Counts.LegalNext
    (countsKernel_legal rate)

theorem historyLaw_firstStep (rate : ℝ≥0) (c : Counts) :
    historyLaw rate c = ((countsKernel rate c).bind (historyLaw rate)).map (prepend c) := by
  have hh := fullLaw_map_shift_one (countsKernel rate) c
  change (historyLaw rate c).map (shift 1) = (countsKernel rate c).bind (historyLaw rate) at hh
  rw [← hh, Measure.map_map (measurable_prepend c) (measurable_shift 1)]
  have he : prepend c ∘ shift 1 =ᵐ[historyLaw rate c] id := by
    filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) c] with H hH
    funext k
    cases k with
    | zero => exact hH.symm
    | succ k =>
      change H (1 + k) = H (k + 1)
      rw [Nat.add_comm]
  rw [Measure.map_congr he, Measure.map_id]

theorem bind_two_dirac (a b : Counts) (p q : ℝ≥0) (f : Counts → Measure History) :
    (p • Measure.dirac a + q • Measure.dirac b).bind f = p • f a + q • f b := by
  ext A hA
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rw [lintegral_dirac' _ (measurable_of_countable _),
    lintegral_dirac' _ (measurable_of_countable _)]
  rfl

def recoveryPath (u m : ℕ) : History := fun k => ⟨u, m - k⟩

theorem legalNext_zero_susceptible {c d : Counts} (h : c.LegalNext d)
    (hu : c.susceptible = 0) : d = recoverCounts c := by
  rcases h with ⟨hi, rfl⟩ | ⟨_, hnext⟩
  · cases d
    simp_all [recoverCounts]
  · rcases hnext with ⟨hup, _⟩ | hd
    · omega
    · exact hd

theorem historyLaw_absorbed (rate : ℝ≥0) (u : ℕ) :
    historyLaw rate ⟨u, 0⟩ = Measure.dirac (recoveryPath u 0) := by
  have hae : ∀ᵐ H ∂historyLaw rate ⟨u, 0⟩, H = recoveryPath u 0 := by
    filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) (⟨u, 0⟩ : Counts),
      historyLaw_legal rate ⟨u, 0⟩] with H h0 hl
    funext k
    rw [legalHistory_absorbed_persists hl (by rw [h0]) k (Nat.zero_le k), h0]
    simp [recoveryPath]
  have hh : HasLaw (id : History → History) (Measure.dirac (recoveryPath u 0))
      (historyLaw rate ⟨u, 0⟩) := hasLaw_dirac_of_ae_eq hae
  simpa only [Measure.map_id] using hh.map_eq

theorem historyLaw_zero_susceptible (rate : ℝ≥0) (m : ℕ) :
    historyLaw rate ⟨0, m⟩ = Measure.dirac (recoveryPath 0 m) := by
  have hae : ∀ᵐ H ∂historyLaw rate ⟨0, m⟩, H = recoveryPath 0 m := by
    filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) (⟨0, m⟩ : Counts),
      historyLaw_legal rate ⟨0, m⟩] with H h0 hl
    funext k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [legalNext_zero_susceptible (hl k) (by rw [ih]; rfl), ih]
      change (⟨0, m - k - 1⟩ : Counts) = ⟨0, m - (k + 1)⟩
      congr 1
  have hh : HasLaw (id : History → History) (Measure.dirac (recoveryPath 0 m))
      (historyLaw rate ⟨0, m⟩) := hasLaw_dirac_of_ae_eq hae
  simpa only [Measure.map_id] using hh.map_eq

def firstTimeShift (t : ℕ) : ℕ := if t = 0 then 0 else t + 1

noncomputable def firstTimeLaw (p : unitInterval) : ℕ → Measure ℕ
  | 0 => Measure.dirac 0
  | m + 1 => unitInterval.toNNReal p • Measure.dirac 1 +
      unitInterval.toNNReal (unitInterval.symm p) • (firstTimeLaw p m).map firstTimeShift

instance firstTimeLaw_probability (p : unitInterval) (m : ℕ) :
    IsProbabilityMeasure (firstTimeLaw p m) := by
  induction m with
  | zero => change IsProbabilityMeasure (Measure.dirac (0 : ℕ)); infer_instance
  | succ m ih =>
    constructor
    change (unitInterval.toNNReal p • Measure.dirac (1 : ℕ) +
      unitInterval.toNNReal (unitInterval.symm p) • (firstTimeLaw p m).map firstTimeShift) univ = 1
    simp

def run (m t : ℕ) : History := fun k =>
  if t = 0 ∨ k < t then ⟨1, m - k⟩ else ⟨0, m + 2 - k⟩

theorem run_shift (m t : ℕ) :
    run (m + 1) (firstTimeShift t) = prepend ⟨1, m + 1⟩ (run m t) := by
  funext k
  cases k with
  | zero => by_cases ht : t = 0 <;> simp [run, prepend, firstTimeShift, ht]
  | succ k =>
    by_cases ht : t = 0
    · simp [run, prepend, firstTimeShift, ht]
    · simp only [run, prepend, firstTimeShift, Nat.succ_ne_zero,
        false_or, Nat.succ_lt_succ_iff, ht, ↓reduceIte]
      split_ifs <;> congr 1 <;> omega

theorem run_first (m : ℕ) :
    run (m + 1) 1 = prepend ⟨1, m + 1⟩ (recoveryPath 0 (m + 2)) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    simp only [run, prepend, recoveryPath, one_ne_zero, false_or,
      Nat.succ_lt_succ_iff, Nat.not_lt_zero, ↓reduceIte]
    congr 1
    omega

theorem law_firstStep (rate : ℝ≥0) (m : ℕ) :
    law rate (m + 1) =
      unitInterval.toNNReal (infectionProbability rate 1) •
        Measure.dirac (prepend ⟨1, m + 1⟩ (recoveryPath 0 (m + 2))) +
      unitInterval.toNNReal (unitInterval.symm (infectionProbability rate 1)) •
        (law rate m).map (prepend ⟨1, m + 1⟩) := by
  rw [law, historyLaw_firstStep]
  rw [countsKernel_split rate (by norm_num : 0 < (⟨1, m + 1⟩ : Counts).infectious),
    bind_two_dirac, Measure.map_add _ _ (measurable_prepend _)]
  simp only [infectCounts, recoverCounts, Nat.add_sub_cancel, Nat.sub_self,
    historyLaw_zero_susceptible,
    Measure.map_smul _ (measurable_prepend _).aemeasurable,
    Measure.map_dirac' (measurable_prepend _)]
  rfl

/-- The full actual stopped-kernel marginal, with no assumed geometric
probabilities or path-law equality as a premise. -/
theorem law_eq_firstTimeLaw_map (rate : ℝ≥0) (m : ℕ) :
    law rate m = (firstTimeLaw (infectionProbability rate 1) m).map (run m) := by
  induction m with
  | zero =>
    rw [law, historyLaw_absorbed]
    simp only [firstTimeLaw, Measure.map_dirac' (measurable_of_countable _)]
    rfl
  | succ m ih =>
    rw [law_firstStep, firstTimeLaw,
      Measure.map_add _ _ (measurable_of_countable _),
      Measure.map_smul _ (measurable_of_countable _).aemeasurable,
      Measure.map_smul _ (measurable_of_countable _).aemeasurable,
      Measure.map_dirac' (measurable_of_countable _), ih,
      Measure.map_map (measurable_prepend _) (measurable_of_countable _),
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have hfun : prepend (⟨1, m + 1⟩ : Counts) ∘ run m = run (m + 1) ∘ firstTimeShift := by
      funext t
      exact (run_shift m t).symm
    rw [run_first, hfun]

end Freezing1.SIR.OneSusceptible
