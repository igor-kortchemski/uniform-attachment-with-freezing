module

public import Freezing1.SIRCounts
public import Freezing1.SIRProbability
public import Freezing1.ForwardAnnealedSigns

/-!
# The genuine finite potential-sign words of the SIR counts

At each step a fresh Bernoulli sign is sampled with the probability supplied
by the actual susceptible count of the preceding word. Signs continue to be
sampled after absorption; the stopped count update then holds the counts.
These signs are not assumed independent. Their finite laws approach iid
words because all early susceptible counts differ from the initial count by
at most the length of the word.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators Classical

set_option backward.isDefEq.respectTransparency false

def countsRunWord (n : ℕ) : {k : ℕ} → (Fin k → Bool) → Counts
  | 0, _ => initialCounts n
  | k + 1, w => countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))

theorem countsRunWord_snoc (n : ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    countsRunWord n (Fin.snoc w b) = countsStep (countsRunWord n w) b := by
  simp only [countsRunWord, Fin.init_snoc, Fin.snoc_last]

theorem countsRunWord_valid (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    (countsRunWord n w).Valid n := by
  induction k with
  | zero => exact initialCounts_valid n
  | succ k ih => exact (ih (Fin.init w)).step _

private theorem countsStep_susceptible_bounds (c : Counts) (b : Bool) :
    (countsStep c b).susceptible ≤ c.susceptible ∧
      c.susceptible ≤ (countsStep c b).susceptible + 1 := by
  unfold countsStep
  split_ifs <;> simp [infectCounts, recoverCounts]
  all_goals omega

theorem countsRunWord_susceptible_bounds (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    n-k ≤ (countsRunWord n w).susceptible ∧ (countsRunWord n w).susceptible ≤ n := by
  induction k with
  | zero => simp [countsRunWord, initialCounts]
  | succ k ih =>
    have hi := ih (Fin.init w)
    have hs := countsStep_susceptible_bounds (countsRunWord n (Fin.init w)) (w (Fin.last k))
    change n - (k+1) ≤ (countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))).susceptible ∧
      (countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))).susceptible ≤ n
    omega

noncomputable def signWordLaw (rate : NNReal) (n : ℕ) : (k : ℕ) → Measure (Fin k → Bool)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | k + 1 => (signWordLaw rate n k).bind (fun w =>
      (bernoulliMeasure true false
        (infectionProbability rate (countsRunWord n w).susceptible)).map (Fin.snoc w))

instance signWordLaw_probability (rate : NNReal) (n k : ℕ) :
    IsProbabilityMeasure (signWordLaw rate n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Eventually.of_forall fun w => by infer_instance)

theorem snoc_eq_iff {k : ℕ} (v : Fin k → Bool) (b : Bool) (w : Fin (k+1) → Bool) :
    Fin.snoc v b = w ↔ v = Fin.init w ∧ b = w (Fin.last k) := by
  constructor
  · intro h
    constructor
    · simpa only [Fin.init_snoc] using congrArg Fin.init h
    · simpa only [Fin.snoc_last] using congrFun h (Fin.last k)
  · rintro ⟨rfl, rfl⟩
    exact Fin.snoc_init_self w

theorem signWordLaw_singleton_succ (rate : NNReal) (n k : ℕ) (w : Fin (k+1) → Bool) :
    signWordLaw rate n (k+1) {w} = signWordLaw rate n k {Fin.init w} *
      bernoulliMeasure true false (infectionProbability rate
        (countsRunWord n (Fin.init w)).susceptible) {w (Fin.last k)} := by
  rw [signWordLaw, Measure.bind_apply (measurableSet_singleton w)
    (measurable_of_countable _).aemeasurable]
  let B : ℝ≥0∞ := bernoulliMeasure true false (infectionProbability rate
    (countsRunWord n (Fin.init w)).susceptible) {w (Fin.last k)}
  have he (v : Fin k → Bool) : (Fin.snoc v) ⁻¹' {w} =
      if v = Fin.init w then {w (Fin.last k)} else ∅ := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, snoc_eq_iff]
    by_cases hv : v = Fin.init w <;> simp [hv]
  calc
    _ = ∫⁻ v, ({Fin.init w} : Set (Fin k → Bool)).indicator (fun _ => B) v
        ∂signWordLaw rate n k := by
      apply lintegral_congr
      intro v
      rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton w), he v]
      by_cases hv : v = Fin.init w <;> simp [hv, B]
    _ = B * signWordLaw rate n k {Fin.init w} :=
      lintegral_indicator_const (measurableSet_singleton _) B
    _ = _ := mul_comm _ _

theorem signWordLaw_real_singleton_succ (rate : NNReal) (n k : ℕ) (w : Fin (k+1) → Bool) :
    (signWordLaw rate n (k+1)).real {w} = (signWordLaw rate n k).real {Fin.init w} *
      (bernoulliMeasure true false (infectionProbability rate
        (countsRunWord n (Fin.init w)).susceptible)).real {w (Fin.last k)} := by
  change (signWordLaw rate n (k+1) {w}).toReal = _
  rw [signWordLaw_singleton_succ, ENNReal.toReal_mul]
  rfl

theorem word_infectionProbability_tendsto (rate : ℕ → NNReal) (l : NNReal)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (l : ℝ)))
    {k : ℕ} (w : Fin k → Bool) :
    Tendsto (fun n => (infectionProbability (rate n) (countsRunWord n w).susceptible : ℝ))
      atTop (𝓝 (infectionProbability l 1 : ℝ)) := by
  have hlim : (infectionProbability l 1 : ℝ) = (l : ℝ) / (1 + (l : ℝ)) := by
    rw [infectionProbability_coe]
    simp only [Nat.cast_one, mul_one]
  rw [hlim]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [infectionProbability_prefix_tendsto rate l.property hl k hε] with n hn
  have hb := countsRunWord_susceptible_bounds n w
  rw [Real.dist_eq]
  exact hn _ hb.1 hb.2

theorem word_infectionProbability_tendsto_one (rate : ℕ → NNReal)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {k : ℕ} (w : Fin k → Bool) :
    Tendsto (fun n => (infectionProbability (rate n) (countsRunWord n w).susceptible : ℝ))
      atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [infectionProbability_prefix_tendsto_one rate hl k hε] with n hn
  have hb := countsRunWord_susceptible_bounds n w
  simpa only [Real.dist_eq] using hn _ hb.1 hb.2

theorem bernoulli_sign_real_singleton (p : unitInterval) (b : Bool) :
    (bernoulliMeasure true false p).real {b} = if b then (p : ℝ) else 1 - (p : ℝ) := by
  cases b <;> simp [bernoulliMeasure_real_apply p (measurableSet_singleton _)]

theorem finiteSignLaw_real_singleton (p : unitInterval) (k : ℕ) (w : Fin k → Bool) :
    (ForwardAnnealed.finiteSignLaw p k).real {w} =
      ∏ i : Fin k, (bernoulliMeasure true false p).real {w i} := by
  change ((Measure.pi fun _ : Fin k => bernoulliMeasure true false p) {w}).toReal = _
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

private theorem signWordLaw_singleton_tendsto_of_parameters
    (rate : ℕ → NNReal) (p : unitInterval)
    (hp : ∀ k (w : Fin k → Bool),
      Tendsto (fun n => (infectionProbability (rate n) (countsRunWord n w).susceptible : ℝ))
        atTop (𝓝 (p : ℝ)))
    (k : ℕ) (w : Fin k → Bool) :
    Tendsto (fun n => (signWordLaw (rate n) n k).real {w}) atTop
      (𝓝 ((ForwardAnnealed.finiteSignLaw p k).real {w})) := by
  rw [finiteSignLaw_real_singleton]
  induction k with
  | zero =>
    have hw : w = fun i : Fin 0 => Fin.elim0 i := by funext i; exact Fin.elim0 i
    simp only [hw, signWordLaw, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, ENNReal.toReal_one,
      Fin.prod_univ_zero]
    exact tendsto_const_nhds
  | succ k ih =>
    have hlast : Tendsto (fun n => (bernoulliMeasure true false
        (infectionProbability (rate n) (countsRunWord n (Fin.init w)).susceptible)).real
          {w (Fin.last k)}) atTop
        (𝓝 ((bernoulliMeasure true false p).real {w (Fin.last k)})) := by
      simp only [bernoulli_sign_real_singleton]
      cases hb : w (Fin.last k)
      · simpa only [hb, Bool.false_eq_true, ite_false] using
          tendsto_const_nhds.sub (hp k (Fin.init w))
      · simpa only [hb, ite_true] using hp k (Fin.init w)
    have hh := (ih (Fin.init w)).mul hlast
    simpa only [signWordLaw_real_singleton_succ, Fin.prod_univ_castSucc, Fin.init] using hh

theorem signWordLaw_singleton_tendsto (rate : ℕ → NNReal) (l : NNReal)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (l : ℝ)))
    (k : ℕ) (w : Fin k → Bool) :
    Tendsto (fun n => (signWordLaw (rate n) n k).real {w}) atTop
      (𝓝 ((ForwardAnnealed.finiteSignLaw (infectionProbability l 1) k).real {w})) :=
  signWordLaw_singleton_tendsto_of_parameters rate (infectionProbability l 1)
    (fun _ w => word_infectionProbability_tendsto rate l hl w) k w

theorem signWordLaw_singleton_tendsto_one (rate : ℕ → NNReal)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (k : ℕ) (w : Fin k → Bool) :
    Tendsto (fun n => (signWordLaw (rate n) n k).real {w}) atTop
      (𝓝 ((ForwardAnnealed.finiteSignLaw 1 k).real {w})) :=
  signWordLaw_singleton_tendsto_of_parameters rate 1
    (fun _ w => word_infectionProbability_tendsto_one rate hl w) k w

end Freezing1.SIR
