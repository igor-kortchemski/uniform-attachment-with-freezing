module

public import Freezing1.ForwardSchedulePrefix
public import Freezing1.ForwardLocalStability
public import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Comparing diagonal and fixed-schedule local balls

The comparison uses a genuine coupling of complete histories. Once the
common prefix has a frozen radius-h ball, both histories keep that same ball,
regardless of their subsequent schedules. The error is the actual probability
that the fixed-schedule ball has not frozen by the prefix time; it tends to
zero under the reciprocal-series divergence criterion.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem prefixCoupling_eval_fst (x y : SignSequence) (k n : ℕ) :
    (prefixCoupling x y k).map (fun p => p.1 n) = treeLaw x n := by
  rw [← map_eval x n, ← prefixCoupling_fst x y k,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem prefixCoupling_eval_snd {x y : SignSequence} {k : ℕ}
    (h : SchedulesAgreeThrough x y k) (n : ℕ) :
    (prefixCoupling x y k).map (fun p => p.2 n) = treeLaw y n := by
  rw [← map_eval y n, ← prefixCoupling_snd h,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Frozen prefix balls agree at all subsequent, possibly different,
horizons in the two true marginal histories. -/
theorem prefixCoupling_frozen_balls {x y : SignSequence} {k : ℕ}
    (h : SchedulesAgreeThrough x y k) (r : ℕ) :
    ∀ᵐ p ∂prefixCoupling x y k, BallFrozen (p.2 k) r →
      ∀ n ≥ k, ∀ m ≥ k, localBall (p.1 n) r = localBall (p.2 m) r := by
  have hvx : ∀ᵐ p ∂prefixCoupling x y k, ∀ n, ValidAt n (p.1 n) := by
    apply ae_of_ae_map (μ := prefixCoupling x y k) (f := Prod.fst)
      (p := fun H : History => ∀ n, ValidAt n (H n)) measurable_fst.aemeasurable
    rw [prefixCoupling_fst]
    exact fullLaw_valid x
  have hvy : ∀ᵐ p ∂prefixCoupling x y k, ∀ n, ValidAt n (p.2 n) := by
    apply ae_of_ae_map (μ := prefixCoupling x y k) (f := Prod.snd)
      (p := fun H : History => ∀ n, ValidAt n (H n)) measurable_snd.aemeasurable
    rw [prefixCoupling_snd h]
    exact fullLaw_valid y
  have hlx : ∀ᵐ p ∂prefixCoupling x y k,
      ∀ n, LegalOrHeld x n (p.1 n) (p.1 (n + 1)) := by
    apply ae_of_ae_map (μ := prefixCoupling x y k) (f := Prod.fst)
      (p := fun H : History => ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
      measurable_fst.aemeasurable
    rw [prefixCoupling_fst]
    exact fullLaw_legalOrHeld x
  have hly : ∀ᵐ p ∂prefixCoupling x y k,
      ∀ n, LegalOrHeld y n (p.2 n) (p.2 (n + 1)) := by
    apply ae_of_ae_map (μ := prefixCoupling x y k) (f := Prod.snd)
      (p := fun H : History => ∀ n, LegalOrHeld y n (H n) (H (n + 1)))
      measurable_snd.aemeasurable
    rw [prefixCoupling_snd h]
    exact fullLaw_legalOrHeld y
  filter_upwards [hvx, hvy, hlx, hly, prefixCoupling_agrees x y k]
    with p hvx hvy hlx hly hp hf n hn m hm
  have hx : BallFrozen (p.1 k) r := by rwa [hp k le_rfl]
  exact ((ballFrozen_persists hvx hlx hx n hn).2.1).trans
    ((congrArg (fun s => localBall s r) (hp k le_rfl)).trans
      (ballFrozen_persists hvy hly hf m hm).2.1.symm)

private theorem abs_event_difference_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E F B : Set Ω)
    (h : ∀ᵐ ω ∂μ, ω ∉ B → (ω ∈ E ↔ ω ∈ F)) :
    |μ.real E - μ.real F| ≤ μ.real B := by
  have hEF : μ.real E - μ.real F ≤ μ.real B := by
    apply (le_measureReal_sdiff (μ := μ) (s₁ := E) (s₂ := F)).trans
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [h] with ω hω hωEF
    by_contra hωB
    exact hωEF.2 ((hω hωB).mp hωEF.1)
  have hFE : μ.real F - μ.real E ≤ μ.real B := by
    apply (le_measureReal_sdiff (μ := μ) (s₁ := F) (s₂ := E)).trans
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [h] with ω hω hωFE
    by_contra hωB
    exact hωFE.2 ((hω hωB).mpr hωFE.1)
  exact abs_le.mpr ⟨by linarith, hEF⟩

/-- Uniform over every set of radius-h balls. The right hand side depends
only on the fixed schedule and the common prefix time. -/
theorem localBall_event_difference_le {x y : SignSequence} {k : ℕ}
    (h : SchedulesAgreeThrough x y k) {n m : ℕ} (hn : k ≤ n) (hm : k ≤ m)
    (r : ℕ) (A : Set LocalTree.Ball) :
    |(treeLaw x n).real {s | localBall s r ∈ A} -
      (treeLaw y m).real {s | localBall s r ∈ A}| ≤
        (treeLaw y k).real {s | ¬BallFrozen s r} := by
  have hbound := abs_event_difference_le (prefixCoupling x y k)
    {p | localBall (p.1 n) r ∈ A} {p | localBall (p.2 m) r ∈ A}
    {p | ¬BallFrozen (p.2 k) r} (by
      filter_upwards [prefixCoupling_frozen_balls h r] with p hp hf
      have hf' : BallFrozen (p.2 k) r := by simpa using hf
      rw [hp hf' n hn m hm])
  have hfst := prefixCoupling_eval_fst x y k n
  have hsnd := prefixCoupling_eval_snd h m
  have hbase := prefixCoupling_eval_snd h k
  have he : ∀ (f : History × History → State)
      (hf : Measurable f) (μ : Measure State) (hfμ : (prefixCoupling x y k).map f = μ)
      (E : Set State),
      (prefixCoupling x y k).real {p | f p ∈ E} = μ.real E := by
    intro f hf μ hfμ E
    rw [← hfμ]
    simp only [measureReal_def]
    rw [Measure.map_apply hf (by trivial)]
    rfl
  have he1 : (prefixCoupling x y k).real {p | localBall (p.1 n) r ∈ A} =
      (treeLaw x n).real {s | localBall s r ∈ A} := by
    simpa only [Set.mem_ofPred_eq] using he _ (by fun_prop) _ hfst {s | localBall s r ∈ A}
  have he2 : (prefixCoupling x y k).real {p | localBall (p.2 m) r ∈ A} =
      (treeLaw y m).real {s | localBall s r ∈ A} := by
    simpa only [Set.mem_ofPred_eq] using he _ (by fun_prop) _ hsnd {s | localBall s r ∈ A}
  have he3 : (prefixCoupling x y k).real {p | ¬BallFrozen (p.2 k) r} =
      (treeLaw y k).real {s | ¬BallFrozen s r} := by
    simpa only [Set.mem_ofPred_eq] using he _ (by fun_prop) _ hbase {s | ¬BallFrozen s r}
  rwa [he1, he2, he3] at hbound

theorem treeLaw_not_ballFrozen_tendsto_zero (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x))
    (r : ℕ) :
    Tendsto (fun k => (treeLaw x k).real {s | ¬BallFrozen s r}) atTop (𝓝 0) := by
  have hevent : ∀ᵐ H ∂fullLaw x, ∀ᶠ k in atTop, BallFrozen (H k) r := by
    filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x,
      fullLaw_all_vertices_eventually_frozen x hτ hdiv] with H hv hl hf
    obtain ⟨a, ha⟩ := all_balls_eventually_frozen hv hl hf r
    filter_upwards [eventually_ge_atTop a] with k hk
    exact (ballFrozen_persists hv hl ha k hk).1
  have hlim : Tendsto (fun k => (fullLaw x) {H | ¬BallFrozen (H k) r}) atTop (𝓝 0) := by
    have hm : ∀ k, MeasurableSet {H : History | ¬BallFrozen (H k) r} := by
      intro k
      exact (measurable_from_top : Measurable (fun s : State => ¬BallFrozen s r)).comp
        (measurable_pi_apply k) |>.setOf
    have hh := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (μ := fullLaw x) (A := ∅) MeasurableSet.empty hm (by
        filter_upwards [hevent] with H hH
        filter_upwards [hH] with k hk
        simp only [Set.mem_empty_iff_false, iff_false, not_not]
        exact hk)
    simpa only [measure_empty] using hh
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim
  simp only [ENNReal.toReal_zero] at hreal
  convert hreal using 1
  ext k
  rw [← map_eval x k, measureReal_def, Measure.map_apply (measurable_pi_apply k) (by trivial)]
  rfl

/-- All fixed-radius event probabilities for the diagonal tree and the
fixed-schedule tree become arbitrarily close. -/
theorem diagonal_localBall_event_difference_tendsto_zero
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal y))
    (r : ℕ) (A : Set LocalTree.Ball) :
    Tendsto (fun n => (treeLaw (x n) n).real {s | localBall s r ∈ A} -
      (treeLaw y n).real {s | localBall s r ∈ A}) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have herr := (treeLaw_not_ballFrozen_tendsto_zero y hτ hdiv r).eventually
    (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := herr.exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_schedulesAgreeThrough hxy k)
  refine ⟨max N k, fun n hn => ?_⟩
  have hkn : k ≤ n := (le_max_right N k).trans hn
  have hbound := localBall_event_difference_le (hN n ((le_max_left N k).trans hn)) hkn hkn r A
  simpa only [Real.dist_eq, sub_zero] using hbound.trans_lt hk

end Freezing1.ForwardInfiniteHistory
