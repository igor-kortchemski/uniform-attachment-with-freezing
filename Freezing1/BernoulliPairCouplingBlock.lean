module

public import Freezing1.BernoulliPairCouplingActual
public import Freezing1.BernoulliPairCouplingWords
public import Freezing1.ReverseHistoryBernoulli
public import Freezing1.ReverseHistoryContinuation

/-! The genuine history is retained while the independent driver words are recorded. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

structure BlockSample (k : ℕ) where
  history : Base
  first : Word k
  second : Word k

instance (k : ℕ) : MeasurableSpace (BlockSample k) := ⊤
instance (k : ℕ) : DiscreteMeasurableSpace (BlockSample k) := ⟨fun _ => trivial⟩

def prependSample {k : ℕ} (u : ℕ ⊕ ℕ) (s : StepSample) (t : BlockSample k) :
    BlockSample (k + 1) :=
  ⟨t.history, Fin.cons (ReverseHistory.heightIncrement u s.history) t.first,
    Fin.cons s.auxiliary t.second⟩

noncomputable def coupledBlockLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a : ℕ) :
    (k : ℕ) → Base → Measure (BlockSample k)
  | 0, H => Measure.dirac ⟨H, Fin.elim0, Fin.elim0⟩
  | k + 1, H => (stepLaw x n hn u v (a + k) H).bind
      (fun s => (coupledBlockLaw x n hn u v a k s.history).map (prependSample u s))

instance coupledBlockLaw_probability (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    IsProbabilityMeasure (coupledBlockLaw x n hn u v a k H) := by
  induction k generalizing H with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
    exact Eventually.of_forall fun s =>
      Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr (ih s.history)

/-- The entire original history, rather than merely two marginal heights, is preserved. -/
theorem coupledBlockLaw_map_history (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    (coupledBlockLaw x n hn u v a k H).map BlockSample.history =
      ReverseHistory.blockHistoryLaw x a k H := by
  induction k generalizing H with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    rw [coupledBlockLaw,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have hf : (fun s : StepSample =>
        ((coupledBlockLaw x n hn u v a k s.history).map (prependSample u s)).map
          BlockSample.history) =
        (fun s => ReverseHistory.blockHistoryLaw x a k s.history) := by
      funext s
      rw [Measure.map_map measurable_from_top measurable_from_top]
      exact ih s.history
    rw [hf]
    rw [← Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      stepLaw_map_history]
    rfl

theorem map_blockHistoryLaw_previous_iterate (x : SignSequence) (a k : ℕ) (H : Base) :
    (ReverseHistory.blockHistoryLaw x a k H).map (ReverseHistory.previous^[k]) =
      Measure.dirac H := by
  induction k generalizing H with
  | zero => simp only [ReverseHistory.blockHistoryLaw, Function.iterate_zero, Measure.map_id]
  | succ k ih =>
    rw [ReverseHistory.blockHistoryLaw,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have he : (fun H' : Base =>
        (ReverseHistory.blockHistoryLaw x a k H').map (ReverseHistory.previous^[k + 1])) =
        (fun H' => Measure.dirac (ReverseHistory.previous H')) := by
      funext H'
      rw [Function.iterate_succ', ← Measure.map_map measurable_from_top measurable_from_top,
        ih, Measure.map_dirac' measurable_from_top]
    rw [he, Measure.bind_dirac_eq_map _ measurable_from_top,
      ReverseHistory.map_transitionLaw_previous]

theorem coupledBlockLaw_previous_iterate (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    ∀ᵐ t ∂coupledBlockLaw x n hn u v a k H,
      (ReverseHistory.previous^[k]) t.history = H := by
  apply ae_of_ae_map (f := BlockSample.history)
    (p := fun H' : Base => (ReverseHistory.previous^[k]) H' = H)
    measurable_from_top.aemeasurable
  rw [coupledBlockLaw_map_history]
  apply ae_of_ae_map (f := ReverseHistory.previous^[k])
    (p := fun H' : Base => H' = H) measurable_from_top.aemeasurable
  rw [map_blockHistoryLaw_previous_iterate]
  simp

theorem stepLaw_previous (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (i : ℕ) (H : Base) :
    ∀ᵐ s ∂stepLaw x n hn u v i H, ReverseHistory.previous s.history = H := by
  apply ae_of_ae_map (f := StepSample.history)
    (p := fun H' : Base => ReverseHistory.previous H' = H) measurable_from_top.aemeasurable
  rw [stepLaw_map_history]
  apply ae_of_ae_map (f := ReverseHistory.previous)
    (p := fun H' : Base => H' = H) measurable_from_top.aemeasurable
  rw [ReverseHistory.map_transitionLaw_previous]
  simp

theorem stepLaw_support {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ s ∂stepLaw x n hn u v i H,
      Reverse.ValidAt x n i s.history.current ∧
      u ∈ s.history.current.vertices ∧ v ∈ s.history.current.vertices := by
  apply ae_of_ae_map (f := StepSample.history)
    (p := fun H' : Base => Reverse.ValidAt x n i H'.current ∧
      u ∈ H'.current.vertices ∧ v ∈ H'.current.vertices) measurable_from_top.aemeasurable
  rw [stepLaw_map_history, ReverseHistory.transitionLaw]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [Reverse.transitionLaw_valid hn hi hH,
    Reverse.transitionLaw_present_depth_support hn hi hH hu,
    Reverse.transitionLaw_present_depth_support hn hi hH hv] with F hF hu' hv'
  exact ⟨hF, hu'.1, hv'.1⟩

/-- The complete first and auxiliary words have a genuine independent product law. -/
theorem coupledBlockLaw_map_drivers {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (coupledBlockLaw x n hn u v a k H).map (fun t => (t.first, t.second)) =
      pairWordLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k := by
  induction k generalizing H with
  | zero => simp only [coupledBlockLaw, Measure.map_dirac' measurable_from_top, pairWordLaw_zero]
  | succ k ih =>
    have hi : a + k < n := by omega
    have hH' : Reverse.ValidAt x n (a + k + 1) H.current := by
      simpa only [Nat.add_assoc] using hH
    rw [coupledBlockLaw,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have hm : (fun s : StepSample =>
        ((coupledBlockLaw x n hn u v a k s.history).map (prependSample u s)).map
          (fun t => (t.first, t.second))) =ᵐ[stepLaw x n hn u v (a + k) H]
        (fun s => (pairWordLaw (Reverse.stepParameter x n hn)
          (auxiliaryParameter x n hn) a k).map
            (fun w : Word k × Word k => (Fin.cons (ReverseHistory.heightIncrement u s.history) w.1,
              Fin.cons s.auxiliary w.2))) := by
      filter_upwards [stepLaw_support hn hi hH' hu hv] with s hs
      rw [Measure.map_map measurable_from_top measurable_from_top]
      have he := ih (H := s.history) (by omega) hs.1 hs.2.1 hs.2.2
      rw [← he, Measure.map_map (measurable_of_countable _) measurable_from_top]
      rfl
    rw [Measure.bind_congr_right hm]
    have hb := Measure.bind_map
      (m := stepLaw x n hn u v (a + k) H)
      (f := fun s => (ReverseHistory.heightIncrement u s.history, s.auxiliary))
      (g := fun h : ℕ × ℕ =>
        (pairWordLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k).map
          (fun w : Word k × Word k =>
            ((Fin.cons h.1 w.1 : Word (k + 1)), (Fin.cons h.2 w.2 : Word (k + 1)))))
      measurable_from_top.aemeasurable (measurable_of_countable _).aemeasurable
    rw [← hb, stepLaw_map_drivers hn hi hH' hu hv, pairWordLaw_succ]

/-- Every recorded coordinate is the actual increment from the completed common
history; the second coordinate satisfies the before-step coalescence formula. -/
theorem coupledBlockLaw_increment_relations {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ t ∂coupledBlockLaw x n hn u v a k H, ∀ j : Fin k,
      t.first j = ReverseHistory.phaseIncrement u (k - 1 - j.val) t.history ∧
      ReverseHistory.phaseIncrement v (k - 1 - j.val) t.history =
        if (ReverseHistory.stage t.history (k - j.val)).root u =
            (ReverseHistory.stage t.history (k - j.val)).root v
        then t.first j else t.second j * (1 - t.first j) := by
  induction k generalizing H with
  | zero => exact Eventually.of_forall fun _ j => Fin.elim0 j
  | succ k ih =>
    have hi : a + k < n := by omega
    have hH' : Reverse.ValidAt x n (a + k + 1) H.current := by
      simpa only [Nat.add_assoc] using hH
    rw [coupledBlockLaw]
    apply ae_bind_of_ae measurable_from_top.aemeasurable (by trivial)
    filter_upwards [stepLaw_support hn hi hH' hu hv, stepLaw_relation hn hi hH' hu hv,
      stepLaw_previous x n hn u v (a + k) H] with s hs hrel hprev
    apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
    filter_upwards [ih (H := s.history) (by omega) hs.1 hs.2.1 hs.2.2,
      coupledBlockLaw_previous_iterate x n hn u v a k s.history] with t ht htail
    have hphase (w : ℕ ⊕ ℕ) : ReverseHistory.phaseIncrement w k t.history =
        ReverseHistory.heightIncrement w s.history := by
      simp only [ReverseHistory.phaseIncrement, htail]
    have hstage : ReverseHistory.stage t.history (k + 1) = H.current := by
      rw [← ReverseHistory.current_previous_iterate_eq_stage,
        Function.iterate_succ_apply', htail, hprev]
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [prependSample, Fin.cons_zero, Fin.val_zero, Nat.add_sub_cancel,
        Nat.sub_zero]
      exact ⟨(hphase u).symm, by rw [hphase v, hstage]; exact hrel⟩
    · have hidx : k + 1 - 1 - (j.val + 1) = k - 1 - j.val := by
        have := j.isLt
        omega
      have hbefore : k + 1 - (j.val + 1) = k - j.val := by omega
      simpa only [prependSample, Fin.cons_succ, Fin.val_succ, hidx, hbefore] using ht j

end Freezing1.BernoulliPairCoupling
