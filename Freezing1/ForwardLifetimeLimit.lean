module

public import Freezing1.ForwardLifetimeEvents
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The exact event of survival forever

Continuity from above is applied to measurable finite-history events. Their
probabilities equal the current active-vertex probabilities because an old
vertex cannot become active again. This identifies the actual infinite
survival event, including its strictly positive probability in the summable
case, and gives the freezing criterion on the common probability space.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem LegalOrHeld.active_old {x : SignSequence} {n : ℕ} {s q : State}
    (h : LegalOrHeld x n s q) {r : ℕ} (hr : r ≤ n) :
    r ∈ q.active → r ∈ s.active := by
  rcases h with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · exact id
  · intro hq
    exact (step_active_old hr hp _).mp hq |>.1

theorem active_old_antitone {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {r a b : ℕ} (hr : r ≤ a) (hab : a ≤ b) :
    r ∈ (H b).active → r ∈ (H a).active := by
  induction b, hab using Nat.le_induction with
  | base => exact id
  | succ b hab ih => exact fun hb => ih ((hl b).active_old (hr.trans hab) hb)

/-- The event that an ID remains active at every horizon after time a. -/
def survivesForever (r a : ℕ) : Set History :=
  {H | ∀ k, r ∈ (H (a + k)).active}

theorem measurableSet_survivesForever (r a : ℕ) : MeasurableSet (survivesForever r a) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro k
  exact (measurable_from_top : Measurable (fun s : State => r ∈ s.active)).comp
    (measurable_pi_apply (a + k))

/-- The finite marginals converge to the probability of the actual event
of survival forever, on the same coherent infinite trajectory. -/
theorem treeLaw_survival_limit (x : SignSequence) (a : ℕ) {r : ℕ} (hr : r ≤ a) :
    Tendsto (fun n => (treeLaw x (a + n)) {s | r ∈ s.active}) atTop
      (𝓝 ((fullLaw x) (survivesForever r a))) := by
  let E : ℕ → Set History := fun n => {H | ∀ k ≤ n, r ∈ (H (a + k)).active}
  have hmeas : ∀ n, MeasurableSet (E n) := by
    intro n
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro k
    exact measurable_const.imp
      ((measurable_from_top : Measurable (fun s : State => r ∈ s.active)).comp
        (measurable_pi_apply (a + k)))
  have hanti : Antitone E := by
    intro n m hnm H hH k hk
    exact hH k (hk.trans hnm)
  have hinter : (⋂ n, E n) = survivesForever r a := by
    ext H
    simp only [Set.mem_iInter, E, survivesForever, Set.mem_ofPred_eq]
    exact ⟨fun h k => h k k le_rfl, fun h _ k _ => h k⟩
  have hprob : ∀ n, (fullLaw x) (E n) = (treeLaw x (a + n)) {s | r ∈ s.active} := by
    intro n
    calc
      _ = (fullLaw x) {H | r ∈ (H (a + n)).active} := by
        apply measure_congr
        filter_upwards [fullLaw_legalOrHeld x] with H hH
        apply propext
        change (∀ k ≤ n, r ∈ (H (a + k)).active) ↔ r ∈ (H (a + n)).active
        constructor
        · exact fun h => h n le_rfl
        · intro hn k hk
          exact active_old_antitone hH (hr.trans (Nat.le_add_right a k))
            (Nat.add_le_add_left hk a) hn
      _ = _ := by
        rw [← map_eval x (a + n), Measure.map_apply (measurable_pi_apply _) (by trivial)]
        rfl
  have hlim := tendsto_measure_iInter_atTop (μ := fullLaw x)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at hlim
  exact hlim.congr' (Eventually.of_forall hprob)

theorem treeLaw_survival_limit_real (x : SignSequence) (a : ℕ) {r : ℕ} (hr : r ≤ a) :
    Tendsto (fun n => (treeLaw x (a + n)).real {s | r ∈ s.active}) atTop
      (𝓝 ((fullLaw x).real (survivesForever r a))) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (treeLaw_survival_limit x a hr)

/-- The corrected product criterion is now a criterion for a genuine
infinite event, rather than only a limit of marginal probabilities. -/
theorem root_survival_zero_iff (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    (fullLaw x) (survivesForever 0 0) = 0 ↔
      ¬Summable (printedFreezingReciprocal x) := by
  have hlim := treeLaw_survival_limit_real x 0 (r := 0) le_rfl
  simp only [Nat.zero_add] at hlim
  constructor
  · intro hz
    have hzR : (fullLaw x).real (survivesForever 0 0) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz
    rw [hzR] at hlim
    exact (treeLaw_root_survival_tendsto_zero_iff x hτ).mp hlim
  · intro hdiv
    have hz := (treeLaw_root_survival_tendsto_zero_iff x hτ).mpr hdiv
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (tendsto_nhds_unique hlim hz)

theorem root_survival_pos_of_summable (x : SignSequence) (hτ : extinctionTime x = ⊤)
    (hsum : Summable (printedFreezingReciprocal x)) :
    0 < (fullLaw x) (survivesForever 0 0) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (root_survival_zero_iff x hτ).mp hz hsum

/-- Almost-sure eventual freezing of the root is exactly the source's
reciprocal-series divergence condition. -/
theorem root_eventually_frozen_iff (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    (∀ᵐ H ∂fullLaw x, ∃ a j, ∀ m ≥ a, (H m).frozenAt 0 = some j) ↔
      ¬Summable (printedFreezingReciprocal x) := by
  constructor
  · intro hfreeze
    apply (root_survival_zero_iff x hτ).mp
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hfreeze, fullLaw_valid x] with H hH hv
    intro hsurv
    obtain ⟨a, j, ha⟩ := hH
    have hactive : 0 ∈ (H a).active := by simpa only [Nat.zero_add] using hsurv a
    have hnone := (hv a).active_iff 0 (hv a).root_mem |>.mp hactive
    have hsome := ha a le_rfl
    rw [hnone] at hsome
    contradiction
  · exact fullLaw_root_eventually_frozen x hτ

/-- The criterion for simultaneous freezing of every vertex that occurs in
the actual infinite tree. -/
theorem all_vertices_eventually_frozen_iff (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    (∀ᵐ H ∂fullLaw x, ∀ r n, r ∈ (H n).vertices →
      ∃ a j, ∀ m ≥ a, (H m).frozenAt r = some j) ↔
        ¬Summable (printedFreezingReciprocal x) := by
  constructor
  · intro hall
    apply (root_eventually_frozen_iff x hτ).mp
    filter_upwards [hall, fullLaw_valid x] with H hH hv
    exact hH 0 0 (hv 0).root_mem
  · exact fullLaw_all_vertices_eventually_frozen x hτ

end Freezing1.ForwardInfiniteHistory
