module

public import Freezing1.ForwardAnnealedHistory
public import Freezing1.ForwardLocalLimit
public import Freezing1.ForwardLifetimeLimit
public import Mathlib.Analysis.PSeries

/-!
# Eventual freezing under the actual iid-sign law

The one-step freezing risk of an old active vertex is at least
`(1-p)/(n+1)`. This bound is integrated over the real forward state law.
It includes absorption and the endpoint `p = 0`.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Forward ForwardInfiniteHistory Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators Classical

set_option backward.isDefEq.respectTransparency false

theorem transitionLaw_apply_split (p : unitInterval) (s : State) (t : ℕ) (A : Set State) :
    transitionLaw p s t A =
      (unitInterval.toNNReal p : ℝ≥0∞) * Forward.transitionLaw s t true A +
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) *
        Forward.transitionLaw s t false A := by
  rw [transitionLaw_apply, signLaw, bernoulliMeasure_def, lintegral_add_measure]
  simp

theorem transitionLaw_old_active_probability {n : ℕ} {s : State}
    (p : unitInterval) {r : ℕ} (hr : r ≤ n) :
    (transitionLaw p s (n + 1)).real {q | r ∈ q.active} =
      if r ∈ s.active then 1 - (1 - (p : ℝ)) / (s.active.card : ℝ) else 0 := by
  by_cases hne : s.active.Nonempty
  · change ((transitionLaw p s (n + 1)) {q | r ∈ q.active}).toReal = _
    rw [transitionLaw_apply_split, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_mul]
    change (p : ℝ) * (Forward.transitionLaw s (n + 1) true).real {q | r ∈ q.active} +
      (1 - (p : ℝ)) * (Forward.transitionLaw s (n + 1) false).real {q | r ∈ q.active} = _
    rw [Forward.transitionLaw_old_active_probability hne hr,
      Forward.transitionLaw_old_active_probability hne hr]
    by_cases hmem : r ∈ s.active
    · simp only [hmem, ite_true, Bool.false_eq_true, ite_false,
        one_mul]
      ring
    · simp [hmem]
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [transitionLaw_eq_dirac_of_empty p he]
    simp [he]

theorem transitionLaw_old_active_le {n : ℕ} {s : State} (hs : ValidAt n s)
    (p : unitInterval) {r : ℕ} (hr : r ≤ n) :
    transitionLaw p s (n + 1) {q | r ∈ q.active} ≤
      {q : State | r ∈ q.active}.indicator
        (fun _ => ENNReal.ofReal (1 - (1 - (p : ℝ)) / (n + 1 : ℝ))) s := by
  rw [← ofReal_measureReal, transitionLaw_old_active_probability p hr]
  by_cases hmem : r ∈ s.active
  · simp only [hmem, ite_true, Set.indicator_of_mem, Set.mem_ofPred_eq]
    apply ENNReal.ofReal_le_ofReal
    have hpos : (0 : ℝ) < s.active.card := by exact_mod_cast Finset.card_pos.mpr ⟨r, hmem⟩
    have hcard : s.active.card ≤ n + 1 := by
      apply le_trans (Finset.card_le_card hs.active_subset)
      apply le_trans (Finset.card_le_card (t := Finset.range (n + 1)) ?_) (by simp)
      intro v hv
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs.vertices_le v hv))
    have hcardR : (s.active.card : ℝ) ≤ n + 1 := by exact_mod_cast hcard
    have hh := div_le_div_of_nonneg_left (sub_nonneg.mpr p.property.2) hpos hcardR
    linarith
  · simp [hmem]

private theorem treeLaw_valid_lifetime (p : unitInterval) (n : ℕ) :
    ∀ᵐ s ∂treeLaw p n, ValidAt n s := by
  rw [← map_eval]
  apply (ae_map_iff (measurable_pi_apply n).aemeasurable (by trivial)).mpr
  exact (fullLaw_valid p).mono fun H hH => hH n

theorem treeLaw_old_active_succ_le (p : unitInterval) (n : ℕ) {r : ℕ} (hr : r ≤ n) :
    treeLaw p (n + 1) {q | r ∈ q.active} ≤
      ENNReal.ofReal (1 - (1 - (p : ℝ)) / (n + 1 : ℝ)) *
        treeLaw p n {q | r ∈ q.active} := by
  rw [treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ ≤ ∫⁻ s, {q : State | r ∈ q.active}.indicator
        (fun _ => ENNReal.ofReal (1 - (1 - (p : ℝ)) / (n + 1 : ℝ))) s ∂treeLaw p n := by
      apply lintegral_mono_ae
      filter_upwards [treeLaw_valid_lifetime p n] with s hs
      exact transitionLaw_old_active_le hs p hr
    _ = _ := lintegral_indicator_const (by trivial) _

noncomputable def survivalRisk (p : unitInterval) (n : ℕ) : ℝ :=
  (1 - (p : ℝ)) / ((n : ℝ) + 2)

theorem survivalRisk_nonneg (p : unitInterval) (n : ℕ) : 0 ≤ survivalRisk p n := by
  unfold survivalRisk
  exact div_nonneg (sub_nonneg.mpr p.property.2) (by positivity)

theorem survivalRisk_lt_one (p : unitInterval) (n : ℕ) : survivalRisk p n < 1 := by
  unfold survivalRisk
  apply (div_lt_one (by positivity)).mpr
  have := p.property.1
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem not_summable_survivalRisk (p : unitInterval) (hp : (p : ℝ) < 1) :
    ¬Summable (survivalRisk p) := by
  intro hsum
  have hq : 1 - (p : ℝ) ≠ 0 := by linarith
  change Summable (fun n : ℕ => (1 - (p : ℝ)) / ((n : ℝ) + 2)) at hsum
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    apply (summable_mul_left_iff hq).mp
    simpa only [div_eq_mul_inv, one_mul] using hsum
  have hh' : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hh
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp hh')

theorem treeLaw_old_active_tail_bound (p : unitInterval) (r k : ℕ) :
    treeLaw p (r + 1 + k) {q | r ∈ q.active} ≤
      ENNReal.ofReal (∏ i ∈ Finset.range k, (1 - survivalRisk p (r + i))) := by
  induction k with
  | zero => simpa using (prob_le_one : treeLaw p (r + 1) {q | r ∈ q.active} ≤ 1)
  | succ k ih =>
    have hfactor : 1 - (1 - (p : ℝ)) / ((r + 1 + k : ℕ) + 1 : ℝ) =
        1 - survivalRisk p (r + k) := by
      unfold survivalRisk
      congr 2
      push_cast
      ring
    calc
      _ ≤ ENNReal.ofReal (1 - (1 - (p : ℝ)) / ((r + 1 + k : ℕ) + 1 : ℝ)) *
          treeLaw p (r + 1 + k) {q | r ∈ q.active} :=
        treeLaw_old_active_succ_le p (r + 1 + k) (by omega)
      _ ≤ ENNReal.ofReal (1 - survivalRisk p (r + k)) *
          ENNReal.ofReal (∏ i ∈ Finset.range k, (1 - survivalRisk p (r + i))) := by
        rw [hfactor]
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (survivalRisk_lt_one p _).le),
          Finset.prod_range_succ, mul_comm]

theorem treeLaw_old_active_tendsto_zero (p : unitInterval) (hp : (p : ℝ) < 1) (r : ℕ) :
    Tendsto (fun k => (treeLaw p (r + 1 + k)).real {q | r ∈ q.active}) atTop (𝓝 0) := by
  have hprod := (tendsto_survivalProduct_tail_zero_iff_not_summable
    (survivalRisk_nonneg p) (survivalRisk_lt_one p) r).mpr (not_summable_survivalRisk p hp)
  simp only [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left] at hprod
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hprod
  intro k
  have hb := ENNReal.toReal_mono (by finiteness) (treeLaw_old_active_tail_bound p r k)
  have hnonneg : 0 ≤ ∏ i ∈ Finset.range k, (1 - survivalRisk p (r + i)) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.mpr (survivalRisk_lt_one p _).le
  change ((treeLaw p (r + 1 + k)) {q | r ∈ q.active}).toReal ≤ _
  simpa only [ENNReal.toReal_ofReal hnonneg] using hb

theorem fullLaw_exists_not_active (p : unitInterval) (hp : (p : ℝ) < 1) (r : ℕ) :
    ∀ᵐ H ∂fullLaw p, ∃ k, r ∉ (H (r + 1 + k)).active := by
  let E : Set History := {H | ∀ k, r ∈ (H (r + 1 + k)).active}
  have hbound : ∀ k, (fullLaw p).real E ≤
      (treeLaw p (r + 1 + k)).real {s | r ∈ s.active} := by
    intro k
    have he : (fullLaw p).real {H | r ∈ (H (r + 1 + k)).active} =
        (treeLaw p (r + 1 + k)).real {s | r ∈ s.active} := by
      rw [← map_eval p (r + 1 + k), map_measureReal_apply (measurable_pi_apply _) (by trivial)]
      rfl
    rw [← he]
    exact measureReal_mono (fun H hH => hH k) (measure_ne_top _ _)
  have hz : (fullLaw p).real E = 0 := le_antisymm
    (ge_of_tendsto (treeLaw_old_active_tendsto_zero p hp r)
      (Eventually.of_forall hbound)) measureReal_nonneg
  have hnull : (fullLaw p) E = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
  apply ae_iff.mpr
  have he : {H : History | ¬∃ k, r ∉ (H (r + 1 + k)).active} = E := by
    ext H
    simp only [E, Set.mem_ofPred_eq, not_exists, not_not]
  rw [he]
  exact hnull

theorem exists_schedule_of_legalOrHeld {H : History}
    (hl : ∀ n, ∃ sign : Bool, LegalOrHeld (fun _ => sign) n (H n) (H (n + 1))) :
    ∃ x : SignSequence, ∀ n, LegalOrHeld x n (H n) (H (n + 1)) := by
  choose sign hsign using hl
  refine ⟨fun i => sign (i - 1), fun n => ?_⟩
  simpa only [LegalOrHeld, LegalStep, Nat.add_sub_cancel] using hsign n

theorem fullLaw_all_vertices_eventually_frozen (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p, ∀ r n, r ∈ (H n).vertices →
      ∃ a j, ∀ m ≥ a, (H m).frozenAt r = some j := by
  have hall : ∀ᵐ H ∂fullLaw p, ∀ r, ∃ k, r ∉ (H (r + 1 + k)).active :=
    ae_all_iff.mpr (fullLaw_exists_not_active p hp)
  filter_upwards [hall, fullLaw_valid p, fullLaw_legalOrHeld p] with H hdead hv hl
  obtain ⟨x, hlx⟩ := exists_schedule_of_legalOrHeld hl
  intro r n hr
  obtain ⟨k, hk⟩ := hdead r
  let a := max n (r + 1 + k)
  have hmem : r ∈ (H a).vertices := by
    have hm : ∀ m ≥ n, r ∈ (H m).vertices := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hr
      | succ m hm ih => exact (hlx m).vertices_mono ih
    exact hm a (le_max_left _ _)
  have hnot : r ∉ (H a).active := by
    intro ha
    exact hk (active_old_antitone hlx (by omega) (le_max_right _ _) ha)
  have hne : (H a).frozenAt r ≠ none := fun he => hnot ((hv a).active_iff r hmem |>.mpr he)
  cases hj : (H a).frozenAt r with
  | none => exact (hne hj).elim
  | some j => exact ⟨a, j, frozenAt_persists hv hlx hmem hj⟩

theorem fullLaw_all_balls_stabilize (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p, ∀ h, ∃ a, ∀ n ≥ a, localBall (H n) h = localBall (H a) h := by
  filter_upwards [fullLaw_valid p, fullLaw_legalOrHeld p,
    fullLaw_all_vertices_eventually_frozen p hp] with H hv hl hf
  obtain ⟨x, hlx⟩ := exists_schedule_of_legalOrHeld hl
  exact all_balls_stabilize hv hlx hf

theorem fullLaw_tendsto_localLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  filter_upwards [fullLaw_valid p, fullLaw_all_balls_stabilize p hp] with H hv hs
  apply tendsto_localLimit_of_exists
  apply LocalTree.exists_limit_of_balls_stabilize
  intro h
  obtain ⟨a, ha⟩ := hs h
  refine ⟨a, fun n hn => ?_⟩
  simp only [(hv n).localTreeOfState_balls, (hv a).localTreeOfState_balls]
  exact ha n hn

theorem aemeasurable_localLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    AEMeasurable localLimit (fullLaw p) :=
  aemeasurable_of_tendsto_metrizable_ae'
    (fun n => (measurable_localTree_eval n).aemeasurable)
    (fullLaw_tendsto_localLimit p hp)

noncomputable def localProbabilityLaw (p : unitInterval) (n : ℕ) :
    ProbabilityMeasure LocalTree.Tree :=
  ProbabilityMeasure.map (⟨treeLaw p n, inferInstance⟩ : ProbabilityMeasure State)
    localTreeOfState

noncomputable def localLimitLaw (p : unitInterval) : ProbabilityMeasure LocalTree.Tree :=
  ProbabilityMeasure.map (⟨fullLaw p, inferInstance⟩ : ProbabilityMeasure History) localLimit

theorem map_eval_localTree (p : unitInterval) (n : ℕ) :
    (fullLaw p).map (fun H : History => localTreeOfState (H n)) =
      (localProbabilityLaw p n : Measure LocalTree.Tree) := by
  change _ = (treeLaw p n).map localTreeOfState
  rw [← map_eval p n, Measure.map_map measurable_from_top (measurable_pi_apply n)]
  rfl

theorem tendsto_localProbabilityLaw (p : unitInterval) (hp : (p : ℝ) < 1) :
    Tendsto (localProbabilityLaw p) atTop (𝓝 (localLimitLaw p)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hc := fullLaw_tendsto_localLimit p hp
  have hlim := tendsto_integral_filter_of_norm_le_const (μ := fullLaw p)
    (F := fun n H => f (localTreeOfState (H n))) (f := fun H => f (localLimit H))
    (Eventually.of_forall fun n =>
      (f.continuous.measurable.comp (measurable_localTree_eval n)).aestronglyMeasurable)
    ⟨‖f‖, Eventually.of_forall fun _ => Eventually.of_forall fun H => f.norm_coe_le_norm _⟩
    (hc.mono fun H hH => (f.continuous.tendsto _).comp hH)
  have hleft : ∀ n, (∫ t, f t ∂(localProbabilityLaw p n : Measure LocalTree.Tree)) =
      ∫ H, f (localTreeOfState (H n)) ∂fullLaw p := by
    intro n
    rw [← map_eval_localTree]
    exact integral_map (measurable_localTree_eval n).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  have hright : (∫ t, f t ∂(localLimitLaw p : Measure LocalTree.Tree)) =
      ∫ H, f (localLimit H) ∂fullLaw p :=
    integral_map (aemeasurable_localLimit p hp)
      f.continuous.measurable.aestronglyMeasurable
  simpa only [hleft, hright] using hlim

end Freezing1.ForwardAnnealed
