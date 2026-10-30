module

public import Freezing1.SIRStoppedFluidTransfer
public import Freezing1.SIRStrongCounts

/-!
# Capturing the finite-rate terminal population by an earlier prefix

After the positive fluid zero, actual survival has vanishing probability:
an alive actual count would equal the auxiliary integer count, whose fluid
profile is strictly negative. Bounded susceptible jumps then control all
births after a prefix just before that zero.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem countsFullLaw_alive_after_fluid_zero_tendsto (rate : ℕ → ℝ≥0)
    {lam s : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (hs : fluidExtinctionTime lam < s) (hs2 : s ≤ 2) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n
      {C | 0 < (C ⌊(n : ℝ) * s⌋₊).infectious}) atTop (𝓝 0) := by
  have hl : 0 < lam := by linarith
  have hs0 : 0 ≤ s := ((fluidExtinctionTime_spec hlam).1.trans hs).le
  let eta : ℝ := -infectiousProfile lam s / 4
  have heta : 0 < eta := by
    dsimp [eta]
    linarith [infectiousProfile_neg_after hlam hs]
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      countsFullLaw (rate n) n {C | 0 < (C ⌊(n : ℝ) * s⌋₊).infectious} ≤
      StoppedCoupling.fullLaw (rate n) n {H | ∃ k ≤ n * 2,
        eta ≤ |(Susceptible.infectious n k (fun j => (H j).2) : ℝ) / n -
          infectiousProfile lam ((k : ℝ) / n)|} := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hinv.eventually (gt_mem_nhds heta)] with n hn hnsmall
    have hmap : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) :=
      measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
    have hmeas : MeasurableSet {C : ℕ → Counts | 0 < (C ⌊(n : ℝ) * s⌋₊).infectious} :=
      measurableSet_lt measurable_const
        ((measurable_of_countable Counts.infectious).comp (measurable_pi_apply _))
    rw [← StoppedCoupling.map_fullLaw_counts (rate n) n,
      Measure.map_apply hmap hmeas]
    apply measure_mono_ae
    filter_upwards [StoppedCoupling.fullLaw_counts_legal (rate n) n,
      StoppedCoupling.fullLaw_agree_until_extinction (rate n) n] with H hlegal hagree
    intro hbad
    let k : ℕ := ⌊(n : ℝ) * s⌋₊
    have hi : 0 < (H k).1.infectious := hbad
    have hp := StoppedCoupling.legalHistory_positive_before hlegal hi
    have he : ((H k).1.infectious : ℝ) =
        (Susceptible.infectious n k (fun j => (H j).2) : ℝ) := by
      exact_mod_cast (hagree k (fun j hj => hp j hj.le)).2
    have hdist := StoppedCoupling.floor_time_distance hn hs0
    have hprof := (StoppedCoupling.infectiousProfile_lipschitz hl s ((k : ℝ) / n)).trans hdist
    have hprofupper := (abs_le.mp hprof).2
    have hinon : 0 ≤ (Susceptible.infectious n k (fun j => (H j).2) : ℝ) / n := by
      rw [← he]
      positivity
    refine ⟨k, StoppedCoupling.floor_time_index_le hs2, ?_⟩
    have habs := le_abs_self
      ((Susceptible.infectious n k (fun j => (H j).2) : ℝ) / n -
        infectiousProfile lam ((k : ℝ) / n))
    dsimp [eta] at heta hnsmall ⊢
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (StoppedCoupling.joint_unstopped_fluid_tendsto rate hl hrate 2 heta)
    (Eventually.of_forall fun _ => bot_le) hbound

theorem countsFullLaw_late_births_between_times_tendsto (rate : ℕ → ℝ≥0)
    {lam t s eta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (ht : 0 ≤ t) (hts : t ≤ s) (hs : fluidExtinctionTime lam < s) (hs2 : s ≤ 2)
    (hgap : s - t < eta) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n
      {C | eta * n ≤ (C ⌊(n : ℝ) * t⌋₊).susceptible -
        ((C (2 * n + 1)).susceptible : ℝ)}) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ => (eta - (s - t)) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      countsFullLaw (rate n) n {C | eta * n ≤
        (C ⌊(n : ℝ) * t⌋₊).susceptible - ((C (2 * n + 1)).susceptible : ℝ)} ≤
      countsFullLaw (rate n) n {C | 0 < (C ⌊(n : ℝ) * s⌋₊).infectious} := by
    filter_upwards [hscale.eventually_gt_atTop 1] with n hn
    let a : ℕ := ⌊(n : ℝ) * t⌋₊
    let b : ℕ := ⌊(n : ℝ) * s⌋₊
    have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_left hts (Nat.cast_nonneg n))
    have hbN : b ≤ 2 * n + 1 := by
      have hh := StoppedCoupling.floor_time_index_le (n := n) (m := 2) hs2
      dsimp [b]
      omega
    have hfloorb : (b : ℝ) ≤ n * s :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (ht.trans hts))
    have hfloora : (n : ℝ) * t < (a : ℝ) + 1 := Nat.lt_floor_add_one _
    have htime : ((b - a : ℕ) : ℝ) < eta * n := by
      rw [Nat.cast_sub hab]
      nlinarith
    apply measure_mono_ae
    filter_upwards [countsFullLaw_legal (rate n) n] with C hlegal hbad
    by_contra hnot
    have hz : (C b).infectious = 0 := by change ¬ 0 < (C b).infectious at hnot; omega
    have hheld := legalHistory_absorbed_persists hlegal hz (2 * n + 1) hbN
    have hdrop := legalHistory_susceptible_drop hlegal hab
    have hdropR : (C a).susceptible ≤ (C b).susceptible + ((b - a : ℕ) : ℝ) := by
      exact_mod_cast hdrop
    change eta * n ≤ (C a).susceptible - ((C (2 * n + 1)).susceptible : ℝ) at hbad
    rw [hheld] at hbad
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (countsFullLaw_alive_after_fluid_zero_tendsto rate hlam hrate hs hs2)
    (Eventually.of_forall fun _ => bot_le) hbound

/-- All actual births after a fixed prefix sufficiently close to the fluid
zero form a negligible prescribed fraction of the initial population. This
bound is unconditional and includes early-extinct histories. -/
theorem countsFullLaw_late_births_near_fluid_zero_tendsto (rate : ℕ → ℝ≥0)
    {lam t eta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (ht : 0 ≤ t) (htt : t < fluidExtinctionTime lam)
    (hgap : fluidExtinctionTime lam - t < eta) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n
      {C | eta * n ≤ (C ⌊(n : ℝ) * t⌋₊).susceptible -
        ((C (2 * n + 1)).susceptible : ℝ)}) atTop (𝓝 0) := by
  have hmin : fluidExtinctionTime lam < min 2 (t + eta) :=
    lt_min (fluidExtinctionTime_spec hlam).2.1 (by linarith)
  obtain ⟨s, hs0, hs1⟩ := exists_between hmin
  exact countsFullLaw_late_births_between_times_tendsto rate hlam hrate ht
    (htt.trans hs0).le hs0 (hs1.trans_le (min_le_left _ _)).le
    (by have := hs1.trans_le (min_le_right _ _); linarith)

/-- On the shared early-survival gate, a fixed prefix strictly before the
positive fluid zero remains alive with probability tending to one. -/
theorem countsFullLaw_gated_prefix_extinct_tendsto (rate : ℕ → ℝ≥0)
    {lam t delta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (hd : 0 < delta)
    (hdsmall : delta < infectiousProfile lam t / 8) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n
      {C | 0 < (C ⌊delta * n⌋₊).infectious ∧
        (C ⌊(n : ℝ) * t⌋₊).infectious = 0}) atTop (𝓝 0) := by
  have hl : 0 < lam := by linarith
  have hprof : 0 < infectiousProfile lam t := infectiousProfile_pos_before hlam ht htt
  have ht2 : t ≤ 2 := (htt.trans (fluidExtinctionTime_spec hlam).2.1).le
  have hfluid := StoppedCoupling.gated_stopped_real_fluid_tendsto rate hl hrate 2
    (half_pos hprof) hd (by linarith : delta < infectiousProfile lam t / 2 / 4)
  have hbound : ∀ n : ℕ,
      countsFullLaw (rate n) n {C | 0 < (C ⌊delta * n⌋₊).infectious ∧
        (C ⌊(n : ℝ) * t⌋₊).infectious = 0} ≤
      StoppedCoupling.fullLaw (rate n) n {H | ∃ u ∈ Icc (0 : ℝ) (2 : ℝ),
        infectiousProfile lam t / 2 ≤ |((H ⌊(n : ℝ) * u⌋₊).1.infectious : ℝ) / n -
          (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam u) 0 else 0)|} := by
    intro n
    have hmap : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) :=
      measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
    have hm (j : ℕ) : Measurable (fun C : ℕ → Counts => (C j).infectious) :=
      (measurable_of_countable Counts.infectious).comp (measurable_pi_apply j)
    have hmeas : MeasurableSet {C : ℕ → Counts | 0 < (C ⌊delta * n⌋₊).infectious ∧
        (C ⌊(n : ℝ) * t⌋₊).infectious = 0} :=
      (measurableSet_lt measurable_const (hm _)).inter
        (measurableSet_eq_fun (hm _) measurable_const)
    rw [← StoppedCoupling.map_fullLaw_counts (rate n) n, Measure.map_apply hmap hmeas]
    apply measure_mono
    rintro H ⟨hgate, hzero⟩
    refine ⟨t, ⟨ht.le, ht2⟩, ?_⟩
    rw [ite_eq_left hgate, max_eq_left hprof.le, hzero, Nat.cast_zero, zero_div,
      zero_sub, abs_neg, abs_of_pos hprof]
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfluid
    (fun _ => bot_le) hbound

theorem legalHistory_alive_prefix_vertices {C : ℕ → Counts} {n k : ℕ}
    (h0 : C 0 = initialCounts n) (hl : ∀ j, (C j).LegalNext (C (j + 1)))
    (hi : 0 < (C k).infectious) : k ≤ 2 * (n + 1 - (C k).susceptible) := by
  have hc := legalHistory_count_identity h0 hl hi
  omega

theorem countsFullLaw_gated_prefix_small_tendsto (rate : ℕ → ℝ≥0)
    {lam t delta b : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (hd : 0 < delta)
    (hdsmall : delta < infectiousProfile lam t / 8) (hbt : 2 * b < t) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n
      {C | 0 < (C ⌊delta * n⌋₊).infectious ∧
        ((n + 1 - (C ⌊(n : ℝ) * t⌋₊).susceptible : ℕ) : ℝ) < b * n}) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ => (t - 2 * b) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      countsFullLaw (rate n) n {C | 0 < (C ⌊delta * n⌋₊).infectious ∧
        ((n + 1 - (C ⌊(n : ℝ) * t⌋₊).susceptible : ℕ) : ℝ) < b * n} ≤
      countsFullLaw (rate n) n {C | 0 < (C ⌊delta * n⌋₊).infectious ∧
        (C ⌊(n : ℝ) * t⌋₊).infectious = 0} := by
    filter_upwards [hscale.eventually_gt_atTop 1] with n hn
    apply measure_mono_ae
    filter_upwards [countsFullLaw_initial (rate n) n, countsFullLaw_legal (rate n) n]
      with C h0 hlegal hbad
    refine ⟨hbad.1, ?_⟩
    by_contra hnot
    have hi : 0 < (C ⌊(n : ℝ) * t⌋₊).infectious := by omega
    have hcard := legalHistory_alive_prefix_vertices h0 hlegal hi
    have hcardR : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤
        2 * ((n + 1 - (C ⌊(n : ℝ) * t⌋₊).susceptible : ℕ) : ℝ) := by exact_mod_cast hcard
    have hfloor := Nat.lt_floor_add_one ((n : ℝ) * t)
    have hsmall := hbad.2
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (countsFullLaw_gated_prefix_extinct_tendsto rate hlam hrate ht htt hd hdsmall)
    (Eventually.of_forall fun _ => bot_le) hbound

/-- On one shared early-survival gate, a prefix close to the positive fluid
zero misses fewer than `eta*n` terminal vertices and has at least a fixed
positive fraction of `n` vertices, outside an event of vanishing probability. -/
theorem countsFullLaw_gated_capture_tendsto (rate : ℕ → ℝ≥0)
    {lam t delta eta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (ht : fluidExtinctionTime lam / 2 < t) (htt : t < fluidExtinctionTime lam)
    (hgap : fluidExtinctionTime lam - t < eta)
    (hd : 0 < delta) (hdsmall : delta < infectiousProfile lam t / 8) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n {C |
      0 < (C ⌊delta * n⌋₊).infectious ∧
        (eta * n ≤ (C ⌊(n : ℝ) * t⌋₊).susceptible - ((C (2 * n + 1)).susceptible : ℝ) ∨
        ((n + 1 - (C ⌊(n : ℝ) * t⌋₊).susceptible : ℕ) : ℝ) <
          (fluidExtinctionTime lam / 8) * n)}) atTop (𝓝 0) := by
  have hT := fluidExtinctionTime_spec hlam
  have ht0 : 0 < t := by linarith
  have hsum := (countsFullLaw_late_births_near_fluid_zero_tendsto rate hlam hrate ht0.le htt hgap).add
    (countsFullLaw_gated_prefix_small_tendsto rate hlam hrate ht0 htt hd hdsmall
      (by linarith : 2 * (fluidExtinctionTime lam / 8) < t))
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  apply le_trans ?_ (measure_union_le _ _)
  apply measure_mono
  rintro C ⟨hg, hlate | hsmall⟩
  · exact Or.inl hlate
  · exact Or.inr ⟨hg, hsmall⟩

end Freezing1.SIR
