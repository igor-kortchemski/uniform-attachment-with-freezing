module

public import Freezing1.SIRFiniteRateCapture

/-!
# Unconditional terminal-to-prefix sampling capture at finite rate

On the surviving early gate the prefix has linear size. Off that same gate,
absorption makes the prefix and terminal tree identical. Thus a prefix near
the positive fluid zero misses a vanishing prescribed fraction of the
terminal vertex population.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

/-- The fraction of terminal vertices born after a fixed near-terminal
prefix is smaller than a prescribed tolerance with probability tending to
one. The tolerance controls how close the prefix is to the fluid zero. -/
theorem countsFullLaw_relative_late_births_tendsto (rate : ℕ → ℝ≥0)
    {lam t eta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (heta : 0 < eta) (ht : fluidExtinctionTime lam / 2 < t)
    (htt : t < fluidExtinctionTime lam)
    (hgap : fluidExtinctionTime lam - t < eta * (fluidExtinctionTime lam / 8)) :
    Tendsto (fun n : ℕ => countsFullLaw (rate n) n {C |
      eta * ((n + 1 - (C (2 * n + 1)).susceptible : ℕ) : ℝ) ≤
        (C ⌊(n : ℝ) * t⌋₊).susceptible - ((C (2 * n + 1)).susceptible : ℝ)})
      atTop (𝓝 0) := by
  have hT := fluidExtinctionTime_spec hlam
  have ht0 : 0 < t := by linarith
  have ht2 : t ≤ 2 := (htt.trans hT.2.1).le
  have hprof : 0 < infectiousProfile lam t := infectiousProfile_pos_before hlam ht0 htt
  let delta : ℝ := min (t / 2) (infectiousProfile lam t / 16)
  have hd : 0 < delta := lt_min (by linarith) (by positivity)
  have hdt : delta < t := (min_le_left _ _).trans_lt (by linarith)
  have hdsmall : delta < infectiousProfile lam t / 8 :=
    (min_le_right _ _).trans_lt (by linarith)
  have hcapture := countsFullLaw_gated_capture_tendsto rate hlam hrate ht htt hgap hd hdsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcapture (fun _ => bot_le)
  intro n
  let a : ℕ := ⌊delta * (n : ℝ)⌋₊
  let k : ℕ := ⌊(n : ℝ) * t⌋₊
  let N : ℕ := 2 * n + 1
  have hak : a ≤ k := Nat.floor_mono
    (show delta * (n : ℝ) ≤ (n : ℝ) * t from by
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hkN : k ≤ N := by
    have hh := StoppedCoupling.floor_time_index_le (n := n) (m := 2) ht2
    dsimp [k, N]
    omega
  apply measure_mono_ae
  filter_upwards [countsFullLaw_initial (rate n) n, countsFullLaw_legal (rate n) n]
    with C h0 hlegal hbad
  have hanti : Antitone (fun j => (C j).susceptible) :=
    antitone_nat_of_succ_le fun j => (hlegal j).susceptible_le
  have hterm : (C N).susceptible ≤ n := (legalHistory_susceptible_bounds h0 hlegal N).2
  by_cases hgate : 0 < (C a).infectious
  · refine ⟨hgate, ?_⟩
    by_cases hsmall : ((n + 1 - (C k).susceptible : ℕ) : ℝ) <
        (fluidExtinctionTime lam / 8) * n
    · exact Or.inr hsmall
    · apply Or.inl
      have hcard : n + 1 - (C k).susceptible ≤ n + 1 - (C N).susceptible :=
        Nat.sub_le_sub_left (hanti hkN) _
      have hcardR : ((n + 1 - (C k).susceptible : ℕ) : ℝ) ≤
          ((n + 1 - (C N).susceptible : ℕ) : ℝ) := by exact_mod_cast hcard
      change eta * (fluidExtinctionTime lam / 8) * n ≤
        (C k).susceptible - ((C N).susceptible : ℝ)
      calc
        _ = eta * ((fluidExtinctionTime lam / 8) * n) := by ring
        _ ≤ eta * ((n + 1 - (C k).susceptible : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) heta.le
        _ ≤ eta * ((n + 1 - (C N).susceptible : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcardR heta.le
        _ ≤ _ := hbad
  · have hz : (C a).infectious = 0 := by omega
    have hk := legalHistory_absorbed_persists hlegal hz k hak
    have hN := legalHistory_absorbed_persists hlegal hz N (hak.trans hkN)
    have hpos : 0 < ((n + 1 - (C N).susceptible : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < n + 1 - (C N).susceptible)
    have hbirth : (C k).susceptible = (C N).susceptible := by rw [hk, hN]
    change eta * ((n + 1 - (C N).susceptible : ℕ) : ℝ) ≤
      (C k).susceptible - ((C N).susceptible : ℝ) at hbad
    rw [hbirth, sub_self] at hbad
    exact ((not_le_of_gt (mul_pos heta hpos)) hbad).elim

/-- Capture prefixes can be chosen arbitrarily close to the fluid zero. -/
theorem exists_finite_rate_capture_time {lam eta lower : ℝ} (hlam : 1 < lam)
    (heta : 0 < eta) (hlower : lower < fluidExtinctionTime lam) :
    ∃ t : ℝ, lower < t ∧ fluidExtinctionTime lam / 2 < t ∧
      t < fluidExtinctionTime lam ∧
      fluidExtinctionTime lam - t < eta * (fluidExtinctionTime lam / 8) := by
  have hT := fluidExtinctionTime_spec hlam
  have hstart : max lower (max (fluidExtinctionTime lam / 2)
      (fluidExtinctionTime lam - eta * (fluidExtinctionTime lam / 8))) < fluidExtinctionTime lam := by
    apply max_lt hlower
    apply max_lt (by linarith)
    have : 0 < eta * (fluidExtinctionTime lam / 8) := mul_pos heta (by linarith)
    linarith
  obtain ⟨t, ht0, ht1⟩ := exists_between hstart
  refine ⟨t, (le_max_left _ _).trans_lt ht0,
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt ht0, ht1, ?_⟩
  have := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt ht0
  linarith

end Freezing1.SIR
