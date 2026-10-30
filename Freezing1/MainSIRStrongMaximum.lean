module

public import Freezing1.SIRTerminalPrefixMaximum
public import Freezing1.SIRRandomEnvironmentTransferPrefix
public import Freezing1.MainSIREmbedded

/-!
# Strong-regime maximum of the actual terminal SIR tree

The earlier maximum and the late cut maximum control the terminal maximum
on the genuine terminal forward mixture. The final statement is transported
to the actual stopped SIR tree law.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem ValidAt.maximum_deviation_imp_prefix_or_cut {N : ℕ} {s : State}
    (hs : ValidAt N s) (a : ℕ) {ell eps c : ℝ} (hell : 0 < ell) (heps : 0 < eps)
    (hbad : eps ≤ |(treeHeight s : ℝ) / ell - c|) :
    eps / 2 ≤ |(treeHeight (truncateAt s a) : ℝ) / ell - c| ∨
      (eps / 2) * ell ≤ (cutMaximum s a : ℝ) := by
  by_contra h
  push Not at h
  obtain ⟨hprefix, hcut⟩ := h
  have hlo : (treeHeight (truncateAt s a) : ℝ) ≤ (treeHeight s : ℝ) := by
    exact_mod_cast treeHeight_truncate_le s a
  have hhi : (treeHeight s : ℝ) ≤
      (treeHeight (truncateAt s a) : ℝ) + (cutMaximum s a : ℝ) := by
    exact_mod_cast hs.treeHeight_le_truncate_add_cutMaximum a
  have hlodiv := div_le_div_of_nonneg_right hlo hell.le
  have hhidiv := div_le_div_of_nonneg_right hhi hell.le
  rw [add_div] at hhidiv
  have hcutdiv : (cutMaximum s a : ℝ) / ell < eps / 2 :=
    (div_lt_iff₀ hell).mpr hcut
  obtain ⟨hp0, hp1⟩ := abs_lt.mp hprefix
  have habs : |(treeHeight s : ℝ) / ell - c| < eps := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_le.mpr habs) hbad

end Freezing1.Forward

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem terminalForwardLaw_prefix_maximum_event_eq_actual (rate : ℝ≥0) (n : ℕ) (A : Set ℕ) :
    terminalForwardLaw rate n {s | Forward.treeHeight (Forward.truncateAt s n) ∈ A} =
      treeFullLaw rate n {H | (H n).tree.vertices.sup List.length ∈ A} := by
  rw [terminalForwardLaw_prefix_maximum_event_eq_earlier_word,
    original_tree_mixture_of_longer_word rate n (2 * n + 1) n (by omega)]
  exact (treeFullLaw_time_n_maximum_event_eq_environment rate n A).symm

theorem terminalForwardLaw_maximum_deviation_le (rate : ℝ≥0) (n : ℕ)
    {eps : ℝ} (heps : 0 < eps) (hlog : 0 < Real.log (n : ℝ)) :
    terminalForwardLaw rate n {s | eps ≤
      |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) - Real.exp 1|} ≤
    treeFullLaw rate n {H | eps / 2 ≤
      |(((H n).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|} +
    terminalForwardLaw rate n
      {s | (eps / 2) * Real.log n ≤ (Forward.cutMaximum s n : ℝ)} := by
  let A : Set Forward.State := {s | eps / 2 ≤
    |(Forward.treeHeight (Forward.truncateAt s n) : ℝ) / Real.log (n : ℝ) - Real.exp 1|}
  let B : Set Forward.State :=
    {s | (eps / 2) * Real.log n ≤ (Forward.cutMaximum s n : ℝ)}
  calc
    _ ≤ terminalForwardLaw rate n (A ∪ B) := by
      apply measure_mono_ae
      filter_upwards [terminalForwardLaw_valid rate n] with s hs hbad
      exact hs.maximum_deviation_imp_prefix_or_cut n hlog heps hbad
    _ ≤ terminalForwardLaw rate n A + terminalForwardLaw rate n B := measure_union_le _ _
    _ = _ := by
      rw [show terminalForwardLaw rate n A = treeFullLaw rate n {H | eps / 2 ≤
        |(((H n).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|} from
        terminalForwardLaw_prefix_maximum_event_eq_actual rate n
          {h | eps / 2 ≤ |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|}]

/-- In the strong regime, the maximum height of the actual terminal stopped
SIR tree, divided by `log n`, converges in probability to `exp 1`. -/
theorem sir_terminal_maximum_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => treeFullLaw (rate n) n {H | eps ≤
      |(((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|})
      atTop (nhds 0) := by
  have heps2 : 0 < eps / 2 := half_pos heps
  have hsum := (sir_time_n_maximum_tendsto rate hstrong heps2).add
    (terminalForwardLaw_cutMaximum_over_log_tendsto_zero rate hstrong heps2)
  simp only [add_zero] at hsum
  have hbound : ∀ᶠ n : ℕ in atTop,
      treeFullLaw (rate n) n {H | eps ≤
        |(((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|} ≤
      treeFullLaw (rate n) n {H | eps / 2 ≤
        |(((H n).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|} +
      terminalForwardLaw (rate n) n
        {s | (eps / 2) * Real.log n ≤ (Forward.cutMaximum s n : ℝ)} := by
    filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 0] with n hnlog
    have heq := terminalForwardLaw_maximum_event_eq_actual (rate n) n
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|}
    simp only [Set.mem_ofPred_eq] at heq
    rw [← heq]
    exact terminalForwardLaw_maximum_deviation_le (rate n) n heps hnlog
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) hbound

theorem sir_terminal_maximum_of_source_ratio (rate : ℕ → ℝ≥0)
    (h : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => treeFullLaw (rate n) n {H | eps ≤
      |(((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|})
      atTop (nhds 0) :=
  sir_terminal_maximum_tendsto rate (scaled_rate_atTop_of_source_ratio rate h) heps

end Freezing1.SIR
