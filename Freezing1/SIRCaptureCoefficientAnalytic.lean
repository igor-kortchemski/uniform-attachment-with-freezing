module

public import Freezing1.SIRFluidProfile

/-! The strict unconditional survival-weight slack behind the source's same-epsilon capture. -/

@[expose] public section

namespace Freezing1.SIR

open Set

set_option backward.isDefEq.respectTransparency false

theorem peakTime_lt_fluidExtinctionTime {lam : ℝ} (hlam : 1 < lam) :
    peakTime lam < fluidExtinctionTime lam := by
  have hp := infectiousProfile_peakTime_pos hlam
  by_contra hnot
  rcases lt_or_eq_of_le (le_of_not_gt hnot) with ht | ht
  · have hn := infectiousProfile_neg_after hlam ht
    linarith only [hp, hn]
  · rw [← ht] at hp
    rw [(fluidExtinctionTime_spec hlam).2.2] at hp
    exact (lt_irrefl 0) hp

theorem fluidProfile_at_extinction_lt_inverse {lam : ℝ} (hlam : 1 < lam) :
    fluidProfile lam (fluidExtinctionTime lam) < 1 / lam := by
  have hl : 0 < lam := by linarith only [hlam]
  have h := fluidProfile_strictAnti hl (peakTime_lt_fluidExtinctionTime hlam)
  rwa [fluidProfile_peakTime hl] at h

theorem twice_survival_lt_fluidExtinctionTime {lam : ℝ} (hlam : 1 < lam) :
    2 * (1 - 1 / lam) < fluidExtinctionTime lam := by
  have hg := fluidProfile_at_extinction_lt_inverse hlam
  have hzero := (fluidExtinctionTime_spec hlam).2.2
  unfold infectiousProfile at hzero
  linarith only [hg, hzero]

/-- For every source tolerance, all three deterministic comparison parameters
can be chosen while retaining a strict unconditional probability margin. -/
theorem exists_same_epsilon_capture_parameters {lam eps : ℝ} (hlam : 1 < lam)
    (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∃ d b a : ℝ,
      0 < fluidExtinctionTime lam - eps ∧ fluidExtinctionTime lam < d ∧ d < 2 ∧
      0 < b ∧ 2 * b < fluidExtinctionTime lam ∧
      d - (fluidExtinctionTime lam - eps) < a ∧
      0 < a ∧ (1 - 1 / lam) * (a / b) < eps := by
  let T := fluidExtinctionTime lam
  let s := 1 - 1 / lam
  have hl : 0 < lam := by linarith only [hlam]
  have hs : 0 < s := by
    dsimp only [s]
    have hi : 1 / lam < 1 := (div_lt_one hl).mpr hlam
    linarith only [hi]
  have hT : 0 < T := (fluidExtinctionTime_spec hlam).1
  have hT2 : T < 2 := (fluidExtinctionTime_spec hlam).2.1
  have hslack : 2 * s < T := twice_survival_lt_fluidExtinctionTime hlam
  have hrange : 2 * eps / T < eps / s := by
    apply (div_lt_div_iff₀ hT hs).mpr
    nlinarith only [mul_pos heps (sub_pos.mpr hslack)]
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hrange
  have hr : 0 < r := (div_pos (by positivity) hT).trans hrlo
  have hdeadline : T < min 2 ((T - eps) + r * (T / 2)) := by
    apply lt_min hT2
    have hh := (div_lt_iff₀ hT).mp hrlo
    linarith only [hh]
  obtain ⟨d, hdlo, hdhi⟩ := exists_between hdeadline
  have hdgap : (d - (T - eps)) / r < T / 2 := by
    apply (div_lt_iff₀ hr).mpr
    have h := hdhi.trans_le (min_le_right _ _)
    linarith only [h]
  obtain ⟨b, hblo, hbhi⟩ := exists_between hdgap
  have hdgap0 : 0 < d - (T - eps) := by linarith only [hdlo, heps]
  have hb : 0 < b := (div_pos hdgap0 hr).trans hblo
  have harange : d - (T - eps) < r * b := by
    have hh := (div_lt_iff₀ hr).mp hblo
    linarith only [hh]
  obtain ⟨a, halo, hahi⟩ := exists_between harange
  refine ⟨d, b, a, sub_pos.mpr hepsT, hdlo, hdhi.trans_le (min_le_left _ _), hb,
    by linarith only [hbhi], halo, hdgap0.trans halo, ?_⟩
  have hab : a / b < r := (div_lt_iff₀ hb).mpr (by simpa only [mul_comm] using hahi)
  have hsr : s * r < eps := by
    have h := (lt_div_iff₀ hs).mp hrhi
    linarith only [h]
  exact (mul_lt_mul_of_pos_left hab hs).trans hsr

end Freezing1.SIR
