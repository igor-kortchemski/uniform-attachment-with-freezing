module

public import Freezing1.SIRSurvivalGateComparison

/-! Actual recovered-vertex and prefix-vertex fractions for the exact capture coefficient. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal Topology

set_option backward.isDefEq.respectTransparency false

def captureVertexCount (n : ℕ) (c : Counts) : ℕ := n + 1 - c.susceptible
def captureRecoveredCount (n : ℕ) (c : Counts) : ℕ :=
  captureVertexCount n c - c.infectious

noncomputable def uncapturedFraction (terminal retained : ℕ) : ℝ :=
  ((terminal - retained : ℕ) : ℝ) / terminal

theorem uncapturedFraction_bounds (terminal retained : ℕ) :
    0 ≤ uncapturedFraction terminal retained ∧ uncapturedFraction terminal retained ≤ 1 := by
  unfold uncapturedFraction
  constructor
  · positivity
  · by_cases hz : terminal = 0
    · simp only [hz, Nat.cast_zero, div_zero, zero_le_one]
    · have hp : (0 : ℝ) < terminal := by exact_mod_cast Nat.pos_of_ne_zero hz
      apply (div_le_one hp).mpr
      exact_mod_cast Nat.sub_le terminal retained

theorem captureRecoveredCount_legal {n : ℕ} {c d : Counts}
    (hc : c.Valid n) (hl : c.LegalNext d) :
    captureRecoveredCount n c ≤ captureRecoveredCount n d ∧
      captureRecoveredCount n d ≤ captureRecoveredCount n c + 1 := by
  unfold captureRecoveredCount captureVertexCount
  unfold Counts.Valid at hc
  rcases hl with ⟨_, rfl⟩ | ⟨hi, ⟨hu, rfl⟩ | rfl⟩
  · omega
  · simp only [infectCounts]
    omega
  · simp only [recoverCounts]
    omega

theorem captureHistory_valid {n : ℕ} {H : ℕ → Counts}
    (h0 : H 0 = initialCounts n) (hl : ∀ k, (H k).LegalNext (H (k + 1))) (k : ℕ) :
    (H k).Valid n := by
  induction k with
  | zero => rw [h0]; exact initialCounts_valid n
  | succ k ih => exact (hl k).valid ih

theorem captureRecoveredCount_drop {n : ℕ} {H : ℕ → Counts}
    (h0 : H 0 = initialCounts n) (hl : ∀ k, (H k).LegalNext (H (k + 1)))
    {a b : ℕ} (hab : a ≤ b) :
    captureRecoveredCount n (H b) ≤ captureRecoveredCount n (H a) + (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => omega
  | succ b hb ih =>
    have h := (captureRecoveredCount_legal (captureHistory_valid h0 hl b) (hl b)).2
    omega

theorem captureVertexCount_mono {n : ℕ} {H : ℕ → Counts}
    (hl : ∀ k, (H k).LegalNext (H (k + 1))) : Monotone (fun k => captureVertexCount n (H k)) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Nat.sub_le_sub_left (hl k).susceptible_le _

noncomputable def reverseMissingFraction (n k : ℕ) (H : ℕ → Counts) : ℝ :=
  uncapturedFraction (captureVertexCount n (H (2 * n + 1))) (captureRecoveredCount n (H k))

noncomputable def forwardMissingFraction (n k : ℕ) (H : ℕ → Counts) : ℝ :=
  uncapturedFraction (captureVertexCount n (H (2 * n + 1))) (captureVertexCount n (H k))

theorem forwardMissingFraction_le_reverse (n k : ℕ) (H : ℕ → Counts) :
    forwardMissingFraction n k H ≤ reverseMissingFraction n k H := by
  unfold forwardMissingFraction reverseMissingFraction uncapturedFraction captureRecoveredCount
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.sub_le_sub_left (Nat.sub_le _ _) _

@[fun_prop] theorem measurable_reverseMissingFraction (n k : ℕ) :
    Measurable (reverseMissingFraction n k) := by
  let f : Counts × Counts → ℝ := fun z =>
    uncapturedFraction (captureVertexCount n z.2) (captureRecoveredCount n z.1)
  have hf : Measurable f := measurable_of_countable f
  have he : reverseMissingFraction n k = f ∘ (fun H : ℕ → Counts => (H k, H (2 * n + 1))) := rfl
  rw [he]
  exact hf.comp ((measurable_pi_apply k).prodMk (measurable_pi_apply (2 * n + 1)))

theorem reverseMissingFraction_bounds (n k : ℕ) (H : ℕ → Counts) :
    0 ≤ reverseMissingFraction n k H ∧ reverseMissingFraction n k H ≤ 1 :=
  uncapturedFraction_bounds _ _

theorem reverseMissingFraction_integrable (r : ℝ≥0) (n k : ℕ) :
    Integrable (reverseMissingFraction n k) (countsFullLaw r n) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_reverseMissingFraction n k).aestronglyMeasurable
  exact Eventually.of_forall fun H => by
    rw [Real.norm_eq_abs, abs_of_nonneg (reverseMissingFraction_bounds n k H).1]
    exact (reverseMissingFraction_bounds n k H).2

theorem reverseMissingFraction_zero_of_absorbed {n k : ℕ} {H : ℕ → Counts}
    (hl : ∀ j, (H j).LegalNext (H (j + 1))) (hk : k ≤ 2 * n + 1)
    (hz : (H k).infectious = 0) : reverseMissingFraction n k H = 0 := by
  have he := legalHistory_absorbed_persists hl hz (2 * n + 1) hk
  simp only [reverseMissingFraction, he, captureRecoveredCount, hz, Nat.sub_zero,
    uncapturedFraction, Nat.sub_self, Nat.cast_zero, zero_div]

theorem reverseMissingFraction_le_late_steps {n k b : ℕ} {H : ℕ → Counts}
    (h0 : H 0 = initialCounts n) (hl : ∀ j, (H j).LegalNext (H (j + 1)))
    (hkb : k ≤ b) (hb : b ≤ 2 * n + 1) (hz : (H b).infectious = 0) :
    reverseMissingFraction n k H ≤
      ((b - k : ℕ) : ℝ) / (captureVertexCount n (H (2 * n + 1)) : ℝ) := by
  have hh := captureRecoveredCount_drop h0 hl hkb
  have he := legalHistory_absorbed_persists hl hz (2 * n + 1) hb
  have hnum : captureVertexCount n (H (2 * n + 1)) - captureRecoveredCount n (H k) ≤ b - k := by
    rw [he]
    have hRb : captureRecoveredCount n (H b) = captureVertexCount n (H b) := by
      simp only [captureRecoveredCount, hz, Nat.sub_zero]
    rw [hRb] at hh
    omega
  unfold reverseMissingFraction uncapturedFraction
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hnum

theorem countsFullLaw_fixed_preFluid_gate_mismatch (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {t q : ℝ} (ht : 0 < t) (htq : t ≤ q) (hq : q < fluidExtinctionTime lam) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious ∧ (H ⌊(n : ℝ) * q⌋₊).infectious = 0})
      atTop (𝓝 0) := by
  have hh := (countsFullLaw_preFluid_extinction_tendsto rate lam hlam hscaled
    (ht.trans_le htq) hq).sub
      (countsFullLaw_preFluid_extinction_tendsto rate lam hlam hscaled ht (htq.trans_lt hq))
  simp only [sub_self] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n =>
    (countsFullLaw_extinction_between_eq_sub (rate n) n _ _
      (Nat.floor_mono (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg n)))).symm

theorem countsFullLaw_alive_small_terminal_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {t b : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam)
    (hb : 2 * b < fluidExtinctionTime lam) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious ∧
        (captureVertexCount n (H (2 * n + 1)) : ℝ) < b * n}) atTop (𝓝 0) := by
  obtain ⟨q, hqlo, hqhi⟩ := exists_between (max_lt htt hb)
  have htq : t < q := (le_max_left _ _).trans_lt hqlo
  have hbq : 2 * b < q := (le_max_right _ _).trans_lt hqlo
  have hscale : Tendsto (fun n : ℕ => (q - 2 * b) * n) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith only [hbq]) tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      (countsFullLaw (rate n) n).real {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious ∧
        (captureVertexCount n (H (2 * n + 1)) : ℝ) < b * n} ≤
      (countsFullLaw (rate n) n).real {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious ∧
        (H ⌊(n : ℝ) * q⌋₊).infectious = 0} := by
    filter_upwards [hscale.eventually_gt_atTop 1] with n hn
    have hkN : ⌊(n : ℝ) * q⌋₊ ≤ 2 * n + 1 := by
      have h := StoppedCoupling.floor_time_index_le (n := n) (m := 2)
        (hqhi.trans (fluidExtinctionTime_spec hlam).2.1).le
      omega
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [countsFullLaw_initial (rate n) n, countsFullLaw_legal (rate n) n]
      with H h0 hl hbad
    refine ⟨hbad.1, ?_⟩
    by_contra hnot
    have hp : 0 < (H ⌊(n : ℝ) * q⌋₊).infectious := Nat.pos_of_ne_zero hnot
    have hc := legalHistory_alive_prefix_vertices h0 hl hp
    have hm := captureVertexCount_mono (n := n) hl hkN
    have hcR : (⌊(n : ℝ) * q⌋₊ : ℝ) ≤ 2 * (captureVertexCount n (H (2 * n + 1)) : ℝ) := by
      exact_mod_cast (hc.trans (Nat.mul_le_mul_left 2 hm))
    have hfloor := Nat.lt_floor_add_one ((n : ℝ) * q)
    have hlarge := hn
    change (q - 2 * b) * (n : ℝ) > 1 at hlarge
    nlinarith only [hcR, hfloor, hbad.2, hlarge]
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (countsFullLaw_fixed_preFluid_gate_mismatch rate lam hlam hscaled ht htq.le hqhi)

end Freezing1.SIR
