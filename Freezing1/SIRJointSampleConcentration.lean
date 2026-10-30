module

public import Freezing1.SIRJointSampleLaw

/-! Combining both branches while retaining their actual common gate. -/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem terminalJointSampleLaw_concentrates_of_branches {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] (rate : ℕ → ℝ≥0) (a : ℕ → ℕ)
    (K : Kernel PlaneForward.State α) [IsMarkovKernel K] (f : ℕ → α → ℝ) (c : ℝ)
    (hnonneg : ∀ n v, 0 ≤ f n v)
    (halive : ∀ eps > 0, Tendsto (fun n => ∫⁻ H, if 0 < (H (a n)).counts.infectious then
      K (H (2 * n + 1)).tree {v | eps ≤ |f n v - c|} else 0 ∂treeFullLaw (rate n) n)
      atTop (nhds 0))
    (hextinct : ∀ eps > 0, Tendsto (fun n => ∫⁻ H, if (H (a n)).counts.infectious = 0 then
      K (H (2 * n + 1)).tree {v | eps ≤ f n v} else 0 ∂treeFullLaw (rate n) n)
      atTop (nhds 0))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (terminalJointSampleLaw (rate n) n (a n) K (f n) : Measure (Bool × ℝ))
      {z | eps ≤ |z.2 - TwoPointMixture.gatedValue c z|}) atTop (nhds 0) := by
  have hh := (halive eps heps).add (hextinct eps heps)
  simp only [add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [terminalJointSampleLaw_bad_apply]
  have hmeas : Measurable (fun H : ℕ → TreeState => if (H (a n)).counts.infectious = 0 then
      K (H (2 * n + 1)).tree {v | eps ≤ f n v} else 0) := by
    have hg : Measurable (fun H : ℕ → TreeState =>
        ((H (a n)).counts.infectious, (H (2 * n + 1)).tree)) := by fun_prop
    exact (measurable_of_countable (fun z : ℕ × PlaneForward.State => if z.1 = 0 then
      K z.2 {v | eps ≤ f n v} else 0)).comp hg
  rw [← lintegral_add_right _ hmeas]
  apply lintegral_congr
  intro H
  by_cases h : 0 < (H (a n)).counts.infectious
  · have hz : (H (a n)).counts.infectious ≠ 0 := h.ne'
    simp only [ite_eq_left h, ite_eq_right hz, add_zero]
  · have hz : (H (a n)).counts.infectious = 0 := by omega
    simp only [ite_eq_right h, ite_eq_left hz, zero_add]
    congr 1
    ext v
    simp only [mem_ofPred_eq, abs_of_nonneg (hnonneg n v)]

end Freezing1.SIR
