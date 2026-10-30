module

public import Freezing1.SIRLateMaximumWord
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The exact reversed-index identity for a pre-step attachment charge,
and a feasible SIR counterexample to the differently indexed printed
identity. No reverse-time independence is inferred from this algebra. -/

@[expose] public section

namespace Freezing1.SIR

open scoped BigOperators Classical

theorem reverse_preStep_attachment_sum (x : SignSequence) (I : ℕ → ℝ)
    (n τ : ℕ) :
    (∑ i ∈ Finset.Ico n τ, if x (i + 1) then 1 / I i else 0) =
      ∑ j ∈ Finset.Icc 1 (τ - n),
        if x (τ - j + 1) then 1 / I (τ - j) else 0 := by
  apply Finset.sum_bij (fun i _ => τ - i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi k hk heq
    simp only [Finset.mem_Ico] at hi hk
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨τ - j, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    have hiτ : i ≤ τ := (Finset.mem_Ico.mp hi).2.le
    rw [Nat.sub_sub_self hiτ]

theorem reverse_activeCount_partialSum (x : SignSequence) {τ : ℕ}
    (hτ : activeCount x τ = 0) (i : ℕ) (hi : i ≤ τ) :
    (∑ j ∈ Finset.range i, -(if x (τ - j) then (1 : ℤ) else -1)) =
      activeCount x (τ - i) := by
  induction i with
  | zero => simpa using hτ.symm
  | succ i ih =>
    have hi' : i ≤ τ := by omega
    have hstep := activeCount_succ x (τ - (i + 1))
    have hidx : τ - (i + 1) + 1 = τ - i := by omega
    rw [hidx] at hstep
    rw [Finset.sum_range_succ, ih hi']
    omega

def reverseIdentityExample : SignSequence := fun i => decide (i = 1)

theorem reverseIdentityExample_feasible :
    SignWordFeasible 1 (![true, false, false] : Fin 3 → Bool) := by
  norm_num [SignWordFeasible, countsRunWord, initialCounts, countsStep,
    infectCounts, recoverCounts, Fin.init]

theorem reverseIdentityExample_wordSchedule :
    ForwardAnnealed.wordSchedule (![true, false, false] : Fin 3 → Bool) =
      reverseIdentityExample := by
  funext i
  unfold ForwardAnnealed.wordSchedule reverseIdentityExample
  split_ifs with hi
  · have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;> norm_num
  · have hne : i ≠ 1 := by intro h; subst i; exact hi ⟨by omega, by omega⟩
    simp [hne]

theorem reverseIdentityExample_population :
    activeCount reverseIdentityExample 0 = 1 ∧
    activeCount reverseIdentityExample 1 = 2 ∧
    activeCount reverseIdentityExample 2 = 1 ∧
    activeCount reverseIdentityExample 3 = 0 := by
  norm_num [activeCount, reverseIdentityExample, Finset.sum_range_succ]

/-- The source's forward charge uses `x i`, whereas its reverse charge
corresponds to `x (i+1)`. The literal equality already fails on the
feasible three-event epidemic consisting of one infection and two
recoveries. -/
theorem printed_reverse_attachment_identity_counterexample :
    let I : ℕ → ℝ := fun i => (activeCount reverseIdentityExample i : ℝ)
    (∑ i ∈ Finset.Ico 1 3, if reverseIdentityExample i then 1 / I i else 0) = 1 / 2 ∧
    (∑ j ∈ Finset.Icc 1 (3 - 1 : ℕ),
      if reverseIdentityExample (3 - j + 1) then 1 / I (3 - j) else 0) = 0 := by
  constructor
  · norm_num [reverseIdentityExample, activeCount, Finset.sum_range_succ,
      Finset.sum_Ico_succ_top]
  · apply Finset.sum_eq_zero
    intro j hj
    have hj' : j = 1 ∨ j = 2 := by simp only [Finset.mem_Icc] at hj; omega
    rcases hj' with rfl | rfl <;> norm_num [reverseIdentityExample]

end Freezing1.SIR
