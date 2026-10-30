module

public import Freezing1.ForwardDegree
public import Freezing1.ForwardSchedulePrefix

/-!
# Monotonicity of the genuine root degree, including absorption

An attachment can add a neighbour of the root; freezing and holding an
absorbed state preserve its degree. Consequently all marginal degree tails
are nondecreasing in time, without any survival hypothesis.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped ENNReal Classical

namespace Forward

theorem rootDegree_le_of_legalOrHeld {x : SignSequence} {n : ℕ} {s r : State}
    (hs : ValidAt n s) (h : ForwardInfiniteHistory.LegalOrHeld x n s r) :
    rootDegree s ≤ rootDegree r := by
  rcases h with ⟨_, rfl⟩ | ⟨v, hv, rfl⟩
  · exact le_rfl
  · rw [rootDegree_step hs hv]
    exact Nat.le_add_right _ _

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem fullLaw_rootDegree_monotone (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x, Monotone (fun n => rootDegree (H n)) := by
  filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x] with H hV hL
  exact monotone_nat_of_le_succ fun n => rootDegree_le_of_legalOrHeld (hV n) (hL n)

end ForwardInfiniteHistory

namespace Forward

theorem treeLaw_rootDegree_tail_mono (x : SignSequence) (d : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    (treeLaw x a) {s | d < rootDegree s} ≤
      (treeLaw x b) {s | d < rootDegree s} := by
  rw [← ForwardInfiniteHistory.map_eval x a, ← ForwardInfiniteHistory.map_eval x b,
    Measure.map_apply (measurable_pi_apply a) (by trivial),
    Measure.map_apply (measurable_pi_apply b) (by trivial)]
  apply measure_mono_ae
  exact (ForwardInfiniteHistory.fullLaw_rootDegree_monotone x).mono
    fun H hH h => lt_of_lt_of_le h (hH hab)

theorem treeLaw_rootDegree_tail_real_mono (x : SignSequence) (d : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    (treeLaw x a).real {s | d < rootDegree s} ≤
      (treeLaw x b).real {s | d < rootDegree s} :=
  ENNReal.toReal_mono (measure_ne_top _ _) (treeLaw_rootDegree_tail_mono x d hab)

end Forward
end Freezing1
