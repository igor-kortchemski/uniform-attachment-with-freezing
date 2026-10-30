module

public import Freezing1.ForwardDegreeSurvival

/-!
# Exact finite products for joint root activity and degree

The products are obtained by iterating the actual forward kernels. The
surviving root weight is bounded for nonnegative Laplace parameters, which
justifies every integration through a bind.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

theorem prod_Ioc_zero_eq_range_succ {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ Finset.Ioc 0 n, f i) = ∏ i ∈ Finset.range n, f (i + 1) := by
  have he : Finset.Ioc 0 n = Finset.Ico 1 (n + 1) := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [he, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem integral_continuationLaw_succ_survivingRootWeight (x : SignSequence)
    (a k : ℕ) (s : State) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ q, survivingRootWeight θ q ∂continuationLaw x a (k + 1) s) =
      ∫ q, (∫ q', survivingRootWeight θ q' ∂continuationLaw x (a + 1) k q)
        ∂transitionLaw s (a + 1) (x (a + 1)) := by
  let K : Kernel State State := ⟨continuationLaw x (a + 1) k, measurable_from_top⟩
  have hi := integrable_survivingRootWeight hθ (continuationLaw x a (k + 1) s)
  rw [continuationLaw] at hi
  have hi' : Integrable (survivingRootWeight θ)
      ((K ∘ₖ Kernel.const Unit (transitionLaw s (a + 1) (x (a + 1)))) ()) := by
    simpa only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hi
  simpa only [K, continuationLaw, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply]
    using Kernel.integral_comp hi'

theorem continuationLaw_survivingRootWeight_product {x : SignSequence}
    {a k : ℕ} {s : State} (hs : PhaseData x a s)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ q, survivingRootWeight θ q ∂continuationLaw x a k s) =
      survivingRootWeight θ s * ∏ i ∈ Finset.Ioc a (a + k), degreeSurvivalFactor x θ i := by
  induction k generalizing a s with
  | zero => simp [continuationLaw]
  | succ k ih =>
    have haτ : (a : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show a < a + (k + 1) by omega)) hτ
    have hpos := ((lt_extinctionTime_iff x a).mp haτ) a le_rfl
    have hne : s.active.Nonempty := by
      apply Finset.card_pos.mp
      have hc := hs.count
      omega
    have hend : (((a + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hτ
    rw [integral_continuationLaw_succ_survivingRootWeight x a k s hθ]
    calc
      _ = ∫ q, survivingRootWeight θ q *
          (∏ i ∈ Finset.Ioc (a + 1) (a + 1 + k), degreeSurvivalFactor x θ i)
          ∂transitionLaw s (a + 1) (x (a + 1)) := by
        apply integral_congr_ae
        filter_upwards [transitionLaw_phaseData hs hne] with q hq
        exact ih hq hend
      _ = (∫ q, survivingRootWeight θ q ∂transitionLaw s (a + 1) (x (a + 1))) *
          (∏ i ∈ Finset.Ioc (a + 1) (a + 1 + k), degreeSurvivalFactor x θ i) := integral_mul_const _ _
      _ = _ := by
        rw [transitionLaw_survivingRootWeight hs hne θ]
        have hp := Finset.prod_Ioc_consecutive (degreeSurvivalFactor x θ)
          (Nat.le_succ a) (show a + 1 ≤ a + 1 + k by omega)
        simp only [Nat.Ioc_succ_singleton, Finset.prod_singleton] at hp
        rw [show a + (k + 1) = a + 1 + k by omega, ← hp]
        ring

theorem treeLaw_survivingRootWeight_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ s, survivingRootWeight θ s ∂treeLaw x n) =
      ∏ i ∈ Finset.Ioc 0 n, degreeSurvivalFactor x θ i := by
  have he : treeLaw x n = continuationLaw x 0 n initial := by
    simpa only [Nat.zero_add, treeLaw, Measure.dirac_bind measurable_from_top] using
      treeLaw_add_eq_bind_continuation x 0 n
  rw [he, continuationLaw_survivingRootWeight_product (initial_phaseData x) (by simpa using hn) hθ]
  simp [survivingRootWeight, rootDegree, initial]

theorem treeLaw_root_survival_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (treeLaw x n).real {s | 0 ∈ s.active} =
      ∏ i ∈ Finset.Ioc 0 n, vertexSurvivalFactor x i := by
  have he : treeLaw x n = continuationLaw x 0 n initial := by
    simpa only [Nat.zero_add, treeLaw, Measure.dirac_bind measurable_from_top] using
      treeLaw_add_eq_bind_continuation x 0 n
  rw [he, continuationLaw_vertex_survival (initial_phaseData x) (by simpa using hn) le_rfl]
  simp [initial]

end Freezing1.Forward
