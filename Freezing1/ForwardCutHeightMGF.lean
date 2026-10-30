module

public import Freezing1.ForwardCutHeightMoments

/-!
# Exponential moments for the heights added after a cut

The estimate starts at the actual cut time and accumulates only subsequent
attachment reciprocals. It is conditional on the deterministic sign schedule.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped BigOperators ENNReal Classical ProbabilityTheory

theorem integral_treeLaw_cutActiveMean_succ (x : SignSequence) (n a : ℕ) (f : ℕ → ℝ) :
    (∫ s', cutActiveMean s' a f ∂treeLaw x (n + 1)) =
      ∫ s, (∫ s', cutActiveMean s' a f ∂transitionLaw s (n + 1) (x (n + 1))) ∂treeLaw x n := by
  let K : ProbabilityTheory.Kernel State State :=
    ⟨fun s => transitionLaw s (n + 1) (x (n + 1)), measurable_from_top⟩
  have hi := treeLaw_integrable_cutActiveMean x (n + 1) a f
  rw [treeLaw] at hi
  have hi' : Integrable (fun s => cutActiveMean s a f)
      ((K ∘ₖ ProbabilityTheory.Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simpa only [K, treeLaw, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
    ProbabilityTheory.Kernel.const_apply] using hh

theorem treeLaw_cutActiveMean_succ (x : SignSequence) (a n : ℕ) (ha : a ≤ n)
    (hτ : ((n + 1 : ℕ) : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ s, cutActiveMean s a f ∂treeLaw x (n + 1)) =
      if x (n + 1) then
        (1 - 1 / (activeCount x (n + 1) : ℝ)) * (∫ s, cutActiveMean s a f ∂treeLaw x n) +
          (1 / (activeCount x (n + 1) : ℝ)) *
            (∫ s, cutActiveMean s a (fun k => f (k + 1)) ∂treeLaw x n)
      else ∫ s, cutActiveMean s a f ∂treeLaw x n := by
  have hnτ : (n : ℕ∞) < extinctionTime x :=
    lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
  rw [integral_treeLaw_cutActiveMean_succ]
  cases hx : x (n + 1)
  · simp only [Bool.false_eq_true, ite_false]
    apply integral_congr_ae
    filter_upwards [treeLaw_counts x n hnτ.le] with s hs
    have hpos := ((lt_extinctionTime_iff x (n + 1)).mp hτ) (n + 1) le_rfl
    rw [activeCount_succ, hx] at hpos
    have hc : 1 < s.active.card := by
      simp only [Bool.false_eq_true, ite_false] at hpos
      omega
    exact transitionLaw_cutActiveMean_freeze hc _ a f
  · simp only [ite_true]
    have hrec : ∀ᵐ s ∂treeLaw x n,
        (∫ s', cutActiveMean s' a f ∂transitionLaw s (n + 1) true) =
        (1 - 1 / (activeCount x (n + 1) : ℝ)) * cutActiveMean s a f +
          (1 / (activeCount x (n + 1) : ℝ)) * cutActiveMean s a (fun k => f (k + 1)) := by
      filter_upwards [treeLaw_valid x n, treeLaw_counts x n hnτ.le,
        treeLaw_active_nonempty x n hnτ] with s hs hc hne
      rw [transitionLaw_cutActiveMean_attach hs hne ha f]
      have hcount : (activeCount x (n + 1) : ℝ) = s.active.card + 1 := by
        rw [activeCount_succ, hx]
        simp only [ite_true, Int.cast_add, Int.cast_one, ← hc.1, Int.cast_natCast]
      rw [hcount]
      have hd : (s.active.card : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [integral_congr_ae hrec, integral_add]
    · rw [integral_const_mul, integral_const_mul]
    · exact (treeLaw_integrable_cutActiveMean x n a f).const_mul _
    · exact (treeLaw_integrable_cutActiveMean x n a (fun k => f (k + 1))).const_mul _

theorem cutActiveMean_at_cut {a : ℕ} {s : State} (hs : ValidAt a s)
    (hne : s.active.Nonempty) (f : ℕ → ℝ) : cutActiveMean s a f = f 0 := by
  have he (v : ℕ) (hv : v ∈ s.active) : cutHeight s a v = 0 :=
    cutHeightAux_eq_zero_of_le s a _ v (hs.vertices_le v (hs.active_subset hv))
  unfold cutActiveMean cutActiveSum activeSum
  simp only [cutHeightView]
  rw [Finset.sum_congr rfl (fun v hv => congrArg f (he v hv)), Finset.sum_const, nsmul_eq_mul]
  have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  field_simp

theorem cutActiveMean_const_mul (s : State) (a : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    cutActiveMean s a (fun k => c * f k) = c * cutActiveMean s a f := by
  unfold cutActiveMean cutActiveSum activeSum
  rw [← Finset.mul_sum]
  ring

theorem treeLaw_cutActiveMean_exp_le (x : SignSequence) (a n : ℕ) (ha : a ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) (theta : ℝ) :
    (∫ s, cutActiveMean s a (fun k => Real.exp (theta * (k : ℝ))) ∂treeLaw x n) ≤
      Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) := by
  revert hτ
  induction n, ha using Nat.le_induction with
  | base =>
    intro hτ
    have he : (∫ s, cutActiveMean s a (fun k => Real.exp (theta * (k : ℝ))) ∂treeLaw x a) = 1 := by
      calc
        _ = ∫ _s, (1 : ℝ) ∂treeLaw x a := by
          apply integral_congr_ae
          filter_upwards [treeLaw_valid x a, treeLaw_active_nonempty x a hτ] with s hs hne
          rw [cutActiveMean_at_cut hs hne]
          simp
        _ = _ := by simp
    simp [he]
  | succ n hna ih =>
    intro hτ
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
    have ih := ih hnτ
    rw [treeLaw_cutActiveMean_succ x a n hna hτ, heightScale_succ]
    cases hx : x (n + 1)
    · simp only [Bool.false_eq_true, ite_false, add_zero]
      exact ih
    · simp only [ite_true]
      let p : ℝ := 1 / (activeCount x (n + 1) : ℝ)
      have hs : (1 : ℤ) ≤ activeCount x (n + 1) := by
        have hh := ((lt_extinctionTime_iff x (n + 1)).mp hτ) (n + 1) le_rfl
        omega
      have hsR : (1 : ℝ) ≤ activeCount x (n + 1) := by exact_mod_cast hs
      have hp0 : 0 ≤ p := by dsimp [p]; positivity
      have hp1 : p ≤ 1 := (div_le_one (by linarith)).mpr hsR
      have hfac : 0 ≤ 1 + p * (Real.exp theta - 1) := by nlinarith [Real.exp_pos theta]
      have hshift :
          (∫ s, cutActiveMean s a (fun k => Real.exp (theta * ((k + 1 : ℕ) : ℝ))) ∂treeLaw x n) =
          Real.exp theta *
            (∫ s, cutActiveMean s a (fun k => Real.exp (theta * (k : ℝ))) ∂treeLaw x n) := by
        simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add,
          mul_comm _ (Real.exp theta), cutActiveMean_const_mul]
        exact integral_const_mul _ _
      rw [hshift]
      calc
        _ = (1 + p * (Real.exp theta - 1)) *
            (∫ s, cutActiveMean s a (fun k => Real.exp (theta * (k : ℝ))) ∂treeLaw x n) := by
          dsimp [p]
          ring
        _ ≤ (1 + p * (Real.exp theta - 1)) *
            Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) :=
          mul_le_mul_of_nonneg_left ih hfac
        _ ≤ Real.exp (p * (Real.exp theta - 1)) *
            Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) :=
          mul_le_mul_of_nonneg_right (by simpa only [add_comm] using
            (Real.add_one_le_exp (p * (Real.exp theta - 1))))
            (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [p]; ring

end Freezing1.Forward
