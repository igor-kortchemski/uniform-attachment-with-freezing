module

public import Freezing1.ReverseCoalescenceTime

/-!
# Finite coalescence tails, including diagonal pairs

Every pair of distinct labels is covered, whether active or frozen. The
diagonal is retained explicitly instead of discarded when averaging.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal BigOperators Classical

theorem one_sub_finset_prod_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := hf0 a (Finset.mem_insert_self _ _)
    have ha1 := hf1 a (Finset.mem_insert_self _ _)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => hf1 i (Finset.mem_insert_of_mem hi)
    have hprod : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one₀ hs0 hs1
    have hind := ih hs0 hs1
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    nlinarith

namespace Reverse

noncomputable def coalescenceHazard (x : SignSequence) (i : ℕ) : ℝ :=
  if x i then 1 / ((activeCount x i).toNat.choose 2 : ℝ) else 0

theorem coalescenceHazard_eq_one_sub (x : SignSequence) (i : ℕ) :
    coalescenceHazard x i = 1 - separationFactor x i := by
  cases hx : x i <;> simp [coalescenceHazard, separationFactor, hx]

theorem coalescenceHazard_nonneg (x : SignSequence) (i : ℕ) :
    0 ≤ coalescenceHazard x i := by
  rw [coalescenceHazard_eq_one_sub]
  exact sub_nonneg.mpr (separationFactor_le_one x i)

/-- A positive lower bound on the active walk gives the reciprocal quadratic
bound on the true hazard. The integer `toNat` is eliminated using positivity. -/
theorem coalescenceHazard_le_of_activeCount (x : SignSequence) (i : ℕ)
    {s : ℝ} (hs : 1 < s) (hi : s ≤ (activeCount x i : ℝ)) :
    coalescenceHazard x i ≤ 2 / (s * (s - 1)) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hi0 : 0 ≤ activeCount x i := by exact_mod_cast (le_trans hs0.le hi)
  have hcast : ((activeCount x i).toNat : ℝ) = (activeCount x i : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hi0
  cases hx : x i
  · simp only [coalescenceHazard, hx, Bool.false_eq_true, ↓reduceIte]
    positivity
  · simp only [coalescenceHazard, hx, ↓reduceIte]
    rw [Nat.cast_choose_two, hcast, one_div, inv_div]
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hs0 (sub_pos.mpr hs))
    apply mul_le_mul hi (sub_le_sub_right hi 1) (sub_nonneg.mpr hs.le)
      (le_trans hs0.le hi)

end Reverse

namespace ReverseHistory

theorem fullLaw_coalescenceTime_le_birth (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, coalescenceTime n H u v ≤ min (birthTime n u) (birthTime n v) := by
  filter_upwards [fullLaw_stages_valid x n hn, fullLaw_coalesced_zero x n hn hu hv]
    with H hvalid hzero
  exact (coalescenceTime_spec hvalid hzero hu hv).2

/-- Uniform over every distinct pair of terminal labels, including active
vertices; no averaging over birth labels is used. -/
theorem fullLaw_coalescenceTime_ge_le_sum (x : SignSequence) (n i : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v) :
    (fullLaw x n).real {H | i ≤ coalescenceTime n H u v} ≤
      ∑ t ∈ Finset.Ioc i n, Reverse.coalescenceHazard x t := by
  by_cases hi : i ≤ min (birthTime n u) (birthTime n v)
  · have he : {H : History | i ≤ coalescenceTime n H u v} =
        {H | coalescenceTime n H u v < i}ᶜ := by
      ext H
      simp
    rw [he, probReal_compl_eq_one_sub (by trivial),
      fullLaw_coalescenceTime_lt_product x n hn hu hv huv hi]
    calc
      _ ≤ ∑ t ∈ Finset.Ioc i (min (birthTime n u) (birthTime n v)),
          (1 - Reverse.separationFactor x t) :=
        one_sub_finset_prod_le_sum _ _
          (fun t _ => Reverse.separationFactor_nonneg x t)
          (fun t _ => Reverse.separationFactor_le_one x t)
      _ = ∑ t ∈ Finset.Ioc i (min (birthTime n u) (birthTime n v)),
          Reverse.coalescenceHazard x t := by
        simp_rw [Reverse.coalescenceHazard_eq_one_sub]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          rcases Finset.mem_Ioc.mp ht with ⟨hit, htb⟩
          exact Finset.mem_Ioc.mpr ⟨hit,
            htb.trans ((min_le_left _ _).trans (Reverse.birthTime_le_of_mem hu))⟩
        · intro t _ _
          exact Reverse.coalescenceHazard_nonneg x t
  · have he : (fullLaw x n).real {H | i ≤ coalescenceTime n H u v} = 0 := by
      have hempty : {H : History | i ≤ coalescenceTime n H u v} =ᵐ[fullLaw x n] ∅ := by
        filter_upwards [fullLaw_coalescenceTime_le_birth x n hn hu hv] with H hH
        apply propext
        simp only [Set.mem_empty_iff_false, iff_false]
        omega
      rw [measureReal_congr hempty]
      simp
    rw [he]
    exact Finset.sum_nonneg fun t _ => Reverse.coalescenceHazard_nonneg x t

/-- An explicit diagonal term makes this usable for independent uniform
samples, including coincident samples. -/
theorem fullLaw_coalescenceTime_ge_le_diag_add_sum (x : SignSequence) (n i : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    (fullLaw x n).real {H | i ≤ coalescenceTime n H u v} ≤
      (if u = v then (1 : ℝ) else 0) +
        ∑ t ∈ Finset.Ioc i n, Reverse.coalescenceHazard x t := by
  by_cases huv : u = v
  · rw [ite_eq_left huv]
    exact (measureReal_le_one).trans (le_add_of_nonneg_right
      (Finset.sum_nonneg fun t _ => Reverse.coalescenceHazard_nonneg x t))
  · rw [ite_eq_right huv, zero_add]
    exact fullLaw_coalescenceTime_ge_le_sum x n i hn hu hv huv

theorem sum_coalescenceHazard_le (x : SignSequence) (n i : ℕ)
    {s : ℝ} (hs : 1 < s)
    (hwalk : ∀ j ∈ Finset.Ioc i n, s ≤ (activeCount x j : ℝ)) :
    ∑ t ∈ Finset.Ioc i n, Reverse.coalescenceHazard x t ≤
      (n : ℝ) * (2 / (s * (s - 1))) := by
  calc
    _ ≤ ∑ _t ∈ Finset.Ioc i n, 2 / (s * (s - 1)) :=
      Finset.sum_le_sum fun t ht => Reverse.coalescenceHazard_le_of_activeCount x t hs (hwalk t ht)
    _ = ((n - i : ℕ) : ℝ) * (2 / (s * (s - 1))) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.sub_le n i
      · positivity

end ReverseHistory
end Freezing1
