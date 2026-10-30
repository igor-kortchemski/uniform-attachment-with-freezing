module

public import Freezing1.ReversePairHeightVariance
public import Freezing1.CoalescenceLogScale

/-!
# Uniform linear variance on geometric blocks

The pair bound comes from the actual reverse history. The hazard sum is
bounded by a reciprocal cutoff using the proved quadratic reciprocal sum.
The threshold is arbitrary, so the same variance constant applies to the
paper's chosen height threshold without additional distributional assumptions.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical Topology

noncomputable def blockVarianceConstant (C : ℕ) (d : ℝ) : ℝ :=
  ((C : ℝ) + 1) + ((C : ℝ) + 1) ^ 2 * (4 / d ^ 2)

theorem blockVarianceConstant_pos (C : ℕ) (d : ℝ) : 0 < blockVarianceConstant C d := by
  unfold blockVarianceConstant
  positivity

/-- Finite linear bound, derived from the actual variance and actual hazards. -/
theorem geometric_block_variance_le (x : SignSequence) (n a C : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hb : a * C ≤ n)
    (ha : 1 ≤ a) (hC : 1 ≤ C) {d : ℝ} (hd : 0 < d) (hda : 2 ≤ d * a)
    (hwalk : ∀ i ∈ Finset.Ioc a (a * C), d * i ≤ (activeCount x i : ℝ)) (t : ℝ) :
    variance (fun H => (ReverseHistory.blockTallRootCount a (a * C) t H : ℝ))
        (ReverseHistory.fullLaw x n) ≤ blockVarianceConstant C d * a := by
  have hab : a ≤ a * C := by nlinarith
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbτ : ((a * C : ℕ) : ℕ∞) ≤ extinctionTime x :=
    (show ((a * C : ℕ) : ℕ∞) ≤ n by exact_mod_cast hb).trans hn
  have hS0 : (0 : ℝ) ≤ activeCount x (a * C) := by
    exact_mod_cast activeCount_nonneg_of_le_extinctionTime hbτ
  have hS : (activeCount x (a * C) : ℝ) ≤ ((C : ℝ) + 1) * a := by
    have h1 : (activeCount x (a * C) : ℝ) ≤ (plusCount x (a * C) : ℝ) + 1 := by
      exact_mod_cast activeCount_le_plusCount_add_one x (a * C)
    have h2 : (plusCount x (a * C) : ℝ) ≤ (a * C : ℕ) := by
      exact_mod_cast plusCount_le x (a * C)
    push_cast at h2
    nlinarith
  have hSq : (activeCount x (a * C) : ℝ) ^ 2 ≤ (((C : ℝ) + 1) * a) ^ 2 :=
    (sq_le_sq₀ hS0 (by positivity)).mpr hS
  have hRisk := ReverseHistory.sum_coalescenceHazard_le_inv_cutoff x (a * C) a
    (by omega) hd hda hwalk
  have hRisk' : Reverse.blockCoalescenceRisk x a (a * C - a) ≤ (4 / d ^ 2) / a := by
    simpa only [Reverse.blockCoalescenceRisk, Nat.add_sub_of_le hab] using hRisk
  calc
    _ ≤ (activeCount x (a * C) : ℝ) + (activeCount x (a * C) : ℝ) ^ 2 *
        Reverse.blockCoalescenceRisk x a (a * C - a) :=
      ReverseHistory.variance_blockTallRootCount_le x n hn hab hb t
    _ ≤ (activeCount x (a * C) : ℝ) + (activeCount x (a * C) : ℝ) ^ 2 * ((4 / d ^ 2) / a) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hRisk' (sq_nonneg _))
    _ ≤ (((C : ℝ) + 1) * a) + (((C : ℝ) + 1) * a) ^ 2 * ((4 / d ^ 2) / a) :=
      add_le_add hS (mul_le_mul_of_nonneg_right hSq (by positivity))
    _ = _ := by
      unfold blockVarianceConstant
      field_simp

/-- Uniform source window. Only the near-origin assumption and diverging
cutoff are needed for this local estimate. -/
theorem uniform_geometricBlock_variance_le
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (C : ℕ) (hC : 1 ≤ C) :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (_hbn : a * C ≤ n), A n ≤ (a : ℝ) → ((a * C : ℕ) : ℝ) ≤ ε * n →
        ∀ t : ℝ, variance (fun H => (ReverseHistory.blockTallRootCount a (a * C) t H : ℝ))
          (ReverseHistory.fullLaw (x n) n) ≤ L * a := by
  let d := c / 2
  have hd : 0 < d := half_pos hc
  obtain ⟨ε, hε, hε1, hpoint⟩ := hnear (c / 2) (half_pos hc)
  refine ⟨blockVarianceConstant C d, blockVarianceConstant_pos C d, ε, hε, hε1, ?_⟩
  filter_upwards [hpoint, hA.eventually_ge_atTop (max 1 (2 / d))] with n hpointn hAn
  intro a hbn hAa hupper t
  have ha1 : (1 : ℝ) ≤ a := (le_max_left _ _).trans (hAn.trans hAa)
  have ha : 1 ≤ a := by exact_mod_cast ha1
  have hda : 2 ≤ d * a := by
    have hh : 2 / d ≤ (a : ℝ) := (le_max_right _ _).trans (hAn.trans hAa)
    exact (div_le_iff₀ hd).mp hh |>.trans_eq (mul_comm _ _)
  apply geometric_block_variance_le (x n) n a C (hn n) hbn ha hC hd hda _ t
  intro i hi
  obtain ⟨hai, hib⟩ := Finset.mem_Ioc.mp hi
  have haiR : (a : ℝ) ≤ i := by exact_mod_cast hai.le
  have hiR : (0 : ℝ) < i := lt_of_lt_of_le zero_lt_one (ha1.trans haiR)
  have hibR : (i : ℝ) ≤ (a * C : ℕ) := by exact_mod_cast hib
  have hh := (abs_le.mp (hpointn i (hAa.trans haiR) (hibR.trans hupper))).1
  have hr : d ≤ (activeCount (x n) i : ℝ) / i := by dsimp [d]; linarith
  exact (le_div_iff₀ hiR).mp hr

end Freezing1
