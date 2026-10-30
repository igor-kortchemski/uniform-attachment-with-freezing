module

public import Freezing1.BernoulliPairCouplingTails
public import Freezing1.BernoulliPairCouplingError
public import Freezing1.CoalescenceLogScale

/-! Source A60--A61's uniform actual pair-covariance estimate, through its auxiliary coupling. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

/-- The last inequality in source `eq:ksi`, for the actual separated event. -/
theorem actual_separated_tail_le_enlarged_square {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {H' | H'.current.root u ≠ H'.current.root v ∧
          t < ((H'.current.depth u - H.current.depth u : ℕ) : ℝ) ∧
          t < ((H'.current.depth v - H.current.depth v : ℕ) : ℝ)} ≤
      wordTail (auxiliaryParameter x n hn) a k t ^ 2 := by
  apply (actual_separated_tail_le hn hk hH hu hv t).trans
  have hpq : ∀ i, a ≤ i → i < a + k →
      (1 - (Reverse.stepParameter x n hn i : ℝ)) * (auxiliaryParameter x n hn i : ℝ) =
        Reverse.stepParameter x n hn i :=
    fun i _ hi => step_parameters_relation x n hn (hi.trans_le hk)
  have hd : 0 ≤ wordTail (auxiliaryParameter x n hn) a k t -
      wordTail (Reverse.stepParameter x n hn) a k t := by
    dsimp only [wordTail]
    rw [thinningLaw_tail_difference _ _ _ _ hpq t]
    exact measureReal_nonneg
  have hle : wordTail (Reverse.stepParameter x n hn) a k t ≤
      wordTail (auxiliaryParameter x n hn) a k t := by linarith only [hd]
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hle
    (show 0 ≤ wordTail (auxiliaryParameter x n hn) a k t from measureReal_nonneg)

theorem uniform_geometric_actual_pair_tail
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (C : ℕ) (hC : 1 < C) :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (_hbn : a * C ≤ n), A n ≤ (a : ℝ) →
        ((a * C : ℕ) : ℝ) ≤ ε * n →
        ∀ H : Base, Reverse.ValidAt (x n) n (a * C) H.current →
          ∀ u ∈ H.current.roots, ∀ v ∈ H.current.roots, u ≠ v → ∀ t : ℝ,
            (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                {H' | t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)} ≤
              (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                  {H' | t < (H'.current.depth u : ℝ)} *
                (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                  {H' | t < (H'.current.depth v : ℝ)} + L / a := by
  obtain ⟨M, hM, ε1, hε1, hε1lt, herror⟩ :=
    uniform_geometric_auxiliaryError x A hc hn hA hnear C hC
  obtain ⟨ε2, hε2, hε2lt, hpoint⟩ := hnear (c / 2) (half_pos hc)
  let d := c / 2
  let K := 4 / d ^ 2
  let L := M + K
  have hd : 0 < d := half_pos hc
  have hK : 0 < K := by dsimp only [K]; positivity
  let ε := min ε1 ε2
  refine ⟨L, add_pos hM hK, ε, lt_min hε1 hε2,
    (min_le_left _ _).trans_lt hε1lt, ?_⟩
  filter_upwards [herror, hpoint, hA.eventually_ge_atTop (max 1 (2 / d))]
    with n herrn hpointn hAn
  intro a hbn hAa hupper H hH u hu v hv huv t
  have ha1 : (1 : ℝ) ≤ a := (le_max_left _ _).trans (hAn.trans hAa)
  have ha : 1 ≤ a := by exact_mod_cast ha1
  have hab : a ≤ a * C := by nlinarith only [hC]
  have he : a + (a * C - a) = a * C := Nat.add_sub_of_le hab
  have hupper1 : ((a * C : ℕ) : ℝ) ≤ ε1 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
  have hupper2 : ((a * C : ℕ) : ℝ) ≤ ε2 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
  have herror' := herrn a hbn hAa hupper1
  have hda : 2 ≤ d * a := by
    have hh : 2 / d ≤ (a : ℝ) := (le_max_right _ _).trans (hAn.trans hAa)
    exact (div_le_iff₀ hd).mp hh |>.trans_eq (mul_comm _ _)
  have hwalk : ∀ i ∈ Finset.Ioc a (a * C), d * i ≤ (activeCount (x n) i : ℝ) := by
    intro i hi
    obtain ⟨hai, hib⟩ := Finset.mem_Ioc.mp hi
    have haiR : (a : ℝ) ≤ i := by exact_mod_cast hai.le
    have hiR : (0 : ℝ) < i := lt_of_lt_of_le zero_lt_one (ha1.trans haiR)
    have hibR : (i : ℝ) ≤ (a * C : ℕ) := by exact_mod_cast hib
    have hh := (abs_le.mp (hpointn i (hAa.trans haiR) (hibR.trans hupper2))).1
    have hr : d ≤ (activeCount (x n) i : ℝ) / i := by dsimp only [d]; linarith only [hh]
    exact (le_div_iff₀ hiR).mp hr
  have hRisk := ReverseHistory.sum_coalescenceHazard_le_inv_cutoff (x n) (a * C) a
    (by omega) hd hda hwalk
  have hRisk' : Reverse.blockCoalescenceRisk (x n) a (a * C - a) ≤ K / a := by
    simpa only [Reverse.blockCoalescenceRisk, he, K] using hRisk
  have hpair := actual_pair_tail_le_product_add_errors (hn n) (by omega)
    (show Reverse.ValidAt (x n) n (a + (a * C - a)) H.current by simpa only [he] using hH)
    hu hv huv t
  change _ ≤ _ + auxiliaryError (x n) n (hn n) a (a * C - a) +
    Reverse.blockCoalescenceRisk (x n) a (a * C - a) at hpair
  apply hpair.trans
  have hsum := add_le_add herror' hRisk'
  have hquot : M / (a : ℝ) + K / a = L / a := by dsimp only [L]; ring
  rw [hquot] at hsum
  linarith only [hsum]

end Freezing1.BernoulliPairCoupling
