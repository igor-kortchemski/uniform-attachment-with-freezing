module

public import Freezing1.BernoulliPairCouplingSeparated
public import Freezing1.BernoulliPairCouplingThinningBounds
public import Freezing1.ReversePairHeightHistory

/-! The source's auxiliary-coupling route to actual joint block-tail control. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def wordTail (p : ℕ → unitInterval) (a k : ℕ) (t : ℝ) : ℝ :=
  (wordLaw p a k).real {w | t < (wordSum w : ℝ)}

/-- The second probability in the source's decomposition is bounded using
the actual auxiliary coupling and independence of its entire driver words. -/
theorem actual_separated_tail_le {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {H' | H'.current.root u ≠ H'.current.root v ∧
          t < ((H'.current.depth u - H.current.depth u : ℕ) : ℝ) ∧
          t < ((H'.current.depth v - H.current.depth v : ℕ) : ℝ)} ≤
      wordTail (Reverse.stepParameter x n hn) a k t *
        wordTail (auxiliaryParameter x n hn) a k t := by
  have hHist : HasLaw BlockSample.history (ReverseHistory.blockHistoryLaw x a k H)
      (coupledBlockLaw x n hn u v a k H) :=
    ⟨measurable_from_top.aemeasurable, coupledBlockLaw_map_history x n hn u v a k H⟩
  have hDrivers : HasLaw (fun s : BlockSample k => (s.first, s.second))
      (pairWordLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k)
      (coupledBlockLaw x n hn u v a k H) :=
    ⟨measurable_from_top.aemeasurable, coupledBlockLaw_map_drivers hn hk hH hu hv⟩
  rw [← hHist.measureReal_eq (p := fun H' : Base =>
    H'.current.root u ≠ H'.current.root v ∧
      t < ((H'.current.depth u - H.current.depth u : ℕ) : ℝ) ∧
      t < ((H'.current.depth v - H.current.depth v : ℕ) : ℝ)) (by trivial)]
  calc
    _ ≤ (coupledBlockLaw x n hn u v a k H).real
        {s | t < (wordSum s.first : ℝ) ∧ t < (wordSum s.second : ℝ)} := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [coupledBlockLaw_geometry hn hk hH hu hv] with s hs
      intro he
      have hfirst : s.history.current.depth u - H.current.depth u = wordSum s.first := by
        dsimp only [wordSum]
        omega
      have hsecond : s.history.current.depth v - H.current.depth v ≤ wordSum s.second := by
        have h := hs.2.2 he.1
        dsimp only [wordSum]
        omega
      exact ⟨by simpa only [hfirst] using he.2.1,
        he.2.2.trans_le (by exact_mod_cast hsecond)⟩
    _ = (pairWordLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k).real
        {w | t < (wordSum w.1 : ℝ) ∧ t < (wordSum w.2 : ℝ)} :=
      hDrivers.measureReal_eq
        (p := fun w : Word k × Word k => t < (wordSum w.1 : ℝ) ∧ t < (wordSum w.2 : ℝ))
        ((Set.to_countable _).measurableSet)
    _ = _ := by
      change ((wordLaw (Reverse.stepParameter x n hn) a k).prod
        (wordLaw (auxiliaryParameter x n hn) a k)).real
          ({w | t < (wordSum w : ℝ)} ×ˢ {w | t < (wordSum w : ℝ)}) = _
      exact measureReal_prod_prod _ _

/-- The exact source expectation error, with the source's actual parameters. -/
theorem actual_enlarged_tail_difference_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) (hk : a + k ≤ n) (t : ℝ) :
    wordTail (auxiliaryParameter x n hn) a k t -
        wordTail (Reverse.stepParameter x n hn) a k t ≤
      ∑ j : Fin k, ((descendingParameter (auxiliaryParameter x n hn) a k j : ℝ) -
        descendingParameter (Reverse.stepParameter x n hn) a k j) := by
  exact thinningLaw_tail_difference_le _ _ _ _
    (fun i _ hi => step_parameters_relation x n hn (hi.trans_le hk)) t

/-- The source A60--A61 route reaches the original separated-height event,
with its explicit finite scalar discrepancy. -/
theorem actual_separated_tail_le_square_add_error {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {H' | H'.current.root u ≠ H'.current.root v ∧
          t < ((H'.current.depth u - H.current.depth u : ℕ) : ℝ) ∧
          t < ((H'.current.depth v - H.current.depth v : ℕ) : ℝ)} ≤
      wordTail (Reverse.stepParameter x n hn) a k t ^ 2 +
        ∑ j : Fin k, ((descendingParameter (auxiliaryParameter x n hn) a k j : ℝ) -
          descendingParameter (Reverse.stepParameter x n hn) a k j) := by
  apply (actual_separated_tail_le hn hk hH hu hv t).trans
  let δ := ∑ j : Fin k, ((descendingParameter (auxiliaryParameter x n hn) a k j : ℝ) -
    descendingParameter (Reverse.stepParameter x n hn) a k j)
  have hgap := actual_enlarged_tail_difference_le x n hn a k hk t
  have hpq : ∀ i, a ≤ i → i < a + k →
      (1 - (Reverse.stepParameter x n hn i : ℝ)) * (auxiliaryParameter x n hn i : ℝ) =
        Reverse.stepParameter x n hn i :=
    fun i _ hi => step_parameters_relation x n hn (hi.trans_le hk)
  have hδ : 0 ≤ δ := by
    have h := thinningLaw_tail_difference (Reverse.stepParameter x n hn)
      (auxiliaryParameter x n hn) a k hpq t
    have hn0 : 0 ≤ wordTail (auxiliaryParameter x n hn) a k t -
        wordTail (Reverse.stepParameter x n hn) a k t := by
      dsimp only [wordTail]
      rw [h]
      exact measureReal_nonneg
    exact hn0.trans hgap
  have hP0 : 0 ≤ wordTail (Reverse.stepParameter x n hn) a k t := measureReal_nonneg
  have hP1 : wordTail (Reverse.stepParameter x n hn) a k t ≤ 1 := measureReal_le_one
  have hmul := mul_le_mul_of_nonneg_left (show wordTail (auxiliaryParameter x n hn) a k t ≤
      wordTail (Reverse.stepParameter x n hn) a k t + δ by linarith only [hgap]) hP0
  have hδmul := mul_le_mul_of_nonneg_right hP1 hδ
  change _ ≤ _ + δ
  nlinarith only [hmul, hδmul]

/-- The same original one-vertex gain has precisely the driver-sum tail. -/
theorem actual_gain_tail_eq_wordTail {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {H' | t < ((H'.current.depth u - H.current.depth u : ℕ) : ℝ)} =
      wordTail (Reverse.stepParameter x n hn) a k t := by
  have hHist : HasLaw BlockSample.history (ReverseHistory.blockHistoryLaw x a k H)
      (coupledBlockLaw x n hn u u a k H) :=
    ⟨measurable_from_top.aemeasurable, coupledBlockLaw_map_history x n hn u u a k H⟩
  have hFirst : HasLaw BlockSample.first (wordLaw (Reverse.stepParameter x n hn) a k)
      (coupledBlockLaw x n hn u u a k H) := by
    refine ⟨measurable_from_top.aemeasurable, ?_⟩
    have h := congrArg (fun μ : Measure (Word k × Word k) => μ.map Prod.fst)
      (coupledBlockLaw_map_drivers hn hk hH hu hu)
    rw [Measure.map_map measurable_fst measurable_from_top, pairWordLaw,
      Measure.map_fst_prod, measure_univ, one_smul] at h
    exact h
  rw [← hHist.measureReal_eq (p := fun H' : Base =>
      t < ((H'.current.depth u - H.current.depth u : ℕ) : ℝ)) (by trivial)]
  calc
    _ = (coupledBlockLaw x n hn u u a k H).real {s | t < (wordSum s.first : ℝ)} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [coupledBlockLaw_geometry hn hk hH hu hu] with s hs
      have he : s.history.current.depth u - H.current.depth u = wordSum s.first := by
        dsimp only [wordSum]
        omega
      simp only [he]
    _ = _ := hFirst.measureReal_eq (p := fun w : Word k => t < (wordSum w : ℝ))
      ((Set.to_countable _).measurableSet)

/-- The complete source decomposition: coalescence, independent auxiliary
tails, thinning and Markov. No supersolution pair-tail theorem is used. -/
theorem actual_pair_tail_le_square_add_errors {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.roots) (hv : v ∈ H.current.roots) (huv : u ≠ v) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {H' | t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)} ≤
      wordTail (Reverse.stepParameter x n hn) a k t ^ 2 +
        (∑ j : Fin k, ((descendingParameter (auxiliaryParameter x n hn) a k j : ℝ) -
          descendingParameter (Reverse.stepParameter x n hn) a k j)) +
        Reverse.blockCoalescenceRisk x a k := by
  have hu' := RootedForest.mem_roots.mp hu
  have hv' := RootedForest.mem_roots.mp hv
  have hdu := (H.current.depth_eq_zero_iff hu'.1).mpr hu'.2
  have hdv := (H.current.depth_eq_zero_iff hv'.1).mpr hv'.2
  have hne : H.current.root u ≠ H.current.root v := by rwa [hu'.2, hv'.2]
  have hcoal := Reverse.blockLaw_coalesced_integral_le hn hk hH hu'.1 hv'.1
  rw [Reverse.integral_coalescedTest] at hcoal
  simp only [Reverse.coalescedTest, ite_eq_right hne, zero_add] at hcoal
  have hCurrent : HasLaw ReverseHistory.History.current
      (Reverse.blockLaw x a k H.current) (ReverseHistory.blockHistoryLaw x a k H) :=
    ⟨measurable_from_top.aemeasurable, ReverseHistory.map_blockHistoryLaw_current x a k H⟩
  rw [← hCurrent.measureReal_eq (p := fun F : Reverse.Forest => F.root u = F.root v)
    (by trivial)] at hcoal
  have hsep := actual_separated_tail_le_square_add_error hn hk hH hu'.1 hv'.1 t
  simp only [hdu, hdv, Nat.sub_zero] at hsep
  calc
    _ ≤ (ReverseHistory.blockHistoryLaw x a k H).real
        ({H' | H'.current.root u ≠ H'.current.root v ∧
          t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)} ∪
         {H' | H'.current.root u = H'.current.root v}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro H' h
      by_cases he : H'.current.root u = H'.current.root v
      · exact Or.inr he
      · exact Or.inl ⟨he, h⟩
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add hsep hcoal)

/-- In particular the product term is the product of the two true marginal
height tails, exactly as in the final source covariance estimate. -/
theorem actual_pair_tail_le_product_add_errors {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.roots) (hv : v ∈ H.current.roots) (huv : u ≠ v) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {H' | t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)} ≤
      (ReverseHistory.blockHistoryLaw x a k H).real {H' | t < (H'.current.depth u : ℝ)} *
        (ReverseHistory.blockHistoryLaw x a k H).real {H' | t < (H'.current.depth v : ℝ)} +
        (∑ j : Fin k, ((descendingParameter (auxiliaryParameter x n hn) a k j : ℝ) -
          descendingParameter (Reverse.stepParameter x n hn) a k j)) +
        Reverse.blockCoalescenceRisk x a k := by
  have hu' := RootedForest.mem_roots.mp hu
  have hv' := RootedForest.mem_roots.mp hv
  have hdu := (H.current.depth_eq_zero_iff hu'.1).mpr hu'.2
  have hdv := (H.current.depth_eq_zero_iff hv'.1).mpr hv'.2
  have hU := actual_gain_tail_eq_wordTail hn hk hH hu'.1 t
  have hV := actual_gain_tail_eq_wordTail hn hk hH hv'.1 t
  simp only [hdu, hdv, Nat.sub_zero] at hU hV
  rw [hU, hV, ← pow_two]
  exact actual_pair_tail_le_square_add_errors hn hk hH hu hv huv t

end Freezing1.BernoulliPairCoupling
