module

public import Freezing1.ReversePairHeightHistory
public import Freezing1.BernoulliBlockRestriction
public import Mathlib.Probability.Moments.Variance

/-!
# Second moment of the actual tall-root count

The diagonal and distinct-root terms are separated on the actual random root
set. Pair estimates are weighted by the probability that both labels are roots;
summing those weights is controlled by the deterministic population at phase b.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators

theorem card_filter_sq_eq_add_offDiag {V : Type*} [DecidableEq V]
    (L : Finset V) (P : V → Prop) [DecidablePred P] :
    ((L.filter P).card : ℝ) ^ 2 = ((L.filter P).card : ℝ) +
      ∑ p ∈ L.offDiag, if P p.1 ∧ P p.2 then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  have he : L.offDiag.filter (fun p => P p.1 ∧ P p.2) = (L.filter P).offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    tauto
  rw [he]
  have hc := Finset.card_union_of_disjoint (L.filter P).disjoint_diag_offDiag
  rw [Finset.diag_union_offDiag, Finset.card_product, Finset.diag_card] at hc
  rw [pow_two]
  exact_mod_cast hc

namespace ReverseHistory

theorem blockTallRootCount_le_population {x : SignSequence} {n a b : ℕ} {H : History}
    (hH : Reverse.ValidAt x n b (stage H b)) (t : ℝ) :
    blockTallRootCount a b t H ≤ (activeCount x b).toNat := by
  unfold blockTallRootCount
  exact (Finset.card_filter_le _ _).trans_eq hH.roots_card

theorem blockTallRootCount_memLp (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hb : b ≤ n)
    (t : ℝ) (p : ℝ≥0∞) :
    MemLp (fun H => (blockTallRootCount a b t H : ℝ)) p (fullLaw x n) := by
  apply MemLp.of_bound measurable_from_top.aestronglyMeasurable ((activeCount x b).toNat : ℝ)
  filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
  rw [Real.norm_natCast]
  exact_mod_cast blockTallRootCount_le_population hH t

theorem blockTallRootCount_sq_eq {x : SignSequence} {n a b : ℕ} {H : History}
    (hH : Reverse.ValidAt x n b (stage H b)) (t : ℝ) :
    (blockTallRootCount a b t H : ℝ) ^ 2 = (blockTallRootCount a b t H : ℝ) +
      ∑ p ∈ (Reverse.phaseLabels x n b).offDiag,
        if (p.1 ∈ (stage H b).roots ∧ t < ((stage H a).depth p.1 : ℝ)) ∧
            (p.2 ∈ (stage H b).roots ∧ t < ((stage H a).depth p.2 : ℝ))
          then (1 : ℝ) else 0 := by
  have hN := blockTallRootCount_eq_sum (a := a) hH t
  rw [Finset.sum_boole] at hN
  rw [hN]
  exact card_filter_sq_eq_add_offDiag _ _

theorem sum_root_pair_indicators_le_population_sq {x : SignSequence} {n b : ℕ} {H : History}
    (hH : Reverse.ValidAt x n b (stage H b)) :
    (∑ p ∈ (Reverse.phaseLabels x n b).offDiag,
      if p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots then (1 : ℝ) else 0) ≤
        ((activeCount x b).toNat : ℝ) ^ 2 := by
  rw [Finset.sum_boole]
  have he : (Reverse.phaseLabels x n b).offDiag.filter
      (fun p => p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots) =
        (stage H b).roots.offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨_, _, hp⟩, h1, h2⟩
      exact ⟨h1, h2, hp⟩
    · rintro ⟨h1, h2, hp⟩
      exact ⟨⟨hH.vertices_eq ▸ (RootedForest.mem_roots.mp h1).1,
        hH.vertices_eq ▸ (RootedForest.mem_roots.mp h2).1, hp⟩, h1, h2⟩
  rw [he, Finset.offDiag_card, hH.roots_card]
  rw [pow_two]
  exact_mod_cast (Nat.sub_le ((activeCount x b).toNat * (activeCount x b).toNat)
    (activeCount x b).toNat)

theorem sum_root_pair_probabilities_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {b : ℕ} (hb : b ≤ n) :
    (∑ p ∈ (Reverse.phaseLabels x n b).offDiag,
      (fullLaw x n).real {H | p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots}) ≤
        ((activeCount x b).toNat : ℝ) ^ 2 := by
  let L := (Reverse.phaseLabels x n b).offDiag
  have hi : Integrable (fun H => ∑ p ∈ L,
      if p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots then (1 : ℝ) else 0)
      (fullLaw x n) := integrable_finsetSum _ (fun _ _ => history_indicator_integrable _ _)
  calc
    _ = ∫ H, ∑ p ∈ L,
        if p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots then (1 : ℝ) else 0 ∂fullLaw x n := by
      rw [integral_finsetSum _ (fun p _ => history_indicator_integrable (fullLaw x n)
        (fun H => p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots))]
      simp_rw [integral_history_indicator]
      rfl
    _ ≤ ∫ _H, (((activeCount x b).toNat : ℝ) ^ 2) ∂fullLaw x n := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
      exact sum_root_pair_indicators_le_population_sq hH
    _ = _ := by simp

/-- The complete second-moment bound on the actual history. Its sole error
term is the derived conditional coalescence risk. -/
theorem integral_blockTallRootCount_sq_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (t : ℝ) :
    (∫ H, (blockTallRootCount a b t H : ℝ) ^ 2 ∂fullLaw x n) ≤
      (∫ H, (blockTallRootCount a b t H : ℝ) ∂fullLaw x n) +
        ((activeCount x b).toNat : ℝ) ^ 2 *
          (Reverse.blockTailProbability x n hn a (b - a) t ^ 2 + Reverse.blockCoalescenceRisk x a (b - a)) := by
  let L := (Reverse.phaseLabels x n b).offDiag
  let P : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) → History → Prop := fun p H =>
    (p.1 ∈ (stage H b).roots ∧ t < ((stage H a).depth p.1 : ℝ)) ∧
      (p.2 ∈ (stage H b).roots ∧ t < ((stage H a).depth p.2 : ℝ))
  let R : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) → History → Prop := fun p H =>
    p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots
  let Q := Reverse.blockTailProbability x n hn a (b - a) t ^ 2 + Reverse.blockCoalescenceRisk x a (b - a)
  have hQ : 0 ≤ Q := add_nonneg (sq_nonneg _) (Reverse.blockCoalescenceRisk_nonneg _ _ _)
  have hiN := blockTallRootCount_integrable x n hn hb (a := a) t
  have hiSum : Integrable (fun H => ∑ p ∈ L, if P p H then (1 : ℝ) else 0) (fullLaw x n) :=
    integrable_finsetSum _ (fun p _ => history_indicator_integrable _ (P p))
  have hpair (p) (hp : p ∈ L) :
      (fullLaw x n).real {H | P p H} ≤ (fullLaw x n).real {H | R p H} * Q := by
    have he : {H | P p H} = {H | p.1 ∈ (stage H b).roots ∧ p.2 ∈ (stage H b).roots ∧
        t < ((stage H a).depth p.1 : ℝ) ∧ t < ((stage H a).depth p.2 : ℝ)} := by
      ext H
      simp only [P, Set.mem_ofPred_eq]
      tauto
    rw [he]
    exact fullLaw_root_pair_tail_le x n hn hab hb (Finset.mem_offDiag.mp hp).2.2 t
  calc
    _ = (∫ H, (blockTallRootCount a b t H : ℝ) ∂fullLaw x n) +
        ∑ p ∈ L, (fullLaw x n).real {H | P p H} := by
      have he : (fun H => (blockTallRootCount a b t H : ℝ) ^ 2) =ᵐ[fullLaw x n]
          fun H => (blockTallRootCount a b t H : ℝ) + ∑ p ∈ L, if P p H then (1 : ℝ) else 0 := by
        filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
        exact blockTallRootCount_sq_eq hH t
      rw [integral_congr_ae he, integral_add hiN hiSum,
        integral_finsetSum _ (fun p _ => history_indicator_integrable _ (P p))]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact integral_history_indicator _ (P p)
    _ ≤ (∫ H, (blockTallRootCount a b t H : ℝ) ∂fullLaw x n) +
        (∑ p ∈ L, (fullLaw x n).real {H | R p H}) * Q := by
      rw [Finset.sum_mul]
      exact add_le_add le_rfl (Finset.sum_le_sum hpair)
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (sum_root_pair_probabilities_le x n hn hb) hQ)


/-- The exact first moment with the same finite-product block law as the
pair estimate; injective restriction changes only the coordinate index type. -/
theorem integral_blockTallRootCount_eq_blockTail (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (t : ℝ) :
    (∫ H, (blockTallRootCount a b t H : ℝ) ∂fullLaw x n) =
      (activeCount x b : ℝ) * Reverse.blockTailProbability x n hn a (b - a) t := by
  rw [integral_blockTallRootCount x n hn hab hb]
  unfold Reverse.blockTailProbability Reverse.blockIndices
  rw [Nat.add_sub_of_le hab, bernoulliPartialSumLaw_fin_restrict _ a b hb]

theorem integral_blockTallRootCount_le_population (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hb : b ≤ n) (t : ℝ) :
    (∫ H, (blockTallRootCount a b t H : ℝ) ∂fullLaw x n) ≤ (activeCount x b : ℝ) := by
  have hbτ : (b : ℕ∞) ≤ extinctionTime x := (show (b : ℕ∞) ≤ n by exact_mod_cast hb).trans hn
  have hc : ((activeCount x b).toNat : ℝ) = (activeCount x b : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hbτ)
  have hi := blockTallRootCount_integrable x n hn hb (a := a) t
  calc
    _ ≤ ∫ _H, ((activeCount x b).toNat : ℝ) ∂fullLaw x n := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [fullLaw_stage_valid x n hn hb] with H hH
      exact_mod_cast blockTallRootCount_le_population hH t
    _ = _ := by simp only [integral_const, probReal_univ, one_smul, hc]

/-- Actual variance bound, uniform over the threshold and with no extra
probabilistic premise. Only the explicit block coalescence risk remains. -/
theorem variance_blockTallRootCount_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (t : ℝ) :
    variance (fun H => (blockTallRootCount a b t H : ℝ)) (fullLaw x n) ≤
      (activeCount x b : ℝ) + (activeCount x b : ℝ) ^ 2 *
        Reverse.blockCoalescenceRisk x a (b - a) := by
  have hbτ : (b : ℕ∞) ≤ extinctionTime x := (show (b : ℕ∞) ≤ n by exact_mod_cast hb).trans hn
  have hc : ((activeCount x b).toNat : ℝ) = (activeCount x b : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hbτ)
  have hsq := integral_blockTallRootCount_sq_le x n hn hab hb t
  rw [hc, integral_blockTallRootCount_eq_blockTail x n hn hab hb] at hsq
  have hmean := integral_blockTallRootCount_le_population x n hn hb (a := a) t
  rw [integral_blockTallRootCount_eq_blockTail x n hn hab hb] at hmean
  rw [variance_eq_sub (blockTallRootCount_memLp x n hn hb (a := a) t 2)]
  simp only [Pi.pow_apply]
  rw [integral_blockTallRootCount_eq_blockTail x n hn hab hb]
  nlinarith [hsq, hmean]

end ReverseHistory
end Freezing1
