module

public import Freezing1.CanonicalReverseFibers
public import Freezing1.ForwardPointMass

/-!
# Actual point masses after forgetting active-label names

The canonical pushforward of Algorithm 2 has a reachable fiber consisting
of exactly `S_n!` timestamped states. Summing their actual kernel-derived
point masses cancels the factorial correction. The forward support bridge
remains a separate obligation; this module proves the quotient mass itself.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory ReverseStamped
open scoped ENNReal Classical

noncomputable def reverseStateLaw (x : SignSequence) (n : ℕ) : Measure Forward.State :=
  (ReverseStamped.treeLaw x n).map reverseState

instance reverseStateLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (reverseStateLaw x n) :=
  Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

theorem treeLaw_real_canonicalFiber (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {F : Forest}
    (hh : HasPartialHistory x n n F) :
    (ReverseStamped.treeLaw x n).real {G | reverseState G = reverseState F} =
      ((activeCount x n).toNat.factorial : ℝ) * reverseHistoryWeight x n := by
  let orbit := (activePermutations (activeCount x n).toNat).image
    (fun σ => relabel F (activeEquiv σ))
  have hfiber := terminalFiber_eq_activeOrbit hh
  have hae : {G | reverseState G = reverseState F} =ᵐ[ReverseStamped.treeLaw x n]
      (orbit : Set Forest) := by
    filter_upwards [treeLaw_hasHistory x n hn] with G hG
    have he := congrArg (fun s : Set Forest => G ∈ s) hfiber
    simpa only [Set.mem_ofPred_eq, hG, true_and] using he
  rw [measureReal_congr hae, ← sum_measureReal_singleton orbit]
  calc
    _ = ∑ _G ∈ orbit, reverseHistoryWeight x n := by
      apply Finset.sum_congr rfl
      intro G hG
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hG
      exact treeLaw_real_singleton_of_hasHistory x n hn (hh.relabel hσ)
    _ = (orbit.card : ℝ) * reverseHistoryWeight x n := by simp
    _ = _ := by
      rw [card_activeOrbit (terminal_history_data hh).valid.vertices_eq
        (terminal_history_times_injective hh)]

/-- The quotient point mass is the actual forward history weight. The
factorial multiplicity is proved by a complete reachable-fiber bijection. -/
theorem reverseStateLaw_real_singleton_of_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {F : Forest}
    (hh : HasPartialHistory x n n F) :
    (reverseStateLaw x n).real {reverseState F} = forwardHistoryWeight x n := by
  unfold reverseStateLaw Measure.real
  rw [Measure.map_apply measurable_from_top (by trivial)]
  change (ReverseStamped.treeLaw x n).real {G | reverseState G = reverseState F} = _
  rw [treeLaw_real_canonicalFiber x n hn hh,
    factorial_mul_reverseHistoryWeight_eq_forward x n hn]

theorem reverseStateLaw_real_singleton_ae (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂reverseStateLaw x n, (reverseStateLaw x n).real {s} = forwardHistoryWeight x n := by
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [treeLaw_hasHistory x n hn] with F hF
  exact reverseStateLaw_real_singleton_of_hasHistory x n hn hF

/-- The state pushforward still has exactly the source common observable. -/
theorem map_reverseStateLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (reverseStateLaw x n).map forward = reverseLaw x n := by
  unfold reverseStateLaw reverseLaw
  rw [Measure.map_map measurable_from_top measurable_from_top]
  apply Measure.map_congr
  filter_upwards [treeLaw_canonical_ids x n hn] with F hF
  exact forward_reverseState hF.1

end Freezing1.CanonicalTree
