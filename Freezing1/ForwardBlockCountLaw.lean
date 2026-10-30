module

public import Freezing1.CanonicalCutHeight
public import Freezing1.ReverseHistoryBlockCount

/-!
# Equality in law of the forward and reverse tall-root counts

The forward count is defined from the terminal forward tree and its explicit
cut forests. On the common stamped history it is exactly the existing reverse
count. Projection of that same probability space then gives equality of the
count laws, with no independence assumption or unidentified auxiliary model.
-/

@[expose] public section

namespace Freezing1.ReverseStampedHistory

open MeasureTheory ReverseStamped CanonicalTree
open scoped Classical ENNReal

theorem phase_vertices_antitone {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    (stage H b).forest.vertices ⊆ (stage H a).forest.vertices := by
  intro v hv
  rw [(hd b hb).valid.vertices_eq] at hv
  rw [(hd a (hab.trans hb)).valid.vertices_eq]
  cases v with
  | inl j => simpa [Reverse.phaseLabels] using hv
  | inr j =>
    simp only [Reverse.phaseLabels, Finset.inr_mem_disjSum, Finset.mem_filter,
      Finset.mem_range] at hv ⊢
    exact ⟨hv.1, hab.trans hv.2.1, hv.2.2⟩

theorem blockTallCount_eq_reverseCount {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (threshold : ℝ) :
    Forward.blockTallCount (reverseState H.current) a b threshold =
      ReverseHistory.blockTallRootCount a b threshold (forget H) := by
  have himage := image_phase_roots_eq_cutRoots hd hs hb
  have hmem : ∀ v ∈ (stage H b).forest.roots,
      H.current.edgeTime v ∈ Forward.cutRoots (reverseState H.current) b := by
    intro v hv
    rw [← himage]
    exact Finset.mem_image_of_mem _ hv
  have hheight : ∀ v ∈ (stage H b).forest.roots,
      Forward.blockHeight (reverseState H.current) a b (H.current.edgeTime v) =
        (stage H a).forest.depth v := by
    intro v hv
    rw [Forward.blockHeight_of_cutRoot _ a b (hmem v hv)]
    exact cutHeight_eq_stage_depth hd hs (hab.trans hb)
      (phase_vertices_antitone hd hab hb (RootedForest.mem_roots.mp hv).1)
  unfold Forward.blockTallCount ReverseHistory.blockTallRootCount
  rw [forget_stage H b, forget_stage H a]
  symm
  apply Finset.card_bij (fun v _ => H.current.edgeTime v)
  · intro v hv
    obtain ⟨hv, ht⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hmem v hv, by simpa only [hheight v hv] using ht⟩
  · intro u hu v hv he
    exact current_times_injective hd _
      (phase_vertices_subset_current hd hb (RootedForest.mem_roots.mp (Finset.mem_filter.mp hu).1).1)
      _ (phase_vertices_subset_current hd hb (RootedForest.mem_roots.mp (Finset.mem_filter.mp hv).1).1) he
  · intro t ht
    obtain ⟨ht, htall⟩ := Finset.mem_filter.mp ht
    rw [← himage] at ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩, rfl⟩
    simpa only [hheight v hv] using htall

theorem fullLaw_blockTallCount_eq_reverseCount (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n)
    (threshold : ℝ) :
    ∀ᵐ H ∂fullLaw x n,
      Forward.blockTallCount (reverseState H.current) a b threshold =
        ReverseHistory.blockTallRootCount a b threshold (forget H) := by
  filter_upwards [fullLaw_phaseData x n hn, fullLaw_legalSteps x n hn] with H hd hs
  exact blockTallCount_eq_reverseCount hd hs hab hb threshold

/-- The literal forward cut count and the actual reverse count have the same
law, jointly constructed through the stamped trajectory. -/
theorem forward_blockTallCount_law (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n)
    (threshold : ℝ) :
    (Forward.treeLaw x n).map (fun s => Forward.blockTallCount s a b threshold) =
      (ReverseHistory.fullLaw x n).map (ReverseHistory.blockTallRootCount a b threshold) := by
  rw [← map_fullLaw_forwardState x n hn, ← map_fullLaw_forget x n,
    Measure.map_map measurable_from_top measurable_from_top,
    Measure.map_map measurable_from_top measurable_from_top]
  apply Measure.map_congr
  exact fullLaw_blockTallCount_eq_reverseCount x n hn hab hb threshold

end Freezing1.ReverseStampedHistory
