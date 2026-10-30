module

public import Freezing1.ForwardComponentUrnPathInfinite

/-!
# Joint path law of the original component after positive extension

The actual conditional future of the extended tree is used, and its whole
past is sampled from the original process. The occupancy observable counts
genuinely active descendants; the marked-root correction remains separate.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace SignedUrn

theorem record_shift {Ω : Type*} (U : ℕ → Ω → ℤ) (offset a k : ℕ) (ω : Ω) :
    record (fun i ω => U (offset + i) ω) a k ω = record U (offset + a) k ω := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [record, Nat.add_assoc]
    rw [ih]

end SignedUrn

namespace ForwardInfiniteHistory

open Forward

/-- The full extended tree law is obtained by retaining the original
finite past and drawing the actual extended conditional future. -/
theorem positiveExtension_bind_original_prefix (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    fullLaw (positiveExtension x b) = ((fullLaw x).map (Preorder.frestrictLe a)).bind
      (continuationHistoryLaw (positiveExtension x b) a) := by
  rw [fullLaw_bind_continuationHistoryLaw,
    map_prefix_eq_of_schedule_prefix ((positiveExtension_agrees x b).mono hab)]

/-- The genuine component along the actual extended forward tree has all
joint urn path laws, conditional on any genuine current state. -/
theorem positiveExtension_actual_component_hasPathLaws (x : SignSequence) {a b : ℕ}
    (_hab : a ≤ b) (hb : PositiveThrough x b)
    (past : (i : Finset.Iic a) → State)
    (hs : HasHistory (positiveExtension x b) a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    {r : ℕ} (hr : r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active) :
    SignedUrn.HasPathLaws (fun i (H : History) => componentPopulation (H (a + i)) a r)
      (SignedUrn.positiveExtensionPopulation x a b) 1
      (continuationHistoryLaw (positiveExtension x b) a past) := by
  intro k
  have hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime (positiveExtension x b) := by
    rw [positiveExtension_extinctionTime x hb]
    exact le_top
  have hmap := continuationHistoryLaw_component_record (positiveExtension x b) a k a r past hs le_rfl hτ
  rw [componentPopulation_at_cut hs.current.valid hr] at hmap
  have hrecord : SignedUrn.record (fun i (H : History) => componentPopulation (H (a + i)) a r) 0 k =
      actualComponentRecord a r a k := by
    funext H
    simpa only [actualComponentRecord, Nat.add_zero] using SignedUrn.record_shift
      (fun i (H : History) => componentPopulation (H i) a r) a 0 k H
  constructor
  · rw [hrecord]
    exact (measurable_actualComponentRecord a r a k).aemeasurable
  · rw [hrecord]
    change _ = SignedUrn.pathLaw (fun i => activeCount (positiveExtension x b) (a + i)) 0 k 1
    rw [SignedUrn.pathLaw_shift, Nat.add_zero]
    exact hmap

/-- Actual original pasts satisfy the preceding theorem almost surely,
for every root active at the cut. Neither a joint path law nor an urn
identification is an extra source hypothesis. -/
theorem positiveExtension_original_component_pathLaws (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ past ∂(fullLaw x).map (Preorder.frestrictLe a),
      ∀ r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active,
        SignedUrn.HasPathLaws (fun i (H : History) => componentPopulation (H (a + i)) a r)
          (SignedUrn.positiveExtensionPopulation x a b) 1
          (continuationHistoryLaw (positiveExtension x b) a past) := by
  have hprefix := map_prefix_eq_of_schedule_prefix ((positiveExtension_agrees x b).mono hab)
  rw [← hprefix]
  have haτ : (a : ℕ∞) ≤ extinctionTime (positiveExtension x b) := by
    rw [positiveExtension_extinctionTime x hb]
    exact le_top
  have hcurrent : ∀ᵐ past ∂(fullLaw (positiveExtension x b)).map (Preorder.frestrictLe a),
      HasHistory (positiveExtension x b) a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := by
    apply ae_of_ae_map
      (μ := (fullLaw (positiveExtension x b)).map (Preorder.frestrictLe a))
      (f := fun past : ((i : Finset.Iic a) → State) => past ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
      (p := HasHistory (positiveExtension x b) a) (measurable_pi_apply _).aemeasurable
    rw [Measure.map_map (measurable_pi_apply _) (by fun_prop)]
    change ∀ᵐ s ∂(fullLaw (positiveExtension x b)).map (fun H => H a),
      HasHistory (positiveExtension x b) a s
    rw [map_eval]
    exact treeLaw_hasHistory (positiveExtension x b) a haτ
  exact hcurrent.mono fun past hs r hr =>
    positiveExtension_actual_component_hasPathLaws x hab hb past hs hr

end ForwardInfiniteHistory
end Freezing1
