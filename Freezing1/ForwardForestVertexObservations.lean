module

public import Freezing1.ForwardForestTallStatistics

/-! Named later vertices and separation of their components in the bare forest. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def forestVertexTallIndicator (F : State) (a : ℕ) (t : ℝ) (v : ℕ) : ℝ :=
  if v ∈ F.active ∧ t < (cutHeight F a v : ℝ) then 1 else 0

theorem forestVertexTallIndicator_bounds (F : State) (a : ℕ) (t : ℝ) (v : ℕ) :
    0 ≤ forestVertexTallIndicator F a t v ∧ forestVertexTallIndicator F a t v ≤ 1 := by
  unfold forestVertexTallIndicator
  split <;> norm_num

theorem mem_active_relabel (e : Equiv.Perm ℕ) (F : State) (v : ℕ) :
    e v ∈ (F.relabel e).active ↔ v ∈ F.active := by simp [State.relabel]

theorem forestVertexTallIndicator_relabel {m a v : ℕ} (hm : m ≤ a + 1)
    (hv : a < v) {e : Equiv.Perm ℕ} (he : RootPermutation m e) (F : State) (t : ℝ) :
    forestVertexTallIndicator (F.relabel e) a t v = forestVertexTallIndicator F a t v := by
  have hev : e v = v := he v (by omega)
  have hmem : v ∈ (F.relabel e).active ↔ v ∈ F.active := by simpa only [hev] using mem_active_relabel e F v
  have hh : cutHeight (F.relabel e) a v = cutHeight F a v := by
    simpa only [hev] using cutHeight_relabel e F a v (fun i hi => he i (by omega))
  simp only [forestVertexTallIndicator, hmem, hh]

theorem forestVertexTallIndicator_slotStarForest (F : State) {m a v : ℕ}
    (hm : m ≤ a + 1) (hv : a < v) (t : ℝ) :
    forestVertexTallIndicator (slotStarForest m F) a t v = forestVertexTallIndicator F a t v := by
  have hvm : v ∉ Finset.range m := by simp only [Finset.mem_range]; omega
  unfold forestVertexTallIndicator
  rw [cutHeight_slotStarForest]
  change (if v ∈ F.active ∪ Finset.range m ∧ t < (cutHeight F a v : ℝ) then 1 else 0) = _
  simp only [Finset.mem_union, hvm, or_false]

noncomputable def bareVertexTallIndicator (a m : ℕ) (hm : m ≤ a + 1) (t : ℝ)
    (v : ℕ) (hv : a < v) : RootErasedForest m → ℝ :=
  Quotient.lift (fun F => forestVertexTallIndicator F a t v) (by
    rintro F Q ⟨e, he, hQ⟩
    rw [hQ, forestVertexTallIndicator_relabel hm hv he F t])

theorem bareVertexTallIndicator_bareSlotOrbit (F : State) (a m : ℕ) (hm : m ≤ a + 1)
    (t : ℝ) (v : ℕ) (hv : a < v) :
    bareVertexTallIndicator a m hm t v hv (bareSlotOrbit m F) = forestVertexTallIndicator F a t v := by
  rw [bareSlotOrbit_eq]
  exact forestVertexTallIndicator_slotStarForest F hm hv t

theorem bareVertexTallIndicator_bounds (a m : ℕ) (hm : m ≤ a + 1)
    (t : ℝ) (v : ℕ) (hv : a < v) (Q : RootErasedForest m) :
    0 ≤ bareVertexTallIndicator a m hm t v hv Q ∧ bareVertexTallIndicator a m hm t v hv Q ≤ 1 := by
  induction Q using Quotient.inductionOn with
  | h F => exact forestVertexTallIndicator_bounds F a t v

def forestVertexSeparated (F : State) (a v w : ℕ) : Prop :=
  cutAncestor F a v ≠ cutAncestor F a w

theorem forestVertexSeparated_relabel {m a v w : ℕ} (hm : m ≤ a + 1)
    (hv : a < v) (hw : a < w) {e : Equiv.Perm ℕ} (he : RootPermutation m e) (F : State) :
    forestVertexSeparated (F.relabel e) a v w ↔ forestVertexSeparated F a v w := by
  have hev : e v = v := he v (by omega)
  have hew : e w = w := he w (by omega)
  have hcv : cutAncestor (F.relabel e) a v = e (cutAncestor F a v) := by
    simpa only [hev] using cutAncestor_relabel e F a v (fun i hi => he i (by omega))
  have hcw : cutAncestor (F.relabel e) a w = e (cutAncestor F a w) := by
    simpa only [hew] using cutAncestor_relabel e F a w (fun i hi => he i (by omega))
  unfold forestVertexSeparated
  rw [hcv, hcw]
  exact not_congr e.injective.eq_iff

noncomputable def bareVertexSeparated (a m : ℕ) (hm : m ≤ a + 1)
    (v : ℕ) (hv : a < v) (w : ℕ) (hw : a < w) : RootErasedForest m → Prop :=
  Quotient.lift (fun F => forestVertexSeparated F a v w) (by
    rintro F Q ⟨e, he, hQ⟩
    rw [hQ]
    exact propext (forestVertexSeparated_relabel hm hv hw he F).symm)

theorem bareVertexSeparated_bareSlotOrbit (F : State) (a m : ℕ) (hm : m ≤ a + 1)
    (v : ℕ) (hv : a < v) (w : ℕ) (hw : a < w) :
    bareVertexSeparated a m hm v hv w hw (bareSlotOrbit m F) ↔ forestVertexSeparated F a v w := by
  rw [bareSlotOrbit_eq]
  change (cutAncestor (slotStarForest m F) a v ≠ cutAncestor (slotStarForest m F) a w) ↔ _
  rw [cutAncestor_slotStarForest, cutAncestor_slotStarForest]
  rfl

end Freezing1.Forward
