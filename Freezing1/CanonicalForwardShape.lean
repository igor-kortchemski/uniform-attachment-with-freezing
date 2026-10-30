module

public import Freezing1.CanonicalReverseState
public import Freezing1.ForwardHistoryExistence

/-!
# The actual reverse terminal data meet the forward history requirements

Every field of the deterministic reconstruction interface is extracted from
the proved reverse label support, timestamp ordering and rooted-forest data.
In particular, each freezing label is later than its vertex birth and every
incident child birth. No forward support or law identity is assumed.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory ReverseStamped
open scoped Classical ENNReal

theorem reverseLabel_some_injective {u v : ℕ ⊕ ℕ} {t : ℕ}
    (hu : reverseLabel u = some t) (hv : reverseLabel v = some t) : u = v := by
  cases u <;> cases v <;> simp_all [reverseLabel]
  omega

theorem reverseState_historyShape {x : SignSequence} {n : ℕ} {F : Forest}
    (hV : Reverse.ValidAt x n 0 F.forest) (ht : TimesValidAt x n 0 F)
    (ho : TimestampOrder F) : Forward.HistoryShape x n (reverseState F) := by
  have hone : F.forest.roots.card = 1 := by simpa [activeCount_zero] using hV.roots_card
  have hinj := ht.edgeTime_injective_of_one_root hone
  have himage := ht.edgeTime_image_of_one_root hone
  have hd := fun {v} (hv : v ∈ F.forest.vertices) => reverseState_vertex_data hinj hv
  have hvertex : ∀ v, v ∈ (reverseState F).vertices ↔
      v = 0 ∨ (1 ≤ v ∧ v ≤ n ∧ x v = true) := by
    intro v
    change v ∈ F.forest.vertices.image F.edgeTime ↔ _
    rw [himage]
    simp [attachmentTimes, Nat.lt_iff_add_one_le, and_assoc]
  have hlabel : ∀ j, Sum.inr j ∈ F.forest.vertices ↔ j < n ∧ x (j + 1) = false := by
    intro j
    simp [hV.vertices_eq, Reverse.phaseLabels]
  have hadj : ∀ u v, (reverseState F).graph.Adj u v →
      u ∈ (reverseState F).vertices ∧ v ∈ (reverseState F).vertices := by
    intro u v huv
    obtain ⟨_, a, ha, b, hb, hau, hbv, _⟩ := huv
    exact ⟨Finset.mem_image.mpr ⟨a, ha, hau⟩, Finset.mem_image.mpr ⟨b, hb, hbv⟩⟩
  have hgraph : ∀ a ∈ F.forest.vertices, ∀ b ∈ F.forest.vertices,
      (reverseState F).graph.Adj (F.edgeTime a) (F.edgeTime b) ↔
        (F.edgeTime a ≠ 0 ∧ (reverseState F).parent (F.edgeTime a) = F.edgeTime b) ∨
        (F.edgeTime b ≠ 0 ∧ (reverseState F).parent (F.edgeTime b) = F.edgeTime a) := by
    intro a ha b hb
    rw [show (reverseState F).graph = (reverse F).graph from rfl,
      reverse_adj_iff hinj ha hb, (hd ha).1, (hd hb).1]
    constructor
    · rintro ⟨_, _, hne, hp | hp⟩
      · refine Or.inl ⟨?_, congrArg F.edgeTime hp⟩
        intro hz
        have hp' := F.forest.parent_of_root ((ht.root_zero a ha).mp hz)
        exact hne (hp'.symm.trans hp)
      · refine Or.inr ⟨?_, congrArg F.edgeTime hp⟩
        intro hz
        have hp' := F.forest.parent_of_root ((ht.root_zero b hb).mp hz)
        exact hne (hp.symm.trans hp')
    · rintro (⟨hz, he⟩ | ⟨hz, he⟩)
      · have hp := hinj _ (F.forest.parent_mem a ha) _ hb he
        refine ⟨ha, hb, ?_, Or.inl hp⟩
        intro heq
        have hlt := ho.parent_lt a ha hz
        rw [hp, heq] at hlt
        exact (lt_irrefl _ hlt)
      · have hp := hinj _ (F.forest.parent_mem b hb) _ ha he
        refine ⟨ha, hb, ?_, Or.inr hp⟩
        intro heq
        have hlt := ho.parent_lt b hb hz
        rw [hp, heq] at hlt
        exact (lt_irrefl _ hlt)
  constructor
  · constructor
    · exact hvertex
    · intro t htV l hl
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htV
      rw [(hd hv).2.2] at hl
      cases v with
      | inl j => simp [reverseLabel] at hl
      | inr j =>
        have he : j + 1 = l := by simpa [reverseLabel] using hl
        obtain ⟨hjn, hx⟩ := (hlabel j).mp hv
        exact ⟨by omega, by omega, he ▸ hx⟩
    · intro t ht0 htn hx
      have ht : t - 1 + 1 = t := by omega
      have hv : Sum.inr (t - 1) ∈ F.forest.vertices :=
        (hlabel _).mpr ⟨by omega, by simpa only [ht] using hx⟩
      refine ⟨F.edgeTime (.inr (t - 1)), Finset.mem_image_of_mem _ hv, ?_⟩
      simpa [reverseLabel, ht] using (hd hv).2.2
  · exact reverseState_defaults ht
  · intro t htv
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htv
    rw [(hd hv).1]
    exact Finset.mem_image_of_mem _ (F.forest.parent_mem v hv)
  · exact fun v hv hv0 => reverseState_parent_lt hinj ho hv hv0
  · have hz := (hvertex 0).mpr (Or.inl rfl)
    obtain ⟨r, hr, hrt⟩ := Finset.mem_image.mp hz
    calc
      (reverseState F).height 0 = (reverseState F).height (F.edgeTime r) := by rw [hrt]
      _ = F.forest.depth r := (hd hr).2.1
      _ = 0 := (F.forest.depth_eq_zero_iff hr).mpr
        (RootedForest.mem_roots.mp ((ht.root_zero r hr).mp hrt)).2
  · intro t htv htn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htv
    rw [(hd hv).1, (hd hv).2.1, (hd (F.forest.parent_mem v hv)).2.1]
    have hn : v ≠ F.forest.root v := by
      intro he
      apply htn
      exact (ht.root_zero v hv).mpr (RootedForest.mem_roots.mpr ⟨hv, he.symm⟩)
    exact (F.forest.depth_parent v hv hn).symm
  · intro t
    constructor
    · intro hta
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hta
      obtain ⟨hv, hl⟩ := Finset.mem_filter.mp hv
      exact ⟨Finset.mem_image_of_mem _ hv, (hd hv).2.2.trans hl⟩
    · rintro ⟨htv, hl⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htv
      exact (reverse_active_iff hinj hv).mpr ((hd hv).2.2.symm.trans hl)
  · intro u v
    constructor
    · intro huv
      obtain ⟨hu, hv⟩ := hadj u v huv
      refine ⟨hu, hv, ?_⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      exact (hgraph a ha b hb).mp huv
    · rintro ⟨hu, hv, huv⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      exact (hgraph a ha b hb).mpr huv
  · intro u hu v hv t hut hvt
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    rw [(hd ha).2.2] at hut
    rw [(hd hb).2.2] at hvt
    exact congrArg F.edgeTime (reverseLabel_some_injective hut hvt)
  · intro t htv l hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htv
    rw [(hd hv).2.2] at hl
    cases v with
    | inl j => simp [reverseLabel] at hl
    | inr j =>
      have he : j + 1 = l := by simpa [reverseLabel] using hl
      exact he ▸ ho.frozen_incoming j hv
  · intro t htv ht0 l hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htv
    rw [(hd hv).1, (hd (F.forest.parent_mem v hv)).2.2] at hl
    cases hp : F.forest.parent v with
    | inl j => simp [hp, reverseLabel] at hl
    | inr j =>
      have he : j + 1 = l := by simpa [hp, reverseLabel] using hl
      have hj : Sum.inr j ∈ F.forest.vertices := hp ▸ F.forest.parent_mem v hv
      exact he ▸ ho.frozen_children j v hj hv hp

theorem treeLaw_reverseState_historyShape (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂ReverseStamped.treeLaw x n, Forward.HistoryShape x n (reverseState F) := by
  filter_upwards [lawAfter_forest_valid x n n hn le_rfl, treeLaw_times_valid x n hn,
    treeLaw_timestamp_order x n hn] with F hV ht ho
  exact reverseState_historyShape (by simpa only [Nat.sub_self] using hV) ht ho

end Freezing1.CanonicalTree
