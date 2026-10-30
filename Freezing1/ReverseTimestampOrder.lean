module

public import Freezing1.ReverseTimestampSupport

/-!
# Ordering of the actual reverse edge and frozen labels

Reverse insertion adds an edge earlier than every edge already present. This
proves increasing edge times away from each root and the strict inequality
between a frozen vertex label and every incident edge. These are actual kernel
invariants, not assumptions about a putative terminal support.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped Classical ENNReal

structure TimestampOrder (F : Forest) : Prop where
  parent_lt : ∀ v ∈ F.forest.vertices, F.edgeTime v ≠ 0 →
    F.edgeTime (F.forest.parent v) < F.edgeTime v
  frozen_incoming : ∀ j, Sum.inr j ∈ F.forest.vertices → F.edgeTime (.inr j) < j + 1
  frozen_children : ∀ j v, Sum.inr j ∈ F.forest.vertices → v ∈ F.forest.vertices →
    F.forest.parent v = Sum.inr j → F.edgeTime v < j + 1

theorem initial_timestamp_order (x : SignSequence) (n : ℕ) :
    TimestampOrder (initial x n) := by
  constructor
  · intro v hv hn
    simp [initial] at hn
  · intro j hj
    simp [initial]
  · intro j v hj hv hp
    simp [initial]

/-- The freezing labels already present at phase `i+1` are strictly later
than the next reverse edge time `i+1`. -/
theorem frozen_label_after_phase {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : Reverse.ValidAt x n (i + 1) F.forest) {j : ℕ}
    (hj : Sum.inr j ∈ F.forest.vertices) : i + 1 < j + 1 := by
  rw [hF.vertices_eq] at hj
  simp only [Reverse.phaseLabels, Finset.inr_mem_disjSum, Finset.mem_filter,
    Finset.mem_range] at hj
  omega

/-- The new edge joins two old zero-time roots, while every existing edge
has a strictly larger time. -/
theorem TimestampOrder.joinChoice {x : SignSequence} {n i : ℕ} {F : Forest}
    (ho : TimestampOrder F) (ht : TimesValidAt x n (i + 1) F)
    (hF : Reverse.ValidAt x n (i + 1) F.forest)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag) :
    TimestampOrder (joinChoice F (i + 1) p) := by
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  have haV := (RootedForest.mem_roots.mp ha).1
  have hbV := (RootedForest.mem_roots.mp hb).1
  have haz : F.edgeTime p.1 = 0 := (ht.root_zero _ haV).mpr ha
  constructor
  · intro v hv hn
    simp only [ReverseStamped.joinChoice, dite_eq_left hp, RootedForest.join_vertices] at hv
    simp only [ReverseStamped.joinChoice, dite_eq_left hp] at hn ⊢
    by_cases hvb : v = p.2
    · subst v
      simp [RootedForest.join, hab, haz]
    · simp only [RootedForest.join, hvb, ↓reduceIte, Function.update_of_ne hvb] at hn ⊢
      by_cases hpb : F.forest.parent v = p.2
      · simp only [hpb, Function.update_self]
        exact (ht.range v hv hn).1
      · simpa only [Function.update_of_ne hpb] using ho.parent_lt v hv hn
  · intro j hj
    simp only [ReverseStamped.joinChoice, dite_eq_left hp, RootedForest.join_vertices] at hj
    simp only [ReverseStamped.joinChoice, dite_eq_left hp]
    by_cases hjb : Sum.inr j = p.2
    · simp only [hjb, Function.update_self]
      exact frozen_label_after_phase hF hj
    · simpa only [Function.update_of_ne hjb] using ho.frozen_incoming j hj
  · intro j v hj hv hparent
    simp only [ReverseStamped.joinChoice, dite_eq_left hp, RootedForest.join_vertices] at hj hv
    simp only [ReverseStamped.joinChoice, dite_eq_left hp, RootedForest.join] at hparent ⊢
    by_cases hvb : v = p.2
    · simp only [hvb, ↓reduceIte] at hparent
      simp only [hvb, Function.update_self]
      exact frozen_label_after_phase hF hj
    · simp only [hvb, ↓reduceIte] at hparent
      simpa only [Function.update_of_ne hvb] using ho.frozen_children j v hj hv hparent

/-- A new frozen singleton has no positive-time edge. Old parent edges cannot
point to its fresh label. -/
theorem TimestampOrder.insertLabel {F : Forest} (ho : TimestampOrder F) {i : ℕ}
    (hfresh : Sum.inr i ∉ F.forest.vertices) : TimestampOrder (insertLabel F i) := by
  constructor
  · intro v hv hn
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh,
      RootedForest.adjoin_vertices, Finset.mem_insert] at hv
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh] at hn ⊢
    rcases hv with rfl | hv
    · simp at hn
    · have hvne : v ≠ Sum.inr i := fun he => hfresh (he ▸ hv)
      have hpne : F.forest.parent v ≠ Sum.inr i :=
        fun he => hfresh (he ▸ F.forest.parent_mem v hv)
      simp only [Function.update_of_ne hvne] at hn
      simpa only [RootedForest.adjoin, hvne, ↓reduceIte,
        Function.update_of_ne hvne, Function.update_of_ne hpne] using ho.parent_lt v hv hn
  · intro j hj
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh,
      RootedForest.adjoin_vertices, Finset.mem_insert, Sum.inr.injEq] at hj
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh]
    rcases hj with rfl | hj
    · simp
    · have hjne : Sum.inr j ≠ Sum.inr i := fun he => hfresh (he ▸ hj)
      simpa only [Function.update_of_ne hjne] using ho.frozen_incoming j hj
  · intro j v hj hv hp
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh,
      RootedForest.adjoin_vertices, Finset.mem_insert] at hj hv
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh, RootedForest.adjoin] at hp ⊢
    rcases hv with rfl | hv
    · simp
    · have hvne : v ≠ Sum.inr i := fun he => hfresh (he ▸ hv)
      simp only [hvne, ↓reduceIte] at hp
      rcases hj with hj | hj
      · exact False.elim (hfresh (hj ▸ hp ▸ F.forest.parent_mem v hv))
      · simpa only [Function.update_of_ne hvne] using ho.frozen_children j v hj hv hp

/-- The actual sign-controlled transition preserves timestamp ordering. -/
theorem transitionLaw_timestamp_order {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F.forest) (ht : TimesValidAt x n (i + 1) F)
    (ho : TimestampOrder F) :
    ∀ᵐ F' ∂transitionLaw x i F, TimestampOrder F' := by
  cases hx : x (i + 1)
  · have hfresh : Sum.inr i ∉ F.forest.vertices := by
      rw [hF.vertices_eq]
      exact Reverse.fresh_freezing_label x n i
    simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr (ho.insertLabel hfresh)
  · have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
    have htwo : 2 ≤ F.forest.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [transitionLaw, hx, ↓reduceIte]
    exact joinLaw_ae F (i + 1) htwo TimestampOrder (fun _ hp => ho.joinChoice ht hF hp)

/-- All actual reverse phases satisfy both strict source ordering conditions. -/
theorem lawAfter_timestamp_order (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂lawAfter x n k, TimestampOrder F := by
  induction k with
  | zero => simpa [lawAfter] using initial_timestamp_order x n
  | succ k ih =>
    have hkn : k < n := by omega
    have ih := ih (by omega)
    have hphase : n - k = n - (k + 1) + 1 := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih, lawAfter_forest_valid x n k hn (by omega),
          lawAfter_times_valid x n k hn (by omega)] with F ho hF ht
        rw [hphase] at hF ht
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (transitionLaw_timestamp_order hn (by omega) hF ht ho)
      _ = 1 := by simp

theorem treeLaw_timestamp_order (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, TimestampOrder F := lawAfter_timestamp_order x n n hn le_rfl

/-- Every genuine parent edge has a positive timestamp. -/
theorem TimesValidAt.edgeTime_ne_zero_of_parent_ne {x : SignSequence} {n i : ℕ} {F : Forest}
    (ht : TimesValidAt x n i F) {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices)
    (hne : F.forest.parent v ≠ v) : F.edgeTime v ≠ 0 := by
  intro hz
  exact hne (F.forest.parent_of_root ((ht.root_zero v hv).mp hz))

/-- In canonical birth-time coordinates, each edge timestamp is the maximum
of its endpoint IDs, matching the forward representation. -/
theorem TimestampOrder.parent_edge_time {F : Forest} (ho : TimestampOrder F)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) (hne : F.edgeTime v ≠ 0) :
    max (F.edgeTime (F.forest.parent v)) (F.edgeTime v) = F.edgeTime v :=
  max_eq_right (ho.parent_lt v hv hne).le

/-- Every frozen label is strictly greater than every incident edge label,
expressed in the common canonical birth-time coordinates. -/
theorem TimestampOrder.frozen_adjacent {x : SignSequence} {n i : ℕ} {F : Forest}
    (ho : TimestampOrder F) (ht : TimesValidAt x n i F) {j : ℕ} {v : ℕ ⊕ ℕ}
    (ha : F.forest.graph.Adj (.inr j) v) :
    max (F.edgeTime (.inr j)) (F.edgeTime v) < j + 1 := by
  rcases ha with ⟨hj, hv, hne, hp | hp⟩
  · have hn : F.edgeTime (.inr j) ≠ 0 :=
      ht.edgeTime_ne_zero_of_parent_ne hj (by rw [hp]; exact hne.symm)
    have hlt := ho.parent_lt (.inr j) hj hn
    rw [hp] at hlt
    exact max_lt (ho.frozen_incoming j hj) (hlt.trans (ho.frozen_incoming j hj))
  · have hn : F.edgeTime v ≠ 0 :=
      ht.edgeTime_ne_zero_of_parent_ne hv (by rw [hp]; exact hne)
    have hlt := ho.parent_lt v hv hn
    rw [hp] at hlt
    have htlt := ho.frozen_children j v hj hv hp
    exact max_lt (hlt.trans htlt) htlt

end Freezing1.ReverseStamped
