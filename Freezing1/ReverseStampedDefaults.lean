module

public import Freezing1.ReverseTimestampSupport

/-!
# Canonical unused values in the timestamped reverse process

All values outside the actual vertex set remain the initial defaults: parent
and root are the identity, while depth and edge time are zero. These invariant
facts allow later reconstruction arguments to compare full functional states.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped Classical ENNReal

structure CanonicalDefaults (F : Forest) : Prop where
  outside : ∀ v, v ∉ F.forest.vertices →
    F.forest.parent v = v ∧ F.forest.root v = v ∧ F.forest.depth v = 0 ∧ F.edgeTime v = 0

theorem initial_canonical_defaults (x : SignSequence) (n : ℕ) :
    CanonicalDefaults (initial x n) := by
  constructor
  intro v hv
  simp [initial, Reverse.initial, RootedForest.isolated]

theorem CanonicalDefaults.joinChoice {F : Forest} (hd : CanonicalDefaults F)
    (t : ℕ) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) : CanonicalDefaults (joinChoice F t p) := by
  by_cases hp : p ∈ F.forest.roots.offDiag
  · constructor
    intro v hv
    simp only [ReverseStamped.joinChoice, dite_eq_left hp, RootedForest.join_vertices] at hv
    obtain ⟨hparent, hroot, hdepth, htime⟩ := hd.outside v hv
    have hvne : v ≠ p.2 := fun he => hv (he ▸ (RootedForest.mem_roots.mp
      (Finset.mem_offDiag.mp hp).2.1).1)
    simpa [ReverseStamped.joinChoice, hp, RootedForest.join, hvne, hroot] using
      And.intro hparent (And.intro hroot (And.intro hdepth htime))
  · simpa only [ReverseStamped.joinChoice, dite_eq_right hp] using hd

theorem CanonicalDefaults.insertLabel {F : Forest} (hd : CanonicalDefaults F) (i : ℕ) :
    CanonicalDefaults (insertLabel F i) := by
  by_cases hi : Sum.inr i ∈ F.forest.vertices
  · simpa only [ReverseStamped.insertLabel, dite_eq_left hi] using hd
  · constructor
    intro v hv
    simp only [ReverseStamped.insertLabel, dite_eq_right hi, RootedForest.adjoin_vertices,
      Finset.mem_insert, not_or] at hv
    simpa [ReverseStamped.insertLabel, hi, RootedForest.adjoin, hv.1] using hd.outside v hv.2

theorem transitionLaw_canonical_defaults {F : Forest} (hd : CanonicalDefaults F)
    (x : SignSequence) (i : ℕ) :
    ∀ᵐ G ∂transitionLaw x i F, CanonicalDefaults G := by
  cases hx : x (i + 1)
  · simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr (hd.insertLabel i)
  · simp only [transitionLaw, hx, ↓reduceIte]
    by_cases htwo : 2 ≤ F.forest.roots.card
    · exact joinLaw_ae F (i + 1) htwo CanonicalDefaults (fun p _ => hd.joinChoice (i + 1) p)
    · simp only [joinLaw, ite_eq_right htwo]
      exact (ae_dirac_iff (by trivial)).mpr hd

/-- Canonical defaults persist even for held phases and totalized schedules. -/
theorem lawAfter_canonical_defaults (x : SignSequence) (n k : ℕ) :
    ∀ᵐ F ∂lawAfter x n k, CanonicalDefaults F := by
  induction k with
  | zero => simpa [lawAfter] using initial_canonical_defaults x n
  | succ k ih =>
    by_cases hk : k < n
    · apply (ae_iff_prob_eq_one measurable_from_top).mpr
      rw [lawAfter, ite_eq_left hk,
        Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
      calc
        _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂lawAfter x n k := by
          apply lintegral_congr_ae
          filter_upwards [ih] with F hd
          exact (ae_iff_prob_eq_one measurable_from_top).mp
            (transitionLaw_canonical_defaults hd x _)
        _ = 1 := by simp
    · simpa only [lawAfter, ite_eq_right hk] using ih

theorem treeLaw_canonical_defaults (x : SignSequence) (n : ℕ) :
    ∀ᵐ F ∂treeLaw x n, CanonicalDefaults F := lawAfter_canonical_defaults x n n

end Freezing1.ReverseStamped
