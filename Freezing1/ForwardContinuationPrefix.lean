module

public import Freezing1.ForwardTruncationLaw

/-!
# A genuine continuation preserves every earlier canonical prefix
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

theorem continuationLaw_hasHistory {x : SignSequence} {a k : ℕ} {s : State}
    (hs : HasHistory x a s) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ t ∂continuationLaw x a k s, HasHistory x (a + k) t := by
  induction k generalizing a s with
  | zero => simpa [continuationLaw] using hs
  | succ k ih =>
    have ha : (a : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show a < a + (k + 1) by omega)) hn
    have hpos := ((lt_extinctionTime_iff x a).mp ha) a le_rfl
    have hne : s.active.Nonempty := by
      apply Finset.card_pos.mp
      have hc := hs.current.count
      omega
    have hnext : ∀ᵐ w ∂transitionLaw s (a + 1) (x (a + 1)),
        HasHistory x (a + 1) w := by
      apply transitionLaw_ae s _ _ _
      · intro he
        exact (hne.ne_empty he).elim
      · intro v hv
        exact hs.extend (hs.current.step hv) ⟨v, hv, rfl⟩
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂transitionLaw s (a + 1) (x (a + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [hnext] with w hw
        have hrest : (((a + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
          simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hn
        have hh := ih hw hrest
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using
          (ae_iff_prob_eq_one measurable_from_top).mp hh
      _ = 1 := by simp

theorem continuationLaw_preserves_prefix {x : SignSequence} {a b k : ℕ} {s : State}
    (hs : HasHistory x b s) (ha : a ≤ b)
    (hn : ((b + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ t ∂continuationLaw x b k s, truncateAt t a = truncateAt s a := by
  induction k generalizing b s with
  | zero => simp [continuationLaw]
  | succ k ih =>
    have hb : (b : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show b < b + (k + 1) by omega)) hn
    have hpos := ((lt_extinctionTime_iff x b).mp hb) b le_rfl
    have hne : s.active.Nonempty := by
      apply Finset.card_pos.mp
      have hc := hs.current.count
      omega
    have hn1 : ((b + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      (by exact_mod_cast (show b + 1 ≤ b + (k + 1) by omega) :
        ((b + 1 : ℕ) : ℕ∞) ≤ (b + (k + 1) : ℕ)).trans hn
    have hnext : ∀ᵐ w ∂transitionLaw s (b + 1) (x (b + 1)),
        HasHistory x (b + 1) w ∧ truncateAt w a = truncateAt s a := by
      apply transitionLaw_ae s _ _ _
      · intro he
        exact (hne.ne_empty he).elim
      · intro v hv
        exact ⟨hs.extend (hs.current.step hv) ⟨v, hv, rfl⟩, truncate_step hs hn1 ha hv⟩
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂transitionLaw s (b + 1) (x (b + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [hnext] with w hw
        have hrest : (((b + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
          simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hn
        have hh := (ih hw.1 (ha.trans (Nat.le_succ b)) hrest).mono
          (fun t ht => ht.trans hw.2)
        exact (ae_iff_prob_eq_one measurable_from_top).mp hh
      _ = 1 := by simp

theorem continuationLaw_truncate_self {x : SignSequence} {a k : ℕ} {s : State}
    (hs : HasHistory x a s) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ t ∂continuationLaw x a k s, truncateAt t a = s := by
  have ha : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast (Nat.le_add_right a k) : (a : ℕ∞) ≤ (a + k : ℕ)).trans hn
  have he := (hs.historyShape ha).prefix_self
  exact (continuationLaw_preserves_prefix hs le_rfl hn).mono fun _ ht => ht.trans he

theorem map_continuationLaw_truncate {x : SignSequence} {a k : ℕ} {s : State}
    (hs : HasHistory x a s) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (continuationLaw x a k s).map (fun t => truncateAt t a) = Measure.dirac s := by
  calc
    _ = (continuationLaw x a k s).map (fun _ => s) :=
      Measure.map_congr (continuationLaw_truncate_self hs hn)
    _ = _ := by simp

end Freezing1.Forward
