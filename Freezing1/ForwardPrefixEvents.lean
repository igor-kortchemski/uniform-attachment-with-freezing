module

public import Freezing1.ForwardContinuationPrefix

/-!
# Events of genuine earlier states under the terminal tree law

The two-prefix bound exposes the actual continuation kernel. In particular,
uniform conditional bounds can be integrated without asserting independence
of the earlier tree and an unlabelled block forest.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem treeLaw_prefix_event (x : SignSequence) {n a : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (ha : a ≤ n) (P : State → Prop) :
    (treeLaw x n) {s | P (truncateAt s a)} = (treeLaw x a) {s | P s} := by
  have he := congrArg (fun μ : Measure State => μ {s | P s}) (treeLaw_map_truncate x hn ha)
  rw [Measure.map_apply measurable_from_top (by trivial)] at he
  exact he

theorem treeLaw_prefix_event_real (x : SignSequence) {n a : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (ha : a ≤ n) (P : State → Prop) :
    (treeLaw x n).real {s | P (truncateAt s a)} = (treeLaw x a).real {s | P s} :=
  congrArg ENNReal.toReal (treeLaw_prefix_event x hn ha P)

theorem treeLaw_two_prefix_event (x : SignSequence) {n a b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b) (hb : b ≤ n)
    (P : State → State → Prop) :
    (treeLaw x n) {s | P (truncateAt s a) (truncateAt s b)} =
      (treeLaw x b) {s | P (truncateAt s a) s} := by
  calc
    _ = (treeLaw x n) {s | P (truncateAt (truncateAt s b) a) (truncateAt s b)} := by
      apply measure_congr
      filter_upwards [treeLaw_historyShape x n hn] with s hs
      simp only [hs.truncate_truncate hn hab hb]
    _ = _ := treeLaw_prefix_event x hn hb (fun s => P (truncateAt s a) s)

/-- A uniform bound on the genuine continuation gives a bound for joint
events of two canonical prefixes of the terminal tree. -/
theorem treeLaw_two_prefix_event_le (x : SignSequence) {n a b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b) (hb : b ≤ n)
    (P : State → State → Prop) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ s, HasHistory x a s →
      (continuationLaw x a (b - a) s).real {t | P s t} ≤ r) :
    (treeLaw x n).real {s | P (truncateAt s a) (truncateAt s b)} ≤ r := by
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast (hab.trans hb) : (a : ℕ∞) ≤ n).trans hn
  have hsum : a + (b - a) = b := Nat.add_sub_of_le hab
  have hbτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by
    rw [hsum]
    exact (by exact_mod_cast hb : (b : ℕ∞) ≤ n).trans hn
  have hh : (treeLaw x n) {s | P (truncateAt s a) (truncateAt s b)} ≤ ENNReal.ofReal r := by
    rw [treeLaw_two_prefix_event x hn hab hb P, ← hsum, treeLaw_add_eq_bind_continuation,
      Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ ≤ ∫⁻ _s, ENNReal.ofReal r ∂treeLaw x a := by
        apply lintegral_mono_ae
        filter_upwards [treeLaw_hasHistory x a haτ] with s hs
        have he : (continuationLaw x a (b - a) s) {t | P (truncateAt t a) t} =
            (continuationLaw x a (b - a) s) {t | P s t} := by
          apply measure_congr
          filter_upwards [continuationLaw_truncate_self hs hbτ] with t ht
          simp only [ht]
        rw [he, ← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hbound s hs)
      _ = _ := by simp
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal hr] at hh'
  exact hh'

end Freezing1.Forward
