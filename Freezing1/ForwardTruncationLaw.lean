module

public import Freezing1.ForwardSupportCharacterization
public import Freezing1.ForwardComponentContinuation

/-!
# Canonical truncation recovers the actual earlier forward law

Complete terminal timestamps determine every predecessor. The proof compares
legal histories, so coherence is asserted on the actual supported states,
without imposing identities on arbitrary malformed states.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

theorem legalHistories_eq {x : SignSequence} {n : ℕ} {F G : ℕ → State}
    (hF : ∀ i ≤ n, PhaseData x i (F i)) (hG : ∀ i ≤ n, PhaseData x i (G i))
    (hFs : ∀ i < n, LegalStep x i (F i) (F (i + 1)))
    (hGs : ∀ i < n, LegalStep x i (G i) (G (i + 1))) (he : F n = G n) :
    ∀ i ≤ n, F i = G i := by
  induction n with
  | zero => intro i hi; simpa only [Nat.le_zero.mp hi] using he
  | succ n ih =>
    have hn : F n = G n := by
      apply legalStep_predecessor_eq (hF n (by omega)).valid (hG n (by omega)).valid
        (hF n (by omega)).defaults (hG n (by omega)).defaults (hG n (by omega)).labels
        (hFs n (by omega))
      rw [he]
      exact hGs n (by omega)
    intro i hi
    by_cases hin : i = n + 1
    · simpa only [hin] using he
    · exact ih (fun j hj => hF j (by omega)) (fun j hj => hG j (by omega))
        (fun j hj => hFs j (by omega)) (fun j hj => hGs j (by omega)) hn i (by omega)

theorem HistoryShape.prefix_phaseData {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) {k : ℕ} (hk : k ≤ n) :
    PhaseData x k (truncateAt s k) := by
  induction k with
  | zero => rw [hs.prefix_zero]; exact initial_phaseData x
  | succ k ih =>
    obtain ⟨v, hv, he⟩ := hs.prefix_legalStep (show k < n by omega)
    rw [he]
    exact (ih (by omega)).step hv

theorem HistoryShape.prefix_hasHistory {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) {k : ℕ} (hk : k ≤ n) :
    HasHistory x k (truncateAt s k) := by
  exact ⟨truncateAt s, rfl, hs.prefix_zero,
    fun i hi => hs.prefix_phaseData (hi.trans hk), fun i hi => hs.prefix_legalStep (hi.trans_le hk)⟩

theorem HistoryShape.truncate_truncate {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    truncateAt (truncateAt s b) a = truncateAt s a := by
  have hbτ : (b : ℕ∞) ≤ extinctionTime x := (by exact_mod_cast hb : (b : ℕ∞) ≤ n).trans hn
  have hshape := (hs.prefix_hasHistory hb).historyShape hbτ
  exact legalHistories_eq (fun i hi => hshape.prefix_phaseData hi)
    (fun i hi => hs.prefix_phaseData (hi.trans hb))
    (fun i hi => hshape.prefix_legalStep hi)
    (fun i hi => hs.prefix_legalStep (hi.trans_le hb)) hshape.prefix_self a hab

theorem truncate_step_predecessor {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x)
    {v : ℕ} (hv : v ∈ s.active) :
    truncateAt (step s (n + 1) (x (n + 1)) v) n = s := by
  have hd := hs.current
  have he : LegalStep x n s (step s (n + 1) (x (n + 1)) v) := ⟨v, hv, rfl⟩
  have hshape := (hs.extend (hd.step hv) he).historyShape hn
  have hprefix := hshape.prefix_phaseData (Nat.le_succ n)
  have hp := hshape.prefix_legalStep (Nat.lt_succ_self n)
  rw [hshape.prefix_self] at hp
  exact legalStep_predecessor_eq hprefix.valid hd.valid hprefix.defaults hd.defaults hd.labels hp he

theorem truncate_step {x : SignSequence} {n a : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : a ≤ n) {v : ℕ} (hv : v ∈ s.active) :
    truncateAt (step s (n + 1) (x (n + 1)) v) a = truncateAt s a := by
  have he : LegalStep x n s (step s (n + 1) (x (n + 1)) v) := ⟨v, hv, rfl⟩
  have hshape := (hs.extend (hs.current.step hv) he).historyShape hn
  rw [← hshape.truncate_truncate hn ha (Nat.le_succ n), truncate_step_predecessor hs hn hv]

theorem transitionLaw_truncate {x : SignSequence} {n a : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : a ≤ n) :
    (transitionLaw s (n + 1) (x (n + 1))).map (fun t => truncateAt t a) =
      Measure.dirac (truncateAt s a) := by
  have hp : ∀ᵐ t ∂transitionLaw s (n + 1) (x (n + 1)), truncateAt t a = truncateAt s a := by
    apply transitionLaw_ae s _ _ _
    · intro _; rfl
    · intro v hv; exact truncate_step hs hn ha hv
  calc
    _ = (transitionLaw s (n + 1) (x (n + 1))).map (fun _ => truncateAt s a) :=
      Measure.map_congr hp
    _ = _ := by simp

/-- The terminal state's canonical truncation has the actual forward law at
any earlier time, including the extinction endpoint of the terminal horizon. -/
theorem treeLaw_map_truncate (x : SignSequence) {n a : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (ha : a ≤ n) :
    (treeLaw x n).map (fun s => truncateAt s a) = treeLaw x a := by
  induction n with
  | zero =>
    have : a = 0 := by omega
    subst a
    simp only [treeLaw, Measure.map_dirac]
    congr 1
    exact (initial_hasHistory x).historyShape hn |>.prefix_self
  | succ n ih =>
    by_cases han : a = n + 1
    · subst a
      calc
        _ = (treeLaw x (n + 1)).map id := by
          apply Measure.map_congr
          filter_upwards [treeLaw_historyShape x (n + 1) hn] with s hs using hs.prefix_self
        _ = _ := Measure.map_id
    · have ha' : a ≤ n := by omega
      have hn' : (n : ℕ∞) ≤ extinctionTime x :=
        (by exact_mod_cast Nat.le_succ n : (n : ℕ∞) ≤ (n + 1 : ℕ)).trans hn
      rw [treeLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      calc
        _ = (treeLaw x n).bind (fun s => Measure.dirac (truncateAt s a)) := by
          apply Measure.bind_congr_right
          filter_upwards [treeLaw_hasHistory x n hn'] with s hs
          exact transitionLaw_truncate hs hn ha'
        _ = (treeLaw x n).map (fun s => truncateAt s a) :=
          Measure.bind_dirac_eq_map _ measurable_from_top
        _ = _ := ih hn' ha'

end Freezing1.Forward
