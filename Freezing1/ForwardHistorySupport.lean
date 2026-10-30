module

public import Freezing1.ForwardReconstruction

/-!
# Legal histories of the actual forward law

All structural, labeling, default-value and population invariants are carried
along the history. Before extinction the genuine uniform transition is
supported on legal active choices, so every actual terminal sample admits
such a history. No shape-only support assertion is assumed.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

structure PhaseData (x : SignSequence) (n : ℕ) (s : State) : Prop where
  valid : ValidAt n s
  labels : LabelsValidAt n s
  defaults : CanonicalDefaults s
  count : (s.active.card : ℤ) = activeCount x n

theorem initial_phaseData (x : SignSequence) : PhaseData x 0 initial := by
  exact ⟨initial_valid, initial_labels_valid, initial_canonical_defaults, by simp [initial]⟩

theorem PhaseData.step {x : SignSequence} {n : ℕ} {s : State}
    (hd : PhaseData x n s) {v : ℕ} (hv : v ∈ s.active) :
    PhaseData x (n + 1) (step s (n + 1) (x (n + 1)) v) := by
  refine ⟨hd.valid.step _ _, hd.labels.step _ _, hd.defaults.step hd.valid _ _, ?_⟩
  have hfresh : n + 1 ∉ s.vertices := by intro h; have := hd.valid.vertices_le _ h; omega
  have hactive : n + 1 ∉ s.active := fun h => hfresh (hd.valid.active_subset h)
  have hcard : 0 < s.active.card := Finset.card_pos.mpr ⟨v, hv⟩
  rw [Forward.step, ite_eq_left hv, activeCount_succ]
  cases hx : x (n + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte, Forward.freeze]
    rw [Finset.card_erase_of_mem hv, Nat.cast_sub (by omega), Nat.cast_one, hd.count]
    omega
  · simp only [↓reduceIte, Forward.attach]
    rw [Finset.card_insert_of_notMem hactive]
    simp [hd.count]

theorem treeLaw_phaseData (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : ∀ᵐ s ∂treeLaw x n, PhaseData x n s := by
  filter_upwards [treeLaw_valid x n, treeLaw_labels_valid x n,
    treeLaw_canonical_defaults x n, treeLaw_counts x n hn] with s hv hl hd hc
  exact ⟨hv, hl, hd, hc.1⟩

/-- With an active vertex available, the genuine transition has only legal outputs. -/
theorem transitionLaw_ae_legalStep (x : SignSequence) (n : ℕ) (s : State)
    (hne : s.active.Nonempty) :
    ∀ᵐ H ∂transitionLaw s (n + 1) (x (n + 1)), LegalStep x n s H := by
  apply transitionLaw_ae
  · intro he
    simp only [he, Finset.not_nonempty_empty] at hne
  · intro v hv
    exact ⟨v, hv, rfl⟩

theorem transitionLaw_phaseData {x : SignSequence} {n : ℕ} {s : State}
    (hd : PhaseData x n s) (hne : s.active.Nonempty) :
    ∀ᵐ H ∂transitionLaw s (n + 1) (x (n + 1)), PhaseData x (n + 1) H := by
  apply transitionLaw_ae
  · intro he
    simp only [he, Finset.not_nonempty_empty] at hne
  · intro v hv
    exact hd.step hv

def HasHistory (x : SignSequence) (n : ℕ) (H : State) : Prop :=
  ∃ F : ℕ → State, F n = H ∧ F 0 = initial ∧
    (∀ i ≤ n, PhaseData x i (F i)) ∧ (∀ i < n, LegalStep x i (F i) (F (i + 1)))

theorem initial_hasHistory (x : SignSequence) : HasHistory x 0 initial := by
  refine ⟨fun _ => initial, rfl, rfl, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst i
    exact initial_phaseData x
  · intro i hi
    omega

theorem HasHistory.current {x : SignSequence} {n : ℕ} {H : State}
    (h : HasHistory x n H) : PhaseData x n H := by
  obtain ⟨F, hcur, _, hd, _⟩ := h
  simpa only [hcur] using hd n le_rfl

theorem HasHistory.extend {x : SignSequence} {n : ℕ} {G H : State}
    (h : HasHistory x n G) (hd : PhaseData x (n + 1) H)
    (hs : LegalStep x n G H) : HasHistory x (n + 1) H := by
  obtain ⟨F, hcur, hinit, hdata, hsteps⟩ := h
  refine ⟨Function.update F (n + 1) H, Function.update_self _ _ _, ?_, ?_, ?_⟩
  · simpa only [Function.update_of_ne (show 0 ≠ n + 1 by omega)] using hinit
  · intro i hi
    by_cases he : i = n + 1
    · subst i
      simpa only [Function.update_self] using hd
    · simpa only [Function.update_of_ne he] using hdata i (by omega)
  · intro i hi
    by_cases he : i = n
    · subst i
      have hs' : LegalStep x n (F n) H := by rw [hcur]; exact hs
      simpa only [Function.update_of_ne (show n ≠ n + 1 by omega), Function.update_self] using hs'
    · have hi' : i < n := by omega
      simpa only [Function.update_of_ne (show i ≠ n + 1 by omega),
        Function.update_of_ne (show i + 1 ≠ n + 1 by omega)] using hsteps i hi'

/-- Every actual sample up to and including extinction has a legal history. -/
theorem treeLaw_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : ∀ᵐ H ∂treeLaw x n, HasHistory x n H := by
  induction n with
  | zero => simpa [treeLaw] using initial_hasHistory x
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    have ih := ih hnτ.le
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _G, (1 : ℝ≥0∞) ∂treeLaw x n := by
        apply lintegral_congr_ae
        filter_upwards [ih, treeLaw_active_nonempty x n hnτ] with G hG hne
        have hnext : ∀ᵐ H ∂transitionLaw G (n + 1) (x (n + 1)), HasHistory x (n + 1) H := by
          filter_upwards [transitionLaw_phaseData hG.current hne,
            transitionLaw_ae_legalStep x n G hne] with H hd hs
          exact hG.extend hd hs
        exact (ae_iff_prob_eq_one measurable_from_top).mp hnext
      _ = 1 := by simp

end Freezing1.Forward
