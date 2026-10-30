module

public import Freezing1.ReverseStampedPointMass

/-!
# Existence of histories for actual timestamped terminal samples

The actual reverse marginal carries a legal partial history almost surely.
The induction extends the recorded history by the sampled transition, retaining
all phase invariants. This supplies the history argument in the actual terminal
point-mass theorem; it does not assert reachability of an arbitrary admissible
shape or perform the active-label quotient count.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped Classical ENNReal

structure PhaseData (x : SignSequence) (n i : ℕ) (F : Forest) : Prop where
  valid : Reverse.ValidAt x n i F.forest
  times : TimesValidAt x n i F
  defaults : CanonicalDefaults F

def HasPartialHistory (x : SignSequence) (n k : ℕ) (H : Forest) : Prop :=
  ∃ F : ℕ → Forest, F (n - k) = H ∧ F n = initial x n ∧
    (∀ i, n - k ≤ i → i ≤ n → PhaseData x n i (F i)) ∧
    (∀ i, n - k ≤ i → i < n → LegalStep x i (F (i + 1)) (F i))

theorem initial_hasPartialHistory (x : SignSequence) (n : ℕ) :
    HasPartialHistory x n 0 (initial x n) := by
  refine ⟨fun _ => initial x n, rfl, rfl, ?_, ?_⟩
  · intro i hi hin
    have he : i = n := by omega
    subst i
    exact ⟨Reverse.initial_valid x n, initial_times_valid x n, initial_canonical_defaults x n⟩
  · intro i hi hin
    omega

theorem HasPartialHistory.current {x : SignSequence} {n k : ℕ} {H : Forest}
    (h : HasPartialHistory x n k H) : PhaseData x n (n - k) H := by
  obtain ⟨F, hcur, _, hd, _⟩ := h
  simpa only [hcur] using hd (n - k) le_rfl (Nat.sub_le _ _)

/-- Extend the recorded history by the actual newly processed reverse phase. -/
theorem HasPartialHistory.extend {x : SignSequence} {n k : ℕ} {G H : Forest}
    (h : HasPartialHistory x n k G) (hk : k < n)
    (hd : PhaseData x n (n - (k + 1)) H)
    (hs : LegalStep x (n - (k + 1)) G H) : HasPartialHistory x n (k + 1) H := by
  obtain ⟨F, hcur, hinit, hdata, hsteps⟩ := h
  let i := n - (k + 1)
  have hi : i < n := by dsimp [i]; omega
  have hphase : n - k = i + 1 := by dsimp [i]; omega
  refine ⟨Function.update F i H, ?_, ?_, ?_, ?_⟩
  · exact Function.update_self _ _ _
  · simpa only [Function.update_of_ne (Ne.symm (Nat.ne_of_lt hi))] using hinit
  · intro j hji hjn
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self] using hd
    · have hji' : n - k ≤ j := by dsimp [i] at he; omega
      simpa only [Function.update_of_ne he] using hdata j hji' hjn
  · intro j hji hjn
    by_cases he : j = i
    · subst j
      have hs' : LegalStep x i (F (i + 1)) H := by
        have hcur' : F (i + 1) = G := by simpa only [hphase] using hcur
        rw [hcur']
        exact hs
      simpa only [Function.update_of_ne (show i + 1 ≠ i by omega), Function.update_self] using hs'
    · have hji' : n - k ≤ j := by dsimp [i] at he; omega
      have hs' := hsteps j hji' hjn
      have hnext : j + 1 ≠ i := by dsimp [i] at *; omega
      simpa only [Function.update_of_ne he, Function.update_of_ne hnext] using hs'

/-- The actual lifted transition preserves the complete phase data. -/
theorem transitionLaw_phaseData {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hd : PhaseData x n (i + 1) F) :
    ∀ᵐ H ∂transitionLaw x i F, PhaseData x n i H := by
  have hv : ∀ᵐ H ∂transitionLaw x i F, Reverse.ValidAt x n i H.forest := by
    apply ae_of_ae_map (f := Forest.forest)
      (p := fun G : Reverse.Forest => Reverse.ValidAt x n i G) measurable_from_top.aemeasurable
    rw [map_transitionLaw]
    exact Reverse.transitionLaw_valid hn hi hd.valid
  filter_upwards [hv, transitionLaw_times_valid hn hi hd.valid hd.times,
    transitionLaw_canonical_defaults hd.defaults x i] with H hv ht hdefault
  exact ⟨hv, ht, hdefault⟩

/-- Every actual partial reverse sample has a complete legal recorded history. -/
theorem lawAfter_hasPartialHistory (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ H ∂lawAfter x n k, HasPartialHistory x n k H := by
  induction k with
  | zero => simpa [lawAfter] using initial_hasPartialHistory x n
  | succ k ih =>
    have hkn : k < n := by omega
    have ih := ih (by omega)
    have hi : n - (k + 1) < n := by omega
    have hphase : n - k = n - (k + 1) + 1 := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _G, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih] with G hG
        have hd := hG.current
        rw [hphase] at hd
        have hnext : ∀ᵐ H ∂transitionLaw x (n - (k + 1)) G,
            HasPartialHistory x n (k + 1) H := by
          filter_upwards [transitionLaw_phaseData hn hi hd,
            transitionLaw_ae_legalStep hn hi hd.valid] with H hdata hstep
          exact hG.extend hkn hdata hstep
        exact (ae_iff_prob_eq_one measurable_from_top).mp hnext
      _ = 1 := by simp

theorem treeLaw_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂treeLaw x n, HasPartialHistory x n n H := lawAfter_hasPartialHistory x n n hn le_rfl

/-- Any terminal state with a legal history has the exact reverse product mass. -/
theorem treeLaw_real_singleton_of_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {H : Forest} (hH : HasPartialHistory x n n H) :
    (treeLaw x n).real {H} = reverseHistoryWeight x n := by
  obtain ⟨F, hcur, hinit, hd, hs⟩ := hH
  simp only [Nat.sub_self] at hcur hd hs
  have hm := treeLaw_real_singleton_of_history hn F
    (fun i hi => (hd i (Nat.zero_le _) hi).valid)
    (fun i hi => (hd i (Nat.zero_le _) hi).times)
    (fun i hi => (hd i (Nat.zero_le _) hi).defaults)
    (fun i hi => hs i (Nat.zero_le _) hi) hinit
  simpa only [hcur] using hm

/-- Almost every actual terminal outcome has exactly the reverse product mass.
Existence of the history is derived from the actual kernel construction. -/
theorem treeLaw_real_singleton_ae (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂treeLaw x n, (treeLaw x n).real {H} = reverseHistoryWeight x n := by
  filter_upwards [treeLaw_hasHistory x n hn] with H hH
  exact treeLaw_real_singleton_of_hasHistory x n hn hH

/-- A terminal atom has nonzero probability exactly when it admits a legal
history. Thus no history existence is assumed for an actual positive atom. -/
theorem treeLaw_singleton_ne_zero_iff_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (H : Forest) :
    (treeLaw x n) {H} ≠ 0 ↔ HasPartialHistory x n n H := by
  constructor
  · intro hmass
    by_contra hhist
    apply hmass
    apply measure_mono_null (t := {G | ¬ HasPartialHistory x n n G}) _
      (ae_iff.mp (treeLaw_hasHistory x n hn))
    intro G hG
    change ¬ HasPartialHistory x n n G
    simpa only [Set.mem_singleton_iff.mp hG] using hhist
  · intro hhist hzero
    have hm := treeLaw_real_singleton_of_hasHistory x n hn hhist
    rw [Measure.real, hzero, ENNReal.toReal_zero] at hm
    exact (ne_of_gt (reverseHistoryWeight_pos x n hn)) hm.symm

/-- The actual terminal singleton law has the source factorial normalization,
including the extinction endpoint. This precedes any active-label quotient. -/
theorem treeLaw_real_singleton_factorial_ae (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂treeLaw x n,
      (treeLaw x n).real {H} =
        (Nat.factorial (activeCount x n).toNat : ℝ)⁻¹ * forwardHistoryWeight x n := by
  simpa only [reverseHistoryWeight_eq_factorial_inv_mul_forward x n hn] using
    treeLaw_real_singleton_ae x n hn

end Freezing1.ReverseStamped
