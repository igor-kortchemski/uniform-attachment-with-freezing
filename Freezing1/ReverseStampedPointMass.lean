module

public import Freezing1.ReverseStampedReconstruction
public import Freezing1.ReverseStampedTransitionProbability

/-!
# Actual point masses along legal reverse histories

Unique predecessor reconstruction turns the genuine Markov bind into a
one-state contribution. Consequently a specified legal history has the exact
product probability claimed in the source. History existence for every
admissible terminal tree and the active-label quotient remain separate.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped Classical ENNReal BigOperators

/-- Exact schedule-dependent mass of one legal reverse step. -/
noncomputable def stepMass (x : SignSequence) (i : ℕ) : ℝ≥0∞ :=
  if x (i + 1) then
    1 / (((activeCount x (i + 1)).toNat * ((activeCount x (i + 1)).toNat - 1) : ℕ) : ℝ≥0∞)
  else 1

/-- The actual transition law is supported on legal deterministic outputs. -/
theorem transitionLaw_ae_legalStep {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hv : Reverse.ValidAt x n (i + 1) F.forest) :
    ∀ᵐ H ∂transitionLaw x i F, LegalStep x i F H := by
  cases hx : x (i + 1)
  · simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr (by simp [LegalStep, hx])
  · have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
    have htwo : 2 ≤ F.forest.roots.card := by
      rw [hv.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [transitionLaw, hx, ↓reduceIte]
    apply joinLaw_ae F (i + 1) htwo (LegalStep x i F)
    intro p hp
    simp only [LegalStep, hx, ↓reduceIte]
    exact ⟨p, hp, rfl⟩

/-- Every legal output has the exact one-step schedule mass. -/
theorem transitionLaw_legalStep_mass {x : SignSequence} {n i : ℕ} {F H : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hv : Reverse.ValidAt x n (i + 1) F.forest) (ht : TimesValidAt x n (i + 1) F)
    (hs : LegalStep x i F H) : (transitionLaw x i F) {H} = stepMass x i := by
  cases hx : x (i + 1)
  · simp only [LegalStep, hx, Bool.false_eq_true, ↓reduceIte] at hs
    simp [transitionLaw, stepMass, hx, hs]
  · simp only [LegalStep, hx, ↓reduceIte] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
    have htwo : 2 ≤ F.forest.roots.card := by
      rw [hv.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [transitionLaw, stepMass, hx, ↓reduceIte]
    rw [joinLaw_singleton F (by omega)
      (fun v hv' => (ht.root_zero v (RootedForest.mem_roots.mp hv').1).mpr hv') htwo hp,
      card_offDiag_eq_mul_pred, hv.roots_card]

/-- A nonlegal output has zero mass in the genuine transition kernel. -/
theorem transitionLaw_singleton_zero {x : SignSequence} {n i : ℕ} {F H : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hv : Reverse.ValidAt x n (i + 1) F.forest) (hs : ¬ LegalStep x i F H) :
    (transitionLaw x i F) {H} = 0 := by
  have hae := transitionLaw_ae_legalStep hn hi hv
  apply measure_mono_null (t := {G | ¬ LegalStep x i F G}) _ (ae_iff.mp hae)
  intro G hG
  change ¬ LegalStep x i F G
  simpa only [Set.mem_singleton_iff.mp hG] using hs

/-- Unique predecessor reconstruction evaluates the actual bind at a legal
output. No product probability is assumed in this identity. -/
theorem lawAfter_singleton_succ {x : SignSequence} {n k : ℕ} {F H : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    (hv : Reverse.ValidAt x n (n - k) F.forest) (ht : TimesValidAt x n (n - k) F)
    (hd : CanonicalDefaults F) (hs : LegalStep x (n - (k + 1)) F H) :
    (lawAfter x n (k + 1)) {H} =
      stepMass x (n - (k + 1)) * (lawAfter x n k) {F} := by
  have hi : n - (k + 1) < n := by omega
  have hphase : n - k = n - (k + 1) + 1 := by omega
  rw [hphase] at hv ht
  rw [lawAfter, ite_eq_left hk, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ G, ({F} : Set Forest).indicator (fun _ => stepMass x (n - (k + 1))) G
        ∂lawAfter x n k := by
      apply lintegral_congr_ae
      filter_upwards [lawAfter_forest_valid x n k hn (by omega),
        lawAfter_times_valid x n k hn (by omega), lawAfter_canonical_defaults x n k]
        with G hvG htG hdG
      rw [hphase] at hvG htG
      by_cases he : G = F
      · subst G
        simp only [Set.indicator_of_mem (show F ∈ ({F} : Set Forest) from rfl)]
        exact transitionLaw_legalStep_mass hn hi hv ht hs
      · have hnot : ¬ LegalStep x (n - (k + 1)) G H := by
          intro hG
          exact he (legalStep_predecessor_eq hvG hv htG ht hdG hd hG hs)
        rw [transitionLaw_singleton_zero hn hi hvG hnot]
        simp [he]
    _ = _ := lintegral_indicator_const (by trivial) _

noncomputable def historyMass (x : SignSequence) (n : ℕ) : ℕ → ℝ≥0∞
  | 0 => 1
  | k + 1 => stepMass x (n - (k + 1)) * historyMass x n k

/-- Exact partial-history point mass, derived from the actual Markov law. -/
theorem lawAfter_singleton_of_history {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (F : ℕ → Forest)
    (hv : ∀ i ≤ n, Reverse.ValidAt x n i (F i).forest)
    (ht : ∀ i ≤ n, TimesValidAt x n i (F i))
    (hd : ∀ i ≤ n, CanonicalDefaults (F i))
    (hs : ∀ i < n, LegalStep x i (F (i + 1)) (F i))
    (hinit : F n = initial x n) (k : ℕ) (hk : k ≤ n) :
    (lawAfter x n k) {F (n - k)} = historyMass x n k := by
  induction k with
  | zero => simp [lawAfter, historyMass, hinit]
  | succ k ih =>
    have hkn : k < n := by omega
    have hphase : n - k = n - (k + 1) + 1 := by omega
    have hstep : LegalStep x (n - (k + 1)) (F (n - k)) (F (n - (k + 1))) := by
      rw [hphase]
      exact hs _ (by omega)
    rw [lawAfter_singleton_succ hn hkn (hv _ (by omega)) (ht _ (by omega))
      (hd _ (by omega)) hstep, ih (by omega)]
    rfl

theorem historyMass_eq_prod (x : SignSequence) (n k : ℕ) :
    historyMass x n k = ∏ j ∈ Finset.range k, stepMass x (n - (j + 1)) := by
  induction k with
  | zero => simp [historyMass]
  | succ k ih => simp only [historyMass, Finset.prod_range_succ, ih, mul_comm]

/-- The source's chronological product equals the reverse processing product. -/
theorem historyMass_terminal_eq_prod (x : SignSequence) (n : ℕ) :
    historyMass x n n = ∏ i ∈ Finset.range n, stepMass x i := by
  rw [historyMass_eq_prod]
  have he : (fun j => stepMass x (n - (j + 1))) = (fun j => stepMass x (n - 1 - j)) := by
    funext j
    congr 1
    omega
  rw [he]
  exact Finset.prod_range_reflect _ _

/-- A specified legal reverse history has the claimed terminal product mass.
Existence of such a history is supplied explicitly, not inferred from a
shape-only admissibility condition. -/
theorem treeLaw_singleton_of_history {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (F : ℕ → Forest)
    (hv : ∀ i ≤ n, Reverse.ValidAt x n i (F i).forest)
    (ht : ∀ i ≤ n, TimesValidAt x n i (F i))
    (hd : ∀ i ≤ n, CanonicalDefaults (F i))
    (hs : ∀ i < n, LegalStep x i (F (i + 1)) (F i))
    (hinit : F n = initial x n) :
    (treeLaw x n) {F 0} = ∏ i ∈ Finset.range n, stepMass x i := by
  simpa only [treeLaw, Nat.sub_self, historyMass_terminal_eq_prod] using
    lawAfter_singleton_of_history hn F hv ht hd hs hinit n le_rfl

/-- Real normalization of a legal step agrees with the source ordered-pair
factor, with no division by zero at an extinction step. -/
theorem stepMass_toReal {x : SignSequence} {i : ℕ}
    (hi : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (stepMass x i).toReal = if x (i + 1) then
      ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))⁻¹ else 1 := by
  cases hx : x (i + 1)
  · simp [stepMass, hx]
  · have htwo : 2 ≤ (activeCount x (i + 1)).toNat :=
      two_le_activeCount_toNat_succ_of_attachment hi hx
    have hc : ((activeCount x (i + 1)).toNat : ℝ) = (activeCount x (i + 1) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hi)
    simp only [stepMass, hx, ↓reduceIte]
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast,
      Nat.cast_mul, Nat.cast_sub (show 1 ≤ (activeCount x (i + 1)).toNat by omega),
      Nat.cast_one, hc, one_div]

/-- The actual terminal mass of any legal history is the reverse product A16. -/
theorem treeLaw_real_singleton_of_history {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (F : ℕ → Forest)
    (hv : ∀ i ≤ n, Reverse.ValidAt x n i (F i).forest)
    (ht : ∀ i ≤ n, TimesValidAt x n i (F i))
    (hd : ∀ i ≤ n, CanonicalDefaults (F i))
    (hs : ∀ i < n, LegalStep x i (F (i + 1)) (F i))
    (hinit : F n = initial x n) :
    (treeLaw x n).real {F 0} = reverseHistoryWeight x n := by
  rw [Measure.real, treeLaw_singleton_of_history hn F hv ht hd hs hinit, ENNReal.toReal_prod]
  unfold reverseHistoryWeight
  apply Finset.prod_congr rfl
  intro i hi
  apply stepMass_toReal
  exact le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by
    exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hi))) hn

/-- The source's factorial normalization, now attached to a genuine terminal
point probability along a legal history, including `n = τ`. -/
theorem treeLaw_real_singleton_factorial_of_history {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (F : ℕ → Forest)
    (hv : ∀ i ≤ n, Reverse.ValidAt x n i (F i).forest)
    (ht : ∀ i ≤ n, TimesValidAt x n i (F i))
    (hd : ∀ i ≤ n, CanonicalDefaults (F i))
    (hs : ∀ i < n, LegalStep x i (F (i + 1)) (F i))
    (hinit : F n = initial x n) :
    (treeLaw x n).real {F 0} =
      (Nat.factorial (activeCount x n).toNat : ℝ)⁻¹ * forwardHistoryWeight x n := by
  rw [treeLaw_real_singleton_of_history hn F hv ht hd hs hinit,
    reverseHistoryWeight_eq_factorial_inv_mul_forward x n hn]

end Freezing1.ReverseStamped
