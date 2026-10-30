module

public import Freezing1.ReverseHistory
public import Freezing1.ReverseStampedHistoryExistence
public import Freezing1.ConstructionEquivalence

/-!
# A common probability space for reverse trajectories and edge timestamps

The original reverse transition kernels are lifted to complete histories of
stamped forests. Forgetting stamps gives the previously defined actual joint
history law, while retaining the current stamped forest gives its existing
marginal law. Thus T05 couples that entire trajectory to the canonical
forward terminal state without assuming a temporal identification.
-/

@[expose] public section

namespace Freezing1.ReverseStampedHistory

open MeasureTheory ReverseStamped
open scoped ENNReal

structure History where
  current : Forest
  past : List Forest

instance : MeasurableSpace History := ⊤
instance : DiscreteMeasurableSpace History := ⟨fun _ => trivial⟩

def initial (x : SignSequence) (n : ℕ) : History := ⟨ReverseStamped.initial x n, []⟩

def push (H : History) (F : Forest) : History := ⟨F, H.current :: H.past⟩

def forget (H : History) : ReverseHistory.History :=
  ⟨H.current.forest, H.past.map Forest.forest⟩

def stage (H : History) (j : ℕ) : Forest :=
  (H.current :: H.past).getD j ⟨RootedForest.isolated ∅, fun _ => 0⟩

@[simp] theorem stage_zero (H : History) : stage H 0 = H.current := rfl

@[simp] theorem stage_push_succ (H : History) (F : Forest) (j : ℕ) :
    stage (push H F) (j + 1) = stage H j := by simp [stage, push]

@[simp] theorem forget_push (H : History) (F : Forest) :
    forget (push H F) = ReverseHistory.push (forget H) F.forest := rfl

theorem forget_stage (H : History) (j : ℕ) :
    ReverseHistory.stage (forget H) j = (stage H j).forest := by
  change (((H.current :: H.past).map Forest.forest)[j]?).getD (RootedForest.isolated ∅) =
    ((H.current :: H.past)[j]?.getD ⟨RootedForest.isolated ∅, fun _ => 0⟩).forest
  rw [List.getElem?_map]
  exact Option.getD_map Forest.forest ⟨RootedForest.isolated ∅, fun _ => 0⟩ _

noncomputable def transitionLaw (x : SignSequence) (i : ℕ) (H : History) : Measure History :=
  (ReverseStamped.transitionLaw x i H.current).map (push H)

instance transitionLaw_probability (x : SignSequence) (i : ℕ) (H : History) :
    IsProbabilityMeasure (transitionLaw x i H) :=
  Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

theorem map_transitionLaw_current (x : SignSequence) (i : ℕ) (H : History) :
    (transitionLaw x i H).map History.current = ReverseStamped.transitionLaw x i H.current := by
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  exact Measure.map_id

theorem map_transitionLaw_forget (x : SignSequence) (i : ℕ) (H : History) :
    (transitionLaw x i H).map forget = ReverseHistory.transitionLaw x i (forget H) := by
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  unfold ReverseHistory.transitionLaw
  change _ = (Reverse.transitionLaw x i H.current.forest).map (ReverseHistory.push (forget H))
  rw [← ReverseStamped.map_transitionLaw x i H.current,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

theorem map_transitionLaw_stage_succ (x : SignSequence) (i : ℕ) (H : History) (j : ℕ) :
    (transitionLaw x i H).map (fun H' => stage H' (j + 1)) = Measure.dirac (stage H j) := by
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  simp only [Function.comp_def, stage_push_succ]
  simp

noncomputable def lawAfter (x : SignSequence) (n : ℕ) : ℕ → Measure History
  | 0 => Measure.dirac (initial x n)
  | k + 1 => if k < n then
      (lawAfter x n k).bind (transitionLaw x (n - (k + 1)))
    else lawAfter x n k

instance lawAfter_probability (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (lawAfter x n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac (initial x n)); infer_instance
  | succ k ih =>
    simp only [lawAfter]
    split_ifs
    · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall fun H => transitionLaw_probability x _ H)
    · exact ih

theorem map_lawAfter_current (x : SignSequence) (n k : ℕ) :
    (lawAfter x n k).map History.current = ReverseStamped.lawAfter x n k := by
  induction k with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    simp only [lawAfter, ReverseStamped.lawAfter]
    split_ifs
    · rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      simp_rw [map_transitionLaw_current]
      rw [← Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable, ih]
    · exact ih

/-- Exact projection to the actual entire reverse history, not just separate marginals. -/
theorem map_lawAfter_forget (x : SignSequence) (n k : ℕ) :
    (lawAfter x n k).map forget = ReverseHistory.lawAfter x n k := by
  induction k with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    simp only [lawAfter, ReverseHistory.lawAfter]
    split_ifs
    · rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      simp_rw [map_transitionLaw_forget]
      rw [← Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable, ih]
    · exact ih

theorem map_lawAfter_stage (x : SignSequence) (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ k) :
    (lawAfter x n k).map (fun H => stage H j) = ReverseStamped.lawAfter x n (k - j) := by
  induction k generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact map_lawAfter_current x n 0
  | succ k ih =>
    cases j with
    | zero => simpa only [stage_zero, Nat.sub_zero] using map_lawAfter_current x n (k + 1)
    | succ j =>
      have hkn : k < n := by omega
      rw [lawAfter, ite_eq_left hkn,
        Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      simp_rw [map_transitionLaw_stage_succ]
      rw [Measure.bind_dirac_eq_map _ measurable_from_top]
      simpa only [Nat.add_sub_add_right] using ih j (by omega) (by omega)

theorem lawAfter_current_phaseData (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ H ∂lawAfter x n k, PhaseData x n (n - k) H.current := by
  apply ae_of_ae_map (f := History.current) measurable_from_top.aemeasurable
  rw [map_lawAfter_current]
  filter_upwards [ReverseStamped.lawAfter_hasPartialHistory x n k hn hk] with F hF
  exact hF.current

theorem lawAfter_stage_phaseData (x : SignSequence) (n k j : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) (hj : j ≤ k) :
    ∀ᵐ H ∂lawAfter x n k, PhaseData x n (n - k + j) (stage H j) := by
  apply ae_of_ae_map (f := fun H => stage H j) measurable_from_top.aemeasurable
  rw [map_lawAfter_stage x n k j hk hj]
  filter_upwards [ReverseStamped.lawAfter_hasPartialHistory x n (k - j) hn (by omega)] with F hF
  have he : n - (k - j) = n - k + j := by omega
  simpa only [he] using hF.current

/-- Every recorded transition is the sampled legal stamped transition. -/
theorem lawAfter_legalSteps (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ H ∂lawAfter x n k, ∀ j < k,
      LegalStep x (n - k + j) (stage H (j + 1)) (stage H j) := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ j hj => (Nat.not_lt_zero j hj).elim
  | succ k ih =>
    have hkn : k < n := by omega
    have hphase : n - k = n - (k + 1) + 1 := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _H, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih (by omega), lawAfter_current_phaseData x n k hn (by omega)] with H hH hd
        have hstep : ∀ᵐ F ∂ReverseStamped.transitionLaw x (n - (k + 1)) H.current,
            LegalStep x (n - (k + 1)) H.current F :=
          ReverseStamped.transitionLaw_ae_legalStep hn (by omega) (by simpa only [hphase] using hd.valid)
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
        filter_upwards [hstep] with F hF
        intro j hj
        cases j with
        | zero => simpa [stage, push] using hF
        | succ j =>
          have hi : n - (k + 1) + (j + 1) = n - k + j := by omega
          simpa only [stage_push_succ, hi] using hH j (by omega)
      _ = 1 := by simp

noncomputable def fullLaw (x : SignSequence) (n : ℕ) : Measure History := lawAfter x n n

instance fullLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (fullLaw x n) := lawAfter_probability x n n

theorem map_fullLaw_current (x : SignSequence) (n : ℕ) :
    (fullLaw x n).map History.current = ReverseStamped.treeLaw x n := map_lawAfter_current x n n

theorem map_fullLaw_forget (x : SignSequence) (n : ℕ) :
    (fullLaw x n).map forget = ReverseHistory.fullLaw x n := map_lawAfter_forget x n n

theorem map_fullLaw_forwardState (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (fullLaw x n).map (fun H => CanonicalTree.reverseState H.current) = Forward.treeLaw x n := by
  change (fullLaw x n).map (CanonicalTree.reverseState ∘ History.current) = _
  rw [← Measure.map_map measurable_from_top measurable_from_top, map_fullLaw_current]
  exact CanonicalTree.reverseStateLaw_eq_forward_treeLaw x n hn

theorem fullLaw_legalSteps (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂fullLaw x n, ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i) := by
  simpa only [fullLaw, Nat.sub_self, Nat.zero_add] using lawAfter_legalSteps x n n hn le_rfl

theorem fullLaw_phaseData (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂fullLaw x n, ∀ i ≤ n, PhaseData x n i (stage H i) := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i ≤ n
  · have hd := lawAfter_stage_phaseData x n n i hn le_rfl hi
    simp only [Nat.sub_self, Nat.zero_add] at hd
    filter_upwards [hd] with H hH
    exact fun _ => hH
  · exact Filter.Eventually.of_forall fun _ h => (hi h).elim

end Freezing1.ReverseStampedHistory
