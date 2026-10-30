module

public import Freezing1.RootedForestDistance
public import Freezing1.ReverseCoalescenceTime
public import Freezing1.ReverseHistoryBernoulli

/-!
# Graph distance and coalescence on one actual reverse history

The first merger gives an exact geometric identity. Later bridges preserve
the old distance, while each tracked depth can grow at most once per step.
All transition and history assertions below are derived from the actual laws.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace Reverse

/-- Adding the singleton does not modify any ambient graph edge. -/
theorem insertLabel_graph (F : Forest) (i : ℕ) : (insertLabel F i).graph = F.graph := by
  unfold insertLabel
  split_ifs
  · rfl
  · exact F.adjoin_graph _

/-- The two distance identities needed at one actual reverse transition. -/
def DistanceStep (F F' : Forest) (u v : ℕ ⊕ ℕ) : Prop :=
  (u ∈ F.vertices → v ∈ F.vertices → F.root u = F.root v →
    F'.graph.dist u v = F.graph.dist u v) ∧
  (u ∈ F.vertices → v ∈ F.vertices → F.root u ≠ F.root v → F'.root u = F'.root v →
    F'.graph.dist u v = F'.depth u + F'.depth v)

theorem transitionLaw_distanceStep (x : SignSequence) (i : ℕ) (F : Forest)
    (hF : F.graph.IsAcyclic) (u v : ℕ ⊕ ℕ) :
    ∀ᵐ F' ∂transitionLaw x i F, DistanceStep F F' u v := by
  cases hx : x (i + 1)
  · simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    apply (ae_dirac_iff (by trivial)).mpr
    constructor
    · intro _ _ _
      rw [insertLabel_graph]
    · intro hu hv hne heq
      rw [insertLabel_root_old F i hu, insertLabel_root_old F i hv] at heq
      exact (hne heq).elim
  · simp only [transitionLaw, hx, ↓reduceIte]
    by_cases htwo : 2 ≤ F.roots.card
    · apply F.joinLaw_ae htwo
      intro p hp
      exact ⟨fun hu hv hroot => F.joinChoice_preserves_dist hF p hu hv hroot,
        fun hu hv hne heq => F.joinChoice_new_coalescence_dist hp hu hv hne heq⟩
    · simp only [RootedForest.joinLaw, ite_eq_right htwo]
      apply (ae_dirac_iff (by trivial)).mpr
      exact ⟨fun _ _ _ => rfl, fun _ _ hne heq => (hne heq).elim⟩

end Reverse

namespace ReverseHistory

/-- Distance identities at every pair of successive forests in the history. -/
def DistanceChain (H : History) (k : ℕ) (u v : ℕ ⊕ ℕ) : Prop :=
  ∀ j, j < k → Reverse.DistanceStep (stage H (j + 1)) (stage H j) u v

theorem lawAfter_distanceChain (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) (u v : ℕ ⊕ ℕ) :
    ∀ᵐ H ∂lawAfter x n k, DistanceChain H k u v := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ j hj => (Nat.not_lt_zero j hj).elim
  | succ k ih =>
    have hkn : k < n := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _H, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih (by omega), lawAfter_current_valid x n k hn (by omega)] with H hH hvalid
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
        filter_upwards [Reverse.transitionLaw_distanceStep x (n - (k + 1)) H.current
          hvalid.acyclic u v] with F hF
        intro j hj
        cases j with
        | zero =>
          have hcur : (push H F).current = F := rfl
          simpa only [stage_push_succ, stage_zero, hcur] using hF
        | succ j => simpa only [stage_push_succ] using hH j (by omega)
      _ = 1 := by simp

/-- After the tracked vertices have coalesced, every subsequent reverse step
preserves their distance. -/
theorem dist_stage_zero_eq_of_coalesced {x : SignSequence} {n : ℕ} {H : History}
    {u v : ℕ ⊕ ℕ} (hvalid : ∀ j, j ≤ n → Reverse.ValidAt x n j (stage H j))
    (hcoal : CoalescenceChain H n u v) (hdist : DistanceChain H n u v)
    {i : ℕ} (hin : i ≤ n) (hi : Coalesced H u v i) :
    (stage H 0).graph.dist u v = (stage H i).graph.dist u v := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hprev := coalesced_mono hvalid hcoal (Nat.le_succ i) hin hi
    exact (ih (by omega) hprev).trans ((hdist i (by omega)).1 hi.1 hi.2.1 hi.2.2)

/-- Every actual height increment before birth is at most one. -/
theorem fullLaw_phaseIncrement_le_one (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    (i : ℕ) (hi : i < birthTime n v) :
    ∀ᵐ H ∂fullLaw x n, phaseIncrement v i H ≤ 1 := by
  apply ((phaseIncrement_hasLaw x n hn hv i hi).ae_iff
    (p := fun k : ℕ => k ≤ 1) (measurable_of_countable _)).mpr
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  exact bernoulliMeasure_apply_of_mem_of_mem _ (by measurability) (by simp) (by simp)

/-- At most `b` edges can be added to the height between phase `b` and phase zero. -/
theorem fullLaw_depth_zero_le_depth_phase_add (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    (b : ℕ) (hb : b ≤ birthTime n v) :
    ∀ᵐ H ∂fullLaw x n, (stage H 0).depth v ≤ (stage H b).depth v + b := by
  have hinc : ∀ᵐ H ∂fullLaw x n, ∀ i < birthTime n v, phaseIncrement v i H ≤ 1 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun hi => fullLaw_phaseIncrement_le_one x n hn hv i hi
  filter_upwards [fullLaw_depth_difference_eq_sum_phaseIncrements x n hn hv (Nat.zero_le b) hb,
    hinc] with H heq hH
  have hsum : (∑ i ∈ Finset.Ico 0 b, phaseIncrement v i H) ≤ b := by
    calc
      _ ≤ ∑ _i ∈ Finset.Ico 0 b, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hH i ((Finset.mem_Ico.mp hi).2.trans_le hb)
      _ = b := by simp
  omega

/-- A tracked terminal vertex has depth at most its own birth phase. -/
theorem fullLaw_depth_le_birth (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, (stage H 0).depth v ≤ birthTime n v := by
  filter_upwards [fullLaw_depth_zero_le_depth_phase_add x n hn hv (birthTime n v) le_rfl,
    fullLaw_birth_depth_zero x n hn hv] with H hbound hzero
  rw [current_previous_iterate_eq_stage] at hzero
  simpa only [hzero, Nat.zero_add] using hbound

/-- Distinct terminal labels have already separated at their earliest birth
phase, so their first common component occurs strictly below that phase. -/
theorem fullLaw_coalescenceTime_lt_min_birth (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v) :
    ∀ᵐ H ∂fullLaw x n,
      coalescenceTime n H u v < min (birthTime n u) (birthTime n v) := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  apply (ENNReal.toReal_eq_one_iff _).mp
  have hh := fullLaw_coalescenceTime_lt_product x n hn hu hv huv
    (i := min (birthTime n u) (birthTime n v)) le_rfl
  simpa only [Measure.real, Finset.Ioc_self, Finset.prod_empty] using hh

/-- The actual distance defect is at most twice the actual coalescence phase.
The diagonal case is included and uses its distinct birth-time law. -/
theorem fullLaw_dist_depth_bounds (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n,
      (stage H 0).graph.dist u v ≤ (stage H 0).depth u + (stage H 0).depth v ∧
      (stage H 0).depth u + (stage H 0).depth v ≤
        (stage H 0).graph.dist u v + 2 * coalescenceTime n H u v := by
  by_cases huv : u = v
  · subst v
    filter_upwards [fullLaw_depth_le_birth x n hn hu,
      fullLaw_coalescenceTime_self x n hn hu] with H hdepth hC
    rw [SimpleGraph.dist_self, hC]
    omega
  have hboundU : ∀ᵐ H ∂fullLaw x n, ∀ b, b ≤ birthTime n u →
      (stage H 0).depth u ≤ (stage H b).depth u + b :=
    ae_all_iff.mpr fun b => ae_all_iff.mpr fun hb =>
      fullLaw_depth_zero_le_depth_phase_add x n hn hu b hb
  have hboundV : ∀ᵐ H ∂fullLaw x n, ∀ b, b ≤ birthTime n v →
      (stage H 0).depth v ≤ (stage H b).depth v + b :=
    ae_all_iff.mpr fun b => ae_all_iff.mpr fun hb =>
      fullLaw_depth_zero_le_depth_phase_add x n hn hv b hb
  filter_upwards [fullLaw_stages_valid x n hn,
    lawAfter_coalescenceChain x n n le_rfl u v,
    lawAfter_distanceChain x n n hn le_rfl u v,
    fullLaw_coalesced_zero x n hn hu hv,
    fullLaw_coalescenceTime_lt_min_birth x n hn hu hv huv,
    hboundU, hboundV] with H hvalid hcoal hdist hzero hC huBound hvBound
  let c := coalescenceTime n H u v
  have hcmin : c < min (birthTime n u) (birthTime n v) := hC
  have hcnu : c < birthTime n u := hcmin.trans_le (min_le_left _ _)
  have hcnv : c < birthTime n v := hcmin.trans_le (min_le_right _ _)
  have hcn : c < n := hcnu.trans_le (Reverse.birthTime_le_of_mem hu)
  have hsame : Coalesced H u v c := (coalescenceTime_spec hvalid hzero hu hv).1
  have hbefore : (stage H (c + 1)).root u ≠ (stage H (c + 1)).root v :=
    (coalescenceTime_lt_iff hvalid hcoal hzero hu hv (by omega : c + 1 ≤
      min (birthTime n u) (birthTime n v))).mp (by change c < c + 1; omega)
  have huOld : u ∈ (stage H (c + 1)).vertices := by
    rw [(hvalid (c + 1) (by omega)).vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) hu).mpr (by omega)
  have hvOld : v ∈ (stage H (c + 1)).vertices := by
    rw [(hvalid (c + 1) (by omega)).vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) hv).mpr (by omega)
  have hfirst : (stage H c).graph.dist u v = (stage H c).depth u + (stage H c).depth v :=
    (hdist c hcn).2 huOld hvOld hbefore hsame.2.2
  have hpres := dist_stage_zero_eq_of_coalesced hvalid hcoal hdist hcn.le hsame
  have hupper := (stage H 0).dist_le_depth_add_depth hzero.1 hzero.2.1 hzero.2.2
  have huGrow := huBound c hcnu.le
  have hvGrow := hvBound c hcnv.le
  refine ⟨hupper, ?_⟩
  change (stage H 0).depth u + (stage H 0).depth v ≤ (stage H 0).graph.dist u v + 2 * c
  omega

/-- Real-valued form of the distance-defect bound, suitable for normalization
and probability estimates. -/
theorem fullLaw_distance_defect_bounds (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n,
      0 ≤ ((stage H 0).depth u : ℝ) + (stage H 0).depth v - (stage H 0).graph.dist u v ∧
      ((stage H 0).depth u : ℝ) + (stage H 0).depth v - (stage H 0).graph.dist u v ≤
        2 * (coalescenceTime n H u v : ℝ) := by
  filter_upwards [fullLaw_dist_depth_bounds x n hn hu hv] with H hH
  have hlow : ((stage H 0).graph.dist u v : ℝ) ≤
      ((stage H 0).depth u : ℝ) + (stage H 0).depth v := by exact_mod_cast hH.1
  have hhigh : ((stage H 0).depth u : ℝ) + (stage H 0).depth v ≤
      ((stage H 0).graph.dist u v : ℝ) + 2 * (coalescenceTime n H u v : ℝ) := by
    exact_mod_cast hH.2
  constructor <;> linarith

end ReverseHistory
end Freezing1
