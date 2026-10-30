module

public import Freezing1.ReverseHistory
public import Freezing1.ReverseSeparationLaw
public import Mathlib.Data.Nat.Find

/-!
# Coalescence time on the actual common reverse history

The largest phase at which two present vertices share a component is defined
on the coherent history law. Coalescence persists along its actual transitions;
the marginal product law can therefore be used for this random time.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory
open scoped ENNReal BigOperators Classical

/-- The two labels are present and in the same actual component at phase `i`. -/
def Coalesced (H : History) (u v : ℕ ⊕ ℕ) (i : ℕ) : Prop :=
  u ∈ (stage H i).vertices ∧ v ∈ (stage H i).vertices ∧
    (stage H i).root u = (stage H i).root v

/-- Source coalescence time. The default case of `findGreatest` is excluded
below by showing that terminal labels coalesce at phase zero almost surely. -/
noncomputable def coalescenceTime (n : ℕ) (H : History) (u v : ℕ ⊕ ℕ) : ℕ :=
  Nat.findGreatest (Coalesced H u v) n

def CoalescenceChain (H : History) (k : ℕ) (u v : ℕ ⊕ ℕ) : Prop :=
  ∀ j, j < k → Coalesced H u v (j + 1) →
    (stage H j).root u = (stage H j).root v

theorem transitionLaw_root_eq_ae (x : SignSequence) (i : ℕ) (F : Reverse.Forest)
    (u v : ℕ ⊕ ℕ) :
    ∀ᵐ F' ∂Reverse.transitionLaw x i F,
      u ∈ F.vertices → v ∈ F.vertices → F.root u = F.root v → F'.root u = F'.root v := by
  by_cases hu : u ∈ F.vertices
  · by_cases hv : v ∈ F.vertices
    · by_cases he : F.root u = F.root v
      · have hprob : (Reverse.transitionLaw x i F) {F' | F'.root u = F'.root v} = 1 :=
          (ENNReal.toReal_eq_one_iff _).mp
            (Reverse.transitionLaw_coalescence_of_eq x i F hu hv he)
        have hae := (ae_iff_prob_eq_one measurable_from_top).mpr hprob
        exact hae.mono fun F' h _ _ _ => h
      · exact Filter.Eventually.of_forall fun _ _ _ h => (he h).elim
    · exact Filter.Eventually.of_forall fun _ _ h => (hv h).elim
  · exact Filter.Eventually.of_forall fun _ h => (hu h).elim

theorem lawAfter_coalescenceChain (x : SignSequence) (n k : ℕ) (hk : k ≤ n)
    (u v : ℕ ⊕ ℕ) : ∀ᵐ H ∂lawAfter x n k, CoalescenceChain H k u v := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ j hj => (Nat.not_lt_zero j hj).elim
  | succ k ih =>
    have hkn : k < n := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _H, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih (by omega)] with H hH
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
        filter_upwards [transitionLaw_root_eq_ae x (n - (k + 1)) H.current u v] with F hF
        intro j hj he
        cases j with
        | zero =>
          have hh : u ∈ H.current.vertices ∧ v ∈ H.current.vertices ∧
              H.current.root u = H.current.root v := by
            simpa only [Coalesced, stage_push_succ, stage_zero] using he
          exact hF hh.1 hh.2.1 hh.2.2
        | succ j =>
          have hh : Coalesced H u v (j + 1) := by
            simpa only [Coalesced, stage_push_succ] using he
          simpa only [stage_push_succ] using hH j (by omega) hh
      _ = 1 := by simp

theorem fullLaw_stages_valid (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂fullLaw x n, ∀ i, i ≤ n → Reverse.ValidAt x n i (stage H i) := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i ≤ n
  · have h : ∀ᵐ H ∂fullLaw x n, Reverse.ValidAt x n i (stage H i) := by
      apply ae_of_ae_map (f := fun H => stage H i) measurable_from_top.aemeasurable
      rw [map_fullLaw_phase x n i hi]
      simpa only [Nat.sub_sub_self hi] using
        Reverse.lawAfter_valid x n (n - i) hn (Nat.sub_le n i)
    exact h.mono fun H hH _ => hH
  · exact Filter.Eventually.of_forall fun _ h => (hi h).elim

theorem fullLaw_coalesced_zero (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, Coalesced H u v 0 := by
  have h : ∀ᵐ H ∂fullLaw x n,
      H.current.vertices = vertexLabels x n ∧ H.current.roots.card = 1 := by
    apply ae_of_ae_map (f := History.current)
      (p := fun F : Reverse.Forest => F.vertices = vertexLabels x n ∧ F.roots.card = 1)
      measurable_from_top.aemeasurable
    rw [fullLaw, map_lawAfter_current]
    exact Reverse.treeLaw_vertices_and_root x n hn
  filter_upwards [h] with H hH
  have huH : u ∈ H.current.vertices := hH.1.symm ▸ hu
  have hvH : v ∈ H.current.vertices := hH.1.symm ▸ hv
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hH.2
  have hur := H.current.root_mem_roots huH
  have hvr := H.current.root_mem_roots hvH
  rw [hr, Finset.mem_singleton] at hur hvr
  exact ⟨huH, hvH, hur.trans hvr.symm⟩

theorem coalesced_mono {x : SignSequence} {n : ℕ} {H : History} {u v : ℕ ⊕ ℕ}
    (hvalid : ∀ i, i ≤ n → Reverse.ValidAt x n i (stage H i))
    (hchain : CoalescenceChain H n u v) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) (hj : Coalesced H u v j) : Coalesced H u v i := by
  induction j generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact hj
  | succ j ih =>
    by_cases hi : i = j + 1
    · simpa only [hi] using hj
    · have huv : (stage H j).root u = (stage H j).root v := hchain j (by omega) hj
      have huj : u ∈ (stage H j).vertices := by
        rw [(hvalid j (by omega)).vertices_eq]
        apply Reverse.phaseLabels_mono x n (Nat.le_succ j)
        rw [← (hvalid (j + 1) hjn).vertices_eq]
        exact hj.1
      have hvj : v ∈ (stage H j).vertices := by
        rw [(hvalid j (by omega)).vertices_eq]
        apply Reverse.phaseLabels_mono x n (Nat.le_succ j)
        rw [← (hvalid (j + 1) hjn).vertices_eq]
        exact hj.2.1
      exact ih (by omega) (by omega) ⟨huj, hvj, huv⟩

/-- The source maximum really exists, and is within both birth phases. -/
theorem coalescenceTime_spec {x : SignSequence} {n : ℕ} {H : History} {u v : ℕ ⊕ ℕ}
    (hvalid : ∀ i, i ≤ n → Reverse.ValidAt x n i (stage H i))
    (hzero : Coalesced H u v 0) (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    Coalesced H u v (coalescenceTime n H u v) ∧
      coalescenceTime n H u v ≤ min (birthTime n u) (birthTime n v) := by
  have hspec : Coalesced H u v (coalescenceTime n H u v) :=
    Nat.findGreatest_spec (Nat.zero_le n) hzero
  have hn' : coalescenceTime n H u v ≤ n := Nat.findGreatest_le _
  have hverts := (hvalid _ hn').vertices_eq
  have hu' : u ∈ Reverse.phaseLabels x n (coalescenceTime n H u v) := hverts ▸ hspec.1
  have hv' : v ∈ Reverse.phaseLabels x n (coalescenceTime n H u v) := hverts ▸ hspec.2.1
  exact ⟨hspec, le_min ((Reverse.mem_phaseLabels_iff_birthTime hn' hu).mp hu')
    ((Reverse.mem_phaseLabels_iff_birthTime hn' hv).mp hv')⟩

theorem coalescenceTime_lt_iff {x : SignSequence} {n : ℕ} {H : History} {u v : ℕ ⊕ ℕ}
    (hvalid : ∀ i, i ≤ n → Reverse.ValidAt x n i (stage H i))
    (hchain : CoalescenceChain H n u v) (hzero : Coalesced H u v 0)
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n)
    {i : ℕ} (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    coalescenceTime n H u v < i ↔ (stage H i).root u ≠ (stage H i).root v := by
  have hin : i ≤ n := hi.trans ((min_le_left _ _).trans (Reverse.birthTime_le_of_mem hu))
  have huI : u ∈ (stage H i).vertices := by
    rw [(hvalid i hin).vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime hin hu).mpr (hi.trans (min_le_left _ _))
  have hvI : v ∈ (stage H i).vertices := by
    rw [(hvalid i hin).vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime hin hv).mpr (hi.trans (min_le_right _ _))
  constructor
  · intro hc he
    have hle : i ≤ coalescenceTime n H u v := Nat.le_findGreatest hin ⟨huI, hvI, he⟩
    omega
  · intro he
    by_contra hc
    have hspec := (coalescenceTime_spec hvalid hzero hu hv).1
    have hmono := coalesced_mono hvalid hchain (Nat.le_of_not_gt hc)
      (Nat.findGreatest_le n) hspec
    exact he hmono.2.2

/-- The actual random-time distribution function equals the previously
derived component-separation marginal. The equality includes phase zero. -/
theorem fullLaw_coalescenceTime_lt (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n)
    {i : ℕ} (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    (fullLaw x n).real {H | coalescenceTime n H u v < i} =
      (Reverse.phaseLaw x n i).real {F | F.root u ≠ F.root v} := by
  have hin : i ≤ n := hi.trans ((min_le_left _ _).trans (Reverse.birthTime_le_of_mem hu))
  calc
    _ = (fullLaw x n).real {H | (stage H i).root u ≠ (stage H i).root v} := by
      apply measureReal_congr
      filter_upwards [fullLaw_stages_valid x n hn,
        lawAfter_coalescenceChain x n n le_rfl u v,
        fullLaw_coalesced_zero x n hn hu hv] with H hvalid hchain hzero
      exact propext (coalescenceTime_lt_iff hvalid hchain hzero hu hv hi)
    _ = _ := by
      have hm : (fullLaw x n).map (fun H => stage H i) = Reverse.phaseLaw x n i :=
        map_fullLaw_phase x n i hin
      rw [← hm]
      unfold Measure.real
      rw [Measure.map_apply measurable_from_top (by trivial)]
      rfl

/-- Exact product for the random coalescence time, on one common probability
space, for distinct terminal vertices. -/
theorem fullLaw_coalescenceTime_lt_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {i : ℕ} (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    (fullLaw x n).real {H | coalescenceTime n H u v < i} =
      ∏ t ∈ Finset.Ioc i (min (birthTime n u) (birthTime n v)),
        Reverse.separationFactor x t := by
  rw [fullLaw_coalescenceTime_lt x n hn hu hv hi]
  exact Reverse.phaseLaw_separation_birth_product x n hn hu hv huv hi

/-- Corrected Lemma `loi du temps de coalescence`: distinct vertices are
required. The hazard and survival factors come from the actual history law. -/
theorem fullLaw_coalescenceTime_eq (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {i : ℕ} (hi : i < min (birthTime n u) (birthTime n v)) (hx : x (i + 1) = true) :
    (fullLaw x n).real {H | coalescenceTime n H u v = i} =
      (1 / ((activeCount x (i + 1)).toNat.choose 2 : ℝ)) *
        ∏ t ∈ (Finset.Ioc (i + 1) (min (birthTime n u) (birthTime n v))).filter
          (fun t => x t = true), (1 - 1 / ((activeCount x t).toNat.choose 2 : ℝ)) := by
  have he : {H : History | coalescenceTime n H u v = i} =
      {H | coalescenceTime n H u v < i + 1} \ {H | coalescenceTime n H u v < i} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    omega
  have hsub : {H : History | coalescenceTime n H u v < i} ⊆
      {H | coalescenceTime n H u v < i + 1} := fun H h => Nat.lt_succ_of_lt h
  rw [he, measureReal_sdiff hsub (by trivial),
    fullLaw_coalescenceTime_lt x n hn hu hv (by omega),
    fullLaw_coalescenceTime_lt x n hn hu hv hi.le,
    Reverse.phaseLaw_separation_drop x n hn hu hv huv hi hx]
  rw [Finset.prod_filter]
  rfl

/-- The omitted diagonal case has a different law: a vertex coalesces with
itself exactly at its own birth phase. -/
theorem fullLaw_coalescenceTime_self (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, coalescenceTime n H v v = birthTime n v := by
  filter_upwards [fullLaw_stages_valid x n hn, fullLaw_coalesced_zero x n hn hv hv]
    with H hvalid hzero
  apply le_antisymm
  · simpa only [min_self] using (coalescenceTime_spec hvalid hzero hv hv).2
  · have hbn := Reverse.birthTime_le_of_mem hv
    have hvb : v ∈ (stage H (birthTime n v)).vertices := by
      rw [(hvalid _ hbn).vertices_eq]
      exact (Reverse.mem_phaseLabels_iff_birthTime hbn hv).mpr le_rfl
    exact Nat.le_findGreatest hbn ⟨hvb, hvb, rfl⟩

end Freezing1.ReverseHistory
