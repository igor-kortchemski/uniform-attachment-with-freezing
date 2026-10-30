module

public import Freezing1.ForwardInfiniteHistory
public import Freezing1.ForwardLifetimeCriterion
public import Freezing1.ForwardScheduleSupport

/-!
# Eventual freezing on the actual infinite trajectory

The finite survival product is first integrated over the genuine earlier
tree. Its vanishing then excludes survival forever for each birth ID. A
countable intersection yields simultaneous eventual freezing of every
vertex that occurs in the trajectory, with its frozen label preserved.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

/-- The exact survival factor after averaging the actual starting tree.
The old vertex may already be frozen or may never have been born. -/
theorem treeLaw_vertex_survival_measure (x : SignSequence) (a k : ℕ)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) {r : ℕ} (hr : r ≤ a) :
    (treeLaw x (a + k)) {s | r ∈ s.active} =
      (treeLaw x a) {s | r ∈ s.active} *
        ∏ i ∈ Finset.Ioc a (a + k), ENNReal.ofReal (vertexSurvivalFactor x i) := by
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast Nat.le_add_right a k : (a : ℕ∞) ≤ (a + k : ℕ)).trans hτ
  rw [treeLaw_add_eq_bind_continuation,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ s, {s : State | r ∈ s.active}.indicator
        (fun _ => ∏ i ∈ Finset.Ioc a (a + k), ENNReal.ofReal (vertexSurvivalFactor x i)) s
        ∂treeLaw x a := by
      apply lintegral_congr_ae
      filter_upwards [treeLaw_phaseData x a haτ] with s hs
      rw [continuationLaw_vertex_survival_measure hs hτ hr]
      by_cases hm : r ∈ s.active <;> simp [hm]
    _ = _ := by rw [lintegral_indicator_const (by trivial), mul_comm]

theorem treeLaw_vertex_survival (x : SignSequence) (a k : ℕ)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) {r : ℕ} (hr : r ≤ a) :
    (treeLaw x (a + k)).real {s | r ∈ s.active} =
      (treeLaw x a).real {s | r ∈ s.active} *
        ∏ i ∈ Finset.Ioc a (a + k), vertexSurvivalFactor x i := by
  change ((treeLaw x (a + k)) {s | r ∈ s.active}).toReal = _
  rw [treeLaw_vertex_survival_measure x a k hτ hr, ENNReal.toReal_mul, ENNReal.toReal_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply ENNReal.toReal_ofReal
  apply vertexSurvivalFactor_nonneg
  have hi' : i - 1 < a + k := by have := Finset.mem_Ioc.mp hi; omega
  exact lt_of_lt_of_le (by exact_mod_cast hi') hτ

/-- Every old ID has vanishing active probability when the printed freezing
series diverges, whether or not that ID occurs in the tree. -/
theorem treeLaw_vertex_survival_tendsto_zero (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x))
    (a : ℕ) {r : ℕ} (hr : r ≤ a) :
    Tendsto (fun k => (treeLaw x (a + k)).real {s | r ∈ s.active}) atTop (𝓝 0) := by
  have hsum : ¬Summable (freezingHazard x) :=
    (not_congr (summable_freezingHazard_iff x hτ)).mpr hdiv
  have hlim := (tendsto_survivalProduct_tail_zero_iff_not_summable
    (freezingHazard_nonneg x hτ) (freezingHazard_lt_one x hτ) a).mpr hsum
  have he : (fun k => (treeLaw x (a + k)).real {s | r ∈ s.active}) =
      (fun k => (treeLaw x a).real {s | r ∈ s.active} *
        ∏ i ∈ Finset.Ico a (a + k), (1 - freezingHazard x i)) := by
    funext k
    rw [treeLaw_vertex_survival x a k (by simp [hτ]) hr, vertexSurvivalFactor_product]
  rw [he]
  simpa only [mul_zero] using hlim.const_mul ((treeLaw x a).real {s | r ∈ s.active})

theorem step_frozenAt_of_frozen {n : ℕ} {s : State} (hs : ValidAt n s)
    {r j p : ℕ} (hr : r ∈ s.vertices) (hf : s.frozenAt r = some j)
    (hp : p ∈ s.active) (sign : Bool) :
    (step s (n + 1) sign p).frozenAt r = some j := by
  have hnew : r ≠ n + 1 := by have := hs.vertices_le r hr; omega
  have hpr : r ≠ p := by
    intro he
    have hn := (hs.active_iff r hr).mp (he.symm ▸ hp)
    rw [hn] at hf
    contradiction
  rw [step, ite_eq_left hp]
  cases sign <;> simp [attach, freeze, hnew, hpr, hf]

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem fullLaw_scheduleSupport (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    ∀ᵐ H ∂fullLaw x, ∀ n, ScheduleSupport x n (H n) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_of_ae_map (μ := fullLaw x) (f := fun H : History => H n)
    (p := ScheduleSupport x n) (measurable_pi_apply n).aemeasurable
  rw [map_eval]
  exact treeLaw_schedule_support x n (by simp [hτ])

/-- The null event is survival at every time after the vertex's possible
birth. No convergence-of-marginals assertion is substituted for this event. -/
theorem fullLaw_exists_not_active (x : SignSequence) (hτ : extinctionTime x = ⊤)
    (hdiv : ¬Summable (printedFreezingReciprocal x)) (r : ℕ) :
    ∀ᵐ H ∂fullLaw x, ∃ k, r ∉ (H (r + k)).active := by
  let E : Set History := {H | ∀ k, r ∈ (H (r + k)).active}
  have hbound : ∀ k, (fullLaw x).real E ≤
      (treeLaw x (r + k)).real {s | r ∈ s.active} := by
    intro k
    have he : (fullLaw x).real {H | r ∈ (H (r + k)).active} =
        (treeLaw x (r + k)).real {s | r ∈ s.active} := by
      rw [← map_eval x (r + k), map_measureReal_apply (measurable_pi_apply _) (by trivial)]
      rfl
    rw [← he]
    exact measureReal_mono (fun H hH => hH k) (measure_ne_top _ _)
  have hz : (fullLaw x).real E = 0 := le_antisymm
    (ge_of_tendsto (treeLaw_vertex_survival_tendsto_zero x hτ hdiv r le_rfl)
      (Eventually.of_forall hbound)) measureReal_nonneg
  have hnull : (fullLaw x) E = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
  apply ae_iff.mpr
  have he : {H : History | ¬∃ k, r ∉ (H (r + k)).active} = E := by
    ext H
    simp only [E, Set.mem_ofPred_eq, not_exists, not_not]
  rw [he]
  exact hnull

theorem LegalOrHeld.vertices_mono {x : SignSequence} {n : ℕ} {s q : State}
    (h : LegalOrHeld x n s q) : s.vertices ⊆ q.vertices := by
  rcases h with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Finset.Subset.refl _
  · rw [step, ite_eq_left hp]
    cases hx : x (n + 1)
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _

theorem LegalOrHeld.frozenAt {x : SignSequence} {n : ℕ} {s q : State}
    (h : LegalOrHeld x n s q) (hs : ValidAt n s)
    {r j : ℕ} (hr : r ∈ s.vertices) (hf : s.frozenAt r = some j) :
    q.frozenAt r = some j := by
  rcases h with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · exact hf
  · exact step_frozenAt_of_frozen hs hr hf hp _

theorem frozenAt_persists {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {a r j : ℕ} (hr : r ∈ (H a).vertices) (hf : (H a).frozenAt r = some j) :
    ∀ n ≥ a, (H n).frozenAt r = some j := by
  have hboth : ∀ n ≥ a, r ∈ (H n).vertices ∧ (H n).frozenAt r = some j := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨hr, hf⟩
    | succ n han ih => exact ⟨(hl n).vertices_mono ih.1, (hl n).frozenAt (hv n) ih.1 ih.2⟩
  exact fun n hn => (hboth n hn).2

/-- Every vertex that ever occurs freezes, simultaneously almost surely.
The time and label may depend on the vertex and the random trajectory. -/
theorem fullLaw_all_vertices_eventually_frozen (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x)) :
    ∀ᵐ H ∂fullLaw x, ∀ r n, r ∈ (H n).vertices →
      ∃ a j, ∀ m ≥ a, (H m).frozenAt r = some j := by
  have hall : ∀ᵐ H ∂fullLaw x, ∀ r, ∃ k, r ∉ (H (r + k)).active :=
    ae_all_iff.mpr (fullLaw_exists_not_active x hτ hdiv)
  filter_upwards [hall, fullLaw_valid x, fullLaw_legalOrHeld x,
    fullLaw_scheduleSupport x hτ] with H hdead hv hl hs
  intro r n hr
  obtain ⟨k, hk⟩ := hdead r
  have hborn := (hs n).vertex_iff r |>.mp hr
  have hmem : r ∈ (H (r + k)).vertices := (hs (r + k)).vertex_iff r |>.mpr (by
    rcases hborn with h0 | ⟨hr1, _, hxr⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hr1, Nat.le_add_right r k, hxr⟩)
  have hne : (H (r + k)).frozenAt r ≠ none := fun he =>
    hk ((hv (r + k)).active_iff r hmem |>.mpr he)
  cases hj : (H (r + k)).frozenAt r with
  | none => exact (hne hj).elim
  | some j => exact ⟨r + k, j, frozenAt_persists hv hl hmem hj⟩

theorem fullLaw_root_eventually_frozen (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x)) :
    ∀ᵐ H ∂fullLaw x, ∃ a j, ∀ m ≥ a, (H m).frozenAt 0 = some j := by
  filter_upwards [fullLaw_all_vertices_eventually_frozen x hτ hdiv, fullLaw_valid x]
    with H hH hv
  exact hH 0 0 (hv 0).root_mem

end ForwardInfiniteHistory
end Freezing1
