module

public import Freezing1.ForwardDegreeLocalCriterion
public import Freezing1.ForwardConditionalAttachments
public import Freezing1.ForwardLocalExtinction

/-!
# A never-frozen vertex has unbounded actual degree almost surely

The deterministic freezing implication is separated from the probabilistic
converse. The latter uses the proved conditional attachment independence and
the second Borel--Cantelli lemma. No converse is asserted for every possible
legal choice sequence.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem all_degrees_stabilize_of_all_eventually_frozen {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hf : ∀ r b, r ∈ (H b).vertices →
      ∃ a j, ∀ n ≥ a, (H n).frozenAt r = some j) :
    ∀ r b, r ∈ (H b).vertices →
      ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r := by
  intro r b hr
  obtain ⟨a, j, ha⟩ := hf r b hr
  let M := max a b
  exact ⟨M, degree_constant_after_freezing hv hl
    (vertices_mono hl (le_max_right _ _) hr) (ha M (le_max_left _ _))⟩

theorem postBirthAttachment_degree_jump {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n))
    (hl : ∀ n, LegalStep x n (H n) (H (n + 1)))
    {r i : ℕ} (hi : H ∈ postBirthAttachment x r i) :
    vertexDegree (H i) r = vertexDegree (H (i - 1)) r + 1 := by
  have hgood : r < i ∧ x i = true := by
    by_contra hbad
    simp [postBirthAttachment, hbad] at hi
  have hp : (H i).parent i = r := by
    simpa [postBirthAttachment, hgood] using hi
  have hi0 : 0 < i := by omega
  have hs : i - 1 + 1 = i := by omega
  obtain ⟨p, hpa, hstep⟩ := hl (i - 1)
  rw [hs] at hstep
  have hpr : p = r := by
    rw [hstep, step, ite_eq_left hpa, hgood.2] at hp
    simpa [attach] using hp
  have hj := vertexDegree_step_old (hv (i - 1)) (r := r) (by omega) hpa (x i)
  rw [hs, ← hstep] at hj
  simpa only [hgood.2, hpr, and_self, ↓reduceIte] using hj

theorem degree_tendsto_atTop_of_infinitely_many_attachments {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n))
    (hl : ∀ n, LegalStep x n (H n) (H (n + 1))) (r : ℕ)
    (hf : ∃ᶠ i in atTop, H ∈ postBirthAttachment x r i) :
    Tendsto (fun n => vertexDegree (H n) r) atTop atTop := by
  have hl' : ∀ n, LegalOrHeld x n (H n) (H (n + 1)) := fun n => Or.inr (hl n)
  have hm := vertexDegree_monotone hl' r
  apply hm.tendsto_atTop_atTop
  intro d
  by_contra hn
  push Not at hn
  have hb : ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r := by
    obtain ⟨a, ha⟩ := neighbors_stabilize_of_degree_bounded hl' r ⟨d, fun n => by
      have := hn n
      omega⟩
    exact ⟨a, fun n hn => congrArg Finset.card (ha n hn)⟩
  obtain ⟨a, ha⟩ := hb
  obtain ⟨i, hia, hi⟩ := frequently_atTop.mp hf (a + 1)
  have hj := postBirthAttachment_degree_jump hv hl hi
  rw [ha i (by omega), ha (i - 1) (by omega)] at hj
  omega

theorem conditional_vertexDegree_tendsto_atTop (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) :
    ∀ᵐ H ∂(fullLaw x)[|survivesForever r r],
      Tendsto (fun n => vertexDegree (H n) r) atTop atTop := by
  have hvalid : ∀ᵐ H ∂(fullLaw x)[|survivesForever r r], ∀ n, ValidAt n (H n) :=
    cond_absolutelyContinuous.ae_le (fullLaw_valid x)
  have hlegal : ∀ᵐ H ∂(fullLaw x)[|survivesForever r r],
      ∀ n, LegalStep x n (H n) (H (n + 1)) := by
    apply cond_absolutelyContinuous.ae_le
    exact (fullLaw_legalSteps x).mono fun H hH n => hH n (by simp [hτ])
  filter_upwards [hvalid, hlegal, conditional_infinitely_many_attachments x hτ r hp]
    with H hv hl hf
  exact degree_tendsto_atTop_of_infinitely_many_attachments hv hl r hf

/-- An unnormalized restriction avoids conditioning on a null event and
states the source conclusion for every birth ID, root included. -/
theorem restrict_survival_vertexDegree_tendsto_atTop (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ) :
    ∀ᵐ H ∂(fullLaw x).restrict (survivesForever r r),
      Tendsto (fun n => vertexDegree (H n) r) atTop atTop := by
  by_cases hp : (fullLaw x) (survivesForever r r) = 0
  · rw [Measure.restrict_eq_zero.mpr hp]
    simp
  · have h := conditional_vertexDegree_tendsto_atTop x hτ r hp
    change ∀ᵐ H ∂((fullLaw x) (survivesForever r r))⁻¹ •
      (fullLaw x).restrict (survivesForever r r), _ at h
    exact (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))).mp h

theorem fullLaw_survival_vertexDegree_tendsto_atTop (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    ∀ᵐ H ∂fullLaw x, ∀ r, H ∈ survivesForever r r →
      Tendsto (fun n => vertexDegree (H n) r) atTop atTop := by
  apply ae_all_iff.mpr
  intro r
  exact (ae_restrict_iff' (measurableSet_survivesForever r r)).mp
    (restrict_survival_vertexDegree_tendsto_atTop x hτ r)

theorem fullLaw_degrees_stabilize_iff_all_eventually_frozen (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    ∀ᵐ H ∂fullLaw x,
      (∀ r b, r ∈ (H b).vertices →
        ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r) ↔
      (∀ r b, r ∈ (H b).vertices →
        ∃ a j, ∀ n ≥ a, (H n).frozenAt r = some j) := by
  filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x, fullLaw_scheduleSupport x hτ,
    fullLaw_survival_vertexDegree_tendsto_atTop x hτ] with H hv hl hs hinf
  constructor
  · intro hd r b hr
    obtain ⟨d, hbound⟩ :=
      (degree_bounded_iff_all_occurring_degrees_stabilize hv hl).mpr hd r
    have hnot : H ∉ survivesForever r r := by
      intro hE
      have hev := (hinf r hE).eventually (eventually_ge_atTop (d + 1))
      obtain ⟨n, hn⟩ := hev.exists
      have := hbound n
      omega
    change ¬∀ k, r ∈ (H (r + k)).active at hnot
    push Not at hnot
    obtain ⟨k, hk⟩ := hnot
    have hborn := (hs b).vertex_iff r |>.mp hr
    have hmem : r ∈ (H (r + k)).vertices :=
      (hs (r + k)).vertex_iff r |>.mpr (by
        rcases hborn with h0 | ⟨hr1, _, hxr⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hr1, Nat.le_add_right r k, hxr⟩)
    have hne : (H (r + k)).frozenAt r ≠ none := fun he =>
      hk (((hv (r + k)).active_iff r hmem).mpr he)
    cases hj : (H (r + k)).frozenAt r with
    | none => exact (hne hj).elim
    | some j => exact ⟨r + k, j, frozenAt_persists hv hl hmem hj⟩
  · exact all_degrees_stabilize_of_all_eventually_frozen hv hl

/-- Source A21/A22 on the same actual infinite probability space. The degree
equivalence is deterministic; the freezing converse is almost sure. -/
theorem fullLaw_local_limit_iff_all_eventually_frozen (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    ∀ᵐ H ∂fullLaw x,
      (∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) ↔
      (∀ r b, r ∈ (H b).vertices →
        ∃ a j, ∀ n ≥ a, (H n).frozenAt r = some j) := by
  filter_upwards [fullLaw_local_limit_iff_all_degrees_stabilize x,
    fullLaw_degrees_stabilize_iff_all_eventually_frozen x hτ] with H hdegree hfreeze
  exact hdegree.trans hfreeze

theorem fullLaw_all_eventually_frozen_of_finite_extinction {x : SignSequence} {a : ℕ}
    (hτ : extinctionTime x = a) :
    ∀ᵐ H ∂fullLaw x, ∀ r b, r ∈ (H b).vertices →
      ∃ c j, ∀ n ≥ c, (H n).frozenAt r = some j := by
  have hactive : ∀ᵐ H ∂fullLaw x, (H a).active = ∅ := by
    apply ae_of_ae_map (μ := fullLaw x) (f := fun H : History => H a)
      (p := fun s => s.active = ∅) (measurable_pi_apply a).aemeasurable
    rw [map_eval]
    exact treeLaw_active_empty_at_extinction hτ
  filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x,
    fullLaw_constant_after_extinction hτ, hactive] with H hv hl hheld hempty
  intro r b hr
  let M := max a b
  have hMa : H M = H a := hheld M (le_max_left _ _)
  have hmem : r ∈ (H a).vertices := by
    rw [← hMa]
    exact vertices_mono hl (le_max_right _ _) hr
  have hne : (H a).frozenAt r ≠ none := by
    intro he
    have ha := ((hv a).active_iff r hmem).mpr he
    simp only [hempty, Finset.notMem_empty] at ha
  cases hj : (H a).frozenAt r with
  | none => exact (hne hj).elim
  | some j => exact ⟨a, j, frozenAt_persists hv hl hmem hj⟩

/-- Absorbed schedules are included explicitly. -/
theorem fullLaw_local_limit_iff_all_eventually_frozen_all_schedules (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x,
      (∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) ↔
      (∀ r b, r ∈ (H b).vertices →
        ∃ a j, ∀ n ≥ a, (H n).frozenAt r = some j) := by
  by_cases hτ : extinctionTime x = ⊤
  · exact fullLaw_local_limit_iff_all_eventually_frozen x hτ
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hτ
    filter_upwards [fullLaw_all_eventually_frozen_of_finite_extinction ha.symm,
      fullLaw_tendsto_localLimit_of_extinction ha.symm] with H hf hc
    exact iff_of_true ⟨_, hc⟩ hf

theorem fullLaw_degrees_stabilize_iff_all_eventually_frozen_all_schedules (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x,
      (∀ r b, r ∈ (H b).vertices →
        ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r) ↔
      (∀ r b, r ∈ (H b).vertices →
        ∃ a j, ∀ n ≥ a, (H n).frozenAt r = some j) := by
  filter_upwards [fullLaw_local_limit_iff_all_degrees_stabilize x,
    fullLaw_local_limit_iff_all_eventually_frozen_all_schedules x] with H hd hf
  exact hd.symm.trans hf

end Freezing1.ForwardInfiniteHistory
