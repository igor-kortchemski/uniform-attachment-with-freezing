module

public import Freezing1.ForwardAttachmentPatterns
public import Freezing1.AttachmentReciprocalSeries
public import Mathlib.Probability.BorelCantelli

/-!
# Genuine conditional independence and infinitely many attachments

The conditioning event is the actual infinite-history event that the fixed
birth ID remains active forever. Independence is a conclusion of the finite
pattern theorem for the original kernels. The second Borel--Cantelli lemma
then applies with the true pre-step active populations. Times at or before
the observed vertex's birth have the empty attachment event.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

def postBirthAttachment (x : SignSequence) (r i : ℕ) : Set History :=
  if r < i ∧ x i = true then {H | (H i).parent i = r} else ∅

theorem measurableSet_postBirthAttachment (x : SignSequence) (r i : ℕ) :
    MeasurableSet (postBirthAttachment x r i) := by
  unfold postBirthAttachment
  split_ifs
  · exact measurableSet_setOfPred.mpr
      ((measurable_from_top : Measurable (fun s : State => s.parent i = r)).comp
        (measurable_pi_apply i))
  · exact MeasurableSet.empty

theorem conditional_attachmentPattern (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) {F : Finset ℕ}
    (hF : ∀ i ∈ F, r < i ∧ x i = true) (ε : ℕ → Bool) :
    (fullLaw x)[|survivesForever r r] (attachmentPatternEvent r F ε) =
      ∏ i ∈ F, ENNReal.ofReal (attachmentPatternFactor x F ε i) := by
  rw [cond_apply' (measurableSet_attachmentPatternEvent r F ε),
    fullLaw_survival_attachmentPattern x hτ r hF ε, ← mul_assoc,
    ENNReal.inv_mul_cancel hp (measure_ne_top _ _), one_mul]

theorem conditional_postBirthAttachment_probability (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) (i : ℕ) :
    (fullLaw x)[|survivesForever r r] (postBirthAttachment x r i) =
      if r < i ∧ x i = true then ENNReal.ofReal (1 / (activeCount x (i - 1) : ℝ))
      else 0 := by
  by_cases hi : r < i ∧ x i = true
  · have hF : ∀ j ∈ ({i} : Finset ℕ), r < j ∧ x j = true := by simpa using hi
    have he : attachmentPatternEvent r {i} (fun _ => true) = postBirthAttachment x r i := by
      ext H
      simp [attachmentPatternEvent, postBirthAttachment, hi]
    rw [← he, conditional_attachmentPattern x hτ r hp hF]
    simp [attachmentPatternFactor, hi]
  · simp [postBirthAttachment, hi]

theorem conditional_postBirthAttachment_iIndepSet (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) :
    iIndepSet (postBirthAttachment x r) ((fullLaw x)[|survivesForever r r]) := by
  apply (iIndepSet_iff_meas_biInter (measurableSet_postBirthAttachment x r)).mpr
  intro F
  by_cases hF : ∀ i ∈ F, r < i ∧ x i = true
  · have he : (⋂ i ∈ F, postBirthAttachment x r i) =
        attachmentPatternEvent r F (fun _ => true) := by
      ext H
      simp only [Set.mem_iInter, attachmentPatternEvent, Set.mem_ofPred_eq,
        iff_true]
      exact ⟨fun h i hi => by simpa [postBirthAttachment, hF i hi] using h i hi,
        fun h i hi => by simpa [postBirthAttachment, hF i hi] using h i hi⟩
    rw [he, conditional_attachmentPattern x hτ r hp hF]
    apply Finset.prod_congr rfl
    intro i hi
    simp [conditional_postBirthAttachment_probability x hτ r hp i,
      attachmentPatternFactor, hi, hF i hi]
  · push Not at hF
    obtain ⟨i, hi, hbad⟩ := hF
    have hbad' : ¬(r < i ∧ x i = true) := by tauto
    have he : (⋂ j ∈ F, postBirthAttachment x r j) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro H hH
      have hh := Set.mem_iInter.mp (Set.mem_iInter.mp hH i) hi
      simp [postBirthAttachment, hbad'] at hh
    rw [he, measure_empty]
    symm
    apply Finset.prod_eq_zero hi
    simp [conditional_postBirthAttachment_probability x hτ r hp i, hbad']

theorem conditional_postBirthAttachment_tsum_eq_top (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) :
    (∑' i, (fullLaw x)[|survivesForever r r] (postBirthAttachment x r i)) = ⊤ := by
  by_contra hn
  have hs := ENNReal.summable_toReal hn
  have ht := hs.comp_injective (show Function.Injective (fun i : ℕ => i + r + 1) by
    intro i j he; dsimp only at he; omega)
  have he : (fun i : ℕ => ((fullLaw x)[|survivesForever r r]
        (postBirthAttachment x r (i + r + 1))).toReal) =
      fun i => attachmentHazard x (i + r) := by
    funext i
    rw [conditional_postBirthAttachment_probability x hτ r hp]
    have hir : r < i + r + 1 := by omega
    cases hx : x (i + r + 1)
    · simp [hx, attachmentHazard]
    · have hnonneg := attachmentHazard_nonneg x hτ (i + r)
      simp only [attachmentHazard, hx, ↓reduceIte] at hnonneg ⊢
      simp only [hir, true_and, ↓reduceIte, Nat.add_sub_cancel]
      exact ENNReal.toReal_ofReal hnonneg
  change Summable (fun i : ℕ => ((fullLaw x)[|survivesForever r r]
    (postBirthAttachment x r (i + r + 1))).toReal) at ht
  rw [he] at ht
  exact not_summable_attachmentHazard x hτ ((summable_nat_add_iff r).mp ht)

/-- The paper's conditional Borel--Cantelli conclusion, on the actual common
history space. The source's finite-horizon independence assertion has been
proved rather than postulated. -/
theorem conditional_infinitely_many_attachments (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ)
    (hp : (fullLaw x) (survivesForever r r) ≠ 0) :
    ∀ᵐ H ∂(fullLaw x)[|survivesForever r r],
      ∃ᶠ i in atTop, H ∈ postBirthAttachment x r i := by
  have h := measure_limsup_eq_one (measurableSet_postBirthAttachment x r)
    (conditional_postBirthAttachment_iIndepSet x hτ r hp)
    (conditional_postBirthAttachment_tsum_eq_top x hτ r hp)
  have : IsProbabilityMeasure ((fullLaw x)[|survivesForever r r]) :=
    cond_isProbabilityMeasure hp
  have hm : MeasurableSet (limsup (postBirthAttachment x r) atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun _ => measurableSet_postBirthAttachment x r _
  have hae := (ae_iff_prob_eq_one (measurableSet_setOfPred.mp hm)).mpr h
  exact hae.mono fun _ hH => mem_limsup_iff_frequently_mem.mp hH

end Freezing1.ForwardInfiniteHistory
