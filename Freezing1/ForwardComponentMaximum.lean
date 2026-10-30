module

public import Freezing1.ForwardComponentContinuation
public import Freezing1.ForwardCutForest

/-!
# A union bound for actual cut-component populations

The maximum counts the distinguished star root even if it later froze, as in
the source's stated convention. It is bounded using the actual component urn
and a union over birth IDs at most the cut time. No independence between
components is needed, and nonexistent roots contribute a zero urn population.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical ENNReal

namespace SignedUrn

theorem continuationLaw_zero (Z : ℕ → ℤ) (a k : ℕ) :
    continuationLaw Z a k 0 = Measure.dirac 0 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [continuationLaw, transitionLaw, parameter_zero,
      ProbabilityTheory.bernoulliMeasure_zero]
    rw [Measure.dirac_bind (measurable_of_countable _)]
    exact ih (a + 1)

end SignedUrn

namespace Forward

/-- The source maximum, with every distinguished root counted as active.
The time `b` is supplied by the tree state sampled at that time. -/
noncomputable def componentMaximum (s : State) (a : ℕ) : ℕ :=
  (cutRoots s a).sup (componentPopulationWithRoot s a)

theorem componentPopulation_at_cut_of_not_mem {a : ℕ} {s : State}
    (hs : ValidAt a s) {r : ℕ} (hr : r ∉ s.active) :
    componentPopulation s a r = 0 := by
  have he : componentActive s a r = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hva, he⟩ := Finset.mem_filter.mp hv
    rw [cutAncestor_of_le s a v (hs.vertices_le v (hs.active_subset hva))] at he
    exact hr (he ▸ hva)
  simp only [componentPopulation, he, Finset.card_empty, Nat.cast_zero]

/-- Each fixed birth ID has a tail bounded by the one-ball urn. If it was
not active at the cut, its population is identically zero. -/
theorem treeLaw_componentPopulation_tail_le (x : SignSequence) (a k r : ℕ)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) {q : ℝ} (hq : 0 ≤ q) :
    (treeLaw x (a + k)).real {t | q < (componentPopulation t a r : ℝ)} ≤
      (SignedUrn.continuationLaw (activeCount x) a k 1).real {u | q < (u : ℝ)} := by
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast (show a ≤ a + k by omega)) hτ
  have hle : (treeLaw x (a + k)) {t | q < (componentPopulation t a r : ℝ)} ≤
      (SignedUrn.continuationLaw (activeCount x) a k 1) {u | q < (u : ℝ)} := by
    rw [treeLaw_add_eq_bind_continuation, Measure.bind_apply (by trivial)
      measurable_from_top.aemeasurable]
    calc
      _ ≤ ∫⁻ _s, (SignedUrn.continuationLaw (activeCount x) a k 1)
          {u | q < (u : ℝ)} ∂treeLaw x a := by
        apply lintegral_mono_ae
        filter_upwards [treeLaw_phaseData x a haτ] with s hs
        by_cases hr : r ∈ s.active
        · have he := continuationLaw_componentPopulation_of_root hs hτ hr
          have hm := congrArg (fun μ : Measure ℤ => μ {u | q < (u : ℝ)}) he
          rw [Measure.map_apply (by fun_prop) (by measurability)] at hm
          exact hm.le
        · have he := continuationLaw_componentPopulation hs le_rfl hτ r
          rw [componentPopulation_at_cut_of_not_mem hs.valid hr,
            SignedUrn.continuationLaw_zero] at he
          have hm := congrArg (fun μ : Measure ℤ => μ {u | q < (u : ℝ)}) he
          rw [Measure.map_apply (by fun_prop) (by measurability)] at hm
          have hz : (Measure.dirac (0 : ℤ)) {u | q < (u : ℝ)} = 0 := by simp [hq.not_gt]
          rw [hz] at hm
          exact hm.le.trans bot_le
      _ = _ := by simp
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- Exceeding the source maximum forces some true active population to
exceed the threshold minus the possible extra star root. -/
theorem componentMaximum_event_subset (a : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    {s : State | q + 1 < (componentMaximum s a : ℝ)} ⊆
      ⋃ r ∈ Finset.range (a + 1), {s | q < (componentPopulation s a r : ℝ)} := by
  intro s hs
  change q + 1 < (componentMaximum s a : ℝ) at hs
  have hne : (cutRoots s a).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [componentMaximum, he, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero] at hs
    linarith
  obtain ⟨r, hr, he⟩ := Finset.exists_mem_eq_sup (cutRoots s a) hne
    (componentPopulationWithRoot s a)
  have hroot : r ∈ Finset.range (a + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_cutRoots s a r).mp hr).2)
  have hp : (componentPopulationWithRoot s a r : ℝ) ≤ (componentPopulation s a r : ℝ) + 1 := by
    exact_mod_cast componentPopulationWithRoot_le s a r
  change q + 1 < (((cutRoots s a).sup (componentPopulationWithRoot s a) : ℕ) : ℝ) at hs
  rw [he] at hs
  exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hroot, by dsimp; linarith⟩⟩

/-- A finite endpoint urn tail controls the source's genuine component maximum. -/
theorem treeLaw_componentMaximum_tail_le (x : SignSequence) (a k : ℕ)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) {q : ℝ} (hq : 0 ≤ q) :
    (treeLaw x (a + k)).real {s | q + 1 < (componentMaximum s a : ℝ)} ≤
      ((a : ℝ) + 1) *
        (SignedUrn.continuationLaw (activeCount x) a k 1).real {u | q < (u : ℝ)} := by
  calc
    _ ≤ (treeLaw x (a + k)).real
        (⋃ r ∈ Finset.range (a + 1), {s | q < (componentPopulation s a r : ℝ)}) :=
      measureReal_mono (componentMaximum_event_subset a hq) (measure_ne_top _ _)
    _ ≤ ∑ r ∈ Finset.range (a + 1), (treeLaw x (a + k)).real
        {s | q < (componentPopulation s a r : ℝ)} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Finset.range (a + 1),
        (SignedUrn.continuationLaw (activeCount x) a k 1).real {u | q < (u : ℝ)} := by
      exact Finset.sum_le_sum (fun r _ => treeLaw_componentPopulation_tail_le x a k r hτ hq)
    _ = _ := by simp

end Forward
end Freezing1
