module

public import Freezing1.ForwardLaw
public import Freezing1.SignedUrn

/-!
# Active populations descended from a time-cut root

The ancestor recursion follows actual parent pointers until reaching a vertex
born at or before the cut. Its fuel is the verified tree height. A new child
inherits its parent's cut ancestor, whereas freezing preserves all ancestors.
Consequently uniform active sampling induces the signed Pólya urn kernel for
the active population associated with each fixed cut root.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

def cutAncestorAux (s : State) (a : ℕ) : ℕ → ℕ → ℕ
  | 0, v => v
  | m + 1, v => if v ≤ a then v else cutAncestorAux s a m (s.parent v)

def cutAncestor (s : State) (a v : ℕ) : ℕ :=
  cutAncestorAux s a (s.height v) v

noncomputable def componentActive (s : State) (a r : ℕ) : Finset ℕ :=
  s.active.filter fun v => cutAncestor s a v = r

noncomputable def componentPopulation (s : State) (a r : ℕ) : ℤ :=
  (componentActive s a r).card

theorem cutAncestorAux_of_le (s : State) (a m v : ℕ) (hv : v ≤ a) :
    cutAncestorAux s a m v = v := by cases m <;> simp [cutAncestorAux, hv]

theorem cutAncestor_of_le (s : State) (a v : ℕ) (hv : v ≤ a) :
    cutAncestor s a v = v := cutAncestorAux_of_le s a _ v hv

theorem componentPopulation_nonneg (s : State) (a r : ℕ) :
    0 ≤ componentPopulation s a r := Int.natCast_nonneg _

theorem componentPopulation_le (s : State) (a r : ℕ) :
    componentPopulation s a r ≤ s.active.card := by
  change ((s.active.filter fun v => cutAncestor s a v = r).card : ℤ) ≤ s.active.card
  exact_mod_cast Finset.card_filter_le s.active (fun v => cutAncestor s a v = r)

theorem componentActive_at_cut {a : ℕ} {s : State} (hs : ValidAt a s)
    {r : ℕ} (hr : r ∈ s.active) : componentActive s a r = {r} := by
  ext v
  simp only [componentActive, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, he⟩
    rwa [cutAncestor_of_le s a v (hs.vertices_le v (hs.active_subset hv))] at he
  · intro he
    subst v
    exact ⟨hr, cutAncestor_of_le s a r (hs.vertices_le r (hs.active_subset hr))⟩

theorem componentPopulation_at_cut {a : ℕ} {s : State} (hs : ValidAt a s)
    {r : ℕ} (hr : r ∈ s.active) : componentPopulation s a r = 1 := by
  simp only [componentPopulation, componentActive_at_cut hs hr, Finset.card_singleton,
    Nat.cast_one]

theorem cutAncestorAux_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (a m p : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    cutAncestorAux (attach s (n + 1) p) a m v = cutAncestorAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    have hne : v ≠ n + 1 := by have := hs.vertices_le v hv; omega
    simp only [cutAncestorAux, attach, Function.update_of_ne hne]
    split_ifs with h
    · rfl
    · exact ih (hs.parent_mem v hv)

theorem cutAncestor_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (a p : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    cutAncestor (attach s (n + 1) p) a v = cutAncestor s a v := by
  have hne : v ≠ n + 1 := by have := hs.vertices_le v hv; omega
  unfold cutAncestor
  simp only [attach, Function.update_of_ne hne]
  exact cutAncestorAux_attach_old hs a _ p hv

theorem cutAncestor_attach_new {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) :
    cutAncestor (attach s (n + 1) p) a (n + 1) = cutAncestor s a p := by
  have hnot : ¬n + 1 ≤ a := by omega
  unfold cutAncestor
  simp only [attach, Function.update_self, cutAncestorAux, ite_eq_right hnot]
  exact cutAncestorAux_attach_old hs a _ p (hs.active_subset hp)

theorem cutAncestorAux_freeze (s : State) (t p a m v : ℕ) :
    cutAncestorAux (freeze s t p) a m v = cutAncestorAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    change (if v ≤ a then v else cutAncestorAux (freeze s t p) a m (s.parent v)) = _
    simp only [cutAncestorAux, ih]

theorem cutAncestor_freeze (s : State) (t p a v : ℕ) :
    cutAncestor (freeze s t p) a v = cutAncestor s a v :=
  cutAncestorAux_freeze s t p a _ v

theorem componentActive_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) (r : ℕ) :
    componentActive (attach s (n + 1) p) a r =
      if cutAncestor s a p = r then insert (n + 1) (componentActive s a r)
      else componentActive s a r := by
  have hfilter : s.active.filter (fun v => cutAncestor (attach s (n + 1) p) a v = r) =
      componentActive s a r := by
    apply Finset.filter_congr
    intro v hv
    rw [cutAncestor_attach_old hs a p (hs.active_subset hv)]
  change (insert (n + 1) s.active).filter
    (fun v => cutAncestor (attach s (n + 1) p) a v = r) = _
  rw [Finset.filter_insert, hfilter, cutAncestor_attach_new hs ha hp]

theorem componentActive_freeze (s : State) (t p a r : ℕ) :
    componentActive (freeze s t p) a r = (componentActive s a r).erase p := by
  change (s.active.erase p).filter (fun v => cutAncestor (freeze s t p) a v = r) = _
  rw [Finset.filter_erase]
  congr 1
  apply Finset.filter_congr
  intro v _
  rw [cutAncestor_freeze]

theorem componentPopulation_step {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) (r : ℕ) (sign : Bool) :
    componentPopulation (step s (n + 1) sign p) a r =
      componentPopulation s a r +
        if cutAncestor s a p = r then (if sign then 1 else -1) else 0 := by
  have hnot : n + 1 ∉ componentActive s a r := by
    intro hm
    have hv := hs.vertices_le _ (hs.active_subset (Finset.mem_filter.mp hm).1)
    omega
  rw [step, ite_eq_left hp]
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte, componentPopulation, componentActive_freeze]
    by_cases hm : cutAncestor s a p = r
    · have hpm : p ∈ componentActive s a r := Finset.mem_filter.mpr ⟨hp, hm⟩
      rw [Finset.card_erase_of_mem hpm, Nat.cast_sub (Finset.card_pos.mpr ⟨p, hpm⟩)]
      simp only [hm, ↓reduceIte, Nat.cast_one]
      omega
    · have hpm : p ∉ componentActive s a r := by simp [componentActive, hm]
      simp [Finset.erase_eq_of_notMem hpm, hm]
  · simp only [↓reduceIte, componentPopulation, componentActive_attach hs ha hp r]
    split_ifs <;> simp [Finset.card_insert_of_notMem hnot]

/-- The chosen active vertex belongs to the tracked component with its actual
population fraction, including occupancy zero or the entire active set. -/
theorem uniform_active_component_probability (s : State) (a r : ℕ)
    (hne : s.active.Nonempty) :
    (Measure.uniformOfFinset s.active).real {v | cutAncestor s a v = r} =
      (SignedUrn.parameter s.active.card (componentPopulation s a r) : ℝ) := by
  have hZ : (0 : ℤ) < s.active.card := by exact_mod_cast hne.card_pos
  rw [SignedUrn.parameter_eq hZ (componentPopulation_nonneg s a r)
    (componentPopulation_le s a r)]
  change ((Measure.uniformOfFinset s.active) {v | cutAncestor s a v = r}).toReal = _
  rw [Measure.uniformOfFinset_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  simp only [componentPopulation, componentActive, Int.cast_natCast]
  simp only [Set.mem_ofPred_eq]

/-- The pushforward of the actual forward transition is exactly the signed
urn kernel, not merely a matching expectation or an assumed transition rule. -/
theorem transitionLaw_componentPopulation {n : ℕ} {s : State} (hs : ValidAt n s)
    {a : ℕ} (ha : a ≤ n) (r : ℕ) (sign : Bool) (hne : s.active.Nonempty) :
    (transitionLaw s (n + 1) sign).map (fun t => componentPopulation t a r) =
      SignedUrn.transitionLaw s.active.card (if sign then 1 else -1)
        (componentPopulation s a r) := by
  let μ := Measure.uniformOfFinset s.active
  let E : Set ℕ := {v | cutAncestor s a v = r}
  let u := componentPopulation s a r
  let z : ℤ := if sign then 1 else -1
  let q := SignedUrn.parameter s.active.card u
  let : IsProbabilityMeasure μ := uniform_active_probability s hne
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  have hp : (⟨μ.real E, by simp⟩ : unitInterval) = q :=
    Subtype.ext (uniform_active_component_probability s a r hne)
  have hI : HasLaw (E.indicator (fun _ => (1 : ℤ))) (bernoulliMeasure 1 0 q) μ := by
    simpa only [hp, Pi.one_def] using
      (hasLaw_indicator_one_bernoulliMeasure (P := μ) (M := ℤ) hE.nullMeasurableSet)
  have hshift : HasLaw (fun j : ℤ => u + z * j) (bernoulliMeasure (u + z) u q)
      (bernoulliMeasure 1 0 q) := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    simpa only [mul_one, mul_zero, add_zero] using
      map_bernoulliMeasure (1 : ℤ) 0 (fun j => u + z * j) q
  have hmap : HasLaw (fun v => componentPopulation (step s (n + 1) sign v) a r)
      (bernoulliMeasure (u + z) u q) μ := by
    apply (hshift.fun_comp hI).congr
    have hmem : ∀ᵐ v ∂μ, v ∈ s.active := by
      rw [ae_iff]
      simp [μ, Measure.uniformOfFinset_apply]
    filter_upwards [hmem] with v hv
    rw [componentPopulation_step hs ha hv]
    by_cases he : cutAncestor s a v = r <;> simp [E, u, z, he]
  rw [transitionLaw, ite_eq_left hne, Measure.map_map (by fun_prop) (by fun_prop)]
  exact hmap.map_eq

/-- If the source convention also counts the distinguished root as active
when it has frozen, at most one extra vertex is counted. -/
noncomputable def componentPopulationWithRoot (s : State) (a r : ℕ) : ℕ :=
  (insert r (componentActive s a r)).card

theorem componentPopulationWithRoot_le (s : State) (a r : ℕ) :
    (componentPopulationWithRoot s a r : ℤ) ≤ componentPopulation s a r + 1 := by
  change ((insert r (componentActive s a r)).card : ℤ) ≤ (componentActive s a r).card + 1
  exact_mod_cast Finset.card_insert_le r (componentActive s a r)

end Freezing1.Forward
