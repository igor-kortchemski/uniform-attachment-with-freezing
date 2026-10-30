module

public import Freezing1.InterleavedSourceFirstSelectionLaw

/-!
# The displayed alternating-chain factorization, including boundary cases

The numerical identities are verified for the actual extracted cylinders.
Their proof uses the independently established harmonic-cylinder law, not a
Markov restart at an asynchronous joint endpoint. Empty prefix words use
the original starting states as their last states; null cylinders require
no division. Absorbed coordinates retain the source's fallback convention.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain Filter Set
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem extractedWord_succ (H : ℕ → State E) (side : Bool) (r : ℕ) :
    extractedWord H side (r + 1) = extractedWord H side r ++ [extracted H side (r + 1)] := by
  simp only [extractedWord, List.ofFn_succ', List.concat_eq_append,
    Fin.val_castSucc, Fin.val_last]

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem extractedWord_snoc_iff (H : ℕ → State E) (side : Bool) (v : List E) (z : E) :
    extractedWord H side (v ++ [z]).length = v ++ [z] ↔
      extractedWord H side v.length = v ∧ extracted H side (v.length + 1) = z := by
  simp only [List.length_append, List.length_singleton, extractedWord_succ]
  constructor
  · intro he
    obtain ⟨hl, hr⟩ := List.append_inj he (by simp [extractedWord])
    exact ⟨hl, by simpa using hr⟩
  · rintro ⟨hl, hr⟩
    rw [hl, hr]

omit [MeasurableSingletonClass E] [Countable E] in
theorem wordProbability_append (α : Kernel E E) (x : E) (u v : List E) :
    wordProbability α x (u ++ v) = wordProbability α x u * wordProbability α (u.getLastD x) v := by
  induction u generalizing x with
  | nil => simp [wordProbability]
  | cons a u ih => simp only [List.cons_append, wordProbability, ih, List.getLastD_cons, mul_assoc]

theorem source_right_prefix_transition (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (i : Bool) (u v : List E) (z : E) :
    (InterleavedChain.fullLaw α κ (x, y, i))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H false (v.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, i))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
          α (v.getLastD y) {z} := by
  have he : {H : ℕ → State E | extractedWord H true u.length = u ∧
      extractedWord H false v.length = v ∧ extracted H false (v.length + 1) = z} =
      {H | extractedWord H true u.length = u ∧ extractedWord H false (v ++ [z]).length = v ++ [z]} := by
    ext H
    simp only [Set.mem_ofPred_eq]
    rw [extractedWord_snoc_iff]
  rw [he, extractedWord_pair_probability α κ hf,
    extractedWord_pair_probability α κ hf, wordProbability_append]
  simp only [wordProbability, mul_one, mul_assoc]

theorem source_right_factorization_nonabsorbing (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hv : ¬Absorbing α (v.getLastD y)) :
    (InterleavedChain.fullLaw α κ (x, y, true))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H false (v.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, true))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        (firstSelectionValue false z) := by
  have hfirst :
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        (firstSelectionValue false z) = α (v.getLastD y) {z} :=
    firstSelectionValue_probability_of_nonabsorbing α κ hf
      (u.getLastD x) (v.getLastD y) z true false hv
  rw [source_right_prefix_transition α κ hf, hfirst]

theorem source_left_prefix_transition (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (i : Bool) (u v : List E) (z : E) :
    (InterleavedChain.fullLaw α κ (x, y, i))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H true (u.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, i))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
          α (u.getLastD x) {z} := by
  have he : {H : ℕ → State E | extractedWord H true u.length = u ∧
      extractedWord H false v.length = v ∧ extracted H true (u.length + 1) = z} =
      {H | extractedWord H true (u ++ [z]).length = u ++ [z] ∧
        extractedWord H false v.length = v} := by
    ext H
    simp only [Set.mem_ofPred_eq, extractedWord_snoc_iff]
    tauto
  rw [he, extractedWord_pair_probability α κ hf,
    extractedWord_pair_probability α κ hf, wordProbability_append]
  simp only [wordProbability, mul_one]
  ring

theorem source_left_factorization_nonabsorbing (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hu : ¬Absorbing α (u.getLastD x)) :
    (InterleavedChain.fullLaw α κ (x, y, true))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H true (u.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, true))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        (firstSelectionValue true z) := by
  have hfirst :
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        (firstSelectionValue true z) = α (u.getLastD x) {z} :=
    firstSelectionValue_probability_of_nonabsorbing α κ hf
      (u.getLastD x) (v.getLastD y) z true true hu
  rw [source_left_prefix_transition α κ hf, hfirst]

theorem source_right_factorization_absorbing (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hv : Absorbing α (v.getLastD y)) :
    let μ := InterleavedChain.fullLaw α κ (x, y, true)
    let ρ := InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true)
    let B := {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v}
    μ {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
      extracted H false (v.length + 1) = z} =
      μ B * ρ (everSelected false)ᶜ * (if v.getLastD y = z then 1 else 0) +
      μ B * ρ (everSelected false) * α (v.getLastD y) {z} := by
  dsimp only
  rw [source_right_prefix_transition α κ hf]
  let ρ := InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true)
  have hsum : ρ (everSelected false)ᶜ + ρ (everSelected false) = 1 := by
    rw [add_comm, measure_add_measure_compl (measurableSet_everSelected false), measure_univ]
  have hα : α (v.getLastD y) {z} = if v.getLastD y = z then 1 else 0 := by
    rw [(absorbing_iff_eq_dirac α _).mp hv]
    simp only [Measure.dirac_apply' _ (measurableSet_singleton z),
      Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  rw [← hα]
  calc
    _ = _ * (ρ (everSelected false)ᶜ + ρ (everSelected false)) * α (v.getLastD y) {z} := by
      rw [hsum, mul_one]
    _ = _ := by ring

theorem source_left_factorization_absorbing (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hu : Absorbing α (u.getLastD x)) :
    let μ := InterleavedChain.fullLaw α κ (x, y, true)
    let ρ := InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true)
    let B := {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v}
    μ {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
      extracted H true (u.length + 1) = z} =
      μ B * ρ (everSelected true)ᶜ * (if u.getLastD x = z then 1 else 0) +
      μ B * ρ (everSelected true) * α (u.getLastD x) {z} := by
  dsimp only
  rw [source_left_prefix_transition α κ hf]
  let ρ := InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true)
  have hsum : ρ (everSelected true)ᶜ + ρ (everSelected true) = 1 := by
    rw [add_comm, measure_add_measure_compl (measurableSet_everSelected true), measure_univ]
  have hα : α (u.getLastD x) {z} = if u.getLastD x = z then 1 else 0 := by
    rw [(absorbing_iff_eq_dirac α _).mp hu]
    simp only [Measure.dirac_apply' _ (measurableSet_singleton z),
      Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  rw [← hα]
  calc
    _ = _ * (ρ (everSelected true)ᶜ + ρ (everSelected true)) * α (u.getLastD x) {z} := by
      rw [hsum, mul_one]
    _ = _ := by ring

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem first_right_value_literal (H : ℕ → State E) (z : E) :
    H ∈ firstSelectionValue false z ↔
      ∃ n : ℕ, 0 < n ∧ (∀ m, 0 < m → m < n → (H m).2.2 = true) ∧
        (H n).2.2 = false ∧ (H n).2.1 = z := by
  rw [firstSelectionValue_iff]
  constructor
  · rintro ⟨n, hn, hm, hb, hz⟩
    refine ⟨n, hn, ?_, hm, hz⟩
    intro m hm0 hmn
    have hh := hb m hm0 hmn
    cases he : (H m).2.2 <;> simp_all
  · rintro ⟨n, hn, hb, hm, hz⟩
    refine ⟨n, hn, hm, ?_, hz⟩
    intro m hm0 hmn
    rw [hb m hm0 hmn]
    decide

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem never_right_selected_literal (H : ℕ → State E) :
    H ∉ everSelected false ↔ ∀ n : ℕ, 0 < n → (H n).2.2 = true := by
  constructor
  · intro h n hn
    have hne : (H n).2.2 ≠ false := fun hh => h ⟨n, hn, hh⟩
    cases he : (H n).2.2 <;> simp_all
  · intro h hn
    obtain ⟨n, hn, hm⟩ := hn
    rw [h n hn] at hm
    contradiction

omit [MeasurableSingletonClass E] [Countable E] in
theorem selectedTime_strict_of_nonabsorbing (α : Kernel E E)
    (H : ℕ → State E) (hf : PathFair α H) (side : Bool) (k : ℕ)
    (ha : ¬Absorbing α (extracted H side k)) :
    selectedTime (fun n => (H n).2.2) side k <
      selectedTime (fun n => (H n).2.2) side (k + 1) := by
  have hstart : ¬Absorbing α
      (coordinate (H (selectedTime (fun n => (H n).2.2) side k)) side) := ha
  exact (nextTime_of_exists (fun n => (H n).2.2) side _ (hf side _ hstart)).1

theorem fullLaw_selectedTime_strict_of_nonabsorbing (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (s : State E) (side : Bool) :
    ∀ᵐ H ∂InterleavedChain.fullLaw α κ s, ∀ k,
      ¬Absorbing α (extracted H side k) →
        selectedTime (fun n => (H n).2.2) side k <
          selectedTime (fun n => (H n).2.2) side (k + 1) :=
  (fullLaw_pathFair α κ hf s).mono
    (fun H hH k ha => selectedTime_strict_of_nonabsorbing α H hH side k ha)

end Freezing1.InterleavedChain
