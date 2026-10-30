module

public import Freezing1.CountableMarkovShift

/-!
# Exact finite avoidance probabilities for a countable Markov chain

The first-step recursion is obtained from the genuine future law, including
its initial state. It is used to prove non-starvation for the interleaved
finite plane processes, rather than assuming independent selection marks.
-/

@[expose] public section

namespace Freezing1.CountableMarkovChain

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

theorem fullLaw_map_shift (α : Kernel E E) [IsMarkovKernel α] (x : E) (n : ℕ) :
    (fullLaw α x).map (shift n) =
      ((fullLaw α x).map (fun H => H n)).bind (fullLaw α) := by
  have hh := congrArg Measure.snd (map_prefix_shift α x n)
  rw [Measure.snd_compProd, Measure.snd,
    Measure.map_map measurable_snd (by fun_prop)] at hh
  change (fullLaw α x).map (shift n) =
    ((fullLaw α x).map (Preorder.frestrictLe n)).bind (futureKernel α n) at hh
  rw [hh, Measure.bind_map (by fun_prop) (futureKernel α n).aemeasurable,
    Measure.bind_map (measurable_pi_apply n).aemeasurable
      (measurable_of_countable _).aemeasurable]
  rfl

theorem fullLaw_map_shift_one (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    (fullLaw α x).map (shift 1) = (α x).bind (fullLaw α) := by
  rw [fullLaw_map_shift, map_eval_succ, map_eval_zero,
    Measure.dirac_bind α.measurable]

/-- A predicate is required at times 1 through n; time zero is excluded. -/
def avoids (P : E → Prop) (n : ℕ) (H : ℕ → E) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ n → P (H i)

theorem measurableSet_avoids (P : E → Prop) (n : ℕ) :
    MeasurableSet {H : ℕ → E | avoids P n H} := by
  apply measurableSet_setOfPred.mpr
  exact Measurable.forall fun i => Measurable.imp measurable_const
    (Measurable.imp measurable_const ((measurable_of_countable P).comp (measurable_pi_apply i)))

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem avoids_succ (P : E → Prop) (n : ℕ) (H : ℕ → E) :
    avoids P (n + 1) H ↔ P (H 1) ∧ avoids P n (shift 1 H) := by
  constructor
  · intro h
    refine ⟨h 1 le_rfl (by omega), ?_⟩
    intro i hi hin
    exact h (1 + i) (by omega) (by omega)
  · rintro ⟨h1, h⟩ i hi hin
    by_cases he : i = 1
    · simpa only [he] using h1
    · have hh := h (i - 1) (by omega) (by omega)
      simpa only [shift, Nat.add_sub_of_le hi] using hh

noncomputable def avoidanceProbability (α : Kernel E E) [IsMarkovKernel α]
    (P : E → Prop) (x : E) (n : ℕ) : ℝ≥0∞ :=
  fullLaw α x {H | avoids P n H}

@[simp] theorem avoidanceProbability_zero (α : Kernel E E) [IsMarkovKernel α]
    (P : E → Prop) (x : E) : avoidanceProbability α P x 0 = 1 := by
  have he : {H : ℕ → E | avoids P 0 H} = Set.univ := by
    ext H
    simp only [avoids, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro i hi hin
    omega
  rw [avoidanceProbability, he, measure_univ]

theorem avoidanceProbability_succ (α : Kernel E E) [IsMarkovKernel α]
    (P : E → Prop) (x : E) (n : ℕ) :
    avoidanceProbability α P x (n + 1) =
      ∫⁻ y, if P y then avoidanceProbability α P y n else 0 ∂α x := by
  let B : Set (ℕ → E) := {H | P (H 0) ∧ avoids P n H}
  have hB : MeasurableSet B :=
    (((Set.to_countable {y | P y}).measurableSet).preimage (measurable_pi_apply 0)).inter
      (measurableSet_avoids P n)
  have he : {H : ℕ → E | avoids P (n + 1) H} = shift 1 ⁻¹' B := by
    ext H
    exact avoids_succ P n H
  rw [avoidanceProbability, he, ← Measure.map_apply (measurable_shift 1) hB,
    fullLaw_map_shift_one, Measure.bind_apply hB (measurable_of_countable _).aemeasurable]
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro y
  have hm : fullLaw α y B = fullLaw α y {H | P y ∧ avoids P n H} := by
    apply measure_congr
    filter_upwards [fullLaw_initial α y] with H hH
    change (P (H 0) ∧ avoids P n H) = (P y ∧ avoids P n H)
    rw [hH]
  change (fullLaw α y) B = (if P y then avoidanceProbability α P y n else 0)
  by_cases hy : P y
  · rw [if_pos hy, avoidanceProbability]
    have he : {H : ℕ → E | P y ∧ avoids P n H} = {H | avoids P n H} := by
      ext H
      simp [hy]
    calc
      (fullLaw α y) B = (fullLaw α y) {H | P y ∧ avoids P n H} := hm
      _ = (fullLaw α y) {H | avoids P n H} := by rw [he]
  · rw [if_neg hy]
    have he : {H : ℕ → E | P y ∧ avoids P n H} = ∅ := by
      ext H
      simp [hy]
    calc
      (fullLaw α y) B = (fullLaw α y) {H | P y ∧ avoids P n H} := hm
      _ = 0 := by rw [he, measure_empty]

end Freezing1.CountableMarkovChain
