module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Actual countable Markov chains and their interleaving

The transition first chooses which coordinate moves, then applies the given
Markov kernel to precisely that coordinate. No independence of extracted
chains is assumed here. The complete path is the Ionescu--Tulcea law.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace CountableMarkovChain

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

noncomputable def historyKernel (α : Kernel E E) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → E) E where
  toFun H := α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := α.measurable.comp (measurable_pi_apply _)

instance historyKernel_markov (α : Kernel E E) [IsMarkovKernel α] (n : ℕ) :
    IsMarkovKernel (historyKernel α n) := by
  constructor
  intro H
  change IsProbabilityMeasure (α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
  infer_instance

noncomputable def fullLaw (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    Measure (ℕ → E) :=
  Kernel.traj (X := fun _ => E) (historyKernel α) 0 (fun _ => x)

instance fullLaw_probability (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    IsProbabilityMeasure (fullLaw α x) := by unfold fullLaw; infer_instance

omit [MeasurableSingletonClass E] [Countable E] in
theorem fullLaw_eq_trajMeasure (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    fullLaw α x = Kernel.trajMeasure (X := fun _ => E) (Measure.dirac x)
      (historyKernel α) := by
  rw [Kernel.trajMeasure, Measure.map_dirac' (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

omit [MeasurableSingletonClass E] [Countable E] in
theorem map_prefix (α : Kernel E E) [IsMarkovKernel α] (x : E) (n : ℕ) :
    (fullLaw α x).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ => E) (historyKernel α) 0 n (fun _ => x) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ => E)
    (κ := historyKernel α) 0 n (fun _ => x)

omit [MeasurableSingletonClass E] [Countable E] in
theorem map_prefix_next (α : Kernel E E) [IsMarkovKernel α] (x : E) (n : ℕ) :
    (fullLaw α x).map (fun H => (Preorder.frestrictLe n H, H (n + 1))) =
      (fullLaw α x).map (Preorder.frestrictLe n) ⊗ₘ historyKernel α n := by
  rw [fullLaw_eq_trajMeasure]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

omit [MeasurableSingletonClass E] [Countable E] in
theorem map_eval_zero (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    (fullLaw α x).map (fun H => H 0) = Measure.dirac x := by
  have h := congrArg (fun μ : Measure ((i : Finset.Iic 0) → E) =>
    μ.map (fun H => H ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) (map_prefix α x 0)
  rw [Measure.map_map (by fun_prop) (by fun_prop), Kernel.partialTraj_self,
    Kernel.id_apply, Measure.map_dirac' (by fun_prop)] at h
  exact h

omit [MeasurableSingletonClass E] [Countable E] in
theorem map_eval_succ (α : Kernel E E) [IsMarkovKernel α] (x : E) (n : ℕ) :
    (fullLaw α x).map (fun H => H (n + 1)) =
      ((fullLaw α x).map (fun H => H n)).bind α := by
  have h := congrArg Measure.snd (map_prefix_next α x n)
  rw [Measure.snd_compProd, Measure.snd,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  change (fullLaw α x).map (fun H => H (n + 1)) =
    ((fullLaw α x).map (Preorder.frestrictLe n)).bind (historyKernel α n) at h
  rw [h, Measure.bind_map (by fun_prop) (historyKernel α n).aemeasurable,
    Measure.bind_map (measurable_pi_apply n).aemeasurable α.aemeasurable]
  rfl

omit [Countable E] in
theorem fullLaw_initial (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    ∀ᵐ H ∂fullLaw α x, H 0 = x := by
  apply ae_of_ae_map (μ := fullLaw α x) (f := fun H : ℕ → E => H 0)
    (p := fun y => y = x) (measurable_pi_apply 0).aemeasurable
  rw [map_eval_zero]
  simp

/-- The source's definition of an absorbing state. -/
def Absorbing (α : Kernel E E) (x : E) : Prop := α x {x} = 1

omit [Countable E] in
theorem absorbing_iff_eq_dirac (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    Absorbing α x ↔ α x = Measure.dirac x := by
  constructor
  · intro h
    change α x {x} = 1 at h
    ext B hB
    by_cases hx : x ∈ B
    · simp only [Measure.dirac_apply' _ hB, Set.indicator_of_mem hx, Pi.one_apply]
      apply le_antisymm (prob_le_one)
      calc
        1 = α x {x} := h.symm
        _ ≤ α x B := measure_mono (Set.singleton_subset_iff.mpr hx)
    · simp only [Measure.dirac_apply' _ hB, Set.indicator_of_notMem hx]
      apply measure_mono_null (show B ⊆ {x}ᶜ by
        intro z hz hzx
        exact hx ((Set.mem_singleton_iff.mp hzx) ▸ hz))
      rw [measure_compl (measurableSet_singleton x) (measure_ne_top _ _), measure_univ, h]
      simp
  · intro h
    simp [Absorbing, h]

end CountableMarkovChain

namespace InterleavedChain

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

abbrev State (E : Type*) := E × E × Bool

/-- `true` is the source's mark `1`, and `false` its mark `2`. -/
noncomputable def transition (α : Kernel E E) (κ : E × E → unitInterval) :
    Kernel (State E) (State E) where
  toFun s := unitInterval.toNNReal (κ (s.1, s.2.1)) •
      (α s.1).map (fun z => (z, s.2.1, true)) +
    unitInterval.toNNReal (unitInterval.symm (κ (s.1, s.2.1))) •
      (α s.2.1).map (fun z => (s.1, z, false))
  measurable' := measurable_of_countable _

instance transition_markov (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) : IsMarkovKernel (transition α κ) := by
  constructor
  intro s
  constructor
  change (unitInterval.toNNReal (κ (s.1, s.2.1)) •
      (α s.1).map (fun z => (z, s.2.1, true)) +
    unitInterval.toNNReal (unitInterval.symm (κ (s.1, s.2.1))) •
      (α s.2.1).map (fun z => (s.1, z, false))) Set.univ = 1
  simp

theorem transition_apply (α : Kernel E E) (κ : E × E → unitInterval)
    (s : State E) (B : Set (State E)) :
    transition α κ s B =
      (unitInterval.toNNReal (κ (s.1, s.2.1)) : ℝ≥0∞) *
        α s.1 {z | (z, s.2.1, true) ∈ B} +
      (unitInterval.toNNReal (unitInterval.symm (κ (s.1, s.2.1))) : ℝ≥0∞) *
        α s.2.1 {z | (s.1, z, false) ∈ B} := by
  simp only [transition, Kernel.coe_mk, Measure.coe_add, Pi.add_apply,
    Measure.coe_smul, Pi.smul_apply,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable B).measurableSet]
  rfl

/-- In particular, these are exactly the two transition probabilities printed
in L06, including coincident coordinates and absorbing states. -/
theorem transition_left_singleton (α : Kernel E E) (κ : E × E → unitInterval)
    (x y x' : E) (i : Bool) :
    transition α κ (x, y, i) {(x', y, true)} =
      (unitInterval.toNNReal (κ (x, y)) : ℝ≥0∞) * α x {x'} := by
  rw [transition_apply]
  simp

theorem transition_right_singleton (α : Kernel E E) (κ : E × E → unitInterval)
    (x y y' : E) (i : Bool) :
    transition α κ (x, y, i) {(x, y', false)} =
      (unitInterval.toNNReal (unitInterval.symm (κ (x, y))) : ℝ≥0∞) * α y {y'} := by
  rw [transition_apply]
  simp

noncomputable def fullLaw (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (s : State E) : Measure (ℕ → State E) :=
  CountableMarkovChain.fullLaw (transition α κ) s

instance fullLaw_probability (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (s : State E) : IsProbabilityMeasure (fullLaw α κ s) := by
  unfold fullLaw
  infer_instance

/-- Exactly the two non-starvation assumptions of L06. No assumption is made
when the corresponding starting state is absorbing. -/
def Fair (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval) : Prop :=
  (∀ x y i, ¬ CountableMarkovChain.Absorbing α x →
    ∀ᵐ H ∂fullLaw α κ (x, y, i), ∃ n : ℕ, 0 < n ∧ (H n).2.2 = true) ∧
  (∀ x y i, ¬ CountableMarkovChain.Absorbing α y →
    ∀ᵐ H ∂fullLaw α κ (x, y, i), ∃ n : ℕ, 0 < n ∧ (H n).2.2 = false)

end InterleavedChain
end Freezing1
