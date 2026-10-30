module

public import Freezing1.SIRTreeWordMixture
public import Freezing1.SIRAbsorption

/-!
# Complete terminal SIR trees as actual adaptive sign-word mixtures

The original attachment/freezing word law agrees with the SIR conditional
tree law on feasible words. Feasibility is proved almost surely from the
actual adaptive Bernoulli law, including its zero infection probability
at zero susceptible count. No restriction on the observation horizon is
needed, and absorption is retained throughout.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Potential signs are still sampled after absorption. At zero susceptible
count they are false, because the adaptive infection probability is zero. -/
def SignWordFeasible (n : ℕ) : {k : ℕ} → (Fin k → Bool) → Prop
  | 0, _ => True
  | k + 1, w => SignWordFeasible n (Fin.init w) ∧
      ((countsRunWord n (Fin.init w)).susceptible = 0 → w (Fin.last k) = false)

theorem signWordFeasible_of_singleton_ne_zero (rate : ℝ≥0) (n : ℕ)
    {k : ℕ} (w : Fin k → Bool) (hw : signWordLaw rate n k {w} ≠ 0) :
    SignWordFeasible n w := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [signWordLaw_singleton_succ] at hw
    have hpref : signWordLaw rate n k {Fin.init w} ≠ 0 := by
      intro hz
      exact hw (by rw [hz, zero_mul])
    have hlast : bernoulliMeasure true false (infectionProbability rate
        (countsRunWord n (Fin.init w)).susceptible) {w (Fin.last k)} ≠ 0 := by
      intro hz
      exact hw (by rw [hz, mul_zero])
    refine ⟨ih (Fin.init w) hpref, ?_⟩
    intro hu
    cases hb : w (Fin.last k) with
    | false => rfl
    | true => simp [hu, hb] at hlast

theorem signWordLaw_feasible (rate : ℝ≥0) (n k : ℕ) :
    ∀ᵐ w ∂signWordLaw rate n k, SignWordFeasible n w := by
  apply ae_iff_of_countable.mpr
  intro w hw
  exact signWordFeasible_of_singleton_ne_zero rate n w hw

theorem treeStep_tree_false (z : TreeState) (u : PlaneTree.Address) :
    (treeStep z false u).tree = PlaneForward.step z.tree false u := by
  by_cases hu : u ∈ z.tree.active <;>
    simp [treeStep, PlaneForward.step, hu, recoverTreeState]

theorem signedTreeLaw_tree_of_feasible_sign {z : TreeState} (b : Bool)
    (hfeasible : z.susceptible = 0 → b = false) :
    (signedTreeLaw z b).map TreeState.tree = PlaneForward.signedTransitionLaw z.tree b := by
  by_cases hu : z.susceptible = 0
  · rw [hfeasible hu]
    unfold signedTreeLaw PlaneForward.signedTransitionLaw
    split_ifs
    · rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      congr 1
      funext u
      exact treeStep_tree_false z u
    · simp
  · exact signedTreeLaw_tree_of_susceptible_pos (by omega) b

/-- The capacity guard is irrelevant on every feasible sign word, at
arbitrary horizons, including the full terminal horizon. -/
theorem conditionalTreeWordLaw_map_tree_feasible (n : ℕ) {k : ℕ}
    (w : Fin k → Bool) (hw : SignWordFeasible n w) :
    (conditionalTreeWordLaw n w).map TreeState.tree = planeWordLaw w := by
  induction k with
  | zero => simp [conditionalTreeWordLaw, planeWordLaw, initialTreeState]
  | succ k ih =>
    rw [conditionalTreeWordLaw, Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
    change (conditionalTreeWordLaw n (Fin.init w)).bind
      (fun z => (signedTreeLaw z (w (Fin.last k))).map TreeState.tree) =
        (planeWordLaw (Fin.init w)).bind
          (fun s => PlaneForward.signedTransitionLaw s (w (Fin.last k)))
    rw [← ih (Fin.init w) hw.1, Measure.bind_map
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [conditionalTreeWordLaw_phase n (Fin.init w)] with z hz
    apply signedTreeLaw_tree_of_feasible_sign
    intro hu
    have hzU : z.susceptible = (countsRunWord n (Fin.init w)).susceptible :=
      congrArg Counts.susceptible hz.2
    exact hw.2 (by rw [← hzU]; exact hu)

theorem treeFullLaw_plane_word_mixture_all (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H => (H k).tree) =
      (signWordLaw rate n k).bind planeWordLaw := by
  change (treeFullLaw rate n).map (TreeState.tree ∘ (fun H => H k)) = _
  rw [← Measure.map_map (measurable_of_countable TreeState.tree) (measurable_pi_apply k),
    treeFullLaw_eval_word_mixture,
    Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [signWordLaw_feasible rate n k] with w hw
  exact conditionalTreeWordLaw_map_tree_feasible n w hw

theorem planeWordLaw_phase_feasible (n : ℕ) {k : ℕ} (w : Fin k → Bool)
    (hw : SignWordFeasible n w) :
    ∀ᵐ s ∂planeWordLaw w, PlaneForward.Valid s ∧
      s.active.card = (countsRunWord n w).infectious ∧
      (countsRunWord n w).susceptible + s.vertices.card = n + 1 := by
  rw [← conditionalTreeWordLaw_map_tree_feasible n w hw]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    (Set.to_countable _).measurableSet).mpr
  filter_upwards [conditionalTreeWordLaw_phase n w] with z hz
  refine ⟨hz.1.1, congrArg Counts.infectious hz.2, ?_⟩
  have hzU : z.susceptible = (countsRunWord n w).susceptible :=
    congrArg Counts.susceptible hz.2
  rw [← hzU]
  exact hz.1.2

theorem countsStep_legal_of_feasible (c : Counts) (b : Bool)
    (hfeasible : c.susceptible = 0 → b = false) : c.LegalNext (countsStep c b) := by
  by_cases hi : c.infectious = 0
  · exact Or.inl ⟨hi, countsStep_of_absorbed hi b⟩
  · have hip : 0 < c.infectious := by omega
    cases b
    · exact Or.inr ⟨hip, Or.inr (by simp [countsStep, hi])⟩
    · have hu : c.susceptible ≠ 0 := by
        intro hu
        have hh := hfeasible hu
        cases hh
      exact Or.inr ⟨hip, Or.inl ⟨by omega, by simp [countsStep, hi, hu]⟩⟩

theorem countsRunWord_feasible_identity (n : ℕ) {k : ℕ} (w : Fin k → Bool)
    (hw : SignWordFeasible n w) (hi : 0 < (countsRunWord n w).infectious) :
    (countsRunWord n w).infectious + 2 * (countsRunWord n w).susceptible + k = 2 * n + 1 := by
  induction k with
  | zero => simp [countsRunWord, initialCounts, Nat.add_comm]
  | succ k ih =>
    have hlegal := countsStep_legal_of_feasible (countsRunWord n (Fin.init w))
      (w (Fin.last k)) hw.2
    have hpos := hlegal.infectious_pos_previous hi
    have hprev := ih (Fin.init w) hw.1 hpos
    have hpot := hlegal.potential_succ hpos
    change (countsRunWord n w).potential + 1 =
      (countsRunWord n (Fin.init w)).potential at hpot
    simp only [Counts.potential] at hpot
    omega

theorem countsRunWord_feasible_terminal (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) : (countsRunWord n w).infectious = 0 := by
  by_contra hn
  have hh := countsRunWord_feasible_identity n w hw (show 0 < (countsRunWord n w).infectious by omega)
  omega

theorem planeWordLaw_terminal_feasible (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) :
    ∀ᵐ s ∂planeWordLaw w, PlaneForward.Valid s ∧ s.active = ∅ ∧
      (countsRunWord n w).susceptible + s.vertices.card = n + 1 := by
  filter_upwards [planeWordLaw_phase_feasible n w hw] with s hs
  refine ⟨hs.1, ?_, hs.2.2⟩
  apply Finset.card_eq_zero.mp
  rw [hs.2.1, countsRunWord_feasible_terminal n w hw]

noncomputable def planeWordTreeLaw {k : ℕ} (w : Fin k → Bool) : Measure PlaneTree.Tree :=
  (planeWordLaw w).map PlaneForward.shape

instance planeWordTreeLaw_probability {k : ℕ} (w : Fin k → Bool) :
    IsProbabilityMeasure (planeWordTreeLaw w) := by
  unfold planeWordTreeLaw
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
    |>.mpr inferInstance

theorem embeddedTerminalTreeLaw_word_mixture (rate : ℝ≥0) (n : ℕ) :
    (embeddedTerminalTreeLaw rate n : Measure PlaneTree.Tree) =
      (signWordLaw rate n (2 * n + 1)).bind planeWordTreeLaw := by
  change (treeFullLaw rate n).map
    (fun H => PlaneForward.shape (H (2 * n + 1)).tree) = _
  rw [show (fun H : ℕ → TreeState => PlaneForward.shape (H (2 * n + 1)).tree) =
      PlaneForward.shape ∘ (fun H => (H (2 * n + 1)).tree) from rfl,
    ← Measure.map_map (measurable_of_countable _) (by fun_prop),
    treeFullLaw_plane_word_mixture_all,
    Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  rfl

end Freezing1.SIR
