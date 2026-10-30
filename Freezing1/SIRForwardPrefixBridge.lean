module

public import Freezing1.PrefixMarkovProjection
public import Freezing1.SIRTreePrefixWordObservations
public import Freezing1.ForwardPlaneHistory
public import Freezing1.ForwardSchedulePrefix

/-!
# The complete fixed-word forward history in the SIR mixture

Every earlier tree and every earlier count are kept in the same joint law.
The proof transports the actual transition kernels at each step, including
the held states after absorption.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory CountableMarkovChain PrefixProjection
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def planePrefixWordLaw :
    {k : ℕ} → (Fin k → Bool) → Measure (Prefix (E := PlaneForward.State) k)
  | 0, _ => Measure.dirac (fun _ => PlaneForward.initial)
  | k + 1, w => (planePrefixWordLaw (Fin.init w)).bind fun P =>
      (PlaneForward.signedTransitionLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
        (w (Fin.last k))).map (prefixAppend P)

theorem conditionalTreePrefixWordLaw_map_tree (n : ℕ) {k : ℕ} (w : Fin k → Bool)
    (hw : SignWordFeasible n w) :
    (conditionalTreePrefixWordLaw n w).map (mapPrefix TreeState.tree k) =
      planePrefixWordLaw w := by
  induction k with
  | zero =>
    rw [conditionalTreePrefixWordLaw,
      Measure.map_dirac' (measurable_mapPrefix TreeState.tree 0)]
    rfl
  | succ k ih =>
    rw [conditionalTreePrefixWordLaw, planePrefixWordLaw, ← ih (Fin.init w) hw.1]
    apply map_extension_of_ae TreeState.tree k
      (conditionalTreePrefixWordLaw n (Fin.init w))
      (fun z => signedTreeLaw z (w (Fin.last k)))
      (fun s => PlaneForward.signedTransitionLaw s (w (Fin.last k)))
    filter_upwards [conditionalTreePrefixWordLaw_phase n (Fin.init w)] with P hP
    apply signedTreeLaw_tree_of_feasible_sign
    intro hu
    apply hw.2
    have hc : (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).counts =
        countsRunWord n (Fin.init w) := by rw [hP.2, countsPrefixWord_last]
    have hh := congrArg Counts.susceptible hc
    change (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).susceptible = _ at hh
    rw [← hh]
    exact hu

theorem originalForwardPrefix_map_tree {k : ℕ} (w : Fin k → Bool) :
    ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
      (Preorder.frestrictLe k)).map (ForwardAnnealed.planePrefix k) =
        planePrefixWordLaw w := by
  induction k with
  | zero =>
    rw [ForwardInfiniteHistory.map_prefix, Kernel.partialTraj_self, Kernel.id_apply,
      Measure.map_dirac' (ForwardAnnealed.measurable_planePrefix 0)]
    apply congrArg Measure.dirac
    funext i
    exact Forward.toPlaneState_initial
  | succ k ih =>
    rw [ForwardInfiniteHistory.map_prefix, partialTraj_succ_bind,
      Measure.map_bind (measurable_append_kernel _ k).aemeasurable
        (ForwardAnnealed.measurable_planePrefix (k + 1)).aemeasurable]
    have hprev := ForwardInfiniteHistory.map_prefix_eq_of_schedule_prefix
      (wordSchedule_agree_init w)
    rw [ForwardInfiniteHistory.map_prefix] at hprev
    rw [hprev, planePrefixWordLaw, ← ih (Fin.init w),
      Measure.bind_map (ForwardAnnealed.measurable_planePrefix k).aemeasurable
        (measurable_of_countable _).aemeasurable]
    have hv : ∀ᵐ P ∂(ForwardInfiniteHistory.fullLaw
        (ForwardAnnealed.wordSchedule (Fin.init w))).map (Preorder.frestrictLe k),
        Forward.ValidAt k (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) := by
      apply (ae_map_iff (Preorder.measurable_frestrictLe k).aemeasurable
        (((measurable_from_top : Measurable (fun s : Forward.State => Forward.ValidAt k s)).comp
          (measurable_pi_apply (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k))).setOf)).mpr
      exact (ForwardInfiniteHistory.fullLaw_valid _).mono fun H hH => hH k
    apply Measure.bind_congr_right
    filter_upwards [hv] with P hP
    change ((Forward.transitionLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (k + 1)
      (ForwardAnnealed.wordSchedule w (k + 1))).map (prefixAppend P)).map
        (ForwardAnnealed.planePrefix (k + 1)) =
      (PlaneForward.signedTransitionLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).toPlaneState
        (w (Fin.last k))).map (prefixAppend (ForwardAnnealed.planePrefix k P))
    rw [wordSchedule_last, Measure.map_map
      (ForwardAnnealed.measurable_planePrefix (k + 1)) (measurable_prefixAppend_right P)]
    have he : ForwardAnnealed.planePrefix (k + 1) ∘ prefixAppend P =
        prefixAppend (ForwardAnnealed.planePrefix k P) ∘ Forward.State.toPlaneState :=
      funext (ForwardAnnealed.planePrefix_append k P)
    rw [he, ← Measure.map_map
      (measurable_prefixAppend_right (ForwardAnnealed.planePrefix k P))
      Forward.measurable_toPlaneState, Forward.map_transitionLaw_toPlaneState hP]

/-- The actual SIR history is mixed over complete original forward histories,
with the actual adaptive sign-word weights. -/
theorem treeFullLaw_original_treePrefix_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H => fun i : Finset.Iic k => (H i.val).tree) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map (ForwardAnnealed.planePrefix k)) := by
  have he : (fun H : ℕ → TreeState => fun i : Finset.Iic k => (H i.val).tree) =
      mapPrefix TreeState.tree k ∘ Preorder.frestrictLe k := rfl
  rw [he, ← Measure.map_map (measurable_mapPrefix TreeState.tree k)
    (Preorder.measurable_frestrictLe k), treeFullLaw_prefix_word_mixture,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_mapPrefix TreeState.tree k).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [signWordLaw_feasible rate n k] with w hw
  rw [conditionalTreePrefixWordLaw_map_tree n w hw, originalForwardPrefix_map_tree w]

/-- Counts and complete tree paths are identified jointly. In particular,
the absorption time can be read from the same count prefix as the trees. -/
theorem treeFullLaw_countsPrefix_original_treePrefix_word_mixture
    (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree))) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map
            (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))) := by
  have he : (fun H : ℕ → TreeState =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree))) =
      (fun P : Prefix (E := TreeState) k =>
        ((fun i => (P i).counts), mapPrefix TreeState.tree k P)) ∘
          Preorder.frestrictLe k := rfl
  have hG : Measurable (fun P : Prefix (E := TreeState) k =>
      ((fun i => (P i).counts), mapPrefix TreeState.tree k P)) := measurable_of_countable _
  rw [he, ← Measure.map_map hG
    (Preorder.measurable_frestrictLe k), treeFullLaw_prefix_word_mixture,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [signWordLaw_feasible rate n k] with w hw
  calc
    _ = (conditionalTreePrefixWordLaw n w).map
        (fun P => (countsPrefixWord n w, mapPrefix TreeState.tree k P)) := by
      apply Measure.map_congr
      filter_upwards [conditionalTreePrefixWordLaw_phase n w] with P hP
      exact congrArg (fun c => (c, mapPrefix TreeState.tree k P)) (funext hP.2)
    _ = (planePrefixWordLaw w).map (fun Q => (countsPrefixWord n w, Q)) := by
      rw [← conditionalTreePrefixWordLaw_map_tree n w hw,
        Measure.map_map (measurable_of_countable _) (measurable_mapPrefix TreeState.tree k)]
      rfl
    _ = _ := by
      rw [← originalForwardPrefix_map_tree w,
        Measure.map_map (measurable_of_countable _) (ForwardAnnealed.measurable_planePrefix k)]
      rfl

end Freezing1.SIR
