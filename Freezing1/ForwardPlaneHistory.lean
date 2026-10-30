module

public import Freezing1.ForwardPlaneLaw
public import Freezing1.CountablePathLaw

/-!
# The complete chronological plane history has the genuine plane-chain law

The proof transports all finite history prefixes through the actual kernel,
using validity on the source history. Product-path measure uniqueness then
identifies the full trajectory law; marginal equality alone is not used.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def planeHistory (H : ForwardInfiniteHistory.History) : ℕ → PlaneForward.State :=
  fun n => (H n).toPlaneState

noncomputable def planePrefix (n : ℕ) (H : Prefix (E := State) n) :
    Prefix (E := PlaneForward.State) n := fun i => (H i).toPlaneState

theorem measurable_planeHistory : Measurable planeHistory :=
  Measurable.of_eval fun n => measurable_toPlaneState.comp (measurable_pi_apply n)

theorem measurable_planePrefix (n : ℕ) : Measurable (planePrefix n) :=
  Measurable.of_eval fun i => measurable_toPlaneState.comp (measurable_pi_apply i)

private theorem partialTraj_append {D : Type*} [MeasurableSpace D]
    (κ : (n : ℕ) → Kernel (Prefix (E := D) n) D) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) (H : Prefix (E := D) n) :
    Kernel.partialTraj (X := fun _ => D) κ n (n + 1) H =
      (κ n H).map (prefixAppend H) := by
  have hg : Measurable (IicProdIoc (X := fun _ => D) n (n + 1)) := measurable_IicProdIoc
  have hp := (MeasurableEquiv.piSingleton (X := fun _ => D) n).measurable
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hg,
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hg measurable_prodMk_left, Kernel.map_apply _ hp,
    Measure.map_map (hg.comp measurable_prodMk_left) hp]
  congr 1
  funext z i
  simp only [Function.comp_def, IicProdIoc, prefixAppend]
  split_ifs with hi
  · rfl
  · simp [MeasurableEquiv.piSingleton]

private theorem measurable_append_kernel {D : Type*} [MeasurableSpace D]
    (κ : (n : ℕ) → Kernel (Prefix (E := D) n) D) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) : Measurable (fun H : Prefix (E := D) n =>
      (κ n H).map (prefixAppend H)) := by
  have he : (fun H : Prefix (E := D) n => (κ n H).map (prefixAppend H)) =
      Kernel.partialTraj (X := fun _ => D) κ n (n + 1) :=
    funext fun H => (partialTraj_append κ n H).symm
  rw [he]
  exact Kernel.measurable _

private theorem partialTraj_succ_bind {D : Type*} [MeasurableSpace D]
    (κ : (n : ℕ) → Kernel (Prefix (E := D) n) D) [∀ n, IsMarkovKernel (κ n)]
    (x : D) (n : ℕ) :
    Kernel.partialTraj (X := fun _ => D) κ 0 (n + 1) (fun _ => x) =
      (Kernel.partialTraj (X := fun _ => D) κ 0 n (fun _ => x)).bind
        (fun H => (κ n H).map (prefixAppend H)) := by
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.comp_apply]
  congr 1
  funext H
  exact partialTraj_append κ n H

theorem planePrefix_append (n : ℕ) (H : Prefix (E := State) n) (s : State) :
    planePrefix (n + 1) (prefixAppend H s) =
      prefixAppend (planePrefix n H) s.toPlaneState := by
  funext i
  by_cases hi : i.val ≤ n
  · simp only [planePrefix, prefixAppend, dite_eq_left hi]
  · simp only [planePrefix, prefixAppend, dite_eq_right hi]

theorem map_prefix_toPlaneState (p : unitInterval) (n : ℕ) :
    ((fullLaw p).map (Preorder.frestrictLe n)).map (planePrefix n) =
      (PlaneForward.fullLaw p PlaneForward.initial).map (Preorder.frestrictLe n) := by
  rw [map_prefix, PlaneForward.fullLaw, CountableMarkovChain.map_prefix]
  induction n with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply,
      Measure.map_dirac' (measurable_planePrefix 0), Kernel.partialTraj_self, Kernel.id_apply]
    congr 1
    funext i
    exact toPlaneState_initial
  | succ n ih =>
    rw [partialTraj_succ_bind, partialTraj_succ_bind, Measure.map_bind
      (measurable_append_kernel (historyKernel p) n).aemeasurable
      (measurable_planePrefix (n + 1)).aemeasurable,
      ← ih, Measure.bind_map (measurable_planePrefix n).aemeasurable
        (measurable_append_kernel (CountableMarkovChain.historyKernel (PlaneForward.transition p)) n).aemeasurable]
    have hvalid : ∀ᵐ H ∂Kernel.partialTraj (X := fun _ => State) (historyKernel p)
        0 n (fun _ => initial), ValidAt n (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
      rw [← map_prefix]
      apply (ae_map_iff (Preorder.measurable_frestrictLe n).aemeasurable
        (((measurable_from_top : Measurable (fun s : State => ValidAt n s)).comp
          (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n))).setOf)).mpr
      exact (fullLaw_valid p).mono fun H hH => hH n
    apply Measure.bind_congr_right
    filter_upwards [hvalid] with H hH
    change ((transitionLaw p (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1)).map
      (prefixAppend H)).map (planePrefix (n + 1)) =
        (PlaneForward.transition p (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩).toPlaneState).map
          (prefixAppend (planePrefix n H))
    rw [Measure.map_map (measurable_planePrefix (n + 1)) (measurable_prefixAppend_right H)]
    have hfun : planePrefix (n + 1) ∘ prefixAppend H =
        prefixAppend (planePrefix n H) ∘ State.toPlaneState :=
      funext (planePrefix_append n H)
    rw [hfun, ← Measure.map_map (measurable_prefixAppend_right (planePrefix n H))
      measurable_toPlaneState, map_annealedTransition_toPlaneState hH p]

theorem map_fullLaw_toPlaneState (p : unitInterval) :
    (fullLaw p).map planeHistory = PlaneForward.fullLaw p PlaneForward.initial := by
  apply CountablePathLaw.eq_of_prefix_map_eq
  intro n
  rw [Measure.map_map (Preorder.measurable_frestrictLe n) measurable_planeHistory,
    ← map_prefix_toPlaneState p n,
    Measure.map_map (measurable_planePrefix n) (Preorder.measurable_frestrictLe n)]
  rfl

end Freezing1.ForwardAnnealed
