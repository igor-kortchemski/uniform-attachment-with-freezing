module

public import Freezing1.ForwardAnnealedSigns
public import Freezing1.CountableMarkovShift

/-!
# Full finite histories under independent random schedules

Every cylinder of the actual averaged process is the integral of the
corresponding original fixed-schedule history law over the genuine iid sign
word. Thus the annealed identification retains the dependence between all
states of the history, as well as their individual marginals.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def historyKernel (p : unitInterval) (n : ℕ) :
    Kernel (Prefix (E := State) n) State where
  toFun H := transitionLaw p (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1)
  measurable' := (transitionKernel p (n + 1)).measurable.comp (measurable_pi_apply _)

instance historyKernel_markov (p : unitInterval) (n : ℕ) :
    IsMarkovKernel (historyKernel p n) := ⟨fun H =>
      transitionLaw_probability p (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1)⟩

noncomputable def fullLaw (p : unitInterval) : Measure ForwardInfiniteHistory.History :=
  Kernel.traj (X := fun _ => State) (historyKernel p) 0 (fun _ => initial)

instance fullLaw_probability (p : unitInterval) : IsProbabilityMeasure (fullLaw p) := by
  unfold fullLaw
  infer_instance

theorem map_prefix (p : unitInterval) (n : ℕ) :
    (fullLaw p).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ => State) (historyKernel p) 0 n (fun _ => initial) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ => State)
    (κ := historyKernel p) 0 n (fun _ => initial)

private theorem partialTraj_append
    (κ : (n : ℕ) → Kernel (Prefix (E := State) n) State) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) (H : Prefix (E := State) n) :
    Kernel.partialTraj (X := fun _ => State) κ n (n + 1) H =
      (κ n H).map (prefixAppend H) := by
  have hg : Measurable (IicProdIoc (X := fun _ => State) n (n + 1)) := measurable_IicProdIoc
  have hp := (MeasurableEquiv.piSingleton (X := fun _ => State) n).measurable
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

private theorem measurable_append_kernel
    (κ : (n : ℕ) → Kernel (Prefix (E := State) n) State) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) : Measurable (fun H : Prefix (E := State) n =>
      (κ n H).map (prefixAppend H)) := by
  have he : (fun H : Prefix (E := State) n => (κ n H).map (prefixAppend H)) =
      Kernel.partialTraj (X := fun _ => State) κ n (n + 1) :=
    funext fun H => (partialTraj_append κ n H).symm
  rw [he]
  exact Kernel.measurable _

private theorem partialTraj_succ_bind
    (κ : (n : ℕ) → Kernel (Prefix (E := State) n) State) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) :
    Kernel.partialTraj (X := fun _ => State) κ 0 (n + 1) (fun _ => initial) =
      (Kernel.partialTraj (X := fun _ => State) κ 0 n (fun _ => initial)).bind
        (fun H => (κ n H).map (prefixAppend H)) := by
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.comp_apply]
  congr 1
  funext H
  exact partialTraj_append κ n H

private theorem bind_averaged_append (p : unitInterval) (n : ℕ)
    (μ : Measure (Prefix (E := State) n)) [SFinite μ] :
    μ.bind (fun H => (historyKernel p n H).map (prefixAppend H)) =
      (signLaw p).bind (fun sign => μ.bind (fun H =>
        (ForwardInfiniteHistory.historyKernel (fun _ => sign) n H).map (prefixAppend H))) := by
  have hsign (sign : Bool) : Measurable (fun H : Prefix (E := State) n =>
      (ForwardInfiniteHistory.historyKernel (fun _ => sign) n H).map (prefixAppend H)) :=
    measurable_append_kernel (ForwardInfiniteHistory.historyKernel (fun _ => sign)) n
  ext A hA
  rw [Measure.bind_apply hA (measurable_append_kernel (historyKernel p) n).aemeasurable,
    Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  have he (H : Prefix (E := State) n) :
      (historyKernel p n H).map (prefixAppend H) = (signLaw p).bind (fun sign =>
        (ForwardInfiniteHistory.historyKernel (fun _ => sign) n H).map (prefixAppend H)) := by
    change ((signLaw p).bind (fun sign => Forward.transitionLaw
      (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1) sign)).map (prefixAppend H) = _
    rw [Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_prefixAppend_right H).aemeasurable]
    rfl
  simp_rw [he, Measure.bind_apply hA (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hA (hsign _).aemeasurable]
  exact lintegral_lintegral_swap
    (measurable_from_prod_countable_left (fun sign =>
      (Measure.measurable_coe hA).comp (hsign sign))).aemeasurable

/-- Exact equality of all finite-history laws, not only of terminal trees. -/
theorem map_prefix_eq_iid_sign_mixture (p : unitInterval) (n : ℕ) :
    (fullLaw p).map (Preorder.frestrictLe n) = (finiteSignLaw p n).bind
      (fun w => (ForwardInfiniteHistory.fullLaw (wordSchedule w)).map
        (Preorder.frestrictLe n)) := by
  simp_rw [map_prefix, ForwardInfiniteHistory.map_prefix]
  induction n with
  | zero =>
      rw [finiteSignLaw, Measure.pi_of_empty _ (fun i => Fin.elim0 i),
        Measure.dirac_bind (measurable_of_countable _)]
      simp only [Kernel.partialTraj_self]
  | succ n ih =>
      rw [partialTraj_succ_bind, bind_averaged_append, ih, finiteSignLaw_succ,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext sign
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_append_kernel (ForwardInfiniteHistory.historyKernel (fun _ => sign)) n).aemeasurable,
        Measure.bind_map (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext w
      rw [partialTraj_succ_bind,
        ForwardInfiniteHistory.partialTraj_eq_of_schedule_prefix (wordSchedule_snoc_prefix w sign),
        ForwardInfiniteHistory.historyKernel_eq_of_sign
          (x := wordSchedule (Fin.snoc w sign)) (y := fun _ => sign)
          (wordSchedule_snoc_last w sign)]

/-- The infinite averaged history has the original averaged tree marginals. -/
theorem map_eval (p : unitInterval) (n : ℕ) :
    (fullLaw p).map (fun H => H n) = treeLaw p n := by
  have hh := congrArg (fun μ : Measure (Prefix (E := State) n) =>
    μ.map (fun H => H ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
      (map_prefix_eq_iid_sign_mixture p n)
  have hm : Measurable (fun H : Prefix (E := State) n =>
      H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  rw [Measure.map_map hm (Preorder.measurable_frestrictLe (X := fun _ => State) n),
    Measure.map_bind (measurable_of_countable _).aemeasurable hm.aemeasurable] at hh
  have he (w : Fin n → Bool) :
      ((ForwardInfiniteHistory.fullLaw (wordSchedule w)).map (Preorder.frestrictLe n)).map
        (fun H : Prefix (E := State) n => H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) =
      Forward.treeLaw (wordSchedule w) n := by
    rw [Measure.map_map hm (Preorder.measurable_frestrictLe (X := fun _ => State) n)]
    exact ForwardInfiniteHistory.map_eval (wordSchedule w) n
  simp_rw [he] at hh
  exact hh.trans (treeLaw_eq_iid_sign_mixture p n).symm


theorem fullLaw_eq_trajMeasure (p : unitInterval) :
    fullLaw p = Kernel.trajMeasure (X := fun _ => State) (Measure.dirac initial)
      (historyKernel p) := by
  rw [Kernel.trajMeasure, Measure.map_dirac' (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem map_prefix_next (p : unitInterval) (n : ℕ) :
    (fullLaw p).map (fun H => (Preorder.frestrictLe n H, H (n + 1))) =
      (fullLaw p).map (Preorder.frestrictLe n) ⊗ₘ historyKernel p n := by
  rw [fullLaw_eq_trajMeasure]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

theorem fullLaw_initial (p : unitInterval) : ∀ᵐ H ∂fullLaw p, H 0 = initial := by
  apply ae_of_ae_map (μ := fullLaw p) (f := fun H : ForwardInfiniteHistory.History => H 0)
    (p := fun s => s = initial) (measurable_pi_apply 0).aemeasurable
  rw [map_eval, treeLaw]
  simp

/-- Every path is an actual sequence of Algorithm 1 operations, with a
possibly different sign at each time; absorption remains an identity step. -/
theorem transitionLaw_legalOrHeld (p : unitInterval) (n : ℕ) (s : State) :
    ∀ᵐ r ∂transitionLaw p s (n + 1), ∃ sign : Bool,
      ForwardInfiniteHistory.LegalOrHeld (fun _ => sign) n s r := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [transitionLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ _sign, (1 : ℝ≥0∞) ∂signLaw p := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun sign =>
        (ae_iff_prob_eq_one measurable_from_top).mp
          ((ForwardInfiniteHistory.transitionLaw_legalOrHeld (fun _ => sign) n s).mono
            (fun r hr => ⟨sign, hr⟩))
    _ = 1 := by simp only [lintegral_const, measure_univ, mul_one]

theorem fullLaw_legalOrHeld (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p, ∀ n, ∃ sign : Bool,
      ForwardInfiniteHistory.LegalOrHeld (fun _ => sign) n (H n) (H (n + 1)) := by
  apply ae_all_iff.mpr
  intro n
  let P : Prefix (E := State) n × State → Prop := fun q => ∃ sign : Bool,
    ForwardInfiniteHistory.LegalOrHeld (fun _ => sign) n
      (q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) q.2
  have hm : MeasurableSet {q | P q} := by
    apply measurableSet_setOfPred.mpr
    exact Measurable.exists fun sign =>
      ForwardInfiniteHistory.measurable_legalOrHeld (fun _ => sign) n (by fun_prop) measurable_snd
  have hh : ∀ᵐ q ∂(fullLaw p).map (Preorder.frestrictLe n) ⊗ₘ historyKernel p n, P q := by
    apply Measure.ae_compProd_of_ae_ae hm
    exact Filter.Eventually.of_forall fun H => transitionLaw_legalOrHeld p n
      (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  rw [← map_prefix_next] at hh
  exact ae_of_ae_map (μ := fullLaw p)
    (f := fun H => (Preorder.frestrictLe n H, H (n + 1))) (by fun_prop) hh

theorem fullLaw_valid (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p, ∀ n, ValidAt n (H n) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_of_ae_map (μ := fullLaw p) (f := fun H : ForwardInfiniteHistory.History => H n)
    (p := ValidAt n) (measurable_pi_apply n).aemeasurable
  rw [map_eval]
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [treeLaw_eq_iid_sign_mixture, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂finiteSignLaw p n := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun w =>
        (ae_iff_prob_eq_one measurable_from_top).mp (Forward.treeLaw_valid (wordSchedule w) n)
    _ = 1 := by simp only [lintegral_const, measure_univ, mul_one]

end Freezing1.ForwardAnnealed
