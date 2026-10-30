module

public import Freezing1.ForwardInfiniteHistory

/-!
# Common prefixes of actual forward histories

Agreement of schedules through a finite time gives equality of the complete
finite-history laws. An explicit coupling first samples that common history,
then extends it using each schedule's actual continuation kernel. Both full
marginals are the original infinite laws, and the coupled histories agree at
every time of the common prefix. No survival hypothesis is needed.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- The paper numbers schedule entries from one; entry zero is irrelevant. -/
def SchedulesAgreeThrough (x y : SignSequence) (n : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → x i = y i

theorem SchedulesAgreeThrough.mono {x y : SignSequence} {n m : ℕ}
    (h : SchedulesAgreeThrough x y n) (hm : m ≤ n) : SchedulesAgreeThrough x y m :=
  fun i hi him => h i hi (him.trans hm)

theorem eventually_schedulesAgreeThrough {x : ℕ → SignSequence} {y : SignSequence}
    (h : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i) (k : ℕ) :
    ∀ᶠ n in atTop, SchedulesAgreeThrough (x n) y k := by
  have hp : ∀ i ∈ Finset.Icc 1 k, ∀ᶠ n in atTop, x n i = y i :=
    fun i hi => h i (Finset.mem_Icc.mp hi).1
  filter_upwards [(Finset.Icc 1 k).eventually_all.mpr hp] with n hn
  exact fun i hi hik => hn i (Finset.mem_Icc.mpr ⟨hi, hik⟩)

namespace Forward

theorem run_eq_of_schedule_prefix {x y : SignSequence} (choice : ℕ → ℕ) {n : ℕ}
    (h : SchedulesAgreeThrough x y n) : run x choice n = run y choice n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run, run, ih (h.mono (Nat.le_succ n)), h (n + 1) (by omega) le_rfl]

theorem treeLaw_eq_of_schedule_prefix {x y : SignSequence} {n : ℕ}
    (h : SchedulesAgreeThrough x y n) : treeLaw x n = treeLaw y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [treeLaw, treeLaw, ih (h.mono (Nat.le_succ n)), h (n + 1) (by omega) le_rfl]

theorem eventually_treeLaw_eq {x : ℕ → SignSequence} {y : SignSequence}
    (h : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i) (k : ℕ) :
    ∀ᶠ n in atTop, treeLaw (x n) k = treeLaw y k :=
  (eventually_schedulesAgreeThrough h k).mono (fun _ hn => treeLaw_eq_of_schedule_prefix hn)

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem historyKernel_eq_of_sign {x y : SignSequence} {n : ℕ}
    (h : x (n + 1) = y (n + 1)) : historyKernel x n = historyKernel y n := by
  ext H : 1
  change transitionLaw _ _ (x (n + 1)) = transitionLaw _ _ (y (n + 1))
  rw [h]

theorem partialTraj_eq_of_schedule_prefix {x y : SignSequence} {n : ℕ}
    (h : SchedulesAgreeThrough x y n) :
    Kernel.partialTraj (X := fun _ => State) (historyKernel x) 0 n =
      Kernel.partialTraj (X := fun _ => State) (historyKernel y) 0 n := by
  induction n with
  | zero => rw [Kernel.partialTraj_self, Kernel.partialTraj_self]
  | succ n ih =>
      rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n),
        Kernel.partialTraj_succ_of_le (Nat.zero_le n), ih (h.mono (Nat.le_succ n)),
        historyKernel_eq_of_sign (h (n + 1) (by omega) le_rfl)]

theorem map_prefix_eq_of_schedule_prefix {x y : SignSequence} {n : ℕ}
    (h : SchedulesAgreeThrough x y n) :
    (fullLaw x).map (Preorder.frestrictLe n) =
      (fullLaw y).map (Preorder.frestrictLe n) := by
  rw [map_prefix, map_prefix, partialTraj_eq_of_schedule_prefix h]

theorem eventually_map_prefix_eq {x : ℕ → SignSequence} {y : SignSequence}
    (h : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i) (k : ℕ) :
    ∀ᶠ n in atTop, (fullLaw (x n)).map (Preorder.frestrictLe k) =
      (fullLaw y).map (Preorder.frestrictLe k) :=
  (eventually_schedulesAgreeThrough h k).mono (fun _ hn => map_prefix_eq_of_schedule_prefix hn)

/-- Sample the first schedule's finite prefix, then continue independently
under the two actual conditional trajectory kernels. -/
noncomputable def prefixCoupling (x y : SignSequence) (n : ℕ) : Measure (History × History) :=
  (((Kernel.traj (X := fun _ => State) (historyKernel x) n) ×ₖ
    (Kernel.traj (X := fun _ => State) (historyKernel y) n)) ∘ₖ
    Kernel.partialTraj (X := fun _ => State) (historyKernel x) 0 n) (fun _ => initial)

instance prefixCoupling_probability (x y : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (prefixCoupling x y n) := by
  unfold prefixCoupling
  infer_instance

theorem prefixCoupling_fst (x y : SignSequence) (n : ℕ) :
    (prefixCoupling x y n).map Prod.fst = fullLaw x := by
  rw [prefixCoupling, ← Kernel.fst_apply, Kernel.fst_comp, Kernel.fst_prod,
    Kernel.traj_comp_partialTraj (Nat.zero_le n), ← fullLaw_eq_traj]

theorem prefixCoupling_snd {x y : SignSequence} {n : ℕ}
    (h : SchedulesAgreeThrough x y n) :
    (prefixCoupling x y n).map Prod.snd = fullLaw y := by
  rw [prefixCoupling, ← Kernel.snd_apply, Kernel.snd_comp, Kernel.snd_prod,
    partialTraj_eq_of_schedule_prefix h, Kernel.traj_comp_partialTraj (Nat.zero_le n),
    ← fullLaw_eq_traj]

theorem traj_preserves_prefix (x : SignSequence) (n : ℕ)
    (s : (i : Finset.Iic n) → State) :
    ∀ᵐ H ∂Kernel.traj (X := fun _ => State) (historyKernel x) n s,
      Preorder.frestrictLe n H = s := by
  apply ae_of_ae_map (μ := Kernel.traj (X := fun _ => State) (historyKernel x) n s)
    (f := Preorder.frestrictLe n) (p := fun q => q = s) (by fun_prop)
  rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
  simp

/-- The coupling is pathwise exact throughout the prefix, even when a
schedule has already reached absorption. -/
theorem prefixCoupling_agrees (x y : SignSequence) (n : ℕ) :
    ∀ᵐ p ∂prefixCoupling x y n, ∀ i ≤ n, p.1 i = p.2 i := by
  have heq : MeasurableSet {p : History × History |
      Preorder.frestrictLe n p.1 = Preorder.frestrictLe n p.2} := by
    have he : {p : History × History | Preorder.frestrictLe n p.1 = Preorder.frestrictLe n p.2} =
        {p | ∀ i : Finset.Iic n, p.1 i = p.2 i} := by
      ext p
      exact funext_iff
    rw [he]
    apply measurableSet_setOfPred.mpr
    exact Measurable.forall (fun i => Measurable.eq (by fun_prop) (by fun_prop))
  have hp : ∀ᵐ p ∂prefixCoupling x y n,
      Preorder.frestrictLe n p.1 = Preorder.frestrictLe n p.2 := by
    unfold prefixCoupling
    apply Kernel.ae_comp_of_ae_ae heq
    apply Eventually.of_forall
    intro s
    rw [Kernel.prod_apply]
    have hx : ∀ᵐ p ∂(Kernel.traj (X := fun _ => State) (historyKernel x) n s).prod
        (Kernel.traj (X := fun _ => State) (historyKernel y) n s), Preorder.frestrictLe n p.1 = s := by
      apply ae_of_ae_map
        (μ := (Kernel.traj (X := fun _ => State) (historyKernel x) n s).prod
          (Kernel.traj (X := fun _ => State) (historyKernel y) n s))
        (f := Prod.fst) (p := fun H : History => Preorder.frestrictLe n H = s)
        measurable_fst.aemeasurable
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact traj_preserves_prefix x n s
    have hy : ∀ᵐ p ∂(Kernel.traj (X := fun _ => State) (historyKernel x) n s).prod
        (Kernel.traj (X := fun _ => State) (historyKernel y) n s), Preorder.frestrictLe n p.2 = s := by
      apply ae_of_ae_map
        (μ := (Kernel.traj (X := fun _ => State) (historyKernel x) n s).prod
          (Kernel.traj (X := fun _ => State) (historyKernel y) n s))
        (f := Prod.snd) (p := fun H : History => Preorder.frestrictLe n H = s)
        measurable_snd.aemeasurable
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact traj_preserves_prefix y n s
    filter_upwards [hx, hy] with p hx hy
    exact hx.trans hy.symm
  filter_upwards [hp] with p hp i hi
  exact congrFun hp ⟨i, Finset.mem_Iic.mpr hi⟩

/-- Pointwise eventual schedule agreement supplies actual couplings of the
complete histories whose fixed prefixes agree almost surely. -/
theorem eventually_prefix_couplings {x : ℕ → SignSequence} {y : SignSequence}
    (h : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i) (k : ℕ) :
    ∀ᶠ n in atTop,
      (prefixCoupling (x n) y k).map Prod.fst = fullLaw (x n) ∧
      (prefixCoupling (x n) y k).map Prod.snd = fullLaw y ∧
      (∀ᵐ p ∂prefixCoupling (x n) y k, ∀ i ≤ k, p.1 i = p.2 i) := by
  filter_upwards [eventually_schedulesAgreeThrough h k] with n hn
  exact ⟨prefixCoupling_fst _ _ _, prefixCoupling_snd hn, prefixCoupling_agrees _ _ _⟩

end ForwardInfiniteHistory
end Freezing1
