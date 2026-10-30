module

public import Freezing1.ForwardComponentUrnPath
public import Freezing1.ForwardInfiniteHistory

/-!
# The actual infinite component process has the signed-urn path laws

The continuation is the original forward history kernel conditioned on a
finite past. Its relation to the original full law is proved explicitly.
Every component record is projected from these genuine tree trajectories.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace ForwardInfiniteHistory

open Forward

noncomputable def continuationHistoryLaw (x : SignSequence) (a : ℕ)
    (past : (i : Finset.Iic a) → State) : Measure History :=
  Kernel.traj (X := fun _ => State) (historyKernel x) a past

instance continuationHistoryLaw_probability (x : SignSequence) (a : ℕ)
    (past : (i : Finset.Iic a) → State) : IsProbabilityMeasure (continuationHistoryLaw x a past) := by
  unfold continuationHistoryLaw
  infer_instance

/-- This conditional future is a genuine disintegration of the original
full forward history over its entire finite prefix. -/
theorem fullLaw_bind_continuationHistoryLaw (x : SignSequence) (a : ℕ) :
    fullLaw x = ((fullLaw x).map (Preorder.frestrictLe a)).bind (continuationHistoryLaw x a) := by
  calc
    _ = Kernel.traj (X := fun _ => State) (historyKernel x) 0 (fun _ => initial) := fullLaw_eq_traj x
    _ = (Kernel.partialTraj (X := fun _ => State) (historyKernel x) 0 a (fun _ => initial)).bind
        (Kernel.traj (X := fun _ => State) (historyKernel x) a) := by
      rw [← Kernel.traj_comp_partialTraj (Nat.zero_le a), Kernel.comp_apply]
    _ = _ := by rw [map_prefix]; rfl

noncomputable def actualComponentRecord (cut r start k : ℕ) : History → SignedUrn.Trajectory :=
  SignedUrn.record (fun i H => componentPopulation (H i) cut r) start k

theorem measurable_actualComponentRecord (cut r a k : ℕ) :
    Measurable (actualComponentRecord cut r a k) := by
  have hobs (i : ℕ) : Measurable (fun H : History => componentPopulation (H i) cut r) :=
    (measurable_from_top : Measurable (fun s : State => componentPopulation s cut r)).comp
      (measurable_pi_apply i)
  induction k generalizing a with
  | zero => exact (measurable_of_countable (fun u : ℤ => (⟨[u]⟩ : SignedUrn.Trajectory))).comp (hobs a)
  | succ k ih =>
    exact (measurable_of_countable (fun p : ℤ × SignedUrn.Trajectory => SignedUrn.prepend p.1 p.2)).comp
      ((hobs a).prodMk (ih (a + 1)))

theorem continuationHistoryLaw_preserves_prefix (x : SignSequence) (a : ℕ)
    (past : (i : Finset.Iic a) → State) :
    ∀ᵐ H ∂continuationHistoryLaw x a past, Preorder.frestrictLe a H = past := by
  apply ae_of_ae_map (μ := continuationHistoryLaw x a past)
    (f := Preorder.frestrictLe (π := fun _ : ℕ => State) a)
    (p := fun q : ((i : Finset.Iic a) → State) => q = past) (by fun_prop)
  rw [continuationHistoryLaw, Kernel.traj_map_frestrictLe_apply (X := fun _ => State),
    Kernel.partialTraj_self, Kernel.id_apply]
  simp

theorem actual_partial_preserves_prefix (x : SignSequence) (a : ℕ)
    (past : (i : Finset.Iic a) → State) :
    ∀ᵐ q ∂Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past,
      Preorder.frestrictLe₂ (π := fun _ : ℕ => State) (Nat.le_succ a) q = past := by
  have hm : Measurable (Preorder.frestrictLe₂ (π := fun _ : ℕ => State) (Nat.le_succ a)) :=
    Measurable.of_eval fun i => (measurable_pi_apply
      (⟨i.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.property).trans (Nat.le_succ a))⟩ :
        Finset.Iic (a + 1)))
  apply ae_of_ae_map (μ := Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past)
    (f := Preorder.frestrictLe₂ (π := fun _ : ℕ => State) (Nat.le_succ a))
    (p := fun q : ((i : Finset.Iic a) → State) => q = past) hm.aemeasurable
  rw [Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => State),
    Kernel.partialTraj_self, Kernel.id_apply]
  simp

theorem actual_partial_map_next (x : SignSequence) (a : ℕ)
    (past : (i : Finset.Iic a) → State) :
    (Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past).map
        (fun q => q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      transitionLaw (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) (a + 1) (x (a + 1)) := by
  have h := congrArg (fun κ : Kernel ((i : Finset.Iic a) → State) State => κ past)
    (Kernel.map_partialTraj_succ_self (X := fun _ => State) (κ := historyKernel x) a)
  rw [Kernel.map_apply _ (by fun_prop)] at h
  exact h

/-- Joint record law of the actual tree component on every finite future
interval, obtained from its original kernels and complete past. -/
theorem continuationHistoryLaw_component_record (x : SignSequence) (a k cut r : ℕ)
    (past : (i : Finset.Iic a) → State)
    (hs : HasHistory x a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) (hcut : cut ≤ a)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (continuationHistoryLaw x a past).map (actualComponentRecord cut r a k) =
      SignedUrn.pathLaw (activeCount x) a k
        (componentPopulation (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) cut r) := by
  induction k generalizing a with
  | zero =>
    calc
      _ = (continuationHistoryLaw x a past).map
          (fun _ => (⟨[componentPopulation (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) cut r]⟩ : SignedUrn.Trajectory)) := by
        apply Measure.map_congr
        filter_upwards [continuationHistoryLaw_preserves_prefix x a past] with H hH
        exact congrArg (fun q : State => (⟨[componentPopulation q cut r]⟩ : SignedUrn.Trajectory))
          (congrFun hH ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
      _ = _ := by simp [SignedUrn.pathLaw]
  | succ k ih =>
    have haτ : (a : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show a < a + (k + 1) by omega)) hτ
    have hpos := ((lt_extinctionTime_iff x a).mp haτ) a le_rfl
    have hne : (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active.Nonempty := by
      have hc := hs.current.count
      exact Finset.card_pos.mp (by omega)
    have hrest : (((a + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hτ
    have hnext : ∀ᵐ q ∂Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past,
        HasHistory x (a + 1) (q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩) := by
      apply ae_of_ae_map
        (μ := Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past)
        (f := fun q : ((i : Finset.Iic (a + 1)) → State) => q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (p := HasHistory x (a + 1)) (measurable_pi_apply _).aemeasurable
      rw [actual_partial_map_next]
      apply transitionLaw_ae _ _ _ _
      · intro he
        exact (hne.ne_empty he).elim
      · intro v hv
        exact hs.extend (hs.current.step hv) ⟨v, hv, rfl⟩
    have hsplit : continuationHistoryLaw x a past =
        (Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past).bind
          (continuationHistoryLaw x (a + 1)) := by
      unfold continuationHistoryLaw
      rw [← Kernel.traj_comp_partialTraj (Nat.le_succ a), Kernel.comp_apply]
    have hmcont : Measurable (continuationHistoryLaw x (a + 1)) :=
      Kernel.measurable (Kernel.traj (X := fun _ => State) (historyKernel x) (a + 1))
    rw [hsplit, Measure.map_bind hmcont.aemeasurable
      (measurable_actualComponentRecord cut r a (k + 1)).aemeasurable]
    calc
      _ = (Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past).bind
          (fun q => (SignedUrn.pathLaw (activeCount x) (a + 1) k
              (componentPopulation (q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩) cut r)).map
            (SignedUrn.prepend (componentPopulation (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) cut r))) := by
        apply Measure.bind_congr_right
        filter_upwards [hnext, actual_partial_preserves_prefix x a past] with q hq hp
        have hhead : ∀ᵐ H ∂continuationHistoryLaw x (a + 1) q,
            actualComponentRecord cut r a (k + 1) H =
              SignedUrn.prepend (componentPopulation (q ⟨a, Finset.mem_Iic.mpr (Nat.le_succ a)⟩) cut r)
                (actualComponentRecord cut r (a + 1) k H) := by
          filter_upwards [continuationHistoryLaw_preserves_prefix x (a + 1) q] with H hH
          change SignedUrn.prepend (componentPopulation (H a) cut r) _ = _
          rw [show H a = q ⟨a, Finset.mem_Iic.mpr (Nat.le_succ a)⟩ from
            congrFun hH ⟨a, Finset.mem_Iic.mpr (Nat.le_succ a)⟩]
          rfl
        calc
          _ = (continuationHistoryLaw x (a + 1) q).map
              ((SignedUrn.prepend (componentPopulation (q ⟨a, Finset.mem_Iic.mpr (Nat.le_succ a)⟩) cut r)) ∘
                actualComponentRecord cut r (a + 1) k) := Measure.map_congr hhead
          _ = _ := by
            rw [← Measure.map_map (measurable_of_countable _) (measurable_actualComponentRecord _ _ _ _),
              ih (a + 1) q hq (hcut.trans (Nat.le_succ a)) hrest]
            rw [show q ⟨a, Finset.mem_Iic.mpr (Nat.le_succ a)⟩ = past ⟨a, Finset.mem_Iic.mpr le_rfl⟩ from
              congrFun hp ⟨a, Finset.mem_Iic.mpr le_rfl⟩]
      _ = ((Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past).map
          (fun q => componentPopulation (q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩) cut r)).bind
            (fun u => (SignedUrn.pathLaw (activeCount x) (a + 1) k u).map
              (SignedUrn.prepend (componentPopulation (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) cut r))) := by
        exact (Measure.bind_map
          (f := fun q : ((i : Finset.Iic (a + 1)) → State) =>
            componentPopulation (q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩) cut r)
          (g := fun u => (SignedUrn.pathLaw (activeCount x) (a + 1) k u).map
            (SignedUrn.prepend (componentPopulation (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) cut r)))
          ((measurable_from_top : Measurable (fun s : State => componentPopulation s cut r)).comp
            (measurable_pi_apply _)).aemeasurable (measurable_of_countable _).aemeasurable).symm
      _ = _ := by
        have hmap : (Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past).map
            (fun q => componentPopulation (q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩) cut r) =
            (transitionLaw (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) (a + 1) (x (a + 1))).map
              (fun s => componentPopulation s cut r) := by
          calc
            _ = ((Kernel.partialTraj (X := fun _ => State) (historyKernel x) a (a + 1) past).map
                (fun q => q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩)).map
                  (fun s => componentPopulation s cut r) :=
              (Measure.map_map
                (f := fun q : ((i : Finset.Iic (a + 1)) → State) =>
                  q ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩)
                (g := fun s => componentPopulation s cut r)
                measurable_from_top (measurable_pi_apply _)).symm
            _ = _ := by rw [actual_partial_map_next]
        rw [hmap, transitionLaw_componentPopulation hs.current.valid hcut r _ hne, hs.current.count,
          SignedUrn.pathLaw, activeCount_succ]
        congr 2
        omega

end ForwardInfiniteHistory
end Freezing1
