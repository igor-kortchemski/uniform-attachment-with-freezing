module

public import Freezing1.ForwardHistorySupport
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The actual forward process on one infinite probability space

Ionescu--Tulcea constructs the whole trajectory from the existing uniform
transition kernels. Its finite prefixes, successive joint laws and one-time
marginals are identified explicitly. Absorption is retained; under a schedule
which never becomes extinct every transition is a genuine legal choice.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

private abbrev StateCode := Finset ℕ × Finset ℕ × (ℕ → ℕ → Bool) ×
  (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ)

private noncomputable def stateCode (s : State) : StateCode :=
  (s.vertices, s.active, fun u v => decide (s.graph.Adj u v), s.parent, s.height,
    fun v => Encodable.encode (s.frozenAt v))

private theorem stateCode_injective : Function.Injective stateCode := by
  intro s r h
  have he : s.vertices = r.vertices ∧ s.active = r.active ∧
      (fun u v => decide (s.graph.Adj u v)) = (fun u v => decide (r.graph.Adj u v)) ∧
      s.parent = r.parent ∧ s.height = r.height ∧
      (fun v => Encodable.encode (s.frozenAt v)) = (fun v => Encodable.encode (r.frozenAt v)) := by
    simpa only [stateCode, Prod.mk.injEq] using h
  obtain ⟨hv, ha, hg, hp, hh, hf⟩ := he
  have hgraph : s.graph = r.graph := by
    ext u v
    exact decide_eq_decide.mp (congrFun (congrFun hg u) v)
  have hfrozen : s.frozenAt = r.frozenAt := by
    funext v
    exact Encodable.encode_injective (congrFun hf v)
  exact State.ext_data hv ha hgraph hp hh hfrozen

/-- The ambient state has measurable equality, despite its non-countable
function fields. This does not replace its sigma-algebra or either tree law. -/
instance : MeasurableEq State where
  measurableSet_diagonal := by
    have hcode : Measurable stateCode := measurable_from_top
    have he : Set.diagonal State =
        (fun p : State × State => (stateCode p.1, stateCode p.2)) ⁻¹'
          Set.diagonal StateCode := by
      ext p
      exact stateCode_injective.eq_iff.symm
    rw [he]
    exact measurableSet_diagonal.preimage
      ((hcode.comp measurable_fst).prodMk (hcode.comp measurable_snd))

end Forward

namespace ForwardInfiniteHistory

open Forward

abbrev History := ℕ → State

/-- The next uniform choice is conditioned on the complete preceding path. -/
noncomputable def historyKernel (x : SignSequence) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → State) State where
  toFun H := transitionLaw (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1) (x (n + 1))
  measurable' := (measurable_from_top : Measurable
    (fun s : State => transitionLaw s (n + 1) (x (n + 1)))).comp (measurable_pi_apply _)

instance historyKernel_markov (x : SignSequence) (n : ℕ) :
    IsMarkovKernel (historyKernel x n) := by
  constructor
  intro H
  change IsProbabilityMeasure (transitionLaw (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (n + 1) (x (n + 1)))
  infer_instance

/-- The law of the complete actual forward history, including held steps
after extinction. -/
noncomputable def fullLaw (x : SignSequence) : Measure History :=
  Kernel.trajMeasure (X := fun _ => State) (Measure.dirac initial) (historyKernel x)

instance fullLaw_probability (x : SignSequence) : IsProbabilityMeasure (fullLaw x) := by
  unfold fullLaw
  infer_instance

theorem fullLaw_eq_traj (x : SignSequence) :
    fullLaw x = Kernel.traj (X := fun _ => State) (historyKernel x) 0 (fun _ => initial) := by
  rw [fullLaw, Kernel.trajMeasure, Measure.map_dirac' (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- Every finite history has the genuine iterated-kernel law. -/
theorem map_prefix (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ => State) (historyKernel x) 0 n (fun _ => initial) := by
  rw [fullLaw_eq_traj]
  exact Kernel.traj_map_frestrictLe_apply (X := fun _ => State)
    (κ := historyKernel x) 0 n (fun _ => initial)

/-- The exact joint law of the past and its next state. -/
theorem map_prefix_next (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (fun H => (Preorder.frestrictLe n H, H (n + 1))) =
      (fullLaw x).map (Preorder.frestrictLe n) ⊗ₘ historyKernel x n := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

theorem map_eval_zero (x : SignSequence) :
    (fullLaw x).map (fun H => H 0) = Measure.dirac initial := by
  have h := congrArg (fun μ : Measure ((i : Finset.Iic 0) → State) =>
    μ.map (fun H => H ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) (map_prefix x 0)
  rw [Measure.map_map (by fun_prop) (by fun_prop), Kernel.partialTraj_self,
    Kernel.id_apply, Measure.map_dirac' (by fun_prop)] at h
  exact h

theorem map_eval_succ (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (fun H => H (n + 1)) =
      ((fullLaw x).map (fun H => H n)).bind
        (fun s => transitionLaw s (n + 1) (x (n + 1))) := by
  have h := congrArg Measure.snd (map_prefix_next x n)
  rw [Measure.snd_compProd, Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at h
  change (fullLaw x).map (fun H => H (n + 1)) =
    ((fullLaw x).map (Preorder.frestrictLe n)).bind (historyKernel x n) at h
  rw [h, Measure.bind_map (by fun_prop) (historyKernel x n).aemeasurable,
    Measure.bind_map (measurable_pi_apply n).aemeasurable measurable_from_top.aemeasurable]
  rfl

/-- The infinite construction projects to the previously defined tree law,
for every schedule and time, including after absorption. -/
theorem map_eval (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (fun H => H n) = treeLaw x n := by
  induction n with
  | zero => exact map_eval_zero x
  | succ n ih => rw [map_eval_succ, ih, treeLaw]

theorem fullLaw_initial (x : SignSequence) : ∀ᵐ H ∂fullLaw x, H 0 = initial := by
  apply ae_of_ae_map (μ := fullLaw x) (f := fun H : History => H 0)
    (p := fun s => s = initial) (measurable_pi_apply 0).aemeasurable
  rw [map_eval, treeLaw]
  simp

theorem fullLaw_valid (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x, ∀ n, ValidAt n (H n) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_of_ae_map (μ := fullLaw x) (f := fun H : History => H n)
    (p := ValidAt n) (measurable_pi_apply n).aemeasurable
  rw [map_eval]
  exact treeLaw_valid x n

theorem fullLaw_phaseData (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x, ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime x → PhaseData x n (H n) := by
  apply ae_all_iff.mpr
  intro n
  by_cases hn : (n : ℕ∞) ≤ extinctionTime x
  · have hh : ∀ᵐ H ∂fullLaw x, PhaseData x n (H n) := by
      apply ae_of_ae_map (μ := fullLaw x) (f := fun H : History => H n)
        (p := PhaseData x n) (measurable_pi_apply n).aemeasurable
      rw [map_eval]
      exact treeLaw_phaseData x n hn
    exact hh.mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => (hn h).elim

/-- An absorbed state is held; otherwise the next state is obtained from an
actual active-vertex choice. -/
def LegalOrHeld (x : SignSequence) (n : ℕ) (s r : State) : Prop :=
  (s.active = ∅ ∧ r = s) ∨ LegalStep x n s r

theorem measurable_legalOrHeld {Ω : Type*} [MeasurableSpace Ω]
    (x : SignSequence) (n : ℕ) {s r : Ω → State}
    (hs : Measurable s) (hr : Measurable r) :
    Measurable (fun ω => LegalOrHeld x n (s ω) (r ω)) := by
  unfold LegalOrHeld LegalStep
  apply Measurable.or
  · exact ((measurable_from_top : Measurable (fun s : State => s.active = ∅)).comp hs).and
      (hr.eq hs)
  · apply Measurable.exists
    intro v
    exact ((measurable_from_top : Measurable (fun s : State => v ∈ s.active)).comp hs).and
      (hr.eq ((measurable_from_top : Measurable
        (fun s : State => step s (n + 1) (x (n + 1)) v)).comp hs))

theorem transitionLaw_legalOrHeld (x : SignSequence) (n : ℕ) (s : State) :
    ∀ᵐ r ∂transitionLaw s (n + 1) (x (n + 1)), LegalOrHeld x n s r := by
  apply transitionLaw_ae
  · intro he
    exact Or.inl ⟨he, rfl⟩
  · intro v hv
    exact Or.inr ⟨v, hv, rfl⟩

/-- Genuine legality holds simultaneously along the entire random path. -/
theorem fullLaw_legalOrHeld (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x, ∀ n, LegalOrHeld x n (H n) (H (n + 1)) := by
  apply ae_all_iff.mpr
  intro n
  let P : ((i : Finset.Iic n) → State) × State → Prop := fun q =>
    LegalOrHeld x n (q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) q.2
  have hm : MeasurableSet {q | P q} :=
    measurableSet_setOfPred.mpr (measurable_legalOrHeld x n (by fun_prop) measurable_snd)
  have h : ∀ᵐ q ∂(fullLaw x).map (Preorder.frestrictLe n) ⊗ₘ historyKernel x n, P q := by
    apply Measure.ae_compProd_of_ae_ae hm
    exact Filter.Eventually.of_forall fun H => transitionLaw_legalOrHeld x n
      (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  rw [← map_prefix_next] at h
  exact ae_of_ae_map (by fun_prop) h

/-- Before extinction, every step of the same infinite trajectory is legal
in the original non-absorbed sense. -/
theorem fullLaw_legalSteps (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x, ∀ n : ℕ, (n : ℕ∞) < extinctionTime x →
      LegalStep x n (H n) (H (n + 1)) := by
  filter_upwards [fullLaw_legalOrHeld x, fullLaw_phaseData x] with H hlegal hdata
  intro n hn
  rcases hlegal n with he | he
  · have hc := (hdata n hn.le).count
    rw [he.1, Finset.card_empty, Nat.cast_zero] at hc
    have hp := ((lt_extinctionTime_iff x n).mp hn) n le_rfl
    omega
  · exact he

end ForwardInfiniteHistory
end Freezing1
