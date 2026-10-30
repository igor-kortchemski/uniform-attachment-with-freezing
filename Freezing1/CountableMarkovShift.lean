module

public import Freezing1.InterleavedChainKernel

/-!
# The actual Markov future after a fixed time

Finite suffixes of the iterated history kernels are identified by their
append-one-state recursion. The infinite suffix law is then obtained from
uniqueness of projective limits. This supplies the real future kernel and
joint past/future law, rather than assuming a Markov property for extracted
subsequences.
-/

@[expose] public section

namespace Freezing1.CountableMarkovChain

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [MeasurableSpace E]

abbrev Prefix (n : ℕ) := Finset.Iic n → E

def prefixAppend {n : ℕ} (H : Prefix (E := E) n) (z : E) : Prefix (E := E) (n + 1) :=
  fun i => if hi : i.val ≤ n then H ⟨i.val, Finset.mem_Iic.mpr hi⟩ else z

@[fun_prop] theorem measurable_prefixAppend (n : ℕ) :
    Measurable (fun p : Prefix (E := E) n × E => prefixAppend p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.val ≤ n
  · simpa only [prefixAppend, dite_eq_left hi, Function.comp_def] using
      (measurable_pi_apply (⟨i.val, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp measurable_fst
  · simpa only [prefixAppend, dite_eq_right hi] using
      (measurable_snd : Measurable (Prod.snd : Prefix (E := E) n × E → E))

@[fun_prop] theorem measurable_prefixAppend_right {n : ℕ} (H : Prefix (E := E) n) :
    Measurable (prefixAppend H) :=
  (measurable_prefixAppend n).comp (measurable_const.prodMk measurable_id)

def suffixPrefix (n k : ℕ) (H : Prefix (E := E) (n + k)) : Prefix (E := E) k :=
  fun i => H ⟨n + i.val, Finset.mem_Iic.mpr
    (Nat.add_le_add_left (Finset.mem_Iic.mp i.property) n)⟩

@[fun_prop] theorem measurable_suffixPrefix (n k : ℕ) :
    Measurable (suffixPrefix (E := E) n k) := by
  exact measurable_pi_iff.mpr fun _ => measurable_pi_apply _

omit [MeasurableSpace E] in
theorem suffixPrefix_append (n k : ℕ) (H : Prefix (E := E) (n + k)) (z : E) :
    suffixPrefix n (k + 1) (prefixAppend H z) = prefixAppend (suffixPrefix n k H) z := by
  funext i
  by_cases hi : i.val ≤ k
  · have hni : n + i.val ≤ n + k := Nat.add_le_add_left hi n
    simp only [suffixPrefix, prefixAppend, dite_eq_left hi]
    exact dite_eq_left hni
  · have hni : ¬n + i.val ≤ n + k := by omega
    simp only [suffixPrefix, prefixAppend, dite_eq_right hi]
    exact dite_eq_right hni

theorem partialTraj_one_step (α : Kernel E E) [IsMarkovKernel α] (n : ℕ)
    (H : Prefix (E := E) n) :
    Kernel.partialTraj (X := fun _ => E) (historyKernel α) n (n + 1) H =
      (α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend H) := by
  have hg : Measurable (IicProdIoc (X := fun _ => E) n (n + 1)) := measurable_IicProdIoc
  have hp := (MeasurableEquiv.piSingleton (X := fun _ => E) n).measurable
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

@[fun_prop] theorem measurable_appended_transition (α : Kernel E E) [IsMarkovKernel α]
    (n : ℕ) : Measurable (fun q : Prefix (E := E) n =>
      (α (q ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend q)) := by
  have he : (fun q : Prefix (E := E) n =>
      (α (q ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend q)) =
      Kernel.partialTraj (X := fun _ => E) (historyKernel α) n (n + 1) :=
    funext fun q => (partialTraj_one_step α n q).symm
  rw [he]
  exact Kernel.measurable _

theorem partialTraj_successor (α : Kernel E E) [IsMarkovKernel α]
    {a b : ℕ} (hab : a ≤ b) (H : Prefix (E := E) a) :
    Kernel.partialTraj (X := fun _ => E) (historyKernel α) a (b + 1) H =
      (Kernel.partialTraj (X := fun _ => E) (historyKernel α) a b H).bind
        (fun q => (α (q ⟨b, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend q)) := by
  rw [Kernel.partialTraj_succ_eq_comp hab, Kernel.comp_apply]
  congr 1
  funext q
  exact partialTraj_one_step α b q

theorem partialTraj_suffixPrefix (α : Kernel E E) [IsMarkovKernel α]
    (n k : ℕ) (H : Prefix (E := E) n) :
    (Kernel.partialTraj (X := fun _ => E) (historyKernel α) n (n + k) H).map
      (suffixPrefix n k) =
    Kernel.partialTraj (X := fun _ => E) (historyKernel α) 0 k
      (fun _ => H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, Kernel.partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_suffixPrefix n 0)]
      congr 1
      funext i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.property; omega
      simp only [suffixPrefix, hi, Nat.add_zero]
  | succ k ih =>
      change (Kernel.partialTraj (X := fun _ => E) (historyKernel α) n ((n + k) + 1) H).map
        (suffixPrefix n (k + 1)) = _
      rw [partialTraj_successor α (Nat.le_add_right n k),
        Measure.map_bind (measurable_appended_transition α (n + k)).aemeasurable
          (measurable_suffixPrefix n (k + 1)).aemeasurable]
      calc
        _ = (Kernel.partialTraj (X := fun _ => E) (historyKernel α) n (n + k) H).bind
            (fun q => (α ((suffixPrefix n k q) ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map
              (prefixAppend (suffixPrefix n k q))) := by
          congr 1
          funext q
          rw [Measure.map_map (measurable_suffixPrefix n (k + 1))
            (measurable_prefixAppend_right q)]
          congr 1
          funext z
          exact suffixPrefix_append n k q z
        _ = ((Kernel.partialTraj (X := fun _ => E) (historyKernel α) n (n + k) H).map
            (suffixPrefix n k)).bind
            (fun q => (α (q ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend q)) := by
          rw [Measure.bind_map (measurable_suffixPrefix n k).aemeasurable
            (measurable_appended_transition α k).aemeasurable]
        _ = _ := by
          rw [ih, partialTraj_successor α (Nat.zero_le k)]


def shift (n : ℕ) (H : ℕ → E) : ℕ → E := fun k => H (n + k)

@[fun_prop] theorem measurable_shift (n : ℕ) : Measurable (shift (E := E) n) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- The entire future of the actual continuation, starting at its current
state, has the original Markov-chain law. -/
theorem traj_map_shift (α : Kernel E E) [IsMarkovKernel α] (n : ℕ)
    (H : Prefix (E := E) n) :
    (Kernel.traj (X := fun _ => E) (historyKernel α) n H).map (shift n) =
      fullLaw α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  let H₀ : Prefix (E := E) 0 := fun _ => H ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hp := Kernel.isProjectiveLimit_trajFun (X := fun _ => E) (historyKernel α) 0 H₀
  have hfamily := Kernel.isProjectiveMeasureFamily_partialTraj
    (X := fun _ => E) (historyKernel α) H₀
  have htarget : IsProjectiveLimit
      ((Kernel.traj (X := fun _ => E) (historyKernel α) n H).map (shift n))
      (inducedFamily (X := fun _ => E) (fun k => Kernel.partialTraj (X := fun _ => E)
        (historyKernel α) 0 k H₀)) := by
    rw [isProjectiveLimit_nat_iff hfamily]
    intro k
    rw [inducedFamily_Iic,
      Measure.map_map (by fun_prop) (measurable_shift n)]
    have he : (Preorder.frestrictLe k) ∘ shift (E := E) n =
        (suffixPrefix n k) ∘ (Preorder.frestrictLe (n + k)) := rfl
    rw [he, ← Measure.map_map (measurable_suffixPrefix n k) (by fun_prop),
      Kernel.traj_map_frestrictLe_apply, partialTraj_suffixPrefix]
  have : ∀ k, IsProbabilityMeasure
      (Kernel.partialTraj (X := fun _ => E) (historyKernel α) 0 k H₀) := fun _ => inferInstance
  have : ∀ I : Finset ℕ, IsFiniteMeasure
      (inducedFamily (X := fun _ => E) (fun k =>
        Kernel.partialTraj (X := fun _ => E) (historyKernel α) 0 k H₀) I) :=
    fun _ => inferInstance
  exact htarget.unique hp

noncomputable def futureKernel (α : Kernel E E) [IsMarkovKernel α] (n : ℕ) :
    Kernel (Prefix (E := E) n) (ℕ → E) :=
  (Kernel.traj (X := fun _ => E) (historyKernel α) 0).comap
    (fun H _ => H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance futureKernel_markov (α : Kernel E E) [IsMarkovKernel α] (n : ℕ) :
    IsMarkovKernel (futureKernel α n) := by unfold futureKernel; infer_instance

theorem futureKernel_apply (α : Kernel E E) [IsMarkovKernel α] (n : ℕ)
    (H : Prefix (E := E) n) :
    futureKernel α n H = fullLaw α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl

theorem traj_map_shift_kernel (α : Kernel E E) [IsMarkovKernel α] (n : ℕ) :
    (Kernel.traj (X := fun _ => E) (historyKernel α) n).map (shift n) =
      futureKernel α n := by
  ext H : 1
  rw [Kernel.map_apply _ (measurable_shift n), futureKernel_apply]
  exact traj_map_shift α n H

/-- The exact joint past/future law. In particular, the future kernel
conditioned on the complete prefix is the original law from its last state. -/
theorem map_prefix_shift (α : Kernel E E) [IsMarkovKernel α] (x : E) (n : ℕ) :
    (fullLaw α x).map (fun H => (Preorder.frestrictLe n H, shift n H)) =
      ((fullLaw α x).map (Preorder.frestrictLe n)) ⊗ₘ futureKernel α n := by
  rw [← traj_map_shift_kernel, map_prefix, Measure.compProd_map (measurable_shift n),
    Kernel.partialTraj_compProd_traj (Nat.zero_le n),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A measurable property holding almost surely from every starting state
also holds for the actual future after any deterministic time. -/
theorem fullLaw_ae_shift (α : Kernel E E) [IsMarkovKernel α] (x : E) (n : ℕ)
    (P : E → (ℕ → E) → Prop) (hP : MeasurableSet {q : E × (ℕ → E) | P q.1 q.2})
    (hp : ∀ z, ∀ᵐ H ∂fullLaw α z, P z H) :
    ∀ᵐ H ∂fullLaw α x, P (H n) (shift n H) := by
  have hm : MeasurableSet {q : Prefix (E := E) n × (ℕ → E) |
      P (q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) q.2} :=
    hP.preimage (show Measurable (fun q : Prefix (E := E) n × (ℕ → E) =>
      (q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, q.2)) by fun_prop)
  have hh : ∀ᵐ q ∂((fullLaw α x).map (Preorder.frestrictLe n)) ⊗ₘ futureKernel α n,
      P (q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) q.2 := by
    apply Measure.ae_compProd_of_ae_ae hm
    exact Eventually.of_forall fun H => hp (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  rw [← map_prefix_shift] at hh
  exact ae_of_ae_map (μ := fullLaw α x)
    (f := fun H => (Preorder.frestrictLe n H, shift n H)) (by fun_prop) hh

end Freezing1.CountableMarkovChain
