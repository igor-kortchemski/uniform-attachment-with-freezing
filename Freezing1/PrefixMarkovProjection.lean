module

public import Freezing1.CountableMarkovShift

/-! Projecting a complete finite history and its next transition. -/

@[expose] public section

namespace Freezing1.PrefixProjection

open MeasureTheory ProbabilityTheory CountableMarkovChain

theorem partialTraj_one_step {D : Type*} [MeasurableSpace D]
    (K : (k : ℕ) → Kernel (Prefix (E := D) k) D) [∀ k, IsMarkovKernel (K k)]
    (k : ℕ) (P : Prefix (E := D) k) :
    Kernel.partialTraj (X := fun _ => D) K k (k + 1) P = (K k P).map (prefixAppend P) := by
  have hg : Measurable (IicProdIoc (X := fun _ => D) k (k + 1)) := measurable_IicProdIoc
  have hp := (MeasurableEquiv.piSingleton (X := fun _ => D) k).measurable
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

theorem partialTraj_succ_bind {D : Type*} [MeasurableSpace D]
    (K : (k : ℕ) → Kernel (Prefix (E := D) k) D) [∀ k, IsMarkovKernel (K k)]
    (z : D) (k : ℕ) :
    Kernel.partialTraj (X := fun _ => D) K 0 (k + 1) (fun _ => z) =
      (Kernel.partialTraj (X := fun _ => D) K 0 k (fun _ => z)).bind
        (fun P => (K k P).map (prefixAppend P)) := by
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le k), Kernel.comp_apply]
  congr 1
  funext P
  exact partialTraj_one_step K k P

theorem measurable_append_kernel {D : Type*} [MeasurableSpace D]
    (K : (k : ℕ) → Kernel (Prefix (E := D) k) D) [∀ k, IsMarkovKernel (K k)]
    (k : ℕ) : Measurable (fun P : Prefix (E := D) k => (K k P).map (prefixAppend P)) := by
  have he : (fun P : Prefix (E := D) k => (K k P).map (prefixAppend P)) =
      Kernel.partialTraj (X := fun _ => D) K k (k + 1) :=
    funext fun P => (partialTraj_one_step K k P).symm
  rw [he]
  exact Kernel.measurable _

variable {A B : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]

def mapPrefix (f : A → B) (k : ℕ) (P : Prefix (E := A) k) : Prefix (E := B) k :=
  fun i => f (P i)

omit [MeasurableSingletonClass B] [Countable B] in
theorem measurable_mapPrefix (f : A → B) (k : ℕ) : Measurable (mapPrefix f k) :=
  Measurable.of_eval fun i => (measurable_of_countable f).comp (measurable_pi_apply i)

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B] in
theorem mapPrefix_append (f : A → B) (k : ℕ) (P : Prefix (E := A) k) (z : A) :
    mapPrefix f (k + 1) (prefixAppend P z) = prefixAppend (mapPrefix f k P) (f z) := by
  funext i
  by_cases hi : i.val ≤ k
  · simp only [mapPrefix, prefixAppend, dite_eq_left hi]
  · simp only [mapPrefix, prefixAppend, dite_eq_right hi]

theorem map_extension_of_ae (f : A → B) (k : ℕ) (mu : Measure (Prefix (E := A) k))
    (L : A → Measure A) (R : B → Measure B)
    (h : ∀ᵐ P ∂mu, (L (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map f =
      R (f (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩))) :
    (mu.bind (fun P => (L (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend P))).map
        (mapPrefix f (k + 1)) =
      (mu.map (mapPrefix f k)).bind (fun Q =>
        (R (Q ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend Q)) := by
  rw [Measure.map_bind (measurable_of_countable _).aemeasurable
    (measurable_mapPrefix f (k + 1)).aemeasurable,
    Measure.bind_map (measurable_mapPrefix f k).aemeasurable
      (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [h] with P hP
  rw [Measure.map_map (measurable_mapPrefix f (k + 1)) (measurable_prefixAppend_right P)]
  have he : mapPrefix f (k + 1) ∘ prefixAppend P =
      prefixAppend (mapPrefix f k P) ∘ f := funext (mapPrefix_append f k P)
  rw [he, ← Measure.map_map (measurable_prefixAppend_right (mapPrefix f k P))
    (measurable_of_countable f), hP]
  rfl

end Freezing1.PrefixProjection
