module

public import Freezing1.SIRClockPopulation

/-!
# Labelled first-contact and recovery updates

An infection fixes the recipient's chronological address once and for all.
After forgetting individual labels, each legal update is exactly the existing
embedded infection-tree update.
-/

@[expose] public section

namespace Freezing1.SIR

open PlaneTree
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def infectPopulation {n : ℕ} (z : PopulationState n)
    (v w : Individual n) : PopulationState n :=
  ⟨z.susceptible.erase w, insert w z.active,
    Function.update z.address w (PlaneForward.newChild z.tree (z.address v)),
    PlaneForward.attach z.tree (z.address v)⟩

def recoverPopulation {n : ℕ} (z : PopulationState n) (v : Individual n) : PopulationState n :=
  ⟨z.susceptible, z.active.erase v, z.address,
    PlaneForward.freeze z.tree (z.address v)⟩

theorem infected_infectPopulation {n : ℕ} (z : PopulationState n) (v w : Individual n) :
    (infectPopulation z v w).infected = insert w z.infected := by
  ext a
  simp [PopulationState.infected, infectPopulation]
  tauto

theorem infected_recoverPopulation {n : ℕ} (z : PopulationState n) (v : Individual n) :
    (recoverPopulation z v).infected = z.infected := rfl

theorem infectPopulation_address_old {n : ℕ} {z : PopulationState n}
    {v w a : Individual n} (hw : w ∈ z.susceptible) (ha : a ∈ z.infected) :
    (infectPopulation z v w).address a = z.address a := by
  have haw : a ≠ w := by
    intro he
    subst a
    exact (Finset.mem_sdiff.mp ha).2 hw
  simp [infectPopulation, haw]

theorem infectPopulation_project {n : ℕ} {z : PopulationState n}
    {v w : Individual n} (hw : w ∈ z.susceptible) :
    (infectPopulation z v w).project = infectTreeState z.project (z.address v) := by
  simp [PopulationState.project, infectPopulation, infectTreeState,
    Finset.card_erase_of_mem hw]

theorem recoverPopulation_project {n : ℕ} (z : PopulationState n) (v : Individual n) :
    (recoverPopulation z v).project = recoverTreeState z.project (z.address v) := rfl

theorem PopulationState.Valid.infect_project_step {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v w : Individual n} (hv : v ∈ z.active) (hw : w ∈ z.susceptible) :
    (infectPopulation z v w).project = treeStep z.project true (z.address v) := by
  have hpos : 0 < z.susceptible.card := Finset.card_pos.mpr ⟨w, hw⟩
  simpa only [treeStep, PopulationState.project, hz.address_active hv,
    ↓reduceIte, hpos.ne'] using infectPopulation_project (v := v) hw

theorem PopulationState.Valid.recover_project_step {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v : Individual n} (hv : v ∈ z.active) :
    (recoverPopulation z v).project = treeStep z.project false (z.address v) := by
  simpa only [treeStep, PopulationState.project, hz.address_active hv,
    Bool.false_eq_true, ↓reduceIte]
    using recoverPopulation_project z v

theorem PopulationState.Valid.recover {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v : Individual n} (hv : v ∈ z.active) :
    (recoverPopulation z v).Valid := by
  constructor
  · exact hz.disjoint.mono_right (Finset.erase_subset _ _)
  · exact hz.root_infected
  · exact hz.root_address
  · exact hz.address_injective
  · exact hz.vertices_eq
  · change (z.active.erase v).image z.address = z.tree.active.erase (z.address v)
    rw [← hz.active_eq]
    ext a
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨w, ⟨hwv, hw⟩, he⟩
      refine ⟨?_, w, hw, he⟩
      intro hav
      exact hwv (hz.address_injective (hz.active_infected hw) (hz.active_infected hv)
        (he.trans hav))
    · rintro ⟨hav, w, hw, he⟩
      refine ⟨w, ⟨?_, hw⟩, he⟩
      intro hwv
      exact hav (hwv ▸ he.symm)
  · exact hz.tree_valid.freeze _

theorem PopulationState.Valid.infect {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v w : Individual n} (hv : v ∈ z.active) (hw : w ∈ z.susceptible) :
    (infectPopulation z v w).Valid := by
  have hnew : PlaneForward.newChild z.tree (z.address v) ∉ z.tree.vertices :=
    hz.tree_valid.newChild_not_mem (hz.tree_valid.active_subset (hz.address_active hv))
  have haddr : (infectPopulation z v w).address w =
      PlaneForward.newChild z.tree (z.address v) := by simp [infectPopulation]
  have hImgI : z.infected.image (infectPopulation z v w).address = z.tree.vertices := by
    calc
      _ = z.infected.image z.address := Finset.image_congr
        (fun a ha => infectPopulation_address_old (v := v) hw ha)
      _ = _ := hz.vertices_eq
  have hImgA : z.active.image (infectPopulation z v w).address = z.tree.active := by
    calc
      _ = z.active.image z.address := Finset.image_congr
        (fun a ha => infectPopulation_address_old (v := v) hw (hz.active_infected ha))
      _ = _ := hz.active_eq
  constructor
  · apply Finset.disjoint_left.mpr
    intro a hS hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact Finset.notMem_erase _ _ hS
    · exact Finset.disjoint_left.mp hz.disjoint (Finset.mem_of_mem_erase hS) hA
  · intro h
    exact hz.root_infected (Finset.mem_of_mem_erase h)
  · exact (infectPopulation_address_old (v := v) hw
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz.root_infected⟩)).trans hz.root_address
  · intro a ha b hb he
    change a ∈ (infectPopulation z v w).infected at ha
    change b ∈ (infectPopulation z v w).infected at hb
    rw [infected_infectPopulation] at ha hb
    by_cases haw : a = w
    · subst a
      by_cases hbw : b = w
      · exact hbw.symm
      · have hbOld := (Finset.mem_insert.mp hb).resolve_left hbw
        exfalso
        apply hnew
        rw [haddr, infectPopulation_address_old (v := v) hw hbOld] at he
        rw [he]
        exact hz.address_mem_vertices hbOld
    · have haOld := (Finset.mem_insert.mp ha).resolve_left haw
      by_cases hbw : b = w
      · subst b
        exfalso
        apply hnew
        rw [infectPopulation_address_old (v := v) hw haOld, haddr] at he
        rw [← he]
        exact hz.address_mem_vertices haOld
      · have hbOld := (Finset.mem_insert.mp hb).resolve_left hbw
        apply hz.address_injective haOld hbOld
        rw [← infectPopulation_address_old (v := v) hw haOld,
          ← infectPopulation_address_old (v := v) hw hbOld]
        exact he
  · rw [infected_infectPopulation, Finset.image_insert, haddr, hImgI]
    rfl
  · change (insert w z.active).image (infectPopulation z v w).address =
      (PlaneForward.attach z.tree (z.address v)).active
    rw [Finset.image_insert, haddr, hImgA]
    rfl
  · exact hz.tree_valid.attach (hz.address_active hv)

noncomputable def populationStep {n : ℕ} (z : PopulationState n)
    (c : ClockSlot n) : PopulationState n :=
  if c ∈ z.liveSlots then
    match c.2 with
    | none => recoverPopulation z c.1
    | some w => infectPopulation z c.1 w
  else z

theorem PopulationState.Valid.step {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) (c : ClockSlot n) : (populationStep z c).Valid := by
  unfold populationStep
  split_ifs with hc
  · rcases c with ⟨v, _ | w⟩
    · exact hz.recover ((recovery_mem_liveSlots z v).mp hc)
    · obtain ⟨hv, hw⟩ := (contact_mem_liveSlots z v w).mp hc
      exact hz.infect hv hw
  · exact hz

theorem PopulationState.Valid.step_project {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {c : ClockSlot n} (hc : c ∈ z.liveSlots) :
    (populationStep z c).project = treeStep z.project c.2.isSome (z.address c.1) := by
  rw [populationStep, ite_eq_left hc]
  rcases c with ⟨v, _ | w⟩
  · exact hz.recover_project_step ((recovery_mem_liveSlots z v).mp hc)
  · obtain ⟨hv, hw⟩ := (contact_mem_liveSlots z v w).mp hc
    exact hz.infect_project_step hv hw

theorem populationStep_of_active_empty {n : ℕ} {z : PopulationState n}
    (hz : z.active = ∅) (c : ClockSlot n) : populationStep z c = z := by
  have he : z.liveSlots = ∅ := by
    simp [PopulationState.liveSlots, hz]
  simp [populationStep, he]

theorem recoverPopulation_relevant_subset {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v : Individual n} (hv : v ∈ z.active) :
    (recoverPopulation z v).relevantSlots ⊆ z.relevantSlots.erase (v, none) := by
  have hsub : (recoverPopulation z v).relevantSlots ⊆ z.relevantSlots := by
    intro c hc
    rcases Finset.mem_union.mp hc with hL | hU
    · apply Finset.mem_union_left
      refine Finset.mem_product.mpr ⟨?_, (Finset.mem_product.mp hL).2⟩
      exact Finset.mem_of_mem_erase (Finset.mem_product.mp hL).1
    · exact Finset.mem_union_right _ hU
  have hnot : (v, none) ∉ (recoverPopulation z v).relevantSlots := by
    intro hc
    rcases Finset.mem_union.mp hc with hL | hU
    · have hactive := (recovery_mem_liveSlots (recoverPopulation z v) v).mp hL
      exact Finset.notMem_erase _ _ hactive
    · have hS := (mem_unusedSlots (recoverPopulation z v) (v, none)).mp hU
      exact Finset.disjoint_left.mp hz.disjoint hS hv
  intro c hc
  exact Finset.mem_erase.mpr ⟨fun he => hnot (he ▸ hc), hsub hc⟩

theorem infectPopulation_relevant_subset {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v w : Individual n} (hv : v ∈ z.active) (hw : w ∈ z.susceptible) :
    (infectPopulation z v w).relevantSlots ⊆ z.relevantSlots.erase (v, some w) := by
  have hsub : (infectPopulation z v w).relevantSlots ⊆ z.relevantSlots := by
    intro c hc
    rcases Finset.mem_union.mp hc with hL | hU
    · rcases c with ⟨a, _ | b⟩
      · have ha := (recovery_mem_liveSlots (infectPopulation z v w) a).mp hL
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_union_right _ ((mem_unusedSlots z (a, none)).mpr hw)
        · exact Finset.mem_union_left _ ((recovery_mem_liveSlots z a).mpr ha)
      · obtain ⟨ha, hb⟩ := (contact_mem_liveSlots (infectPopulation z v w) a b).mp hL
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_union_right _ ((mem_unusedSlots z (a, some b)).mpr hw)
        · exact Finset.mem_union_left _ ((contact_mem_liveSlots z a b).mpr
            ⟨ha, Finset.mem_of_mem_erase hb⟩)
    · exact Finset.mem_union_right _ ((mem_unusedSlots z c).mpr
        (Finset.mem_of_mem_erase ((mem_unusedSlots (infectPopulation z v w) c).mp hU)))
  have hnot : (v, some w) ∉ (infectPopulation z v w).relevantSlots := by
    intro hc
    rcases Finset.mem_union.mp hc with hL | hU
    · have hS := ((contact_mem_liveSlots (infectPopulation z v w) v w).mp hL).2
      exact Finset.notMem_erase _ _ hS
    · have hS := (mem_unusedSlots (infectPopulation z v w) (v, some w)).mp hU
      exact Finset.disjoint_left.mp hz.disjoint (Finset.mem_of_mem_erase hS) hv
  intro c hc
  exact Finset.mem_erase.mpr ⟨fun he => hnot (he ▸ hc), hsub hc⟩

theorem PopulationState.Valid.step_relevant_subset {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {c : ClockSlot n} (hc : c ∈ z.liveSlots) :
    (populationStep z c).relevantSlots ⊆ z.relevantSlots.erase c := by
  rw [populationStep, ite_eq_left hc]
  rcases c with ⟨v, _ | w⟩
  · exact recoverPopulation_relevant_subset hz ((recovery_mem_liveSlots z v).mp hc)
  · obtain ⟨hv, hw⟩ := (contact_mem_liveSlots z v w).mp hc
    exact infectPopulation_relevant_subset hz hv hw

end Freezing1.SIR
