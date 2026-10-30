module

public import Freezing1.SIRTreeState

/-!
# Labelled finite populations for preassigned first-contact clocks

Individuals have fixed labels. Their chronological addresses record the
actual infection genealogy in the existing plane state. Clock coordinates
are fixed source/target slots: `none` is the source's recovery clock and
`some w` its first contact with individual `w`.
-/

@[expose] public section

namespace Freezing1.SIR

open PlaneTree
open scoped Classical

set_option backward.isDefEq.respectTransparency false

abbrev Individual (n : ℕ) := Fin (n + 1)
abbrev ClockSlot (n : ℕ) := Individual n × Option (Individual n)

structure PopulationState (n : ℕ) where
  susceptible : Finset (Individual n)
  active : Finset (Individual n)
  address : Individual n → Address
  tree : PlaneForward.State
  deriving DecidableEq, Countable

instance (n : ℕ) : MeasurableSpace (PopulationState n) := ⊤
instance (n : ℕ) : DiscreteMeasurableSpace (PopulationState n) := ⟨fun _ => trivial⟩

def PopulationState.infected {n : ℕ} (z : PopulationState n) : Finset (Individual n) :=
  Finset.univ \ z.susceptible

def PopulationState.project {n : ℕ} (z : PopulationState n) : TreeState :=
  ⟨z.susceptible.card, z.tree⟩

structure PopulationState.Valid {n : ℕ} (z : PopulationState n) : Prop where
  disjoint : Disjoint z.susceptible z.active
  root_infected : (0 : Individual n) ∉ z.susceptible
  root_address : z.address 0 = []
  address_injective : Set.InjOn z.address (z.infected : Set (Individual n))
  vertices_eq : z.infected.image z.address = z.tree.vertices
  active_eq : z.active.image z.address = z.tree.active
  tree_valid : PlaneForward.Valid z.tree

def initialPopulation (n : ℕ) : PopulationState n :=
  ⟨Finset.univ.erase 0, {0}, fun _ => [], PlaneForward.initial⟩

theorem infected_initialPopulation (n : ℕ) : (initialPopulation n).infected = {0} := by
  ext v
  simp [PopulationState.infected, initialPopulation]

theorem initialPopulation_valid (n : ℕ) : (initialPopulation n).Valid := by
  constructor
  · simp [initialPopulation]
  · simp [initialPopulation]
  · rfl
  · rw [infected_initialPopulation]
    intro v hv w hw _
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hv hw
    exact hv.trans hw.symm
  · rw [infected_initialPopulation]
    simp [initialPopulation, PlaneForward.initial]
  · simp [initialPopulation, PlaneForward.initial]
  · exact PlaneForward.initial_valid

theorem PopulationState.Valid.active_infected {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) : z.active ⊆ z.infected := by
  intro v hv
  apply Finset.mem_sdiff.mpr
  exact ⟨Finset.mem_univ v, fun hS => Finset.disjoint_left.mp hz.disjoint hS hv⟩

theorem PopulationState.Valid.address_mem_vertices {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v : Individual n} (hv : v ∈ z.infected) :
    z.address v ∈ z.tree.vertices := by
  rw [← hz.vertices_eq]
  exact Finset.mem_image_of_mem _ hv

theorem PopulationState.Valid.address_active {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v : Individual n} (hv : v ∈ z.active) :
    z.address v ∈ z.tree.active := by
  rw [← hz.active_eq]
  exact Finset.mem_image_of_mem _ hv

theorem PopulationState.Valid.vertices_card {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) : z.tree.vertices.card = z.infected.card := by
  rw [← hz.vertices_eq]
  apply Finset.card_image_iff.mpr
  exact hz.address_injective

theorem PopulationState.Valid.active_card {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) : z.tree.active.card = z.active.card := by
  rw [← hz.active_eq]
  apply Finset.card_image_iff.mpr
  intro v hv w hw he
  exact hz.address_injective (hz.active_infected hv) (hz.active_infected hw) he

theorem PopulationState.Valid.project_valid {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) : z.project.Valid n := by
  refine ⟨hz.tree_valid, ?_⟩
  change z.susceptible.card + z.tree.vertices.card = n + 1
  rw [hz.vertices_card]
  have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ z.susceptible)
  simpa only [PopulationState.infected, Finset.card_univ, Fintype.card_fin,
    Nat.add_comm] using hh

theorem project_initialPopulation (n : ℕ) :
    (initialPopulation n).project = initialTreeState n := by
  simp [initialPopulation, PopulationState.project, initialTreeState]

noncomputable def PopulationState.availableTargets {n : ℕ} (z : PopulationState n) :
    Finset (Option (Individual n)) := insert none (z.susceptible.image some)

noncomputable def PopulationState.liveSlots {n : ℕ} (z : PopulationState n) :
    Finset (ClockSlot n) := z.active ×ˢ z.availableTargets

noncomputable def PopulationState.unusedSlots {n : ℕ} (z : PopulationState n) :
    Finset (ClockSlot n) := z.susceptible ×ˢ Finset.univ

noncomputable def PopulationState.relevantSlots {n : ℕ} (z : PopulationState n) :
    Finset (ClockSlot n) := z.liveSlots ∪ z.unusedSlots

@[simp] theorem recovery_mem_liveSlots {n : ℕ} (z : PopulationState n) (v : Individual n) :
    (v, none) ∈ z.liveSlots ↔ v ∈ z.active := by
  simp [PopulationState.liveSlots, PopulationState.availableTargets]

@[simp] theorem contact_mem_liveSlots {n : ℕ} (z : PopulationState n)
    (v w : Individual n) :
    (v, some w) ∈ z.liveSlots ↔ v ∈ z.active ∧ w ∈ z.susceptible := by
  simp [PopulationState.liveSlots, PopulationState.availableTargets]

@[simp] theorem mem_unusedSlots {n : ℕ} (z : PopulationState n) (c : ClockSlot n) :
    c ∈ z.unusedSlots ↔ c.1 ∈ z.susceptible := by
  simp [PopulationState.unusedSlots]

theorem PopulationState.Valid.live_disjoint_unused {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) : Disjoint z.liveSlots z.unusedSlots := by
  apply Finset.disjoint_left.mpr
  intro c hL hU
  exact Finset.disjoint_left.mp hz.disjoint (mem_unusedSlots z c |>.mp hU)
    (Finset.mem_product.mp hL).1

theorem liveSlots_nonempty_iff {n : ℕ} (z : PopulationState n) :
    z.liveSlots.Nonempty ↔ z.active.Nonempty := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.1, (Finset.mem_product.mp hc).1⟩
  · rintro ⟨v, hv⟩
    exact ⟨(v, none), (recovery_mem_liveSlots z v).mpr hv⟩

theorem availableTargets_card {n : ℕ} (z : PopulationState n) :
    z.availableTargets.card = z.susceptible.card + 1 := by
  rw [PopulationState.availableTargets, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective (Individual n))]

theorem liveSlots_card {n : ℕ} (z : PopulationState n) :
    z.liveSlots.card = z.active.card * (z.susceptible.card + 1) := by
  simpa only [PopulationState.liveSlots, availableTargets_card] using
    Finset.card_product z.active z.availableTargets

def clockSlotRate {n : ℕ} (r : ℝ) (c : ClockSlot n) : ℝ :=
  c.2.elim 1 (fun _ => r)

theorem clockSlotRate_pos {n : ℕ} {r : ℝ} (hr : 0 < r) (c : ClockSlot n) :
    0 < clockSlotRate r c := by
  rcases c with ⟨v, _ | w⟩ <;> simp [clockSlotRate, hr]

theorem sum_clockSlotRate_live {n : ℕ} (r : ℝ) (z : PopulationState n) :
    (∑ c ∈ z.liveSlots, clockSlotRate r c) =
      (z.active.card : ℝ) * (1 + r * z.susceptible.card) := by
  have hrow : ∀ v : Individual n,
      (∑ q ∈ z.availableTargets, clockSlotRate r (v, q)) =
        1 + r * z.susceptible.card := by
    intro v
    rw [PopulationState.availableTargets, Finset.sum_insert (by simp), Finset.sum_image]
    · simp only [clockSlotRate, Option.elim_none, Option.elim_some,
        Finset.sum_const, nsmul_eq_mul]
      ring
    · intro a _ b _ he
      exact Option.some.inj he
  change (∑ c ∈ z.active ×ˢ z.availableTargets, clockSlotRate r c) = _
  rw [Finset.sum_product]
  simp_rw [hrow]
  simp only [Finset.sum_const, nsmul_eq_mul]

theorem sum_clockSlotRate_live_pos {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z : PopulationState n) (ha : z.active.Nonempty) :
    0 < ∑ c ∈ z.liveSlots, clockSlotRate r c := by
  rw [sum_clockSlotRate_live]
  have hc : (0 : ℝ) < z.active.card := by exact_mod_cast ha.card_pos
  positivity

end Freezing1.SIR
