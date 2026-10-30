module

public import Freezing1.PlaneTreeLocalTopology
public import Mathlib.Topology.Clopen
public import Mathlib.Tactic.DeriveCountable

/-!
# Locally finite plane trees with arbitrary countable discrete labels

The shape is the existing Ulam--Harris plane tree. Present vertices carry
vertex labels; present nonroot vertices carry incoming-edge labels. Absent
addresses have empty slots, so the coordinate topology has no fictitious
labels outside the tree. Labels need not be distinct or chronological.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

open Filter Set
open scoped Topology Classical

variable {V E : Type*}

/-- The extra `none` denotes an absent address, even when the actual vertex
alphabet itself contains an active-symbol option. -/
structure LabelSlot (L : Type*) where
  label : Option L
  deriving DecidableEq, Countable

instance (L : Type*) : TopologicalSpace (LabelSlot L) := ⊥
instance (L : Type*) : DiscreteTopology (LabelSlot L) := ⟨rfl⟩
instance (L : Type*) [Countable L] : PolishSpace (LabelSlot L) := inferInstance

def emptySlot (L : Type*) : LabelSlot L := ⟨none⟩

theorem LabelSlot.eq_empty_iff (s : LabelSlot V) :
    s = emptySlot V ↔ s.label.isSome = false := by
  cases s with
  | mk label => cases label <;> simp [emptySlot]

theorem isClopen_present (u : PlaneTree.Address) :
    IsClopen {T : PlaneTree.Tree | PlaneTree.Present T u} := by
  induction u with
  | nil => simpa only [PlaneTree.present_nil, Set.ofPred_true] using isClopen_univ
  | cons j u ih =>
    have hdegree : IsClopen {T : PlaneTree.Tree | 1 ≤ j ∧ j ≤ PlaneTree.degree T} :=
      (isClopen_discrete (s := {k : ℕ | 1 ≤ j ∧ j ≤ k})).preimage PlaneTree.continuous_degree
    have hchild := ih.preimage (PlaneTree.continuous_child j)
    simpa only [PlaneTree.present_cons, Set.ofPred_and, Set.preimage_ofPred_eq,
      Set.inter_assoc] using hdegree.inter hchild

noncomputable def presence (T : PlaneTree.Tree) (u : PlaneTree.Address) : Bool :=
  decide (PlaneTree.Present T u)

theorem continuous_presence (u : PlaneTree.Address) :
    Continuous (fun T : PlaneTree.Tree => presence T u) := by
  apply (continuous_bool_rng true).mpr
  simpa only [presence, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    using isClopen_present u

noncomputable def edgePresence (T : PlaneTree.Tree) (u : PlaneTree.Address) : Bool :=
  if u = [] then false else presence T u

theorem continuous_edgePresence (u : PlaneTree.Address) :
    Continuous (fun T : PlaneTree.Tree => edgePresence T u) := by
  by_cases hu : u = []
  · simpa only [edgePresence, ite_eq_left hu] using (continuous_const : Continuous (fun _ : PlaneTree.Tree => false))
  · simpa only [edgePresence, ite_eq_right hu] using continuous_presence u

abbrev RawTree (V E : Type*) :=
  PlaneTree.Tree × (PlaneTree.Address → LabelSlot V) × (PlaneTree.Address → LabelSlot E)

def Valid (p : RawTree V E) : Prop :=
  ∀ u, (p.2.1 u).label.isSome = presence p.1 u ∧
    (p.2.2 u).label.isSome = edgePresence p.1 u

theorem isClosed_valid (V E : Type*) : IsClosed {p : RawTree V E | Valid p} := by
  have hset : {p : RawTree V E | Valid p} = ⋂ u, {p : RawTree V E |
      (p.2.1 u).label.isSome = presence p.1 u ∧
      (p.2.2 u).label.isSome = edgePresence p.1 u} := by
    ext p
    simp only [Valid, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply isClosed_iInter
  intro u
  have hv : Continuous (fun p : RawTree V E => (p.2.1 u).label.isSome) :=
    (continuous_of_discreteTopology : Continuous (fun s : LabelSlot V => s.label.isSome)).comp
      ((continuous_apply u).comp (continuous_fst.comp continuous_snd))
  have he : Continuous (fun p : RawTree V E => (p.2.2 u).label.isSome) :=
    (continuous_of_discreteTopology : Continuous (fun s : LabelSlot E => s.label.isSome)).comp
      ((continuous_apply u).comp (continuous_snd.comp continuous_snd))
  exact (isClosed_eq hv ((continuous_presence u).comp continuous_fst)).inter
    (isClosed_eq he ((continuous_edgePresence u).comp continuous_fst))

abbrev Tree (V E : Type*) := {p : RawTree V E // Valid p}

instance [Countable V] [Countable E] : PolishSpace (Tree V E) :=
  (isClosed_valid V E).polishSpace

def shape (T : Tree V E) : PlaneTree.Tree := T.val.1
def vertexSlot (T : Tree V E) (u : PlaneTree.Address) : LabelSlot V := T.val.2.1 u
def edgeSlot (T : Tree V E) (u : PlaneTree.Address) : LabelSlot E := T.val.2.2 u

theorem vertexSlot_empty_of_absent (T : Tree V E) (u : PlaneTree.Address)
    (hu : ¬PlaneTree.Present (shape T) u) : vertexSlot T u = emptySlot V := by
  change ¬PlaneTree.Present T.val.1 u at hu
  apply (LabelSlot.eq_empty_iff _).mpr
  have hh := (T.property u).1
  simpa only [presence, shape, vertexSlot, decide_eq_false hu] using hh

theorem edgeSlot_empty_of_absent (T : Tree V E) (u : PlaneTree.Address)
    (hu : ¬PlaneTree.Present (shape T) u) : edgeSlot T u = emptySlot E := by
  change ¬PlaneTree.Present T.val.1 u at hu
  apply (LabelSlot.eq_empty_iff _).mpr
  have hh := (T.property u).2
  by_cases hroot : u = []
  · simpa only [edgeSlot, edgePresence, ite_eq_left hroot] using hh
  · simpa only [edgeSlot, edgePresence, ite_eq_right hroot, presence, shape, decide_eq_false hu] using hh

theorem root_edgeSlot (T : Tree V E) : edgeSlot T [] = emptySlot E := by
  apply (LabelSlot.eq_empty_iff _).mpr
  simpa [edgeSlot, edgePresence] using (T.property []).2

abbrev Ball (V E : Type*) := Finset (PlaneTree.Address × LabelSlot V × LabelSlot E)

noncomputable def ball (T : Tree V E) (h : ℕ) : Ball V E :=
  (PlaneTree.ball (shape T) h).image (fun u => (u, vertexSlot T u, edgeSlot T u))

theorem mem_ball (T : Tree V E) (h : ℕ) (u : PlaneTree.Address) (v : LabelSlot V) (e : LabelSlot E) :
    (u, v, e) ∈ ball T h ↔ PlaneTree.Present (shape T) u ∧ u.length ≤ h ∧
      vertexSlot T u = v ∧ edgeSlot T u = e := by
  simp only [ball, Finset.mem_image, PlaneTree.mem_ball, Prod.mk.injEq]
  constructor
  · rintro ⟨w, ⟨hw, hlen⟩, rfl, hv, he⟩
    exact ⟨hw, hlen, hv, he⟩
  · rintro ⟨hu, hlen, hv, he⟩
    exact ⟨u, ⟨hu, hlen⟩, rfl, hv, he⟩

theorem addresses_ball (T : Tree V E) (h : ℕ) :
    (ball T h).image Prod.fst = PlaneTree.ball (shape T) h := by
  simp only [ball, Finset.image_image, Function.comp_def, Finset.image_id']

theorem ball_restrict (T : Tree V E) {h H : ℕ} (hh : h ≤ H) :
    (ball T H).filter (fun r => r.1.length ≤ h) = ball T h := by
  ext ⟨u, v, e⟩
  simp only [Finset.mem_filter, mem_ball]
  constructor
  · rintro ⟨⟨hu, _, hv, he⟩, hlen⟩
    exact ⟨hu, hlen, hv, he⟩
  · rintro ⟨hu, hlen, hv, he⟩
    exact ⟨⟨hu, hlen.trans hh, hv, he⟩, hlen⟩

theorem tendsto_iff_coordinates {ι : Type*} {l : Filter ι} (S : ι → Tree V E) (T : Tree V E) :
    Tendsto S l (𝓝 T) ↔ Tendsto (fun i => shape (S i)) l (𝓝 (shape T)) ∧
      (∀ u, ∀ᶠ i in l, vertexSlot (S i) u = vertexSlot T u) ∧
      (∀ u, ∀ᶠ i in l, edgeSlot (S i) u = edgeSlot T u) := by
  rw [tendsto_subtype_rng, nhds_prod_eq, tendsto_prod_iff', nhds_prod_eq, tendsto_prod_iff']
  simp only [tendsto_pi_nhds, nhds_discrete, tendsto_pure, shape, vertexSlot, edgeSlot]

theorem ball_eventually_eq {ι : Type*} {l : Filter ι} (S : ι → Tree V E) (T : Tree V E)
    (hc : Tendsto S l (𝓝 T)) (h : ℕ) : ∀ᶠ i in l, ball (S i) h = ball T h := by
  obtain ⟨hs, hv, he⟩ := (tendsto_iff_coordinates S T).mp hc
  have hb := (PlaneTree.tendsto_iff_balls _ _).mp hs h
  have hd : ∀ᶠ i in l, ∀ u ∈ PlaneTree.ball (shape T) h,
      vertexSlot (S i) u = vertexSlot T u ∧ edgeSlot (S i) u = edgeSlot T u :=
    (eventually_all_finset _).mpr (fun u _ => (hv u).and (he u))
  filter_upwards [hb, hd] with i hi hdata
  unfold ball
  rw [hi]
  apply Finset.image_congr
  intro u hu
  dsimp only
  rw [(hdata u hu).1, (hdata u hu).2]

theorem slots_eventually_eq_of_balls {ι : Type*} {l : Filter ι} (S : ι → Tree V E) (T : Tree V E)
    (hc : ∀ h, ∀ᶠ i in l, ball (S i) h = ball T h) (u : PlaneTree.Address) :
    ∀ᶠ i in l, vertexSlot (S i) u = vertexSlot T u ∧ edgeSlot (S i) u = edgeSlot T u := by
  filter_upwards [hc u.length] with i hi
  by_cases hu : PlaneTree.Present (shape T) u
  · have hr : (u, vertexSlot T u, edgeSlot T u) ∈ ball T u.length :=
      (mem_ball _ _ _ _ _).mpr ⟨hu, le_rfl, rfl, rfl⟩
    rw [← hi] at hr
    exact (mem_ball _ _ _ _ _).mp hr |>.2.2
  · have hsi : ¬PlaneTree.Present (shape (S i)) u := by
      intro hpres
      have hr : (u, vertexSlot (S i) u, edgeSlot (S i) u) ∈ ball (S i) u.length :=
        (mem_ball _ _ _ _ _).mpr ⟨hpres, le_rfl, rfl, rfl⟩
      rw [hi] at hr
      exact hu ((mem_ball _ _ _ _ _).mp hr).1
    rw [vertexSlot_empty_of_absent _ _ hsi, vertexSlot_empty_of_absent _ _ hu,
      edgeSlot_empty_of_absent _ _ hsi, edgeSlot_empty_of_absent _ _ hu]
    exact ⟨rfl, rfl⟩

/-- The topology records the complete finite labelled truncation, including
the labels of boundary vertices and their incoming edges. -/
theorem tendsto_iff_balls {ι : Type*} {l : Filter ι} (S : ι → Tree V E) (T : Tree V E) :
    Tendsto S l (𝓝 T) ↔ ∀ h, ∀ᶠ i in l, ball (S i) h = ball T h := by
  constructor
  · exact fun hc h => ball_eventually_eq S T hc h
  · intro hc
    apply (tendsto_iff_coordinates S T).mpr
    refine ⟨(PlaneTree.tendsto_iff_balls _ _).mpr (fun h => ?_), ?_, ?_⟩
    · filter_upwards [hc h] with i hi
      simpa only [addresses_ball] using congrArg (Finset.image Prod.fst) hi
    · exact fun u => (slots_eventually_eq_of_balls S T hc u).mono (fun _ hh => hh.1)
    · exact fun u => (slots_eventually_eq_of_balls S T hc u).mono (fun _ hh => hh.2)

theorem tendsto_iff_positive_balls {ι : Type*} {l : Filter ι} (S : ι → Tree V E) (T : Tree V E) :
    Tendsto S l (𝓝 T) ↔ ∀ h, 1 ≤ h → ∀ᶠ i in l, ball (S i) h = ball T h := by
  rw [tendsto_iff_balls]
  constructor
  · exact fun hc h _ => hc h
  · intro hc h
    by_cases hh : 1 ≤ h
    · exact hc h hh
    · have hz : h = 0 := by omega
      subst h
      filter_upwards [hc 1 le_rfl] with i hi
      simpa only [ball_restrict _ (by omega : 0 ≤ 1)] using
        congrArg (Finset.filter (fun r => r.1.length ≤ 0)) hi

end Freezing1.PlaneLabelled
