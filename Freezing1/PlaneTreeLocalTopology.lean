module

public import Freezing1.PlaneTreeGeometry

/-!
# Offspring coordinates give the usual plane-tree local topology

Convergence in the closed product encoding is equivalent to eventual equality
of each complete finite radius ball. Offspring counts can be read from one
additional radius, so absent addresses introduce no extra topology.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open Filter
open scoped Topology Classical

theorem generation_eventually_eq {ι : Type*} {l : Filter ι}
    (S : ι → Tree) (T : Tree) (hc : ∀ u, ∀ᶠ i in l, (S i).val u = T.val u) (n : ℕ) :
    ∀ᶠ i in l, generation (S i) n = generation T n := by
  induction n generalizing S T with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ n ih =>
    have hall : ∀ᶠ i in l, ∀ j ∈ Finset.Icc 1 (degree T),
        generation (child (S i) j) n = generation (child T j) n := by
      apply (eventually_all_finset _).mpr
      intro j hj
      exact ih (fun i => child (S i) j) (child T j) (fun u => hc (j :: u))
    filter_upwards [hc [], hall] with i hi hchild
    have hd : degree (S i) = degree T := hi
    simp only [generation, hd]
    apply Finset.biUnion_congr rfl
    intro j hj
    rw [hchild j hj]

theorem ball_eventually_eq {ι : Type*} {l : Filter ι}
    (S : ι → Tree) (T : Tree) (hc : ∀ u, ∀ᶠ i in l, (S i).val u = T.val u) (h : ℕ) :
    ∀ᶠ i in l, ball (S i) h = ball T h := by
  have hall : ∀ᶠ i in l, ∀ n ∈ Finset.range (h + 1),
      generation (S i) n = generation T n :=
    (eventually_all_finset _).mpr fun n _ => generation_eventually_eq S T hc n
  filter_upwards [hall] with i hi
  exact Finset.biUnion_congr rfl hi

theorem ball_children (T : Tree) (u : Address) :
    (ball T (u.length + 1)).filter (fun w => ∃ j : ℕ, w = u ++ [j]) =
      (Finset.Icc 1 (T.val u)).image (fun j => u ++ [j]) := by
  ext w
  simp only [Finset.mem_filter, mem_ball, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hw, hlen⟩, j, rfl⟩
    have hj := (present_append_singleton T u j).mp hw
    exact ⟨j, ⟨hj.2.1, hj.2.2⟩, rfl⟩
  · rintro ⟨j, ⟨hj1, hjT⟩, rfl⟩
    have hu : Present T u := by
      by_contra hn
      have hz := not_present_offspring_zero T u hn
      omega
    exact ⟨⟨(present_append_singleton T u j).mpr ⟨hu, hj1, hjT⟩,
      by simp⟩, j, rfl⟩

theorem offspring_eq_card_ball_children (T : Tree) (u : Address) :
    T.val u = ((ball T (u.length + 1)).filter
      (fun w => ∃ j : ℕ, w = u ++ [j])).card := by
  rw [ball_children, Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact List.singleton_injective (List.append_right_injective u h)

/-- The product encoding has exactly the usual local topology of plane
trees, with finite balls in the Ulam--Harris address representation. -/
theorem tendsto_iff_balls {ι : Type*} {l : Filter ι} (S : ι → Tree) (T : Tree) :
    Tendsto S l (𝓝 T) ↔ ∀ h, ∀ᶠ i in l, ball (S i) h = ball T h := by
  have hcoord : Tendsto S l (𝓝 T) ↔ ∀ u, ∀ᶠ i in l, (S i).val u = T.val u := by
    rw [tendsto_subtype_rng, tendsto_pi_nhds]
    simp only [nhds_discrete, tendsto_pure]
  rw [hcoord]
  constructor
  · exact fun hc h => ball_eventually_eq S T hc h
  · intro hc u
    filter_upwards [hc (u.length + 1)] with i hi
    rw [offspring_eq_card_ball_children (S i) u, offspring_eq_card_ball_children T u, hi]

end Freezing1.PlaneTree
