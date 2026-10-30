module

public import Freezing1.LocalTreeChildren
public import Freezing1.PlaneTreeGeometry

/-!
# Ordering by birth time and forgetting labels

At each vertex, child indices are the positions in the increasing list of
actual child birth IDs. Following these indices defines the canonical plane
offspring coordinates. Every coordinate depends locally on finitely many
labelled balls, so the ordering-and-forgetting map is continuous.
-/

@[expose] public section

namespace Freezing1.LocalTree

open Filter
open scoped Topology Classical

noncomputable def follow (T : Tree) (v : ℕ) : PlaneTree.Address → Option ℕ
  | [] => some v
  | j :: u => if j = 0 then none else
      ((childList T v)[j - 1]?).bind (fun w => follow T w u)

theorem follow_append (T : Tree) (v : ℕ) (u w : PlaneTree.Address) :
    follow T v (u ++ w) = (follow T v u).bind (fun z => follow T z w) := by
  induction u generalizing v with
  | nil => rfl
  | cons j u ih =>
    simp only [List.cons_append, follow]
    by_cases hj : j = 0
    · simp [hj]
    · cases hz : (childList T v)[j - 1]? <;> simp [hj, ih]

noncomputable def planeOffspring (T : Tree) (u : PlaneTree.Address) : ℕ :=
  match follow T 0 u with
  | none => 0
  | some v => (childIDs T v).card

theorem canonical_planeOffspring (T : Tree) : PlaneTree.Canonical (planeOffspring T) := by
  intro u j hj
  cases hu : follow T 0 u with
  | none => simp [planeOffspring, follow_append, hu]
  | some v =>
    simp only [planeOffspring, hu] at hj
    by_cases hj0 : j = 0
    · simp [planeOffspring, follow_append, hu, follow, hj0]
    · have hidx : (childList T v).length ≤ j - 1 := by
        rw [length_childList]
        omega
      simp [planeOffspring, follow_append, hu, follow, hj0, List.getElem?_eq_none hidx]

noncomputable def toPlaneTree (T : Tree) : PlaneTree.Tree :=
  ⟨planeOffspring T, canonical_planeOffspring T⟩

theorem degree_toPlaneTree (T : Tree) :
    PlaneTree.degree (toPlaneTree T) = (childIDs T 0).card := rfl

theorem recordAt_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (v : ℕ) :
    ∀ᶠ i in l, recordAt (S i) v = recordAt T v :=
  (hc v).mono fun _ h => congrArg (fun B => findRecord B v) h

theorem childIDs_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (v : ℕ) :
    ∀ᶠ i in l, childIDs (S i) v = childIDs T v := by
  cases hr : recordAt T v with
  | none =>
    filter_upwards [recordAt_eventually_eq hc v] with i hi
    simp only [childIDs, hi, hr]
  | some r =>
    filter_upwards [recordAt_eventually_eq hc v, hc (r.height + 1)] with i hi hb
    simp only [childIDs, hi, hr, hb]

theorem childList_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (v : ℕ) :
    ∀ᶠ i in l, childList (S i) v = childList T v :=
  (childIDs_eventually_eq hc v).mono fun _ h => congrArg (fun V : Finset ℕ => V.sort (· ≤ ·)) h

theorem follow_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (v : ℕ) (u : PlaneTree.Address) :
    ∀ᶠ i in l, follow (S i) v u = follow T v u := by
  induction u generalizing v with
  | nil => exact Eventually.of_forall fun _ => rfl
  | cons j u ih =>
    by_cases hj : j = 0
    · subst j
      exact Eventually.of_forall fun _ => by simp [follow]
    · cases hw : (childList T v)[j - 1]? with
      | none =>
        filter_upwards [childList_eventually_eq hc v] with i hi
        simp [follow, hi, hj, hw]
      | some w =>
        filter_upwards [childList_eventually_eq hc v, ih w] with i hi hw'
        simp [follow, hi, hj, hw, hw']

theorem planeOffspring_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (u : PlaneTree.Address) :
    ∀ᶠ i in l, planeOffspring (S i) u = planeOffspring T u := by
  cases hu : follow T 0 u with
  | none =>
    filter_upwards [follow_eventually_eq hc 0 u] with i hi
    simp only [planeOffspring, hi, hu]
  | some v =>
    filter_upwards [follow_eventually_eq hc 0 u, childIDs_eventually_eq hc v] with i hi hv
    simp only [planeOffspring, hi, hu, hv]

theorem tendsto_toPlaneTree {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hS : Tendsto S l (𝓝 T)) :
    Tendsto (fun i => toPlaneTree (S i)) l (𝓝 (toPlaneTree T)) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro u
  rw [nhds_discrete, tendsto_pure]
  exact planeOffspring_eventually_eq ((tendsto_iff_balls S T).mp hS) u

theorem continuous_toPlaneTree : Continuous toPlaneTree := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact tendsto_toPlaneTree (S := id) (l := 𝓝 T) tendsto_id

end Freezing1.LocalTree
