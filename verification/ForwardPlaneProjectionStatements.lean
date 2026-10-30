module

import Freezing1.ForwardPlaneLaw

/-!
Independent source reconstruction for the finite chronological projection
used in T02 (source proof lines 978--1012). These examples deliberately
expand sibling ranks and the two projected finite sets. They do not claim
the still-open infinite-limit, split-kernel, or fairness conclusions of T02.
-/

open Freezing1 MeasureTheory
open scoped Classical

example (s : Forward.State) (u v : ℕ) (hv : v ∈ s.vertices) (hv0 : v ≠ 0)
    (hp : s.parent u = s.parent v) (huv : u < v) :
    (s.vertices.filter (fun w => w ≠ 0 ∧ s.parent w = s.parent u ∧ w ≤ u)).card <
      (s.vertices.filter (fun w => w ≠ 0 ∧ s.parent w = s.parent v ∧ w ≤ v)).card :=
  Forward.childRank_lt hv hv0 hp huv

example (n : ℕ) (s : Forward.State) (hs : Forward.ValidAt n s)
    (v : ℕ) (hv : v ∈ s.vertices) (hv0 : v ≠ 0) :
    Forward.planeAddress s v = Forward.planeAddress s (s.parent v) ++
      [(s.vertices.filter (fun w => w ≠ 0 ∧ s.parent w = s.parent v ∧ w ≤ v)).card] :=
  hs.planeAddress_nonroot hv hv0

example (n : ℕ) (s : Forward.State) (hs : Forward.ValidAt n s) :
    ∀ u ∈ s.vertices, ∀ v ∈ s.vertices,
      Forward.planeAddress s u = Forward.planeAddress s v → u = v :=
  fun _ hu _ hv he => hs.planeAddress_injective hu hv he

example (n : ℕ) (s : Forward.State) (hs : Forward.ValidAt n s)
    (v : ℕ) (hv : v ∈ s.vertices) :
    (Forward.planeAddress s v).length = s.height v :=
  hs.planeAddress_length hv

example (n : ℕ) (s : Forward.State) (hs : Forward.ValidAt n s)
    (sign : Bool) (v : ℕ) (hv : v ∈ s.vertices) :
    ({ vertices := (Forward.step s (n + 1) sign v).vertices.image
         (Forward.planeAddress (Forward.step s (n + 1) sign v))
       active := (Forward.step s (n + 1) sign v).active.image
         (Forward.planeAddress (Forward.step s (n + 1) sign v)) } : PlaneForward.State) =
      PlaneForward.step
        { vertices := s.vertices.image (Forward.planeAddress s),
          active := s.active.image (Forward.planeAddress s) }
        sign (Forward.planeAddress s v) :=
  Forward.toPlaneState_step hs sign hv

example (n : ℕ) (s : Forward.State) (hs : Forward.ValidAt n s)
    (p : unitInterval) :
    ((ForwardAnnealed.signLaw p).bind
      (fun sign => Forward.transitionLaw s (n + 1) sign)).map
      (fun z : Forward.State => ({ vertices := z.vertices.image (Forward.planeAddress z), active := z.active.image (Forward.planeAddress z) } : PlaneForward.State)) =
      (ForwardAnnealed.signLaw p).bind
        (PlaneForward.signedTransitionLaw
          { vertices := s.vertices.image (Forward.planeAddress s),
            active := s.active.image (Forward.planeAddress s) }) :=
  Forward.map_annealedTransition_toPlaneState hs p

example (p : unitInterval) :
    ∀ᵐ H ∂ForwardAnnealed.fullLaw p, ∀ n,
      PlaneForward.Valid
        { vertices := (H n).vertices.image (Forward.planeAddress (H n))
          active := (H n).active.image (Forward.planeAddress (H n)) } :=
  ForwardAnnealed.fullLaw_toPlaneState_valid p

example (p : unitInterval) (n : ℕ) :
    (ForwardAnnealed.treeLaw p n).map
      (fun s : Forward.State => ({ vertices := s.vertices.image (Forward.planeAddress s), active := s.active.image (Forward.planeAddress s) } : PlaneForward.State)) =
      (CountableMarkovChain.fullLaw (PlaneForward.transition p)
        { vertices := {[]}, active := {[]} }).map (fun H => H n) :=
  ForwardAnnealed.map_treeLaw_toPlaneState p n

#print axioms Freezing1.Forward.childRank
#print axioms Freezing1.Forward.childRank_lt
#print axioms Freezing1.Forward.planeAddress
#print axioms Freezing1.Forward.ValidAt.planeAddress_injective
#print axioms Freezing1.Forward.ValidAt.planeAddress_length
#print axioms Freezing1.Forward.State.toPlaneState
#print axioms Freezing1.Forward.toPlaneState_freeze
#print axioms Freezing1.Forward.planeAddress_attach_old
#print axioms Freezing1.Forward.planeAddress_child_iff
#print axioms Freezing1.Forward.toPlaneState_children
#print axioms Freezing1.Forward.toPlaneState_attach
#print axioms Freezing1.Forward.toPlaneState_step
#print axioms Freezing1.Forward.map_transitionLaw_toPlaneState
#print axioms Freezing1.Forward.map_annealedTransition_toPlaneState
#print axioms Freezing1.ForwardAnnealed.fullLaw_toPlaneState_valid
#print axioms Freezing1.ForwardAnnealed.map_treeLaw_toPlaneState
