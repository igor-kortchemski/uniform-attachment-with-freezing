module

public import Freezing1.RootedPlaneLabelledCoding
public import Freezing1.UnorderedCoherentBalls

/-!
# Reading finite rooted labelled truncations of an arbitrary plane tree

The labels are the source alphabets `Option Nat` and `Nat`; the generic
countable-alphabet plane topology remains in its separate earlier module.
The list order here is the actual plane order and is forgotten only by the
proved sibling-permutation quotient.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

open BinaryBijection
open scoped Classical

def childVertex (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (j : Fin ((shape T).val u.val)) : Vertex (shape T) :=
  ⟨u.val ++ [j.val + 1], (PlaneTree.present_append_singleton _ _ _).mpr
    ⟨u.property, by omega, by omega⟩⟩

def childEdge (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (j : Fin ((shape T).val u.val)) : Edge (shape T) :=
  ⟨(childVertex T u j).val, (childVertex T u j).property, by simp [childVertex]⟩

noncomputable def finiteRootedAt (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T)) : ℕ → Rooted
  | 0 => .node (vertexLabel T u) []
  | h + 1 => .node (vertexLabel T u) (List.ofFn (fun j : Fin ((shape T).val u.val) =>
      (edgeLabel T (childEdge T u j), finiteRootedAt T (childVertex T u j) h)))

@[simp] theorem finiteRootedAt_zero (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T)) :
    finiteRootedAt T u 0 = .node (vertexLabel T u) [] := rfl

@[simp] theorem finiteRootedAt_succ (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T)) (h : ℕ) :
    finiteRootedAt T u (h + 1) = .node (vertexLabel T u)
      (List.ofFn (fun j : Fin ((shape T).val u.val) =>
        (edgeLabel T (childEdge T u j), finiteRootedAt T (childVertex T u j) h))) := rfl

theorem finiteRootedAt_truncate (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (h H : ℕ) (hH : H ≤ h) :
    (finiteRootedAt T u h).truncate H = finiteRootedAt T u H := by
  induction H generalizing h u with
  | zero => cases h <;> rfl
  | succ H ih =>
    cases h with
    | zero => omega
    | succ h =>
      simp only [finiteRootedAt_succ, Rooted.truncate_succ, List.map_ofFn, Function.comp_def]
      apply congrArg (Rooted.node (vertexLabel T u))
      apply congrArg List.ofFn
      funext j
      exact Prod.ext rfl (ih (childVertex T u j) h (by omega))

noncomputable def finiteRooted (T : Tree (Option ℕ) ℕ) (h : ℕ) : Rooted :=
  finiteRootedAt T ⟨[], PlaneTree.present_nil _⟩ h

theorem finiteRooted_truncate (T : Tree (Option ℕ) ℕ) (h H : ℕ) (hH : H ≤ h) :
    (finiteRooted T h).truncate H = finiteRooted T H := finiteRootedAt_truncate T _ h H hH

theorem finiteRooted_coherent (T : Tree (Option ℕ) ℕ) (h : ℕ) :
    (finiteRooted T (h + 1)).truncate h = finiteRooted T h :=
  finiteRooted_truncate T _ _ (by omega)

noncomputable def toBallTower (T : Tree (Option ℕ) ℕ) : UnorderedLocal.BallTower :=
  ⟨fun h => UnorderedLocal.ofRooted (finiteRooted T h), fun h => by
    change UnorderedLocal.ofRooted ((finiteRooted T (h + 1)).truncate h) =
      UnorderedLocal.ofRooted (finiteRooted T h)
    rw [finiteRooted_coherent]⟩

end Freezing1.PlaneLabelled
