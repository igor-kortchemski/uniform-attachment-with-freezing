module

public import Freezing1.FiniteFullBinaryTrees
public import Mathlib.Tactic.DeriveCountable
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Arbitrarily labelled finite unordered trees and their truncations

Sibling permutation is quotiented without any distinctness, increasing
label or chronology restriction. The representative fiber of each finite
unordered tree is proved finite, for the later compact realization step.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

deriving instance Countable for FullBinary

instance : Countable Rooted := rawEquiv.injective.countable

def Rooted.truncate : ℕ → Rooted → Rooted
  | 0, .node label _ => .node label []
  | h + 1, .node label children =>
      .node label (children.map (fun p => (p.1, truncate h p.2)))

@[simp] theorem Rooted.truncate_zero (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).truncate 0 = .node label [] := rfl

@[simp] theorem Rooted.truncate_succ (h : ℕ) (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).truncate (h + 1) =
      .node label (children.map (fun p => (p.1, p.2.truncate h))) := rfl

theorem Rooted.truncate_truncate (h H : ℕ) (hh : h ≤ H) (t : Rooted) :
    (t.truncate H).truncate h = t.truncate h := by
  induction h generalizing H t with
  | zero => cases H <;> cases t <;> rfl
  | succ h ih =>
    cases H with
    | zero => omega
    | succ H =>
      cases t with
      | node label children =>
        simp only [truncate_succ, List.map_map]
        apply congrArg (Rooted.node label)
        apply List.map_congr_left
        intro p _
        change (p.1, (p.2.truncate H).truncate h) = (p.1, p.2.truncate h)
        rw [ih H (by omega) p.2]

theorem Rooted.UnorderedEq.truncate {s t : Rooted} (he : s.UnorderedEq t) (h : ℕ) :
    (s.truncate h).UnorderedEq (t.truncate h) := by
  induction he generalizing h with
  | refl t => exact .refl _
  | symm he ih => exact .symm (ih h)
  | trans he1 he2 ih1 ih2 => exact .trans (ih1 h) (ih2 h)
  | perm label hp =>
    cases h with
    | zero => exact .refl _
    | succ h => exact .perm label (hp.map (fun p => (p.1, p.2.truncate h)))
  | child label edge before after he ih =>
    cases h with
    | zero => exact .refl _
    | succ h =>
      simpa only [Rooted.truncate_succ, List.map_append, List.map_cons] using
        (Rooted.UnorderedEq.child label edge
          (before.map (fun p => (p.1, p.2.truncate h)))
          (after.map (fun p => (p.1, p.2.truncate h))) (ih h))

end Freezing1.BinaryBijection

namespace Freezing1.UnorderedLocal

open BinaryBijection
open scoped Classical

abbrev FiniteTree := Quotient Rooted.unorderedSetoid

instance : Countable FiniteTree := inferInstance
instance : TopologicalSpace FiniteTree := ⊥
instance : DiscreteTopology FiniteTree := ⟨rfl⟩
instance : PolishSpace FiniteTree := inferInstance

def ofRooted (t : Rooted) : FiniteTree := Quotient.mk Rooted.unorderedSetoid t

theorem ofRooted_eq_iff (s t : Rooted) : ofRooted s = ofRooted t ↔ s.UnorderedEq t := Quotient.eq

def truncate (h : ℕ) : FiniteTree → FiniteTree :=
  Quotient.map (Rooted.truncate h) (fun _ _ he => he.truncate h)

@[simp] theorem truncate_ofRooted (h : ℕ) (t : Rooted) :
    truncate h (ofRooted t) = ofRooted (t.truncate h) := rfl

theorem truncate_truncate (h H : ℕ) (hh : h ≤ H) (q : FiniteTree) :
    truncate h (truncate H q) = truncate h q := by
  refine Quotient.inductionOn q (fun t => ?_)
  change ofRooted ((t.truncate H).truncate h) = ofRooted (t.truncate h)
  rw [Rooted.truncate_truncate h H hh]

abbrev Representative (q : FiniteTree) := {t : Rooted // ofRooted t = q}

instance representative_finite (q : FiniteTree) : Finite (Representative q) := by
  refine Quotient.inductionOn q (fun t => ?_)
  let A := t.labels.toFinset
  let N := 2 * t.vertexCount - 1
  let f : Representative (ofRooted t) → {b : FullBinary // b.vertexCount = N ∧ b.LabelsIn A} :=
    fun s => ⟨phi s.val, by
      have hs := (ofRooted_eq_iff s.val t).mp s.property
      constructor
      · rw [phi_vertexCount, hs.data_eq.1]
      · intro label hl
        rw [phi_labels, hs.data_eq.2.2] at hl
        exact Multiset.mem_toFinset.mpr hl⟩
  apply Finite.of_injective f
  intro s u hh
  apply Subtype.ext
  apply rawEquiv.injective
  exact congrArg (fun b : {b : FullBinary // b.vertexCount = N ∧ b.LabelsIn A} => b.val) hh

noncomputable instance representative_fintype (q : FiniteTree) : Fintype (Representative q) :=
  Fintype.ofFinite _

instance representative_nonempty (q : FiniteTree) : Nonempty (Representative q) :=
  ⟨⟨q.out, Quotient.out_eq q⟩⟩

end Freezing1.UnorderedLocal
