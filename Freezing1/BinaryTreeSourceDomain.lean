module

public import Freezing1.IncreasingBinaryBijection

/-!
# The least-edge map on the source's unrestricted union

Canonical sibling order is determined by the distinct integer edge labels;
it is not a plane order chosen as extra source data. The unrestricted map
is well-defined, but no unrestricted binary bijection is claimed. The
bijection of increasing classes is `paperEquiv`.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def Rooted.Canonical : Rooted → Prop
  | .node _ [] => True
  | .node label ((edge, child) :: rest) =>
      child.Canonical ∧ (Rooted.node label rest).Canonical ∧ ∀ p ∈ rest, edge < p.1
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem Rooted.canonical_node_iff (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).Canonical ↔
      children.Pairwise (fun p q => p.1 < q.1) ∧ ∀ p ∈ children, p.2.Canonical := by
  induction children with
  | nil => simp [Rooted.Canonical]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    rw [Rooted.Canonical, ih, List.pairwise_cons]
    constructor
    · rintro ⟨hc, ⟨hs, hr⟩, hfirst⟩
      refine ⟨⟨hfirst, hs⟩, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with he | hp
      · simpa only [he] using hc
      · exact hr p hp
    · rintro ⟨⟨hfirst, hs⟩, hall⟩
      exact ⟨hall (edge, child) (by simp),
        ⟨hs, fun p hp => hall p (List.mem_cons_of_mem _ hp)⟩, hfirst⟩

theorem Rooted.canonical_of_increasing : ∀ t : Rooted, t.Increasing → t.Canonical
  | .node _ [] , _ => by simp [Rooted.Canonical]
  | .node label ((edge, child) :: rest), hi => by
      rw [Rooted.Increasing] at hi
      rw [Rooted.Canonical]
      exact ⟨canonical_of_increasing child hi.1,
        canonical_of_increasing (.node label rest) hi.2.1, hi.2.2.2.2⟩
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- The first list child is precisely the child selected by the source's
minimum incident-edge rule. -/
theorem Rooted.first_edge_least {label : Option ℕ} {edge : ℕ} {child : Rooted}
    {rest : List (ℕ × Rooted)} (hc : (Rooted.node label ((edge, child) :: rest)).Canonical) :
    ∀ p ∈ (edge, child) :: rest, edge ≤ p.1 := by
  rw [Rooted.Canonical] at hc
  intro p hp
  rcases List.mem_cons.mp hp with he | hp
  · simp only [he, le_refl]
  · exact (hc.2.2 p hp).le

theorem Rooted.first_edge_unique {label : Option ℕ} {edge : ℕ} {child : Rooted}
    {rest : List (ℕ × Rooted)} (hc : (Rooted.node label ((edge, child) :: rest)).Canonical)
    {p : ℕ × Rooted} (hp : p ∈ (edge, child) :: rest) (he : p.1 = edge) : p = (edge, child) := by
  rw [Rooted.Canonical] at hc
  rcases List.mem_cons.mp hp with hp | hp
  · exact hp
  · have hh := hc.2.2 p hp
    rw [he] at hh
    omega

def SourceRootedClass (k n : ℕ) (A : Finset ℕ) :=
  {t : Rooted // t.Canonical ∧ t.vertexCount = n ∧ t.activeCount = k ∧ t.labels = A.val}

def SourceBinaryClass (k n : ℕ) (A : Finset ℕ) :=
  {t : FullBinary // t.leafCount = n ∧ t.activeCount = k ∧ t.labels = A.val}

/-- The well-defined map on the entire unrestricted source union. Its
restriction to increasing trees is the proved bijection. -/
def sourcePhi (k n : ℕ) (A : Finset ℕ) : SourceRootedClass k n A → SourceBinaryClass k n A :=
  fun t => ⟨phi t.val, (phi_leafCount t.val).trans t.property.2.1,
    (phi_activeCount t.val).trans t.property.2.2.1, (phi_labels t.val).trans t.property.2.2.2⟩

def RootedClass.toSource {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) : SourceRootedClass k n A :=
  ⟨t.val, t.val.canonical_of_increasing t.property.1, t.property.2⟩

theorem sourcePhi_agrees_with_increasingEquiv {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    (sourcePhi k n A t.toSource).val = (increasingEquiv k n A t).val := rfl

end Freezing1.BinaryBijection
