module

public import Freezing1.RootedForest

/-!
# Parent maps determine finite rooted forests

The root and depth on actual vertices are forced by the parent pointers and
the rooted-forest invariants. Equality outside the finite carrier must be
supplied separately when comparing the full functional representation.
-/

@[expose] public section

namespace Freezing1.RootedForest

variable {V : Type*} [DecidableEq V]

/-- The parent map determines both component roots and depths on the carrier. -/
theorem root_depth_eq_of_parent_eq {F G : RootedForest V}
    (hvertices : F.vertices = G.vertices)
    (hparent : ∀ v ∈ F.vertices, F.parent v = G.parent v)
    {v : V} (hv : v ∈ F.vertices) : F.root v = G.root v ∧ F.depth v = G.depth v := by
  have aux : ∀ d : ℕ, ∀ v ∈ F.vertices, F.depth v = d →
      F.root v = G.root v ∧ F.depth v = G.depth v := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro v hv hd
      have hvG : v ∈ G.vertices := hvertices ▸ hv
      by_cases hr : v = F.root v
      · have hpF : F.parent v = v := by simpa only [← hr] using F.parent_root v hv
        have hpG : G.parent v = v := (hparent v hv).symm.trans hpF
        have hrG : v = G.root v := by
          by_contra hne
          exact G.parent_ne hvG hne hpG
        constructor
        · exact hr.symm.trans hrG
        · have hF0 : F.depth v = 0 := by simpa only [← hr] using F.depth_root v hv
          have hG0 : G.depth v = 0 := by simpa only [← hrG] using G.depth_root v hvG
          exact hF0.trans hG0.symm
      · have hdF := F.depth_parent v hv hr
        have hlt : F.depth (F.parent v) < d := by omega
        obtain ⟨hir, hid⟩ := ih (F.depth (F.parent v)) hlt (F.parent v) (F.parent_mem v hv) rfl
        have hrG : v ≠ G.root v := by
          intro he
          have hpG : G.parent v = v := by simpa only [← he] using G.parent_root v hvG
          exact F.parent_ne hv hr ((hparent v hv).trans hpG)
        have hdG := G.depth_parent v hvG hrG
        constructor
        · calc
            F.root v = F.root (F.parent v) := (F.root_parent v hv).symm
            _ = G.root (F.parent v) := hir
            _ = G.root (G.parent v) := congrArg G.root (hparent v hv)
            _ = G.root v := G.root_parent v hvG
        · have hid' : F.depth (F.parent v) = G.depth (G.parent v) :=
            hid.trans (congrArg G.depth (hparent v hv))
          omega
  exact aux (F.depth v) v hv rfl

/-- Extensionality for all data fields; proof fields are propositionally
irrelevant. This deliberately includes unused functional values. -/
theorem ext_data {F G : RootedForest V} (hv : F.vertices = G.vertices)
    (hp : F.parent = G.parent) (hr : F.root = G.root) (hd : F.depth = G.depth) : F = G := by
  cases F
  cases G
  cases hv
  cases hp
  cases hr
  cases hd
  rfl

/-- Parent equality and canonical outside defaults suffice for full equality. -/
theorem eq_of_parent_eq {F G : RootedForest V} (hv : F.vertices = G.vertices)
    (hp : F.parent = G.parent)
    (hF : ∀ v, v ∉ F.vertices → F.root v = v ∧ F.depth v = 0)
    (hG : ∀ v, v ∉ G.vertices → G.root v = v ∧ G.depth v = 0) : F = G := by
  apply ext_data hv hp
  · funext v
    by_cases hmem : v ∈ F.vertices
    · exact (root_depth_eq_of_parent_eq hv (fun _ _ => congrFun hp _) hmem).1
    · exact (hF v hmem).1.trans ((hG v (by simpa only [← hv] using hmem)).1.symm)
  · funext v
    by_cases hmem : v ∈ F.vertices
    · exact (root_depth_eq_of_parent_eq hv (fun _ _ => congrFun hp _) hmem).2
    · exact (hF v hmem).2.trans ((hG v (by simpa only [← hv] using hmem)).2.symm)

end Freezing1.RootedForest
