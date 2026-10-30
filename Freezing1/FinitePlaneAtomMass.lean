module

public import Freezing1.FinitePlaneConditionalBounds
public import Freezing1.MainGeometricLimit
public import Freezing1.ForwardPlaneLeafMass

/-!
# Exact atoms of the actual plane limit law on finite plane trees

For $p<1$ the actual chronological plane limit law, obtained from the iid-sign
process, gives a finite plane tree with $m$ vertices the mass
$(1-p)^m p^{m-1}$. The proof is by induction on the true vertex count, from
the first-step fixed-point identity of the actual limit law. No assumed
Bienaymé law and no assumed atom mass is used.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem graft_preimage_singleton_of_degree_pos {T : PlaneTree.Tree}
    (hd : 0 < PlaneTree.degree T) :
    (fun q : PlaneTree.Tree × PlaneTree.Tree => PlaneTree.graft q.1 q.2) ⁻¹' {T} =
      {PlaneTree.child T 1} ×ˢ {PlaneTree.dropFirst T} := by
  ext ⟨A, B⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
  constructor
  · rintro rfl
    exact ⟨(PlaneTree.child_one_graft A B).symm, (PlaneTree.dropFirst_graft A B).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact PlaneTree.graft_child_dropFirst hd

theorem planeLimitLaw_atom (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ (m : ℕ) (T : PlaneTree.Tree), PlaneTree.FiniteVertices T →
      PlaneTree.finiteVertexCount T = m →
        (planeLimitLaw p : Measure PlaneTree.Tree) {T} =
          ENNReal.ofReal ((1 - (p : ℝ)) ^ m * (p : ℝ) ^ (m - 1)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T hT hm
  by_cases hd : PlaneTree.degree T = 0
  · have hT0 : T = PlaneTree.leaf := (PlaneTree.degree_zero_iff T).mp hd
    subst hT0
    have hm1 : m = 1 := by rw [← hm, PlaneTree.finiteVertexCount_leaf]
    subst hm1
    rw [planeLimitLaw_leaf p hp]
    simp
  · have hdpos : 0 < PlaneTree.degree T := Nat.pos_of_ne_zero hd
    have hTleaf : PlaneTree.leaf ∉ ({T} : Set PlaneTree.Tree) := by
      intro h
      exact hd ((PlaneTree.degree_zero_iff T).mpr (Set.mem_singleton_iff.mp h).symm)
    have hfix := DFunLike.congr_fun (planeLimitLaw_fixedPoint p hp) {T}
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.map_apply PlaneTree.continuous_graft.measurable (measurableSet_singleton T),
      Measure.dirac_apply' _ (measurableSet_singleton T), Set.indicator_of_notMem hTleaf,
      graft_preimage_singleton_of_degree_pos hdpos, Measure.prod_prod] at hfix
    have hc1 : PlaneTree.FiniteVertices (PlaneTree.child T 1) :=
      PlaneTree.finiteVertices_child hT ⟨le_rfl, hdpos⟩
    have hc2 : PlaneTree.FiniteVertices (PlaneTree.dropFirst T) :=
      PlaneTree.finiteVertices_dropFirst hT
    have ha := PlaneTree.finiteVertexCount_pos hc1
    have hb := PlaneTree.finiteVertexCount_pos hc2
    have hsplit := PlaneTree.finiteVertexCount_first_split hT hdpos
    have hA := ih (PlaneTree.finiteVertexCount (PlaneTree.child T 1)) (by omega) _ hc1 rfl
    have hB := ih (PlaneTree.finiteVertexCount (PlaneTree.dropFirst T)) (by omega) _ hc2 rfl
    rw [hfix, hA, hB, mul_zero, zero_add,
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (sub_nonneg.mpr p.2.2) _) (pow_nonneg p.2.1 _)),
      ← ENNReal.ofReal_mul p.2.1]
    congr 1
    obtain ⟨a, ha'⟩ : ∃ a, PlaneTree.finiteVertexCount (PlaneTree.child T 1) = a + 1 :=
      ⟨PlaneTree.finiteVertexCount (PlaneTree.child T 1) - 1, by omega⟩
    obtain ⟨b, hb'⟩ : ∃ b, PlaneTree.finiteVertexCount (PlaneTree.dropFirst T) = b + 1 :=
      ⟨PlaneTree.finiteVertexCount (PlaneTree.dropFirst T) - 1, by omega⟩
    have hm' : m = a + b + 2 := by omega
    rw [ha', hb', hm']
    simp only [Nat.add_sub_cancel, show a + b + 2 - 1 = a + b + 1 by omega]
    ring

end Freezing1.ForwardAnnealed
