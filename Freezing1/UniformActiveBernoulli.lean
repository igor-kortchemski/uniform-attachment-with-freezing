module

public import Freezing1.CanonicalActiveSampling
public import Freezing1.UniformBirthBernoulli

/-! The source's independent Bernoulli representation of uniform active height. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def activeLabelSet (x : SignSequence) (n : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (vertexLabels x n).filter (fun v => CanonicalTree.reverseLabel v = none)

theorem activeLabelSet_birth {x : SignSequence} {n : ℕ} {v : ℕ ⊕ ℕ}
    (hv : v ∈ activeLabelSet x n) : birthTime n v = n := by
  have hh := (Finset.mem_filter.mp hv).2
  cases v with
  | inl i => rfl
  | inr i => simp [CanonicalTree.reverseLabel] at hh

theorem activeLabelSet_nonempty {x : SignSequence} {n : ℕ} (h : PositiveThrough x n) :
    (activeLabelSet x n).Nonempty := by
  refine ⟨Sum.inl 0, ?_⟩
  have hp : 0 < (activeCount x n).toNat := by have := h n le_rfl; omega
  simp [activeLabelSet, vertexLabels, CanonicalTree.reverseLabel, hp]

theorem uniformActiveLabel_probability {x : SignSequence} {n : ℕ} (h : PositiveThrough x n) :
    IsProbabilityMeasure (Measure.uniformOfFinset (activeLabelSet x n)) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast (activeLabelSet_nonempty h).card_pos.ne') (by simp)

theorem reverse_uniformActiveHeight_eq_label_bind (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) :
    (Reverse.treeLaw x n).bind (fun F =>
      (Measure.uniformOfFinset (CanonicalTree.reverseActiveVertices F)).map F.depth) =
      (Measure.uniformOfFinset (activeLabelSet x n)).bind (fun v =>
        (Reverse.treeLaw x n).map (fun F => F.depth v)) := by
  calc
    _ = (Reverse.treeLaw x n).bind (fun F =>
        (Measure.uniformOfFinset (activeLabelSet x n)).map F.depth) := by
      apply Measure.bind_congr_right
      filter_upwards [Reverse.treeLaw_vertices_and_root x n (UniformBirth.horizon_le_extinction h)]
        with F hF
      have he : CanonicalTree.reverseActiveVertices F = activeLabelSet x n := by
        rw [CanonicalTree.reverseActiveVertices, hF.1]
        rfl
      rw [he]
    _ = (Reverse.treeLaw x n).bind (fun F =>
        (Measure.uniformOfFinset (activeLabelSet x n)).bind (fun v => Measure.dirac (F.depth v))) := by
      congr 1
      funext F
      exact (Measure.bind_dirac_eq_map _ (measurable_of_countable _)).symm
    _ = (Measure.uniformOfFinset (activeLabelSet x n)).bind (fun v =>
        (Reverse.treeLaw x n).bind (fun F => Measure.dirac (F.depth v))) := by
      apply Measure.bind_comm
      exact measurable_from_prod_countable_left (fun _ => measurable_from_top)
    _ = _ := by
      congr 1
      funext v
      exact Measure.bind_dirac_eq_map _ measurable_from_top

/-- Equality with a genuinely independent unmasked Bernoulli array,
with the attachment mask applied inside the sum. -/
theorem uniformActiveHeightLaw_eq_bernoulli_array (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) :
    Forward.uniformActiveHeightLaw x n =
      (bernoulliProductLaw (UniformBirth.reciprocalParameter x n h)).map
        (UniformBirth.truncatedSum x n) := by
  have : IsProbabilityMeasure (Measure.uniformOfFinset (activeLabelSet x n)) :=
    uniformActiveLabel_probability h
  rw [CanonicalTree.forward_uniformActiveHeightLaw_eq_reverse x n
      ((lt_extinctionTime_iff x n).mpr h), reverse_uniformActiveHeight_eq_label_bind x n h]
  calc
    _ = (Measure.uniformOfFinset (activeLabelSet x n)).bind (fun _ =>
        (bernoulliProductLaw (UniformBirth.reciprocalParameter x n h)).map
          (UniformBirth.truncatedSum x n)) := by
      apply Measure.bind_congr_right
      have hs : ∀ᵐ v ∂Measure.uniformOfFinset (activeLabelSet x n), v ∈ activeLabelSet x n := by
        rw [ae_iff]
        simp [Measure.uniformOfFinset_apply]
      filter_upwards [hs] with v hv
      have hd := Reverse.treeLaw_depth_hasLaw x n (UniformBirth.horizon_le_extinction h)
        (Finset.mem_filter.mp hv).1
      have hz := UniformBirth.truncatedSum_hasLaw x n h n
      rw [activeLabelSet_birth hv] at hd
      exact hd.map_eq.trans hz.map_eq.symm
    _ = _ := by rw [Measure.bind_const, measure_univ, one_smul]

end Freezing1
