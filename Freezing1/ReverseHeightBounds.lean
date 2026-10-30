module

public import Freezing1.ReverseHeightLaw
public import Freezing1.HeightTailBounds
public import Freezing1.TreeSourceChecks

/-!
# Actual reverse-tree height tails

The lower estimate is the lower half of Proposition `prop:bounds`.
The upper estimate repairs its false factor `n` to the exact number of
vertices. The threshold has no one-edge shift: the proof uses the actual
reverse Bernoulli marginal law, followed by the manuscript's union bound.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

theorem Reverse.sum_attachmentParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (∑ i : Fin n, (Reverse.attachmentParameter x n hn i : ℝ)) = heightScale x n := by
  simp_rw [Reverse.attachmentParameter_coe]
  exact Fin.sum_univ_eq_sum_range
    (fun i => if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) n

/-- The existing natural-valued graph maximum agrees with the finite real
maximum on the deterministic terminal label set. -/
theorem reverseMaximum_eq_finiteHeightMax {x : SignSequence} {n : ℕ}
    {F : Reverse.Forest} (hv : F.vertices = vertexLabels x n)
    (hne : (vertexLabels x n).Nonempty) :
    (reverseMaximum F : ℝ) =
      finiteHeightMax (vertexLabels x n) hne (fun v (G : Reverse.Forest) => (G.depth v : ℝ)) F := by
  unfold reverseMaximum finiteHeightMax
  rw [hv]
  apply le_antisymm
  · obtain ⟨v, hv', hsup⟩ := Finset.exists_mem_eq_sup (vertexLabels x n) hne F.depth
    rw [hsup]
    exact Finset.le_sup' (fun v => (F.depth v : ℝ)) hv'
  · apply Finset.sup'_le
    intro v hv'
    change (F.depth v : ℝ) ≤ (((vertexLabels x n).sup F.depth : ℕ) : ℝ)
    exact_mod_cast (Finset.le_sup (f := F.depth) hv')

theorem reverseMaximum_eq_finiteHeightMax_ae (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂Reverse.treeLaw x n, (reverseMaximum F : ℝ) =
      finiteHeightMax (vertexLabels x n)
        (vertexLabels_nonempty (activeCount_nonneg_of_le_extinctionTime hn))
        (fun v (G : Reverse.Forest) => (G.depth v : ℝ)) F := by
  filter_upwards [Reverse.treeLaw_vertices_and_root x n hn] with F hF
  exact reverseMaximum_eq_finiteHeightMax hF.1 _

/-- Corrected upper half of Proposition 3, for the actual reverse tree. The
union factor is exactly the deterministic number of vertices. -/
theorem reverseMaximum_corrected_upper_tail (x : SignSequence) (n : ℕ)
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real {F | heightScale x n + t < (reverseMaximum F : ℝ)} ≤
      ((vertexLabels x n).card : ℝ) *
        Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) := by
  let p := Reverse.attachmentParameter x n hτ.le
  let H : (ℕ ⊕ ℕ) → Reverse.Forest → ℝ := fun v F => (F.depth v : ℝ)
  let u : (ℕ ⊕ ℕ) → Finset (Fin n) :=
    fun v => Finset.univ.filter fun i => i.val < birthTime n v
  have hne := vertexLabels_nonempty (activeCount_nonneg_of_le_extinctionTime hτ.le)
  have hm : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), (p i : ℝ) := by
    rw [Reverse.sum_attachmentParameter]
    exact heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hb := finiteHeightMax_bernoulli_upper_tail
    (μ := Reverse.treeLaw x n) (ν := bernoulliProductLaw p)
    (vertexLabels x n) hne (H := H)
    (Y := fun i (ω : Fin n → ℕ) => (ω i : ℝ))
    (fun i => by fun_prop) (Reverse.heightBernoulli_independent x n hτ.le)
    (Reverse.heightBernoulli_hasLaw x n hτ.le) u
    (fun _ _ => Finset.filter_subset _ _) (fun v hv => Reverse.treeLaw_height_identDistrib_bernoulli x n hτ.le hv)
    hm ht
  rw [Reverse.sum_attachmentParameter] at hb
  have he : (Reverse.treeLaw x n).real {F | heightScale x n + t < (reverseMaximum F : ℝ)} =
      (Reverse.treeLaw x n).real {F | heightScale x n + t < finiteHeightMax (vertexLabels x n) hne H F} := by
    apply measureReal_congr
    filter_upwards [reverseMaximum_eq_finiteHeightMax_ae x n hτ.le] with F hF
    rw [hF]
  rw [he]
  exact hb

/-- The same repaired upper bound with the elementary factor `n+1`. -/
theorem reverseMaximum_upper_tail_nat_succ (x : SignSequence) (n : ℕ)
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real {F | heightScale x n + t < (reverseMaximum F : ℝ)} ≤
      ((n : ℝ) + 1) * Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) := by
  apply (reverseMaximum_corrected_upper_tail x n hn hτ ht).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [card_vertexLabels (activeCount_nonneg_of_le_extinctionTime hτ.le)]
  exact_mod_cast Nat.add_le_add_right (plusCount_le x n) 1

/-- Original lower half of Proposition 3. The terminal active label `a₁`
has the full Bernoulli sum as its height law. -/
theorem reverseMaximum_lower_tail (x : SignSequence) (n : ℕ)
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real {F | (reverseMaximum F : ℝ) < heightScale x n - t} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) := by
  let p := Reverse.attachmentParameter x n hτ.le
  let H : (ℕ ⊕ ℕ) → Reverse.Forest → ℝ := fun v F => (F.depth v : ℝ)
  have hs := ((lt_extinctionTime_iff x n).mp hτ) n le_rfl
  have hne := vertexLabels_nonempty hs.le
  have hv : Sum.inl 0 ∈ vertexLabels x n := by
    simp only [vertexLabels, Finset.inl_mem_disjSum, Finset.mem_range]
    omega
  have hfilter : Finset.univ.filter (fun i : Fin n => i.val < birthTime n (.inl 0)) =
      Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact i.isLt
  have hIdent := Reverse.treeLaw_height_identDistrib_bernoulli x n hτ.le hv
  rw [hfilter] at hIdent
  have hm : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), (p i : ℝ) := by
    rw [Reverse.sum_attachmentParameter]
    exact heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hb := finiteHeightMax_bernoulli_lower_tail
    (μ := Reverse.treeLaw x n) (ν := bernoulliProductLaw p)
    (vertexLabels x n) hne (H := H)
    (Y := fun i (ω : Fin n → ℕ) => (ω i : ℝ))
    (fun i => by fun_prop) (Reverse.heightBernoulli_independent x n hτ.le)
    (Reverse.heightBernoulli_hasLaw x n hτ.le) Finset.univ hv hIdent hm ht
  rw [Reverse.sum_attachmentParameter] at hb
  have he : (Reverse.treeLaw x n).real {F | (reverseMaximum F : ℝ) < heightScale x n - t} =
      (Reverse.treeLaw x n).real {F | finiteHeightMax (vertexLabels x n) hne H F < heightScale x n - t} := by
    apply measureReal_congr
    filter_upwards [reverseMaximum_eq_finiteHeightMax_ae x n hτ.le] with F hF
    rw [hF]
  rw [he]
  exact hb

/-- The repaired upper estimate in the manuscript's centered strict-tail and
exponential notation: `log |Vₙ|` replaces the false `log n` term. -/
theorem reverseMaximum_corrected_upper_tail_source (x : SignSequence) (n : ℕ)
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real {F | t < (reverseMaximum F : ℝ) - heightScale x n} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n) +
        Real.log ((vertexLabels x n).card : ℝ)) := by
  have hcard : (0 : ℝ) < (vertexLabels x n).card := by
    exact_mod_cast (vertexLabels_nonempty (activeCount_nonneg_of_le_extinctionTime hτ.le)).card_pos
  rw [Real.exp_add, Real.exp_log hcard, mul_comm]
  have hevent : {F : Reverse.Forest | t < (reverseMaximum F : ℝ) - heightScale x n} =
      {F | heightScale x n + t < (reverseMaximum F : ℝ)} := by
    ext F
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact reverseMaximum_corrected_upper_tail x n hn hτ ht

/-- The literal centered strict lower-tail statement of Proposition 3. -/
theorem reverseMaximum_lower_tail_source (x : SignSequence) (n : ℕ)
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real {F | (reverseMaximum F : ℝ) - heightScale x n < -t} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) := by
  have hevent : {F : Reverse.Forest | (reverseMaximum F : ℝ) - heightScale x n < -t} =
      {F | (reverseMaximum F : ℝ) < heightScale x n - t} := by
    ext F
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact reverseMaximum_lower_tail x n hn hτ ht

end Freezing1
