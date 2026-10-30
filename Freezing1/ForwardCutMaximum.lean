module

public import Freezing1.ForwardCutHeightMGF
public import Freezing1.ForwardMaximum
public import Freezing1.ForwardGoodChainMaximum

/-!
# Maximum additional height after a cut

The actual forward vertex sum is controlled by the cut active-height MGF.
The bound includes the extinction endpoint, where the last step freezes.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def cutVertexSum (s : State) (a : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ v ∈ s.vertices, f (cutHeight s a v)

def cutMaximum (s : State) (a : ℕ) : ℕ := s.vertices.sup (cutHeight s a)

theorem cutHeight_le_cutMaximum {s : State} {a v : ℕ} (hv : v ∈ s.vertices) :
    cutHeight s a v ≤ cutMaximum s a := Finset.le_sup hv

theorem cutVertexSum_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) (f : ℕ → ℝ) :
    cutVertexSum (attach s (n + 1) p) a f =
      cutVertexSum s a f + f (cutHeight s a p + 1) := by
  have hfresh : n + 1 ∉ s.vertices := by intro h; have := hs.vertices_le _ h; omega
  unfold cutVertexSum
  change (∑ v ∈ insert (n + 1) s.vertices, f (cutHeight (attach s (n + 1) p) a v)) = _
  rw [Finset.sum_insert hfresh, cutHeight_attach_new hs ha hp, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  exact congrArg f (cutHeight_attach_old hs a p hv)

theorem cutVertexSum_freeze (s : State) (t p a : ℕ) (f : ℕ → ℝ) :
    cutVertexSum (freeze s t p) a f = cutVertexSum s a f := by
  change (∑ v ∈ s.vertices, f (cutHeight (freeze s t p) a v)) = _
  simp_rw [cutHeight_freeze]
  rfl

theorem transitionLaw_cutVertexSum_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    (hne : s.active.Nonempty) {a : ℕ} (ha : a ≤ n) (f : ℕ → ℝ) :
    (∫ s', cutVertexSum s' a f ∂transitionLaw s (n + 1) true) =
      cutVertexSum s a f + cutActiveMean s a (fun k => f (k + 1)) := by
  rw [transitionLaw_integral s _ _ hne]
  have he : ∀ p ∈ s.active, cutVertexSum (step s (n + 1) true p) a f =
      cutVertexSum s a f + f (cutHeight s a p + 1) := by
    intro p hp
    simpa [step, hp] using cutVertexSum_attach hs ha hp f
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  unfold cutActiveMean cutActiveSum activeSum
  simp only [cutHeightView]
  have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  field_simp

theorem transitionLaw_cutVertexSum_freeze (s : State) (t a : ℕ)
    (hne : s.active.Nonempty) (f : ℕ → ℝ) :
    (∫ s', cutVertexSum s' a f ∂transitionLaw s t false) = cutVertexSum s a f := by
  rw [transitionLaw_integral s _ _ hne]
  have he : ∀ p ∈ s.active, cutVertexSum (step s t false p) a f = cutVertexSum s a f := by
    intro p hp
    simpa only [step, ite_eq_left hp, Bool.false_eq_true, ite_false] using cutVertexSum_freeze s t p a f
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  field_simp

theorem ValidAt.cutVertexSum_bound {n : ℕ} {s : State} (hs : ValidAt n s) (a : ℕ) (f : ℕ → ℝ) :
    |cutVertexSum s a f| ≤ (n + 1) * ∑ k ∈ Finset.range (n + 1), |f k| := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc : s.vertices.card ≤ n + 1 := by
    apply (Finset.card_le_card (t := Finset.range (n + 1)) ?_).trans (by simp)
    intro v hv
    exact Finset.mem_range.mpr (by have := hs.vertices_le v hv; omega)
  calc
    _ ≤ ∑ v ∈ s.vertices, |f (cutHeight s a v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ s.vertices, C := by
      apply Finset.sum_le_sum
      intro v hv
      have hh := (cutHeight_le_height s a v).trans ((hs.height_le_id v hv).trans (hs.vertices_le v hv))
      exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    _ = (s.vertices.card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hC

theorem treeLaw_integrable_cutVertexSum (x : SignSequence) (n a : ℕ) (f : ℕ → ℝ) :
    Integrable (fun s => cutVertexSum s a f) (treeLaw x n) := by
  apply (integrable_const ((n + 1 : ℝ) * ∑ k ∈ Finset.range (n + 1), |f k|)).mono'
    measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  simpa only [Real.norm_eq_abs] using hs.cutVertexSum_bound a f

theorem integral_treeLaw_cutVertexSum_succ (x : SignSequence) (n a : ℕ) (f : ℕ → ℝ) :
    (∫ s', cutVertexSum s' a f ∂treeLaw x (n + 1)) =
      ∫ s, (∫ s', cutVertexSum s' a f ∂transitionLaw s (n + 1) (x (n + 1))) ∂treeLaw x n := by
  let K : Kernel State State := ⟨fun s => transitionLaw s (n + 1) (x (n + 1)), measurable_from_top⟩
  have hi := treeLaw_integrable_cutVertexSum x (n + 1) a f
  rw [treeLaw] at hi
  have hi' : Integrable (fun s => cutVertexSum s a f)
      ((K ∘ₖ Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hi
  have hh := Kernel.integral_comp hi'
  simpa only [K, treeLaw, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hh

theorem treeLaw_cutVertexSum_succ (x : SignSequence) (a n : ℕ) (ha : a ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ s, cutVertexSum s a f ∂treeLaw x (n + 1)) =
      (∫ s, cutVertexSum s a f ∂treeLaw x n) +
        if x (n + 1) then (∫ s, cutActiveMean s a (fun k => f (k + 1)) ∂treeLaw x n) else 0 := by
  rw [integral_treeLaw_cutVertexSum_succ]
  cases hx : x (n + 1)
  · simp only [Bool.false_eq_true, ite_false, add_zero]
    apply integral_congr_ae
    filter_upwards [treeLaw_active_nonempty x n hτ] with s hs
    exact transitionLaw_cutVertexSum_freeze s _ a hs f
  · simp only [ite_true]
    rw [← integral_add (treeLaw_integrable_cutVertexSum x n a f)
      (treeLaw_integrable_cutActiveMean x n a (fun k => f (k + 1)))]
    apply integral_congr_ae
    filter_upwards [treeLaw_valid x n, treeLaw_active_nonempty x n hτ] with s hs hne
    exact transitionLaw_cutVertexSum_attach hs hne ha f

/-- The vertex-weight estimate includes `n = extinctionTime x`: the recursion
only needs the preceding active state, and the final step is a freeze. -/
theorem treeLaw_cutVertexSum_exp_le (x : SignSequence) (a n : ℕ) (ha : a ≤ n)
    (hτ : (n : ℕ∞) ≤ extinctionTime x) {theta : ℝ} (htheta : 0 ≤ theta) :
    (∫ s, cutVertexSum s a (fun k => Real.exp (theta * (k : ℝ))) ∂treeLaw x n) ≤
      (n + 1) * Real.exp theta *
        Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) := by
  revert hτ
  induction n, ha using Nat.le_induction with
  | base =>
    intro hτ
    have hbound : ∀ᵐ s ∂treeLaw x a,
        cutVertexSum s a (fun k => Real.exp (theta * (k : ℝ))) ≤ (a + 1 : ℝ) := by
      filter_upwards [treeLaw_valid x a] with s hs
      have he : ∀ v ∈ s.vertices, cutHeight s a v = 0 :=
        fun v hv => cutHeightAux_eq_zero_of_le s a _ v (hs.vertices_le v hv)
      unfold cutVertexSum
      have hsum : (∑ v ∈ s.vertices, Real.exp (theta * (cutHeight s a v : ℝ))) =
          ∑ _v ∈ s.vertices, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [he v hv]
        simp
      rw [hsum]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (show s.vertices.card ≤ a + 1 from by
        apply (Finset.card_le_card (t := Finset.range (a + 1)) ?_).trans (by simp)
        intro v hv
        exact Finset.mem_range.mpr (by have := hs.vertices_le v hv; omega))
    have hh := integral_mono_ae (treeLaw_integrable_cutVertexSum x a a _) (integrable_const (a + 1 : ℝ)) hbound
    simp only [integral_const, probReal_univ, one_smul] at hh
    simp only [sub_self, zero_mul, Real.exp_zero, mul_one]
    exact hh.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp htheta))
  | succ n hna ih =>
    intro hτ
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hτ
    have ih := ih hnτ.le
    have he : 0 ≤ Real.exp theta - 1 := sub_nonneg.mpr (Real.one_le_exp htheta)
    have hm : heightScale x n ≤ heightScale x (n + 1) := by
      rw [heightScale_succ]
      split_ifs with hx
      · have hs := ((lt_extinctionTime_iff x n).mp hnτ) n le_rfl
        have hs' : 0 < activeCount x (n + 1) := by rw [activeCount_succ, hx]; simp only [ite_true]; omega
        have hsR : (0 : ℝ) < activeCount x (n + 1) := by exact_mod_cast hs'
        have : 0 ≤ 1 / (activeCount x (n + 1) : ℝ) := by positivity
        linarith
      · simp
    have hMon := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (sub_le_sub_right hm (heightScale x a)) he)
    have hinc : (if x (n + 1) then
        (∫ s, cutActiveMean s a (fun k => Real.exp (theta * ((k + 1 : ℕ) : ℝ))) ∂treeLaw x n) else 0) ≤
        Real.exp theta * Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) := by
      split_ifs
      · have hshift : (∫ s, cutActiveMean s a (fun k => Real.exp (theta * ((k + 1 : ℕ) : ℝ))) ∂treeLaw x n) =
            Real.exp theta * (∫ s, cutActiveMean s a (fun k => Real.exp (theta * (k : ℝ))) ∂treeLaw x n) := by
          simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add,
            mul_comm _ (Real.exp theta), cutActiveMean_const_mul]
          exact integral_const_mul _ _
        rw [hshift]
        exact mul_le_mul_of_nonneg_left (treeLaw_cutActiveMean_exp_le x a n hna hnτ theta) (Real.exp_pos _).le
      · positivity
    rw [treeLaw_cutVertexSum_succ x a n hna hnτ]
    calc
      _ ≤ (n + 1) * Real.exp theta * Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) +
          Real.exp theta * Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) := add_le_add ih hinc
      _ = ((n + 1 : ℕ) + 1) * Real.exp theta * Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hMon (by positivity)

theorem ValidAt.exp_cutMaximum_le_cutVertexSum {n : ℕ} {s : State} (hs : ValidAt n s)
    (a : ℕ) (theta : ℝ) :
    Real.exp (theta * (cutMaximum s a : ℝ)) ≤ cutVertexSum s a (fun k => Real.exp (theta * (k : ℝ))) := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup s.vertices ⟨0, hs.root_mem⟩ (cutHeight s a)
  rw [cutMaximum, hmax]
  exact Finset.single_le_sum (f := fun w => Real.exp (theta * (cutHeight s a w : ℝ)))
    (fun _ _ => (Real.exp_pos _).le) hv

theorem treeLaw_integrable_exp_cutMaximum (x : SignSequence) (n a : ℕ) (theta : ℝ) :
    Integrable (fun s => Real.exp (theta * (cutMaximum s a : ℝ))) (treeLaw x n) := by
  apply (treeLaw_integrable_cutVertexSum x n a (fun k => Real.exp (theta * (k : ℝ)))).mono'
    measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hs.exp_cutMaximum_le_cutVertexSum a theta

theorem cutMaximum_exponential_tail (x : SignSequence) (a n : ℕ) (ha : a ≤ n)
    (hτ : (n : ℕ∞) ≤ extinctionTime x) {theta L : ℝ} (htheta : 0 ≤ theta) :
    (treeLaw x n).real {s | L ≤ (cutMaximum s a : ℝ)} ≤
      (n + 1) * Real.exp theta *
        Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1) - theta * L) := by
  have hmgf : mgf (fun s => (cutMaximum s a : ℝ)) (treeLaw x n) theta ≤
      (n + 1) * Real.exp theta * Real.exp ((heightScale x n - heightScale x a) * (Real.exp theta - 1)) := by
    apply (integral_mono_ae (treeLaw_integrable_exp_cutMaximum x n a theta)
      (treeLaw_integrable_cutVertexSum x n a _) ?_).trans (treeLaw_cutVertexSum_exp_le x a n ha hτ htheta)
    exact (treeLaw_valid x n).mono fun s hs => hs.exp_cutMaximum_le_cutVertexSum a theta
  calc
    _ ≤ Real.exp (-theta * L) * mgf (fun s => (cutMaximum s a : ℝ)) (treeLaw x n) theta :=
      measure_ge_le_exp_mul_mgf _ htheta (treeLaw_integrable_exp_cutMaximum x n a theta)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      have he : -theta * L = -(theta * L) := by ring
      rw [he, Real.exp_neg, Real.exp_sub]
      ring

/-- Terminal height consists of an old prefix height and height added
above that prefix. The statement uses the actual canonical truncation. -/
theorem ValidAt.treeHeight_le_truncate_add_cutMaximum {n : ℕ} {s : State}
    (hs : ValidAt n s) (a : ℕ) : treeHeight s ≤ treeHeight (truncateAt s a) + cutMaximum s a := by
  have hrec : ∀ v ∈ s.vertices,
      s.height v ≤ treeHeight (truncateAt s a) + cutHeight s a v := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro hv
      by_cases hva : v ≤ a
      · have hm : v ∈ (truncateAt s a).vertices := Finset.mem_filter.mpr ⟨hv, hva⟩
        have hh := height_le_treeHeight hm
        have he : cutHeight s a v = 0 := cutHeightAux_eq_zero_of_le s a _ v hva
        simpa only [truncateAt, ite_eq_left hva, he, Nat.add_zero] using hh
      · have hv0 : v ≠ 0 := by omega
        have hparent := ih (s.parent v) (hs.parent_lt v hv hv0) (hs.parent_mem v hv)
        have hheight := hs.height_parent v hv hv0
        have hcut : cutHeight s a v = cutHeight s a (s.parent v) + 1 := by
          unfold cutHeight
          rw [hheight]
          simp only [cutHeightAux, ite_eq_right hva]
        omega
  apply Finset.sup_le
  intro v hv
  exact (hrec v hv).trans (Nat.add_le_add_left (cutHeight_le_cutMaximum hv) _)

end Freezing1.Forward
