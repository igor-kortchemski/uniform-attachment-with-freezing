module

public import Freezing1.ReverseCoalescence
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Separation probabilities in the actual reverse marginal laws

The product of noncoalescence factors is derived from the actual measure-bind
recursion. No independence assumption is introduced. These are probabilities
of component separation at a specified reverse phase; identifying them with a
random coalescence time requires a coherent joint-history construction.
-/

@[expose] public section

namespace Freezing1.Reverse

open MeasureTheory
open scoped ENNReal BigOperators Classical

/-- The actual reverse marginal at paper phase `i`, for `i ≤ n`. -/
noncomputable def phaseLaw (x : SignSequence) (n i : ℕ) : Measure Forest :=
  lawAfter x n (n - i)

instance phaseLaw_probability (x : SignSequence) (n i : ℕ) :
    IsProbabilityMeasure (phaseLaw x n i) := lawAfter_probability x n (n - i)

theorem phaseLaw_top (x : SignSequence) (n : ℕ) :
    phaseLaw x n n = Measure.dirac (initial x n) := by
  simp [phaseLaw, lawAfter]

theorem phaseLaw_valid (x : SignSequence) (n i : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i ≤ n) :
    ∀ᵐ F ∂phaseLaw x n i, ValidAt x n i F := by
  simpa only [phaseLaw, Nat.sub_sub_self hi] using
    lawAfter_valid x n (n - i) hn (Nat.sub_le n i)

/-- Reverse phase `i` is obtained by the actual transition from phase `i+1`. -/
theorem phaseLaw_succ (x : SignSequence) (n i : ℕ) (hi : i < n) :
    phaseLaw x n i = (phaseLaw x n (i + 1)).bind (transitionLaw x i) := by
  have hsub : n - i = (n - (i + 1)) + 1 := by omega
  have hk : n - (i + 1) < n := by omega
  have hphase : n - (n - (i + 1) + 1) = i := by omega
  unfold phaseLaw
  rw [hsub, lawAfter, ite_eq_left hk, hphase]

/-- More vertices are present as the reverse phase decreases. -/
theorem phaseLabels_mono (x : SignSequence) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    phaseLabels x n j ⊆ phaseLabels x n i := by
  intro v hv
  cases v with
  | inl k => simpa only [phaseLabels, Finset.inl_mem_disjSum] using hv
  | inr k =>
    simp only [phaseLabels, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_range] at hv ⊢
    exact ⟨hv.1, hij.trans hv.2.1, hv.2.2⟩

/-- The source's survival factor at a positive schedule step, and one at an insertion. -/
noncomputable def separationFactor (x : SignSequence) (i : ℕ) : ℝ :=
  if x i then 1 - 1 / ((activeCount x i).toNat.choose 2 : ℝ) else 1

theorem separationFactor_nonneg (x : SignSequence) (i : ℕ) : 0 ≤ separationFactor x i := by
  unfold separationFactor
  split_ifs
  · by_cases hz : (activeCount x i).toNat.choose 2 = 0
    · simp [hz]
    · have hpos : (1 : ℝ) ≤ ((activeCount x i).toNat.choose 2 : ℝ) := by
        exact_mod_cast (show 1 ≤ (activeCount x i).toNat.choose 2 by omega)
      have hdiv : 1 / ((activeCount x i).toNat.choose 2 : ℝ) ≤ 1 :=
        (div_le_one (by linarith)).mpr hpos
      linarith
  · norm_num

theorem separationFactor_le_one (x : SignSequence) (i : ℕ) : separationFactor x i ≤ 1 := by
  unfold separationFactor
  split_ifs
  · have hdiv : (0 : ℝ) ≤ 1 / ((activeCount x i).toNat.choose 2 : ℝ) := by positivity
    linarith
  · exact le_rfl

/-- Kernel separation is the source factor times the indicator that the two
components have not yet merged. -/
theorem transitionLaw_separation_indicator {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    (transitionLaw x i F) {F' | F'.root u ≠ F'.root v} =
      {F' : Forest | F'.root u ≠ F'.root v}.indicator
        (fun _ => ENNReal.ofReal (separationFactor x (i + 1))) F := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (transitionLaw x i F) _)]
  change ENNReal.ofReal ((transitionLaw x i F).real {F' | F'.root u ≠ F'.root v}) = _
  by_cases huv : F.root u = F.root v
  · have he : (transitionLaw x i F).real {F' | F'.root u ≠ F'.root v} = 0 := by
      change (transitionLaw x i F).real ({F' | F'.root u = F'.root v}ᶜ) = 0
      rw [probReal_compl_eq_one_sub (by trivial),
        transitionLaw_coalescence_of_eq x i F hu hv huv]
      ring
    simp [he, huv]
  · rw [Set.indicator_of_mem huv, transitionLaw_noncoalescence hF hu hv huv]
    rfl

/-- Exact one-step recurrence for the actual marginal separation probability. -/
theorem phaseLaw_separation_succ (x : SignSequence) (n i : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ phaseLabels x n (i + 1))
    (hv : v ∈ phaseLabels x n (i + 1)) :
    (phaseLaw x n i).real {F | F.root u ≠ F.root v} =
      separationFactor x (i + 1) *
        (phaseLaw x n (i + 1)).real {F | F.root u ≠ F.root v} := by
  have he : (phaseLaw x n i) {F | F.root u ≠ F.root v} =
      ENNReal.ofReal (separationFactor x (i + 1)) *
        (phaseLaw x n (i + 1)) {F | F.root u ≠ F.root v} := by
    rw [phaseLaw_succ x n i hi, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ F, {F' : Forest | F'.root u ≠ F'.root v}.indicator
          (fun _ => ENNReal.ofReal (separationFactor x (i + 1))) F ∂phaseLaw x n (i + 1) := by
        apply lintegral_congr_ae
        filter_upwards [phaseLaw_valid x n (i + 1) hn (by omega)] with F hF
        exact transitionLaw_separation_indicator hF
          (by rwa [hF.vertices_eq]) (by rwa [hF.vertices_eq])
      _ = _ := lintegral_indicator_const (by trivial) _
  change ((phaseLaw x n i) {F | F.root u ≠ F.root v}).toReal = _
  rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal (separationFactor_nonneg x (i + 1))]
  rfl

/-- The exact interval product for existing vertices, with their actual
separation probability at the upper phase retained. -/
theorem phaseLaw_separation_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ phaseLabels x n j) (hv : v ∈ phaseLabels x n j) :
    (phaseLaw x n i).real {F | F.root u ≠ F.root v} =
      (phaseLaw x n j).real {F | F.root u ≠ F.root v} *
        ∏ t ∈ Finset.Ioc i j, separationFactor x t := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    simp
  | succ j ih =>
    by_cases hij' : i ≤ j
    · have huj := phaseLabels_mono x n (Nat.le_succ j) hu
      have hvj := phaseLabels_mono x n (Nat.le_succ j) hv
      rw [ih hij' (by omega) huj hvj,
        phaseLaw_separation_succ x n j hn (by omega) hu hv,
        Finset.prod_Ioc_succ_top hij']
      ring
    · have hi : i = j + 1 := by omega
      subst i
      simp

/-- Every terminal label is born no later than the terminal phase. -/
theorem birthTime_le_of_mem {x : SignSequence} {n : ℕ} {v : ℕ ⊕ ℕ}
    (hv : v ∈ vertexLabels x n) : birthTime n v ≤ n := by
  cases v with
  | inl j => simp [birthTime]
  | inr j =>
    have hj : j < n ∧ x (j + 1) = false := by
      simpa [vertexLabels, frozenIndices] using hv
    exact hj.1.le

/-- A label born strictly below the terminal phase is exactly the singleton
inserted at its freezing step. -/
theorem label_eq_frozen_of_birthTime_lt {x : SignSequence} {n : ℕ} {v : ℕ ⊕ ℕ}
    (hv : v ∈ vertexLabels x n) (hlt : birthTime n v < n) :
    v = Sum.inr (birthTime n v) ∧ x (birthTime n v + 1) = false := by
  cases v with
  | inl j => simp [birthTime] at hlt
  | inr j =>
    have hj : j < n ∧ x (j + 1) = false := by
      simpa [vertexLabels, frozenIndices] using hv
    exact ⟨rfl, hj.2⟩

/-- A newly inserted singleton is separate from every already present vertex
under the actual phase marginal. -/
theorem phaseLaw_separated_from_inserted (x : SignSequence) (n i : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n) (hx : x (i + 1) = false)
    {v : ℕ ⊕ ℕ} (hv : v ∈ phaseLabels x n (i + 1)) :
    (phaseLaw x n i).real {F | F.root (Sum.inr i) ≠ F.root v} = 1 := by
  have he : (phaseLaw x n i) {F | F.root (Sum.inr i) ≠ F.root v} = 1 := by
    rw [phaseLaw_succ x n i hi, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂phaseLaw x n (i + 1) := by
        apply lintegral_congr_ae
        filter_upwards [phaseLaw_valid x n (i + 1) hn (by omega)] with F hF
        have hfresh : Sum.inr i ∉ F.vertices := by
          rw [hF.vertices_eq]
          exact fresh_freezing_label x n i
        have hvF : v ∈ F.vertices := by rwa [hF.vertices_eq]
        have hvi : v ≠ Sum.inr i := fun h => hfresh (h ▸ hvF)
        have hri : F.root v ≠ Sum.inr i := fun h => hfresh (h ▸ F.root_mem v hvF)
        simp [transitionLaw, hx, insertLabel, hfresh, RootedForest.adjoin, hvi, Ne.symm hri]
      _ = 1 := by simp
  change ((phaseLaw x n i) {F | F.root (Sum.inr i) ≠ F.root v}).toReal = 1
  rw [he, ENNReal.toReal_one]

/-- At the birth of the later-inserted vertex, two vertices with different
birth phases are necessarily still in different components. -/
theorem phaseLaw_separation_at_birth_of_lt (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n)
    (hbirth : birthTime n u < birthTime n v) :
    (phaseLaw x n (birthTime n u)).real {F | F.root u ≠ F.root v} = 1 := by
  have hvn := birthTime_le_of_mem hv
  have hun : birthTime n u < n := hbirth.trans_le hvn
  obtain ⟨huid, hx⟩ := label_eq_frozen_of_birthTime_lt hu hun
  have hvphase : v ∈ phaseLabels x n (birthTime n u + 1) :=
    (mem_phaseLabels_iff_birthTime (by omega) hv).mpr (by omega)
  have he := phaseLaw_separated_from_inserted x n (birthTime n u) hn hun hx hvphase
  simpa only [← huid] using he

/-- Distinct terminal vertices start separated at the smaller of their birth
phases. This includes two terminal active vertices and frozen-label insertions. -/
theorem phaseLaw_separation_at_min_birth (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v) :
    (phaseLaw x n (min (birthTime n u) (birthTime n v))).real
      {F | F.root u ≠ F.root v} = 1 := by
  rcases lt_trichotomy (birthTime n u) (birthTime n v) with hlt | heq | hgt
  · rw [min_eq_left hlt.le]
    exact phaseLaw_separation_at_birth_of_lt x n hn hu hv hlt
  · have hun := birthTime_le_of_mem hu
    have htop : birthTime n u = n := by
      by_contra hnot
      have hlt : birthTime n u < n := lt_of_le_of_ne hun hnot
      have hlt' : birthTime n v < n := by omega
      have h1 := (label_eq_frozen_of_birthTime_lt hu hlt).1
      have h2 := (label_eq_frozen_of_birthTime_lt hv hlt').1
      exact huv (h1.trans ((congrArg Sum.inr heq).trans h2.symm))
    have htop' : birthTime n v = n := by omega
    rw [htop, htop', min_self, phaseLaw_top]
    simp [Measure.real, initial, RootedForest.isolated, huv]
  · rw [min_eq_right hgt.le]
    have he := phaseLaw_separation_at_birth_of_lt x n hn hv hu hgt
    have hs : {F : Forest | F.root u ≠ F.root v} = {F | F.root v ≠ F.root u} := by
      ext F
      exact ne_comm
    rwa [hs]

/-- The actual marginal separation probability is exactly the product of the
source survival factors down from the smaller birth phase. This does not yet
identify a random coalescence time on a joint history space. -/
theorem phaseLaw_separation_birth_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {i : ℕ} (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    (phaseLaw x n i).real {F | F.root u ≠ F.root v} =
      ∏ t ∈ Finset.Ioc i (min (birthTime n u) (birthTime n v)), separationFactor x t := by
  have hbn : min (birthTime n u) (birthTime n v) ≤ n :=
    (min_le_left _ _).trans (birthTime_le_of_mem hu)
  have huB : u ∈ phaseLabels x n (min (birthTime n u) (birthTime n v)) :=
    (mem_phaseLabels_iff_birthTime hbn hu).mpr (min_le_left _ _)
  have hvB : v ∈ phaseLabels x n (min (birthTime n u) (birthTime n v)) :=
    (mem_phaseLabels_iff_birthTime hbn hv).mpr (min_le_right _ _)
  rw [phaseLaw_separation_product x n hn hi hbn huB hvB,
    phaseLaw_separation_at_min_birth x n hn hu hv huv, one_mul]

/-- The same actual marginal product with only attachment steps retained,
as in the manuscript's displayed product. -/
theorem phaseLaw_separation_birth_product_attachment (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {i : ℕ} (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    (phaseLaw x n i).real {F | F.root u ≠ F.root v} =
      ∏ t ∈ (Finset.Ioc i (min (birthTime n u) (birthTime n v))).filter
        (fun t => x t = true), (1 - 1 / ((activeCount x t).toNat.choose 2 : ℝ)) := by
  rw [phaseLaw_separation_birth_product x n hn hu hv huv hi, Finset.prod_filter]
  rfl

/-- The actual probability that two terminal vertices are together at a phase. -/
theorem phaseLaw_coalesced_birth_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {i : ℕ} (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    (phaseLaw x n i).real {F | F.root u = F.root v} =
      1 - ∏ t ∈ Finset.Ioc i (min (birthTime n u) (birthTime n v)), separationFactor x t := by
  have he : {F : Forest | F.root u = F.root v} = {F | F.root u ≠ F.root v}ᶜ := by
    ext F
    simp
  rw [he, probReal_compl_eq_one_sub (by trivial),
    phaseLaw_separation_birth_product x n hn hu hv huv hi]

/-- The loss of separation between adjacent actual marginals is exactly the
source hazard times the subsequent survival product. This is a marginal
identity; it does not define a coalescence-time random variable. -/
theorem phaseLaw_separation_drop (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {i : ℕ} (hi : i < min (birthTime n u) (birthTime n v)) (hx : x (i + 1) = true) :
    (phaseLaw x n (i + 1)).real {F | F.root u ≠ F.root v} -
        (phaseLaw x n i).real {F | F.root u ≠ F.root v} =
      (1 / ((activeCount x (i + 1)).toNat.choose 2 : ℝ)) *
        ∏ t ∈ Finset.Ioc (i + 1) (min (birthTime n u) (birthTime n v)), separationFactor x t := by
  have hbn : min (birthTime n u) (birthTime n v) ≤ n :=
    (min_le_left _ _).trans (birthTime_le_of_mem hu)
  have hip : i + 1 ≤ n := by omega
  have huI : u ∈ phaseLabels x n (i + 1) :=
    (mem_phaseLabels_iff_birthTime hip hu).mpr (by omega)
  have hvI : v ∈ phaseLabels x n (i + 1) :=
    (mem_phaseLabels_iff_birthTime hip hv).mpr (by omega)
  rw [phaseLaw_separation_succ x n i hn (by omega) huI hvI,
    phaseLaw_separation_birth_product x n hn hu hv huv (by omega : i + 1 ≤ min (birthTime n u) (birthTime n v))]
  simp only [separationFactor, hx, ↓reduceIte]
  ring

end Freezing1.Reverse
