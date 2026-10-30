module

public import Freezing1.ReverseForest
public import Freezing1.BernoulliProductLaw
public import Mathlib.Probability.IdentDistrib

/-!
# The height law of a fixed reverse vertex

The tracked height is zero before a vertex appears. The Bernoulli parameter
is masked by both the attachment sign and the vertex's exact birth time.
Thus the extinction endpoint never introduces a Bernoulli parameter `1 / 0`.
The terminal comparison is a marginal equality for each fixed vertex; it is
not a joint representation of the depths of several vertices. Conditional
probabilities on a coherent reverse-history space remain separate.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators

/-- A natural-valued variable supported at two consecutive values has the
corresponding shifted Bernoulli law. -/
theorem hasLaw_nat_succ_of_support {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℕ} {d : ℕ} {p : unitInterval}
    (hZ : Measurable Z) (hsupport : ∀ᵐ ω ∂μ, Z ω = d ∨ Z ω = d + 1)
    (hp : μ.real {ω | Z ω = d + 1} = (p : ℝ)) :
    HasLaw Z (bernoulliMeasure (d + 1) d p) μ := by
  let s : Set Ω := {ω | Z ω = d + 1}
  have hs : MeasurableSet s := hZ (measurableSet_singleton (d + 1))
  have hp' : (⟨μ.real s, by simp⟩ : unitInterval) = p := Subtype.ext hp
  have hI : HasLaw (s.indicator (fun _ => (1 : ℕ))) (bernoulliMeasure 1 0 p) μ := by
    simpa only [hp', Pi.one_def] using
      (hasLaw_indicator_one_bernoulliMeasure (P := μ) (M := ℕ) hs.nullMeasurableSet)
  have hshift : HasLaw (fun z : ℕ => d + z) (bernoulliMeasure (d + 1) d p)
      (bernoulliMeasure 1 0 p) := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    simpa only [Nat.add_zero] using map_bernoulliMeasure 1 0 (fun z : ℕ => d + z) p
  apply (hshift.fun_comp hI).congr
  filter_upwards [hsupport] with ω hω
  rcases hω with hω | hω <;> simp [s, hω]

namespace Reverse

/-- The height process is totalized by zero while the tracked label is absent. -/
def trackedDepth (v : ℕ ⊕ ℕ) (F : Forest) : ℕ :=
  if v ∈ F.vertices then F.depth v else 0

/-- Masked Bernoulli parameter for one paper step and one fixed label. -/
noncomputable def heightParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (v : ℕ ⊕ ℕ) (i : Fin n) : unitInterval :=
  if h : x (i.val + 1) = true ∧ i.val + 1 ≤ birthTime n v then
    ⟨1 / (activeCount x (i.val + 1) : ℝ), by
      have hiτ : ((i.val + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
        le_trans (by exact_mod_cast Nat.succ_le_of_lt i.isLt) hn
      have htwo : (2 : ℝ) ≤ activeCount x (i.val + 1) := by
        exact_mod_cast two_le_activeCount_succ_of_attachment hiτ h.1
      have hp : (0 : ℝ) < activeCount x (i.val + 1) := by linarith
      exact ⟨one_div_nonneg.mpr hp.le, (div_le_iff₀ hp).mpr (by linarith)⟩⟩
  else 0

theorem heightParameter_coe (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (v : ℕ ⊕ ℕ) (i : Fin n) :
    (heightParameter x n hn v i : ℝ) =
      if x (i.val + 1) = true ∧ i.val + 1 ≤ birthTime n v then
        1 / (activeCount x (i.val + 1) : ℝ) else 0 := by
  unfold heightParameter
  split_ifs <;> rfl

/-- The common auxiliary family depends only on the schedule, not the tracked
vertex. Freezing coordinates have parameter zero. -/
noncomputable def attachmentParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) : unitInterval :=
  heightParameter x n hn (.inl 0) i

theorem attachmentParameter_coe (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) :
    (attachmentParameter x n hn i : ℝ) =
      if x (i.val + 1) then 1 / (activeCount x (i.val + 1) : ℝ) else 0 := by
  rw [attachmentParameter, heightParameter_coe]
  simp only [birthTime, Nat.succ_le_of_lt i.isLt, and_true]

theorem heightParameter_eq_attachmentParameter {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} {i : Fin n}
    (hi : i.val < birthTime n v) :
    heightParameter x n hn v i = attachmentParameter x n hn i := by
  apply Subtype.ext
  rw [heightParameter_coe, attachmentParameter_coe]
  simp only [Nat.succ_le_of_lt hi, and_true]

theorem heightParameter_eq_zero_of_not_before_birth {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} {i : Fin n}
    (hi : ¬ i.val < birthTime n v) : heightParameter x n hn v i = 0 := by
  apply Subtype.ext
  rw [heightParameter_coe]
  have hn' : ¬ i.val + 1 ≤ birthTime n v := by omega
  simp only [hn', and_false, ↓reduceIte]
  rfl

/-- Coordinates processed by `k` reverse steps and present after the vertex's birth. -/
def heightIndices (n : ℕ) (v : ℕ ⊕ ℕ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => n - k ≤ i.val ∧ i.val < birthTime n v

@[simp] theorem heightIndices_zero (n : ℕ) (v : ℕ ⊕ ℕ) : heightIndices n v 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [heightIndices, Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_zero] at hi
  exact (not_le_of_gt i.isLt) hi.1

theorem heightIndices_not_mem_next (n : ℕ) (v : ℕ ⊕ ℕ) {k : ℕ} (hk : k < n) :
    (⟨n - (k + 1), by omega⟩ : Fin n) ∉ heightIndices n v k := by
  simp only [heightIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem heightIndices_succ_of_before_birth (n : ℕ) (v : ℕ ⊕ ℕ) {k : ℕ}
    (hk : k < n) (hb : n - (k + 1) < birthTime n v) :
    heightIndices n v (k + 1) = insert ⟨n - (k + 1), by omega⟩ (heightIndices n v k) := by
  ext i
  simp only [heightIndices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

theorem heightIndices_succ_of_not_before_birth (n : ℕ) (v : ℕ ⊕ ℕ) {k : ℕ}
    (hk : k < n) (hb : ¬ n - (k + 1) < birthTime n v) :
    heightIndices n v (k + 1) = heightIndices n v k := by
  ext i
  simp only [heightIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem heightIndices_full (n : ℕ) (v : ℕ ⊕ ℕ) :
    heightIndices n v n = Finset.univ.filter fun i : Fin n => i.val < birthTime n v := by
  simp [heightIndices]

theorem trackedDepth_initial (x : SignSequence) (n : ℕ) (v : ℕ ⊕ ℕ) :
    trackedDepth v (initial x n) = 0 := by
  simp [trackedDepth, initial, RootedForest.isolated]

theorem trackedDepth_insertLabel_of_absent (F : Forest) (i : ℕ) {v : ℕ ⊕ ℕ}
    (hv : v ∉ F.vertices) : trackedDepth v (insertLabel F i) = 0 := by
  by_cases hi : Sum.inr i ∈ F.vertices
  · simp [insertLabel, hi, trackedDepth, hv]
  · by_cases hvi : v = Sum.inr i
    · subst v
      simp [insertLabel, hi, trackedDepth, RootedForest.adjoin]
    · have hn : v ∉ insert (Sum.inr i) F.vertices := by simp [hvi, hv]
      simp [insertLabel, hi, trackedDepth, RootedForest.adjoin_vertices, hn]

/-- A present vertex remains present and changes height by either zero or one. -/
theorem transitionLaw_present_depth_support {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {v : ℕ ⊕ ℕ} (hv : v ∈ F.vertices) :
    ∀ᵐ F' ∂transitionLaw x i F,
      v ∈ F'.vertices ∧ (F'.depth v = F.depth v ∨ F'.depth v = F.depth v + 1) := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
  cases hx : x (i + 1)
  · have hfresh : Sum.inr i ∉ F.vertices := by
      rw [hF.vertices_eq]
      exact fresh_freezing_label x n i
    simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    apply (ae_dirac_iff (by trivial)).mpr
    rw [insertLabel, dite_eq_right hfresh]
    exact ⟨Finset.mem_insert_of_mem hv, Or.inl (RootedForest.adjoin_depth_old F hfresh hv)⟩
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [transitionLaw, hx, ↓reduceIte]
    filter_upwards [F.joinLaw_vertices htwo, F.joinLaw_depth_support htwo v] with F' hv' hd
    exact ⟨hv' ▸ hv, hd⟩

/-- Before its birth a tracked label still has height zero after a reverse
transition; its insertion also creates it at height zero. -/
theorem transitionLaw_absent_trackedDepth {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {v : ℕ ⊕ ℕ} (hv : v ∉ F.vertices) :
    ∀ᵐ F' ∂transitionLaw x i F, trackedDepth v F' = 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
  cases hx : x (i + 1)
  · simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr (trackedDepth_insertLabel_of_absent F i hv)
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [transitionLaw, hx, ↓reduceIte]
    filter_upwards [F.joinLaw_vertices htwo] with F' hv'
    simp only [trackedDepth, hv', ite_eq_right hv]

/-- The tracked height transition is exactly a shifted Bernoulli law with a
deterministic, birth-masked parameter. It also covers an empty terminal forest. -/
theorem transitionLaw_trackedDepth_hasLaw {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    HasLaw (trackedDepth v)
      (bernoulliMeasure (trackedDepth v F + 1) (trackedDepth v F)
        (heightParameter x n hn v ⟨i, hi⟩)) (transitionLaw x i F) := by
  by_cases hpresent : v ∈ F.vertices
  · have hbirth : i + 1 ≤ birthTime n v :=
      (mem_phaseLabels_iff_birthTime (by omega) hv).mp (hF.vertices_eq ▸ hpresent)
    have hs := transitionLaw_present_depth_support hn hi hF hpresent
    have hprob : (transitionLaw x i F).real {F' | F'.depth v = F.depth v + 1} =
        (heightParameter x n hn v ⟨i, hi⟩ : ℝ) := by
      rw [transitionLaw_height_increment hn hi hF hpresent, heightParameter_coe]
      simp only [hbirth, and_true]
    have hdepth := hasLaw_nat_succ_of_support
      (show Measurable (fun F' : Forest => F'.depth v) from measurable_from_top)
      (hs.mono fun _ h => h.2) hprob
    have hae : trackedDepth v =ᵐ[transitionLaw x i F] fun F' => F'.depth v := by
      filter_upwards [hs] with F' h
      exact ite_eq_left h.1
    simpa only [trackedDepth, ite_eq_left hpresent] using hdepth.congr hae
  · have hbirth : ¬ i + 1 ≤ birthTime n v := by
      intro hb
      have hvphase := (mem_phaseLabels_iff_birthTime (by omega) hv).mpr hb
      exact hpresent (hF.vertices_eq.symm ▸ hvphase)
    have hparam : heightParameter x n hn v ⟨i, hi⟩ = 0 := by
      apply Subtype.ext
      rw [heightParameter_coe]
      simp only [hbirth, and_false, ↓reduceIte]
      rfl
    rw [hparam, bernoulliMeasure_zero, trackedDepth, ite_eq_right hpresent]
    have hzero : HasLaw (fun _ : Forest => (0 : ℕ)) (Measure.dirac 0)
        (transitionLaw x i F) := ⟨aemeasurable_const, by simp⟩
    exact hzero.congr (transitionLaw_absent_trackedDepth hn hi hF hpresent)

/-- Every actual reverse marginal has the law of the corresponding sum of
coordinates on one common, explicitly independent Bernoulli product space. -/
theorem lawAfter_trackedDepth_hasLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    (k : ℕ) (hk : k ≤ n) :
    HasLaw (trackedDepth v)
      (bernoulliPartialSumLaw (attachmentParameter x n hn) (heightIndices n v k))
      (lawAfter x n k) := by
  induction k with
  | zero =>
    refine ⟨measurable_from_top.aemeasurable, ?_⟩
    rw [lawAfter, Measure.map_dirac' measurable_from_top, trackedDepth_initial,
      heightIndices_zero, bernoulliPartialSumLaw_empty]
  | succ k ih =>
    have hkn : k < n := by omega
    have ih := ih (by omega)
    let j : Fin n := ⟨n - (k + 1), by omega⟩
    have hphase : n - k = j.val + 1 := by dsimp [j]; omega
    have hmap : (lawAfter x n (k + 1)).map (trackedDepth v) =
        ((lawAfter x n k).map (trackedDepth v)).bind
          (fun d => bernoulliMeasure (d + 1) d (heightParameter x n hn v j)) := by
      rw [lawAfter, ite_eq_left hkn,
        Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
        Measure.bind_map measurable_from_top.aemeasurable (measurable_of_countable _).aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards [lawAfter_valid x n k hn (by omega)] with F hF
      rw [hphase] at hF
      exact (transitionLaw_trackedDepth_hasLaw hn j.isLt hF hv).map_eq
    refine ⟨measurable_from_top.aemeasurable, ?_⟩
    rw [hmap, ih.map_eq]
    by_cases hb : j.val < birthTime n v
    · rw [heightIndices_succ_of_before_birth n v hkn hb,
        heightParameter_eq_attachmentParameter hn hb,
        bernoulliPartialSumLaw_insert _ _ (heightIndices_not_mem_next n v hkn)]
    · rw [heightIndices_succ_of_not_before_birth n v hkn hb,
        heightParameter_eq_zero_of_not_before_birth hn hb]
      simp

/-- The actual terminal depth law, including active labels born at `n` and
frozen labels born at their paper index minus one. -/
theorem treeLaw_depth_hasLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    HasLaw (fun F : Forest => F.depth v)
      (bernoulliPartialSumLaw (attachmentParameter x n hn)
        (Finset.univ.filter fun i : Fin n => i.val < birthTime n v)) (treeLaw x n) := by
  have ht : HasLaw (trackedDepth v)
      (bernoulliPartialSumLaw (attachmentParameter x n hn)
        (Finset.univ.filter fun i : Fin n => i.val < birthTime n v)) (treeLaw x n) := by
    simpa only [treeLaw, heightIndices_full] using
      lawAfter_trackedDepth_hasLaw x n hn hv n le_rfl
  apply ht.congr
  filter_upwards [treeLaw_vertices_and_root x n hn] with F hF
  have hvF : v ∈ F.vertices := by rwa [hF.1]
  simp only [trackedDepth, ite_eq_left hvF]

/-- The distributional representation in `eq:H0`, with the necessary
attachment mask already included in the Bernoulli parameters. The auxiliary
product depends only on the schedule. This is a per-vertex equality in law,
not a simultaneous representation of the depths of different vertices. -/
theorem treeLaw_depth_identDistrib_bernoulli (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    IdentDistrib (fun F : Forest => F.depth v)
      (fun ω : Fin n → ℕ => ∑ i ∈ Finset.univ.filter
        (fun i : Fin n => i.val < birthTime n v), ω i)
      (treeLaw x n) (bernoulliProductLaw (attachmentParameter x n hn)) :=
  (treeLaw_depth_hasLaw x n hn hv).identDistrib
    (bernoulliPartialSumLaw_hasLaw _ _)

/-- The real-valued coordinates of the auxiliary row are independent. -/
theorem heightBernoulli_independent (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    iIndepFun (fun i (ω : Fin n → ℕ) => (ω i : ℝ))
      (bernoulliProductLaw (attachmentParameter x n hn)) := by
  simpa only [Function.comp_def] using
    (bernoulliProductLaw_independent (attachmentParameter x n hn)).comp
      (fun (_ : Fin n) (k : ℕ) => (k : ℝ)) (fun _ => measurable_of_countable _)

/-- Every real-valued auxiliary coordinate has the actual masked parameter. -/
theorem heightBernoulli_hasLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) :
    HasLaw (fun ω : Fin n → ℕ => (ω i : ℝ))
      (bernoulliMeasure (1 : ℝ) 0 (attachmentParameter x n hn i))
      (bernoulliProductLaw (attachmentParameter x n hn)) := by
  have hcast : HasLaw (fun k : ℕ => (k : ℝ))
      (bernoulliMeasure (1 : ℝ) 0 (attachmentParameter x n hn i))
      (bernoulliMeasure (1 : ℕ) 0 (attachmentParameter x n hn i)) := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    simpa only [Nat.cast_one, Nat.cast_zero] using
      map_bernoulliMeasure 1 0 (fun k : ℕ => (k : ℝ)) (attachmentParameter x n hn i)
  exact hcast.fun_comp (bernoulliProductLaw_coordinate _ i)

/-- The real-valued form of `eq:H0`, ready for concentration and moment bounds. -/
theorem treeLaw_height_identDistrib_bernoulli (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    IdentDistrib (fun F : Forest => (F.depth v : ℝ))
      (fun ω : Fin n → ℕ => ∑ i ∈ Finset.univ.filter
        (fun i : Fin n => i.val < birthTime n v), (ω i : ℝ))
      (treeLaw x n) (bernoulliProductLaw (attachmentParameter x n hn)) := by
  simpa only [Function.comp_def, Nat.cast_sum] using
    (treeLaw_depth_identDistrib_bernoulli x n hn hv).comp
      (u := fun k : ℕ => (k : ℝ)) (measurable_of_countable _)

end Reverse
end Freezing1
