module

public import Freezing1.ReverseHistory
public import Freezing1.ReverseHeightLaw
public import Mathlib.Probability.ConditionalExpectation

/-!
# Height increments conditional on the whole reverse history

The predecessor variable records every earlier forest. Its joint law with
the new height increment factors as the actual old-history law times the
specified Bernoulli law. Thus the conditional probability in Lemma
`lem:accroissementH` follows from the constructed process, not from an
assumption of independent increments.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

def heightIncrement (v : ℕ ⊕ ℕ) (H : History) : ℕ :=
  H.current.depth v - (previous H).current.depth v

theorem forest_heightIncrement_hasLaw {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {v : ℕ ⊕ ℕ} (hv : v ∈ F.vertices) :
    HasLaw (fun F' : Reverse.Forest => F'.depth v - F.depth v)
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.attachmentParameter x n hn ⟨i, hi⟩))
      (Reverse.transitionLaw x i F) := by
  have hs := Reverse.transitionLaw_present_depth_support hn hi hF hv
  have hprob : (Reverse.transitionLaw x i F).real {F' | F'.depth v = F.depth v + 1} =
      (Reverse.attachmentParameter x n hn ⟨i, hi⟩ : ℝ) := by
    rw [Reverse.transitionLaw_height_increment hn hi hF hv, Reverse.attachmentParameter_coe]
  have hD := hasLaw_nat_succ_of_support
    (show Measurable (fun F' : Reverse.Forest => F'.depth v) from measurable_from_top)
    (hs.mono fun _ h => h.2) hprob
  have hshift : HasLaw (fun d : ℕ => d - F.depth v)
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.attachmentParameter x n hn ⟨i, hi⟩))
      (bernoulliMeasure (F.depth v + 1) (F.depth v)
        (Reverse.attachmentParameter x n hn ⟨i, hi⟩)) := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    rw [map_bernoulliMeasure]
    simp
  exact hshift.fun_comp hD

/-- Conditional on any admissible entire predecessor history, the new
increment has the same deterministic Bernoulli parameter. -/
theorem transitionLaw_previous_increment {x : SignSequence} {n i : ℕ} {H : History}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) H.current)
    {v : ℕ ⊕ ℕ} (hv : v ∈ H.current.vertices) :
    (transitionLaw x i H).map (fun H' => (previous H', heightIncrement v H')) =
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.attachmentParameter x n hn ⟨i, hi⟩)).map
        (Prod.mk H) := by
  have hD := forest_heightIncrement_hasLaw hn hi hF hv
  have hh := congrArg (fun μ : Measure ℕ => μ.map (Prod.mk H)) hD.map_eq
  rw [Measure.map_map (by fun_prop) measurable_from_top] at hh
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  simpa only [Function.comp_def, heightIncrement, push, previous, List.headD_cons,
    List.tail_cons] using hh

/-- The factorization is over the whole past history, not only its last forest. -/
theorem lawAfter_previous_increment_joint (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) (hbirth : n - k ≤ birthTime n v) :
    (lawAfter x n (k + 1)).map (fun H => (previous H, heightIncrement v H)) =
      (lawAfter x n k).prod
        (bernoulliMeasure (1 : ℕ) 0
          (Reverse.attachmentParameter x n hn ⟨n - (k + 1), by omega⟩)) := by
  rw [lawAfter, ite_eq_left hk,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.prod_eq_of_sfinite]
  apply Measure.bind_congr_right
  filter_upwards [lawAfter_current_valid x n k hn hk.le] with H hH
  have hphase : n - k = n - (k + 1) + 1 := by omega
  have hvH : v ∈ H.current.vertices := by
    rw [hH.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) hv).mpr hbirth
  rw [hphase] at hH
  exact transitionLaw_previous_increment hn (by omega) hH hvH

theorem lawAfter_heightIncrement_hasLaw (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) (hbirth : n - k ≤ birthTime n v) :
    HasLaw (heightIncrement v)
      (bernoulliMeasure (1 : ℕ) 0
        (Reverse.attachmentParameter x n hn ⟨n - (k + 1), by omega⟩))
      (lawAfter x n (k + 1)) := by
  refine ⟨measurable_from_top.aemeasurable, ?_⟩
  have hh := congrArg (fun μ : Measure (History × ℕ) => μ.map Prod.snd)
    (lawAfter_previous_increment_joint x n k hn hk hv hbirth)
  rw [Measure.map_map measurable_snd measurable_from_top] at hh
  simpa only [Function.comp_def, Measure.map_snd_prod, measure_univ, one_smul] using hh

/-- The genuine new increment is independent of the entire previous history. -/
theorem lawAfter_heightIncrement_indep_previous (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) (hbirth : n - k ≤ birthTime n v) :
    IndepFun (heightIncrement v) previous (lawAfter x n (k + 1)) := by
  have hprev : HasLaw previous (lawAfter x n k) (lawAfter x n (k + 1)) :=
    ⟨measurable_from_top.aemeasurable, map_lawAfter_previous x n k hk⟩
  have hinc := lawAfter_heightIncrement_hasLaw x n k hn hk hv hbirth
  have hJoint : HasLaw (fun H => (previous H, heightIncrement v H))
      ((lawAfter x n k).prod
        (bernoulliMeasure (1 : ℕ) 0
          (Reverse.attachmentParameter x n hn ⟨n - (k + 1), by omega⟩)))
      (lawAfter x n (k + 1)) :=
    ⟨measurable_from_top.aemeasurable, lawAfter_previous_increment_joint x n k hn hk hv hbirth⟩
  exact ((indepFun_iff_hasLaw_prodMk_prod hprev hinc).mpr hJoint).symm

/-- A precise conditional-expectation form of Lemma `lem:accroissementH`.
The conditioning sigma-algebra is generated by the complete predecessor
history, and the right side is the paper's attachment-masked reciprocal. -/
theorem height_increment_conditional_probability (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) (hbirth : n - k ≤ birthTime n v) :
    (lawAfter x n (k + 1))[
      (fun H => if heightIncrement v H = 1 then (1 : ℝ) else 0) |
      MeasurableSpace.comap previous (⊤ : MeasurableSpace History)] =ᵐ[lawAfter x n (k + 1)]
        fun _ => if x (n - k) then 1 / (activeCount x (n - k) : ℝ) else 0 := by
  let μ := lawAfter x n (k + 1)
  let m₁ := MeasurableSpace.comap (heightIncrement v) inferInstance
  let m₂ := MeasurableSpace.comap previous (⊤ : MeasurableSpace History)
  let f : History → ℝ := fun H => if heightIncrement v H = 1 then 1 else 0
  have hle₁ : m₁ ≤ (⊤ : MeasurableSpace History) := le_top
  have hle₂ : m₂ ≤ (⊤ : MeasurableSpace History) := le_top
  have hmeas : @Measurable History ℕ m₁ inferInstance (heightIncrement v) :=
    comap_measurable _
  have hf : StronglyMeasurable[m₁] f := by
    apply Measurable.stronglyMeasurable
    exact (measurable_of_countable (fun d : ℕ => if d = 1 then (1 : ℝ) else 0)).comp hmeas
  have hind : Indep m₁ m₂ μ := lawAfter_heightIncrement_indep_previous x n k hn hk hv hbirth
  have he := condExp_indep_eq hle₁ hle₂ hf hind
  have hinc := lawAfter_heightIncrement_hasLaw x n k hn hk hv hbirth
  have hint : (∫ H, f H ∂μ) =
      (Reverse.attachmentParameter x n hn ⟨n - (k + 1), by omega⟩ : ℝ) := by
    rw [show (∫ H, f H ∂μ) = ∫ d : ℕ, (if d = 1 then (1 : ℝ) else 0)
        ∂bernoulliMeasure (1 : ℕ) 0
          (Reverse.attachmentParameter x n hn ⟨n - (k + 1), by omega⟩) from
      hinc.integral_comp (f := fun d : ℕ => if d = 1 then (1 : ℝ) else 0) (by fun_prop)]
    rw [integral_bernoulliMeasure]
    simp
  rw [hint, Reverse.attachmentParameter_coe] at he
  have hphase : n - (k + 1) + 1 = n - k := by omega
  simpa only [hphase, μ, f, m₂] using he

end Freezing1.ReverseHistory
