module

public import Freezing1.ForwardForestConditionalChebyshev
public import Freezing1.ForwardConditionalGoodChain

/-! Source A53: integrate the full-forest conditional Chebyshev bound. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Integrating a genuine conditional event bound over an observed event.
This is the tower step used below, not an assumed conditional kernel. -/
theorem real_inter_le_of_observed_condExp {B : Type*} [MeasurableSpace B]
    (μ : Measure State) [IsFiniteMeasure μ] (O : State → B)
    (S : Set B) (hS : MeasurableSet S) (D : Set State) {r : ℝ}
    (hbound : ∀ᵐ q ∂μ, O q ∈ S →
      μ[D.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap O inferInstance] q ≤ r) :
    μ.real (O ⁻¹' S ∩ D) ≤ r * μ.real (O ⁻¹' S) := by
  have hO : Measurable O := measurable_from_top
  have hOc : @Measurable State B (MeasurableSpace.comap O inferInstance) inferInstance O :=
    measurable_iff_comap_le.mpr le_rfl
  have hSO : MeasurableSet[MeasurableSpace.comap O inferInstance] (O ⁻¹' S) := hS.preimage hOc
  have hD : MeasurableSet D := by trivial
  have hi : Integrable (D.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hD
  calc
    _ = ∫ q in O ⁻¹' S, D.indicator (fun _ => (1 : ℝ)) q ∂μ := by
      rw [setIntegral_indicator hD, setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    _ = ∫ q in O ⁻¹' S,
        μ[D.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap O inferInstance] q ∂μ :=
      (setIntegral_condExp hO.comap_le hi hSO).symm
    _ ≤ ∫ _q in O ⁻¹' S, r ∂μ :=
      setIntegral_mono_on_ae integrable_condExp.integrableOn (integrable_const _).integrableOn
        (hO hS) hbound
    _ = _ := by rw [setIntegral_const]; simp only [smul_eq_mul, mul_comm]

theorem treeLaw_favorable_goodChain_failure_le_from_forest (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) {target cap : ℝ}
    (hTarget : 0 < target) (hCap : 0 ≤ cap) :
    (treeLaw x (C ^ (k + 1))).real {q |
      target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) ∧
      4 * ((C ^ k : ℕ) : ℝ) ≤ (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ∧
      (componentMaximum q (C ^ k) : ℝ) ≤ cap ∧
      ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * target} ≤
      (3 * cap / target) * (treeLaw x (C ^ (k + 1))).real {q |
        target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)} := by
  let a := C ^ k
  let z := C ^ (k + 1)
  let μ := treeLaw x z
  let m := (activeCount x a).toNat
  have haz : a ≤ z := pow_le_pow_right₀ hC (Nat.le_succ k)
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast haz : (a : ℕ∞) ≤ z).trans hb
  have hm : m ≤ a + 1 := by
    have hn := activeCount_nonneg_of_le_extinctionTime haτ
    have hu := activeCount_le_plusCount_add_one x a
    have hp := plusCount_le x a
    dsimp only [m]
    omega
  let O := pastBareForest x a
  let S : Set (State × RootErasedForest m) := {u |
    target ≤ ((goodSet u.1 C k₀ k t).card : ℝ) ∧
    4 * (a : ℝ) ≤ (bareForestTallCount a m hm t u.2 : ℝ) ∧
    (bareForestComponentMaximum a m hm u.2 : ℝ) ≤ cap}
  let Old : Set State := {q | target ≤ ((goodSet (truncateAt q a) C k₀ k t).card : ℝ)}
  let Bad : Set State := {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * target}
  have hS : MeasurableSet S := by
    have hg : Measurable (fun u : State × RootErasedForest m => ((goodSet u.1 C k₀ k t).card : ℝ)) :=
      (show Measurable (fun s : State => ((goodSet s C k₀ k t).card : ℝ)) from measurable_from_top).comp measurable_fst
    have hn : Measurable (fun u : State × RootErasedForest m => (bareForestTallCount a m hm t u.2 : ℝ)) :=
      (show Measurable (fun F : RootErasedForest m => (bareForestTallCount a m hm t F : ℝ)) from measurable_from_top).comp measurable_snd
    have hM : Measurable (fun u : State × RootErasedForest m => (bareForestComponentMaximum a m hm u.2 : ℝ)) :=
      (show Measurable (fun F : RootErasedForest m => (bareForestComponentMaximum a m hm F : ℝ)) from measurable_from_top).comp measurable_snd
    exact (measurableSet_le measurable_const hg).inter
      ((measurableSet_le measurable_const hn).inter (measurableSet_le hM measurable_const))
  have hobs : ∀ᵐ q ∂μ, O q ∈ S ↔ q ∈ Old ∧
      4 * (a : ℝ) ≤ (blockTallCount q a z t : ℝ) ∧ (componentMaximum q a : ℝ) ≤ cap := by
    filter_upwards [treeLaw_hasHistory x z hb] with q hq
    change (target ≤ ((goodSet (truncateAt q a) C k₀ k t).card : ℝ) ∧
      4 * (a : ℝ) ≤ (bareForestTallCount a m hm t (bareSlotOrbit m (slotForest q a)) : ℝ) ∧
      (bareForestComponentMaximum a m hm (bareSlotOrbit m (slotForest q a)) : ℝ) ≤ cap) ↔ _
    rw [bareForestTallCount_actual hq hb a m hm ht,
      bareForestComponentMaximum_actual hq hb haz hm]
    rfl
  have hce := condExp_goodSet_doubling_on_favorable_forest x hC hk hb ha ht hTarget
  have hbound : ∀ᵐ q ∂μ, O q ∈ S →
      μ[Bad.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap O inferInstance] q ≤ 3 * cap / target := by
    filter_upwards [hce, hobs] with q hq hobsq hS_q
    obtain ⟨hG, hN, hM⟩ := hobsq.mp hS_q
    have hh := hq hG (by simpa only [a, z, Nat.cast_pow] using hN)
    have hI : Bad.indicator (fun _ => (1 : ℝ)) =
        (fun r => if ((goodSet r C k₀ (k + 1) t).card : ℝ) < 2 * target then 1 else 0) := rfl
    rw [hI]
    exact hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) hTarget.le)
  have hi := real_inter_le_of_observed_condExp μ O S hS Bad hbound
  have hleft : μ.real (O ⁻¹' S ∩ Bad) = μ.real {q | q ∈ Old ∧
      4 * (a : ℝ) ≤ (blockTallCount q a z t : ℝ) ∧
      (componentMaximum q a : ℝ) ≤ cap ∧ q ∈ Bad} := by
    have hevents : (O ⁻¹' S ∩ Bad) =ᵐ[μ] {q | q ∈ Old ∧
        4 * (a : ℝ) ≤ (blockTallCount q a z t : ℝ) ∧
        (componentMaximum q a : ℝ) ≤ cap ∧ q ∈ Bad} := by
      filter_upwards [hobs] with q hq
      simp only [Set.mem_inter_iff, Set.mem_preimage, hq, and_assoc]
    exact congrArg ENNReal.toReal (measure_congr hevents)
  rw [hleft] at hi
  have hsub : O ⁻¹' S ⊆ Old := fun q hq => hq.1
  simpa only [a, z, μ, Old, Bad, Set.mem_ofPred_eq] using
    hi.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _)) (by positivity))

/-- Exact source failure decomposition, using the new full-forest conditional
Chebyshev and its tower integration for the favorable contribution. -/
theorem treeLaw_goodChain_failure_inter_le_from_forest (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) {target cap : ℝ}
    (hTarget : 0 < target) (hCap : 0 ≤ cap) :
    (treeLaw x (C ^ (k + 1))).real {q |
      target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) ∧
      ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * target} ≤
      ((treeLaw x (C ^ (k + 1))).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * ((C ^ k : ℕ) : ℝ)} +
       (treeLaw x (C ^ (k + 1))).real {q | cap < (componentMaximum q (C ^ k) : ℝ)} +
       3 * cap / target) *
      (treeLaw x (C ^ (k + 1))).real {q |
        target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)} := by
  let a := C ^ k
  let z := C ^ (k + 1)
  let μ := treeLaw x z
  let A : Set State := {s | target ≤ ((goodSet s C k₀ k t).card : ℝ)}
  let Old : Set State := {q | truncateAt q a ∈ A}
  let Bad : Set State := {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * target}
  let Nbad : Set State := {q | (blockTallCount q a z t : ℝ) ≤ 4 * (a : ℝ)}
  let Mbad : Set State := {q | cap < (componentMaximum q a : ℝ)}
  let R : Set State := {q | 4 * (a : ℝ) ≤ (blockTallCount q a z t : ℝ) ∧
    (componentMaximum q a : ℝ) ≤ cap ∧ q ∈ Bad}
  have haz : a ≤ z := pow_le_pow_right₀ hC (Nat.le_succ k)
  have hR : μ.real (Old ∩ R) ≤ 3 * cap / target * μ.real Old := by
    simpa only [a, z, μ, Old, R, A, Bad, Set.inter_def, Set.mem_ofPred_eq] using
      treeLaw_favorable_goodChain_failure_le_from_forest x hC hk hτ ha ht hTarget hCap
  have hN : μ.real (Old ∩ Nbad) = μ.real Old * μ.real Nbad := by
    simpa only [μ, Old, Nbad, Set.inter_def, Set.mem_ofPred_eq] using
      treeLaw_prefix_blockStatistics_factorization_at_endpoint x haz hτ t A (by trivial)
        {p : ℕ × ℕ | (p.1 : ℝ) ≤ 4 * (a : ℝ)} (by measurability)
  have hM : μ.real (Old ∩ Mbad) = μ.real Old * μ.real Mbad := by
    simpa only [μ, Old, Mbad, Set.inter_def, Set.mem_ofPred_eq] using
      treeLaw_prefix_blockStatistics_factorization_at_endpoint x haz hτ t A (by trivial)
        {p : ℕ × ℕ | cap < (p.2 : ℝ)} (by measurability)
  have hsub : Old ∩ Bad ⊆ (Old ∩ Nbad) ∪ (Old ∩ Mbad) ∪ (Old ∩ R) := by
    intro q hq
    by_cases hNq : q ∈ Nbad
    · exact Or.inl (Or.inl ⟨hq.1, hNq⟩)
    by_cases hMq : q ∈ Mbad
    · exact Or.inl (Or.inr ⟨hq.1, hMq⟩)
    exact Or.inr ⟨hq.1, (not_le.mp hNq).le, not_lt.mp hMq, hq.2⟩
  calc
    _ = μ.real (Old ∩ Bad) := rfl
    _ ≤ μ.real ((Old ∩ Nbad) ∪ (Old ∩ Mbad) ∪ (Old ∩ R)) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (μ.real (Old ∩ Nbad) + μ.real (Old ∩ Mbad)) + μ.real (Old ∩ R) :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ (μ.real Old * μ.real Nbad + μ.real Old * μ.real Mbad) + 3 * cap / target * μ.real Old := by
      rw [hN, hM]
      exact add_le_add le_rfl hR
    _ = _ := by
      change (μ.real Old * μ.real Nbad + μ.real Old * μ.real Mbad) +
        3 * cap / target * μ.real Old = (μ.real Nbad + μ.real Mbad + 3 * cap / target) * μ.real Old
      ring

/-- Actual normalized one-step conditional probability through the full
forest argument. Null conditioning events use Mathlib's zero measure. -/
theorem treeLaw_cond_goodChain_failure_le_from_forest (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) {target cap : ℝ}
    (hTarget : 0 < target) (hCap : 0 ≤ cap) :
    (ProbabilityTheory.cond (treeLaw x (C ^ (k + 1)))
      {q | target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)}).real
      {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * target} ≤
      (treeLaw x (C ^ (k + 1))).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * ((C ^ k : ℕ) : ℝ)} +
      (treeLaw x (C ^ (k + 1))).real {q | cap < (componentMaximum q (C ^ k) : ℝ)} +
      3 * cap / target := by
  apply cond_real_le_of_inter_le_mul _ _ _ (by trivial) (by positivity)
  exact treeLaw_goodChain_failure_inter_le_from_forest x hC hk hτ ha ht hTarget hCap

end Freezing1.Forward
