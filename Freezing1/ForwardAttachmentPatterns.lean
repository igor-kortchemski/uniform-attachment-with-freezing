module

public import Freezing1.ForwardVertexDegree
public import Freezing1.ForwardLifetimeLimit
public import Freezing1.ForwardDegreeProducts

/-!
# Actual finite attachment patterns jointly with survival

At an attachment time `i`, the persistent parent of vertex `i` records the
chosen active individual. All constrained times are strictly after the
observed vertex's birth. The product law is derived from the genuine
uniform transition kernels, retaining the population at time `i - 1`.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def attachmentPattern (r : ℕ) (F : Finset ℕ) (ε : ℕ → Bool) (n : ℕ) (s : State) : Prop :=
  ∀ i ∈ F, i ≤ n → (s.parent i = r ↔ ε i = true)

noncomputable def attachmentPatternFactor (x : SignSequence) (F : Finset ℕ)
    (ε : ℕ → Bool) (i : ℕ) : ℝ :=
  if i ∈ F then
    if ε i then 1 / (activeCount x (i - 1) : ℝ)
    else 1 - 1 / (activeCount x (i - 1) : ℝ)
  else 1

theorem attachmentPattern_step {x : SignSequence} {n r : ℕ} {s : State}
    {F : Finset ℕ} (hF : ∀ i ∈ F, x i = true) (ε : ℕ → Bool)
    {p : ℕ} (hp : p ∈ s.active) :
    attachmentPattern r F ε (n + 1) (step s (n + 1) (x (n + 1)) p) ↔
      attachmentPattern r F ε n s ∧
        (n + 1 ∈ F → (p = r ↔ ε (n + 1) = true)) := by
  have hold : ∀ i ≤ n, (step s (n + 1) (x (n + 1)) p).parent i = s.parent i := by
    intro i hi
    have hne : i ≠ n + 1 := by omega
    rw [step, ite_eq_left hp]
    cases x (n + 1) <;> simp [attach, freeze, hne]
  have hnew : n + 1 ∈ F → (step s (n + 1) (x (n + 1)) p).parent (n + 1) = p := by
    intro hm
    simp [step, hp, hF _ hm, attach]
  constructor
  · intro h
    exact ⟨fun i hi hin => by simpa only [hold i hin] using h i hi (by omega),
      fun hi => by simpa only [hnew hi] using h (n + 1) hi le_rfl⟩
  · rintro ⟨h, hn⟩ i hi hin
    by_cases he : i = n + 1
    · subst i
      simpa only [hnew hi] using hn hi
    · have hi' : i ≤ n := by omega
      simpa only [hold i hi'] using h i hi hi'

theorem transitionLaw_attachmentPattern {x : SignSequence} {n r : ℕ} {s : State}
    (hs : PhaseData x n s) (hne : s.active.Nonempty) (hr : r ≤ n)
    {F : Finset ℕ} (hF : ∀ i ∈ F, x i = true) (ε : ℕ → Bool) :
    (transitionLaw s (n + 1) (x (n + 1))).real
        {q | r ∈ q.active ∧ attachmentPattern r F ε (n + 1) q} =
      (if r ∈ s.active ∧ attachmentPattern r F ε n s then (1 : ℝ) else 0) *
        (vertexSurvivalFactor x (n + 1) * attachmentPatternFactor x F ε (n + 1)) := by
  have he : ∀ p ∈ s.active,
      (r ∈ (step s (n + 1) (x (n + 1)) p).active ∧
        attachmentPattern r F ε (n + 1) (step s (n + 1) (x (n + 1)) p)) ↔
      (r ∈ s.active ∧ attachmentPattern r F ε n s) ∧
        ((x (n + 1) = true ∨ r ≠ p) ∧
          (n + 1 ∈ F → (p = r ↔ ε (n + 1) = true))) := by
    intro p hp
    rw [step_active_old hr hp, attachmentPattern_step hF ε hp]
    tauto
  have hc : (s.active.card : ℝ) = activeCount x n := by exact_mod_cast hs.count
  have hc0 : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  change ((transitionLaw s (n + 1) (x (n + 1))) _).toReal = _
  rw [transitionLaw_apply _ _ _ hne]
  have hfilter : s.active.filter
      (fun p => step s (n + 1) (x (n + 1)) p ∈
        {q | r ∈ q.active ∧ attachmentPattern r F ε (n + 1) q}) =
      if r ∈ s.active ∧ attachmentPattern r F ε n s then
        (if n + 1 ∈ F then
          (if ε (n + 1) then {r} else s.active.erase r)
        else if x (n + 1) then s.active else s.active.erase r)
      else ∅ := by
    ext p
    by_cases hp : p ∈ s.active
    · simp only [Finset.mem_filter, hp, true_and, Set.mem_ofPred_eq, he p hp]
      by_cases hA : r ∈ s.active ∧ attachmentPattern r F ε n s
      · simp only [hA, true_and, ↓reduceIte]
        by_cases hn : n + 1 ∈ F
        · have hx := hF _ hn
          by_cases hpr : p = r
          · cases hε : ε (n + 1) <;> simp [hn, hx, hε, hp, hpr]
          · cases hε : ε (n + 1) <;> simp [hn, hx, hε, hp, hpr, Ne.symm hpr]
        · by_cases hpr : p = r
          · cases hx : x (n + 1) <;> simp [hn, hx, hp, hpr, hA.1]
          · cases hx : x (n + 1) <;> simp [hn, hx, hp, hpr, Ne.symm hpr]
      · simp [hA]
    · simp only [Finset.mem_filter, hp, false_and]
      by_cases hA : r ∈ s.active ∧ attachmentPattern r F ε n s
      · simp only [hA, ↓reduceIte]
        have hpr : p ≠ r := fun he => hp (he ▸ hA.1)
        by_cases hn : n + 1 ∈ F <;>
          cases ε (n + 1) <;> cases x (n + 1) <;> simp [hn, hp, hpr]
      · simp [hA]
  simp only [Set.mem_ofPred_eq] at hfilter ⊢
  erw [hfilter]
  by_cases hA : r ∈ s.active ∧ attachmentPattern r F ε n s
  · simp only [hA, ↓reduceIte, one_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
    by_cases hn : n + 1 ∈ F
    · have hx := hF _ hn
      cases hε : ε (n + 1)
      · simp only [hn, hε, Bool.false_eq_true, ↓reduceIte, Finset.card_erase_of_mem hA.1,
          vertexSurvivalFactor, hx, attachmentPatternFactor, Nat.add_sub_cancel, one_mul,
          and_self, ↓reduceIte]
        rw [Nat.cast_sub (by have := hne.card_pos; omega), Nat.cast_one, ← hc]
        field_simp
      · simp [hn, hε, vertexSurvivalFactor, hx, attachmentPatternFactor, hc]
    · cases hx : x (n + 1)
      · simp only [hn, hx, Bool.false_eq_true, ↓reduceIte, Finset.card_erase_of_mem hA.1,
          vertexSurvivalFactor, attachmentPatternFactor, Nat.add_sub_cancel, mul_one,
          and_self, ↓reduceIte, one_mul]
        rw [Nat.cast_sub (by have := hne.card_pos; omega), Nat.cast_one, ← hc]
        field_simp
      · simp [hn, hx, vertexSurvivalFactor, attachmentPatternFactor, hc0]
  · simp [hA]

theorem treeLaw_attachmentPattern_survival (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r k : ℕ) {F : Finset ℕ}
    (hF : ∀ i ∈ F, r < i ∧ x i = true) (ε : ℕ → Bool) :
    (treeLaw x (r + k)) {s | r ∈ s.active ∧ attachmentPattern r F ε (r + k) s} =
      (treeLaw x r) {s | r ∈ s.active} *
        ∏ i ∈ Finset.Ioc r (r + k), ENNReal.ofReal
          (vertexSurvivalFactor x i * attachmentPatternFactor x F ε i) := by
  induction k with
  | zero =>
    have he : ∀ s, attachmentPattern r F ε r s := by
      intro s i hi hin
      have := (hF i hi).1
      omega
    simp [he]
  | succ k ih =>
    rw [show r + (k + 1) = (r + k) + 1 by omega, treeLaw,
      Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ s, {s : State | r ∈ s.active ∧ attachmentPattern r F ε (r + k) s}.indicator
          (fun _ => ENNReal.ofReal (vertexSurvivalFactor x (r + k + 1) *
            attachmentPatternFactor x F ε (r + k + 1))) s ∂treeLaw x (r + k) := by
        apply lintegral_congr_ae
        filter_upwards [treeLaw_phaseData x (r + k) (by simp [hτ]),
          treeLaw_active_nonempty x (r + k) (by simp [hτ])] with s hs hne
        rw [← ofReal_measureReal, transitionLaw_attachmentPattern hs hne
          (Nat.le_add_right _ _) (fun i hi => (hF i hi).2) ε]
        by_cases hm : r ∈ s.active ∧ attachmentPattern r F ε (r + k) s <;> simp [hm]
      _ = _ := by
        rw [lintegral_indicator_const (by trivial), ih]
        have hp := Finset.prod_Ioc_consecutive
          (fun i => ENNReal.ofReal (vertexSurvivalFactor x i *
            attachmentPatternFactor x F ε i)) (Nat.le_add_right r k)
          (Nat.le_succ (r + k))
        simp only [Nat.Ioc_succ_singleton, Finset.prod_singleton] at hp
        rw [← hp]
        ring

theorem treeLaw_attachmentPattern_survival_factor (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r k : ℕ) {F : Finset ℕ}
    (hF : ∀ i ∈ F, r < i ∧ x i = true) (ε : ℕ → Bool)
    (hmax : ∀ i ∈ F, i ≤ r + k) :
    (treeLaw x (r + k)) {s | r ∈ s.active ∧ attachmentPattern r F ε (r + k) s} =
      (treeLaw x (r + k)) {s | r ∈ s.active} *
        ∏ i ∈ F, ENNReal.ofReal (attachmentPatternFactor x F ε i) := by
  rw [treeLaw_attachmentPattern_survival x hτ r k hF ε,
    treeLaw_vertex_survival_measure x r k (by simp [hτ]) le_rfl]
  have he : ∀ i ∈ Finset.Ioc r (r + k), ENNReal.ofReal
      (vertexSurvivalFactor x i * attachmentPatternFactor x F ε i) =
      ENNReal.ofReal (vertexSurvivalFactor x i) *
        ENNReal.ofReal (attachmentPatternFactor x F ε i) := by
    intro i hi
    exact ENNReal.ofReal_mul (vertexSurvivalFactor_nonneg (x := x) (i := i)
      (by rw [hτ]; exact ENat.natCast_lt_top _))
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, mul_assoc]
  congr 1
  congr 1
  symm
  apply Finset.prod_subset
    (show F ⊆ Finset.Ioc r (r + k) from fun i hi => Finset.mem_Ioc.mpr ⟨(hF i hi).1, hmax i hi⟩)
  intro i _ hi
  simp [attachmentPatternFactor, hi]

end Freezing1.Forward

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

theorem LegalOrHeld.parent_at_le {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) {i : ℕ} (hi : i ≤ n) : q.parent i = s.parent i := by
  have hnew : i ≠ n + 1 := by omega
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · rfl
  · rw [step, ite_eq_left hp]
    cases x (n + 1) <;> simp [attach, freeze, hnew]

theorem parent_eq_at_birth {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) {i n : ℕ} (hin : i ≤ n) :
    (H n).parent i = (H i).parent i := by
  induction n, hin using Nat.le_induction with
  | base => rfl
  | succ n hin ih => exact ((hl n).parent_at_le hin).trans ih

def attachmentPatternEvent (r : ℕ) (F : Finset ℕ) (ε : ℕ → Bool) : Set History :=
  {H | ∀ i ∈ F, (H i).parent i = r ↔ ε i = true}

theorem measurableSet_attachmentPatternEvent (r : ℕ) (F : Finset ℕ) (ε : ℕ → Bool) :
    MeasurableSet (attachmentPatternEvent r F ε) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro _
  exact ((measurable_from_top : Measurable (fun s : State => s.parent i = r)).comp
    (measurable_pi_apply i)).iff measurable_const

/-- All finite binary patterns of attachment to a never-frozen vertex have
their genuine Bernoulli product probability, jointly with that infinite
survival event. This remains meaningful when survival has probability zero. -/
theorem fullLaw_survival_attachmentPattern (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (r : ℕ) {F : Finset ℕ}
    (hF : ∀ i ∈ F, r < i ∧ x i = true) (ε : ℕ → Bool) :
    (fullLaw x) (survivesForever r r ∩ attachmentPatternEvent r F ε) =
      (fullLaw x) (survivesForever r r) *
        ∏ i ∈ F, ENNReal.ofReal (attachmentPatternFactor x F ε i) := by
  let A := attachmentPatternEvent r F ε
  let E : ℕ → Set History := fun n => {H | ∀ j ≤ n, r ∈ (H (r + j)).active} ∩ A
  have hm : ∀ n, MeasurableSet (E n) := by
    intro n
    apply MeasurableSet.inter _ (measurableSet_attachmentPatternEvent r F ε)
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro j
    exact measurable_const.imp
      ((measurable_from_top : Measurable (fun s : State => r ∈ s.active)).comp
        (measurable_pi_apply (r + j)))
  have hanti : Antitone E := by
    intro a b hab H hH
    exact ⟨fun j hj => hH.1 j (hj.trans hab), hH.2⟩
  have he : (⋂ n, E n) = survivesForever r r ∩ A := by
    ext H
    simp only [Set.mem_iInter, E, survivesForever, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨fun j => (h j).1 j le_rfl, (h 0).2⟩,
      fun h n => ⟨fun j _ => h.1 j, h.2⟩⟩
  have hlim := tendsto_measure_iInter_atTop (μ := fullLaw x)
    (fun n => (hm n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [he] at hlim
  have hfinite : ∀ᶠ k in atTop, (fullLaw x) (E k) =
      (treeLaw x (r + k)) {s | r ∈ s.active} *
        ∏ i ∈ F, ENNReal.ofReal (attachmentPatternFactor x F ε i) := by
    filter_upwards [eventually_ge_atTop (F.sup id)] with k hk
    have hmax : ∀ i ∈ F, i ≤ r + k := by
      intro i hi
      have hh : i ≤ F.sup id := Finset.le_sup (f := id) hi
      omega
    rw [← treeLaw_attachmentPattern_survival_factor x hτ r k hF ε hmax,
      ← map_eval x (r + k), Measure.map_apply (measurable_pi_apply _) (by trivial)]
    apply measure_congr
    filter_upwards [fullLaw_legalOrHeld x] with H hl
    apply propext
    change ((∀ j ≤ k, r ∈ (H (r + j)).active) ∧ ∀ i ∈ F,
        (H i).parent i = r ↔ ε i = true) ↔
      r ∈ (H (r + k)).active ∧ attachmentPattern r F ε (r + k) (H (r + k))
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨h k le_rfl, fun i hi _ => by
        simpa only [parent_eq_at_birth hl (hmax i hi)] using hp i hi⟩
    · rintro ⟨h, hp⟩
      refine ⟨fun j hj => active_old_antitone hl (by omega) (Nat.add_le_add_left hj r) h,
        fun i hi => ?_⟩
      simpa only [parent_eq_at_birth hl (hmax i hi)] using hp i hi (hmax i hi)
  have hc : (∏ i ∈ F, ENNReal.ofReal (attachmentPatternFactor x F ε i)) ≠ ⊤ := by
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have hlim' := ((ENNReal.continuous_mul_const hc).tendsto
    ((fullLaw x) (survivesForever r r))).comp (treeLaw_survival_limit x r le_rfl)
  exact tendsto_nhds_unique hlim (hlim'.congr' (hfinite.mono fun _ h => h.symm))

end Freezing1.ForwardInfiniteHistory
