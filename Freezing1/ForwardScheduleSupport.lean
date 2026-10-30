module

public import Freezing1.ForwardLabels

/-!
# Schedule-compatible labels in the forward construction

The nonroot vertex identifiers are exactly the attachment times, hence also
the labels of their incoming edges. Frozen labels are exactly freezing times.
This is the support restriction missing from the printed Lemma `lem:loiTn`.
It is a necessary support theorem, not the unproved terminal point-mass formula.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal

structure ScheduleSupport (x : SignSequence) (n : ℕ) (s : State) : Prop where
  vertex_iff : ∀ v, v ∈ s.vertices ↔ v = 0 ∨ (1 ≤ v ∧ v ≤ n ∧ x v = true)
  frozen_label : ∀ v ∈ s.vertices, ∀ t, s.frozenAt v = some t →
    1 ≤ t ∧ t ≤ n ∧ x t = false
  frozen_exists : ∀ t, 1 ≤ t → t ≤ n → x t = false →
    ∃ v ∈ s.vertices, s.frozenAt v = some t

theorem initial_schedule_support (x : SignSequence) : ScheduleSupport x 0 initial := by
  constructor
  · intro v
    simp only [initial, Finset.mem_singleton]
    omega
  · intro v hv t ht
    simp [initial] at ht
  · intro t ht ht0 _
    omega

theorem ScheduleSupport.attach {x : SignSequence} {n : ℕ} {s : State}
    (h : ScheduleSupport x n s) (hs : ValidAt n s)
    (hx : x (n + 1) = true) (v : ℕ) :
    ScheduleSupport x (n + 1) (attach s (n + 1) v) := by
  have hfresh : n + 1 ∉ s.vertices := by
    intro hv
    have := hs.vertices_le _ hv
    omega
  constructor
  · intro u
    change u ∈ insert (n + 1) s.vertices ↔ _
    rw [Finset.mem_insert, h.vertex_iff]
    constructor
    · rintro (rfl | rfl | ⟨hu, hun, hxu⟩)
      · exact Or.inr ⟨by omega, le_rfl, hx⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hu, by omega, hxu⟩
    · rintro (rfl | ⟨hu, hun, hxu⟩)
      · exact Or.inr (Or.inl rfl)
      · by_cases hue : u = n + 1
        · exact Or.inl hue
        · exact Or.inr (Or.inr ⟨hu, by omega, hxu⟩)
  · intro u hu t ht
    by_cases hue : u = n + 1
    · simp [Forward.attach, hue] at ht
    · have huo := (Finset.mem_insert.mp hu).resolve_left hue
      have hto : s.frozenAt u = some t := by simpa [Forward.attach, hue] using ht
      obtain ⟨ht1, htn, hxt⟩ := h.frozen_label u huo t hto
      exact ⟨ht1, by omega, hxt⟩
  · intro t ht1 htn hxt
    have htne : t ≠ n + 1 := by
      intro ht
      rw [ht, hx] at hxt
      contradiction
    obtain ⟨u, hu, hut⟩ := h.frozen_exists t ht1 (by omega) hxt
    have hue : u ≠ n + 1 := by intro he; exact hfresh (he ▸ hu)
    exact ⟨u, Finset.mem_insert_of_mem hu, by simpa [Forward.attach, hue] using hut⟩

theorem ScheduleSupport.freeze {x : SignSequence} {n : ℕ} {s : State}
    (h : ScheduleSupport x n s) (hs : ValidAt n s)
    (hx : x (n + 1) = false) {v : ℕ} (hv : v ∈ s.active) :
    ScheduleSupport x (n + 1) (freeze s (n + 1) v) := by
  constructor
  · intro u
    change u ∈ s.vertices ↔ _
    rw [h.vertex_iff]
    constructor
    · rintro (rfl | ⟨hu, hun, hxu⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hu, by omega, hxu⟩
    · rintro (rfl | ⟨hu, hun, hxu⟩)
      · exact Or.inl rfl
      · have hune : u ≠ n + 1 := by
          intro he
          rw [he, hx] at hxu
          contradiction
        exact Or.inr ⟨hu, by omega, hxu⟩
  · intro u hu t ht
    by_cases huv : u = v
    · simp only [Forward.freeze, huv, Function.update_self, Option.some.injEq] at ht
      subst t
      exact ⟨by omega, le_rfl, hx⟩
    · have hto : s.frozenAt u = some t := by simpa [Forward.freeze, huv] using ht
      obtain ⟨ht1, htn, hxt⟩ := h.frozen_label u hu t hto
      exact ⟨ht1, by omega, hxt⟩
  · intro t ht1 htn hxt
    by_cases hte : t = n + 1
    · subst t
      exact ⟨v, hs.active_subset hv, by simp [Forward.freeze]⟩
    · obtain ⟨u, hu, hut⟩ := h.frozen_exists t ht1 (by omega) hxt
      have huv : u ≠ v := by
        intro hue
        have hvnone := (hs.active_iff v (hs.active_subset hv)).mp hv
        rw [hue, hvnone] at hut
        contradiction
      exact ⟨u, hu, by simpa [Forward.freeze, huv] using hut⟩

theorem ScheduleSupport.step {x : SignSequence} {n : ℕ} {s : State}
    (h : ScheduleSupport x n s) (hs : ValidAt n s) {v : ℕ} (hv : v ∈ s.active) :
    ScheduleSupport x (n + 1) (step s (n + 1) (x (n + 1)) v) := by
  rw [Forward.step, ite_eq_left hv]
  cases hx : x (n + 1)
  · exact h.freeze hs hx hv
  · exact h.attach hs hx v

/-- Corrected fixed-schedule support of the actual random forward tree.
The endpoint `n=τ` is included, just as in the source's finite law statement. -/
theorem treeLaw_schedule_support (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, ScheduleSupport x n s := by
  induction n with
  | zero => simp [treeLaw, initial_schedule_support]
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hτ
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂treeLaw x n := by
        apply lintegral_congr_ae
        filter_upwards [ih hnτ.le, treeLaw_valid x n, treeLaw_active_nonempty x n hnτ]
          with s hs hv hne
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (transitionLaw_ae s (n + 1) (x (n + 1)) (ScheduleSupport x (n + 1))
            (fun he => False.elim (hne.ne_empty he)) (fun v hvs => hs.step hv hvs))
      _ = 1 := by simp

theorem ScheduleSupport.frozen_iff {x : SignSequence} {n : ℕ} {s : State}
    (h : ScheduleSupport x n s) (t : ℕ) :
    (∃ v ∈ s.vertices, s.frozenAt v = some t) ↔ 1 ≤ t ∧ t ≤ n ∧ x t = false := by
  constructor
  · rintro ⟨v, hv, ht⟩
    exact h.frozen_label v hv t ht
  · rintro ⟨ht1, htn, hxt⟩
    exact h.frozen_exists t ht1 htn hxt

end Freezing1.Forward
