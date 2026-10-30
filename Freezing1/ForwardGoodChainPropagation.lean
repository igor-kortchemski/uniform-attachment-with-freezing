module

public import Freezing1.ForwardGoodChains
public import Freezing1.ForwardComponentContinuation

/-!
# Good-block predicates propagate along the actual forward continuation

Every new child inherits all completed block tests from its parent. The
ancestor at the current cut belongs to the original active set. These facts
are proved along the actual kernels and give the precise marked-population
identity used in the block-chain argument.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

/-- A state predicate preserved by every legal forward choice also holds
along the genuine continuation, including held absorbed states. -/
theorem continuationLaw_ae_invariant (x : SignSequence) (a : ℕ) (P : State → Prop)
    (hstep : ∀ b, a ≤ b → ∀ s, ValidAt b s → P s →
      ∀ v ∈ s.active, P (step s (b + 1) (x (b + 1)) v))
    {b k : ℕ} {s : State} (hab : a ≤ b) (hs : ValidAt b s) (hP : P s) :
    ∀ᵐ t ∂continuationLaw x b k s, P t := by
  induction k generalizing b s with
  | zero => simpa [continuationLaw] using hP
  | succ k ih =>
    have hnext : ∀ᵐ t ∂transitionLaw s (b + 1) (x (b + 1)), ValidAt (b + 1) t ∧ P t := by
      apply transitionLaw_ae
      · intro _; exact ⟨hs.mono (Nat.le_succ b), hP⟩
      · intro v hv; exact ⟨hs.step _ _, hstep b hab s hs hP v hv⟩
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _t, (1 : ℝ≥0∞) ∂transitionLaw s (b + 1) (x (b + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [hnext] with t ht
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (ih (hab.trans (Nat.le_succ b)) ht.1 ht.2)
      _ = 1 := by simp

theorem continuationLaw_valid (x : SignSequence) {b k : ℕ} {s : State}
    (hs : ValidAt b s) : ∀ᵐ t ∂continuationLaw x b k s, ValidAt (b + k) t := by
  induction k generalizing b s with
  | zero => simpa [continuationLaw] using hs
  | succ k ih =>
    have hnext : ∀ᵐ t ∂transitionLaw s (b + 1) (x (b + 1)), ValidAt (b + 1) t := by
      apply transitionLaw_ae
      · intro _; exact hs.mono (Nat.le_succ b)
      · intro v _; exact hs.step _ _
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _t, (1 : ℝ≥0∞) ∂transitionLaw s (b + 1) (x (b + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [hnext] with t ht
        have hh := ih ht
        rw [show b + 1 + k = b + (k + 1) by omega] at hh
        exact (ae_iff_prob_eq_one measurable_from_top).mp hh
      _ = 1 := by simp

def InheritsBlocks (s q : State) (C k₀ k : ℕ) : Prop :=
  ∀ v ∈ q.active, cutAncestor q (C ^ k) v ∈ s.active ∧
    ∀ ell ∈ Finset.Ico k₀ k,
      blockHeight q (C ^ ell) (C ^ (ell + 1)) v =
        blockHeight s (C ^ ell) (C ^ (ell + 1)) (cutAncestor q (C ^ k) v)

theorem InheritsBlocks.initial {s : State} {C k₀ k : ℕ}
    (hs : ValidAt (C ^ k) s) : InheritsBlocks s s C k₀ k := by
  intro v hv
  rw [cutAncestor_of_le s (C ^ k) v (hs.vertices_le v (hs.active_subset hv))]
  exact ⟨hv, fun _ _ => rfl⟩

theorem InheritsBlocks.step {s q : State} {C k₀ k n : ℕ}
    (h : InheritsBlocks s q C k₀ k) (hq : ValidAt n q)
    (hC : 1 ≤ C) (ha : C ^ k ≤ n) {p : ℕ} (hp : p ∈ q.active) (sign : Bool) :
    InheritsBlocks s (step q (n + 1) sign p) C k₀ k := by
  rw [Forward.step, ite_eq_left hp]
  cases sign
  · change InheritsBlocks s (freeze q (n + 1) p) C k₀ k
    intro v hv
    have hvq : v ∈ q.active := Finset.mem_of_mem_erase hv
    simpa only [cutAncestor_freeze, blockHeight_freeze] using h v hvq
  · change InheritsBlocks s (attach q (n + 1) p) C k₀ k
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [cutAncestor_attach_new hq ha hp]
      refine ⟨(h p hp).1, ?_⟩
      intro ell he
      have heK : ell + 1 ≤ k := by have := Finset.mem_Ico.mp he; omega
      have hb : C ^ (ell + 1) ≤ n := (pow_le_pow_right₀ hC heK).trans ha
      have ha' : C ^ ell ≤ n := (pow_le_pow_right₀ hC (Nat.le_succ ell)).trans hb
      rw [blockHeight_attach_new hq ha' hb hp]
      exact (h p hp).2 ell he
    · have hvV := hq.active_subset hv
      rw [cutAncestor_attach_old hq (C ^ k) p hvV]
      refine ⟨(h v hv).1, ?_⟩
      intro ell he
      rw [blockHeight_attach_old hq _ _ p hvV]
      exact (h v hv).2 ell he

theorem continuationLaw_inheritsBlocks (x : SignSequence) {s : State} {C k₀ k j : ℕ}
    (hs : ValidAt (C ^ k) s) (hC : 1 ≤ C) :
    ∀ᵐ q ∂continuationLaw x (C ^ k) j s, InheritsBlocks s q C k₀ k := by
  apply continuationLaw_ae_invariant x (C ^ k) (fun q => InheritsBlocks s q C k₀ k)
    (fun n hn q hq h v hv => h.step hq hC hn hv _) le_rfl hs
  exact InheritsBlocks.initial hs

/-- At the next endpoint, the complete good predicate is precisely the old
mark carried by the cut ancestor together with the new block-height test. -/
theorem InheritsBlocks.goodSet_succ_iff {s q : State} {C k₀ k : ℕ}
    (h : InheritsBlocks s q C k₀ k) (hq : ValidAt (C ^ (k + 1)) q)
    (hk : k₀ ≤ k) (t : ℝ) {v : ℕ} (hv : v ∈ q.active) :
    v ∈ goodSet q C k₀ (k + 1) t ↔
      cutAncestor q (C ^ k) v ∈ goodSet s C k₀ k t ∧ t < (cutHeight q (C ^ k) v : ℝ) := by
  rw [Forward.goodSet_succ_iff hk hq]
  constructor
  · rintro ⟨hgood, hnew⟩
    refine ⟨Finset.mem_filter.mpr ⟨(h v hv).1, ?_⟩, hnew⟩
    intro ell he
    rw [← (h v hv).2 ell he]
    exact (Finset.mem_filter.mp hgood).2 ell he
  · rintro ⟨hgood, hnew⟩
    refine ⟨Finset.mem_filter.mpr ⟨hv, ?_⟩, hnew⟩
    intro ell he
    rw [(h v hv).2 ell he]
    exact (Finset.mem_filter.mp hgood).2 ell he

theorem InheritsBlocks.goodSet_succ_eq_filter {s q : State} {C k₀ k : ℕ}
    (h : InheritsBlocks s q C k₀ k) (hq : ValidAt (C ^ (k + 1)) q)
    (hk : k₀ ≤ k) (t : ℝ) :
    goodSet q C k₀ (k + 1) t = q.active.filter fun v =>
      cutAncestor q (C ^ k) v ∈ goodSet s C k₀ k t ∧ t < (cutHeight q (C ^ k) v : ℝ) := by
  ext v
  by_cases hv : v ∈ q.active
  · simpa only [Finset.mem_filter, hv, true_and] using h.goodSet_succ_iff hq hk t hv
  · have hn : v ∉ goodSet q C k₀ (k + 1) t := fun hm => hv (goodSet_subset _ _ _ _ _ hm)
    simp only [hn, Finset.mem_filter, hv, false_and]

/-- The marked-population identity holds under the actual conditional
continuation from any valid tree at the left endpoint. -/
theorem continuationLaw_goodSet_succ (x : SignSequence) {s : State} {C k₀ k : ℕ}
    (hs : ValidAt (C ^ k) s) (hC : 1 ≤ C) (hk : k₀ ≤ k) (t : ℝ) :
    ∀ᵐ q ∂continuationLaw x (C ^ k) (C ^ (k + 1) - C ^ k) s,
      goodSet q C k₀ (k + 1) t = q.active.filter fun v =>
        cutAncestor q (C ^ k) v ∈ goodSet s C k₀ k t ∧ t < (cutHeight q (C ^ k) v : ℝ) := by
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have he : C ^ k + (C ^ (k + 1) - C ^ k) = C ^ (k + 1) := Nat.add_sub_of_le hab
  have hvalid := continuationLaw_valid (k := C ^ (k + 1) - C ^ k) x hs
  rw [he] at hvalid
  filter_upwards [continuationLaw_inheritsBlocks (k₀ := k₀) x hs hC, hvalid] with q hq hv
  exact hq.goodSet_succ_eq_filter hv hk t

end Freezing1.Forward
