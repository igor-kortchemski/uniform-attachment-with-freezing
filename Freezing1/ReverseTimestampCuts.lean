module

public import Freezing1.ReverseStampedHistory

/-!
# Recovering each reverse phase by cutting the terminal timestamps

An edge born at time `t` is present at reverse phase `i` exactly when `i<t`.
Cutting the other parent edges makes their child endpoints roots. The proof
follows the actual legal transitions, including singleton freezing insertions,
and identifies entire parent and timestamp functions, with unused defaults.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open scoped Classical

def parentCut (F : Forest) (i : ℕ) (v : ℕ ⊕ ℕ) : ℕ ⊕ ℕ :=
  if i < F.edgeTime v then F.forest.parent v else v

def timeCut (F : Forest) (i : ℕ) (v : ℕ ⊕ ℕ) : ℕ :=
  if i < F.edgeTime v then F.edgeTime v else 0

theorem parent_of_time_zero {x : SignSequence} {n i : ℕ} {F : Forest}
    (ht : TimesValidAt x n i F) (hd : CanonicalDefaults F) {v : ℕ ⊕ ℕ}
    (hz : F.edgeTime v = 0) : F.forest.parent v = v := by
  by_cases hv : v ∈ F.forest.vertices
  · exact F.forest.parent_of_root ((ht.root_zero v hv).mp hz)
  · exact (hd.outside v hv).1

theorem parentCut_at_phase {x : SignSequence} {n i : ℕ} {F : Forest}
    (ht : TimesValidAt x n i F) (hd : CanonicalDefaults F) : parentCut F i = F.forest.parent := by
  funext v
  by_cases hz : F.edgeTime v = 0
  · simp [parentCut, hz, parent_of_time_zero ht hd hz]
  · have hv : v ∈ F.forest.vertices := by
      by_contra hv
      exact hz (hd.outside v hv).2.2.2
    simp [parentCut, (ht.range v hv hz).1]

theorem timeCut_at_phase {x : SignSequence} {n i : ℕ} {F : Forest}
    (ht : TimesValidAt x n i F) (hd : CanonicalDefaults F) : timeCut F i = F.edgeTime := by
  funext v
  by_cases hz : F.edgeTime v = 0
  · simp [timeCut, hz]
  · have hv : v ∈ F.forest.vertices := by
      by_contra hv
      exact hz (hd.outside v hv).2.2.2
    simp [timeCut, (ht.range v hv hz).1]

theorem cut_joinChoice {x : SignSequence} {n t : ℕ} {F : Forest}
    (ht : TimesValidAt x n t F) (hd : CanonicalDefaults F)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag) :
    parentCut (joinChoice F t p) t = F.forest.parent ∧
      timeCut (joinChoice F t p) t = F.edgeTime := by
  have hp' := Finset.mem_offDiag.mp hp
  have hpb := F.forest.parent_of_root hp'.2.1
  have htb := (ht.root_zero p.2 (RootedForest.mem_roots.mp hp'.2.1).1).mpr hp'.2.1
  constructor
  · funext v
    by_cases hv : v = p.2
    · subst v
      simp [parentCut, joinChoice, hp, hpb]
    · have he := congrFun (parentCut_at_phase ht hd) v
      simpa [parentCut, joinChoice, hp, RootedForest.join, hv] using he
  · funext v
    by_cases hv : v = p.2
    · subst v
      simp [timeCut, joinChoice, hp, htb]
    · have he := congrFun (timeCut_at_phase ht hd) v
      simpa [timeCut, joinChoice, hp, hv] using he

theorem insertLabel_parent_time_eq {F : Forest} (hd : CanonicalDefaults F) (i : ℕ) :
    (insertLabel F i).forest.parent = F.forest.parent ∧
      (insertLabel F i).edgeTime = F.edgeTime := by
  by_cases hi : Sum.inr i ∈ F.forest.vertices
  · simp [insertLabel, hi]
  · have hd' := hd.outside (.inr i) hi
    constructor
    · funext v
      by_cases hv : v = Sum.inr i <;> simp [insertLabel, hi, RootedForest.adjoin, hv, hd'.1]
    · funext v
      by_cases hv : v = Sum.inr i <;> simp [insertLabel, hi, hv, hd'.2.2.2]

theorem LegalStep.previous_cut {x : SignSequence} {n i : ℕ} {F G : Forest}
    (hs : LegalStep x i F G) (ht : TimesValidAt x n (i + 1) F) (hd : CanonicalDefaults F) :
    parentCut G (i + 1) = F.forest.parent ∧ timeCut G (i + 1) = F.edgeTime := by
  cases hx : x (i + 1)
  · simp only [LegalStep, hx, Bool.false_eq_true, ↓reduceIte] at hs
    rw [hs]
    have he := insertLabel_parent_time_eq hd i
    have hp : parentCut (insertLabel F i) (i + 1) = parentCut F (i + 1) := by
      funext v; simp only [parentCut, he.1, he.2]
    have ht' : timeCut (insertLabel F i) (i + 1) = timeCut F (i + 1) := by
      funext v; simp only [timeCut, he.2]
    exact ⟨hp.trans (parentCut_at_phase ht hd), ht'.trans (timeCut_at_phase ht hd)⟩
  · simp only [LegalStep, hx, ↓reduceIte] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact cut_joinChoice ht hd hp

theorem cut_succ_of_cut_eq {F G : Forest} {i : ℕ}
    (hp : G.forest.parent = parentCut F i) (ht : G.edgeTime = timeCut F i) :
    parentCut G (i + 1) = parentCut F (i + 1) ∧
      timeCut G (i + 1) = timeCut F (i + 1) := by
  constructor <;> funext v
  · by_cases hi : i < F.edgeTime v
    · by_cases hj : i + 1 < F.edgeTime v <;> simp [parentCut, hp, ht, timeCut, hi, hj]
    · have hj : ¬i + 1 < F.edgeTime v := by omega
      simp [parentCut, ht, timeCut, hi, hj]
  · by_cases hi : i < F.edgeTime v
    · by_cases hj : i + 1 < F.edgeTime v <;> simp [timeCut, ht, hi, hj]
    · have hj : ¬i + 1 < F.edgeTime v := by omega
      simp [timeCut, ht, hi, hj]

end Freezing1.ReverseStamped

namespace Freezing1.ReverseStampedHistory

open MeasureTheory ReverseStamped
open scoped ENNReal

/-- The recorded phase parent edges are exactly the terminal edges later
than that phase. This is a deterministic trajectory reconstruction theorem. -/
theorem stage_eq_terminal_cuts {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i)) :
    ∀ i ≤ n, (stage H i).forest.parent = parentCut H.current i ∧
      (stage H i).edgeTime = timeCut H.current i := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 := hd 0 (Nat.zero_le _)
    exact ⟨(parentCut_at_phase h0.times h0.defaults).symm,
      (timeCut_at_phase h0.times h0.defaults).symm⟩
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hnxt := hd (i + 1) hi
    have hcut := (hs i (by omega)).previous_cut hnxt.times hnxt.defaults
    have hcomp := cut_succ_of_cut_eq hprev.1 hprev.2
    exact ⟨hcut.1.symm.trans hcomp.1, hcut.2.symm.trans hcomp.2⟩

theorem fullLaw_stage_eq_terminal_cuts (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ H ∂fullLaw x n, ∀ i ≤ n,
      (stage H i).forest.parent = parentCut H.current i ∧
      (stage H i).edgeTime = timeCut H.current i := by
  filter_upwards [fullLaw_phaseData x n hn, fullLaw_legalSteps x n hn] with H hd hs
  exact stage_eq_terminal_cuts hd hs

/-- The actual phase graph retains precisely the terminal parent edges whose
timestamps exceed the cut, on the prescribed surviving label set. -/
theorem stage_graph_cut_iff {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {i : ℕ} (hi : i ≤ n) (u v : ℕ ⊕ ℕ) :
    (stage H i).forest.graph.Adj u v ↔
      u ∈ Reverse.phaseLabels x n i ∧ v ∈ Reverse.phaseLabels x n i ∧ u ≠ v ∧
        ((H.current.forest.parent u = v ∧ i < H.current.edgeTime u) ∨
          (H.current.forest.parent v = u ∧ i < H.current.edgeTime v)) := by
  have hp := (stage_eq_terminal_cuts hd hs i hi).1
  change u ∈ (stage H i).forest.vertices ∧ v ∈ (stage H i).forest.vertices ∧ u ≠ v ∧
    ((stage H i).forest.parent u = v ∨ (stage H i).forest.parent v = u) ↔ _
  rw [(hd i hi).valid.vertices_eq, hp]
  by_cases hu : i < H.current.edgeTime u <;> by_cases hv : i < H.current.edgeTime v <;>
    simp only [parentCut, hu, hv, ite_true, ite_false] <;> tauto

/-- Roots at phase `i` are exactly surviving vertices already born by time
`i`, expressed in the terminal incoming-edge coordinates. -/
theorem stage_roots_cut_iff {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {i : ℕ} (hi : i ≤ n) (v : ℕ ⊕ ℕ) :
    v ∈ (stage H i).forest.roots ↔
      v ∈ Reverse.phaseLabels x n i ∧ H.current.edgeTime v ≤ i := by
  have hp := (stage_eq_terminal_cuts hd hs i hi).1
  have hzero := hd 0 (Nat.zero_le _)
  have hsub : Reverse.phaseLabels x n i ⊆ Reverse.phaseLabels x n 0 := by
    intro w hw
    cases w <;> simp_all [Reverse.phaseLabels]
  constructor
  · intro hv
    have hvI : v ∈ Reverse.phaseLabels x n i :=
      (hd i hi).valid.vertices_eq ▸ (RootedForest.mem_roots.mp hv).1
    refine ⟨hvI, ?_⟩
    by_contra hle
    have hlt : i < H.current.edgeTime v := Nat.lt_of_not_ge hle
    have hv0 : v ∈ H.current.forest.vertices := hzero.valid.vertices_eq.symm ▸ hsub hvI
    have hneq : v ≠ H.current.forest.root v := by
      intro he
      have hz := (hzero.times.root_zero v hv0).mpr (RootedForest.mem_roots.mpr ⟨hv0, he.symm⟩)
      change H.current.edgeTime v = 0 at hz
      omega
    have hparent := (stage H i).forest.parent_of_root hv
    rw [hp] at hparent
    have hparent0 : H.current.forest.parent v = v := by simpa only [parentCut, ite_eq_left hlt] using hparent
    exact H.current.forest.parent_ne hv0 hneq hparent0
  · rintro ⟨hv, hle⟩
    have hvI : v ∈ (stage H i).forest.vertices := (hd i hi).valid.vertices_eq.symm ▸ hv
    refine RootedForest.mem_roots.mpr ⟨hvI, ?_⟩
    by_contra hroot
    apply (stage H i).forest.parent_ne hvI (Ne.symm hroot)
    rw [hp]
    simp only [parentCut, ite_eq_right (Nat.not_lt.mpr hle)]

end Freezing1.ReverseStampedHistory
