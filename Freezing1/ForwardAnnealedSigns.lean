module

public import Freezing1.ForwardAnnealed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

/-!
# Averaging the genuine construction over independent random signs

The sign word has the actual finite Bernoulli product law. Its coordinates
are independent, and integrating the existing fixed-schedule tree law gives
exactly the process which samples a fresh sign at each transition. The
identification retains absorption and the degenerate parameters.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def finiteSignLaw (p : unitInterval) (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ => signLaw p

instance finiteSignLaw_probability (p : unitInterval) (n : ℕ) :
    IsProbabilityMeasure (finiteSignLaw p n) := by unfold finiteSignLaw; infer_instance

theorem finiteSignLaw_coordinate (p : unitInterval) (n : ℕ) (i : Fin n) :
    HasLaw (fun w : Fin n → Bool => w i) (signLaw p) (finiteSignLaw p n) :=
  (measurePreserving_eval (fun _ : Fin n => signLaw p) i).hasLaw

theorem finiteSignLaw_independent (p : unitInterval) (n : ℕ) :
    iIndepFun (fun i (w : Fin n → Bool) => w i) (finiteSignLaw p n) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- A finite word specifies signs numbered one through n. Its arbitrary
continuation is irrelevant at every horizon at most n. -/
def wordSchedule {n : ℕ} (w : Fin n → Bool) : SignSequence :=
  fun i => if hi : 1 ≤ i ∧ i ≤ n then w ⟨i - 1, by omega⟩ else false

theorem wordSchedule_snoc_prefix {n : ℕ} (w : Fin n → Bool) (sign : Bool) :
    SchedulesAgreeThrough (wordSchedule (Fin.snoc w sign)) (wordSchedule w) n := by
  intro i hi hin
  have h1 : 1 ≤ i ∧ i ≤ n + 1 := ⟨hi, by omega⟩
  have h2 : 1 ≤ i ∧ i ≤ n := ⟨hi, hin⟩
  simp only [wordSchedule, dite_eq_left h1, dite_eq_left h2]
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => Bool) sign w (⟨i - 1, by omega⟩ : Fin n)

theorem wordSchedule_snoc_last {n : ℕ} (w : Fin n → Bool) (sign : Bool) :
    wordSchedule (Fin.snoc w sign) (n + 1) = sign := by
  have h : 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 := ⟨by omega, le_rfl⟩
  simp only [wordSchedule, dite_eq_left h, Nat.add_sub_cancel]
  exact Fin.snoc_last (α := fun _ : Fin (n + 1) => Bool) sign w

/-- The last sign is independent of the preceding finite word. -/
theorem finiteSignLaw_succ (p : unitInterval) (n : ℕ) :
    finiteSignLaw p (n + 1) = (signLaw p).bind
      (fun sign => (finiteSignLaw p n).map (fun w => Fin.snoc w sign)) := by
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => signLaw p) (Fin.last n)).symm.map_eq
  change ((signLaw p).prod (finiteSignLaw p n)).map
      (fun q : Bool × (Fin n → Bool) => Fin.insertNth (Fin.last n) q.1 q.2) =
      finiteSignLaw p (n + 1) at hm
  simp only [Fin.insertNth_last'] at hm
  rw [← hm, Measure.prod_eq_of_sfinite,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  congr 1
  funext sign
  rw [Measure.map_map (measurable_of_countable _) measurable_prodMk_left]
  rfl

/-- The true averaged tree law equals the integral of the original
fixed-schedule laws over an independent Bernoulli sign word. -/
theorem treeLaw_eq_iid_sign_mixture (p : unitInterval) (n : ℕ) :
    treeLaw p n = (finiteSignLaw p n).bind (fun w => Forward.treeLaw (wordSchedule w) n) := by
  induction n with
  | zero =>
      rw [finiteSignLaw, Measure.pi_of_empty _ (fun i => Fin.elim0 i),
        Measure.dirac_bind (measurable_of_countable _)]
      rfl
  | succ n ih =>
      rw [treeLaw_succ, ih, finiteSignLaw_succ,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext sign
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
          measurable_from_top.aemeasurable,
        Measure.bind_map (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext w
      rw [Forward.treeLaw, wordSchedule_snoc_last,
        Forward.treeLaw_eq_of_schedule_prefix (wordSchedule_snoc_prefix w sign)]

end Freezing1.ForwardAnnealed
