module

public import Freezing1.ForwardAnnealedSigns
public import Freezing1.Extinction
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The source integer walk under the actual infinite iid sign product

The zero sign coordinate is ignored, exactly as in activeCount. Independent
real sign observables satisfy Mathlib's strong law; both the walk drift and
the freezing-step density are then derived for the actual product measure.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical Topology BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def iidSignLaw (p : unitInterval) : Measure SignSequence :=
  Measure.infinitePi (fun _ : ℕ => signLaw p)

instance iidSignLaw_probability (p : unitInterval) : IsProbabilityMeasure (iidSignLaw p) := by
  unfold iidSignLaw
  infer_instance

theorem iidSignLaw_coordinate (p : unitInterval) (i : ℕ) :
    HasLaw (fun x : SignSequence => x i) (signLaw p) (iidSignLaw p) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => signLaw p) i).hasLaw

theorem iidSignLaw_independent (p : unitInterval) :
    iIndepFun (fun i (x : SignSequence) => x i) (iidSignLaw p) :=
  iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)

/-- The positive-index prefix has exactly the existing finite iid sign law. -/
theorem iidSignLaw_prefix (p : unitInterval) (n : ℕ) :
    (iidSignLaw p).map (fun x : SignSequence => fun i : Fin n => x (i.val + 1)) =
      finiteSignLaw p n := by
  have hi : Function.Injective (fun i : Fin n => i.val + 1) := by
    intro i j he
    apply Fin.ext
    change i.val + 1 = j.val + 1 at he
    omega
  have hh := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => signLaw p) hi
  exact hh.trans (Measure.infinitePi_eq_pi _)

theorem prefix_wordSchedule_agrees (x : SignSequence) (n : ℕ) :
    SchedulesAgreeThrough (wordSchedule (fun i : Fin n => x (i.val + 1))) x n := by
  intro i hi hin
  simp only [wordSchedule, dite_eq_left (show 1 ≤ i ∧ i ≤ n from ⟨hi, hin⟩)]
  rw [Nat.sub_add_cancel hi]

theorem iidSignLaw_observable_strong_law (p : unitInterval) (f : Bool → ℝ) :
    ∀ᵐ x ∂iidSignLaw p, Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, f (x (i + 1))) / n) atTop
        (𝓝 ((p : ℝ) * f true + (1 - (p : ℝ)) * f false)) := by
  let Y : ℕ → SignSequence → ℝ := fun i x => f (x (i + 1))
  have hcoord := (iidSignLaw_independent p).precomp Nat.succ_injective
  have hind : iIndepFun Y (iidSignLaw p) :=
    hcoord.comp (fun _ => f) (fun _ => measurable_of_countable f)
  have hLaw : ∀ i, HasLaw (Y i) ((signLaw p).map f) (iidSignLaw p) := by
    intro i
    exact (hasLaw_map (measurable_of_countable f).aemeasurable).comp (iidSignLaw_coordinate p (i + 1))
  have hint : Integrable (Y 0) (iidSignLaw p) :=
    (iidSignLaw_coordinate p 1).integrable_comp (integrable_bernoulliMeasure true false p f)
  have hexpect : (∫ x, Y 0 x ∂iidSignLaw p) =
      (p : ℝ) * f true + (1 - (p : ℝ)) * f false := by
    change (∫ x, (f ∘ fun x : SignSequence => x 1) x ∂iidSignLaw p) = _
    rw [(iidSignLaw_coordinate p 1).integral_comp (measurable_of_countable f).aestronglyMeasurable]
    exact integral_bernoulliMeasure true false p f
  simpa only [Y, hexpect] using strong_law_ae_real Y hint (fun i j hij => hind.indepFun hij)
    (fun i => (hLaw i).identDistrib (hLaw 0))

theorem activeCount_cast_eq_observable (x : SignSequence) (n : ℕ) :
    (activeCount x n : ℝ) = 1 + ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1 := by
  simp only [activeCount, Int.cast_add, Int.cast_one, Int.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  cases x (i + 1) <;> simp

/-- The source's unstopped integer walk has the actual strong-law drift. -/
theorem iid_activeCount_drift (p : unitInterval) :
    ∀ᵐ x ∂iidSignLaw p,
      Tendsto (fun n : ℕ => (activeCount x n : ℝ) / n) atTop (𝓝 (2 * (p : ℝ) - 1)) := by
  have hh := iidSignLaw_observable_strong_law p (fun b => if b then (1 : ℝ) else -1)
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hh] with x hx
  have hs := hinv.add hx
  convert hs using 1
  · funext n
    rw [activeCount_cast_eq_observable, add_div]
  · simp
    ring

/-- Freezing signs have their actual limiting frequency, including the
boundary parameters p=0 and p=1. -/
theorem iid_freezing_density (p : unitInterval) :
    ∀ᵐ x ∂iidSignLaw p,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
        if x (i + 1) then (0 : ℝ) else 1) / (n : ℝ)) atTop (𝓝 (1 - (p : ℝ))) := by
  simpa using iidSignLaw_observable_strong_law p (fun b => if b then (0 : ℝ) else 1)

/-- A strictly negative limiting drift forces a genuine zero crossing,
using the source nearest-neighbour walk rather than a stopped surrogate. -/
theorem zero_exists_of_negative_drift {x : SignSequence} {c : ℝ} (hc : c < 0)
    (h : Tendsto (fun n : ℕ => (activeCount x n : ℝ) / n) atTop (𝓝 c)) :
    ∃ k, activeCount x k = 0 := by
  by_contra hnone
  have hp : ∀ n, 0 < activeCount x n := by
    intro n
    exact (positiveThrough_iff_no_zero x n).mpr (fun k _ hk => hnone ⟨k, hk⟩) n le_rfl
  obtain ⟨n, hn, hnpos⟩ := ((h.eventually (eventually_lt_nhds hc)).and
    (eventually_gt_atTop (0 : ℕ))).exists
  have hratio : 0 < (activeCount x n : ℝ) / n := by
    exact div_pos (by exact_mod_cast hp n) (by exact_mod_cast hnpos)
  linarith

/-- The strictly subcritical source extinction assertion, directly under
its actual infinite iid sign law. The critical case is handled separately. -/
theorem iid_extinction_of_lt_half (p : unitInterval) (hp : (p : ℝ) < 1 / 2) :
    ∀ᵐ x ∂iidSignLaw p, ∃ k, activeCount x k = 0 := by
  filter_upwards [iid_activeCount_drift p] with x hx
  exact zero_exists_of_negative_drift (by linarith) hx

end Freezing1.ForwardAnnealed
