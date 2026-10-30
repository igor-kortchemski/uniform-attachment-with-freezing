module

public import Freezing1.BernoulliProductLaw
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Independent finite driver words, ordered from the upper phase downwards. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open MeasureTheory ProbabilityTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

abbrev Word (k : ℕ) := Fin k → ℕ

def descendingParameter (p : ℕ → unitInterval) (a k : ℕ) (j : Fin k) : unitInterval :=
  p (a + k - 1 - j.val)

@[simp] theorem descendingParameter_zero (p : ℕ → unitInterval) (a k : ℕ) :
    descendingParameter p a (k + 1) 0 = p (a + k) := by
  simp [descendingParameter]

@[simp] theorem descendingParameter_succ (p : ℕ → unitInterval) (a k : ℕ) (j : Fin k) :
    descendingParameter p a (k + 1) j.succ = descendingParameter p a k j := by
  unfold descendingParameter
  simp only [Fin.val_succ]
  congr 1
  have := j.isLt
  omega

noncomputable def wordLaw (p : ℕ → unitInterval) (a k : ℕ) : Measure (Word k) :=
  bernoulliProductLaw (descendingParameter p a k)

instance wordLaw_probability (p : ℕ → unitInterval) (a k : ℕ) :
    IsProbabilityMeasure (wordLaw p a k) := by unfold wordLaw; infer_instance

theorem wordLaw_coordinate (p : ℕ → unitInterval) (a k : ℕ) (j : Fin k) :
    HasLaw (fun w : Word k => w j)
      (bernoulliMeasure (1 : ℕ) 0 (descendingParameter p a k j)) (wordLaw p a k) :=
  bernoulliProductLaw_coordinate _ _

theorem wordLaw_independent (p : ℕ → unitInterval) (a k : ℕ) :
    iIndepFun (fun j (w : Word k) => w j) (wordLaw p a k) :=
  bernoulliProductLaw_independent _

@[simp] theorem wordLaw_zero (p : ℕ → unitInterval) (a : ℕ) :
    wordLaw p a 0 = Measure.dirac Fin.elim0 := by
  exact Measure.pi_of_empty _ _

theorem wordLaw_succ (p : ℕ → unitInterval) (a k : ℕ) :
    wordLaw p a (k + 1) =
      (bernoulliMeasure (1 : ℕ) 0 (p (a + k))).bind
        (fun y => (wordLaw p a k).map (Fin.cons y)) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun j : Fin (k + 1) =>
      bernoulliMeasure (1 : ℕ) 0 (descendingParameter p a (k + 1) j)) 0).symm.map_eq
  have hi : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ) 0).symm =
      (fun z : ℕ × Word k => Fin.cons z.1 z.2) := by
    funext z
    exact Fin.insertNth_zero' z.1 z.2
  rw [hi] at h
  simp only [Fin.succAbove_zero, descendingParameter_succ, descendingParameter_zero] at h
  change ((bernoulliMeasure (1 : ℕ) 0 (p (a + k))).prod (wordLaw p a k)).map
      (fun z : ℕ × Word k => Fin.cons z.1 z.2) = wordLaw p a (k + 1) at h
  rw [← h, Measure.prod_eq_of_sfinite,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  congr 1
  funext y
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

noncomputable def pairWordLaw (p q : ℕ → unitInterval) (a k : ℕ) :
    Measure (Word k × Word k) := (wordLaw p a k).prod (wordLaw q a k)

instance pairWordLaw_probability (p q : ℕ → unitInterval) (a k : ℕ) :
    IsProbabilityMeasure (pairWordLaw p q a k) := by unfold pairWordLaw; infer_instance

theorem pairWordLaw_independent (p q : ℕ → unitInterval) (a k : ℕ) :
    IndepFun Prod.fst Prod.snd (pairWordLaw p q a k) := by
  exact indepFun_prod measurable_id measurable_id

@[simp] theorem pairWordLaw_zero (p q : ℕ → unitInterval) (a : ℕ) :
    pairWordLaw p q a 0 = Measure.dirac (Fin.elim0, Fin.elim0) := by
  simp only [pairWordLaw, wordLaw_zero, Measure.dirac_prod_dirac]

/-- Independent probability kernels may be sampled in either block order. -/
theorem bind_prod_bind_of_countable
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    [Countable α] [Countable β] [Countable γ] [Countable δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Measure γ) (L : β → Measure δ)
    [∀ x, IsProbabilityMeasure (K x)] [∀ y, IsProbabilityMeasure (L y)] :
    (μ.bind K).prod (ν.bind L) =
      (μ.prod ν).bind (fun z => (K z.1).prod (L z.2)) := by
  have : IsProbabilityMeasure (μ.bind K) :=
    isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  have : IsProbabilityMeasure (ν.bind L) :=
    isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  have hleft : (μ.bind K).prod (ν.bind L) =
      μ.bind (fun x => (K x).bind (fun u => ν.bind
        (fun y => (L y).map (Prod.mk u)))) := by
    rw [Measure.prod_eq_of_sfinite,
      Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    congr 1
    funext x
    congr 1
    funext u
    exact Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable
  have hright : (μ.prod ν).bind (fun z => (K z.1).prod (L z.2)) =
      μ.bind (fun x => ν.bind (fun y => (K x).bind
        (fun u => (L y).map (Prod.mk u)))) := by
    rw [Measure.prod_eq_of_sfinite,
      Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    congr 1
    funext x
    rw [Measure.bind_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
    congr 1
    funext y
    exact Measure.prod_eq_of_sfinite _ _
  rw [hleft, hright]
  congr 1
  funext x
  exact Measure.bind_comm (measurable_of_countable _)

theorem pairWordLaw_succ (p q : ℕ → unitInterval) (a k : ℕ) :
    pairWordLaw p q a (k + 1) =
      ((bernoulliMeasure (1 : ℕ) 0 (p (a + k))).prod
        (bernoulliMeasure (1 : ℕ) 0 (q (a + k)))).bind
          (fun h => (pairWordLaw p q a k).map
            (fun w => (Fin.cons h.1 w.1, Fin.cons h.2 w.2))) := by
  rw [pairWordLaw, wordLaw_succ p, wordLaw_succ q, bind_prod_bind_of_countable]
  congr 1
  funext h
  rw [Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)]
  rfl

end Freezing1.BernoulliPairCoupling
