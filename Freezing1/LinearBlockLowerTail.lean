module

public import Freezing1.PoissonApproximation
public import Freezing1.PoissonLowerTail
public import Freezing1.BlockAttachmentParameters
public import Freezing1.LinearRegimeUniform

/-!
# Quantitative Poisson approximation on the paper's geometric blocks

The parameters and mean are exactly those of `(a,b]`. The uniform estimate
uses Lemma 8 with ratio `(C+1)/2`, strictly smaller than the block ratio `C`,
and bounds the upper endpoint `a*C` by the chosen macroscopic cutoff.
The actual-history block law and the weighted random-root count are distinct
bridges; an auxiliary Bernoulli law alone is not claimed to prove Lemma 12.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal Classical

/-- Finite, fully quantified approximation for the exact paper block parameters. -/
theorem block_bernoulli_poisson_event_error (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n)
    (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c)
    (herr : ∀ j ∈ Finset.Icc a b, |(activeCount x j : ℝ) / j - c| ≤ c / 2)
    (rate : ℝ≥0) (E : Set ℕ) :
    |(bernoulliPartialSumLaw (blockAttachmentParameter x n hn b hbn)
        (blockAttachmentIndices a b)).real E - (poissonMeasure rate).real E| ≤
      (2 / (c * a)) * heightInterval x a b + |heightInterval x a b - (rate : ℝ)| := by
  have hh := bernoulliPartialSumLaw_poisson_parameter_event
    (blockAttachmentParameter x n hn b hbn) (blockAttachmentIndices a b) rate E
  rw [sum_blockAttachmentParameter] at hh
  exact hh.trans (add_le_add
    (sum_sq_blockAttachmentParameter_le_linear x n hn a b hbn ha hc herr) le_rfl)

/-- The upper-endpoint cutoff supplies the typing bound for a block in the row. -/
theorem geometricBlock_le_horizon {a C n : ℕ} {ε : ℝ}
    (hε : ε ≤ 1) (hupper : (a * C : ℕ) ≤ ε * (n : ℝ)) : a * C ≤ n := by
  have hh : ((a * C : ℕ) : ℝ) ≤ n := hupper.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  exact_mod_cast hh

/-- Uniform Poisson approximation for every geometric block in the source
window. The proof of `a*C ≤ n` is supplied explicitly only to type its parameter
restriction; `geometricBlock_le_horizon` derives it from the displayed cutoff. -/
theorem uniform_geometricBlock_poisson_approximation
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A (c : ℝ))
    (C : ℕ) (hC : 1 < C) :
    ∀ δ > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (hbn : a * C ≤ n), A n ≤ (a : ℝ) →
        ((a * C : ℕ) : ℝ) ≤ ε * n → ∀ E : Set ℕ,
        |(bernoulliPartialSumLaw (blockAttachmentParameter (x n) n (hn n) (a * C) hbn)
            (blockAttachmentIndices a (a * C))).real E -
          (poissonMeasure (linearPoissonRate c C)).real E| ≤ δ := by
  intro δ hδ
  let K : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  let L : ℝ := Real.log (C : ℝ)
  let D : ℝ := min (δ / (2 * L)) (1 / L)
  let M : ℝ := K * L + 1
  let C0 : ℝ := ((C : ℝ) + 1) / 2
  have hc := c.property.1
  have hCR : (1 : ℝ) < C := by exact_mod_cast hC
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := Real.log_pos hCR
  have hD : 0 < D := lt_min (by positivity) (by positivity)
  have hM : 0 < M := by dsimp [M]; positivity
  have hC0 : 1 < C0 := by dsimp [C0]; linarith
  have hC0C : C0 < (C : ℝ) := by dsimp [C0]; linarith
  obtain ⟨ε1, hε1, hε1lt, hpoint⟩ := hnear ((c : ℝ) / 2) (half_pos hc)
  obtain ⟨ε2, hε2, hε2lt, hblock⟩ :=
    uniformLogIntervals_of_nearOriginLinear hnear hA hc hC0 D hD
  let ε : ℝ := min ε1 ε2
  have hε : 0 < ε := lt_min hε1 hε2
  have hεlt : ε < 1 := (min_le_left _ _).trans_lt hε1lt
  refine ⟨ε, hε, hεlt, ?_⟩
  filter_upwards [hpoint, hblock, hA.eventually_ge_atTop (max 1 (4 * M / ((c : ℝ) * δ)))]
    with n hpointn hblockn hAn
  intro a hbn hAa hupper E
  have ha1 : (1 : ℝ) ≤ a := (le_max_left _ _).trans (hAn.trans hAa)
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have ha : 1 ≤ a := by exact_mod_cast ha1
  have hab : a < a * C := by nlinarith
  have hupper1 : ((a * C : ℕ) : ℝ) ≤ ε1 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
  have hupper2 : ((a * C : ℕ) : ℝ) ≤ ε2 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
  have herr : ∀ j ∈ Finset.Icc a (a * C),
      |(activeCount (x n) j : ℝ) / j - (c : ℝ)| ≤ (c : ℝ) / 2 := by
    intro j hj
    obtain ⟨haj, hjb⟩ := Finset.mem_Icc.mp hj
    exact hpointn j (hAa.trans (by exact_mod_cast haj))
      ((by exact_mod_cast hjb : (j : ℝ) ≤ (a * C : ℕ)).trans hupper1)
  have hsep : (a : ℝ) * C0 < (a * C : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_left hC0C ha0
  have hmid := hblockn a (a * C) hAa hab hupper2 hsep
  have hlogratio : Real.log (((a * C : ℕ) : ℝ) / a) = L := by
    dsimp [L]
    congr 1
    push_cast
    field_simp
  rw [hlogratio] at hmid
  have heq : heightInterval (x n) a (a * C) / L - K =
      (heightInterval (x n) a (a * C) - K * L) / L := by field_simp
  rw [heq, abs_div, abs_of_pos hL] at hmid
  have hmean := (div_le_iff₀ hL).mp hmid
  have hDδ : D * L ≤ δ / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp (min_le_left (δ / (2 * L)) (1 / L))
    change D * (2 * L) ≤ δ at hh
    nlinarith
  have hD1 : D * L ≤ 1 := (le_div_iff₀ hL).mp (min_le_right (δ / (2 * L)) (1 / L))
  have hrate : (linearPoissonRate c C : ℝ) = K * L := rfl
  have hmeanδ : |heightInterval (x n) a (a * C) - (linearPoissonRate c C : ℝ)| ≤ δ / 2 := by
    rw [hrate]
    exact hmean.trans hDδ
  have hH : heightInterval (x n) a (a * C) ≤ M := by
    have hh := (le_abs_self (heightInterval (x n) a (a * C) - K * L)).trans (hmean.trans hD1)
    dsimp [M]
    linarith
  have hcut : 4 * M / ((c : ℝ) * δ) ≤ (a : ℝ) :=
    (le_max_right _ _).trans (hAn.trans hAa)
  have hsquare : (2 / ((c : ℝ) * a)) * heightInterval (x n) a (a * C) ≤ δ / 2 := by
    refine (mul_le_mul_of_nonneg_left hH (by positivity)).trans ?_
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hc ha0)).mpr
    have hh := (div_le_iff₀ (mul_pos hc hδ)).mp hcut
    nlinarith
  have hfinite := block_bernoulli_poisson_event_error (x n) n (hn n) a (a * C) hbn ha hc herr
    (linearPoissonRate c C) E
  exact hfinite.trans (by linarith)

/-- The analytic part of Lemma 12, with the exact block parameters. Multiplying
by the actual deterministic population at the upper endpoint gives the source
constant `5*a`. Turning this product into the expectation of a random-root
count still requires the conditional block-law factorization. -/
theorem exists_uniform_geometricBlock_weighted_tail_lower
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A (c : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      (2 : ℝ) < linearPoissonRate c C ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ (a : ℕ) (hbn : a * C ≤ n), A n ≤ (a : ℝ) →
          ((a * C : ℕ) : ℝ) ≤ ε * n →
          5 * (a : ℝ) ≤ (activeCount (x n) (a * C) : ℝ) *
            (bernoulliPartialSumLaw
              (blockAttachmentParameter (x n) n (hn n) (a * C) hbn)
              (blockAttachmentIndices a (a * C))).real
              {k : ℕ | (linearPoissonRate c C : ℝ) *
                (linearHeightFactor c - η) < (k : ℝ)} := by
  obtain ⟨C, hC, hsize, hrate, htail⟩ := exists_linear_poisson_tail_scale c hη
  have hc := c.property.1
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hCR : (1 : ℝ) < C := by exact_mod_cast hC
  have hδ : 0 < 1 / (2 * (c : ℝ) * C) := by positivity
  obtain ⟨ε1, hε1, hε1lt, happ⟩ :=
    uniform_geometricBlock_poisson_approximation x A c hn hA hnear C hC
      (1 / (2 * (c : ℝ) * C)) hδ
  obtain ⟨ε2, hε2, hε2lt, hpoint⟩ := hnear ((c : ℝ) / 11) (by positivity)
  let ε := min ε1 ε2
  refine ⟨C, hC, hsize, hrate, ε, lt_min hε1 hε2,
    (min_le_left _ _).trans_lt hε1lt, ?_⟩
  filter_upwards [happ, hpoint, hA.eventually_ge_atTop 1] with n happn hpointn hAn
  intro a hbn hAa hupper
  have ha1 : (1 : ℝ) ≤ a := hAn.trans hAa
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hab : (a : ℝ) ≤ (a * C : ℕ) := by
    push_cast
    nlinarith
  have hb0 : (0 : ℝ) < (a * C : ℕ) := ha0.trans_le hab
  have hupper1 : ((a * C : ℕ) : ℝ) ≤ ε1 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
  have hupper2 : ((a * C : ℕ) : ℝ) ≤ ε2 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
  let E : Set ℕ := {k | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)}
  let P : ℝ := (bernoulliPartialSumLaw
    (blockAttachmentParameter (x n) n (hn n) (a * C) hbn)
    (blockAttachmentIndices a (a * C))).real E
  have happE := happn a hbn hAa hupper1 E
  have hP : 11 / (2 * (c : ℝ) * C) ≤ P := by
    have hh := (abs_le.mp happE).1
    change -(1 / (2 * (c : ℝ) * C)) ≤ P - (poissonMeasure (linearPoissonRate c C)).real E at hh
    have he : 6 / ((c : ℝ) * C) - 1 / (2 * (c : ℝ) * C) =
        11 / (2 * (c : ℝ) * C) := by field_simp; ring
    rw [← he]
    dsimp [E] at hh ⊢
    linarith
  have hSratio := (abs_le.mp (hpointn (a * C) (hAa.trans hab) hupper2)).1
  have hSratio' : 10 * (c : ℝ) / 11 ≤
      (activeCount (x n) (a * C) : ℝ) / (a * C : ℕ) := by linarith
  have hS := (le_div_iff₀ hb0).mp hSratio'
  have hS0 : 0 ≤ (activeCount (x n) (a * C) : ℝ) := by
    exact le_trans (by positivity) hS
  change 5 * (a : ℝ) ≤ (activeCount (x n) (a * C) : ℝ) * P
  calc
    5 * (a : ℝ) = (10 * (c : ℝ) / 11 * (a * C : ℕ)) *
        (11 / (2 * (c : ℝ) * C)) := by push_cast; field_simp; ring
    _ ≤ (activeCount (x n) (a * C) : ℝ) * (11 / (2 * (c : ℝ) * C)) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ ≤ (activeCount (x n) (a * C) : ℝ) * P := mul_le_mul_of_nonneg_left hP hS0

end Freezing1
