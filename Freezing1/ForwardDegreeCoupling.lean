module

public import Freezing1.ForwardDegreeDivergence
public import Freezing1.ForwardSchedulePrefix

/-! The source's increasing matching-prefix extraction and actual coupling
of every old vertex degree with the later row horizon. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Classical

theorem exists_strictMono_matching_prefixes (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n,
      n ≤ φ n ∧ SchedulesAgreeThrough (rows (φ n)) y n := by
  have hN : ∀ n, ∃ N, ∀ j ≥ N, SchedulesAgreeThrough (rows j) y n :=
    fun n => eventually_atTop.mp (eventually_schedulesAgreeThrough hxy n)
  choose N hN using hN
  let φ : ℕ → ℕ := Nat.rec (N 0) (fun n m => max (m + 1) (N (n + 1)))
  have hs (n : ℕ) : φ (n + 1) = max (φ n + 1) (N (n + 1)) := rfl
  have hφN : ∀ n, N n ≤ φ n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => rw [hs]; exact le_max_right _ _
  have hmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hs]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hnφ : ∀ n, n ≤ φ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt (hmono (Nat.lt_succ_self n)))
  exact ⟨φ, hmono, fun n => ⟨hnφ n, hN n (φ n) (hφN n)⟩⟩

namespace ForwardInfiniteHistory

open Forward

theorem prefixCoupling_vertexDegree_le {x y : SignSequence} {a b : ℕ}
    (hxy : SchedulesAgreeThrough x y a) (hab : a ≤ b) (r : ℕ) :
    ∀ᵐ p ∂prefixCoupling x y a, vertexDegree (p.1 a) r ≤ vertexDegree (p.2 b) r := by
  have hm : ∀ᵐ p ∂prefixCoupling x y a,
      Monotone (fun k => vertexDegree (p.2 k) r) := by
    apply ae_of_ae_map (μ := prefixCoupling x y a) (f := Prod.snd)
      (p := fun H : History => Monotone (fun k => vertexDegree (H k) r))
      measurable_snd.aemeasurable
    rw [prefixCoupling_snd hxy]
    exact (fullLaw_all_vertexDegree_monotone y).mono fun _ h => h r
  filter_upwards [prefixCoupling_agrees x y a, hm] with p hp hmono
  rw [hp a le_rfl]
  exact hmono hab

/-- Each extracted row admits the actual full-history coupling used by
the source. Its fixed-schedule prefix degree is dominated at the row's
terminal horizon; no diagonal nonextinction premise is needed. -/
theorem exists_matching_degree_couplings (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n,
      (prefixCoupling y (rows (φ n)) n).map Prod.fst = fullLaw y ∧
      (prefixCoupling y (rows (φ n)) n).map Prod.snd = fullLaw (rows (φ n)) ∧
      ∀ᵐ p ∂prefixCoupling y (rows (φ n)) n, ∀ r,
        vertexDegree (p.1 n) r ≤ vertexDegree (p.2 (φ n)) r := by
  obtain ⟨φ, hmono, hφ⟩ := exists_strictMono_matching_prefixes rows y hxy
  refine ⟨φ, hmono, fun n => ?_⟩
  have hp : SchedulesAgreeThrough y (rows (φ n)) n :=
    fun i hi hin => ((hφ n).2 i hi hin).symm
  exact ⟨prefixCoupling_fst _ _ _, prefixCoupling_snd hp,
    ae_all_iff.mpr (fun r => prefixCoupling_vertexDegree_le hp (hφ n).1 r)⟩

end ForwardInfiniteHistory
end Freezing1
