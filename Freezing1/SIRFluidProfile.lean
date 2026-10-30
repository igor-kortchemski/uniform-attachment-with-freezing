module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Order.Hom.Set
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

/-!
# The actual susceptible fluid profile in the SIR theorem

For positive lambda, the globally increasing map z ↦ z + lambda exp z is
inverted by an order isomorphism. Exponentiating its inverse gives the unique
positive solution of log g + lambda g = lambda (1-t). The definition outside
positive lambda is a total default and is never used in the source results.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

noncomputable def expLinear (lam z : ℝ) : ℝ := z + lam * Real.exp z

theorem expLinear_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (expLinear lam) := by
  intro x y hxy
  have he := (Real.exp_lt_exp.mpr hxy)
  dsimp [expLinear]
  exact add_lt_add hxy (mul_lt_mul_of_pos_left he hlam)

theorem expLinear_continuous (lam : ℝ) : Continuous (expLinear lam) := by
  unfold expLinear
  fun_prop

theorem expLinear_surjective {lam : ℝ} (hlam : 0 < lam) : Function.Surjective (expLinear lam) := by
  intro y
  let a := y - lam * Real.exp y
  have hmul : 0 ≤ lam * Real.exp y := mul_nonneg hlam.le (Real.exp_pos y).le
  have hab : a ≤ y := by dsimp [a]; linarith
  have hlow : expLinear lam a ≤ y := by
    have he := Real.exp_le_exp.mpr hab
    have hm := mul_le_mul_of_nonneg_left he hlam.le
    dsimp [a, expLinear] at *
    linarith
  have hhigh : y ≤ expLinear lam y := by
    dsimp [expLinear]
    linarith
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc hab (expLinear_continuous lam).continuousOn
    ⟨hlow, hhigh⟩
  exact ⟨z, hz⟩

noncomputable def expLinearIso (lam : ℝ) (hlam : 0 < lam) : ℝ ≃o ℝ :=
  (expLinear_strictMono hlam).orderIsoOfSurjective _ (expLinear_surjective hlam)

theorem expLinearIso_apply (lam : ℝ) (hlam : 0 < lam) (z : ℝ) :
    expLinearIso lam hlam z = expLinear lam z := rfl

noncomputable def fluidProfile (lam t : ℝ) : ℝ :=
  if hlam : 0 < lam then Real.exp ((expLinearIso lam hlam).symm (lam * (1 - t))) else 1

theorem fluidProfile_pos {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    0 < fluidProfile lam t := by
  simp only [fluidProfile, dite_eq_left hlam]
  exact Real.exp_pos _

theorem fluidProfile_implicit {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    Real.log (fluidProfile lam t) + lam * fluidProfile lam t = lam * (1 - t) := by
  simp only [fluidProfile, dite_eq_left hlam, Real.log_exp]
  exact (expLinearIso lam hlam).apply_symm_apply (lam * (1 - t))

theorem fluidProfile_eq_of_implicit {lam t x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (he : Real.log x + lam * x = lam * (1 - t)) : x = fluidProfile lam t := by
  have h : expLinear lam (Real.log x) = lam * (1 - t) := by
    simpa only [expLinear, Real.exp_log hx] using he
  have hi : Real.log x = (expLinearIso lam hlam).symm (lam * (1 - t)) := by
    apply (expLinearIso lam hlam).injective
    rw [expLinearIso_apply, h, OrderIso.apply_symm_apply]
  rw [fluidProfile, dite_eq_left hlam, ← hi, Real.exp_log hx]

theorem fluidProfile_zero {lam : ℝ} (hlam : 0 < lam) : fluidProfile lam 0 = 1 := by
  symm
  apply fluidProfile_eq_of_implicit hlam zero_lt_one
  simp

theorem fluidProfile_strictAnti {lam : ℝ} (hlam : 0 < lam) : StrictAnti (fluidProfile lam) := by
  intro s t hst
  simp only [fluidProfile, dite_eq_left hlam]
  apply Real.exp_lt_exp.mpr
  apply (expLinearIso lam hlam).symm.strictMono
  exact mul_lt_mul_of_pos_left (by linarith) hlam

theorem fluidProfile_le_one {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    fluidProfile lam t ≤ 1 := by
  rw [← fluidProfile_zero hlam]
  exact (fluidProfile_strictAnti hlam).antitone ht

theorem fluidProfile_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (fluidProfile lam) := by
  have he : fluidProfile lam = fun t => Real.exp ((expLinearIso lam hlam).symm (lam * (1 - t))) := by
    funext t
    simp [fluidProfile, hlam]
  rw [he]
  exact Real.continuous_exp.comp ((expLinearIso lam hlam).symm.continuous.comp (by fun_prop))

theorem expLinear_hasDerivAt (lam z : ℝ) :
    HasDerivAt (expLinear lam) (1 + lam * Real.exp z) z := by
  change HasDerivAt (fun x : ℝ => x + lam * Real.exp x) _ z
  convert (hasDerivAt_id z).add ((Real.hasDerivAt_exp z).const_mul lam) using 1
  funext x
  rfl

theorem fluidProfile_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (fluidProfile lam)
      (-lam * fluidProfile lam t / (1 + lam * fluidProfile lam t)) t := by
  let e := expLinearIso lam hlam
  let y := lam * (1 - t)
  have hpos : 0 < 1 + lam * Real.exp (e.symm y) := by positivity
  have hi : HasDerivAt e.symm (1 + lam * Real.exp (e.symm y))⁻¹ y := by
    apply (expLinear_hasDerivAt lam (e.symm y)).of_local_left_inverse e.symm.continuous.continuousAt
      (ne_of_gt hpos)
    exact Eventually.of_forall (fun z => e.apply_symm_apply z)
  have ht : HasDerivAt (fun r : ℝ => lam * (1 - r)) (-lam) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).const_mul lam
  have hd := (Real.hasDerivAt_exp (e.symm y)).comp t (hi.comp t ht)
  convert hd using 1
  · funext r
    simp [fluidProfile, hlam, e]
  · simp only [fluidProfile, dite_eq_left hlam]
    dsimp [e, y]
    ring

theorem fluidProfile_deriv_zero {lam : ℝ} (hlam : 0 < lam) :
    deriv (fluidProfile lam) 0 = -lam / (1 + lam) := by
  rw [(fluidProfile_hasDerivAt hlam 0).deriv, fluidProfile_zero hlam]
  ring

theorem fluidProfile_contDiff {lam : ℝ} (hlam : 0 < lam) :
    ContDiff ℝ ∞ (fluidProfile lam) := by
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr (fluidProfile_continuous hlam)
  | succ n ih =>
    change ContDiff ℝ ((n : ℕ∞ω) + 1) (fluidProfile lam)
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun t => (fluidProfile_hasDerivAt hlam t).differentiableAt, ?_, ?_⟩
    · intro h
      have hn : (n : ℕ∞ω) ≠ ω := by simp
      exact (hn h).elim
    · have he : deriv (fluidProfile lam) =
          fun t => -lam * fluidProfile lam t / (1 + lam * fluidProfile lam t) :=
        funext fun t => (fluidProfile_hasDerivAt hlam t).deriv
      rw [he]
      exact (contDiff_const.mul ih).div (contDiff_const.add (contDiff_const.mul ih))
        (fun t => ne_of_gt (by have := fluidProfile_pos hlam t; positivity))

theorem fluidProfile_le_exp {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    fluidProfile lam t ≤ Real.exp (lam * (1 - t)) := by
  have hh := fluidProfile_implicit hlam t
  have hm := mul_nonneg hlam.le (fluidProfile_pos hlam t).le
  have he : Real.log (fluidProfile lam t) ≤ lam * (1 - t) := by linarith
  have hexp := Real.exp_le_exp.mpr he
  rwa [Real.exp_log (fluidProfile_pos hlam t)] at hexp

theorem fluidProfile_tendsto_zero {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fluidProfile lam) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => -(lam * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hlam)
  have hlinear : Tendsto (fun t : ℝ => lam * (1 - t)) atTop atBot := by
    convert tendsto_atBot_add_const_left atTop lam ht using 1
    ext t
    ring
  exact squeeze_zero (fun t => (fluidProfile_pos hlam t).le)
    (fluidProfile_le_exp hlam) (Real.tendsto_exp_atBot.comp hlinear)

noncomputable def infectiousProfile (lam t : ℝ) : ℝ := 2 - 2 * fluidProfile lam t - t

theorem infectiousProfile_zero {lam : ℝ} (hlam : 0 < lam) : infectiousProfile lam 0 = 0 := by
  simp [infectiousProfile, fluidProfile_zero hlam]

theorem infectiousProfile_continuous {lam : ℝ} (hlam : 0 < lam) :
    Continuous (infectiousProfile lam) :=
  (continuous_const.sub (continuous_const.mul (fluidProfile_continuous hlam))).sub continuous_id

theorem infectiousProfile_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (infectiousProfile lam)
      ((lam * fluidProfile lam t - 1) / (1 + lam * fluidProfile lam t)) t := by
  have hd := ((hasDerivAt_const t (2 : ℝ)).sub
    ((fluidProfile_hasDerivAt hlam t).const_mul 2)).sub (hasDerivAt_id t)
  convert hd using 1
  · funext r
    rfl
  · have hn : 1 + lam * fluidProfile lam t ≠ 0 := ne_of_gt (by
      have := fluidProfile_pos hlam t
      positivity)
    field_simp
    ring

theorem infectiousProfile_deriv_zero {lam : ℝ} (hlam : 0 < lam) :
    deriv (infectiousProfile lam) 0 = (lam - 1) / (lam + 1) := by
  rw [(infectiousProfile_hasDerivAt hlam 0).deriv, fluidProfile_zero hlam]
  congr 1 <;> ring

theorem fluidProfile_deriv_strictMono {lam : ℝ} (hlam : 0 < lam) :
    StrictMono (deriv (fluidProfile lam)) := by
  intro s t hst
  rw [(fluidProfile_hasDerivAt hlam s).deriv, (fluidProfile_hasDerivAt hlam t).deriv]
  have hspos : 0 < 1 + lam * fluidProfile lam s := by
    have := fluidProfile_pos hlam s
    positivity
  have htpos : 0 < 1 + lam * fluidProfile lam t := by
    have := fluidProfile_pos hlam t
    positivity
  apply (div_lt_div_iff₀ hspos htpos).mpr
  have hg := fluidProfile_strictAnti hlam hst
  nlinarith

theorem fluidProfile_strictConvex {lam : ℝ} (hlam : 0 < lam) :
    StrictConvexOn ℝ univ (fluidProfile lam) :=
  (fluidProfile_deriv_strictMono hlam).strictConvexOn_univ_of_deriv
    (fluidProfile_continuous hlam)

theorem infectiousProfile_deriv_strictAnti {lam : ℝ} (hlam : 0 < lam) :
    StrictAnti (deriv (infectiousProfile lam)) := by
  intro s t hst
  rw [(infectiousProfile_hasDerivAt hlam t).deriv,
    (infectiousProfile_hasDerivAt hlam s).deriv]
  have hspos : 0 < 1 + lam * fluidProfile lam s := by
    have := fluidProfile_pos hlam s
    positivity
  have htpos : 0 < 1 + lam * fluidProfile lam t := by
    have := fluidProfile_pos hlam t
    positivity
  apply (div_lt_div_iff₀ htpos hspos).mpr
  have hg := fluidProfile_strictAnti hlam hst
  nlinarith

theorem infectiousProfile_strictConcave {lam : ℝ} (hlam : 0 < lam) :
    StrictConcaveOn ℝ univ (infectiousProfile lam) :=
  (infectiousProfile_deriv_strictAnti hlam).strictConcaveOn_univ_of_deriv
    (infectiousProfile_continuous hlam)

noncomputable def peakTime (lam : ℝ) : ℝ := (lam - 1 + Real.log lam) / lam

theorem fluidProfile_peakTime {lam : ℝ} (hlam : 0 < lam) :
    fluidProfile lam (peakTime lam) = 1 / lam := by
  symm
  apply fluidProfile_eq_of_implicit hlam (one_div_pos.mpr hlam)
  rw [Real.log_div (by norm_num) hlam.ne', Real.log_one]
  dsimp [peakTime]
  field_simp
  ring

theorem infectiousProfile_peakTime {lam : ℝ} (hlam : 0 < lam) :
    infectiousProfile lam (peakTime lam) = (lam - 1 - Real.log lam) / lam := by
  rw [infectiousProfile, fluidProfile_peakTime hlam]
  dsimp [peakTime]
  field_simp [hlam.ne']
  ring

theorem peakTime_pos_lt_two {lam : ℝ} (hlam : 1 < lam) :
    0 < peakTime lam ∧ peakTime lam < 2 := by
  have hlpos : 0 < lam := by linarith
  have hlogpos := Real.log_pos hlam
  have hloglt := Real.log_lt_sub_one_of_pos hlpos (ne_of_gt hlam)
  constructor
  · unfold peakTime
    apply div_pos _ hlpos
    linarith
  · unfold peakTime
    apply (div_lt_iff₀ hlpos).mpr
    linarith

theorem infectiousProfile_peakTime_pos {lam : ℝ} (hlam : 1 < lam) :
    0 < infectiousProfile lam (peakTime lam) := by
  have hlpos : 0 < lam := by linarith
  rw [infectiousProfile_peakTime hlpos]
  apply div_pos _ hlpos
  have hloglt := Real.log_lt_sub_one_of_pos hlpos (ne_of_gt hlam)
  linarith

theorem infectiousProfile_two_neg {lam : ℝ} (hlam : 0 < lam) :
    infectiousProfile lam 2 < 0 := by
  have hp := fluidProfile_pos hlam 2
  unfold infectiousProfile
  linarith

theorem infectiousProfile_exists_positive_zero {lam : ℝ} (hlam : 1 < lam) :
    ∃ t : ℝ, 0 < t ∧ t < 2 ∧ infectiousProfile lam t = 0 := by
  have hlpos : 0 < lam := by linarith
  have hpeak := peakTime_pos_lt_two hlam
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hpeak.2.le
    (infectiousProfile_continuous hlpos).continuousOn
    ⟨(infectiousProfile_two_neg hlpos).le, (infectiousProfile_peakTime_pos hlam).le⟩
  refine ⟨t, hpeak.1.trans_le ht.1, ?_, he⟩
  by_contra hnot
  have ht2 : t = 2 := by linarith [ht.2]
  have := infectiousProfile_two_neg hlpos
  rw [← ht2, he] at this
  linarith

theorem infectiousProfile_positive_zero_unique {lam u v : ℝ} (hlam : 0 < lam)
    (hu : 0 < u) (hv : 0 < v) (heu : infectiousProfile lam u = 0)
    (hev : infectiousProfile lam v = 0) : u = v := by
  have hc := infectiousProfile_strictConcave hlam
  have hzero := infectiousProfile_zero hlam
  rcases lt_trichotomy u v with huv | he | hvu
  · have hh := hc.lt_on_openSegment (mem_univ 0) (mem_univ v) (ne_of_lt hv)
      (by rw [openSegment_eq_Ioo hv]; exact ⟨hu, huv⟩ : u ∈ openSegment ℝ 0 v)
    rw [hzero, hev, heu, min_self] at hh
    linarith
  · exact he
  · have hh := hc.lt_on_openSegment (mem_univ 0) (mem_univ u) (ne_of_lt hu)
      (by rw [openSegment_eq_Ioo hu]; exact ⟨hv, hvu⟩ : v ∈ openSegment ℝ 0 u)
    rw [hzero, heu, hev, min_self] at hh
    linarith

noncomputable def fluidExtinctionTime (lam : ℝ) : ℝ :=
  if hlam : 1 < lam then (infectiousProfile_exists_positive_zero hlam).choose else 0

theorem fluidExtinctionTime_spec {lam : ℝ} (hlam : 1 < lam) :
    0 < fluidExtinctionTime lam ∧ fluidExtinctionTime lam < 2 ∧
      infectiousProfile lam (fluidExtinctionTime lam) = 0 := by
  simp only [fluidExtinctionTime, dite_eq_left hlam]
  exact (infectiousProfile_exists_positive_zero hlam).choose_spec

theorem infectiousProfile_pos_before {lam t : ℝ} (hlam : 1 < lam)
    (ht0 : 0 < t) (ht : t < fluidExtinctionTime lam) : 0 < infectiousProfile lam t := by
  have hlpos : 0 < lam := by linarith
  have hT := fluidExtinctionTime_spec hlam
  have hh := (infectiousProfile_strictConcave hlpos).lt_on_openSegment
    (mem_univ 0) (mem_univ (fluidExtinctionTime lam)) (ne_of_lt hT.1)
    (by rw [openSegment_eq_Ioo hT.1]; exact ⟨ht0, ht⟩ : t ∈ openSegment ℝ 0 (fluidExtinctionTime lam))
  simpa only [infectiousProfile_zero hlpos, hT.2.2, min_self] using hh

theorem infectiousProfile_neg_after {lam t : ℝ} (hlam : 1 < lam)
    (ht : fluidExtinctionTime lam < t) : infectiousProfile lam t < 0 := by
  have hlpos : 0 < lam := by linarith
  have hT := fluidExtinctionTime_spec hlam
  have htp := hT.1.trans ht
  have hh := (infectiousProfile_strictConcave hlpos).lt_on_openSegment
    (mem_univ 0) (mem_univ t) (ne_of_lt htp)
    (by rw [openSegment_eq_Ioo htp]; exact ⟨hT.1, ht⟩ : fluidExtinctionTime lam ∈ openSegment ℝ 0 t)
  rw [infectiousProfile_zero hlpos, hT.2.2, min_lt_iff] at hh
  exact hh.resolve_left (lt_irrefl _)

/-- Positive solutions of the source ODE with the prescribed initial value
coincide with the actual constructed profile on nonnegative times. -/
theorem fluidProfile_unique_positive {lam : ℝ} (hlam : 0 < lam) {g : ℝ → ℝ}
    (hg0 : g 0 = 1) (hgpos : ∀ t ≥ 0, 0 < g t)
    (hgderiv : ∀ t ≥ 0, HasDerivAt g (-lam * g t / (1 + lam * g t)) t)
    {t : ℝ} (ht : 0 ≤ t) : g t = fluidProfile lam t := by
  let F : ℝ → ℝ := fun s => Real.log (g s) + lam * g s + lam * s
  have hF : ∀ s ≥ 0, HasDerivAt F 0 s := by
    intro s hs
    have hp := hgpos s hs
    have hn : 1 + lam * g s ≠ 0 := ne_of_gt (by positivity)
    have hd := (((hgderiv s hs).log hp.ne').add ((hgderiv s hs).const_mul lam)).add
      ((hasDerivAt_id s).const_mul lam)
    convert hd using 1
    · funext r
      rfl
    · field_simp [hp.ne', hn]
      ring
  have hFt : F t = F 0 := by
    by_cases ht0 : t = 0
    · rw [ht0]
    · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      obtain ⟨c, _, he⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) htp
        (fun s hs => (hF s hs.1).continuousAt.continuousWithinAt)
        (fun s hs => hF s hs.1.le)
      have he' : (F t - F 0) / t = 0 := by simpa using he.symm
      exact sub_eq_zero.mp ((div_eq_zero_iff).mp he' |>.resolve_right ht0)
  apply fluidProfile_eq_of_implicit hlam (hgpos t ht)
  have he0 : F 0 = lam := by simp [F, hg0]
  rw [he0] at hFt
  dsimp [F] at hFt
  linarith

end Freezing1.SIR
