module

public import Freezing1.SIRFluidProfile

/-!
# The principal real Lambert inverse and the SIR profile

The principal branch is the inverse of `w ↦ w * exp w` on `[-1,∞)`.
Values below its real domain are totalized to `-1` and are never used in
the characterization or derivative statements. The derivative quotient
excludes zero, where its displayed source expression is indeterminate.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set
open scoped Topology

noncomputable def lambertMap (w : ℝ) : ℝ := w * Real.exp w

theorem lambertMap_hasDerivAt (w : ℝ) :
    HasDerivAt lambertMap (Real.exp w * (1 + w)) w := by
  convert (hasDerivAt_id w).mul (Real.hasDerivAt_exp w) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem lambertMap_strictMonoOn : StrictMonoOn lambertMap (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by unfold lambertMap; fun_prop)
  intro w hw
  rw [interior_Ici] at hw
  have hw' : -1 < w := hw
  rw [(lambertMap_hasDerivAt w).deriv]
  exact mul_pos (Real.exp_pos w) (by linarith)

theorem lambertMap_tendsto_atTop : Tendsto lambertMap atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
  exact le_mul_of_one_le_right hw (Real.one_le_exp hw)

theorem lambertMap_surjOn : SurjOn lambertMap (Ici (-1)) (Ici (-Real.exp (-1))) := by
  have hh := intermediate_value_Ici (f := lambertMap) (a := (-1 : ℝ))
    (by unfold lambertMap; fun_prop) lambertMap_tendsto_atTop
  simpa [SurjOn, lambertMap] using hh

noncomputable def lambertMapIso : Ici (-1 : ℝ) ≃o Ici (-Real.exp (-1)) :=
  (show StrictMono (fun w : Ici (-1 : ℝ) =>
    (⟨lambertMap w, by
      have hh := lambertMap_strictMonoOn.monotoneOn (by simp) w.property w.property
      simpa [lambertMap] using hh⟩ : Ici (-Real.exp (-1)))) from
    fun x y hxy => lambertMap_strictMonoOn x.property y.property hxy).orderIsoOfSurjective _ (by
      intro x
      obtain ⟨w, hw, he⟩ := lambertMap_surjOn x.property
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩)

noncomputable def principalLambertW (x : ℝ) : ℝ :=
  if hx : -Real.exp (-1) ≤ x then (lambertMapIso.symm ⟨x, hx⟩ : ℝ) else -1

theorem principalLambertW_mem {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    -1 ≤ principalLambertW x := by
  simp only [principalLambertW, dite_eq_left hx]
  exact (lambertMapIso.symm ⟨x, hx⟩).property

theorem lambertMap_principalLambertW {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    lambertMap (principalLambertW x) = x := by
  have hh := congrArg Subtype.val (lambertMapIso.apply_symm_apply ⟨x, hx⟩)
  change lambertMap (lambertMapIso.symm ⟨x, hx⟩ : ℝ) = x at hh
  simpa only [principalLambertW, dite_eq_left hx] using hh

theorem principalLambertW_eq_of_characterization {x w : ℝ} (hw : -1 ≤ w)
    (he : lambertMap w = x) : principalLambertW x = w := by
  have hx : -Real.exp (-1) ≤ x := by
    rw [← he]
    have hh := lambertMap_strictMonoOn.monotoneOn (by simp) hw hw
    simpa [lambertMap] using hh
  exact lambertMap_strictMonoOn.injOn (principalLambertW_mem hx) hw
    ((lambertMap_principalLambertW hx).trans he.symm)

theorem principalLambertW_zero : principalLambertW 0 = 0 :=
  principalLambertW_eq_of_characterization (by norm_num) (by simp [lambertMap])

theorem principalLambertW_left_endpoint :
    principalLambertW (-Real.exp (-1)) = -1 :=
  principalLambertW_eq_of_characterization le_rfl (by simp [lambertMap])

theorem principalLambertW_lambertMap {w : ℝ} (hw : -1 ≤ w) :
    principalLambertW (lambertMap w) = w :=
  principalLambertW_eq_of_characterization hw rfl

theorem principalLambertW_strictMonoOn :
    StrictMonoOn principalLambertW (Ici (-Real.exp (-1))) := by
  intro x hx y hy hxy
  apply lt_of_not_ge
  intro h
  have hh := lambertMap_strictMonoOn.monotoneOn
    (principalLambertW_mem hy) (principalLambertW_mem hx) h
  rw [lambertMap_principalLambertW hy, lambertMap_principalLambertW hx] at hh
  exact (not_le_of_gt hxy) hh

theorem principalLambertW_continuousOn :
    ContinuousOn principalLambertW (Ici (-Real.exp (-1))) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun x : Ici (-Real.exp (-1)) => principalLambertW x)
  have he : (fun x : Ici (-Real.exp (-1)) => principalLambertW x) =
      fun x => (lambertMapIso.symm x : ℝ) := by
    funext x
    rw [principalLambertW, dite_eq_left (show -Real.exp (-1) ≤ (x : ℝ) from x.property)]
  rw [he]
  exact continuous_subtype_val.comp lambertMapIso.symm.continuous

theorem principalLambertW_hasDerivAt {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt principalLambertW
      (Real.exp (principalLambertW x) * (1 + principalLambertW x))⁻¹ x := by
  have hw : -1 < principalLambertW x := by
    have hle := principalLambertW_mem hx.le
    have he := lambertMap_principalLambertW hx.le
    by_contra hn
    have hz : principalLambertW x = -1 := by linarith
    rw [hz] at he
    simp only [lambertMap, neg_mul, one_mul] at he
    linarith
  apply (lambertMap_hasDerivAt (principalLambertW x)).of_local_left_inverse
    ((principalLambertW_continuousOn x hx.le).continuousAt (Ici_mem_nhds hx))
    (mul_pos (Real.exp_pos _) (by linarith)).ne'
  filter_upwards [Ici_mem_nhds hx] with y hy
  exact lambertMap_principalLambertW hy

theorem principalLambertW_deriv_quotient {x : ℝ}
    (hx : -Real.exp (-1) < x) (hx0 : x ≠ 0) :
    deriv principalLambertW x =
      principalLambertW x / (x * (1 + principalLambertW x)) := by
  rw [(principalLambertW_hasDerivAt hx).deriv]
  have he := lambertMap_principalLambertW hx.le
  unfold lambertMap at he
  have hw0 : principalLambertW x ≠ 0 := by
    intro hh
    simp [hh] at he
    exact hx0 he.symm
  generalize hw : principalLambertW x = w at *
  rw [← he]
  field_simp

theorem principalLambertW_hasDerivAt_zero : HasDerivAt principalLambertW 1 0 := by
  have hh := principalLambertW_hasDerivAt
    (show -Real.exp (-1) < 0 by linarith [Real.exp_pos (-1 : ℝ)])
  simpa [principalLambertW_zero] using hh

theorem fluidProfile_lambertW {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    fluidProfile lam t =
      (1 / lam) * principalLambertW (lam * Real.exp lam * Real.exp (-lam * t)) := by
  have hg := fluidProfile_pos hlam t
  have hh := congrArg Real.exp (fluidProfile_implicit hlam t)
  rw [Real.exp_add, Real.exp_log hg] at hh
  have he : lambertMap (lam * fluidProfile lam t) =
      lam * Real.exp lam * Real.exp (-lam * t) := by
    unfold lambertMap
    rw [mul_assoc, hh]
    rw [show lam * (1 - t) = lam + (-lam * t) by ring, Real.exp_add]
    ring
  have hw : -1 ≤ lam * fluidProfile lam t := by nlinarith [mul_pos hlam hg]
  rw [principalLambertW_eq_of_characterization hw he]
  field_simp

end Freezing1.SIR
