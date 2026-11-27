import PermutationStrips.Angular

/-! The height parameter is a smooth coordinate on the whole first quadrant.
The angle π/4 + arctan(2t−1) has Jacobian between one and two, even at the axes. -/

open Set MeasureTheory
namespace PermutationStrips.Angular
noncomputable section

theorem affine_length (a c : ℝ) (F : Set ℝ) :
    volume.real ((fun x => a+c*x) '' F) = |c| * volume.real F := by
  by_cases hc : c = 0
  · subst c
    have sub : (fun x : ℝ => a+0*x) '' F ⊆ {a} := by rintro _ ⟨x,_,rfl⟩; simp
    have hh := measureReal_mono (μ := volume) sub (by simp)
    have hzero : volume.real ({a} : Set ℝ) = 0 := by simp [measureReal_def]
    rw [hzero] at hh
    rw [abs_zero,zero_mul]
    exact le_antisymm hh measureReal_nonneg
  have he : (fun x => a+c*x) '' F = (fun z : ℝ => z+ -a) ⁻¹' ((fun z : ℝ => c⁻¹*z) ⁻¹' F) := by
    ext z
    change (∃ y ∈ F, a+c*y=z) ↔ c⁻¹*(z+-a) ∈ F
    constructor
    · rintro ⟨y,hy,rfl⟩
      convert hy using 1; field_simp; ring
    · intro hz
      refine ⟨_,hz,?_⟩; field_simp; ring
  rw [measureReal_def,he,measure_preimage_add_right, Real.volume_preimage_mul_left (inv_ne_zero hc),
    inv_inv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

def angle (t : ℝ) : ℝ := Real.pi/4 + Real.arctan (2*t-1)
def jac (t : ℝ) : ℝ := 2/(1+(2*t-1)^2)

theorem angle_deriv (t : ℝ) : HasDerivAt angle (jac t) t := by
  have h := ((Real.hasDerivAt_arctan _).comp t (((hasDerivAt_id t).const_mul 2).sub_const 1)).const_add (Real.pi/4)
  convert h using 1
  simp [jac,id]; ring

theorem angle_mono : Monotone angle := by
  intro a b h
  exact add_le_add_left (Real.arctan_strictMono.monotone (by linarith)) _

theorem angle_ends : angle 0 = 0 ∧ angle 1 = Real.pi/2 := by
  constructor
  · norm_num [angle, Real.arctan_neg, Real.arctan_one]
  · norm_num [angle, Real.arctan_one]; ring

theorem angle_change (g : ℝ → ℝ) :
    (∫ θ in (0:ℝ)..(Real.pi/2), g θ) = ∫ t in (0:ℝ)..1, jac t * g (angle t) := by
  have eq := ContinuousOn.image_Icc_of_monotoneOn (zero_le_one : (0:ℝ) ≤ 1)
    (continuous_iff_continuousAt.mpr (fun t => (angle_deriv t).continuousAt)).continuousOn (angle_mono.monotoneOn _)
  rw [angle_ends.1,angle_ends.2] at eq
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, ← eq]
  exact integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Icc
    (fun t _ => (angle_deriv t).hasDerivWithinAt) (angle_mono.monotoneOn _) g

theorem jac_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : jac t ∈ Icc 1 2 := by
  have hd : 0 < 1+(2*t-1)^2 := by positivity
  exact ⟨(le_div_iff₀ hd).mpr (by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]),
    (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg (2*t-1)])⟩

theorem angle_components {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Real.cos (angle t) = speed (angle t)*(1-t) ∧ Real.sin (angle t) = speed (angle t)*t := by
  let a := angle t
  have range : a ∈ Icc (0:ℝ) (Real.pi/2) := ⟨angle_ends.1 ▸ angle_mono ht.1, angle_ends.2 ▸ angle_mono ht.2⟩
  have hs : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi range.1 (range.2.trans (by linarith [Real.pi_pos]))
  have hc : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [range.1, Real.pi_pos], range.2⟩
  have H : (1-t)*Real.sin a = t*Real.cos a := by
    dsimp [a,angle]
    rw [Real.sin_add,Real.cos_add,Real.sin_pi_div_four,Real.cos_pi_div_four,Real.sin_arctan,Real.cos_arctan]
    ring
  change Real.cos a = speed a*(1-t) ∧ Real.sin a = speed a*t
  rw [speed, abs_of_nonneg hs,abs_of_nonneg hc]
  constructor <;> nlinarith

theorem rho_angle {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : rho (angle t) = min t (1-t) := by
  obtain ⟨hc,hs⟩ := angle_components ht
  have hp := speed_pos (angle t)
  unfold rho
  rw [hc,hs,abs_of_nonneg (mul_nonneg hp.le (sub_nonneg.mpr ht.2)), abs_of_nonneg (mul_nonneg hp.le ht.1),
    ← mul_min_of_nonneg _ _ hp.le, min_comm]
  field_simp

theorem length_angle (K : Set (ℝ × ℝ)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    length K (angle t) = speed (angle t)*volume.real (projection t '' K) := by
  obtain ⟨hc,hs⟩ := angle_components ht
  have he : proj (angle t) '' K = (fun z => 0+speed (angle t)*z) '' (projection t '' K) := by
    rw [image_image]; apply image_congr; intro p _
    unfold projection proj; rw [hc,hs]; ring
  rw [length,he,affine_length,abs_of_pos (speed_pos _)]

theorem weighted_height_le {b : ℝ → ℝ} (hb : Admissible b) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {t : ℝ} (ht : t ∈ Ioc (0:ℝ) (1/2)) :
    b t * volume.real (projection t '' K) ≤ weighted b K := by
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.trans (by norm_num)⟩
  have he : rho (angle t) = t := by rw [rho_angle ht',min_eq_left (by linarith [ht.2])]
  have h := le_weighted hb hK (θ := angle t) (by rw [he]; exact ht.1)
  rw [he,length_angle K ht'] at h
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_left _ (hb.2 t ht).1
  exact le_mul_of_one_le_left measureReal_nonneg (speed_bounds _).1

theorem area_le_favard {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    (∫ t in (0:ℝ)..1, volume.real (projection t '' K)) ≤ favard K := by
  have hpi : (0:ℝ) ≤ Real.pi/2 := by positivity
  have hpi' : Real.pi/2 ≤ Real.pi := by linarith [Real.pi_pos]
  let f (t : ℝ) := volume.real (projection t '' K)
  have hm : Measurable ((Icc (0:ℝ) 1).indicator f) := by
    have ha : Continuous angle := continuous_iff_continuousAt.mpr fun t => (angle_deriv t).continuousAt
    have hs : Continuous speed := by unfold speed; fun_prop
    have e : (Icc (0:ℝ) 1).indicator f =
        (Icc (0:ℝ) 1).indicator (fun t => length K (angle t) / speed (angle t)) := by
      apply indicator_congr; intro t ht
      change volume.real _ = length K (angle t) / speed (angle t)
      rw [length_angle K ht]; field_simp [(speed_pos (angle t)).ne']
    rw [e]; exact (((measurable_length hK).comp ha.measurable).div (hs.comp ha).measurable).indicator measurableSet_Icc
  obtain ⟨C,hC,hbound⟩ := length_bounded hK
  have hff (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : f t ≤ length K (angle t) := by
    rw [length_angle K ht]; exact le_mul_of_one_le_left measureReal_nonneg (speed_bounds _).1
  have hi : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine (IntegrableOn.of_bound (s := Ioc (0:ℝ) 1) measure_Ioc_lt_top hm.aestronglyMeasurable C ?_).congr_fun ?_ measurableSet_Ioc
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
      rw [indicator_of_mem ht',Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ f t from measureReal_nonneg)]
      exact (hff t ht').trans (hbound _)
    · intro t ht; exact indicator_of_mem (show t ∈ Icc (0:ℝ) 1 from ⟨ht.1.le,ht.2⟩) _
  have hj : IntervalIntegrable (fun t => jac t * length K (angle t)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hmj : Measurable (fun t => jac t * length K (angle t)) :=
      (show Measurable jac by unfold jac; fun_prop).mul ((measurable_length hK).comp (continuous_iff_continuousAt.mpr (fun t => (angle_deriv t).continuousAt)).measurable)
    apply IntegrableOn.of_bound measure_Ioc_lt_top hmj.aestronglyMeasurable (2*C)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    have hb := jac_bounds ⟨ht.1.le,ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ jac t * length K (angle t) from mul_nonneg (by linarith [hb.1]) measureReal_nonneg)]
    exact mul_le_mul hb.2 (hbound _) measureReal_nonneg (by norm_num)
  calc
    _ ≤ ∫ t in (0:ℝ)..1, jac t * length K (angle t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hi hj
      intro t ht; exact (hff t ht).trans (le_mul_of_one_le_left measureReal_nonneg (jac_bounds ht).1)
    _ = _ := (angle_change _).symm
    _ ≤ favard K := by
      unfold favard
      rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_length hK 0 (Real.pi/2))
        (intervalIntegrable_length hK (Real.pi/2) Real.pi)]
      exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hpi' (fun _ _ => measureReal_nonneg))

end
end PermutationStrips.Angular
