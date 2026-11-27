import PermutationStrips.AngularCoordinates

open Set MeasureTheory
namespace PermutationStrips.Angular
noncomputable section

theorem length_add_pi (K : Set (ℝ × ℝ)) (θ : ℝ) : length K (θ+Real.pi) = length K θ := by
  have e : proj (θ+Real.pi) '' K = (fun x : ℝ => 0+(-1)*x) '' (proj θ '' K) := by
    rw [image_image]; apply image_congr; intro p _; simp [proj]; ring
  rw [length,e,affine_length]; simp [length]

theorem length_swap (K : Set (ℝ × ℝ)) (θ : ℝ) :
    length (Prod.swap '' K) θ = length K (Real.pi/2-θ) := by
  unfold length
  rw [image_image]
  apply congrArg volume.real
  apply image_congr
  intro p _; simp [proj,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]; ring

theorem rho_swap (θ : ℝ) : rho (Real.pi/2-θ) = rho θ := by
  simp [rho,speed,Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,min_comm,add_comm]

theorem weighted_swap (b : ℝ → ℝ) (K : Set (ℝ × ℝ)) : weighted b (Prod.swap '' K) = weighted b K := by
  unfold weighted
  congr 1
  ext x
  constructor
  · rintro ⟨θ,h,rfl⟩
    refine ⟨Real.pi/2-θ, ?_, ?_⟩
    · change 0 < rho _; rwa [rho_swap]
    · simp only [rho_swap,length_swap]
  · rintro ⟨θ,h,rfl⟩
    refine ⟨Real.pi/2-θ, ?_, ?_⟩
    · change 0 < rho _; rwa [rho_swap]
    · simp only [rho_swap,length_swap,sub_sub_cancel]

theorem favard_swap {K : Set (ℝ × ℝ)} (hK : IsCompact K) : favard (Prod.swap '' K) = favard K := by
  have hs := hK.image (show Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ) from continuous_swap)
  let h := Real.pi/2
  have hp : 0 ≤ h := by dsimp [h]; positivity
  have hr : h ≤ Real.pi := by dsimp [h]; linarith [Real.pi_pos]
  have comp (a b : ℝ) : (∫ θ in a..b, length (Prod.swap '' K) θ) =
      ∫ θ in (h-b)..(h-a), length K θ := by
    simp_rw [length_swap]
    exact intervalIntegral.integral_comp_sub_left (length K) _
  have neg : (∫ θ in (-h)..0, length K θ) = ∫ θ in h..Real.pi, length K θ := by
    have eq := intervalIntegral.integral_comp_add_right (a := -h) (b := 0) (length K) Real.pi
    simp_rw [length_add_pi] at eq
    simpa [show -h+Real.pi=h by dsimp [h];ring] using eq
  unfold favard
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_length hs 0 h) (intervalIntegrable_length hs h Real.pi),
    ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_length hK 0 h) (intervalIntegrable_length hK h Real.pi),
    comp,comp,sub_self,sub_zero,show h-Real.pi = -h by dsimp [h];ring,neg]

theorem rho_supplement (θ : ℝ) : rho (Real.pi-θ) = rho θ := by
  simp [rho,speed,Real.cos_pi_sub,Real.sin_pi_sub]

theorem inv_sqrt_eq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x)⁻¹ = x ^ (-(1/2):ℝ) := by
  rw [Real.rpow_neg hx,Real.sqrt_eq_rpow]

theorem inv_sqrt_integrable : IntervalIntegrable (fun x : ℝ => (Real.sqrt x)⁻¹) volume 0 1 := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by norm_num : (-1:ℝ) < -(1/2))).congr
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  exact (inv_sqrt_eq t ht.1.le).symm

theorem inv_sqrt_integral : (∫ t in (0:ℝ)..1, (Real.sqrt t)⁻¹) = 2 := by
  calc
    _ = ∫ t in (0:ℝ)..1, t^(-(1/2):ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht; exact inv_sqrt_eq t (by rw [uIcc_of_le zero_le_one] at ht; exact ht.1)
    _ = _ := by rw [integral_rpow (Or.inl (by norm_num))]; norm_num

/-- Integrating the square-root envelope controls unnormalised Favard length. -/
theorem favard_of_sqrt {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ θ, 0 < rho θ → Real.sqrt (rho θ)*length K θ ≤ A) :
    favard K ≤ 16*A := by
  let g := fun θ => length K θ + length K (Real.pi-θ)
  have hg : favard K = ∫ θ in (0:ℝ)..(Real.pi/2), g θ := by
    have he := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi/2) (length K) Real.pi
    have ha := intervalIntegrable_length hK (Real.pi/2) Real.pi
    have hb : IntervalIntegrable (fun θ => length K (Real.pi-θ)) volume 0 (Real.pi/2) := by
      convert (ha.comp_sub_left Real.pi).symm using 1 <;> ring
    rw [favard, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_length hK 0 (Real.pi/2)) ha,
      show (∫ θ in (0:ℝ)..(Real.pi/2), g θ) = _ from
        intervalIntegral.integral_add (intervalIntegrable_length hK 0 (Real.pi/2)) hb,he]
    congr 2 <;> ring
  let e := fun t : ℝ => (Real.sqrt t)⁻¹ + (Real.sqrt (1-t))⁻¹
  have he : IntervalIntegrable e volume 0 1 := by
    apply inv_sqrt_integrable.add
    convert (inv_sqrt_integrable.comp_sub_left 1).symm using 1 <;> norm_num
  have hei : (∫ t in (0:ℝ)..1, e t) = 4 := by
    unfold e
    rw [intervalIntegral.integral_add inv_sqrt_integrable (by
      convert (inv_sqrt_integrable.comp_sub_left 1).symm using 1 <;> norm_num),
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => (Real.sqrt t)⁻¹), sub_self,sub_zero, inv_sqrt_integral]
    norm_num
  rw [hg,angle_change]
  have hbnd : ∀ t ∈ Ioo (0:ℝ) 1, jac t*g (angle t) ≤ 4*A*e t := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hr : 0 < rho (angle t) := by rw [rho_angle ht']; exact lt_min ht.1 (sub_pos.mpr ht.2)
    have ir : (Real.sqrt (rho (angle t)))⁻¹ ≤ e t := by
      rw [rho_angle ht']; unfold e
      rcases le_total t (1-t) with h|h
      · rw [min_eq_left h]; exact le_add_of_nonneg_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
      · rw [min_eq_right h]; linarith [inv_nonneg.mpr (Real.sqrt_nonneg t)]
    have aux (θ : ℝ) (eq : rho θ = rho (angle t)) : length K θ ≤ A*e t := by
      have v := h θ (eq.symm ▸ hr)
      rw [eq] at v
      calc
        _ ≤ A/(Real.sqrt (rho (angle t))) := (le_div_iff₀ (Real.sqrt_pos.2 hr)).mpr (by linarith)
        _ ≤ _ := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left ir hA
    have q := aux (angle t) rfl
    have q' := aux _ (rho_supplement (angle t))
    have j := jac_bounds ht'
    change jac t * (length K (angle t) + length K (Real.pi-angle t)) ≤ _
    apply (mul_le_mul_of_nonneg_right j.2 (add_nonneg (show 0 ≤ length K (angle t) from measureReal_nonneg)
      (show 0 ≤ length K (Real.pi-angle t) from measureReal_nonneg))).trans
    linarith only [q,q']
  have hnon : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ jac t*g (angle t) := by
    intro t ht
    exact mul_nonneg (zero_le_one.trans (jac_bounds ht).1) (add_nonneg measureReal_nonneg measureReal_nonneg)
  have major := he.const_mul (4*A)
  have hm : Measurable (fun t => jac t*g (angle t)) := by
    have ha := (continuous_iff_continuousAt.mpr fun t => (angle_deriv t).continuousAt).measurable
    apply (show Measurable jac by unfold jac; fun_prop).mul
    exact ((measurable_length hK).comp ha).add ((measurable_length hK).comp (measurable_const.sub ha))
  have ae : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), t ∈ Ioo (0:ℝ) 1 := by
    rw [← restrict_Ioo_eq_restrict_Ioc]; exact ae_restrict_mem measurableSet_Ioo
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp major
  calc
    _ ≤ ∫ t in Ioc (0:ℝ) 1, 4*A*e t := by
      apply integral_mono_ae _ hi (ae.mono fun t ht => hbnd t ht)
      apply hi.mono' hm.aestronglyMeasurable
      filter_upwards [ae] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hnon t ⟨ht.1.le,ht.2.le⟩)]
      exact hbnd t ht
    _ = _ := by rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,hei]; ring

end
end PermutationStrips.Angular
