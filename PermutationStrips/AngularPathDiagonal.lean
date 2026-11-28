import PermutationStrips.AngularPathLower
import PermutationStrips.AngularFiniteTests

/-! Each prescribed sublinear sample count fails for a single fixed, integrable
profile, even when the constant in the target is allowed to depend on the profile. -/

open Filter Set MeasureTheory
open scoped BigOperators Topology
namespace PermutationStrips.AngularBlock
noncomputable section

private def mass (j : ℕ) : ℝ := 1/2/2^j

/-- A convex sum of admissible profiles is admissible and dominates each
summand. Tonelli's theorem preserves the logarithmic integral budget. -/
private theorem combine_profiles (f : ℕ → ℝ → ℝ) (hf : ∀ j, AdmissibleProfile (f j)) :
    ∃ v, AdmissibleProfile v ∧ ∀ j r, r ∈ Ioc (0:ℝ) (1/2) → mass j*f j r ≤ v r := by
  let D := Ioc (0:ℝ) (1/2)
  let μ := volume.restrict D
  let v (r : ℝ) := (∑' j, ENNReal.ofReal (mass j*f j r)).toReal
  have ap j : 0 < mass j := by dsimp [mass]; positivity
  have ha : HasSum mass 1 := hasSum_geometric_two' 1
  have pos j r (hr : r ∈ D) := mul_nonneg (ap j).le ((hf j).2.1 r hr).1
  have upper j r (hr : r ∈ D) := mul_le_of_le_one_right (ap j).le ((hf j).2.1 r hr).2
  have sum r (hr : r ∈ D) : Summable (fun j => mass j*f j r) :=
    .of_nonneg_of_le (fun j => pos j r hr) (fun j => upper j r hr) ha.summable
  have eqv r (hr : r ∈ D) : v r = ∑' j, mass j*f j r := by
    dsimp only [v]; rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => pos j r hr) (sum r hr),
      ENNReal.toReal_ofReal (tsum_nonneg fun j => pos j r hr)]
  have vm : Measurable v :=
    (Measurable.ennreal_tsum (fun j => (measurable_const.mul (hf j).1).ennreal_ofReal)).ennreal_toReal
  have vr r (hr : r ∈ D) : v r ∈ Icc 0 1 := ⟨ENNReal.toReal_nonneg,by
    rw [eqv r hr,← ha.tsum_eq]; exact (sum r hr).tsum_le_tsum (fun j => upper j r hr) ha.summable⟩
  have g j : Integrable (fun r => mass j*(f j r/r)) μ := (hf j).2.2.2.1.const_mul _
  have gp j : 0 ≤ᵐ[μ] fun r => mass j*(f j r/r) := by
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=D) measurableSet_Ioc] with r hr
    exact mul_nonneg (ap j).le (div_nonneg ((hf j).2.1 r hr).1 hr.1.le)
  have gi j : (∫ r, mass j*(f j r/r) ∂μ) ≤ mass j := by
    rw [integral_const_mul]; exact mul_le_of_le_one_right (ap j).le (hf j).2.2.2.2
  have ep : 0 ≤ᵐ[μ] fun r => v r/r := by
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=D) measurableSet_Ioc] with r hr
    exact div_nonneg (vr _ hr).1 hr.1.le
  have cost : (∫⁻ r, ENNReal.ofReal (v r/r) ∂μ) ≤ 1 := calc
    _ = ∫⁻ r, ∑' j, ENNReal.ofReal (mass j*(f j r/r)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) (s:=D) measurableSet_Ioc] with r hr
      rw [eqv r hr,← tsum_div_const,ENNReal.ofReal_tsum_of_nonneg (fun j => div_nonneg (pos j r hr) hr.1.le) ((sum r hr).div_const r)]
      simp only [mul_div_assoc]
    _ = ∑' j, ∫⁻ r, ENNReal.ofReal (mass j*(f j r/r)) ∂μ :=
      lintegral_tsum fun j => ((g j).aestronglyMeasurable.aemeasurable).ennreal_ofReal
    _ ≤ ∑' j, ENNReal.ofReal (mass j) := ENNReal.tsum_le_tsum (fun j => by
      rw [← ofReal_integral_eq_lintegral_ofReal (g j) (gp j)]; exact ENNReal.ofReal_le_ofReal (gi j))
    _ = 1 := by rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (ap j).le) ha.summable,ha.tsum_eq,ENNReal.ofReal_one]
  have vi : Integrable (fun r => v r/r) μ := ⟨(vm.div measurable_id).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal ep).mpr (cost.trans_lt (by simp))⟩
  refine ⟨v,⟨vm,vr,?_,vi,?_⟩,?_⟩
  · intro r hr s hs hrs
    rw [eqv _ hr,eqv _ hs]
    exact (sum r hr).tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left ((hf j).2.2.1 hr hs hrs) (ap j).le) (sum s hs)
  · apply (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp
    rwa [ofReal_integral_eq_lintegral_ofReal vi ep,ENNReal.ofReal_one]
  · intro j r hr
    rw [eqv _ hr]; exact (sum r hr).le_tsum j fun i _ => pos i r hr

/-- Given any o(k) sample budget, a single admissible profile forces
arbitrarily large constants at arbitrarily large depths. Each height can depend
on the competing ensemble. -/
theorem fixed_profile_obstruction (M : ℕ → ℕ)
    (sublinear : Tendsto (fun k : ℕ => (M k:ℝ)/(k:ℝ)) atTop (𝓝 0)) :
    ∃ v, AdmissibleProfile v ∧ ∀ j : ℕ, ∃ k > j, ∀ N : ℕ, 0 < N → N ≤ M k →
      ∀ p : Fin N → Path, PathBudget k p →
      ∃ t ∈ Ioo (0:ℝ) 1, (j:ℝ)/k < weightedMean v p t := by
  classical
  have pick (j : ℕ) : ∃ k > j, ∃ f, AdmissibleProfile f ∧ ∀ N : ℕ, 0 < N → N ≤ M k →
      ∀ p : Fin N → Path, PathBudget k p →
      ∃ t ∈ Ioo (0:ℝ) 1, ((j:ℝ)/mass j)/k < weightedMean f p t := by
    obtain ⟨c,hc,hard⟩ := exists_hard_profile ((j:ℝ)/mass j)
    obtain ⟨k,⟨hk,small⟩,f,hf,h⟩ := ((eventually_gt_atTop j).and
      (sublinear.eventually_lt_const hc)).and hard |>.exists
    have kp : (0:ℝ)<k := by exact_mod_cast (Nat.zero_le j).trans_lt hk
    refine ⟨k,hk,f,hf,fun N hN bound => h N hN ?_⟩
    exact (Nat.cast_le.mpr bound).trans ((div_lt_iff₀ kp).mp small).le
  choose k hk f hf force using pick
  obtain ⟨v,hv,dom⟩ := combine_profiles f hf
  refine ⟨v,hv,fun j => ⟨k j,hk j,fun N hN bound p hp => ?_⟩⟩
  obtain ⟨t,ht,bad⟩ := force j N hN bound p hp
  have ap : 0 < mass j := by dsimp [mass]; positivity
  have a1 : mass j≤1 := by
    rw [mass,div_le_iff₀ (by positivity)]
    exact (by norm_num : (1:ℝ)/2≤1).trans (by simpa using one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j))
  have hr := radius_mem_of_interior ht
  have w : mass j*max (f j (radius t)) (Real.sqrt (radius t)) ≤ max (v (radius t)) (Real.sqrt (radius t)) := by
    rw [mul_max_of_nonneg _ _ ap.le]
    exact max_le_max (dom j _ hr) (mul_le_of_le_one_left (Real.sqrt_nonneg _) a1)
  have h := mul_le_mul_of_nonneg_right w (show 0≤(∑ i, len (p i).pattern t)/(N:ℝ) by positivity)
  refine ⟨t,ht,lt_of_lt_of_le ?_ h⟩
  calc
    _ = mass j*(((j:ℝ)/mass j)/(k j:ℝ)) := by field_simp
    _ < mass j*weightedMean (f j) p t := mul_lt_mul_of_pos_left bad ap
    _ = _ := by unfold weightedMean; ring

end
end PermutationStrips.AngularBlock
