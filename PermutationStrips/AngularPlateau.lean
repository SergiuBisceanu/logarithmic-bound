import PermutationStrips.AngularScales

/-! An admissible near-axis plateau whose logarithmic cost is at most one. -/

open MeasureTheory Set
namespace PermutationStrips.AngularBlock
noncomputable section

def plateauBase (m k : ℕ) : ℝ := Real.exp ((k:ℝ)/(4*m))
def plateauCutoff (m k : ℕ) : ℝ := Real.exp (-((k:ℝ)/m))
def plateauProfile (m k : ℕ) (r : ℝ) : ℝ := if plateauCutoff m k ≤ r then (m:ℝ)/k else 0
def plateauWeight (m k : ℕ) (r : ℝ) : ℝ := max (plateauProfile m k r) (Real.sqrt r)

theorem plateauBase_lower {m k : ℕ} (hm : 0 < m) (hk : 32768*m^2 ≤ k) :
    1024*(k:ℝ) ≤ plateauBase m k := by
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have hk' : 32768*(m:ℝ)^2 ≤ k := by exact_mod_cast hk
  have h := Real.pow_div_factorial_le_exp ((k:ℝ)/(4*m)) (by positivity) 2
  norm_num [Nat.factorial] at h
  apply le_trans _ h
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg k)]

theorem plateauCutoff_mul_base_pow (m k : ℕ) :
    plateauCutoff m k * (plateauBase m k)^4 = 1 := by
  unfold plateauCutoff plateauBase
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  norm_num only [Nat.cast_ofNat]
  by_cases hm : (m:ℝ)=0
  · simp [hm]
  · rw [show -((k:ℝ)/m) + 4*((k:ℝ)/(4*m)) = 0 by field_simp; ring, Real.exp_zero]

theorem plateauWeight_ge {m k : ℕ} {r : ℝ} (h : plateauCutoff m k ≤ r) :
    (m:ℝ)/k ≤ plateauWeight m k r := by
  exact (le_of_eq (by simp [plateauProfile,h] : (m:ℝ)/k=plateauProfile m k r)).trans (le_max_left ..)

theorem plateauProfile_properties {m k : ℕ} (hm : 0 < m) (hmk : m≤k) :
    let v := plateauProfile m k
    Measurable v ∧ (∀ r ∈ Ioc (0:ℝ) (1/2), v r ∈ Icc 0 1) ∧
      MonotoneOn v (Ioc (0:ℝ) (1/2)) ∧ IntegrableOn (fun r => v r/r) (Ioc (0:ℝ) (1/2)) ∧
      (∫ r in Ioc (0:ℝ) (1/2), v r/r) ≤ 1 := by
  let T := plateauCutoff m k
  let a := (m:ℝ)/k
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have kp : 0 < (k:ℝ) := by exact_mod_cast hm.trans_le hmk
  have mk : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have ap : 0 ≤ a := div_nonneg mp.le kp.le
  have a1 : a≤1 := (div_le_one kp).mpr mk
  have tp : 0<T := Real.exp_pos _
  have th : T≤1/2 := by
    change Real.exp (-((k:ℝ)/m)) ≤ 1/2
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp ((k:ℝ)/m), (one_le_div mp).mpr mk])
  let v := plateauProfile m k
  have vm : Monotone v := by
    intro r s hrs
    by_cases h : T ≤ r
    · change (if T ≤ r then a else 0) ≤ (if T ≤ s then a else 0)
      rw [if_pos h,if_pos (h.trans hrs)]
    · change (if T ≤ r then a else 0) ≤ (if T ≤ s then a else 0)
      rw [if_neg h]; split <;> simp_all
  have vr (r : ℝ) : v r ∈ Icc 0 1 := by
    change (if T ≤ r then a else 0) ∈ Icc 0 1
    split <;> simp_all
  have eqf : (fun r => v r/r) = (Ici T).indicator (fun r => a*r⁻¹) := by
    funext r
    change (if T ≤ r then a else 0)/r = (Ici T).indicator (fun s => a*s⁻¹) r
    by_cases h : T ≤ r <;> simp [Set.indicator,mem_Ici,h,div_eq_mul_inv]
  have sub : Ioc (0:ℝ) (1/2) ∩ Ici T = Icc T (1/2) := by
    ext r; exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨tp.trans_le h.1,h.2⟩,h.1⟩⟩
  have vi : IntegrableOn (fun r => v r/r) (Ioc (0:ℝ) (1/2)) := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top (vm.measurable.div measurable_id).aestronglyMeasurable T⁻¹
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
    rw [id_eq,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (vr _).1 hr.1.le)]
    by_cases h : T ≤ r
    · exact (div_le_div_of_nonneg_right (vr _).2 hr.1.le).trans (by simpa [one_div] using inv_anti₀ tp h)
    · change (if T ≤ r then a else 0)/r ≤ _; simp [h,tp.le]
  refine ⟨vm.measurable, fun r _ => vr r, vm.monotoneOn _, vi, ?_⟩
  change (∫ r in Ioc (0:ℝ) (1/2), v r/r) ≤ 1
  rw [eqf, setIntegral_indicator measurableSet_Ici, sub, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le th, intervalIntegral.integral_const_mul,
    integral_inv_of_pos tp (by norm_num), Real.log_div (by norm_num) tp.ne']
  change a*(Real.log (1/2)-Real.log (Real.exp (-((k:ℝ)/m)))) ≤ 1
  rw [Real.log_exp]
  calc
    _ ≤ a*((k:ℝ)/m) := mul_le_mul_of_nonneg_left (by linarith [Real.log_nonpos (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2≤1)]) ap
    _ = 1 := by dsimp [a]; field_simp

theorem plateauWeight_properties {m k : ℕ} (hm : 0 < m) (hmk : m≤k) :
    let w := plateauWeight m k
    Measurable w ∧ (∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1) ∧
      MonotoneOn w (Ioc (0:ℝ) (1/2)) ∧ IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)) ∧
      (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3 := by
  obtain ⟨vm,vr,vmono,vi,vI⟩ := plateauProfile_properties hm hmk
  let v := plateauProfile m k
  let w := plateauWeight m k
  let J := Ioc (0:ℝ) (1/2)
  have wm : Measurable w := vm.max Real.continuous_sqrt.measurable
  have wr (r : ℝ) (hr : r ∈ J) : w r ∈ Icc 0 1 := ⟨(vr r hr).1.trans (le_max_left ..),
    max_le (vr r hr).2 (Real.sqrt_le_one.mpr (hr.2.trans (by norm_num)))⟩
  have si : IntegrableOn (fun r : ℝ => (Real.sqrt r)⁻¹) J :=
    Angular.inv_sqrt_integrable.1.mono_set (Ioc_subset_Ioc le_rfl (by norm_num))
  have sI : (∫ r in J, (Real.sqrt r)⁻¹) ≤ 2 := by
    rw [show J = Ioc (0:ℝ) (1/2) from rfl, ← intervalIntegral.integral_of_le (by norm_num)]
    exact (intervalIntegral.integral_mono_interval le_rfl (by norm_num) (by norm_num)
      (Filter.Eventually.of_forall fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _)) Angular.inv_sqrt_integrable).trans
      Angular.inv_sqrt_integral.le
  have bound (r : ℝ) (hr : r ∈ J) : w r/r ≤ v r/r + (Real.sqrt r)⁻¹ := by
    have eq : Real.sqrt r/r = (Real.sqrt r)⁻¹ := by
      field_simp [(Real.sqrt_pos.mpr hr.1).ne', hr.1.ne']; exact Real.sq_sqrt hr.1.le
    change max (v r) (Real.sqrt r) / r ≤ _
    rw [← max_div_div_right hr.1.le,eq]
    exact max_le (le_add_of_nonneg_right (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (le_add_of_nonneg_left (div_nonneg (vr r hr).1 hr.1.le))
  have wi : IntegrableOn (fun r => w r/r) J := by
    apply (vi.add si).mono' (wm.div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
    rw [id_eq,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (wr r hr).1 hr.1.le)]
    exact bound r hr
  refine ⟨wm,wr,vmono.max (Real.sqrt_monotone.monotoneOn _),wi,?_⟩
  have h := integral_mono_ae wi (vi.add si) ((ae_restrict_mem (μ:=volume) measurableSet_Ioc).mono (fun r hr => bound r hr))
  simp only [Pi.add_apply] at h
  rw [integral_add vi si] at h
  linarith only [vI,sI,h]

end
end PermutationStrips.AngularBlock
