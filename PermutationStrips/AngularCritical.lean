import PermutationStrips.AngularExtrema
import PermutationStrips.Profile

/-! The critical logarithmic weight detects the extra log-log factor even without Favard length. -/

open MeasureTheory Set Filter Asymptotics
open scoped Interval Topology Asymptotics

namespace PermutationStrips.Angular
noncomputable section

def criticalWeight (r : ℝ) : ℝ := 1/(1+Real.log (1/r))

theorem critical_admissible : Admissible criticalWeight := by
  have bounds {r : ℝ} (hr : r ∈ Ioc (0:ℝ) (1/2)) : 1 ≤ 1+Real.log (1/r) := by
    have hr' : r≤1 := hr.2.trans (by norm_num)
    linarith [Real.log_nonneg ((le_div_iff₀ hr.1).2 (by linarith) : 1≤1/r)]
  constructor
  · intro x hx y hy hxy
    apply one_div_le_one_div_of_le (zero_lt_one.trans_le (bounds hy))
    exact add_le_add_left (Real.log_le_log (one_div_pos.mpr hy.1)
      (one_div_le_one_div_of_le hx.1 hxy)) _
  · intro r hr
    exact ⟨(one_div_pos.mpr (zero_lt_one.trans_le (bounds hr))).le, (div_le_one (zero_lt_one.trans_le (bounds hr))).2 (bounds hr)⟩

theorem critical_truncated {δ : ℝ} (hd : 0<δ) (hh : δ≤1/2) :
    truncated criticalWeight δ = Real.log (1+Real.log (1/δ))-Real.log (1+Real.log 2) := by
  rw [← Profile.critical_integral hd hh]
  apply intervalIntegral.integral_congr
  intro r _
  change (1/(1+Real.log (1/r)))/r=1/(r*(1+Real.log (1/r)))
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The least value of the weighted directional supremum on the equal grid. -/
def gridWeightedMin (b : ℝ → ℝ) (n : ℕ) : ℝ :=
  if hn : 0<n then sInf (range (fun σ : Equiv.Perm (Fin n) => weighted b (Pattern.equalGrid hn σ).carrier))
  else 0

theorem gridWeightedMin_attained (b : ℝ → ℝ) {n : ℕ} (hn : 0<n) :
    ∃ σ : Equiv.Perm (Fin n), weighted b (Pattern.equalGrid hn σ).carrier = gridWeightedMin b n := by
  rw [gridWeightedMin,dif_pos hn]
  exact (range_nonempty _).csInf_mem (finite_range _)

theorem gridWeightedMin_le_joint (b : ℝ → ℝ) {n : ℕ} (hn : 0<n) :
    gridWeightedMin b n ≤ gridMin b n hn := by
  obtain ⟨σ,he⟩ := gridMin_attained b hn
  let K := (Pattern.equalGrid hn σ).carrier
  change favard K+weighted b K = _ at he
  rw [← he,gridWeightedMin,dif_pos hn]
  refine (csInf_le (finite_range _).bddBelow (mem_range_self σ)).trans ?_
  exact le_add_of_nonneg_left (intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => measureReal_nonneg))

/-- The grid upper law at the critical weight implies the sharp rate for the
weighted supremum alone, using its separate geometric lower bound. -/
theorem critical_grid_rate_of_joint {C : ℝ} (hC : 0 ≤ C)
    (upper : ∀ n : ℕ, (hn : 2≤n) → gridMin criticalWeight n (by omega) ≤
      C*(1+truncated criticalWeight (1/n))/Real.log n) :
    gridWeightedMin criticalWeight =Θ[atTop] (fun n : ℕ => Real.log (Real.log n)/Real.log n) := by
  let c := Real.log (1+Real.log 2)
  let L (n : ℕ) := Real.log n
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT := Real.tendsto_log_atTop.comp hL
  have ev : ∀ᶠ n : ℕ in atTop,
      Real.log (L n)/L n ≤ 48*gridWeightedMin criticalWeight n ∧
      gridWeightedMin criticalWeight n ≤ 3*C*(Real.log (L n)/L n) ∧
      0 ≤ gridWeightedMin criticalWeight n ∧ 0 ≤ Real.log (L n)/L n := by
    filter_upwards [eventually_ge_atTop (2:ℕ),hL.eventually_ge_atTop 1,
      hT.eventually_ge_atTop (2*|c|+4)] with n hn hl ht
    change 2*|c|+4 ≤ Real.log (L n) at ht
    have hn0 : 0<n := by omega
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    have lp : 0<L n := zero_lt_one.trans_le hl
    have hh : 1/(n:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hnR
    have tr := critical_truncated (one_div_pos.mpr (by positivity : 0<(n:ℝ))) hh
    rw [show 1/(1/(n:ℝ)) = n by simp] at tr
    change truncated criticalWeight (1/n) = Real.log (1+L n)-c at tr
    have lo : Real.log (L n) ≤ Real.log (1+L n) := Real.log_le_log lp (by linarith)
    have hi : Real.log (1+L n) ≤ Real.log 2 + Real.log (L n) := by
      rw [← Real.log_mul (by norm_num) lp.ne']
      apply Real.log_le_log (by positivity); linarith
    have upperI : 1+truncated criticalWeight (1/n) ≤ 3*Real.log (L n) := by
      linarith [abs_nonneg c,neg_abs_le c,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have lowerI : Real.log (L n) ≤ 2*truncated criticalWeight (1/n) := by
      linarith [le_abs_self c]
    obtain ⟨σ,he⟩ := gridWeightedMin_attained criticalWeight hn0
    have g := (AngularLower.grid_lower critical_admissible hn σ).2
    rw [he] at g
    change truncated criticalWeight (1/n) ≤ 24*L n*gridWeightedMin criticalWeight n at g
    have cmp := (gridWeightedMin_le_joint criticalWeight hn0).trans (upper n hn)
    have non : 0 ≤ Real.log (L n)/L n := div_nonneg (Real.log_nonneg hl) lp.le
    have inflo : Real.log (L n)/L n ≤ 48*gridWeightedMin criticalWeight n := by
      apply (div_le_iff₀ lp).2; linarith
    refine ⟨inflo,?_,by linarith [non.trans inflo],non⟩
    calc
      _ ≤ C*(1+truncated criticalWeight (1/n))/L n := cmp
      _ ≤ C*(3*Real.log (L n))/L n := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left upperI hC) lp.le
      _ = _ := by ring
  constructor
  · apply isBigO_iff.mpr
    refine ⟨3*C,?_⟩
    filter_upwards [ev] with n h
    change ‖gridWeightedMin criticalWeight n‖ ≤ 3*C*‖Real.log (L n)/L n‖
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.2.2.1,abs_of_nonneg h.2.2.2] using h.2.1
  · apply isBigO_iff.mpr
    refine ⟨48,?_⟩
    filter_upwards [ev] with n h
    change ‖Real.log (L n)/L n‖ ≤ 48*‖gridWeightedMin criticalWeight n‖
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.2.2.1,abs_of_nonneg h.2.2.2] using h.1

end
end PermutationStrips.Angular
