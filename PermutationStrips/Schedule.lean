import PermutationStrips.Profile

/-! Deterministic scale selection. Thresholds (i+1)/k replace a random threshold.
Only active stages spend logarithmic scale at radius r. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.Schedule

noncomputable section

/-- The stages active at weight z. -/
def active (k : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.range k).filter fun i => ((i+1:ℕ):ℝ) ≤ k*z

theorem active_eq {k : ℕ} {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
    active k z = Finset.range ⌊(k:ℝ)*z⌋₊ := by
  have hn : 0 ≤ (k:ℝ)*z := mul_nonneg (Nat.cast_nonneg _) hz.1
  have hk : ⌊(k:ℝ)*z⌋₊ ≤ k := by
    exact_mod_cast (Nat.floor_le hn).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hz.2)
  ext i
  simp only [active, Finset.mem_filter, Finset.mem_range, ← Nat.le_floor_iff hn]
  omega

/-- Exactly the active stages need a quadratic saving. A nonincreasing sequence of
mean section lengths then obeys the uniform bound in the block lemma. -/
theorem active_decay {k : ℕ} (hk : 0 < k) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) (hone : x 0 = 1) (hm : Antitone x)
    (hs : ∀ i ∈ active k z, (x i)^2/128 ≤ x i - x (i+1)) :
    z*x k ≤ 128/(k:ℝ) := by
  let m := ⌊(k:ℝ)*z⌋₊
  have hn : 0 ≤ (k:ℝ)*z := mul_nonneg (Nat.cast_nonneg _) hz.1
  have hmle : m ≤ k := by
    exact_mod_cast (Nat.floor_le hn).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hz.2)
  have hcount : (k:ℝ)*z < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have h := Profile.quadratic_saving (c := 1/128) (by norm_num) hpos m (by
    intro i hi
    have ha : i ∈ active k z := by rw [active_eq hz]; exact Finset.mem_range.mpr hi
    linarith [hs i ha])
  rw [hone, inv_one, ← one_div, le_div_iff₀ (hpos m)] at h
  apply (le_div_iff₀ (by exact_mod_cast hk : (0:ℝ) < k)).mpr
  have bound := mul_le_mul (le_of_lt hcount) (hm hmle) (hpos k).le
    (show (0:ℝ) ≤ (m:ℝ)+1 by positivity)
  nlinarith [hpos m]

/-- Integrand for the logarithmic cost of stage i. -/
def density (k i : ℕ) (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  if ((i+1:ℕ):ℝ) ≤ k*w r then 1/r else 0

def cost (k i : ℕ) (w : ℝ → ℝ) : ℝ :=
  ∫ r in Ioc (0:ℝ) (1/2), density k i w r

private theorem density_le {k i : ℕ} {w : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hw : 0 ≤ w r) :
    0 ≤ density k i w r ∧ density k i w r ≤ (k:ℝ) * (w r/r) := by
  rw [← mul_div_assoc]
  unfold density
  split_ifs with h
  · exact ⟨by positivity, (div_le_div_iff_of_pos_right hr).mpr (by push_cast at h; linarith)⟩
  · exact ⟨le_rfl, by positivity⟩

private theorem integrable_density {k i : ℕ} {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), 0 ≤ w r)
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2))) :
    IntegrableOn (density k i w) (Ioc (0:ℝ) (1/2)) := by
  apply (hi.const_mul (k:ℝ)).mono'
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_le measurable_const (measurable_const.mul hm))
      (measurable_const.div measurable_id) measurable_const
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr
    obtain ⟨hp,hl⟩ := density_le (i := i) (k := k) hr.1 (hw r hr)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Pi.mul_apply] using hl

/-- Summing the scale costs over all k stages costs at most k times the weight integral. -/
theorem total_cost {k : ℕ} {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2))) :
    ∑ i ∈ Finset.range k, cost k i w ≤ (k:ℝ) * ∫ r in Ioc (0:ℝ) (1/2), w r/r := by
  have hint (i : ℕ) := integrable_density (i := i) (k := k) hm (fun r hr => (hw r hr).1) hi
  unfold cost
  rw [← integral_finset_sum _ (fun i _ => hint i), ← integral_const_mul]
  apply setIntegral_mono_on (integrable_finset_sum _ (fun i _ => hint i)) (hi.const_mul _) measurableSet_Ioc
  intro r hr
  have eq : (∑ i ∈ Finset.range k, density k i w r) = ((active k (w r)).card : ℝ) * (1/r) := by
    unfold density active
    rw [← Finset.sum_filter]
    simp
  rw [eq, active_eq (hw r hr), Finset.card_range]
  have hl := Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) (hw r hr).1)
  calc
    _ ≤ ((k:ℝ)*w r) * (1/r) := mul_le_mul_of_nonneg_right hl (one_div_nonneg.mpr hr.1.le)
    _ = _ := by ring

/-- At an active radius, the shell starts beyond 8/r, as needed for a complete sweep. -/
theorem active_scale {k i : ℕ} {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), 0 ≤ w r) (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    {r : ℝ} (hr : r ∈ Ioc (0:ℝ) (1/2)) (ha : i ∈ active k (w r)) :
    8 ≤ (16 * Real.exp (cost k i w))*r := by
  have hsub : Ioc r (1/2:ℝ) ⊆ Ioc 0 (1/2:ℝ) := fun _ ⟨h,h'⟩ => ⟨hr.1.trans h,h'⟩
  have hl : Real.log ((1/2)/r) ≤ cost k i w := by
    rw [← integral_one_div_of_pos hr.1 (by norm_num : (0:ℝ) < 1/2),
      intervalIntegral.integral_of_le hr.2]
    calc
      _ = ∫ s in Ioc r (1/2:ℝ), density k i w s := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        have act := (Finset.mem_filter.mp ha).2.trans
          (mul_le_mul_of_nonneg_left (hmono hr (hsub hs) hs.1.le) (Nat.cast_nonneg k))
        exact (if_pos act).symm
      _ ≤ _ := setIntegral_mono_set (integrable_density hm hw hi)
        (by filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with s hs
            exact (density_le hs.1 (hw s hs)).1) (ae_of_all _ (fun _ h => hsub h))
  have hexp := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (by have := hr.1; positivity)] at hexp
  have := (div_le_iff₀ hr.1).mp hexp
  linarith

end
end PermutationStrips.Schedule
