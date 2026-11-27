import Mathlib

/-! The reciprocal iteration and the critical angular integral. -/

open Set MeasureTheory

namespace PermutationStrips.Profile

/-- A quadratic saving at every step gives a reciprocal bound at every finite time. -/
theorem quadratic_saving {x : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hx : ∀ i, 0 < x i) (k : ℕ) (hs : ∀ i < k, c * (x i)^2 ≤ x i - x (i+1)) :
    (x 0)⁻¹ + k*c ≤ (x k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
    have last := hs k (Nat.lt_succ_self _)
    have hm : x (k+1) ≤ x k := by nlinarith [last, mul_nonneg hc (sq_nonneg (x k))]
    have hstep : c ≤ (x (k+1))⁻¹ - (x k)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ (hx _).ne' (hx _).ne',
        le_div_iff₀ (mul_pos (hx _) (hx _))]
      nlinarith [last, mul_nonneg (mul_nonneg hc (hx k).le) (sub_nonneg.mpr hm)]
    push_cast
    linarith

/-- The exact truncated integral for the weight `1/(1+log(1/r))`. -/
theorem critical_integral {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1/2) :
    (∫ r in δ..(1/2:ℝ), 1 / (r * (1 + Real.log (1/r)))) =
    Real.log (1 + Real.log (1/δ)) - Real.log (1 + Real.log 2) := by
  have bounds {r : ℝ} (hr : r ∈ uIcc δ (1/2:ℝ)) : 0 < r ∧ r ≤ 1 := by
    rw [uIcc_of_le hhalf] at hr
    exact ⟨hδ.trans_le hr.1, hr.2.trans (by norm_num)⟩
  have deriv {r : ℝ} (hr : r ∈ uIcc δ (1/2:ℝ)) :
      HasDerivAt (fun x => -Real.log (1 - Real.log x)) (1 / (r * (1+Real.log (1/r)))) r := by
    obtain ⟨hp, hle⟩ := bounds hr
    have hd : 0 < 1 - Real.log r := by linarith [Real.log_nonpos hp.le hle]
    have h := (((Real.hasDerivAt_log hp.ne').const_sub 1).log hd.ne').neg
    convert h using 1
    rw [one_div r, Real.log_inv, ← sub_eq_add_neg]
    field_simp [hd.ne', hp.ne']
  have hi : IntervalIntegrable (fun r : ℝ => 1 / (r * (1+Real.log (1/r)))) volume δ (1/2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div
    · apply continuousOn_id.mul
      apply continuousOn_const.add
      apply Real.continuousOn_log.comp (continuousOn_const.div continuousOn_id (fun r hr => (bounds hr).1.ne'))
      intro r hr
      exact (one_div_pos.mpr (bounds hr).1).ne'
    · intro r hr
      obtain ⟨hp, hle⟩ := bounds hr
      apply mul_ne_zero hp.ne'
      have h := Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using hle))
      linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun _ hr => deriv hr) hi]
  simp only [one_div, Real.log_inv, ← sub_eq_add_neg]
  norm_num [Real.log_div]; ring

end PermutationStrips.Profile
