import Mathlib

/-! A deterministic subdivision budget. The reciprocal of the area pays for each
chosen subdivision; the final step has a separate bound on its cost. -/

namespace PermutationStrips.Iteration

theorem reach {S : Type*} (area logSize : S → ℝ) (start : S) (hstart : logSize start = 0)
    {C : ℝ} (hC : 0 < C)
    (step : ∀ s, 0 < area s → ∃ s' d, 1 ≤ d ∧ d*area s ≤ C ∧
        logSize s' ≤ logSize s+d ∧ (area s)^2*d ≤ C*(area s-area s'))
    {k : ℝ} (hk : 0 < k) :
    ∃ s, area s ≤ 1/k ∧ logSize s ≤ 2*C*k := by
  by_contra! no
  have threshold : ∀ s, logSize s ≤ 2*C*k → 1/k < area s := by
    intro s hs
    by_contra! h
    exact (no s h).not_ge hs
  have recur : ∀ m : ℕ, ∃ s, 1/k < area s ∧ logSize s ≤ C/(area s) ∧
      (m:ℝ)/C ≤ 1/(area s) := by
    intro m
    induction m with
    | zero =>
      have ha := threshold start (by rw [hstart]; positivity)
      have hp := (one_div_pos.mpr hk).trans ha
      exact ⟨start, ha, by rw [hstart]; positivity, by simp [hp.le]⟩
    | succ m ih =>
      obtain ⟨s,ha,hl,hm⟩ := ih
      have hp := (one_div_pos.mpr hk).trans ha
      have small : 1/(area s) ≤ k := (div_le_iff₀ hp).mpr (by
        have h := (div_lt_iff₀ hk).mp ha; nlinarith)
      obtain ⟨s',d,hd,hcost,hs',hg⟩ := step s hp
      have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
      have old : C/(area s) ≤ C*k := by
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left small hC.le
      have dcost := (le_div_iff₀ hp).mpr hcost
      have ha' := threshold s' (by linarith)
      have hp' := (one_div_pos.mpr hk).trans ha'
      have mono : area s' ≤ area s := by
        by_contra! hn
        have := mul_neg_of_pos_of_neg hC (sub_neg.mpr hn)
        linarith [mul_nonneg (sq_nonneg (area s)) hd0.le]
      have q : d ≤ C/(area s') - C/(area s) := by
        rw [div_sub_div _ _ hp'.ne' hp.ne', le_div_iff₀ (mul_pos hp' hp)]
        nlinarith [mul_nonneg (mul_nonneg hd0.le hp.le) (sub_nonneg.mpr mono)]
      refine ⟨s',ha',by linarith,?_⟩
      have hh := (div_le_div_iff_of_pos_right hC).mpr (show 1 ≤ C/area s' - C/area s by linarith)
      have ident : (C/area s' - C/area s)/C = 1/area s' - 1/area s := by
        field_simp
      rw [ident] at hh
      push_cast
      rw [add_div]
      linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (C*k)
  obtain ⟨s,ha,_,hb⟩ := recur m
  have hp := (one_div_pos.mpr hk).trans ha
  have h₁ := (div_lt_iff₀ hk).mp ha
  have h₂ : 1/area s < k := (div_lt_iff₀ hp).mpr (by nlinarith)
  have h₃ := (div_lt_iff₀ hC).mp (hb.trans_lt h₂)
  nlinarith

end PermutationStrips.Iteration
