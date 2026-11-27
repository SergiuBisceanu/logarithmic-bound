import Mathlib

/-! A shell with enough squared section length to pay for a subdivision.
The radius at level j is (1/2)4⁻ʲ; its square root makes the cost summable. -/

open MeasureTheory Set
open scoped BigOperators

namespace PermutationStrips.AreaShell

noncomputable def radius (j : ℕ) : ℝ := (1/2)*(1/4)^j

theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

theorem radius_le_half (j : ℕ) : radius j ≤ 1/2 := by
  unfold radius
  have h := pow_le_one₀ (show (0:ℝ) ≤ 1/4 by norm_num) (by norm_num : (1/4:ℝ) ≤ 1) (n := j)
  linarith

theorem radius_succ (j : ℕ) : radius (j+1) = radius j / 4 := by unfold radius; rw [pow_succ]; ring

private theorem sum_weights (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j:ℝ)+1)*(1/2)^j = 4-2*(n+2)*(1/2)^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; push_cast; ring

/-- One dyadic shell in the lower half contains a definite amount of section mass. -/
theorem exists_shell_mass {f : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hi : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, IntervalIntegrable f volume a b)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ 1)
    (hhalf : A ≤ 2 * ∫ t in (0:ℝ)..(1/2), f t) :
    ∃ j : ℕ, A/16*((j:ℝ)+1)*(1/2)^j ≤ ∫ t in radius (j+1)..radius j, f t := by
  have hr (j : ℕ) : radius j ∈ Icc (0:ℝ) 1 :=
    ⟨(radius_pos j).le, (radius_le_half j).trans (by norm_num)⟩
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (show 0 < A/4 by positivity) (by norm_num : (1/4:ℝ) < 1)
  have hend : radius n < A/8 := by unfold radius; linarith
  have left : (∫ t in (0:ℝ)..radius n, f t) ≤ radius n := by
    calc
      _ ≤ ∫ _ in (0:ℝ)..radius n, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on (radius_pos n).le (hi 0 (by norm_num) _ (hr n)) intervalIntegrable_const
        intro t ht; exact hb t ⟨ht.1,ht.2.trans (hr n).2⟩
      _ = _ := by simp
  have telescope : (∑ j ∈ Finset.range n, ∫ t in radius (j+1)..radius j, f t) =
      ∫ t in radius n..(1/2), f t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := radius) (n := n)
      (fun j _ => hi _ (hr j) _ (hr (j+1)))
    calc
      _ = -(∑ j ∈ Finset.range n, ∫ t in radius j..radius (j+1), f t) := by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl
        intro j _; exact intervalIntegral.integral_symm ..
      _ = _ := by rw [h, ← intervalIntegral.integral_symm]; simp [radius]
  by_contra! h
  have sum_bound : (∑ j ∈ Finset.range n, ∫ t in radius (j+1)..radius j, f t) ≤ A/4 := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, A/16*(((j:ℝ)+1)*(1/2)^j) := by
        exact Finset.sum_le_sum fun j _ => by simpa [mul_assoc] using (h j).le
      _ = (A/16) * (4-2*(n+2)*(1/2)^n) := by rw [← Finset.mul_sum, sum_weights]
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ A/16 by positivity)
                                 (show (0:ℝ) ≤ 2*(n+2)*(1/2)^n by positivity)]
  rw [telescope] at sum_bound
  have add := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (by norm_num) _ (hr n)) (hi _ (hr n) _ (by norm_num : (1/2:ℝ) ∈ Icc 0 1))
  linarith

/-- From the mass on a shell to its quadratic gain. Pointwise positivity of (f−v)²
is the interval form of Cauchy–Schwarz used here. -/
theorem shell_energy {f : ℝ → ℝ} {A : ℝ} (hA : 0 < A) {j : ℕ}
    (hi : IntervalIntegrable f volume (radius (j+1)) (radius j))
    (hi2 : IntervalIntegrable (fun t => (f t)^2) volume (radius (j+1)) (radius j))
    (hm : A/16*((j:ℝ)+1)*(1/2)^j ≤ ∫ t in radius (j+1)..radius j, f t) :
    (A/16*((j:ℝ)+1))^2 ≤ ∫ t in radius (j+1)..radius j, (f t)^2 := by
  let b := (1/2:ℝ)^j
  let s := A/16*((j:ℝ)+1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  let v := s/b
  have hv : 0 < v := div_pos hs hb
  have hvb : v*b = s := div_mul_cancel₀ s hb.ne'
  have order : radius (j+1) ≤ radius j := by rw [radius_succ]; linarith [radius_pos j]
  have width : radius j - radius (j+1) ≤ b^2 := by
    rw [radius_succ]; dsimp [radius,b]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
    linarith [show (0:ℝ) ≤ (1/4)^j by positivity]
  have tangent : (∫ t in radius (j+1)..radius j, (2*v*f t - v^2)) ≤
      ∫ t in radius (j+1)..radius j, (f t)^2 := by
    apply intervalIntegral.integral_mono_on order ((hi.const_mul _).sub intervalIntegrable_const) hi2
    intro t _; nlinarith [sq_nonneg (f t-v)]
  rw [intervalIntegral.integral_sub (hi.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at tangent
  have hmass : s*b ≤ ∫ t in radius (j+1)..radius j, f t := hm
  have hmul := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2*v by positivity)
  have hlen := mul_le_mul_of_nonneg_right width (sq_nonneg v)
  have e₁ : 2*v*(s*b) = 2*s^2 := by rw [show 2*v*(s*b) = 2*(v*b)*s by ring, hvb]; ring
  have e₂ : b^2*v^2 = s^2 := by rw [← mul_pow, mul_comm b v, hvb]
  change s^2 ≤ _
  linarith

end PermutationStrips.AreaShell
