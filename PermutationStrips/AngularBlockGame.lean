import Mathlib.Tactic

/-! Equal-weight simultaneous approximation of a one-sided finite family of tests.
The greedy choice uses the positive part of the accumulated excess as the next test. -/

open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

private theorem square_step (x d : ℝ) (hd : |d| ≤ 1) :
    (max 0 (x+d))^2 ≤ (max 0 x)^2 + 2*(max 0 x)*d + 1 := by
  have he := abs_le.mp hd
  have hds : d^2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-d) (by linarith : 0 ≤ 1+d)]
  rcases le_total 0 x with hx|hx
  · rw [max_eq_right hx]
    rcases le_total 0 (x+d) with hy|hy
    · rw [max_eq_right hy]; nlinarith
    · rw [max_eq_left hy]; nlinarith [sq_nonneg (x+d)]
  · rw [max_eq_left hx]
    rcases le_total 0 (x+d) with hy|hy
    · rw [max_eq_right hy]
      nlinarith [mul_nonneg hy (by linarith : 0 ≤ -x)]
    · rw [max_eq_left hy]; norm_num

/-- A support-function estimate against every nonnegative test gives an actual equal-weight
sample. Every coordinate of the summed excess is at most sqrt(M · card J). -/
theorem exists_sample {J X : Type*} [Fintype J] (e : X → J → ℝ)
    (he : ∀ x j, |e x j| ≤ 1)
    (hw : ∀ a : J → ℝ, (∀ j, 0 ≤ a j) → ∃ x, ∑ j, a j*e x j ≤ 0)
    (M : ℕ) : ∃ s : Fin M → X,
      ∀ j, ∑ i, e (s i) j ≤ Real.sqrt ((M:ℝ)*Fintype.card J) := by
  classical
  have potential (m : ℕ) : ∃ s : Fin m → X,
      ∑ j, (max 0 (∑ i, e (s i) j))^2 ≤ (m:ℝ)*Fintype.card J := by
    induction m with
    | zero => exact ⟨Fin.elim0,by simp⟩
    | succ m ih =>
      obtain ⟨s,hs⟩ := ih
      let v := fun j => ∑ i, e (s i) j
      obtain ⟨x,hx⟩ := hw (fun j => max 0 (v j)) (fun j => le_max_left _ _)
      refine ⟨Fin.cons x s,?_⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      change ∑ j, (max 0 (e x j + v j))^2 ≤ _
      calc
        _ ≤ ∑ j, ((max 0 (v j))^2 + 2*(max 0 (v j)*e x j) + 1) := by
          apply Finset.sum_le_sum; intro j _
          simpa only [add_comm (e x j),mul_assoc] using square_step (v j) (e x j) (he x j)
        _ ≤ _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
            nsmul_eq_mul,mul_one,Nat.cast_succ]
          change ∑ j, (max 0 (v j))^2 ≤ _ at hs
          linarith
  obtain ⟨s,hs⟩ := potential M
  refine ⟨s,fun j => (le_max_right 0 _).trans ?_⟩
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun p _ => sq_nonneg (max 0 (∑ i, e (s i) p)))
    (Finset.mem_univ j)).trans hs

end
end PermutationStrips.AngularBlock
