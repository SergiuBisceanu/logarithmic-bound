import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Exponential moments for a path of shrinking sections

At an active stage the squared-length saving compensates for increasing the
exponent. A secant inequality converts the saving for length into a saving for
its exponential. Greedy selection then multiplies the resulting moment bounds.
-/

open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

def moment (m : ℕ) (x : ℝ) : ℝ := Real.exp ((m:ℝ)*x/256)
def momentSlope (m : ℕ) (x : ℝ) : ℝ := (moment m x-1)/x
def momentThreshold (m : ℕ) : ℝ := Real.log 2/(m:ℝ)

theorem momentSlope_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ momentSlope m x :=
  div_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity : 0 ≤ (m:ℝ)*x/256))) hx

theorem moment_secant (m : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    moment m y ≤ moment m x - momentSlope m x*(x-y) := by
  rcases eq_or_lt_of_le hx with h|hp
  · have hy' : y=0 := by linarith
    simp [← h,hy',moment,momentSlope]
  let u := y/x
  have u₀ : 0 ≤ u := div_nonneg hy hp.le
  have u₁ : u ≤ 1 := (div_le_one hp).2 hyx
  calc
    moment m y = Real.exp ((1-u)*0+u*((m:ℝ)*x/256)) := by
      unfold moment u; congr 1; field_simp; ring
    _ ≤ (1-u)*Real.exp 0 + u*Real.exp ((m:ℝ)*x/256) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr u₁) u₀ (by ring)
    _ = _ := by simp only [Real.exp_zero,mul_one,momentSlope,moment,u]; field_simp; ring

theorem momentThreshold_bounds (m : ℕ) (hm : 0<m) : momentThreshold m ∈ Set.Icc (0:ℝ) 1 := by
  have mp : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  exact ⟨div_nonneg (Real.log_nonneg (by norm_num)) (by positivity),
    (div_le_one (by linarith)).2 (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)])⟩

private theorem moment_crossing (m : ℕ) (hm : 0<m) (x : ℝ) :
    0 ≤ (x-256*momentThreshold m)*(moment m x-2) := by
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have mono : Monotone (moment m) := fun _ _ h => Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h mp.le) (by norm_num))
  have atThreshold : moment m (256*momentThreshold m) = 2 := by
    rw [moment,momentThreshold,show (m:ℝ)*(256*(Real.log 2/m))/256 = Real.log 2 by field_simp,
      Real.exp_log (by norm_num : (0:ℝ)<2)]
  rcases le_total x (256*momentThreshold m) with h|h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr ((mono h).trans_eq atThreshold))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (atThreshold.symm.trans_le (mono h)))

/-- The envelope is affine in the old moment, with the fixed value two. -/
theorem moment_damped (m : ℕ) (hm : 0<m) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    moment (m+1) x - momentSlope (m+1) x*(x^2/128) ≤
      (1-momentThreshold m)*moment m x + 2*momentThreshold m := by
  let r := x/256
  have rp : 0 ≤ r := by dsimp [r]; linarith [hx.1]
  have r₁ : r ≤ 1 := by dsimp [r]; linarith [hx.2]
  have exp_step : (1-2*r)*Real.exp r ≤ 1-r := by
    have h := Real.add_one_le_exp (-r)
    rw [Real.exp_neg] at h
    have e : (1-r)*Real.exp r ≤ 1 := by
      calc
        _ ≤ (Real.exp r)⁻¹*Real.exp r := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = 1 := inv_mul_cancel₀ (Real.exp_pos _).ne'
    nlinarith only [mul_le_mul_of_nonneg_left e (sub_nonneg.mpr r₁),
      mul_nonneg (sq_nonneg r) (Real.exp_pos r).le]
  have mult : moment (m+1) x = moment m x*Real.exp r := by
    dsimp [moment,r]; rw [← Real.exp_add]; congr 1; push_cast; ring
  have cancel : momentSlope (m+1) x*(x^2/128) = (moment (m+1) x-1)*(x/128) := by
    by_cases hz : x=0
    · simp [hz,momentSlope]
    · unfold momentSlope; field_simp
  rw [cancel,mult]
  have h := mul_le_mul_of_nonneg_right exp_step (Real.exp_pos ((m:ℝ)*x/256)).le
  change (1-2*r)*Real.exp r * moment m x ≤ (1-r)*moment m x at h
  dsimp [r] at h ⊢
  linarith only [h,moment_crossing m hm x]

theorem moment_one_le_two {x : ℝ} (hx : x ≤ 1) : moment 1 x ≤ 2 := by
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  unfold moment
  rw [← Real.exp_log (by norm_num : (0:ℝ)<2), Real.exp_le_exp]
  norm_num at hl ⊢; linarith

/-- Exponential weights extract a finite ensemble from a uniform bound on the
weighted moments. After M rounds every coordinate costs at most log J + M log 2. -/
theorem exists_sample_moment {J X : Type*} [Fintype J] [Nonempty J] (z : X → J → ℝ)
    (hw : ∀ a : J → ℝ, (∀ j, 0≤a j) → ∃ p, ∑ j, a j*Real.exp (z p j) ≤ 2*∑ j, a j)
    (M : ℕ) : ∃ s : Fin M → X, ∀ j, ∑ i, z (s i) j ≤ Real.log (Fintype.card J)+(M:ℝ)*Real.log 2 := by
  classical
  let N : ℝ := Fintype.card J
  have np : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have potential (m : ℕ) : ∃ s : Fin m → X, (∑ j, Real.exp (∑ i, z (s i) j)) ≤ N*2^m := by
    induction m with
    | zero => exact ⟨Fin.elim0,by simp [N]⟩
    | succ m ih =>
      obtain ⟨s,hs⟩ := ih
      let a (j : J) := Real.exp (∑ i, z (s i) j)
      obtain ⟨p,hp⟩ := hw a (fun j => (Real.exp_pos _).le)
      refine ⟨Fin.cons p s,?_⟩
      simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Real.exp_add,pow_succ]
      change (∑ j, Real.exp (z p j)*a j) ≤ _
      simp_rw [mul_comm (Real.exp (z p _)) (a _)]
      change (∑ j, a j) ≤ _ at hs
      linarith
  obtain ⟨s,hs⟩ := potential M
  refine ⟨s,fun j => ?_⟩
  have hb := (Finset.single_le_sum (fun j _ => (Real.exp_pos (∑ i, z (s i) j)).le)
    (Finset.mem_univ j)).trans hs
  have h := Real.log_le_log (Real.exp_pos _) hb
  simpa only [Real.log_exp,Real.log_mul np.ne' (by positivity : (2:ℝ)^M ≠ 0),Real.log_pow] using h

end
end PermutationStrips.AngularBlock
