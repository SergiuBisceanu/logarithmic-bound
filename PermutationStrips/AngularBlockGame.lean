import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Equal-weight simultaneous approximation of a one-sided finite family of tests.
Exponential weights give a logarithmic dependence on the number of coordinates.
The squared positive-part potential gives a second, elementary estimate. -/

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

private theorem exp_increment {η d : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hd : |d| ≤ 1) :
    Real.exp (η*d) ≤ 1+η*d+η^2 := by
  have h : |η*d| ≤ η := by
    rw [abs_mul,abs_of_nonneg hη]
    simpa using mul_le_mul_of_nonneg_left hd hη
  have ht := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (h.trans hη1))).2
  have hs := pow_le_pow_left₀ (abs_nonneg (η*d)) h 2
  rw [sq_abs] at hs
  linarith

/-- An affine upper bound for the exponential increment turns a one-round
weighted comparison into a bound on every coordinate after `M` rounds. -/
private theorem sample_of_affine_exp {J X : Type*} [Fintype J] [Nonempty J] (x : X → J → ℝ)
    {η offset slope μ : ℝ} (hη : 0 < η) (h₀ : 0 ≤ offset) (h₁ : 0 ≤ slope) (hμ : 0 ≤ μ)
    (step : ∀ p j, Real.exp (η*x p j) ≤ 1+offset+slope*x p j)
    (choose : ∀ a : J → ℝ, (∀ j, 0 ≤ a j) → ∃ p, ∑ j, a j*x p j ≤ μ*∑ j, a j)
    (M : ℕ) : ∃ s : Fin M → X, ∀ j, ∑ i, x (s i) j ≤
      (Real.log (Fintype.card J)+(M:ℝ)*(offset+slope*μ))/η := by
  classical
  let N : ℝ := Fintype.card J
  let growth := offset+slope*μ
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hg : 0 ≤ growth := add_nonneg h₀ (mul_nonneg h₁ hμ)
  have potential (m : ℕ) : ∃ s : Fin m → X,
      (∑ j, Real.exp (η*∑ i, x (s i) j)) ≤ N*Real.exp ((m:ℝ)*growth) := by
    induction m with
    | zero => exact ⟨Fin.elim0,by simp [N]⟩
    | succ m ih =>
      obtain ⟨s,hs⟩ := ih
      let a (j : J) := Real.exp (η*∑ i, x (s i) j)
      have ha (j : J) : 0 ≤ a j := (Real.exp_pos _).le
      obtain ⟨p,hp⟩ := choose a ha
      refine ⟨Fin.cons p s,?_⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have pt (j : J) : Real.exp (η*(x p j + ∑ i, x (s i) j)) ≤
          a j*(1+offset) + slope*(a j*x p j) := by
        rw [mul_add,Real.exp_add,mul_comm]
        change a j*Real.exp (η*x p j) ≤ _
        linarith only [mul_le_mul_of_nonneg_left (step p j) (ha j)]
      change (∑ j, a j) ≤ _ at hs
      calc
        _ ≤ ∑ j, (a j*(1+offset) + slope*(a j*x p j)) := Finset.sum_le_sum fun j _ => pt j
        _ ≤ (∑ j, a j)*(1+growth) := by
          rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
          dsimp [growth]; linarith only [mul_le_mul_of_nonneg_left hp h₁]
        _ ≤ (N*Real.exp ((m:ℝ)*growth))*Real.exp growth :=
          mul_le_mul hs (by simpa only [add_comm] using Real.add_one_le_exp growth) (by positivity) (by positivity)
        _ = N*Real.exp ((↑(m+1):ℝ)*growth) := by
          rw [mul_assoc,← Real.exp_add]; congr 2; push_cast; ring
  obtain ⟨s,hs⟩ := potential M
  refine ⟨s,fun j => ?_⟩
  have bound := (Finset.single_le_sum (fun j _ => (Real.exp_pos (η*∑ i, x (s i) j)).le)
    (Finset.mem_univ j)).trans hs
  have h := Real.log_le_log (Real.exp_pos _) bound
  rw [Real.log_exp,Real.log_mul hN.ne' (Real.exp_pos _).ne',Real.log_exp] at h
  exact (le_div_iff₀ hη).2 (by linarith only [h])

/-- Greedy selection with the exponential of each coordinate's accumulated excess as
its next weight. The coordinate bound grows logarithmically in the number of tests. -/
theorem exists_sample_exp {J X : Type*} [Fintype J] [Nonempty J] (e : X → J → ℝ)
    (he : ∀ x j, |e x j| ≤ 1)
    (hw : ∀ a : J → ℝ, (∀ j, 0 ≤ a j) → ∃ x, ∑ j, a j*e x j ≤ 0)
    (M : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ s : Fin M → X, ∀ j, ∑ i, e (s i) j ≤ Real.log (Fintype.card J)/η + (M:ℝ)*η := by
  obtain ⟨s,hs⟩ := sample_of_affine_exp e hη (sq_nonneg η) hη.le (le_refl 0)
    (fun p j => by linarith only [exp_increment hη.le hη1 (he p j)])
    (fun a ha => by simpa using hw a ha) M
  refine ⟨s,fun j => (hs j).trans_eq ?_⟩
  simp only [mul_zero,add_zero]; field_simp

/-- At least `4 k² log |J|` rounds make the coordinatewise mean excess at most `1/k`
when the sample is nonempty. The cumulative form also covers the empty sample. -/
theorem exists_sample_of_log {J X : Type*} [Fintype J] [Nonempty J] (e : X → J → ℝ)
    (he : ∀ x j, |e x j| ≤ 1)
    (hw : ∀ a : J → ℝ, (∀ j, 0 ≤ a j) → ∃ x, ∑ j, a j*e x j ≤ 0)
    (k M : ℕ) (hk : 0 < k) (hM : 4*(k:ℝ)^2*Real.log (Fintype.card J) ≤ M) :
    ∃ s : Fin M → X, ∀ j, ∑ i, e (s i) j ≤ (M:ℝ)/k := by
  have hk' : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  let η := (2*(k:ℝ))⁻¹
  have hp : 0 < η := by dsimp [η]; positivity
  have h1 : η ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨s,hs⟩ := exists_sample_exp e he hw M hp h1
  refine ⟨s,fun j => (hs j).trans ?_⟩
  dsimp [η]
  rw [div_inv_eq_mul]
  have pos : 0 < (k:ℝ) := by positivity
  field_simp
  linarith only [hM]

/-- For costs in `[0,1]` the multiplicative slack is `1+η`. Choosing the
positive exponential weight at each coordinate lets one comparison control
all coordinates at once. -/
theorem exists_sample_nonneg_rate {J X : Type*} [Fintype J] [Nonempty J] (x : X → J → ℝ)
    (hx : ∀ p j, x p j ∈ Set.Icc 0 1) {μ : ℝ} (hμ : 0 ≤ μ)
    (hw : ∀ a : J → ℝ, (∀ j, 0 ≤ a j) → ∃ p, ∑ j, a j*x p j ≤ μ*∑ j, a j)
    (M : ℕ) {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    ∃ s : Fin M → X, ∀ j, ∑ i, x (s i) j ≤
      Real.log (Fintype.card J)/η + (1+η)*(M:ℝ)*μ := by
  let q := η*(1+η)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have chord {z : ℝ} (hz : z ∈ Set.Icc 0 1) : Real.exp (η*z) ≤ 1+q*z := by
    have hp : 0 ≤ η*z := mul_nonneg hη.le hz.1
    have h1 : η*z ≤ 1 := (mul_le_of_le_one_right hη.le hz.2).trans hη1
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x:=η*z) (by simpa [abs_of_nonneg hp] using h1))).2
    dsimp [q]
    nlinarith only [h,mul_nonneg (sq_nonneg η) (mul_nonneg hz.1 (sub_nonneg.mpr hz.2))]
  obtain ⟨s,hs⟩ := sample_of_affine_exp x hη (le_refl 0) hq hμ
    (fun p j => by simpa only [add_zero] using chord (hx p j)) hw M
  refine ⟨s,fun j => (hs j).trans_eq ?_⟩
  dsimp [q]; field_simp; ring

end
end PermutationStrips.AngularBlock
