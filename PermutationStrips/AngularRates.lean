import PermutationStrips.AngularLimit
import PermutationStrips.AngularLower

/-! Passage from one sequence of finite blocks to every positive observation scale. -/

open Set MeasureTheory Filter
open scoped Topology
namespace PermutationStrips.Angular
open CompactPlane
noncomputable section

/-- A common absolute constant. No sharp upper coefficient is asserted. -/
def upperConstant : ℝ := 200000000

theorem upperConstant_ge_one : 1 ≤ upperConstant := by norm_num [upperConstant]

theorem dyadic_error_tendsto : Tendsto (fun j : ℕ => 1000/(2:ℝ)^(j+1)) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)
  exact tendsto_const_nhds.div_atTop (ht.comp (tendsto_add_atTop_nat 1))

theorem limit_oblique {b : ℝ → ℝ} {B : ℕ → FinitePattern} (hB : BlocksFor b B)
    {θ : ℝ} (hθ : 0 < rho θ) : length (limitSet B) θ = 0 := by
  have stage (j : ℕ) :
      Real.sqrt (rho θ)*length (limitSet B) θ ≤ 1000/(2:ℝ)^(j+1) := by
    have hi : length (limitSet B) θ ≤ length (B j).pat.carrier θ :=
      (length_mono (compact_carrier _) (limitSet_subset_level B (j+1)) θ).trans
        (length_insert_le_inner (level B j).pat (B j).pat θ)
    exact (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)).trans (hB.sqrt_bound j θ hθ)
  have hz := ge_of_tendsto' dyadic_error_tendsto stage
  exact le_antisymm (nonpos_of_mul_nonpos_right hz (Real.sqrt_pos.2 hθ)) measureReal_nonneg

theorem limit_upper {b : ℝ → ℝ} (hb : Admissible b) {B : ℕ → FinitePattern} (hB : BlocksFor b B)
    {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/2) :
    let K := thick δ (limitSet B)
    let L := Real.log (1/δ)
    favard K ≤ upperConstant/L ∧ weighted b K ≤ upperConstant*(1+truncated b δ)/L := by
  let S := limitSet B
  let L := Real.log (1/δ)
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hd).mpr (by linarith))
  let a := 1+truncated b δ
  have hA : 1 ≤ a := le_add_of_nonneg_right (truncated_nonneg hb hd hh)
  have hA0 : 0 ≤ a := zero_le_one.trans hA
  have coarse := coarse_bounds hb (compact_limitSet B) (limit_subset_unit B) (hh.trans (by norm_num))
  have coarseF : favard (thick δ S) ≤ 32 := coarse.1.trans (by linarith [Real.pi_lt_four])
  have coarseM : weighted b (thick δ S) ≤ 32 := coarse.2.trans (by norm_num)
  have F := all_scales_upper (B := 32) (D := 16000) (C := 2000) (a := 1)
    (by norm_num) (by norm_num) le_rfl hd hh coarseF (by
      intro j; dsimp only; intro _
      have hl := (limit_scale B hb (C := 1000) (by norm_num) hB.count j hd.le).1
      have he : 0 ≤ δ * Real.exp (2000*(2:ℝ)^(j+1)) := by positivity
      have hcost : Real.pi*(4*δ*Real.exp (2*1000*(2:ℝ)^(j+1))) ≤
          16000*(δ*Real.exp (2000*(2:ℝ)^(j+1))) := by
        norm_num only [show (2:ℝ)*1000=2000 by norm_num]
        nlinarith only [mul_nonneg (show 0 ≤ 16000-4*Real.pi by linarith [Real.pi_lt_four]) he]
      simpa only [mul_one] using hl.trans (add_le_add (hB.favard_bound j) hcost))
  have M := all_scales_upper (B := 32) (D := 16000) (C := 2000) (a := a)
    (by norm_num) (by norm_num) hA hd hh coarseM (by
      intro j; dsimp only; intro hcut
      let k : ℕ := 2^(j+1)
      have hk : 2 ≤ k := by dsimp [k]; rw [pow_succ]; have := Nat.one_le_two_pow (n := j); omega
      have hkcast : (k:ℝ)=(2:ℝ)^(j+1) := by norm_cast
      have hf : scaleFactor b k ≤ a := by
        unfold scaleFactor
        exact add_le_add_left (truncated_mono_cutoff hb hd (by simpa [hkcast] using hcut) (cutoff_le_half hk)) _
      have hi := hB.weighted_bound j
      have hl := (limit_scale B hb (C := 1000) (by norm_num) hB.count j hd.le).2
      apply hl.trans
      apply add_le_add
      · apply hi.trans
        apply div_le_div_of_nonneg_right _ (by positivity)
        change 1000*scaleFactor b k ≤ 16000*a
        linarith
      · norm_num only [show (2:ℝ)*1000=2000 by norm_num]
        have he : 0 ≤ δ*Real.exp (2000*(2:ℝ)^(j+1)) := by positivity
        linarith only [show 4*δ*Real.exp (2000*(2:ℝ)^(j+1)) = 4*(δ*Real.exp (2000*(2:ℝ)^(j+1))) by ring,he])
  constructor
  · exact F.trans (div_le_div_of_nonneg_right (by norm_num [upperConstant]) hL.le)
  · exact M.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num [upperConstant]) hA0) hL.le)

end
end PermutationStrips.Angular
