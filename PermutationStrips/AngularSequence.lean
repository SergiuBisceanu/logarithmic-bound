import PermutationStrips.AngularFiniteBlock
import PermutationStrips.AngularLimit

/-! Choosing one sequence of genuine blocks for an arbitrary angular profile. -/

open Set MeasureTheory
namespace PermutationStrips.Angular
open CompactPlane
noncomputable section

/-- A profile can be truncated separately at each scale. The square-root control on
the same block simultaneously gives the absolute Favard estimate. -/
theorem exists_profile_block {b : ℝ → ℝ} (hb : Admissible b) {k : ℕ} (hk : 2≤k) :
    ∃ Q : FinitePattern,
      (Fintype.card Q.index : ℝ) ≤ Real.exp (1000*k) ∧
      Metric.diam (toEuclidean '' Q.pat.carrier) ≤ 1+1000/k ∧
      (∀ i, Q.pat.w i ≤ 1/2) ∧ LocalGeometry Q.pat ∧
      favard Q.pat.carrier ≤ 16000/k ∧
      weighted b Q.pat.carrier ≤ 1000*scaleFactor b k/k ∧
      ∀ θ, 0 < rho θ → Real.sqrt (rho θ)*length Q.pat.carrier θ ≤ 1000/k := by
  obtain ⟨w,hm,hw,hmono,hi,hI,hsqrt,hlo,hsmall⟩ := exists_scale_weight hb hk
  obtain ⟨Q,hcount,hd,hwid,hl,hprof⟩ := AngularBlock.exists_block hm hw hmono hi hI k hk
  have ks : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hA : 0≤scaleFactor b k := zero_le_one.trans (one_le_scaleFactor hb hk)
  have hs (θ : ℝ) (hθ : 0 < rho θ) : Real.sqrt (rho θ)*length Q.pat.carrier θ ≤ 1000/k :=
    (mul_le_mul_of_nonneg_right (hsqrt _ ⟨hθ,(rho_bounds θ).2⟩) measureReal_nonneg).trans (hprof θ hθ)
  refine ⟨Q,hcount,hd,hwid,hl,(favard_of_sqrt (compact_carrier Q.pat)
    (by positivity : (0:ℝ)≤1000/k) hs).trans_eq (by ring),?_,hs⟩
  apply csSup_le (weighted_nonempty b Q.pat.carrier)
  rintro _ ⟨θ,hθ,rfl⟩
  by_cases hcut : Real.exp (-(k:ℝ)) ≤ rho θ
  · have ha := hlo _ ⟨hcut,(rho_bounds θ).2⟩
    calc
      _ ≤ (scaleFactor b k*w (rho θ))*length Q.pat.carrier θ :=
        mul_le_mul_of_nonneg_right ha measureReal_nonneg
      _ ≤ scaleFactor b k*(1000/k) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hprof θ hθ) hA
      _ = _ := by ring
  · have ha := hsmall _ ⟨hθ,lt_of_not_ge hcut⟩
    have hlen : length Q.pat.carrier θ ≤ 4 := length_unit (carrier_subset_unit Q.pat) θ
    calc
      _ ≤ (2*scaleFactor b k/k)*4 := mul_le_mul ha hlen measureReal_nonneg (by positivity)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right ks]
        linarith

/-- One dyadic sequence realizes the Favard, angular, and local geometry bounds. -/
theorem exists_blocks {b : ℝ → ℝ} (hb : Admissible b) : ∃ B, BlocksFor b B := by
  have hk (j : ℕ) : 2 ≤ (2:ℕ)^(j+1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n:=j); omega
  choose B hcount hdiam hw hloc hfav hprof hsqrt using fun j => exists_profile_block hb (hk j)
  refine ⟨B,⟨fun j => ?_,fun j => ?_,hw,hloc,fun j => ?_,fun j => ?_,fun j θ hθ => ?_⟩⟩
  · simpa using hcount j
  · simpa using hdiam j
  · simpa using hfav j
  · simpa using hprof j
  · simpa using hsqrt j θ hθ

end
end PermutationStrips.Angular
