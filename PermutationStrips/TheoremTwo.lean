import PermutationStrips.AngularSequence
import PermutationStrips.AngularRates
import PermutationStrips.AngularExtrema
import PermutationStrips.AngularGridTransfer
import PermutationStrips.AngularCritical
import PermutationStrips.CompactAhlfors

/-!
# Sharp angular decay at every scale (Theorem 2)

For each nondecreasing weight on (0,1/2], one compact set realizes all scales.
The lower bound for the compact infimum permits either visible coordinate axis.
The Euclidean length, marginals and Ahlfors bounds are spelled out in
`CompactPlane.WitnessGeometry`; `thick` uses the coordinate square [-δ,δ]².
-/

open Set MeasureTheory
open scoped Asymptotics
namespace PermutationStrips.Angular
open CompactPlane
noncomputable section

/-- The two extremal laws and their simultaneous realizations.
The same numerical constant applies to every weight, scale and grid size. -/
structure SharpProfile (C : ℝ) (b : ℝ → ℝ) (S : Set (ℝ × ℝ)) : Prop where
  geometry : WitnessGeometry S
  oblique_null : ∀ θ, 0 < rho θ → length S θ = 0
  compact_optimum : ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
    (1+truncated b δ)/(C*Real.log (1/δ)) ≤ compactInf b δ ∧
    compactInf b δ ≤ C*(1+truncated b δ)/Real.log (1/δ)
  all_scales : ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
    let K := thick δ S
    1/(C*Real.log (1/δ)) ≤ favard K ∧ favard K ≤ C/Real.log (1/δ) ∧
      favard K + weighted b K ≤ C*(1+truncated b δ)/Real.log (1/δ)
  grid_optimum : ∀ (n : ℕ) (hn : 2 ≤ n),
    (1+truncated b (1/n))/(C*Real.log n) ≤ gridMin b n (by omega) ∧
    gridMin b n (by omega) ≤ C*(1+truncated b (1/n))/Real.log n
  grid_witness : ∀ (n : ℕ) (hn : 2 ≤ n), ∃ σ : Equiv.Perm (Fin n),
    let K := (Pattern.equalGrid (by omega : 0<n) σ).carrier
    favard K ≤ C/Real.log n ∧
      favard K + weighted b K ≤ C*(1+truncated b (1/n))/Real.log n

/-- Theorem 2. Both comparisons hold with absolute constants, and the compact
witness has Euclidean Hausdorff length one, uniform marginals and Ahlfors regular
length measure. Its projections have zero length in every oblique direction. -/
theorem sharp_angular_profile :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ b : ℝ → ℝ, Admissible b →
      ∃ S : Set (ℝ × ℝ), SharpProfile C b S := by
  let C := 2*upperConstant
  have hu := upperConstant_ge_one
  have hc : 48 ≤ C := by norm_num [C,upperConstant]
  have huc : upperConstant ≤ C := by dsimp [C]; linarith
  refine ⟨C,by linarith,?_⟩
  intro b hb
  obtain ⟨B,hB⟩ := exists_blocks hb
  let S := limitSet B
  have hg : WitnessGeometry S :=
    witnessGeometry B hB.width hB.local_geometry dyadic_error_tendsto (fun _ => by positivity) hB.diameter
  have hv : visibleCompact S := ⟨hg.compact,hg.subset_unit,Or.inl hg.horizontal⟩
  have upper {δ : ℝ} (hd : 0<δ) (hh : δ≤1/2) :
      favard (thick δ S) ≤ C/Real.log (1/δ) ∧
      favard (thick δ S)+weighted b (thick δ S) ≤ C*(1+truncated b δ)/Real.log (1/δ) := by
    have hp : 0 < Real.log (1/δ) := Real.log_pos ((lt_div_iff₀ hd).mpr (by linarith))
    obtain ⟨hF,hM⟩ := limit_upper hb hB hd hh
    have ha := truncated_nonneg hb hd hh
    refine ⟨hF.trans (div_le_div_of_nonneg_right huc hp.le), (add_le_add hF hM).trans ?_⟩
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hp.le
    dsimp [C]; nlinarith [mul_nonneg (by linarith : 0 ≤ upperConstant) ha]
  obtain ⟨μ,hprob,hsupport,hx,hy⟩ := hg.hall
  letI : IsProbabilityMeasure μ := hprob
  have grid (n : ℕ) (hn : 2≤n) :
      ∃ σ : Equiv.Perm (Fin n), let K := (Pattern.equalGrid (by omega : 0<n) σ).carrier
        favard K ≤ C/Real.log n ∧ favard K+weighted b K ≤ C*(1+truncated b (1/n))/Real.log n := by
    have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hn
    have hd : 0 < 1/(n:ℝ) := by positivity
    have hh : 1/(n:ℝ) ≤ 1/2 := by apply (div_le_div_iff₀ hp (by norm_num : (0:ℝ)<2)).mpr; linarith
    obtain ⟨σ,hσ⟩ := exists_grid_subset_thick μ hsupport hx hy (n := n) (by omega)
    have hs := compact_thick hg.compact (1/(n:ℝ))
    have hF := favard_mono (compact_carrier _) hs hσ
    have hM := weighted_mono hb hs hσ
    obtain ⟨u,v⟩ := upper hd hh
    rw [show 1/(1/(n:ℝ))=n by simp] at u v
    exact ⟨σ,hF.trans u,(add_le_add hF hM).trans v⟩
  refine ⟨S,hg,fun _ h => limit_oblique hB h,?_,?_,?_,grid⟩
  · intro δ hd hh
    simpa only [max_eq_right hc] using compact_law hb hd hh ⟨S,hv,(upper hd hh).2⟩
  · intro δ hd hh
    have hL : 0 < Real.log (1/δ) := Real.log_pos ((lt_div_iff₀ hd).mpr (by linarith))
    have hf := (AngularLower.compact_lower hb hg.compact hg.subset_unit
      (Or.inl hg.horizontal.ge) hd hh).1
    have hf' : 1/(8*Real.log (1/δ)) ≤ favard (thick δ S) :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    exact ⟨(by
      apply le_trans _ hf'
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) hL.le),upper hd hh⟩
  · intro n hn
    obtain ⟨σ,_,hu'⟩ := grid n hn
    simpa only [max_eq_right hc] using grid_law hb hn ⟨σ,hu'⟩

/-- The minimum weighted projection alone incurs the log-log loss at the critical weight. -/
theorem critical_grid_rate :
    gridWeightedMin criticalWeight =Θ[Filter.atTop] (fun n : ℕ => Real.log (Real.log n)/Real.log n) := by
  obtain ⟨C,hC,H⟩ := sharp_angular_profile
  obtain ⟨S,hS⟩ := H _ critical_admissible
  exact critical_grid_rate_of_joint (zero_le_one.trans hC) (fun n hn => (hS.grid_optimum n hn).2)

end
end PermutationStrips.Angular
