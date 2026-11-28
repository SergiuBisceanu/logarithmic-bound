import PermutationStrips.AngularExceptional
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Logarithmically many depth-k paths give the weighted profile eventually
at almost every height along one sequence of deterministic ensembles. -/

open Set MeasureTheory Filter
open scoped BigOperators ENNReal

namespace PermutationStrips.AngularBlock
noncomputable section

/-- Ensemble size used for the summable exceptional-height bound. -/
def logSampleCount (k : ℕ) : ℕ := 1 + ⌈32 * Real.log ((k : ℝ) + 1)⌉₊

theorem logSampleCount_le (k : ℕ) :
    (logSampleCount k : ℝ) ≤ 2 + 32 * Real.log ((k : ℝ) + 1) := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 32 * Real.log ((k : ℝ) + 1) by
    apply mul_nonneg (by norm_num); exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  unfold logSampleCount; push_cast; linarith

private theorem logSample_tail (k : ℕ) :
    2 * Real.exp (-(logSampleCount k : ℝ) * (1/16)) ≤ 2 / ((k : ℝ) + 1)^2 := by
  have h := Nat.le_ceil (32 * Real.log ((k : ℝ) + 1))
  have h' : -(logSampleCount k : ℝ) * (1/16) ≤ -(2 * Real.log ((k : ℝ) + 1)) := by
    unfold logSampleCount; push_cast; linarith
  calc
    _ ≤ 2 * Real.exp (-(2 * Real.log ((k : ℝ) + 1))) := by gcongr
    _ = _ := by
      rw [Real.exp_neg, two_mul (Real.log _), Real.exp_add, Real.exp_log (by positivity)]; ring

/-- A single triangular array of concrete paths attains the weighted 195/k
estimate eventually at almost every interior height. -/
theorem profile_eventually_ae {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3) :
    ∃ p : (k : ℕ) → Fin (logSampleCount k) → Path,
      (∀ k i, (p k i).depth = k ∧ (Fintype.card (p k i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ᵐ x : ℝ, x ∈ Ioo (0:ℝ) 1 → ∀ᶠ k in atTop,
        w (radius x) * ((∑ i, len (p k i).pattern x)/(logSampleCount k : ℝ)) ≤ 195/k := by
  classical
  let bad (k : ℕ) (p : Fin (logSampleCount k) → Path) := {x ∈ Ioo (0:ℝ) 1 |
    (256*(Real.log 2 + 1/16)+1)/k < w (radius x) * ((∑ i, len (p i).pattern x)/(logSampleCount k : ℝ))}
  have hfin : volume (Ioo (0:ℝ) 1) < ∞ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hb (k : ℕ) : ∃ p : Fin (logSampleCount k) → Path,
      (∀ i, (p i).depth = k ∧ (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      volume.real (bad k p) ≤ 2/((k : ℝ)+1)^2 := by
    cases k with
    | zero =>
      refine ⟨fun _ => .seed, fun _ => ⟨rfl, by simp [Path.Index]⟩, ?_⟩
      have sub : bad 0 (fun _ => .seed) ⊆ Ioo (0:ℝ) 1 := fun _ h => h.1
      exact (measureReal_mono sub hfin.ne).trans (by norm_num [Real.volume_real_Ioo])
    | succ k =>
      obtain ⟨p, hp, he⟩ := profile_exceptional hm hw hmono hi hI (k+1) _ (by omega)
        (show 0 < logSampleCount (k+1) by unfold logSampleCount; omega)
      exact ⟨p, hp, (he (1/16)).trans (logSample_tail _)⟩
  choose p hp he using hb
  refine ⟨p, hp, ?_⟩
  have hs : Summable (fun k : ℕ => 2/((k : ℝ)+1)^2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    simpa [div_eq_mul_inv] using h.mul_left (2 : ℝ)
  have hsum : (∑' k, volume (bad k (p k))) < ∞ := calc
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (2/((k : ℝ)+1)^2) := by
      apply ENNReal.tsum_le_tsum; intro k
      have sub : bad k (p k) ⊆ Ioo (0:ℝ) 1 := fun _ h => h.1
      have fin : volume (bad k (p k)) ≠ ∞ := ((measure_mono sub).trans_lt hfin).ne
      simpa only [measureReal_def, ENNReal.ofReal_toReal fin] using ENNReal.ofReal_le_ofReal (he k)
    _ < ∞ := by rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs]; exact ENNReal.ofReal_lt_top
  filter_upwards [ae_eventually_notMem hsum.ne] with x hx
  intro hxi
  filter_upwards [hx] with k hk
  exact (le_of_not_gt (fun h => hk ⟨hxi,h⟩)).trans
    (div_le_div_of_nonneg_right (by linarith [Real.log_two_lt_d9]) (Nat.cast_nonneg k))

end
end PermutationStrips.AngularBlock
