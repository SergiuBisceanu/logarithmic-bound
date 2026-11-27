import PermutationStrips.Crossings

/-!
# Sliding top intervals

The bottom intervals form the equal grid. Their top intervals may start at any
admissible real coordinates, including coincident ones. The pairwise estimate
in this module uses only the gap between the bottom intervals.
-/

open Set MeasureTheory
open scoped Interval BigOperators

namespace PermutationStrips.Sliding

open Crossings

noncomputable section

/-- In grid units, a pair whose bottom intervals start at distance `p ≥ 1`
has overlap area at most `1/p`, regardless of its final displacement. -/
theorem free_pair_area_le {a b c d : ℝ} (hp : 1 ≤ c - a) :
    (∫ t in (0 : ℝ)..1, volume.real (slice a b t ∩ slice c d t)) ≤ (c - a)⁻¹ := by
  let p := c - a
  let s := d - b
  let q := min s 0
  have hp' : 1 ≤ p := hp
  have hq : q ≤ 0 := min_le_right ..
  have hv : 0 < p - q := by linarith
  have ht : Continuous tent := by unfold tent; fun_prop
  have shape (t : ℝ) : volume.real (slice a b t ∩ slice c d t) = tent (path p s t) := by
    rw [length_inter_slice]
    congr 1
    unfold p s path
    ring
  have majorant (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) 1) :
      tent (path p s t) ≤ tent (p - (p-q)*t) := by
    by_cases hs : s ≤ 0
    · have he : path p s t = p - (p-q)*t := by
        dsimp [path, q]; rw [min_eq_left hs]; ring
      rw [he]
    · have hs' : 0 ≤ s := le_of_not_ge hs
      have left : 0 ≤ (1-t)*p := mul_nonneg (sub_nonneg.mpr ht'.2) (by linarith)
      have right := mul_nonneg ht'.1 hs'
      dsimp [tent, path, q]
      rw [min_eq_right hs', sub_zero, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      apply max_le_max_right
      linarith
  have mass : (∫ x in q..p, tent x) ≤ 1 := by
    calc
      _ ≤ ∫ x in min q (-1)..p, tent x := intervalIntegral.integral_mono_interval
        (min_le_left ..) (by linarith) le_rfl
        (Filter.Eventually.of_forall fun x => le_max_right _ _) (ht.intervalIntegrable ..)
      _ = 1 := integral_tent _ _ (min_le_right ..) hp'
  simp_rw [shape]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, tent (p - (p-q)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · exact (ht.comp (by unfold path; fun_prop)).intervalIntegrable ..
      · exact (ht.comp (by fun_prop)).intervalIntegrable ..
      · exact majorant
    _ = (p-q)⁻¹ * ∫ x in q..p, tent x := by
      rw [intervalIntegral.integral_comp_sub_mul tent hv.ne' p]
      simp
    _ ≤ (p-q)⁻¹ := by simpa using mul_le_mul_of_nonneg_left mass (inv_nonneg.mpr hv.le)
    _ ≤ p⁻¹ := inv_anti₀ (by linarith) (by linarith)

private theorem one_le_harmonic {n : ℕ} (hn : 0 < n) : 1 ≤ (harmonic n : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [harmonic_succ]
    push_cast
    exact le_add_of_le_of_nonneg (ih (by omega)) (by positivity)

/-- The area of any freely sliding configuration is at least `1/(2 Hₙ − 1)`.
The argument `b i` is the top start in grid units, so its physical coordinate
is `b i / n`. The bottom starts are the prescribed coordinates `i / n`. -/
theorem sliding_harmonic_lower {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i + 1 ≤ n) :
    (2 * (harmonic n : ℝ) - 1)⁻¹ ≤
      squareMeasure.real (⋃ i : Fin n, strip (1 / n) i.val (b i)) := by
  classical
  let w : ℝ := 1 / n
  let S (i : Fin n) := strip w i.val (b i)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 < w := by dsimp [w]; positivity
  have inside {x : ℝ} (hx : x + 1 ≤ n) : w * (x+1) ≤ 1 := by
    rw [show w * (x+1) = (x+1) / n by dsimp [w]; ring]
    exact (div_le_one hn').2 hx
  have bot (i : Fin n) : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have single (i : Fin n) : squareMeasure.real (S i) = w :=
    measure_strip hw (Nat.cast_nonneg _) (hb i) (inside (bot i)) (inside (hb' i))
  have total : ∑ i, squareMeasure.real (S i) = 1 := by simp [single, w, hn.ne']
  have pair (i j : Fin n) (hij : i < j) :
      squareMeasure.real (S i ∩ S j) ≤ w * gapWeight i.val j.val := by
    have sep : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    calc
      _ = w * (∫ t in (0 : ℝ)..1, volume.real (slice i.val (b i) t ∩ slice j.val (b j) t)) :=
        measure_pair hw (Nat.cast_nonneg _) (hb i) (inside (bot i)) (inside (hb' i))
      _ ≤ w * ((j.val : ℝ) - i.val)⁻¹ := mul_le_mul_of_nonneg_left (free_pair_area_le (by linarith)) hw.le
      _ = w * gapWeight i.val j.val := by
        rw [gapWeight, abs_of_nonpos (by linarith), neg_sub]
  have entry (i j : Fin n) :
      squareMeasure.real (S i ∩ S j) ≤ w * ((if i = j then 1 else 0) + gapWeight i.val j.val) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simpa [ne_of_lt h] using pair i j h
    · simp [single, gapWeight]
    · simpa [Set.inter_comm, gapWeight, abs_sub_comm (j.val : ℝ), ne_of_gt h] using pair j i h
  let D : ℝ := 2 * (harmonic n : ℝ) - 1
  have hD : 0 < D := by dsimp [D]; linarith [one_le_harmonic hn]
  have energy : ∑ i, ∑ j, squareMeasure.real (S i ∩ S j) ≤ D := by
    calc
      _ ≤ ∑ i, ∑ j, w * ((if i = j then 1 else 0) + gapWeight i.val j.val) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
      _ = w * (n + ∑ i : Fin n, ∑ j : Fin n, gapWeight i.val j.val) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        simp
      _ = D := by rw [fin_sum_gapWeight]; dsimp [D,w]; field_simp; ring
  have moment := union_lower squareMeasure S (fun _ => measurable_strip ..) D⁻¹
  rw [total] at moment
  calc
    D⁻¹ = 2 * D⁻¹ * 1 - (D⁻¹)^2 * D := by field_simp; ring
    _ ≤ _ := sub_le_sub_left (mul_le_mul_of_nonneg_left energy (sq_nonneg D⁻¹)) _
    _ ≤ _ := moment

/-- Explicit logarithmic lower bound in the original sliding-top model. -/
theorem sliding_log_lower {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i + 1 ≤ n) :
    (1 + 2 * Real.log n)⁻¹ ≤
      squareMeasure.real (⋃ i : Fin n, strip (1 / n) i.val (b i)) := by
  apply le_trans _ (sliding_harmonic_lower hn b hb hb')
  apply inv_anti₀ <;> linarith [one_le_harmonic hn, harmonic_le_one_add_log n]

end

end PermutationStrips.Sliding
