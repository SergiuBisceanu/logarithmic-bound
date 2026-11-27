import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Crossings of strips with equal horizontal width

Lengths in this file are initially measured in grid units: a single base interval
has width one.  Dividing horizontal coordinates by the grid size recovers the
unit-square normalization.
-/

open MeasureTheory Set
open scoped Interval BigOperators

namespace PermutationStrips.Crossings

noncomputable section

/-- Horizontal position of a particle with bottom position `a` and top position `b`. -/
def path (a b t : ℝ) : ℝ := (1 - t) * a + t * b

/-- The actual closed section of a parallelogram at height `t`, in grid units. -/
def slice (a b t : ℝ) : Set ℝ := Icc (path a b t) (path a b t + 1)

/-- The overlap length of two width-one intervals at displacement `x`. -/
def tent (x : ℝ) : ℝ := max (1 - |x|) 0

theorem continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

theorem length_inter_slice (a b c d t : ℝ) :
    volume.real (slice a b t ∩ slice c d t) =
      tent (path c d t - path a b t) := by
  rw [slice, slice, Icc_inter_Icc, Real.volume_real_Icc]
  unfold tent
  rcases le_total (path a b t) (path c d t) with h | h
  · rw [max_eq_right h, min_eq_left (by linarith), abs_of_nonneg (sub_nonneg.mpr h)]
    congr 1
    ring
  · rw [max_eq_left h, min_eq_right (by linarith), abs_of_nonpos (sub_nonpos.mpr h)]
    congr 1
    ring

/-- Two strictly ordered starting points cross at an interior height exactly when their
top endpoints have the opposite order. The height is unique. -/
theorem existsUnique_cross_iff {a b c d : ℝ} (h : a < c) :
    (∃! t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ path a b t = path c d t) ↔ d < b := by
  constructor
  · rintro ⟨t, ⟨⟨ht0, ht1⟩, heq⟩, _⟩
    unfold path at heq
    by_contra! hn
    nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr h),
      mul_nonneg ht0.le (sub_nonneg.mpr hn)]
  · intro htop
    let v := (c - a) + (b - d)
    have hv : 0 < v := by dsimp [v]; linarith
    refine ⟨(c - a) / v, ⟨⟨div_pos (sub_pos.mpr h) hv, (div_lt_one hv).2 ?_⟩, ?_⟩, ?_⟩
    · dsimp [v]; linarith
    · unfold path
      field_simp [ne_of_gt hv]
      dsimp [v]
      ring
    · rintro t ⟨_, heq⟩
      apply (eq_div_iff hv.ne').2
      dsimp [v]
      unfold path at heq
      linarith only [heq]

theorem integral_tent (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∫ x in a..b, tent x = 1 := by
  have intg (u v : ℝ) : IntervalIntegrable tent volume u v :=
    continuous_tent.intervalIntegrable _ _
  have left : (∫ x in a..(-1 : ℝ), tent x) = 0 := by
    calc
      _ = ∫ _ in a..(-1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha] at hx
        simp [tent, abs_of_nonpos (by linarith [hx.2] : x ≤ 0),
          max_eq_right (by linarith [hx.2] : 1 + x ≤ 0)]
      _ = 0 := by simp
  have right : (∫ x in (1 : ℝ)..b, tent x) = 0 := by
    calc
      _ = ∫ _ in (1 : ℝ)..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hb] at hx
        simp [tent, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x),
          max_eq_right (by linarith [hx.1] : 1 - x ≤ 0)]
      _ = 0 := by simp
  have rise : (∫ x in (-1 : ℝ)..0, tent x) = 1 / 2 := by
    calc
      _ = ∫ x in (-1 : ℝ)..0, (1 + x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        simp [tent, abs_of_nonpos hx.2, sub_neg_eq_add,
          max_eq_left (by linarith [hx.1] : 0 ≤ 1 + x)]
      _ = _ := by
        rw [intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x) (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
        norm_num
  have fall : (∫ x in (0 : ℝ)..1, tent x) = 1 / 2 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (1 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        simp [tent, abs_of_nonneg hx.1, max_eq_left (sub_nonneg.mpr hx.2)]
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x) (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
        norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (intg a (-1)) (intg (-1) b),
    ← intervalIntegral.integral_add_adjacent_intervals (intg (-1) 0) (intg 0 b),
    ← intervalIntegral.integral_add_adjacent_intervals (intg 0 1) (intg 1 b),
    left, rise, fall, right]
  norm_num

/-- The area of intersection of a crossing pair, computed by integrating its actual
Lebesgue section lengths. The two base gaps can be arbitrary reals at least one. -/
theorem crossing_pair_area {a b c d : ℝ} (hp : 1 ≤ c - a) (hq : 1 ≤ b - d) :
    (∫ t in (0 : ℝ)..1, volume.real (slice a b t ∩ slice c d t)) =
      1 / ((c - a) + (b - d)) := by
  let p := c - a
  let q := b - d
  have hv : 0 < p + q := by dsimp [p, q]; linarith
  have shape (t : ℝ) : volume.real (slice a b t ∩ slice c d t) =
      tent (p - (p + q) * t) := by
    rw [length_inter_slice]
    congr 1
    unfold p q path
    ring
  simp_rw [shape]
  rw [intervalIntegral.integral_comp_sub_mul tent hv.ne' p]
  simp only [mul_one, mul_zero, sub_zero, sub_add_cancel_left, smul_eq_mul]
  rw [integral_tent (-q) p (by dsimp [q]; linarith) hp]
  simp [p, q, one_div]

/-- A non-inverted pair with disjoint bases on both edges contributes zero area. -/
theorem ordered_pair_area {a b c d : ℝ} (h0 : 1 ≤ c - a) (h1 : 1 ≤ d - b) :
    (∫ t in (0 : ℝ)..1, volume.real (slice a b t ∩ slice c d t)) = 0 := by
  calc
    _ = ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have hgap : 1 ≤ path c d t - path a b t := by
        unfold path
        nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0),
          mul_nonneg ht.1 (sub_nonneg.mpr h1)]
      change volume.real (slice a b t ∩ slice c d t) = 0
      rw [length_inter_slice, tent, abs_of_nonneg (by linarith),
        max_eq_right (by linarith)]
    _ = 0 := by simp

def gapWeight (i j : ℕ) : ℝ := |(i : ℝ) - (j : ℝ)|⁻¹

theorem gapWeight_comm (i j : ℕ) : gapWeight i j = gapWeight j i := by
  simp [gapWeight, abs_sub_comm]

private theorem gap_last (n : ℕ) :
    ∑ i ∈ Finset.range n, gapWeight n i = (harmonic n : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range n, (((n - 1 - i : ℕ) : ℝ) + 1)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i hi
      have h : i < n := Finset.mem_range.mp hi
      have he : n - 1 - i + 1 + i = n := by omega
      have hc : ((n - 1 - i : ℕ) : ℝ) + 1 + i = n := by exact_mod_cast he
      have hii : (i : ℝ) ≤ n := by exact_mod_cast h.le
      simp only [gapWeight, abs_of_nonneg (sub_nonneg.mpr hii)]
      congr 1
      linarith
    _ = ∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹ := Finset.sum_range_reflect (fun i : ℕ => ((i : ℝ) + 1)⁻¹) n
    _ = _ := by simp [harmonic]

/-- Exact distribution count for reciprocal distances of all ordered pairs on one grid. -/
theorem sum_gapWeight (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, |(i : ℝ) - (j : ℝ)|⁻¹ =
      2 * ((n : ℝ) * (harmonic n : ℝ) - n) := by
  change ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, gapWeight i j = _
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih]
    have col : ∑ i ∈ Finset.range n, gapWeight i n = (harmonic n : ℝ) := by
      simpa only [gapWeight_comm n] using gap_last n
    rw [col, gap_last]
    have hd : gapWeight n n = 0 := by simp [gapWeight]
    rw [hd, harmonic_succ]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

private theorem inv_add_bound {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    1 / (p + q) ≤ (p⁻¹ + q⁻¹) / 4 := by
  field_simp
  nlinarith [sq_nonneg (p-q)]

/-- Lebesgue height measure on the unit interval. -/
def timeMeasure : Measure ℝ := volume.restrict (Ioc 0 1)
/-- Lebesgue horizontal measure on the unit interval. -/
def spaceMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsFiniteMeasure timeMeasure := ⟨by simp [timeMeasure]⟩
instance : IsFiniteMeasure spaceMeasure := ⟨by simp [spaceMeasure]⟩

/-- Lebesgue area restricted to the unit square. The coordinates are (height, position).
The choice to omit the bottom edge has no effect on area. -/
def squareMeasure : Measure (ℝ × ℝ) := timeMeasure.prod spaceMeasure

instance : IsFiniteMeasure squareMeasure := by
  unfold squareMeasure
  infer_instance

/-- Region between the two straight sides of a strip. The horizontal grid unit is `w`. -/
def strip (w a b : ℝ) : Set (ℝ × ℝ) := {z |
  w * path a b z.1 ≤ z.2 ∧ z.2 ≤ w * (path a b z.1 + 1)}

theorem measurable_strip (w a b : ℝ) : MeasurableSet (strip w a b) := by
  change MeasurableSet ({z : ℝ × ℝ | w * path a b z.1 ≤ z.2} ∩
    {z : ℝ × ℝ | z.2 ≤ w * (path a b z.1 + 1)})
  unfold path
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

/-- Length of a fiber of the physical intersection, in unit-square coordinates. -/
theorem section_pair {w a b c d t : ℝ} (hw : 0 < w)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haw : w*(a+1) ≤ 1) (hbw : w*(b+1) ≤ 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    spaceMeasure.real ((Prod.mk t) ⁻¹' (strip w a b ∩ strip w c d)) =
      w * volume.real (slice a b t ∩ slice c d t) := by
  let A := Icc (w * path a b t) (w * (path a b t + 1))
  let B := Icc (w * path c d t) (w * (path c d t + 1))
  have hsub : A ∩ B ⊆ Icc (0 : ℝ) 1 := by
    rintro x ⟨⟨hl, hr⟩, _⟩
    refine ⟨le_trans ?_ hl, le_trans hr ?_⟩
    · exact mul_nonneg hw.le (add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) ha)
        (mul_nonneg ht.1.le hb))
    · dsimp [path]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr haw),
        mul_nonneg ht.1.le (sub_nonneg.mpr hbw)]
  change (volume.restrict (Icc (0 : ℝ) 1)).real (A ∩ B) = _
  rw [measureReal_restrict_apply (measurableSet_Icc.inter measurableSet_Icc)]
  change volume.real ((A ∩ B) ∩ Icc (0 : ℝ) 1) = _
  rw [inter_eq_left.mpr hsub]
  dsimp [A, B, slice]
  rw [Icc_inter_Icc, Icc_inter_Icc, Real.volume_real_Icc, Real.volume_real_Icc]
  rw [← mul_min_of_nonneg _ _ hw.le, ← mul_max_of_nonneg _ _ hw.le, ← mul_sub]
  rw [mul_max_of_nonneg _ _ hw.le, mul_zero]

/-- Fubini's formula for the area of any measurable set inside the unit square. -/
theorem area_sections {T : Set (ℝ × ℝ)} (mT : MeasurableSet T) :
    squareMeasure.real T = ∫ t, spaceMeasure.real ((Prod.mk t) ⁻¹' T) ∂timeMeasure := by
  rw [← integral_indicator_one mT]
  change (∫ z : ℝ × ℝ, T.indicator (fun _ => (1 : ℝ)) z ∂timeMeasure.prod spaceMeasure) = _
  rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator mT)]
  apply integral_congr_ae
  filter_upwards with t
  have e : (fun x : ℝ => T.indicator (fun _ => (1 : ℝ)) (t,x)) =
      (((Prod.mk t) ⁻¹' T).indicator (1 : ℝ → ℝ)) := by
    funext x
    by_cases h : (t, x) ∈ T
    · simp [h, Set.indicator, Set.mem_preimage]
    · simp [h, Set.indicator, Set.mem_preimage]
  rw [e, integral_indicator_one (measurable_prodMk_left mT)]

theorem measure_pair {w a b c d : ℝ} (hw : 0 < w)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haw : w*(a+1) ≤ 1) (hbw : w*(b+1) ≤ 1) :
    squareMeasure.real (strip w a b ∩ strip w c d) =
      w * (∫ t in (0 : ℝ)..1, volume.real (slice a b t ∩ slice c d t)) := by
  rw [area_sections ((measurable_strip ..).inter (measurable_strip ..)),
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht => section_pair hw ha hb haw hbw ht

/-- A finite second-moment inequality for actual measures of unions and intersections.
It follows by integrating the nonnegative square of `1 - c Z` on the covered set. -/
theorem union_lower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : ι → Set Ω) (hm : ∀ i, MeasurableSet (S i))
    (c : ℝ) :
    2*c*(∑ i, μ.real (S i)) - c^2*(∑ i, ∑ j, μ.real (S i ∩ S j))
      ≤ μ.real (⋃ i, S i) := by
  classical
  let χ (A : Set Ω) := A.indicator (1 : Ω → ℝ)
  have hi {A : Set Ω} (hA : MeasurableSet A) : Integrable (χ A) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have val {A : Set Ω} (hA : MeasurableSet A) : (∫ x, χ A x ∂μ) = μ.real A :=
    integral_indicator_one hA
  have hi₁ : Integrable (fun x => ∑ i, χ (S i) x) μ :=
    integrable_finset_sum _ fun i _ => hi (hm i)
  have hi₂ (i : ι) : Integrable (fun x => ∑ j, χ (S i ∩ S j) x) μ :=
    integrable_finset_sum _ fun j _ => hi ((hm i).inter (hm j))
  have hi₃ : Integrable (fun x => ∑ i, ∑ j, χ (S i ∩ S j) x) μ :=
    integrable_finset_sum _ fun i _ => hi₂ i
  have mulχ (i j : ι) (x : Ω) : χ (S i ∩ S j) x = χ (S i) x * χ (S j) x := by
    by_cases h : x ∈ S i <;> by_cases h' : x ∈ S j <;> simp [χ, h, h']
  have pt (x : Ω) : 2*c*(∑ i, χ (S i) x) - c^2*(∑ i, ∑ j, χ (S i ∩ S j) x)
      ≤ χ (⋃ i, S i) x := by
    simp_rw [mulχ, ← Finset.mul_sum, ← Finset.sum_mul]
    by_cases hx : x ∈ ⋃ i, S i
    · simp only [χ, indicator_of_mem hx, Pi.one_apply]
      nlinarith [sq_nonneg (1 - c * (∑ i, χ (S i) x))]
    · have hn (i : ι) : x ∉ S i := fun hx' => hx (mem_iUnion.mpr ⟨i,hx'⟩)
      simp [χ, hx, hn]
  have h := integral_mono ((hi₁.const_mul (2*c)).sub (hi₃.const_mul (c^2)))
    (hi (MeasurableSet.iUnion hm)) pt
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi₁.const_mul _) (hi₃.const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum _ (fun i _ => hi (hm i)), integral_finset_sum _ (fun i _ => hi₂ i),
    val (MeasurableSet.iUnion hm)] at h
  simpa only [integral_finset_sum _ (fun j _ => hi ((hm _).inter (hm j))),
    val (hm _), val ((hm _).inter (hm _))] using h

theorem measure_strip {w a b : ℝ} (hw : 0 < w)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haw : w*(a+1) ≤ 1) (hbw : w*(b+1) ≤ 1) :
    squareMeasure.real (strip w a b) = w := by
  have h := measure_pair (c := a) (d := b) hw ha hb haw hbw
  simp_rw [length_inter_slice] at h
  simpa [tent] using h

theorem fin_sum_gapWeight (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, gapWeight i.val j.val) =
      2 * ((n:ℝ) * (harmonic n:ℝ) - n) := by
  have row (i : ℕ) : (∑ j : Fin n, gapWeight i j.val) =
      ∑ j ∈ Finset.range n, gapWeight i j := Fin.sum_univ_eq_sum_range (gapWeight i) n
  simp_rw [row]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, gapWeight i j) n]
  exact sum_gapWeight n

private theorem grid_end_bound {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (n : ℝ)⁻¹ * ((i.val : ℝ) + 1) ≤ 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  simpa [← div_eq_inv_mul] using (div_le_one hn').2 hi

/-- Area in the unit square of the strips specified by the permutation `σ`. -/
def permutationArea {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℝ :=
  squareMeasure.real (⋃ i : Fin n, strip (n : ℝ)⁻¹ i.val (σ i).val)

/-- The harmonic lower bound for every permutation, in genuine two-dimensional
Lebesgue area. This counts both orientations of every off-diagonal intersection. -/
theorem harmonic_lower {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    1 / (harmonic n : ℝ) ≤ permutationArea σ := by
  classical
  let w := (n : ℝ)⁻¹
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have wpos : 0 < w := inv_pos.mpr npos
  let S (i : Fin n) := strip w i.val (σ i).val
  have single (i : Fin n) : squareMeasure.real (S i) = w :=
    measure_strip wpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (grid_end_bound hn i)
      (grid_end_bound hn (σ i))
  have wi : (n:ℝ) * w = 1 := by dsimp [w]; field_simp
  have G (i j : Fin n) (h : i < j) : 1 ≤ (j.val:ℝ) - i.val := by
    have aux : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
    linarith
  have off (i j : Fin n) (ltij : i < j) :
      squareMeasure.real (S i ∩ S j) ≤ w / 4 *
        (gapWeight i.val j.val + gapWeight (σ i).val (σ j).val) := by
    change squareMeasure.real (strip w i.val (σ i).val ∩ strip w j.val (σ j).val) ≤ _
    rw [measure_pair wpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (grid_end_bound hn i)
      (grid_end_bound hn (σ i))]
    have p := G i j ltij
    rcases lt_or_gt_of_ne (σ.injective.ne ltij.ne) with htop | htop
    · rw [ordered_pair_area p (G _ _ htop), mul_zero]
      unfold gapWeight
      positivity
    · have q := G _ _ htop
      rw [crossing_pair_area p q]
      have bound := inv_add_bound (by linarith : 0 < (j.val:ℝ) - i.val)
        (by linarith : 0 < ((σ i).val:ℝ) - (σ j).val)
      have gap₁ : gapWeight i.val j.val = ((j.val:ℝ) - i.val)⁻¹ := by
        rw [gapWeight, abs_sub_comm, abs_of_nonneg (by linarith)]
      have gap₂ : gapWeight (σ i).val (σ j).val = (((σ i).val:ℝ) - (σ j).val)⁻¹ := by
        rw [gapWeight, abs_of_nonneg (by linarith)]
      rw [gap₁, gap₂]
      linarith only [mul_le_mul_of_nonneg_left bound wpos.le]
  have pairs (i j : Fin n) :
      squareMeasure.real (S i ∩ S j) ≤
        (if i = j then w else 0) + w/4*(gapWeight i.val j.val + gapWeight (σ i).val (σ j).val) := by
    rcases lt_trichotomy i j with h | h | h
    · simpa [h.ne] using off i j h
    · subst j
      simp [single, gapWeight]
    · simpa only [if_neg h.ne', zero_add, inter_comm (S i), gapWeight_comm i.val j.val,
        gapWeight_comm (σ i).val (σ j).val] using off j i h
  have permG :
      (∑ i : Fin n, ∑ j : Fin n, gapWeight (σ i).val (σ j).val) =
        2 * ((n:ℝ) * (harmonic n:ℝ) - n) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, gapWeight (σ i).val j.val := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j : Fin n => gapWeight (σ i).val j.val)
      _ = ∑ i : Fin n, ∑ j : Fin n, gapWeight i.val j.val :=
        Equiv.sum_comp σ (fun i : Fin n => ∑ j : Fin n, gapWeight i.val j.val)
      _ = _ := fin_sum_gapWeight n
  have energy : ∑ i, ∑ j, squareMeasure.real (S i ∩ S j) ≤ (harmonic n : ℝ) := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ((if i = j then w else 0) +
          w/4*(gapWeight i.val j.val + gapWeight (σ i).val (σ j).val)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pairs i j
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp_rw [Finset.sum_add_distrib]
        rw [fin_sum_gapWeight, permG]
        dsimp [w]
        field_simp
        ring
  have mass : ∑ i, squareMeasure.real (S i) = 1 := by simpa [single] using wi
  have Hpos : 0 < (harmonic n : ℝ) := lt_of_lt_of_le
    (Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))) (log_add_one_le_harmonic n)
  have h := union_lower squareMeasure S (fun i => measurable_strip ..) (1/(harmonic n : ℝ))
  rw [mass, mul_one] at h
  calc
    1 / (harmonic n : ℝ) =
        2*(1/(harmonic n:ℝ)) - (1/(harmonic n:ℝ))^2 * (harmonic n:ℝ) := by
      field_simp
      ring
    _ ≤ _ := (sub_le_sub_left (mul_le_mul_of_nonneg_left energy (sq_nonneg _)) _).trans h

/-- In particular the minimum permitted area cannot decay faster than logarithmically. -/
theorem logarithmic_lower {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    1 / (1 + Real.log n) ≤ permutationArea σ := by
  have hpos : 0 < (harmonic n : ℝ) := lt_of_lt_of_le
    (Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))) (log_add_one_le_harmonic n)
  exact (one_div_le_one_div_of_le hpos (harmonic_le_one_add_log n)).trans (harmonic_lower hn σ)


end
end PermutationStrips.Crossings
