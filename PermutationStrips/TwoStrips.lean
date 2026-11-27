import Mathlib

/-! Exact minima for two equal strips with sliding or permuted top intervals. -/

open Set MeasureTheory

namespace PermutationStrips.TwoStrips

/-- The horizontal section at height `t`, for top intervals starting at `a` and `b`. -/
def sectionAt (a b t : ℝ) : Set ℝ :=
  Icc (t * a) (t * a + 1/2) ∪ Icc ((1-t)/2 + t*b) ((1-t)/2 + t*b + 1/2)

/-- The signed separation of the left endpoints. -/
noncomputable def gap (a b t : ℝ) : ℝ := 1/2 + (b-a-1/2)*t

/-- Area by horizontal sections (Cavalieri). -/
noncomputable def area (q : ℝ × ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, volume.real (sectionAt q.1 q.2 t)

def sliding : Set (ℝ × ℝ) := Icc 0 (1/2) ×ˢ Icc 0 (1/2)
def permuted : Set (ℝ × ℝ) := {(0,1/2), (1/2,0)}

private theorem touching_intervals {x y w : ℝ} (hxy : x ≤ y) (hgap : y ≤ x+w) :
    Icc x (x+w) ∪ Icc y (y+w) = Icc x (y+w) := by
  ext z
  constructor
  · rintro (⟨hz, hz'⟩ | ⟨hz, hz'⟩)
    · exact ⟨hz, by linarith⟩
    · exact ⟨by linarith, hz'⟩
  · rintro ⟨hz, hz'⟩
    by_cases h : z ≤ x+w
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨by linarith,hz'⟩

theorem section_length {a b t : ℝ} (hq : (a,b) ∈ sliding) (ht : t ∈ Icc (0:ℝ) 1) :
    volume.real (sectionAt a b t) = 1/2 + |gap a b t| := by
  obtain ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩ := hq
  obtain ⟨ht, ht'⟩ := ht
  let x := t*a
  let y := (1-t)/2+t*b
  have hg : gap a b t = y-x := by dsimp [x,y,gap]; ring
  have hx : 0 ≤ x := mul_nonneg ht ha
  have hy : 0 ≤ y := by dsimp [y]; nlinarith [mul_nonneg ht hb]
  have hx' : x ≤ 1/2 := by dsimp [x]; nlinarith [mul_nonneg ht (sub_nonneg.mpr ha')]
  have hy' : y ≤ 1/2 := by dsimp [y]; nlinarith [mul_nonneg ht (sub_nonneg.mpr hb')]
  change volume.real (Icc x (x+1/2) ∪ Icc y (y+1/2)) = _
  rw [hg]
  rcases le_total x y with h|h
  · rw [touching_intervals h (by linarith), Real.volume_real_Icc_of_le (by linarith),
        abs_of_nonneg (sub_nonneg.mpr h)]
    ring
  · rw [Set.union_comm, touching_intervals h (by linarith), Real.volume_real_Icc_of_le (by linarith),
        abs_of_nonpos (sub_nonpos.mpr h)]
    ring

/-- The union of the two closed parallelograms, in (height, position) coordinates. -/
def covered (q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (0:ℝ) 1 ∧ z.2 ∈ sectionAt q.1 q.2 z.1}

/-- Cavalieri's formula for the two actual planar strips. -/
theorem area_eq_volume {q : ℝ × ℝ} (hq : q ∈ sliding) :
    area q = volume.real (covered q) := by
  have hm : MeasurableSet (covered q) := by
    apply (measurableSet_Icc.preimage measurable_fst).inter
    apply MeasurableSet.union <;>
      exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (by fun_prop) (by fun_prop))
  have sub : covered q ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    obtain ⟨⟨ha,ha'⟩,⟨hb,hb'⟩⟩ := hq
    refine ⟨ht, ?_⟩
    rcases hx with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · constructor
      · exact le_trans (mul_nonneg ht.1 ha) hl
      · dsimp at hr; nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ha'), ht.2]
    · constructor
      · dsimp at hl; nlinarith [mul_nonneg ht.1 hb, ht.2]
      · dsimp at hr; nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hb')]
  have hf : volume (covered q) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono sub) (by rw [Measure.volume_eq_prod, Measure.prod_prod]; simp)).ne
  rw [← integral_indicator_one hm, Measure.volume_eq_prod,
    integral_prod _ ((integrable_indicator_iff hm).mpr (integrableOn_const hf))]
  unfold area
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · rw [indicator_of_mem ht, ← integral_indicator_one (s := sectionAt q.1 q.2 t) (measurableSet_Icc.union measurableSet_Icc)]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ sectionAt q.1 q.2 t
    · have hz : (t,x) ∈ covered q := ⟨ht,hx⟩
      simp [hx,hz]
    · have hz : (t,x) ∉ covered q := fun h => hx h.2
      simp [hx,hz]
  · rw [indicator_of_notMem ht]
    simp [covered, ht, Set.indicator]

private theorem gap_integral (a b l r : ℝ) :
    (∫ t in l..r, gap a b t) = (r-l)/2+(b-a-1/2)*(r^2-l^2)/2 := by
  unfold gap
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  · simp only [smul_eq_mul]; ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) ..

private theorem area_eq {a b : ℝ} (hq : (a,b) ∈ sliding) :
    area (a,b) = 1/2 + ∫ t in (0:ℝ)..1, |gap a b t| := by
  unfold area
  calc
    _ = ∫ t in (0:ℝ)..1, (1/2 + |gap a b t|) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact section_length hq (by simpa [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht)
    _ = _ := by
      rw [intervalIntegral.integral_add, intervalIntegral.integral_const]
      · norm_num
      all_goals exact Continuous.intervalIntegrable (by first | fun_prop | (unfold gap; fun_prop)) ..

private theorem split_bound {a b c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    (∫ t in (0:ℝ)..c, gap a b t) - (∫ t in c..1, gap a b t) ≤
      ∫ t in (0:ℝ)..1, |gap a b t| := by
  have hi : ∀ l r : ℝ, IntervalIntegrable (fun t => |gap a b t|) volume l r := by
    intro l r; exact Continuous.intervalIntegrable (by first | fun_prop | (unfold gap; fun_prop)) ..
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1), sub_eq_add_neg,
    ← intervalIntegral.integral_neg]
  apply add_le_add
  · apply intervalIntegral.integral_mono_on hc.1
    · exact Continuous.intervalIntegrable (by first | fun_prop | (unfold gap; fun_prop)) ..
    · exact hi ..
    · intro t _; exact le_abs_self _
  · apply intervalIntegral.integral_mono_on hc.2
    · exact Continuous.intervalIntegrable (by first | fun_prop | (unfold gap; fun_prop)) ..
    · exact hi ..
    · intro t _; exact neg_le_abs _

private theorem split_exact {a b c : ℝ} (hc : c ∈ Icc (0:ℝ) 1)
    (hl : ∀ t ∈ Icc 0 c, 0 ≤ gap a b t) (hr : ∀ t ∈ Icc c 1, gap a b t ≤ 0) :
    (∫ t in (0:ℝ)..1, |gap a b t|) =
    (∫ t in (0:ℝ)..c, gap a b t) - (∫ t in c..1, gap a b t) := by
  have hi : ∀ l r : ℝ, IntervalIntegrable (fun t => |gap a b t|) volume l r := by
    intro l r; exact Continuous.intervalIntegrable (by first | fun_prop | (unfold gap; fun_prop)) ..
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1),
      sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonneg (hl t (by simpa [uIcc_of_le hc.1] using ht))
  · apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonpos (hr t (by simpa [uIcc_of_le hc.2] using ht))

/-- The exact minimum in the freely sliding problem. -/
theorem sliding_minimum : IsLeast (area '' sliding) (Real.sqrt 2 / 2) := by
  let c := Real.sqrt 2 / 2
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hcs : c*c = 1/2 := by dsimp [c]; nlinarith
  have hc : c ∈ Icc (0:ℝ) 1 := by
    constructor <;> dsimp [c] <;> nlinarith [Real.sqrt_nonneg 2]
  have hc' : 1/2 ≤ c := by dsimp [c]; nlinarith [Real.sqrt_nonneg 2]
  have calc_area (a b : ℝ) : (∫ t in (0:ℝ)..c, gap a b t) - (∫ t in c..1, gap a b t) =
      c-1/2 := by
    rw [gap_integral, gap_integral]
    linear_combination (b-a-1/2) * hcs
  change IsLeast _ c
  constructor
  · have hq : ((1/2:ℝ),1-c) ∈ sliding := ⟨⟨by norm_num, le_rfl⟩, ⟨by linarith [hc.2],by linarith⟩⟩
    refine ⟨_, hq, ?_⟩
    rw [area_eq hq, split_exact hc, calc_area]
    · ring
    · intro t ht; unfold gap; nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr ht.2)]
    · intro t ht; unfold gap; nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr ht.1)]
  · rintro _ ⟨⟨a,b⟩, hq, rfl⟩
    rw [area_eq hq]
    linarith [split_bound (a := a) (b := b) hc, calc_area a b]

/-- The exact minimum when the two top intervals permute the bottom grid. -/
theorem permutation_minimum : IsLeast (area '' permuted) (3/4 : ℝ) := by
  have hs : ((1/2:ℝ),0) ∈ sliding := by norm_num [sliding]
  have hswap : area (1/2,0) = 3/4 := by
    rw [area_eq hs, split_exact (c := 1/2) (by norm_num : (1/2:ℝ) ∈ Icc 0 1),
        gap_integral, gap_integral]
    · norm_num
    · intro t ht; simp [gap]; linarith [ht.2]
    · intro t ht; simp [gap]; linarith [ht.1]
  have hi : ((0:ℝ),1/2) ∈ sliding := by norm_num [sliding]
  have hid : area (0,1/2) = 1 := by
    rw [area_eq hi]; norm_num [gap]
  constructor
  · exact ⟨_, by simp [permuted], hswap⟩
  · rintro _ ⟨q,hq,rfl⟩
    rcases (show q = (0,1/2) ∨ q = (1/2,0) from hq) with rfl | rfl
    · rw [hid]; norm_num
    · exact hswap.ge

end PermutationStrips.TwoStrips
